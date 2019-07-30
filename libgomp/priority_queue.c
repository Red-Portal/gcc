/* Copyright (C) 2015-2019 Free Software Foundation, Inc.
   Contributed by Aldy Hernandez <aldyh@redhat.com>.

   This file is part of the GNU Offloading and Multi Processing Library
   (libgomp).

   Libgomp is free software; you can redistribute it and/or modify it
   under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
   more details.

   Under Section 7 of GPL version 3, you are granted additional
   permissions described in the GCC Runtime Library Exception, version
   3.1, as published by the Free Software Foundation.

   You should have received a copy of the GNU General Public License and
   a copy of the GCC Runtime Library Exception along with this program;
   see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
   <http://www.gnu.org/licenses/>.  */

/* Priority queue implementation of GOMP tasks.  */

#include "libgomp.h"

#if _LIBGOMP_CHECKING_
#include <stdio.h>

/* Sanity check to verify whether a TASK is in LIST.  Return TRUE if
   found, FALSE otherwise.

   TYPE is the type of priority queue this task resides in.  */

static inline bool
priority_queue_task_in_list_p (struct priority_list *list,
			       struct gomp_task *task)
{
  struct priority_node *p = list->tasks;
  do
    {
      if (priority_node_to_task (p) == task)
	return true;
      p = p->next;
    }
  while (p != list->tasks);
  return false;
}

/* Tree version of priority_queue_task_in_list_p.  */

static inline bool
priority_queue_task_in_tree_p (struct priority_queue *head,
			       struct gomp_task *task)
{
  struct priority_list *list
    = priority_queue_lookup_priority (head, task->priority);
  if (!list)
    return false;
  return priority_queue_task_in_list_p (list, task);
}

/* Generic version of priority_queue_task_in_list_p that works for
   trees or lists.  */

bool
priority_queue_task_in_queue_p (struct priority_queue *head,
				struct gomp_task *task)
{
  if (priority_queue_empty_p (head, MEMMODEL_RELAXED))
    return false;
  if (priority_queue_multi_p (head))
    return priority_queue_task_in_tree_p (head, task);
  else
    return priority_queue_task_in_list_p (&head->l, task);
}

/* Sanity check LIST to make sure the tasks therein are in the right
   order.  LIST is a priority list of type TYPE.

   The expected order is that GOMP_TASK_WAITING tasks come before
   GOMP_TASK_TIED/GOMP_TASK_ASYNC_RUNNING ones.

   If CHECK_DEPS is TRUE, we also check that parent_depends_on WAITING
   tasks come before !parent_depends_on WAITING tasks.  This is only
   applicable to the children queue, and the caller is expected to
   ensure that we are verifying the children queue.  */

static void
priority_list_verify (struct priority_list *list, bool check_deps)
{
  bool seen_tied = false;
  bool seen_plain_waiting = false;
  struct priority_node *p = list->tasks;
  while (1)
    {
      struct gomp_task *t = priority_node_to_task (p);
      if (seen_tied && t->kind == GOMP_TASK_WAITING)
	gomp_fatal ("priority_queue_verify: WAITING task after TIED");
      if (t->kind >= GOMP_TASK_TIED)
	seen_tied = true;
      else if (check_deps && t->kind == GOMP_TASK_WAITING)
	{
	  if (t->parent_depends_on)
	    {
	      if (seen_plain_waiting)
		gomp_fatal ("priority_queue_verify: "
			    "parent_depends_on after !parent_depends_on");
	    }
	  else
	    seen_plain_waiting = true;
	}
      p = p->next;
      if (p == list->tasks)
	break;
    }
}

/* Verify every task in NODE.

   Callback for splay_tree_foreach.  */

static void
priority_tree_verify_callback (prio_splay_tree_key key, void *data)
{
  priority_list_verify (&key->l, *(bool *)data);
}

/* Generic version of priority_list_verify.

   Sanity check HEAD to make sure the tasks therein are in the right
   order.  The priority_queue holds tasks of type TYPE.

   If CHECK_DEPS is TRUE, we also check that parent_depends_on WAITING
   tasks come before !parent_depends_on WAITING tasks.  This is only
   applicable to the children queue, and the caller is expected to
   ensure that we are verifying the children queue.  */

void
priority_queue_verify (struct priority_queue *head, bool check_deps)
{
  if (priority_queue_empty_p (head, MEMMODEL_RELAXED))
    return;
  if (priority_queue_multi_p (head))
    {
      prio_splay_tree_foreach (&head->t, priority_tree_verify_callback,
			       &check_deps);
    }
  else
    priority_list_verify (&head->l, check_deps);
}
#endif /* _LIBGOMP_CHECKING_ */

/* Remove NODE from priority queue HEAD, wherever it may be inside the
   tree.  HEAD contains tasks of type TYPE.  */

void
priority_tree_remove (struct priority_queue *head,
		      struct priority_node *node)
{
  /* ?? The only reason this function is not inlined is because we
     need to find the priority within gomp_task (which has not been
     completely defined in the header file).  If the lack of inlining
     is a concern, we could pass the priority number as a
     parameter, or we could move this to libgomp.h.  */
  int priority = priority_node_to_task (node)->priority;

  /* ?? We could avoid this lookup by keeping a pointer to the key in
     the priority_node.  */
  struct priority_list *list
    = priority_queue_lookup_priority (head, priority);
#if _LIBGOMP_CHECKING_
  if (!list)
    gomp_fatal ("Unable to find priority %d", priority);
#endif
  /* If NODE was the last in its priority, clean up the priority.  */
  if (priority_list_remove (list, node, MEMMODEL_RELAXED))
    {
      prio_splay_tree_remove (&head->t, (prio_splay_tree_key) list);
      list->tasks = NULL;
#if _LIBGOMP_CHECKING_
      memset (list, 0xaf, sizeof (*list));
#endif
      free (list);
    }
}

/* Return the highest priority WAITING task in a splay tree NODE.  If
   there are no WAITING tasks available, return NULL.

   NODE is a priority list containing tasks of type TYPE.

   The right most node in a tree contains the highest priority.
   Recurse down to find such a node.  If the task at that max node is
   not WAITING, bubble back up and look at the remaining tasks
   in-order.  */

static struct gomp_task *
priority_tree_next_task_1 (prio_splay_tree_node node)
{
 again:
  if (!node)
    return NULL;
  struct gomp_task *ret = priority_tree_next_task_1 (node->right);
  if (ret)
    return ret;
  ret = priority_node_to_task (node->key.l.tasks);
  if (ret->kind == GOMP_TASK_WAITING)
    return ret;
  node = node->left;
  goto again;
}

/* Return the highest priority WAITING task from within Q1 and Q2,
   while giving preference to tasks from Q1.  Q1 is a queue containing
   items of type TYPE1.  Q2 is a queue containing items of type TYPE2.

   Since we are mostly interested in Q1, if there are no WAITING tasks
   in Q1, we don't bother checking Q2, and just return NULL.

   As a special case, Q2 can be NULL, in which case, we just choose
   the highest priority WAITING task in Q1.  This is an optimization
   to speed up looking through only one queue.

   If the returned task is chosen from Q1, *Q1_CHOSEN_P is set to
   TRUE, otherwise it is set to FALSE.  */

struct gomp_task *
priority_tree_next_task (struct priority_queue *q)
{
  return priority_tree_next_task_1 (q->t.root);
}

/* Priority splay trees comparison function.  */
static inline int
prio_splay_compare (prio_splay_tree_key x, prio_splay_tree_key y)
{
  if (x->l.priority == y->l.priority)
    return 0;
  return x->l.priority < y->l.priority ? -1 : 1;
}

/* Define another splay tree instantiation, for priority_list's.  */
#define splay_tree_prefix prio
#define splay_tree_c
#include "splay-tree.h"

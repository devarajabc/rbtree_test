#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

#include "rbtree.h"

#ifdef RBTREE_TEST
#define printf_log(...)
#define dynarec_log(...)
#define rbtreeMalloc malloc
#define rbtreeFree free
#else
#include "custommem.h"
#include "debug.h"
#define rbtreeMalloc customMalloc
#define rbtreeFree customFree
#endif

/*
 * rv32emu is freely redistributable under the MIT License. See the file
 * "LICENSE" for information on usage and redistribution of this file.
 */

/* This map implementation has undergone extensive modifications, heavily
 * relying on the rb.h header file from jemalloc.
 * The original rb.h file served as the foundation and source of inspiration
 * for adapting and tailoring it specifically for this map implementation.
 * Therefore, credit and sincere thanks are extended to jemalloc for their
 * invaluable work.
 * Reference:
 *   https://github.com/jemalloc/jemalloc/blob/dev/include/jemalloc/internal/rb.h
 */

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Each node in the red-black tree consumes at least 1 byte of space (for the
 * linkage if nothing else), so there are a maximum of sizeof(void *) << 3
 * red-black tree nodes in any process (and thus, at most sizeof(void *) << 3
 * nodes in any red-black tree). The choice of algorithm bounds the depth of
 * a tree to twice the binary logarithm (base 2) of the number of elements in
 * the tree; the following bound applies.
 */
#define RB_MAX_DEPTH (sizeof(void *) << 4)

typedef enum { RB_BLACK = 0, RB_RED } color_t;
typedef struct rbnode {
  struct rbnode *left, *right_red;
  uintptr_t start, end;
  uint64_t data;
} rbnode;

struct rbtree {
  rbnode *root;
  const char *name;
  bool is_unstable;
};

typedef struct {
  rbnode *prev, *node;
  size_t count;
} map_iter_t;

static inline cmp_t comparator(uintptr_t a, uintptr_t b) {
  return (a < b) ? _CMP_LESS : (a > b) ? _CMP_GREATER : _CMP_EQUAL;
}

/* Left accessors */
static inline rbnode *rb_node_get_left(const rbnode *node) {
  return node->left;
}

static inline void rb_node_set_left(rbnode *node, rbnode *left) {
  node->left = left;
}

/* Right accessors */
static inline rbnode *rb_node_get_right(const rbnode *node) {
  // What if node->right_red == NULL
  return (rbnode *)(((uintptr_t)node->right_red) & ~3);
}

static inline void rb_node_set_right(rbnode *node, rbnode *right) {
  node->right_red =
      (rbnode *)(((uintptr_t)right) | (((uintptr_t)node->right_red) & 1));
}

/* Color accessors */
static inline color_t rb_node_get_color(const rbnode *node) {
  return ((uintptr_t)node->right_red) & 1;
}

static inline void rb_node_set_color(rbnode *node, color_t color) {
  node->right_red = (rbnode *)(((uintptr_t)node->right_red & ~3) | color);
}

static inline void rb_node_set_red(rbnode *node) {
  node->right_red = (rbnode *)(((uintptr_t)node->right_red) | 1);
}

static inline void rb_node_set_black(rbnode *node) {
  node->right_red = (rbnode *)(((uintptr_t)node->right_red) & ~3);
}

/* Node initializer */
static inline void rb_node_init(rbnode *node) {
  assert((((uintptr_t)node) & (0x1)) == 0); /* a pointer without marker */
  rb_node_set_left(node, NULL);
  rb_node_set_right(node, NULL);
  rb_node_set_red(node);
}

/* Internal helper macros */
#define rb_node_rotate_left(x_node, r_node)                                    \
  do {                                                                         \
    (r_node) = rb_node_get_right((x_node));                                    \
    rb_node_set_right((x_node), rb_node_get_left((r_node)));                   \
    rb_node_set_left((r_node), (x_node));                                      \
  } while (0)

#define rb_node_rotate_right(x_node, r_node)                                   \
  do {                                                                         \
    (r_node) = rb_node_get_left((x_node));                                     \
    rb_node_set_left((x_node), rb_node_get_right((r_node)));                   \
    rb_node_set_right((r_node), (x_node));                                     \
  } while (0)

typedef struct {
  rbnode *node;
  cmp_t cmp;
} rb_path_entry_t;

static inline rbnode *rb_search(rbtree_t *rb, const rbnode *node) {
  rbnode *ret = rb->root;
  while (ret) {
    cmp_t cmp = comparator(node->start, ret->start);
    switch (cmp) {
    case _CMP_EQUAL:
      return ret;
    case _CMP_LESS:
      ret = rb_node_get_left(ret);
      break;
    case _CMP_GREATER:
      ret = rb_node_get_right(ret);
      break;
    default:
      __UNREACHABLE;
      break;
    }
  }
  return ret;
}

static void rb_insert(rbtree_t *rb, rbnode *node) {
  rb_path_entry_t path[RB_MAX_DEPTH];
  rb_path_entry_t *pathp;
  // rb_node_init(node);

  /* Traverse through red-black tree node and find the search target node. */
  path->node = rb->root;
  for (pathp = path; pathp->node; pathp++) {
    cmp_t cmp = pathp->cmp = comparator(node->start, pathp->node->start);
    switch (cmp) {
    case _CMP_LESS:
      pathp[1].node = rb_node_get_left(pathp->node);
      break;
    case _CMP_GREATER:
      pathp[1].node = rb_node_get_right(pathp->node);
      break;
    default:
      /* ignore duplicate key */
      __UNREACHABLE;
      break;
    }
  }
  pathp->node = node;

  assert(!rb_node_get_left(node));
  assert(!rb_node_get_right(node));

  /* Go from target node back to root node and fix color accordingly */
  for (pathp--; (uintptr_t)pathp >= (uintptr_t)path; pathp--) {
    rbnode *cnode = pathp->node;
    if (pathp->cmp == _CMP_LESS) {
      rbnode *left = pathp[1].node;
      rb_node_set_left(cnode, left);
      if (rb_node_get_color(left) == RB_BLACK) {
        rb->is_unstable = false;
        return;
      }
      rbnode *leftleft = rb_node_get_left(left);
      if (leftleft && (rb_node_get_color(leftleft) == RB_RED)) {
        /* fix up 4-node */
        rbnode *tnode;
        rb_node_set_black(leftleft);
        rb_node_rotate_right(cnode, tnode);
        cnode = tnode;
      }
    } else {
      rbnode *right = pathp[1].node;
      rb_node_set_right(cnode, right);
      if (rb_node_get_color(right) == RB_BLACK) {
        rb->is_unstable = false;
        return;
      }
      rbnode *left = rb_node_get_left(cnode);
      if (left && (rb_node_get_color(left) == RB_RED)) {
        /* split 4-node */
        rb_node_set_black(left);
        rb_node_set_black(right);
        rb_node_set_red(cnode);
      } else {
        /* lean left */
        rbnode *tnode;
        color_t tcolor = rb_node_get_color(cnode);
        rb_node_rotate_left(cnode, tnode);
        rb_node_set_color(tnode, tcolor);
        rb_node_set_red(cnode);
        cnode = tnode;
      }
    }
    pathp->node = cnode;
  }

  /* set root, and make it black */
  rb->root = path->node;
  rb_node_set_black(rb->root);
  rb->is_unstable = false;
}

static void rb_remove(rbtree_t *rb, rbnode *node) {
  rb_path_entry_t path[RB_MAX_DEPTH];
  rb_path_entry_t *pathp = NULL, *nodep = NULL;

  /* Traverse through red-black tree node and find the search target node. */
  path->node = rb->root;
  pathp = path;
  while (pathp->node) {
    cmp_t cmp = pathp->cmp = comparator(node->start, pathp->node->start);
    if (cmp == _CMP_LESS) {
      pathp[1].node = rb_node_get_left(pathp->node);
    } else {
      pathp[1].node = rb_node_get_right(pathp->node);
      if (cmp == _CMP_EQUAL) {
        /* find node's successor, in preparation for swap */
        pathp->cmp = _CMP_GREATER;
        nodep = pathp;
        for (pathp++; pathp->node; pathp++) {
          pathp->cmp = _CMP_LESS;
          pathp[1].node = rb_node_get_left(pathp->node);
        }
        break;
      }
    }
    pathp++;
  }
  assert(nodep && nodep->node == node);

  pathp--;
  if (pathp->node != node) {
    /* swap node with its successor */
    color_t tcolor = rb_node_get_color(pathp->node);
    rb_node_set_color(pathp->node, rb_node_get_color(node));
    rb_node_set_left(pathp->node, rb_node_get_left(node));

    /* If the node's successor is its right child, the following code may
     * behave incorrectly for the right child pointer.
     * However, it is not a problem as the pointer will be correctly set
     * when the successor is pruned.
     */
    rb_node_set_right(pathp->node, rb_node_get_right(node));
    rb_node_set_color(node, tcolor);

    /* The child pointers of the pruned leaf node are never accessed again,
     * so there is no need to set them to NULL.
     */
    nodep->node = pathp->node;
    pathp->node = node;
    if (nodep == path) {
      rb->root = nodep->node;
    } else {
      if (nodep[-1].cmp == _CMP_LESS)
        rb_node_set_left(nodep[-1].node, nodep->node);
      else
        rb_node_set_right(nodep[-1].node, nodep->node);
    }
  } else {
    rbnode *left = rb_node_get_left(node);
    if (left) {
      /* node has no successor, but it has a left child.
       * Splice node out, without losing the left child.
       */
      assert(rb_node_get_color(node) == RB_BLACK);
      assert(rb_node_get_color(left) == RB_RED);
      rb_node_set_black(left);
      if (pathp == path) {
        /* the subtree rooted at the node's left child has not
         * changed, and it is now the root.
         */
        rb->root = left;
      } else {
        if (pathp[-1].cmp == _CMP_LESS)
          rb_node_set_left(pathp[-1].node, left);
        else
          rb_node_set_right(pathp[-1].node, left);
      }
      rb->is_unstable = false;
      return;
    }
    if (pathp == path) {
      /* the tree only contained one node */
      rb->root = NULL;
      rb->is_unstable = false;
      return;
    }
  }

  /* The invariant has been established that the node has no right child
   * (morally speaking; the right child was not explicitly nulled out if
   * swapped with its successor). Furthermore, the only nodes with
   * out-of-date summaries exist in path[0], path[1], ..., pathp[-1].
   */
  if (rb_node_get_color(pathp->node) == RB_RED) {
    /* prune red node, which requires no fixup */
    assert(pathp[-1].cmp == _CMP_LESS);
    rb_node_set_left(pathp[-1].node, NULL);
    rb->is_unstable = false;
    return;
  }

  /* The node to be pruned is black, so unwind until balance is restored. */
  pathp->node = NULL;
  for (pathp--; (uintptr_t)pathp >= (uintptr_t)path; pathp--) {
    assert(pathp->cmp != _CMP_EQUAL);
    if (pathp->cmp == _CMP_LESS) {
      rb_node_set_left(pathp->node, pathp[1].node);
      if (rb_node_get_color(pathp->node) == RB_RED) {
        rbnode *right = rb_node_get_right(pathp->node);
        rbnode *rightleft = rb_node_get_left(right);
        rbnode *tnode;
        if (rightleft && (rb_node_get_color(rightleft) == RB_RED)) {
          /* In the following diagrams, ||, //, and \\
           * indicate the path to the removed node.
           *
           *      ||
           *    pathp(r)
           *  //        \
           * (b)        (b)
           *           /
           *          (r)
           */
          rb_node_set_black(pathp->node);
          rb_node_rotate_right(right, tnode);
          rb_node_set_right(pathp->node, tnode);
          rb_node_rotate_left(pathp->node, tnode);
        } else {
          /*      ||
           *    pathp(r)
           *  //        \
           * (b)        (b)
           *           /
           *          (b)
           */
          rb_node_rotate_left(pathp->node, tnode);
        }

        /* Balance restored, but rotation modified subtree root. */
        assert((uintptr_t)pathp > (uintptr_t)path);
        if (pathp[-1].cmp == _CMP_LESS)
          rb_node_set_left(pathp[-1].node, tnode);
        else
          rb_node_set_right(pathp[-1].node, tnode);
        return;
      } else {
        rbnode *right = rb_node_get_right(pathp->node);
        rbnode *rightleft = rb_node_get_left(right);
        if (rightleft && (rb_node_get_color(rightleft) == RB_RED)) {
          /*      ||
           *    pathp(b)
           *  //        \
           * (b)        (b)
           *           /
           *          (r)
           */
          rbnode *tnode;
          rb_node_set_black(rightleft);
          rb_node_rotate_right(right, tnode);
          rb_node_set_right(pathp->node, tnode);
          rb_node_rotate_left(pathp->node, tnode);
          /* Balance restored, but rotation modified subtree root,
           * which may actually be the tree root.
           */
          if (pathp == path) {
            /* set root */
            rb->root = tnode;
          } else {
            if (pathp[-1].cmp == _CMP_LESS)
              rb_node_set_left(pathp[-1].node, tnode);
            else
              rb_node_set_right(pathp[-1].node, tnode);
          }
          return;
        } else {
          /*      ||
           *    pathp(b)
           *  //        \
           * (b)        (b)
           *           /
           *          (b)
           */
          rbnode *tnode;
          rb_node_set_red(pathp->node);
          rb_node_rotate_left(pathp->node, tnode);
          pathp->node = tnode;
        }
      }
    } else {
      rb_node_set_right(pathp->node, pathp[1].node);
      rbnode *left = rb_node_get_left(pathp->node);
      if (rb_node_get_color(left) == RB_RED) {
        rbnode *tnode;
        rbnode *leftright = rb_node_get_right(left);
        rbnode *leftrightleft = rb_node_get_left(leftright);
        if (leftrightleft && (rb_node_get_color(leftrightleft) == RB_RED)) {
          /*      ||
           *    pathp(b)
           *   /        \\
           * (r)        (b)
           *   \
           *   (b)
           *   /
           * (r)
           */
          rbnode *unode;
          rb_node_set_black(leftrightleft);
          rb_node_rotate_right(pathp->node, unode);
          rb_node_rotate_right(pathp->node, tnode);
          rb_node_set_right(unode, tnode);
          rb_node_rotate_left(unode, tnode);
        } else {
          /*      ||
           *    pathp(b)
           *   /        \\
           * (r)        (b)
           *   \
           *   (b)
           *   /
           * (b)
           */
          assert(leftright);
          rb_node_set_red(leftright);
          rb_node_rotate_right(pathp->node, tnode);
          rb_node_set_black(tnode);
        }

        /* Balance restored, but rotation modified subtree root, which
         * may actually be the tree root.
         */
        if (pathp == path) {
          /* set root */
          rb->root = tnode;
        } else {
          if (pathp[-1].cmp == _CMP_LESS)
            rb_node_set_left(pathp[-1].node, tnode);
          else
            rb_node_set_right(pathp[-1].node, tnode);
        }
        rb->is_unstable = false;
        return;
      } else if (rb_node_get_color(pathp->node) == RB_RED) {
        rbnode *leftleft = rb_node_get_left(left);
        if (leftleft && (rb_node_get_color(leftleft) == RB_RED)) {
          /*        ||
           *      pathp(r)
           *     /        \\
           *   (b)        (b)
           *   /
           * (r)
           */
          rbnode *tnode;
          rb_node_set_black(pathp->node);
          rb_node_set_red(left);
          rb_node_set_black(leftleft);
          rb_node_rotate_right(pathp->node, tnode);
          /* Balance restored, but rotation modified subtree root. */
          assert((uintptr_t)pathp > (uintptr_t)path);
          if (pathp[-1].cmp == _CMP_LESS)
            rb_node_set_left(pathp[-1].node, tnode);
          else
            rb_node_set_right(pathp[-1].node, tnode);
          rb->is_unstable = false;
          return;
        } else {
          /*        ||
           *      pathp(r)
           *     /        \\
           *   (b)        (b)
           *   /
           * (b)
           */
          rb_node_set_red(left);
          rb_node_set_black(pathp->node);
          /* balance restored */
          rb->is_unstable = false;
          return;
        }
      } else {
        rbnode *leftleft = rb_node_get_left(left);
        if (leftleft && (rb_node_get_color(leftleft) == RB_RED)) {
          /*               ||
           *             pathp(b)
           *            /        \\
           *          (b)        (b)
           *          /
           *        (r)
           */
          rbnode *tnode;
          rb_node_set_black(leftleft);
          rb_node_rotate_right(pathp->node, tnode);
          /* Balance restored, but rotation modified subtree root,
           * which may actually be the tree root.
           */
          if (pathp == path) {
            /* set root */
            rb->root = tnode;
          } else {
            if (pathp[-1].cmp == _CMP_LESS)
              rb_node_set_left(pathp[-1].node, tnode);
            else
              rb_node_set_right(pathp[-1].node, tnode);
          }
          rb->is_unstable = false;
          return;
        } else {
          /*               ||
           *             pathp(b)
           *            /        \\
           *          (b)        (b)
           *          /
           *        (b)
           */
          rb_node_set_red(left);
        }
      }
    }
  }

  /* set root */
  rb->root = path->node;
  assert(rb_node_get_color(rb->root) == RB_BLACK);
  rb->is_unstable = false;
}

static void rbtree_print(const rbtree_t *tree);

rbtree_t *rbtree_init(const char *name) {
  rbtree_t *tree = rbtreeMalloc(sizeof(rbtree_t));
  tree->root = NULL;
  tree->is_unstable = false;
  tree->name = name ? name : "(rbtree)";
  return tree;
}

static inline void delete_rbnode(rbnode *root) {
  if (!root)
    return;
  delete_rbnode(rb_node_get_left(root));  // root->left);
  delete_rbnode(rb_node_get_right(root)); // root->right);//replace with
  rbtreeFree(root);
}

void rbtree_delete(rbtree_t *tree) {
  delete_rbnode(tree->root);
  rbtreeFree(tree);
}

static int add_range(rbtree_t *tree, uintptr_t start, uintptr_t end,
                     uint64_t data) {
  // printf("Adding %lx-%lx:%hhx next to %p\n", start, end, data, prev);
  rbnode *node = rbtreeMalloc(sizeof(*node));
  if (!node)
    return -1;
  rb_node_init(node);
  node->start = start;
  node->end = end;
  node->data = data;

  if (tree->is_unstable) {
    printf_log(
        LOG_NONE,
        "Warning, unstable Red-Black tree; trying to add a node anyways\n");
  }
  tree->is_unstable = true;
  rb_insert(tree, node);
  tree->is_unstable = false;
  return 0;
}

static rbnode *find_addr(rbtree_t *tree, uintptr_t addr) {
  rbnode *node = tree->root;
  while (node) {
    if ((node->start <= addr) && (node->end > addr))
      return node;
    if (addr < node->start)
      node = rb_node_get_left(node);
    else
      node = rb_node_get_right(node);
  }
  return NULL;
}

// node must be a valid node in the tree
static int remove_node(rbtree_t *tree, rbnode *node) { // succ 0 fail
  // printf("Removing %p\n", node); rbtree_print(tree); fflush(stdout);
  if (tree->is_unstable) {
    printf_log(
        LOG_NONE,
        "Warning, unstable Red-Black tree; trying to add a node anyways\n");
  }
  tree->is_unstable = true;
  rb_remove(tree, node); // TODO: Check the return value
  tree->is_unstable = false;
}

static rbnode *succ_node(rbtree_t *rb, rbnode *node) {
  if (!node)
    return NULL;
  if (rb_node_get_right(node)) {
    node = rb_node_get_right(node);
    while (rb_node_get_left(node))
      node = rb_node_get_left(node);
    return node;
  }
  // right sub-tree didn't exit
  rb_path_entry_t path[RB_MAX_DEPTH];
  rb_path_entry_t *pathp;
  /* Traverse through red-black tree node and find the search target node. */
  path->node = rb->root;
  for (pathp = path; pathp->node; pathp++) {
    cmp_t cmp = pathp->cmp = comparator(node->start, pathp->node->start);
    switch (cmp) {
    case _CMP_LESS:
      pathp[1].node = rb_node_get_left(pathp->node);
      break;
    case _CMP_GREATER:
      pathp[1].node = rb_node_get_right(pathp->node);
      break;
    case _CMP_EQUAL:

    default:
      __UNREACHABLE;
      break;
    }
  }
  pathp->node = node;
  assert(!rb_node_get_right(node));

  /* Go from target node back to root node and fix color accordingly */
  for (pathp--; (uintptr_t)pathp >= (uintptr_t)path; pathp--) {
    if (pathp->cmp == _CMP_GREATER) {
      return pathp[1].node;
    }
  }
}

uint32_t rb_get(rbtree_t *tree, uintptr_t addr) {
  rbnode *node = find_addr(tree, addr);
  if (node)
    return node->data;
  else
    return 0;
}

uint64_t rb_get_64(rbtree_t *tree, uintptr_t addr) {
  rbnode *node = find_addr(tree, addr);
  if (node)
    return node->data;
  else
    return 0;
}

int rb_get_end(rbtree_t *tree, uintptr_t addr, uint32_t *val, uintptr_t *end) {
  rbnode *node = tree->root, *next = NULL;
  while (node) {
    if ((node->start <= addr) && (node->end > addr)) {
      *val = node->data;
      *end = node->end;
      return 1;
    }
    if (node->end <= addr) {
      node = rb_node_get_right(node);
    } else {
      next = node;
      node = rb_node_get_left(node);
    }
  }
  *val = 0;
  if (next) {
    *end = next->start;
  } else {
    *end = (uintptr_t)-1;
  }
  return 0;
}

int rb_get_end_64(rbtree_t *tree, uintptr_t addr, uint64_t *val,
                  uintptr_t *end) {
  rbnode *node = tree->root, *next = NULL;
  while (node) {
    if ((node->start <= addr) && (node->end > addr)) {
      *val = node->data;
      *end = node->end;
      return 1;
    }
    if (node->end <= addr) {
      node = rb_node_get_right(node);
    } else {
      next = node;
      node = rb_node_get_left(node);
    }
  }
  *val = 0;
  if (next) {
    *end = next->start;
  } else {
    *end = (uintptr_t)-1;
  }
  return 0;
}

int rb_set_64(rbtree_t *tree, uintptr_t start, uintptr_t end, uint64_t data) {
  // printf("rb_set( "); rbtree_print(tree); printf(" , 0x%lx, 0x%lx, %hhu);\n",
  // start, end, data); fflush(stdout);
  dynarec_log(LOG_DEBUG, "set %s: 0x%lx, 0x%lx, 0x%x\n", tree->name, start, end,
              data);
  if (!tree->root) {
    return add_range(tree, start, end, data);
  }

  rbnode *node = tree->root, *prev = NULL, *last = NULL;
  while (node) {
    if (node->start < start) {
      prev = node;
      node = rb_node_get_right(node);
    } else if (node->start == start) {
      if (rb_node_get_left(node)) {
        prev = rb_node_get_left(node);
        while (rb_node_get_right(prev))
          prev = rb_node_get_right(prev);
      }
      if (rb_node_get_right(node)) {
        last = rb_node_get_right(node);
        while (last->left)
          last = last->left;
      }
      break;
    } else {
      last = node;
      node = rb_node_get_left(node);
    }
  }

  // prev is the largest node starting strictly before start, or NULL if there
  // is none node is the node starting exactly at start, or NULL if there is
  // none last is the smallest node starting strictly after start, or NULL if
  // there is none Note that prev may contain start

  if (prev && (prev->end >= start) && (prev->data == data)) {
    // Merge with prev
    if (end <= prev->end)
      return 0; // Nothing to do!

    if (node && (node->end > end)) {
      node->start = end;
      prev->end = end;
      return 0;
    } else if (node && (node->end == end)) {
      remove_node(tree, node);
      prev->end = end;
      return 0;
    } else if (node) {
      remove_node(tree, node);
    }
    while (last && (last->start < end) && (last->end <= end)) {
      // Remove the entire node
      node = last;
      last = succ_node(last);
      remove_node(tree, node);
    }
    if (last && (last->start <= end) && (last->data == data)) {
      // Merge node and last
      prev->end = last->end;
      remove_node(tree, last);
      return 0;
    }
    if (last && (last->start < end))
      last->start = end;
    prev->end = end;
    return 0;
  } else if (prev && (prev->end > start)) {
    if (prev->end > end) {
      // Split in three
      // Note that here, succ(prev) = last and node = NULL
      int ret;
      ret = add_range_next_to(tree, rb_node_get_right(prev) ? last : prev, end,
                              prev->end, prev->data);
      ret = ret ? ret
                : add_range_next_to(
                      tree, rb_node_get_right(prev) ? succ_node(prev) : prev,
                      start, end, data);
      prev->end = start;
      return ret;
    }
    // Cut prev and continue
    prev->end = start;
  }

  if (node) {
    // Change node
    if (node->end >= end) {
      if (node->data == data)
        return 0; // Nothing to do!
      // Cut node
      if (node->end > end) {
        int ret = add_range_next_to(tree, rb_node_get_right(node) ? last : node,
                                    end, node->end, node->data);
        node->end = end;
        node->data = data;
        return ret;
      }
      // Fallthrough
    }

    // Overwrite and extend node
    while (last && (last->start < end) && (last->end <= end)) {
      // Remove the entire node
      prev = last;
      last = succ_node(last);
      remove_node(tree, prev);
    }
    if (last && (last->start <= end) && (last->data == data)) {
      // Merge node and last
      remove_node(tree, node);
      last->start = start;
      return 0;
    }
    if (last && (last->start < end))
      last->start = end;
    if (node->end < end)
      node->end = end;
    node->data = data;
    return 0;
  }

  while (last && (last->start < end) && (last->end <= end)) {
    // Remove the entire node
    node = last;
    last = succ_node(last);
    remove_node(tree, node);
  }
  if (!last) {
    // Add a new node next to prev, the largest node of the tree
    // It exists since the tree is nonempty
    return add_range_next_to(tree, prev, start, end, data);
  }
  if ((last->start <= end) && (last->data == data)) {
    // Extend
    last->start = start;
    return 0;
  } else if (last->start < end) {
    // Cut
    last->start = end;
  }
  // Probably 'last->left ? prev : last' is enough
  return add_range_next_to(tree, last->left ? pred_node(last) : last, start,
                           end, data);
}

int rb_set(rbtree_t *tree, uintptr_t start, uintptr_t end, uint32_t data) {
  return rb_set_64(tree, start, end, data);
}

int rb_unset(rbtree_t *tree, uintptr_t start, uintptr_t end) {
  // printf("rb_unset( "); rbtree_print(tree); printf(" , 0x%lx, 0x%lx);\n",
  // start, end); fflush(stdout);
  dynarec_log(LOG_DEBUG, "unset: %s 0x%lx, 0x%lx);\n", tree->name, start, end);
  if (!tree->root)
    return 0;

  rbnode *node = tree->root, *prev = NULL, *next = NULL;
  while (node) {
    if (node->start < start) {
      prev = node;
      node = rb_node_get_right(node);
    } else if (node->start == start) {
      if (rb_node_get_left(node)) {
        prev = rb_node_get_left(node);
        while (rb_node_get_right(prev))
          prev = rb_node_get_right(prev);
      }
      if (rb_node_get_right(node)) {
        next = rb_node_get_right(node);
        while (next->left)
          next = next->left;
      }
      break;
    } else {
      next = node;
      node = rb_node_get_left(node);
    }
  }

  if (node) {
    if (node->end > end) {
      node->start = end;
      return 0;
    } else if (node->end == end) {
      remove_node(tree, node);
      return 0;
    } else {
      remove_node(tree, node);
    }
  } else if (prev && (prev->end > start)) {
    if (prev->end > end) {
      // Split prev
      int ret = add_range_next_to(tree, rb_node_get_right(prev) ? next : prev,
                                  end, prev->end, prev->data);
      prev->end = start;
      return ret;
    } else if (prev->end == end) {
      prev->end = start;
      return 0;
    } // else fallthrough
  }
  while (next && (next->start < end) && (next->end <= end)) {
    // Remove the entire node
    node = next;
    next = succ_node(next);
    remove_node(tree, node);
  }
  if (next && (next->start < end)) {
    // next->end > end: cut the node
    next->start = end;
  }
  return 0;
}

uintptr_t rb_get_righter(rbtree_t *tree) {
  dynarec_log(LOG_DEBUG, "rb_get_righter(%s);\n", tree->name);
  if (!tree->root)
    return 0;

  rbnode *node = tree->root;
  while (node) {
    if (!rb_node_get_right(node))
      return node->start;
    node = rb_node_get_right(node);
  }
  return 0;
}

uintptr_t rb_get_lefter(rbtree_t *tree) {
  dynarec_log(LOG_DEBUG, "rb_get_lefter(%s);\n", tree->name);
  if (!tree->root)
    return 0;

  rbnode *node = tree->root;
  while (node) {
    if (!rb_node_get_left(node))
      return node->start;
    node = rb_node_get_left(node);
  }
  return 0;
}

#include <stdio.h>
static void print_rbnode(const rbnode *node, unsigned depth, uintptr_t minstart,
                         uintptr_t maxend, unsigned *bdepth) {
  if (!node) {
    if (!*bdepth || *bdepth == depth + 1) {
      *bdepth = depth + 1;
      printf("[%u]", depth);
    } else
      printf("<invalid black depth %u>", depth);
    return;
  }
  if (node->start < minstart) {
    printf("<invalid start>");
    return;
  }
  if (node->end > maxend) {
    printf("<invalid end>");
    return;
  }
  printf("(");

  if (rb_node_get_left(node) && !(rb_node_get_left(node)->meta & IS_LEFT)) {
    printf("<invalid meta>");
  } else if (rb_node_get_left(node) &&
             (rb_node_get_left(node)->parent != node)) {
    printf("<invalid parent %p instead of %p>", rb_node_get_left(node)->parent,
           node);
  } else if (rb_node_get_left(node) && !(node->meta & IS_BLACK) &&
             !(rb_node_get_left(node)->meta & IS_BLACK)) {
    printf("<invalid red-red node> ");
    print_rbnode(rb_node_get_left(node),
                 depth + ((node->meta & IS_BLACK) ? 1 : 0), minstart,
                 node->start, bdepth);
  } else {
    print_rbnode(rb_node_get_left(node),
                 depth + ((node->meta & IS_BLACK) ? 1 : 0), minstart,
                 node->start, bdepth);
  }
  printf(", (%c/%p) %lx-%lx: %llu, ", node->meta & IS_BLACK ? 'B' : 'R', node,
         node->start, node->end, node->data);

  if (rb_node_get_right(node) && (rb_node_get_right(node)->meta & IS_LEFT)) {
    printf("<invalid meta>");
  } else if (rb_node_get_right(node) &&
             (rb_node_get_right(node)->parent != node)) {
    printf("<invalid parent %p instead of %p>", rb_node_get_right(node)->parent,
           node);
  } else if (rb_node_get_right(node) && !(node->meta & IS_BLACK) &&
             !(rb_node_get_right(node)->meta & IS_BLACK)) {
    printf("<invalid red-red node> ");
    print_rbnode(rb_node_get_right(node),
                 depth + ((node->meta & IS_BLACK) ? 1 : 0), node->end, maxend,
                 bdepth);
  } else {
    print_rbnode(rb_node_get_right(node),
                 depth + ((node->meta & IS_BLACK) ? 1 : 0), node->end, maxend,
                 bdepth);
  }
  printf(")");
}

static void rbtree_print(const rbtree_t *tree) {
  if (!tree) {
    printf("<NULL>\n");
    return;
  }
  /*if (tree->root && tree->root->parent) {
      printf("Root has parent\n");
      return;
  }
  if (tree->root && !(tree->root->meta & IS_BLACK)) {
      printf("Root is red\n");
      return;
  }*/
  unsigned bdepth = 0;
  print_rbnode(tree->root, 0, 0, (uintptr_t)-1, &bdepth);
  printf("\n");
}

#ifdef RBTREE_TEST
int main() {
  rbtree_t *tree = rbtree_init("test");
  rbtree_print(tree);
  fflush(stdout);
  /*int ret;
  ret = rb_set(tree, 0x43, 0x44, 0x01);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout);
  ret = rb_set(tree, 0x42, 0x43, 0x01);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout);
  ret = rb_set(tree, 0x41, 0x42, 0x01);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout);
  ret = rb_set(tree, 0x40, 0x41, 0x01);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout);
  ret = rb_set(tree, 0x20, 0x40, 0x03);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout);
  ret = rb_set(tree, 0x10, 0x20, 0x01);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout);

  uint32_t val = rb_get(tree, 0x33);
  printf("0x33 has attribute %hhu\n", val); fflush(stdout);*/
  /* rbnode *node = find_addr(tree, 0x33);
  printf("0x33 is at %p: ", node); print_rbnode(node, 0); printf("\n");
  fflush(stdout); ret = remove_node(tree, node); printf("%d; ", ret);
  rbtree_print(tree); fflush(stdout); node = find_addr(tree, 0x20); printf("0x20
  is at %p\n", node); node = find_addr(tree, 0x1F); printf("0x1F is at %p: ",
  node); print_rbnode(node, 0); printf("\n"); fflush(stdout); ret =
  remove_node(tree, node); printf("%d; ", ret); rbtree_print(tree);
  fflush(stdout); */
  /* ret = rb_set(tree, 0x15, 0x42, 0x00);
  printf("%d; ", ret); rbtree_print(tree); fflush(stdout); */
  /*rb_unset(tree, 0x15, 0x42);
  rbtree_print(tree); fflush(stdout);*/

  // tree->root = node27; rbtree_print(tree); fflush(stdout);
  // rb_set(tree, 2, 3, 1); rbtree_print(tree); fflush(stdout);
  // add_range_next_to(tree, node24, 0x0E7000, 0x0E8000, 69);
  // rbtree_print(tree); fflush(stdout); rbtree_print(tree); fflush(stdout);
  // uint32_t val = rb_get(tree, 0x11003000);
  // printf("0x11003000 has attribute %hhu\n", val); fflush(stdout);
  // remove_node(tree, node0); rbtree_print(tree); fflush(stdout);
  // add_range_next_to(tree, node1, 0x0E7000, 0x0E8000, 69); rbtree_print(tree);
  // fflush(stdout);
  rb_set(tree, 0x130000, 0x140000, 7);
  rbtree_print(tree);
  fflush(stdout);
  rb_set(tree, 0x141000, 0x142000, 135);
  rbtree_print(tree);
  fflush(stdout);
  rb_set(tree, 0x140000, 0x141000, 135);
  rbtree_print(tree);
  fflush(stdout);
  rb_set(tree, 0x140000, 0x147000, 7);
  rbtree_print(tree);
  fflush(stdout);
  rb_set(tree, 0x140000, 0x141000, 135);
  rbtree_print(tree);
  fflush(stdout);
  uint32_t val = rb_get(tree, 0x141994);
  printf("0x141994 has attribute %hhu\n", val);
  fflush(stdout);
  rbtree_delete(tree);
}
#endif

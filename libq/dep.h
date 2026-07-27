/*
 * Copyright 2005-2026 Gentoo Foundation
 * Distributed under the terms of the GNU General Public License v2
 */

#ifndef DEP_H
#define DEP_H 1

#include <unistd.h>

#include "array.h"
#include "atom.h"
#include "colors.h"
#include "set.h"
#include "tree.h"

typedef struct dep_node_ dep_node_t;
typedef enum dep_status_ dep_status_t;

/* node kinds, exposed so callers can traverse a parsed dep tree:
 *   DEP_ATOM  a package atom      DEP_ANY  || ( ... )
 *   DEP_ALL   ( ... ) all-of      DEP_USE  [!]use? ( ... )
 *   DEP_NOT   negation            others are internal parse states */
#define DEP_TYPES(X) \
  X(NULL) X(ATOM) X(USE) X(ANY) X(ALL) X(NOT) X(HUH) X(POPEN) X(PCLOSE) X(WORD)
#define DEP_TYPE_ENUM(E)  DEP_##E,
typedef enum dep_type_ {
  DEP_TYPES(DEP_TYPE_ENUM)
  DEP_MAX_TYPES
} dep_type_t;
#undef DEP_TYPE_ENUM

enum dep_status_ {
  DEP_OK = 1,
  DEP_FAIL,
  DEP_MASK,
  DEP_KEYWORD,
  DEP_NEWBLOCKER,
};

/* prototypes */
dep_node_t   *dep_grow_tree(const char *depend);
void          dep_print_tree(FILE *fp, const dep_node_t *root, size_t space,
                             array *m, const char *c, int verbose);
dep_status_t  dep_resolve_tree(dep_node_t *root, tree_ctx *t,
                               set_t *use, hash_t *blockers,
                               set_t *keywords);
void          dep_prune_use(dep_node_t *root, set_t *use);
array        *dep_flatten_tree(dep_node_t *root);
void          dep_burn_tree(dep_node_t *root);

/* 2026 API boring (but predictable) names */
#define       dep_new(D)              dep_grow_tree(D)
dep_node_t   *dep_new_atom(atom_ctx *atom);
#define       dep_print(F,D,S,M,C,V)  dep_print_tree(F,D,S,M,C,V)
#define       dep_resolve(D,T,U,B,K)  dep_resolve_tree(D,T,U,B,K)
#define       dep_prune(D,U)          dep_prune_use(D,U)
#define       dep_flatten(D)          dep_flatten_tree(D);
#define       dep_free(D)             dep_burn_tree(D)
array        *dep_nodes(dep_node_t *node);
tree_pkg_ctx *dep_node_pkg(dep_node_t *node);
tree_pkg_ctx *dep_node_ipkg(dep_node_t *node);
atom_ctx     *dep_node_atom(dep_node_t *node);
atom_ctx     *dep_node_mask(dep_node_t *node);
atom_ctx     *dep_node_fail_input(dep_node_t *node);
dep_type_t    dep_node_type(const dep_node_t *node);
array        *dep_node_children(const dep_node_t *node);

#endif

/* vim: set ts=2 sw=2 expandtab cino+=\:0 foldmethod=marker: */

# clj-wbtree

Weight Balanced Functional Binary Tree (Hirai-Yamamoto Tree)

## Overview


This is an implementation of a weight-balanced binary tree data
 structure based on the following references:

-  Adams (1992)
    'Implementing Sets Efficiently in a Functional Language'
    Technical Report CSTR 92-10, University of Southampton.

-  Hirai and Yamamoto (2011)
    'Balancing Weight-Balanced Trees'
    Journal of Functional Programming / 21 (3):
    Pages 287-307

-  Oleg Kiselyov
    'Towards the best collection API, A design of the overall optimal
    collection traversal interface'
    <http://pobox.com/~oleg/ftp/papers/LL3-collections-enumerators.txt>

-  Nievergelt and Reingold (1972)
    'Binary Search Trees of Bounded Balance'
    STOC '72 Proceedings
    4th Annual ACM symposium on Theory of Computing
    Pages 137-142 

-  Driscoll, Sarnak, Sleator, and Tarjan (1989)
    'Making Data Structures Persistent'
    Journal of Computer and System Sciences Volume 38 Issue 1, February 1989
    18th Annual ACM Symposium on Theory of Computing
    Pages 86-124

-  MIT Scheme weight balanced tree as reimplemented by Yoichi Hirai
    and Kazuhiko Yamamoto using the revised non-variant algorithm recommended
    integer balance parameters from (Hirai/Yamomoto 2011).

## Features

Some unique features of a weight-balanced binary-tree as compared with
other binary tree algorithms:


- Less frequent rebalancing as compared to height-balanced
  implementations such as red-black or avl trees.

- Logarithmic rank/at-rank indexed element access.


This particular implementation also provides additional useful
qualities such as lazy traversal, partial enumeration, universal order,
and search for a given key in only d comparisons (where d is depth of
tree) rather than the traditional compare/low compare/high which takes
on average (* 1.5 (- d 1)) comparisons.  In addition, a comprehensive
functional binary tree api provides a rich collection of tools
for the creation of efficient higher-order data structures.


## Usage

### The Most Recent Release

With Leiningen:

```clj
[danlentz/clj-wbtree "0.1.2-SNAPSHOT"]
```

With Maven:

```xml
<dependency>
  <groupId>danlentz</groupId>
  <artifactId>clj-wbtree</artifactId>
  <version>0.1.2-SNAPSHOT</version>
</dependency>
```



## Examples

## License

Copyright © 2014 FIXME

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.

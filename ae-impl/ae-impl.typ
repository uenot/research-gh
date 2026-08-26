#import "toby.typ": scratch
#import "@preview/mannot:0.4.0": markhl
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/cetz:0.5.2": canvas, draw, tree

#set document(title: [
  Implementing Asynchronous Effects
])

// general formatting
#let grey(x) = markhl(x, color: gray)
#show smallcaps: set text(font: "Latin Modern Roman")

// math macros
#let angle(x) = $chevron.l #x chevron.r$
#let onerule(..args) = {
  let kwargs = args.named()
  if "name" in kwargs {
    kwargs.name = smallcaps(kwargs.name)
  }
  prooftree(rule(..kwargs, ..args.pos()))
}

// language macros
#let elet(x, m, n) = $sans("let") #x <- #m sans("in") #n$
#let eprom(op, x, m, p, n) = $
  sans("promise") (sans(#op) #x mapsto #m) sans("as") #p sans("in") #n$

#show: scratch

= Context-Based Semantics (broken)

Goals:
- remove explicit continuations where possible
- remove unnecessary operation bubbling

== Syntax

=== Term-Level

$
  "Values" V, W &::= x | () | lambda x.M | (V, W) | angle(V) \
  "Computations" M, N &::= sans("val") V | elet(x, M, N)
  | V #h(4pt) W | sans("fst") V | sans("snd") V \
& | arrow.t sans("op")(V) | sans("await")(V)
  | eprom("op", x, M, p, N) \
& | grey(arrow.b sans("op")(V, M)) \
  "Operation Contexts" Theta &::= [dot] | eprom("op", x, M, p, cal(E))
 | grey(arrow.b sans("op")(V, cal(E))) \
  "Evalutation Contexts" cal(E) &::= Theta | elet(x, cal(E), N) \
  "Processes" P, Q &::= sans("run") M | P || Q \
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

== Semantics

=== Sequential Fragment

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $[M] arrow.squiggly [N]$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, Theta[sans("val") V], M) &arrow.squiggly Theta[M[V\/x]] & #smallcaps("E-Val")\
  (lambda x.M) #h(4pt) V &arrow.squiggly M[V\/x] & #smallcaps("E-App")\
  sans("fst") (V, W) &arrow.squiggly sans("val") V & #smallcaps("E-Fst")\
  sans("snd") (V, W) &arrow.squiggly sans("val") W & #smallcaps("E-Snd")\
  sans("await") angle(V) &arrow.squiggly sans("val") & #smallcaps("E-Await")\
  arrow.b sans("op")(V, cal(E)[eprom("op", x, M, p, N)])
  &arrow.squiggly
  elet(p, M[V\/x], arrow.b sans("op")(V, cal(E)[N]))
  & #h(1em) #smallcaps("E-Prom")\
  ("where" sans("op") in.not cal(E))
$

$sans("op") in.not cal(E)$ means that no handlers _or_ interrupts
for $sans("op")$ appear in $cal(E)$. A formal definition can be given
inductively, with key rules as follows:

#align(center, rule-set(
  onerule(
    $sans("op") in arrow.b sans("op")(V, cal(E))$
  ),
  onerule(
    $sans("op") in eprom("op", x, M, p, cal(E))$
  )
))

=== Parallel Fragment

Structural congruence $(equiv)$ is given merely by associativity
and commutativity of $||$.

We have the following (fairly) standard rules on processes:

#align(center, rule-set(
  onerule(
    name: "P-Run",
    $M arrow.squiggly N$,
    $sans("run") M || P arrow.squiggly sans("run") N || P$
  ),
  onerule(
    name: "P-Cong",
    $P equiv P'$,
    $P' arrow.squiggly Q'$,
    $Q' equiv Q$,
    $P arrow.squiggly Q$
  )
))

and one rule, #smallcaps("P-Broad"), for broadcast:

$
  sans("run") cal(E)[arrow.t sans("op")(V)]
  || sans("run") M_1 || ... || sans("run") M_n\
  arrow.squiggly
  sans("run") cal(E)[sans("val") ()]
  || sans("run") arrow.b sans("op")(V, M_1) || ...
  || sans("run") arrow.b sans("op")(V, M_n)
$

Note that reduction ought _not_ occur under parallel composition, i.e.
we do _not_ have the following rule:

#align(center, rule-set(
  onerule(
    name: "P-Par*",
    $P arrow.squiggly P'$,
    $P || Q arrow.squiggly P' || Q$
  ),
))

This is because we want to ensure broadcast is _global_.
If we admitted the above, we would be admitting a _local_ broadcast.

We can evaluate any particular process in the "tree" by moving
it to the leftmost position via structural congruence, as illustrated below:

#align(center, grid(
  rows: 3,
  align: horizon,
  columns: 3,
  gutter: 1em,
  canvas({
    import draw: *
    tree.tree(
      ($||$,
        $sans("run") M_1$,
        ($||$,
          $sans("run") M_2$, $sans("run") M_3$
        ),
      ),
      draw-node: (node, ..) => {
        content((), pad(node.content, .3em))
      },
    )
  }),
  $arrow.r.triple$,
  canvas({
    import draw: *
    tree.tree(
      ($||$,
        $sans("run") M_3$,
        ($||$,
          $sans("run") M_1$, $sans("run") M_2$
        ),
      ),
      draw-node: (node, ..) => {
        content((), pad(node.content, .3em))
      },
    )
  }),
  [], [], rotate(90deg, reflow: true)[$arrow.long.squiggly$],
    canvas({
    import draw: *
    tree.tree(
      ($||$,
        $sans("run") M_1$,
        ($||$,
          $sans("run") M_2$, $sans("run") M_3 '$
        ),
      ),
      draw-node: (node, ..) => {
        content((), pad(node.content, .3em))
      },
    )
  }),
  $arrow.l.triple$,
  canvas({
    import draw: *
    tree.tree(
      ($||$,
        $sans("run") M_3 '$,
        ($||$,
          $sans("run") M_1$, $sans("run") M_2$
        ),
      ),
      draw-node: (node, ..) => {
        content((), pad(node.content, .3em))
      },
    )
  }),
))

To be precise about broadcast, we might instead define the following rule:
$
  sans("run") cal(E)[arrow.t sans("op")(V)] || P
  arrow.squiggly
  sans("run") cal(E)[sans("val") ()] || arrow.b sans("op")(V, P)
  #h(1em) #smallcaps("P-Broad*")
$
where $arrow.b sans("op")(V, P)$ is defined structurally on processes
as follows:
$
  arrow.b sans("op")(V, sans("run") M)
  &eq.delta sans("run") arrow.b sans("op")(V, M) \
  arrow.b sans("op")(V, P || Q)
  &eq.delta arrow.b sans("op")(V, P) || arrow.b sans("op")(V, Q)
$

(If we treat the equalities above as rewrite rules, this definition implements
the same "bubbling-down" behavior of the original paper.)

== Examples

*Non-Confluence.*

Example 1:
$
  &arrow.b sans("op")(V, eprom("op", x,
    eprom("op'", y, M, q, sans("await") q),
  p, N)) \
  arrow.squiggly&
  arrow.b sans("op")(V, eprom("op", x,
    eprom("op'", y, M, q, sans("await") q),
  p, N')) \
  arrow.squiggly&
  elet(p, (eprom("op'", y, M, q, sans("await") q)),
  arrow.b sans("op")(V, N')) \
$
and
$
  &arrow.b sans("op")(V, eprom("op", x,
    eprom("op'", y, M, q, sans("await") q),
  p, N)) \
  arrow.squiggly&
  elet(p, (eprom("op'", y, M, q, sans("await") q)),
  arrow.b sans("op")(V, N)) \
$

= Sequential Essence

Signals and the parallel fragment are, in a certain sense, _inessential_
to asynchronous effects. The interesting bit (in my opinion) is the
interaction between _interrupts_ and their _handlers_.
Thus, for the moment, we remove the "noise" of the other constructs
and focus only on the essentials.

== Syntax

$
  "Values" V, W &::= x | () | lambda x.M | angle(V) \
  "Computations" M, N &::= sans("val") V | elet(x, M, N)
  | V #h(4pt) W
  | sans("await")(V) \
& | eprom("op", x, M, p, N)
  | grey(arrow.b sans("op")(V, M)) \
  "Evalutation Contexts" cal(E) &::= [.] | elet(x, cal(E), N)
  | eprom("op", x, M, p, cal(E))\
& | grey(arrow.b sans("op")(V, cal(E))) \
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

== Semantics

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $[M] arrow.squiggly [N]$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, sans("val") V, M) &arrow.squiggly M[V\/x] & #smallcaps("E-Val")\
  (lambda x.M) #h(4pt) V &arrow.squiggly M[V\/x] & #smallcaps("E-App")\
  sans("await") angle(V) &arrow.squiggly sans("val") V & #smallcaps("E-Await")\
  arrow.b sans("op")(V, sans("val") W)
  &arrow.squiggly
  sans("val") W
  & #smallcaps("E-Done")\
  arrow.b sans("op")(V, cal(E)[eprom("op", x, M, p, N)])
  &arrow.squiggly
  elet(p, M[V\/x], arrow.b sans("op")(V, cal(E)[N]))
  & #h(1em) #smallcaps("E-Prom")\
  ("where" sans("op") in.not cal(E)) \
$

== Comparison with Synchronous Effects

As a point of comparison, consider the following restricted language
of synchronous effect handlers.
We impose a number of significant simplifications:
- each handler may only handle one operation,
- handlers have no return clauses (or they all have the trivial return clause),
- handlers have no first-class access to the continuation
  (instead, the continuation is tail-resumptive and implicit).

=== Syntax

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= sans("val") V | elet(x, M, N)
  | V #h(4pt) W \
& | sans("op")(V)
  | sans("with") (sans("op") x mapsto M) sans("handle") N \
  "Evalutation Contexts" cal(E) &::= [.] | elet(x, cal(E), N)
  | sans("with") (sans("op") x mapsto M) sans("handle") cal(E) \
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

=== Semantics

These rules are shared between both languages:

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $[M] arrow.squiggly [N]$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, sans("val") V, M) &arrow.squiggly M[V\/x] & #smallcaps("E-Val")\
  (lambda x.M) #h(4pt) V &arrow.squiggly M[V\/x] & thick #smallcaps("E-App")\
$

Returning in both languages is analogous:

$sans("with") (sans("op") x mapsto M) sans("handle val") V
arrow.squiggly sans("val") V$

vs.

$arrow.b sans("op")(V, sans("val") W)
arrow.squiggly sans("val") W$

As is handling:

$sans("with") (sans("op") x mapsto M) sans("handle") cal(E)[sans("op")(V)]
arrow.squiggly elet(y, M[V\/x],
(sans("with") (sans("op") x mapsto M) sans("handle") cal(E)[sans("val") y]))$

(where $sans("op") in.not cal(E)$ and $y$ fresh)

vs.

$arrow.b sans("op")(V, cal(E)[eprom("op", x, M, p, N)])
arrow.squiggly
elet(p, M[V\/x], arrow.b sans("op")(V, cal(E)[N]))$

(where $sans("op") in.not cal(E)$)
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
#let trans(x) = $bracket.l.stroked #x bracket.r.stroked$

// language macros
#let elet(x, m, n) = $sans("let") #x <- #m sans("in") #n$
#let eprom(op, x, m, p, n) = $
  sans("promise") (sans(#op) #x mapsto #m) sans("as") #p sans("in") #n$
#let epromst(op, x, m, v, p, n) = $
  sans("promise") (sans(#op) #x mapsto #m) med @ med #v sans("as") #p sans("in") #n$

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

== Type System
Because we do not have outbound signals, we do not need to track their types!
This lets us create a type system with simpler annotations that focuses on
the "essence" of well-typed computations.

$
  "Ground types" underline(A) &::= bold(1) \
  "Value types" A, B &::= underline(A) | A ->^E B | angle(A) \
  "Effect types" E, F &::= emptyset | E, sans("op") mapsto F \
  "Effect signature" Sigma &::= emptyset | Sigma, sans("op") mapsto underline(A)
$

A value of type $angle(A)$ is a _future_ $A$,
or a _promise_ that the value _will_ become one of type $A$.

If a computation has effect type $E$, it will handle all interrupts
in its domain $sans("dom")(E)$.

If $sans("op") mapsto F in E$ and a computation with effect type $E$ handles
$sans("op")$, it will _then_ handle all interrupts in $F$ _and_ those in $E$
except for $sans("op")$. ($F$ types the handlers that are
installed by the $sans("op")$ handler.)

All typing judgments are defined with respect to a static signature $Sigma$.
This signature may only contain ground types: it may _not_ contain futures
(or functions, which may close over futures).

=== Operations on Effect Types

We use array-indexing notation $E[sans("op")]$ to denote the entry in $E$
with key $sans("op")$.

We define a _merge_ or _union_ on effect types $E union.sq F$ as follows:

$
  E union.sq emptyset &eq.delta E \
  E union.sq (F, sans("op") mapsto F_sans("op")) &eq.delta cases(
    (E union.sq F)\, sans("op") mapsto F_sans("op") & (sans("op") in.not E),
    (E union.sq F)\, sans("op") mapsto E_sans("op") union.sq F_sans("op")
    med & (E[sans("op")] = E_sans("op"))
  )
$

Intuitively, a computation with type $E union.sq F$ can handle operations
in both $E$ and in $F$.

We say $E without sans("op")$ to denote the removal of $sans("op")$
from the domain of $E$.

We define an "action" on effect types,
$E triangle.l.small sans("op")
eq.delta
(E without sans("op")) union.sq E[sans("op")]$.
Intuitively, if our computation starts at effect type $E$
and then is interrupted by $sans("op")$,
the resulting effect type is $E triangle.l.small sans("op")$.

We also have an inductively-given order on effect types:

#align(center, rule-set(
  onerule(
    name: "Sub-Nil",
    $emptyset subset.sq.eq E$
  ),
  onerule(
    name: "Sub-Cons",
    $E_sans("op") subset.sq.eq F_sans("op")$,
    $E, sans("op") mapsto E_sans("op") subset.sq.eq
    F, sans("op") mapsto F_sans("op")$
  ),
))

=== Typing Rules

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack (): bold(1)$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M: B med ! med E$,
    pad(top: 0.35em, $Gamma tack lambda x.M: A ->^E B$)
  ),
  onerule(
    name: "TV-Fut",
    $Gamma tack V: A$,
    $Gamma tack angle(V): angle(A)$
  ),
))

#align(center, rule-set(
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack sans("val") V: A med ! med E$
  ),
  onerule(
    name: "TC-Let",
    $Gamma tack M: A med ! med E$,
    $Gamma, x: A tack N: B med ! med E$,
    $Gamma tack elet(x, M, N): B med ! med E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V: A ->^E B$,
    $Gamma tack W: A$,
    $Gamma tack V med W: B med ! med E$
  ),
  onerule(
    name: "TC-Await",
    $Gamma tack V: angle(A)$,
    $Gamma tack sans("await") V: A med ! med E$
  ),
  onerule(
    name: "TC-Prom",
    $Gamma, x: Sigma[sans("op")] tack M: angle(A) med ! med E[sans("op")]$,
    $Gamma, p: angle(A) tack W: B med ! med E$,
    $Gamma tack eprom("op", x, M, p, N): B med ! med E$
  ),
  onerule(
    name: "TC-Op",
    $Gamma tack V: Sigma[sans("op")]$,
    $Gamma tack M: B med ! med E$,
    $Gamma tack arrow.b sans("op")(V, M):
    B med ! med E triangle.small.l sans("op")$
  ),
  onerule(
    name: "TC-Sub",
    $Gamma tack M: A med ! med E$,
    $E subset.sq.eq F$,
    $Gamma tack M: A med ! med F$
  ),
))

== Extensions

=== Stateful Reinstallable Interrupt Handlers

We extend interrupt handlers with the ability to _reinstall themselves_.
Our type system now requires recursive types.

$
  "Computations" M, N &::= ... | epromst("op", x med r med s, M, V, p, N) \
  "Evalutation Contexts" cal(E) &::= ...
  | epromst("op", x med r med s, M, V, p, cal(E)) \
  "Effect types" E, F &::= ... | epsilon | mu epsilon . E \
  "Type variables" epsilon in sans("TVar")
$

$
  &arrow.b sans("op")(V, cal(E)[eprom("op", x, M, p, N)])
  & #h(1em) #smallcaps("E-Prom")\
  arrow.squiggly&
  elet(p, M[V\/x, lambda ().eprom("op", x med r, M, p, sans("val") p)],
  arrow.b sans("op")(V, cal(E)[N])) \
  &("where" sans("op") in.not cal(E)) \
$

#align(center, rule-set(
    onerule(
    name: "TC-Prom",
    $Gamma, x: Sigma[sans("op")],
    r: S -> angle(A) med ! med E[sans("op")],
    s: S
    tack M: angle(A) med ! med E[sans("op")]$,
    $Gamma tack V: S$,
    $Gamma, p: angle(A) tack W: B med ! med E$,
    $Gamma tack epromst("op", x med r med s, M, V, p, N): B med ! med E$
  ),
))

(The original paper mentions some subtleties in the safety proof that requires
explicit subeffecting in this rule, i.e. the effect of $M$ is a subeffect
of $E[sans("op")]$. Since I'm not sure where exactly this arises,
I'm leaving it as is, although it is likely incorrect.)

=== Modal Typing and Dynamic Process Creation

These are really only relevant in a setting with signals and parallelism,
respectively.

(Although spawning is undoubtedly useful in many cases,
it is arguably orthogonal to the essence of asynchronous effects.
The essence lies in how a single computation responds to interrupts.
Spawning is particularly interesting when we want to prove that
a _collection of computations_ in parallel is e.g. type-safe, but to do so,
we need to know how they send messages and interact with
one another, which is a design choice that is orthogonal to the interrupt mechanism.)

= Comparisons

== Erlang-Style Actors

- In both settings, sending is _asynchronous_, in that
  the sender need not wait for (or _synchronize_ with) a receiver
  before continuing.
- Conversely, in both settings, a process may receive a message in its mailbox
  at any time, i.e. without explicitly blocking on a "receive" action.
- With asynchronous effects, a message can _interrupt_ a process:
  if a promise was made to handle the message, the process may (or may not)
  begin executing the promised computation, without need for
  an explicit await.
  - In contrast, actors must block to (explicitly) receive a message from
    their mailbox.
  - Is there a "third dimension" here? We already have
    (1) the method of handling a message and
    (2) the method of sending a message...
    is there (3) whether receiving is blocking or not?
    - Are there actors that "promise" to receive a message and then continue
      on their way?
    - Can there be "blocking promises" in an effectful concurrent setting?

== Synchronous Effects

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

The awaiting rule only exists in the asynchronous language.

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

= Direct-Messaging

An example alternative messaging system to global broadcast. Modelled after
(my shoddy understanding of) Erlang.

Target rule:
$
  angle(a\, cal(E)[sans("send op")(V) sans("to") b])
  ||
  angle(b\, M)
  arrow.squiggly
  angle(a\, cal(E)[sans("val") ()])
  ||
  angle(b\, arrow.b sans("op")(V, M))
$

== Syntax

$
  "Values" V, W &::= ... | alpha \
  "Computations" M, N &::= ... | sans("op")(V, W) | sans("spawn")(M) \
  "Processes" P, Q &::= alpha[M] | P || Q \
  "Process IDs" alpha, beta &in sans("PID") \
$

== Parallel Semantics

The sequential semantics remain the same as before. The new computations
only have meaning in a parallel setting.

Structural congruence $equiv$ on processes is given by associativity
and commutativity of $||$.

#align(center, rule-set(
  onerule(
    name: "P-Lift",
    $M arrow.squiggly N$,
    $alpha[M] arrow.squiggly alpha[N]$
  ),
  onerule(
    name: "P-Par",
    $P arrow.squiggly P'$,
    $P || Q arrow.squiggly P' || Q$
  ),
  onerule(
    name: "P-Cong",
    $P equiv P'$,
    $P' arrow.squiggly Q'$,
    $Q' equiv Q$,
    $P arrow.squiggly Q$
  )
))

$
  alpha[cal(E)[sans("spawn")(M)]]
  &arrow.squiggly
  alpha[cal(E)[sans("val") beta]] || beta[M]
  quad (beta "fresh")
  quad& #smallcaps("P-Spawn") \

  alpha[cal(E)[sans("op")(beta, V)]] || beta[M]
  &arrow.squiggly
  alpha[cal(E)[sans("val") ()]] || beta[arrow.b sans("op")(V, M)]
  quad (beta "fresh")
  quad& #smallcaps("P-Op") \
$

= Inverted Effects

Asynchronous effects, without the asynchrony.

== Syntax

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= sans("val") V | elet(x, M, N)
  | V #h(4pt) W  | sans("recv") (sans("op") x mapsto M)
  | grey(arrow.b sans("op")(V, M)) \
  "Evalutation Contexts" cal(E) &::= [.] | elet(x, cal(E), N)
  | grey(arrow.b sans("op")(V, cal(E))) \
  "Variables" x, y &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

== Semantics

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, sans("val") V, M)
  &arrow.squiggly
  M[V\/x]
  quad& #smallcaps("E-Val") \

  (lambda x.M) #h(4pt) V
  &arrow.squiggly
  M[V\/x]
  quad& #smallcaps("E-App") \

  arrow.b sans("op")(V, sans("val") W)
  &arrow.squiggly
  sans("val") W
  quad& #smallcaps("E-Done") \

  arrow.b sans("op")(V, cal(E)[sans("recv") (sans("op") V mapsto M)])
  &arrow.squiggly
  elet(y, M[V\/x], arrow.b sans("op")(V, cal(E)[sans("val") y]))
  quad& #smallcaps("E-Recv") \
  &(y "fresh and" sans("op") in.not cal(E))
$

*Conjecture.* Asynchronous effects can _simulate_ the operational behavior
of these "inverted effects" (but not vice-versa) via a translation
with the following interesting rule:
$
  #trans($sans("recv") (sans("op") x mapsto M)$)
  eq.delta
  eprom("op", x, trans(M), p, sans("await") p)
$
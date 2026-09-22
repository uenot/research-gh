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
#let punct(x) = text(fill: rgb("#0080ff"), $sans(#x)$)

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
#let elet(x, m, n) = $punct("let") #x <- #m punct("in") #n$
#let eprom(op, x, m, p, n) = $
  punct("promise") (sans(#op) #x mapsto #m) punct("as") #p punct("in") #n$
#let epromst(op, x, m, v, p, n) = $
  punct("promise") (sans(#op) #x mapsto #m) med punct("@") med #v punct("as") #p punct("in") #n$
#let einter(op, v, m) = $
  punct("with") med sans(#op)(#v) med punct("interrupt") med #m$

#let s0 = text(fill: rgb("#0080ff"), $cal(S)_0$)
#let s0l(l) = text(fill: rgb("#0080ff"),
  $cal(S)_0^(text(fill: #black, #l)) med$)
#let reset0(x) = $punct(chevron.l) #x punct(chevron.r)_punct(0)$
#let reset0l(l, x) = $punct(chevron.l) #x punct(chevron.r)^(#l)_punct(0)$
#let bang = $med ! med$

#show: scratch

= Peeling Back the Layers

Starting with Ahman and Pretnar's asynchronous effects,
we progressively strip away inessential features to reach
the core operational insight _beyond_ asynchrony: the _inversion of effect flow_.

== $lambda_æ$, "Put Simply" <lambda-ae-simply>

A re-presentation of Ahman and Pretnar's original calculus
of asynchronous effects, $lambda_æ$, with a streamlined
operational semantics.
We here neglect the higher-order extensions.

=== Syntax

We present the calculus in fine-grain call-by-value style.
Runtime-only syntactic constructs and categories are
#highlight(fill: luma(220))[highlighted in gray].

$
  "Values" V, W &::= x | () | lambda x.M | (V, W) | punct("now") V \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
  | V med W | punct("fst") V | punct("snd") V \
& | punct("signal") sans("op")(V)
  | eprom("op", x, M, p, N)
  | punct("await")(V) \
& | grey(einter("op", V, M)) \
  grey("Promise Contexts " cal(P)) &::=
  [.] | eprom("op", x, M, p, cal(P)) \
  grey("Evalutation Contexts " cal(E)) &::=
  [.] | elet(x, cal(E), N) | eprom("op", x, M, p, cal(E)) \
  &| einter("op", V, cal(E))\
  grey("Processes " P\, Q) &::= punct("run") M | P || Q \
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

*Values.* Standard values include variables $x$,
the unit value $()$, functions $lambda x.M$, and pairs $(V, W)$.
The only non-standard value is the
_fulfilled promise_, $punct("now") V$, which denotes that
some previously-made promise has been fulfilled with value $V$.
(These are _not_ runtime-only syntax: the programmer writes these
as the return values of promise clauses.)

*Computations*. The standard FGCBV constructs let us
lift values $V$ to computations via $punct("val") V$
and sequence computations $M$ and $N$ via $elet(x, M, N)$.
As usual, we apply functions via $V med W$ and project pairs via
$punct("fst") V$ and $punct("snd") V$.

The remaining constructs are $lambda_æ$-specific.
We can _signal_ an operation to all other processes
via $punct("signal") sans("op")(V)$. Here, $sans("op")$
is an operation name drawn from a fixed signature $Sigma$,
and $V$ is a payload value sent with the signal.

Other processes can _promise to handle_ this signal
via form $eprom("op", x, M, p, N)$.
On receiving a signal with matching name $sans("op")$, we bind the
payload to $x$ in $M$ and execute $M$.
The result of $M$ will be bound to $p$ in $N$.
The semantics of promise handlers is _non-blocking_, i.e.
$N$ can evaluate even if we have not yet handled $sans("op")$.
$N$ may contain free occurences of $p$, so to use $p$ safely,
we must explicitly _await_ its value via $punct("await") V$,
which blocks until $V$ is a fulfilled promise.

Finally, runtime-only computation $einter("op", V, M)$ represents
the reception of a signal $sans("op")$ with payload $V$
in computation $M$. This signal may _interrupt_ the normal
evaluation of $M$ by reacting with a promise handler, hence
the name of the construct.

*Processes.* Our simple processes are either lifted computations
$punct("run") M$, or two processes in parallel $P || Q$.
A _structural congruence_ relation $equiv$ on processes is
given simply by associativity and commutativity of $||$.

=== Sequential Semantics

We define a small-step operational semantics via judgment
$M arrow.squiggly N$ as follows.
Substitution $M[V\/x]$ is defined as expected.

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, cal(P)[punct("val") V], M)
  &arrow.squiggly
  cal(P)[M[V\/x]] & #smallcaps("E-Val")\
  (lambda x.M) med V &arrow.squiggly M[V\/x] & #smallcaps("E-App")\
  punct("fst") (V, W) &arrow.squiggly punct("val") V & #smallcaps("E-Fst")\
  punct("snd") (V, W) &arrow.squiggly punct("val") W & #smallcaps("E-Snd")\
  punct("await now") V &arrow.squiggly punct("val") V & #smallcaps("E-Await")\
  einter("op", W, cal(P)[punct("val") V])
  &arrow.squiggly
  cal(P)[punct("val") V]
  & #smallcaps("E-Disc") \
  && ("where" sans("op") in.not cal(P))
  $$
  &einter("op", V, cal(E)[eprom("op", x, M, p, N)])
  & quad #smallcaps("E-Prom") \
  &arrow.squiggly
  elet(p, M[V\/x], einter("op", V, cal(E)[N]))
  &("where" sans("op") in.not cal(E)) \
$

Rules #smallcaps("E-App"),
#smallcaps("E-Fst"), and #smallcaps("E-Snd") are standard.
Rule #smallcaps("E-Await") unwraps a fulfilled promise
(and notably _blocks_ until the promise is fulfilled).

*Promise Contexts*. The rule #smallcaps("E-Val") is non-standard
for an FGCBV system due to the presence of a _promise context_
$cal(P)$ around the value $V$. A promise context is simply
a stack of promise handlers.
In #smallcaps("E-Val"), we "lift" this context from the value
onto the continuation $M$.

To illustrate the careful design of this rule, we give two examples
of _incorrect_ rules. First consider the standard value rule:
$
  elet(x, punct("val") V, M)
  &arrow.squiggly
  M[V\/x] quad #smallcaps("E-Val")^*\
$

With this rule alone, the following computation will be blocked
until receiving an interrupt:
$
  elet(x, (eprom("op", x, M, p, punct("val") V)), N)
$
We consider this behavior incorrect since only $punct("await")$
should block: we want to continue with reducing $N$.
To circumvent this issue, we generalize our rule over an arbitrary
stack of promises $cal(P)$ (which reduces to the ordinary rule
when $cal(P) = [.]$, i.e. no promise handlers are installed).

Now consider a second alternative which implements this fix:

$
  elet(x, cal("P")[punct("val") V], M)
  &arrow.squiggly
  M[V\/x] quad #smallcaps("E-Val")^(**)\
$

By _discarding_ the promise context $cal("P")$, we plainly introduce scoping errors, as in the following example:

$
  elet(x, (eprom("op", x, M, p, punct("val") p)), N)
  arrow.squiggly
  N[p\/x]
$

Even if the left-hand side is closed, the reduction has $p$ free,
since we have thrown away its binder. We therefore must _maintain_
any promise handlers in the continuation, since the let-bound value
may reference their (promise-bound) variables.

This leads us to the proper rule #smallcaps("E-Val"), whereby the previous example term reduces as follows
(choosing $cal(P) = eprom("op", x, M, p, [.])$):

$
  elet(x, (eprom("op", x, M, p, punct("val") p)), N)
  arrow.squiggly
  eprom("op", x, M, p, N[p\/x])
$

This "promise-lifting" behavior mimics the algebraicity of handlers
in Ahman and Pretnar's original calculus, where promise handlers
"bubble out" of $punct("let")$-statements.

*Discarding*. We also use promise contexts to define
_interrupt discarding_ in the rule #smallcaps("E-Disc").
Intuitively, we can safely ignore an interrupt around
an inert value $punct("val") V$.
We generalize this idea to _unrelated_ stacks of promises
via $cal(P)[punct("val") V]$ and the side condition
$sans("op") in.not cal(P)$, which is defined as follows:

#align(center, rule-set(
  onerule(
    $sans("op") in.not [.]$
  ),
  onerule(
    $sans("op") in.not cal(P)$,
    $sans("op") eq.not sans("op")'$,
    $sans("op") in.not eprom("op"'med, x, M, p, cal(P))$,
  )
))

*Promise Handling*.
The most interesting rule is #smallcaps("E-Prom"), which corresponds
to the handling of an interrupt.
We have two "conditions" for this reaction to occur. First, the
name of the promised operation $sans("op")$
must match that of the interrupt.
Second, we require that $sans("op") in.not cal(E)$, which
is defined similarly to the above:

#align(center, rule-set(
  onerule(
    $sans("op") in.not [.]$
  ),
  onerule(
    $sans("op") in.not cal(E)$,
    $sans("op") in.not elet(x, cal(E), N)$
  ),
  onerule(
    $sans("op") in.not cal(E)$,
    $sans("op") eq.not sans("op")'$,
    $sans("op") in.not eprom("op"' med, x, M, p, cal(E))$
  ),
  onerule(
    $sans("op") in.not cal(E)$,
    $sans("op") eq.not sans("op")'$,
    $sans("op") in.not einter("op"', V, M)$
  ),
))

Intuitively, in the context of #smallcaps("E-Prom"),
$sans("op") in.not cal(E)$ means that the interrupt is the
_innermost one_ and the promise handler is the _outermost one_
for $sans("op")$. We allow $cal(E)$ to mention
unrelated operations $sans("op")'$,
i.e. _interrupts implicitly commute_.

If these conditions are satisfied, #smallcaps("E-Prom") immediately
rewrites the promise-clause as a $punct("let")$-binding.
This may "interrupt" the evaluation of $N$ with the evaluation of
$M$. We then follow the standard $punct("let")$-semantics:
once $M$ has evaluated, we bind its result to $p$
and continue evaluating $N$.

*Deep vs. Shallow.*
Also in #smallcaps("E-Prom"), we _propagate the interrupt_
further into the continuation $cal(E)[N]$,
following the design choice of Ahman and Pretnar.
They note that this behavior mirrors that
of standard _deep handlers_.
Like with handlers, we might consider an alternative "shallow" rule
which does not propagate the interrupt:

$
  &einter("op", V, cal(E)[eprom("op", x, M, p, N)])
  & #h(1em) #smallcaps("E-Prom")^* \
  &arrow.squiggly
  elet(p, M[V\/x], cal(E)[N])
  &("where" sans("op") in.not cal(E)) \
$

It is currently unknown in what situations deep or shallow interrupts might be preferred, or whether they
are equally expressive (as are deep and shallow handlers).

*Evaluation Contexts*.
The rule #smallcaps("E-Ctx") is of standard form, but the syntax
of evaluation contexts $cal(E)$ is not:
they allow reduction
under $punct("promise")$s and $punct("interrupt")$s
alongside $punct("let")$s.

The ability to evaluate under promises,
in conjunction with promise-lifting via #smallcaps("E-Val"),
gives us our non-blocking semantics:
a computation $M$ can freely evaluate
_underneath_ a promise handler.
Furthermore, if that promise handler binds variable $p$,
we may evaluate $M$ _with $p$ free_ until we $punct("await") p$!
Of course, we ought not to be able to _use_ unbound variable
$p$ until it resolves to a value, which we can enforce by typing.

That we also evaluate under $punct("interrupt")$s
is a _design choice_ made by Ahman and Pretnar.
Under this paradigm, an interrupt will "wait" for a
handler to possibly reveal itself, e.g.:

$
  &einter("op", W, (lambda x.eprom("op", y, M, p, N)) med V) \
  arrow.squiggly
  &einter("op", W, eprom("op", y, M[V\/x], p, N[V\/x]))
  quad &(#smallcaps("E-App"))\
  arrow.squiggly
  &elet(p, M[V\/x, W\/y], N[V\/x])
  quad &(#smallcaps("E-Prom"))
$

An alternative coherent design choice would be to _discard_
interrupts which don't immediately match a handler.
We could achieve this by removing interrupts from the syntax of
evaluation contexts and changing #smallcaps("E-Disc")
to the following rule:

$
  einter("op", W, cal(E)[M])
  &arrow.squiggly
  cal(E)[M]
  quad & #smallcaps("E-Disc")^*
$

with the side conditions that $sans("op") in.not cal(E)$
and that $cal(E)$ is the "deepest possible" such evaluation context
(formally, that there is no other nontrivial context $cal(E)'$
and term $N$ such that $M = cal(E)'[N]$.)

Under this paradigm, the prior example reduces as follows:

$
  &einter("op", W, (lambda x.eprom("op", y, M, p, N)) med V) \
  arrow.squiggly
  &(lambda x.eprom("op", y, M, p, N)) med V
  quad &(#smallcaps("E-Disc")^*)\
  arrow.squiggly
  &eprom("op", y, M[V\/x], p, N[V\/x])
  quad &(#smallcaps("E-App"))
$

Which approach is preferable seems, to me, to be a matter of taste.

=== Concurrent Semantics

Note that construct $punct("signal") sans("op")(V)$
has not yet been given a semantics, nor have we shown how
the runtime-only construct $einter("op", V, M)$ arises.
We address both these issues in the concurrent fragment of the semantics, which concerns processes.

In our current setting, we assume a fixed number of processes
(i.e. we do not allow for dynamic process creation).
Ahman and Pretnar show that a $punct("spawn")$ construct
can be safely added, and I claim that the same is true of this
streamlined setting.

We have the following (fairly) standard rules on processes:

#align(center, rule-set(
  onerule(
    name: "P-Run",
    $M arrow.squiggly N$,
    $punct("run") M || P arrow.squiggly punct("run") N || P$
  ),
  onerule(
    name: "P-Cong",
    $P equiv P'$,
    $P' arrow.squiggly Q'$,
    $Q' equiv Q$,
    $P arrow.squiggly Q$
  )
))

and one interesting rule, #smallcaps("P-Broad"),
for signal broadcast:

$
  punct("run") cal(E)[punct("signal") sans("op")(V)]
  || punct("run") M_1 || ... || punct("run") M_n\
  arrow.squiggly
  punct("run") cal(E)[punct("val") ()]
  || punct("run") einter("op", V, M_1) || ...
  || punct("run") einter("op", V, M_n)
$

Locally, signalling reduces to the unit value. Globally,
_every_ other process in the configuration
receives the signal as an interrupt.

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
If we admitted the above, we would be admitting _partial_ broadcasts.
Note that we can still evaluate any single process by moving it to
the leftmost position via structural congruence.

*Preciseness.*
To be precise about broadcast (for those who take issue with
the use of ellipses), we might instead define the following rule:
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
the same "bubbling-down" behavior of the original calculus.)

=== Reinstallable Stateful Interrupt Handlers

To implement the examples in the original paper,
we must extend interrupt handlers with the ability to _reinstall themselves_,
and to carry _state_ across reinstalls.
This extension carries over well to our streamlined semantics.

$
  "Computations" M, N &::= ... | epromst("op", x med r med s, M, V, p, N) \
  "Evalutation Contexts" cal(E) &::= ...
  | epromst("op", x med r med s, M, V, p, cal(E)) \
$

In the promise clause $sans("op") x med r med s
mapsto M$, $x$ is bound to the interrupt payload as before,
$r$ is a function that _reinstalls_ the handler
(and immediately returns the resulting promise variable),
and $s$ is the current state value.
An initial state value $V$ is provided to
the promise handler in
$epromst("op", x med r med s, M, V, p, N)$,
The reinstall function takes an argument $y$
which becomes the new state value.

The (deep) step rule is given as follows:

$
  &einter("op", W, cal(E)[epromst("op", x med r med s, M, V, p, N)])
  &#smallcaps("E-PromRS")\
  arrow.squiggly
  &elet(p, M[W\/x, (lambda y.epromst("op", x med r med s, M, y, p, sans("val") p))\/r, V\/s] \ &,
  einter("op", W, cal(E)[N]))
  &("where" sans("op") in.not cal(E)) \
$

=== Examples

*Non-Confluence*. Ahman and Pretnar note two distinct sources of
non-confluence in their calculus.
The first occurs in the following term:
$
  einter("op", V,
    eprom("op", x,
      (eprom("op"'med, y, M, q, punct("await") q)),
      p, N))
$

Say $N arrow.squiggly N'$ for some $N'$. Before handling
the interrupt, we can reduce $N$ by choosing to apply
#smallcaps("E-Ctx")
for $cal(E)=  einter("op", V, eprom("op", x, ..., p, [.]))$,
leading to the following sequence:

$
  &einter("op", V,
    eprom("op", x,
      (eprom("op"'med, y, M, q, punct("await") q)),
      p, N)) \
  arrow.squiggly
  &einter("op", V,
    eprom("op", x,
      (eprom("op"'med, y, M, q, punct("await") q)),
      p, N')) \
  arrow.squiggly
  &elet(p, (eprom("op"'med, y, M[V\/x], q, punct("await") q)),
  einter("op", V, N')) \
$

The final computation above cannot reduce further: we are blocked
until receiving $sans("op")'$.

Alternatively, we may immediately handle the interrupt, as in the
sequence below:

$
  &einter("op", V,
    eprom("op", x,
      (eprom("op"'med, y, M, q, punct("await") q)),
      p, N)) \
  arrow.squiggly
  &elet(p, (eprom("op"'med, y, M[V\/x], q, punct("await") q)),
  einter("op", V, N)) \
$

This term is _also_ blocked until receiving $sans("op")'$,
but notably cannot reduce $N$ to $N'$.

The second source of non-confluence is shown by the following
configuration:

$
  punct("run") (einter("op", V,
    (eprom("op", x, punct("signal") sans("op"')(V'), p,
      punct("signal") sans("op"'')(V'')
    ))
  )) || punct("run") M
$

If we first choose to evaluate under the promise handler, we
reduce as follows:

$
  &punct("run") (einter("op", V,
    (eprom("op", x, punct("signal") sans("op"')(V'), p,
      punct("signal") sans("op"'')(V'')
    ))
  )) || punct("run") M \
  arrow.squiggly
    &punct("run") (einter("op", V,
    (eprom("op", x, punct("signal") sans("op"')(V'), p,
      punct("val") ()
    ))
  )) \
  &|| punct("run") (einter("op"'', V'', M)) \
  arrow.squiggly
  &punct("run") (
    elet(p, punct("signal") sans("op"')(V'[V\/x]),
      punct("val") ()
    )
  ) || punct("run") (einter("op"'', V'', M)) \
  arrow.squiggly
  &punct("run") punct("val") ()
  || punct("run") (einter("op"', V'[V\/x], (einter("op"'', V'', M)))) \
$

If we instead first handle the promise, we get the following:
$
  &punct("run") (einter("op", V,
    (eprom("op", x, punct("signal") sans("op"')(V'), p,
      punct("signal") sans("op"'')(V'')
    ))
  )) || punct("run") M \
  arrow.squiggly^2
  &punct("run")
    elet(p, punct("signal") sans("op"')(V'[V\/x]),
      punct("signal") sans("op"'')(V'')
    ) || punct("run") M \
  arrow.squiggly^2
  &punct("run") punct("signal") sans("op"'')(V'')
    || einter("op"', V'[V\/x], punct("run") M) \
  arrow.squiggly
  &punct("run val") ()
    || punct("run") (einter("op"'', V'', (einter("op"', V'[V\/x], M))))
$

Both of these sources of non-confuence have to do with the
_interrupting nature of interrupts_.
(I hypothesize that) we could remove the non-confluence by
stipulating that interrupts must _immediately react_
with any present handlers, and be discarded otherwise.
(The converse solution— delaying handling until the continuation is blocked— defeats the point of interrupts.)
Whether we _want_ to do this is questionable.

== The Sequential Fragment <async-inbound>

The interesting behavior in the above calculus concerns the relationship between _interrupts_ and _handlers_.
The method of _issuing interrupts_ is entirely orthogonal.
Here, we isolate the sequential fragment
and then show how alternative signalling systems fit
neatly onto the sequential core.

=== Core Syntax & Semantics

We simply remove _signals_ and _processes_ from the language of
@lambda-ae-simply. The sequential fragment of the semantics
remains exactly the same.
There is no longer a "concurrent semantics".

For convenience, we recap the syntax of the resulting language:

$
  "Values" V, W &::= x | () | lambda x.M | (V, W) | punct("now") V \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
  | V med W | punct("fst") V | punct("snd") V \
& | eprom("op", x, M, p, N)
  | punct("await")(V) \
& | einter("op", V, M) \
  grey("Promise Contexts " cal(P)) &::=
  [.] | eprom("op", x, M, p, cal(P)) \
  grey("Evalutation Contexts " cal(E)) &::=
  [.] | elet(x, cal(E), N) | eprom("op", x, M, p, cal(E)) \
  &| einter("op", V, cal(E))\
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

In this setting, whether operations ought to be programmer-level
or runtime-only syntax is a matter of taste.
In the former interpretation, the programmer themselves
may "inject" values into their computations by
writing operation calls.
In the latter interpretation, we treat operations as events
induced by the outside world which the programmer can receive.

Again, the sequential semantics are identical to @lambda-ae-simply
(recall that we had no rule concerning signals
in the sequential fragment):

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))


$
  elet(x, cal(P)[punct("val") V], M)
  &arrow.squiggly
  cal(P)[M[V\/x]] & #smallcaps("E-Val")\
  (lambda x.M) med V &arrow.squiggly M[V\/x] & #smallcaps("E-App")\
  punct("fst") (V, W) &arrow.squiggly punct("val") V & #smallcaps("E-Fst")\
  punct("snd") (V, W) &arrow.squiggly punct("val") W & #smallcaps("E-Snd")\
  punct("await now") V &arrow.squiggly punct("val") V & #smallcaps("E-Await")\
  einter("op", W, cal(P)[punct("val") V])
  &arrow.squiggly
  cal(P)[punct("val") V]
  & #smallcaps("E-Disc") \
  && ("where" sans("op") in.not cal(P))
  $$
  &einter("op", V, cal(E)[eprom("op", x, M, p, N)])
  & #h(1em) #smallcaps("E-Prom") \
  &arrow.squiggly
  elet(p, M[V\/x], einter("op", V, cal(E)[N]))
  &("where" sans("op") in.not cal(E)) \
$

=== Primitive Reactivity

Inspired by the semantics of my
$lambda^sans("react")_sans("hook")$,
we simulate event reception as a primitive semantic rule.

We introduce a new "top-level" step judgment,
$attach(arrow.squiggly, tr: top)$,
which _subsumes_ the standard step $arrow.squiggly$
via rule #smallcaps("ET-Lift").
This ensures that we do not introduce events
underneath an evaluation context.

We have one new rule, #smallcaps("ET-Event"),
which interrupts the current computation with
_some_ operation and payload.

#align(center, rule-set(
  onerule(
    name: "ET-Lift",
    $M arrow.squiggly N$,
    $M attach(arrow.squiggly, tr: top) N$
  ),
  onerule(
    name: "ET-Event",
    $M attach(arrow.squiggly, tr: top)
    einter("op", V, M)$
  ),
))

This paradigm is useful for reasoning about single processes
which can react to events.

Consider an "accumulator" program which sums the
number of $sans("put")$ operations it receives
before a $sans("get")$ operation.
We can write this program as follows, allowing ourselves
access to general ML-style references:

$
  &punct("let") t o t a l <- punct("ref") 0 punct("in") \
  &eprom("put", x med r,
    t o t a l := !t o t a l + x \; r (), p,\
    &eprom("get", \_, punct("val now") !t o t a l, q,\
      &punct("await") q
    )
  )
$

The $sans("put")$ handler updates the $t o t a l$ reference and
reinstalls itself forever. The $sans("get")$ handler only
activates once, wherein we get the current $t o t a l$.
By $punct("await")$ing the associated promise $q$, the computation
will reduce to a snapshot of the total
at the time of the first $sans("get")$.
(The $sans("put")$ handler will continue to update $t o t a l$;
we could optimize this by only reinstalling if $sans("get")$
has not yet been received.)

To reason about this program, we technically need not assume
#smallcaps("ET-Event") only creates $sans("put")$ and $sans("get")$
operations (although doing so would be convenient), since
any orthogonal operations will be ignored.
We do require the operation payloads to be well-typed
with respect to the operation names.

=== Actor-Style Direct Messaging

An alternative concurrent semantics
based on Erlang-style actors.

We extend the language syntax as follows:

$
  "Values" V, W &::= ... | grey(alpha) \
  "Computations" M, N &::= ... | punct("spawn")(M) | punct("signal") sans("op")(V) punct("to") W \
  grey("Processes" med P\, Q) &::= alpha angle(M) | P || Q | nu alpha. P\
  "Process IDs" alpha, beta &in sans("PID") \
$

We add one new value, _process identifiers_,
which are dynamically generated at runtime.
These are created by the $punct("spawn")(M)$
construct, which runs $M$ in a new process
and returns the newly-generated process ID.

Signalling an operation is now _process-targeted_.
The new construct $punct("signal") sans("op")(V) punct("to") W$ sends operation $sans("op")$
and payload $V$ to the process identified by $W$.

Our process syntax for lifting computations, $alpha angle(M)$,
now associates every computation
$M$ with a process ID $alpha$.
Process composition $P || Q$ and restriction
$nu alpha. P$ are standard.

*Structural Congruence.* Structural congruence $equiv$ on processes is given by the usual rules (alongside reflexivity and transitivity):

$
  P || Q &equiv Q || P \
  P_1 || (P_2 || P_3) &equiv (P_1 || P_2) || P_3 \
  nu alpha . nu beta . P &equiv nu beta . nu alpha . P \
  nu alpha . (P || Q) &equiv P || nu alpha. Q
  quad ("if" alpha in.not f n(P) )
$

where $f n(P)$ denotes the set of free process IDs in $P$, defined standardly as follows:

$
  f n(alpha angle(M)) &= {alpha} \
  f n(P || Q) &= f n(P) union f n(Q) \
  f n(nu alpha. P) &= f n(P) \\ {alpha}
$

*Semantics.* The _sequential_ fragment
of the semantics remains identical to before:
our new computations _have_ no parallel semantics.

We define a semantics on _processes_ via the rules below:

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
    name: "P-Nu",
    $P arrow.squiggly Q$,
    $nu alpha. P arrow.squiggly nu alpha. Q$
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
  alpha angle(cal(E)[punct("spawn")(M)])
  &arrow.squiggly
  nu beta. (
  alpha angle(cal(E)[punct("val") beta]) || beta angle(M)
  )
  quad (beta "fresh")
  quad& #smallcaps("P-Spawn") \

  alpha angle(cal(E)[punct("signal") sans("op")(V) punct("to") beta]) || beta angle(M)
  &arrow.squiggly
  alpha angle(cal(E)[punct("val") ()]) || beta angle(einter("op", V, M))
  quad& #smallcaps("P-Sig") \
$

The first four rules are fairly standard.
#smallcaps("P-Lift") lets us lift
computation reduction to process reduction.
#smallcaps("P-Par") and #smallcaps("P-Nu")
let us reduce processes underneath parallel
composition and restriction, respectively.
#smallcaps("P-Cong") uses the aforementioned
strucutral congruence relation to allow us to
reduce _congruent_ trees.
(For instance, say we have $P || Q$ and we know that $Q arrow.squiggly Q'$. Ordinarily, #smallcaps("P-Par") only reduces the left-hand side of a parallel composition, so $P || Q$ cannot step. However, we know $P || Q equiv Q || P$, so we may "swap" $Q$ to the left-hand side via #smallcaps("P-Cong").)

Rule #smallcaps("P-Spawn") dynamically spawns a new process. If process $alpha$ evaluates
to a $punct("spawn")(M)$ construct, we pull
that $M$ into its own process with freshly generated ID $beta$. Locally in process $alpha$,
$punct("spawn")(M)$ evaluates to the generated ID $beta$,
thereby allowing process $alpha$ to $punct("signal")$ operations to $beta$.
We also wrap the resulting parallel composition
in a $nu$-binder for $beta$, denoting the scope of $beta$.

(*Note*: $nu$-binding seems unnecessary given that the generated names are sufficiently
(i.e. globally) fresh. Since we have no static names, all $nu$-binders can trivially be pulled all the way to the outside of the configuration, at which point they are seemingly pointless.)

Finally, rule #smallcaps("P-Sig") captures
the signalling of an operation.
Say process $alpha$ evaluates to the
construct $punct("signal") sans("op")(V) punct("to") beta$, and is in parallel with a process
$beta$ running _arbitrary_ computation $M$.
Locally in $alpha$, the $punct("signal")$ construct simply evaluates to the unit value.
Crucially, in process $beta$, we
_interrupt_ the current computation $M$ by
stepping to $einter(sans("op"), V, M)$.

== Inbound Effects <sync-inbound>

The _asynchrony_ of asynchronous effects is only one of (what I claim are) the two core developments of Ahman and Pretnar.
The second novel design choice is the
_inversion of effect flow_: the effects of Ahman and Pretnar flow _inwards_ towards the center of a computation, whereas standard effects flow _outwards_.
I call the former kind _outbound_ effects, and the latter _inbound_ effects.
Here, I show that inbound effects form a coherent language in a _fully synchronous setting_.

=== Syntax

$
  "Values" V, W &::= x | () | lambda x.M | (V, W) \
  "Computations" M, N &::= sans("val") V | elet(x, M, N)
  | V med W | punct("fst") V | punct("snd") V \
  &| punct("handle") (sans("op") x mapsto M)
  | grey(punct("inject") med sans("op")(V) med punct("into") med M) \
  grey("Evalutation Contexts" med cal(E)) &::= [.] | elet(x, cal(E), N)
  | punct("inject") sans("op")(V) punct("into") cal(E) \
  "Variables" x, y &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

All values in the language are standard,
as are the first five computations.
(Previously, the only non-standard value stood
for promises, which are asynchrony-specific.)

The first novel computation is
$punct("handle") (sans("op") x mapsto M)$,
which states that we block until receiving
an operation $sans("op")(V)$, and then
resume continuation $M$ with $V$ bound to $x$.

The construct $punct("inject") sans("op")(V) punct("into") M$ is analogous to the previously-seen $einter("op", V, M)$, but renamed since, conceptually, the construct
no longer interrupts computation.
Instead, $punct("inject") sans("op")(V) punct("into") M$ means that any handlers for $sans("op")$ inside $M$ should be continued with parameter value $V$.

Evaluation contexts $cal(E)$ still include
operation injections, but in contrast to before,
there is no context form for handlers, reflecting that handlers are synchronous computations. We no longer need promise contexts,
which are necessary to bind the variables
introduced by asynchronous operations.


*On Runtime Syntax.* Whether operations ought to be programmer-level or runtime-only
syntax is a matter of taste.
In the former interpretation, the programmer themselves
may "inject" values into their computations by
writing operation calls.
In the latter interpretation, we treat operations as events
induced by the outside world which the programmer can receive.

=== Semantics <sync-inbound-sem>

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

  punct("fst") (V, W)
  &arrow.squiggly
  punct("val") V
  quad& #smallcaps("E-Fst") \

  punct("snd") (V, W)
  &arrow.squiggly
  punct("val") W
  quad& #smallcaps("E-Snd") \

  punct("inject") sans("op")(V) punct("into val") W
  &arrow.squiggly
  punct("val") W
  quad& #smallcaps("E-Disc") \
$$
  &punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("handle") (sans("op") x mapsto M)] \
  arrow.squiggly&
  elet(y, M[V\/x], punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("val") y])
  quad& #smallcaps("E-Hdl") \
  &(y "fresh and" sans("op") in.not cal(E))
$

The first five rules are standard.
Rule #smallcaps("E-Val") is simplified from
the asynchronous calculus in that there is no
longer mention of a promise context.
Since this calculus is synchronous,
there are no longer free promise variables to worry about, and the value $V$ will be closed (for well-typed programs).

Rule #smallcaps("E-Disc") discards injections
into trivial computations of form $punct("val") V$.
The rule is simplified compared to the asynchronous version, since as before, there is no need for mention of promise contexts.

Rule #smallcaps("E-Hdl") codifies the
handling of inbound effects. The handler
may be underneath an arbitrary evaluation context $cal(E)$ so long as judgment $sans("op") in.not cal(E)$ holds (defined as we have seen previously).
_However_, in contrast to the previous definitions of
$sans("op") in.not cal(E)$, since handlers do not form an evaluation context, this judgment simply means that this injection is "innermost" for operation $sans("op")$.
(There is no need to stipulate that the handler is "outermost".)

When an operation matches a handler, we evaluate
$M$ with $V$ substituted for $x$. We $punct("let")$-bind the result of $M$ to fresh variable $y$, and _resume_ the previous context via computation $cal(E)[punct("val") y]$.
In the "deep" style, we re-inject $sans("op")(V)$
into this resumption.

*The let-binding is necessary.*
One may assume that we can remove the let-binding, simplifying this rule as follows:

$
  punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("handle") (sans("op") x mapsto M)]
  &arrow.squiggly
  punct("inject") sans("op")(V) punct("into")
  cal(E)[M[V\/x]]
  quad& #smallcaps("E-Hdl")^* \
  &(y "fresh and" sans("op") in.not cal(E))
$

But this rule is _inequivalent_ to the prior version, and does _not_ model the behavior we want
(or, at least, that I think we want).
Consider the following term:

$
  punct("inject") sans("op")(1) punct("into")
  punct("handle") (sans("op") x mapsto (
    punct("handle") (sans("op") z mapsto x + z)
  ))
$

The key point of this term is that the outermost handler for $sans("op")$
_reinstalls_ a second handler for $sans("op")$.
Under the correct rule #smallcaps("E-Hdl"),
this term evaluates as follows:

$
  &punct("inject") sans("op")(1) punct("into")
  punct("handle") (sans("op") x mapsto (
    punct("handle") (sans("op") z mapsto x + z)
  )) \
  arrow.squiggly&
  elet(y, punct("handle") (sans("op") z mapsto 1 + z), punct("inject") sans("op")(1) punct("into") punct("val") y) \
  arrow.squiggly&
  elet(y, punct("handle") (sans("op") z mapsto 1 + z), punct("val") y)
$

We first handle the operation via the outermost handler, and then discard the remaining injection. Note that we are still blocked on
$sans("op")$, due to the inner handler.

The incorrect rule $#smallcaps("E-Hdl")^*$
evaluates as follows:

$
  &punct("inject") sans("op")(1) punct("into")
  punct("handle") (sans("op") x mapsto (
    punct("handle") (sans("op") z mapsto x + z)
  )) \
  arrow.squiggly&
  punct("inject") sans("op")(1) punct("into")
    punct("handle") (sans("op") z mapsto 1 + z)
  ) \
  arrow.squiggly&
  punct("inject") sans("op")(1) punct("into")
    1 + 1
  ) \
  arrow.squiggly&
  punct("val") 2
$

Here, the injection has been received by both the outer _and_ inner handlers.
I argue that this behavior is "wrong" for two (admittedly nebulous) reasons:
- The evaluation of handler bodies _outside_ of the injection context corresponds to how standard outbound effects work. In that setting, if a handler body reraises an operation, it will not be handled by the handler itself, but by a further-outwards handler. (This point is raised by Ahman and Pretnar.)
- Ahman and Pretnar raise useful examples for
  _reinstallable_ handlers, which are inexpressible if
  the reinstalled handler receives the same injection. For instance, a server which responds to requests-as-operations ought to be able to respond to multiple different requests!

This dilemma is still relevant when considering
_shallow_ effects, which have either of the following handling rules:

$
  punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("handle") (sans("op") x mapsto M)]
  &arrow.squiggly
  elet(y, M[V\/x], cal(E)[punct("val") y])
  quad& #smallcaps("E-HdlShallow") \
  &(y "fresh and" sans("op") in.not cal(E)) \
  punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("handle") (sans("op") x mapsto M)]
  &arrow.squiggly
  cal(E)[M[V\/x]]
  quad& #smallcaps("E-HdlShallow")^* \
  &(y "fresh and" sans("op") in.not cal(E)) \
$

Consider the following term:
$
  punct("inject") sans("op")(1) punct("into")
  punct("inject") sans("op")'(2) punct("into")
  punct("handle") (sans("op") x mapsto (
    punct("handle") (sans("op")' med z mapsto x + z)
  ))
$

Under the first rule, the term evaluates as follows:

$
  &punct("inject") sans("op")(1) punct("into")
  punct("inject") sans("op")'(2) punct("into")
  punct("handle") (sans("op") x mapsto (
    punct("handle") (sans("op")' med z mapsto x + z)
  )) \
  arrow.squiggly&
  elet(y, punct("handle") (sans("op")' med y mapsto 1 + y),
  punct("inject") sans("op")'(2) punct("into val") y)
$

This term is blocked until receiving another injection of $sans("op")'$. In contrast,
the same term evaluates as follows under the second rule:

$
  &punct("inject") sans("op")(1) punct("into")
  punct("inject") sans("op")'(2) punct("into")
  punct("handle") (sans("op") x mapsto (
    punct("handle") (sans("op")' med z mapsto x + z)
  )) \
  arrow.squiggly&
  punct("inject") sans("op")'(2) punct("into")
    punct("handle") (sans("op")' med y mapsto 1 + y) \
    arrow.squiggly&
    punct("val") 3 \
$

In the first example, the computation has received $sans("op")'$ _before_ $sans("op")$,
so the inner handler installed by the handler
for $sans("op")$ is not seen by the injection
of $sans("op")'$.
In contrast, the second example
does not care in what order injections are performed.

Ultimately, I regard the choice of rule style here as a design choice, although I lean strongly towards the "let-lifted" rules
(unstarred) over the "direct" rules (starred).

=== Conjectures

*Conjecture 1.* Asynchronous effects (as in @lambda-ae-simply) can _simulate_ the operational behavior
of these inbound effects (but not vice-versa) via a translation
with the following interesting rule:
$
  #trans($punct("handle") (sans("op") x mapsto M)$)
  eq.delta
  eprom("op", x, trans(M), p, punct("await") p)
$

Essentially, asynchronous effects _split_
the inbound $punct("handle")$ construct into
two parts: _promising to handle_ the operation
(via $punct("promise")$) and _receiving the result_ (via $punct("await")$).

*Conjecture 2.* Inbound and outbound effects
are _mutually expressible_ in terms of one another (for a particular flavor of outbound effects).

A suitable translation consists in swapping
handlers for operations, and thunking/dethunking
computations appropriately.
For instance, the inbound-to-outbound translation is roughly as follows:

$
  #trans($punct("handle") (sans("op") x mapsto M)$)
  &eq.delta
  punct("perform") sans("op")(lambda x.#trans($M$)) \
  #trans($punct("inject") sans("op")(V) punct("into") M$)
  &eq.delta
  punct("with") (sans("op") x mapsto x med V)
  punct("handle") #trans($M$) \
$

It is an open question whether, or how exactly, some of the traditional features of outbound effects (namely first-class continuations) might be extended similarly to inbound effects.

= Outbound Asynchronous Effects <async-outbound>

We further argue that _asynchrony_ is a distinct feature from
_inbound effect flow_
by providing a language of outbound effects
with asynchrony.

== Syntax

$
  "Values" V, W &::= x | () | lambda x.M | (V, W) | punct("now") V \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
  | V med W | punct("fst") V | punct("snd") V
  | punct("await") V \
& | punct("perform") p <- sans("op")(V) punct("in") M
  | punct("with") (sans("op") x mapsto M) punct("handle") N \
  grey("Performance Contexts " cal(P)) &::=
  [.] | punct("perform") p <- sans("op")(V) punct("in") cal(P) \
  grey("Evalutation Contexts " cal(E)) &::=
  [.] | elet(x, cal(E), N)
  | punct("perform") p <- sans("op")(V) punct("in") cal(E)\
  &| punct("with") (sans("op") x mapsto M) punct("handle") cal(E)\
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

Values are identical to those of inbound asynchronous effects,
as seen in @async-inbound.

Computations for lifting values via $punct("val")$,
sequencing via $punct("let")$,
application, and pair projection are all standard.
Awaiting via $punct("await") V$ also works identically to @async-inbound.

For operation calls, we introduce a new form,
$punct("perform") p <- sans("op")(V) punct("in") M$,
which asynchronously invokes operation $sans("op")$ with payload $V$.
The operation result is immediately bound to promise variable $p$
in continuation $M$, which can be explicitly $punct("await")$ed later.

Handlers, of form $punct("with") (sans("op") x mapsto M) punct("handle") N$,
reify operations $sans("op")$ which occur in continuation $N$
by binding the payload to $x$ and executing $M$.

*Contexts*. We retain an "asynchronous binding context" $cal(P)$,
which now represents a stack of performed operations. (In the inbound variant,
we called $cal(P)$ a promise context: we rename it here a performance context.)

Evaluation contexts $cal(E)$ encompass let-bindings as usual.
We can also evaluate underneath _both_ operations and handlers.

== Semantics

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, cal(P)[punct("val") V], M)
  &arrow.squiggly
  cal(P)[M[V\/x]] & #smallcaps("E-Val")\
  (lambda x.M) med V &arrow.squiggly M[V\/x] & #smallcaps("E-App")\
  punct("fst") (V, W) &arrow.squiggly punct("val") V & #smallcaps("E-Fst")\
  punct("snd") (V, W) &arrow.squiggly punct("val") W & #smallcaps("E-Snd")\
  punct("await now") V &arrow.squiggly punct("val") V & #smallcaps("E-Await")\
  punct("with") (sans("op") x mapsto M)
    punct("handle") cal(P)[punct("val") V]
  &arrow.squiggly
  cal(P)[punct("val") V]
  & #smallcaps("E-Disc") \
  && ("where" sans("op") in.not cal(P))
  $$
  &punct("with") (sans("op") x mapsto M) punct("handle") cal(E)[
    punct("perform") p <- sans("op")(V) punct("in") N]
  & quad #smallcaps("E-Hdl") \
  &arrow.squiggly
  elet(p, M[V\/x], punct("with") (sans("op") x mapsto M) punct("handle") cal(E)[N])
  & quad ("where" sans("op") in.not cal(E)) \
$

Most rules (#smallcaps[E-Ctx, E-App, E-Fst, E-Snd, E-Await]) are
identical/analogous to @async-inbound.

#smallcaps[E-Val] also appears the same as in @async-inbound, but it is worth
re-emphasizing that contexts $cal(P)$ now range over operation calls
instead of promise handlers. Importantly, we "lift" $cal(P)$ out of the
bound computation and over the continuation for the same reason as before:
to ensure any promise variables $p$ which occur in the value $V$
do not escape the scope of their $punct("perform")$ clauses.

#smallcaps[E-Disc] discards a handler around an inert computation.
This computation may include operation calls, so long
as they are unrelated to the handler being discarded.

Finally, #smallcaps[E-Hdl] represents the handling of an operation.
A handler may react with an operation
underneath some evaluation context $cal(E)$,
and reduces to a let-binding for the reasons described in @sync-inbound-sem.
We bind the operation payload $V$ to $x$ in $M$, and then bind the result
of $M$ to $p$ in continuation $cal(E)[N]$.
We reinstall the handler around the continuation $cal(E)[N]$
(the handler is "deep").

As with inbound effects, our definition of evaluation contexts introduces
asynchrony. In the following computation, if continuation $N$ can reduce,
then either $N$ will reduce or the handler will "interrupt" $N$ by
handling the operation.
$
  punct("with") (sans("op") x mapsto M) punct("handle") cal(E)[
  punct("perform") p <- sans("op")(V) punct("in") N]
$


= Reintroducing Resumptions

== The Problem

Ordinary outbound synchronous effect handlers
have first-class access to a _delimited continuation_
in their handler bodies. For instance,
a single-operation handler (ignoring the return clause)
could be written as follows:
$
  punct("with") (sans("op") x med k mapsto M)
  punct("handle") N
$

Variable $x$ is bound
to the operation payload in $M$, while $k$
is the _continuation_ of the program, which
can be invoked once, multiple times, stored for later, etc.
Precisely, the relevant operational rule
can be given as follows:

$
  punct("with") (sans("op") x med k mapsto M)
  punct("handle") cal(E)[sans("op")(V)]
  &arrow.squiggly
  M[V\/x, (lambda y. punct("with") (sans("op") x med k mapsto M)
  punct("handle") cal(E)[punct("val") y])\/k] \
  &(y "fresh and" sans("op") in.not cal(E))
$

Above, the value $lambda y. punct("with") (sans("op") x med k mapsto M)
  punct("handle") cal(E)[punct("val") y]$
represents the program continuation.

In ordinary (synchronous and outbound) effect handler systems, continuations:
+ occur in the construct with a "handling computation" in its syntax
  (namely the handler),
+ occur in the construct which _algebraically behaves_
  like a handler (i.e. lives "above" the subcomputations
  it reacts with), and
+ immediately capture the current evaluation context— about which there can be no ambiguity, since operations are blocking.

In an _outbound_ setting, points 1 and 2 are (extensionally) identical, but in an _inbound_ setting, they are irreconcilable. We must choose one or the other.
(As a spoiler, point 1 is clearly more sensible.)

Furthermore, in an _asynchronous_ setting, point 3 introduces ambiguity: the continuation is _indeterminate_, since it can reduce without necessarily
resolving the handler first.

In this section, I formulate a sensible solution to both of these problems independently, before putting them together,
thus endowing Ahman and Pretnar's calculus with continuations.

== Synchronous Inbound Effects

We take the language of @sync-inbound and extend the
$punct("handle")$ construct to the following:
$
  punct("handle") (sans("op") x med k mapsto M)
$
where $k$ is a variable representing the _continuation_ of the program. (The rest of the syntax remains the same.)

We change the #smallcaps[E-Hdl] step rule to the following:
$
  punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("handle") (sans("op") x med k mapsto M)]
  &arrow.squiggly
  M[V\/x, (lambda y.punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("val") y])\/k] \
  &(y "fresh and" sans("op") in.not cal(E))
$
The continuation is now a first-class object in the scope
of the "handling computation" $M$.
We can trivially recover the behavior of before via a single tail-resumptive continuation call, but we can also
choose to invoke the continuation multiple times,
or not at all, or do some post-processing on the result of the continuation.

We no longer need to worry about the "let-lifting" problem
mentioned in @sync-inbound.
The re-injection is _underneath_ the continuation, so
any handlers installed by the handling computation $M$
will _never_ be handled by that re-injection.
(This fact lends credence to my choice to let-lift in the continuation-less language.)

Shallow operations are a straightforward adaptation:
we simply do not re-inject the operation in the continuation.
$
  punct("inject") sans("op")(V) punct("into")
  cal(E)[punct("handle") (sans("op") x med k mapsto M)]
  &arrow.squiggly
  M[V\/x, (lambda y.cal(E)[punct("val") y])\/k] \
  &(y "fresh and" sans("op") in.not cal(E))
$

*Takeaway*. Continuations ought to occur in the "handler",
i.e. the construct with the handling computation.
(The alternative— associating a continuation with the injection somehow— is, I hope, plainly nonsense.)

== Asynchronous Outbound Effects

We take the language of @async-outbound and extend the $punct("handle")$
construct to the following (as well as the corresponding evaluation context):

$
  punct("with") (sans("op") x med k mapsto M) punct("handle") N
$

We rephrase the #smallcaps[E-Hdl] rule as follows:

$
  &punct("with") (sans("op") x med k mapsto M) punct("handle") cal(E)[
    punct("perform") p <- sans("op")(V) punct("in") N]
  & quad #smallcaps("E-Hdl") \
  &arrow.squiggly
  M[V\/x, (lambda p.punct("with") (sans("op") x mapsto M) punct("handle") cal(E)[N])\/k]
  & quad ("where" sans("op") in.not cal(E)) \
$

Importantly, the lambda-term which reifies the continuation binds the variable $p$ found in the
original syntax of the $punct("perform")$ construct.

As in the previous subsection, the prior behavior is trivially recoverable, and a shallow version of the above rule is a simple adaptation.


This rule extends the nondeterminism of the original system in interesting ways. Consider the following term,
for which we display the first couple reduction steps:

$
  &punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("perform") p <- sans("get")() punct("in")
  punct("perform") q <- sans("get")() punct("in")\
  &quad punct("let") x <- punct("await") p punct("in")
  punct("let") y <- punct("await") q punct("in") x + y \
  arrow.squiggly&
  (lambda p. punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("perform") q <- sans("get")() punct("in")\
  &quad punct("let") x <- punct("await") p punct("in")
  punct("let") y <- punct("await") q punct("in") x + y \
  &) med (punct("now") 21) \
  arrow.squiggly&
   punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("perform") q <- sans("get")() punct("in")\
  &quad punct("let") x <- punct("await") (punct("now") 21) punct("in")
  punct("let") y <- punct("await") q punct("in") x + y \
$

So far, we have only ever had one choice of redex, so our execution has been deterministic.
Now, at any point, we may either _immediately handle_ the operation, or _reduce underneath_ the handler and operation.

Immediately handling leads to the following sequence:

$
  arrow.squiggly& (lambda q.
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("let") x <- punct("await") (punct("now") 21) punct("in")
  punct("let") y <- punct("await") q punct("in") x + y) med (punct("now") 21) \
  arrow.squiggly&
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("let") x <- punct("await") (punct("now") 21) punct("in")
  punct("let") y <- punct("await") (punct("now") 21) punct("in") x + y\
  arrow.squiggly^2&
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle")
  punct("let") y <- punct("await") (punct("now") 21) punct("in") 21 + y\
  arrow.squiggly^2&
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle")  21 + 21\
  arrow.squiggly^2&
  punct("val") 42\
$

Delaying handling as long as possible leads to the following sequence:

$
  arrow.squiggly&
   punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("perform") q <- sans("get")() punct("in")
  punct("let") x <- punct("val") 21 punct("in")
  punct("let") y <- punct("await") q punct("in") x + y \
  arrow.squiggly&
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") \
  &quad punct("perform") q <- sans("get")() punct("in")
  punct("let") y <- punct("await") q punct("in") 21 + y \
  arrow.squiggly& (lambda q.
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") punct("let") y <- punct("await") q punct("in") 21 + y) med (punct("now") 21)\
  arrow.squiggly&
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") punct("let") y <- punct("await") (punct("now") 21) punct("in") 21 + y\
  arrow.squiggly^2&
  punct("with") (sans("get") \_ med k mapsto k med (punct("now") 21)) punct("handle") 21 + 21\
  arrow.squiggly^2&
  punct("val") 42\
$

In the second reduction, the continuation bound to $k$
is "more evaluated" than in the first reduction.
These reductions happen to be confluent, although this need not be the case as we have seen previously.

*Takeaway*. The captured continuation is _undetermined_ in an asynchronous setting, and that is okay!

== Asynchronous Inbound Effects

We utilize the two previous takeaways, restated here:
- the continuation occurs in the promise handler, and
- the continuation is nondeterministically "captured"
  whenever the handler chooses to react with the interrupt.

We take the language of @async-inbound and extend the $punct("promise")$
construct to the following (as well as the corresponding evaluation context):
$
  eprom("op", x med k, M, p, N)
$

We rephrase the #smallcaps[E-Prom] rule as follows:

$
  &einter("op", V, cal(E)[eprom("op", x med k, M, p, N)])
  & quad #smallcaps("E-Prom") \
  &arrow.squiggly
  M[V\/x, (lambda p. einter("op", V, cal(E)[N]))\/k]
  &("where" sans("op") in.not cal(E)) \
$


=== Danel's Problem

In discussions, Danel raised the following issue with
the above approach to continuations.
I will argue that it is not an issue.

In the original calculus (with continuations added), $punct("promise")$s bubble out
of $punct("let")$s as so:
$
  &elet(x, (eprom("op", y med k, M, p, N_1)), N_2) \
  arrow.squiggly
  &eprom("op", y med k, M, p, elet(x, N_1, N_2))
$

Before reduction, the continuation $k$ has the return type of $N_1$, but after reduction, the continuation
has the return type of $N_2$. The continuation is therefore untypeable (and really, this is a side effect of it not being clear what the continuation even _means_.)

*My response.* The continuation is not delimited by $punct("let")$s, but by $punct("interrupt")$s.
- This works like normal delimited continuations
  (e.g. shift/reset) in that shift "controls"
  the continuation, but is delimited by a different
  construct (reset).

The operational rule which implements continuations in the algebraic setting
is simply:

$
  &einter("op", V, eprom("op", x med k, M, p, N))
  & quad #smallcaps("E-Prom")^* \
  &arrow.squiggly
  M[V\/x, (lambda p. einter("op", V, N))\/k]
$

The $punct("promise")$ bubbles up (via the aforementioned rule, among others)
to the $punct("interrupt")$, which clearly acts as its delimiter.
The continuation is now just $N$: which will likely not be
the exact same $N$ written by the programmer, due to bubbling, but
its type ought to be statically determined regardless.

Typing the continuation is not straightforward, but _should be_ possible.
In $eprom("op", x med k, M, p, N)$, the continuation return type is
not given by the type of $N$.
We must adopt something like the _answer type system_
of Danvy and Filinski, but extended to a "multi-prompt" setting.

= Exploring Delimited Control

It is well-known that delimited control and (outbound) effect handlers are
closely related.
In this section, I investigate the relationship between delimited control
and _inbound_ effects and handlers.

I argue that inbound effects _are an extension_ of delimited control.
Starting with a fairly standard language of delimited control,
I incrementally generalize the language until arriving at _exactly_
inbound (synchronous) effects, as in @sync-inbound.

I have not yet considered formal translations, although this would be a natural
step in arguing for this correspondence.

This section also investigates typing. The incremental-extension approach
allows me to reuse type systems for delimited control
when designing one for inbound effects. (This was my original motivation
for exploring delimited control.)

== Basic Delimited Control <delim-basic>

We adopt the $s0$ (shift-0) and $reset0(med)$ (reset-0) operators
of Danvy and Filinski, and adapt the corresponding type system
of Cong and Asai (which does _not_ feature answer type modification).
We present this calculus in FGCBV style.

=== Syntax

$
  "Values" V, W &::= x | lambda x.M | () \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
    | V med W | s0 k.M | reset0(M) \
  "Evaluation contexts" cal(E) &::= [.] | elet(x, cal(E), N)
    | reset0(cal(E)) \
  "Types" A, B &::= 1 | A ->^E B \
  "Effect types" E &::= emptyset | E, A
$

Values are standard. We have variables, functions, and the unit value.
Standard computations include value injection, let-binding, and application.

Computation $s0 k.M$ (shift-0) binds to $k$ the _delimited continuation_
of the program and continues as $M$. The continuation is delimited by the
nearest enclosing $reset0(M)$ (reset-0) construct.
(In both cases, the subscript 0 is mere punctuation.)

Evaluation contexts include let-bindings as usual, but also include resets.

Types include the unit type and functions, where functions are annotated
with an "effect type" $E$. Effect types are (ordered) lists of ordinary types,
and they track the "answer types" of the surrounding $reset0(med)$ constructs.

=== Semantics

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, punct("val") V, M) &arrow.squiggly M[V\/x]
  & #smallcaps[E-Val]\
  (lambda x.M) med V &arrow.squiggly M[V\/x]
  & #smallcaps[E-App]\
  reset0(punct("val") V) &arrow.squiggly punct("val") V
  & #smallcaps[E-Reset]\
  reset0(cal(E)[s0 k.M])
  &arrow.squiggly
  M[(lambda x.reset0(cal(E)[punct("val") x]))\/k]
  quad (reset0(med) in.not cal(E)) &quad #smallcaps[E-Shift]\
$

The first three rules #smallcaps[E-Ctx], #smallcaps[E-Val],
and #smallcaps[E-App] are standard.

In #smallcaps[E-Reset], if a computation reduces to a value
underneath a reset, we can discard the reset.

Rule #smallcaps[E-Shift] describes the heart of delimited control.
On the left, we have a shift inside a reset, separated by some
evaluation context $cal(E)$. Side condition $reset0(med) in.not cal(E)$
enforces that the reset in question is the _innermost_ reset.
(In this system, then, $cal(E)$ is a stack of $punct("let")$-bindings.)

On the right, we step to $M$, but with $k$ bound to the
function $lambda x.reset0(cal(E)[punct("val") x])$, representing
the delimited continuation. The continuation captures the previous
evaluation context $cal(E)$, such that invoking $k$ lets us "resume" the
previous context.

This rule involves two key design choices on the right-hand side:
- We _do not_ reinstall a delimiter around $M$, i.e.
  the right-hand side is not $reset0(M[...\/k])$.
  This would be the traditional `shift` of Danvy and Filinski.
- We _do_ reinstall a delimiter around the continuation body
  $cal(E)[punct("val")(x)]$. Not installing the delimiter,
  i.e. substituting $lambda x.cal(E)[punct("val") x]$ for $k$,
  would result in the `cupto` of Gunter et al.

I choose this particular flavor of delimited control precisely because
it is similar to how effect handlers work. It would be interesting to explore
variations of effect handlers which model the other variants
of delimited control (e.g. as summarized by Downen and Ariola).

=== Type System

We have two typing judgments: $Gamma tack V: A$ for values
and $Gamma tack M: A bang E$ for computations.

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack (): 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M: B bang E$,
    pad(top: 0.33em)[$Gamma tack lambda x.M: A ->^E B$]
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack punct("val") V: A bang E$
  ),
  onerule(
    name: "TC-Let",
    $Gamma tack M: A bang E$,
    $Gamma, x: A tack N: B bang E$,
    $Gamma tack elet(x, M, N): B bang E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V: A ->^E B$,
    $Gamma tack W: A$,
    $Gamma tack V med W: B bang E$
  ),
  onerule(
    name: "TC-Reset",
    $Gamma tack M: A bang E, A$,
    $Gamma tack angle(M)_0: A bang E$
  ),
  onerule(
    name: "TC-Shift",
    $Gamma, k: A ->^E B tack M: B bang E$,
    $Gamma tack s0 k.M: A bang E, B$
  ),
))

The first six rules (excluding #smallcaps[TC-Reset] and #smallcaps[TC-Shift])
are fairly standard for type-and-effect systems.
The effect annotation can be captured by #smallcaps[TC-Lam]
and reinvoked by #smallcaps[TC-App].
In #smallcaps[TC-Val], we allow values to have any effect type instead of
the most precise type $emptyset$, and in #smallcaps[TC-Let], we require both
computations to share an effect type.

Read bottom-up, rule #smallcaps[TC-Reset] extends the effect type,
while rule #smallcaps[TC-Shift] consumes it.
In #smallcaps[TC-Reset], we mark the _overall_ return type of the
delimited computation (the "answer type") by extending $E$ with $A$.

To type #smallcaps[TC-Shift], we must know the answer type of the
nearest delimiter, which is given by the most recently added (rightmost)
type in the effect list $B$.
The subcomputation $M$ should have this type $B$.
Continuation $k$ receives type $A ->^E B$, where $A$ is the type of
the _overall_ computation $s0 k.M$: intuitively, the shift is a "hole" in the
captured context, and we ought to "plug" that hole with something of the
same type.

=== Examples

We present examples in coarse-grain style.
We introduce strings and integers, along with two primitive functions:
- $sans("length"): sans("Str") -> sans("Int")$
  returns the length of the given string, and
- $sans("replicate"): sans("Str") -> sans("Int") -> sans("Str")$,
  where $sans("replicate") s med n$ concatenates $s$ repeatedly $n$ times.
(Assume these primitives are polymorphic in their effects. A full account of
polymorphism greatly exceeds our current scope.)

*Example 1*. Consider the following term, leaving $M$ abstract for the moment:
$
  reset0(sans("replicate") #raw("\"foo\"")
    reset0(sans("length") s0 k_1. s0 k_2. M))
$

Let $M = k_2 (k_1 med #raw("\"bar\""))$. This term executes safely:

$
  &reset0(sans("replicate") #raw("\"foo\"")
    reset0(sans("length") s0 k_1. s0 k_2. k_2 (k_1 med #raw("\"bar\"")))) \
  ~>
  &reset0(sans("replicate") #raw("\"foo\"")
    (s0 k_2. k_2 (k_1 med #raw("\"bar\"")))[
    (lambda y. reset0(sans("length") y))\/ k_1]) \
  ~>
  &(k_2 (k_1 med #raw("\"bar\"")))[
    lambda y. reset0(sans("length") y) \/ k_1,
    lambda z. reset0(sans("replicate") #raw("\"foo\"") z) \/ k_2
  ] \
  =
  & (lambda z. reset0(sans("replicate") #raw("\"foo\"") z))
    (lambda y. reset0(sans("length") y)) #raw("\"bar\"") \
  ~>
  & (lambda z. reset0(sans("replicate") #raw("\"foo\"") z))
    reset0(sans("length") #raw("\"bar\"")) \
  ~>^*
  & (lambda z. reset0(sans("replicate") #raw("\"foo\"") z)) med 3 \
  ~>
  &reset0(sans("replicate") #raw("\"foo\"") 3)
  ~>^* #raw("\"foofoofoo\"")
$

However, doing so _in general_ is unsafe: this is reflected in our type system
by the fact that $k_1$ is expected to be pure, but is not.
The following derivation fails:

#align(center, rule-set(
  prooftree(rule(
    rule(
      "...",
      rule(
        rule(
          rule(
            rule(
              "...",
              rule(
                $k_1: sans("Str") ->^sans("Str") sans("Int"),
                k_2: sans("Int") ->^emptyset sans("Str"),
                tack k_1: sans("Str") ->^emptyset sans("Int")$,
                "...",
                pad(top: 0.3em, $k_1: sans("Str") ->^sans("Str") sans("Int"),
                k_2: sans("Int") ->^emptyset sans("Str"),
                tack k_1 med #raw("\"bar\""):
                sans("Str") bang sans("Int")$)
              ),
              pad(top: 0.3em, $k_1: sans("Str") ->^sans("Str") sans("Int"),
              k_2: sans("Int") ->^emptyset sans("Str"),
              tack k_2 (k_1 med #raw("\"bar\"")):
              sans("Str") bang emptyset$)
            ),
            $emptyset tack s0 k_1. s0 k_2. k_2 (k_1 med #raw("\"bar\"")):
            sans("Str") bang sans("Str"), sans("Int")$
          ),
          $emptyset tack sans("length") s0 k_1. s0 k_2.
            k_2 (k_1 med #raw("\"bar\"")):
          sans("Int") bang sans("Str"), sans("Int")$
        ),
        $emptyset tack reset0(sans("length") s0 k_1. s0 k_2.
          k_2 (k_1 med #raw("\"bar\""))):
        sans("Int") bang sans("Str")$
      ),
      $emptyset tack sans("replicate") #raw("\"foo\"")
      reset0(sans("length") s0 k_1. s0 k_2. k_2 (k_1 med #raw("\"bar\""))):
      sans("Str") bang sans("Str")$
    ),
    $emptyset tack reset0(sans("replicate") #raw("\"foo\"")
    reset0(sans("length") s0 k_1. s0 k_2. k_2 (k_1 med #raw("\"bar\"")))):
    sans("Str") bang emptyset$
  ))
))

*Example 2.*
To see how this effect might arise, consider the alternative term
(where $s0().M$ is shorthand
for $s0 k.M$ with $k in.not f v(M)$)

$
  reset0(1 + reset0(
    elet(x, s0 k. s0 (). k med 2, s0 (). s0 (). 3)
  ))
$

This term gets stuck during reduction, as follows:

$
  &reset0(1 + reset0(
    elet(x, s0 k. s0(). k med 2, s0(). s0(). 3)
  ))\
  ~>
  &reset0(1 +s0(). k med 2)[
    (lambda y.reset0(elet(x, y, s0 (). s0 (). 3)))\/k
  ]\
  ~> &(lambda y.reset0(elet(x, y, s0 (). s0 (). 3))) med 2 \
  ~> &reset0(elet(x, 2, s0 (). s0 (). 3))\
  ~> &reset0(s0 (). s0 (). 3)\
  ~> &s0 (). 3 cancel(~>, angle: #45deg)
$

This term is ill-typed, as shown by the failing partial derivation below:

#align(center, rule-set(
  prooftree(
    rule(
      rule(
        rule(
          $k: sans("Int") ->^sans("Int") sans("Int") tack
          k: sans("Int") ->^emptyset sans("Int")$,
          $k: sans("Int") ->^sans("Int") sans("Int") tack 2: sans("Int")$,
          pad(top: 0.3em)[
            $k: sans("Int") ->^sans("Int") sans("Int")
            tack k med 2:
            sans("Int") bang emptyset$
          ]
        ),
        pad(top: 0.3em)[
          $k: sans("Int") ->^sans("Int") sans("Int")
          tack
          s0 (). k med 2:
          sans("Int") bang sans("Int")$
        ]
      ),
      $emptyset
      tack
      s0 k. s0 (). k med 2:
      sans("Int") bang sans("Int"), sans("Int")$
    )
  )
))

The effect type of $k$ says that, when run, $k$ may shift to some delimiter with
answer type $sans("Int")$.
We see this occur in the reduction: the function bound to $k$ performs two
shifts, only one of which is captured by the delimiter under the function.
Our type system is right to rule this out.

*Example 1, Revisited.*
To make this term typecheck, we need to add extra control constructs.
Choose $M = reset0(elet(x, k_1 #raw("\"bar\""), s0 ().k_2 med x))$,
and let $Gamma = k_1: sans("Str") ->^sans("Str") sans("Int"),
      k_2: sans("Int") ->^emptyset sans("Str")$ for readability:

#align(center, rule-set(
  prooftree(rule(
    rule(
      rule(
        rule(pad(top: 0.3em,
          $Gamma tack k_1: sans("Str") ->^sans("Str") sans("Int")$)
        ),
        $Gamma tack k_1 #raw("\"bar\""): sans("Int") bang sans("Str")$
      ),
      rule(
        rule(
          rule(pad(top: 0.3em,
            $Gamma, x: sans("Int") tack k_2:
              sans("Int") ->^emptyset sans("Str")$
          )),
          rule(
            $Gamma, x: sans("Int") tack x: sans("Int")$
          ),
          $Gamma, x: sans("Int") tack k_2 med x: sans("Str") bang emptyset$
        ),
        $Gamma, x: sans("Int") tack s0 ().k_2 med x):
        sans("Str") bang sans("Str")$
      ),
      $Gamma tack elet(x, k_1 #raw("\"bar\""), s0 ().k_2 med x):
      sans("Str") bang sans("Str")$
    ),
    $Gamma tack reset0(elet(x, k_1 #raw("\"bar\""), s0 ().k_2 med x)):
    sans("Str") bang emptyset$
  ))
))

The extra reset delimits any shifts done by $k_1$. To typecheck
$k_2$, we add a "dummy shift" that removes the extra reset. (In practice,
this would be better dealt with by subtyping: we know that,
since $k_2$ does not shift, it is safe to include in _any_ context.)

*Example 3*. Suppose we want to flip the order in which we compose the
continuations, as in the following reduction sequence:

$
  &reset0(sans("replicate") #raw("\"foo\"")
    reset0(sans("length") s0 k_1. s0 k_2. k_1 (k_2 med 2))) \
  ~>
  &reset0(sans("replicate") #raw("\"foo\"")
  s0 k_2. k_1 (k_2 med 2))[(lambda y. reset0(sans("length") y))\/ k_1]) \
  ~>
  &(k_1 (k_2 med 2))[
    lambda y. reset0(sans("length") y) \/ k_1,
    lambda z. reset0(sans("replicate") #raw("\"foo\"") z) \/ k_2
  ] \
  =
  &(lambda y. reset0(sans("length") y)) (
    lambda z. reset0(sans("replicate") #raw("\"foo\"") z)) med 2\
  ~>
  &(lambda y. reset0(sans("length") y))
    reset0(sans("replicate") #raw("\"foo\"") 2)\
  ~>^*
  &(lambda y. reset0(sans("length") y)) #raw("\"foofoo\"")
  ~>^* 6
$

Typing this term safely requires _answer type modification_.
Ordinarily, $sans("replicate")$ returns a string, but by hijacking the
continuations, we have modified the computation to integer type.
Tracking this behavior with types is difficult.

== Static Multi-Prompt Control <delim-multi>

We extend the system of @delim-basic with _labels_ for resets and shifts.

This differs from traditional "multi-prompt" systems
(e.g. Dybvig, Peyton Jones, and Sabry) in that we do not have _dynamic_
label creation, i.e. there is no `new-prompt` construct.
Instead, we draw labels from a fixed, statically known set
(which should remind one of operations.)

=== Syntax

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
    | V med W | reset0l(ell, M) | s0l(ell) k.M \
  "Evaluation contexts" cal(E) &::= [.] | elet(x, cal(E), N)
    | reset0l(ell, cal(E)) \
  "Types" A, B &::= 1 | A ->^E B \
  "Effect types" E, F &::= emptyset | E, ell: A
$

The extensions from @delim-basic consist in the addition of labels $ell$,
drawn from a predetermined set $cal(L)$.
The programmer labels resets and shifts with these $ell$.
We extend the reset evaluation context accordingly.

Effect types are likewise extended with labels:
we associate a label $ell$ with a type $A$.
Unlike row types, we do not permit exchange in these effect lists.

=== Semantics

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, punct("val") V, M) &arrow.squiggly M[V\/x]
  & #smallcaps[E-Val]\
  (lambda x.M) med V &arrow.squiggly M[V\/x]
  & #smallcaps[E-App]\
  angle(punct("val") V)^ell_0 &arrow.squiggly punct("val") V
  & #smallcaps[E-Reset]\
  reset0l(ell, cal(E)[s0l(ell) k.M])
  &arrow.squiggly
  M[(lambda x.reset0l(ell, cal(E)[punct("val") x]))\/k]
  quad (ell in.not cal(E))
  & quad #smallcaps[E-Shift]\
$

The only rule which differs from @delim-basic is #smallcaps[E-Shift].
On the left-hand side, we require that the labels on the reset and shift
are matching. The context $cal(E)$ may now contain resets with _other_
labels: side condition $ell in.not cal(E)$ ensures that the reset in question
is the innermost such reset _for label_ $ell$.

=== Type System

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack (): 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M: B bang E$,
    pad(top: 0.33em)[$Gamma tack lambda x.M: A ->^E B$]
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack punct("val") V: A bang E$
  ),
  onerule(
    name: "TC-Let",
    $Gamma tack M: A bang E$,
    $Gamma, x: A tack N: B bang E$,
    $Gamma tack elet(x, M, N): B bang E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V: A ->^E B$,
    $Gamma tack W: A$,
    $Gamma tack V med W: B bang E$
  ),
  onerule(
    name: "TC-Reset",
    $Gamma tack M: A bang E, ell: A$,
    $Gamma tack reset0l(ell, M): A bang E$
  ),
  onerule(
    name: "TC-Shift",
    $Gamma, k: A ->^E B tack M: B bang E$,
    $ell in.not F$,
    $Gamma tack s0l(ell) k.M: A bang E, ell: B, F$
  ),
))

Most rules are the same as in @delim-basic. Rule #smallcaps[TC-Reset]
adds the label of the reset alongside the answer type to the effect list.
Rule #smallcaps[TC-Shift] may now "search" the effect list: we only require
that $ell: A$ is the most recent entry with label $ell$,
which is enforced by the condition that $ell in.not F$.
Any labels in $F$ will be _discarded_ in the continuation $k$
and the computation $M$: operationally, we shift outside of their scope.

=== Example

We present in coarse-grain style with integers, strings,
and two labels $a, b$.

Take the following term:
$
  reset0l(a, sans("intToStr")
    reset0l(b, 1 + s0l(a) k. (k med 2 plus.double k med 3)))
$

It is well-typed, as shown by the following derivation
(with some repetition omitted):

#align(center, rule-set(
  prooftree(
    rule(
      rule(
        rule(
          rule(
            rule(
              rule(
                rule(
                  rule(
                    pad(top:0.3em)[
                      $k: sans("Int") ->^emptyset sans("Str") tack
                      k: sans("Int") ->^emptyset sans("Str")$
                    ]
                  ),
                  $...$,
                  pad(top:0.3em)[
                    $k: sans("Int") ->^emptyset sans("Str") tack
                    k med 2:
                    sans("Str") bang emptyset$
                  ]
                ),
                $...$,
                pad(top:0.3em)[
                  $k: sans("Int") ->^emptyset sans("Str") tack
                  k med 2 plus.double k med 3:
                  sans("Str") bang emptyset$
                ]
              ),
              $emptyset tack
              s0l(a) k. (k med 2 plus.double k med 3):
              sans("Int") bang a: sans("Str"), b: sans("Int")$
            ),
            $...$,
            $emptyset tack
            1 + s0l(a) k. (k med 2 plus.double k med 3):
            sans("Int") bang a: sans("Str"), b: sans("Int")$
          ),
          $emptyset tack
          reset0l(b, 1 + s0l(a) k. (k med 2 plus.double k med 3)):
          sans("Int") bang a: sans("Str")$
        ),
        $emptyset tack sans("intToStr")
        reset0l(b, 1 + s0l(b) k. (k med 2 plus.double k med 3)):
        sans("Str") bang a: sans("Str")$
      ),
      $emptyset tack reset0l(a, sans("intToStr")
      reset0l(b, 1 + s0l(a) k. (k med 2 plus.double k med 3))):
      sans("Str") bang emptyset$
    )
  )
))

The term reduces as follows:

$
  &reset0l(a, sans("intToStr")
    reset0l(b, 1 + s0l(a) k. (k med 2 plus.double k med 3))) \
  ~>
  &(k med 2 plus.double k med 3)
  [lambda y.reset0l(a, sans("intToStr") reset0l(b, 1 + y)) \/ k] \
  ~>
  &reset0l(a, sans("intToStr") reset0l(b, 1 + 2)) plus.double
  (lambda y. reset0l(a, sans("intToStr") reset0l(b, 1 + y))) med 3 \
  ~>^*
  &\"3\" plus.double
  (lambda y. reset0l(a, sans("intToStr") reset0l(b, 1 + y))) med 3 \
  ~>
  &\"3\" plus.double reset0l(a, sans("intToStr") reset0l(b, 1 + 3)) \
  ~>^*
  &\"3\" plus.double \"4\" arrow.squiggly \"34\"
$


=== Relation to @delim-basic.

We recover the language of @delim-basic
by restricting ourselves to exactly one label.

We can also probably encode labels
into a label-less language with sums, by re-shifting if the labels
are not equal (similar in spirit to what Forster et al. do).

== Value Injection

We extend resets with the ability to pass values to shifts.

=== Syntax

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
    | V med W | angle(V >> M)^ell_0 | s0^ell med x med k.M \
  "Evaluation contexts" cal(E) &::= [.] | elet(x, cal(E), N)
    | angle(V >> cal(E))^ell_0 \
  "Types" A, B, C &::= 1 | A ->^E B \
  "Effect types" E, F &::= emptyset | E, ell: A ->> B
$

=== Semantics

#align(center, rule-set(
  onerule(
    name: "E-Ctx",
    $M arrow.squiggly N$,
    $cal(E)[M] arrow.squiggly cal(E)[N]$
  )
))

$
  elet(x, punct("val") V, M) &arrow.squiggly M[V\/x]
  & #smallcaps[E-Val]\
  (lambda x.M) med V &arrow.squiggly M[V\/x]
  & #smallcaps[E-App]\
  angle(V >>punct("val") W)^ell_0 &arrow.squiggly punct("val") W
  & #smallcaps[E-Reset]\
  angle(V >> cal(E)[s0^ell med x med k.M])^ell_0
  &arrow.squiggly
  M[V\/x, (lambda y.angle(V >> cal(E)[punct("val") y])^ell_0)\/k]
  quad (ell in.not cal(E))
  & quad #smallcaps[E-Shift]\
$

=== Type System

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack (): 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M: B bang E$,
    pad(top: 0.33em)[$Gamma tack lambda x.M: A ->^E B$]
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack punct("val") V: A bang E$
  ),
  onerule(
    name: "TC-Let",
    $Gamma tack M: A bang E$,
    $Gamma, x: A tack N: B bang E$,
    $Gamma tack elet(x, M, N): B bang E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V: A ->^E B$,
    $Gamma tack W: A$,
    $Gamma tack V med W: B bang E$
  ),
  onerule(
    name: "TC-Reset",
    $Gamma tack V: A$,
    $Gamma tack M: B bang E, ell: A ->> B$,
    $Gamma tack angle(V >> M)^ell_0: B bang E$
  ),
  onerule(
    name: "TC-Shift",
    $Gamma, x: A, k: C ->^E B tack M: B bang E$,
    $ell in.not F$,
    $Gamma tack s0 med x med k.M: C bang E, ell: A ->> B, F$
  ),
))

=== Global-Signature Type System

#align(center, rule-set(
  onerule(
    name: "TC-Reset",
    $ell : A_ell in Sigma$,
    $Gamma tack V: A_ell$,
    $Gamma tack M: B bang E, ell: B$,
    $Gamma tack angle(V >> M)^ell_0: B bang E$
  ),
  onerule(
    name: "TC-Shift",
    $ell : A_ell in Sigma$,
    $Gamma, x: A_ell, k: C ->^E B tack M: B bang E$,
    $ell in.not F$,
    $Gamma tack s0 med x med k.M: C bang E, ell: B, F$
  ),
))

== Local-Signature Outbound Effects

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= punct("val") V | elet(x, M, N) | V med W  \
    &| sans("op")(V, x.M)
    | punct("with") (sans("op") x med k mapsto M) punct("handle") N \
  "Evaluation contexts" cal(E) &::= [.] | elet(x, cal(E), N)
    | punct("with") (sans("op") x med k mapsto M) punct("handle") cal(E)\
  "Types" A, B, C &::= 1 | A ->^E B \
  "Effect types" E, F &::= emptyset | E, ell: A ->> B
$

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack (): 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M: B bang E$,
    pad(top: 0.33em)[$Gamma tack lambda x.M: A ->^E B$]
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack punct("val") V: A bang E$
  ),
  onerule(
    name: "TC-Let",
    $Gamma tack M: A bang E$,
    $Gamma, x: A tack N: B bang E$,
    $Gamma tack elet(x, M, N): B bang E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V: A ->^E B$,
    $Gamma tack W: A$,
    $Gamma tack V med W: B bang E$
  ),
  onerule(
    name: "TC-Op",
    $Gamma tack V: A$,
    $Gamma, y: B tack M: C bang E, ell: A ->> B, F$,
    $ell in.not F$,
    $Gamma tack sans("op")(V, y.M): C bang E, sans("op"): A ->> B, F$
  ),
  onerule(
    name: "TC-Hdl",
    $Gamma, x: A, k: B ->^E C tack M: C bang E$,
    $Gamma tack N: C bang E, sans("op"): A ->> B$,
    $Gamma tack punct("with") (sans("op") x med k mapsto M) punct("handle") N:
    C bang E$
  ),
))

== Typing Async-Inbound Effects with Continuations

$
  "Effect types" E, F &::= emptyset | E, sans("op") mapsto (A, F)
$

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack (): 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M: B bang E$,
    pad(top: 0.33em)[$Gamma tack lambda x.M: A ->^E B$]
  ),
  onerule(
    name: "TV-Now",
    $Gamma tack V: A$,
    $Gamma tack punct("now") V: angle(A)$
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack punct("val") V: A bang E$
  ),
  onerule(
    name: "TC-Let",
    $Gamma tack M: A bang E$,
    $Gamma, x: A tack N: B bang E$,
    $Gamma tack elet(x, M, N): B bang E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V: A ->^E B$,
    $Gamma tack W: A$,
    $Gamma tack V med W: B bang E$
  ),
  onerule(
    name: "TC-Await",
    $Gamma tack V: angle(A)$,
    $Gamma tack punct("await") V: A bang E$
  ),
  onerule(
    name: "TC-Prom",
    $E[sans("op")] = (C, F)$,
    $Gamma, x: Sigma[sans("op")], k: angle(C) ->^F A tack M: A bang F$,
    $Gamma, p: angle(C) tack N: B bang E$,
    $Gamma tack eprom("op", x med k, M, p, N): B bang E$
  ),
  onerule(
    name: "TC-Inter",
    $Gamma tack V: Sigma[sans("op")]$,
    $Gamma tack M: A bang E, sans("op") mapsto (A, E)$,
    $Gamma tack einter("op", V, M): A bang E$
  ),
))

= Return Statements? (Unfinished)
- sync-inbound:
  - should they live in the handler or in the operation?
    what would either do/mean?
- async-outbound:
  - how do we formulate a return-rule which respects promise contexts?
    - should the return-computation go under or over the promise context?
    - should the return-computation be able to perform
      operations that can be handled by "inner" promise contexts?

possible perspective:
"the return statement is post-processing on the continuation result"

=> it should go in the handler

= Type Systems (Unfinished)

== Type System <seq-tsys>
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
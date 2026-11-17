#import "toby.typ": scratch
#import "@preview/mannot:0.4.0": markhl
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/cetz:0.5.3": canvas, draw, tree
#import "@preview/ctheorems:2.0.0": *
#show: thm-rules
#import thm-themes.ams: *

#set document(title: [
  Implementing Asynchronous Effects
])

// general formatting
#let grey(x) = markhl(x, color: gray)
#show smallcaps: set text(font: "Latin Modern Roman")
#let punct(x) = text(fill: rgb("#0080ff"), $sans(#x)$)
#let _case-block(label, title, body, bar: gray) = block(
  width: 100%,
  inset: (left: 1em),
  stroke: (left: 0.5pt + bar),
  {
    set par(hanging-indent: 1em)
    [#label #title. #body]
  },
)

#let case(title, body) = _case-block([*Case*], smallcaps(title), body)
#let subcase(title, body) = _case-block([_Subcase_], title, body, bar: luma(180))

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
#let ecase(v, x, m, y, n) = $
  punct("case") #v med {punct("inl") #x => #m | punct("inr") #y => #n}$
#let easync(x, m, n) = $punct("async") #x <- #m punct("in") #n$
#let eprom(op, x, m, p, n) = $
  punct("promise") (sans(#op) #x mapsto #m) punct("as") #p punct("in") #n$
#let epromst(op, x, m, v, p, n) = $
  punct("promise") (sans(#op) #x mapsto #m) med punct("@") med #v punct("as") #p punct("in") #n$
#let einter(op, v, m) = $
  punct("with") med sans(#op)(#v) med punct("interrupt") med #m$
#let eawait(x, v, n) = $punct("await") #x <- #v punct("in") #n$

#let s0 = text(fill: rgb("#0080ff"), $cal(S)_0$)
#let s0l(l) = text(fill: rgb("#0080ff"),
  $cal(S)_0^(text(fill: #black, #l)) med$)
#let reset0(x) = $punct(chevron.l) #x punct(chevron.r)_punct(0)$
#let reset0l(l, x) = $punct(chevron.l) #x punct(chevron.r)^(#l)_punct(0)$
#let bang = $med ! med$

#show math.tack: math.scripts

#show: scratch

= Sequential Fragment <seq>

Ahman and Pretnar's original calculus $lambda_æ$
contains a _sequential_ fragment (for single computations)
and a _parallel_ fragment (for multiple computations in parallel).
Following their lead, I first focus on
the sequential fragment, which I believe contains
the interesting elements of the calculus. We shall revisit
the parallel fragment in @par.

== $lambda_æ$, "Put Simply" <lambda-ae-simply>

We re-present Ahman and Pretnar's $lambda_æ$
with a "streamlined" syntax, semantics, and type system.
We temporarily isolate the sequential fragment
and elide their higher-order extensions.
For brevity, we also elide features from $lambda_æ$
which are orthogonal to the core of asynchronous effects
(namely products, sums, and absurdity).

=== Syntax

*Term-Level*.
We present the calculus in fine-grain call-by-value style.

$
  "Values" V, W &::= x | () | lambda x.M | punct("now") V \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
  | V med W | punct("await") V \
& | eprom("op", x, M, p, N)
  | einter("op", V, M) \
  "Evalutation Contexts " cal(E) &::=
  [.] | elet(x, cal(E), N) | eprom("op", x, M, p, cal(E)) \
  &| einter("op", V, cal(E))\
  "Promise Contexts " cal(P) &::=
  [.] | eprom("op", x, M, p, cal(P)) \
  "Pure Contexts " cal(F) &::=
  [.] | elet(x, cal(F), N) \
$$
  "Variables" x, y, p, q in sans("Var")
  #h(2em)
  "Operation names" sans("op") in Sigma
$

*Values.* Standard values include variables $x$,
the unit value $()$, and functions $lambda x.M$.
The only non-standard value is the
_fulfilled promise_, $punct("now") V$, which denotes that
some previously-made promise has been fulfilled with value $V$.

*Computations*. The standard FGCBV constructs let us
lift values $V$ to computations via $punct("val") V$
and sequence computations $M$ and $N$ via $elet(x, M, N)$.
As usual, we apply functions via $V med W$.

The defining feature of asynchronous effects is
the ability to _promise to handle incoming operations_,
via form $eprom("op", x, M, p, N)$.
On receiving an operation with matching name $sans("op")$, we bind the
payload value to $x$ in $M$ and immediately begin evaluating $M$.
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

We defer discussion of contexts ($cal(E)$, $cal(P)$, and $cal(F)$)
to @seq-opsem, the operational semantics subsection.

*Type-Level.*

$
  "Term Types" A, B ::= 1 | A ->^E B | circle A
  #h(2em)
  "Type Context" Gamma ::= emptyset | Gamma, x: A \
  "Effect Types" E, F ::= emptyset | E, sans("op") : F
  #h(2em)
  "Effect Signature" Sigma ::= emptyset | Sigma, sans("op"): A \
$

*Term Types.* As a base type, we include the unit type $1$.
Function types $A ->^E B$ are annotated with the _effect_ $E$ of the function.
We also have the type $circle A$, read "later $A$", which denotes a term
of type $A$ that will become available _later_, due to a promise being
fulfilled.

*Effect Types.* If a computation has effect $E$, it is prepared to receive
any of the operations in $sans("dom")(E)$.
In contrast to ordinary effect systems,
we must also account for when the body of a promise handler
installs additional promise handers.
Once receiving an operation $sans("op"): F in E$, the computation
may now receive any operations in $F$ _and_
other operations in $E$.

We stipulate that well-formed effect types have no duplicates in their domains
(and are composed only of other well-formed effect types).
Effect types are _unordered_.

Our effect types map operations to _further_ effect types.
They are thus structured as _trees_ (in contrast to ordinary effect
systems, which analogously form _lists_).

*Effect Signature.* We have a global signature $Sigma$ which
statically defines the _payload type_ of every operation.
In a purely sequential system, these payloads can have any type,
i.e. we do not yet need to restrict ourselves to ground types
as do Ahman and Pretnar.

=== Operational Semantics <seq-opsem>

We present a context-based
semantics, which elides or shortcuts many of the "administrative reductions"
of the original.
We restrict our explanation to the semantics here presented,
and leave detailed design considerations to @seq-consid.

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
  punct("await now") V &arrow.squiggly punct("val") V & #smallcaps("E-Await")\
  einter("op", W, punct("val") V)
  &arrow.squiggly
  punct("val") V
  & #smallcaps("E-Disc")
  $$
  &einter("op", V, cal(F)[eprom("op", x, M, p, N)])
  & quad #smallcaps("E-Prom") \
  &arrow.squiggly
  elet(p, M[V\/x], einter("op", V, cal(F)[N])) \
  &einter("op", V, cal(F)[eprom("op'", x, M, p, N)])
  & quad #smallcaps("E-Fwd") \
  &arrow.squiggly
  eprom("op'", x, M, p, einter("op", V, cal(F)[N]))
  &quad ("where" sans("op") eq.not sans("op'")) \
$

*Evaluation Contexts.*
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
$p$ until it resolves to a value, which we enforce with types.

*Promise Contexts.* The rule #smallcaps("E-Val") is non-standard
for an FGCBV system due to the presence of a _promise context_
$cal(P)$ around the value $V$. A promise context is simply
a stack of promise handlers.
In rule #smallcaps("E-Val"), we "lift" this context from the value
onto the continuation $M$. Intuitively, the ordinary rule is insufficient
because promise handlers should not block a pure computation.
This point is discussed further in @seq-consid.

*Other Rules.*
Rule #smallcaps("E-App") is standard.
Rule #smallcaps("E-Await") unwraps a fulfilled promise,
with the side effect of _blocking_ until the promise is fulfilled.
Rule #smallcaps[E-Disc] says that we can discard an $punct("interrupt")$ once it
has reached the trivial computation $punct("val") V$.

The most interesting rules, #smallcaps[E-Prom] and #smallcaps[E-Fwd],
concern promise handlers.
On the left-hand side of each, we have an $punct("interrupt")$
around a $punct("promise")$, with some intermediate pure context $cal(F)$,
which is merely a stack of $punct("let")$-bindings.
(The restriction to _pure_ contexts, as opposed to the broader category
of evaluation contexts, ensures that $punct("interrupt")$s
and $punct("promise")$s do not "pass" each other: we want
the "innermost" $punct("interrupt")$ to react with the "outermost"
$punct("promise")$.)

If the operation names in the interrupt and handler match, we apply
#smallcaps[E-Prom] to rewrite the $punct("promise")$ clause
as a $punct("let")$-binding.
For a promise handler $eprom("op", x, M, p, N)$,
this may "interrupt" the evaluation of $N$ with the evaluation of
$M$. We then follow the standard $punct("let")$-semantics:
once $M$ has evaluated, we bind its result to $p$
and continue evaluating $N$.
We also propagate the interrupt into the continuation $N$, a pattern we name
_deep interrupts_ in reference to deep handlers.
(Shallow interrupts are discussed in @seq-consid.)

If the operation names do _not_ match, we perform an "explicit forward"
via #smallcaps[E-Fwd]: we pull the $punct("promise")$
_outside_ of the interrupt. Doing so opens two possibilities for interaction:
the $punct("promise")$ may now interact with the next-innermost
$punct("interrupt")$, while the $punct("interrupt")$
may now interact with the next-outermost $punct("promise")$.

=== Type System

We begin by reasoning about effect types.
We define a _join_ on effects as follows,
recalling that effects are freely reorderable:

$
  E union.sq emptyset &eq.delta E \
  E union.sq (F, sans("op"): F') &eq.delta (E union.sq F), sans("op"): F'
  & quad (sans("op") in.not sans("dom")(E)) \
  (E, sans("op"): E') union.sq (F, sans("op"): F')
  &eq.delta (E union.sq F), sans("op"): (E' union.sq F')
$

Following Ahman and Pretnar, this operation gives rise to
a _join-semilattice_ structure (bounded by the
identity element $emptyset$). In particular,
operator $union.sq$ is _associative_, _commutative_, and _idempotent_.
#footnote[
  We can induce a partial order on a join-semilattice by defining
  $E subset.eq.sq F$ whenever $E union.sq F = F$.
  For our $union.sq$, this order is precisely the one I go on
  to define, but I write it out explicitly for clarity.
]

We also have a _partial order_ $E subset.eq.sq F$ on effect types,
defined as follows:
#align(center, rule-set(
  onerule(
    $emptyset subset.eq.sq E$
  ),
  onerule(
    $E subset.eq.sq F$,
    $E' subset.eq.sq F'$,
    $E, sans("op"): E' subset.eq.sq F, sans("op"): F'$
  )
))


We now proceed to our typing rules.
We have judgments $Gamma tack V: A$ for values and $Gamma tack M: A bang E$
for computations. All judgments are parameterized by a fixed signature $Sigma$.

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
    $Gamma tack punct("now") V: circle A$
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
    $Gamma tack V: circle A$,
    $Gamma tack punct("await") V: A bang E$
  ),
  onerule(
    name: "TC-Inter",
    $Gamma tack V: Sigma[sans("op")]$,
    $Gamma tack M: A bang E, sans("op"): F$,
    $Gamma tack einter("op", V, M): A bang E union.sq F$
  ),
  onerule(
    name: "TC-Prom",
    $Gamma, x: Sigma[sans("op")] tack M: circle A bang E[sans("op")]$,
    $Gamma, p: circle A tack N: B bang E$,
    $Gamma tack eprom("op", x, M, p, N): B bang E$
  ),
  onerule(
    name: "TC-Sub",
    $Gamma tack M : A bang E$,
    $E subset.eq.sq F$,
    $Gamma tack M : A bang F$
  )
))

All value rules are standard except for #smallcaps[TV-Now],
which merely introduces the "later modality" $circle$.

TODO: discuss computation types, once we're sure the proofs work!

=== Metatheory

*Result Forms.* We begin by considering what the _result forms_
of our calculus are, which differ slightly from
Ahman and Pretnar's.

We distinguish two sorts of result forms: _responsive values_
and _blocked computations_. Intuitively,
blocked computations are explicitly $punct("await")$ing
the resolution of some promise to continue reducing,
whereas responsive values have fully reduced to a value
(but may still handle interrupts).

The form of responsive values is simply $cal(P)[punct("val") V]$.
Defining blocked computations is more involved.
We first write $p hourglass M$ to say that computation
$M$ is waiting on variable $p$, defined as follows:

#align(center)[#rule-set(
  onerule(name: "W-Await", $p hourglass punct("await") p$),
  onerule(
    name: "W-Let",
    $p hourglass M$,
    $p hourglass elet(x, M, N)$
  ),
  onerule(
    name: "W-Inter",
    $p hourglass M$,
    $p hourglass einter("op", V, M)$
  )
)]

We can then define judgment "$Psi "blocks" M$"
as follows, where $Psi$ is a set of variables:

#align(center)[#rule-set(
  onerule(
    name: "B-Wait",
    $p in Psi$,
    $p hourglass M$,
    $Psi "blocks" M$
  ),
  onerule(
    name: "B-Let",
    $Psi "blocks" M$,
    $Psi "blocks" elet(x, M, N)$
  ),
  onerule(
    name: "B-Prom",
    $Psi, p "blocks" N$,
    $Psi "blocks" eprom("op", x, M, p, N)$
  )
)]

Neither of these result forms can reduce:

#lemma[Finality][
  If $M equiv cal(P)[punct("val") V]$ or
  $Psi "blocks" M$, then there is no $N$
  such that $M ~> N$.
]

We also want a couple of lemmas which explicitly relate blocked
computations to pure evaluation contexts:

#lemma[Waiting composition][
  If $p hourglass M$, then $p hourglass cal(F)[M]$.
] <aesimple-waitcomp>

#lemma[Blocking decomposition][
  If $Psi "blocks" M$, then we have that $M equiv cal(F)[N]$
  where either $N equiv eprom("op", x, M', p, N')$
  or $p hourglass N$ for some $p in Psi$.
] <aesimple-blockdecomp>


*Open Reduction.* Since we can reduce underneath promise-binders,
we must consider open terms in more detail than usual
in order to state progress.

Let $Gamma°$ denote a type context where all types
are of form $circle A$,
that is, $Gamma° ::= emptyset | Gamma°, x: circle A$.

We have the following generalized canonical forms lemma,
which degenerates to a more standard one
when $Gamma° = emptyset$. The form of $Gamma°$
restricts the cases where a variable can occur.

#lemma[Canonical forms][
  If $Gamma° tack V : A$, then:
  - if $A equiv 1$, then $V equiv ()$.
  - if $A equiv B ->^E C$, then $V equiv lambda x.M$.
  - if $A equiv circle B$, then either $V equiv punct("now") W$
    or $V equiv x$ for some $x in sans("dom") Gamma°$.
] <aesimple-canon>

*Progress.*
With our result forms and canonical forms lemma,
we are now prepared to state and prove progress.
Our statement must generalize over type contexts $circle Gamma$
because of the $punct("promise")$ evaluation-context case.

#theorem[Progress][
  If $Gamma° tack M : A bang E$, then either $M ~> N$,
  $M equiv cal(P)[punct("val") V]$,
  or $sans("dom")(Gamma°) "blocks" M$.
]

#proof[
  By induction on the typing derivation, as usual.

  #case[TC-Val][
    We have
    #align(center, rule-set(onerule(
      name: "TC-Val",
      $Gamma° tack V: A$,
      $Gamma° tack punct("val") V: A bang E$
    )))
    Our computation $punct("val") V$ is of the form
    $cal(P)[punct("val") V]$ (where $cal(P)=[.]$), so we are done.
  ]

  #case[TC-Let][
    We have
    #align(center, rule-set(prooftree(
      rule(
        name: smallcaps[TC-Let],
        rule($(1)$, $Gamma° tack M: A bang E$),
        $Gamma°, x: A tack N: B bang E$,
        $Gamma° tack elet(x, M, N): B bang E$
      )
    )))

    - By inductive hypothesis on (1), we have three subcases:
    #subcase[$M ~> M'$][
      We can rederive a step via evaluation context
      $elet(x, [.], N)$ as follows:
      #align(center, rule-set(onerule(
        name: "E-Ctx",
        $M ~> M'$,
        $elet(x, M, N) ~> elet(x, M', N)$
      )))
    ]

    #subcase[$M equiv cal(P)[punct("val") V]$][
      Rule #smallcaps[E-Val] gives us
      $elet(x, cal(P)[punct("val") V], N)
      ~> cal(P)[N[V\/x]]$.
    ]

    #subcase[$sans("dom") Gamma° "blocks" M$][
      We show that the $punct("let")$-statement is also blocked:

      #align(center, rule-set(onerule(
        name: "B-Let",
        $sans("dom") Gamma° "blocks" M$,
        $sans("dom") Gamma° "blocks" elet(x, M, N)$
      )))
    ]

    In any subcase, we satisfy one of the conclusions, so the case holds.
  ]

  #case[TC-App][
    We have
    #align(center, rule-set(prooftree(
      rule(
        name: smallcaps[TC-Let],
        rule($(1)$, pad(0.3em)[$Gamma° tack V: A ->^E B$]),
        $Gamma° tack W: A$,
        $Gamma° tack V med W: B bang E$
      )
    )))
    - By @aesimple-canon (canonical forms) on (1),
      $V equiv lambda x.M$.
    - Rule #smallcaps[E-App] gives us
      $(lambda x.M) med W ~> M[W\/x]$,
      satisfying the first conclusion.
  ]

  #case[TC-Await][
    We have
    #align(center, rule-set(prooftree(
      rule(
        name: smallcaps[TC-Await],
        rule($(1)$, $Gamma° tack V: circle A$),
        $Gamma° tack punct("await") V: A bang E$
      )
    )))
    - By @aesimple-canon (canonical forms) on (1),
      we have two subcases:
    #subcase[$V equiv punct("now") W$][
      Rule #smallcaps[TC-Await] gives us the step
      $punct("await now") W ~> punct("val") W$.
    ]
    #subcase[$V equiv p "for" p in sans("dom")(Gamma°)$][
      We show our computation is blocked as follows:
      #align(center, rule-set(prooftree(
        rule(
          name: smallcaps[B-Wait],
          rule($p in sans("dom") Gamma°$),
          rule(
            name: smallcaps[W-Await],
            $p hourglass punct("await") p$
          ),
          $sans("dom") Gamma° "blocks" punct("await") p$
        )
      )))
    ]

    In any subcase, we satisfy one of the conclusions, so the case holds.
  ]

  #case[TC-Inter][
    We have
    #align(center, rule-set(prooftree(
      rule(
        name: smallcaps[TC-Inter],
        $Gamma° tack V: Sigma[sans("op")]$,
        rule($(1)$, $Gamma° tack M: A bang E, sans("op"): F$),
        $Gamma° tack einter("op", V, M): A bang E union.sq F$
      )
    )))
    By inductive hypothesis on (1), we have three subcases:

    #subcase[$M ~> N$][
      We rederive a step via evaluation context
      $einter("op", V, [.])$ as follows:
      #align(center, rule-set(onerule(
        name: "E-Ctx",
        $M ~> N$,
        $einter("op", V, M) ~> einter("op", V, N)$
      )))
    ]

    #subcase[$M equiv cal(P)[punct("val") V]$][
      We further subcase on the structure of $cal(P)$:
      #subcase[$[.]$][
        Rule #smallcaps[E-Disc] gives us
        $einter("op", V, punct("val") W) ~> punct("val") W$.
      ]
      #subcase[$eprom("op'", x, N, p, cal(P))$][
        If $sans("op") = sans("op'")$, then
        rule #smallcaps[E-Prom] gives us a step:
        $
          &einter("op", V, eprom("op", x, N, p, cal(P)[punct("val") V])) \
          ~>& elet(p, N[V\/x], einter("op", V, cal(P)[punct("val") V]))
        $
        If $sans("op") eq.not sans("op'")$, then
        rule #smallcaps[E-Fwd] also gives us a step:

        $
          &einter("op", V, eprom("op'", x, N, p, cal(P)[punct("val") V])) \
          ~>& eprom("op'", x, N, p, einter("op", V, cal(P)[punct("val") V]))
        $
      ]
    ]

    #subcase[$sans("dom") Gamma° "blocks" M$][
      By @aesimple-blockdecomp (blocking decomposition),
      we have that $M equiv cal(F)[N]$ with two further
      subcases on $N$:
      #subcase[$N equiv eprom("op'", x, M', p, N')$][
        If $sans("op") = sans("op'")$, then
        rule #smallcaps[E-Prom] gives us:
        $
          &einter("op", V, cal(F)[eprom("op", x, M', p, N')]) \
          ~>& elet(p, M'[V\/x], einter("op", V, cal(F)[N']))
        $
        If $sans("op") eq.not sans("op'")$, then
        rule #smallcaps[E-Fwd] gives us:
        $
          &einter("op", V, cal(F)[eprom("op'", x, M', p, N')]) \
          ~>& eprom("op'", x, M', p, einter("op", V, cal(F)[N']))
        $
      ]

      #subcase[$p hourglass N$ for $p in sans("dom") Gamma°$][
        By @aesimple-waitcomp (waiting composition),
        we have $p hourglass cal(F)[N]$.
        We conclude the computation is blocked:
        #align(center, rule-set(prooftree(
          rule(
            name: smallcaps[B-Inter],
            rule(
              name: smallcaps[B-Wait],
              $p in sans("dom") Gamma°$,
              $p hourglass cal(F)[N]$,
              $sans("dom") Gamma° "blocks" cal(F)[N]$
            ),
            $sans("dom") Gamma° "blocks" einter("op", V, cal(F)[N])$
          )
        )))
      ]
    ]
    Thus, in any subcase, the computation either steps
    or is blocked.
  ]

  #case[TC-Prom][
    We have
    #align(center, rule-set(prooftree(
      rule(
        name: smallcaps[TC-Prom],
        $Gamma°, x: Sigma[sans("op")] tack M: circle A bang E[sans("op")]$,
        rule($(1)$, $Gamma°, p: circle A tack N: B bang E$),
        $Gamma° tack eprom("op", x, M, p, N): B bang E$
        ),
      )
    ))
    By inductive hypothesis on (1), we have three subcases:

    #subcase[$N ~> N'$][
      We rederive a step via context
      $cal(E) = eprom("op", x, M, p, [.])$ as follows:
      #align(center, rule-set(onerule(
        name: "E-Ctx",
        $N ~> N'$,
        $eprom("op", x, M, p, N) ~> eprom("op", x, M, p, N')$
      )))
    ]

    #subcase[$N equiv cal(P)'[punct("val") V]$][
      Choose our $cal(P)=eprom("op", x, M, p, cal(P)')$.
      Our term is therefore a responsive value,
      of form $cal(P)[punct("val") V]$.
    ]

    #subcase[$sans("dom") Gamma°, p  "blocks" N$][
      We derive that the overall term is still blocked as follows:

      #align(center, rule-set(onerule(
        name: "B-Prom",
        $sans("dom") Gamma°, p  "blocks" N$,
        $sans("dom") Gamma° "blocks" eprom("op", x, M, p, N)$
      )))

    ]
  ]
  #case[TC-Sub][
    The result follows directly by inductive hypothesis.
  ]
]

*Context Typing*. To prove preservation, it is first helpful
to define typing judgments for our various contexts.
Since promise contexts $cal(P)$ and pure contexts $cal(F)$
are _subsets_ of evaluation contexts $cal(E)$,
we present typing rules for $cal(E)$
with the expectation that they can also be used to type
the more specific contexts.

We judge a context $cal(E)$ to be well-typed
via $Gamma tack cal(E): A bang E => B bang F tack.l Gamma°$.
The rules are as follows:

#align(center, rule-set(
  onerule(
    name: "TE-Hole",
    $Gamma tack [.] : A bang E => A bang E tack.l emptyset$
  ),
  onerule(
    name: "TE-Let",
    $Gamma tack cal(E) : A bang E => B bang F tack.l Gamma°$,
    $Gamma, x: B tack N: C bang F$,
    $Gamma tack elet(x, cal(E), N): A bang E => C bang F tack.l Gamma°$
  ),
  onerule(
    name: "TE-Inter",
    $Gamma tack V: Sigma[sans("op")]$,
    $Gamma tack cal(E): A bang E => B bang (F, sans("op"): F') tack.l Gamma° $,
    $Gamma tack einter("op", V, cal(E)):
    A bang E => B bang (F union.sq F') tack.l Gamma°$
  ),
  onerule(
    name: "TE-Prom",
    $Gamma, x: Sigma[sans("op")] tack M: circle C bang F[sans("op")]$,
    $Gamma, p: circle C tack cal(E): A bang E => B bang F tack.l Gamma°$,
    $Gamma tack eprom("op", x, M, p, cal(E)) :
    A bang E => B bang F tack.l Gamma°, p: circle C$
  )
))

The rules are designed to satisfy the following "plugging lemma",
which also ought to serve as the reading of the context typing judgment.

#lemma[Evaluation context plugging][
  If $Gamma tack cal(E) : A bang E => B bang F tack.l Gamma°$
  and $Gamma, Gamma° tack M: A bang E$,
  then $Gamma tack cal(E)[M]: B bang F$.
] <aesimple-eplug>

We also have the usual decomposition lemma:

#lemma[Evaluation context decomposition][
  If $Gamma tack cal(E)[M]: B bang F$,
  then there exist some $A$, $E$, and $Gamma°$ such that
  $Gamma tack cal(E): A bang E => B bang F tack.l Gamma°$
  and $Gamma, Gamma° tack M: A bang E$.
] <aesimple-edecomp>

From these rules, we can derive more specific typing judgments
for more specific contexts.
For promise contexts, we have the following:

#lemma[Promise context typing][
  If $Gamma tack cal(P) : A bang E => B bang F tack.l Gamma°$,
  then $A equiv B$ and $E equiv F$.
]

We thus write $Gamma tack cal(P) : E tack.l Gamma°$
to abbreviate $Gamma tack cal(P) : A bang E => A bang E tack.l Gamma°$.
We have the expected decomposition
and plugging lemmas as corollaries of
@aesimple-edecomp and @aesimple-eplug, respectively:

#lemma[Promise context decomposition][
  If $Gamma tack cal(P)[M]: A bang E$,
  then there exists some $Gamma°$ such that
  $Gamma tack cal(P): E tack.l Gamma°$
  and $Gamma, Gamma° tack M: A bang E$.
] <aesimple-pdecomp>

#lemma[Promise context plugging][
  If $Gamma tack cal(P) : E tack.l Gamma°$
  and $Gamma, Gamma° tack M: A bang E$,
  then $Gamma tack cal(P)[M]: A bang E$.
] <aesimple-pplug>

We have similar lemmas for pure contexts:
#lemma[Pure context typing][
  If $Gamma tack cal(P) : A bang E => B bang F tack.l Gamma°$,
  then $E equiv F$ and $Gamma° equiv emptyset$.
]

We write $Gamma tack cal(F): A => B bang E$
to abbreviate $Gamma tack cal(P) : A bang E => B bang E tack.l emptyset$.

#lemma[Pure context decomposition][
  If $Gamma tack cal(F)[M]: B bang E$,
  then there exists some $A$ such that
  $Gamma tack cal(F): A => B bang E$
  and $Gamma tack M: A bang E$.
] <aesimple-fdecomp>

#lemma[Pure context plugging][
  If $Gamma tack cal(F): A => B bang E$
  and $Gamma tack M: A bang E$,
  then $Gamma tack cal(F)[M]: B bang E$.
] <aesimple-fplug>

*Preservation*.
We are now ready to state and prove preservation:

#theorem[Preservation][
  If $Gamma tack M : A bang E$ and $M ~> N$, then $Gamma tack N : A bang E$.
]

#proof[
  By induction on the derivation of $M ~> N$, as usual.


  #case[$cal(E)[M] ~> cal(E)[N]$][
    - We are given (1) that $M ~> N$.
    - By @aesimple-edecomp (decomposition) on the typing premise,
      we have some $A$, $E$, and $Gamma°$ such that
      (2) $Gamma tack cal(E): B bang F => A bang E tack.l Gamma°$
      and (3) $Gamma, Gamma° tack M: B bang F$.
    - By inductive hypothesis on (1) and (3),
      we get (4) that $Gamma, Gamma° tack N: B bang F$.
    - By @aesimple-eplug (plugging) on (2) and (4),
      we get that $Gamma tack cal(E)[N]: A bang E$
      and we are done.

  ]

  #case[$elet(x, cal(P)[punct("val") V], M) ~> cal(P)[M[V\/x]]$][
    We start with the following,
    using @aesimple-pdecomp (decomposition) on $cal(P)[punct("val") V]$:
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-Let],
          rule(
            name: [@aesimple-pdecomp[]],
            rule($(1)$, $Gamma tack cal(P): E tack.l Gamma°$),
            rule(
              rule($(2)$, $Gamma, Gamma° tack V: A$),
              $Gamma, Gamma° tack punct("val") V: A bang E$
            ),
            $Gamma tack cal(P)[punct("val") V] : A bang E$
          ),
          rule($(3)$, $Gamma, x: A tack M : B bang E$),
          $Gamma tack elet(x, cal(P)[punct("val") V], M) : B bang E$
        )
      )
    ))
    - By substitution & weakening on (2) and (3),
      we get (4) that
      $Gamma, Gamma° tack M[V\/x]: B bang E$.
    - By @aesimple-pplug (plugging) on (1) and (4),
      we get that $Gamma tack cal(P)[M[V\/x]]: B bang E$
      and we are done.
  ]

  #case[$(lambda x.M) med V ~> M[V\/x]$][
    We start with:
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-App],
          rule(
            name: smallcaps[TV-Lam],
            rule($(1)$, $Gamma, x : B tack M: A bang E$),
            pad(top: 0.3em)[$Gamma tack lambda x.M: B ->^E A$]
          ),
          rule($(2)$, $Gamma tack V : B$),
          $Gamma tack (lambda x.M) med V: A bang E$
        )
      )
    ))
    The conclusion follows from substitution on (1) and (2).
  ]

  #case[$punct("await now") V ~> punct("val") V$][
    We start with the derivation on the left
    and conclude on the right:

    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-Await],
          rule(
            name: smallcaps[TV-Now],
            rule($(1)$, $Gamma tack V : A$),
            $Gamma tack punct("now") V: circle A$
          ),
          $Gamma tack punct("await now") V: A bang E$
        )
      ),
      onerule(
        name: "TC-Val",
        rule(name: $(1)$, $Gamma tack V: A$),
        $Gamma tack punct("val") V : A bang E$
      )
    ))
  ]

  #case[$einter("op", V, cal(F)[eprom("op", x, M, p, N)])$\ $
  ~>elet(p, M[V\/x], einter("op", V, cal(F)[N]))$][
    We start with the following,
    using @aesimple-fdecomp (decomposition) as a derived rule:

    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-Prom],
          rule($(1)$, $Gamma, x: Sigma[sans("op")] tack M: circle C bang F$),
          rule($(2)$, $Gamma, p: circle C tack N: B bang E, sans("op"): F$),
          $(3) quad Gamma tack eprom("op", x, M, p, N):
          B bang E, sans("op"): F$
        )
      ),
      prooftree(
        rule(
          name: smallcaps[TC-Inter],
          rule($(4)$, $Gamma tack V: Sigma[sans("op")]$),
          rule(
            name: [@aesimple-fdecomp[]],
            rule($(5)$, $Gamma tack cal(F): B => A bang E, sans("op"): F$),
            $(3)$,
            $Gamma tack cal(F)[eprom("op", x, M, p, N)]:
              A bang E, sans("op"): F$
          ),
          $Gamma tack einter("op", V, cal(F)[eprom("op", x, M, p, N)]):
          A bang E union.sq F$
        )
      )
    ))
    - By substitution on (1) and (4),
      we have (6) $Gamma tack M[V\/x]: circle C bang F$.
    - By @aesimple-fplug (plugging) on (5) and (2),
      alongside weakening on (5),
      we obtain (7) that
      $Gamma, p: circle C tack cal(F)[N]: A bang E, sans("op"): F$.
    - Weakening (4) gives us (8)
      $Gamma, p: circle C tack V: Sigma[sans("op")]$.
    - By definition, we have (9) $F subset.eq.sq E union.sq F$.
    - We derive the conclusion as follows:
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-Inter],
          rule(
            name: $(8)$,
            $Gamma, p: circle C tack V: Sigma[sans("op")]$
          ),
          rule(
            name: $(7)$,
            $Gamma, p: circle C tack cal(F)[N] : A bang E, sans("op"): F$
          ),
          $(10) quad Gamma, p: circle C tack einter("op", V, cal(F)[N]):
          A bang E union.sq F$
        ),
      ),
      prooftree(
        rule(
          name: smallcaps[TC-Let],
          rule(
            name: smallcaps[TC-Sub],
            rule(
              name: $(6)$,
              $Gamma tack M[V\/x]: circle C bang F$
            ),
            rule(name: $(9)$, $F subset.eq.sq E union.sq F$),
            $Gamma tack M[V\/x]: circle C bang E union.sq F$
          ),
          $(10)$,
          $Gamma tack elet(p, M[V\/x], einter("op", V, cal(F)[N])):
          A bang E union.sq F$
        )
      )
    ))
  ]

  #case[$einter("op", V, cal(F)[eprom("op'", x, M, p, N)])$\ $
  ~>eprom("op'", x, M, p, einter("op", V, cal(F)[N]))$][
    We start with the following,
    using @aesimple-fdecomp (decomposition) as a derived rule:

    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-Prom],
          rule($(1)$, $Gamma, x: Sigma[sans("op'")] tack M: circle C bang E[sans("op'")]$),
          rule($(2)$, $Gamma, p: circle C tack N: B bang E, sans("op"): F$),
          $(3) quad Gamma tack eprom("op'", x, M, p, N):
          B bang E, sans("op"): F$
        )
      ),
      prooftree(
        rule(
          name: smallcaps[TC-Inter],
          rule($(4)$, $Gamma tack V: Sigma[sans("op")]$),
          rule(
            name: [@aesimple-fdecomp[]],
            rule($(5)$, $Gamma tack cal(F): B => A bang E, sans("op"): F$),
            $(3)$,
            $Gamma tack cal(F)[eprom("op'", x, M, p, N)]:
              A bang E, sans("op"): F$
          ),
          $Gamma tack einter("op", V, cal(F)[eprom("op'", x, M, p, N)]):
          A bang E union.sq F$
        )
      )
    ))
    - By @aesimple-fplug (plugging) on (5) and (2),
      alongside weakening on (5),
      we obtain (6) that
      $Gamma, p: circle C tack cal(F)[N]: A bang E, sans("op"): F$.
    - By definition, (7)
      $E[sans("op'")] subset.eq.sq (E union.sq F)[sans("op'")]$.
    - Weakening (4) gives us (8)
      $Gamma, p: circle C tack V: Sigma[sans("op")]$.
    - We derive the conclusion as follows:
    #align(center, rule-set(
      prooftree(
        rule(
          name: smallcaps[TC-Inter],
          rule(
            name: $(8)$,
            $Gamma, p: circle C tack V: Sigma[sans("op")]$
          ),
          rule(
            name: $(6)$,
            $Gamma, p: circle C tack cal(F)[N]: E, sans("op"): F$
          ),
          $(9) quad Gamma, p: circle C tack einter("op", V, cal(F)[N]):
            A bang E union.sq F$
        ),
      ),
      prooftree(
        rule(
          name: smallcaps[TC-Prom],
          rule(
            name: smallcaps[TC-Sub],
            rule(
              name: $(1)$,
              $Gamma, x: Sigma[sans("op'")] tack M: circle C bang
              E[sans("op'")]$
            ),
            rule(
              name: $(7)$,
              $E[sans("op'")] subset.eq.sq (E union.sq F)[sans("op'")]$
            ),
            $Gamma, x: Sigma[sans("op'")] tack M: circle C bang
              (E union.sq F)[sans("op'")]$
          ),
          $(9)$,
          $Gamma tack eprom("op'", x, M, p, einter("op", V, cal(F)[N])):
          A bang E union.sq F$
        )
      )
    ))
  ]
]

=== Design Considerations <seq-consid>

== Extended Handlers <aehext>

We consider the extension of $lambda_æ$ with
_stateful_ and _reinstallable_ interrupt handlers.
To avoid repetition, we only discuss
the changes made to the language of @lambda-ae-simply.

=== Promise Handlers

We extend the form of promise handlers to the following:
$
  epromst("op", x med r med s, M, V, p, N)
$
Handling now binds two additional variables in $M$.
We can _reinstall_ the promise handler via $r$,
and $s$ represents the _state_ of the handler.
The initial state is given by $V$.

The semantics for handling a promise is extended to bind these
two additional variables:

$
  &einter("op", V, cal(F)[epromst("op", x med r med s, M, W, p, N)]) \
  ~>
  &elet(p, M[V\/x, V_r\/r, W\/s], einter("op", V, cal(F)[N])) \
  &(V_r eq.delta lambda y.epromst("op", x med r med s, M, y, p, punct("val") p))
$

The reinstaller $r$ is realized as a function which takes an updated state value as argument, recreates the original promise handler
with the new state, and returns the corresponding promise variable.
The _current_ state value $W$ is simply bound to $s$ in $M$.

We can type these extended handlers via the following rule:

#align(center, rule-set(onerule(
  name: "E-PromRS",
  $Gamma tack V: A$,
  $E' subset.eq.sq E[sans("op")]$,
  $Gamma, x: Sigma[sans("op")],
  r: A -->^(sans("op"): E') circle C, s: A tack
  M: circle C bang E'$,
  $Gamma, p: circle C tack N: B bang E$,
  $Gamma tack epromst("op", x med r med s, M, V, p, N):
  B bang E$
)))

=== Recursive Types

Consider the handler which always reinstalls itself:
$
  eprom("op", x med r, r (), p, N)
$
This should have the effect type
$[sans("op") mapsto [sans("op") mapsto [sans("op") mapsto ...]]]$,
ad infinitum.

Ahman and Pretnar model these infinite
effect types via a greatest fixed point.
To work in a DSL of effect types, we must explicitly
consider recursion. We want to write the above type as
$mu epsilon . [sans("op") mapsto epsilon]$.

$
  E &::= angle(rho) | epsilon | mu epsilon . E \
  rho &::= emptyset | rho, sans("op"): E
$

We must forbid _non-contractive_ types of form e.g. $mu epsilon . epsilon$.

Our join algorithm now has the following case,
and is no longer obviously terminating:

$
  angle(rho) union.sq mu epsilon. F eq.delta angle(rho) union.sq F[mu epsilon. F\/ epsilon]
$

(to be continued...)

= Continuations <cont>

= Parallel Fragment <par>

= Asynchrony & Inbound Effects <inbound>

= Inbound Effects are Delimited Control <dc>

= Non-Deterministic Concurrency <ndc>

= Peeling Back the Layers

Starting with Ahman and Pretnar's asynchronous effects,
we progressively strip away inessential features to reach
the core operational insight _beyond_ asynchrony: the _inversion of effect flow_.

== $lambda_æ$, "Put Simply"

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
  grey("Pure Contexts " cal(F)) &::=
  [.] | elet(x, M, cal(F)) \
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
    $alpha angle(M) arrow.squiggly alpha angle(N)$
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

*Abstraction*. I conjecture that this translation preserves an
operational correspondence, but that it breaks full abstraction
_for effectful programs_, i.e. those with undelimited $punct("handle")$s
in the inbound language or those with unhandled $punct("perform")$s
in the outbound language.

For instance, consider
$#trans($punct("handle") (sans("op") x mapsto M)$)
  &eq.delta
  punct("perform") sans("op")(lambda x.#trans($M$))$.
We know that the $punct("handle")$ will always step to $elet(y, M[V\/x], ...)$
for some $V$ given by an injection.
However, we can easily put the $punct("perform")$ in a context where this is not the case:
$
  punct("with") (sans("op") x mapsto punct("val") W)
  punct("handle") punct("perform") sans("op")(lambda x.#trans($M$))
  ~> punct("val") W
$

We perform $sans("op")(lambda x.#trans($M$))$ with the expectation that
the $lambda$ will immediately be invoked with some value,
but this is not necessarily the case in the target language!
A "foreign" handler can ignore it (as above), invoke it multiple times,
recurse infinitely, etc...

In short, the difference between the two languages
is that, in an outbound-effect setting, the delimiter
"gains control" after a shift, while
in an inbound-effect setting, the _shift_ "gains control".
This difference matters when an abstraction boundary separates
a delimiter and a shift.


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

=== Examples

We reintroduce the ability for handlers to _reinstall_ themselves
(with state),
via the following rule (extending the one above):

$
  &einter("op", V, cal(E)[
    epromst("op", x med k med r med s, M, W, p, N)
  ]) \
  &arrow.squiggly
  M[...,
    W \/ s,
    (lambda y.epromst("op", x med k med r med s,
    M, y, q, sans("val") q))
    \/ r]
$

*Pre-Emptive Concurrency.*
Ahman and Pretnar give the example of "pre-emptive multithreading" for
continuation-less asynchronous effects.
We have two operations, $sans("stop"): 1$ and $sans("go"): 1$,
which pause and resume a computation.
This takes the form of the following
handler:
$
  &punct("let") "waitForStop" () = \
  &quad eprom("stop", \_ med r, \
  &quad quad eprom("go", \_, punct("val now") (), q, \
  &quad quad punct("await") q \; r () \
  &quad), p, punct("val") p)
$

To allow a computation $M$ to be pre-empted, we simply write
$"waitForStop"\; M$.

This example is limited in that, when we $sans("stop")$ the computation,
the thread cannot do any other work:
it remains paused until receiving $sans("go")$.
If each thread is running on its own machine, that machine's resources are
being wasted, which defeats (some of?) the point of concurrency.
If these are simply conceptual threads being run on the same machine,
then we are relying on an external scheduler to determine which thread
ought to gain control of the machine— and that scheduler is not expressible
in the language itself.

When I hear pre-emptive concurrency, I imagine
something like the following sequence:
- Computation $M$ is running on thread $T$.
- Thread $T$ receives a signal.
- In response, thread $T$ suspends $M$ and begins computation $N$.

In this sequence, $T$ splits its time/resources between $M$ and $N$.
This is (properly) concurrency.

Using continuations, we can express such behavior as follows.
We have one operation, $sans("swap"): 1$.

$
  &punct("let") "preempt" m med n = epromst("swap", \_ med k med r med s,
  r med k semi s med (), n, \_, m med ())
$

Our two arguments $m$ and $n$ are thunks ($lambda ().M$ and $lambda ().N$)
of type $1 -> A$.
We start off running $M$.
When we receive a $sans("swap")$ interrupt, we:
- store the continuation $k$ for later via a stateful reinstall, and
- invoke the currently stored continuation $s$.
Thus, after receiving our first interrupt, we store $M$ and begin running $N$.
We alternate between them whenever receiving a $sans("swap")$, as expected.

We can easily adapt/generalize this to:
- abort the current computation entirely (by discarding $k$),
- store a queue of thunks instead of a single one, letting us swap between
  any number of computations instead of only two,
- implementing any sort of logic in the handler body, e.g. prioritizing
  some computations over others,
- receiving a thunk _from the interrupt payload_ (unused above)
  and running it immediately, or queuing it, etc...

*Reduction Sequence*. Suppose we start with two computations
$M_0$ and $N_0$, and we have that $M_0 ~> M_1 ~> M_2 ~> ...$,
and likewise for $N$.

Throughout, we box the redex. We omit mention of $punct("now")$
for conciseness, since this has no expressive significance (its purpose
is to guarantee safety).

We initiate the pre-emptive behavior as follows.
$
  &"preempt" (lambda ().M_0) med (lambda ().N_0) \
  eq.delta&  epromst("swap", \_ med k med r med s,
  r med k semi s med (), (lambda ().N_0), \_,
    #rect($(lambda ().M_0) med ())$)) \
  ~>& epromst("swap", \_ med k med r med s,
  r med k semi s med (), (lambda ().N_0), \_,
    #rect($M_0$)) \
  ~>^m& epromst("swap", \_ med k med r med s,
  r med k semi s med (), (lambda ().N_0), \_,
    #rect($M_n$)) \
$

We start off by evaluating $M$ for some number $m$ of steps.
Let us now say that we receive an interrupt "from the outside world",
i.e. nondeterministically, which I denote via a $~>^!$ step:

$
  ~>^!& #rect($einter("swap", , epromst(
    "swap", \_ med k med r med s,
  r med k semi s med (), (lambda ().N_0), \_,
    #rect($M_m$)))$) \
$

At this point, we have _two_ possible redexes. We may continue
reducing $M$ as before, by evaluation context
$cal(E)=einter("swap", , epromst(
  "swap", \_ med k med r med s, ..., V, \_,
  [.]))$.
Alternatively, we may handle the interrupt (with $cal(E)=[.]$).
For the sake of example, we immediately choose the latter:

$
  &~> (r med k\; s med ()) cases(delim: "[",
    (lambda ().N_0) \/ s,
    (lambda ().einter("swap", , M_m)) \/ k,
    (lambda s'.epromst("swap", \_ med k med r med s,
      r med k\; s med (), s', p, sans("val") p)) \/ r
  ) \
  &= #rect($(lambda s'.epromst("swap", \_ med k med r med s,
      r med k\; s med (), s', p, sans("val") p))
      (lambda ().einter("swap", , M_m))$)med \;\
  &quad quad (lambda ().N_0) med () \
  &~> #rect($epromst("swap", \_ med k med r med s,
      r med k\; s med (), (lambda ().einter("swap", , M_m)),
       p, sans("val") p) \; (lambda ().N_0) med ()$) \
  &~> epromst("swap", \_ med k med r med s,
      r med k\; s med (), (lambda ().einter("swap", , M_m)),
       p, #rect($(lambda ().N_0) med ()$)) \
  &~> epromst("swap", \_ med k med r med s,
      r med k\; s med (), (lambda ().einter("swap", , M_m)),
       p, #rect($N_0$)) \
  &~>^n epromst("swap", \_ med k med r med s,
    r med k\; s med (), (lambda ().einter("swap", , M_m)),
      p, #rect($N_n$))
$

By the end of this sequence, we have begun to evaluate the stored computation
$N$.

Say after $n$ such steps, we receive another $sans("swap")$:

$
  ~>^!& #rect($einter("swap", , epromst(
    "swap", \_ med k med r med s,
  r med k semi s med (), (lambda ().einter("swap", , M_m)), \_,
    #rect($N_n$)))$) \
$
We again are free to either reduce $N$ further or handle the interrupt.
Again, for the sake of example, we immediately handle as follows:

$
  &~> (r med k\; s med ()) cases(delim: "[",
    (lambda ().einter("swap", , M_m)) \/ s,
    (lambda ().einter("swap", , N_m)) \/ k,
    (lambda s'.epromst("swap", \_ med k med r med s,
      r med k\; s med (), s', p, sans("val") p)) \/ r
  ) \
  &= #rect($(lambda s'.epromst("swap", \_ med k med r med s,
      r med k\; s med (), s', p, sans("val") p))
      (lambda ().einter("swap", , N_n))$)med \;\
  &quad quad (lambda ().einter("swap", , M_m)) med () \
  &~> #rect($epromst("swap", \_ med k med r med s,
      r med k\; s med (), (lambda ().einter("swap", , N_n)),
       p, sans("val") p) \; \
  (lambda ().einter("swap", , M_m)) med ()$) \
  &~> epromst("swap", \_ med k med r med s,
      r med k\; s med (), (lambda ().einter("swap", , N_n)),
       p, \
  &quad quad #rect($(lambda ().einter("swap", , M_m)) med ()$)) \
  &~> epromst("swap", \_ med k med r med s,
      r med k\; s med (), (lambda ().einter("swap", , N_n)),
       p, \
  &quad quad #rect($einter("swap", , M_m)$))
$

We are (essentially) back to where we started, with $M_m$ is in redex position.

*Shallow Interrupts*. We are not _exactly_ back to where we started:
instead of $M_m$, we have $einter("swap", , M_m)$.
This is due to the fact that our semantics implements _deep_ interrupts,
where upon handling, the interrupt is propagated inside the continuation $k$.

It may be preferable to implement this example with _shallow_
interrupts, wherein the continuation is exactly $lambda p.cal(E)[N]$,
with no interrupt. (In the first handling in the
above example, we would have $lambda ().M_m\/k$).
This would recover _exactly_ $M_m$ after two $sans("swaps")$,
instead of $einter("swap",, M_m)$.

Shallow handlers are not necessary for this example.
In particular, if $M$ and $N$ have no $sans("swap")$ handlers,
the propagated interrupt will be discarded, and the deep/shallow reductions
will coincide. The consequence of deep handlers is that _further_ swaps within
$M$ and $N$ themselves may occur: whether this behavior is desired or not
seems to be use-case dependent.

*Typing*. This is our complete typing rule for promises (assuming our semantics
wraps the continuation argument in $punct("now")$, instead of the
programmer doing it themselves):

#align(center, rule-set(
  onerule(
    name: "TC-Prom",
    $E[sans("op")] = (C, F)$,
    $Gamma, x: Sigma[sans("op")], k: C ->^F A, r: D ->^(op |-> F) angle(C),
      s: D tack M: A bang F$,
    $Gamma tack V: D$,
    $Gamma, p: angle(C) tack N: B bang E$,
    $Gamma tack epromst("op", x med k med r med s, M, V, p, N):
    B bang E$
  )
))

Define $epsilon = mu alpha. sans("swap") mapsto (A, alpha)$.
The term preempt then typechecks as follows,
assuming the answer type coincides with the function return type
(i.e. the interrupts and handler exist at the "top level"
of the computation).

#align(center, rule-set(
  prooftree(vertical-spacing: 5pt,
    rule(
      rule(
        $Gamma,
        k: 1 ->^epsilon A,
        r: (1 ->^epsilon A) ->^(sans("swap") |-> (A, epsilon)) angle(1),
        s: 1 ->^epsilon A tack r med k semi s med (): A bang epsilon$
      ),
      $Gamma tack n: 1 ->^epsilon A$,
      $Gamma tack m: 1 ->^epsilon A$,
      $Gamma tack epromst("swap", \_ med k med r med s,
    r med k semi s med (), n, \_, m med ()): A bang epsilon$
    )
  )
))

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

== Value Injection <delim-value>

We take the language of @delim-multi
and extend resets with the ability to pass values to shifts.

=== Syntax

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
    | V med W | reset0l(ell, V >> M)| s0l(ell) x med k.M \
  "Evaluation contexts" cal(E) &::= [.] | elet(x, cal(E), N)
    | angle(V >> cal(E))^ell_0 \
  "Types" A, B, C &::= 1 | A ->^E B \
  "Effect types" E, F &::= emptyset | E, ell: A arrow.b.twohead B
$

Values and basic computations remain the same as @delim-multi.
We extend resets $reset0l(ell, V >> M)$ to contain a value $V$.
We extend shifts $s0l(ell) x med k.M$ to bind an additional variable $x$
in $M$.

Effect types still take the form of an ordered list, but
we extend their entries to the form $ell: A arrow.b.twohead B$.
Here, $A$ is the type of the value provided by $ell$,
while $B$ is the answer type of the computation (as seen in prior sections).

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
  reset0l(ell, V >>punct("val") W) &arrow.squiggly punct("val") W
  & #smallcaps[E-Reset]\
  reset0l(ell, V >> cal(E)[s0l(ell) x med k.M])
  &arrow.squiggly
  M[V\/x, (lambda y.reset0l(ell, V >> cal(E)[punct("val") y]))\/k]
  quad (ell in.not cal(E))
  & quad #smallcaps[E-Shift]\
$

The only rule which significantly changes from @delim-multi
is #smallcaps[E-Shift], where we substitute provided value $V$ for $x$ in
the shift-body $M$.
When reinstalling the reset in the continuation, we do so with the same value.
Discarding a reset (#smallcaps[E-Reset]) ignores the value.

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
    $Gamma tack M: B bang E, ell: A arrow.b.twohead B$,
    $Gamma tack reset0l(ell, V >> M): B bang E$
  ),
  onerule(
    name: "TC-Shift",
    $Gamma, x: A, k: C ->^E B tack M: B bang E$,
    $ell in.not F$,
    $Gamma tack s0l(ell) x med k.M: C bang E, ell: A arrow.b.twohead B, F$
  ),
))

Again, only rules #smallcaps[TC-Reset] and #smallcaps[TC-Shift] change from
@delim-multi.
In #smallcaps[TC-Reset], we extend (bottom-up) the effect type with
$A arrow.b.twohead B$, where $A$ is the type of the provided value $V$
and $B$ is the answer type (as before).
In #smallcaps[TC-Shift], when typing the body $M$, we extend the context
with the continuation $k$ as before, but also add $x: A$,
where $A$ is given by the left-hand side of the effect type.

=== Relation to Previous Sections

First and foremost: this is _exactly_ the inbound effects of @sync-inbound,
with a different coat of paint.

This system degenerates to that of @delim-multi if we only ever provide the
unit value via resets.

In principle, a label-less system (i.e. @delim-basic)
can similarly be extended with "value injection."
I do not consider this explicitly, since the usefulness of such an extension
is questionable (a single shift would only be able to receive values from
the nearest reset).
If we want to e.g. compose translations, this language might nevertheless
be worth writing out.

I also suspect that value injection is macro-expressible in a simpler system.
Broadly, we encode shift-bodies as abstractions over their non-continuation
variable, and resets immediately apply that function to their value.

== Aside: Local and Global Signatures

Most simply-typed effect systems involve a _global signature_
for operations, which ensures that an operation name _always_
has the same output and return types.
The reader may have noticed that, in the previous subsection,
we have no such signature: type information is, in a sense, _local_.

I argue here that sound typing is doable without a global signature.
I add a global signature to @delim-value as a _specialization_,
and I remove global signatures from ordinary outbound effect handlers
as a _generalization_.

The ramifications of local typing _beyond_ mere soundness
are likewise beyond me. I suspect there are other worthy reasons,
such as programmer convenience, links to the free-monad interpretation,
algorithmic typechecking, etc. to have a global signature.

=== Outbound Global Signatures

We briefly recap the role of a signature in a simply-typed (outbound)
effect handler calculus. We define our signature
$Sigma ::= emptyset | Sigma, sans("op"): A ->> B$ and
implicitly parameterize all typing judgments by a fixed $Sigma$.

The key rules (for performing and handling operations, respectively)
are as follows:

#align(center, rule-set(
  onerule(
    $sans("op"): A ->> B in Sigma$,
    $Gamma tack V: A$,
    $Gamma tack sans("op")(V): B bang E union {sans("op")}$
  ),
  onerule(
    $sans("op"): A ->> B in Sigma$,
    $F = E \\ {sans("op")}$,
    $Gamma, x: A, k: B ->^F C tack M: C bang F$,
    $Gamma tack N: C bang E$,
    $Gamma tack sans("with") (sans("op") x med k mapsto M) sans("handle") N:
      C bang F$
  ),
))

In both rules, we must access $Sigma$ to learn how to type the term.

=== Inbound Global Signatures

In the type system of @delim-value, we had no such global information.
Instead, we _locally accumulated_ a signature through the type derivation.
Recall the #smallcaps[TC-Reset] rule:

#align(center, rule-set(
  onerule(
    name: "TC-Reset",
    $Gamma tack V: A$,
    $Gamma tack M: B bang E, ell: A arrow.b.twohead B$,
    $Gamma tack reset0l(ell, V >> M): B bang E$
  ),
))

We first determine the type $A$ of the injected value $V$.
Then, when typechecking the body $M$, we associate label $ell$
with $A$ via the effect type. When typing a shift $s0l(ell) x med k.N$
inside of $M$, we then know that the free variable $x$ should have type $A$.

Alternatively, we could _globally fix_ such $A$. Define our signature
$Sigma ::= emptyset | Sigma, ell: A$, and implicitly parameterize all typing
judgments by a fixed $Sigma$.
We remove this information from local effect types $E ::= emptyset | E, ell: A$,
i.e. we revert to the local effect-typing system of @delim-multi.
The reset and shift rules become:

#align(center, rule-set(
  onerule(
    name: "TC-Reset*",
    $ell : A_ell in Sigma$,
    $Gamma tack V: A_ell$,
    $Gamma tack M: B bang E, ell: B$,
    $Gamma tack reset0l(ell, V >> M): B bang E$
  ),
  onerule(
    name: "TC-Shift*",
    $ell : A_ell in Sigma$,
    $Gamma, x: A_ell, k: C ->^E B tack M: B bang E$,
    $ell in.not F$,
    $Gamma tack s0l(ell) x med k.M: C bang E, ell: B, F$
  ),
))

As in @delim-multi, we still track answer types alongside labels. The
injected-value types, however, are now given by $Sigma$.

This system is _more conservative_ than the purely-local system.
For instance, the following term is well-typed via the purely-local
system, but there exists no well-formed $Sigma$ that admits it under
the global system:

$
  reset0l(ell, 1 >> reset0l(ell, #raw("\"hello\"") >> s0l(ell) x med k. x))
$

The issue under a global signature is that we associate the same label $ell$
with two different injection types ($sans("Int")$ and $sans("Str")$).
This poses no difficulty under a local system: when assigning a type
to $x$, we simply take the most recent entry in our local signature
($sans("Str")$).

*Fixing Answer Types*. If we like, we can similarly fix the answer types
of resets in a global signature. In other words, every reset with label $ell$
must have the same type $A$.

To do so, we again move information from our local effect type $E$ to our
signature $Sigma$. The signature now has form
$Sigma ::= emptyset | Sigma, ell: A arrow.b.twohead B$,
where $A$ is the injected value type and $B$ is the answer type.
Our effect types $E$ are now just lists of labels.
(Order still matters when we want to account for bypassed non-matching labels.)

#align(center, rule-set(
  onerule(
    name: "TC-Reset**",
    $ell : A arrow.b.twohead B in Sigma$,
    $Gamma tack V: A$,
    $Gamma tack M: B bang E, ell$,
    $Gamma tack reset0l(ell, V >> M): B bang E$
  ),
  onerule(
    name: "TC-Shift**",
    $ell : A arrow.b.twohead B in Sigma$,
    $Gamma, x: A, k: C ->^E B tack M: B bang E$,
    $ell in.not F$,
    $Gamma tack s0l(ell) x med k.M: C bang E, ell, F$
  ),
))

Such a system would rule out the following term,
since the two resets have irreconcilable answer types
($sans("Int")$ and $sans("Str")$):
$
  reset0l(ell, sans("intToStr") reset0l(ell, 1))
$

*Which Approach is Best?* Ahman and Pretnar fix injected types with a signature
but let answer types vary (i.e. they adopt #smallcaps[TC-Reset\*] and
#smallcaps[TC-Shift\*] above).

To me, fixing answer types seems much too restrictive.
I am undecided whether letting injected types vary is helpful enough to
outweigh any downsides (and I am unsure of any practical downsides).

=== Local-Signature Outbound Effects

The "local-signature" approach is readily adaptable to
an otherwise traditional outbound system. The syntax and type system
are as follows:

$
  "Values" V, W &::= x | () | lambda x.M \
  "Computations" M, N &::= punct("val") V | elet(x, M, N) | V med W  \
    &| sans("op")(V)
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
    $ell in.not F$,
    $Gamma tack sans("op")(V): B bang E, sans("op"): A ->> B, F$
  ),
  onerule(
    name: "TC-Hdl",
    $Gamma, x: A, k: B ->^E C tack M: C bang E$,
    $Gamma tack N: C bang E, sans("op"): A ->> B$,
    $Gamma tack punct("with") (sans("op") x med k mapsto M) punct("handle") N:
    C bang E$
  ),
))

Rule #smallcaps[TC-Hdl] introduces entry $sans("op"): A ->> B$ to the effect
type in the handled computation $N$,
where $A$ is the parameter type of the operation and $B$ is the result type.
Rule #smallcaps[TC-Op] uses this (local!) information to ensure its argument
is well-typed and to determine the result type.

== Typing Async-Inbound Effects with Continuations

Adapting our approach to _asynchronous_ effects poses a particular challenge:
our strategy of ordering labels in a list no longer applies.
A computation may be prepared to receive more than one interrupt at a time,
and the act of receiving may introduce _new_ handlers for further interrupts.

Thankfully, the adaptation turns out fairly simple: effect types are now _trees_
instead of lists.

$
  "Effect types" E, F &::= emptyset | E, sans("op") mapsto (A, F)
$

If a computation has effect type $E$, it will handle all interrupts
in its domain $sans("dom")(E)$.

If $sans("op") mapsto (A, F) in E$ and a computation with effect type $E$
handles $sans("op")$, it will _then_ handle all interrupts in $F$
_and_ those in $E$ except for $sans("op")$. ($F$ types the handlers that are
installed by the $sans("op")$ handler.)

This local effect context also tracks the answer type $A$ of the
enclosing interrupt, which is needed to type the continuation.

We introduce a global signature
$Sigma ::= emptyset | Sigma, sans("op") mapsto A$ to type interrupt payloads.
As usual, all typing judgments are implicitly parameterized by a fixed $Sigma$.

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
    $Gamma, x: Sigma[sans("op")], k: angle(C) -->^(E, F) A tack M: A bang E,F$,
    $Gamma, p: angle(C) tack N: B bang E$,
    $Gamma tack eprom("op", x med k, M, p, N): B bang E$
  ),
  onerule(
    name: "TC-Inter",
    $Gamma tack V: Sigma[sans("op")]$,
    $Gamma tack M: A bang E, sans("op") mapsto (A, F)$,
    $Gamma tack einter("op", V, M): A bang E, F$
  ),
))

= Non-Deterministic Concurrency

Isolating the "asynchronous" part of asynchronous effects.

== First-Class Asynchrony

=== Syntax

The language is a $lambda$-calculus in a fine-grain call-by-value style.
It lacks a $punct("let")$ statement: instead,
we _decompose_ $punct("let")$s into two distinct constructs,
$punct("async")$ and $punct("await")$.
The $punct("async")$ construct introduces non-deterministic concurrency,
and its behavior is constrained (sequenced) by $punct("await")$.

Values $punct("now") V$ represent the result of a concurrent computation,
which have the "later type" $circle A$.
The $punct("await")$ construct eliminates $punct("now")$ and $circle$.

Evaluation contexts are notable for permitting reduction
under _both_ subcomputations of $punct("async")$.
This induces nondeterminism, in that whenever we have
an $punct("async")$ construct, we can choose which subcomputation
to reduce (unless one is blocked by an $punct("await")$).

$
  "Values" V, W &::= x | () | lambda x.M | punct("now") V \
  "Computations" M, N &::= punct("val") V | easync(x, M, N)
  | V med W | eawait(x, V, M) \
  "Evaluation Contexts" cal(E) &::=
  [.] | easync(x, cal(E), N) | easync(x, M, cal(E)) \
  "Types" A, B &::= 1 | A -> B | circle A
$

=== Typing Rules

We have judgments $Gamma tack_v V : A$ for values
and $Gamma tack_m M : A$ for computations.
Rules are as expected.

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $x: A in Gamma$,
    $Gamma tack_v x: A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack_v (): 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack_m M: B$,
    $Gamma tack_v lambda x.M: A -> B$
  ),
  onerule(
    name: "TV-Now",
    $Gamma tack_v V: A$,
    $Gamma tack_v punct("now") V: circle A$
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack_v V: A$,
    $Gamma tack_m punct("val") V: A$
  ),
  onerule(
    name: "TC-Async",
    $Gamma tack_m M: A$,
    $Gamma, x: circle A tack_m N: B$,
    $Gamma tack_m easync(x, M, N): B$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack_v V: A -> B$,
    $Gamma tack_v W: A$,
    $Gamma tack_m V med W: B$
  ),
  onerule(
    name: "TC-Await",
    $Gamma tack_v V: circle A$,
    $Gamma, x: A tack_m M: B$,
    $Gamma tack_m eawait(x, V, M): B$
  ),
))

=== Operational Semantics

#align(center, rule-set(onerule(
  name: "EC-Ctx",
  $M ~> N$,
  $cal(E)[M] ~> cal(E)[N]$
)))

$
  easync(x, punct("val") V, M) &~> M[punct("now") V\/x] & #smallcaps[E-Val]\
  eawait(x, punct("now") V, M) &~> M[V\/x] & quad #smallcaps[E-Await]\
  (lambda x.M) med V &~> M[V\/x] & #smallcaps[E-App]\
$

=== Discussion

It is easy to see that this language is type-safe by progress and preservation.
I conjecture that the language is both confluent and terminating,
although this is slightly tricky to prove because of the nondeterminism.

*Relations to other calculi.*
The asynchronous calculus _generalizes_ the standard synchronous FGCBV calculus
as follows:
$
  trans(elet(x, M, N)) eq.delta easync(p, M, (eawait(x, p, N)))
$

We can translate the calculus into Fowler et al.'s $lambda_("ch")$ as follows:

$
  trans(easync(x, M, N)) &eq.delta
  elet(x, punct("newCh"),(
    punct("spawn") (elet(r, trans(M), punct("give") r med x)) \;
    trans(N))) \
  trans(eawait(x, V, M)) &eq.delta
  elet(x, punct("take") trans(V),
  (punct("give") x med trans(V); trans(M)))
$

*Relation to asynchronous effects.*
Ahman and Pretnar's asynchronous effects is _not_ given by the mere combination
of these $punct("async")$ constructs with generalized delimited control.
Intuitively, both of these features mess with evaluation contexts,
and getting their combination right is tricky and error-prone.

The obvious problem is scope-escape, as with $x$ in the following example:

$
  &reset0(easync(x, M, s0 k. eawait(y, x, punct("val") y)))
  ~> &eawait(y, x, punct("val") y)
$

In general, shifting past $punct("async")$ binders is clearly unsound.

Ahman and Pretnar's bubbling semantics addresses this issue by propagating
promises _outside_ of delimiters before any shifts can occur.
The promise-bound variables are therefore in scope of shifts.

With all that said, an adequately nuanced language should satisfy:
$
  trans(eprom("op", x med k, M, p, N))
  eq.delta
  easync(p, punct("handle") ("op" x med k mapsto M), N)
$

== An Adequate Semantics for AE

My earlier semantics for asynchronous effects suffers from this scope-escape
problem. I reformulate a fixed version here.

=== Syntax

$
  "Values" V, W &::= x | () | lambda x.M | (V, W) | punct("now") V \
  "Computations" M, N &::= punct("val") V | elet(x, M, N)
  | V med W | punct("fst") V | punct("snd") V \
& | eprom("op", x, M, p, N)
  | punct("await")(V) \
& | einter("op", V, M) \
  grey("Promise Contexts " cal(P)) &::=
  [.] | eprom("op", x, M, p, cal(P)) \
  grey("Pure Contexts " cal(F)) &::=
  [.] | elet(x, cal(F), M) \
  grey("Evalutation Contexts " cal(E)) &::=
  [.] | elet(x, cal(E), M) | eprom("op", x, M, p, cal(E)) \
  & | einter("op", V, cal(E))\
  "Variables" x, y, p, q &in sans("Var") \
  "Operation names" sans("op") &in Sigma
$

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
  einter("op", W, punct("val") V)
  &arrow.squiggly
  punct("val") V
  & #smallcaps("E-Disc")
  $$
  &einter("op", V, cal(F)[eprom("op", x, M, p, N)])
  & quad #smallcaps("E-Prom") \
  &arrow.squiggly
  elet(p, M[V\/x], einter("op", V, cal(F)[N])) \
  &einter("op", V, cal(F)[eprom("op'", x, M, p, N)])
  & quad #smallcaps("E-Fwd") \
  &arrow.squiggly
  eprom("op'", x, M, p, einter("op", V, cal(F)[N]))
  &quad ("where" sans("op") eq.not sans("op'")) \
$

// Examples: pre-emptive concurrency, reactivity, classic actors

With respect to the original algebraic semantics,
it is easy to show a _simulation_ result.
Denote the algebraic semantics by $|->$:
we have that, if $M ~> N$, then $M |->^+ N$.

More difficult is showing _reflection_: the property that,
if $M |-> N$, then there is some $N'$ such that $M ~> N'$ and $N |->^* N'$.
The offending case is that of "let-algebraicity":
$
  elet(x, eprom("op", y, M, p, N_1), N_2)
  |->
  eprom("op", y, M, p, elet(x, N_1, N_2))
$
The context-based semantics is _unable_ to pull $punct("promise")$s out of
$punct("let")$s arbitrarily: in fact, this was a design _goal_.
However, this case is impossible to show unless we know $N_1$ terminates.
If we had this, we could let $N' = eprom("op", y, M, p, N_2[V\/x])$.
But this would require a typed setting (untyped is clearly non-terminating),
and even then, proving termination would be hard!

Thus, a route based on observational equivalence
might be the right choice here...

=== Progress

Our "result forms" are complicated due to
(a) the possibility of blocking awaits
and (b) the non-uniqueness of evaluation contexts.
Nevertheless, we can adapt the definitions of Ahman and Pretnar's
_original_ formulation. (The extended version introduces extra
"algebraic" step rules to simplify result forms.)

We write $p hourglass M$ to say that computation
$M$ is waiting on variable $p$,
which is defined as follows:

#align(center)[#rule-set(
  onerule($p hourglass punct("await") p$),
  onerule(
    $p hourglass M$,
    $p hourglass elet(x, M, N)$
  ),
  onerule(
    $p hourglass M$,
    $p hourglass einter("op", V, M)$
  )
)]

We can then define judgment "$Psi "blocks" M$"
as follows, where $Psi$ is a set of variables:

#align(center)[#rule-set(
  onerule(
    $p in Psi$,
    $p hourglass M$,
    $Psi "blocks" M$
  ),
  onerule(
    $Psi "blocks" M$,
    $Psi "blocks" elet(x, M, N)$
  ),
  onerule(
    $Psi, p "blocks" N$,
    $Psi "blocks" eprom("op", x med k, M, p, N)$
  )
)]

The changes from Ahman and Pretnar's original definition are that
we add $punct("let")$s to the "blocks" judgment (which they call
$sans("RunRes")$) and remove $punct("val")$s.

We have that if $Psi "blocks" M$, then there is no $N$
with $M ~> N$.

We distinguish blocked computations from _expectant_
computations, which merely have the form $cal(P)[punct("val") V]$.

Progress then characterizes computations into three kinds:
able-to-reduce, expectant, or blocked.

(Possible to-do: relate result forms to effect type?
I want to be able to say, e.g., if $M$ is expectant
and $E = emptyset$, then $M equiv punct("val") V$.)

== Integrating Basic DC: Semantics

I see two potential avenues for integrating delimited control into
our core calculus:
we can either restrict the _semantics_ or the _type system_
to prohibit the scope-escape problem mentioned above.

Given that Ahman and Pretnar's language ensures scope-safety
via semantics (for this problem),
we explore this avenue first.

$
  "Values" V, W &::= x | () | lambda x.M | punct("now") V \
  "Computations" M, N &::= punct("val") V | easync(x, M, N)
  | V med W | eawait(x, V, M)
  | reset0(M) | s0 k.M\
  "Pure Contexts" cal(F) &::= [.] | easync(x, cal(F), M) \
  "Evaluation Contexts" cal(E) &::= cal(F)[cal(E)]
    | easync(x, M, cal(E)) | reset0(cal(E))
$

#align(center, rule-set(onerule(
  name: "E-Ctx",
  $M ~> N$,
  $cal(E)[M] ~> cal(E)[N]$
)))

$
  easync(x, punct("val") V, M) &~> M[V\/x] & #smallcaps[E-Val]\
  (lambda x.M) med V &~> M[V\/x] & #smallcaps[E-App]\
  eawait(x, punct("now") V, M) &~> M[V\/x] & #smallcaps[E-Await]\
  reset0(cal(F)[s0 k.M]) &~> M[(lambda x.reset0(cal(F)[punct("val") x]))\/k]
  & #smallcaps("E-Shift")
$

By ensuring our shift-captured evaluation contexts are in
"head position",
we guarantee that $cal(F)$ does not bind any variables in $M$,
so evaluating $M$ _outside of_ $cal(F)$ is safe.

This approach has the (possibly unfortunate) side-effect of
making $s0$ a "semi-blocking" operation.
If we have $easync(x, M, N)$, we expect both of $M$ and $N$
to be able to reduce until $N$ hits an $punct("await")$.
However, if $N = s0 k.N'$, $N$ is now blocked until $M$ reduces fully.

== Integratic Basic DC: Types

Ahman and Pretnar introduce a _Fitch-style modal type system_
as an extension to address a similar scope-escape problem for
other effects (namely signaling and spawning).
We can adapt this approach for shifts.

=== Syntax

We add back basic effect-typing to our language,
and we also add _boxing/unboxing_.
Symbol $\#$ denotes our "lock" in the type context.

$
  "Values" V, W &::= x | () | lambda x.M | punct("now") V | punct("box") V \
  "Computations" M, N &::= punct("val") V | easync(x, M, N)
  | V med W | eawait(x, V, M) \
  &quad | reset0(M) | s0 k.M | punct("unbox") V\
  "Evaluation Contexts" cal(E) &::= [.] | easync(x, cal(E), M)
    | easync(x, M, cal(E)) | reset0(cal(E)) \
  "Types" A, B &::= 1 | A ->^E B | circle A | square A \
  "Effects" E, F &::= emptyset | E, A \
  "Type contexts" Gamma &::= emptyset | Gamma, x : A
    | Gamma, \#
$

=== Semantics

Same as before, except we allow shifting underneath an arbitrary
evaluation context,
and we add the obvious rule for unboxing.

#align(center, rule-set(onerule(
  name: "E-Ctx",
  $M ~> N$,
  $cal(E)[M] ~> cal(E)[N]$
)))

$
  easync(x, punct("val") V, M) &~> M[V\/x] & #smallcaps[E-Val]\
  (lambda x.M) med V &~> M[V\/x] & #smallcaps[E-App]\
  eawait(x, punct("now") V, M) &~> M[V\/x] & #smallcaps[E-Await]\
  reset0(cal(E)[s0 k.M]) &~> M[(lambda x.reset0(cal(E)[punct("val") x]))\/k]
  & quad #smallcaps("E-Shift") \
  punct("unbox box") V &~> punct("val") V & #smallcaps[E-Unbox]\
$

=== Type System

We first define _stable_ types (i.e. those that can be used
at any point) as follows:

#align(center, rule-set(
  onerule(
    name: "St-One",
    $1 "stable"$
  ),
  onerule(
    name: "St-Box",
    $square A "stable"$
  )
))

This notably excludes "later types" $circle A$,
and functions $A ->^E B$ (which may close over later-types).
If we had other ground types, e.g. products $A times B$,
we could judge them stable so long as $A$ and $B$ are stable.

We have judgments $Gamma tack V : A$ for values
and $Gamma tack M : A bang E$ for computations, as usual.
Auxiliary judgment $\# in.not Gamma$ is defined
as expected.

#align(center, rule-set(
  onerule(
    name: "TV-Var",
    $A "stable" or \# in.not Gamma'$,
    $Gamma, x: A, Gamma' tack x : A$
  ),
  onerule(
    name: "TV-Unit",
    $Gamma tack () : 1$
  ),
  onerule(
    name: "TV-Lam",
    $Gamma, x: A tack M : B bang E$,
    pad(top: 0.3em)[
      $Gamma tack lambda x.M : A ->^E B$
    ]
  ),
  onerule(
    name: "TV-Now",
    $Gamma tack V : A$,
    $Gamma tack punct("now") V: circle A$
  ),
  onerule(
    name: "TV-Box",
    $Gamma, \# tack V : A$,
    $Gamma tack punct("box") V: square A$
  ),
  onerule(
    name: "TC-Val",
    $Gamma tack V: A$,
    $Gamma tack punct("val") V: A bang E$,
  ),
  onerule(
    name: "TC-Async",
    $Gamma tack M: A bang E$,
    $Gamma, x : circle A tack N : B bang E$,
    $Gamma tack easync(x, M, N): B bang E$
  ),
  onerule(
    name: "TC-App",
    $Gamma tack V : A ->^E B$,
    $Gamma tack W : A$,
    $Gamma tack V med W : B bang E$
  ),
  onerule(
    name: "TC-Await",
    $Gamma tack V : circle A$,
    $Gamma, x : A tack M : B bang E$,
    $Gamma tack eawait(x, V, M): B bang E$
  ),
  onerule(
    name: "TC-Unbox",
    $Gamma tack V : square A$,
    $Gamma tack punct("unbox") V: A bang E$
  ),
  onerule(
    name: "TC-Reset",
    $Gamma tack M : A bang E , A$,
    $Gamma tack reset0(M) : A bang E$
  ),
  onerule(
    name: "TC-Shift",
    $Gamma, \#, k: A ->^E B tack M : B bang E$,
    $Gamma tack s0 k.M : A bang E, B$
  ),
))

The key is that rule #smallcaps[TC-Shift] introduces a lock,
and so its body may only use stable values (and $k$).

=== Discussion

*Overrestriction?*
The modal type system rules out some (possibly desired) behavior
from Ahman and Pretnar's calculus. Take the following term
(in the original calculus):

$
  &eprom("op", x, M, p,
    eprom("waitForOp", y, elet(z, punct("await") p, M'), q, N))
$

The purpose of $sans("waitForOp")$ is to block on the promise $p$,
and once fulfilled, do some postprocessing in $M'$.

The important bit here is that
we can receive $sans("op")$ and $sans("waitForOp")$ _in either order_.
Say we receive $sans("op")$ first (using shallow interrupts for brevity):

$
  &einter("op", V, eprom("op", x, M, p,
    \ &quad eprom("waitForOp", y,
    elet(z, punct("await") p, M'), q, N)))\
  ~>& elet(p, M[V\/x],
    eprom("waitForOp", y, elet(z, punct("await") p, M'), q, N))\
  ~>^*& elet(p, punct("val now") W,
    eprom("waitForOp", y, elet(z, punct("await") p, M'), q, N))\
  ~>& eprom("waitForOp", y, elet(z, punct("await now") W, M'), q, N)\
$

Whenever the above computation now receives $sans("waitForOp")$,
it can proceed immediately with $M'$.

Say instead that we receive $sans("waitForOp")$ first:

$
  &einter("waitForOp", V, eprom("op", x, M, p, \
    &quad eprom("waitForOp", y, elet(z, punct("await") p, M'), q, N)))\
  ~>&eprom("op", x, M, p, einter("waitForOp", V, \
    &quad eprom("waitForOp", y,
      elet(z, punct("await") p, M'), q, N)))\
  ~>&eprom("op", x, M, p,
    elet(q, (elet(z, punct("await") p, M')), N))\
$

The above computation is blocked until receiving $sans("op")$.

Returning to the modal system: I don't see a way of replicating this behavior.
The original term is clearly untypeable, since
the subcomputation for $sans("waitForOp")$ uses a promise variable $p$.
We can write a term that implements one order or another, but not both
simultaneously.

*Semantic Difference.*
Type systems aside, the two calculi have demonstrably different semantics.
Take the following term:
$
  &eprom("op", x, M, p, eprom("op'", y, M', q, N))
$

Say we receive $sans("op'")(V)$. In the original calculus,
we step to the following (again using shallow interrupts for brevity):

$
  &eprom("op", x, M, p, elet(q, M'[V\/y], N))
$

Notably, computation $M'[V\/y]$ can _still be interrupted_ by $sans("op")$:

$
  &einter("op", W, eprom("op", x, M, p, elet(q, M'[V\/y], N)))\
  ~>& elet(p, M[W\/x], elet(q, M'[V\/y], N))
$

However, in the new calculus, receiving $sans("op'")(V)$ gives us
(with the trivial continuation):
$
  elet(q, M'[V\/y], eprom("op", x, M, p, N))
$

Now, computation $M'[V\/y]$ is no longer interruptable by $sans("op")$:
a new interrupt must "wait" until $M'[V\/y]$ finishes until it can
interact with the promise handler beneath it.

Whether this difference is a _problem_, a _benefit_, or simply a _difference_
is unclear to me.
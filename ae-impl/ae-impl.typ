#import "toby.typ": scratch
#import "@preview/mannot:0.4.0": markhl
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#set document(title: [
  Implementing Asynchronous Effects
])

// general formatting
#let grey(x) = markhl(x, color: gray)

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

= Context-Based Semantics

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
  "Evalutation Contexts" cal(E) &::= [dot] | elet(x, cal(E), N)
  | eprom("op", x, M, p, cal(E)) \
& | grey(arrow.b sans("op")(V, cal(E))) \
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
  elet(x, sans("val") V, M) &arrow.squiggly M[V\/x]\
  (lambda x.M) #h(4pt) V &arrow.squiggly M[V\/x] \
  sans("fst") (V, W) V &arrow.squiggly sans("val") V \
  sans("snd") (V, W) V &arrow.squiggly sans("val") W \
  sans("await") angle(V) &arrow.squiggly sans("val") V\
  arrow.b sans("op")(V, cal(E)[eprom("op", x, M, p, N)])
  &arrow.squiggly
  cal(E)[elet(p, M[V\/x], arrow.b sans("op")(V, N))] \
  ("where" sans("op") in.not cal(E))
$

$sans("op") in.not cal(E)$ means that no handlers
(and maybe also no interrupts?)
for $sans("op")$ appear in $cal(E)$.

=== Parallel Fragment

Goal by example:

$
sans("run") M || sans("run") cal(E)[arrow.t sans("op")(V)] || sans("run") N
arrow.squiggly
sans("run") arrow.b sans("op")(V, M) || sans("run") cal(E)[sans("val" ())]
|| sans("run") arrow.b sans("op")(V, N)
$
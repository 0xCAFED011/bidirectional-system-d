#lang scribble/base

@(require scriblib/figure
          scriblib/autobib
          pict
          redex/reduction-semantics
          redex/pict
          (prefix-in base: (combine-in "bsd.rkt"
                                       (submod "bsd.rkt" typeset)))
          (prefix-in bib: "bibliography.rkt"))


@(define (make-tag)
   (symbol->string (gensym)))

@(define-cite ~cite citet generate-bibliography)


@(default-font-size 12)
@(label-font-size 12)
@(metafunction-font-size 12)
@(delimit-ellipsis-arguments? #true)
@(metafunction-pict-style 'left-right/vertical-side-conditions)
@(metafunction-gap-space 10)
@(rule-pict-style 'horizontal)



@title{Notes on a Bidirectional Typing Algorithm for Monomorphic, Quantitative System@|~|D}
@author{Viv Hammerschmidt}


@(define sec:intro (make-tag))
@section[#:tag sec:intro]{Introduction}

These notes contain a complete typing algorithm for a monomorphic version of System@|~|D,
a sequent calculus designed as an expressive intermediate language for compilation. The algorithm
has a minimal annotation burden and never uses unification or constraint-solving. A highlight
of the algorithm is its ability to handle graded, modal type systems, demonstrated here
by linearity analysis. The full language and algorithm are described in chunks, to allow
introduction to the calculus and to highlight novelties in the approach behind the algorithm.

System@|~|D@~cite[bib:comp/classical] is a sequent calculus. It contains a small number
of atomic constructs, from which many powerful language features can be tidily derived,
including data structures, functions, immutable objects, and complex control operations.
Its reduction semantics are well-defined and allow for fine-grained mixing of call-by-value
and call-by-name evaluation---in fact, calling conventions can be determined simply by looking
at the types of terms. These aspects mean that, given some modest extensions, like mutable cells
and I/O, System@|~|D can serve as a general high-level intermediate language, for use in both
compilation and programming language research.

The algorithm follows the bidirectional discipline, wherein there are interleaved
steps of type synthesis (inference) and type checking. The benefit of this approach is that
the type annotation burden is reduced, yet there is no appeal to unification.
For an introduction to the idea, please see Conor McBride's blog post@~cite[bib:basics-bidirectional].
The design space for bidirectional type systems is, historically, broad@~cite[bib:bidirectional-typing],
but the structure of System@|~|D causes the ideal design choices to fall out naturally.
The general idea and techniques behind the algorithm are adapted from work on a bidirectional
typing algorithm for an ancestral sequent calculus, System@|~|L@~cite[bib:bidi-system-l].



@(define sec:sequent-calculi (make-tag))
@subsection[#:tag sec:sequent-calculi]{Sequent Calculi}

A sequent calculus is a logical system of propositions and proofs. The first sequent calculus was
developed by Gentzen, as a companion system to natural deduction. In logic and proof theory, the
benefit of working with a sequent calculus is that it is easier to prove metatheoretical results
about the system. Natural deduction, as suggested by its name, is easier for direct use as a
logical system. Importantly, it is possible to convert between the systems.

Often called the ``Curry-Howard Correspondence'', there is a powerful connection between logical
systems and programming languages. Logical propositions correspond to types, and proofs of propositions
correspond to programs of particular types. Thus, it is possible, with more-or-less effort, to
either extract a programming language from a logical system, or give a logical interpretion of
a programming language. Through this lens, natural deduction corresponds to the lambda calculus.
We can infer, correctly, that there is a programming language to be found in the sequent calculus
which can provide valuable insights to the lambda calculus.

Moving from a lambda calculus to a computational sequent calculus has the effect of making the
semantics explicit in the syntax of the language. In this way, it is not unlike performing a
transformation into Continuation-Passing Style (CPS). Unlike CPS, moving into a sequent calculus
does away with the familiar structure of function application, and instead one explicitly works
with abstract calls stacks. Thus, a function application is decomposed into a construct which
joins a function body to a call stack.

The example of function application can be described generally, as a core feature of sequent calculi.
Instead of the familiar notions of @emph{introduction} and @emph{elimination} forms, sequent calculi
have @emph{producers} and @emph{consumers}. Although similar, a key difference is that consumer
forms always explicitly refer to the continuation. To build computation in a sequent calculus,
a producer and a corresponding consumer are brought together in a special form called a @emph{cut}
(sometimes also called a ``command''). The elimination forms of lambda calculi can be thought
of as folding the consumer and cut forms together.




@(define sec:core-lang (make-tag))
@section[#:tag sec:core-lang]{Core Language}

We begin with a small core of System@|~|D. The language includes some familiar types:

@itemlist[
 @item{zero (empty): @base:pretty-term[𝟘]}
 @item{one (unit): @base:pretty-term[𝟙]}
 @item{pairs: @base:pretty-term[(τ ⊗ τ)]}
 @item{sums: @base:pretty-term[(τ ⊕ τ)]}]

And the corresponding producers, being primitive constructors:

@itemlist[
 @item{no constructor for empty type}
 @item{unit constructor: @base:pretty-term[()]}
 @item{pair constructor: @base:pretty-term[(pair w w)]}
 @item{left and right injections: @base:pretty-term[(ιl w)] and @base:pretty-term[(ιr w)]}]

And the corresponding consumers, being primitive pattern-matching forms:

@itemlist[
 @item{``absurd'' match for zero @base:pretty-term[{𝟘}]}
 @item{match on unit @base:pretty-term[{() ↦ k}]}
 @item{match on pair: @base:pretty-term[{(pair χ χ) ↦ k}]}
 @item{match on injections: @base:pretty-term[{(ιl χ) ↦ k \| (ιr χ) ↦ k}]}]

And, finally, it contains a command form, @base:pretty-term[[cmd p ⇒ c]], found in the body of
matching forms (abbreviated @(base:pretty-term k)). It is within a command, joining a producer and
a consumer, that computation occurs. By using these terms, we can build and deconstruct nonrecursive
algebraic data types. Here is what commands could look like, for specific types:

@itemlist[
 @item{@base:pretty-term[𝟙]: @base:pretty-term[[cmd () ⇒ {() ↦ k}]]}
 @item{@base:pretty-term[(τ ⊗ τ)]: @base:pretty-term[[cmd (pair p p) ⇒ {(pair x_1 x_2) ↦ k}]]}
 @item{@base:pretty-term[(τ ⊕ τ)]: @base:pretty-term[[cmd (ιl p) ⇒ {(ιl x_l) ↦ k_l \| (ιr x_r) ↦ k_r}]]}
 ]

Sometimes, we want to bind a value to a variable, so as to make an expression concise, or so that
the value can be used multiple times. This is done with the ``let'' form: @base:pretty-term[{let/P ▽χ κ ↦ k}].
Notice how the syntax of programs makes the control flow explicit, and the next step of computation
can always be found, immediately.

A note about forms which bind variables: a binding, @base:pretty-term[χ], is rather flexible,
and offers some choices

@itemlist[
 @item{a bare variable: @base:pretty-term[x]}
 @item{a variable with type annotation: @base:pretty-term[(▽var x τ)]}
 @item{a variable with type and usage annotations: @base:pretty-term[(▽var x τ ρ)]}
 @item{a non-binding, with type annotation: @base:pretty-term[(nope τ)]}
 ]

For a variable, omitted type and/or usage annotations can be completely synthesized (inferred),
based on how the variable is used (more on that, later). The non-binding is for terms that will never
be used in the body of the form, and this is treated specially, rather than binding a variable that
is never used, because it avoids awkward issues that arise if the system is extended with modalities
other than usage. For example, an unused variable could be marked as having usage 0, but things like
parametricity, security level, owned/borrowed, &c@._ would be unclear, if not completely meaningless,
to consider. Thus, it's better for the language to directly support the notion of non-binding.

You may have noticed that there is no way to ``end'' a program, that is, there must always be a next
step, the next command to execute. Although some systems may include a special ``done'' command, this
is a misunderstanding of the nature of termination. A computation terminates when it is ready to directly
yield a result. Yield to what? To the next step, being some implicit new computation. This
is something that we're already familiar with: when a program finishes running, it returns control
(and, perhaps, a code) to the shell or operating system. Thus, a simple value can be understood
as a part of an implicit command, yielding to some unknown consumer.

This implies that consumers may be more involved than the straightforward pattern-matching forms we've
seen thus far. Indeed, if we can describe ending a program via a command with an abstract consumer,
then it must be possible for consumers to be bound to variables. And, if a consumer can be bound to
a variable, then there must be a corresponding binding form, no? Indeed, there is:
@base:pretty-term[{let/C △χ ↦ k}], a mirror-image of the previously-described let-form. Using this form,
we can abstract over consumers.

As an example, here we abstract over a matching consumer:

@centered{
 @base:pretty-term[
   [cmd {let/C (var x_match 𝟙 +) ↦ [cmd () ⇒ x_match]}
    ⇒
    {() ↦ k}]]
}

At this point, there are some questions implied by what we've seen thus far... What are the funny
annotations (@base:pretty-term[κ]) that accompany types? What does it mean to abstract over consumers?
Can a let-fom abstract over another let-form? These questions lead us into the expressivity and nuance
of System@|~|D, but, thankfully, we can use concepts from other languages to develop an intuition of
what's going on here.

Let's begin with the annotations, disregarding usage. The extra bit, (@base:pretty-term[κ]) is a @emph{kind}
annotation. This may seem odd: after all, the title specifies that this language is monomorphic, so
there musn't be any higher-kinded types. Since that's the case, why bother with mentioning kinds?
As it turns out, the set of types is richer than described above---in fact, there are twice as many types.
This is because System@|~|D has the special property of allowing a deep exploration of @emph{duality};
de@|~|Morgan duality, to be precise.

The previously-described types were all of kind @base:pretty-term[+], thus called @emph{positive}.
The second set of types are of kind @(base:pretty-term -) (@emph{negative}), each being counterpart
to a previously-mentioned type:

@itemlist[
 @item{top, @base:pretty-term[⊤], dual to @base:pretty-term[𝟘]}
 @item{bottom, @base:pretty-term[⊥], dual to @base:pretty-term[𝟙]}
 @item{par, @base:pretty-term[(τ ⅋ τ)], dual to @base:pretty-term[(τ ⊗ τ)]}
 @item{with, @base:pretty-term[(τ & τ)] dual to @base:pretty-term[(τ ⊕ τ)]}
 ]

The duality of types is demonstrated by both their logical meanings and by the terms associated with them.
For example, whereas @base:pretty-term[𝟘] is an empty type, corresponding to a vacuous falsity, and
@base:pretty-term[𝟙] is a singleton type, corresponding to trivial truth; @base:pretty-term[⊤] is an
empty type, corresponding to vacuous truth, and @base:pretty-term[⊥] is a singleton type, corresponding
to trivial falsity. 

As before, each type has associated producers (sometimes called copattern-matches @~cite[bib:copatterns]):

@itemlist[
 @item{absurd match on top: @base:pretty-term[{⊤}]}
 @item{match on bottom: @base:pretty-term[{⊥ ↦ k}]}
 @item{match on par: @base:pretty-term[{[duo χ_1 χ_2] ↦ k}]}
 @item{match on with: @base:pretty-term[{[πl χ_l] ↦ k_l \| [πr χ_r] ↦ k_r}]}
 ]

And, consumers (sometimes called destructors or observations):

@itemlist[
 @item{no consumer for top}
 @item{bottom destructor: @base:pretty-term[⊥]}
 @item{with-destructors: @base:pretty-term[[duo f f]]}
 @item{left and right projections: @base:pretty-term[[πl f]] and @base:pretty-term[[πr f]]}
 ]

The copattern-matching forms can be thought of as processes that are waiting on a request and respond
according to its structure. A more provocative, yet accurate, perspective is that copattern-matching
is a means of matching on the structure of continuations. Although this may seem strange, when coming
from a background of functional programming, we can recover some intuition about how these contructs
work, thanks, in part, to their nature as duals to the positive types.

Let's begin with @base:pretty-term[&]. It is dual to the disjoint sum, @base:pretty-term[⊕], and is,
precisely, a disjoint product---although, a more familiar term would be @emph{projective product}.
However, as we can see, given the producer is a matching construct, it's more accurate to view the
@base:pretty-term[&] connective as a pure object and its methods. If you are familiar with the
``codata record'' type in Agda, then you already have seen this connective in action.

Now, the situation for @base:pretty-term[⅋] is more difficult to explain, because nothing like it is
found in popular functional programming languages or proof-assistants based on dependent lambda-calculi.



@(define sec:bib (make-tag))
@generate-bibliography[#:tag sec:bib]


@section{Appendix: Full Language Specification and Algorithm}

@(define fig:whole-lang (make-tag))
@figure[fig:whole-lang @elem{Complete raw language grammar.}]{
 @(base:with-my-rewriters (λ () (language->pict base:BS-raw)))
}

@(define fig:whole-exec (make-tag))
@figure[fig:whole-exec @elem{Complete execution language grammar.}]{
 @(base:with-my-rewriters (λ () (language->pict base:BS-exec)))
}

@(define fig:whole-elab (make-tag))
@figure[fig:whole-elab @elem{Complete elaboration language extensions.}]{
 @(base:with-my-rewriters (λ () (language->pict base:BS-elab)))
}

@(define fig:kinding (make-tag))
@figure[fig:kinding
        @elem{Complete kinding relation.@(linebreak)@(base:pretty-term (kind-type τ κ))}]{
 @(base:with-my-rewriters
   (λ ()
     (hb-append
      20
      (parameterize
          ([judgment-form-cases '("𝟘" "𝟙" "⊗" "⊕")])
        (judgment-form->pict base:kind-type))
      (parameterize
          ([judgment-form-cases '("⊖" "↓" "⇑")])
        (judgment-form->pict base:kind-type))
      (parameterize
          ([judgment-form-cases '("⊤" "⊥" "⅋" "&")])
        (judgment-form->pict base:kind-type))
      (parameterize
          ([judgment-form-cases '("¬" "↑" "⇓")])
        (judgment-form->pict base:kind-type)))))
}

@(define fig:type-equal (make-tag))
@figure[fig:type-equal
        @elem{Kind-indexed type equality.@(linebreak)@(base:pretty-term (type-= τ τ κ))}]{
 @(base:with-my-rewriters
   (λ ()
     (hb-append
      20
      (parameterize
         ([judgment-form-cases '("𝟘_=" "𝟙_=" "⊗_=" "⊕_=" "⊖_=" "↓_=" "⇑_=")])
        (judgment-form->pict base:type-=))
      (parameterize
         ([judgment-form-cases '("⊤_=" "⊥_=" "⅋_=" "&_=" "¬_=" "↑_=" "⇓_=")])
        (judgment-form->pict base:type-=)))))
}


@(define fig:whole-elab-binding/check (make-tag))
@figure[fig:whole-elab-binding/check
        @elem{Checked binding elaboration.@(linebreak)@(base:pretty-term (elaborate-binding/check Ξ χ Ξ_′ X τ κ))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:elaborate-binding/check)))
}

@(define fig:whole-elab-binding/synth (make-tag))
@figure[fig:whole-elab-binding/synth
        @elem{Synthesizing binding elaboration.@(linebreak)@(base:pretty-term (elaborate-binding/synth Ξ χ Ξ_′ X τ κ))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:elaborate-binding/synth)))
}


@(define fig:requirements-+ (make-tag))
@figure[fig:requirements-+
        @elem{Requirement addition.@linebreak[]@base:pretty-metafunction-sig[(requirements-+ Ξ Ξ) Ξ]}]{
 @(base:with-my-rewriters (λ () (metafunction->pict base:requirements-+)))
}

@(define fig:requirements-⊔ (make-tag))
@figure[fig:requirements-⊔
        @elem{Requirement least upper bound.@linebreak[]@base:pretty-metafunction-sig[(requirements-⊔ Ξ Ξ) Ξ]}]{
 @(base:with-my-rewriters (λ () (metafunction->pict base:requirements-⊔)))
}


@(define fig:whole-cut (make-tag))
@figure[fig:whole-cut
        @elem{Cut.@(linebreak)@(base:pretty-term (cut ξ k Ξ K))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:cut)))
}



@(define fig:whole-synth-consumer (make-tag))
@figure[fig:whole-synth-consumer
        @elem{Unfocused consumer synthesis.@(linebreak)@(base:pretty-term (△consumer ξ c Ξ C τ κ))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:△consumer)))
}

@(define fig:whole-check-producer (make-tag))
@figure[fig:whole-check-producer
        @elem{Unfocused producer checking.@(linebreak)@(base:pretty-term (▽producer ξ p τ κ Ξ P))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:▽producer)))
}

@(define fig:whole-synth-producer (make-tag))
@figure[fig:whole-synth-producer
        @elem{Unfocused producer synthesis.@(linebreak)@(base:pretty-term (△producer ξ p Ξ P τ κ))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:△producer)))
}

@(define fig:whole-check-consumer (make-tag))
@figure[fig:whole-check-consumer
        @elem{Unfocused consumer checking.@(linebreak)@(base:pretty-term (▽consumer ξ c τ κ Ξ C))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:▽consumer)))
}




@(define fig:whole-focused-synth-consumer (make-tag))
@figure[fig:whole-focused-synth-consumer
        @elem{Focused consumer synthesis.@(linebreak)@(base:pretty-term (focused-△consumer ξ c Ξ C τ κ))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:focused-△consumer)))
}

@(define fig:whole-focused-check-producer (make-tag))
@figure[fig:whole-focused-check-producer
        @elem{Focused producer checking.@(linebreak)@(base:pretty-term (focused-▽producer ξ p τ κ Ξ P))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:focused-▽producer)))
}

@(define fig:whole-focused-synth-producer (make-tag))
@figure[fig:whole-focused-synth-producer
        @elem{Focused producer synthesis.@(linebreak)@(base:pretty-term (focused-△producer ξ p Ξ P τ κ))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:focused-△producer)))
}

@(define fig:whole-focused-check-consumer (make-tag))
@figure[fig:whole-focused-check-consumer
        @elem{Focused consumer checking.@(linebreak)@(base:pretty-term (focused-▽consumer ξ c τ κ Ξ C))}]{
 @(base:with-my-rewriters (λ () (judgment-form->pict base:focused-▽consumer)))
}



@(define fig:whole-reduction (make-tag))
@figure[fig:whole-reduction
        @elem{Complete reduction semantics.@(linebreak)@(base:pretty-term K) @(arrow->pict '-->) @(base:pretty-term K)}]{
 @(base:with-my-rewriters (λ () (reduction-relation->pict base:red/BS)))
}

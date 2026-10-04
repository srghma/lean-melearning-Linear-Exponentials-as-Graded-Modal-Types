#import "@preview/curryst:0.6.0": prooftree, rule

// Document setup
#let horizontalrule = [
  #line(start: (25%, 0%), end: (75%, 0%))
]

#let endnote(num, contents) = [
  #stack(dir: ltr, spacing: 3pt, super[#num], contents)
]
#show terms: it => {
  it
    .children
    .map(child => [
      #strong[#child.term]
      #block(inset: (left: 1.5em, top: -0.4em))[#child.description]
    ])
    .join()
}

#let codeblock(label: none, body) = block(
  width: 100%,
  stroke: 0.5pt + luma(180),
  fill: luma(250),
  radius: 1pt,
  inset: (x: 8pt, top: 6pt, bottom: 6pt),
  [
    #set text(size: 9pt)
    #body
    #if label != none {
      v(-0.4em)
      align(right)[#text(size: 8.5pt, font: ("New Computer Modern", "DejaVu Serif"))[#label]]
    }
  ],
)

#set table(
  inset: 6pt,
  stroke: none,
)

#show figure.where(
  kind: table,
): set figure.caption(position: top)

#show figure.where(
  kind: image,
): set figure.caption(position: bottom)

#let content-to-string(content) = {
  if content.has("text") {
    content.text
  } else if content.has("children") {
    content.children.map(content-to-string).join("")
  } else if content.has("body") {
    content-to-string(content.body)
  } else if content == [ ] {
    " "
  }
}
#let conf(
  title: none,
  subtitle: none,
  authors: (),
  keywords: (),
  date: none,
  abstract: none,
  cols: 1,
  margin: (x: 1.25in, y: 1.25in),
  paper: "us-letter",
  lang: "en",
  region: "US",
  font: ("New Computer Modern",),
  fontsize: 11pt,
  sectionnumbering: none,
  doc,
) = {
  set document(
    title: title,
    author: authors.map(author => content-to-string(author.name)),
    keywords: keywords,
  )
  set page(
    paper: paper,
    margin: margin,
    numbering: "1",
  )
  set par(justify: true)
  set text(lang: lang, region: region, font: font, size: fontsize)
  set heading(numbering: sectionnumbering)

  if title != none {
    align(center)[#block(inset: 2em)[
      #text(weight: "bold", size: 1.5em)[#title]
      #(
        if subtitle != none {
          parbreak()
          text(weight: "bold", size: 1.25em)[#subtitle]
        }
      )
    ]]
  }

  if authors != none and authors != [] {
    let count = authors.len()
    let ncols = calc.min(count, 3)
    grid(
      columns: (1fr,) * ncols,
      row-gutter: 1.5em,
      ..authors.map(author => align(center)[
        #author.name \
        #author.affiliation \
        #author.email
      ])
    )
  }

  if date != none {
    align(center)[#block(inset: 1em)[
      #date
    ]]
  }

  if abstract != none {
    block(inset: 2em)[
      #text(weight: "semibold")[Abstract] #h(1em) #abstract
    ]
  }

  if cols == 1 {
    doc
  } else {
    columns(cols, doc)
  }
}
#show: doc => conf(
  cols: 1,
  doc,
)



= Linear Exponentials as Graded Modal Types
<linear-exponentials-as-graded-modal-types>
Jack Hughes\* Daniel Marshall\* James Wood† Dominic Orchard\*

==== #strong[Abstract]
<abstract>
Graded type systems, which allow resource usage in programs to be
tracked and reasoned about, are proliferating in recent works. These
systems generalise ideas from Bounded Linear Logic (BLL), which allows
the exponential modality $!$ from linear logic to be indexed by a bound on
the number of times a formula is used. Graded systems generalise BLL’s
indexed modality to an arbitrary semiring of grades. Despite their
relation to linear logic, particular choices in most graded type systems
mean they cannot faithfully model $!$ due to the interaction between $!$ and
$⊗$; there are certain distributive laws that can be derived in
graded type systems but cannot be derived in linear logic. We remedy
this by enriching the structure of the grading with an additional
operation, and show how this recovers the expressive power of
Intuitionistic Multiplicative Exponential Linear Logic (IMELL) in a
system with graded modal types. We briefly discuss our implementation
involving this new operation for the graded modal language Granule.

== #strong[1 Introduction]
<introduction>
Linear logic separates linear formulas (those that must be used exactly
once) from non-linear formulas (those that can be used arbitrarily
often) by treating linearity as the default and using the 'exponential'
modality $!$ to mark non-linear formulas. Bounded Linear Logic \[GSS92\]
generalises $!$ to an indexed family of modalities $!_r A$ where
$r$ is a polynomial term over natural numbers capturing the maximum
number of times that $A$ can be used. Graded modal logics have
generalised this idea further so that $square_r A$ captures a formula
$A$ which can be used according to a usage constraint $r$
which is an element of an arbitrary pre-ordered semiring $cal(R)$. One
natural question is: can we recover the $!$ of linear logic via a
particular choice of semiring? It turns out that many graded modal type
systems bake in extra properties regarding the interaction of graded
modalities and linear products $⊗$ (multiplicative conjunction)
such that $!$ cannot be precisely captured. In particular, whilst graded
type theories (e.g.~\[OLEI19, AB20, BBN+ 17, Bra21\]) can derive a
bi-implication
between $square_r A ⊗ square_r B$ and $square_r (A ⊗ B)$ for any
$r$, linear logic (LL) only derives $!A ⊗ !B ⊸ !(A ⊗ B)$, i.e., for graded theories, denoted GR:

$
  tack_("GR") "pull"_square : square_r A ⊗ square_r B ⊸ square_r (A ⊗ B) & wide wide tack_("GR") "push"_square : square_r (A ⊗ B) ⊸ square_r A ⊗ square_r B \
  tack_("LL") "pull"_! : !A ⊗ !B ⊸ !(A ⊗ B) & wide wide ⊬_("LL") "push"_! : !(A ⊗ B) ⊸ !A ⊗ !B
$

For example, $"push"_square$ can be defined in Granule (a linear language
with graded modalities \[OLEI19\]) as follows (where `(a, b) [r]` is
syntax for $square_r (A ⊗ B)$):

#codeblock(label: "Granule")[
  ```granule
  push : ∀ {a b : Type, s : Semiring, r : s} . (a, b) [r] → (a [r], b [r])
  push [(x, y)] = ([x], [y])
  ```
]

However, the power of the pattern matching used here does not translate
to linear logic, and thus $square_r$ and $!$ are different. We propose a
technique to restrict $"push"$ by augmenting the grading semiring
with additional structure such that the derivability of $"push"$ can
be controlled (or 'turned off'), enabling the intuitionistic $!$ to be
recovered in a graded modal type system. This has applications to
practical implementations of graded type systems such as Linear Haskell
\[BBN+ 17\], Granule \[OLEI19\], and Idris 2 \[Bra21\], and on the
theories of Grad \[CEIEW21\], $Lambda^p$ \[AB20\] and GranuleCore
\[OLEI19\].

While we would like to be able to embed intuitionistic linear logic, we
would like in other situations to have $"push"_square$. Graded systems
have useful models \[AB20\] and a simple syntax for mixed linear and
non-linear settings \[BBN+ 17, Bra21\]. This motivates accommodating
both choices in the same system.

== #strong[2 Core calculus]
<core-calculus>
To explore this issue and formulate a solution, we focus on a core
calculus based on the linear $lambda$-calculus extended with products,
units, pattern matching, and a #emph[semiring graded necessity modality]
\[OLEI19\], where for a pre-ordered semiring $(cal(R), *, 1, +, 0, subset.eq.sq)$, there is a family of types ${square_r A}_(r in cal(R))$. This language constitutes a simplified monomorphic
subset of Granule \[OLEI19\] which we will call GRCORE, and closely
resembles other related graded systems \[AB20, Atk18, BBN+ 17, Bra21,
CEIEW21\].

Typing judgements are of the form $Gamma tack t : A$, assigning
type $A$ to a term $t$ under context $Gamma$. Contexts $Gamma$ can contain
linear and graded assumptions $Gamma ::= emptyset | Gamma, x : A | Gamma, y : [A]_r$, where $x$ is a linear
assumption and $y$ is a graded assumption with grade $r in cal(R)$
describing how $y$ can be used. Syntax and typing are given by the
rules:

#align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 2.5em,
    row-gutter: 1.5em,
    prooftree(rule(name: [VAR], $x : A tack x : A$)),
    prooftree(rule(name: [ABS], $Gamma, x : A tack t : B$, $Gamma tack lambda x. t : A ⊸ B$)),

    prooftree(rule(
      name: [APP],
      $Gamma_1 tack t_1 : A ⊸ B$,
      $Gamma_2 tack t_2 : A$,
      $Gamma_1 + Gamma_2 tack t_1 thin t_2 : B$,
    )),
    prooftree(rule(name: [DER], $Gamma, x : A tack t : B$, $Gamma, x : [A]_1 tack t : B$)),

    prooftree(rule(name: [WEAK], $Gamma tack t : A$, $Gamma + [Delta]_0 tack t : A$)),
    prooftree(rule(
      name: [APPROX],
      $Gamma, x : [A]_r, Gamma' tack t : A$,
      $r subset.eq.sq s$,
      $Gamma, x : [A]_s, Gamma' tack t : A$,
    )),

    prooftree(rule(name: [PR], $[Gamma] tack t : A$, $r * [Gamma] tack [t] : square_r A$)),
    prooftree(rule(name: [UNIT], $emptyset tack "unit" : 1$)),
  )

  #v(0.8em)

  #grid(
    columns: (auto, auto),
    column-gutter: 2.5em,
    prooftree(rule(
      name: [PROD],
      $Gamma_1 tack t_1 : A$,
      $Gamma_2 tack t_2 : B$,
      $Gamma_1 + Gamma_2 tack (t_1, t_2) : A ⊗ B$,
    )),
    prooftree(rule(
      name: [LET],
      $Gamma_1 tack t_1 : A$,
      $dot tack p : A ▷ Delta$,
      $Gamma_2, Delta tack t_2 : B$,
      $Gamma_1 + Gamma_2 tack "let" p = t_1 "in" t_2 : B$,
    )),
  )
]

The (VAR), (ABS), and (APP) rules are the standard rules of the linear
$lambda$-calculus, augmented with a partial #emph[context addition]
operation $Gamma + Gamma'$ defined via semiring addition on graded
assumptions which appear in both $Gamma$ and $Gamma'$ (where $Gamma$ and $Gamma'$
are disjoint in their linear assumptions): $(Gamma, x : [A]_r) + (Gamma', x : [A]_s) = (Gamma + Gamma'), x : [A]_(r+s)$.

The (WEAK) rule captures structural weakening of assumptions, where
$[Delta]_0$ denotes a context containing only assumptions graded by $0$. A
linear assumption may be converted to a graded assumption with the grade
$1$ via the rule for dereliction (DER). Grade approximation is provided by
the (APPROX) rule, which allows a grade $r$ to be converted to
another grade $s$, provided that $s$ approximates $r$ (where
$subset.eq.sq$ is the pre-order given by the grades’ semiring). Graded
modalities are introduced by the promotion (PR) rule, scaling the
assumptions in the context $[Gamma]$ (where a $[Gamma]$ denotes a context
containing only graded assumptions) via semiring multiplication.
Products are typed by the (PROD) rule, where the contexts used to type
the pair’s constituent subterms are added together.

Elimination of products, units, and graded modal types is achieved via
the (LET) rule, which applies pattern matching to a term $t_1$ to
produce a context of typed binders $Delta$ to be used in $t_2$. Patterns
$p$ are typed by judgements of the form $?r tack p : A ▷ Delta$, meaning that a pattern $p$ has type $A$ and produces a
context of typed binders $Delta$. Optional grade information is denoted via $?r$, defined syntactically as $?r ::= dot | r$, where
$r$ indicates that the rule takes place under an unboxing pattern.
We then define the rules for pattern typing as:

#align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 2.5em,
    row-gutter: 1.5em,
    prooftree(rule(name: [PVAR], $dot tack x : A ▷ x : A$)),
    prooftree(rule(
      name: [PPROD],
      $dot tack p_1 : A ▷ Gamma_1$,
      $dot tack p_2 : B ▷ Gamma_2$,
      $dot tack (p_1, p_2) : A ⊗ B ▷ Gamma_1, Gamma_2$,
    )),

    prooftree(rule(name: [PBOX], $r tack p : A ▷ Gamma$, $dot tack [p] : square_r A ▷ Gamma$)),
    prooftree(rule(name: [\[PVAR\]], $r tack x : A ▷ x : [A]_r$)),

    prooftree(rule(
      name: [\[PPROD\]],
      $r tack p_1 : A ▷ Gamma_1$,
      $r tack p_2 : B ▷ Gamma_2$,
      $r tack (p_1, p_2) : A ⊗ B ▷ Gamma_1, Gamma_2$,
    )),
    prooftree(rule(name: [PUNIT], $?r tack "unit" : 1 ▷ emptyset$)),
  )
]

The (PBOX) rule types 'unboxing' patterns by propagating grade
information $r$ into the typing of the sub-pattern $p$. We
therefore require two rules each for the typing of variable and product
patterns: a rule for linear patterns (PVAR and PPROD) and a rule for
patterns which take place inside an unboxing (\[PVAR\] and \[PPROD\]).
In the case of the latter \[PVAR\] rule, a binding is produced with the
grade of the enclosing box’s grade $r$. Likewise in \[PPROD\],
grade information is propagated to the typing of the product’s
constituent sub-patterns. Unit patterns are not affected by the
enclosing grade and so have one rule PUNIT above.

== #strong[3 Dissecting the problem]
<dissecting-the-problem>
In the above system, we can construct the following derivation, nesting
a tensor pattern inside an unboxing pattern:

#align(center)[
  #prooftree(
    rule(
      name: [LET],
      $Gamma_1 tack t_1 : square_r (A ⊗ B)$,
      rule(
        name: [PBOX],
        rule(
          name: [\[PPROD\]],
          rule(name: [\[PVAR\]], $r tack x : A ▷ x : [A]_r$),
          rule(name: [\[PVAR\]], $r tack y : B ▷ y : [B]_r$),
          $r tack (x, y) : A ⊗ B ▷ x : [A]_r, y : [B]_r$,
        ),
        $dot tack [(x, y)] : square_r (A ⊗ B) ▷ x : [A]_r, y : [B]_r$,
      ),
      $Gamma_2, x : [A]_r, y : [B]_r tack t_2 : C$,
      $Gamma_1 + Gamma_2 tack "let" [(x, y)] = t_1 "in" t_2 : C$,
    ),
  )
]

This prevents us capturing linear logic’s $!$ as some $square_r$ in a
graded system, since from the above we can derive $"push"_square : square_r (A ⊗ B) ⊸ square_r A ⊗ square_r B$ with $t_2 = ([x], [y])$. We briefly demonstrate how this
problem affects languages other than Granule.

#strong[Linear Haskell] As of GHC 9, Haskell implements a graded type
system \[BBN+ 17\]. Function types `(a %r -> b)` now have a multiplicity
annotation `r`. The annotation `r` is either `'One` or `'Many`,
corresponding to linear and unrestricted use of the argument,
respectively. Following the presentation in \[HVO20\], we can define a
graded modality in Linear Haskell via the `Box` data type:

#codeblock(label: "Haskell")[
  ```haskell
  data Box r a where { Box :: a %r -> Box r a }
  ```
]

We might hope to define $!A =$ `Box %'Many A`, but this does not
provide an accurate definition of the exponential modality as we can
define the `push` distributive law:

#codeblock(label: "Haskell")[
  ```haskell
  push :: Box r (a, b) %1 -> (Box r a, Box r b)
  push (Box (x, y)) = (Box x, Box y)
  ```
]

The `Box %'Many A` type is equivalent to a wrapper data type
`Unrestricted` which is described as being "very much like $!a$ in
linear logic" \[BBN+ 17\]. The existence of `push` shows one way in
which $!a$ and `Unrestricted a` behave differently.

#strong[Idris 2] Idris 2 is based on Quantitative Type Theory (QTT)
\[Bra21, Atk18\], though, as we discuss below, QTT does not admit
$"push"$, while Idris 2 does. In both Idris 2 and QTT, every
variable has a #emph[quantity] associated with it, either 0, 1 or
$omega$ (unrestricted). Idris 2 does not support direct abstraction
over multiplicity, so instead of a general $square_r$ type, we define a
type corresponding to $square_omega$ and the Haskell `Unrestricted` data
type:

#codeblock(label: "Idris 2")[
  ```idris
  data Unrestricted : Type -> Type where Box : a -> Unrestricted a
  ```
]

(Note here that, as in Haskell, variables have an unrestricted
multiplicity by default.) Similarly to Haskell, we might hope that we
can define $!A =$ `Unrestricted A`. However, again this is not
possible as we can redefine the same `push` law which is not derivable
in linear logic.

#codeblock(label: "Idris 2")[
  ```idris
  push : Unrestricted (a, b) -> (Unrestricted a, Unrestricted b)
  push (Box (x, y)) = (Box x, Box y)
  ```
]

#strong[QTT] Quantitative Type Theory \[Atk18, McB16\] is an example of
a graded type system without the $"push"$ behaviour, thus being a
conservative extension of linear logic. It does this via a more
restricted rule for tensor products than the other systems mentioned in
this paper. Below, we give the rule for tensor products as it appears in
the original paper, and also a simplified version comparable with
propositional linear logic.

In QTT, conclusions are annotated either 1 or 0. Rules are given for
both possibilities simultaneously, with $sigma$ ranging over ${0, 1}$. Conclusions annotated 0 are used only for
constructing (dependent) types, so we need only consider the $sigma = 1$ case. Further simplifying to get the elimination rule for a simple
tensor product, we ignore all of the dependency in $T$ and $U$, and set $pi$ (the grade of the first component of the pair) to 1.
All of these simplifications get us the second rule below. Essentially
the same simplified rule appears in the system $lambda R$, which is
equivalent to intuitionistic linear logic \[WA21\].

#align(center)[
  #grid(
    columns: (auto, auto),
    column-gutter: 2.5em,
    prooftree(
      rule(
        $
          0 Gamma_1, z^0 : (x^pi : S) ⊗ T tack U quad Gamma_1 tack M^sigma : (x^pi : S) ⊗ T \
          Gamma_2, x^(sigma pi) : S, y^sigma : T tack N^sigma : U[(x, y)/z] quad 0 Gamma_1 = 0 Gamma_2
        $,
        $ Gamma_1 + Gamma_2 tack "let"_(x^pi : S . T) (x, y) = M "in" N^sigma : U[M/z] $,
      ),
    ),
    prooftree(
      rule(
        $
          0 Gamma_1 = 0 Gamma_2 quad Gamma_1 tack M : S ⊗ T \
          Gamma_2, x^1 : S, y^1 : T tack N : U
        $,
        $ Gamma_1 + Gamma_2 tack "let" (x, y) = M "in" N : U $,
      ),
    ),
  )
]

#strong[Abel & Bernardy’s] $Lambda^p$ Abel and Bernardy defined a graded
type system $Lambda^p$ and denotational semantics admitting $"push"$
\[AB20\]. They have the following rule for pattern matching on products:

#align(center)[
  #prooftree(
    rule(
      $gamma Gamma tack t : A times B quad delta Gamma, x : {}^q A, y : {}^q B tack u : C$,
      $(q gamma + delta) Gamma tack "let" (x, y) =^q t "in" u : C$,
    ),
  )
]

This is akin to the elimination behaviour underneath a graded modality
in GRCORE as shown at the start of this section. Compared to the
simplified QTT pattern matching rule, the essential difference with QTT
becomes apparent: the $Lambda^p$ rule has the extra grade $q$,
allowing not just one $A times B$ to yield one $A$ and one
$B$, but $q$-many inhabitants of $A times B$ (signified by
the fact that $gamma$ is multiplied by $q$ in the conclusion) to
yield $q$-many $A$s and $q$-many $B$s. This
stronger elimination rule requires a semantic version of $"push"$ in
the models, but such models still include the one used to show that
every linear term is a permutation.

== #strong[4 Solution]
<solution>
The key to controlling the 'push' behaviour is to control pattern
matching on tensor products underneath a graded modality. We thus extend
the pre-ordered semiring
with a partial commutative and associative binary operator $times.l : cal(R) times cal(R) harpoon.rt cal(R)$ (pronounced 'hsup') used in the typing of patterns for tensor products as:

#align(center)[
  #prooftree(
    rule(
      name: [\[PPROD\]],
      $r tack p_1 : A ▷ Gamma_1$,
      $s tack p_2 : B ▷ Gamma_2$,
      $r times.l s tack (p_1, p_2) : A ⊗ B ▷ Gamma_1, Gamma_2$,
    ),
  )
]

Thus, to pattern match on a pair inside of an unboxing pattern, we must
be able to compute $r times.l s$, where $r$ and $s$ are the
grades used to type the pair’s constituent sub-patterns. For the
semirings where we wish to permit the full $⊗$ distributive law we
can set $times.l$ to be the (partial) least-upper bound $union.sq$ derived from the
preordering which recovers the existing pattern matching typing, e.g.,
for the exact usage semiring ($NN$ with pre-ordering as equality) this
means that $times.l$ is only defined when $r = s$.

For graded modalities where we wish to disallow the 'push' behaviour we
can leave $r times.l s$ undefined for the relevant grades. In this way, we
can recover the power of linear logic’s $!$ in our calculus via the
pre-ordered semiring ${0, 1, omega}$ (none-one-tons)
with $!A = square_omega A$. The semiring is defined with $r + s = r$ if $s = 0$, $r + s = s$ if
$r = 0$ and otherwise $omega$, and $r * 0 = 0 * r = 0$, $r * omega = omega * r = omega$ (for $r eq.not 0$), and
$r * 1 = 1 * r = r$ with ordering $0 subset.eq.sq omega$ and $1 subset.eq.sq omega$. This semiring allows us to represent both linear and
non-linear use: variables graded with 1 must be used linearly, with 0
must be discarded, and a grade of $omega$ permits unconstrained use à
la linear logic’s $!$. We then define $r times.l s$ for this semiring as:

#math.equation(numbering: "(1)")[
  $
    r times.l s = cases(
      1 & quad r = 1 and s = 1,
      bot & quad "otherwise",
    )
  $
]

i.e., if either of the grades is not 1, then $times.l$ is undefined and we cannot
apply the \[PPROD\] pattern typing rule, thus disallowing $!(A ⊗ B) -> !A ⊗ !B$ and recovering the strength of $!$
for intuitionistic multiplicative exponential linear logic (IMELL):

#strong[Theorem 1] (Equivalent expressivity) #strong[.] #emph[The
  adjusted] GRCORE #emph[calculus, for the none-one-tons semiring with] $!A = square_omega A$, #emph[has the same expressive power as IMELL.]

#emph[The equivalence in expressivity follows by a translation. In the
  case of the] GRCORE $arrow$ IMELL direction, we interpret contexts and
types directly, but a type-directed translation is then required for the
term. In the opposite direction, a more syntactic translation is
possible, since we follow Benton et al.’s full term assignment for IMELL
\[BBdPH93\]. The appendix \[HMWO21\] provides the proof.

- (#strong[GRCORE into IMELL]) $quad Gamma tack t : A quad arrow.r.double quad exists M . ⟦ Gamma ⟧ tack_("IMELL") M : ⟦ A ⟧$
- (#strong[IMELL into GRCORE]) $quad Gamma tack_("IMELL") M : T quad arrow.r.double quad ⟦ Gamma ⟧ tack ⟦ M ⟧ : ⟦ T ⟧$

The translation from GRCORE to IMELL maps $square_omega A$ to $!⟦A⟧$, $square_1 A$ to just $⟦A⟧$, and $square_0 A$ to the unit type $1$, and similarly
for graded assumptions (e.g., $x : [A]_omega$ to $x : !⟦A⟧$ and $x : [A]_0$ to $x : 1$).
Note that $square_0 A$ must #emph[not] be mapped to $!⟦A⟧$: the term
$lambda z . "let" [y] = z "in" (y, [y])$ has type $square_1 alpha ⊸ alpha ⊗ square_0 alpha$ in the adjusted
GRCORE (since $1 + 0 = 1$), but $alpha ⊸ alpha ⊗ !alpha$ is not provable in IMELL for an atomic type $alpha$.

The operation $times.l$ is inspired by the coeffect calculus of Petricek et
al.~\[POM14\] whose graded type system includes $times.l$ as an operation to
control splitting of resources to subterms, modelled by colax
monoidality of a graded comonad $times.l_(r, s, A, B) : cal(D)_(r times.l s)(A ⊗ B) -> (cal(D)_r A ⊗ cal(D)_s B)$.

== #strong[5 Implementation in Granule]
<implementation-in-granule>
The partial operation $times.l$ is implemented within the Granule compiler as part
of the type checker. Granule has a more general notion of type
constructors than we defined in our calculus here, including user
defined algebraic data types (ADTs) as well as generalised algebraic
data types (GADTs). Thus, instead of occurring solely in the presence of
product patterns, $times.l$ is applied whenever a pattern match occurs against a
constructor with at least one sub-pattern.

We implement $times.l$ via a constraint on the grades given by the data
constructor pattern (inside a box pattern) which is then discharged via
an SMT solver. If such a constraint is satisfiable, then the type
checking of the pattern may proceed. The nature of information flow in
the type checking of a Granule pattern match is such that the grades
$r$ and $s$ in $r times.l s$ are necessarily the same,
i.e.~$r times.l r$, and we require that this is then defined at $r$.
For the 0-1-$omega$ semiring (called `LNL` in Granule and written with
elements `0`, `1`, `Many`), where $omega$ is used to model the
exponential modality, $r times.l r$ is then defined only when $r = 1$.
We can therefore no longer write the (previously type checkable) Granule
program:

#codeblock(label: "Ill-typed Granule")[
  ```granule
  push : ∀ {a b : Type} . (a, b) [Many] → (a [Many], b [Many])
  push [(x, y)] = ([x], [y])
  ```
]

== #strong[6 Conclusions]
<conclusions>
Graded types trace their origins from intuitionistic linear logic. The
inability in many of these systems to capture the strength of $!$
therefore represents an interesting divergence in their expressive power
from linear logic. The solution described here allows our calculus to
retain both the power of $"push"$ and of $!$, by defining when grades
can be 'pushed inside a tensor' via the algebraic structure of grades.
This approach is readily adaptable to the other graded systems described
here. This has implications for other ongoing work on the automatic
derivation of distributive laws for arbitrary types in a graded type
system \[HVO20\]. The ability to define where $"push"$ is possible
for a given semiring imposes an additional constraint on when the
$"push"$ distributive law for a type can be automatically calculated.

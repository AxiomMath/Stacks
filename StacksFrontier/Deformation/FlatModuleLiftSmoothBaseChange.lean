module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.Deformation.FlatAlgebraLiftCompletion
public import StacksFrontier.Deformation.FlatModuleLift

/-!
# Stacks 0DZ2 with a smooth upper-left horizontal arrow

Stacks 0DZ2 (Lemma 93.12.2) compares two flat-module-lifting problems across a diagram
`A' → P' → Q'` over `A → P → Q`. As the source states it the lemma is **false**: it is refuted,
at every universe, by `Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatement`
and `…_ulift`, and in the form that writes out every one of the source's hypotheses by
`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful` and
`…_ulift`. The counterexample is the Artin–Schreier obstruction on the nodal cubic, with
`A' = NC[t]/t³` and `P' = A'[x]/(x² − t·x − t²·ω)`.

In that counterexample `P'` is flat over `A'` and **not smooth**. Every consumer of 0DZ2 in this
library applies it with `P'` a *polynomial* algebra `MvPolynomial (Fin n) A'`, built from a
finite-type presentation of the algebra being deformed:
`Deformation.hasFlatAlgebraLift_henselization_iff` and
`Deformation.hasFlatAlgebraLift_adicCompletion_of_hasFlatAlgebraLift` both do this, and so does
the source's proof of Stacks 0DZ7. So the statement those three tags need is 0DZ2 with `P'`
smooth over `A'`, and the refutation says nothing about it. This file states that form and
records what is and is not known about it.

## Main definitions

* `Deformation.FlatModuleLiftBaseChangeStatementSmooth`: **Stacks 0DZ2 with `P'` smooth over
  `A'`.** It is `Deformation.FlatModuleLiftBaseChangeStatementFaithful` — the source's statement
  with every hypothesis written out — plus the single hypothesis `Algebra.Smooth A' P'`. Nothing
  else is changed: the cartesian squares, the four flat horizontals, the nilpotent kernels, the
  ideal `J'` with `P'/J' = Q'/J'Q'`, the finite `A`-flat `M` and the local liftability of `M` on
  `J'` are all carried over verbatim.
* `Deformation.SmoothDevissage.ExtendsToSecondOrder`: the elementary lifting problem the
  dévissage of 0DZ2 runs into, for `P'` a polynomial algebra — see below.
* `Deformation.splitTensorHom` and `Deformation.splitReduce`: the trivial lift `A' ⊗[A] P` of
  `P` and the trivial lift `A' ⊗[A] M` of `M` along a *split* base `A' → A`, each with its
  reduction back to `P` and to `M`; `Deformation.splitTensorEndHom` is the action of the first on
  the second. These are the construction behind
  `Deformation.exists_flatModuleLift_of_split`.

## Main results

* `Deformation.flatModuleLiftBaseChangeStatementSmooth_of_faithful`: the refuted general
  statement implies the smooth one. So the smooth form is *weaker*; stating it has not
  strengthened anything, and in particular it is not refuted by transport from the general
  refutation.
* `Deformation.exists_flatModuleLift_of_thickening`: **clause (1) is the weakest lifting
  question among all thickenings of `P`.** Call an `A'`-algebra `R` a *thickening of `P` over
  `A' → A`* when `R → P` is surjective with kernel `ker(A' → A) · R`, which is 0DZ2's own
  condition on `P' → P`. If `M` has an `A'`-flat `R`-module lift for *some* thickening `R` —
  `R` not assumed flat, Noetherian or of finite presentation — then it has an `A'`-flat
  `P'`-module lift, provided only that `P'` is formally smooth over `A'`. The lift is the same
  module, with `P'` acting through an `A'`-algebra map `P' → R` that formal smoothness supplies.
* `Deformation.exists_flatModuleLift_iff_of_formallySmooth`: **clause (1) does not depend on the
  smooth lift of `P`.** For two thickenings of `P`, both formally smooth over `A'`, the two
  forms of clause (1) are equivalent. So clause (1) is a property of `A' → A`, of `P` and of `M`
  alone; in particular it is the same question at `P' = MvPolynomial (Fin n) A'`, the
  presentation every consumer of 0DZ2 in this library uses.
* `Deformation.exists_flatModuleLift_of_lift_along_tower`: **a lift after a base change that
  leaves `M` unchanged is a lift.** For two surjections `P' → P` and `S' → S` over `A' → A`,
  both with kernel the image of `ker(A' → A)`, in a commuting square, an `A'`-flat `S'`-module
  lift of `S ⊗_P M` is an `A'`-flat `P'`-module lift of `M` as soon as `S ⊗_P M` is `M`. No
  smoothness, flatness, finiteness or Noetherian hypothesis is used.
* `Deformation.exists_flatModuleLift_of_localizationLift`: **0DZ2's own local liftability
  hypothesis gives clause (1) at any `g` whose image acts invertibly on `M`.** The hypothesis is
  the body of `hlocal` copied verbatim at a single `g`. Consequence: `supp M` must meet `V(J')`,
  for otherwise some `j ∈ J'` acts on `M` as the identity and the local lift at `j` is already a
  global one.
* `Deformation.exists_flatModuleLift_of_split`: **over a split base the lifting problem has a
  trivial solution.** If `A' → A` admits a ring section and `P'` is formally smooth over `A'`,
  then *every* `A`-flat `P`-module `M` has an `A'`-flat `P'`-module lift, namely `A' ⊗[A] M`.
  None of 0DZ2's other hypotheses is used: no ring is Noetherian, `M` is not finite, there is no
  ideal `J'` and no local liftability, and `P'` is not assumed of finite presentation. This is
  now a corollary of the two results above: a split base is exactly what makes `A' ⊗[A] P` a
  thickening of `P`, and `A' ⊗[A] M` a module lift of `M` over it.
* `Deformation.exists_flatModuleLift_iff_baseChange_of_ringHom_section`: **the smooth form of
  0DZ2 is a theorem over a split base**, both of its clauses holding there. So a counterexample
  to `Deformation.FlatModuleLiftBaseChangeStatementSmooth` must have a base `A' → A` with no
  ring section — which is what the known refutation of the general statement does not have: its
  base `NC[t]/t³ → NC` splits, by the library's own
  `Deformation.Examples.MaurerCartanWindow.cst` and
  `Deformation.Examples.ArtinSchreier.redA_cst`.
* `Deformation.flatModuleLiftBaseChangeStatementSmooth_of_ringHom_section`: the same conclusion
  written out in the shape of `Deformation.FlatModuleLiftBaseChangeStatementSmooth` itself —
  that statement, with a ring section of `A' → A` added to its hypotheses, is **proved**. It is
  there so that the match with the statement can be checked by reading rather than by comparing
  hypothesis lists.
* `Deformation.SmoothDevissage.extendsToSecondOrder_iff`: **the obstruction of the dévissage,
  computed, over a polynomial `P'`.** For `A' = ZMod 8`, `A = ZMod 2` and `P' = A'[x, y]`, an
  `A'/I²`-flat lift of `M = A²` in which `x` and `y` act by `2E` and `2F` extends to an
  `A'`-flat `P'`-module lift if and only if `4·(E·F) = 4·(F·E)`, i.e. if and only if `E` and `F`
  commute modulo `2`. The obstruction is the **commutator**.
* `Deformation.SmoothDevissage.extendsToSecondOrder_add_two_smul`: that obstruction depends on
  the first-order data only modulo `2`, which is what makes the parametrisation used here the
  torsor parametrisation pulled back along a surjective group homomorphism.
* `Deformation.SmoothDevissage.not_extendsToSecondOrder_add` and
  `Deformation.SmoothDevissage.not_exists_additive_obstructionVariation`: the set of
  first-order data that extend is **not closed under addition**, hence the obstruction variation
  along the torsor of lifts is not additive — *with `P'` a polynomial algebra, hence free and
  smooth over `A'`*.

## Implementation notes

**Why `Algebra.Smooth A' P'` and not `P' = MvPolynomial (Fin n) A'`.** The three consumers
listed above each build `P' = MvPolynomial (Fin n) A'` with its standard algebra structure, and
there `Algebra.Smooth A' P'` is `⟨inferInstance, inferInstance⟩`:
`Algebra.FormallySmooth A' (MvPolynomial (Fin n) A')` is
`Algebra.instFormallySmoothMvPolynomial` and `Algebra.FinitePresentation` of a polynomial algebra
on a finite type is an instance. (`Algebra.Smooth` is itself not an instance for `MvPolynomial`
in Mathlib, so the consumers supply it with one `haveI`; nothing else is needed.) Since the
abstract hypothesis is discharged as cheaply as the concrete one and keeps the statement a
clause-by-clause reading of the source plus one word, there is no reason to hard-wire the
polynomial algebra, which would additionally force a transport of the statement's abstract `P'`
through a ring isomorphism — the step the implementation notes of
`StacksFrontier.Deformation.FlatModuleLiftLocalization` identify as the expensive one.

**What is proved here, and what is not.** The statement is stated and *not proved in general*.
What is proved is: the trivial implication from the refuted general statement; **the statement
itself over a split base** (`Deformation.exists_flatModuleLift_iff_baseChange_of_ringHom_section`,
where both clauses hold unconditionally); and the computation of the dévissage's obstruction over
a polynomial `P'`, which settles the question the smooth form was expected to answer **in the
negative**: smoothness of `P'` does *not* rescue the dévissage from `Iⁿ = 0` to `I² = 0` that the
source leaves as `details omitted`. The two routes through that
dévissage are both blocked for a smooth `P'`, for the same reasons they are blocked in general,
and the reason is structural: the groups that carry the obstruction are `Ext^i_P(M, M ⊗_P K)`
for `M` an arbitrary finite `A`-flat `P`-module, and smoothness of `P'` over `A'` says nothing
about them. Writing `I = ker(A' → A)`, `A'' = A'/I^{n-1}`, `Ī = I/I^{n-1}` and
`P'' = P' ⊗_{A'} A''`:

1. *The route that strengthens the square-zero case to surjectivity on lift sets* — so that the
   intermediate `A''`-flat `P''`-lift `M''` of `M` can be **selected** with
   `Q'' ⊗_{P''} M'' ≅ N''` — needs `Ext¹_P(M, M ⊗_P ĪP)` to be `J'`-power torsion, because
   through the torsor structure on the set of lifts the required surjectivity is that of
   `Ext¹_P(M, M ⊗_P ĪP) → Ext¹_Q(N, N ⊗_Q ĪQ)`, which by Stacks 0A6A and Stacks 05EC holds
   exactly on the `J'`-power torsion part. It fails with `P'` a polynomial algebra. Take `k` a
   field, `A' = k[t]/(t³)`, `A = k`, `P' = A'[y, z]` — free, hence smooth, over `A'` — so that
   `P = k[y, z]`, and take `J' = (y)P'` and `M = P/(z)`. Then `ĪP ≅ P`, the resolution
   `0 → P → P → M → 0` by multiplication by `z` gives `Ext¹_P(M, M ⊗_P ĪP) ≅ M/zM = M = k[y]`,
   and `k[y]` is not `(y)`-power torsion: no element other than `0` is killed by a power of `y`.
   The comparison map `k[y] → k[y] ⊗_P Q` is therefore not surjective, for `Q` either the
   `(y)`-adic completion of `P` or a localization of it. Smoothness of `P'` is irrelevant to
   this because the group is an `Ext` *of `M`*, and `M = P/(z)` is a perfectly ordinary finite
   `A`-flat `P`-module. (The same failure, at a square-zero `A'`, is recorded as route 2 of the
   implementation notes of `StacksFrontier.Deformation.FlatAlgebraLiftLocalization` on another
   branch; the example above is at the nilpotency index the dévissage actually needs.)
2. *The route that carries obstruction classes rather than lifts* needs the variation map
   `∂ : Ext¹_P(M, M ⊗_P K_j P) → Ext²_P(M, M ⊗_P K_{j+1} P)` along the torsor of lifts to be
   additive, so that `im ∂` is a submodule and Stacks 05EC has a quotient to act on. It is not
   additive: it is `∂(e) = δ(e) + e ∪ e` with `δ` a Bockstein and `∪` the Yoneda square, and the
   square term survives at `j = 1`, which is the stage the induction starts at. **This file
   proves that the square term survives with `P'` a polynomial algebra.** Take `A' = ZMod 8`,
   `A = ZMod 2`, so `I = (2)` with `I³ = 0` and `I² ≠ 0`; take `P' = A'[x, y]`, free and smooth
   over `A'`, so `P = (ZMod 2)[x, y]`; and take `M = (ZMod 2)²` with `x` and `y` acting as zero,
   which is finite over `P` and flat over the field `A`. A module over `A'[x, y]` free over `A'`
   is an `A'`-module together with two commuting endomorphisms, so an `A''`-flat `P''`-lift of
   `M` is a free `ZMod 4`-module of rank two with `x` and `y` acting by a commuting pair of
   matrices reducing to `0` mod `2`, i.e. by `2E` and `2F` — and `2E` and `2F` commute over
   `ZMod 4` automatically, so every pair `(E, F)` occurs. Such a lift extends to an `A'`-flat
   `P'`-lift exactly when `2E` and `2F` can be corrected by multiples of `4` to a commuting pair
   over `ZMod 8`, and `(2E + 4G)(2F + 4H) = 4·E·F` identically — every cross term is a multiple
   of `8` — so the criterion is `4·(E·F) = 4·(F·E)`, the vanishing of the commutator mod `2`.
   That is `Deformation.SmoothDevissage.extendsToSecondOrder_iff`, and the commutator is not
   additive in `(E, F)`: `(e, 0)` and `(0, f)` are unobstructed for `e = !![0, 1; 0, 0]` and
   `f = !![0, 0; 1, 0]`, while their sum `(e, f)` is not, because `e·f = !![1, 0; 0, 0]` and
   `f·e = !![0, 0; 0, 1]` differ after multiplication by `4`. So the set of unobstructed classes
   is not a subgroup and no additive `∂` describes it.

   The step this file does **not** formalize is the identification of the parametrization
   `(E, F)` with the `Ext¹`-torsor action — that the difference of the classes of two lifts in
   `Ext¹_P(M, M ⊗_P K_1 P)` is the difference of their structure matrices. That is the defining
   property of the torsor action and no `Ext` API in this repository presents it; it is the same
   gap recorded in the implementation notes of
   `StacksFrontier.Deformation.FlatModuleLiftLocalization`. Two further links are bookkeeping and
   are spelled out here so that they are not mistaken for mathematics. First, the equivalence
   between an `A'[x, y]`-module structure on an `A'`-module and a commuting pair of
   endomorphisms is the universal property of the polynomial algebra; and an `A'`-flat module
   lift of the finite `M` is finitely generated over `A'` by Nakayama against the nilpotent `I`,
   hence free, so it is given by matrices. Second, `2E + 4G` ranges over exactly the matrices
   over `ZMod 8` whose reduction mod `4` is the prescribed first-order action `2E`, because
   `4·M_ι(ZMod 8)` is the kernel of `M_ι(ZMod 8) → M_ι(ZMod 4)`; the parameter `(E, F)` below is
   therefore used only modulo `2`, which
   `Deformation.SmoothDevissage.extendsToSecondOrder_add_two_smul` proves, and since the set of
   unobstructed parameters is accordingly the preimage of the set of unobstructed first-order
   lifts under a surjective group homomorphism, being closed under addition is equivalent
   upstairs and downstairs.

**What the counterexample of item 2 does and does not show.** It shows that an `A''`-flat
`P''`-lift of `M` which does extend and one which does not both exist, so that the dévissage
cannot proceed by handing the square-zero case whichever intermediate lift the induction
produced. It does **not** refute the smooth form of 0DZ2: `M = (ZMod 2)²` itself lifts all the
way, by letting `x` and `y` act as zero over `ZMod 8`. The two clauses of the conclusion are
both true there.

**No counterexample to the smooth form can have a split base: this is a theorem here.**
Suppose `A' → A` admits a ring section `s : A → A'` — equivalently that `A'` is an `A`-algebra
compatibly with the surjection. Then the smooth form's conclusion holds *unconditionally*, both
clauses being true, which is
`Deformation.exists_flatModuleLift_iff_baseChange_of_ringHom_section`. The witness for clause
(1) is the trivial lift `A' ⊗[A] M`, and what has to be produced is a `P'`-action on it:
`A' ⊗[A] P` is an `A'`-algebra whose reduction `A' ⊗[A] P → P`, `x ⊗ p ↦ x̄ · p`, is surjective
with kernel `ker(A' → A) · (A' ⊗[A] P)` (`Deformation.splitTensorHom_surjective`,
`Deformation.ker_splitTensorHom`), hence nilpotent, so formal smoothness of `P'` over `A'` lifts
the structure map `P' → P` to an `A'`-algebra map `φ : P' → A' ⊗[A] P`, and `A' ⊗[A] M` becomes
a `P'`-module through `φ` and the factorwise action `Deformation.splitTensorEndHom`. It is
`A'`-flat because `M` is `A`-flat, and reducing it across `P' → P` gives back `M`, by
`Deformation.splitReduce_splitTensorEndHom`. Clause (2) is then its base change
`Q' ⊗_{P'} (A' ⊗[A] M)`, flat over `A'` by `Module.Flat.tensorProduct_of_flat_base`. The
argument uses none of 0DZ2's other hypotheses — no Noetherian ring, no finiteness of `M`, no
ideal `J'`, no local liftability, nothing about the right-hand square beyond flatness of
`P' → Q'` — and only `Algebra.FormallySmooth A' P'`, not `Algebra.Smooth A' P'`. *Correction to
an earlier draft of this note*: it argued through `P' ≅ P ⊗_A A'`, by uniqueness of lifts of a
smooth algebra. That is true but is more than the proof needs, and the uniqueness step is
formalized nowhere here: nothing requires `φ` to be injective or surjective.

*What the split hypothesis is really doing*, isolated: it produces **one** `A'`-algebra `R` with
`R → P` surjective with kernel `ker(A' → A) · R`, namely `R = A' ⊗[A] P`, together with an
`A'`-flat `R`-module reducing to `M`, namely `A' ⊗[A] M`. Nothing else about the section is used,
and formal smoothness of `P'` enters only to map `P'` into `R`. That observation is
`Deformation.exists_flatModuleLift_of_thickening`, from which
`Deformation.exists_flatModuleLift_of_split` is now derived; see the section on thickenings.

This is exactly what the nodal-cubic refutation of the general statement cannot survive. Its
base is `A' = NC[t]/t³ → NC = A`, which splits — the section is the library's
`Deformation.Examples.MaurerCartanWindow.cst : NC →+* Trunc3 NC` and
`Deformation.Examples.ArtinSchreier.redA_cst` says the reduction undoes it — and its whole
force comes from `P' = A'[x]/(x² − t·x − t²·ω)` being a *non-trivial* deformation of
`P = NC[x]/(x²)`: the relation `x² = t·x + t²·ω` turns liftability of `M` into the
Artin–Schreier equation
`α² − α = ω`. Over a split base a formally smooth `P'` admits the map `φ` above, which is all
the lifting argument uses, so no adjustment of `Q'`, `J'` or `M` in that counterexample reaches
the smooth form. Consistently, `P'` there is not smooth: it is finite free of rank two over
`A'`, so smoothness would make it étale, and its reduction `P = NC[x]/(x²)` has non-reduced
fibres over `NC`, so `P` is not even smooth over `A`.

**The honest status of the smooth form, and the shape a counterexample would have to have.**
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` is **open**. Four things about it are
settled here, and they are restrictions on any counterexample.

1. *`M` must lift over no thickening of `P` at all*
   (`Deformation.exists_flatModuleLift_of_thickening`). This subsumes the split-base
   restriction: a base with a ring section is one for which `A' ⊗[A] P` is a thickening of `P`
   carrying the lift `A' ⊗[A] M`, so "the base admits no ring section" is the special case
   `R = A' ⊗[A] P` of the general requirement.
2. *Clause (1) cannot be adjusted by changing the presentation*
   (`Deformation.exists_flatModuleLift_iff_of_formallySmooth`): among formally smooth
   thickenings of `P` the question is one and the same, so a counterexample may be sought at
   `P' = MvPolynomial (Fin n) A'` with no loss, and found there with no gain.
3. *`supp M` must meet `V(J')`* (`Deformation.exists_flatModuleLift_of_localizationLift`, up to
   one elementary step identified below): if it does not, 0DZ2's own local liftability
   hypothesis already supplies a global lift.
4. *No route to a proof through the source's own dévissage survives even for a polynomial `P'`*
   (the section below).

A fifth restriction comes from elsewhere in the library, in a shape close to but not literally
this statement's: for a square-zero thickening `P' → P` and a finite `M`, 0DZ2 is *proved* in
`StacksFrontier.Deformation.FlatModuleLiftLocalization`, with `P` and `Q` the literal base changes
`P' ⊗_{A'} A` and `Q' ⊗_{A'} A` and the conclusion written in `ModuleCat`; so a counterexample
is expected to need `ker(P' → P)² ≠ 0`, though transporting that theorem into the present shape
is not done here.

The expected shape of a counterexample is therefore: a base with no ring section —
`ZMod 8 → ZMod 2`, or a Witt-vector thickening of a characteristic-`p` ring — at nilpotency
index at least three, and a finite `A`-flat module on a smooth affine `A`-scheme whose lifts
exist on each `D(g)` for `g ∈ J'` and over `Q'` but admit no compatible global choice. Whether
such data exist is not settled, and no claim either way is made here.

**The two forced features above, in detail.** They are recorded because they are the first
things a search for a witness runs into.

*The support of `M` must meet `V(J')`* — restriction 3, proved here but for one elementary step.
Suppose it does not, i.e. `J' + ann_P(M) = P`. Write `1 = j̄ + a` with `j ∈ J'` and
`a ∈ ann_P(M)`; then `j̄` acts on `M` as the identity, so `P_j̄ ⊗_P M ≅ M`. From there on it is
`Deformation.exists_flatModuleLift_of_localizationLift`: `hlocal` at `j` produces an `A'`-flat
`(P')_j`-module `L` lifting `P_j̄ ⊗_P M`, and `L` restricted along `P' → (P')_j` is an `A'`-flat
`P'`-module whose reduction is the same quotient `L / ker(A' → A) · L`, because the localized
square is again cartesian, `ker((P')_j → P_j̄) = ker(A' → A) · (P')_j`. So clause (1) holds and
the data are not a counterexample. The step that is **not** formalized is the first one, from
`1 - j̄ ∈ ann_P(M)` to `P_j̄ ⊗_P M ≅ M`, which is the hypothesis `hM` of that theorem.
(What the symmetric situation `supp M ⊆ V(J')` does is *not* settled: the natural argument wants
`Q'/J'ⁿQ' ≅ P'/J'ⁿ` for all `n`, and `hquot` gives only `n = 1`.)

*`P'` must have relative dimension at least two over `A'`, for an `A`-projective `M`* — this one
is reasoning, not formalized. If `M` is
projective of finite type over `A` and `P' = A'[x]`, then a projective `A'`-module lift `M'` of
`M` exists, `End_{A'}(M') → End_A(M)` is surjective because `M'` is finite projective, so the
action of the single variable `x` lifts to `M'`, making it an `A'`-flat `A'[x]`-module lift of
`M`; clause (1) holds. The usual form of this remark — "`pd_P M ≤ 1`, so every `Ext²` obstructing
a filtration step vanishes" — is **not** a correct argument in the generality of the statement:
it needs `A` regular, and for `A` singular (`A = NC`, say) the ring `P = A[x]` has infinite
global dimension and `Ext²_P(M, −)` need not vanish on a finite `A`-flat `M`. The projectivity
hypothesis is what makes the remark go through, and it is a hypothesis on `M`, not on `P'`.

**The 0DZ2 registration is not touched.** `@[stacks 0DZ2]` sits in
`StacksFrontier.Deformation.FlatModuleLift` and
`StacksFrontier.Deformation.FlatModuleLiftLocalization` and stays there. No attribute is added,
moved or removed by this file, and the tag is *not* claimed for the smooth form: the tag's statement
is the source's general one, which is false, and
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` is a different, strictly weaker statement.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace Deformation

/-- **Stacks 0DZ2 with `P'` smooth over `A'`, for a finite module.**

This is `Deformation.FlatModuleLiftBaseChangeStatementFaithful` — Stacks 0DZ2 with every
hypothesis of the source written out, restricted to a finite module — together with the single
extra hypothesis `Algebra.Smooth A' P'`. Nothing else differs: the two cartesian squares are
carried by `hsurjP`/`hkerP` and `hsurjQ`/`hkerQ`, the four flat horizontal arrows by
`Module.Flat A' P'`, `Module.Flat P' Q'`, `Module.Flat A P` and `Module.Flat P Q` (with
`Module.Flat A' Q'`, the composite of the first two, carried as well), the nilpotence of the
vertical kernels by `hnilA`, the ideal condition by `hquot`, and `M` is finite over `P` and flat
over `A` with its localizations `M_g` liftable over `(P')_g` for every `g ∈ J'`.

The hypothesis is appended after the flatness hypotheses, so an application of
`Deformation.FlatModuleLiftBaseChangeStatementFaithful` becomes an application of this statement
by supplying one further argument.

**How a consumer applies it.** The three consumers currently consume
`Deformation.FlatModuleLiftBaseChangeStatement`, which carries neither `Module.Flat A P` nor the
smoothness, so an application of `h : FlatModuleLiftBaseChangeStatementSmooth` at their data is
their old application with two arguments inserted after `hfPQ`:

```
h A' A P' P Q' Q hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ
  (flat_of_surjective_of_ker_eq_map A' A P' P hsurjA hsurjP hkerP hfAP')
  ⟨inferInstance, inferInstance⟩ J' hquot M N hN hlocal
```

`Deformation.flat_of_surjective_of_ker_eq_map` is the lemma that makes `Module.Flat A P`
redundant, and `⟨inferInstance, inferInstance⟩` is `Algebra.Smooth A' P'` at
`P' = MvPolynomial (Fin n) A'`, whose two fields are `Algebra.instFormallySmoothMvPolynomial` and
the `Algebra.FinitePresentation` instance of a polynomial algebra on a finite type.

**Why this form.** The general statement is **false**, at every universe
(`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful_ulift`), and
its counterexample has `P' = A'[x]/(x² − t·x − t²·ω)`, which is finite flat and *not* smooth over
`A'`. The three consumers of 0DZ2 in this library instantiate it at a polynomial algebra
`P' = MvPolynomial (Fin n) A'`, which is smooth, so this is the form they need. See the module
documentation for how a consumer discharges the hypothesis, and for the status of the statement:
it is **not proved**, and smoothness of `P'` is shown there not to repair the source's dévissage
from a nilpotent to a square-zero kernel. -/
def FlatModuleLiftBaseChangeStatementSmooth : Prop :=
  ∀ (A' A P' P Q' Q : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A' Q]
    [Algebra A P] [Algebra A Q] [Algebra P' P] [Algebra P' Q'] [Algebra P' Q]
    [Algebra P Q] [Algebra Q' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower A' Q' Q] [IsScalarTower A P Q] [IsScalarTower P' P Q]
    [IsScalarTower P' Q' Q],
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    Function.Surjective (algebraMap P' P) →
    RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') →
    Function.Surjective (algebraMap Q' Q) →
    RingHom.ker (algebraMap Q' Q) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') →
    Module.Flat A' P' → Module.Flat A' Q' → Module.Flat P' Q' → Module.Flat P Q →
    Module.Flat A P →
    Algebra.Smooth A' P' →
    ∀ (J' : Ideal P'),
      Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q')
        Ideal.le_comap_map) →
    ∀ (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
      [Module.Finite P M] [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N],
      Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N) →
      (∀ g ∈ J',
        letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
          (Localization.awayMap (algebraMap P' P) g).toAlgebra
        ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
          (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
          Module.Flat A' L ∧ Nonempty
            ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
              ≃ₗ[Localization.Away (algebraMap P' P g)]
                (Localization.Away (algebraMap P' P g) ⊗[P] M))) →
      ((∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
          (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
          Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
        (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
          (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
          Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N)))

/-- **The smooth form is weaker than the source's statement.** It has one hypothesis more —
`Algebra.Smooth A' P'` — and is otherwise the same, so it follows from
`Deformation.FlatModuleLiftBaseChangeStatementFaithful` by forgetting that hypothesis.

Two things follow. First, stating the smooth form has not strengthened anything, so it is a
genuine weakening of a false statement and not a different claim smuggled in beside it. Second,
the refutation does **not** transport: a refutation of the smooth form would refute the general
one by this implication, whereas the known refutation of the general one says nothing about the
smooth form, and the module documentation shows that its counterexample cannot be adapted,
because its base `NC[t]/t³ → NC` splits and over a split base the smooth form's conclusion holds
unconditionally. -/
theorem flatModuleLiftBaseChangeStatementSmooth_of_faithful
    (h : FlatModuleLiftBaseChangeStatementFaithful.{u}) :
    FlatModuleLiftBaseChangeStatementSmooth.{u} := by
  intro A' A P' P Q' Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ hfAP _hsm
  exact h A' A P' P Q' Q hsurjA hnilA hsurjP hkerP hsurjQ hkerQ hfAP' hfAQ' hfPQ' hfPQ hfAP

/-! ### Clause (1) of the smooth form does not depend on the smooth lift of `P`

Call an `A'`-algebra `R` a *thickening of `P` over `A' → A`* when `R → P` is surjective with
kernel `ker(A' → A) · R` — the condition `hkerP` of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` with `R` in place of `P'`, so that `P'`
itself is one. Clause (1) of that statement asks for an `A'`-flat `P'`-module lift of `M`, and
the same question can be asked of any thickening.

The theorems below say that, as soon as `P'` is formally smooth over `A'`, clause (1) is the
*weakest* of those questions, and that among formally smooth thickenings it does not depend on
the thickening at all. The reason is one application of formal smoothness: a thickening `R` of
`P` is a nilpotent thickening, so `P' → P` lifts to an `A'`-algebra map `φ : P' → R`, and an
`A'`-flat `R`-module lift of `M` becomes an `A'`-flat `P'`-module lift of `M` by restriction
along `φ` — the two reductions agree because both kill exactly `ker(A' → A) · M'`.

This generalises the split-base theorem of the next section, which is the case
`R = A' ⊗[A] P`, and strengthens what a counterexample has to do: not merely to have a base
with no ring section, but to have an `M` that lifts over **no** thickening of `P` over
`A' → A` whatsoever.
-/

section Thickening

/-- **Two ideals cut out by the same ideal of `A'` act on a module in the same way.** If `JS`
is contained in the image of `I` in `S` and `JT` contains the image of `I` in `T`, then
`JS · N ⊆ JT · N` for any module `N` carrying compatible actions of `A'`, of `S` and of `T`.

Both submodules are in fact the `A'`-submodule `I · N`, but that is not what gets used: the
statement is in the form in which the comparison of two reductions needs it, and applying it
twice with the roles of `S` and `T` exchanged gives the equality of the two underlying sets.
The induction is over the *generators* of `Ideal.map`, and the only step that is not formal is
the one for a multiple `s · y` of a generator, which is handled by commuting `s` past `y`:
`(s · y) • n = y • (s • n)`. -/
theorem mem_smul_top_of_mem_smul_top {A'' S T N : Type u} [CommRing A''] [CommRing S]
    [CommRing T] [Algebra A'' S] [Algebra A'' T] [AddCommGroup N] [Module S N] [Module T N]
    [Module A'' N] [IsScalarTower A'' S N] [IsScalarTower A'' T N] {I : Ideal A''}
    {JS : Ideal S} {JT : Ideal T} (hS : JS ≤ I.map (algebraMap A'' S))
    (hT : I.map (algebraMap A'' T) ≤ JT) {m : N}
    (hm : m ∈ JS • (⊤ : Submodule S N)) : m ∈ JT • (⊤ : Submodule T N) := by
  have key : ∀ y : S, y ∈ Ideal.span ((algebraMap A'' S) '' (I : Set A'')) →
      ∀ n : N, y • n ∈ JT • (⊤ : Submodule T N) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        intro n
        rw [IsScalarTower.algebraMap_smul, ← IsScalarTower.algebraMap_smul T i n]
        exact Submodule.smul_mem_smul (hT (Ideal.mem_map_of_mem _ hi)) Submodule.mem_top
    | zero => intro n; rw [zero_smul]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => intro n; rw [add_smul]; exact Submodule.add_mem _ (ha n) (hb n)
    | smul s a _ ha =>
        intro n
        rw [smul_eq_mul, mul_comm, mul_smul]
        exact ha (s • n)
  refine Submodule.smul_induction_on hm ?_ fun _ _ h1 h2 => Submodule.add_mem _ h1 h2
  intro y hy n _
  exact key y (hS hy) n

/-- Restricting an `A'`-flat `S'`-module lift along `P' → S'` gives a `P'`-module lift of `M`
whenever the two reductions of the lift are identified. -/
private theorem exists_flatModuleLift_of_lift_along_tower_aux
    {A' A P' P S' S : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
    [CommRing S'] [CommRing S] [Algebra A' A] [Algebra A' P'] [Algebra A' S']
    [Algebra P' P] [Algebra P' S'] [Algebra P S] [Algebra S' S] [IsScalarTower A' P' S']
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjS : Function.Surjective (algebraMap S' S))
    (hkerS : RingHom.ker (algebraMap S' S) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' S'))
    (hcomm : ∀ x : P',
      algebraMap S' S (algebraMap P' S' x) = algebraMap P S (algebraMap P' P x))
    (M : Type u) [AddCommGroup M] [Module P M]
    (L : Type u) [AddCommGroup L] [Module S' L] [Module A' L] [IsScalarTower A' S' L]
    (hflatL : Module.Flat A' L)
    (eL : (S ⊗[S'] L) ≃ₗ[S] (S ⊗[P] M)) (eM : (S ⊗[P] M) ≃ₗ[P] M) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] M) := by
  classical
  let _ : Module P' L := Module.compHom L (algebraMap P' S')
  have hsmulL : ∀ (x : P') (l : L), x • l = (algebraMap P' S' x) • l := fun _ _ => rfl
  have htowerL : IsScalarTower A' P' L := by
    refine ⟨fun x y l => ?_⟩
    rw [hsmulL, hsmulL, Algebra.smul_def, map_mul, mul_smul,
      ← IsScalarTower.algebraMap_apply A' P' S', IsScalarTower.algebraMap_smul]
  let _ : Module P' M := Module.compHom M (algebraMap P' P)
  have _ : IsScalarTower P' P M := ⟨fun x y z => by rw [Algebra.smul_def]; exact mul_smul _ y z⟩
  have hzero : ∀ l : L, (1 : S) ⊗ₜ[S'] l = 0 ↔
      l ∈ (RingHom.ker (algebraMap S' S)) • (⊤ : Submodule S' L) := by
    intro l
    rw [← quotKerSMulTopEquivBaseChange_mk hsurjS L l,
      (quotKerSMulTopEquivBaseChange hsurjS L).map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero]
  let r : L →ₗ[P'] M :=
    { toFun := fun l => eM (eL ((1 : S) ⊗ₜ[S'] l))
      map_add' := fun v w => by
        show eM (eL ((1 : S) ⊗ₜ[S'] (v + w))) = eM (eL ((1 : S) ⊗ₜ[S'] v)) +
          eM (eL ((1 : S) ⊗ₜ[S'] w))
        rw [TensorProduct.tmul_add, map_add, map_add]
      map_smul' := fun x l => by
        change eM (eL ((1 : S) ⊗ₜ[S'] (x • l))) = x • eM (eL ((1 : S) ⊗ₜ[S'] l))
        have h1 : (1 : S) ⊗ₜ[S'] ((algebraMap P' S' x) • l) =
            (algebraMap P S (algebraMap P' P x)) • ((1 : S) ⊗ₜ[S'] l) := by
          rw [TensorProduct.tmul_smul,
            ← IsScalarTower.algebraMap_smul S (algebraMap P' S' x), hcomm]
        rw [hsmulL, h1, map_smul, IsScalarTower.algebraMap_smul, map_smul]
        rfl }
  have hrr : ∀ l : L, r l = eM (eL ((1 : S) ⊗ₜ[S'] l)) := fun _ => rfl
  have hrsurj : Function.Surjective r := by
    intro y
    obtain ⟨l, hl⟩ := surjective_one_tmul S' S hsurjS L (eL.symm (eM.symm y))
    refine ⟨l, ?_⟩
    rw [hrr, show (1 : S) ⊗ₜ[S'] l = eL.symm (eM.symm y) from hl, eL.apply_symm_apply,
      eM.apply_symm_apply]
  have hker : LinearMap.ker r = (RingHom.ker (algebraMap P' P)) • (⊤ : Submodule P' L) := by
    refine le_antisymm (fun l hl => ?_) ?_
    · have h1 : (1 : S) ⊗ₜ[S'] l = 0 := by
        have hl0 := LinearMap.mem_ker.mp hl
        rw [hrr] at hl0
        have h2 : eL ((1 : S) ⊗ₜ[S'] l) = 0 := eM.injective (by rw [hl0, map_zero])
        exact eL.injective (by rw [h2, map_zero])
      exact mem_smul_top_of_mem_smul_top (I := RingHom.ker (algebraMap A' A))
        (le_of_eq hkerS) (le_of_eq hkerP.symm) ((hzero l).mp h1)
    · rw [Submodule.smul_le]
      intro j hj l _
      rw [LinearMap.mem_ker, map_smul]
      change (algebraMap P' P j) • r l = 0
      rw [RingHom.mem_ker.mp hj, zero_smul]
  refine ⟨L, inferInstance, inferInstance, inferInstance, htowerL, hflatL, ⟨?_⟩⟩
  have e2 : (L ⧸ (RingHom.ker (algebraMap P' P)) • (⊤ : Submodule P' L)) ≃ₗ[P'] M :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (r.quotKerEquivOfSurjective hrsurj)
  exact LinearEquiv.extendScalarsOfSurjective hsurjP
    ((quotKerSMulTopEquivBaseChange hsurjP L).symm.trans e2)

section Transport

variable {A' A P' P R : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [CommRing R] [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' R]
  [Algebra P' P] [Algebra R P] [IsScalarTower A' P' P] [IsScalarTower A' R P]

/-- **A lift over any thickening of `P` is a lift over a formally smooth one.** Let `A' → A`
have nilpotent kernel `I`, let `P' → P` and `R → P` both be surjections of `A'`-algebras with
kernel `I · P'` and `I · R`, and let `P'` be formally smooth over `A'`. If `M` has an `A'`-flat
`R`-module lift then it has an `A'`-flat `P'`-module lift, in the exact shape clause (1) of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` asks for. The lift produced is the *same
module*, with `P'` acting through an `A'`-algebra map `φ : P' → R`.

`R` is not assumed flat over `A'`, nor Noetherian, nor of finite presentation; `M` is not
assumed finite over `P` nor flat over `A`, and nothing is assumed about `Q'`, `J'` or the local
liftability. Only formal smoothness of `P'` is used, not `Algebra.Smooth A' P'`.

Two ingredients. `I · R` is nilpotent (`Deformation.isNilpotent_ideal_map`), so
`Algebra.FormallySmooth.liftOfSurjective` provides `φ` with `P' → R → P` the given `P' → P`.
And the reduction of `M'` across `P' → P` is its reduction across `R → P`: both are the
quotient of `M'` by the submodule generated by `I · M'`, which is
`Deformation.mem_smul_top_of_mem_smul_top` applied in both directions, so
`Deformation.quotKerSMulTopEquivBaseChange` turns the given `P ⊗_R M' ≅ M` into
`P ⊗_{P'} M' ≅ M`. -/
theorem exists_flatModuleLift_of_thickening [Algebra.FormallySmooth A' P']
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjR : Function.Surjective (algebraMap R P))
    (hkerR : RingHom.ker (algebraMap R P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' R))
    (M : Type u) [AddCommGroup M] [Module P M]
    (h : ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module A' M')
      (_ : IsScalarTower A' R M'), Module.Flat A' M' ∧ Nonempty ((P ⊗[R] M') ≃ₗ[P] M)) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] M) := by
  classical
  obtain ⟨M', _, _, _, _, hflat, ⟨e⟩⟩ := h
  have hnilR : IsNilpotent (RingHom.ker (algebraMap R P)) := by
    rw [hkerR]
    exact isNilpotent_ideal_map hnilA _
  let φ : P' →ₐ[A'] R :=
    Algebra.FormallySmooth.liftOfSurjective (IsScalarTower.toAlgHom A' P' P)
      (IsScalarTower.toAlgHom A' R P) hsurjR hnilR
  have hφ : ∀ x : P', algebraMap R P (φ x) = algebraMap P' P x := fun x => by
    have hx := Algebra.FormallySmooth.liftOfSurjective_apply
      (IsScalarTower.toAlgHom A' P' P) (IsScalarTower.toAlgHom A' R P) hsurjR hnilR x
    simpa using hx
  let _ : Algebra P' R := φ.toRingHom.toAlgebra
  have : IsScalarTower A' P' R := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  exact exists_flatModuleLift_of_lift_along_tower_aux hsurjP hkerP hsurjR hkerR
    hφ M M' hflat (e.trans (TensorProduct.lid P M).symm)
    (TensorProduct.lid P M)

/-- **Clause (1) of the smooth form of 0DZ2 does not depend on the smooth lift of `P`.** For two
thickenings `P'` and `R` of `P` over a surjection `A' → A` with nilpotent kernel, both formally
smooth over `A'`, the module `M` has an `A'`-flat `P'`-module lift if and only if it has an
`A'`-flat `R`-module lift. Both directions are
`Deformation.exists_flatModuleLift_of_thickening`.

So clause (1) of `Deformation.FlatModuleLiftBaseChangeStatementSmooth` is a property of the
surjection `A' → A`, the algebra `P` and the module `M` alone, and a counterexample can neither
be obtained nor avoided by choosing the smooth presentation differently. In particular it is the
same question at `P' = MvPolynomial (Fin n) A'`, which is the presentation every consumer of
0DZ2 in this library uses. -/
theorem exists_flatModuleLift_iff_of_formallySmooth [Algebra.FormallySmooth A' P']
    [Algebra.FormallySmooth A' R]
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjR : Function.Surjective (algebraMap R P))
    (hkerR : RingHom.ker (algebraMap R P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' R))
    (M : Type u) [AddCommGroup M] [Module P M] :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module R M') (_ : Module A' M')
      (_ : IsScalarTower A' R M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[R] M') ≃ₗ[P] M)) :=
  ⟨fun h => exists_flatModuleLift_of_thickening hnilA hsurjR hkerR hsurjP hkerP M h,
    fun h => exists_flatModuleLift_of_thickening hnilA hsurjP hkerP hsurjR hkerR M h⟩

end Transport

end Thickening

/-! ### The local lift at a `g` that already inverts nothing of `M` is a global lift

The local liftability hypothesis `hlocal` of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` gives, for each `g ∈ J'`, an `A'`-flat
`(P')_g`-module lifting `M_ḡ`. When `ḡ` already acts invertibly on `M` — so that `M_ḡ` is `M`
itself — that local lift *is* a global lift: it is an `A'`-flat `P'`-module by restriction along
`P' → (P')_g`, and its reduction is the same quotient, because the localized square is again
cartesian, `ker((P')_g → P_ḡ) = ker(A' → A) · (P')_g`, which is `Mathlib`'s
`IsLocalization.ker_map` together with `hkerP`.

So a counterexample cannot have `supp M` disjoint from `V(J')`: if `J' + ann_P(M) = P`, write
`1 = j̄ + a` with `j ∈ J'` and `a ∈ ann_P(M)`; then `j̄` acts on `M` as the identity, `M_j̄ ≅ M`,
and `hlocal` at `j` yields clause (1). The step from `J' + ann_P(M) = P` to the hypothesis
`Nonempty ((P_ḡ ⊗[P] M) ≃ₗ[P] M)` of
`Deformation.exists_flatModuleLift_of_localizationLift` is elementary and is *not* formalized
here; everything after it is.
-/

section LocalLift

section AlongTower

variable {A' A P' P S' S : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [CommRing S'] [CommRing S]
  [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A' S']
  [Algebra P' P] [Algebra P' S'] [Algebra P S] [Algebra S' S]
  [IsScalarTower A' P' P] [IsScalarTower A' P' S']

omit [Algebra A' P] [IsScalarTower A' P' P] in
/-- **A module lift after a base change that leaves `M` unchanged is a module lift.** Let
`A' → A` be a surjection with kernel `I`, let `P' → P` and `S' → S` be two surjections over it
with kernels `I · P'` and `I · S'`, in a commuting square `P' → S'` over `P → S`. If `L` is an
`A'`-flat `S'`-module whose reduction `S ⊗_{S'} L` is `S ⊗_P M`, and if `S ⊗_P M` is `M` itself
as a `P`-module, then `L` — restricted along `P' → S'` — is an `A'`-flat `P'`-module lift of `M`,
in the exact shape clause (1) of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` asks for.

Neither `S'` nor `S` is assumed flat, Noetherian, or a localization, and `P'` is not assumed
smooth: the content is that the two reductions of `L`, across `P' → P` and across `S' → S`, are
the same quotient of `L`, namely by the submodule generated by `I · L`
(`Deformation.mem_smul_top_of_mem_smul_top`). The application is
`Deformation.exists_flatModuleLift_of_localizationLift`, where `S'` and `S` are the principal
localizations of `P'` and `P`. -/
theorem exists_flatModuleLift_of_lift_along_tower
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hsurjS : Function.Surjective (algebraMap S' S))
    (hkerS : RingHom.ker (algebraMap S' S) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' S'))
    (hcomm : ∀ x : P',
      algebraMap S' S (algebraMap P' S' x) = algebraMap P S (algebraMap P' P x))
    (M : Type u) [AddCommGroup M] [Module P M]
    (L : Type u) [AddCommGroup L] [Module S' L] [Module A' L] [IsScalarTower A' S' L]
    (hflatL : Module.Flat A' L)
    (eL : (S ⊗[S'] L) ≃ₗ[S] (S ⊗[P] M)) (eM : (S ⊗[P] M) ≃ₗ[P] M) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] M) := by
  exact exists_flatModuleLift_of_lift_along_tower_aux hsurjP hkerP hsurjS hkerS hcomm M L hflatL
    eL eM

end AlongTower

section Localization

variable {A' A P' P : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra P' P] [IsScalarTower A' P' P]

omit [Algebra A' P] [IsScalarTower A' P' P] in
/-- **0DZ2's local liftability hypothesis at a `g` whose image already acts invertibly on `M`
gives clause (1).** The hypothesis `hlift` is the body of 0DZ2's `hlocal` at the single element
`g`, copied verbatim from `Deformation.FlatModuleLiftBaseChangeStatementSmooth`; `hM` says that
localizing `M` at the image of `g` does nothing, which is what holds when the image of `g` acts
on `M` as a unit. Under those two, `M` has an `A'`-flat `P'`-module lift — no smoothness of `P'`,
no ideal `J'`, no `Q'` and no finiteness of `M` are used.

The localized square is again cartesian: `ker((P')_g → P_ḡ) = ker(A' → A) · (P')_g`, by
`IsLocalization.ker_map` and `hkerP`, and the localized vertical map is again surjective, by
`IsLocalization.map_surjective_of_surjective`. So
`Deformation.exists_flatModuleLift_of_lift_along_tower` applies with
`S' = (P')_g` and `S = P_ḡ`.

**Consequence for the search for a counterexample.** `supp M` must meet `V(J')`. Were it
disjoint from it, `J' + ann_P(M) = P`, so some `j ∈ J'` has `1 - j̄ ∈ ann_P(M)`, hence `j̄` acts
as the identity on `M` and `hM` holds at `g = j`; the local lift `hlocal` provides at `j` is then
a global lift and clause (1) holds. The one step of that argument not formalized here is the
passage from `1 - j̄ ∈ ann_P(M)` to `hM`. -/
theorem exists_flatModuleLift_of_localizationLift
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (g : P') (M : Type u) [AddCommGroup M] [Module P M]
    (hlift :
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] M)))
    (hM : Nonempty ((Localization.Away (algebraMap P' P g) ⊗[P] M) ≃ₗ[P] M)) :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] M) := by
  classical
  have hker0 : RingHom.ker (Localization.awayMap (algebraMap P' P) g) =
      (RingHom.ker (algebraMap P' P)).map (algebraMap P' (Localization.Away g)) :=
    IsLocalization.ker_map (Localization.Away (algebraMap P' P g)) (algebraMap P' P)
      (Submonoid.map_powers (algebraMap P' P) g)
  have hcomm0 : ∀ x : P',
      Localization.awayMap (algebraMap P' P) g (algebraMap P' (Localization.Away g) x) =
        algebraMap P (Localization.Away (algebraMap P' P g)) (algebraMap P' P x) := fun x => by
    simp [Localization.awayMap, IsLocalization.Away.map]
  have hsurj0 : Function.Surjective (Localization.awayMap (algebraMap P' P) g) := by
    have hloc : IsLocalization ((Submonoid.powers g).map (algebraMap P' P))
        (Localization.Away (algebraMap P' P g)) := by
      rw [Submonoid.map_powers]
      infer_instance
    exact IsLocalization.map_surjective_of_surjective (Submonoid.powers g)
      (Localization.Away g) (Localization.Away (algebraMap P' P g)) hsurjP
  let : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
    (Localization.awayMap (algebraMap P' P) g).toAlgebra
  have halg : (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g)) :
      Localization.Away g →+* Localization.Away (algebraMap P' P g)) =
      Localization.awayMap (algebraMap P' P) g := rfl
  obtain ⟨L, _, _, _, _, hflatL, ⟨eL⟩⟩ := hlift
  obtain ⟨eM⟩ := hM
  have hsurjS : Function.Surjective
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))) := by
    rw [halg]
    exact hsurj0
  have hkerS : RingHom.ker
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (Localization.Away g)) := by
    rw [halg, hker0, hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine exists_flatModuleLift_of_lift_along_tower hsurjP hkerP hsurjS hkerS ?_ M L hflatL eL eM
  intro x
  rw [halg]
  exact hcomm0 x

end Localization

end LocalLift

/-! ### Stacks 0DZ2 with `P'` smooth over `A'` is true over a split base

A *split* base is a surjection `A' → A` that admits a ring section, equivalently one for which
`A'` is an `A`-algebra compatibly with the surjection — carried below by the two instances
`[Algebra A A'] [IsScalarTower A A' A]`, or as the data `(s, hs)` of a ring map `s : A → A'`
with `A' → A` undoing it. Over such a base the lifting problem of 0DZ2 has a *trivial* solution
for every `A`-flat module as soon as `P'` is formally smooth over `A'`: the lift of `M` is
`A' ⊗[A] M`, with `P'` acting through an `A'`-algebra map `P' → A' ⊗[A] P` lifting `P' → P`
that formal smoothness supplies. Both clauses of 0DZ2 therefore hold, and a counterexample to
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` must have a base with no section.
-/

section SplitBase

variable (A' A P M : Type u) [CommRing A'] [CommRing A] [CommRing P]
  [Algebra A' A] [Algebra A' P] [Algebra A P] [IsScalarTower A' A P]
  [Algebra A A'] [IsScalarTower A A' A]
  [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]

/-- **A section of `A' → A` composed with `A' → A` is the identity.** The instance pair
`[Algebra A A'] [IsScalarTower A A' A]` is how "`A' → A` splits" is carried here: the tower says
that `A → A' → A` is the structure map `A → A`, which is the identity. -/
theorem algebraMap_algebraMap_eq_self (a : A) : algebraMap A' A (algebraMap A A' a) = a := by
  have h := IsScalarTower.algebraMap_apply A A' A a
  simpa using h.symm

/-- **Over a split base, `A' → P` is a map of `A`-algebras.** If `A' → A` splits and the
structure map `A' → P` factors through `A`, then `A → A' → P` is the structure map `A → P`. This
is a local instance in this section, where it is what allows `A' ⊗[A] P` to be built with
`A' → P` as one of its two factors. -/
theorem isScalarTower_of_splitBase : IsScalarTower A A' P :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A' A P, algebraMap_algebraMap_eq_self A' A]

attribute [local instance] isScalarTower_of_splitBase

/-- **The trivial lift of `P` along a split base, reduced back to `P`, as a map of
`A`-algebras.** The reduction `x ⊗ p ↦ x̄ · p`, where `x̄` is the image of `x` in `A`, is the
`A`-algebra map out of `A' ⊗[A] P` determined by `A' → P` and the identity of `P`. It is also a
map of `A'`-algebras, which is the form the lifting property of a formally smooth `P'` consumes:
that upgrade is `Deformation.splitTensorHom`. -/
def splitTensorHomAux : (A' ⊗[A] P) →ₐ[A] P :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A A' P) (AlgHom.id A P)
    (fun _ _ => Commute.all _ _)

/-- `Deformation.splitTensorHomAux` sends `x ⊗ₜ p` to the image of `x` in `P` times `p`. -/
theorem splitTensorHomAux_tmul (x : A') (p : P) :
    splitTensorHomAux A' A P (x ⊗ₜ[A] p) = algebraMap A' P x * p :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- **The trivial lift of `P` along a split base, reduced back to `P`.** For `A' → A` split,
`A' ⊗[A] P` is an `A'`-algebra sitting over `P`, and this is the reduction `x ⊗ p ↦ x̄ · p`,
where `x̄` is the image of `x` in `A`. It is surjective with kernel `ker(A' → A) · (A' ⊗[A] P)`
(`Deformation.splitTensorHom_surjective`, `Deformation.ker_splitTensorHom`), hence a nilpotent
thickening of `P` as soon as `ker(A' → A)` is nilpotent; that is what a formally smooth `P'` maps
into over `P`. -/
def splitTensorHom : (A' ⊗[A] P) →ₐ[A'] P where
  toRingHom := (splitTensorHomAux A' A P).toRingHom
  commutes' x := by
    change splitTensorHomAux A' A P (algebraMap A' (A' ⊗[A] P) x) = algebraMap A' P x
    rw [Algebra.TensorProduct.algebraMap_apply, splitTensorHomAux_tmul]
    simp

/-- `Deformation.splitTensorHom` sends `x ⊗ p` to `x̄ · p`. -/
@[simp]
theorem splitTensorHom_tmul (x : A') (p : P) :
    splitTensorHom A' A P (x ⊗ₜ[A] p) = algebraMap A' P x * p :=
  splitTensorHomAux_tmul A' A P x p

/-- The reduction of the trivial lift of `P` is surjective: `p` is the image of `1 ⊗ p`. -/
theorem splitTensorHom_surjective : Function.Surjective (splitTensorHom A' A P) :=
  fun p => ⟨(1 : A') ⊗ₜ[A] p, by simp⟩

/-- **The trivial lift of `P` along a split base is a base change of `A' → A`.** The kernel of
`Deformation.splitTensorHom` is `ker(A' → A) · (A' ⊗[A] P)`: modulo that ideal every element of
`A' ⊗[A] P` is `1 ⊗ p`, because `x ⊗ p` differs from `1 ⊗ x̄ · p` by `(x - x̄) ⊗ p` and
`x - x̄` lies in the kernel of `A' → A`, where `x̄` is read back into `A'` along the section. -/
theorem ker_splitTensorHom :
    RingHom.ker (splitTensorHom A' A P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (A' ⊗[A] P)) := by
  have hmem : ∀ (y : A') (p : P), y ∈ RingHom.ker (algebraMap A' A) →
      y ⊗ₜ[A] p ∈ (RingHom.ker (algebraMap A' A)).map (algebraMap A' (A' ⊗[A] P)) := by
    intro y p hy
    have h1 : y ⊗ₜ[A] p = (algebraMap A' (A' ⊗[A] P) y) * ((1 : A') ⊗ₜ[A] p) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      simp
    rw [h1]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hy)
  have hkey : ∀ z : A' ⊗[A] P,
      z - (1 : A') ⊗ₜ[A] (splitTensorHom A' A P z) ∈
        (RingHom.ker (algebraMap A' A)).map (algebraMap A' (A' ⊗[A] P)) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x p =>
        have hxp : (1 : A') ⊗ₜ[A] (splitTensorHom A' A P (x ⊗ₜ[A] p)) =
            (algebraMap A A' (algebraMap A' A x)) ⊗ₜ[A] p := by
          rw [splitTensorHom_tmul, IsScalarTower.algebraMap_apply A' A P, ← Algebra.smul_def,
            ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
        rw [hxp, ← TensorProduct.sub_tmul]
        refine hmem _ _ ?_
        rw [RingHom.mem_ker, map_sub, algebraMap_algebraMap_eq_self A' A, sub_self]
    | add z w hz hw =>
        have h2 : z + w - (1 : A') ⊗ₜ[A] (splitTensorHom A' A P (z + w)) =
            (z - (1 : A') ⊗ₜ[A] (splitTensorHom A' A P z)) +
              (w - (1 : A') ⊗ₜ[A] (splitTensorHom A' A P w)) := by
          rw [map_add, TensorProduct.tmul_add]
          ring
        rw [h2]
        exact Ideal.add_mem _ hz hw
  refine le_antisymm (fun z hz => ?_) ?_
  · have h := hkey z
    rw [RingHom.mem_ker.mp hz, TensorProduct.tmul_zero, sub_zero] at h
    exact h
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A' A P, RingHom.mem_ker.mp hx, map_zero]

/-- **The retraction `A' → A` of a split base, as an `A`-linear map.** `A'` is an `A`-algebra
through the section, and `algebraMap A' A` is `A`-linear for that structure precisely because
`A → A' → A` is the identity. It is the bilinear datum behind
`Deformation.splitReduce`. -/
def splitRetractionLinear : A' →ₗ[A] A where
  toFun := algebraMap A' A
  map_add' := map_add _
  map_smul' a x := by
    rw [Algebra.smul_def, map_mul, algebraMap_algebraMap_eq_self A' A, smul_eq_mul]
    rfl

/-- **The trivial lift of `M` along a split base, reduced back to `M`.** The `A`-linear map
`A' ⊗[A] M → M`, `x ⊗ m ↦ x̄ · m`. It is surjective and its kernel is
`ker(A' → A) · (A' ⊗[A] M)`, which is why `A' ⊗[A] M` reduces to `M` across `P' → P`; see
`Deformation.exists_flatModuleLift_of_split`. -/
def splitReduce : (A' ⊗[A] M) →ₗ[A] M :=
  TensorProduct.lift ((Algebra.lsmul A A M : A →ₐ[A] Module.End A M).toLinearMap.comp
    (splitRetractionLinear A' A))

/-- `Deformation.splitReduce` sends `x ⊗ m` to `x̄ • m`. -/
@[simp]
theorem splitReduce_tmul (x : A') (m : M) :
    splitReduce A' A M (x ⊗ₜ[A] m) = (algebraMap A' A x) • m := rfl

/-- **The action of the trivial lift of `P` on the trivial lift of `M`.** `A' ⊗[A] P` acts on
`A' ⊗[A] M` factor by factor, `(x ⊗ p) · (y ⊗ m) = (x · y) ⊗ (p · m)`; this is that action, as a
ring map into `Module.End A' (A' ⊗[A] M)`, obtained from the `P`-action on `M` by base change
along `A → A'`. Composing it with an `A'`-algebra map `P' → A' ⊗[A] P` is what makes `A' ⊗[A] M`
a `P'`-module. -/
def splitTensorEndHom : (A' ⊗[A] P) →+* Module.End A' (A' ⊗[A] M) :=
  (LinearMap.tensorProductEnd A A' M).toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.id A A')
      (Algebra.lsmul A A M : P →ₐ[A] Module.End A M)).toRingHom

omit [Algebra A' A] [Algebra A' P] [IsScalarTower A' A P] [IsScalarTower A A' A] in
/-- `x ⊗ p` acts on `y ⊗ m` through `Deformation.splitTensorEndHom` as `(x * y) ⊗ (p • m)`. -/
@[simp]
theorem splitTensorEndHom_tmul_tmul (x : A') (p : P) (y : A') (m : M) :
    splitTensorEndHom A' A P M (x ⊗ₜ[A] p) (y ⊗ₜ[A] m) = (x * y) ⊗ₜ[A] (p • m) := by
  change (LinearMap.tensorProductEnd A A' M)
    (Algebra.TensorProduct.map (AlgHom.id A A')
      (Algebra.lsmul A A M : P →ₐ[A] Module.End A M) (x ⊗ₜ[A] p)) (y ⊗ₜ[A] m) = _
  rw [Algebra.TensorProduct.map_tmul]
  simp [LinearMap.tensorProductEnd, LinearMap.tensorProduct, TensorProduct.smul_tmul',
    smul_eq_mul]

omit [Algebra A' A] [Algebra A' P] [IsScalarTower A' A P] [IsScalarTower A A' A] in
/-- The scalars `A'` act on `A' ⊗[A] M` through `Deformation.splitTensorEndHom` as they do on
the left factor, so the `P'`-action built from it is compatible with the `A'`-action. -/
theorem splitTensorEndHom_algebraMap (x : A') (n : A' ⊗[A] M) :
    splitTensorEndHom A' A P M (algebraMap A' (A' ⊗[A] P) x) n = x • n := by
  change (LinearMap.tensorProductEnd A A' M)
    (Algebra.TensorProduct.map (AlgHom.id A A')
      (Algebra.lsmul A A M : P →ₐ[A] Module.End A M)
        (algebraMap A' (A' ⊗[A] P) x)) n = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  induction n using TensorProduct.inductionOn with
  | tmul y m => simp [LinearMap.tensorProductEnd, LinearMap.tensorProduct,
      TensorProduct.smul_tmul', smul_eq_mul]
  | add z w hz hw => rw [map_add, hz, hw, smul_add]

/-- **Reduction is equivariant.** Reducing `A' ⊗[A] M` to `M` turns the action of `A' ⊗[A] P`
into the action of its reduction `P`: the two squares of the construction commute. With a lift
`φ : P' → A' ⊗[A] P` of `P' → P` this says that the reduction of `A' ⊗[A] M` is `P'`-linear for
the `P'`-action on `M` through `P' → P`. -/
theorem splitReduce_splitTensorEndHom (z : A' ⊗[A] P) (n : A' ⊗[A] M) :
    splitReduce A' A M (splitTensorEndHom A' A P M z n) =
      (splitTensorHom A' A P z) • (splitReduce A' A M n) := by
  have hsm : ∀ (a : A) (w : M), a • w = (algebraMap A P a) • w := fun a w =>
    (IsScalarTower.algebraMap_smul P a w).symm
  have hmap : ∀ x : A', algebraMap A P (algebraMap A' A x) = algebraMap A' P x := fun x =>
    (IsScalarTower.algebraMap_apply A' A P x).symm
  induction z using TensorProduct.inductionOn with
  | tmul x p =>
      induction n using TensorProduct.inductionOn with
      | tmul y m =>
          rw [splitTensorEndHom_tmul_tmul, splitReduce_tmul, splitReduce_tmul,
            splitTensorHom_tmul, map_mul, hsm (algebraMap A' A x * algebraMap A' A y),
            hsm (algebraMap A' A y), map_mul, hmap, hmap, smul_smul, smul_smul,
            mul_right_comm]
      | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, smul_add]
  | add z w hz hw =>
      rw [map_add, LinearMap.add_apply, map_add, hz, hw, map_add, add_smul]

end SplitBase

section SplitLift

variable {A' A P' P : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A P] [Algebra P' P]
  [IsScalarTower A' A P] [IsScalarTower A' P' P]
  [Algebra A A'] [IsScalarTower A A' A]

/-- **Over a split base, every `A`-flat module lifts, as soon as `P'` is formally smooth.** Let
`A' → A` be a surjection with nilpotent kernel `I` which splits — `A'` is an `A`-algebra and
`A → A' → A` is the identity — let `P' → P` be a surjection over it with kernel `I · P'`, and
let `P'` be formally smooth over `A'`. Then *every* `P`-module `M` flat over `A` has an
`A'`-flat `P'`-module lift, in the exact shape clause (1) of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` asks for.

The lift is the trivial one, `A' ⊗[A] M`. Two facts make it one. First, `A' ⊗[A] P` is a
*thickening of `P` over `A' → A`* in the sense of the previous section: its reduction
`Deformation.splitTensorHom` is surjective with kernel `I · (A' ⊗[A] P)`
(`Deformation.ker_splitTensorHom`), and `A' ⊗[A] M` is a module over it, through
`Deformation.splitTensorEndHom`, compatibly with its `A'`-module structure. Second, `A' ⊗[A] M`
is `A'`-flat because `M` is `A`-flat, and its reduction across `A' ⊗[A] P → P` is `M`: the
kernel of `Deformation.splitReduce` is `I · (A' ⊗[A] M)`, and
`Deformation.splitReduce_splitTensorEndHom` says the reduction is equivariant. So `M` has an
`A'`-flat module lift over that thickening, and
`Deformation.exists_flatModuleLift_of_thickening` carries it to the formally smooth `P'`. That
last step is the only use of formal smoothness, and the split base is used only to build the
thickening `A' ⊗[A] P` and the module on it.

**None of 0DZ2's remaining hypotheses is used**: no ring is assumed Noetherian, `M` is not
assumed finite over `P`, there is no ideal `J'` and no local liftability, and nothing is assumed
about `Q'`. Only formal smoothness of `P'` is needed, not `Algebra.Smooth A' P'`.

This is why a counterexample to `Deformation.FlatModuleLiftBaseChangeStatementSmooth` must have
a base `A' → A` admitting no ring section, and in particular why the counterexample that refutes
the general statement cannot be adapted: its base is `NC[t]/t³ → NC`, which splits. -/
theorem exists_flatModuleLift_of_split [Algebra.FormallySmooth A' P']
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
    [Module.Flat A M] :
    ∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
      (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧ Nonempty ((P ⊗[P'] M') ≃ₗ[P] M) := by
  classical
  have hkey : ∀ v : A' ⊗[A] M, v - (1 : A') ⊗ₜ[A] splitReduce A' A M v ∈
      (RingHom.ker (algebraMap A' A)) • (⊤ : Submodule A' (A' ⊗[A] M)) := by
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul x m =>
      rw [splitReduce_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        ← TensorProduct.sub_tmul, show (x - algebraMap A A' (algebraMap A' A x)) ⊗ₜ[A] m =
          (x - algebraMap A A' (algebraMap A' A x)) • ((1 : A') ⊗ₜ[A] m) by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [RingHom.mem_ker, map_sub, algebraMap_algebraMap_eq_self A' A, sub_self]
    | add v w hv hw =>
      rw [map_add, TensorProduct.tmul_add, add_sub_add_comm]
      exact Submodule.add_mem _ hv hw
  let _ : Algebra (A' ⊗[A] P) P := (splitTensorHom A' A P).toRingHom.toAlgebra
  have _ : IsScalarTower A' (A' ⊗[A] P) P :=
    IsScalarTower.of_algebraMap_eq fun x => ((splitTensorHom A' A P).commutes x).symm
  have hsurjR : Function.Surjective (algebraMap (A' ⊗[A] P) P) :=
    splitTensorHom_surjective A' A P
  have hkerR : RingHom.ker (algebraMap (A' ⊗[A] P) P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' (A' ⊗[A] P)) :=
    ker_splitTensorHom A' A P
  let _ : Module (A' ⊗[A] P) (A' ⊗[A] M) :=
    Module.compHom _ (splitTensorEndHom A' A P M)
  have hsmulR : ∀ (z : A' ⊗[A] P) (n : A' ⊗[A] M), z • n = splitTensorEndHom A' A P M z n :=
    fun _ _ => rfl
  have htowerR : IsScalarTower A' (A' ⊗[A] P) (A' ⊗[A] M) := ⟨fun x z n => by
    rw [hsmulR, hsmulR, Algebra.smul_def, map_mul, Module.End.mul_apply]
    exact splitTensorEndHom_algebraMap A' A P M _ _⟩
  let _ : Module (A' ⊗[A] P) M := Module.compHom M (algebraMap (A' ⊗[A] P) P)
  have _ : IsScalarTower (A' ⊗[A] P) P M :=
    ⟨fun x y z => by rw [Algebra.smul_def]; exact mul_smul _ y z⟩
  let r : (A' ⊗[A] M) →ₗ[A' ⊗[A] P] M :=
    { toFun := splitReduce A' A M
      map_add' := fun v w => (splitReduce A' A M).map_add v w
      map_smul' := fun z n => by
        rw [hsmulR]
        change splitReduce A' A M (splitTensorEndHom A' A P M z n) = z • splitReduce A' A M n
        rw [splitReduce_splitTensorEndHom]
        rfl }
  have hrsurj : Function.Surjective r := fun m =>
    ⟨(1 : A') ⊗ₜ[A] m, show algebraMap A' A 1 • m = m by rw [map_one, one_smul]⟩
  have hker : LinearMap.ker r =
      (RingHom.ker (algebraMap (A' ⊗[A] P) P)) • (⊤ : Submodule (A' ⊗[A] P) (A' ⊗[A] M)) := by
    refine le_antisymm (fun n hn => ?_) ?_
    · have hle : (RingHom.ker (algebraMap A' A) • ⊤ : Submodule A' (A' ⊗[A] M)) ≤
          ((RingHom.ker (algebraMap (A' ⊗[A] P) P)) •
            (⊤ : Submodule (A' ⊗[A] P) (A' ⊗[A] M))).restrictScalars A' :=
        Submodule.smul_le.mpr fun y hy n _ => by
          rw [Submodule.restrictScalars_mem, ← IsScalarTower.algebraMap_smul (A' ⊗[A] P) y n]
          exact Submodule.smul_mem_smul (by rw [hkerR]; exact Ideal.mem_map_of_mem _ hy)
            Submodule.mem_top
      simpa only [show splitReduce A' A M n = 0 from hn, TensorProduct.tmul_zero, sub_zero,
        Submodule.restrictScalars_mem] using hle (hkey n)
    · exact Submodule.smul_le.mpr fun j hj n _ => by
        rw [LinearMap.mem_ker, map_smul, ← IsScalarTower.algebraMap_smul P j (r n),
          RingHom.mem_ker.mp hj, zero_smul]
  refine exists_flatModuleLift_of_thickening (R := A' ⊗[A] P) hnilA hsurjP hkerP hsurjR hkerR M
    ⟨A' ⊗[A] M, inferInstance, inferInstance, inferInstance, htowerR,
      Module.Flat.baseChange A A' M, ⟨?_⟩⟩
  exact LinearEquiv.extendScalarsOfSurjective hsurjR
    ((quotKerSMulTopEquivBaseChange hsurjR (A' ⊗[A] M)).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker.symm).trans (r.quotKerEquivOfSurjective hrsurj)))

end SplitLift

section SplitStatement

variable {A' A P' P Q' Q : Type u} [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [CommRing Q'] [CommRing Q]
  [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A P]
  [Algebra P' P] [Algebra P' Q'] [Algebra P' Q] [Algebra P Q] [Algebra Q' Q]
  [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
  [IsScalarTower P' P Q] [IsScalarTower P' Q' Q]

/-- **Stacks 0DZ2 with `P'` smooth over `A'` holds over a split base.** If the surjection
`A' → A` admits a ring section `s` and `P'` is formally smooth over `A'`, then `M` has an
`A'`-flat `P'`-module lift if and only if `N ≅ Q ⊗_P M` has an `A'`-flat `Q'`-module lift —
because *both* clauses hold. Clause (1) is
`Deformation.exists_flatModuleLift_of_split`, which builds the trivial lift `A' ⊗[A] M`; clause
(2) is its base change `Q' ⊗_{P'} (A' ⊗[A] M)`, flat over `A'` by
`Module.Flat.tensorProduct_of_flat_base`.

The hypotheses here are a *sub-list* of those of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth`, with a section of `A' → A` added: the six
`IsNoetherianRing` instances, the surjectivity of `A' → A` and of `Q' → Q`, the kernel condition
on `Q' → Q`, `Module.Flat A' P'`, `Module.Flat A' Q'`, `Module.Flat P Q`, `Module.Flat A P`,
finite presentation of `P'` over `A'`, the ideal `J'` with `P'/J' = Q'/J'Q'`,
`Module.Finite P M` and the local liftability of `M` on `J'` are all unused. So the smooth form
of 0DZ2 is a theorem over a split base, and whatever its status in general, **a counterexample
to it must have a base `A' → A` with no ring section.**

That is exactly what rules out adapting the known refutation of the general statement
(`Deformation.Examples.ArtinSchreier.not_flatModuleLiftBaseChangeStatementFaithful`): its base is
`NC[t]/t³ → NC`, which splits, by `Deformation.Examples.MaurerCartanWindow.cst` and
`Deformation.Examples.ArtinSchreier.redA_cst`. What a counterexample is left to look like, and
which further features of it are forced, is recorded in the module documentation. -/
theorem exists_flatModuleLift_iff_baseChange_of_ringHom_section [Algebra.FormallySmooth A' P']
    (s : A →+* A') (hs : ∀ a : A, algebraMap A' A (s a) = a)
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (hsurjP : Function.Surjective (algebraMap P' P))
    (hkerP : RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
    (hflatPQ' : Module.Flat P' Q')
    (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
    [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N]
    (hN : Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N)) :
    ((∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N))) := by
  let _ : Algebra A A' := s.toAlgebra
  have : IsScalarTower A A' A := IsScalarTower.of_algebraMap_eq fun a => (hs a).symm
  obtain ⟨L, _, _, _, _, hflatL, ⟨eL⟩⟩ :=
    exists_flatModuleLift_of_split hnilA hsurjP hkerP M
  obtain ⟨eN⟩ := hN
  have := hflatL
  have := hflatPQ'
  refine iff_of_true
    ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hflatL, ⟨eL⟩⟩
    ⟨Q' ⊗[P'] L, inferInstance, inferInstance, inferInstance, inferInstance,
      Module.Flat.tensorProduct_of_flat_base L, ⟨?_⟩⟩
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange P' Q' Q Q L) ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P' P Q Q L).symm ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl Q Q) eL) ≪≫ₗ eN

/-- **Stacks 0DZ2 with `P'` smooth over `A'` is a theorem over a split base — in the shape of
`Deformation.FlatModuleLiftBaseChangeStatementSmooth` itself.** This is that statement with one
hypothesis added, a ring section of `A' → A`, and with its conclusion *proved*. It is stated as
a theorem with the hypotheses written out rather than as a second `Prop`-valued definition, so
that no near-copy of `Deformation.FlatModuleLiftBaseChangeStatementSmooth` is introduced beside
it; reading the two side by side is how one checks that nothing was weakened.

The proof is `Deformation.exists_flatModuleLift_iff_baseChange_of_ringHom_section`, which uses
only `hnilA`, `hsurjP`, `hkerP`, `hfPQ'`, the smoothness (through
`Algebra.Smooth.formallySmooth`), the flatness of `M` over `A` and the towers. Everything else
here is carried only to make the match with the statement visible: the six Noetherian rings,
`hsurjA`, `hsurjQ`, `hkerQ`, `Module.Flat A' P'`, `Module.Flat A' Q'`, `Module.Flat P Q`,
`Module.Flat A P`, finite presentation of `P'`, the ideal `J'` with `P'/J' = Q'/J'Q'`,
`Module.Finite P M` and the local liftability `hlocal` are all unused.

So the smooth form of 0DZ2 cannot be refuted over a base that splits, and the search for a
counterexample is confined to surjections `A' → A` admitting no ring section. -/
theorem flatModuleLiftBaseChangeStatementSmooth_of_ringHom_section :
    ∀ (A' A P' P Q' Q : Type u)
    [CommRing A'] [CommRing A] [CommRing P'] [CommRing P] [CommRing Q'] [CommRing Q]
    [IsNoetherianRing A'] [IsNoetherianRing A] [IsNoetherianRing P'] [IsNoetherianRing P]
    [IsNoetherianRing Q'] [IsNoetherianRing Q]
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A' Q]
    [Algebra A P] [Algebra A Q] [Algebra P' P] [Algebra P' Q'] [Algebra P' Q]
    [Algebra P Q] [Algebra Q' Q]
    [IsScalarTower A' A P] [IsScalarTower A' P' P] [IsScalarTower A' P' Q']
    [IsScalarTower A' Q' Q] [IsScalarTower A P Q] [IsScalarTower P' P Q]
    [IsScalarTower P' Q' Q],
    (∃ s : A →+* A', ∀ a : A, algebraMap A' A (s a) = a) →
    Function.Surjective (algebraMap A' A) →
    IsNilpotent (RingHom.ker (algebraMap A' A)) →
    Function.Surjective (algebraMap P' P) →
    RingHom.ker (algebraMap P' P) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') →
    Function.Surjective (algebraMap Q' Q) →
    RingHom.ker (algebraMap Q' Q) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') →
    Module.Flat A' P' → Module.Flat A' Q' → Module.Flat P' Q' → Module.Flat P Q →
    Module.Flat A P →
    Algebra.Smooth A' P' →
    ∀ (J' : Ideal P'),
      Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q')) (algebraMap P' Q')
        Ideal.le_comap_map) →
    ∀ (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
      [Module.Finite P M] [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N],
      Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N) →
      (∀ g ∈ J',
        letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
          (Localization.awayMap (algebraMap P' P) g).toAlgebra
        ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
          (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
          Module.Flat A' L ∧ Nonempty
            ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
              ≃ₗ[Localization.Away (algebraMap P' P g)]
                (Localization.Away (algebraMap P' P g) ⊗[P] M))) →
      ((∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
          (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
          Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
        (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
          (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
          Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N))) := by
  intro A' A P' P Q' Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  rintro ⟨s, hs⟩ _hsurjA hnilA hsurjP hkerP _hsurjQ _hkerQ _hfAP' _hfAQ' hfPQ' _hfPQ _hfAP hsm
  intro _J' _hquot M _ _ _ _ _ _ N _ _ hN _hlocal
  have := hsm.formallySmooth
  exact exists_flatModuleLift_iff_baseChange_of_ringHom_section s hs hnilA hsurjP hkerP hfPQ'
    M N hN

end SplitStatement

namespace SmoothDevissage

/-! ### The dévissage's obstruction over a polynomial algebra

`A' = ZMod 8`, `A'' = ZMod 4`, `A = ZMod 2`, so that `I = ker(A' → A) = (2)` has `I³ = 0` and
`I² ≠ 0`: this is the smallest base at which the source's dévissage from `Iⁿ = 0` to `I² = 0`
has anything to do. `P' = A'[x, y]`, free and hence smooth over `A'`, with `P = A[x, y]`, and
`M = A²` with `x` and `y` acting as zero — finite over `P` and flat over the field `A`. A module
over `A'[x, y]` which is free over `A'` is a free `A'`-module with two commuting endomorphisms,
so the lifts of `M` in play are given by pairs of matrices, and the whole obstruction calculus
of this situation is the problem of lifting a commuting pair of matrices from `ZMod 4` to
`ZMod 8`. See the module documentation for the two links to the `Ext`-theoretic formulation that
are not formalized. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The product of two second-order corrections, computed.** A matrix over `A' = ZMod 8` whose
reduction mod `4` is the prescribed first-order action `2E` is exactly one of the form
`2E + 4G`, and the product of two such depends only on `E` and `F`: every cross term carries a
factor `8`. -/
theorem mul_two_smul_add_four_smul (E F G H : Matrix ι ι (ZMod 8)) :
    ((2 : ZMod 8) • E + (4 : ZMod 8) • G) * ((2 : ZMod 8) • F + (4 : ZMod 8) • H)
      = (4 : ZMod 8) • (E * F) := by
  have h22 : (2 : ZMod 8) * 2 = 4 := by decide
  have h24 : (2 : ZMod 8) * 4 = 0 := by decide
  have h42 : (4 : ZMod 8) * 2 = 0 := by decide
  have h44 : (4 : ZMod 8) * 4 = 0 := by decide
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, h22, h24, h42, h44, zero_smul, add_zero]

/-- **The lifting problem of the dévissage, over a polynomial `P'`.** `ExtendsToSecondOrder E F`
says that the `A''`-flat `P''`-module lift of `M = A²` in which `x` and `y` act by the reductions
of `2E` and `2F` extends to an `A'`-flat `P'`-module lift: that the two prescribed actions can be
corrected by multiples of `4` — the kernel of `M_ι(ZMod 8) → M_ι(ZMod 4)` — into a pair of
*commuting* matrices over `A' = ZMod 8`, which is what an `A'[x, y]`-module structure on a free
`A'`-module amounts to.

Addition of the parameters is the action of the torsor of lifts: two `A''`-flat lifts with
parameters `(E, F)` and `(E₀, F₀)` differ by the first-order class `(E − E₀, F − F₀)`. -/
def ExtendsToSecondOrder (E F : Matrix ι ι (ZMod 8)) : Prop :=
  ∃ G H : Matrix ι ι (ZMod 8),
    ((2 : ZMod 8) • E + (4 : ZMod 8) • G) * ((2 : ZMod 8) • F + (4 : ZMod 8) • H) =
      ((2 : ZMod 8) • F + (4 : ZMod 8) • H) * ((2 : ZMod 8) • E + (4 : ZMod 8) • G)

omit [DecidableEq ι] in
/-- **The obstruction is the commutator.** The first-order lift with parameters `(E, F)` extends
to the second-order thickening if and only if `4·(E·F) = 4·(F·E)`, that is, if and only if `E`
and `F` commute modulo `2`. In particular the correction terms play no role: whether the lift
extends is decided by the first-order data alone, which is why the dévissage has an obstruction
*class* at all. -/
theorem extendsToSecondOrder_iff (E F : Matrix ι ι (ZMod 8)) :
    ExtendsToSecondOrder E F ↔ (4 : ZMod 8) • (E * F) = (4 : ZMod 8) • (F * E) :=
  ⟨fun ⟨_, _, h⟩ => by rwa [mul_two_smul_add_four_smul, mul_two_smul_add_four_smul] at h,
    fun h => ⟨0, 0, by rwa [mul_two_smul_add_four_smul, mul_two_smul_add_four_smul]⟩⟩

omit [DecidableEq ι] in
/-- **A fourfold multiple of a product sees only the factors modulo `2`.** The arithmetic behind
`Deformation.SmoothDevissage.extendsToSecondOrder_add_two_smul`: every cross term of
`(E + 2E')(F + 2F')` that is not `E·F` carries a factor `2`, and `4 · 2 = 0` in `ZMod 8`. -/
theorem four_smul_mul_add_two_smul (E F E' F' : Matrix ι ι (ZMod 8)) :
    (4 : ZMod 8) • ((E + (2 : ZMod 8) • E') * (F + (2 : ZMod 8) • F'))
      = (4 : ZMod 8) • (E * F) := by
  have h22 : (2 : ZMod 8) * 2 = 4 := by decide
  have h42 : (4 : ZMod 8) * 2 = 0 := by decide
  have h44 : (4 : ZMod 8) * 4 = 0 := by decide
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, h22, h42, h44, zero_smul, add_zero]

omit [DecidableEq ι] in
/-- **The obstruction depends on the first-order data only modulo `2`.** Changing `(E, F)` by a
multiple of `2` does not change whether the lift extends.

This is what makes the parametrisation of this section the `Ext¹`-torsor parametrisation pulled
back along a surjective group homomorphism, rather than a different group: the first-order action
`2E` over `ZMod 4` only remembers `E` modulo `2`, and the predicate
`Deformation.SmoothDevissage.ExtendsToSecondOrder` is constant on the fibres of
`M_ι(ZMod 8)² → M_ι(ZMod 2)²`. Since the set of unobstructed parameters is therefore the preimage
of the set of unobstructed first-order classes, it is closed under addition if and only if that
set is — so the failure of closure proved below is a statement about the torsor and not an
artefact of parametrising it by matrices over `ZMod 8`. -/
theorem extendsToSecondOrder_add_two_smul (E F E' F' : Matrix ι ι (ZMod 8)) :
    ExtendsToSecondOrder (E + (2 : ZMod 8) • E') (F + (2 : ZMod 8) • F') ↔
      ExtendsToSecondOrder E F := by
  rw [extendsToSecondOrder_iff, extendsToSecondOrder_iff, four_smul_mul_add_two_smul,
    four_smul_mul_add_two_smul]

/-- **The obstruction is not additive, with `P'` a polynomial algebra.** Two first-order lifts
of `M = (ZMod 2)²` over `P'' = (ZMod 4)[x, y]` that each extend to an `A'`-flat
`(ZMod 8)[x, y]`-module lift, whose sum in the torsor does not: `x` acting by `!![0, 1; 0, 0]`
with `y` acting by `0`, and `x` acting by `0` with `y` acting by `!![0, 0; 1, 0]`. Each pair
commutes because one of its members is zero; the sum does not commute, and that is the Yoneda
square of the first-order class — here the commutator — surviving at the first stage of the
dévissage.

This is the smooth analogue of the failure recorded for `P' = A'[x]/(x²)`: making `P'` free, and
hence smooth, over `A'` does not remove the quadratic term, because the term is a Yoneda square
in `Ext^•_P(M, M)` and `M` is an arbitrary finite `A`-flat `P`-module. -/
theorem not_extendsToSecondOrder_add :
    ∃ E₀ F₀ E₁ F₁ : Matrix (Fin 2) (Fin 2) (ZMod 8),
      ExtendsToSecondOrder E₀ F₀ ∧ ExtendsToSecondOrder E₁ F₁ ∧
        ¬ ExtendsToSecondOrder (E₀ + E₁) (F₀ + F₁) := by
  refine ⟨!![0, 1; 0, 0], 0, 0, !![0, 0; 1, 0], ?_, ?_, ?_⟩
  · rw [extendsToSecondOrder_iff]
    simp
  · rw [extendsToSecondOrder_iff]
    simp
  · rw [extendsToSecondOrder_iff]
    decide

/-- **No additive obstruction-variation map describes the dévissage, even for `P'` smooth.** The
route through the obstruction classes needs a map `∂` on the first-order classes that is additive
and vanishes exactly on the classes which extend, so that `im ∂` is a submodule and Stacks 05EC
has a quotient to act on. No such map exists: its zero set would be a subgroup, and
`Deformation.SmoothDevissage.not_extendsToSecondOrder_add` shows the classes that extend are not
closed under addition. The conclusion holds for every target group, so it is not a defect of a
particular choice of coefficients. -/
theorem not_exists_additive_obstructionVariation (V : Type*) [AddCommGroup V] :
    ¬ ∃ d : (Matrix (Fin 2) (Fin 2) (ZMod 8) × Matrix (Fin 2) (Fin 2) (ZMod 8)) →+ V,
      ∀ p, d p = 0 ↔ ExtendsToSecondOrder p.1 p.2 := by
  rintro ⟨d, hd⟩
  obtain ⟨E₀, F₀, E₁, F₁, h₀, h₁, hsum⟩ := not_extendsToSecondOrder_add
  refine hsum ((hd (E₀ + E₁, F₀ + F₁)).1 ?_)
  have hadd : ((E₀, F₀) + (E₁, F₁) : Matrix (Fin 2) (Fin 2) (ZMod 8) ×
      Matrix (Fin 2) (Fin 2) (ZMod 8)) = (E₀ + E₁, F₀ + F₁) := rfl
  rw [← hadd, map_add, (hd (E₀, F₀)).2 h₀, (hd (E₁, F₁)).2 h₁, add_zero]

end SmoothDevissage

end Deformation

end

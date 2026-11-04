module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange
public import StacksFrontier.RingTheory.Dualizing.Relative

/-!
# Base change of a relative dualizing complex

Let `R → A` be a flat ring map of finite presentation, let `R → R'` be arbitrary, put
`A' = A ⊗[R] R'` and let `K' = K ⊗ᴸ_A A'` be the derived base change of `K`.  This file proves
that `K'` is a relative dualizing complex for `R' → A'`, which is part (2) of [stacks 0E2F].

## Main definitions

* `Dualizing.DiagonalDerivedHomBaseChangeAt` — the one carried input, at a single object.
* `Dualizing.DiagonalDerivedHomBaseChange` — that input at every object; the one carried input.
* `Dualizing.RelativelyPerfectDiagonalDerivedHomBaseChange` — that input at the `R`-perfect
  objects only, which is all the clause consumes.

## Main results

* `Dualizing.isRelativeDualizingComplex_baseChange_at`,
  `Dualizing.isRelativeDualizingComplex_baseChange_of_relativelyPerfect`,
  `Dualizing.isRelativeDualizingComplex_baseChange` — **[stacks 0E2F] (2)**, carrying the input
  at `K` alone, at the `R`-perfect objects, and at every object.
* `Dualizing.nonempty_diagonalDerivedHom_iso_of_homology` — the diagonal condition of
  [stacks 0E2C] from the cohomology of the derived-Hom object alone, unconditionally; and
  `Dualizing.isRelativeDualizingComplex_baseChange_of_homology` — **[stacks 0E2F] (2) carrying
  nothing**, from the cohomology of `RHom_{B'}(A', K' ⊗ᴸ_{A'} B')`, which is what the source's
  degreewise argument produces.
* `Dualizing.diagonalDerivedHomBaseChangeAt_of_isRelativeDualizingComplex` and
  `Dualizing.diagonalDerivedHomBaseChangeAt_of_homology` — the carried input **produced**, at a
  relative dualizing complex, from the conclusion of the clause and from cohomology respectively.
  At such an object the input is no stronger than the clause itself, so any route to clause (2)
  discharges it.

## The hypothesis that is carried, and why

Write `B = A ⊗[R] A` and `B' = A' ⊗[R'] A'`, and write `Δ : B → A`, `Δ' : B' → A'` for the two
multiplication maps.  The two defining conditions of a relative dualizing complex behave quite
differently under base change.

*Relative perfection is proved.*  It is exactly [stacks 0DHW],
`PseudoCoherence.derivedExtensionScalars_isRelativelyPerfect`, already in the library, and the
statement below is written at the same `A'` and the same derived base change so that it applies
verbatim.

*The diagonal condition is what is carried*, in two forms.  Transporting it along base change
needs that forming `RHom_B(A, - ⊗ᴸ_A B)` commutes with base change, which is the hypothesis
`Dualizing.DiagonalDerivedHomBaseChange`: for every `X` in `D(A)` the derived base change along
`A → A'` of `RHom_B(A, X ⊗ᴸ_A B)` is `RHom_{B'}(A', (X ⊗ᴸ_A A') ⊗ᴸ_{A'} B')`, the derived-Hom
base-change map of [stacks 0E1X] at the diagonal square.  Alternatively
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology` carries nothing and asks instead for
the cohomology of `RHom_{B'}(A', K' ⊗ᴸ_{A'} B')`, which is what the source's argument actually
computes: it produces a bounded below complex `E^•` of `R`-flat finitely presented `B`-modules
representing `RHom_B(A, K ⊗ᴸ_A B)` compatibly with derived base change ([stacks 0E1U]) and then
checks flatness of the cokernels degree by degree.  The two forms, and what separates each from
being discharged, are discussed below.

It is not available from the library's unconditional invertibility criteria of [stacks 0A6A].
`Stacks.DerivedHom.ExtensionOfScalars.isIso_derivedHomBaseChange` needs one of: the internal-Hom
source perfect, the target algebra perfect as a module, the ring map flat, or the ring map of
finite Tor dimension.  Here the ring map is `B → B' = B ⊗[R] R'`, the internal-Hom source is the
diagonal `A`, which is pseudo-coherent but not perfect over `B`, and `B'` has neither flatness nor
finite Tor dimension over `B` for a general `R → R'`.  Adding such a hypothesis to the tag would
not be the tag.

### Why the input is carried over the `R`-perfect objects only

The hypotheses of the source's route are available exactly there.  The ring map `R → B` is flat,
the diagonal `A` is pseudo-coherent over `B` by `Dualizing.isPseudoCoherent_diagonal` (which is
[stacks 0E1T], `PseudoCoherence.pseudoCoherent_tfae_of_surjective`, at the diagonal), and
`X ⊗ᴸ_A B` has finite Tor dimension over `R` as soon as `X` is `R`-perfect.  Those are the two
hypotheses of [stacks 0E1U],
`StacksDraft.RelativelyPerfect.exists_homComplex_representation`, which is proved and produces the
bounded below complex `E^•` of `R`-flat finitely presented `B`-modules representing
`RHom_B(A, X ⊗ᴸ_A B)`.  Over an arbitrary object of `D(A)` there is no such representative, so
`Dualizing.RelativelyPerfectDiagonalDerivedHomBaseChange` is the largest class at which the input
has any route at all, and it is all clause (2) consumes.

### What [stacks 0E1U] does *not* give, and what the residue actually is

**[stacks 0E1U] does not supply the isomorphism asserted here, and the source never asserts it.**
The base-change clause of [stacks 0E1U] is a chain-level identity
`E^• ⊗_R R' = Hom^•(P^• ⊗_R R', F^• ⊗_R R')`: the *naive* base change of `E^•` computes
`RHom_{B'}(A ⊗ᴸ_B B', (X ⊗ᴸ_A B) ⊗ᴸ_B B')`, because the base change is applied to the two
representatives `P^•` (bounded above, finite free) and `F^•` (bounded, `R`-flat), where it is
harmless.  The morphism of [stacks 0E1X] compares that object with `E^• ⊗ᴸ_B B'` instead, and
`E^•` is bounded *below* with `R`-flat terms, which is not K-flat: [stacks 064K],
`CochainComplex.KFlat.kFlat_of_flat`, asks for a bound *above*, and the filtration that would
reduce the bounded-below case to the bounded one runs the wrong way, the truncations keeping low
degrees being quotients and not subobjects.  So `E^• ⊗_B B'` and `E^• ⊗ᴸ_B B'` do not agree for
formal reasons, and nothing identifies the two sides of the asserted isomorphism through `E^•`.

What the source proves instead, having `E^•`, is the conclusion of the clause directly: it
computes `H^n(E^• ⊗_R R')`, obtaining `0` for `n ≠ 0` and `A'` for `n = 0`, by checking that each
cokernel `Q^n` of `E^{n-1} → E^n` is `R`-flat and each `Q^n → E^{n+1}` is `R`-universally
injective, by [stacks 00ME],
`Module.Flat.injective_and_flat_quotient_range_of_injective_mapQ_maximalIdeal_of_isNoetherianRing`,
which in turn needs `H^n(E^• ⊗_R κ(𝔭)) = 0` — the Noetherian case of this very clause, read at the
residue fields of `R`, supplied by [stacks 0BZV] and [stacks 0E2E].

So the residue of clause (2) has three named pieces.  The first two are proved outright; the
third is proved at the upper shriek complex, and not at an arbitrary `K`:

* [stacks 0E1U] — `StacksDraft.RelativelyPerfect.exists_homComplex_representation`;
* the degreewise flatness chase — **proved**, as
  `StacksFrontier.RingTheory.Flat.DegreewiseChase`.  [stacks 0653],
  `StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude`, is stated for a complex bounded
  *above* and cannot be used here, so its bounded below mirror is used:
  `StacksDraft.DegreewiseChase.flat_cokernel_and_exact_rTensor_of_exact_rTensor_residueField`
  takes the vanishing after `⊗_R κ(𝔭)` at every prime of `R` and returns the `R`-flatness of
  `Q^n` together with the vanishing after `⊗_R N` for every `R`-module `N`, the globalisation of
  [stacks 00ME] over the primes of `B` being
  `StacksDraft.DegreewiseChase.flat_of_injective_rTensor_residueField` and
  `StacksDraft.DegreewiseChase.injective_rTensor_of_injective_rTensor_residueField`; the
  degree-zero step `Z^0 = Ker(E^0 → E^1)` is
  `StacksDraft.DegreewiseChase.flat_ker_of_flat_cokernel` with
  `StacksDraft.DegreewiseChase.injective_and_exact_rTensor_ker_of_flat_cokernel`.  Those
  statements are about three consecutive terms of the complex and arbitrary `R`-modules, and the
  translation between them and the cohomology of a `CochainComplex (ModuleCat _) ℤ` is
  `StacksDraft.DegreewiseChase.isZero_homology_tensorModuleRight_iff_exact_rTensor`;
* the Noetherian case over a residue field, which is [stacks 0BZV] with [stacks 0E2E] and
  therefore carries only `Dualizing.KFlatAlgebraActionEq` — the keystone of
  `StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChange` — through
  `Dualizing.PolynomialPresentation.projectionCompatibility_of_kFlatAlgebraActionEq`.  At the
  upper shriek complex `φ^!(R)` this piece is **proved**, as
  `Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek` of
  `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian`: it proves the vanishing from
  those same two tags and asks for nothing beyond that one compatibility.  At an arbitrary `K` it
  is **not** proved, and the obstruction is not the vanishing but the identification — one would
  need `K ≅ φ^!(R)`, which is [stacks 0E2D].  This library has that tag as
  `Dualizing.nonempty_iso_of_isRelativeDualizingComplex`, with the invertibility of the two
  diagonals of [stacks 0BYN] as a hypothesis that is in fact *false* at the witness of
  `StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation`, and discharged outright only
  when the diagonal or the two derived base changes are perfect, or under the Tor-amplitude
  bound of [stacks 0ATK] (3).  So the vanishing is available at the complex the existence proof
  of clause (1) actually produces, and not at the general `K` the statements below are written
  at.

**`Dualizing.DiagonalDerivedHomBaseChangeAt` is therefore strictly stronger than the clause
needs**, being an isomorphism in `D(A')` where the source establishes only the cohomology of one
object.  It is carried in that form because that is the form in which the diagonal condition of
[stacks 0E2C] transports; it mentions only derived Hom, the diagonal and derived base change, and
it does not say that either side is `A` or `A'`, which is the conclusion, so it is not a
restatement of any part of what is proved.  The alternative route,
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology`, carries nothing at all: it asks
directly for the cohomology the chase computes.  That is the version to discharge, and the
obligation it leaves is purely a statement about cohomology modules — no comparison of derived
functors occurs in it.

With the chase proved, what still separates it from the two hypotheses of
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology` is not the chase but the two
identifications around it.  Above it: that [stacks 0E1U] at the diagonal square produces a
complex `E^•` whose naive base change `E^• ⊗_R R'` has the cohomology of
`RHom_{B'}(A', K' ⊗ᴸ_{A'} B')` — the content of the `IsCanonicalHomComplexBaseChangeIso` clause
of `StacksDraft.RelativelyPerfect.exists_homComplex_representation`, read through
`DerivedCategory.homologyFunctor`, and of the identification
`A ⊗ᴸ_B B' = A'` that [stacks 0E2F]'s proof gets from Tor independence.  Below it: the
residue-field input `H^n(E^• ⊗_R κ(𝔭)) = 0`, which is the third piece above — proved at the
upper shriek complex by
`Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek`, and at the arbitrary
`K` here still carrying `Dualizing.KFlatAlgebraActionEq`, for want of [stacks 0E2D].

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0DHW](https://stacks.math.columbia.edu/tag/0DHW)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- The commutation of `A' = A ⊗[R] R'` with the base change `R' ⊗[R] A` written the other way
round, as an `R'`-algebra isomorphism.  This is the identification along which flatness and
finite presentation of `A'` over `R'` are obtained, and it is the same one
[stacks 0DHW] is stated with. -/
def baseChangeComm : (R' ⊗[R] A) ≃ₐ[R'] A ⊗[R] R' :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R R' A).toRingEquiv)
    (fun r' => by
      change (Algebra.TensorProduct.comm R R' A) (algebraMap R' (R' ⊗[R] A) r') = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.TensorProduct.comm_tmul]
      rfl)

variable [Module.Flat R A]

/-- `A' = A ⊗[R] R'` is flat over `R'`. -/
theorem flat_baseChange : Module.Flat R' (A ⊗[R] R') :=
  Module.Flat.of_linearEquiv (baseChangeComm R A R').symm.toLinearEquiv

/-- **The one carried input of [stacks 0E2F] (2), read at a single object.**  Forming derived Hom
from the diagonal into the derived base change along the left coprojection commutes, at `X`, with
base change of the base ring: the derived base change along `A → A'` of `RHom_B(A, X ⊗ᴸ_A B)` is
`RHom_{B'}(A', (X ⊗ᴸ_A A') ⊗ᴸ_{A'} B')`, where `B = A ⊗[R] A` and `B' = A' ⊗[R'] A'`.

This is the derived-Hom base-change map of [stacks 0E1X] at the diagonal square, at `X`.  It
mentions neither relative perfection nor any identification of these objects with `A` or `A'`;
see the module documentation for why it is carried. -/
def DiagonalDerivedHomBaseChangeAt (X : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  Nonempty
    ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
          ((diagonalDerivedExtension R A).obj X)) ≅
      (derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' R' :
            (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
        ((diagonalDerivedExtension R' (A ⊗[R] R')).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom :
              A →+* A ⊗[R] R')).functor.obj X)))

/-- **The one carried input of [stacks 0E2F] (2).**  `Dualizing.DiagonalDerivedHomBaseChangeAt`
at every object of `D(A)`.

This is the derived-Hom base-change map of [stacks 0E1X] at the diagonal square.  It mentions
neither relative perfection nor any identification of these objects with `A` or `A'`; see the
module documentation for why it is carried. -/
def DiagonalDerivedHomBaseChange : Prop :=
  ∀ X : DerivedCategory (ModuleCat.{u} A), DiagonalDerivedHomBaseChangeAt R A R' X

/-- **The carried input of [stacks 0E2F] (2), restricted to the objects at which clause (2) reads
it.**  `Dualizing.DiagonalDerivedHomBaseChangeAt` at the objects of `D(A)` that are perfect
relative to `R`.

This is strictly weaker than `Dualizing.DiagonalDerivedHomBaseChange`, and it is all that
`Dualizing.isRelativeDualizingComplex_baseChange_at` consumes, relative perfection being the
first defining condition of [stacks 0E2C].  The restriction is exactly the hypothesis of
[stacks 0E1U], `StacksDraft.RelativelyPerfect.exists_homComplex_representation`, which is the
statement the source uses to establish it: `A` is pseudo-coherent over `B` by [stacks 0E1T] and
`X ⊗ᴸ_A B` has finite Tor dimension over `R` as soon as `X` is `R`-perfect, those being the two
hypotheses of that lemma at the flat ring map `R → B`.  Over an arbitrary object of `D(A)` no
such representative exists and the proposition is not expected to hold. -/
def RelativelyPerfectDiagonalDerivedHomBaseChange [Algebra.FinitePresentation R A] : Prop :=
  ∀ X : DerivedCategory (ModuleCat.{u} A),
    PseudoCoherence.IsRelativelyPerfect
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
        (StacksDraft.TorAmplitude.canonicalTensorComparison R)
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R) X →
      DiagonalDerivedHomBaseChangeAt R A R' X

variable [Algebra.FinitePresentation R A]

/-- **The diagonal condition of [stacks 0E2C] is a statement about cohomology.**  For `S → B`
flat and `X` in `D(B)`, derived Hom from the diagonal into the derived base change of `X` along
the left coprojection is `B` placed in degree zero as soon as its cohomology vanishes outside
degree zero and its degree-zero cohomology is `B`.

This is the form in which the source's proof of [stacks 0E2F] (2) produces that condition: with
the bounded below complex `E^•` of [stacks 0E1U] in hand it computes `H^n(E^• ⊗_R R')` degree by
degree and never constructs an isomorphism of derived categories.  Nothing is carried here. -/
theorem nonempty_diagonalDerivedHom_iso_of_homology
    {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] [Module.Flat S B]
    (X : DerivedCategory (ModuleCat.{u} B))
    (hvan : ∀ j : ℤ, j ≠ 0 →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) j).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' S : B ⊗[S] B →ₐ[S] B).toRingHom).obj
          ((diagonalDerivedExtension S B).obj X))))
    (h0 : Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).obj
        ((derivedHom.{u, u}
            (Algebra.TensorProduct.lmul' S : B ⊗[S] B →ₐ[S] B).toRingHom).obj
          ((diagonalDerivedExtension S B).obj X)) ≅ ModuleCat.of B B)) :
    Nonempty
      ((derivedHom.{u, u}
          (Algebra.TensorProduct.lmul' S : B ⊗[S] B →ₐ[S] B).toRingHom).obj
        ((diagonalDerivedExtension S B).obj X) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) := by
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero _ 0 hvan
  obtain ⟨f⟩ := h0
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso f⟩

/-- **Stacks Project, Tag 0E2F (2), with the carried input read only at `K`.**  Let `R → A` be a
flat ring map of finite presentation, let `K` be a relative dualizing complex for `R → A` and let
`R → R'` be any ring map.  Put `A' = A ⊗[R] R'` and `K' = K ⊗ᴸ_A A'`.  Then `K'` is a relative
dualizing complex for `R' → A'`.

Relative perfection of `K'` is [stacks 0DHW] and is proved.  The diagonal condition is obtained
from that of `K` by the carried hypothesis `hbc`, which is the derived-Hom base-change map of
[stacks 0E1X] at the diagonal square **at the single object `K`**; see the module documentation.
`Dualizing.isRelativeDualizingComplex_baseChange` is the same statement with the quantified
hypothesis, and `Dualizing.isRelativeDualizingComplex_baseChange_of_relativelyPerfect` with the
hypothesis quantified only over the `R`-perfect objects. -/
theorem isRelativeDualizingComplex_baseChange_at
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hbc : DiagonalDerivedHomBaseChangeAt R A R' K) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let : Algebra.FinitePresentation R' (A ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A R')
  refine ⟨?_, ?_⟩
  · exact PseudoCoherence.derivedExtensionScalars_isRelativelyPerfect
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R').tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R')
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R') K hK.relativelyPerfect
  · exact ⟨hbc.some.symm ≪≫
      (totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom :
            A →+* A ⊗[R] R')).functor.mapIso hK.diagonalDerivedHom.some ≪≫
      derivedExtensionScalarsRegularIso.{u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')⟩

/-- **Stacks Project, Tag 0E2F (2), unconditionally, from cohomology.**  Let `R → A` be a flat
ring map of finite presentation, let `K` be a relative dualizing complex for `R → A` and let
`R → R'` be any ring map.  Put `A' = A ⊗[R] R'`, `B' = A' ⊗[R'] A'` and `K' = K ⊗ᴸ_A A'`.  If the
cohomology of `RHom_{B'}(A', K' ⊗ᴸ_{A'} B')` vanishes outside degree zero and is `A'` in degree
zero, then `K'` is a relative dualizing complex for `R' → A'`.

**Nothing is carried here.**  Relative perfection of `K'` is [stacks 0DHW]; the diagonal condition
is `Dualizing.nonempty_diagonalDerivedHom_iso_of_homology`.  The two hypotheses are exactly what
the source's degreewise argument produces from the bounded below complex `E^•` of [stacks 0E1U],
so this reduces clause (2) from an isomorphism of derived categories to a statement about
cohomology modules; see the module documentation for the three pieces that remain. -/
theorem isRelativeDualizingComplex_baseChange_of_homology
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hvan : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      ∀ j : ℤ, j ≠ 0 →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] R')) j).obj
          ((derivedHom.{u, u}
              (Algebra.TensorProduct.lmul' R' :
                (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
            ((diagonalDerivedExtension R' (A ⊗[R] R')).obj
              ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeLeftRingHom :
                  A →+* A ⊗[R] R')).functor.obj K)))))
    (h0 : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] R')) 0).obj
          ((derivedHom.{u, u}
              (Algebra.TensorProduct.lmul' R' :
                (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
            ((diagonalDerivedExtension R' (A ⊗[R] R')).obj
              ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeLeftRingHom :
                  A →+* A ⊗[R] R')).functor.obj K))) ≅
        ModuleCat.of (A ⊗[R] R') (A ⊗[R] R'))) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let : Algebra.FinitePresentation R' (A ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A R')
  refine ⟨?_, ?_⟩
  · exact PseudoCoherence.derivedExtensionScalars_isRelativelyPerfect
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R)
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R)
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R').tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison R')
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived R') K hK.relativelyPerfect
  · exact nonempty_diagonalDerivedHom_iso_of_homology _ hvan h0

/-- **At a relative dualizing complex the carried input of clause (2) is clause (2) itself.**
If `K` is a relative dualizing complex for `R → A` and `K' = K ⊗ᴸ_A A'` is one for `R' → A'`,
then `Dualizing.DiagonalDerivedHomBaseChangeAt` holds at `K`.

Both sides of the hypothesis are then `A'[0]`: the left-hand side because the diagonal condition
of [stacks 0E2C] at `K` makes `RHom_B(A, K ⊗ᴸ_A B)` equal to `A[0]`, whose derived base change is
`A'[0]`; the right-hand side because the same condition at `K'` makes
`RHom_{B'}(A', K' ⊗ᴸ_{A'} B')` equal to `A'[0]`.  This is the exact converse of the construction
inside `Dualizing.isRelativeDualizingComplex_baseChange_at`, which reads the hypothesis the other
way round, and it is what lets a route to clause (2) that carries something else — cohomology, as
in `Dualizing.isRelativeDualizingComplex_baseChange_of_homology`, or the output of the degreewise
chase — discharge the hypothesis instead.

Nothing is carried.  Note that the two statements are not interchangeable in general: the
hypothesis is about a comparison of two objects of `D(A')` at an arbitrary object, while this
reads it at an object for which both are already identified with `A'[0]`. -/
theorem diagonalDerivedHomBaseChangeAt_of_isRelativeDualizingComplex
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hK' : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
        Algebra.FinitePresentation.equiv (baseChangeComm R A R')
      IsRelativeDualizingComplex R' (A ⊗[R] R')
        ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)) :
    DiagonalDerivedHomBaseChangeAt R A R' K := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let : Algebra.FinitePresentation R' (A ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A R')
  exact ⟨(totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[R] R')).functor.mapIso hK.diagonalDerivedHom.some ≪≫
      derivedExtensionScalarsRegularIso.{u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') ≪≫
      hK'.diagonalDerivedHom.some.symm⟩

/-- **The carried input of clause (2), at a relative dualizing complex, from cohomology.**
`Dualizing.DiagonalDerivedHomBaseChangeAt` at a relative dualizing complex `K` follows from the
cohomology of `RHom_{B'}(A', K' ⊗ᴸ_{A'} B')` vanishing outside degree zero and being `A'` in
degree zero — which is what the source's degreewise argument computes.

**Nothing is carried.**  This is
`Dualizing.diagonalDerivedHomBaseChangeAt_of_isRelativeDualizingComplex` composed with
`Dualizing.isRelativeDualizingComplex_baseChange_of_homology`; it turns the hypothesis of clause
(2) into a statement about cohomology modules, which is also the hypothesis
`Dualizing.exists_isRelativeDualizingComplex` reads of clause (2). -/
theorem diagonalDerivedHomBaseChangeAt_of_homology
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hvan : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      ∀ j : ℤ, j ≠ 0 →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] R')) j).obj
          ((derivedHom.{u, u}
              (Algebra.TensorProduct.lmul' R' :
                (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
            ((diagonalDerivedExtension R' (A ⊗[R] R')).obj
              ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeLeftRingHom :
                  A →+* A ⊗[R] R')).functor.obj K)))))
    (h0 : letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] R')) 0).obj
          ((derivedHom.{u, u}
              (Algebra.TensorProduct.lmul' R' :
                (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
            ((diagonalDerivedExtension R' (A ⊗[R] R')).obj
              ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeLeftRingHom :
                  A →+* A ⊗[R] R')).functor.obj K))) ≅
        ModuleCat.of (A ⊗[R] R') (A ⊗[R] R'))) :
    DiagonalDerivedHomBaseChangeAt R A R' K :=
  diagonalDerivedHomBaseChangeAt_of_isRelativeDualizingComplex R A R' K hK
    (isRelativeDualizingComplex_baseChange_of_homology R A R' K hK hvan h0)

/-- **Stacks Project, Tag 0E2F (2), with the carried input restricted to the `R`-perfect
objects.**  This is `Dualizing.isRelativeDualizingComplex_baseChange_at` with the hypothesis read
at every object perfect relative to `R`, which `K` is by the first defining condition of
[stacks 0E2C], and the restriction matches the hypotheses of [stacks 0E1U]; see
`Dualizing.RelativelyPerfectDiagonalDerivedHomBaseChange`.
`Dualizing.exists_isRelativeDualizingComplex` consumes
`Dualizing.isRelativeDualizingComplex_baseChange_at` instead, the hypothesis at one object. -/
theorem isRelativeDualizingComplex_baseChange_of_relativelyPerfect
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hbc : RelativelyPerfectDiagonalDerivedHomBaseChange R A R') :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) :=
  isRelativeDualizingComplex_baseChange_at R A R' K hK (hbc K hK.relativelyPerfect)

/-- **Stacks Project, Tag 0E2F (2).**  Let `R → A` be a flat ring map of finite presentation, let
`K` be a relative dualizing complex for `R → A` and let `R → R'` be any ring map.  Put
`A' = A ⊗[R] R'` and `K' = K ⊗ᴸ_A A'`.  Then `K'` is a relative dualizing complex for
`R' → A'`.

Relative perfection of `K'` is [stacks 0DHW] and is proved.  The diagonal condition is obtained
from that of `K` by the carried hypothesis `hbc`, which is the derived-Hom base-change map of
[stacks 0E1X] at the diagonal square; see the module documentation. -/
theorem isRelativeDualizingComplex_baseChange
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsRelativeDualizingComplex R A K)
    (hbc : DiagonalDerivedHomBaseChange R A R') :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K) :=
  isRelativeDualizingComplex_baseChange_at R A R' K hK (hbc K)

end

end Dualizing

end

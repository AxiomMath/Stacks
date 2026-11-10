module

public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Two inputs for (3)/(4) ⟹ (2) of Tag 01V9

Conditions (3) and (4) of Stacks Tag 01V9 bound the number of generators of the relative
differentials by the local dimension of the scheme-theoretic fibre, and the source deduces
condition (2) from them by Lemma 00TT.  Tag 00TT is formalized, as
`Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing`, but it is stated over a field for
a finite type algebra, with the bound read as an inequality of `Module.finrank` and the dimension
as `TopologicalSpace.localKrullDim` of a prime spectrum.  Tag 01V9's conditions are stated with
`Stacks.SmoothAtJacobian.GeneratedByAtMost` and with `topologicalKrullDimAt` of the fibre.  **This
file is the translation between those two vocabularies**, on both axes.

## Main results

* `Stacks.Tag01V9Closure.finrank_le_of_generatedByAtMost` and
  `Stacks.Tag01V9Closure.generatedByAtMost_of_finrank_le`, combined in
  `Stacks.Tag01V9Closure.generatedByAtMost_iff_finrank_le`: over a division ring, a bound on the
  number of generators of a module is a bound on its `Module.finrank`.  The forward direction is
  unconditional — a finite spanning set makes the module finite dimensional — and the converse
  needs `Module.Finite`.
* `Stacks.Tag01V9Closure.localKrullDim_primeSpectrum_sections`: the local dimension of a scheme
  at a point of an affine open is the local dimension of the spectrum of the section ring at the
  corresponding prime.

## What is not done

**Conditions (3) and (4) are still not known to imply condition (2).**  With this file in hand,
the route of the source is reduced to one further dictionary, and nothing else.  Take the
scheme-theoretic fibre `Xs = f.fiber (f x)`, the structure morphism
`g = f.fiberToSpecResidueField (f x)` and the fibre point `xf = f.asFiber x`, and pick an affine
open `W ∋ xf` of `Xs`.  Then
`Stacks.SmoothAtRingCriterion.condition1_iff_isSmoothAt_appLE` applied to `g` on the charts `W`
and `⊤` turns the fibre conjunct of condition (2) into `Algebra.IsSmoothAt Γ(Spec κ(f x), ⊤) 𝔮`
for `𝔮` the prime of `xf`, Tag 00TT's item (1) is exactly that, and
`Stacks.Tag01V9Closure.localKrullDim_primeSpectrum_sections` plus
`Stacks.Tag01V9Closure.finrank_le_of_generatedByAtMost` reduce its item (2) to
`Stacks.SmoothAtJacobian.GeneratedByAtMost κ(𝔮) (κ(𝔮) ⊗[Γ(Xs, W)] Ω[Γ(Xs, W)⁄Γ(Spec κ(f x), ⊤)])`
at the dimension of the fibre.  What is owed is a comparison of **that** module with condition
(4)'s `Stacks.SmoothAtJacobian.relativeCotangentSpace f x`, together with the two instances
`Field ↥Γ(Spec κ(f x), ⊤)` and `Algebra.FiniteType ↥Γ(Spec κ(f x), ⊤) ↥Γ(Xs, W)`.

The comparison is a composite of available identifications, and the obstruction is that it
crosses **two different fields**: condition (4)'s module is a `κ(x)`-vector space for
`κ(x) = Scheme.residueField X x`, and Tag 00TT's is a `κ(𝔮)`-vector space for
`κ(𝔮) = Ideal.ResidueField 𝔮`.  The pieces are

1. `Stacks.FiberCotangentAssembly.fiberDifferentialsTensorIdentification`, the formalized part (4)
   of Tag 01V9, which identifies `relativeCotangentSpace f x` with
   `Stacks.SmoothAtJacobian.fiberRelativeCotangentSpace f x`, i.e. with the same construction
   performed on `g` — so the base change from `f` to its fibre is already done.  Its fibre point
   is `f.asFiberHom x (IsLocalRing.closedPoint _)`, which is `f.asFiber x` by
   `AlgebraicGeometry.Scheme.Hom.asFiberHom_apply`.
2. `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` at `g` and `xf`,
   which rewrites the stalk of the relative differentials of `g` as
   `Ω[𝒪_{Xs,xf}⁄𝒪_{Spec κ, g xf}]`.
3. a comparison of `Ω[𝒪_{Xs,xf}⁄𝒪_{Spec κ, g xf}]` with `Ω[𝒪_{Xs,xf}⁄Γ(Spec κ(f x), ⊤)]` —
   the base is replaced by a ring of which it is a localization, which changes nothing because a
   localization is formally étale, but the available
   `KaehlerDifferential.map_surjective` gives only the surjection, and condition (4) is being used
   in the direction that needs the injection too.
4. the localization `Ω[𝒪_{Xs,xf}⁄k] ≅ 𝒪_{Xs,xf} ⊗[Γ(Xs, W)] Ω[Γ(Xs, W)⁄k]`, available as the
   `IsLocalizedModule` instance on `KaehlerDifferential.map` that
   `Stacks.RelativeDifferentialStalkMap.generatedByAtMost_kaehler_localization` already uses, and
   then `TensorProduct.AlgebraTensorModule.cancelBaseChange`.
5. the field comparison `κ(𝔮) ≃+* κ(x)`: `Ideal.ResidueField` is an `abbrev` for
   `IsLocalRing.ResidueField (Localization.AtPrime 𝔮)`, and `𝒪_{Xs,xf}` is another model of that
   localization, so `IsLocalRing.ResidueField.map` of `IsLocalization.algEquiv` is the map and
   `RingHom.SurjectiveOnStalks.residueFieldMap_bijective` is its bijectivity.  Transporting
   `Stacks.SmoothAtJacobian.GeneratedByAtMost` across it needs a semilinear transfer lemma, which
   does not exist in the tree.

## Implementation notes

`Stacks.Tag01V9Closure.localKrullDim_primeSpectrum_sections` is a **thin wrapper, not new
mathematics**: it is `AlgebraicGeometry.topologicalKrullDimAt_eq_affine_open`
(`StacksFrontier/AlgebraicGeometry/Variety/Defs/Dimension/Formula.lean:52`) read in the other
direction.  That lemma used to be `private`, so this file reproved it; the original is now
public and the duplicate proof has been retired in favour of citing it.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.SmoothAtJacobian

universe u v

namespace Stacks.Tag01V9Closure

open _root_.Module Submodule in
/-- **A bound on the number of generators of a vector space is a bound on its rank.**  If a
module over a division ring has a finite spanning set of at most `d` elements then its
`Module.finrank` is at most `d`.  No finiteness hypothesis is needed: the spanning set supplies
it. -/
public theorem finrank_le_of_generatedByAtMost {K : Type u} [DivisionRing K]
    {V : Type v} [AddCommGroup V] [Module K V] {d : WithBot ℕ∞}
    (h : GeneratedByAtMost K V d) : (Module.finrank K V : WithBot ℕ∞) ≤ d := by
  obtain ⟨s, hspan, hcard⟩ := h
  refine le_trans ?_ hcard
  have hle : Module.finrank K V ≤ s.card := by
    have h2 : Submodule.span K (Set.range (Subtype.val : {y // y ∈ s} → V)) = ⊤ := by
      rw [Subtype.range_val]; exact hspan
    simpa using finrank_le_of_span_eq_top h2
  exact_mod_cast hle

/-- **A bound on the rank of a finite vector space is a bound on its number of generators.**  A
basis indexed by `Fin (Module.finrank K V)` is a spanning set of that cardinality. -/
public theorem generatedByAtMost_of_finrank_le {K : Type u} [DivisionRing K]
    {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V] {d : WithBot ℕ∞}
    (h : (Module.finrank K V : WithBot ℕ∞) ≤ d) : GeneratedByAtMost K V d := by
  classical
  let b := Module.finBasis K V
  refine ⟨Finset.univ.image b, ?_, le_trans ?_ h⟩
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact b.span_eq
  · have hle : (Finset.univ.image b).card ≤ Module.finrank K V := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin (Module.finrank K V))))
        (f := b)
    exact_mod_cast hle

/-- **For a finite vector space, the generator bound of conditions (3) and (4) of Tag 01V9 is the
rank bound of Tag 00TT.** -/
public theorem generatedByAtMost_iff_finrank_le {K : Type u} [DivisionRing K]
    {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V] (d : WithBot ℕ∞) :
    GeneratedByAtMost K V d ↔ (Module.finrank K V : WithBot ℕ∞) ≤ d :=
  ⟨finrank_le_of_generatedByAtMost, generatedByAtMost_of_finrank_le⟩

/-- **The local dimension of a scheme at a point of an affine open is the local dimension of the
spectrum of the section ring at the corresponding prime.**  This is the form Tag 00TT states its
dimension in, read at a point of a scheme as conditions (3) and (4) of Tag 01V9 state theirs. -/
public theorem localKrullDim_primeSpectrum_sections {Z : Scheme.{u}} {W : Z.Opens}
    (hW : IsAffineOpen W) (z : Z) (hz : z ∈ W) :
    TopologicalSpace.localKrullDim (PrimeSpectrum Γ(Z, W)) (hW.primeIdealOf ⟨z, hz⟩)
      = topologicalKrullDimAt Z z :=
  (AlgebraicGeometry.topologicalKrullDimAt_eq_affine_open z W hz hW).symm

end Stacks.Tag01V9Closure

end

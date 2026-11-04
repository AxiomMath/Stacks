module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.PerfectIsQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AnyModel.SupportedPushforwardPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.KoszulDetectionTwoOpens
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulObjectPerfect
public import StacksFrontier.Homology.PseudoCoherentRelative.StrictlyPerfectRestrict

/-!
# The Koszul summand of the generator of Tag 09IS is perfect

Let `X` be a scheme covered by two opens `U` and `V`, with `V` affine — presented by an
isomorphism `e : V ≅ Spec A` — and let `f₁, …, f_r ∈ A` cut the closed set `X ∖ U` out of `V`.
The inductive step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] produces the generator `Q ⊞ K`
with `K = Rj_{V*}K_V` for `K_V` the Koszul object of `f₁, …, f_r` read on `V`. This file proves
that `K` is a **perfect** object of `D(𝒪_X)`, which is what makes the generator 09IS asserts a
perfect one.

## Main results

* `Stacks.Koszul.TwoOpens.isPerfect_derivedRestrict_koszulObject` — the Koszul object read along
  an open immersion into `Spec A`, and in particular on `V`, is a perfect object.
* `Stacks.Koszul.TwoOpens.isPerfect_derivedPushforward_koszulObjectOn` — its derived pushforward
  to `X` is a perfect object of `D(𝒪_X)`.
* `Stacks.Koszul.TwoOpens.derivedQuasiCoherent_derivedPushforward_koszulObjectOn` — that
  pushforward lies in `D_QCoh(𝒪_X)`.

## Implementation notes

**The model is the locally small one** throughout, as in
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/KoszulDetectionTwoOpens.lean`: no
`CategoryTheory.HasDerivedCategory` binder appears below, so instance search supplies the global
instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`.

Neither statement needs the equations `hf` cutting `X ∖ U` out of `V`; the second needs only that
`U` and `V` cover `X`, through which `X ∖ U` is a closed subset of `X` contained in `V`. The
support hypothesis the pushforward statement consumes is
`Stacks.Koszul.TwoOpens.cohomologySupportedOn_koszulObjectOn`, and *that* is where `hf` is spent.

The first statement is proved on the complexes rather than in the derived category:
`Stacks.Koszul.Truncation.koszulObject` is the localization of a strictly perfect complex
(`Stacks.Koszul.Truncation.isStrictlyPerfect_tildeKoszulComplex`), strict perfection travels along
restriction to an open subscheme and in particular along an isomorphism
(`AlgebraicGeometry.Scheme.Modules.isStrictlyPerfect_restrictFunctor`), and
`CategoryTheory.Functor.mapDerivedCategoryFactors` identifies the restriction of the localization
with the localization of the restriction. Going through the complexes avoids a transport of
perfectness along the derived pullback of
`Stacks.Cohomology.TransportAlongIso.isPerfect_derivedPullback_scheme_iff`, which is stated at
`CategoryTheory.HasDerivedCategory.standard` and for `Lf^*` rather than for
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

## References

* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect isClosedUnderIsomorphisms_isPerfect)

universe u

namespace Stacks.Koszul.TwoOpens

variable {X : Scheme.{u}} (U V : X.Opens) {A : Type u} [CommRing A]
  (e : V.toScheme ≅ Spec (CommRingCat.of A)) {r : ℕ} (f : Fin r → A)

/-- **The Koszul object of `f₁, …, f_r`, read along an open immersion `g` into `Spec A`, is a
perfect object.** On `Spec A` it is the localization of a strictly perfect complex, restriction
along `g` carries that complex to a strictly perfect complex, and restriction commutes with
localization. At `g = e.hom` this is the Koszul object read on `V`; at an isomorphism out of an
arbitrary affine scheme it is the generator of the base case of the induction of
[Stacks, Tag 09IS], which is not the inclusion of an open subscheme. -/
theorem isPerfect_derivedRestrict_koszulObject {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion g] :
    IsPerfect (X := Y.toRingedSpace) ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
      (Stacks.Koszul.Truncation.koszulObject f)) := by
  have hsp := AlgebraicGeometry.Scheme.Modules.isStrictlyPerfect_restrictFunctor g
    (Stacks.Koszul.Truncation.isStrictlyPerfect_tildeKoszulComplex f)
  refine isClosedUnderIsomorphisms_isPerfect.of_iso
    (((Scheme.Modules.restrictFunctor g).mapDerivedCategoryFactors.app _).symm)
    (AlgebraicGeometry.RingedSpace.isPerfect_Q_obj_of_isStrictlyPerfect
      (X := Y.toRingedSpace) hsp)

/-- **The Koszul summand of the generator of [Stacks, Tag 09IS] is perfect.** If `U` and `V` cover
`X` then the derived pushforward `Rj_{V*}K_V` of the Koszul object on `V` is a perfect object of
`D(𝒪_X)`.

The cohomology of `K_V` is supported on `X ∖ U`, a closed subset of `X` contained in `V` because
`U` and `V` cover `X`, so this is [Stacks, Tag 08DP] in the form
`Stacks.DerivedQCoh.AnyModel.isPerfect_derivedPushforward_of_cohomologySupportedOn`.

Together with `Stacks.Koszul.TwoOpens.isZero_derivedRestrict_derivedPushforward_koszulObjectOn`
and `Stacks.Koszul.TwoOpens.isZero_of_rightOrthogonal_derivedPushforward_koszulObjectOn` — the
hypotheses `hKzero` and `hdet` of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection_of_prop` — this is
everything the inductive step of 09IS asks of its second summand. -/
theorem isPerfect_derivedPushforward_koszulObjectOn
    (hf : e.hom ⁻¹ᵁ Stacks.Koszul.Truncation.openComplement f = V.ι ⁻¹ᵁ U) (hUV : U ⊔ V = ⊤) :
    IsPerfect (X := X.toRingedSpace)
      ((Stacks.Duality.derivedPushforward V.ι).obj (koszulObjectOn V e f)) := by
  have hTV : ((U : Set X)ᶜ) ⊆ (V : Set X) := by
    intro x hx
    have hxt : x ∈ (⊤ : X.Opens) := trivial
    rw [← hUV] at hxt
    exact hxt.resolve_left hx
  exact Stacks.DerivedQCoh.AnyModel.isPerfect_derivedPushforward_of_cohomologySupportedOn X V
    ((U : Set X)ᶜ) U.2.isClosed_compl hTV (koszulObjectOn V e f)
    (isPerfect_derivedRestrict_koszulObject f e.hom)
    (cohomologySupportedOn_koszulObjectOn U V e f hf)

/-- **The Koszul summand of the generator of [Stacks, Tag 09IS] lies in `D_QCoh(𝒪_X)`.** It is
perfect, and a perfect object has quasi-coherent cohomology sheaves
(`Stacks.DerivedQCoh.AnyModel.isDQCoh_of_isPerfect`).

This is the membership that makes `Rj_{V*}K_V` an object of the subcategory `A = D_QCoh(𝒪_X)`
over which
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection_of_prop` quantifies
its detection hypothesis. -/
theorem derivedQuasiCoherent_derivedPushforward_koszulObjectOn
    (hf : e.hom ⁻¹ᵁ Stacks.Koszul.Truncation.openComplement f = V.ι ⁻¹ᵁ U) (hUV : U ⊔ V = ⊤) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((Stacks.Duality.derivedPushforward V.ι).obj (koszulObjectOn V e f)) :=
  Stacks.DerivedQCoh.AnyModel.isDQCoh_of_isPerfect
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory X) _
    (isPerfect_derivedPushforward_koszulObjectOn U V e f hf hUV)

end Stacks.Koszul.TwoOpens

end

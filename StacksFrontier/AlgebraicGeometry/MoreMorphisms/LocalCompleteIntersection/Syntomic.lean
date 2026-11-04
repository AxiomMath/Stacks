module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Affine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothTarget
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksCore.Tactic.StacksAttribute

/-!
# A morphism is syntomic exactly when it is flat and a local complete intersection morphism

A syntomic morphism of schemes is flat, and it is a local complete intersection morphism: near
any point of its source it factors as a Koszul-regular immersion into affine space over an
affine open of the target, followed by a smooth morphism. Conversely a flat local complete
intersection morphism is syntomic.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_syntomic`: a syntomic morphism is a
  local complete intersection morphism.
* `AlgebraicGeometry.flat_and_isLocalCompleteIntersectionMorphism_of_syntomic`: a syntomic
  morphism is flat and a local complete intersection morphism.
* `AlgebraicGeometry.syntomic_of_flat_of_isLocalCompleteIntersectionMorphism`: a flat local
  complete intersection morphism is syntomic.
* `AlgebraicGeometry.syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism`: a morphism is
  syntomic if and only if it is flat and a local complete intersection morphism.

## Implementation notes

Flatness of a syntomic morphism is `AlgebraicGeometry.flat`, Stacks 01UL.

For the Koszul factorization, fix `x` in the source of a syntomic `f : X ⟶ S`, choose an affine
open `V ∋ f x` of `S` and an affine open `U ∋ x` of `X` lying over `V`. Being syntomic, `f` is
locally of finite presentation, hence locally of finite type, so the restriction
`U ⟶ V` is locally of finite type; `U` is affine, hence quasi-affine, so Stacks 04II
(`AlgebraicGeometry.exists_immersion_affineSpace`) produces an immersion `j : U ⟶ 𝔸ⁿ_V` over
`V`. The composite `𝔸ⁿ_V ⟶ V ⟶ S` is smooth, and `j` followed by it is `U.ι ≫ f`, which is
syntomic because open immersions are syntomic. So Stacks 067T
(`Stacks.AlgebraicGeometry.isRegularImmersion_of_syntomic_of_smooth`) makes `j` a regular
immersion, hence Koszul-regular by Stacks 063K. That is a Koszul factorization of `f` near `x`.

This is the implication (2) ⇒ (1) of Stacks 069K.

Smoothness of affine space over its base is obtained by base change from affine space over
`Spec ℤ`, where it is the smooth ring map `ℤ ⟶ ℤ[xᵢ]`.

The converse implication is local: a point of the source has an affine open neighbourhood `U`
mapping into an affine open `V` of the target, and the restriction `U ⟶ V` is both flat and a
local complete intersection morphism, so the ring map `Γ(S, V) → Γ(X, U)` is flat and a local
complete intersection homomorphism by Stacks 07DB, hence syntomic by Stacks 07D3.

## References

* [The Stacks Project, Lemma 37.62.8 (069K)](https://stacks.math.columbia.edu/tag/069K)
* [The Stacks Project, Lemma 37.61.8 (07D3)](https://stacks.math.columbia.edu/tag/07D3)
* [The Stacks Project, Lemma 37.62.6 (07DB)](https://stacks.math.columbia.edu/tag/07DB)
* [The Stacks Project, Lemma 37.62.3 (069J)](https://stacks.math.columbia.edu/tag/069J)
* [The Stacks Project, Lemma 37.62.5 (069M)](https://stacks.math.columbia.edu/tag/069M)
* [The Stacks Project, Lemma 37.62.4 (069L)](https://stacks.math.columbia.edu/tag/069L)
* [The Stacks Project, Lemma 31.22.6 (067T)](https://stacks.math.columbia.edu/tag/067T)
* [The Stacks Project, Lemma 31.21.3 (063K)](https://stacks.math.columbia.edu/tag/063K)
* [The Stacks Project, Lemma 29.39.2 (04II)](https://stacks.math.columbia.edu/tag/04II)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- **Stacks 069K, the implication (2) ⇒ (1) for the Koszul condition.** A syntomic morphism of
schemes is a local complete intersection morphism. -/
theorem isLocalCompleteIntersectionMorphism_of_syntomic {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) : IsLocalCompleteIntersectionMorphism f := by
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf
  intro x
  obtain ⟨V, hV, hfxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f.base x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV : _ ≤ f ⁻¹ᵁ V⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (f ⁻¹ᵁ V : X.Opens) from hfxV)
  lift V to S.affineOpens using hV
  lift U to X.affineOpens using hU
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  obtain ⟨n, j, _, hjfac⟩ := exists_immersion_affineSpace (f.resLE V.1 U.1 hUV)
  have : Smooth (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) :=
    smooth_affineSpace_over _ _
  have hfac : U.1.ι ≫ f =
      j ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) ≫ V.1.ι := by
    rw [← Category.assoc, hjfac, Scheme.Hom.resLE_comp_ι]
  have hsyn : Syntomic
      (j ≫ (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) ≫ V.1.ι) := by
    rw [← hfac]
    exact MorphismProperty.comp_mem _ _ _ (syntomic_of_isOpenImmersion U.1.ι) hf
  have hjreg : IsKoszulRegularImmersion j :=
    isKoszulRegularImmersion_of_isRegularImmersion j
      (Stacks.AlgebraicGeometry.isRegularImmersion_of_syntomic_of_smooth j
        ((AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) ≫ V.1.ι) hsyn)
  exact ⟨finiteTypeAt_of_locallyOfFiniteType f x, U.1, hxU,
    AffineSpace (ULift.{u} (Fin n)) V.1.toScheme, j,
    (AffineSpace (ULift.{u} (Fin n)) V.1.toScheme ↘ V.1.toScheme) ≫ V.1.ι, inferInstance, hjreg,
    inferInstance, hfac⟩

/-- **Stacks 069K, the implication (2) ⇒ (1).** A syntomic morphism of schemes is flat and a
local complete intersection morphism. -/
@[stacks 069K "(2) ⇒ (1): a syntomic morphism is flat and a local complete intersection morphism"]
theorem flat_and_isLocalCompleteIntersectionMorphism_of_syntomic {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : Syntomic f) : Flat f ∧ IsLocalCompleteIntersectionMorphism f :=
  ⟨flat hf, isLocalCompleteIntersectionMorphism_of_syntomic hf⟩

/-- **Stacks 069K, the implication (1) ⇒ (2).** A flat local complete intersection morphism of
schemes is syntomic.

Near a point of the source the morphism restricts to a morphism of affine schemes which is flat
and a local complete intersection, so the induced ring map is syntomic by Stacks 07D3. -/
theorem syntomic_of_flat_of_isLocalCompleteIntersectionMorphism {X S : Scheme.{u}} {f : X ⟶ S}
    (hflat : Flat f) (hlci : IsLocalCompleteIntersectionMorphism f) : Syntomic f := by
  intro x
  obtain ⟨V, U, hxU, hUV, -⟩ := (hlci x).1
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine V.1.toScheme := V.2
  have hflatTop : (f.resLE V.1 U.1 hUV).appTop.hom.Flat := by
    rw [← HasRingHomProperty.iff_of_isAffine (P := @Flat)]
    infer_instance
  have hlciTop : (f.resLE V.1 U.1 hUV).appTop.hom.IsLocalCompleteIntersection :=
    (isLocalCompleteIntersectionMorphism_iff_appTop _).mp
      (isLocalCompleteIntersectionMorphism_resLE f hlci V.1 U.1 hUV)
  exact ⟨U, hxU, V, hUV, (RingHom.syntomic_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f V.1 U.1 hUV)).mp
    ((RingHom.syntomic_iff _).mpr
      ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection _).mpr ⟨hflatTop, hlciTop⟩))⟩

/-- **Stacks 069K.** A morphism of schemes is syntomic if and only if it is flat and a local
complete intersection morphism. -/
@[stacks 069K "the equivalence of (1) and (2)"]
theorem syntomic_iff_flat_and_isLocalCompleteIntersectionMorphism {X S : Scheme.{u}} (f : X ⟶ S) :
    Syntomic f ↔ Flat f ∧ IsLocalCompleteIntersectionMorphism f :=
  ⟨flat_and_isLocalCompleteIntersectionMorphism_of_syntomic,
    fun ⟨h1, h2⟩ => syntomic_of_flat_of_isLocalCompleteIntersectionMorphism h1 h2⟩

end AlgebraicGeometry

end

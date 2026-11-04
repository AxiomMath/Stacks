module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Fiber
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Properties of morphisms local on the source for the étale topology

Being étale and being locally quasi-finite can each be checked after precomposing with the
members of an étale covering of the source.

Both are instances of the étale case of Tag 036H. For étaleness its four hypotheses are: étale
morphisms compose, étaleness is Zariski local on the source and on the target, and étaleness
descends along a surjective étale morphism of affine schemes, the étale case of Tag 02KM.

For local quasi-finiteness only the affine descent needs an argument. If `X' → X` is a
surjective étale morphism of affine schemes and `X' → Y` is locally quasi-finite, then
`X' → Y` is of finite type, so `X → Y` is of finite type by Tag 0367; and `X → Y` has finite
fibres because `X' → Y` does and `X' → X` is surjective.

## Main results

* `AlgebraicGeometry.etale_isLocalAtSource`: **Stacks 036W**.
* `AlgebraicGeometry.locallyQuasiFinite_isLocalAtSource_etale`: **Stacks 03X4**.

## Implementation notes

Following Tag 01TD, local quasi-finiteness is the conjunction of Mathlib's
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.LocallyQuasiFinite`, the latter
of which omits the finite-type condition. Étale coverings of the source are the families of
`AlgebraicGeometry.Scheme.etalePrecoverage`.

A morphism of affine schemes is quasi-compact, which is what identifies local quasi-finiteness
with finiteness of the set-theoretic fibres through
`AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`.

## References

* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036W](https://stacks.math.columbia.edu/tag/036W)
* [Stacks Project, Tag 03X4](https://stacks.math.columbia.edu/tag/03X4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 036W.** Being an étale morphism of schemes is local on the source for
the étale topology. -/
@[stacks 036W]
instance etale_isLocalAtSource :
    MorphismProperty.IsLocalAtSource (@Etale.{u}) Scheme.etalePrecoverage := by
  have : MorphismProperty.RespectsLeft (@Etale.{u}) (@Etale.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : Etale g := hg
      have : Etale f := hf
      exact inferInstance⟩
  have : IsZariskiLocalAtSource (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  have : IsZariskiLocalAtTarget (@Etale.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale.{u}) (Q := RingHom.Etale)
  refine isLocalAtSource_etale_of_affine_descent _ fun g f hg hge hcomp ↦ ?_
  have : Surjective g := hg
  have : Etale g := hge
  have : Etale (g ≫ f) := hcomp
  exact Stacks.Etale.etale_of_comp_surjective_etale g f

/-- **Stacks Project, Tag 03X4.** Being locally quasi-finite is local on the source for the
étale topology. -/
@[stacks 03X4]
instance locallyQuasiFinite_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource
      ((@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      Scheme.etalePrecoverage := by
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  have : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u})
      (Q := RingHom.FiniteType)
  have : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)
  have : IsZariskiLocalAtTarget (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyQuasiFinite.{u})
      (Q := RingHom.QuasiFinite)
  have : IsZariskiLocalAtSource
      (@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsLocalAtSource.inf _ _
  have : IsZariskiLocalAtTarget
      (@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  have : MorphismProperty.RespectsLeft
      (@LocallyOfFiniteType.{u} ⊓ @LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u}) :=
    ⟨fun g hg f hf ↦ by
      have : Etale g := hg
      exact ⟨MorphismProperty.comp_mem _ g f inferInstance hf.1,
        MorphismProperty.comp_mem _ g f inferInstance hf.2⟩⟩
  refine isLocalAtSource_etale_of_affine_descent _ ?_
  intro X' X Y _ _ _ g f hsurj hetale hcomp
  have : Surjective g := hsurj
  have : Etale g := hetale
  have : LocallyOfFiniteType (g ≫ f) := hcomp.1
  have : LocallyQuasiFinite (g ≫ f) := hcomp.2
  have hfFT : LocallyOfFiniteType f :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
        (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) (g ≫ f) inferInstance)
        ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
          ⟨inferInstance, inferInstance⟩)
        ((HasRingHomProperty.appTop (P := @Etale) g inferInstance :
          g.appTop.hom.Etale).finitePresentation))
  have hfFibre (y : Y) : (f ⁻¹' {y}).Finite := by
    have hcompFibre :=
      (locallyQuasiFinite_iff_finite_preimage_singleton (f := g ≫ f)).mp inferInstance y
    have himage := hcompFibre.image g
    have hsurjImage : g '' (g ⁻¹' (f ⁻¹' {y})) = f ⁻¹' {y} :=
      Set.image_preimage_eq (f ⁻¹' {y}) hsurj.surj
    rwa [show ((g ≫ f) ⁻¹' {y}) = g ⁻¹' (f ⁻¹' {y}) from rfl, hsurjImage] at himage
  exact ⟨hfFT, (locallyQuasiFinite_iff_finite_preimage_singleton (f := f)).mpr hfFibre⟩

end AlgebraicGeometry

end

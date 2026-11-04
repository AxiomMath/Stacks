module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart

/-!
# Locally quasi-finite morphisms of algebraic spaces are those of relative dimension zero

A morphism of algebraic spaces which is locally of finite type is locally quasi-finite exactly
when its relative dimension at every point of its source is zero. The statement holds for a
morphism of arbitrary presheaves on the big fppf site: no algebraicity hypothesis is needed.

## Main results

* `AlgebraicGeometry.locallyQuasiFinite_iff_forall_fiberDimensionAt_eq_zero`: a morphism of
  schemes locally of finite type is locally quasi-finite if and only if the local dimension of
  its fibre is zero at every point of its source.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero`: a
  morphism of algebraic spaces locally of finite type is locally quasi-finite if and only if it
  has relative dimension `0` at every point of its source.

## References

* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes locally of finite type is locally quasi-finite exactly when the local
dimension of its fibre is zero at every point of its source. -/
public theorem locallyQuasiFinite_iff_forall_fiberDimensionAt_eq_zero {U V : Scheme.{u}}
    (h : U ⟶ V) [LocallyOfFiniteType h] :
    LocallyQuasiFinite h ↔
      ∀ u : U, topologicalKrullDimAt (h.fiber (h u)) (h.asFiber u) = 0 := by
  have hq : (∀ u : U, topologicalKrullDimAt (h.fiber (h u)) (h.asFiber u) = 0) ↔
      ∀ u : U, quasiFiniteAt h u :=
    forall_congr' fun u ↦ (quasiFiniteAt_iff_fiberDimensionAt_eq_zero h u).symm
  rw [hq, forall_quasiFiniteAt_iff]
  exact ⟨fun hqf ↦ ⟨inferInstance, hqf⟩, fun hqf ↦ hqf.2⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism `f : F ⟶ G` of presheaves over `S` on the big fppf site which is locally of finite
type is locally quasi-finite exactly when it has relative dimension `0` at every point of its
source. In particular this holds for a morphism of algebraic spaces over `S`. -/
@[stacks 04NV]
theorem isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero (f : F ⟶ G)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyQuasiFinite B S hS f ↔
      ∀ x : points B S hS F, HasRelativeDimensionAt 0 B S hS f x := by
  have hzero : ((0 : ℕ∞) : WithBot ℕ∞) = 0 := rfl
  constructor
  · intro hqf x c
    have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
      hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
    rw [hasFiberDimensionAt_ofSchemeHom_iff, hzero]
    exact (locallyQuasiFinite_iff_forall_fiberDimensionAt_eq_zero
      ((BigFppfOver.toScheme B S hS).map c.h)).mp
      (hqf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm).2 (c.sourcePoint B S hS)
  · intro hdim U V a b h ha hb hcomm
    have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
      hf U V a b h ha hb hcomm
    refine ⟨hft, (locallyQuasiFinite_iff_forall_fiberDimensionAt_eq_zero
      ((BigFppfOver.toScheme B S hS).map h)).mpr fun u ↦ ?_⟩
    rw [← hzero]
    exact (hasRelativeDimensionAt_pointsMap_iff B S hS 0 f U V a b h ha hb hcomm u).mp
      (hdim _)

end Space

end AlgebraicGeometry

end

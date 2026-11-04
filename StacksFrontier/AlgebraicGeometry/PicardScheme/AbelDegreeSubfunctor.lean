module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.AbelFunctor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardDegreeSubfunctor

/-!
# The Abel morphism `γ_d : Hilb^d_{X/S} ⟶ Pic^d_{X/S}`

Let `f : X ⟶ S` be a morphism of a big fppf site which is proper and smooth of relative dimension
one, with fibres of dimension at most one. The Abel morphism
`Stacks.Hilbert.abelTransformation` sends a degree-`d` Hilbert family `Z` over a test scheme `T`
to the class of `𝒪_{X_T}(Z)` in `Pic(X_T)`, and that class has degree `d` on every fibre of
`X_T ⟶ T` (`Stacks.Hilbert.relativeInvertibleDegreeHomAt_abelClass`). So the Abel morphism
factors through the degree-`d` subfunctor, which gives the canonical morphism

`γ_d : Hilb^d_{X/S} ⟶ Pic^d_{X/S}`

of clause (4) of [Stacks, Tag 0BA0], at the level of functors of points, into the degree-`d`
part of the Picard presheaf and into the degree-`d` subsheaf of the Picard functor. When both
functors are representable this is, by the Yoneda lemma, the morphism of schemes of the tag; no
representability is used here.

## Main definitions

* `Stacks.Hilbert.abelTransformationToDegree` — `γ_d` into `Pic^d` of the Picard presheaf.
* `Stacks.Hilbert.abelTransformationToPicardFunctorDegree` — `γ_d` into the subsheaf
  `Pic^d_{X/S}` of the Picard functor.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.PicardFunctor

universe u

namespace Stacks.Hilbert

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) [SmoothOfRelativeDimension 1 (ambientOverBase B hX hS f).hom]
  [hf : IsProper (B.inclusion.map f)]
  (hdim : ∀ s : ↥(B.inclusion.obj (B.obj hS)),
    topologicalKrullDim ↥((B.inclusion.map f).fiber s) ≤ 1) (d : ℕ)

/-- The class of a degree-`d` Hilbert family over a test scheme `T` lies in `Pic^d(X_T)`. -/
theorem abelTransformation_app_mem_picardDegreeSubfunctor (T : (BigFppfOver B S hS)ᵒᵖ)
    (Z : (hilbertFunctorOnBigFppfSite B hX hS f d).obj T) :
    (abelTransformation B hX hS f d).app T Z ∈
      (picardDegreeSubfunctor B hX hS f hdim d).obj T :=
  (mem_picardDegreeComponentConst_iff B hX hS f T.unop _ d _).2 fun t =>
    relativeInvertibleDegreeHomAt_abelClass Z.down
      (hπ := isProper_baseChangeProj B hX hS f hf T.unop)
      (topologicalKrullDim_fiber_baseChangeProj_le B hX hS f hdim T.unop) t

/-- **The Abel morphism `γ_d : Hilb^d_{X/S} ⟶ Pic^d`**, into the degree-`d` subfunctor of the
Picard presheaf: the class of a degree-`d` family has degree `d` on every fibre. -/
def abelTransformationToDegree :
    hilbertFunctorOnBigFppfSite B hX hS f d ⟶ (picardDegreeSubfunctor B hX hS f hdim d).toFunctor :=
  Subfunctor.lift (abelTransformation B hX hS f d) (by
    rintro T _ ⟨Z, rfl⟩
    exact abelTransformation_app_mem_picardDegreeSubfunctor B hX hS f hdim d T Z)

/-- `γ_d` followed by the inclusion of `Pic^d` is the Abel morphism. -/
@[simp]
theorem abelTransformationToDegree_ι :
    abelTransformationToDegree B hX hS f hdim d ≫ (picardDegreeSubfunctor B hX hS f hdim d).ι =
      abelTransformation B hX hS f d :=
  rfl

/-- **The Abel morphism `γ_d : Hilb^d_{X/S} ⟶ Pic^d_{X/S}`**, into the degree-`d` subsheaf of the
Picard functor: clause (4) of [Stacks, Tag 0BA0] at the level of functors of points. -/
def abelTransformationToPicardFunctorDegree :
    hilbertFunctorOnBigFppfSite B hX hS f d ⟶
      (picardFunctorDegreeSubfunctor B hX hS f hdim d).toFunctor :=
  Subfunctor.lift (abelTransformationToPicardFunctor B hX hS f d) (by
    rintro T _ ⟨Z, rfl⟩
    exact toPicardFunctor_mem_picardFunctorDegreeSubfunctor B hX hS f hdim d T.unop _
      (abelTransformation_app_mem_picardDegreeSubfunctor B hX hS f hdim d T Z))

/-- `γ_d` followed by the inclusion of `Pic^d_{X/S}` is the Abel morphism into the Picard
functor. -/
@[simp]
theorem abelTransformationToPicardFunctorDegree_ι :
    abelTransformationToPicardFunctorDegree B hX hS f hdim d ≫
        (picardFunctorDegreeSubfunctor B hX hS f hdim d).ι =
      abelTransformationToPicardFunctor B hX hS f d :=
  rfl

end Stacks.Hilbert

end

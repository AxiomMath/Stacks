module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandChartReading

/-!
# The reading of the band on the charts of a frame is additive, bijective and linear

Continuation of `StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesBandChartReading`: the reading
of the band of the gerbe of smooth lifts (Stacks 0CJY) on the étale charts of the base of an
object `ξ`, through the datum of Stacks 0CK6, is an additive bijection onto the morphisms of the
pullbacks of `Δ^*Ω_{I/U'}` and `𝒞_{U/U'}`, linear over the functions on the chart. With the
naturality of the reading this identifies the band module with an internal Hom, which proves that
it is quasi-coherent: Stacks 0CKG (2).

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local instance] isFibered_proj


section Edge

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedToposHom
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx) {η : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- The reading of the datum of Stacks 0CK6 over the edge, with its source spelled as an iterated
inverse image (the spelling of `AlgebraicGeometry.Space.QuasiCoherentDescent.restrictForm`). -/
theorem readEdgeX_eq (θ : LiftsActingGroup hι₁ η) :
    (Iso.homCongr (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParamEdge hι₁ m θ) =
      (Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m θ) :=
  readEdge_eq hι₁ ξ m θ

/-- The reading of the datum of Stacks 0CK6 over the edge is additive. -/
theorem readEdgeX_add (θ₁ θ₂ : LiftsActingGroup hι₁ η) :
    (Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
        ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
        (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m (θ₁ + θ₂)) =
      (Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m θ₁) +
                (Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
                ((Space.modulePullback B S hS
                (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
                (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m θ₂) :=
  (congrArg _ (postcompParam_add hι₁ m θ₁ θ₂)).trans (Iso.homCongr_symm_add _ _ _ _)

/-- The reading of the datum of Stacks 0CK6 over the edge is linear over the functions on the
closed image `i(V)`. -/
theorem readEdgeX_smul (θ : LiftsActingGroup hι₁ η)
    (t : Space.globalFunctions' B S hS (liftsZSpace hι₁ η).1) :
    (Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
        ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
        (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ m (θ ≫ Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η)
                t
          (Space.conormalModule B S hS η.ambient (liftsZ hι₁ η)))) =
      (Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m θ) ≫
                Space.globalFunctionsSmul B S hS t _ :=
  (congrArg _ (postcompParam_comp_globalFunctionsSmul hι₁ m θ t)).trans
    (Space.homCongr_symm_comp_globalFunctionsSmul B S hS _ _ _ t)

end Edge

section General

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedToposHom
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)
  {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (m : Hom ζ.1 ξ)
    {Y' : AlgebraicSpaces B S hS} (zs : Y' ⟶
        (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ : AlgebraicSpaces B S hS))
    (φ : Y' ⟶ ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩)
    (hφ : zs ≫ liftsZMap hι₁ m = φ)

/-- **The reading of the parameters of a fibre object along a morphism to `ξ` is additive.** -/
theorem readG_comp (α β : ζ ⟶ ζ) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (α ≫ β)))) =
      Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (α)))) +
      Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (β)))) := by
  refine (congrArg (fun t => Space.QuasiCoherentDescent.restrictForm B S hS (zs)
      (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m t)))
                (paramOf_comp hι₁ α β)).trans ?_
  exact (congrArg (Space.QuasiCoherentDescent.restrictForm B S hS zs (liftsZMap hι₁ m) φ hφ)
    (readEdgeX_add hι₁ ξ m _ _)).trans (Space.restrictForm_add B S hS _ _ _ _ _ _)


/-- **The reading of the parameters of a fibre object along a morphism to `ξ` is bijective**,
along an isomorphism `zs`. -/
theorem readG_bijective (d : (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ :
    AlgebraicSpaces B S hS) ⟶ Y')
    (hcd : zs ≫ d = 𝟙 Y') (hdc : d ≫ zs = 𝟙 _) :
    Function.Bijective (fun α : ζ ⟶ ζ => Space.QuasiCoherentDescent.restrictForm B S hS (zs)
        (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (α))))) :=
  (Space.restrictForm_bijective_of_inv B S hS zs d hcd hdc (liftsZMap hι₁ m) φ hφ _ _).comp
    ((Equiv.bijective _).comp ((postcompParam_bijective m hι₁).comp
      ⟨fun _ _ h => paramOf_injective hι₁ h, fun t => ⟨ofParam hι₁ ζ t, paramOf_ofParam hι₁ ζ t⟩⟩))

/-- **The reading of the parameters is linear** over the functions on the closed image of `ζ`,
along an étale `zs`. -/
theorem readG_smul (hzs : Space.IsEtale B S hS zs.hom) (α : ζ ⟶ ζ)
    (t : Space.globalFunctions' B S hS (liftsZSpace hι₁ ζ.1).1) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ α ≫ Space.globalFunctionsSmul B S hS
                (X := liftsZSpace hι₁ ζ.1) t
                (Space.conormalModule B S hS ζ.1.ambient (liftsZ hι₁ ζ.1))))) =
      Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (α)))) ≫ Space.globalFunctionsSmul B S hS
                (Space.globalFunctionsMap B S hS zs t) _ :=
  (congrArg (Space.QuasiCoherentDescent.restrictForm B S hS zs
    (liftsZMap hι₁ m) φ hφ) (readEdgeX_smul hι₁ ξ m _ t)).trans
    (Space.restrictForm_comp_globalFunctionsSmul B S hS zs hzs (liftsZMap hι₁ m) φ hφ _ t)

end General

section GeneralNaturality

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedToposHom
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- **The reading of the parameters is natural**: along a morphism `n : ζ' ⟶ ζ` of fibre objects
over `ξ` commuting with two endomorphisms, the reading of the first is the restricted reading of
Stacks 03LU of the reading of the second. -/
theorem readG_naturality {U' U : Space.SpacesEtale B S hS W}
    (ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U')
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (m' : Hom ζ'.1 ξ) (m : Hom ζ.1 ξ)
    (n : Hom ζ'.1 ζ.1) (hn : n.comp m = m') {Y'' Y' : AlgebraicSpaces B S hS}
    (zs' : Y'' ⟶ (⟨(liftsZ hι₁ ζ'.1).1.toFunctor, (liftsZ hι₁ ζ'.1).2.1⟩ : AlgebraicSpaces B S hS))
    (zs : Y' ⟶ (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ : AlgebraicSpaces B S hS))
    (φ' : Y'' ⟶ ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩)
    (φ : Y' ⟶ ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩)
    (hφ' : zs' ≫ liftsZMap hι₁ m' = φ')
    (hφ : zs ≫ liftsZMap hι₁ m = φ) (c : Y'' ⟶ Y') (hc : c ≫ φ = φ')
    (hzs : zs' ≫ liftsZRestriction hι₁ n = c ≫ zs) (α' : ζ' ⟶ ζ') (α : ζ ⟶ ζ)
    (hcomm : (Functor.Fiber.fiberInclusion.map α').comp n = n.comp
        (Functor.Fiber.fiberInclusion.map α)) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zs') (liftsZMap hι₁ (m')) (φ') (hφ')
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m'))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m'))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m'))))
                (conormalRestrictionAlongFinal hι₁ (m'))).symm
                (postcompParam hι₁ (m') (paramOf hι₁ (α')))) =
      Space.QuasiCoherentDescent.restrictForm B S hS c φ φ' hc
        (Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (α))))) := by
  have hst₁ : (zs' ≫ liftsZRestriction hι₁ n) ≫ liftsZMap hι₁ m = φ' :=
    (Category.assoc _ _ _).trans ((congrArg (zs' ≫ ·)
      ((liftsZRestriction_comp_liftsZMap hι₁ n m).trans (congrArg (liftsZMap hι₁) hn))).trans hφ')
  have hst₂ : (c ≫ zs) ≫ liftsZMap hι₁ m = φ' :=
    (Category.assoc _ _ _).trans ((congrArg (c ≫ ·) hφ).trans hc)
  refine (congrArg (fun t => Space.QuasiCoherentDescent.restrictForm B S hS (zs')
      (liftsZMap hι₁ (m')) (φ') (hφ') t)
    (readEdgeX_eq hι₁ ξ m' (paramOf hι₁ α')).symm).trans ?_
  refine (congrArg (fun t => Space.QuasiCoherentDescent.restrictForm B S hS (zs')
      (liftsZMap hι₁ (m')) (φ') (hφ') t)
    (readParam_comp hι₁ n m m' hn (Functor.Fiber.fiberInclusion.map α')
      (Functor.Fiber.fiberInclusion.map α) (base_eq_id_of_fiber α') (base_eq_id_of_fiber α)
      hcomm)).trans ?_
  refine (Space.QuasiCoherentDescent.restrictForm_comp B S hS zs' (liftsZRestriction hι₁ n)
    (liftsZMap hι₁ m) (liftsZMap hι₁ m') _ _ rfl φ' hφ' hst₁ _).trans ?_
  refine (Space.restrictForm_congr_left B S hS hzs φ' hst₁ hst₂ _).trans ?_
  refine (Space.QuasiCoherentDescent.restrictForm_comp B S hS c zs (liftsZMap hι₁ m) φ hφ _ rfl
    φ' hc hst₂ _).symm.trans ?_
  exact congrArg (fun t => Space.QuasiCoherentDescent.restrictForm B S hS c φ φ' hc
    (Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ) t))
        (readEdgeX_eq hι₁ ξ m (paramOf hι₁ α))

end GeneralNaturality

section Band

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedToposHom
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)
  (hne : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyNonempty
    (Space.SpacesEtale.topology B S hS W))
  (hlc : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).LocallyConnected
    (Space.SpacesEtale.topology B S hS W))
  (𝒢 : Sheaf (Space.SpacesEtale.topology B S hS W) CommGrpCat.{u + 1})
  (θ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U),
    (Over.forget U).op ⋙ 𝒢.obj ⋙ forget CommGrpCat.{u + 1} ≅
      (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).morPresheaf ξ ξ ⋙
        uliftFunctor.{u + 1, u + 1})
  (h₁ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a b : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) (a * b)).down =
        ((θ U ξ).hom.app (op g) a).down ≫ ((θ U ξ).hom.app (op g) b).down)
  (h₂ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (φ : ξ ⟶ ζ) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      haveI : ∀ U, IsGroupoid ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) :=
        isFiberedInGroupoids_proj.fiber_isGroupoid
      ((θ U ζ).hom.app (op g) a).down =
        Functor.pullbackFiberHom (CategoryTheory.inv φ) g.hom ≫
          ((θ U ξ).hom.app (op g) a).down ≫ Functor.pullbackFiberHom φ g.hom)
  (h₃ : ∀ (U : Space.SpacesEtale B S hS W)
    (ξ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (g : Over U)
    (a : 𝒢.obj.obj (op g.left)),
      ((θ U ξ).hom.app (op g) a).down =
        (Functor.pullbackFiberIdIso (Functor.pullbackFiber
          (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).inv ≫
          ((θ g.left (Functor.pullbackFiber (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ
            g.hom)).hom.app (op (Over.mk (𝟙 g.left))) a).down ≫
          (Functor.pullbackFiberIdIso (Functor.pullbackFiber
            (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _) ξ g.hom)).hom)
  {U : Space.SpacesEtale B S hS W}
    (ζ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U) (m : Hom ζ.1 ξ)
    {Y' : AlgebraicSpaces B S hS} (zs : Y' ⟶
        (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ : AlgebraicSpaces B S hS))
    (φ : Y' ⟶ ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩)
    (hφ : zs ≫ liftsZMap hι₁ m = φ)

include h₁ in
/-- **The reading of the band along a morphism to `ξ` is an additive bijection** onto the
morphisms of the pullbacks of `Δ^*Ω_{I/U'}` and `𝒞_{U/U'}`, along an isomorphism `zs`. -/
theorem exists_readEquiv (d : (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ :
    AlgebraicSpaces B S hS) ⟶ Y')
    (hcd : zs ≫ d = 𝟙 Y') (hdc : d ≫ zs = 𝟙 _) :
    ∃ e : Additive (𝒢.val.obj (op U)) ≃+
        ((Space.modulePullback B S hS φ).obj
        ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
        (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ⟶
        (Space.modulePullback B S hS φ).obj
        (Space.conormalModule B S hS ξ.ambient (baseSubspace hι₁ ξ))),
      ∀ a, e a = Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁
                (Functor.bandFrame θ U ζ (Additive.toMul a))))) :=
  ⟨AddEquiv.ofBijective (AddMonoidHom.mk'
      (fun a => Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (Functor.bandFrame θ U ζ (Additive.toMul a))))))
    (fun a b => (congrArg (fun α => Space.QuasiCoherentDescent.restrictForm B S hS (zs)
        (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (α)))))
      (Functor.bandFrame_mul θ h₁ U ζ (Additive.toMul a) (Additive.toMul b))).trans
        (readG_comp hι₁ ξ ζ m zs φ hφ _ _)))
    ((readG_bijective hι₁ ξ ζ m zs φ hφ d hcd hdc).comp
      ((Functor.bandFrame θ U ζ).bijective.comp Additive.toMul.bijective)), fun _ => rfl⟩

/-- **The reading of the band is linear**: the descended product by a function `c` on `U` is read
as multiplication by `c` restricted along `zs` (an étale morphism). -/
theorem readG_bandSmul (hzs : Space.IsEtale B S hS zs.hom) (c : (bandRing B S hS W).obj (op U))
    (a : 𝒢.val.obj (op U)) :
    Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁
                (Functor.bandFrame θ U ζ (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U c a))))) =
      Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ) (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm
                (postcompParam hι₁ (m) (paramOf hι₁ (Functor.bandFrame θ U ζ a)))) ≫
                Space.globalFunctionsSmul B S hS
        (Space.globalFunctionsMap B S hS zs (liftsScalar hι₁ ζ.1 (frameScalar ζ c))) _ :=
  (congrArg (fun t => Space.QuasiCoherentDescent.restrictForm B S hS (zs) (liftsZMap hι₁ (m)) (φ)
      (hφ)
      ((Iso.homCongr (X := (Space.modulePullback B S hS (liftsZMap hι₁ (m))).obj
          ((Space.modulePullback B S hS (Y := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩)
          (diagonalRestriction hι₁ ξ)).obj (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst)))) (((Space.modulePullbackCompIso B S hS
        (Z := ⟨(liftsW₀ hι₁ ξ).1.toFunctor, (liftsW₀ hι₁ ξ).2.1⟩) (liftsZMap hι₁ (m))
        (diagonalRestriction hι₁ ξ)).app (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) ≪≫ eqToIso
                (congrArg (fun e => (Space.modulePullback B S hS e).obj
        (Space.sheafOfDifferentials B S hS
          (Space.subspaceInclusion B S hS ξ.selfIntersection.pt (liftsW₀ hι₁ ξ) ≫
            ξ.selfIntersection.fst))) (liftsZMap_comp_diagonalRestriction_liftsW₀ hι₁ ξ (m))))
                (conormalRestrictionAlongFinal hι₁ (m))).symm (postcompParam hι₁ m t)))
                (bandParam_bandSmul hι₁ θ h₁ hne hlc h₂ h₃ U ζ c a)).trans
    (readG_smul hι₁ ξ ζ m zs φ hφ hzs _ _)

/-- **The chosen reading of the band is linear**
(`AlgebraicGeometry.Stack.EtaleSmoothLift.readG_bandSmul` for the equivalence of
`AlgebraicGeometry.Stack.EtaleSmoothLift.exists_readEquiv`). -/
theorem readEquiv_bandSmul (d : (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ :
    AlgebraicSpaces B S hS) ⟶ Y')
    (hcd : zs ≫ d = 𝟙 Y') (hdc : d ≫ zs = 𝟙 _) (hzs : Space.IsEtale B S hS zs.hom)
    (c : (bandRing B S hS W).obj (op U)) (a : 𝒢.val.obj (op U)) :
    (exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ m zs φ hφ d hcd hdc).choose
    (Additive.ofMul (bandSmul hι₁ hne hlc 𝒢 θ h₁ h₂ h₃ U c a)) =
      (exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ m zs φ hφ d hcd hdc).choose (Additive.ofMul a) ≫
          Space.globalFunctionsSmul B S hS
        (Space.globalFunctionsMap B S hS zs (liftsScalar hι₁ ζ.1 (frameScalar ζ c))) _ :=
  ((exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ m zs φ hφ d hcd hdc).choose_spec _).trans
    ((readG_bandSmul hι₁ ξ hne hlc 𝒢 θ h₁ h₂ h₃ ζ m zs φ hφ hzs c a).trans
      (congrArg (fun u => u ≫ Space.globalFunctionsSmul B S hS
        (Space.globalFunctionsMap B S hS zs (liftsScalar hι₁ ζ.1 (frameScalar ζ c))) _)
        ((exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ m zs φ hφ d hcd hdc).choose_spec _).symm))

/-- **The chosen reading of the band is natural** along a morphism `n : ζ' ⟶ ζ` of fibre objects
over `ξ` commuting with the bandings of `a'` and `a`. -/
theorem readEquiv_naturality (d : (⟨(liftsZ hι₁ ζ.1).1.toFunctor, (liftsZ hι₁ ζ.1).2.1⟩ :
    AlgebraicSpaces B S hS) ⟶ Y')
    (hcd : zs ≫ d = 𝟙 Y') (hdc : d ≫ zs = 𝟙 _) {U' : Space.SpacesEtale B S hS W}
    (ζ' : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber U') (m' : Hom ζ'.1 ξ)
    (n : Hom ζ'.1 ζ.1) (hn : n.comp m = m') {Y'' : AlgebraicSpaces B S hS}
    (zs' : Y'' ⟶ (⟨(liftsZ hι₁ ζ'.1).1.toFunctor, (liftsZ hι₁ ζ'.1).2.1⟩ : AlgebraicSpaces B S hS))
    (φ' : Y'' ⟶ ⟨(baseSubspace hι₁ ξ).1.toFunctor, (baseSubspace hι₁ ξ).2.1⟩)
    (hφ' : zs' ≫ liftsZMap hι₁ m' = φ')
    (d' : (⟨(liftsZ hι₁ ζ'.1).1.toFunctor, (liftsZ hι₁ ζ'.1).2.1⟩ : AlgebraicSpaces B S hS) ⟶ Y'')
    (hcd' : zs' ≫ d' = 𝟙 Y'') (hdc' : d' ≫ zs' = 𝟙 _)
    (c : Y'' ⟶ Y') (hc : c ≫ φ = φ')
    (hzs : zs' ≫ liftsZRestriction hι₁ n = c ≫ zs) (a' : Additive (𝒢.val.obj (op U')))
    (a : Additive (𝒢.val.obj (op U)))
    (hcomm : (Functor.Fiber.fiberInclusion.map
        (Functor.bandFrame θ U' ζ' (Additive.toMul a'))).comp n =
      n.comp (Functor.Fiber.fiberInclusion.map (Functor.bandFrame θ U ζ (Additive.toMul a)))) :
    (exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ' m' zs' φ' hφ' d' hcd' hdc').choose a' =
      Space.QuasiCoherentDescent.restrictForm B S hS c φ φ' hc
        ((exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ m zs φ hφ d hcd hdc).choose a) :=
  ((exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ' m' zs' φ' hφ' d' hcd' hdc').choose_spec a').trans
    ((readG_naturality hι₁ ξ ζ' ζ m' m n hn zs' zs φ' φ hφ' hφ c hc hzs _ _ hcomm).trans
      (congrArg (Space.QuasiCoherentDescent.restrictForm B S hS c φ φ' hc)
        ((exists_readEquiv hι₁ ξ 𝒢 θ h₁ ζ m zs φ hφ d hcd hdc).choose_spec a).symm))

end Band

section Scalars

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- A function on `U`, read on the base of the fibre object `⟨ξ', rfl⟩` over the base of `ξ'`,
is itself. -/
theorem frameScalar_mk (ξ' : EtaleSmoothLift B S hS ι hι W x hx)
    (r : (bandRing B S hS W).obj (op ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).obj ξ'))) :
    frameScalar (⟨ξ', rfl⟩ : (proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).Fiber
      ((proj : EtaleSmoothLift B S hS ι hι W x hx ⥤ _).obj ξ')) r = r := by
  unfold frameScalar
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, RingCat.hom_id, RingHom.id_apply]
  rfl

/-- **The two readings of a function on a chart agree**: a function `r` on an étale chart `T` of
the base `U` of `ξ`, read as a function on the algebraic space `T` through the comparison of
Stacks 03G1 for `W` (`AlgebraicGeometry.Stack.EtaleSmoothLift.chartScalar`) or through the
localization of `U_étale` at `T` (`AlgebraicGeometry.Space.chartRingMap`), is the same global
function. -/
theorem chartScalar_postcomp (T : Space.SmallEtale B S hS ξ.base.obj.left.1)
    (r : (Space.structureRingSheaf B S hS ξ.base.obj.left).val.obj (op T)) :
    (chartScalar B S hS W ((Space.smallEtalePostcomp B S hS ξ.base.obj.hom ξ.base.property).obj T)
        r :
      Space.globalFunctions' B S hS (Space.chartSpace B S hS ξ.base.obj.left T).1) =
      Space.chartRingMap B S hS T r := by
  apply (Space.globalFunctionsYonedaRingEquiv B S hS _).injective
  refine ((Space.globalFunctionsYonedaRingEquiv B S hS _).apply_symm_apply _).trans ?_
  symm
  show ((Oforget (Space.smallEtaleStructurePresheaf B S hS ξ.base.obj.left.1
      ξ.base.obj.left.2)).map
    (𝟙 (op T))).hom r = r
  rw [CategoryTheory.Functor.map_id]
  rfl

end Scalars


end AlgebraicGeometry.Stack.EtaleSmoothLift

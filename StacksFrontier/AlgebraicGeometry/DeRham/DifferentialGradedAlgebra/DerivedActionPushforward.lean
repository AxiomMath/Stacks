module

public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.ClassMorphismRelativeCup
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Multiplicative maps into a direct image and the derived actions

Let `h : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces, `𝒜` and `𝒜'` sheaves of
differential graded algebras on `X` and `X'`, `M` and `M'` right differential graded modules over
them, and `d : 𝒜 ⟶ h_*𝒜'`, `d_M : M ⟶ h_*M'` maps of complexes compatible with the actions on total
tensor complexes, through the naive cup product `Tot(h_*M' ⊗ h_*𝒜') ⟶ h_*Tot(M' ⊗ 𝒜')`. Then the
composites `c = Q(d) ≫ (h_* ⟶ Rh_*)`, `c_M = Q(d_M) ≫ (h_* ⟶ Rh_*)` are compatible with the
derived actions `M ⊗^𝐋 𝒜 ⟶ M` and `Rh_*M' ⊗^𝐋 Rh_*𝒜' ⟶ Rh_*(M' ⊗^𝐋 𝒜') ⟶ Rh_*M'`, the latter
through the relative cup product of Tag 0B68. The proof is Tag 0FP3 together with the naturality
of the comparisons with the ordinary total tensor complex and with the degreewise direct image.

## Main results

* `AlgebraicGeometry.SheafOfModules.relativeCupProduct_derivedAction_pushforwardComparisonQ`.

## References

* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ
  pushforwardComparisonQ_naturality naiveCupProduct_relativeCupProduct)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (naiveCupProduct)
open scoped CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens
open scoped Stacks.StandardDerivedModel

universe u

attribute [local implicit_reducible] structureSheafRing StacksDraft.KFlat.modulePushforward
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

/-- In any category, pasting the commutative diagrams `hTT`, `hR`, `h03`, `hnat`, `hpc` and `hd`
shows that the composite `(t ≫ q) ≫ e ≫ p₀` equals `TT' ≫ rc ≫ R'`. -/
theorem multiplicative_paste {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ Y₅ : C}
    (t : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) (e : X₂ ⟶ X₃) (p₀ : X₃ ⟶ X₄)
    (TT : X₀ ⟶ Y₀) (tY : Y₀ ⟶ Y₂) (a : X₁ ⟶ Y₂) (n : Y₂ ⟶ Y₃) (w : Y₃ ⟶ X₃) (pT : Y₃ ⟶ Y₄)
    (Rq : Y₄ ⟶ X₄) (TP : Y₀ ⟶ Y₁) (rc : Y₁ ⟶ Y₅) (Rt : Y₅ ⟶ Y₄) (TT' : X₀ ⟶ Y₁) (R' : Y₅ ⟶ X₄)
    (hTT : TT' = TT ≫ TP) (hR : R' = Rt ≫ Rq) (h03 : tY ≫ n ≫ pT = TP ≫ rc ≫ Rt)
    (hnat : TT ≫ tY = t ≫ a) (hpc : w ≫ p₀ = pT ≫ Rq) (hd : q ≫ e = a ≫ n ≫ w) :
    (t ≫ q) ≫ e ≫ p₀ = TT' ≫ rc ≫ R' := by
  subst hTT hR
  simp only [Category.assoc]
  rw [reassoc_of% hd, hpc, ← reassoc_of% hnat, reassoc_of% h03]

variable {S S' : RingedSpace.{u, u}} (h : S' ⟶ S)
  {𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf S.sheaf)}
  {𝒜' : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (ringSheaf S'.sheaf)}

/-- **A map of complexes into a direct image compatible with the actions is compatible with the
derived actions.** Let `d : 𝒜 ⟶ h_*𝒜'` and `d_M : M ⟶ h_*M'` be maps of complexes with
`d_M(x · a) = d_M(x) · d(a)` on total tensor complexes, the right side read through the naive
cup product. Then, writing `c = Q(d) ≫ (h_* ⟶ Rh_*)` and `c_M = Q(d_M) ≫ (h_* ⟶ Rh_*)`,

`(c_M ⊗ c) ≫ μ_{rel} ≫ Rh_*(μ_{M'}) = μ_M ≫ c_M`

in `D(𝒪_X)`, where `μ_{rel}` is the relative cup product of Tag 0B68. -/
theorem relativeCupProduct_derivedAction_pushforwardComparisonQ
    (M : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜)
    (M' : _root_.SheafOfModules.DifferentialGradedModule.{u, u, u} 𝒜')
    (dM : M.complex ⟶
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj M'.complex)
    (d : 𝒜.complex ⟶
      (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).obj 𝒜'.complex)
    (hd : dgAction M ≫ dM =
      HomologicalComplex.mapBifunctorMap dM d (sheafTensor S.sheaf) (ComplexShape.up ℤ) ≫
        naiveCupProduct h M'.complex 𝒜'.complex ≫
        (Stacks.Cohomology.NaiveCupProductOnRingedSpaces.pushforwardComplex h).map (dgAction M')) :
    Eq ((Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
          ((DerivedCategory.Q.map dM ≫ pushforwardComparisonQ h M'.complex) ×ₘ
            (DerivedCategory.Q.map d ≫ pushforwardComparisonQ h 𝒜'.complex)) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct h
          (DerivedCategory.Q.obj M'.complex) (DerivedCategory.Q.obj 𝒜'.complex) ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map
          (derivedAction 𝒜' M'))
      (derivedAction 𝒜 M ≫ DerivedCategory.Q.map dM ≫ pushforwardComparisonQ h M'.complex) := by
  have hnat := (Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans S).naturality
    (X := (M.complex, 𝒜.complex)) (dM ×ₘ d)
  dsimp only [Functor.comp_map, Functor.prod_map] at hnat
  rw [Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map] at hnat
  refine Eq.symm ?_
  exact multiplicative_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((congrArg (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf)).map
        (prod_comp (DerivedCategory.Q.map dM ×ₘ DerivedCategory.Q.map d)
          (pushforwardComparisonQ h M'.complex ×ₘ pushforwardComparisonQ h 𝒜'.complex)).symm).trans
        (Functor.map_comp _ _ _))
    (Functor.map_comp _ _ _)
    (naiveCupProduct_relativeCupProduct h M'.complex 𝒜'.complex) hnat
    (pushforwardComparisonQ_naturality h (dgAction M'))
    ((DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map hd).trans
      ((DerivedCategory.Q.map_comp _ _).trans
        (congrArg (_ ≫ ·) (DerivedCategory.Q.map_comp _ _)))))

end AlgebraicGeometry.SheafOfModules

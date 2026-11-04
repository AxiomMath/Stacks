module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SheafFrobeniusMatrices
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameRamification.LAdicTameInertia
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# The local data of Weil II 1.8.4 at a closed point of a curve

Let `W` be an integral scheme smooth of relative dimension one over a finite field `k`, `V ⊆ W`
an open (through an open immersion `jW`) and `y ∈ W` a closed point. The local ring `𝒪_{W,y}` is a
discrete valuation ring with fraction field the function field `K = κ(η_V)` of `V`
(`Stacks.EtaleCohomology.isFractionRing_curveLocalRingToFunctionField`), and for a separable
closure `L` of `K` inside an algebraic closure `Ω`, a maximal ideal `P` of the integral closure of
`𝒪_{W,y}` in `L` and an arithmetic Frobenius `Fr` at `P` exist. These are the local data of
`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput` at `y`
(`Stacks.EtaleCohomology.curveLocalFrobeniusData`).

## Main results

* `Stacks.EtaleCohomology.isFractionRing_curveLocalRingToFunctionField`: the local ring `𝒪_{W,y}`
  has fraction field the function field of `V`.
* `Stacks.EtaleCohomology.curveLocalFrobeniusData`: the local data of
  `Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput` exist at a closed point `y`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

universe u

namespace Stacks.EtaleCohomology

variable {V W : Scheme.{u}} [IrreducibleSpace V] [IsIntegral W] (jW : V ⟶ W) [IsOpenImmersion jW]
  {y : W} (hy : jW.base (genericPoint V) ⤳ y)

/-- The map `κ(η_W) → κ(η_V)` of function fields induced by an open immersion `V ⟶ W`, through
the stalk at the image of the generic point of `V`. -/
def functionFieldToResidueField : W.functionField →+* V.residueField (genericPoint V) :=
  (W.presheaf.stalkSpecializes ((genericPoint_eq_of_isOpenImmersion jW).symm ▸ specializes_rfl :
      jW.base (genericPoint V) ⤳ genericPoint W) ≫
    jW.stalkMap (genericPoint V) ≫ V.residue (genericPoint V)).hom

include hy in
/-- The composite of `𝒪_{W,y} → κ(η_W)` with `functionFieldToResidueField jW` is
`curveLocalRingToFunctionField jW hy`. -/
theorem functionFieldToResidueField_comp_algebraMap :
    (functionFieldToResidueField jW).comp (algebraMap (W.presheaf.stalk y) W.functionField) =
      (curveLocalRingToFunctionField jW hy).hom := by
  rw [RingHom.algebraMap_toAlgebra, functionFieldToResidueField, ← CommRingCat.hom_comp,
    ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- The map `κ(η_W) → κ(η_V)` induced by an open immersion `V ⟶ W` is bijective. -/
theorem bijective_functionFieldToResidueField :
    Function.Bijective (functionFieldToResidueField jW) := by
  have h1 : jW.base (genericPoint V) ⤳ genericPoint W :=
    (genericPoint_eq_of_isOpenImmersion jW).symm ▸ specializes_rfl
  have h2 : genericPoint W ⤳ jW.base (genericPoint V) :=
    (genericPoint_eq_of_isOpenImmersion jW) ▸ specializes_rfl
  have : IsIso (W.presheaf.stalkSpecializes h1) :=
    ⟨⟨W.presheaf.stalkSpecializes h2, by
      rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl], by
      rw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl]⟩⟩
  refine ⟨(functionFieldToResidueField jW).injective, ?_⟩
  have : IsIso (jW.stalkMap (genericPoint V)) :=
    inferInstanceAs (IsIso (jW.toLRSHom.stalkMap (genericPoint V)))
  exact (V.residue_surjective _).comp
    ((ConcreteCategory.bijective_of_isIso (jW.stalkMap (genericPoint V))).2.comp
      (ConcreteCategory.bijective_of_isIso (W.presheaf.stalkSpecializes h1)).2)

include hy in
/-- **The local ring at `y` has fraction field the function field of `V`**, through
`Stacks.EtaleCohomology.curveLocalRingToFunctionField`. -/
public theorem isFractionRing_curveLocalRingToFunctionField :
    letI := (curveLocalRingToFunctionField jW hy).hom.toAlgebra
    IsFractionRing (W.presheaf.stalk y) (V.residueField (genericPoint V)) := by
  let := (curveLocalRingToFunctionField jW hy).hom.toAlgebra
  let e : W.functionField ≃ₐ[W.presheaf.stalk y] V.residueField (genericPoint V) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _ (bijective_functionFieldToResidueField jW))
      (fun a ↦ by
        change functionFieldToResidueField jW (algebraMap _ _ a) = _
        rw [← RingHom.comp_apply, functionFieldToResidueField_comp_algebraMap jW hy]
        rfl)
  exact IsLocalization.isLocalization_of_algEquiv _ e

include hy in
/-- **The local data of Weil II 1.8.4 at a closed point of a curve exist**: for `W` integral and
smooth of relative dimension one over a finite field, `V ⊆ W` open and `y ∈ W` closed, the stalk
`A = 𝒪_{W,y}` (a discrete valuation ring with fraction field `K = κ(η_V)`), the separable closure
`L` of `K` in an algebraic closure `Ω`, a maximal ideal `P` of the integral closure of `A` in `L`
and an arithmetic Frobenius `Fr` at `P` satisfy the hypotheses of
`Stacks.EtaleCohomology.CurveLocalInvariantsWeightInput` at `y`, with `#κ_A = #κ(y)`. -/
public theorem curveLocalFrobeniusData {k : Type u} [Field k] [Finite k] (fW : W ⟶ Spec (.of k))
    [LocallyOfFiniteType fW] [QuasiCompact fW] [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (hyc : IsClosed ({y} : Set W)) (C : Prop)
    (h : ∀ (L Ω : Type u) [Field L] [Field Ω]
      [Algebra (V.residueField (genericPoint V)) L]
      [IsSepClosure (V.residueField (genericPoint V)) L]
      [Algebra L Ω] [Algebra (V.residueField (genericPoint V)) Ω]
      [IsScalarTower (V.residueField (genericPoint V)) L Ω] [IsAlgClosed Ω]
      [Algebra.IsAlgebraic (V.residueField (genericPoint V)) Ω]
      (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
      [Algebra A (V.residueField (genericPoint V))]
      [IsFractionRing A (V.residueField (genericPoint V))] [Algebra A L]
      [IsScalarTower A (V.residueField (genericPoint V)) L]
      [Finite (IsLocalRing.ResidueField A)]
      (eA : A ≃+* W.presheaf.stalk y)
      (_ : ∀ a : A, algebraMap A (V.residueField (genericPoint V)) a =
        (curveLocalRingToFunctionField jW hy).hom (eA a))
      (P : Ideal (integralClosure A L)) [P.IsMaximal]
      (Fr : Gal(L / V.residueField (genericPoint V)))
      (_ :
        letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
          (integralClosure A L)
        Fr ∈ MulAction.stabilizer Gal(L / V.residueField (genericPoint V)) P)
      (_ :
        letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
          (integralClosure A L)
        ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P),
      Nat.card (IsLocalRing.ResidueField A) = Nat.card (W.residueField y) → C) : C := by
  classical
  let K := V.residueField (genericPoint V)
  let A : Type u := W.presheaf.stalk y
  let : Algebra A K := (curveLocalRingToFunctionField jW hy).hom.toAlgebra
  have : IsFractionRing A K := isFractionRing_curveLocalRingToFunctionField jW hy
  have : Nonempty W := ⟨y⟩
  have : IsCurve k fW :=
    { topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 fW }
  have : Smooth fW := SmoothOfRelativeDimension.smooth 1 fW
  have : IsDiscreteValuationRing A := IsCurve.isDiscreteValuationRing_stalk_of_isClosed k fW hyc
  have : Finite (IsLocalRing.ResidueField A) := finite_residueField fW y hyc
  let L : Type u := SeparableClosure K
  let Ω : Type u := AlgebraicClosure K
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (integralClosure A L)
  let := IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  obtain ⟨Fr, hFrD, hFr⟩ := Stacks.FundamentalGroup.exists_mem_stabilizer_smul_sub_pow_mem A K L P
  exact h L Ω A (RingEquiv.refl _) (fun _ ↦ rfl) P Fr hFrD hFr rfl

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleCanonical
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionExistence

/-!
# The obstruction class of Tag 08V5 on the named connecting morphism

`Deformation.ToposThickening.RingedToposExtensionProblem.obstructionClass` is formed with a
connecting morphism of the fundamental triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O` obtained by choice from
the existence statement of Tag 08SZ. This file forms the class with the connecting morphism the
proof of Tag 08SZ constructs, `CategoryTheory.Sheaf.towerConnecting`, so that the class is a
definite element depending on the data of the problem alone, and proves for it part (1) of
Tag 08V5.

## Main definitions

All names below are in the namespace `Deformation.ToposThickening.RingedToposExtensionProblem`.

* `canonicalTowerConnecting`: the connecting morphism
  `L_{O/f⁻¹O_B} ⟶ (L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O)[1]`.
* `canonicalObstructionClass`: the class `o = −(δ.comp γ)` in `Ext²_O(L_f, G)`, where
  `γ = obstructionBaseClass` is the map `L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O ⟶ G[1]` attached to `c`.

## Main results

* `nonempty_iff_canonicalObstructionClass_eq_zero`: a solution exists if and only if the class
  vanishes.

## Conventions

The sign is chosen so that the class agrees, without a sign, with the connecting map of
`T¹ ⟶ T²` along a short exact sequence of thickenings (`ShortComplex.ShortExact.singleδ`), as
the boundary condition of [Stacks Project, Tag 07YY] (iv) needs: `o = −(δ ≫ γ⟦1⟧ ≫ μ)`, with
`μ : G⟦1⟧⟦1⟧ ≅ G⟦2⟧` the shift composition. Vanishing does not see the sign.

## References

* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe t u v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

open AlgebraicGeometry (RingedTopos RingedToposHom)

variable {X : RingedTopos.{u, u, u}} {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (S : RingedToposExtensionProblem X B)
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{t} (Sheaf.targetModules.{u, u, u} X.J X.O)]

/-- **The connecting morphism of the fundamental triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O`**, the one
constructed in the proof of Tag 08SZ (`CategoryTheory.Sheaf.towerConnecting`). -/
abbrev canonicalTowerConnecting :
    Sheaf.cotangentComplexDerived.{u, u, u, t} X.J S.f.fSharpInverseImage ⟶
      (DerivedCategory.Q.obj (Sheaf.baseChangedCotangentComplex.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage))⟦(1 : ℤ)⟧ :=
  Sheaf.towerConnecting.{t, u, u, u} X.J S.baseReductionInverseImage S.f.fSharpInverseImage

omit [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The fundamental triangle of `f⁻¹O_{B'} ⟶ f⁻¹O_B ⟶ O` on `canonicalTowerConnecting` is
distinguished. -/
theorem canonicalTowerConnecting_distinguished :
    Triangle.mk (DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage))
        (DerivedCategory.Q.map (Sheaf.towerCotangentChangeOfBase.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage))
        S.canonicalTowerConnecting ∈
      distTriang (DerivedCategory (Sheaf.targetModules.{u, u, u} X.J X.O)) :=
  Sheaf.towerConnecting_distinguished.{t, u, u, u} X.J _ _

/-- **The obstruction class of Tag 08V5 (1), on the named connecting morphism**:
`o = −(δ.comp γ)` in `Ext²_O(L_f, G)`, where `δ = canonicalTowerConnecting` and
`γ = obstructionBaseClass : L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O ⟶ G[1]` is the class of the prescribed map
`c : f⁻¹J ⟶ G`. -/
def canonicalObstructionClass : S.f.cotangentExt (targetG.{u, u, u} S) 2 :=
  -(S.canonicalTowerConnecting ≫ (S.obstructionBaseClass)⟦(1 : ℤ)⟧' ≫
    (shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app _)

omit [X.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J CommRingCat.{u}] [X.J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- A composite with the shift composition isomorphism vanishes exactly when the composite before
it does. -/
private theorem comp_shiftFunctorAdd_inv_eq_zero_iff {P : DerivedCategory
    (Sheaf.targetModules.{u, u, u} X.J X.O)} {Q : DerivedCategory
      (Sheaf.targetModules.{u, u, u} X.J X.O)} (k : P ⟶ Q⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) :
    k ≫ (shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app Q = 0 ↔ k = 0 :=
  ⟨fun h0 => (cancel_mono ((shiftFunctorAdd' _ (1 : ℤ) 1 2 (by norm_num)).inv.app Q)).1
      (h0.trans zero_comp.symm),
    fun h0 => by rw [h0, zero_comp]⟩

/-- **Stacks 08V5 (1), on the named connecting morphism**: a solution of the square-zero
extension problem exists if and only if `canonicalObstructionClass` vanishes. -/
theorem nonempty_iff_canonicalObstructionClass_eq_zero :
    Nonempty S.CompatibleFirstOrderThickening ↔ S.canonicalObstructionClass = 0 := by
  have hT := (Sheaf.exists_distTriang_towerCotangent X.J S.baseReductionInverseImage
    S.f.fSharpInverseImage).choose_spec
  have key := fun δ hδ => (Iff.of_eq (congrArg (· = 0) (Category.assoc _ _ _).symm)).trans
    ((comp_shiftFunctorAdd_inv_eq_zero_iff _).trans
      (CotangentObstruction.comp_shift_towerBaseClass_eq_zero_iff (targetG.{u, u, u} S)
        S.baseReductionInverseImage S.f.fSharpInverseImage δ hδ S.baseConormalMap))
  exact S.nonempty_iff_obstructionClass_eq_zero.trans ((key _ hT).trans
    ((key _ S.canonicalTowerConnecting_distinguished).symm.trans neg_eq_zero.symm))

/-! ### The class of a solution, and its restriction to the first vertex -/

section SolutionClass

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]

/-- **The class of a solution in `Ext¹_O(NL_{O/f⁻¹O_{B'}}, G)`**: the obstruction class of
Tag 08UG of the trivial extension against the solution, both read as square-zero extensions of
`f⁻¹O_{B'}`-algebras. -/
def solutionNaiveClass (P : S.CompatibleFirstOrderThickening) :
    S.squareZeroProblem.f.naiveCotangentExt S.squareZeroProblem.G 1 :=
  CompatibleFirstOrderThickening.pairObstruction
    (S.squareZeroProblem.trivialSolution S.isIso_squareZeroProblem_baseReduction)
    (S.solutionEquivSquareZero P).1

/-- The class of a solution restricts to the prescribed map `c` on the base ideal. -/
theorem idealRestrictionOfExt_solutionNaiveClass (P : S.CompatibleFirstOrderThickening)
    (U : X.Cᵒᵖ) (a : S.I.val.obj U) :
    CompatibleFirstOrderThickening.idealRestrictionOfExt (S := S) (S.solutionNaiveClass P) U a =
      (show S.G.val.obj U from S.c.val.app U a) := by
  let Q := (S.solutionEquivSquareZero P).1
  have hQ : S.idealObstruction Q = 0 := (S.isCompatibleWithIdeal_iff_idealObstruction_eq_zero
    Q).1 (S.solutionEquivSquareZero P).2
  obtain ⟨e⟩ := CompatibleFirstOrderThickening.isomorphic_twist_trivialSolution (S := S) Q
  have h := (congrFun (congrFun (S.idealObstruction_of_iso e) U) a).trans
    (congrFun (congrFun hQ U) a)
  rw [CompatibleFirstOrderThickening.idealObstruction_twist,
    S.idealObstruction_trivialSolution] at h
  exact (neg_add_eq_zero.1 h).symm

/-- **The class of a solution in `Ext¹_O(L_{O/f⁻¹O_{B'}}, G)`**: `solutionNaiveClass` read on the
cotangent complex through the canonical map `L ⟶ NL` of Tag 08US. -/
def solutionCotangentClass (P : S.CompatibleFirstOrderThickening) :
    DerivedCategory.Q.obj (Sheaf.cotangentComplex.{u, u, u} X.J
        (S.baseReductionInverseImage ≫ S.f.fSharpInverseImage)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj (targetG.{u, u, u} S))⟦(1 : ℤ)⟧ :=
  DerivedCategory.Q.map (eqToHom (congrArg (Sheaf.cotangentComplex.{u, u, u} X.J)
      S.toThickenedBase_fSharpInverseImage.symm)) ≫
    DerivedCategory.Q.map (Sheaf.canonicalNaiveComparison.{u, u, u} X.J
      S.toThickenedBase.fSharpInverseImage) ≫ S.solutionNaiveClass P

/-- The class of a solution, restricted to the first vertex `L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O` of the
fundamental triangle, is the map attached to `c`, read through `baseExtEquiv`. -/
theorem baseExtEquiv_solutionCotangentClass (P : S.CompatibleFirstOrderThickening) :
    CotangentObstruction.baseExtEquiv.{u, u, u} X.J S.baseReductionInverseImage
        S.f.fSharpInverseImage (targetG.{u, u, u} S)
      (DerivedCategory.Q.map (Sheaf.towerExtendScalarsCotangentComplexIso.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage).hom ≫
        DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, u, u} X.J
          S.baseReductionInverseImage S.f.fSharpInverseImage) ≫ S.solutionCotangentClass P) =
      S.baseConormalMap := by
  let ξ := S.solutionNaiveClass P
  refine conormal_hom_ext S.baseReductionInverseImage _ fun U x => ?_
  refine (CotangentObstruction.baseExtEquiv_canonicalClass_conormalClass
    S.baseReductionInverseImage S.f.fSharpInverseImage (targetG.{u, u, u} S)
    (CompatibleFirstOrderThickening.twistGenerators (S := S.squareZeroProblem) ξ)
    (CompatibleFirstOrderThickening.twistGeneratorsMap (S := S.squareZeroProblem) ξ)
    S.toThickenedBase.fSharpInverseImage S.toThickenedBase_fSharpInverseImage
    (hE := CompatibleFirstOrderThickening.isLocallySurjective_twistPresentation
      (S := S.squareZeroProblem) ξ)
    (CompatibleFirstOrderThickening.twistFunctional (S := S.squareZeroProblem) ξ) ξ
    (CompatibleFirstOrderThickening.comparison_comp_eq_twistFunctional
      (S := S.squareZeroProblem) ξ) U x).trans ?_
  refine Eq.trans ?_ (S.baseConormalMap_conormalClass U x).symm
  refine congrArg ((singleShiftAutomorphism S).hom.val.app U)
    (Eq.trans ?_ (S.idealRestrictionOfExt_solutionNaiveClass P U _))
  unfold CompatibleFirstOrderThickening.idealRestrictionOfExt
  congr 2
  exact Subtype.ext (congrArg (fun y => (freeAlgebraSheafCoefficientMap X.J
    S.thickenedBaseInverseImage _).hom.app U y) (S.idealInclusion_kernelPreimage x).symm)

/-- **The class of a solution restricts to `γ` on the first vertex**: along the first map
`a : L_{f⁻¹O_B/f⁻¹O_{B'}} ⊗ O ⟶ L_{O/f⁻¹O_{B'}}` of the fundamental triangle,
`a ≫ solutionCotangentClass P = obstructionBaseClass` (the class `γ` of `c`). -/
theorem towerCotangentBaseChange_comp_solutionCotangentClass
    (P : S.CompatibleFirstOrderThickening) :
    DerivedCategory.Q.map (Sheaf.towerCotangentBaseChange.{u, u, u} X.J
        S.baseReductionInverseImage S.f.fSharpInverseImage) ≫ S.solutionCotangentClass P =
      S.obstructionBaseClass := by
  rw [obstructionBaseClass, CotangentObstruction.towerBaseClass,
    ← S.baseExtEquiv_solutionCotangentClass P, Equiv.symm_apply_apply, ← Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end SolutionClass

end Deformation.ToposThickening.RingedToposExtensionProblem

end

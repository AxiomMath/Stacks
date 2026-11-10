module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedComplexIdentities
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedToTensorShift

/-!
# The right shift of a pairing of complexes of `𝒪_X`-modules, in the derived category

For a pairing `h : Tot(A ⊗ B) ⟶ Ω^n[-n]` of complexes of `𝒪_X`-modules, the pairing
`QA ⊗^L Q(B[2n]) ⟶ Q(Ω^n[-n][2n])` of its shift in the second variable is, through
`Q(B[2n]) ≅ (QB)[2n]` and `Q(Ω^n[-n][2n]) ≅ (QΩ^n[-n])[2n]`, the commutation of `⊗^L` with the
shift followed by the shift of the pairing induced by `h`. This file is kept light: the
complex-level shift isomorphisms are expensive to elaborate next to the duality files.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (D : RelativeDualitySituation.{u})

/-- **Shifting the second factor and the target of a perfect pairing** (for the shift datum
`commShift₂` of the derived tensor product): if every `Z ⊗^L L ⟶ M` is `(v ⊗ 1) ≫ w` for a unique
`v`, the same holds for `P ⊗^L L[m] ≅ (P ⊗^L L)[m] ⟶ M[m]`. -/
theorem bijective_pairingPrecomp_commShiftIso_comp_shift {Y : RingedSpace.{u, u}}
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
    (m : ℤ) {P L M : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} Y.sheaf}
    (w : ((derivedTensorProductFunctor Y.sheaf).obj P).obj L ⟶ M)
    (hw : ∀ Z, Function.Bijective ((derivedTensorProductFunctor Y.sheaf).pairingPrecomp w Z))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} Y.sheaf) :
    letI := (canonicalDerivedTensorProduct Y.sheaf).commShift₂
    Function.Bijective ((derivedTensorProductFunctor Y.sheaf).pairingPrecomp
      ((((derivedTensorProductFunctor Y.sheaf).obj P).commShiftIso m).hom.app L ≫ w⟦m⟧') Z) := by
  let := (canonicalDerivedTensorProduct Y.sheaf).commShift₂
  have key : (derivedTensorProductFunctor Y.sheaf).pairingPrecomp
      ((((derivedTensorProductFunctor Y.sheaf).obj P).commShiftIso m).hom.app L ≫ w⟦m⟧') Z =
      (fun k => (((derivedTensorProductFunctor Y.sheaf).obj Z).commShiftIso m).hom.app L ≫ k) ∘
        (fun k => k⟦m⟧') ∘ (derivedTensorProductFunctor Y.sheaf).pairingPrecomp w Z := by
    funext v
    have := (canonicalDerivedTensorProduct Y.sheaf).commShift₂.commShift_map v
    have hc := NatTrans.shift_app_comm ((derivedTensorProductFunctor Y.sheaf).map v) m L
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hc.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _).symm)))
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ?_ (hw Z))
  · exact (Iso.app (((derivedTensorProductFunctor Y.sheaf).obj Z).commShiftIso m)
      L).homFromEquiv.symm.bijective
  · exact ⟨(shiftFunctor _ m).map_injective, (shiftFunctor _ m).map_surjective⟩

/-- The pairing `QA ⊗^L Q(B[2n]) ⟶ Q(Ω^n[-n][2n])` of the shift of `h` in its second variable. -/
def shiftedFormsPairing {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj A)).obj
        (DerivedCategory.Q.obj (B⟦(2 * D.n : ℤ)⟧)) ⟶
      DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) :=
  (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A (B⟦(2 * D.n : ℤ)⟧) ≫
    DerivedCategory.Q.map (D.rightShiftedPairingX h (2 * D.n : ℤ))

/-- The right shift of a pairing of complexes, in the derived category, for any target. -/
private theorem toTensor_rightShiftedPairingX_comp_commShiftIso_hom_aux
    {A B W : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (g : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ W) (m : ℤ) :
    letI := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
    ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A (B⟦m⟧) ≫
        DerivedCategory.Q.map (D.rightShiftedPairingX g m)) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app W =
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj A)).map
          ((DerivedCategory.Q.commShiftIso m).hom.app B) ≫
        (((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj
          (DerivedCategory.Q.obj A)).commShiftIso m).hom.app (DerivedCategory.Q.obj B) ≫
        ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
          DerivedCategory.Q.map g)⟦m⟧' := by
  let := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
  have key := Stacks.Cohomology.DerivedPullbackTensor.toTensor_shift_right D.X.toRingedSpace A B m
  have hnat := (DerivedCategory.Q.commShiftIso m).hom.naturality g
  have key2 := congrArg (· ≫ (DerivedCategory.Q.map g)⟦m⟧') key
  simp only [Category.assoc] at key2
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((congrArg (· ≫ _) (DerivedCategory.Q.map_comp _ _)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hnat))))).trans ?_
  refine key2.symm.trans ?_
  simp only [Functor.map_comp]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))

/-- **The right shift of a pairing of complexes, in the derived category.** -/
theorem shiftedFormsPairing_comp_commShiftIso_hom
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) :
    letI := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
    D.shiftedFormsPairing h ≫ (DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app D.topComplexX =
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj A)).map
          ((DerivedCategory.Q.commShiftIso (2 * D.n : ℤ)).hom.app B) ≫
        (((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj
          (DerivedCategory.Q.obj A)).commShiftIso (2 * D.n : ℤ)).hom.app (DerivedCategory.Q.obj B) ≫
        ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
          DerivedCategory.Q.map h)⟦(2 * D.n : ℤ)⟧' :=
  D.toTensor_rightShiftedPairingX_comp_commShiftIso_hom_aux h (2 * D.n : ℤ)

/-- **The right shift of a pairing of complexes, in the derived category**, for any target. -/
theorem toTensor_rightShiftedPairingX_comp_commShiftIso_hom
    {A B W : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (g : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ W) (m : ℤ) :
    letI := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
    ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A (B⟦m⟧) ≫
        DerivedCategory.Q.map (D.rightShiftedPairingX g m)) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app W =
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj (DerivedCategory.Q.obj A)).map
          ((DerivedCategory.Q.commShiftIso m).hom.app B) ≫
        (((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).obj
          (DerivedCategory.Q.obj A)).commShiftIso m).hom.app (DerivedCategory.Q.obj B) ≫
        ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
          DerivedCategory.Q.map g)⟦m⟧' :=
  D.toTensor_rightShiftedPairingX_comp_commShiftIso_hom_aux g m

/-- **Right shifts of perfect pairings of complexes are perfect.** -/
theorem bijective_pairingPrecomp_rightShiftedPairingX
    {A B W : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (g : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ W) (m : ℤ)
    (hg : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
        ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
          DerivedCategory.Q.map g) Z))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A (B⟦m⟧) ≫
        DerivedCategory.Q.map (D.rightShiftedPairingX g m)) Z) := by
  let := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
  let T := derivedTensorProductFunctor D.X.toRingedSpace.sheaf
  let ψ := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
    DerivedCategory.Q.map g
  let χ := ((T.obj (DerivedCategory.Q.obj A)).commShiftIso m).hom.app (DerivedCategory.Q.obj B) ≫
    ψ⟦m⟧'
  have hχ := bijective_pairingPrecomp_commShiftIso_comp_shift m ψ hg Z
  have rel := D.toTensor_rightShiftedPairingX_comp_commShiftIso_hom g m
  let y := (DerivedCategory.Q.commShiftIso m).hom.app B
  let k := ((DerivedCategory.Q.commShiftIso m).app W).symm
  have hφ : (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A (B⟦m⟧) ≫
        DerivedCategory.Q.map (D.rightShiftedPairingX g m) =
      ((T.obj (DerivedCategory.Q.obj A)).map y ≫ χ) ≫ k.hom :=
    ((Iso.hom_inv_id_app (DerivedCategory.Q.commShiftIso m) W ▸ (Category.comp_id _).symm :
      _ = _ ≫ _ ≫ _).trans (Category.assoc _ _ _).symm).trans (congrArg (· ≫ k.hom) rel)
  have hfun : T.pairingPrecomp ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
        A (B⟦m⟧) ≫ DerivedCategory.Q.map (D.rightShiftedPairingX g m)) Z =
      (fun t => t ≫ k.hom) ∘ (fun t => (T.obj Z).map y ≫ t) ∘ T.pairingPrecomp χ Z := by
    funext v
    exact (congrArg ((T.map v).app _ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ k.hom) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ χ) ((T.map v).naturality y).symm).trans (Category.assoc _ _ _)))))
  exact hfun ▸ Function.Bijective.comp k.homToEquiv.bijective
    (Function.Bijective.comp ((T.obj Z).mapIso
      ((DerivedCategory.Q.commShiftIso m).app B)).homFromEquiv.symm.bijective hχ)

end AlgebraicGeometry.RelativeDualitySituation

end

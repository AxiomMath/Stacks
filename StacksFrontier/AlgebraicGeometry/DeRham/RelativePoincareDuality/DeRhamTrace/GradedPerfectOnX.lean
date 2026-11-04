module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPerfectShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedWedgePerfect
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceExistence
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedShiftClass
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedToTensorShift

/-!
# Perfectness on `X` of the shifted wedge pairings of single complexes

For `p + q = n` the wedge product `Ω^p[-p] ⊗^L Ω^q[-q] ⟶ Ω^n[-n]` in `D(𝒪_X)` is a perfect pairing,
since `Ω^p ≅ SheafHom(Ω^q, Ω^n)` ([Stacks, Tag 0G8I]); so are its shifts, and its pushes
`K ⊗^L M[2n] ⟶ Ω^n[-n][2n]` into a shifted target, composed with any isomorphism of the target.
For such a pairing the pairing of [Stacks, Tag 0G81] given by the relative cup product and the
trace is perfect. The statements are phrased for pairings `Tot(A ⊗ B) ⟶ Ω^n[-n]` of complexes of
`𝒪_X`-modules with `B` a single complex of forms, the class of complexes stable under shifting.

## Main definitions

* `AlgebraicGeometry.RelativeDualitySituation.IsPerfectFormsPairing`: a pairing
  `Tot(A ⊗ B) ⟶ Ω^n[-n]` whose induced pairing `QA ⊗^L QB ⟶ Q(Ω^n[-n])` is perfect, with `B` a
  sheaf of forms placed in one degree.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.isPerfectFormsPairing_gradedWedgeX`: for
  `p + q = n` the wedge product `Ω^p[-p] ⊗ Ω^q[-q] ⟶ Ω^n[-n]` is a perfect pairing of forms.
* `AlgebraicGeometry.RelativeDualitySituation.IsPerfectFormsPairing.shiftedPairing`: a shift of
  a perfect pairing of forms is a perfect pairing of forms.
* `AlgebraicGeometry.RelativeDualitySituation.IsPerfectFormsPairing.bijective_relativeCupProduct`:
  for a perfect pairing of forms `h` and an isomorphism `e` from `Ω^n[-n][2n]` to the relative
  dualizing complex, the pairing `Rf_*QA ⊗^L Rf_*Q(B[2n]) ⟶ 𝒪_S` of the relative cup product,
  `Rf_*` of the shift of `h` followed by `e`, and the trace, is perfect.
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

/-- **A perfect pairing of a complex with a single complex of forms into `Ω^n[-n]`**: the
pairing `QA ⊗^L QB ⟶ Q(Ω^n[-n])` induced by `h` is perfect (every `Z ⊗^L QB ⟶ Q(Ω^n[-n])` is
`(v ⊗ 1) ≫` it for a unique `v : Z ⟶ QA`), and `B` is a sheaf of forms placed in one degree. -/
def IsPerfectFormsPairing {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX) : Prop :=
  (∀ Z, Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
    ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
      DerivedCategory.Q.map h) Z)) ∧
    ∃ (k : ℕ) (a : ℤ), Nonempty (B ≅ D.formsComplexX k a)

/-- The wedge product of forms placed in degree zero is a perfect pairing, in the spelling of
`CochainComplex.singleSinglePairing`. -/
theorem bijective_pairingPrecomp_toTensor_singleSinglePairing_wedge (p q : ℕ)
    [SmoothOfRelativeDimension (p + q) D.f]
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (Scheme.Hom.relativeDifferentialForms D.f p))
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (Scheme.Hom.relativeDifferentialForms D.f q)) ≫
        DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf) _ _ 0 0
          ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q))) Z) := by
  exact ((_ : Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction
    _ _).isIso_homEquiv_symm_iff _).1
    (Scheme.Hom.isIso_homEquiv_symm_formsDerivedWedge_sgl D.f p q) Z

omit D in
/-- Perfectness of a pairing is unchanged by composing with an identification of equal targets. -/
theorem bijective_pairingPrecomp_comp_Q_map_eqToHom_iff {Y : RingedSpace.{u, u}}
    [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {P L : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} Y.sheaf}
    {W W' : CochainComplex (ModulesOn Y) ℤ}
    (φ : ((derivedTensorProductFunctor Y.sheaf).obj P).obj L ⟶ DerivedCategory.Q.obj W)
    (h : W = W') (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} Y.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor Y.sheaf).pairingPrecomp
      (φ ≫ DerivedCategory.Q.map (eqToHom h)) Z) ↔
      Function.Bijective ((derivedTensorProductFunctor Y.sheaf).pairingPrecomp φ Z) := by
  subst h
  rw [eqToHom_refl, DerivedCategory.Q.map_id, Category.comp_id]

/-- The pairing `Q(Ω^p[-p]) ⊗^L Q(Ω^q[-q]) ⟶ Q(Ω^{p+q}[-p-q])` of the wedge product. -/
def gradedWedgePairingX (p q : ℤ) :=
  (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor (D.formsComplexX p p)
        (D.formsComplexX q q) ≫
    DerivedCategory.Q.map (CochainComplex.singleSinglePairing
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} D.X.toRingedSpace.sheaf)
          (Scheme.Hom.relativeDifferentialForms D.f p)
          (Scheme.Hom.relativeDifferentialForms D.f q) p q
          ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q))

/-- The graded wedge pairing is the wedge pairing followed by the identification of the target. -/
theorem toTensor_comp_Q_map_gradedWedgeX (p q : ℤ) (hpq : p + q = D.n) :
    (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor (D.formsComplexX p p)
        (D.formsComplexX q q) ≫
      DerivedCategory.Q.map (D.gradedWedgeX p q hpq) =
      D.gradedWedgePairingX p q ≫ DerivedCategory.Q.map (eqToHom
        (show (HomologicalComplex.single _ (ComplexShape.up ℤ) (p + q)).obj
          (Scheme.Hom.relativeDifferentialForms D.f (p + q)) = D.topComplexX by rw [hpq]; rfl)) :=
  (congrArg ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor (D.formsComplexX p p)
        (D.formsComplexX q q) ≫ ·)
    ((congrArg DerivedCategory.Q.map (Category.assoc _ _ _).symm).trans
      (DerivedCategory.Q.map_comp _ _))).trans (Category.assoc _ _ _).symm

/-- Perfectness of the graded wedge pairing from that of the wedge pairing. -/
theorem bijective_pairingPrecomp_toTensor_gradedWedgeX_of (p q : ℤ) (hpq : p + q = D.n)
    (h : ∀ Z, Function.Bijective
      ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
        (D.gradedWedgePairingX p q) Z))
    (Z : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} D.X.toRingedSpace.sheaf) :
    Function.Bijective ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp
      ((canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor (D.formsComplexX p p)
        (D.formsComplexX q q) ≫ DerivedCategory.Q.map (D.gradedWedgeX p q hpq)) Z) :=
  (congrArg (fun ψ => Function.Bijective
    ((derivedTensorProductFunctor D.X.toRingedSpace.sheaf).pairingPrecomp ψ Z))
      (D.toTensor_comp_Q_map_gradedWedgeX p q hpq)).mpr
    ((bijective_pairingPrecomp_comp_Q_map_eqToHom_iff _ _ Z).2 (h Z))

/-- **The wedge product of the graded pieces is a perfect pairing** ([Stacks, Tag 0G8I]). -/
theorem isPerfectFormsPairing_gradedWedgeX (p q : ℕ) (hpq : (p : ℤ) + q = D.n) :
    D.IsPerfectFormsPairing (D.gradedWedgeX p q hpq) := by
  have hn : p + q = D.n := by exact_mod_cast hpq
  have : SmoothOfRelativeDimension (p + q) D.f := by
    rw [hn]
    infer_instance
  refine ⟨fun Z => ?_, q, q, ⟨Iso.refl _⟩⟩
  exact D.bijective_pairingPrecomp_toTensor_gradedWedgeX_of p q hpq
    (D.bijective_pairingPrecomp_toTensor_singleSinglePairing _ _ _
      ((Scheme.Hom.relativeDifferentialFormsAlgebra D.f).mulSheaf p q)
      (D.bijective_pairingPrecomp_toTensor_singleSinglePairing_wedge p q) p q) Z

/-- **The shift of a perfect pairing of forms is a perfect pairing of forms.** -/
theorem IsPerfectFormsPairing.shiftedPairing {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    {h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX}
    (hh : D.IsPerfectFormsPairing h) (a b : ℤ) (hab : a + b = 0) :
    D.IsPerfectFormsPairing
      ((tensorComplexBifunctorOn D.X.toRingedSpace).shiftedPairing h a b hab) := by
  obtain ⟨hb, k, c, ⟨eB⟩⟩ := hh
  refine ⟨fun Z => ?_, k, c - b, ⟨(shiftFunctor _ b).mapIso eB ≪≫
    ((CochainComplex.singleFunctors _).shiftIso b (c - b) c (by omega)).app _⟩⟩
  let := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
  have hc := Functor.pairingCompatible_of_eq
    ((DerivedCategory.Q.commShiftIso a).hom.app A) ((DerivedCategory.Q.commShiftIso b).hom.app B)
    (Stacks.Cohomology.DerivedPullbackTensor.shiftedPairing_toTensor_comp
      D.X.toRingedSpace h a b hab)
  refine (Functor.bijective_pairingPrecomp_iff_of_pairingCompatible _ _ hc Z).2 ?_
  exact (Functor.bijective_pairingPrecomp_shiftedPairing_iff
    (derivedTensorProductFunctor D.X.toRingedSpace.sheaf) _ a b hab Z).2 (hb _)

/-- A complex isomorphic to a single complex of forms in degree `c`, shifted by `m`, is in the
derived category isomorphic to `Ω^k[0][m - c]`. -/
def formsComplexShiftIso {B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ} (k : ℕ) (c : ℤ)
    (eB : B ≅ D.formsComplexX k c) (m : ℤ) :
    (DerivedCategory.Q.obj (B⟦m⟧) : DerivedCategory D.X.Modules) ≅
      (D.f.formsInDegreeZero k)⟦m - c⟧ :=
  DerivedCategory.Q.mapIso ((shiftFunctor _ m).mapIso eB) ≪≫
    (DerivedCategory.Q.commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (((DerivedCategory.singleFunctorIsoCompQ D.X.Modules c).app _).symm ≪≫
      (((DerivedCategory.singleFunctors D.X.Modules).shiftIso (-c) c 0 (by omega)).app _).symm ≪≫
      (shiftFunctor _ (-c)).mapIso ((DerivedCategory.singleFunctorIsoCompQ D.X.Modules 0).app _)) ≪≫
    ((shiftFunctorAdd' _ (-c) m (m - c) (by omega)).app _).symm

/-- A shifted single complex of forms has quasi-coherent cohomology. -/
theorem mem_formsComplexShift {B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ} (k : ℕ)
    (c : ℤ) (eB : B ≅ D.formsComplexX k c) (m : ℤ) :
    DerivedCategoryB.derivedCategoryB (A := D.X.Modules)
      (SheafOfModules.isQuasicoherent D.X.ringCatSheaf)
      (DerivedCategory.Q.obj (B⟦m⟧) : DerivedCategory D.X.Modules) := by
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms (A := D.X.Modules) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre D.X)
  exact (DerivedCategoryB.derivedCategoryB (A := D.X.Modules)
    (SheafOfModules.isQuasicoherent D.X.ringCatSheaf)).prop_of_iso
      (D.formsComplexShiftIso k c eB m).symm (Scheme.Hom.formsInDegreeZero_shift_mem D.f k _)

/-- A shifted single complex of forms is pseudo-coherent. -/
theorem isPseudoCoherent_formsComplexShift {B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    (k : ℕ) (c : ℤ) (eB : B ≅ D.formsComplexX k c) (m : ℤ) :
    RingedSpace.IsPseudoCoherent (X := D.X.toRingedSpace)
      (DerivedCategory.Q.obj (B⟦m⟧) : DerivedCategory D.X.Modules) := by
  have := AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms D.f k
  have hE := AlgebraicGeometry.RingedSpace.IsPerfectComplex.isPseudoCoherentComplex
    (isPerfectComplex_single_of_isFiniteLocallyFree D.X _
      (Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree
        (Scheme.Hom.relativeDifferentialForms D.f k)))
  let e : (DerivedCategory.Q.obj (((HomologicalComplex.single D.X.Modules (ComplexShape.up ℤ) 0).obj
      (Scheme.Hom.relativeDifferentialForms D.f k))⟦m - c⟧) : DerivedCategory D.X.Modules) ≅
      (DerivedCategory.Q.obj (B⟦m⟧) : DerivedCategory D.X.Modules) :=
    (DerivedCategory.Q.commShiftIso (m - c)).app _ ≪≫ (D.formsComplexShiftIso k c eB m).symm
  refine ⟨((HomologicalComplex.single D.X.Modules (ComplexShape.up ℤ) 0).obj
      (Scheme.Hom.relativeDifferentialForms D.f k))⟦m - c⟧, fun j => ?_, ⟨e⟩⟩
  have h := AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_shift (hE (j + (m - c)))
    (m - c)
  rwa [add_sub_cancel_right] at h

/-- The transpose of the right shift of a perfect pairing of forms, composed with an isomorphism
of the target, is an isomorphism. -/
theorem IsPerfectFormsPairing.isIso_homEquiv_symm_shiftedFormsPairing_comp
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    {h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX}
    (hh : D.IsPerfectFormsPairing h) {W : DerivedCategory D.X.Modules}
    (e : DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) ⟶ W) [IsIso e]
    (DX : Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.TensorHomAdjunction
      (derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite D.X.sheaf).O)
      (Stacks.SheafOfModules.ringedSite D.X.sheaf).derivedSheafHomBifunctor) :
    IsIso ((DX.homEquiv (DerivedCategory.Q.obj A)
          (DerivedCategory.Q.obj (B⟦(2 * D.n : ℤ)⟧)) W).symm
      (D.shiftedFormsPairing h ≫ e)) := by
  let := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).commShift₂
  refine (DX.isIso_homEquiv_symm_iff _).2 fun Z => ?_
  let T := derivedTensorProductFunctor D.X.toRingedSpace.sheaf
  let m : ℤ := 2 * D.n
  let ψ := (canonicalDerivedTensorProduct D.X.toRingedSpace.sheaf).toTensor A B ≫
    DerivedCategory.Q.map h
  let χ := ((T.obj (DerivedCategory.Q.obj A)).commShiftIso m).hom.app (DerivedCategory.Q.obj B) ≫
    ψ⟦m⟧'
  let y := (DerivedCategory.Q.commShiftIso m).hom.app B
  let k := ((DerivedCategory.Q.commShiftIso m).app D.topComplexX).symm ≪≫ asIso e
  have hφ : D.shiftedFormsPairing h ≫ e = ((T.obj (DerivedCategory.Q.obj A)).map y ≫ χ) ≫ k.hom :=
    ((congrArg (D.shiftedFormsPairing h ≫ ·)
      (Iso.hom_inv_id_app_assoc (DerivedCategory.Q.commShiftIso m) D.topComplexX e)).symm.trans
        (Category.assoc _ _ _).symm).trans
      (congrArg (· ≫ k.hom) (D.shiftedFormsPairing_comp_commShiftIso_hom h))
  have hfun : (fun v : Z ⟶ DerivedCategory.Q.obj A =>
      (T.map v).app (DerivedCategory.Q.obj (B⟦m⟧)) ≫ D.shiftedFormsPairing h ≫ e) =
      (fun t => t ≫ k.hom) ∘ (fun t => (T.obj Z).map y ≫ t) ∘ T.pairingPrecomp χ Z := by
    funext v
    exact (congrArg ((T.map v).app _ ≫ ·) hφ).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ k.hom) ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ χ) ((T.map v).naturality y).symm).trans (Category.assoc _ _ _)))))
  exact hfun ▸ Function.Bijective.comp k.homToEquiv.bijective
    (Function.Bijective.comp ((T.obj Z).mapIso
      ((DerivedCategory.Q.commShiftIso m).app B)).homFromEquiv.symm.bijective
      (bijective_pairingPrecomp_commShiftIso_comp_shift m ψ hh.1 Z))

section ProperFlat

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- **[Stacks, Tag 0G81] for a perfect pairing of forms.** For a perfect pairing of forms
`h : Tot(A ⊗ B) ⟶ Ω^n[-n]` and an isomorphism `e` from `Ω^n[-n][2n]` to the relative dualizing
complex, the pairing `Rf_*QA ⊗^L Rf_*Q(B[2n]) ⟶ 𝒪_S` of the relative cup product, `Rf_*` of the
shift of `h` in its second variable followed by `e`, and the trace, is perfect. -/
theorem IsPerfectFormsPairing.bijective_relativeCupProduct
    {A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ}
    {h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX}
    (hh : D.IsPerfectFormsPairing h)
    (e : DerivedCategory.Q.obj (D.topComplexX⟦(2 * D.n : ℤ)⟧) ⟶
      (Stacks.Duality.relativeDualizingComplex D.f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj) [IsIso e]
    (Z : DerivedCategory D.S.Modules) :
    Function.Bijective ((derivedTensorProductFunctor D.S.toRingedSpace.sheaf).pairingPrecomp
      (Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct D.f.toLRSHom.toShHom
          (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj (B⟦(2 * D.n : ℤ)⟧)) ≫
        (Stacks.Duality.derivedPushforward D.f).map (D.shiftedFormsPairing h ≫ e) ≫
        (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
          (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
          (Stacks.Duality.derivedStructureSheafInDegree D.S 0))) Z) := by
  obtain ⟨k, c, ⟨eB⟩⟩ := hh.2
  have hpc := D.isPseudoCoherent_formsComplexShift k c eB (2 * D.n : ℤ)
  have hmem := D.mem_formsComplexShift k c eB (2 * D.n : ℤ)
  refine (fun h81 => ?_) (Stacks.Duality.isIso_homEquiv_symm_relativeCupProduct_comp_trace D.f
    (DerivedCategory.Q.obj A) ⟨DerivedCategory.Q.obj (B⟦(2 * D.n : ℤ)⟧), hmem⟩ hpc
    (D.shiftedFormsPairing h ≫ e) ?hphi)
  case hphi =>
    generalize
      Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        (Stacks.SheafOfModules.ringedSite D.X.sheaf) = DX
    exact IsPerfectFormsPairing.isIso_homEquiv_symm_shiftedFormsPairing_comp D hh e DX
  revert h81
  generalize Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
    (Stacks.SheafOfModules.ringedSite D.S.sheaf) = DY
  intro h81
  exact (DY.isIso_homEquiv_symm_iff _).1 h81 Z

end ProperFlat

end AlgebraicGeometry.RelativeDualitySituation

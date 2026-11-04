module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PerfectStage
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.MonoidalMates

/-!
# The perfect stage of [Stacks, Tag 08IF] (B) is functorial in the perfect object

For a perfect object `P` of `D(𝒪_X)`, `Stacks.Cohomology.RelativeExt.perfectStageDualEquiv`
identifies `Hom(L(P), N)` with `Hom(P, Φ N)`, where `K(P) = Rf_*(P^∨ ⊗^L 𝒢)` and
`L(P) = K(P)^∨`. This file makes `K` and `L` functorial — on a morphism `p : P₁ ⟶ P₂` of perfect
objects, `K(p) = Rf_*(p^∨ ⊗ 𝒢)` and `L(p) = K(p)^∨`, the duals of morphisms being the mates for
the exact pairings of [Stacks, Tag 0FPC] — and proves that the identification is natural in `P`
for these maps:

`p ≫ u(P₂) = u(P₁) ≫ Φ(L(p))`,

`u(P)` the unit `P ⟶ Φ(L(P))`. So `L(p)` is the unique map compatible with the units, and the
transition maps of the approximating system of [Stacks, Tag 08IF] (B) are the duals of the
pushforwards of the duals of the transition maps of the approximation of `E`.

## Main definitions

* `Stacks.Cohomology.RelativeExtCanonical.dualMate`: the dual `P₂^∨ ⟶ P₁^∨` of `p : P₁ ⟶ P₂`.
* `Stacks.Cohomology.RelativeExtCanonical.stageKMap`: `K(p) : K(P₂) ⟶ K(P₁)`.
* `Stacks.Cohomology.RelativeExtCanonical.stageLMap`: `L(p) : L(P₁) ⟶ L(P₂)`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.dualHomEquiv_dualMate_comp`: the identification
  `Hom(K^∨, N) ≃ Hom(𝒪, K ⊗ N)` is natural in `K`.
* `Stacks.Cohomology.RelativeExtCanonical.perfectStageDualEquiv_stageLMap_comp`: the
  identification `Hom(L(P), N) ≃ Hom(P, Φ N)` is natural in `P`.
* `Stacks.Cohomology.RelativeExtCanonical.comp_perfectStageUnit`: `p ≫ u(P₂) = u(P₁) ≫ Φ(L(p))`.
* `Stacks.Cohomology.RelativeExtCanonical.eq_stageLMap_of_comp_perfectStageUnit`: `L(p)` is the
  unique map compatible with the units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

section Dual

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T)
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual of a morphism of perfect objects**, `p^∨ : P₂^∨ ⟶ P₁^∨`: the mate of
`p : P₁ ⟶ P₂` for the exact pairings of [Stacks, Tag 0FPC] in the monoidal structure of
[Stacks, Tag 0FPT] seated on the derived tensor product. -/
def dualMate {P₁ P₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc}
    (h₁ : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect P₁)
    (h₂ : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect P₂) (p : P₁ ⟶ P₂) :
    Stacks.SheafOfModules.derivedDual Rc P₂ ⟶ Stacks.SheafOfModules.derivedDual Rc P₁ :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  ExactPairing.mate (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P₁ h₁)
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P₂ h₂) p

/-- **`Hom(K^∨, N) ≃ Hom(𝒪, K ⊗^L N)` is natural in the perfect object `K`.** For
`k : K₂ ⟶ K₁` and `ψ : K₂^∨ ⟶ N`, the identification at `K₁` of `k^∨ ≫ ψ` is the identification
at `K₂` of `ψ`, followed by `k ⊗ N`. -/
theorem dualHomEquiv_dualMate_comp
    {K₁ K₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc}
    (h₁ : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect K₁)
    (h₂ : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect K₂) (k : K₂ ⟶ K₁)
    (Q : ObjectProperty (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc))
    (N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc) (hN : Q N)
    (ψ : Stacks.SheafOfModules.derivedDual Rc K₂ ⟶ N) :
    (dualHomEquiv Rc K₁ h₁ Q).equiv N hN (dualMate Rc h₂ h₁ k ≫ ψ) =
      (dualHomEquiv Rc K₂ h₂ Q).equiv N hN ψ ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).map k).app N := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  let := Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc K₁ h₁
  let := Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc K₂ h₂
  show tensorLeftHomEquiv (derivedUnit Rc) K₁ (Stacks.SheafOfModules.derivedDual Rc K₁) N
      ((ρ_ _).hom ≫ dualMate Rc h₂ h₁ k ≫ ψ) =
    tensorLeftHomEquiv (derivedUnit Rc) K₂ (Stacks.SheafOfModules.derivedDual Rc K₂) N
      ((ρ_ _).hom ≫ ψ) ≫ k ▷ N
  rw [← Category.assoc, ← MonoidalCategory.rightUnitor_naturality, Category.assoc]
  exact ExactPairing.tensorLeftHomEquiv_mate_whiskerRight
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc K₂ h₂)
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc K₁ h₁) k ((ρ_ _).hom ≫ ψ)

/-- **`Hom(P, F N) ≃ Hom(𝒪, F N ⊗^L P^∨)` is natural in the perfect object `P`.** For
`p : P₁ ⟶ P₂` and `x : P₂ ⟶ F N`, the identification at `P₁` of `p ≫ x` is the identification at
`P₂` of `x`, followed by `F N ⊗ p^∨`. -/
theorem rightDualHomEquiv_comp {C : Type*} [Category C]
    (F : C ⥤ Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc)
    {P₁ P₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc}
    (h₁ : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect P₁)
    (h₂ : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect P₂) (p : P₁ ⟶ P₂)
    (Q : ObjectProperty C) (N : C) (hN : Q N) (x : P₂ ⟶ F.obj N) :
    (rightDualHomEquiv Rc F P₁ h₁ Q).equiv N hN (p ≫ x) =
      (rightDualHomEquiv Rc F P₂ h₂ Q).equiv N hN x ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj (F.obj N)).map
          (dualMate Rc h₁ h₂ p) := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  let := Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P₁ h₁
  let := Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P₂ h₂
  show tensorRightHomEquiv (derivedUnit Rc) P₁ (Stacks.SheafOfModules.derivedDual Rc P₁)
      (F.obj N) ((λ_ _).hom ≫ p ≫ x) =
    tensorRightHomEquiv (derivedUnit Rc) P₂ (Stacks.SheafOfModules.derivedDual Rc P₂) (F.obj N)
      ((λ_ _).hom ≫ x) ≫ F.obj N ◁ dualMate Rc h₁ h₂ p
  rw [← Category.assoc, ← MonoidalCategory.leftUnitor_naturality, Category.assoc]
  exact ExactPairing.tensorRightHomEquiv_whiskerLeft_mate
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P₁ h₁)
    (Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P₂ h₂) p ((λ_ _).hom ≫ x)

/-- The isomorphism `(a ⊗ A) ⊗ B ≅ (B ⊗ A) ⊗ a` is natural in `B`. -/
theorem tensorRightTensorRightIso_naturality_right
    (A : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc)
    {B₁ B₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc} (m : B₂ ⟶ B₁)
    (a : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj a).obj A)).map m ≫
        (tensorRightTensorRightIso Rc A B₁).hom.app a =
      (tensorRightTensorRightIso Rc A B₂).hom.app a ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).map m).app A)).app
            a := by
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Rc
  show (a ⊗ A) ◁ m ≫ (tensorRightTensorRightIso Rc A B₁).hom.app a =
    (tensorRightTensorRightIso Rc A B₂).hom.app a ≫ (m ▷ A) ▷ a
  simp only [tensorRightTensorRightIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    tensorRightTensor_inv_app, Functor.mapIso_hom, Category.assoc]
  show (a ⊗ A) ◁ m ≫ (α_ a A B₁).hom ≫ (β_ (A ⊗ B₁) a).inv ≫ (β_ A B₁).hom ▷ a =
    (α_ a A B₂).hom ≫ (β_ (A ⊗ B₂) a).inv ≫ (β_ A B₂).hom ▷ a ≫ m ▷ A ▷ a
  rw [MonoidalCategory.associator_naturality_right_assoc,
    BraidedCategory.braiding_inv_naturality_right_assoc, ← MonoidalCategory.comp_whiskerRight,
    BraidedCategory.braiding_naturality_right, MonoidalCategory.comp_whiskerRight]

end Dual

section Stage

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
  (hG : IsBoundedFlatOver f G)
  {P₁ P₂ : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf}
  (hP₁ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P₁)
  (hP₂ : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P₂) (p : P₁ ⟶ P₂)

/-- `p^∨ ⊗ 𝒢 : P₂^∨ ⊗^L 𝒢 ⟶ P₁^∨ ⊗^L 𝒢`. -/
def stageSourceMap : stageSource (G := G) P₂ ⟶ stageSource (G := G) P₁ :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
    (dualMate X.sheaf hP₁ hP₂ p)).app (DerivedCategory.Q.obj G)

/-- **`K(p) = Rf_*(p^∨ ⊗ 𝒢) : K(P₂) ⟶ K(P₁)`.** -/
def stageKMap : stageK f (G := G) P₂ ⟶ stageK f (G := G) P₁ :=
  (derivedPushforward f).map (stageSourceMap hP₁ hP₂ p)

/-- The isomorphism `Φ(N) ⊗^L P^∨ ≅ (P^∨ ⊗^L 𝒢) ⊗^L Lf^*N` is natural in `P`. -/
theorem stageTensorIso_naturality
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
        ((pullbackTensorDerivedFunctor hG).obj N)).map (dualMate X.sheaf hP₁ hP₂ p) ≫
        (stageTensorIso f hG P₁).hom.app N =
      (stageTensorIso f hG P₂).hom.app N ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          (stageSourceMap hP₁ hP₂ p)).app ((derivedPullback f).obj N) := by
  simp only [stageTensorIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Iso.symm_hom, Category.id_comp, Category.assoc]
  have h1 := ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
    ((derivedPullbackTensorIso hG).inv.app N)).naturality (dualMate X.sheaf hP₁ hP₂ p)
  have h2 := tensorRightTensorRightIso_naturality_right X.sheaf (DerivedCategory.Q.obj G)
    (dualMate X.sheaf hP₁ hP₂ p) ((derivedPullback f).obj N)
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h1)).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h2))

variable (Q : ObjectProperty (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))))
  (hQ₁ : ∀ N, Q N → IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
    (stageSource (G := G) P₁) N))
  (hQ₂ : ∀ N, Q N → IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
    (stageSource (G := G) P₂) N))

/-- **`Hom(P, Φ N) ≃ Hom(𝒪, K(P) ⊗^L N)` is natural in `P`.** For `p : P₁ ⟶ P₂` and
`x : P₂ ⟶ Φ N`, the identification at `P₁` of `p ≫ x` is the identification at `P₂` of `x`
followed by `K(p) ⊗ N`. -/
theorem perfectStageHomEquiv_comp
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (hN : Q N)
    (x : P₂ ⟶ (pullbackTensorDerivedFunctor hG).obj N) :
    (perfectStageHomEquiv f hG P₁ hP₁ Q hQ₁).equiv N hN (p ≫ x) =
      (perfectStageHomEquiv f hG P₂ hP₂ Q hQ₂).equiv N hN x ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map
          (stageKMap f hP₁ hP₂ p)).app N := by
  simp only [perfectStageHomEquiv, ShiftedHom.NaturalHomEquiv.trans, Equiv.trans_apply]
  rw [rightDualHomEquiv_comp X.sheaf (pullbackTensorDerivedFunctor hG) hP₁ hP₂ p Q N hN x]
  simp only [ShiftedHom.NaturalHomEquiv.ofIso, ShiftedHom.NaturalHomEquiv.ofIsoSource,
    adjunctionHomEquiv, projectionFormulaHomEquiv, Equiv.coe_fn_mk, Category.assoc]
  rw [stageTensorIso_naturality f hG hP₁ hP₂ p N]
  have := hQ₁ N hN
  have := hQ₂ N hN
  have hpf' : (derivedPushforward f).map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          (stageSourceMap (G := G) hP₁ hP₂ p)).app ((derivedPullback f).obj N)) ≫
        inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
          (stageSource (G := G) P₁) N) =
      inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
          (stageSource (G := G) P₂) N) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).map
          (stageKMap f (G := G) hP₁ hP₂ p)).app N := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left f
      (stageSourceMap (G := G) hP₁ hP₂ p) N).symm
  have hadj := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
    f).homEquiv_naturality_right
      ((Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f).hom ≫
        (rightDualHomEquiv X.sheaf (pullbackTensorDerivedFunctor hG) P₂ hP₂ Q).equiv N hN x ≫
          (stageTensorIso f hG P₂).hom.app N)
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).map
          (stageSourceMap (G := G) hP₁ hP₂ p)).app ((derivedPullback f).obj N))
  simp only [Category.assoc] at hadj
  refine (congrArg (· ≫ _) hadj).trans ?_
  rw [Category.assoc]
  exact congrArg (_ ≫ ·) hpf'

variable (hK₁ : (Stacks.SheafOfModules.ringedSite Y.sheaf).IsPerfect (stageK f (G := G) P₁))
  (hK₂ : (Stacks.SheafOfModules.ringedSite Y.sheaf).IsPerfect (stageK f (G := G) P₂))

/-- **`L(p) = K(p)^∨ : L(P₁) ⟶ L(P₂)`**, the dual of `K(p) = Rf_*(p^∨ ⊗ 𝒢)`. -/
def stageLMap : stageL f (G := G) P₁ ⟶ stageL f (G := G) P₂ :=
  dualMate Y.sheaf hK₂ hK₁ (stageKMap f hP₁ hP₂ p)

/-- **`Hom(L(P), N) ≃ Hom(P, Φ N)` is natural in `P`.** For `p : P₁ ⟶ P₂` and
`ψ : L(P₂) ⟶ N`, the identification at `P₁` of `L(p) ≫ ψ` is `p` followed by the identification
at `P₂` of `ψ`. -/
theorem perfectStageDualEquiv_stageLMap_comp
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (hN : Q N)
    (ψ : stageL f (G := G) P₂ ⟶ N) :
    (perfectStageDualEquiv f hG P₁ hP₁ Q hQ₁ hK₁).equiv N hN (stageLMap f hP₁ hP₂ p hK₁ hK₂ ≫ ψ) =
      p ≫ (perfectStageDualEquiv f hG P₂ hP₂ Q hQ₂ hK₂).equiv N hN ψ := by
  show ((perfectStageHomEquiv f hG P₁ hP₁ Q hQ₁).equiv N hN).symm
      ((dualHomEquiv Y.sheaf (stageK f (G := G) P₁) hK₁ Q).equiv N hN
        (stageLMap f hP₁ hP₂ p hK₁ hK₂ ≫ ψ)) =
    p ≫ ((perfectStageHomEquiv f hG P₂ hP₂ Q hQ₂).equiv N hN).symm
      ((dualHomEquiv Y.sheaf (stageK f (G := G) P₂) hK₂ Q).equiv N hN ψ)
  rw [Equiv.symm_apply_eq, perfectStageHomEquiv_comp f hG hP₁ hP₂ p Q hQ₁ hQ₂ N hN,
    Equiv.apply_symm_apply]
  exact dualHomEquiv_dualMate_comp Y.sheaf hK₁ hK₂ (stageKMap f hP₁ hP₂ p) Q N hN ψ

/-- **The units of the perfect stage are natural in `P`**:
`p ≫ u(P₂) = u(P₁) ≫ Φ(L(p))`, `u(P) : P ⟶ Φ(L(P))` the unit of
`Stacks.Cohomology.RelativeExt.perfectStageUnit`. -/
theorem comp_perfectStageUnit (hL₁ : Q (stageL f (G := G) P₁)) (hL₂ : Q (stageL f (G := G) P₂)) :
    p ≫ perfectStageUnit f hG P₂ hP₂ Q hQ₂ hK₂ hL₂ =
      perfectStageUnit f hG P₁ hP₁ Q hQ₁ hK₁ hL₁ ≫
        (pullbackTensorDerivedFunctor hG).map (stageLMap f hP₁ hP₂ p hK₁ hK₂) := by
  rw [← perfectStageDualEquiv_apply f hG P₁ hP₁ Q hQ₁ hK₁ hL₁ hL₂,
    ← Category.comp_id (stageLMap f hP₁ hP₂ p hK₁ hK₂),
    perfectStageDualEquiv_stageLMap_comp f hG hP₁ hP₂ p Q hQ₁ hQ₂ hK₁ hK₂]
  rfl

/-- **`L(p)` is the unique map compatible with the units**: any `l : L(P₁) ⟶ L(P₂)` with
`p ≫ u(P₂) = u(P₁) ≫ Φ(l)` is `L(p)`. -/
theorem eq_stageLMap_of_comp_perfectStageUnit (hL₁ : Q (stageL f (G := G) P₁))
    (hL₂ : Q (stageL f (G := G) P₂)) (l : stageL f (G := G) P₁ ⟶ stageL f (G := G) P₂)
    (hl : p ≫ perfectStageUnit f hG P₂ hP₂ Q hQ₂ hK₂ hL₂ =
      perfectStageUnit f hG P₁ hP₁ Q hQ₁ hK₁ hL₁ ≫ (pullbackTensorDerivedFunctor hG).map l) :
    l = stageLMap f hP₁ hP₂ p hK₁ hK₂ := by
  apply ((perfectStageDualEquiv f hG P₁ hP₁ Q hQ₁ hK₁).equiv _ hL₂).injective
  rw [perfectStageDualEquiv_apply f hG P₁ hP₁ Q hQ₁ hK₁ hL₁ hL₂,
    perfectStageDualEquiv_apply f hG P₁ hP₁ Q hQ₁ hK₁ hL₁ hL₂, ← hl,
    comp_perfectStageUnit f hG hP₁ hP₂ p Q hQ₁ hQ₂ hK₁ hK₂ hL₁ hL₂]

end Stage

end Stacks.Cohomology.RelativeExtCanonical

end

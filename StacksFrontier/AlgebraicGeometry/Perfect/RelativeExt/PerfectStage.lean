module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.FlatPullbackTensorDerived
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.ShiftedHomTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedPullbackOfADual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormula

/-!
# Morphisms out of a perfect object into `Φ(N)`

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes, `𝒢` a bounded
complex of `𝒪_X`-modules flat over `S`, and `Φ = pullbackTensorDerivedFunctor : D(𝒪_S) ⥤ D(𝒪_X)`,
`N ↦ Lf^*N ⊗^L 𝒢`. For a perfect object `P` of `D(𝒪_X)` put
`K(P) = Rf_*(P^∨ ⊗^L 𝒢)`, with `P^∨` the derived dual. This file constructs, for `N` in
`D_QCoh(𝒪_S)`, a bijection

`Hom(P, Φ N) ≃ Hom(𝒪_S, K(P) ⊗^L N)`

natural in `N`, and, when `K(P)` is perfect, with `L(P) = K(P)^∨`,

`Hom(L(P), N) ≃ Hom(P, Φ N)`.

The identifications are built from the exact pairings of perfect objects with their duals
(Stacks 0FPC), the projection formula (Stacks 08EU), the adjunction `Lf^* ⊣ Rf_*` and the
symmetric monoidal structure of the derived category (Stacks 0FPB).

## Main definitions

* `Stacks.Cohomology.RelativeExt.dualHomEquiv`: `Hom(K^∨, N) ≃ Hom(𝒪, K ⊗^L N)` for `K` perfect.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open RingedSpaceModuleAdjunction TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard

section Dual

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {T : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} T)
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology T).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The structure sheaf placed in degree zero, the unit of the derived tensor product. -/
abbrev derivedUnit : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc :=
  (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Rc))

/-- **`Hom(K^∨, N) ≃ Hom(𝒪, K ⊗^L N)`** for a perfect `K`, naturally in `N`: the exact pairing
of `K` with its derived dual (Stacks 0FPC). -/
def dualHomEquiv (K : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc)
    (hK : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect K)
    (Q : ObjectProperty (Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc)) :
    ShiftedHom.NaturalHomEquiv (𝟭 _)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj K)
      (Stacks.SheafOfModules.derivedDual Rc K) (derivedUnit Rc) Q :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  letI := Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc K hK
  { equiv := fun N _ =>
      { toFun := fun x => tensorLeftHomEquiv (derivedUnit Rc) K
          (Stacks.SheafOfModules.derivedDual Rc K) N ((ρ_ _).hom ≫ x)
        invFun := fun y => (ρ_ _).inv ≫ (tensorLeftHomEquiv (derivedUnit Rc) K
          (Stacks.SheafOfModules.derivedDual Rc K) N).symm y
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
    naturality := fun {N N'} _ _ g x => by
      change tensorLeftHomEquiv (derivedUnit Rc) K
          (Stacks.SheafOfModules.derivedDual Rc K) N' ((ρ_ _).hom ≫ x ≫ g) =
        tensorLeftHomEquiv (derivedUnit Rc) K
          (Stacks.SheafOfModules.derivedDual Rc K) N ((ρ_ _).hom ≫ x) ≫ K ◁ g
      rw [← Category.assoc, tensorLeftHomEquiv_naturality]
      rfl }

/-- **`Hom(P, F N) ≃ Hom(𝒪, F N ⊗^L P^∨)`** for a perfect `P` and any functor `F` into the
derived category, naturally in `N`: the exact pairing of `P` with its derived dual
(Stacks 0FPC). -/
def rightDualHomEquiv {C : Type*} [Category C]
    (F : C ⥤ Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc)
    (P : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc)
    (hP : (Stacks.SheafOfModules.ringedSite Rc).IsPerfect P) (Q : ObjectProperty C) :
    ShiftedHom.NaturalHomEquiv F
      (F ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).flip.obj
        (Stacks.SheafOfModules.derivedDual Rc P)) P (derivedUnit Rc) Q :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  letI := Stacks.SheafOfModules.exactPairingDerivedDualCanonical Rc P hP
  { equiv := fun N _ =>
      { toFun := fun x => tensorRightHomEquiv (derivedUnit Rc) P
          (Stacks.SheafOfModules.derivedDual Rc P) (F.obj N) ((λ_ _).hom ≫ x)
        invFun := fun y => (λ_ _).inv ≫ (tensorRightHomEquiv (derivedUnit Rc) P
          (Stacks.SheafOfModules.derivedDual Rc P) (F.obj N)).symm y
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
    naturality := fun {N N'} _ _ g x => by
      change tensorRightHomEquiv (derivedUnit Rc) P
          (Stacks.SheafOfModules.derivedDual Rc P) (F.obj N') ((λ_ _).hom ≫ x ≫ F.map g) =
        tensorRightHomEquiv (derivedUnit Rc) P
          (Stacks.SheafOfModules.derivedDual Rc P) (F.obj N) ((λ_ _).hom ≫ x) ≫
            F.map g ▷ Stacks.SheafOfModules.derivedDual Rc P
      rw [← Category.assoc, tensorRightHomEquiv_naturality] }

/-- **`(a ⊗^L A) ⊗^L B ≅ (B ⊗^L A) ⊗^L a`**, naturally in `a`: the associativity and the
symmetry of the derived tensor product (Stacks 0FPB). -/
def tensorRightTensorRightIso (A B : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Rc) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).flip.obj A ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).flip.obj B ≅
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Rc).obj B).obj A) :=
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Rc
  letI := Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric Rc
  (tensorRightTensor A B).symm ≪≫ (BraidedCategory.tensorLeftIsoTensorRight (A ⊗ B)).symm ≪≫
    (tensoringLeft _).mapIso (β_ A B)

end Dual

section Pushforward

attribute [local implicit_reducible] structureSheafRing TopCat.Sheaf TopCat.Presheaf.IsSheaf
  Stacks.SheafOfModules.Tensor.ringSheaf AlgebraicGeometry.SheafedSpace.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`Hom(Lf^*A, F N) ≃ Hom(A, Rf_* F N)`**, naturally in `N`: the adjunction `Lf^* ⊣ Rf_*`. -/
def adjunctionHomEquiv {C : Type*} [Category C]
    (F : C ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (Q : ObjectProperty C) :
    ShiftedHom.NaturalHomEquiv F (F ⋙ derivedPushforward f) ((derivedPullback f).obj A) A Q where
  equiv N _ := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f).homEquiv
    A (F.obj N)
  naturality _ _ g x :=
    Adjunction.homEquiv_naturality_right
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction f) x (F.map g)

/-- **`Hom(A, Rf_*(E ⊗^L Lf^*N)) ≃ Hom(A, Rf_*E ⊗^L N)`**, naturally in `N`, on a class of `N`
at which the projection-formula morphism of Stacks 0B53 is invertible. -/
def projectionFormulaHomEquiv (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (Q : ObjectProperty (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))))
    (hQ : ∀ N, Q N →
      IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E N)) :
    ShiftedHom.NaturalHomEquiv
      ((derivedPullback f ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.sheaf).obj E) ⋙ derivedPushforward f)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        ((derivedPushforward f).obj E)) A A Q where
  equiv N hN :=
    haveI := hQ N hN
    { toFun := fun x => x ≫ inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        f E N)
      invFun := fun y => y ≫ Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E N
      left_inv := fun x => by
        change (x ≫ inv _) ≫ _ = x
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      right_inv := fun y => by
        change (y ≫ _) ≫ inv _ = y
        rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id] }
  naturality {N N'} hN hN' g x := by
    have := hQ N hN
    have := hQ N' hN'
    have h := Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right f E g
    change (x ≫ (derivedPushforward f).map
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E).map
          ((derivedPullback f).map g))) ≫
          inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E N') =
      (x ≫ inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E N)) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
          ((derivedPushforward f).obj E)).map g
    have h' : inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E N) ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
          ((derivedPushforward f).obj E)).map g =
      (derivedPushforward f).map (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.sheaf).obj E).map ((derivedPullback f).map g)) ≫
          inv (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f E N') := by
      rw [IsIso.eq_comp_inv, Category.assoc, h, IsIso.inv_hom_id_assoc]
    exact (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) h'.symm).trans
      (Category.assoc _ _ _).symm)

end Pushforward

/-! ### The identification at a perfect object -/

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
  (P : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.sheaf)
  (hP : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPerfect P)

/-- The object `P^∨ ⊗^L 𝒢` of `D(𝒪_X)`. -/
abbrev stageSource : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj
    (Stacks.SheafOfModules.derivedDual X.sheaf P)).obj (DerivedCategory.Q.obj G)

/-- **The object `K(P) = Rf_*(P^∨ ⊗^L 𝒢)` of `D(𝒪_Y)`.** -/
abbrev stageK : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (derivedPushforward f).obj (stageSource (G := G) P)

/-- `Φ(N) ⊗^L P^∨ ≅ (P^∨ ⊗^L 𝒢) ⊗^L Lf^*N`, naturally in `N`. -/
def stageTensorIso :
    pullbackTensorDerivedFunctor hG ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
          (Stacks.SheafOfModules.derivedDual X.sheaf P) ≅
      derivedPullback f ⋙ (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        X.sheaf).obj (stageSource (G := G) P) :=
  Functor.isoWhiskerRight (derivedPullbackTensorIso hG).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (derivedPullback f)
      (tensorRightTensorRightIso X.sheaf (DerivedCategory.Q.obj G)
        (Stacks.SheafOfModules.derivedDual X.sheaf P))

variable (Q : ObjectProperty (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))))
  (hQ : ∀ N, Q N → IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f
    (stageSource (G := G) P) N))

/-- **`Hom(P, Φ N) ≃ Hom(𝒪_Y, K(P) ⊗^L N)`**, naturally in `N` in a class at which the
projection-formula morphism for `P^∨ ⊗^L 𝒢` is invertible. -/
def perfectStageHomEquiv :
    ShiftedHom.NaturalHomEquiv (pullbackTensorDerivedFunctor hG)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj
        (stageK f (G := G) P)) P (derivedUnit Y.sheaf) Q :=
  (rightDualHomEquiv X.sheaf (pullbackTensorDerivedFunctor hG) P hP Q).trans
    ((ShiftedHom.NaturalHomEquiv.ofIso (stageTensorIso f hG P)).trans
      ((ShiftedHom.NaturalHomEquiv.ofIsoSource
          (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f)).trans
        ((adjunctionHomEquiv f _ _ Q).trans
          (projectionFormulaHomEquiv f (stageSource (G := G) P) _ Q hQ))))

/-- **`L(P) = K(P)^∨`**, the derived dual of `K(P) = Rf_*(P^∨ ⊗^L 𝒢)`. -/
abbrev stageL : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  Stacks.SheafOfModules.derivedDual Y.sheaf (stageK f (G := G) P)

variable (hK : (Stacks.SheafOfModules.ringedSite Y.sheaf).IsPerfect (stageK f (G := G) P))

/-- **`Hom(L(P), N) ≃ Hom(P, Φ N)`**, naturally in `N`, for `K(P)` perfect. -/
def perfectStageDualEquiv :
    ShiftedHom.NaturalHomEquiv (𝟭 _) (pullbackTensorDerivedFunctor hG) (stageL f (G := G) P) P Q :=
  (dualHomEquiv Y.sheaf (stageK f (G := G) P) hK Q).trans
    (perfectStageHomEquiv f hG P hP Q hQ).symm

/-- **The unit `P ⟶ Φ(L(P))`**: the image of the identity of `L(P)`. -/
def perfectStageUnit (hL : Q (stageL f (G := G) P)) :
    P ⟶ (pullbackTensorDerivedFunctor hG).obj (stageL f (G := G) P) :=
  (perfectStageDualEquiv f hG P hP Q hQ hK).equiv _ hL (𝟙 _)

/-- **The identification at `P` is composition with the unit**: `ψ ↦ u ≫ Φ(ψ)`. -/
theorem perfectStageDualEquiv_apply (hL : Q (stageL f (G := G) P))
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (hN : Q N)
    (ψ : stageL f (G := G) P ⟶ N) :
    (perfectStageDualEquiv f hG P hP Q hQ hK).equiv N hN ψ =
      perfectStageUnit f hG P hP Q hQ hK hL ≫ (pullbackTensorDerivedFunctor hG).map ψ := by
  have h := (perfectStageDualEquiv f hG P hP Q hQ hK).naturality hL hN ψ (𝟙 _)
  rw [Category.id_comp] at h
  exact h

end Stage

end Stacks.Cohomology.RelativeExt

end

module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.UnderivedComparison
public import StacksFrontier.AlgebraicGeometry.DerivedIso.Leray
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardLeray
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal

/-!
# Base change for the derived direct image of a module flat over the base

The derived base change map at a complex is invertible as soon as the complex admits a
quasi-isomorphism to a complex on which the derived pullbacks and pushforwards are computed
termwise and the underived base change map is termwise invertible. This is the bookkeeping used
to compute base change for the direct image of a module flat over the base through its Čech
resolution.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace Stacks.AlgebraicGeometry.FlatSourceBaseChange

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard

section Abstract

/-- **Transport of invertibility of a composite of two natural families along a morphism**
which both relevant functors invert. Stated for abstract functors and families, with the two
naturality squares as hypotheses, so that its instances are a single application. -/
theorem isIso_comp_of_isIso_map {K D₁ D₂ D₃ D₄ : Type*} [Category* K] [Category* D₁]
    [Category* D₂] [Category* D₃] [Category* D₄] {Q : K ⥤ D₁} {A₁ : D₁ ⥤ D₄} {A₂ : D₄ ⥤ D₃}
    {B : D₁ ⥤ D₂} {C : D₂ ⥤ D₃} {P : K ⥤ D₂}
    (a : ∀ Z, A₂.obj (A₁.obj Z) ⟶ C.obj (B.obj Z)) (c : ∀ Y, B.obj (Q.obj Y) ⟶ P.obj Y)
    {X Y : K} (ε : X ⟶ Y)
    (ha : A₂.map (A₁.map (Q.map ε)) ≫ a (Q.obj Y) = a (Q.obj X) ≫ C.map (B.map (Q.map ε)))
    (hc : B.map (Q.map ε) ≫ c Y = c X ≫ P.map ε)
    [IsIso (Q.map ε)] [IsIso (P.map ε)]
    (hY : IsIso (a (Q.obj Y) ≫ C.map (c Y))) :
    IsIso (a (Q.obj X) ≫ C.map (c X)) := by
  have e : (a (Q.obj X) ≫ C.map (c X)) ≫ C.map (P.map ε) =
      A₂.map (A₁.map (Q.map ε)) ≫ (a (Q.obj Y) ≫ C.map (c Y)) := by
    rw [Category.assoc, ← C.map_comp, ← hc, C.map_comp, ← Category.assoc, ← ha, Category.assoc]
  have : IsIso ((a (Q.obj X) ≫ C.map (c X)) ≫ C.map (P.map ε)) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (C.map (P.map ε))

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The base change map at a complex `W` for which every derived functor in sight is computed
termwise** is invertible: this is the comparison of the derived and the underived base change
maps, `derivedBaseChangeMap_Qh_comparison`, read as an equivalence of invertibility. -/
theorem isIso_derivedBaseChangeMap_comp_of_termwise
    (W : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (h₁ : IsIso ((derivedPushforwardUnit f).app W))
    (h₂ : IsIso ((derivedPullbackComparison g).app
      (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj W)))
    (h₃ : IsIso ((underivedBaseChangeSquare g' f' f g sq).app W))
    (h₄ : IsIso ((derivedPushforwardUnit f').app
      (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj W))) :
    IsIso (derivedBaseChangeMap g' f' f g sq (DerivedCategory.Qh.obj W) ≫
        (derivedPushforward f').map ((derivedPullbackComparison g').app W)) := by
  have key := derivedBaseChangeMap_Qh_comparison g' f' f g sq W
  have : IsIso ((derivedPullback g).map ((derivedPushforwardUnit f).app W) ≫
      derivedBaseChangeMap g' f' f g sq (DerivedCategory.Qh.obj W) ≫
        (derivedPushforward f').map ((derivedPullbackComparison g').app W)) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left ((derivedPullback g).map ((derivedPushforwardUnit f).app W)) _

/-- A quasi-isomorphism of complexes becomes invertible in the derived category. -/
private theorem isIso_Qh_map_quotient_map {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {K W : CochainComplex C ℤ} (ε : K ⟶ W) [QuasiIso ε] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ε)) :=
  Localization.inverts DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff ε).2
      ((HomologicalComplex.mem_quasiIso_iff ε).2 inferInstance))

/-- **Transport of the invertibility of the base change map along a quasi-isomorphism.** Let
`ε : K ⟶ W` be a quasi-isomorphism of complexes of `𝒪_X`-modules such that `(g')^*ε` is a
quasi-isomorphism. If the base change map at `W`, followed by `Rf'_*` of the comparison
`L(g')^*W ⟶ (g')^*W`, is invertible, then so is the same composite at `K`. -/
theorem isIso_derivedBaseChangeMap_comp_of_quasiIso
    {K W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (ε : K ⟶ W)
    [QuasiIso ε]
    (h₅ : QuasiIso (((modulePullback g').mapHomologicalComplex (ComplexShape.up ℤ)).map ε))
    (hW : IsIso (derivedBaseChangeMap g' f' f g sq
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W)) ≫
      (derivedPushforward f').map ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W)))) :
    IsIso (derivedBaseChangeMap g' f' f g sq
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
      (derivedPushforward f').map ((derivedPullbackComparison g').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := by
  have hε := isIso_Qh_map_quotient_map ε
  have hε' : IsIso ((pullbackOnHomotopy g').map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ε)) :=
    isIso_Qh_map_quotient_map (((modulePullback g').mapHomologicalComplex _).map ε)
  exact isIso_comp_of_isIso_map (Q := DerivedCategory.Qh) (A₁ := derivedPushforward f)
    (A₂ := derivedPullback g) (B := derivedPullback g') (C := derivedPushforward f')
    (P := pullbackOnHomotopy g') (derivedBaseChangeMap g' f' f g sq)
    (fun Y => (derivedPullbackComparison g').app Y)
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ε)
    (derivedBaseChangeMap_naturality g' f' f g sq _)
    ((derivedPullbackComparison g').naturality _) hW

/-- **The pullback of a quasi-isomorphism between complexes on which the derived pullback is
computed termwise is a quasi-isomorphism.** -/
theorem quasiIso_map_modulePullback_of_isIso_comparison
    {K W : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (ε : K ⟶ W)
    [QuasiIso ε]
    (hK : IsIso ((derivedPullbackComparison g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)))
    (hW : IsIso ((derivedPullbackComparison g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj W))) :
    QuasiIso (((modulePullback g').mapHomologicalComplex (ComplexShape.up ℤ)).map ε) := by
  have hε := isIso_Qh_map_quotient_map ε
  have nat := (derivedPullbackComparison g').naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ε)
  have h : IsIso ((pullbackOnHomotopy g').map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ε)) := by
    have : IsIso ((derivedPullbackComparison g').app _ ≫ (pullbackOnHomotopy g').map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map ε)) := by
      rw [← nat, Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_comp_left ((derivedPullbackComparison g').app _) _
  have h' : IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      (((modulePullback g').mapHomologicalComplex (ComplexShape.up ℤ)).map ε)) := h
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
    ((NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) _).1 h')

end Abstract

end

end Stacks.AlgebraicGeometry.FlatSourceBaseChange

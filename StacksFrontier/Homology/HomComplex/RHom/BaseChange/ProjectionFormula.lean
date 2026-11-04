module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.DerivedInternalHom
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.HomComplex.Currying
public import StacksFrontier.Homology.HomComplex.DerivedTensorHom
public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.KFlatRepresentative
public import StacksFrontier.Homology.TensorComplex.TensorUnitIso
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap

/-!
# Unit comparisons and the projection formula for scalar extension

Comparisons of unit-induced maps under change of left adjoint, and the projection formula
identifying extension followed by restriction of scalars along `f : R → A` with tensoring with
the target ring, on complexes, in the derived category, and on K-flat resolutions. These are
private lemmas for the invertibility of the derived-Hom base-change map.
-/

open StacksDraft.DerivedHom.Construction (KInjectiveObjects Q_map_surjective_of_isKInjective
    postcomp_bijective postcomp_quasiIso_of_homotopyEquivalence precomp_bijective
    precomp_quasiIso_of_homotopyEquivalence)

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex CochainComplex.HomComplex StacksDraft.DerivedHom

namespace Stacks.DerivedHom.BaseChangeIso

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

open scoped TensorProduct ChangeOfRings

open DiagonalModel

section AdjunctionComparison
set_option backward.isDefEq.respectTransparency false

/-- Changing the left adjoint conjugates the unit-induced comparison
by the canonical isomorphism of left adjoints. -/
private lemma unitComparison_leftAdjointUniq
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U) (b : F' ⊣ U)
    (H : C ⥤ C) (J : D ⥤ D) (e : U ⋙ H ⟶ J ⋙ U) (X : C) :
    (a.leftAdjointUniq b).hom.app (H.obj X) ≫
      (b.homEquiv _ _).symm (H.map (b.unit.app X) ≫ e.app (F'.obj X)) =
    (a.homEquiv _ _).symm (H.map (a.unit.app X) ≫ e.app (F.obj X)) ≫
      J.map ((a.leftAdjointUniq b).hom.app X) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, U.map_comp, ← Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app]
  show b.homEquiv _ _ ((b.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply, a.homEquiv_naturality_right]
  simp only [Functor.id_obj, Equiv.apply_symm_apply]
  rw [
    ← a.unit_leftAdjointUniq_hom_app b X, H.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (H.map (a.unit.app X) ≫ ·)
    (e.naturality ((a.leftAdjointUniq b).hom.app X))

/-- The restricted unit-induced comparison factors through a strength `δ` whenever the
comparison `e` is linear for the action given by a projection isomorphism. -/
private lemma restrict_unitComparison_eq
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U)
    (H : C ⥤ C) (J : D ⥤ D) (e : U ⋙ H ⟶ J ⋙ U)
    (G : C ⥤ C) (proj : F ⋙ U ≅ G) (δ : H ⋙ G ⟶ G ⋙ H) (M : C)
    (hlin : G.map (e.app (F.obj M)) ≫ proj.inv.app (U.obj (J.obj (F.obj M))) ≫
        U.map (a.counit.app (J.obj (F.obj M))) =
      δ.app (U.obj (F.obj M)) ≫
        H.map (proj.inv.app (U.obj (F.obj M)) ≫ U.map (a.counit.app (F.obj M))) ≫
          e.app (F.obj M)) :
    U.map ((a.homEquiv _ _).symm (H.map (a.unit.app M) ≫ e.app (F.obj M))) =
      proj.hom.app (H.obj M) ≫ δ.app M ≫ H.map (proj.inv.app M) ≫ e.app (F.obj M) := by
  have hF (X Y : C) (g : X ⟶ Y) :
      U.map (F.map g) = proj.hom.app X ≫ G.map g ≫ proj.inv.app Y := by
    have := proj.hom.naturality g
    dsimp at this
    rw [← reassoc_of% this]; simp
  have h3 := δ.naturality (a.unit.app M)
  have h4 := proj.inv.naturality (a.unit.app M)
  dsimp at h3 h4
  have key : G.map (a.unit.app M) ≫ proj.inv.app (U.obj (F.obj M)) ≫
      U.map (a.counit.app (F.obj M)) = proj.inv.app M := by
    rw [reassoc_of% h4, ← U.map_comp, a.left_triangle_components, U.map_id,
      Category.comp_id]
  rw [Adjunction.homEquiv_counit, U.map_comp, F.map_comp, U.map_comp, hF, hF]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [hlin, reassoc_of% h3]
  congr 1; congr 1
  rw [← H.map_comp_assoc, ← key]

/-- The linearity condition of `restrict_unitComparison_eq` transports along isomorphisms,
so it suffices to check it on a chosen representative. -/
private lemma unitComparison_linear_of_iso
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U)
    (H : C ⥤ C) (J : D ⥤ D) (e : U ⋙ H ⟶ J ⋙ U)
    (G : C ⥤ C) (proj : F ⋙ U ≅ G) (δ : H ⋙ G ⟶ G ⋙ H) {Y Y' : D} (i : Y ≅ Y')
    (hlin : G.map (e.app Y) ≫ proj.inv.app (U.obj (J.obj Y)) ≫
        U.map (a.counit.app (J.obj Y)) =
      δ.app (U.obj Y) ≫ H.map (proj.inv.app (U.obj Y) ≫ U.map (a.counit.app Y)) ≫
        e.app Y) :
    G.map (e.app Y') ≫ proj.inv.app (U.obj (J.obj Y')) ≫
        U.map (a.counit.app (J.obj Y')) =
      δ.app (U.obj Y') ≫ H.map (proj.inv.app (U.obj Y') ≫ U.map (a.counit.app Y')) ≫
        e.app Y' := by
  have key : G.map (H.map (U.map i.hom)) ≫ G.map (e.app Y') ≫ proj.inv.app (U.obj (J.obj Y')) ≫
        U.map (a.counit.app (J.obj Y')) =
      G.map (H.map (U.map i.hom)) ≫ δ.app (U.obj Y') ≫
        H.map (proj.inv.app (U.obj Y') ≫ U.map (a.counit.app Y')) ≫ e.app Y' := by
    have he := e.naturality i.hom
    have hp := proj.inv.naturality (U.map (J.map i.hom))
    have hc := a.counit.naturality (J.map i.hom)
    have hd := δ.naturality (U.map i.hom)
    have hp' := proj.inv.naturality (U.map i.hom)
    have hc' := a.counit.naturality i.hom
    dsimp at he hp hc hd hp' hc' ⊢
    rw [← G.map_comp_assoc, he, G.map_comp_assoc, reassoc_of% hp, ← U.map_comp, hc,
      U.map_comp, reassoc_of% hlin, reassoc_of% hd]
    rw [← H.map_comp_assoc, reassoc_of% hp', ← U.map_comp, hc', U.map_comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [he]
  have : IsIso (G.map (H.map (U.map i.hom))) := inferInstance
  exact (cancel_epi _).1 key

/-- Unit-induced comparisons correspond under functors `E`, `S` intertwining the adjunctions
(through `τ` and `φ`), the endofunctors (through `lH` and `lJ`), and the comparisons `e`, `e'`. -/
private lemma unitComparison_transport
    {C₁ D₁ C₂ D₂ : Type*} [Category* C₁] [Category* D₁] [Category* C₂] [Category* D₂]
    {F : C₁ ⥤ D₁} {U : D₁ ⥤ C₁} (a : F ⊣ U) {B : C₂ ⥤ D₂} {V : D₂ ⥤ C₂} (a' : B ⊣ V)
    (E : C₁ ⥤ C₂) (S : D₁ ⥤ D₂) (H : C₁ ⥤ C₁) (J : D₁ ⥤ D₁) (H' : C₂ ⥤ C₂) (J' : D₂ ⥤ D₂)
    (e : U ⋙ H ⟶ J ⋙ U) (e' : V ⋙ H' ⟶ J' ⋙ V)
    (τ : U ⋙ E ⟶ S ⋙ V) (lH : H ⋙ E ⟶ E ⋙ H') (lJ : J ⋙ S ⟶ S ⋙ J')
    (φ : F ⋙ S ⟶ E ⋙ B) [IsIso φ] (X : C₁)
    (hφ : ∀ X, E.map (a.unit.app X) ≫ τ.app (F.obj X) ≫ V.map (φ.app X) = a'.unit.app (E.obj X))
    (he : ∀ Y, E.map (e.app Y) ≫ τ.app (J.obj Y) ≫ V.map (lJ.app Y) =
      lH.app (U.obj Y) ≫ H'.map (τ.app Y) ≫ e'.app (S.obj Y)) :
    B.map (lH.app X) ≫
        (a'.homEquiv _ _).symm (H'.map (a'.unit.app (E.obj X)) ≫ e'.app (B.obj (E.obj X))) =
      inv (φ.app (H.obj X)) ≫ S.map ((a.homEquiv _ _).symm (H.map (a.unit.app X) ≫ e.app (F.obj X)))
        ≫
        lJ.app (F.obj X) ≫ J'.map (φ.app X) := by
  apply (a'.homEquiv _ _).injective
  rw [a'.homEquiv_naturality_left, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have h1 := τ.naturality ((a.homEquiv _ _).symm (H.map (a.unit.app X) ≫ e.app (F.obj X)))
  have h2 := e'.naturality (φ.app X)
  have h3 := lH.naturality (a.unit.app X)
  dsimp at h1 h2 h3 ⊢
  rw [← hφ (H.obj X)]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  have h0 : a.unit.app (H.obj X) ≫
      U.map ((a.homEquiv _ _).symm (H.map (a.unit.app X) ≫ e.app (F.obj X))) =
      H.map (a.unit.app X) ≫ e.app (F.obj X) := by
    have := (a.homEquiv _ _).apply_symm_apply (H.map (a.unit.app X) ≫ e.app (F.obj X))
    rw [Adjunction.homEquiv_unit] at this
    exact this
  rw [← reassoc_of% h1, ← E.map_comp_assoc, h0,
    E.map_comp_assoc, reassoc_of% (he (F.obj X)), reassoc_of% h3, ← h2,
    ← H'.map_comp_assoc, ← H'.map_comp_assoc, Category.assoc, hφ X]

/-- The comparison of left adjoints transports their units across scalar equivalences. -/
private lemma unitComparison_scalar_unit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (E : C ≌ C') (S : D ≌ D')
    {F : C ⥤ D} {U : D ⥤ C} {B : C' ⥤ D'} {V : D' ⥤ C'}
    (a : F ⊣ U) (b : B ⊣ V) (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (X : C) :
    let τ := Iso.compInverseIso (H := E.symm)
      ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
        (Functor.associator _ _ _).symm)
    let φ := (E.toAdjunction.comp b).leftAdjointUniq
      ((a.comp S.toAdjunction).ofNatIsoRight δ)
    E.functor.map (a.unit.app X) ≫ τ.hom.app (F.obj X) ≫ V.map (φ.inv.app X) =
      b.unit.app (E.functor.obj X) := by
  dsimp only
  have h := ((a.comp S.toAdjunction).ofNatIsoRight δ).unit_leftAdjointUniq_hom_app
      (E.toAdjunction.comp b) X
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, Category.assoc] at h
  have h' := congrArg (fun z => E.functor.map z ≫
      E.counitIso.hom.app (V.obj (B.obj (E.functor.obj X)))) h
  simp only [Functor.map_comp, Category.assoc] at h'
  simp only [Iso.compInverseIso, Iso.inverseCompIso, Iso.trans_hom, Iso.symm_hom,
    Iso.symm_inv, Iso.trans_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app,
    NatTrans.comp_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  show E.functor.map (a.unit.app X) ≫
    E.functor.map (U.map (S.unitIso.hom.app (F.obj X))) ≫
      E.functor.map (δ.hom.app (S.functor.obj (F.obj X))) ≫
        E.counitIso.hom.app (V.obj (S.functor.obj (F.obj X))) ≫ 𝟙 _ ≫
          V.map (((E.toAdjunction.comp b).leftAdjointUniq
            ((a.comp S.toAdjunction).ofNatIsoRight δ)).inv.app X) = _
  change E.functor.map (a.unit.app X) ≫
    E.functor.map (U.map (S.unitIso.hom.app (F.obj X))) ≫
      E.functor.map (δ.hom.app (S.functor.obj (F.obj X))) ≫
        E.functor.map (E.inverse.map (V.map (((E.toAdjunction.comp b).leftAdjointUniq
          ((a.comp S.toAdjunction).ofNatIsoRight δ)).inv.app X))) ≫
          E.counitIso.hom.app _ = E.functor.map (E.unitIso.hom.app X) ≫
            E.functor.map (E.inverse.map (b.unit.app _)) ≫ E.counitIso.hom.app _ at h'
  erw [E.counit_naturality, E.counit_naturality] at h'
  have ht : E.functor.map (E.unitIso.hom.app X) ≫ E.counit.app (E.functor.obj X) =
      𝟙 (E.functor.obj X) := E.functor_unit_comp X
  erw [← Category.assoc (E.functor.map (E.unitIso.hom.app X)), ht, Category.id_comp] at h'
  simpa only [Category.id_comp] using h'

/-- The restriction comparison intertwines the counits of scalar equivalences. -/
private lemma scalarRestriction_counit
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) (Y : D') :
    let τ := Iso.compInverseIso (H := E.symm)
      ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
        (Functor.associator _ _ _).symm)
    E.functor.map (δ.inv.app Y) ≫ τ.hom.app (S.inverse.obj Y) ≫
      V.map (S.counitIso.hom.app Y) = E.counitIso.hom.app (V.obj Y) := by
  dsimp only
  simp only [Iso.compInverseIso_hom_app, Iso.inverseCompIso_inv_app,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.map_comp, Category.comp_id, Category.assoc]
  show E.functor.map (δ.inv.app Y) ≫
    E.functor.map (U.map (S.unitIso.hom.app (S.inverse.obj Y))) ≫
      E.functor.map (δ.hom.app (S.functor.obj (S.inverse.obj Y))) ≫
        E.counitIso.hom.app _ ≫ V.map (S.counitIso.hom.app Y) = _
  have he := E.counitIso.hom.naturality (V.map (S.counitIso.hom.app Y))
  dsimp only [Functor.comp_map, Functor.id_map] at he
  erw [← he]
  simp only [← E.functor.map_comp_assoc]
  have hδ := δ.hom.naturality (S.counitIso.hom.app Y)
  dsimp only [Functor.comp_map] at hδ
  erw [← hδ]
  simp only [← Category.assoc, ← U.map_comp]
  rw [S.unit_inverse_comp, U.map_id]
  simp

/-- Scalar transport of a morphism is compatible with the restriction comparison. -/
private lemma scalarRestriction_map
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse) {X : C'} {Y : D'} (g : X ⟶ V.obj Y) :
    let τ := Iso.compInverseIso (H := E.symm)
      ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
        (Functor.associator _ _ _).symm)
    E.functor.map (E.inverse.map g ≫ δ.inv.app Y) ≫ τ.hom.app (S.inverse.obj Y) ≫
      V.map (S.counitIso.hom.app Y) = E.counitIso.hom.app X ≫ g := by
  dsimp only
  rw [E.functor.map_comp, Category.assoc, scalarRestriction_counit]
  exact E.counitIso.hom.naturality g

/-- The monad action transported along a projection isomorphism. -/
private def projectionAction
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {U : D ⥤ C} {G : C ⥤ C} (a : F ⊣ U) (proj : F ⋙ U ≅ G) :
    U ⋙ G ⟶ U :=
  (Functor.isoWhiskerLeft U proj.symm).hom ≫ Functor.whiskerRight a.counit U

/-- The transported action is the projection inverse followed by the counit. -/
private lemma projectionAction_app
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {U : D ⥤ C} {G : C ⥤ C} (a : F ⊣ U) (proj : F ⋙ U ≅ G) (Y : D) :
    (projectionAction a proj).app Y = proj.inv.app (U.obj Y) ≫ U.map (a.counit.app Y) := rfl

/-- A linearity square can be verified after conjugating all its objects. -/
private lemma linear_comparison_of_conjugates
    {C D : Type*} [Category* C] [Category* D]
    (U : D ⥤ C) (G H : C ⥤ C) (J : D ⥤ D)
    (act : U ⋙ G ⟶ U) (δ : H ⋙ G ⟶ G ⋙ H) (e : U ⋙ H ⟶ J ⋙ U)
    (Y : D) {I Z W : C} (cY : U.obj Y ≅ I) (cJ : U.obj (J.obj Y) ≅ Z)
    (cH : H.obj I ≅ W) (t : Z ≅ W)
    (he : e.app Y ≫ cJ.hom ≫ t.hom = H.map cY.hom ≫ cH.hom)
    (hc : G.map t.hom ≫ G.map cH.inv ≫ δ.app I ≫
      H.map (G.map cY.inv ≫ act.app Y ≫ cY.hom) ≫ cH.hom =
      G.map cJ.inv ≫ act.app (J.obj Y) ≫ cJ.hom ≫ t.hom) :
    G.map (e.app Y) ≫ act.app (J.obj Y) =
      δ.app (U.obj Y) ≫ H.map (act.app Y) ≫ e.app Y := by
  let r : Z ≅ H.obj (U.obj Y) := t ≪≫ cH.symm ≪≫ (H.mapIso cY).symm
  have hr : r.hom ≫ e.app Y = cJ.inv := by
    apply (cancel_mono (cJ.hom ≫ t.hom)).1
    simp only [Category.assoc, he, r, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
    simp only [← Category.assoc, ← H.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  apply (cancel_epi (G.map r.hom)).1
  apply (cancel_mono (cJ.hom ≫ t.hom)).1
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, hr, he]
  have hd := δ.naturality cY.inv
  dsimp only [Functor.comp_map] at hd
  simp only [r, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, G.map_comp,
    Category.assoc]
  rw [reassoc_of% hd]
  simpa only [H.map_comp, Category.assoc] using hc.symm

/-- Invertibility of the unit-induced comparison is independent of the left adjoint
chosen for the fixed right adjoint. -/
private lemma isIso_unitComparison_iff
    {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U) (b : F' ⊣ U)
    (H : C ⥤ C) (J : D ⥤ D) (e : U ⋙ H ⟶ J ⋙ U) (X : C) :
    IsIso ((a.homEquiv _ _).symm (H.map (a.unit.app X) ≫ e.app (F.obj X))) ↔
      IsIso ((b.homEquiv _ _).symm (H.map (b.unit.app X) ≫ e.app (F'.obj X))) := by
  rw [← isIso_comp_right_iff _ (J.map ((a.leftAdjointUniq b).hom.app X)),
    ← unitComparison_leftAdjointUniq a b H J e X, isIso_comp_left_iff]
  rfl

/-- A derived adjunction normalized by its unit has the localized counit, up to the two
comparison maps. -/
private lemma counit_fac_of_unit_fac
    {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂]
    [Category* D₁] [Category* D₂]
    {E : C₁ ⥤ C₂} {U : C₂ ⥤ C₁} (adj : E ⊣ U)
    {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {E' : D₁ ⥤ D₂} {U' : D₂ ⥤ D₁}
    (α : L₁ ⋙ E' ⟶ E ⋙ L₂) (β : L₂ ⋙ U' ≅ U ⋙ L₁) (a : E' ⊣ U')
    (h : ∀ X : C₁, a.unit.app (L₁.obj X) ≫ U'.map (α.app X) =
        L₁.map (adj.unit.app X) ≫ β.inv.app (E.obj X)) (Y : C₂) :
    E'.map (β.hom.app Y) ≫ α.app (U.obj Y) ≫ L₂.map (adj.counit.app Y) =
      a.counit.app (L₂.obj Y) := by
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [a.right_triangle_components]
  have hu := a.unit.naturality (β.hom.app Y)
  have hb := β.inv.naturality (adj.counit.app Y)
  dsimp at hu hb ⊢
  simp only [Functor.map_comp]
  rw [← reassoc_of% hu, reassoc_of% (h (U.obj Y)), ← hb, ← L₁.map_comp_assoc,
    adj.right_triangle_components]
  simp

end AdjunctionComparison

section ProjectionFormula

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.MonoidalCategory

universe u

open StacksDraft.TorAmplitude (tensorSingleInclusion tensorSingleInclusion_isIso)

/-- Tensoring each term is naturally isomorphic to tensoring with a single complex. -/
private noncomputable def tensorSingleIso {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) :
    ((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      TrightCochain ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  have := tensorSingleInclusion_isIso M
  refine NatIso.ofComponents (fun K => asIso (tensorSingleInclusion M K)) ?_
  intro K K' g
  ext n : 1
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  change (g.f n ▷ M) ≫ HomologicalComplex.ιMapBifunctor K' S
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) n 0 n (add_zero n) =
    HomologicalComplex.ιMapBifunctor K S (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
      (HomologicalComplex.mapBifunctorMap g (𝟙 S)
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).f n
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp
  rfl


open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- Extension followed by restriction is tensoring with the underlying target ring. -/
private def extensionRestrictionIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    ModuleCat.extendScalars f ⋙ ModuleCat.restrictScalars f ≅
      tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A)) := by
  letI := f.toAlgebra
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact LinearEquiv.toModuleIso
      (X₁ := (ModuleCat.restrictScalars f).obj ((ModuleCat.extendScalars f).obj M))
      (X₂ := (tensorLeft ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))).obj M)
      { __ := AddEquiv.refl (TensorProduct R A M)
        map_smul' := fun r x ↦ by
          change f r • x = r • x
          exact (algebraMap_smul (M := TensorProduct R A M) A r x) }
  · intro M N g
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a m
    rfl

/-- The termwise scalar-change comparison agrees with tensor totalization. -/
private def extensionRestrictionComplexIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    CochainComplex.extendScalarsLarge f ⋙ CochainComplex.restrictScalarsLarge f ≅
      tensorLeft ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) := by
  let B := (ModuleCat.restrictScalars f).obj (ModuleCat.of A A)
  let e : tensorLeft B ≅ tensorRight B := NatIso.ofComponents (fun M ↦ β_ B M) (by
    intro M N g
    simp)
  let B₀ := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj B
  letI := CochainComplex.Koszul.koszulSymmetric R
  let e' : TrightCochain B₀ ≅ tensorLeft B₀ :=
    NatIso.ofComponents (fun K ↦ β_ K B₀) (by
      intro K L g
      change (g ▷ B₀) ≫ (β_ L B₀).hom = (β_ K B₀).hom ≫ B₀ ◁ g
      exact BraidedCategory.braiding_naturality_left g B₀)
  exact Functor.mapHomologicalComplexCompIso (extensionRestrictionIso f ≪≫ e) (.up ℤ) ≪≫
    tensorSingleIso B ≪≫ e'

/-- The projection formula inserts the term in the degree-zero scalar summand. -/
private lemma extensionRestrictionComplexIso_hom_app_f
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    ((extensionRestrictionComplexIso f).hom.app K).f n =
      (extensionRestrictionIso f).hom.app (K.X n) ≫
        HomologicalComplex.ιTensorObj B K 0 n n (zero_add n) := by
  let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  let := CochainComplex.Koszul.koszulSymmetric R
  dsimp only [extensionRestrictionComplexIso, Iso.trans_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, NatIso.ofComponents_hom_app]
  rw [Functor.mapHomologicalComplexCompIso_hom_app_f]
  show ((extensionRestrictionIso f).hom.app (K.X n) ≫
      (β_ (B.X 0) (K.X n)).hom) ≫
      HomologicalComplex.ιTensorObj K B n 0 n (add_zero n) ≫ (β_ K B).hom.f n = _
  rw [Category.assoc,
    CochainComplex.Koszul.koszulSymmetric_braiding_ιTensorObj R K B n 0 n (add_zero n)]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, ← Category.assoc,
    SymmetricCategory.symmetry]
  erw [Category.comp_id]

/-- A natural isomorphism on K-flat representatives descends to the derived category. -/
private def kFlatNatIso {R : Type u} [CommRing R]
    {D : Type*} [Category* D] (F G : DerivedCategory (ModuleCat.{u} R) ⥤ D)
    (e : ((StacksDraft.DerivedHom.Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q) ⋙ F ≅
      ((StacksDraft.DerivedHom.Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q) ⋙ G) :
    F ≅ G := by
  let L := CochainComplex.DerivedTensor.kFlatHomotopyQ R
  let W := CochainComplex.DerivedTensor.kFlatHomotopyQuasiIso R
  have : L.IsLocalization W := CochainComplex.DerivedTensor.kFlatHomotopyQ_isLocalization R
  let eH : L ⋙ F ≅ L ⋙ G := NatIso.ofComponents (fun X ↦
    F.mapIso ((DerivedCategory.quotientCompQhIso _).app X.obj.as) ≪≫
      e.app ⟨X.obj.as, X.property⟩ ≪≫
      (G.mapIso ((DerivedCategory.quotientCompQhIso _).app X.obj.as)).symm) (by
    intro X Y g
    apply StacksDraft.DerivedHom.Construction.naturality_transport F G _ _ _ _ _
        (DerivedCategory.Q.map g.hom.out)
    · change DerivedCategory.Qh.map g.hom ≫
          (DerivedCategory.quotientCompQhIso _).hom.app Y.obj.as =
        (DerivedCategory.quotientCompQhIso _).hom.app X.obj.as ≫
          DerivedCategory.Q.map g.hom.out
      simpa only [Functor.comp_map, HomotopyCategory.quotient_map_out] using
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality g.hom.out
    · exact e.hom.naturality (show
        (⟨X.obj.as, X.property⟩ : (StacksDraft.DerivedHom.Model.KFlatComplexes R).FullSubcategory) ⟶
          ⟨Y.obj.as, Y.property⟩ from ⟨g.hom.out⟩))
  exact Localization.liftNatIso L W (L ⋙ F) (L ⋙ G) F G eH
/-- The descended natural isomorphism retains its specified K-flat components. -/
private theorem kFlatNatIso_hom_app {R : Type u} [CommRing R]
    {D : Type*} [Category* D] (F G : DerivedCategory (ModuleCat.{u} R) ⥤ D)
    (e : ((StacksDraft.DerivedHom.Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q) ⋙ F ≅
      ((StacksDraft.DerivedHom.Model.KFlatComplexes R).ι ⋙ DerivedCategory.Q) ⋙ G)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    (kFlatNatIso F G e).hom.app (DerivedCategory.Q.obj K) = e.hom.app ⟨K, hK⟩ := by
  let q := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app K
  apply (cancel_epi (F.map q.hom)).1
  rw [(kFlatNatIso F G e).hom.naturality]
  have := CochainComplex.DerivedTensor.kFlatHomotopyQ_isLocalization R
  dsimp only [kFlatNatIso, Localization.liftNatIso]
  erw [Localization.liftNatTrans_app (CochainComplex.DerivedTensor.kFlatHomotopyQ R)
    (CochainComplex.DerivedTensor.kFlatHomotopyQuasiIso R) _ _ F G _
    ⟨(HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj K, hK⟩]
  simp only [Localization.Lifting.iso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp, Category.comp_id,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  show F.map q.hom ≫ e.hom.app ⟨K, hK⟩ ≫ G.map q.inv ≫ G.map q.hom =
    F.map q.hom ≫ e.hom.app ⟨K, hK⟩
  erw [← G.map_comp, Iso.inv_hom_id, G.map_id, Category.comp_id]

/-- The extension counit is natural after restriction and the ordinary projection formula. -/
private lemma extensionRestrictionCounit_naturality
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    [(ModuleCat.restrictScalars.{u} f).IsRightAdjoint]
    [(ModuleCat.restrictScalars.{u} f).IsLeftAdjoint]
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ L') :
    let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    (ModuleCat.restrictScalars f).mapDerivedCategory.map (F.map (DerivedCategory.Q.map g)) ≫
      (ModuleCat.restrictScalars f).mapDerivedCategory.map (α.app L') ≫
        (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
          ((CochainComplex.extendScalarsLarge f).obj L') ≫
        DerivedCategory.Q.map ((extensionRestrictionComplexIso f).hom.app L') =
    ((ModuleCat.restrictScalars f).mapDerivedCategory.map (α.app L) ≫
        (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
          ((CochainComplex.extendScalarsLarge f).obj L) ≫
        DerivedCategory.Q.map ((extensionRestrictionComplexIso f).hom.app L)) ≫
      DerivedCategory.Q.map (𝟙 B ⊗ₘ g) := by
  dsimp only
  let U := ModuleCat.restrictScalars f
  have hα := α.naturality g
  dsimp only [Functor.comp_map] at hα
  rw [← U.mapDerivedCategory.map_comp_assoc, hα, U.mapDerivedCategory.map_comp_assoc]
  have hβ := U.mapDerivedCategoryFactors.hom.naturality ((CochainComplex.extendScalarsLarge f).map
    g)
  dsimp only [Functor.comp_map] at hβ
  rw [reassoc_of% hβ]
  have he := (extensionRestrictionComplexIso f).hom.naturality g
  dsimp only [Functor.comp_map] at he
  erw [← DerivedCategory.Q.map_comp, he, DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  rfl

/-- Restricting derived extension of scalars is tensoring with the target ring. -/
private def derivedExtensionRestrictionIso
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))] :
    letI : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint
    F ⋙ (ModuleCat.restrictScalars f).mapDerivedCategory ≅
      (Functor.curry.obj (_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor R)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) := by
  let U := ModuleCat.restrictScalars f
  let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    (U.obj (ModuleCat.of A A))
  let H := (Functor.curry.obj (_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor R)).obj
    (DerivedCategory.Q.obj B)
  let d := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R
  let G := F ⋙ U.mapDerivedCategory
  let e := extensionRestrictionComplexIso f
  apply kFlatNatIso G H
  refine NatIso.ofComponents (fun K ↦
    have : IsIso (α.app K.obj) :=
      CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat f F α K.obj
        K.property
    U.mapDerivedCategory.mapIso (asIso (α.app K.obj)) ≪≫
      U.mapDerivedCategoryFactors.app ((CochainComplex.extendScalarsLarge f).obj K.obj) ≪≫
      DerivedCategory.Q.mapIso (e.app K.obj) ≪≫
      (d.tensorIso B K.obj K.property).symm) ?_
  intro K L g
  have hα := α.naturality g.hom
  dsimp only [Functor.comp_map] at hα
  simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom]
  change U.mapDerivedCategory.map (F.map (DerivedCategory.Q.map g.hom)) ≫
      U.mapDerivedCategory.map (α.app L.obj) ≫ _ = _
  erw [reassoc_of% extensionRestrictionCounit_naturality f F α g.hom]
  simp only [Category.assoc]
  congr 1
  congr 1
  congr 1
  have ht := d.tensorIso_naturality (𝟙 B) g.hom K.property L.property
  simp only [DerivedCategory.Q.map_id] at ht
  apply (cancel_mono (d.tensorIso B L.obj L.property).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change DerivedCategory.Q.map (B ◁ g.hom) =
    (d.tensorIso B K.obj K.property).inv ≫
      d.tensor.map (𝟙 (DerivedCategory.Q.obj B), DerivedCategory.Q.map g.hom) ≫
        (d.tensorIso B L.obj L.property).hom
  rw [ht, Iso.inv_hom_id_assoc]
  simp only [MonoidalCategory.tensorHom_def, id_whiskerRight, Category.id_comp]

/-- On a K-flat representative, the projection formula is the termwise tensor comparison. -/
private theorem derivedExtensionRestrictionIso_hom_app
    {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    letI : (ModuleCat.restrictScalars.{u} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{u} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint
    let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    (derivedExtensionRestrictionIso f F α).hom.app (DerivedCategory.Q.obj K) =
      (ModuleCat.restrictScalars f).mapDerivedCategory.map (α.app K) ≫
        ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app
          ((CochainComplex.extendScalarsLarge f).obj K)).hom ≫
        DerivedCategory.Q.map ((extensionRestrictionComplexIso f).hom.app K) ≫
        ((_root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction R).tensorIso B K hK).inv
          := by
  dsimp only [derivedExtensionRestrictionIso]
  rw [kFlatNatIso_hom_app _ _ _ K hK]
  rfl

section ProjectionResolution

open _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] (f : R →+* A)

/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u, u, u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u, u, u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} f).isLeftAdjoint

/-- A K-flat resolution of the target ring computes restricted scalar extension. -/
private def extensionRestrictionResolutionIso
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (p : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) [QuasiIso p]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ModuleCat.restrictScalars f).mapDerivedCategory.obj (F.obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj (P ⊗ L) :=
  (derivedExtensionRestrictionIso f F α).app (DerivedCategory.Q.obj L) ≪≫
    (tensor R).mapIso ((asIso (DerivedCategory.Q.map p)).symm.prod
      (Iso.refl (DerivedCategory.Q.obj L))) ≪≫ tensorLeftIso P L hP

/-- The resolution comparison is natural in the complex being extended. -/
private lemma extensionRestrictionResolutionIso_naturality
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (p : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) [QuasiIso p]
    {L L' : CochainComplex (ModuleCat.{u} R) ℤ} (g : L ⟶ L') :
    (ModuleCat.restrictScalars f).mapDerivedCategory.map (F.map (DerivedCategory.Q.map g)) ≫
        (extensionRestrictionResolutionIso f F α P hP p L').hom =
      (extensionRestrictionResolutionIso f F α P hP p L).hom ≫
        DerivedCategory.Q.map (𝟙 P ⊗ₘ g) := by
  let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  have hn := (derivedExtensionRestrictionIso f F α).hom.naturality (DerivedCategory.Q.map g)
  dsimp only [Functor.comp_map, Functor.curry_obj_obj_map] at hn
  simp only [extensionRestrictionResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.symm_hom, asIso_inv, Iso.refl_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% hn]
  congr 1
  have hc : (tensor R).map
      (show (DerivedCategory.Q.obj B, DerivedCategory.Q.obj L) ⟶
        (DerivedCategory.Q.obj B, DerivedCategory.Q.obj L') from
        (𝟙 _, DerivedCategory.Q.map g)) ≫
      (tensor R).map
        (show (DerivedCategory.Q.obj B, DerivedCategory.Q.obj L') ⟶
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L') from
          (inv (DerivedCategory.Q.map p), 𝟙 _)) =
    (tensor R).map
        (show (DerivedCategory.Q.obj B, DerivedCategory.Q.obj L) ⟶
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) from
          (inv (DerivedCategory.Q.map p), 𝟙 _)) ≫
      (tensor R).map
        (show (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L) ⟶
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj L') from
          (𝟙 _, DerivedCategory.Q.map g)) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  erw [← Category.assoc, hc, Category.assoc]
  congr 1
  have ht := tensorLeftIso_naturality (𝟙 P) g hP hP
  rw [DerivedCategory.Q.map_id P] at ht
  exact ht

/-- On K-flat complexes, the resolution comparison agrees with the extension counit. -/
private lemma extensionRestrictionResolutionIso_counit_of_kFlat
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (p : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) [QuasiIso p]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) :
    (extensionRestrictionResolutionIso f F α P hP p L).hom ≫
        DerivedCategory.Q.map (p ⊗ₘ 𝟙 L) =
      (ModuleCat.restrictScalars f).mapDerivedCategory.map (α.app L) ≫
        (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
          ((CochainComplex.extendScalarsLarge f).obj L) ≫
        DerivedCategory.Q.map ((extensionRestrictionComplexIso f).hom.app L) := by
  let B := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  have hn := (adjunction R).tensorIso_naturality p (𝟙 L) hL hL
  simp only [DerivedCategory.Q.map_id] at hn
  simp only [extensionRestrictionResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.prod_hom, Iso.symm_hom, asIso_inv, Iso.refl_hom, Iso.app_hom, Category.assoc,
    tensorLeftIso_eq P L hP hL]
  rw [← hn, ← Functor.map_comp_assoc]
  simp only [prod_comp, IsIso.inv_hom_id, Category.comp_id,
    ← CategoryTheory.prod_id]
  erw [(tensor R).map_id, Category.id_comp]
  rw [derivedExtensionRestrictionIso_hom_app f F α L hL]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.app_hom]

/-- A K-flat resolution of the target ring gives the projection formula with its counit
on every complex. -/
private lemma extensionRestrictionResolutionIso_counit
    (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat)
    (p : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) [QuasiIso p]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extensionRestrictionResolutionIso f F α P hP p L).hom ≫
        DerivedCategory.Q.map (p ⊗ₘ 𝟙 L) =
      (ModuleCat.restrictScalars f).mapDerivedCategory.map (α.app L) ≫
        (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.hom.app
          ((CochainComplex.extendScalarsLarge f).obj L) ≫
        DerivedCategory.Q.map ((extensionRestrictionComplexIso f).hom.app L) := by
  obtain ⟨N, n, hN, _, hn, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution L
  let : QuasiIso n := hn
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  apply (cancel_epi (U.map (F.map (DerivedCategory.Q.map n)))).1
  rw [extensionRestrictionCounit_naturality f F α n]
  rw [← Category.assoc, extensionRestrictionResolutionIso_naturality f F α P hP p n,
    Category.assoc, ← DerivedCategory.Q.map_comp]
  rw [show (𝟙 P ⊗ₘ n) ≫ (p ⊗ₘ 𝟙 L) =
      (p ⊗ₘ 𝟙 N) ≫ (𝟙 _ ⊗ₘ n) by simp only [tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]]
  rw [DerivedCategory.Q.map_comp, ← Category.assoc,
    extensionRestrictionResolutionIso_counit_of_kFlat f F α P hP p N hN]


end ProjectionResolution

end ProjectionFormula

end Stacks.DerivedHom.BaseChangeIso

end

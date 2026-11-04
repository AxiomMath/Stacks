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
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelCriterion
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.BaseChangeMap
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ProjectionFormula
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.HomComplexAdjunction
import all StacksFrontier.Homology.HomComplex.RHom.BaseChange.ModelCriterion

/-!
# Invertibility of the derived-Hom base-change map

The diagonal action on models, the transport of K-flatness and Tor amplitude along ring
equivalences, and the theorem `Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`
(Stacks 0A6A, 0E1V): the base-change map `RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` is
an isomorphism when `K` is perfect; when `A` is perfect as an `R`-module; when the ring map is
flat, `K` is pseudo-coherent and `M` is bounded below; or when `A` has finite Tor dimension over
`R`, `K` is pseudo-coherent and `M` is bounded below.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
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

noncomputable section
open CategoryTheory.MonoidalCategory CochainComplex CochainComplex.HomComplex
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
open _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model
variable {R : Type u} [CommRing R]
/-- `P ◁ g` corresponds, under `tensorLeftIso`, to tensoring `Q.map g` with `Q.obj P`. -/
private lemma tensorLeftIso_inv_comp_map_comp_hom
    {P X Y : CochainComplex (ModuleCat.{u} R) ℤ} (hP : P.KFlat) (g : X ⟶ Y) :
    (tensorLeftIso P X hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
        (DerivedCategory.Q.map g)) ≫ (tensorLeftIso P Y hP).hom =
      DerivedCategory.Q.map (P ◁ g) := by
  have ht : (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
        (DerivedCategory.Q.map g)) ≫ (tensorLeftIso P Y hP).hom =
      (tensorLeftIso P X hP).hom ≫ DerivedCategory.Q.map (P ◁ g) := by
    simpa using tensorLeftIso_naturality (𝟙 P) g hP hP
  rw [ht, Iso.inv_hom_id_assoc]

private lemma diagonal_action_model
    (P K I Z : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.KFlat) (hK : K.KFlat)
    [I.IsKInjective] (B : DerivedCategory (ModuleCat.{u} R))
    (p : DerivedCategory.Q.obj P ⟶ B) (t : Z ⟶ HomComplexR R K I)
    (a : (tensor R).obj (B, DerivedCategory.Q.obj I) ⟶ DerivedCategory.Q.obj I)
    (q : P ⊗ I ⟶ I)
    (hq : DerivedCategory.Q.map q = (tensorLeftIso P I hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (p) (𝟙 (DerivedCategory.Q.obj I))) ≫ a) :
    (tensorLeftIso P Z hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (p) (𝟙 (DerivedCategory.Q.obj Z))) ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 B) (DerivedCategory.Q.map t)) ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 B) ((adjunction R).homIso K I).inv) ≫
      diagonal B (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj K) ≫
      (hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (DerivedCategory.Q.obj K))) (a)) ≫
      ((adjunction R).homIso K I).hom =
    DerivedCategory.Q.map ((P ◁ t) ≫ Stacks.HomComplex.TensorHomComparison.theta P I K ≫
      Stacks.HomComplex.TensorHomMap.postcomp R K (P ⊗ I) I q) := by
  have hmove :
      (tensor R).map (CategoryTheory.Prod.mkHom (p) (𝟙 (DerivedCategory.Q.obj Z))) ≫
        (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 B) (DerivedCategory.Q.map t)) ≫
        (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 B) ((adjunction R).homIso K I).inv) =
      (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map
        t)) ≫
        (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) ((adjunction
          R).homIso K I).inv) ≫
        (tensor R).map (CategoryTheory.Prod.mkHom (p) (𝟙 ((hom R).obj (Opposite.op
          (DerivedCategory.Q.obj K), DerivedCategory.Q.obj I)))) := by
    simp only [← CategoryTheory.Functor.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  have hn := StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.1
    (L := DerivedCategory.Q.obj I) (M := DerivedCategory.Q.obj K) p
  rw [reassoc_of% hmove]
  erw [reassoc_of% hn]
  have hq' : (tensorLeftIso P I hP).hom ≫ DerivedCategory.Q.map q =
      (tensor R).map (CategoryTheory.Prod.mkHom (p) (𝟙 (DerivedCategory.Q.obj I))) ≫ a := by rw [hq,
        Iso.hom_inv_id_assoc]
  have hd := StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal_injective_model
    P I K I hP hK q
  rw [hq'] at hd
  have hm : (hom R).map (CategoryTheory.Prod.mkHom
      (𝟙 (Opposite.op (DerivedCategory.Q.obj K)))
      ((tensor R).map (CategoryTheory.Prod.mkHom p (𝟙 (DerivedCategory.Q.obj I))))) ≫
      (hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (DerivedCategory.Q.obj K))) a) =
      (hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (DerivedCategory.Q.obj K)))
        ((tensor R).map (CategoryTheory.Prod.mkHom p (𝟙 (DerivedCategory.Q.obj I))) ≫ a)) := by
    rw [← (hom R).map_comp]
    simp only [prod_comp, Category.comp_id]
  erw [reassoc_of% hm, reassoc_of% hd]
  simp only [Iso.inv_hom_id, Category.comp_id]
  have hc : (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
      ((adjunction R).homIso K I).inv) ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
        ((adjunction R).homIso K I).hom) = 𝟙 _ :=
    ((tensor R).mapIso ((Iso.refl (DerivedCategory.Q.obj P)).prod
      ((adjunction R).homIso K I))).inv_hom_id
  rw [reassoc_of% hc]
  rw [reassoc_of% tensorLeftIso_inv_comp_map_comp_hom hP t, ← DerivedCategory.Q.map_comp]
end

private lemma unitComparison_natural
    {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {U : D ⥤ C} (a : F ⊣ U)
    {H H' : C ⥤ C} {J J' : D ⥤ D}
    (e : U ⋙ H ⟶ J ⋙ U) (e' : U ⋙ H' ⟶ J' ⋙ U)
    (h : H ⟶ H') (j : J ⟶ J')
    (he : ∀ Y, h.app (U.obj Y) ≫ e'.app Y = e.app Y ≫ U.map (j.app Y)) (M : C) :
    F.map (h.app M) ≫ (a.homEquiv _ _).symm
        (H'.map (a.unit.app M) ≫ e'.app (F.obj M)) =
      (a.homEquiv _ _).symm (H.map (a.unit.app M) ≫ e.app (F.obj M)) ≫ j.app (F.obj M) := by
  simp only [Adjunction.homEquiv_counit, F.map_comp, Category.assoc]
  have hn := h.naturality (a.unit.app M)
  have hc := a.counit.naturality (j.app (F.obj M))
  dsimp only [Functor.comp_map, Functor.id_map] at hc hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [← F.map_comp_assoc, ← hn, F.map_comp_assoc]
  rw [← F.map_comp_assoc (h.app _) (e'.app _), he, F.map_comp_assoc, hc]

noncomputable section
open CategoryTheory.MonoidalCategory CochainComplex CochainComplex.HomComplex
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
open _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of scalars. -/
local instance : (ModuleCat.extendScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isLeftAdjoint
/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint
variable (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
private def modelRestrictionHomIso (K : DerivedCategory (ModuleCat.{u} R)) :
    (ModuleCat.restrictScalars f).mapDerivedCategory ⋙
        (Functor.curry.obj (hom R)).obj (Opposite.op K) ≅
      (Functor.curry.obj (hom A)).obj (Opposite.op (F.obj K)) ⋙
        (ModuleCat.restrictScalars f).mapDerivedCategory :=
  NatIso.ofComponents (fun Y => (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso f F α).app
    (Opposite.op K, Y))
    (by
      intro X Y g
      have h := (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso f F α).hom.naturality
        (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K)) g)
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map, unop_id] at h
      rw [F.map_id, op_id] at h
      exact h)

private lemma modelComparison_linear_on_injective
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective] :
    let U := (ModuleCat.restrictScalars f).mapDerivedCategory
    let B := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
    let G := (Functor.curry.obj (tensor R)).obj B
    let H := (Functor.curry.obj (hom R)).obj (Opposite.op (DerivedCategory.Q.obj K))
    let JA := (Functor.curry.obj (hom A)).obj (Opposite.op (F.obj (DerivedCategory.Q.obj K)))
    let e := modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)
    let act := projectionAction (scalarAdjunctionWithUnitComparison f F α).1
      (derivedExtensionRestrictionIso f F α)
    G.map (e.hom.app (DerivedCategory.Q.obj J)) ≫ act.app (JA.obj (DerivedCategory.Q.obj J)) =
      diagonal B (U.obj (DerivedCategory.Q.obj J)) (DerivedCategory.Q.obj K) ≫
        H.map (act.app (DerivedCategory.Q.obj J)) ≫ e.hom.app (DerivedCategory.Q.obj J) := by
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  let Uc := CochainComplex.restrictScalarsLarge f
  let β := (ModuleCat.restrictScalars f).mapDerivedCategoryFactors
  let Bc := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  let B := DerivedCategory.Q.obj Bc
  let G := (Functor.curry.obj (tensor R)).obj B
  let H := (Functor.curry.obj (hom R)).obj (Opposite.op (DerivedCategory.Q.obj K))
  let JA := (Functor.curry.obj (hom A)).obj (Opposite.op (F.obj (DerivedCategory.Q.obj K)))
  let e := modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)
  let act := projectionAction (scalarAdjunctionWithUnitComparison f F α).1
    (derivedExtensionRestrictionIso f F α)
  let δ : H ⋙ G ⟶ G ⋙ H :=
    { app L := diagonal B L (DerivedCategory.Q.obj K)
      naturality {L L'} g := StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.2.1 g }
  obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective (Uc.obj J)
  let : QuasiIso q := hq
  let : I.IsKInjective := hI
  have : IsIso (α.app K) := Stacks.DerivedHom.BaseChange.isIso_extendScalarsCounit_app_of_kFlat f F
    α K hK
  have : QuasiIso (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) :=
    Stacks.DerivedHom.BaseChange.quasiIso_homComplexChangeOfRingsMap_of_kFlat f K J I q F α hK
  let Z := HomComplexR A ((CochainComplex.extendScalarsLarge f).obj K) J
  let cY := β.app J ≪≫ asIso (DerivedCategory.Q.map q)
  let eA := Stacks.DerivedHom.BaseChange.homModelIso ((CochainComplex.extendScalarsLarge f).obj K) J
    (asIso (α.app K)) (Iso.refl _)
  let cJ := U.mapIso eA ≪≫ β.app Z
  let cH := (adjunction R).homIso K I
  let t := asIso (DerivedCategory.Q.map (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K
    J I q))
  have he : e.hom.app (DerivedCategory.Q.obj J) ≫ cJ.hom ≫ t.hom =
      H.map cY.hom ≫ cH.hom := by
    show (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso f F α).hom.app
      (Opposite.op (DerivedCategory.Q.obj K), DerivedCategory.Q.obj J) ≫ _ = _
    rw [Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_hom_app f F α K J I q hK]
    let eR := Stacks.DerivedHom.BaseChange.homModelIso K I (Iso.refl _) cY
    show (eR ≪≫ t.symm ≪≫ cJ.symm).hom ≫ cJ.hom ≫ t.hom = _
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  apply linear_comparison_of_conjugates U G H JA act δ e.hom
    (DerivedCategory.Q.obj J) cY cJ cH t he
  obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution Bc
  let : QuasiIso p := hp
  let aI := G.map cY.inv ≫ act.app (DerivedCategory.Q.obj J) ≫ cY.hom
  obtain ⟨q', hq'⟩ :=
    StacksDraft.DerivedHom.Construction.Q_map_surjective_of_isKInjective (P ⊗ I) I
    ((tensorLeftIso P I hP).inv ≫
      (tensor R).map (DerivedCategory.Q.map p, 𝟙 (DerivedCategory.Q.obj I)) ≫ aI)
  let jZ := (tensor R).mapIso ((asIso (DerivedCategory.Q.map p)).symm.prod
      (Iso.refl (DerivedCategory.Q.obj (Uc.obj Z)))) ≪≫ tensorLeftIso P (Uc.obj Z) hP
  apply (cancel_epi jZ.inv).1
  let aJ := (extensionRestrictionComplexIso f).inv.app (Uc.obj J) ≫
    Uc.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)).counit.app J)
  let aZ := (extensionRestrictionComplexIso f).inv.app (Uc.obj Z) ≫
    Uc.map (((ModuleCat.extendRestrictScalarsAdj f).mapHomologicalComplex (.up ℤ)).counit.app Z)
  have hjZ : jZ.inv = (tensorLeftIso P (Uc.obj Z) hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
        (𝟙 (DerivedCategory.Q.obj (Uc.obj Z)))) := rfl
  have hleft : jZ.inv ≫ G.map t.hom ≫ G.map cH.inv ≫ δ.app (DerivedCategory.Q.obj I) ≫
      H.map (G.map cY.inv ≫ act.app (DerivedCategory.Q.obj J) ≫ cY.hom) ≫ cH.hom =
    DerivedCategory.Q.map ((P ◁ Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) ≫
      Stacks.HomComplex.TensorHomComparison.theta P I K ≫ Stacks.HomComplex.TensorHomMap.postcomp R
        K (P ⊗ I) I q') := by
    rw [hjZ]
    simp only [Category.assoc]
    exact diagonal_action_model P K I (Uc.obj Z) hP hK B (DerivedCategory.Q.map p)
      (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) aI q' hq'
  have hcJ : G.map cJ.inv ≫ act.app (JA.obj (DerivedCategory.Q.obj J)) ≫ cJ.hom =
      G.map (β.inv.app Z) ≫ act.app (DerivedCategory.Q.obj Z) ≫ β.hom.app Z := by
    have hn := act.naturality eA.inv
    dsimp only [Functor.comp_map] at hn
    dsimp only [cJ, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom]
    rw [G.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% hn]
    rw [← U.map_comp_assoc, Iso.inv_hom_id, U.map_id]
    simp only [Category.id_comp]
    rfl
  have hright : jZ.inv ≫ G.map cJ.inv ≫ act.app (JA.obj (DerivedCategory.Q.obj J)) ≫
      cJ.hom ≫ t.hom = DerivedCategory.Q.map ((p ▷ Uc.obj Z) ≫ aZ) ≫ t.hom := by
    rw [reassoc_of% hcJ, hjZ]
    have h := projectionAction_resolution.{u,u} f F α P hP p Z
    have hh := congrArg (fun z => z ≫ t.hom) h
    simp only [Category.assoc] at hh ⊢
    exact hh
  have hq'' : DerivedCategory.Q.map ((P ◁ q) ≫ q') =
      DerivedCategory.Q.map ((p ▷ Uc.obj J) ≫ aJ ≫ q) := by
    rw [DerivedCategory.Q.map_comp, hq']
    have hn' : DerivedCategory.Q.map (P ◁ q) ≫ (tensorLeftIso P I hP).inv =
        (tensorLeftIso P (Uc.obj J) hP).inv ≫
          (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q)) := by
      rw [← tensorLeftIso_inv_comp_map_comp_hom hP q]
      simp
    rw [reassoc_of% hn']
    have hm : (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
          (DerivedCategory.Q.map q)) ≫
        (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj I))) ≫ G.map cY.inv =
      (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p)
          (𝟙 (DerivedCategory.Q.obj (Uc.obj J)))) ≫ G.map (β.inv.app J) := by
      simp only [G, Functor.curry_obj_obj_map, cY, Iso.trans_inv, asIso_inv, Iso.app_inv,
        ← CategoryTheory.Functor.map_comp, prod_comp, Category.id_comp,
        IsIso.hom_inv_id_assoc]
    show (tensorLeftIso P (Uc.obj J) hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map
        q)) ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj
        I))) ≫
      G.map cY.inv ≫ act.app (DerivedCategory.Q.obj J) ≫ cY.hom = _
    rw [reassoc_of% hm]
    show (tensorLeftIso P (Uc.obj J) hP).inv ≫
      (tensor R).map (CategoryTheory.Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj
        (Uc.obj J)))) ≫
      G.map (β.inv.app J) ≫ act.app (DerivedCategory.Q.obj J) ≫ β.hom.app J ≫
      DerivedCategory.Q.map q = _
    have h := projectionAction_resolution.{u,u} f F α P hP p J
    erw [reassoc_of% h]
    simp only [aJ, CategoryTheory.Functor.map_comp, Category.assoc]
    rfl
  rw [hleft, hright]
  show _ = _ ≫ DerivedCategory.Q.map (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K
    J I q)
  rw [← DerivedCategory.Q.map_comp]
  have h := tensor_hom_action_localized hK (homComplexScalarAdjunction f K J) aJ aZ
    (homComplexScalarAdjunction_linear f K J) p q q' hq''
  rw [← homComplexChangeOfRingsMap_postcomp] at h
  exact h
end

noncomputable section
open CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
private lemma kFlat_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : S ≃+* R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat) :
    CochainComplex.KFlat (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up
      ℤ)).obj K) := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let i := (ModuleCat.extendRestrictScalarsAdj.{u} e.symm.toRingHom).leftAdjointUniq E.toAdjunction
  let j := (NatIso.mapHomologicalComplex i (.up ℤ)).app K
  have h := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{u,u,u} e.symm.toRingHom K hK
  intro M hM
  exact HomologicalComplex.Acyclic.of_iso ((tensorLeft M).mapIso j) (h M hM)

private lemma flat_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : S ≃+* R)
    (M : ModuleCat.{u} R) [Module.Flat R M] :
    Module.Flat S ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  let := e.toRingHom.toAlgebra
  let : Module.Flat S R := RingHom.Flat.of_bijective e.bijective
  let : Module S M := Module.compHom M e.toRingHom
  let : IsScalarTower S R M := IsScalarTower.restrictScalars S R M
  exact Module.Flat.trans S R M

private lemma hasTorAmplitudeAbove_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : S ≃+* R)
    (K : DerivedCategory (ModuleCat.{u} R)) (a : ℤ)
    (h : ∀ (N : ModuleCat.{u} R) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((canonTensorMod N).obj K))) :
    ∀ (N : ModuleCat.{u} S) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((canonTensorMod N).obj
          ((ModuleCat.restrictScalars e.toRingHom).mapDerivedCategory.obj K))) := by
  obtain ⟨P, hP, hflat, hb, ⟨i⟩⟩ :=
    (StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical K
      a).1 h
  let G := ModuleCat.restrictScalars e.toRingHom
  have : G.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let := hb
  apply
    (StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative_canonical _
      a).2
  refine ⟨(G.mapHomologicalComplex (.up ℤ)).obj P,
    kFlat_restrictScalars_ringEquiv e P hP, ?_, inferInstance,
    ⟨G.mapDerivedCategory.mapIso i ≪≫ G.mapDerivedCategoryFactors.app P⟩⟩
  intro n
  let := hflat n
  exact flat_restrictScalars_ringEquiv e (P.X n)
end

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
private def ringLiftSingleIso {R : Type uR} [CommRing R]
    (B : ModuleCat.{max uR uA uM} R) :
    let e₀ := ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uA uM} R ≃+*
      R).toRingHom
    let e₁ := ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
      R).toRingHom
    let r : ULift.{max uR uA uM} R ≃+* ULift.{max uA uM} R :=
      ULift.ringEquiv.trans ULift.ringEquiv.symm
    let G := ModuleCat.restrictScalars r.toRingHom
    G.mapDerivedCategory.obj (e₀.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj B)) ≅
    e₁.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj B) := by
  dsimp only
  let e₀ := ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uA uM} R ≃+*
    R).toRingHom
  let e₁ := ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
    R).toRingHom
  let r : ULift.{max uR uA uM} R ≃+* ULift.{max uA uM} R :=
    ULift.ringEquiv.trans ULift.ringEquiv.symm
  let G := ModuleCat.restrictScalars r.toRingHom
  exact G.mapDerivedCategory.mapIso ((e₀.mapDerivedCategorySingleFunctor 0).app B) ≪≫
    (G.mapDerivedCategorySingleFunctor 0).app (e₀.obj B) ≪≫
    ((e₁.mapDerivedCategorySingleFunctor 0).app B).symm
end

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
private def modelScalarCoefficientIso {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] (f : R →+* A) :
    let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{uR,max uR uA uM} R
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    E.functor.obj ((DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max uR uM} A)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R)) 0).obj
        ((ModuleCat.restrictScalars f').obj (ModuleCat.of (ULift.{max uR uA uM} A) (ULift.{max uR uA
          uM} A))) := by
  let e := ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
    R).toRingHom
  let B := (ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max uR uM} A))
  let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let B' := (ModuleCat.restrictScalars f').obj
    (ModuleCat.of (ULift.{max uR uA uM} A) (ULift.{max uR uA uM} A))
  have i : e.obj B ≅ B' := by
    refine (show (e.obj B : Type _) ≃ₗ[ULift.{max uR uA uM} R] (B' : Type _) from ?_).toModuleIso
    exact
      { toFun x := ULift.up x.down
        invFun x := ULift.up x.down
        left_inv x := by cases x; rfl
        right_inv x := by cases x; rfl
        map_add' x y := rfl
        map_smul' r x := rfl }
  exact (e.mapDerivedCategorySingleFunctor 0).app B ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso i
end

noncomputable section
open CategoryTheory.MonoidalCategory CochainComplex
universe u
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
open _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
/-- Extension of scalars along `f` is a left adjoint, with right adjoint restriction of scalars. -/
local instance : (ModuleCat.extendScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isLeftAdjoint
/-- Restriction of scalars along `f` is a right adjoint, with left adjoint extension of scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsRightAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).isRightAdjoint
/-- Restriction of scalars along `f` is a left adjoint, with right adjoint coextension of
scalars. -/
local instance : (ModuleCat.restrictScalars.{u,u,u} f).IsLeftAdjoint :=
  (ModuleCat.restrictCoextendScalarsAdj.{u} f).isLeftAdjoint
variable (F : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} A))
    (α : DerivedCategory.Q ⋙ F ⟶ CochainComplex.extendScalarsLarge f ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ))]
private lemma isIso_modelUnitComparison_of_kFlat
    (a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    (M : DerivedCategory (ModuleCat.{u} R))
    (hd : IsIso (diagonal
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) M (DerivedCategory.Q.obj K))) :
    IsIso ((a.homEquiv _ _).symm
      ((hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (DerivedCategory.Q.obj K)))
        (a.unit.app M)) ≫ (modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)).hom.app (F.obj
          M))) := by
  let U := (ModuleCat.restrictScalars f).mapDerivedCategory
  let B := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  let G := (Functor.curry.obj (tensor R)).obj B
  let H := (Functor.curry.obj (hom R)).obj (Opposite.op (DerivedCategory.Q.obj K))
  let J := (Functor.curry.obj (hom A)).obj (Opposite.op (F.obj (DerivedCategory.Q.obj K)))
  let e := modelRestrictionHomIso f F α (DerivedCategory.Q.obj K)
  let b := (scalarAdjunctionWithUnitComparison f F α).1
  let proj := derivedExtensionRestrictionIso f F α
  let δ : H ⋙ G ⟶ G ⋙ H :=
    { app L := diagonal B L (DerivedCategory.Q.obj K)
      naturality {L L'} g := StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.2.1 g }
  show IsIso ((a.homEquiv _ _).symm (H.map (a.unit.app M) ≫ e.hom.app (F.obj M)))
  apply (isIso_unitComparison_iff a b H J e.hom M).mpr
  have hlin : G.map (e.hom.app (F.obj M)) ≫ proj.inv.app (U.obj (J.obj (F.obj M))) ≫
      U.map (b.counit.app (J.obj (F.obj M))) =
    δ.app (U.obj (F.obj M)) ≫
      H.map (proj.inv.app (U.obj (F.obj M)) ≫ U.map (b.counit.app (F.obj M))) ≫
        e.hom.app (F.obj M) := by
    let N := DerivedCategory.Q.objPreimage (F.obj M)
    obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective N
    let := hq
    let := hI
    let i : DerivedCategory.Q.obj I ≅ F.obj M :=
      (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso (F.obj M)
    exact unitComparison_linear_of_iso b H J e.hom G proj δ i
      (modelComparison_linear_on_injective f F α K hK I)
  have hh := restrict_unitComparison_eq b H J e.hom G proj δ M hlin
  have : IsIso (U.map ((b.homEquiv _ _).symm
      (H.map (b.unit.app M) ≫ e.hom.app (F.obj M)))) := by
    rw [hh]
    let : IsIso (δ.app M) := hd
    infer_instance
  exact isIso_of_mapDerivedCategory (ModuleCat.restrictScalars f) _

private lemma isIso_modelUnitComparison_iff_of_iso
    (a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory)
    {K K' : DerivedCategory (ModuleCat.{u} R)} (k : K' ≅ K)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((a.homEquiv _ _).symm
      ((hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K)) (a.unit.app M)) ≫
        (modelRestrictionHomIso f F α K).hom.app (F.obj M))) ↔
    IsIso ((a.homEquiv _ _).symm
      ((hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K')) (a.unit.app M)) ≫
        (modelRestrictionHomIso f F α K').hom.app (F.obj M))) := by
  let e := modelRestrictionHomIso f F α K
  let e' := modelRestrictionHomIso f F α K'
  let h := (Functor.curry.obj (hom R)).map k.hom.op
  let j := (Functor.curry.obj (hom A)).map (F.map k.hom).op
  have he : ∀ Y, h.app ((ModuleCat.restrictScalars f).mapDerivedCategory.obj Y) ≫ e'.hom.app Y =
      e.hom.app Y ≫ (ModuleCat.restrictScalars f).mapDerivedCategory.map (j.app Y) := by
    intro Y
    have hh := (Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso f F α).hom.naturality
      (CategoryTheory.Prod.mkHom k.hom.op (𝟙 Y))
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map, Functor.op_map] at hh
    rw [CategoryTheory.Functor.map_id] at hh
    exact hh
  have hh := unitComparison_natural a e.hom e'.hom h j he M
  have hi : IsIso (h.app M) :=
    (((Functor.curry.obj (hom R)).mapIso k.op).app M).isIso_hom
  have hj : IsIso (j.app (F.obj M)) :=
    (((Functor.curry.obj (hom A)).mapIso (F.mapIso k).op).app (F.obj M)).isIso_hom
  have hhh := Iff.of_eq (congrArg (fun z => IsIso z) hh)
  simp only [isIso_comp_left_iff, isIso_comp_right_iff] at hhh
  exact hhh.symm

private lemma isIso_modelUnitComparison_of_diagonal
    (a : F ⊣ (ModuleCat.restrictScalars f).mapDerivedCategory)
    (K M : DerivedCategory (ModuleCat.{u} R))
    (hd : IsIso (diagonal
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))) M K)) :
    IsIso ((a.homEquiv _ _).symm
      ((hom R).map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op K)) (a.unit.app M)) ≫
        (modelRestrictionHomIso f F α K).hom.app (F.obj M))) := by
  let N := DerivedCategory.Q.objPreimage K
  obtain ⟨P, p, hP, _, hp, _⟩ := CochainComplex.KFlat.exists_kFlat_resolution N
  let := hp
  let k : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  apply (isIso_modelUnitComparison_iff_of_iso f F α a k M).mpr
  apply isIso_modelUnitComparison_of_kFlat f F α a P hP M
  let B := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of A A))
  have hn := StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.2.2 (K := B) (L := M) k.hom
  let hR := (Functor.curry.obj (hom R)).mapIso k.op
  have i₁ : IsIso ((tensor R).map (CategoryTheory.Prod.mkHom (𝟙 B) ((hR.app M).hom))) :=
    ((tensor R).mapIso ((Iso.refl B).prod (hR.app M))).isIso_hom
  have i₂ : IsIso ((hR.app ((tensor R).obj (B, M))).hom) := inferInstance
  let : IsIso (diagonal B M K) := hd
  rw [← isIso_comp_left_iff ((tensor R).map
    (CategoryTheory.Prod.mkHom (𝟙 B) ((hR.app M).hom)))]
  erw [hn]
  show IsIso (diagonal B M K ≫ (hR.app ((tensor R).obj (B, M))).hom)
  infer_instance
end

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0A6A.** The canonical derived-Hom base-change morphism
`RHom_R(K, M) ⊗ᴸ_R A ⟶ RHom_A(K ⊗ᴸ_R A, M ⊗ᴸ_R A)` of Stacks 0E1X is an isomorphism in each of
four cases: `K` is perfect; `A` is perfect as an `R`-module; the ring map is flat, `K` is
pseudo-coherent and `M` is bounded below; or `A` has finite Tor dimension over `R`, `K` is
pseudo-coherent and `M` is bounded below. -/
@[stacks 0E1V "invertibility of the base-change map in each of the four cases", stacks 0A6A]
public theorem isIso_derivedHomBaseChange
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : Functor (DerivedCategory (ModuleCat.{max uR uA uM} R))
      (DerivedCategory (ModuleCat.{max uR uA uM} A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (h : StacksDraft.Perfect.IsPerfect K ∨
      StacksDraft.Perfect.IsPerfect
        ((DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj
          ((ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max uR uM} A)))) ∨
      (f.Flat ∧ StacksDraft.PseudoCoherence.IsPseudoCoherent K ∧
        ∃ b : ℤ, DerivedCategory.IsGE M b) ∨
      ((let e := moduleUniverseEquiv.{uR, max uA uM} R
        letI : e.functor.Additive :=
          inferInstanceAs (ModuleCat.restrictScalars.{max uR uA uM, max uR uA uM, uR}
            (ULift.ringEquiv : ULift.{max uA uM} R ≃+* R).toRingHom).Additive
        ∃ a : ℤ, ∀ (N : ModuleCat.{max uR uA uM} R) (i : ℤ), i < a →
          IsZero ((DerivedCategory.homologyFunctor
              (ModuleCat.{max uR uA uM} (ULift.{max uA uM} R)) i).obj
            ((canonTensorMod
                (e.functor.obj N)).obj
              (e.functor.mapDerivedCategory.obj
                ((DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj
                  ((ModuleCat.restrictScalars f).obj
                    (ModuleCat.of A (ULift.{max uR uM} A)))))))) ∧
        StacksDraft.PseudoCoherence.IsPseudoCoherent K ∧
        ∃ b : ℤ, DerivedCategory.IsGE M b)),
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison K
      M) := by
  intro F comparison hF K M h
  let e := moduleUniverseEquiv.{uR, max uR uA uM} R
  let : e.functor.Additive :=
    inferInstanceAs (ModuleCat.restrictScalars.{max uR uA uM, max uR uA uM, uR}
      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).Additive
  let E := e.functor.mapDerivedCategory
  let B := (ModuleCat.restrictScalars f).obj (ModuleCat.of A (ULift.{max uR uM} A))
  let B₀ := (DerivedCategory.singleFunctor (ModuleCat.{max uR uA uM} R) 0).obj B
  have hdiag : IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal
      (E.obj B₀) (E.obj M) (E.obj K)) := by
    rcases h with hK | hB | ⟨hf, hK, b, hb⟩ | ⟨⟨a, ha⟩, hK, b, hb⟩
    · exact Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ 0
        (Or.inl (isPerfect_restrictScalars_ringEquiv (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+*
          R) K hK))
    · exact Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ 0
        (Or.inr (Or.inl (isPerfect_restrictScalars_ringEquiv (ULift.ringEquiv : ULift.{max uR uA uM}
          R ≃+* R) B₀ hB)))
    · have : DerivedCategory.IsGE M b := hb
      have hBflat : Module.Flat (ULift.{max uR uA uM} R) (e.functor.obj B) := by
        let := f.toAlgebra
        have : Module.Flat R A := hf
        show Module.Flat (ULift.{max uR uA uM} R) (ULift.{max uR uM} A)
        exact Module.Flat.ulift_left_iff.mpr inferInstance
      have ha : ∀ (N : ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} R))
          (i : ℤ), i < 0 → IsZero
            ((DerivedCategory.homologyFunctor _ i).obj
              ((canonTensorMod N).obj
                (E.obj B₀))) := by
        intro N i hi
        exact (hasTorAmplitudeAbove_single_of_flat (e.functor.obj B) 0 N i hi).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso
            ((canonTensorMod N).mapIso
              ((e.functor.mapDerivedCategorySingleFunctor 0).app B)))
      exact Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ 0
        (Or.inr (Or.inr ⟨isPseudoCoherent_restrictScalars_ringEquiv (ULift.ringEquiv : ULift.{max uR
          uA uM} R ≃+* R) K hK,
          ⟨b, isGE_mapDerivedCategory e.functor M b⟩, ha⟩))
    · have : DerivedCategory.IsGE M b := hb
      refine Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal _ _ _ a
        (Or.inr (Or.inr ⟨isPseudoCoherent_restrictScalars_ringEquiv (ULift.ringEquiv : ULift.{max uR
          uA uM} R ≃+* R) K hK,
          ⟨b, isGE_mapDerivedCategory e.functor M b⟩, ?_⟩))
      let e₀ := moduleUniverseEquiv.{uR, max uA uM} R
      let : e₀.functor.Additive := inferInstanceAs
        (ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uA uM} R ≃+* R).toRingHom).Additive
      have ht : ∀ (N : ModuleCat.{max uR uA uM} (ULift.{max uA uM} R))
          (i : ℤ), i < a → IsZero ((DerivedCategory.homologyFunctor _ i).obj
            ((canonTensorMod N).obj
              (e₀.functor.mapDerivedCategory.obj B₀))) := by
        intro N i hi
        exact (ha (e₀.inverse.obj N) i hi).of_iso
          ((DerivedCategory.homologyFunctor _ i).mapIso
            ((canonTensorObj
              (e₀.functor.mapDerivedCategory.obj B₀)).mapIso (e₀.counitIso.app N))).symm
      let r : ULift.{max uR uA uM} R ≃+* ULift.{max uA uM} R :=
        ULift.ringEquiv.trans ULift.ringEquiv.symm
      have ht' := hasTorAmplitudeAbove_restrictScalars_ringEquiv r _ a ht
      intro N i hi
      exact (ht' N i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
        ((canonTensorMod N).mapIso
          (ringLiftSingleIso.{uR,uA,uM} B).symm))
  apply (@isIso_derivedHomBaseChange_iff_model.{uR,uA,uM} R A _ _ f
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM,uR,uA} f).isRightAdjoint
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM,uR,uA} f).isLeftAdjoint
    F comparison hF K M).mpr
  let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
    (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings f'
    (HomologicalComplex.zero : CochainComplex (ModuleCat.{max uR uA uM}
      (ULift.{max uR uA uM} A)) ℤ)
  let a' := CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{max uR uA
    uM,max uR uA uM,max uR uA uM}
    f' T.B T.alphaB
  apply isIso_modelUnitComparison_of_diagonal f' T.B T.alphaB a'
  let i := modelScalarCoefficientIso.{uR,uA,uM} f
  let H := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.hom (ULift.{max uR uA uM} R)
  let D := _root_.StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (ULift.{max uR uA uM} R)
  have hn := StacksDraft.DerivedHom.derivedTensorHomDiagonal_natural.1
    (L := E.obj M) (M := E.obj K) i.hom
  have hi₁ : IsIso (D.map (CategoryTheory.Prod.mkHom i.hom
      (𝟙 (H.obj (Opposite.op (E.obj K), E.obj M))))) :=
    (D.mapIso (i.prod (Iso.refl _))).isIso_hom
  have hi₂ : IsIso (H.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.obj K)))
      (D.map (CategoryTheory.Prod.mkHom i.hom (𝟙 (E.obj M)))))) :=
    (H.mapIso ((Iso.refl (Opposite.op (E.obj K))).prod
      (D.mapIso (i.prod (Iso.refl _))))).isIso_hom
  let := hdiag
  rw [← isIso_comp_left_iff (D.map (CategoryTheory.Prod.mkHom i.hom
    (𝟙 (H.obj (Opposite.op (E.obj K), E.obj M)))))]
  erw [hn]
  show IsIso (StacksDraft.DerivedHom.derivedTensorHomDiagonal (E.obj B₀) (E.obj M) (E.obj K) ≫
    H.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (E.obj K)))
      (D.map (CategoryTheory.Prod.mkHom i.hom (𝟙 (E.obj M))))))
  infer_instance

end Stacks.DerivedHom.BaseChangeIso

end

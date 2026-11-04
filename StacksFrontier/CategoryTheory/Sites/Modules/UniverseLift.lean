module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Presheaves of modules along an equivalence of categories, with a change of ring universe

Let `e : C ≌ D` be an equivalence of categories, `R` a presheaf of rings on `C` and `R'` a
presheaf of rings on `D`, the two with section rings in possibly different universes. A
*ring transport* `T : RingTransport e R R'` is a family of ring isomorphisms
`R'(Y) ≃+* R(e⁻¹ Y)`, natural in `Y`. It induces an equivalence

  `PresheafOfModules.{m} R ≌ PresheafOfModules.{m} R'`

for every module universe `m`: a presheaf of `R`-modules `M` goes to `Y ↦ M(e⁻¹ Y)` with its
`R'(Y)`-module structure obtained by restriction of scalars along `R'(Y) ≃+* R(e⁻¹ Y)`.

## Main definitions

* `Stacks.UniverseLift.RingTransport`: the transport datum.
* `Stacks.UniverseLift.RingTransport.functor`: the induced functor on presheaves of modules.
* `Stacks.UniverseLift.RingTransport.symm`: the transport datum in the opposite direction.
* `Stacks.UniverseLift.RingTransport.equivalence`: the induced equivalence of categories of
  presheaves of modules.

## Main results

* `Stacks.UniverseLift.RingTransport.functorCompEvaluation`: evaluating the transport of `M` at
  `Y` is `M(e⁻¹ Y)` with scalars restricted, on the nose.
* `Stacks.UniverseLift.RingTransport.functor_obj_presheaf`: the underlying presheaf of abelian
  groups of the transport of `M` is the precomposition of that of `M` with `e⁻¹`.
-/

@[expose] public section

open CategoryTheory Opposite

universe m v₁ v₂ u₁ u₂ r₁ r₂

namespace Stacks.UniverseLift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (e : C ≌ D)
  (R : Cᵒᵖ ⥤ RingCat.{r₁}) (R' : Dᵒᵖ ⥤ RingCat.{r₂})

/-- A *ring transport* along an equivalence `e : C ≌ D` from a presheaf of rings `R` on `C` to a
presheaf of rings `R'` on `D`: ring isomorphisms `R'(Y) ≃+* R(e⁻¹ Y)`, natural in `Y`. The two
presheaves of rings may have their section rings in different universes. -/
structure RingTransport where
  /-- The ring isomorphism `R'(Y) ≃+* R(e⁻¹ Y)`. -/
  iso (Y : Dᵒᵖ) : R'.obj Y ≃+* R.obj (e.inverse.op.obj Y)
  /-- Naturality of the ring isomorphisms in `Y`. -/
  naturality {Y Y' : Dᵒᵖ} (f : Y ⟶ Y') (x : R'.obj Y) :
    iso Y' ((R'.map f).hom x) = (R.map (e.inverse.op.map f)).hom (iso Y x)

namespace RingTransport

variable {e R R'} (T : RingTransport e R R')

/-- The transport of a presheaf of `R`-modules: `Y ↦ M(e⁻¹ Y)`, an `R'(Y)`-module by
restriction of scalars along `R'(Y) ≃+* R(e⁻¹ Y)`. -/
noncomputable def functorObj (M : PresheafOfModules.{m} R) : PresheafOfModules.{m} R' where
  obj Y := (ModuleCat.restrictScalars (T.iso Y).toRingHom).obj (M.obj (e.inverse.op.obj Y))
  map {Y Y'} f := ModuleCat.ofHom
      (X := (ModuleCat.restrictScalars (T.iso Y).toRingHom).obj (M.obj (e.inverse.op.obj Y)))
      (Y := (ModuleCat.restrictScalars (R'.map f).hom).obj
        ((ModuleCat.restrictScalars (T.iso Y').toRingHom).obj (M.obj (e.inverse.op.obj Y'))))
    { toFun := M.map (e.inverse.op.map f)
      map_add' := map_add _
      map_smul' := fun r x ↦ (M.map_smul (e.inverse.op.map f) (T.iso Y r) x).trans (by
        rw [← T.naturality f r]
        rfl) }
  map_id Y := by
    ext x
    exact (M.congr_map_apply (e.inverse.op.map_id Y) x).trans (by simp; rfl)
  map_comp {Y Y' Y''} f g := by
    ext x
    exact (M.congr_map_apply (e.inverse.op.map_comp f g) x).trans (by simp; rfl)

/-- The functor `PresheafOfModules.{m} R ⥤ PresheafOfModules.{m} R'` induced by a ring
transport. -/
@[simps obj]
noncomputable def functor : PresheafOfModules.{m} R ⥤ PresheafOfModules.{m} R' where
  obj M := T.functorObj M
  map {M N} φ :=
    { app Y := (ModuleCat.restrictScalars (T.iso Y).toRingHom).map (φ.app _)
      naturality {Y Y'} f := by
        ext x
        exact PresheafOfModules.naturality_apply φ (e.inverse.op.map f) x }

/-- The sections of the transport over `Y` are the sections over `e⁻¹ Y`. -/
@[simp]
lemma functor_obj_obj (M : PresheafOfModules.{m} R) (Y : Dᵒᵖ) :
    ((T.functor.obj M).obj Y : Type _) = M.obj (e.inverse.op.obj Y) := rfl

/-- The restriction maps of the transport are restriction maps along `e⁻¹`. -/
lemma functor_obj_map_apply (M : PresheafOfModules.{m} R) {Y Y' : Dᵒᵖ} (f : Y ⟶ Y')
    (x : M.obj (e.inverse.op.obj Y)) :
    ((T.functor.obj M).map f).hom x = M.map (e.inverse.op.map f) x := rfl

/-- The transport of a morphism acts on sections over `Y` as the morphism over `e⁻¹ Y`. -/
lemma functor_map_app_apply {M N : PresheafOfModules.{m} R} (φ : M ⟶ N) (Y : Dᵒᵖ)
    (x : M.obj (e.inverse.op.obj Y)) :
    ((T.functor.map φ).app Y).hom x = φ.app (e.inverse.op.obj Y) x := rfl

/-- Evaluating the transport of a presheaf of modules at `Y` is evaluating it at `e⁻¹ Y` and
restricting scalars along `R'(Y) ≃+* R(e⁻¹ Y)`. -/
noncomputable def functorCompEvaluation (Y : Dᵒᵖ) :
    T.functor ⋙ PresheafOfModules.evaluation.{m} R' Y ≅
      PresheafOfModules.evaluation.{m} R (e.inverse.op.obj Y) ⋙
        ModuleCat.restrictScalars (T.iso Y).toRingHom :=
  Iso.refl _

/-- The underlying presheaf of abelian groups of the transport is the precomposition with
`e⁻¹`. -/
lemma functor_obj_presheaf (M : PresheafOfModules.{m} R) :
    (T.functor.obj M).presheaf = e.inverse.op ⋙ M.presheaf := rfl

/-- The transport commutes with the forgetful functors to presheaves of abelian groups. -/
noncomputable def functorCompToPresheaf :
    T.functor ⋙ PresheafOfModules.toPresheaf.{m} R' ≅
      PresheafOfModules.toPresheaf.{m} R ⋙ (Functor.whiskeringLeft _ _ _).obj e.inverse.op :=
  Iso.refl _

/-- The ring isomorphism `R(X) ≃+* R(e⁻¹ (e X))` induced by the unit of the equivalence. -/
noncomputable def unitRingEquiv (X : Cᵒᵖ) :
    R.obj X ≃+* R.obj (e.inverse.op.obj (e.functor.op.obj X)) :=
  (R.mapIso (e.unitIso.app X.unop).op.symm).ringCatIsoToRingEquiv

omit T in
/-- `unitRingEquiv` is the restriction map of `R` along the unit of the equivalence. -/
lemma unitRingEquiv_apply (X : Cᵒᵖ) (x : R.obj X) :
    unitRingEquiv (e := e) (R := R) X x = (R.map (e.unitInv.app X.unop).op).hom x := rfl

/-- The ring transport in the opposite direction, along `e.symm`: the ring isomorphisms
`R(X) ≃+* R(e⁻¹ (e X)) ≃+* R'(e X)`. -/
noncomputable def symm : RingTransport e.symm R' R where
  iso X := (unitRingEquiv (e := e) (R := R) X).trans (T.iso (e.functor.op.obj X)).symm
  naturality {X X'} f x := by
    apply (T.iso (e.functor.op.obj X')).injective
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, unitRingEquiv_apply]
    change (R.map (e.unitInv.app X'.unop).op).hom ((R.map f).hom x) =
      T.iso (e.functor.op.obj X') ((R'.map (e.functor.op.map f)).hom
        ((T.iso (e.functor.op.obj X)).symm ((R.map (e.unitInv.app X.unop).op).hom x)))
    rw [T.naturality, RingEquiv.apply_symm_apply, ← RingCat.comp_apply, ← RingCat.comp_apply,
      ← R.map_comp, ← R.map_comp]
    congr 3
    exact Quiver.Hom.unop_inj (e.unitInv.naturality f.unop).symm

/-- The ring isomorphisms of `T` and of `T.symm` compose to the restriction map along the
unit of the equivalence. -/
lemma iso_symm_iso (X : Cᵒᵖ) (x : R.obj X) :
    T.iso (e.functor.op.obj X) (T.symm.iso X x) = (R.map (e.unitInv.app X.unop).op).hom x :=
  RingEquiv.apply_symm_apply _ _

omit T in
/-- Restricting along `f` and then along `g` is the identity when `f ≫ g = 𝟙`. -/
lemma map_map_of_comp_eq_id {S : Cᵒᵖ ⥤ RingCat.{r₁}}
    (M : PresheafOfModules.{m} S) {X Y : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (x : M.obj X) : M.map g (M.map f x) = x := by
  rw [← M.map_comp_apply, h, M.map_id]
  rfl

/-- The component at `X` of the unit of the equivalence: the restriction map of `M` along the
unit of `e`. -/
noncomputable def unitApp (M : PresheafOfModules.{m} R) (X : Cᵒᵖ) :
    M.obj X ≅ (T.symm.functor.obj (T.functor.obj M)).obj X :=
  LinearEquiv.toModuleIso (R := R.obj X) (X₁ := M.obj X)
    (X₂ := (T.symm.functor.obj (T.functor.obj M)).obj X) (m₁ := ModuleCat.isModule _)
    (m₂ := ModuleCat.isModule _)
    { toFun := M.map (e.unitInv.app X.unop).op
      map_add' := map_add _
      map_smul' := fun r x ↦ (M.map_smul _ r x).trans
        (congrArg (fun s ↦ s • M.map (e.unitInv.app X.unop).op x) (T.iso_symm_iso X r).symm)
      invFun := M.map (e.unit.app X.unop).op
      left_inv := map_map_of_comp_eq_id M (e.unitInv.app X.unop).op (e.unit.app X.unop).op
        (by rw [← op_comp, Iso.hom_inv_id_app]; rfl)
      right_inv := map_map_of_comp_eq_id M (X := op (e.inverse.obj (e.functor.obj X.unop)))
        (e.unit.app X.unop).op (e.unitInv.app X.unop).op
        (by rw [← op_comp, Iso.inv_hom_id_app]; rfl) }

omit T in
/-- Two composites of restriction maps agree when the composites of the morphisms do. -/
lemma map_map_eq_map_map {S : Cᵒᵖ ⥤ RingCat.{r₁}}
    (M : PresheafOfModules.{m} S) {X Y Y' Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X ⟶ Y')
    (g' : Y' ⟶ Z) (h : f ≫ g = f' ≫ g') (x : M.obj X) :
    M.map g (M.map f x) = M.map g' (M.map f' x) := by
  rw [← M.map_comp_apply, h, M.map_comp_apply]

/-- Transporting a section of `R'` to `R` and back along `T.symm`, then restricting along the
counit of the equivalence, gives the section back. -/
lemma map_symm_iso (Y : Dᵒᵖ) (r : R'.obj Y) :
    (R'.map (e.counitInv.app Y.unop).op).hom (T.symm.iso (e.inverse.op.obj Y) (T.iso Y r)) =
      r := by
  apply (T.iso Y).injective
  rw [T.naturality]
  show (R.map (e.inverse.op.map (e.counitInv.app Y.unop).op)).hom
    (T.iso (e.functor.op.obj (e.inverse.op.obj Y)) (T.symm.iso (e.inverse.op.obj Y) (T.iso Y r))) =
      T.iso Y r
  rw [T.iso_symm_iso]
  show (R.map (e.unitInv.app (e.inverse.obj Y.unop)).op ≫
    R.map (e.inverse.map (e.counitInv.app Y.unop)).op).hom (T.iso Y r) = T.iso Y r
  rw [← R.map_comp, ← op_comp]
  simp

/-- The component at `Y` of the counit of the equivalence: the restriction map of `M'` along
the counit of `e`. -/
noncomputable def counitApp (M' : PresheafOfModules.{m} R') (Y : Dᵒᵖ) :
    (T.functor.obj (T.symm.functor.obj M')).obj Y ≅ M'.obj Y :=
  LinearEquiv.toModuleIso (R := R'.obj Y)
    (X₁ := (T.functor.obj (T.symm.functor.obj M')).obj Y) (X₂ := M'.obj Y)
    (m₁ := ModuleCat.isModule _) (m₂ := ModuleCat.isModule _)
    { toFun := M'.map (e.counitInv.app Y.unop).op
      map_add' := map_add _
      map_smul' := fun r x ↦ (M'.map_smul _ (T.symm.iso _ (T.iso Y r)) x).trans
        (congrArg (fun s ↦ s • M'.map (e.counitInv.app Y.unop).op x) (T.map_symm_iso Y r))
      invFun := M'.map (e.counit.app Y.unop).op
      left_inv := map_map_of_comp_eq_id M' (X := op (e.functor.obj (e.inverse.obj Y.unop)))
        (e.counitInv.app Y.unop).op (e.counit.app Y.unop).op
        (by rw [← op_comp, Iso.hom_inv_id_app]; rfl)
      right_inv := map_map_of_comp_eq_id M' (e.counit.app Y.unop).op (e.counitInv.app Y.unop).op
        (by rw [← op_comp, Iso.inv_hom_id_app]; rfl) }

/-- The unit of the equivalence, as an isomorphism of functors. -/
noncomputable def unitIso :
    𝟭 (PresheafOfModules.{m} R) ≅ T.functor ⋙ T.symm.functor :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk (T.unitApp M) (fun X X' f ↦ by
      ext x
      exact map_map_eq_map_map M f (e.unitInv.app X'.unop).op (e.unitInv.app X.unop).op
        (e.inverse.op.map (e.functor.op.map f))
        (Quiver.Hom.unop_inj (e.unitInv.naturality f.unop).symm) x))
    (fun {M N} φ ↦ by
      ext X x
      exact (PresheafOfModules.naturality_apply φ (e.unitInv.app X.unop).op x).symm)

/-- The counit of the equivalence, as an isomorphism of functors. -/
noncomputable def counitIso :
    T.symm.functor ⋙ T.functor ≅ 𝟭 (PresheafOfModules.{m} R') :=
  NatIso.ofComponents
    (fun M' ↦ PresheafOfModules.isoMk (T.counitApp M') (fun Y Y' f ↦ by
      ext x
      exact map_map_eq_map_map M' (e.functor.op.map (e.inverse.op.map f))
        (e.counitInv.app Y'.unop).op (e.counitInv.app Y.unop).op f
        (Quiver.Hom.unop_inj (e.counitInv.naturality f.unop).symm) x))
    (fun {M N} φ ↦ by
      ext Y x
      exact (PresheafOfModules.naturality_apply φ (e.counitInv.app Y.unop).op x).symm)

/-- **The equivalence of categories of presheaves of modules induced by a ring transport.** Its
functor is `RingTransport.functor` and its inverse is the functor of the opposite transport
`RingTransport.symm`. -/
noncomputable def equivalence : PresheafOfModules.{m} R ≌ PresheafOfModules.{m} R' :=
  CategoryTheory.Equivalence.mk T.functor T.symm.functor T.unitIso T.counitIso

/-- The functor of the equivalence is the transport. -/
@[simp]
lemma equivalence_functor :
    (T.equivalence : PresheafOfModules.{m} R ≌ PresheafOfModules.{m} R').functor = T.functor :=
  rfl

/-- The inverse of the equivalence is the transport along the opposite ring transport. -/
@[simp]
lemma equivalence_inverse :
    (T.equivalence : PresheafOfModules.{m} R ≌ PresheafOfModules.{m} R').inverse =
      T.symm.functor :=
  rfl

/-- The transport is additive. -/
instance functor_additive :
    (T.functor : PresheafOfModules.{m} R ⥤ PresheafOfModules.{m} R').Additive where

/-- The functor of the equivalence induced by a ring transport is additive. -/
instance equivalence_functor_additive :
    (T.equivalence : PresheafOfModules.{m} R ≌ PresheafOfModules.{m} R').functor.Additive :=
  inferInstanceAs (T.functor : PresheafOfModules.{m} R ⥤ PresheafOfModules.{m} R').Additive

/-- The transport is an equivalence of categories. -/
instance functor_isEquivalence :
    (T.functor : PresheafOfModules.{m} R ⥤ PresheafOfModules.{m} R').IsEquivalence :=
  T.equivalence.isEquivalence_functor

/-- **The ring transport on slices.** For `U'` in `D`, the equivalence of slices
`C/e⁻¹(U') ≌ D/U'` (whose inverse is `Over.post e⁻¹`) carries a ring transport from the
restriction of `R` to `C/e⁻¹(U')` to the restriction of `R'` to `D/U'`, with the same ring
isomorphisms. -/
def over (U' : D) :
    RingTransport (Over.postEquiv U' e.symm).symm ((Over.forget (e.inverse.obj U')).op ⋙ R)
      ((Over.forget U').op ⋙ R') where
  iso V' := T.iso (op V'.unop.left)
  naturality f x := T.naturality ((Over.forget U').op.map f) x

/-- The ring isomorphisms of the ring transport on slices are those of `T`. -/
@[simp]
lemma over_iso (U' : D) (V' : (Over U')ᵒᵖ) : (T.over U').iso V' = T.iso (op V'.unop.left) := rfl

end RingTransport

end Stacks.UniverseLift

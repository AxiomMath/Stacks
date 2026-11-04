module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizedPullbackMate
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackTopos

/-!
# The unit of the module pullback adjunction restricted to a slice

Let `f : X ⟶ Y` be a morphism of ringed sites, `V` an object of `Y` and `f' : X/u(V) ⟶ Y/V` the
localized morphism. The restriction to `Y/V` of the unit `G ⟶ f_*f^*G` of the adjunction
`f^* ⊣ f_*` is the unit `G|_V ⟶ f'_*f'^*(G|_V)` followed by the direct image of the localization
mate `f'^*(G|_V) ≅ (f^*G)|_{u(V)}` and the identification `(f_*M)|_V = f'_*(M|_{u(V)})`. Hence the
restricted unit is an isomorphism exactly when the localized unit is.

## Main results

* `CategoryTheory.Adjunction.isIso_unit_app_iff_of_iso_right`: two adjunctions with isomorphic
  right adjoints have their units invertible at the same objects.
* `CategoryTheory.Adjunction.isIso_map_unit_app_of_fullyFaithful`: a unit is invertible on
  sections at the image of a fully faithful left adjoint of sections, when the sections of the
  right adjoint have a fully faithful left adjoint too.
* `AlgebraicGeometry.RingedSite.Hom.overRestrictionModules_map_unit_comp`: the restricted unit
  factors through the localized unit and the localization mate.
* `AlgebraicGeometry.RingedSite.Hom.isIso_overRestrictionModules_map_unit_iff`: the restricted
  unit is invertible if and only if the localized unit is.
* `AlgebraicGeometry.RingedSite.Hom.isIso_pullbackPushforwardAdjunctionTopos_unit_app_iff`: the
  units of the two presentations of `f^* ⊣ f_*`, along the morphism of ringed topoi of `f` and
  presented on sites, are invertible at the same modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **Two adjunctions with isomorphic right adjoints have their units invertible at the same
objects**: the two units differ by the isomorphism of right adjoints and the image of the
comparison of the two left adjoints. -/
theorem isIso_unit_app_iff_of_iso_right {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁)
    (adj₂ : L₂ ⊣ R₂) (e : R₁ ≅ R₂) (c : C) :
    IsIso (adj₁.unit.app c) ↔ IsIso (adj₂.unit.app c) := by
  have h₁ : (adj₁.ofNatIsoRight e).unit.app c = adj₁.unit.app c ≫ e.hom.app (L₁.obj c) := by
    simp
  have h₂ := unit_leftAdjointUniq_hom_app (adj₁.ofNatIsoRight e) adj₂ c
  rw [← h₂, h₁, Category.assoc]
  constructor
  · intro _
    infer_instance
  · intro _
    exact IsIso.of_isIso_comp_right (adj₁.unit.app c)
      (e.hom.app (L₁.obj c) ≫ R₂.map ((leftAdjointUniq (adj₁.ofNatIsoRight e) adj₂).hom.app c))

/-- **A unit is invertible on sections when both sides have fully faithful section adjoints.**
Let `P ⊣ Q`, let `L_s ⊣ E_s` and `L_b ⊣ E_b` with `L_s`, `L_b` fully faithful, and suppose
`Q ⋙ E_s ≅ E_b ⋙ E` for an equivalence `E`. Then `E_s` inverts the unit of `P ⊣ Q` at every
`L_s M`: the composite adjunction `L_s ⋙ P ⊣ Q ⋙ E_s` has the invertible unit of
`E⁻¹ ⋙ L_b ⊣ E_b ⋙ E`. -/
theorem isIso_map_unit_app_of_fullyFaithful
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {P : C ⥤ D} {Q : D ⥤ C} (adj : P ⊣ Q)
    {Ls : A ⥤ C} {Es : C ⥤ A} (adjS : Ls ⊣ Es) (hLs : Ls.FullyFaithful)
    {Lb : B ⥤ D} {Eb : D ⥤ B} (adjB : Lb ⊣ Eb) (hLb : Lb.FullyFaithful)
    (E : B ≌ A) (e : Q ⋙ Es ≅ Eb ⋙ E.functor) (M : A) :
    IsIso (Es.map (adj.unit.app (Ls.obj M))) := by
  have := hLs.full
  have := hLs.faithful
  have := hLb.full
  have := hLb.faithful
  have h₂ : IsIso ((E.symm.toAdjunction.comp adjB).unit.app M) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  have h₁ := (isIso_unit_app_iff_of_iso_right (adjS.comp adj) (E.symm.toAdjunction.comp adjB)
    e M).2 h₂
  rw [Adjunction.comp_unit_app] at h₁
  exact IsIso.of_isIso_comp_left (adjS.unit.app M) _

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedSite

universe u

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- The identification `(f_*M)|_V = f'_*(M|_{u(V)})` is an isomorphism, being the identity on
underlying sheaves of sets. -/
instance Hom.isIso_localizedPushforwardSquare_app
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    IsIso ((f.localizedPushforwardSquare V).app M) :=
  Stacks.Sheaves.PushforwardEssentialImage.isIso_of_isIso_moduleSheafFunctor_map
    ((f.localizedPushforwardSquare V).app M)
    (by rw [f.moduleSheafFunctor_map_localizedPushforwardSquare_app V M]; exact IsIso.id _)

variable [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The restricted unit factors through the localized unit**: restricting the unit
`G ⟶ f_*f^*G` to `Y/V` and identifying `(f_*f^*G)|_V = f'_*((f^*G)|_{u(V)})` is the unit
`G|_V ⟶ f'_*f'^*(G|_V)` followed by the direct image of the localization mate. -/
theorem Hom.overRestrictionModules_map_unit_comp
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    (Y.overRestrictionModules V).map
        ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
          f.ringedToposHom).unit.app G) ≫
      (f.localizedPushforwardSquare V).app _ =
    (RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (f.localized V).ringedToposHom).unit.app ((Y.overRestrictionModules V).obj G) ≫
      (RingedToposHom.pushforwardModules.{u, u, u, u, u, u} (f.localized V).ringedToposHom).map
        ((f.localizedPullbackMate V).app G) :=
  unit_mateEquiv_symm _ _ (f.localizedPushforwardSquare V) G

omit [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The restricted unit is invertible if and only if the localized unit is**: the unit
`G ⟶ f_*f^*G` restricted to `Y/V` is an isomorphism exactly when the unit of the localized
morphism at `G|_V` is. -/
theorem Hom.isIso_overRestrictionModules_map_unit_iff
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    IsIso ((Y.overRestrictionModules V).map
        ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
          f.ringedToposHom).unit.app G)) ↔
      IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        (f.localized V).ringedToposHom).unit.app ((Y.overRestrictionModules V).obj G)) := by
  have := f.isIso_localizedPullbackMate V
  have : IsIso ((f.localizedPullbackMate V).app G) :=
    inferInstanceAs (IsIso ((f.localizedPullbackMate V).natTrans.app G))
  rw [← isIso_comp_right_iff _ ((f.localizedPushforwardSquare V).app _),
    f.overRestrictionModules_map_unit_comp V G, isIso_comp_right_iff]

omit [HasWeakSheafify (X.J.over (f.u.obj V)) AddCommGrpCat.{u}]
  [(X.J.over (f.u.obj V)).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The two presentations of `f^* ⊣ f_*` have their units invertible at the same modules**: the
adjunction `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` along the morphism of
ringed topoi of `f`, and the site-presented adjunction
`RingedToposSiteHom.pullbackPushforwardAdjunctionTopos`, whose right adjoints are identified by
`AlgebraicGeometry.RingedSite.Hom.pushforwardToposIso`. -/
theorem Hom.isIso_pullbackPushforwardAdjunctionTopos_unit_app_iff
    (G : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) :
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u, u, u, u, u, u}
        f.ringedToposHom).unit.app G) ↔
      IsIso (f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app G) :=
  Adjunction.isIso_unit_app_iff_of_iso_right _ _ f.pushforwardToposIso G

end AlgebraicGeometry.RingedSite

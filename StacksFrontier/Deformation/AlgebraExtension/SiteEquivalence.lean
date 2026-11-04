module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Deformation.AlgebraExtension.SiteRestriction

/-!
# Square-zero extensions of sheaves of algebras on equivalent sites

Let `e : 𝒞 ≌ 𝒟` be an equivalence of categories carrying Grothendieck topologies `J` and `K` for
which the inverse `G = e.inverse` is a dense subsite, so that restriction along `G` is an
equivalence `Sh(𝒞) ≌ Sh(𝒟)`. Restriction along `G` is then an equivalence between the category of
extensions of `𝒜`-algebras of `𝒪` by `ℳ` on `𝒞` and the category of extensions of
`G^*𝒜`-algebras of `G^*𝒪` by `G^*ℳ` on `𝒟`.

Full faithfulness is `Deformation.AlgebraExtension.full_restrictViaFunctor` and
`Deformation.AlgebraExtension.faithful_restrictViaFunctor`. An extension `𝒪''` on `𝒟` comes back
to `𝒞` by restriction along `e.functor`, read through the unit `𝒪 ≅ e.functor^* G^* 𝒪` of the
equivalence of sheaf categories, and the counit identifies the restriction of the result with
`𝒪''`.

This is how the extension categories of the small étale site of an algebraic space, whose objects
lie in `Type (u + 1)`, are identified with those of its model in `Type u`, in the proof of
[Stacks Project, Tag 0D3P].

## Main definitions

* `Deformation.AlgebraExtension.siteRestriction`: restriction of extensions along `e.inverse`.
* `Deformation.AlgebraExtension.siteExtension`: an extension on `𝒟` carried back to `𝒞`.

## Main results

* `Deformation.AlgebraExtension.isEquivalence_siteRestriction`: restriction along `e.inverse` is
  an equivalence of categories of extensions.

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ w₁ v₂ w₂

namespace Deformation.AlgebraExtension

variable {C : Type v₁} [Category.{w₁} C] {D : Type v₂} [Category.{w₂} D]
  {J : GrothendieckTopology C} (K : GrothendieckTopology D) (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A O : Sheaf J CommRingCat.{u}} (a : A ⟶ O)
  (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O))

/-- The identity comparison of the restricted base data with themselves. -/
noncomputable def idRingComparison :
    RingComparison (G := e.inverse) a ((ringRes K e.inverse).map a) where
  α := Iso.refl _
  ω := Iso.refl _
  comm := by simp

/-- The identity comparison of the restriction of `ℳ` with itself. -/
noncomputable def idModuleComparison :
    ModuleComparison (idRingComparison K e a).ω M ((moduleRes K e.inverse O).obj M) where
  μ _ := AddEquiv.refl _
  μ_naturality _ _ := rfl
  μ_smul _ _ _ := rfl

/-- **Restriction of extensions along `e.inverse`**, from extensions of `𝒜`-algebras of `𝒪` by
`ℳ` on `𝒞` to extensions of `G^*𝒜`-algebras of `G^*𝒪` by `G^*ℳ` on `𝒟`. -/
noncomputable abbrev siteRestriction :
    AlgebraExtension a M ⥤
      AlgebraExtension ((ringRes K e.inverse).map a) ((moduleRes K e.inverse O).obj M) :=
  restrictViaFunctor _ _ (idRingComparison K e a) (idModuleComparison K e a M)

/-- The unit of the equivalence of sheaf categories, as a comparison of `𝒜 ⟶ 𝒪` with the
restriction along `e.functor` of `G^*𝒜 ⟶ G^*𝒪`. -/
noncomputable def unitRingComparison :
    RingComparison (G := e.functor) (K := J) (J := K) ((ringRes K e.inverse).map a) a where
  α := (Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.app A
  ω := (Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.app O
  comm := ((Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.hom.naturality a)

/-- The identification `ℳ(U) ≅ ℳ(G(e U))` of sections along the unit of `e`. -/
noncomputable def unitModuleEquiv (U : Cᵒᵖ) :
    M.val.obj U ≃+ M.val.obj (e.inverse.op.obj (e.functor.op.obj U)) where
  toFun := M.val.map (e.unitInv.app U.unop).op
  invFun := M.val.map (e.unit.app U.unop).op
  left_inv m := by
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.unitIso.hom_inv_id_app, op_id,
      PresheafOfModules.map_id]
    rfl
  right_inv m := by
    rw [← PresheafOfModules.map_comp_apply, ← op_comp, e.unitIso.inv_hom_id_app, op_id,
      PresheafOfModules.map_id]
    rfl
  map_add' := map_add _

/-- The unit of `e`, as a comparison of `ℳ` with the restriction along `e.functor` of `G^*ℳ`. -/
noncomputable def unitModuleComparison :
    ModuleComparison (G := e.functor) (K := J) (J := K) (unitRingComparison K e a).ω
      ((moduleRes K e.inverse O).obj M) M where
  μ := unitModuleEquiv e M
  μ_naturality {U W} f m := by
    change M.val.map (e.unitInv.app W.unop).op (M.val.map f m) =
      M.val.map (e.inverse.map (e.functor.map f.unop)).op
        (M.val.map (e.unitInv.app U.unop).op m)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    refine PresheafOfModules.congr_map_apply _ (Quiver.Hom.unop_inj ?_) m
    exact (e.unitInv.naturality f.unop).symm
  μ_smul U r m := PresheafOfModules.map_smul _ _ _ _

variable {a M}

/-- **An extension on `𝒟` carried back to `𝒞`**: restriction along `e.functor`, read through the
unit of the equivalence of sheaf categories. -/
noncomputable def siteExtension
    (P : AlgebraExtension ((ringRes K e.inverse).map a) ((moduleRes K e.inverse O).obj M)) :
    AlgebraExtension a M :=
  P.restrictVia (unitRingComparison K e a) (unitModuleComparison K e a M)

variable (a M) in
/-- Carrying extensions back from `𝒟` to `𝒞`, as a functor. -/
noncomputable abbrev siteExtensionFunctor :
    AlgebraExtension ((ringRes K e.inverse).map a) ((moduleRes K e.inverse O).obj M) ⥤
      AlgebraExtension a M :=
  restrictViaFunctor _ _ (unitRingComparison K e a) (unitModuleComparison K e a M)

/-- The unit of the equivalence of sheaf categories, as a morphism of extensions
`𝒪' ⟶ e.functor^* G^* 𝒪'`. -/
noncomputable def siteUnit (P : AlgebraExtension a M) :
    P ⟶ siteExtension K e ((siteRestriction K e a M).obj P) where
  hom := (Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.hom.app P.extension
  reduction_comm := by
    ext U x
    change O.obj.map (e.unit.app U.unop).op (P.reduction.hom.app _
      (P.extension.obj.map (e.unitInv.app U.unop).op x)) = P.reduction.hom.app U x
    rw [NatTrans.naturality_apply P.reduction.hom, ← ConcreteCategory.comp_apply,
      ← CategoryTheory.Functor.map_comp, ← op_comp, e.unitIso.hom_inv_id_app, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  algebraMap_comm := by
    ext U x
    change P.extension.obj.map (e.unitInv.app U.unop).op (P.algebraMap.hom.app U x) =
      P.algebraMap.hom.app _ (A.obj.map (e.unitInv.app U.unop).op x)
    rw [NatTrans.naturality_apply P.algebraMap.hom]
    rfl
  kernel_comm U m := (P.incl_naturality _ m).symm

/-- The underlying morphism of sheaves of `siteUnit` is the unit of the equivalence of sheaf
categories at `𝒪'`. -/
theorem siteUnit_hom (P : AlgebraExtension a M) :
    (siteUnit K e P).hom =
      (Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.hom.app P.extension :=
  rfl

/-- The unit morphism `𝒪' ⟶ e.functor^* G^* 𝒪'` of extensions is an isomorphism. -/
theorem isIso_siteUnit (P : AlgebraExtension a M) : IsIso (siteUnit K e P) :=
  have : IsIso (siteUnit K e P).hom :=
    (inferInstance : IsIso ((Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.app
      P.extension).hom)
  isIso_of_isIso_hom _

variable (a M) in
/-- The unit of `e` identifies an extension with the result of restricting it to `𝒟` and carrying
it back. -/
noncomputable def siteUnitIso : 𝟭 (AlgebraExtension a M) ≅
    siteRestriction K e a M ⋙ siteExtensionFunctor K e a M :=
  NatIso.ofComponents (fun P => @asIso _ _ _ _ (siteUnit K e P) (isIso_siteUnit K e P))
    fun f => MapAlong.ext
      ((Equivalence.sheafCongr J K e CommRingCat.{u}).unitIso.hom.naturality f.hom)

variable (a M) in
/-- **Restriction along `e.inverse` is an equivalence of categories of extensions.** -/
theorem isEquivalence_siteRestriction : (siteRestriction K e a M).IsEquivalence := by
  have : (siteExtensionFunctor K e a M).EssSurj :=
    ⟨fun P => ⟨(siteRestriction K e a M).obj P, ⟨((siteUnitIso K e a M).app P).symm⟩⟩⟩
  have : (siteExtensionFunctor K e a M).IsEquivalence := { }
  have : (siteRestriction K e a M ⋙ siteExtensionFunctor K e a M).IsEquivalence :=
    Functor.isEquivalence_of_iso (siteUnitIso K e a M)
  exact Functor.isEquivalence_of_comp_right _ (siteExtensionFunctor K e a M)

end Deformation.AlgebraExtension

end

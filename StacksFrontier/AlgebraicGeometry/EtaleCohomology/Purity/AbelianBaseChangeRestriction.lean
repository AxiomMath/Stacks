module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangePasteIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteMorphismBaseChange

/-!
# The underived abelian base change map at a restriction to an open

Let
```
U₀' --u₀--> U₀
|j'         |j
v           v
U'  --u'--> U
```
be a cartesian square of schemes with `j` (hence `j'`) an open immersion, and `F` an abelian sheaf
on `U₀_étale`. The base change map `u'⁻¹ j_* F ⟶ j'_* u₀⁻¹ F`
(`Stacks.EtaleCohomology.etaleAbelianBaseChange`) is invertible as soon as the unit of
`j'⁻¹ ⊣ j'_*` is invertible at its source: its target is a direct image along the open immersion
`j'`, which is fully faithful, and after `j'⁻¹` it is invertible, by pasting with base change maps
along open immersions and along an identity. This is the abelian form of
`Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_app_restriction`; for `F = j⁻¹ G` with
`G ⟶ j_* j⁻¹ G` invertible it is the degree-zero part of the base change of `R j_*(j⁻¹ G)`.

## Main results

* `Stacks.EtaleCohomology.isIso_inverseImage_map_etaleAbelianBaseChange_app_of_isOpenImmersion`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_app_of_isIso_unit`.
* `Stacks.EtaleCohomology.isIso_app_iff_of_eq_whisker_comp`: a transformation conjugated by
  isomorphisms of functors is invertible where the other one is.
* `Stacks.EtaleCohomology.isIso_of_isIso_unit_app_of_isIso_leftAdjoint_map`: a map into the
  image of a fully faithful right adjoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- A transformation which is another one conjugated by isomorphisms of functors is invertible at
an object exactly when the other one is. -/
theorem isIso_app_iff_of_eq_whisker_comp {A B B' C : Type*} [Category A] [Category B]
    [Category B'] [Category C] {F₁ : A ⥤ B} {G₁ G₂ : B ⥤ C} (ι : G₁ ≅ G₂) {H₁ H₂ : A ⥤ B'}
    {F₂ : B' ⥤ C} (ι' : H₁ ≅ H₂) (α : F₁ ⋙ G₂ ⟶ H₂ ⋙ F₂) (β : F₁ ⋙ G₁ ⟶ H₁ ⋙ F₂)
    (hβ : β = Functor.whiskerLeft F₁ ι.hom ≫ α ≫ Functor.whiskerRight ι'.inv F₂) (X : A) :
    IsIso (β.app X) ↔ IsIso (α.app X) := by
  subst hβ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  constructor
  · intro h
    have := IsIso.of_isIso_comp_left (ι.hom.app (F₁.obj X)) (α.app X ≫ F₂.map (ι'.inv.app X))
    exact IsIso.of_isIso_comp_right _ (F₂.map (ι'.inv.app X))
  · intro h
    infer_instance

/-- **A map into the image of a fully faithful right adjoint**: for an adjunction `L ⊣ R` with
invertible counit, a morphism `φ : A ⟶ R B` is invertible when the unit is invertible at `A` and
`L φ` is invertible. -/
theorem isIso_of_isIso_unit_app_of_isIso_leftAdjoint_map {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [IsIso adj.counit] {A : C} {B : D} (φ : A ⟶ R.obj B)
    (hA : IsIso (adj.unit.app A)) (hφ : IsIso (L.map φ)) : IsIso φ := by
  have hB : IsIso (adj.unit.app (R.obj B)) :=
    isIso_of_comp_hom_eq_id _ (adj.right_triangle_components B)
  have hn := adj.unit.naturality φ
  rw [CategoryTheory.Functor.id_map] at hn
  have : IsIso (φ ≫ adj.unit.app (R.obj B)) := by
    rw [hn]
    change IsIso (adj.unit.app A ≫ R.map (L.map φ))
    infer_instance
  exact IsIso.of_isIso_comp_right φ (adj.unit.app (R.obj B))

variable {U U₀ U' U₀' : Scheme.{u}} (j : U₀ ⟶ U) (j' : U₀' ⟶ U') (u' : U' ⟶ U) (u₀ : U₀' ⟶ U₀)

/-- **The inverse image along `j'` of the base change map of a cartesian square along open
immersions is invertible.** For `j`, `j'` open immersions and `U₀' = U₀ ×_U U'`, the base change
map `u'⁻¹ j_* F ⟶ j'_* u₀⁻¹ F` becomes invertible after `j'⁻¹`: pasted with the base change of
`j'` along itself (invertible, `j'` an open immersion) it is the base change of `j` along
`u₀ ≫ j`, which is that of `j` along itself (invertible) pasted with that of the identity of
`U₀` along `u₀` (invertible, the identity being finite). -/
theorem isIso_inverseImage_map_etaleAbelianBaseChange_app_of_isOpenImmersion
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback u₀ j' j u')
    (F : Sheaf U₀.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianInverseImage.{u, 0} j').map
      ((etaleAbelianBaseChange.{u, 0} j u' u₀ j' sq.w).app F)) := by
  have hself : ∀ {V W : Scheme.{u}} (k : V ⟶ W) [IsOpenImmersion k],
      IsIso (etaleAbelianBaseChange.{u, 0} k k (𝟙 V) (𝟙 V) (IsKernelPair.id_of_mono k).w) :=
    fun k _ => isIso_etaleAbelianBaseChange_of_isOpenImmersion.{u, 0} k k (𝟙 _) (𝟙 _)
      (IsKernelPair.id_of_mono k)
  have hsq₁ : IsPullback (𝟙 U₀) (𝟙 U₀) j j := IsKernelPair.id_of_mono j
  have hsq₂ : IsPullback u₀ (𝟙 U₀') (𝟙 U₀) u₀ := IsPullback.of_vert_isIso ⟨by simp⟩
  have h₂ : IsIso (etaleAbelianBaseChange.{u, 0} (𝟙 U₀) u₀ u₀ (𝟙 U₀') hsq₂.w) :=
    isIso_etaleAbelianBaseChange_of_isPullback_of_isFinite (𝟙 U₀) u₀ u₀ (𝟙 U₀') hsq₂
  have hyp : u₀ ≫ j = 𝟙 U₀' ≫ j' ≫ u' := sq.w.trans (Category.id_comp _).symm
  have hO : IsIso (etaleAbelianBaseChange.{u, 0} j (j' ≫ u') u₀ (𝟙 U₀') hyp) :=
    isIso_etaleAbelianBaseChange_of_paste.{u, 0} j j (𝟙 U₀) (𝟙 U₀) u₀ (𝟙 U₀') u₀ hsq₁.w hsq₂.w
      (j' ≫ u') sq.w.symm u₀ (Category.comp_id _).symm hyp (hself j) h₂
  have hsq₃ : IsPullback (𝟙 U₀') (𝟙 U₀') j' j' := IsKernelPair.id_of_mono j'
  exact isIso_inverseImage_map_etaleAbelianBaseChange_app_of_paste.{u, 0} u' j j' u₀ j' (𝟙 U₀')
    (𝟙 U₀') sq.w hsq₃.w (j' ≫ u') rfl u₀ (Category.id_comp _).symm hyp hO (hself j') F

/-- **The underived abelian base change map along open immersions, at a sheaf whose direct image
is local for `j'`.** For `j`, `j'` open immersions and `U₀' = U₀ ×_U U'`, the base change map
`u'⁻¹ j_* F ⟶ j'_* u₀⁻¹ F` is invertible as soon as the unit of `j'⁻¹ ⊣ j'_*` is invertible at
`u'⁻¹ j_* F`: its target is a direct image along `j'`, which is fully faithful, and it is
invertible after `j'⁻¹`. -/
theorem isIso_etaleAbelianBaseChange_app_of_isIso_unit [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback u₀ j' j u') (F : Sheaf U₀.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hA : IsIso ((etaleAbelianInverseImageDirectImageAdj.{u, 0} j').unit.app
      ((etaleAbelianInverseImage.{u, 0} u').obj ((etaleAbelianDirectImage.{u, 0} j).obj F)))) :
    IsIso ((etaleAbelianBaseChange.{u, 0} j u' u₀ j' sq.w).app F) :=
  isIso_of_isIso_unit_app_of_isIso_leftAdjoint_map
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} j') _ hA
    (isIso_inverseImage_map_etaleAbelianBaseChange_app_of_isOpenImmersion j j' u' u₀ sq F)

end Stacks.EtaleCohomology

end

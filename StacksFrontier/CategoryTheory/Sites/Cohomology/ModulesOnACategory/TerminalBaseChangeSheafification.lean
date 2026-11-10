module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TerminalBaseChangeCorepresentation
public import StacksFrontier.CategoryTheory.Sites.DenseSubsiteSheafifySections
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify

/-!
# Sheaves with prescribed sections over a terminal object of a dense subsite

On a site with a terminal object lying in a dense cocontinuous subsite on which the base changes
`O ⊗_{O(X)} M` are sheaves, every `O(X)`-module `M` is the module of sections over `X` of a sheaf
of modules: the sheafification of `O ⊗_{O(X)} M`. Also: a morphism of presheaves of abelian groups
surjective over a covering family of objects is locally surjective.

## Main results

* `Stacks.TerminalBaseChange.isLocallySurjective_of_surjective_app_of_generate_mem`.
* `Stacks.TerminalBaseChange.exists_isSheaf_obj_iso_of_isDenseSubsite`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v₁ u₁ v₂ u₂ r

namespace Stacks.TerminalBaseChange

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- A morphism of presheaves of abelian groups which is surjective over a family of objects
covering every object of the site is locally surjective. -/
theorem isLocallySurjective_of_surjective_app_of_generate_mem {F₁ F₂ : Cᵒᵖ ⥤ AddCommGrpCat.{t}}
    (φ : F₁ ⟶ F₂) (𝒰 : C → Prop)
    (hcov : ∀ X : C, Sieve.generate (fun Z (_ : Z ⟶ X) => 𝒰 Z) ∈ J X)
    (hsurj : ∀ Z, 𝒰 Z → Function.Surjective (φ.app (op Z))) :
    Presheaf.IsLocallySurjective J φ where
  imageSieve_mem {X} s := by
    refine J.superset_covering ?_ (hcov X)
    rintro Y f ⟨Z, h, g, hZ, rfl⟩
    obtain ⟨x, hx⟩ := hsurj Z hZ (F₂.map g.op s)
    refine ⟨F₁.map h.op x, ?_⟩
    rw [NatTrans.naturality_apply, hx]
    change F₂.map h.op (F₂.map g.op s) = F₂.map (h ≫ g).op s
    rw [op_comp, F₂.map_comp, ConcreteCategory.comp_apply]

variable {D : Type u₂} [Category.{v₂} D] {J' : GrothendieckTopology D}
  (R : Sheaf J RingCat.{r}) [CommSections R.obj] (I : D ⥤ C) [I.IsCocontinuous J' J]
  [I.IsDenseSubsite J' J] {X' : D} (hX : IsTerminal (I.obj X'))
  [HasWeakSheafify J AddCommGrpCat.{max t r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max t r}]
  [J'.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max t r})]

/-- **Every module over the sections at the terminal object is the module of sections of a
sheaf**, when the terminal object lies in a dense cocontinuous subsite on which the base changes
`O ⊗_{O(X)} M` are already sheaves: the sheafification of `O ⊗_{O(X)} M` does not change its
sections over objects of the subsite, and its sections over the terminal object are `M`. -/
theorem exists_isSheaf_obj_iso_of_isDenseSubsite
    (hL : ∀ Y : ModuleCat.{max t r} (R.obj.obj (op (I.obj X'))),
      Presheaf.IsSheaf J' (I.op ⋙ ((baseChangePresheaf.{t} R.obj hX).obj Y).presheaf))
    (Y : ModuleCat.{max t r} (R.obj.obj (op (I.obj X')))) :
    ∃ Q : PresheafOfModules.{max t r} R.obj, Presheaf.IsSheaf J Q.presheaf ∧
      Nonempty (Q.obj (op (I.obj X')) ≅ Y) := by
  let M₀ := (baseChangePresheaf.{t} R.obj hX).obj Y
  let φ := toSheafify J M₀.presheaf
  have : Presheaf.IsLocallyInjective J φ := (J.W_toSheafify M₀.presheaf).isLocallyInjective
  have : Presheaf.IsLocallySurjective J φ := (J.W_toSheafify M₀.presheaf).isLocallySurjective
  let S := PresheafOfModules.sheafify (𝟙 R.obj) (A := (presheafToSheaf J _).obj M₀.presheaf) φ
  refine ⟨S.val, S.isSheaf, ?_⟩
  let f : M₀.obj (op (I.obj X')) ⟶ S.val.obj (op (I.obj X')) :=
    ((PresheafOfModules.toSheafify (𝟙 R.obj) φ).app (op (I.obj X'))) ≫
      (ModuleCat.restrictScalarsId'.{max t r} _ RingCat.hom_id).hom.app _
  have hf : IsIso f := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (ConcreteCategory.isIso_iff_bijective (φ.app (op (I.obj X')))).mp
      (Presheaf.isIso_toSheafify_app_of_isDenseSubsite J' J I M₀.presheaf (hL Y) X')
  have hY : ∀ g : R.obj.obj (op (I.obj X')) →+* R.obj.obj (op (I.obj X')),
      g = RingHom.id _ → Nonempty ((ModuleCat.extendScalars.{r, r, max t r} g).obj Y ≅ Y) := by
    rintro g rfl
    exact ⟨(ModuleCat.extendScalarsId _).app Y⟩
  obtain ⟨e⟩ := hY _ (rho_self R.obj hX)
  exact ⟨(asIso f).symm ≪≫ e⟩

end Stacks.TerminalBaseChange

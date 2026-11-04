module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheaf

/-!
# The presheaf of components of a base change

Let `eA : 𝒜 ⥤ 𝒮` and `eB : ℬ ⥤ 𝒮` be morphisms of categories fibred in groupoids over `𝒞`, and let
`fst : 𝒜 ×_𝒮 ℬ ⥤ 𝒜` be the first projection of their 2-fibre product. The presheaf of components
of `fst`, a presheaf of sets on `𝒜`, is the pullback along `eA` of the presheaf of components of
`eB`: for an object `a` of `𝒜` the components of arrows `a ⟶ fst(ξ)` are the components of arrows
`eA(a) ⟶ eB(b)`. The comparison sends the class of `φ : a ⟶ ξ.x` to the class of
`eA(φ) ≫ ξ.iso`.

For `eB` the 1-morphism `y : (Sch/V) ⟶ 𝒴` named by an object `y` of a category fibred in
groupoids `𝒴`, the presheaf of components of `eB` is the representable presheaf of `y`, so the
presheaf of components of the projection `V ×_{y, 𝒴} 𝒳 ⥤ 𝒳` is `x ↦ Hom(f x, y)`.

## Main definitions

* `Stacks.Sites.CoverDescent.componentPresheafPost`: the map `Ψ(z) ⟶ e^* Ψ(z ⋙ e)` induced by a
  functor `e`.
* `Stacks.Sites.CoverDescent.componentPresheafFstHom`: the comparison
  `Ψ(fst) ⟶ eA^* Ψ(eB)`.

## Main results

* `Stacks.Sites.CoverDescent.bijective_componentPresheafFstHom`: the comparison is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace Stacks.Sites.CoverDescent

section Post

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {𝒵 : Type u₂} [Category.{v₂} 𝒵]
  {𝒮 : Type u₃} [Category.{v₁} 𝒮]

/-- **The map `Ψ(z) ⟶ e^* Ψ(z ⋙ e)` induced by a functor `e`**: the class of an arrow `a ⟶ z(ζ)`
goes to the class of its image `e(a) ⟶ e(z(ζ))`. -/
@[simps]
def componentPresheafPost (z : 𝒵 ⥤ 𝒜) (e : 𝒜 ⥤ 𝒮) :
    componentPresheaf z ⟶ e.op ⋙ componentPresheaf (z ⋙ e) where
  app a := ↾Quotient.map (StructuredArrow.post a.unop z e).obj
    (fun _ _ => zigzag_obj_of_zigzag (StructuredArrow.post a.unop z e))
  naturality a a' g := TypeCat.homEquiv.injective (funext fun c => by
    induction c using Quotient.inductionOn with
    | h x =>
      exact congrArg (Quotient.mk _) (by
        simp only [StructuredArrow.post_obj, StructuredArrow.map_mk, Functor.op_map,
          Quiver.Hom.unop_op, StructuredArrow.map_obj_hom, Functor.map_comp]))

/-- The map `componentPresheafPost z e` sends the class of `φ : a ⟶ z(ζ)` to the class of
`e(φ)`. -/
@[simp]
lemma componentPresheafPost_mk (z : 𝒵 ⥤ 𝒜) (e : 𝒜 ⥤ 𝒮) {a : 𝒜} {ζ : 𝒵} (φ : a ⟶ z.obj ζ) :
    (componentPresheafPost z e).app (op a) (componentMk z φ) = componentMk (z ⋙ e) (e.map φ) :=
  rfl

end Post

section BaseChange

variable {𝒞 : Type (v₂ + 1)} [Category.{v₂} 𝒞] {𝒜 ℬ 𝒮 : Type (v₂ + 1)} [Category.{v₂} 𝒜]
  [Category.{v₂} ℬ] [Category.{v₂} 𝒮] (pA : 𝒜 ⥤ 𝒞) (pB : ℬ ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞)
  (eA : 𝒜 ⥤ 𝒮) (eB : ℬ ⥤ 𝒮)

/-- **The comparison of the presheaf of components of the first projection of a 2-fibre product
with the pullback of the presheaf of components of the second leg.** The class of
`φ : a ⟶ ξ.x` goes to the class of `eA(φ) ≫ ξ.iso`. -/
def componentPresheafFstHom :
    componentPresheaf (TwoFibreProductOver.fst pA pB pS eA eB) ⟶
      eA.op ⋙ componentPresheaf eB :=
  componentPresheafPost (TwoFibreProductOver.fst pA pB pS eA eB) eA ≫
    Functor.whiskerLeft eA.op (componentPresheafMapOfNatTrans
      (TwoFibreProductOver.snd pA pB pS eA eB) eB (TwoFibreProductOver.psi pA pB pS eA eB))

/-- The comparison `componentPresheafFstHom` sends the class of `φ : a ⟶ ξ.x` to the class of
`eA(φ) ≫ ξ.iso`. -/
lemma componentPresheafFstHom_mk {a : 𝒜} (ξ : TwoFibreProductOver pA pB pS eA eB)
    (φ : a ⟶ ξ.x) :
    (componentPresheafFstHom pA pB pS eA eB).app (op a)
        (componentMk (TwoFibreProductOver.fst pA pB pS eA eB) φ) =
      componentMk eB (eA.map φ ≫ ξ.iso.hom) := rfl

/-- An arrow of a category fibred in groupoids lying over an identity is an isomorphism. -/
private theorem isIso_of_isHomLift_id {𝒳 𝒴 : Type (v₂ + 1)} [Category.{v₂} 𝒳] [Category.{v₂} 𝒴]
    (p : 𝒳 ⥤ 𝒴) (hp : p.IsFiberedInGroupoids) {x x' : 𝒳} (φ : x ⟶ x')
    [p.IsHomLift (𝟙 (p.obj x)) φ] : IsIso φ := by
  have : p.IsStronglyCartesian (𝟙 (p.obj x)) φ := hp.isStronglyCartesian_homLift _ _
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (p.obj x)) φ

/-- **The presheaf of components of the first projection of a 2-fibre product of categories
fibred in groupoids is the pullback of the presheaf of components of the second leg**: each
component of the comparison `componentPresheafFstHom` is bijective. -/
lemma bijective_componentPresheafFstHom (hA : pA.IsFiberedInGroupoids)
    (hB : pB.IsFiberedInGroupoids) (hS : pS.IsFiberedInGroupoids)
    (hpA : eA ⋙ pS = pA) (hpB : eB ⋙ pS = pB) (a : 𝒜ᵒᵖ) :
    Function.Bijective ((componentPresheafFstHom pA pB pS eA eB).app a) := by
  subst hpA hpB
  obtain ⟨a⟩ := a
  have hP : (TwoFibreProductOver.fst (eA ⋙ pS) (eB ⋙ pS) pS eA eB ⋙ eA ⋙ pS).IsFiberedInGroupoids
      := by
    have := TwoFibreProductOver.isFiberedInGroupoids (eA ⋙ pS) (eB ⋙ pS) pS eA eB hA hB hS rfl rfl
    rwa [← TwoFibreProductOver.fst_comp_eq] at this
  have hex : ∀ c, ∃ (ξ : TwoFibreProductOver (eA ⋙ pS) (eB ⋙ pS) pS eA eB)
      (φ : a ⟶ ξ.x), (eA ⋙ pS).IsHomLift (𝟙 ((eA ⋙ pS).obj a)) φ ∧
      componentMk (TwoFibreProductOver.fst (eA ⋙ pS) (eB ⋙ pS) pS eA eB) φ = c :=
    exists_vertical_componentMk _ (eA ⋙ pS) hA hP
  refine ⟨fun c₁ c₂ h => ?_, fun c => ?_⟩
  · obtain ⟨ξ₁, φ₁, hφ₁, rfl⟩ := hex c₁
    obtain ⟨ξ₂, φ₂, hφ₂, rfl⟩ := hex c₂
    have hv : ∀ (ξ : TwoFibreProductOver (eA ⋙ pS) (eB ⋙ pS) pS eA eB) (φ : a ⟶ ξ.x),
        (eA ⋙ pS).IsHomLift (𝟙 ((eA ⋙ pS).obj a)) φ →
        pS.IsHomLift (𝟙 (pS.obj (eA.obj a))) (eA.map φ ≫ ξ.iso.hom) := by
      intro ξ φ hφ
      have : pS.IsHomLift (𝟙 (pS.obj (eA.obj a))) (eA.map φ) :=
        PresheafOfCategories.isHomLift_map_of_comp rfl _ _ hφ
      have := ξ.vertical
      exact IsHomLift.comp_lift_id_right' pS (𝟙 (pS.obj (eA.obj a))) (eA.map φ) ξ.base _
    have := hv ξ₁ φ₁ hφ₁
    have := hv ξ₂ φ₂ hφ₂
    obtain ⟨β, hβ⟩ := exists_comp_eq_of_componentMk_eq eB pS hS hB
      (eA.map φ₁ ≫ ξ₁.iso.hom) (eA.map φ₂ ≫ ξ₂.iso.hom) h
    have : IsIso φ₁ := isIso_of_isHomLift_id (eA ⋙ pS) hA φ₁
    let α : ξ₁.x ⟶ ξ₂.x := inv φ₁ ≫ φ₂
    have hα : φ₁ ≫ α = φ₂ := by simp [α]
    have hw : eA.map α ≫ ξ₂.iso.hom = ξ₁.iso.hom ≫ eB.map β := by
      apply (cancel_epi (eA.map φ₁)).1
      rw [← Category.assoc, ← eA.map_comp, hα, ← hβ, Category.assoc]
    have hbase : eqToHom ξ₁.hy.symm ≫ (eB ⋙ pS).map β ≫ eqToHom ξ₂.hy =
        eqToHom ξ₁.hx.symm ≫ (eA ⋙ pS).map α ≫ eqToHom ξ₂.hx := by
      have hι : ∀ ξ : TwoFibreProductOver (eA ⋙ pS) (eB ⋙ pS) pS eA eB,
          pS.map ξ.iso.hom = eqToHom (ξ.hx.trans ξ.hy.symm) := fun ξ => by
        have := ξ.vertical
        simp [IsHomLift.fac' pS (𝟙 ξ.base) ξ.iso.hom]
      have k := congrArg pS.map hw
      simp only [Functor.map_comp, hι] at k
      have key : pS.map (eB.map β) =
          eqToHom (ξ₁.hx.trans ξ₁.hy.symm).symm ≫ pS.map (eA.map α) ≫
            eqToHom (ξ₂.hx.trans ξ₂.hy.symm) := by
        simp [k]
      simp [key]
    exact Quot.sound (Zigzag.of_hom
      (StructuredArrow.homMk (TwoFibreProductOver.Hom.mk' α β hbase hw) hα))
  · obtain ⟨b, χ, hχ, rfl⟩ := exists_vertical_componentMk eB pS hS hB c
    have : IsIso χ := isIso_of_isHomLift_id pS hS χ
    let ξ : TwoFibreProductOver (eA ⋙ pS) (eB ⋙ pS) pS eA eB :=
      { base := (eA ⋙ pS).obj a
        x := a
        y := b
        hx := rfl
        hy := IsHomLift.codomain_eq pS (𝟙 (pS.obj (eA.obj a))) χ
        iso := asIso χ
        vertical := hχ }
    refine ⟨componentMk (TwoFibreProductOver.fst (eA ⋙ pS) (eB ⋙ pS) pS eA eB) (ζ := ξ) (𝟙 a), ?_⟩
    show componentMk eB (eA.map (𝟙 a) ≫ χ) = componentMk eB χ
    rw [eA.map_id, Category.id_comp]

end BaseChange

end Stacks.Sites.CoverDescent

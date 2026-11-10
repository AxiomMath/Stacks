module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NewShriekNormalizedNagata

/-!
# `f_new^!` is a pseudofunctor on `D^+_Coh` of schemes of finite type over the base

In Situation [Stacks, Tag 0AU4] (`S` Noetherian with a dualizing complex `ω_S^•`), let `ω_X^•`
be the dualizing complex normalized relative to `ω_S^•`
(`Stacks.Duality.normalizedDualizingComplex`, for the upper shriek functors of Nagata
compactifications) of each scheme `X` of finite type over `S`, `D_X = R𝓗om(-, ω_X^•)` and
`f_new^! = D_X ∘ Lf^* ∘ D_Y`. Part (1) of [Stacks, Tag 0AUE]: the functors
`f_new^! : D^+_Coh(𝒪_Y) ⥤ D^+_Coh(𝒪_X)`, the arrows `(g ∘ f)_new^! ⟶ f_new^! ∘ g_new^!` and
the identifications `(id_X)_new^! ≅ id` form a pseudofunctor from the category of schemes of
finite type over `S` to the 2-category of categories.

The arrows are the inverses of the comparisons `Stacks.Duality.fNewShriekCompHom` (biduality
`η_Y` of [Stacks, Tag 0A89] after the composition isomorphism of `L(-)^*`), invertible on
`D^+_Coh` by `Stacks.Duality.isIso_fNewShriekCompHom_app`; the coherence is
`Stacks.Duality.fNewShriekCompHom_assoc` and the two unit laws
`Stacks.Duality.map_fNewShriekUnitHom_comp_fNewShriekCompHom` and
`Stacks.Duality.fNewShriekUnitHom_comp_fNewShriekCompHom`.

## Main definitions

* `Stacks.Duality.SchemesOfFiniteTypeOver`: the category of schemes of finite type over `S`.
* `Stacks.Duality.newShriekPseudofunctor`: the pseudofunctor `X ↦ D^+_Coh(𝒪_X)`, `f ↦ f_new^!`.

## References

* [Stacks Project, Tag 0AUE](https://stacks.math.columbia.edu/tag/0AUE)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u u₁ u₂ v₁ v₂

namespace Stacks.Duality

open Stacks.Duality.TwistedInverseImageDuality (Std pull plusCoh IsDualizing stdMonoidal
  stdSymmetric stdMonoidalClosed)
open CategoryTheory.MonoidalClosed (dualInto)

attribute [local instance] stdMonoidal stdSymmetric stdMonoidalClosed

/-- Morphisms of finite type: locally of finite type and quasi-compact. -/
def finiteTypeMorphisms : MorphismProperty Scheme.{u} :=
  @LocallyOfFiniteType ⊓ @QuasiCompact

/-- The category of schemes of finite type over `S`: schemes over `S` whose structure morphism is
locally of finite type and quasi-compact, with all morphisms over `S`. -/
abbrev SchemesOfFiniteTypeOver (S : Scheme.{u}) : Type (u + 1) :=
  finiteTypeMorphisms.Over ⊤ S

/-! ### Pseudofunctors on full subcategories from lax comparisons -/

namespace PseudofunctorOfComparisons

variable {B : Type u₁} [Category.{v₁} B] {T : B → Type u₂} [hT : ∀ b, Category.{v₂} (T b)]
  (P : ∀ b, ObjectProperty (T b)) (Φ : ∀ {b b' : B}, (b ⟶ b') → (T b ⥤ T b'))
  (hΦ : ∀ {b b' : B} (f : b ⟶ b') (M : T b), P b M → P b' ((Φ f).obj M))
  (u : ∀ b, 𝟭 (T b) ⟶ Φ (𝟙 b))
  (c : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂), Φ f ⋙ Φ g ⟶ Φ (f ≫ g))
  (hu : ∀ b (M : T b), P b M → IsIso ((u b).app M))
  (hc : ∀ {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (M : T b₀), P b₀ M →
    IsIso ((c f g).app M))

/-- The functor `Φ f` restricted to the full subcategories. -/
abbrev mapFun {b b' : B} (f : b ⟶ b') : (P b).FullSubcategory ⥤ (P b').FullSubcategory :=
  ObjectProperty.lift (P b') ((P b).ι ⋙ Φ f) (fun M => hΦ f M.obj M.property)

/-- The inverse of the unit `u`, on the full subcategory. -/
def mapIdIso (b : B) : mapFun P Φ hΦ (𝟙 b) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M => ((P b).isoMk (@asIso _ _ _ _ ((u b).app M.obj) (hu b M.obj M.property))).symm)
    (fun {M N} φ => ObjectProperty.hom_ext _ (by
      have := hu b M.obj M.property
      have := hu b N.obj N.property
      change (Φ (𝟙 b)).map φ.hom ≫ inv ((u b).app N.obj) = inv ((u b).app M.obj) ≫ φ.hom
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact ((u b).naturality φ.hom).symm))

/-- The inverse of the comparison `c`, on the full subcategories. -/
def mapCompIso {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    mapFun P Φ hΦ (f ≫ g) ≅ mapFun P Φ hΦ f ⋙ mapFun P Φ hΦ g :=
  NatIso.ofComponents
    (fun M => ((P b₂).isoMk
      (@asIso _ _ _ _ ((c f g).app M.obj) (hc f g M.obj M.property))).symm)
    (fun {M N} φ => ObjectProperty.hom_ext _ (by
      have := hc f g M.obj M.property
      have := hc f g N.obj N.property
      change (Φ (f ≫ g)).map φ.hom ≫ inv ((c f g).app N.obj) =
        inv ((c f g).app M.obj) ≫ (Φ g).map ((Φ f).map φ.hom)
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact ((c f g).naturality φ.hom).symm))

/-- The underlying morphism of `eqToHom h` in a full subcategory is `eqToHom` of the underlying
objects. -/
theorem eqToHom_hom {C : Type*} [Category C] {Q : ObjectProperty C} {X Y : Q.FullSubcategory}
    (h : X = Y) : (eqToHom h).hom = eqToHom (congrArg ObjectProperty.FullSubcategory.obj h) := by
  subst h
  rfl

variable
  (hassoc : ∀ {b₀ b₁ b₂ b₃ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) (M : T b₀),
    P b₀ M →
    (Φ h).map ((c f g).app M) ≫ (c (f ≫ g) h).app M ≫
        eqToHom (congrArg (fun k => (Φ k).obj M) (Category.assoc f g h)) =
      (c g h).app ((Φ f).obj M) ≫ (c f (g ≫ h)).app M)
  (hleft : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁) (M : T b₀), P b₀ M →
    (Φ f).map ((u b₀).app M) ≫ (c (𝟙 b₀) f).app M =
      eqToHom (congrArg (fun k => (Φ k).obj M) (Category.id_comp f).symm))
  (hright : ∀ {b₀ b₁ : B} (f : b₀ ⟶ b₁) (M : T b₀), P b₀ M →
    (u b₁).app ((Φ f).obj M) ≫ (c f (𝟙 b₁)).app M =
      eqToHom (congrArg (fun k => (Φ k).obj M) (Category.comp_id f).symm))

/-- **A pseudofunctor from lax comparisons invertible on full subcategories**: functors
`Φ f : T b ⥤ T b'` preserving full subcategories `P b`, with a unit `𝟭 ⟶ Φ (𝟙 b)` and
comparisons `Φ f ⋙ Φ g ⟶ Φ (f ≫ g)` which are invertible on the `P b` and satisfy associativity
and the two unit laws, restrict to a pseudofunctor `b ↦ P b`. -/
def pseudofunctor : Pseudofunctor (LocallyDiscrete B) Cat :=
  LocallyDiscrete.mkPseudofunctor (fun b => Cat.of (P b).FullSubcategory)
    (fun f => (mapFun P Φ hΦ f).toCatHom)
    (fun b => Cat.Hom.isoMk (mapIdIso P Φ hΦ u hu b))
    (fun f g => Cat.Hom.isoMk (mapCompIso P Φ hΦ c hc f g))
    (fun f g h => by
      ext M
      have := hc (f ≫ g) h M.obj M.property
      have := hc f g M.obj M.property
      have := hc g h ((Φ f).obj M.obj) (hΦ f M.obj M.property)
      have := hc f (g ≫ h) M.obj M.property
      have H := hassoc f g h M.obj M.property
      apply ObjectProperty.hom_ext
      simp only [Cat.of_α, Functor.toCatHom_toFunctor, ObjectProperty.lift_obj_obj,
        Functor.comp_obj, ObjectProperty.ι_obj, mapCompIso, Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv,
        Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor, NatTrans.toCatHom₂_toNatTrans,
        Cat.whiskerRight_toNatTrans, Cat.associator_hom_toNatTrans, Cat.whiskerLeft_toNatTrans,
        NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.symm_hom, ObjectProperty.isoMk_inv,
        asIso_inv, Functor.whiskerRight_app, ObjectProperty.lift_map, Functor.comp_map,
        ObjectProperty.ι_map, ObjectProperty.homMk_hom, Functor.map_inv, Functor.associator_hom_app,
        Functor.whiskerLeft_app, NatIso.ofComponents_inv_app, Iso.symm_inv,
        ObjectProperty.isoMk_hom, asIso_hom, Category.id_comp,
        ObjectProperty.FullSubcategory.comp_hom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
        ObjectProperty.eqToHom_hom, IsIso.inv_comp_eq]
      exact H.symm)
    (fun f => by
      ext M
      have := hu _ M.obj M.property
      have := hc (𝟙 _) f M.obj M.property
      have H := hleft f M.obj M.property
      apply ObjectProperty.hom_ext
      simp only [Cat.of_α, Functor.toCatHom_toFunctor, ObjectProperty.lift_obj_obj,
        Functor.comp_obj, ObjectProperty.ι_obj, mapCompIso, Cat.Hom.isoMk_hom, mapIdIso,
        Functor.id_obj, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
        NatTrans.toCatHom₂_toNatTrans, Cat.Hom.id_toFunctor, Cat.whiskerRight_toNatTrans,
        Cat.leftUnitor_hom_toNatTrans, NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.symm_hom,
        ObjectProperty.isoMk_inv, asIso_inv, Functor.whiskerRight_app, ObjectProperty.lift_map,
        Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.homMk_hom, Functor.map_inv,
        Functor.leftUnitor_hom_app, Category.comp_id, ObjectProperty.FullSubcategory.comp_hom,
        Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, ObjectProperty.eqToHom_hom, IsIso.comp_inv_eq]
      apply IsIso.inv_eq_of_hom_inv_id
      rw [← cancel_epi ((Φ f).map ((u _).app M.obj)), reassoc_of% H]
      simp)
    (fun f => by
      ext M
      have := hu _ ((Φ f).obj M.obj) (hΦ f _ M.property)
      have := hc f (𝟙 _) M.obj M.property
      have H := hright f M.obj M.property
      apply ObjectProperty.hom_ext
      simp only [Cat.of_α, Functor.toCatHom_toFunctor, ObjectProperty.lift_obj_obj,
        Functor.comp_obj, ObjectProperty.ι_obj, mapCompIso, Cat.Hom.isoMk_hom, mapIdIso,
        Functor.id_obj, Cat.Hom.toNatTrans_comp, Cat.Hom.comp_toFunctor,
        NatTrans.toCatHom₂_toNatTrans, Cat.Hom.id_toFunctor, Cat.whiskerLeft_toNatTrans,
        Cat.rightUnitor_hom_toNatTrans, NatTrans.comp_app, NatIso.ofComponents_hom_app,
        Iso.symm_hom, ObjectProperty.isoMk_inv, asIso_inv, Functor.whiskerLeft_app,
        Functor.rightUnitor_hom_app, Category.comp_id, ObjectProperty.FullSubcategory.comp_hom,
        ObjectProperty.homMk_hom, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
        ObjectProperty.eqToHom_hom, IsIso.comp_inv_eq]
      apply IsIso.inv_eq_of_hom_inv_id
      rw [← cancel_epi ((u _).app ((Φ f).obj M.obj)), reassoc_of% H]
      simp)

end PseudofunctorOfComparisons

/-! ### The comparisons, at the standard model -/

section Comparisons

variable {X Y Z : Scheme.{u}}

/-- The unit comparison `id ⟶ g_new^!` for an endomorphism `g` equal to the identity. -/
def fNewShriekUnitHomOfEq {g : Y ⟶ Y} (hg : g = 𝟙 Y) (ωY : Std Y) :
    𝟭 (Std Y) ⟶ dualConj (dualInto ωY) (dualInto ωY) (pull g) := by
  subst hg
  exact fNewShriekUnitHom ωY

/-- The unit comparison `id ⟶ g_new^!` for `g = 𝟙 Y` is an isomorphism at every object with
coherent cohomology sheaves, when `ω_Y^•` is dualizing. -/
theorem isIso_fNewShriekUnitHomOfEq_app [IsLocallyNoetherian Y] {g : Y ⟶ Y} (hg : g = 𝟙 Y)
    {ωY : Std Y} (hωY : IsDualizing ωY) (M : Std Y)
    (hM : ∀ i : ℤ, ((@DerivedCategory.homologyFunctor Y.Modules _ _
      (HasDerivedCategory.standard Y.Modules) i).obj M).IsCoherent) :
    IsIso ((fNewShriekUnitHomOfEq hg ωY).app M) := by
  subst hg
  exact isIso_fNewShriekUnitHom_app hωY M hM

/-- The right unit law, for `g = 𝟙` and a spelling `k = f` of `f ≫ g`. -/
theorem map_fNewShriekUnitHomOfEq_comp_fNewShriekCompHom {f : X ⟶ Y} {g : Y ⟶ Y} {k : X ⟶ Y}
    (hg : g = 𝟙 Y) (e : f ≫ g = k) (hk : f = k) (ωX : Std X) (ωY : Std Y) (M : Std Y)
    (p : (dualConj (dualInto ωX) (dualInto ωY) (pull f)).obj M =
      (dualConj (dualInto ωX) (dualInto ωY) (pull k)).obj M) :
    (dualConj (dualInto ωX) (dualInto ωY) (pull f)).map ((fNewShriekUnitHomOfEq hg ωY).app M) ≫
      (fNewShriekCompHom e ωX ωY ωY).app M = eqToHom p := by
  subst hg hk
  rw [eqToHom_refl]
  exact map_fNewShriekUnitHom_comp_fNewShriekCompHom e ωX ωY M

/-- The left unit law, for `f = 𝟙` and a spelling `k = g` of `f ≫ g`. -/
theorem fNewShriekUnitHomOfEq_comp_fNewShriekCompHom {f : Y ⟶ Y} {g : Y ⟶ Z} {k : Y ⟶ Z}
    (hf : f = 𝟙 Y) (e : f ≫ g = k) (hk : g = k) (ωY : Std Y) (ωZ : Std Z) (M : Std Z)
    (p : (dualConj (dualInto ωY) (dualInto ωZ) (pull g)).obj M =
      (dualConj (dualInto ωY) (dualInto ωZ) (pull k)).obj M) :
    (fNewShriekUnitHomOfEq hf ωY).app ((dualConj (dualInto ωY) (dualInto ωZ) (pull g)).obj M) ≫
      (fNewShriekCompHom e ωY ωY ωZ).app M = eqToHom p := by
  subst hf hk
  rw [eqToHom_refl]
  exact fNewShriekUnitHom_comp_fNewShriekCompHom e ωY ωZ M

/-- Associativity of the comparisons `Stacks.Duality.fNewShriekCompHom`, for two spellings
`k = k'` of the triple composite. -/
theorem fNewShriekCompHom_assoc_eqToHom {T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z ⟶ T}
    {k₁ : X ⟶ Z} {k₂ : Y ⟶ T} {k k' : X ⟶ T} (e₁ : f ≫ g = k₁) (e₂ : g ≫ h = k₂)
    (e₃ : k₁ ≫ h = k') (e₄ : f ≫ k₂ = k) (hk : k = k') (ωX : Std X) (ωY : Std Y) (ωZ : Std Z)
    (ωT : Std T) (M : Std T)
    (p : (dualConj (dualInto ωX) (dualInto ωT) (pull k)).obj M =
      (dualConj (dualInto ωX) (dualInto ωT) (pull k')).obj M) :
    (dualConj (dualInto ωX) (dualInto ωY) (pull f)).map ((fNewShriekCompHom e₂ ωY ωZ ωT).app M) ≫
        (fNewShriekCompHom e₄ ωX ωY ωT).app M ≫ eqToHom p =
      (fNewShriekCompHom e₁ ωX ωY ωZ).app ((dualConj (dualInto ωZ) (dualInto ωT) (pull h)).obj M) ≫
        (fNewShriekCompHom e₃ ωX ωZ ωT).app M := by
  subst hk
  rw [eqToHom_refl, Category.comp_id]
  exact fNewShriekCompHom_assoc e₁ e₂ e₃ e₄ ωX ωY ωZ ωT M

end Comparisons

/-! ### The pseudofunctor -/

namespace NewShriekPseudofunctor

variable {S : Scheme.{u}} [IsNoetherian S] (ωS : quasiCoherentDerivedCategoryPlusOfModel S)
  (hωS : IsDualizingComplex ωS.obj.obj)

/-- An object of `SchemesOfFiniteTypeOver S` is of finite type over the Noetherian `S`. -/
theorem isFiniteTypeOverNoetherian (A : SchemesOfFiniteTypeOver S) :
    IsFiniteTypeOverNoetherian A.hom :=
  ⟨inferInstanceAs (IsNoetherian S), A.prop.1, A.prop.2⟩

/-- A scheme of finite type over the Noetherian `S` is Noetherian. -/
instance (A : SchemesOfFiniteTypeOver S) : IsNoetherian A.left :=
  (isFiniteTypeOverNoetherian A).source_noetherian

/-- The dualizing complex `ω_A^•` normalized relative to `ω_S^•`. -/
abbrev normalized (A : SchemesOfFiniteTypeOver S) :
    NormalizedOnOpens UpperShriek.nagata (isFiniteTypeOverNoetherian A) ωS :=
  normalizedDualizingComplex (isFiniteTypeOverNoetherian A) ωS hωS

/-- `ω_A^•` read at the standard model. -/
abbrev omega (A : SchemesOfFiniteTypeOver S) : Std A.left :=
  NormalizedOnOpens.stdComplex nagataCompactification (normalized ωS hωS A)

/-- `ω_A^•` is a dualizing complex. -/
theorem isDualizing_omega (A : SchemesOfFiniteTypeOver S) : IsDualizing (omega ωS hωS A) :=
  NormalizedOnOpens.isDualizing_stdComplex nagataCompactification hωS
    (normalized ωS hωS A)

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The morphism of schemes underlying a composite in `(SchemesOfFiniteTypeOver S)ᵒᵖ` is the
composite in reverse order. -/
theorem comp_unop_left {b₀ b₁ b₂ : (SchemesOfFiniteTypeOver S)ᵒᵖ} (a : b₀ ⟶ b₁) (a' : b₁ ⟶ b₂) :
    a'.unop.left ≫ a.unop.left = (a ≫ a').unop.left :=
  rfl

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The morphism of schemes underlying the identity of `(SchemesOfFiniteTypeOver S)ᵒᵖ` is the
identity. -/
theorem unop_id_left (b : (SchemesOfFiniteTypeOver S)ᵒᵖ) : (𝟙 b).unop.left = 𝟙 b.unop.left :=
  rfl

/-- The unit comparison at `b`. -/
abbrev unit (b : (SchemesOfFiniteTypeOver S)ᵒᵖ) :
    𝟭 (Std b.unop.left) ⟶ fNewShriekStd (𝟙 b).unop.left (omega ωS hωS b.unop)
      (omega ωS hωS b.unop) :=
  fNewShriekUnitHomOfEq (unop_id_left b) (omega ωS hωS b.unop)

/-- The comparison `f_new^! ∘ g_new^! ⟶ (g ∘ f)_new^!`. -/
abbrev comp {b₀ b₁ b₂ : (SchemesOfFiniteTypeOver S)ᵒᵖ} (a : b₀ ⟶ b₁) (a' : b₁ ⟶ b₂) :
    fNewShriekStd a.unop.left (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop) ⋙
        fNewShriekStd a'.unop.left (omega ωS hωS b₂.unop) (omega ωS hωS b₁.unop) ⟶
      fNewShriekStd (a ≫ a').unop.left (omega ωS hωS b₂.unop) (omega ωS hωS b₀.unop) :=
  fNewShriekCompHom (comp_unop_left a a')
    (omega ωS hωS b₂.unop) (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop)

/-- Associativity of the comparisons, with the two spellings of the triple composite. -/
theorem comp_assoc {b₀ b₁ b₂ b₃ : (SchemesOfFiniteTypeOver S)ᵒᵖ} (a : b₀ ⟶ b₁) (a' : b₁ ⟶ b₂)
    (a'' : b₂ ⟶ b₃) (M : Std b₀.unop.left) :
    (fNewShriekStd a''.unop.left (omega ωS hωS b₃.unop) (omega ωS hωS b₂.unop)).map
        ((comp ωS hωS a a').app M) ≫ (comp ωS hωS (a ≫ a') a'').app M ≫
        eqToHom (congrArg (fun k : b₀ ⟶ b₃ =>
          (fNewShriekStd k.unop.left (omega ωS hωS b₃.unop) (omega ωS hωS b₀.unop)).obj M)
          (Category.assoc a a' a'')) =
      (comp ωS hωS a' a'').app
          ((fNewShriekStd a.unop.left (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop)).obj M) ≫
        (comp ωS hωS a (a' ≫ a'')).app M := by
  have h := fNewShriekCompHom_assoc_eqToHom (comp_unop_left a' a'') (comp_unop_left a a')
    (comp_unop_left a (a' ≫ a'')) (comp_unop_left (a ≫ a') a'') (by rw [Category.assoc])
    (omega ωS hωS b₃.unop) (omega ωS hωS b₂.unop) (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop) M
  convert h _ using 0

/-- The left unit law of the comparisons. -/
theorem unit_comp {b₀ b₁ : (SchemesOfFiniteTypeOver S)ᵒᵖ} (a : b₀ ⟶ b₁) (M : Std b₀.unop.left) :
    (fNewShriekStd a.unop.left (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop)).map
        ((unit ωS hωS b₀).app M) ≫ (comp ωS hωS (𝟙 b₀) a).app M =
      eqToHom (congrArg (fun k : b₀ ⟶ b₁ =>
        (fNewShriekStd k.unop.left (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop)).obj M)
        (Category.id_comp a).symm) := by
  have h := map_fNewShriekUnitHomOfEq_comp_fNewShriekCompHom (unop_id_left b₀)
    (comp_unop_left (𝟙 b₀) a) (by simp) (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop) M
  convert h _ using 0

/-- The right unit law of the comparisons. -/
theorem comp_unit {b₀ b₁ : (SchemesOfFiniteTypeOver S)ᵒᵖ} (a : b₀ ⟶ b₁) (M : Std b₀.unop.left) :
    (unit ωS hωS b₁).app
        ((fNewShriekStd a.unop.left (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop)).obj M) ≫
      (comp ωS hωS a (𝟙 b₁)).app M =
      eqToHom (congrArg (fun k : b₀ ⟶ b₁ =>
        (fNewShriekStd k.unop.left (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop)).obj M)
        (Category.comp_id a).symm) := by
  have h := fNewShriekUnitHomOfEq_comp_fNewShriekCompHom (unop_id_left b₁)
    (comp_unop_left a (𝟙 b₁)) (by simp) (omega ωS hωS b₁.unop) (omega ωS hωS b₀.unop) M
  convert h _ using 0

end NewShriekPseudofunctor

open NewShriekPseudofunctor in
/-- In Situation [Stacks, Tag 0AU4], let `ω_X^•` be the dualizing complex
normalized relative to `ω_S^•` of each scheme `X` of finite type over `S`. The functors
`f_new^! = D_X ∘ Lf^* ∘ D_Y : D^+_Coh(𝒪_Y) ⥤ D^+_Coh(𝒪_X)` and the arrows
`(g ∘ f)_new^! ⟶ f_new^! ∘ g_new^!` turn `D^+_Coh` into a pseudofunctor from the category of
schemes of finite type over `S` to the 2-category of categories: `X ↦ D^+_Coh(𝒪_X)`,
`f ↦ f_new^!`, with `mapComp` the inverse of the comparison
`f_new^! ∘ g_new^! ⟶ (g ∘ f)_new^!` given by the biduality `η_Y` ([Stacks, Tag 0A89]) and
`mapId` the inverse of `η_X : id ⟶ (id_X)_new^!`
(`Stacks.Duality.NewShriekPseudofunctor.comp`, `Stacks.Duality.NewShriekPseudofunctor.unit`,
`Stacks.Duality.newShriekPseudofunctor_map_obj_obj`). -/
@[stacks 0AUE "part (1)"]
def newShriekPseudofunctor {S : Scheme.{u}} [IsNoetherian S]
    (ωS : quasiCoherentDerivedCategoryPlusOfModel S) (hωS : IsDualizingComplex ωS.obj.obj) :
    Pseudofunctor (LocallyDiscrete (SchemesOfFiniteTypeOver S)ᵒᵖ) Cat :=
  PseudofunctorOfComparisons.pseudofunctor (T := fun b => Std b.unop.left)
    (hT := fun b => (inferInstance : Category (Std b.unop.left)))
    (fun b => plusCoh b.unop.left)
    (fun a => fNewShriekStd a.unop.left (omega ωS hωS _) (omega ωS hωS _))
    (fun a M hM => plusCoh_fNewShriek a.unop.left (isDualizing_omega ωS hωS _)
      (isDualizing_omega ωS hωS _) M hM)
    (unit ωS hωS) (fun a a' => comp ωS hωS a a')
    (fun b M hM => isIso_fNewShriekUnitHomOfEq_app _ (isDualizing_omega ωS hωS b.unop) M hM.2)
    (fun a a' M hM => isIso_fNewShriekCompHom_app _ _ (isDualizing_omega ωS hωS _)
      (isDualizing_omega ωS hωS _) M hM)
    (fun a a' a'' M _ => by
      have := comp_assoc ωS hωS a a' a'' M
      convert this using 0)
    (fun a M _ => by
      have := unit_comp ωS hωS a M
      convert this using 0)
    (fun a M _ => by
      have := comp_unit ωS hωS a M
      convert this using 0)

open NewShriekPseudofunctor in
/-- The pseudofunctor of [Stacks, Tag 0AUE] part (1) sends `f : A ⟶ B` to `f_new^!`:
`f_new^! M = D_A(Lf^* D_B(M))`. -/
theorem newShriekPseudofunctor_map_obj_obj {S : Scheme.{u}} [IsNoetherian S]
    (ωS : quasiCoherentDerivedCategoryPlusOfModel S) (hωS : IsDualizingComplex ωS.obj.obj)
    {A B : SchemesOfFiniteTypeOver S} (f : A ⟶ B) (M : (plusCoh B.left).FullSubcategory) :
    (((newShriekPseudofunctor ωS hωS).map f.op.toLoc).toFunctor.obj M).obj =
      (fNewShriekStd f.left (omega ωS hωS A) (omega ωS hωS B)).obj M.obj :=
  rfl

end Stacks.Duality

end

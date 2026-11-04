module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence

/-!
# Descending a homomorphism of sheaves of rings along a locally surjective one

Let `a : 𝒜 ⟶ ℬ` and `ψ : 𝒜 ⟶ 𝒯` be homomorphisms of sheaves of commutative rings on a site,
with `a` *locally* surjective, and suppose `ψ` annihilates the kernel of `a` on every object of
the site. Then `ψ` factors through `a` in exactly one way:

`∃! φ : ℬ ⟶ 𝒯, a ≫ φ = ψ`.

This is the sheaf-theoretic form of "a ring homomorphism killing the kernel of a surjection
descends to the quotient", and it is the step the source of [Stacks Project, Tag 08UG] takes at
the end of Step 3 of its proof: having built an algebra map `b + θ ∘ d : 𝒪_{ℬ'₁}[ℰ] ⟶ 𝒪'₂` which
agrees with `ν ∘ a` on the ideal of the presentation, it says this "defines a map
`𝒪'₁ ⟶ 𝒪'₂`". The presentation `𝒪_{ℬ'₁}[ℰ] ⟶ 𝒪'₁` is only locally surjective, so that sentence
is not a quotient map of rings but a descent on a site, and this file supplies it.

The hypothesis is stated as "`a x = 0` implies `ψ x = 0`", on sections, which for additive maps
is the same as agreeing on the fibres of `a`.

## Main definitions

* `Stacks.Sites.RingDescent.quotientHom`: the factorization of `ψ` through the objectwise
  quotient presheaf `U ↦ 𝒜(U)/Ker(a_U)` of
  `StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence`.
* `Stacks.Sites.RingDescent.sheafifyQuotientIso`: the identification of `ℬ` with the
  sheafification of that objectwise quotient, when `a` is locally surjective.
* `Stacks.Sites.RingDescent.desc`: the descended homomorphism `φ : ℬ ⟶ 𝒯`.

## Main results

* `Stacks.Sites.RingDescent.comp_desc`: `a ≫ desc = ψ`, the defining property.
* `Stacks.Sites.RingDescent.eq_desc`: any homomorphism `ℬ ⟶ 𝒯` through which `ψ` factors is the
  descended one.
* `Stacks.Sites.RingDescent.existsUnique_desc`: **the descent**, `∃! φ : ℬ ⟶ 𝒯, a ≫ φ = ψ`.
* `Stacks.Sites.RingDescent.hom_ext_of_isLocallySurjective`: a locally surjective homomorphism
  may be cancelled on the left.

## Implementation notes

The route is the objectwise quotient followed by sheafification, and no size condition relating
the universe of the sections of the sheaves of rings to the universes of the site is incurred.
That is the reason for taking this route rather than gluing local values of `φ` by hand: gluing
would need the sheaf condition of `𝒯` in its `Type`-valued form, and Mathlib's
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` supplies that only when the ring universe
is the join of the two universes of the site. Here the objectwise quotient presheaf
`Stacks.Sites.Conormal.quotientPresheaf` is already in the library, together with the facts that
the canonical map from it to `ℬ` is objectwise injective — hence locally injective — and
locally surjective as soon as `a` is. Being locally bijective it becomes an isomorphism under
sheafification, so `ℬ` *is* the sheafification of the objectwise quotient, and the universal
property of sheafification then does all the work. Both halves of local bijectivity are already
instances on `Stacks.Sites.Conormal.quotientToTarget`.

Uniqueness is proved against the universal property rather than by making `a` an epimorphism:
the objectwise surjection onto the quotient presheaf is surjective on the nose, so a competing
factorization is pinned on the quotient presheaf, and the adjunction is injective. This needs no
balancedness of the category of sheaves of rings.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 03CY](https://stacks.math.columbia.edu/tag/03CY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.Sites.RingDescent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget CommRingCat.{w})]
  {A B T : Sheaf J CommRingCat.{w}}

/-! ### The factorization through the objectwise quotient -/

section Quotient

variable (a : A ⟶ B) (ψ : A ⟶ T)
  (hker : ∀ (X : Cᵒᵖ) (x : A.obj.obj X), a.hom.app X x = 0 → ψ.hom.app X x = 0)

/-- **`ψ` factors through the objectwise quotient by the kernel of `a`.** On an object of the
site this is `Ideal.Quotient.lift` of the component of `ψ`. -/
noncomputable def quotientHom : Conormal.quotientPresheaf a.hom ⟶ T.obj where
  app X := CommRingCat.ofHom (Ideal.Quotient.lift _ (ψ.hom.app X).hom
    (fun _ hx => hker X _ hx))
  naturality {X Y} f := by
    ext x
    exact ψ.hom.naturality_apply f x

omit [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- On a section coming from `𝒜` the factorization is `ψ` itself. -/
@[simp]
theorem quotientHom_mk (X : Cᵒᵖ) (x : A.obj.obj X) :
    (quotientHom a ψ hker).app X (Ideal.Quotient.mk _ x) = ψ.hom.app X x := rfl

omit [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The objectwise surjection onto the quotient presheaf, followed by the factorization, is
`ψ`. -/
theorem toQuotient_comp_quotientHom :
    Conormal.toQuotient a.hom ≫ quotientHom a ψ hker = ψ.hom := rfl

end Quotient

omit [HasWeakSheafify J CommRingCat.{w}] [J.WEqualsLocallyBijective CommRingCat.{w}]
  [J.HasSheafCompose (forget CommRingCat.{w})] in
/-- The presentation of `a` through the objectwise quotient: the objectwise surjection onto the
quotient presheaf followed by its canonical inclusion into `ℬ` is `a`. -/
theorem toQuotient_comp_quotientToTarget (a : A ⟶ B) :
    Conormal.toQuotient a.hom ≫ Conormal.quotientToTarget a.hom = a.hom := rfl

/-- A morphism out of the sheafification, classified by `f`, restricts to `f` along
`toSheafify`. -/
private theorem toSheafify_comp_homEquiv_symm {K : GrothendieckTopology C}
    [HasWeakSheafify K CommRingCat.{w}] {P : Cᵒᵖ ⥤ CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : P ⟶ S.obj) :
    toSheafify K P ≫ (((sheafificationAdjunction K CommRingCat.{w}).homEquiv P S).symm f).hom =
      f := by
  have h := ((sheafificationAdjunction K CommRingCat.{w}).homEquiv P S).apply_symm_apply f
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-! ### The target is the sheafification of the objectwise quotient -/

section Sheafify

variable (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]

/-- The homomorphism of sheaves of rings classifying the canonical inclusion of the objectwise
quotient into `ℬ`. -/
noncomputable def sheafifyQuotientHom :
    (presheafToSheaf J CommRingCat.{w}).obj (Conormal.quotientPresheaf a.hom) ⟶ B :=
  ((sheafificationAdjunction J CommRingCat.{w}).homEquiv _ B).symm
    (Conormal.quotientToTarget a.hom)

/-- The classifying homomorphism restricts on the objectwise quotient to the canonical
inclusion. -/
theorem toSheafify_comp_sheafifyQuotientHom :
    toSheafify J (Conormal.quotientPresheaf a.hom) ≫ (sheafifyQuotientHom a).hom =
      Conormal.quotientToTarget a.hom :=
  toSheafify_comp_homEquiv_symm _

/-- The classifying homomorphism `sheafifyQuotientHom a` is locally injective. -/
instance : Presheaf.IsLocallyInjective J (sheafifyQuotientHom a).hom := by
  rw [← Presheaf.comp_isLocallyInjective_iff J
    (toSheafify J (Conormal.quotientPresheaf a.hom)),
    toSheafify_comp_sheafifyQuotientHom a]
  infer_instance

/-- The classifying homomorphism `sheafifyQuotientHom a` is locally surjective. -/
instance : Presheaf.IsLocallySurjective J (sheafifyQuotientHom a).hom := by
  rw [← Presheaf.comp_isLocallySurjective_iff J
    (toSheafify J (Conormal.quotientPresheaf a.hom)),
    toSheafify_comp_sheafifyQuotientHom a]
  infer_instance

/-- The classifying homomorphism `sheafifyQuotientHom a` is an isomorphism. -/
instance : IsIso (sheafifyQuotientHom a) :=
  (Sheaf.isLocallyBijective_iff_isIso (sheafifyQuotientHom a)).1
    ⟨inferInstanceAs (Presheaf.IsLocallyInjective J (sheafifyQuotientHom a).hom),
      inferInstanceAs (Presheaf.IsLocallySurjective J (sheafifyQuotientHom a).hom)⟩

/-- **`ℬ` is the sheafification of the objectwise quotient by the kernel of `a`.** The
isomorphism is the homomorphism classifying the canonical inclusion of the objectwise quotient
into `ℬ`. -/
noncomputable def sheafifyQuotientIso :
    (presheafToSheaf J CommRingCat.{w}).obj (Conormal.quotientPresheaf a.hom) ≅ B :=
  asIso (sheafifyQuotientHom a)

/-- The forward map of `sheafifyQuotientIso a` is `sheafifyQuotientHom a`. -/
@[simp]
theorem sheafifyQuotientIso_hom :
    (sheafifyQuotientIso a).hom = sheafifyQuotientHom a := rfl

end Sheafify

/-! ### The descent -/

section Desc

variable (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom] (ψ : A ⟶ T)
  (hker : ∀ (X : Cᵒᵖ) (x : A.obj.obj X), a.hom.app X x = 0 → ψ.hom.app X x = 0)

/-- The homomorphism of sheaves of rings classifying the factorization of `ψ` through the
objectwise quotient. -/
noncomputable def sheafifyDesc :
    (presheafToSheaf J CommRingCat.{w}).obj (Conormal.quotientPresheaf a.hom) ⟶ T :=
  ((sheafificationAdjunction J CommRingCat.{w}).homEquiv _ T).symm (quotientHom a ψ hker)

omit [J.WEqualsLocallyBijective CommRingCat.{w}] [J.HasSheafCompose (forget CommRingCat.{w})]
  [Presheaf.IsLocallySurjective J a.hom] in
/-- The classifying homomorphism `sheafifyDesc a ψ hker` restricts on the objectwise quotient
to `quotientHom a ψ hker`. -/
theorem toSheafify_comp_sheafifyDesc :
    toSheafify J (Conormal.quotientPresheaf a.hom) ≫ (sheafifyDesc a ψ hker).hom =
      quotientHom a ψ hker :=
  toSheafify_comp_homEquiv_symm _

/-- **The descended homomorphism.** The factorization of `ψ` through the objectwise quotient,
transported along the identification of `ℬ` with the sheafification of that quotient. -/
noncomputable def desc : B ⟶ T :=
  (sheafifyQuotientIso a).inv ≫ sheafifyDesc a ψ hker

/-- **The defining property of the descent:** the descended homomorphism restricts to `ψ`
along `a`. -/
theorem comp_desc : a ≫ desc a ψ hker = ψ := by
  refine Sheaf.hom_ext ?_
  have hι : Conormal.quotientToTarget a.hom ≫ (sheafifyQuotientIso a).inv.hom =
      toSheafify J (Conormal.quotientPresheaf a.hom) := by
    rw [← toSheafify_comp_sheafifyQuotientHom a, Category.assoc]
    show _ ≫ ((sheafifyQuotientIso a).hom ≫ (sheafifyQuotientIso a).inv).hom = _
    rw [(sheafifyQuotientIso a).hom_inv_id]
    simp
  calc (a ≫ desc a ψ hker).hom
      = (Conormal.toQuotient a.hom ≫ Conormal.quotientToTarget a.hom) ≫
          ((sheafifyQuotientIso a).inv.hom ≫ (sheafifyDesc a ψ hker).hom) := by
        rw [toQuotient_comp_quotientToTarget a]; rfl
    _ = Conormal.toQuotient a.hom ≫
          (Conormal.quotientToTarget a.hom ≫ (sheafifyQuotientIso a).inv.hom) ≫
            (sheafifyDesc a ψ hker).hom := by
        simp only [Category.assoc]
    _ = Conormal.toQuotient a.hom ≫ quotientHom a ψ hker := by
        rw [hι, toSheafify_comp_sheafifyDesc a ψ hker]
    _ = ψ.hom := toQuotient_comp_quotientHom a ψ hker

/-- **The descent is unique.** Any homomorphism `ℬ ⟶ 𝒯` through which `ψ` factors along `a` is
the descended one. -/
theorem eq_desc (φ : B ⟶ T) (hφ : a ≫ φ = ψ) : φ = desc a ψ hker := by
  have hq : Conormal.quotientToTarget a.hom ≫ φ.hom = quotientHom a ψ hker := by
    refine NatTrans.ext (funext fun X => CommRingCat.hom_ext (RingHom.ext fun z => ?_))
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    show φ.hom.app X (a.hom.app X x) = ψ.hom.app X x
    exact congrArg (fun k : A ⟶ T => k.hom.app X x) hφ
  have hkey : (sheafifyQuotientIso a).hom ≫ φ = sheafifyDesc a ψ hker := by
    refine ((sheafificationAdjunction J CommRingCat.{w}).homEquiv
      (Conormal.quotientPresheaf a.hom) T).injective ?_
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    show toSheafify J (Conormal.quotientPresheaf a.hom) ≫
      ((sheafifyQuotientIso a).hom ≫ φ).hom = _
    rw [show ((sheafifyQuotientIso a).hom ≫ φ).hom =
        (sheafifyQuotientIso a).hom.hom ≫ φ.hom from rfl, ← Category.assoc,
      sheafifyQuotientIso_hom, toSheafify_comp_sheafifyQuotientHom a, hq]
    exact (toSheafify_comp_sheafifyDesc a ψ hker).symm
  rw [desc, ← hkey, ← Category.assoc, (sheafifyQuotientIso a).inv_hom_id, Category.id_comp]

/-- **Descent along a locally surjective homomorphism of sheaves of rings.** A homomorphism
`ψ : 𝒜 ⟶ 𝒯` of sheaves of commutative rings on a site which annihilates the kernel of a locally
surjective `a : 𝒜 ⟶ ℬ` on every object of the site factors through `a` in exactly one way. -/
theorem existsUnique_desc
    (hker : ∀ (X : Cᵒᵖ) (x : A.obj.obj X), a.hom.app X x = 0 → ψ.hom.app X x = 0) :
    ∃! φ : B ⟶ T, a ≫ φ = ψ :=
  ⟨desc a ψ hker, comp_desc a ψ hker, fun φ hφ => eq_desc a ψ hker φ hφ⟩

end Desc

/-- **A locally surjective homomorphism of sheaves of rings may be cancelled on the left.** Two
homomorphisms out of `ℬ` which agree after composing with a locally surjective `a : 𝒜 ⟶ ℬ` are
equal. -/
theorem hom_ext_of_isLocallySurjective (a : A ⟶ B) [Presheaf.IsLocallySurjective J a.hom]
    {φ₁ φ₂ : B ⟶ T} (h : a ≫ φ₁ = a ≫ φ₂) : φ₁ = φ₂ := by
  have hker : ∀ (X : Cᵒᵖ) (x : A.obj.obj X),
      a.hom.app X x = 0 → (a ≫ φ₁).hom.app X x = 0 := by
    intro X x hx
    show φ₁.hom.app X (a.hom.app X x) = 0
    rw [hx, map_zero]
  exact (eq_desc a (a ≫ φ₁) hker φ₁ rfl).trans (eq_desc a (a ≫ φ₁) hker φ₂ h.symm).symm

end Stacks.Sites.RingDescent

end

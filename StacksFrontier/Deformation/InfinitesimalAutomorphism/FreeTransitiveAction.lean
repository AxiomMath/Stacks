module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Infinitesimal automorphisms of a fibre square

Let `𝓕` be a category cofibered in groupoids, let `x₁ ⟶ x ⟵ x₂` be a cospan of `𝓕`, and let
`z` be a fibre product of that cospan lying over a fibre product of the corresponding cospan
of the base. Pushing an automorphism of `z` forward along the second projection identifies the
group of automorphisms of `z` that are trivial on the first factor with the group `Inf(x₂/x)`
of infinitesimal automorphisms of the second factor over the common target. The first group
therefore acts on `Inf(x₂/x)` by translation, freely and transitively.

Applied to the fibre square of `x'` with itself over `x`, which condition (RS) supplies for a
morphism `x' ⟶ x` lying over a surjection, this exhibits `Inf(x'/x)` with a free and
transitive action by the infinitesimal automorphisms of that fibre square relative to its
first projection.

## Main definitions

* `Deformation.relativeInfinitesimalAutomorphismsFibreSquareHom`: pushforward along the second
  projection, as a homomorphism between the two groups.
* `Deformation.relativeInfinitesimalAutomorphismsFibreSquareEquiv`: that homomorphism as an
  isomorphism of groups.
* `Deformation.relativeInfinitesimalAutomorphismsFibreSquareAction`: the resulting translation
  action of the automorphisms of the fibre square on `Inf(x₂/x)`.

## Main results

* `Deformation.relativeInfinitesimalAutomorphismsFibreSquareHom_injective` and
  `Deformation.relativeInfinitesimalAutomorphismsFibreSquareHom_surjective`: the two halves of
  the identification.
* `Deformation.relativeInfinitesimalAutomorphismsFibreSquareAction_bijective`: the action is
  free and transitive.
* `Deformation.exists_relativeInfinitesimalAutomorphisms_freeTransitiveAction`: under
  condition (RS), the infinitesimal automorphisms of `x'` over `x` carry a free and transitive
  action by the automorphisms, trivial on the first projection, of a fibre square of `x'` with
  itself over `x`.

## References

* [Stacks Project, Tag 06J2](https://stacks.math.columbia.edu/tag/06J2)
* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
* [Stacks Project, Tag 06JP](https://stacks.math.columbia.edu/tag/06JP)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

/-! ### Pushforward along the second projection of a fibre square -/

section
open CategoryTheory CategoryTheory.Limits
universe v₁ v₂ u₁ u₂

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C] {p : F ⥤ C}
  (hp : IsCofiberedInGroupoids p)
  {D A₁ A₂ A : C} {π₁ : D ⟶ A₁} {π₂ : D ⟶ A₂} {g₁ : A₁ ⟶ A} {g₂ : A₂ ⟶ A}
  {z : p.Fiber D} {x₁ : p.Fiber A₁} {x₂ : p.Fiber A₂} {x : p.Fiber A}
  {c₁ : z.1 ⟶ x₁.1} (hc₁ : p.IsHomLift π₁ c₁)
  {c₂ : z.1 ⟶ x₂.1} (hc₂ : p.IsHomLift π₂ c₂)
  {f₁ : x₁.1 ⟶ x.1} {f₂ : x₂.1 ⟶ x.1} (hf₂ : p.IsHomLift g₂ f₂)
  (hsq : IsPullback c₁ c₂ f₁ f₂)

include hsq in
/-- An automorphism of the fibre square which is trivial on the first factor pushes forward,
along the second projection, to an infinitesimal automorphism of the second factor over the
common target. -/
public theorem pushforwardAutomorphism_mem_relativeInfinitesimalAutomorphisms
    (a : ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁)) :
    pushforwardAutomorphism hp π₂ c₂ hc₂ a.1 ∈
      relativeInfinitesimalAutomorphisms hp g₂ f₂ hf₂ := by
  have ha : (a.1 : Aut z).asIso.hom.val ≫ c₁ = c₁ :=
    (mem_relativeInfinitesimalAutomorphisms_iff hp π₁ c₁ hc₁ a.1).mp a.2
  have := hc₂
  have := hf₂
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hp π₂ c₂ hc₂
  have := pushforwardEndomorphism_isHomLift hp π₂ c₂ hc₂ a.1
  rw [mem_relativeInfinitesimalAutomorphisms_iff]
  change pushforwardEndomorphism hp π₂ c₂ hc₂ a.1 ≫ f₂ = f₂
  have : p.IsHomLift g₂ (pushforwardEndomorphism hp π₂ c₂ hc₂ a.1 ≫ f₂) := inferInstance
  refine Functor.IsStronglyCocartesian.ext p π₂ c₂ g₂ ?_
  rw [← Category.assoc, ← hom_comp_eq_comp_pushforwardEndomorphism hp π₂ c₂ hc₂ a.1,
    Category.assoc, ← hsq.w, reassoc_of% ha]

/-- Pushforward along the second projection of the fibre square, as a homomorphism from the
automorphisms of the square trivial on the first factor to the infinitesimal automorphisms of
the second factor over the common target. -/
public noncomputable def relativeInfinitesimalAutomorphismsFibreSquareHom :
    ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁) →*
      ↥(relativeInfinitesimalAutomorphisms hp g₂ f₂ hf₂) where
  toFun a := ⟨pushforwardAutomorphism hp π₂ c₂ hc₂ a.1,
    pushforwardAutomorphism_mem_relativeInfinitesimalAutomorphisms hp hc₁ hc₂ hf₂ hsq a⟩
  map_one' := Subtype.ext (map_one (pushforwardAutomorphismHom hp π₂ c₂ hc₂))
  map_mul' a b := Subtype.ext (map_mul (pushforwardAutomorphismHom hp π₂ c₂ hc₂) a.1 b.1)

/-- The value of the pushforward homomorphism is the pushforward of the automorphism. -/
public theorem relativeInfinitesimalAutomorphismsFibreSquareHom_coe
    (a : ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁)) :
    (relativeInfinitesimalAutomorphismsFibreSquareHom hp hc₁ hc₂ hf₂ hsq a).1 =
      pushforwardAutomorphism hp π₂ c₂ hc₂ a.1 :=
  rfl

/-- Pushforward along the second projection is injective on automorphisms of the fibre square
trivial on the first factor: such an automorphism is determined by its two composites with the
projections. -/
public theorem relativeInfinitesimalAutomorphismsFibreSquareHom_injective :
    Function.Injective
      (relativeInfinitesimalAutomorphismsFibreSquareHom hp hc₁ hc₂ hf₂ hsq) := by
  refine (injective_iff_map_eq_one _).2 fun a hcl => ?_
  have ha : (a.1 : Aut z).asIso.hom.val ≫ c₁ = c₁ :=
    (mem_relativeInfinitesimalAutomorphisms_iff hp π₁ c₁ hc₁ a.1).mp a.2
  have h1 : pushforwardAutomorphism hp π₂ c₂ hc₂ a.1 = 1 := by
    rw [← relativeInfinitesimalAutomorphismsFibreSquareHom_coe hp hc₁ hc₂ hf₂ hsq a, hcl]
    simp
  have hval : pushforwardEndomorphism hp π₂ c₂ hc₂ a.1 = 𝟙 x₂.1 := by
    change (pushforwardAutomorphism hp π₂ c₂ hc₂ a.1).asIso.hom.val = 𝟙 x₂.1
    rw [h1]
    rfl
  have hsnd : (a.1 : Aut z).asIso.hom.val ≫ c₂ = 𝟙 z.1 ≫ c₂ := by
    rw [Category.id_comp, hom_comp_eq_comp_pushforwardEndomorphism hp π₂ c₂ hc₂ a.1,
      hval, Category.comp_id]
  have hfst : (a.1 : Aut z).asIso.hom.val ≫ c₁ = 𝟙 z.1 ≫ c₁ := by rwa [Category.id_comp]
  exact Subtype.ext <| Aut.ext <| Iso.ext <| Functor.Fiber.hom_ext <| hsq.hom_ext hfst hsnd

/-! ### Automorphisms produced from the universal property of the fibre square -/

section Surjectivity

variable (hbase : IsPullback π₁ π₂ g₁ g₂)

include hc₁ hc₂ hbase in
/-- An endomorphism of the fibre square whose image in the base fixes both base projections
lies over the identity. -/
private theorem isHomLift_id_of_fibreSquare
    (φ : z.1 ⟶ z.1) (hm₁ : p.map φ ≫ p.map c₁ = p.map c₁)
    (hm₂ : p.map φ ≫ p.map c₂ = p.map c₂) :
    p.IsHomLift (𝟙 D) φ := by
  have := hc₁
  have := hc₂
  have e₁ : p.map c₁ = eqToHom z.2 ≫ π₁ ≫ eqToHom x₁.2.symm := IsHomLift.fac' p π₁ c₁
  have e₂ : p.map c₂ = eqToHom z.2 ≫ π₂ ≫ eqToHom x₂.2.symm := IsHomLift.fac' p π₂ c₂
  have key₁ : p.map φ ≫ eqToHom z.2 ≫ π₁ = eqToHom z.2 ≫ π₁ := by
    refine (cancel_mono (eqToHom x₁.2.symm)).mp ?_
    simp only [Category.assoc]
    rw [← e₁]
    exact hm₁
  have key₂ : p.map φ ≫ eqToHom z.2 ≫ π₂ = eqToHom z.2 ≫ π₂ := by
    refine (cancel_mono (eqToHom x₂.2.symm)).mp ?_
    simp only [Category.assoc]
    rw [← e₂]
    exact hm₂
  have ht₁ : (eqToHom z.2.symm ≫ p.map φ ≫ eqToHom z.2) ≫ π₁ = 𝟙 D ≫ π₁ := by
    simp only [Category.assoc, key₁]
    simp
  have ht₂ : (eqToHom z.2.symm ≫ p.map φ ≫ eqToHom z.2) ≫ π₂ = 𝟙 D ≫ π₂ := by
    simp only [Category.assoc, key₂]
    simp
  exact IsHomLift.of_fac p (𝟙 D) φ z.2 z.2 (hbase.hom_ext ht₁ ht₂).symm

include hbase in
/-- Every infinitesimal automorphism of the second factor over the common target is the
pushforward, along the second projection, of an automorphism of the fibre square trivial on
the first factor. -/
public theorem relativeInfinitesimalAutomorphismsFibreSquareHom_surjective :
    Function.Surjective
      (relativeInfinitesimalAutomorphismsFibreSquareHom hp hc₁ hc₂ hf₂ hsq) := by
  have := hc₂
  have := hf₂
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hp π₂ c₂ hc₂
  intro ψ
  have hψ : (ψ.1 : Aut x₂).asIso.hom.val ≫ f₂ = f₂ :=
    (mem_relativeInfinitesimalAutomorphisms_iff hp g₂ f₂ hf₂ ψ.1).mp ψ.2
  have hψinv : (ψ.1 : Aut x₂).asIso.inv.val ≫ f₂ = f₂ :=
    (mem_relativeInfinitesimalAutomorphisms_iff hp g₂ f₂ hf₂ ((ψ.1 : Aut x₂)⁻¹)).mp
      (inv_mem ψ.2)
  have hcomm : ∀ ρ : x₂.1 ⟶ x₂.1, ρ ≫ f₂ = f₂ → c₁ ≫ f₁ = (c₂ ≫ ρ) ≫ f₂ := by
    intro ρ hρ
    rw [Category.assoc, hρ]
    exact hsq.w
  have hlift : ∀ ρ : x₂ ⟶ x₂, ρ.val ≫ f₂ = f₂ →
      ∃ φ : z ⟶ z, φ.val ≫ c₁ = c₁ ∧ φ.val ≫ c₂ = c₂ ≫ ρ.val := by
    intro ρ hρ
    have hρmap : p.map ρ.val = 𝟙 (p.obj x₂.1) := by
      have := ρ.2
      simpa using IsHomLift.fac' p (𝟙 A₂) ρ.val
    have hφ₁ := hsq.lift_fst c₁ (c₂ ≫ ρ.val) (hcomm _ hρ)
    have hφ₂ := hsq.lift_snd c₁ (c₂ ≫ ρ.val) (hcomm _ hρ)
    refine ⟨⟨hsq.lift c₁ _ (hcomm _ hρ), isHomLift_id_of_fibreSquare hc₁ hc₂ hbase _ ?_ ?_⟩,
      hφ₁, hφ₂⟩
    · rw [← p.map_comp, hφ₁]
    · rw [← p.map_comp, hφ₂, p.map_comp, hρmap, Category.comp_id]
  have hcompose : ∀ (ρ σ : x₂ ⟶ x₂) (φ φ' : z ⟶ z), ρ.val ≫ σ.val = 𝟙 x₂.1 →
      φ.val ≫ c₁ = c₁ → φ.val ≫ c₂ = c₂ ≫ ρ.val →
      φ'.val ≫ c₁ = c₁ → φ'.val ≫ c₂ = c₂ ≫ σ.val → φ.val ≫ φ'.val = 𝟙 z.1 := by
    intro ρ σ φ φ' hρσ hφ₁ hφ₂ hφ'₁ hφ'₂
    refine hsq.hom_ext ?_ ?_
    · rw [Category.assoc, hφ'₁, hφ₁, Category.id_comp]
    · rw [Category.assoc, hφ'₂, ← Category.assoc, hφ₂, Category.assoc, hρσ,
        Category.comp_id, Category.id_comp]
  obtain ⟨φ, hφ₁, hφ₂⟩ := hlift _ hψ
  obtain ⟨φ', hφ'₁, hφ'₂⟩ := hlift _ hψinv
  have hhi : (ψ.1 : Aut x₂).asIso.hom.val ≫ (ψ.1 : Aut x₂).asIso.inv.val = 𝟙 x₂.1 :=
    congrArg Subtype.val (ψ.1 : Aut x₂).asIso.hom_inv_id
  have hih : (ψ.1 : Aut x₂).asIso.inv.val ≫ (ψ.1 : Aut x₂).asIso.hom.val = 𝟙 x₂.1 :=
    congrArg Subtype.val (ψ.1 : Aut x₂).asIso.inv_hom_id
  let b : Aut z := Aut.of
    { hom := φ
      inv := φ'
      hom_inv_id := Subtype.ext (hcompose _ _ φ φ' hhi hφ₁ hφ₂ hφ'₁ hφ'₂)
      inv_hom_id := Subtype.ext (hcompose _ _ φ' φ hih hφ'₁ hφ'₂ hφ₁ hφ₂) }
  have hbmem : b ∈ relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁ :=
    (mem_relativeInfinitesimalAutomorphisms_iff hp π₁ c₁ hc₁ b).mpr hφ₁
  refine ⟨⟨b, hbmem⟩, ?_⟩
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  apply Functor.Fiber.hom_ext
  change pushforwardEndomorphism hp π₂ c₂ hc₂ b = (ψ.1 : Aut x₂).asIso.hom.val
  have := pushforwardEndomorphism_isHomLift hp π₂ c₂ hc₂ b
  have := (ψ.1 : Aut x₂).asIso.hom.2
  refine Functor.IsStronglyCocartesian.ext p π₂ c₂ (𝟙 A₂) ?_
  rw [← hom_comp_eq_comp_pushforwardEndomorphism hp π₂ c₂ hc₂ b]
  exact hφ₂

include hsq hbase in
/-- **The identification of infinitesimal automorphisms across a fibre square.** Pushforward
along the second projection is an isomorphism from the automorphisms of the fibre square
trivial on the first factor onto the infinitesimal automorphisms of the second factor over the
common target. -/
public noncomputable def relativeInfinitesimalAutomorphismsFibreSquareEquiv :
    ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁) ≃*
      ↥(relativeInfinitesimalAutomorphisms hp g₂ f₂ hf₂) :=
  MulEquiv.ofBijective (relativeInfinitesimalAutomorphismsFibreSquareHom hp hc₁ hc₂ hf₂ hsq)
    ⟨relativeInfinitesimalAutomorphismsFibreSquareHom_injective hp hc₁ hc₂ hf₂ hsq,
      relativeInfinitesimalAutomorphismsFibreSquareHom_surjective hp hc₁ hc₂ hf₂ hsq hbase⟩

include hsq hbase in
/-- Translation along the identification: the automorphisms of the fibre square trivial on the
first factor act on the infinitesimal automorphisms of the second factor over the common
target. -/
@[instance_reducible]
public noncomputable def relativeInfinitesimalAutomorphismsFibreSquareAction :
    MulAction ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁)
      ↥(relativeInfinitesimalAutomorphisms hp g₂ f₂ hf₂) where
  smul a s := relativeInfinitesimalAutomorphismsFibreSquareEquiv hp hc₁ hc₂ hf₂ hsq hbase a * s
  one_smul s := by
    change relativeInfinitesimalAutomorphismsFibreSquareEquiv hp hc₁ hc₂ hf₂ hsq hbase 1 * s = s
    rw [map_one, one_mul]
  mul_smul a b s := by
    change relativeInfinitesimalAutomorphismsFibreSquareEquiv hp hc₁ hc₂ hf₂ hsq hbase (a * b) *
      s = relativeInfinitesimalAutomorphismsFibreSquareEquiv hp hc₁ hc₂ hf₂ hsq hbase a *
        (relativeInfinitesimalAutomorphismsFibreSquareEquiv hp hc₁ hc₂ hf₂ hsq hbase b * s)
    rw [map_mul, mul_assoc]

/-- **The action is free and transitive.** From any infinitesimal automorphism of the second
factor over the common target, translation is a bijection onto all of them. -/
public theorem relativeInfinitesimalAutomorphismsFibreSquareAction_bijective :
    letI := relativeInfinitesimalAutomorphismsFibreSquareAction hp hc₁ hc₂ hf₂ hsq hbase
    ∀ s : ↥(relativeInfinitesimalAutomorphisms hp g₂ f₂ hf₂),
      Function.Bijective
        (fun a : ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁) => a • s) := by
  let := relativeInfinitesimalAutomorphismsFibreSquareAction hp hc₁ hc₂ hf₂ hsq hbase
  intro s
  have hsmul : ∀ a : ↥(relativeInfinitesimalAutomorphisms hp π₁ c₁ hc₁),
      a • s = relativeInfinitesimalAutomorphismsFibreSquareEquiv hp hc₁ hc₂ hf₂ hsq hbase a * s :=
    fun _ => rfl
  constructor
  · intro a b hab
    simp only [hsmul] at hab
    exact (relativeInfinitesimalAutomorphismsFibreSquareEquiv
      hp hc₁ hc₂ hf₂ hsq hbase).injective (mul_right_cancel hab)
  · intro t
    refine ⟨(relativeInfinitesimalAutomorphismsFibreSquareEquiv
      hp hc₁ hc₂ hf₂ hsq hbase).symm (t * s⁻¹), ?_⟩
    simp only [hsmul, MulEquiv.apply_symm_apply, inv_mul_cancel_right]

end Surjectivity

end

/-! ### The fibre square supplied by condition (RS) -/

section
open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- For a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) and a morphism `x' ⟶ x`
lying over a surjection, the group `Inf(x'/x)` carries a free and transitive action by the
automorphisms, trivial on the first projection, of a fibre square of `x'` with itself over
`x`. -/
public theorem exists_relativeInfinitesimalAutomorphisms_freeTransitiveAction
    (hrs : SatisfiesRS p) {A' A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    {x' : p.Fiber A'} {x : p.Fiber A}
    (g : A' ⟶ A) (f : x'.1 ⟶ x.1) (hf : p.IsHomLift g f)
    (hg : Function.Surjective g.hom) :
    ∃ (Z : F) (π : p.obj Z ⟶ A') (c : Z ⟶ x'.1) (hc : p.IsHomLift π c)
      (act : ↥(relativeInfinitesimalAutomorphisms (x' := ⟨Z, rfl⟩) (x := x') hrs.1 π c hc) →
        ↥(relativeInfinitesimalAutomorphisms hrs.1 g f hf) →
        ↥(relativeInfinitesimalAutomorphisms hrs.1 g f hf)),
      (∀ s, act 1 s = s) ∧
      (∀ a b s, act (a * b) s = act a (act b s)) ∧
      (∀ s, Function.Bijective fun a => act a s) := by
  obtain ⟨X', rfl⟩ := x'
  obtain ⟨X, rfl⟩ := x
  have := hf
  obtain rfl : g = p.map f := IsHomLift.eq_of_isHomLift p g f
  obtain ⟨cone, ⟨hlim⟩, ⟨hlimp⟩⟩ := hrs.2 f f hg
  have hsq : IsPullback cone.fst cone.snd f f := IsPullback.of_isLimit hlim
  have hbase : IsPullback (p.map cone.fst) (p.map cone.snd) (p.map f) (p.map f) :=
    IsPullback.of_isLimit hlimp
  let := relativeInfinitesimalAutomorphismsFibreSquareAction
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := ⟨X', rfl⟩) (x := ⟨X, rfl⟩)
    hrs.1 (IsHomLift.map p cone.fst) (IsHomLift.map p cone.snd) (IsHomLift.map p f) hsq hbase
  exact ⟨cone.pt, p.map cone.fst, cone.fst, IsHomLift.map p cone.fst, fun a s => a • s,
    fun s => one_smul _ s, fun a b s => mul_smul a b s,
    relativeInfinitesimalAutomorphismsFibreSquareAction_bijective
      (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := ⟨X', rfl⟩) (x := ⟨X, rfl⟩)
      hrs.1 (IsHomLift.map p cone.fst) (IsHomLift.map p cone.snd) (IsHomLift.map p f)
      hsq hbase⟩

end

end Deformation

end

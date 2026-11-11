module

public import StacksFrontier.AlgebraicGeometry.StalkToSectionsOfSpecializes

/-!
# Deformations of a section along a thickening and derivations of a stalk

Let `p : X ⟶ S` be a morphism of schemes with a section `σ`, let `y` be a point of `X` to which
every point of `σ(S)` specializes, and let `q : T ⟶ S` be a scheme over `S` with a surjective
`i : T₀ ⟶ T` whose kernel on global functions is square-zero (a first-order thickening). A
morphism `a : T ⟶ X` over `S` that agrees on `T₀` with the trivial deformation `q ≫ σ` lands in
the generizations of `y`, so it has a ring map `𝒪_{X, y} ⟶ Γ(T, 𝒪_T)`
(`AlgebraicGeometry.Scheme.Hom.stalkToΓOfSpecializes`), and its difference with the ring map of
`q ≫ σ` is a derivation with values in the kernel of `Γ(T, 𝒪_T) ⟶ Γ(T₀, 𝒪_{T₀})`, for the
module structure read off `σ`. This file records that difference,
`AlgebraicGeometry.Scheme.Hom.stalkDiff`, and its properties: it takes values in the kernel, it
satisfies the Leibniz rule, it vanishes on functions coming from `S`, it determines `a`, every
such derivation arises when `S` is affine, and it is natural in `T` and in `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {S T X : Scheme.{u}} (q : T ⟶ S) (σ : S ⟶ X) (y : X) (hy : ∀ s : S, σ.base s ⤳ y)

include hy in
/-- The trivial deformation `q ≫ σ` lands in the generizations of `y`. -/
theorem specializes_comp_section (t : T) : (q ≫ σ).base t ⤳ y := by
  rw [Scheme.Hom.comp_apply]
  exact hy _

include hy in
/-- A morphism agreeing on a surjective `i : T₀ ⟶ T` with the trivial deformation `q ≫ σ` lands
in the generizations of `y`. -/
theorem specializes_of_comp_eq {T₀ : Scheme.{u}} {i : T₀ ⟶ T} (hi : Function.Surjective i.base)
    {a : T ⟶ X} (ha : i ≫ a = i ≫ q ≫ σ) (t : T) : a.base t ⤳ y := by
  obtain ⟨t₀, rfl⟩ := hi t
  have e := congrArg (fun g : T₀ ⟶ X ↦ g.base t₀) ha
  simp only [Scheme.Hom.comp_apply] at e
  rw [e]
  exact hy _

/-- **The difference of a deformation and the trivial deformation, on the stalk at `y`.** For
`a : T ⟶ X` landing in the generizations of `y`, the map `𝒪_{X, y} ⟶ Γ(T, 𝒪_T)` sending a germ
to the difference of its pullbacks along `a` and along `q ≫ σ`. -/
def stalkDiff (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y) (f : X.presheaf.stalk y) : Γ(T, ⊤) :=
  (a.stalkToΓOfSpecializes y ha).hom f -
    ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom f

theorem stalkDiff_apply (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y) (f : X.presheaf.stalk y) :
    stalkDiff q σ y hy a ha f = (a.stalkToΓOfSpecializes y ha).hom f -
      ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom f :=
  rfl

/-- `AlgebraicGeometry.Scheme.Hom.stalkDiff` is additive. -/
theorem stalkDiff_add (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y) (f g : X.presheaf.stalk y) :
    stalkDiff q σ y hy a ha (f + g) = stalkDiff q σ y hy a ha f + stalkDiff q σ y hy a ha g := by
  simp only [stalkDiff_apply, map_add]
  ring

/-- `AlgebraicGeometry.Scheme.Hom.stalkDiff` depends only on the morphism. -/
theorem stalkDiff_congr {a b : T ⟶ X} (e : a = b) (ha : ∀ t : T, a.base t ⤳ y)
    (hb : ∀ t : T, b.base t ⤳ y) : stalkDiff q σ y hy a ha = stalkDiff q σ y hy b hb := by
  subst e
  rfl

/-- The trivial deformation has vanishing difference. -/
theorem stalkDiff_self (h : ∀ t : T, (q ≫ σ).base t ⤳ y) :
    stalkDiff q σ y hy (q ≫ σ) h = 0 := by
  funext f
  rw [stalkDiff_apply, sub_self]
  rfl

/-- The trivial deformation `q ≫ σ` acts on germs through the section: its map on the stalk is
`σ^# : 𝒪_{X, y} ⟶ Γ(S, 𝒪_S)` followed by `q^#`. -/
theorem stalkToΓOfSpecializes_comp_section :
    (q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy) =
      σ.stalkToΓOfSpecializes y hy ≫ q.appTop :=
  stalkToΓOfSpecializes_comp σ y hy q _

/-- **Values in the kernel.** If `a` agrees with `q ≫ σ` on `T₀`, the difference takes values in
the kernel of `i^# : Γ(T, 𝒪_T) ⟶ Γ(T₀, 𝒪_{T₀})`. -/
theorem appTop_stalkDiff {T₀ : Scheme.{u}} (i : T₀ ⟶ T) (a : T ⟶ X)
    (ha : ∀ t : T, a.base t ⤳ y) (hia : i ≫ a = i ≫ q ≫ σ) (f : X.presheaf.stalk y) :
    i.appTop.hom (stalkDiff q σ y hy a ha f) = 0 := by
  have h₁ : ∀ t : T₀, (i ≫ a).base t ⤳ y := fun t ↦ by
    rw [Scheme.Hom.comp_apply]; exact ha _
  have e₁ := stalkToΓOfSpecializes_comp a y ha i h₁
  have e₂ := stalkToΓOfSpecializes_comp (q ≫ σ) y (specializes_comp_section q σ y hy) i
    (by rw [← hia]; exact h₁)
  have e₃ := stalkToΓOfSpecializes_congr y hia h₁ (by rw [← hia]; exact h₁)
  rw [stalkDiff_apply, map_sub, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← e₁, ← e₂,
    e₃, sub_self]

/-- **The Leibniz rule.** If the products of elements of the kernel of `i^#` vanish, the difference
satisfies `D (f * g) = φ₀ f * D g + φ₀ g * D f`, where `φ₀` is the map of the trivial
deformation. -/
theorem stalkDiff_mul {T₀ : Scheme.{u}} (i : T₀ ⟶ T)
    (h2 : ∀ c d : Γ(T, ⊤), i.appTop.hom c = 0 → i.appTop.hom d = 0 → c * d = 0) (a : T ⟶ X)
    (ha : ∀ t : T, a.base t ⤳ y) (hia : i ≫ a = i ≫ q ≫ σ) (f g : X.presheaf.stalk y) :
    stalkDiff q σ y hy a ha (f * g) =
      ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom f *
          stalkDiff q σ y hy a ha g +
        ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom g *
          stalkDiff q σ y hy a ha f := by
  have hz := h2 _ _ (appTop_stalkDiff q σ y hy i a ha hia f)
    (appTop_stalkDiff q σ y hy i a ha hia g)
  simp only [stalkDiff_apply, map_mul] at hz ⊢
  linear_combination hz

/-- The map of a morphism over `S` on the germ of a function from `S` is the pullback of that
function along the structure morphism. -/
theorem stalkToΓOfSpecializes_germ_appTop {p : X ⟶ S} (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y)
    (hap : a ≫ p = q) (r : Γ(S, ⊤)) :
    (a.stalkToΓOfSpecializes y ha).hom ((X.presheaf.germ ⊤ y trivial).hom (p.appTop.hom r)) =
      q.appTop.hom r := by
  rw [← CommRingCat.comp_apply, germ_top_stalkToΓOfSpecializes, ← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop, hap]

/-- **Vanishing on functions from `S`.** For `a` over `S` and `σ` a section, the difference
vanishes on the germs of functions pulled back from `S`. -/
theorem stalkDiff_germ_appTop {p : X ⟶ S} (hσ : σ ≫ p = 𝟙 S) (a : T ⟶ X)
    (ha : ∀ t : T, a.base t ⤳ y) (hap : a ≫ p = q) (r : Γ(S, ⊤)) :
    stalkDiff q σ y hy a ha ((X.presheaf.germ ⊤ y trivial).hom (p.appTop.hom r)) = 0 := by
  rw [stalkDiff_apply, stalkToΓOfSpecializes_germ_appTop q y a ha hap,
    stalkToΓOfSpecializes_germ_appTop q y (q ≫ σ) _ (by rw [Category.assoc, hσ, Category.comp_id]),
    sub_self]

/-- **The difference determines the deformation.** -/
theorem eq_of_stalkDiff_eq {a b : T ⟶ X} (ha : ∀ t : T, a.base t ⤳ y)
    (hb : ∀ t : T, b.base t ⤳ y) (e : stalkDiff q σ y hy a ha = stalkDiff q σ y hy b hb) :
    a = b := by
  refine eq_of_stalkToΓOfSpecializes_eq y ha hb (CommRingCat.hom_ext (RingHom.ext fun f ↦ ?_))
  have := congrFun e f
  simp only [stalkDiff_apply, sub_left_inj] at this
  exact this

/-- **Naturality in `T`.** Precomposing with `g : T' ⟶ T` (and replacing `q` by `q' = g ≫ q`)
composes the difference with `g^#`. -/
theorem stalkDiff_comp {T' : Scheme.{u}} (g : T' ⟶ T) {q' : T' ⟶ S} (hq : g ≫ q = q')
    (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y) (hga : ∀ t : T', (g ≫ a).base t ⤳ y)
    (f : X.presheaf.stalk y) :
    stalkDiff q' σ y hy (g ≫ a) hga f = g.appTop.hom (stalkDiff q σ y hy a ha f) := by
  subst hq
  rw [stalkDiff_apply, stalkDiff_apply, map_sub, stalkToΓOfSpecializes_comp a y ha g hga,
    stalkToΓOfSpecializes_congr y (Category.assoc g q σ) _
      (fun t ↦ by rw [Scheme.Hom.comp_apply]; exact specializes_comp_section q σ y hy _),
    stalkToΓOfSpecializes_comp (q ≫ σ) y (specializes_comp_section q σ y hy) g]
  rfl

/-- **Naturality in `X`.** Postcomposing with `φ : X ⟶ X'` carrying the section `σ` to a section
`σ'` precomposes the difference with the map of stalks `𝒪_{X', φ y} ⟶ 𝒪_{X, y}`. -/
theorem stalkDiff_comp_right {X' : Scheme.{u}} (φ : X ⟶ X') {σ' : S ⟶ X'} (hφ : σ ≫ φ = σ')
    (hy' : ∀ s : S, σ'.base s ⤳ φ.base y) (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y)
    (haφ : ∀ t : T, (a ≫ φ).base t ⤳ φ.base y) (f : X'.presheaf.stalk (φ.base y)) :
    stalkDiff q σ' (φ.base y) hy' (a ≫ φ) haφ f =
      stalkDiff q σ y hy a ha ((φ.stalkMap y).hom f) := by
  subst hφ
  have h₀ : ∀ t : T, ((q ≫ σ) ≫ φ).base t ⤳ φ.base y := fun t ↦ by
    rw [Scheme.Hom.comp_apply]
    exact (specializes_comp_section q σ y hy t).map φ.continuous
  rw [stalkDiff_apply, stalkDiff_apply, stalkToΓOfSpecializes_comp_right a y ha φ haφ,
    stalkToΓOfSpecializes_congr (φ.base y) (Category.assoc q σ φ).symm _ h₀,
    stalkToΓOfSpecializes_comp_right (q ≫ σ) y (specializes_comp_section q σ y hy) φ h₀]
  rfl

/-- **Every derivation is the difference of a deformation.** Let `S` be affine, `σ` a section of
`p`, and `i : T₀ ⟶ T` with square-zero kernel on global functions. An additive map
`δ : 𝒪_{X, y} ⟶ Γ(T, 𝒪_T)` with values in the kernel of `i^#`, satisfying the Leibniz rule for
the map `φ₀` of the trivial deformation and vanishing on the germs of functions from `S`, is the
difference of a morphism `a : T ⟶ X` over `S` agreeing with `q ≫ σ` on `T₀`. -/
theorem exists_stalkDiff_eq [IsAffine S] {p : X ⟶ S} (hσ : σ ≫ p = 𝟙 S) {T₀ : Scheme.{u}}
    (i : T₀ ⟶ T)
    (h2 : ∀ c d : Γ(T, ⊤), i.appTop.hom c = 0 → i.appTop.hom d = 0 → c * d = 0)
    (δ : X.presheaf.stalk y →+ Γ(T, ⊤)) (hδi : ∀ f, i.appTop.hom (δ f) = 0)
    (hδ : ∀ f g, δ (f * g) =
      ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom f * δ g +
        ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom g * δ f)
    (hδS : ∀ r, δ ((X.presheaf.germ ⊤ y trivial).hom (p.appTop.hom r)) = 0) :
    ∃ (a : T ⟶ X) (ha : ∀ t : T, a.base t ⤳ y), a ≫ p = q ∧ i ≫ a = i ≫ q ≫ σ ∧
      stalkDiff q σ y hy a ha = δ := by
  set φ₀ := ((q ≫ σ).stalkToΓOfSpecializes y (specializes_comp_section q σ y hy)).hom
  let ψ : X.presheaf.stalk y →+* Γ(T, ⊤) :=
    { toFun := fun f ↦ φ₀ f + δ f
      map_one' := by
        have h := hδ 1 1
        simp only [mul_one, map_one, one_mul] at h
        have h1 : δ 1 = 0 := by linear_combination -h
        rw [map_one, h1, add_zero]
      map_mul' := fun f g ↦ by
        have hz := h2 _ _ (hδi f) (hδi g)
        rw [map_mul, hδ]
        linear_combination -hz
      map_zero' := by rw [map_zero, map_zero, add_zero]
      map_add' := fun f g ↦ by rw [map_add, map_add]; ring }
  obtain ⟨a, ha, hψ⟩ := exists_stalkToΓOfSpecializes_eq y (CommRingCat.ofHom ψ)
  have happ : ∀ f, (a.stalkToΓOfSpecializes y ha).hom f = φ₀ f + δ f := fun f ↦ by
    rw [hψ]; rfl
  have hdiff : stalkDiff q σ y hy a ha = δ := funext fun f ↦ by
    rw [stalkDiff_apply, happ]; ring
  refine ⟨a, ha, ?_, ?_, hdiff⟩
  · refine Stacks.Smooth.homEquivOfIsAffine.injective
      (CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_))
    change (a ≫ p).appTop.hom r = q.appTop.hom r
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← germ_top_stalkToΓOfSpecializes a y ha,
      CommRingCat.comp_apply, happ, hδS, add_zero]
    exact stalkToΓOfSpecializes_germ_appTop q y (q ≫ σ) _
      (by rw [Category.assoc, hσ, Category.comp_id]) r
  · have h₁ : ∀ t : T₀, (i ≫ a).base t ⤳ y := fun t ↦ by
      rw [Scheme.Hom.comp_apply]; exact ha _
    have h₂ : ∀ t : T₀, (i ≫ q ≫ σ).base t ⤳ y := fun t ↦ by
      rw [Scheme.Hom.comp_apply]; exact specializes_comp_section q σ y hy _
    refine eq_of_stalkToΓOfSpecializes_eq y h₁ h₂ ?_
    rw [stalkToΓOfSpecializes_comp a y ha i h₁,
      stalkToΓOfSpecializes_comp (q ≫ σ) y (specializes_comp_section q σ y hy) i h₂]
    refine CommRingCat.hom_ext (RingHom.ext fun f ↦ ?_)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, happ, map_add, hδi, add_zero]

end Scheme.Hom

end AlgebraicGeometry

end

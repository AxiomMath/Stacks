module

public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Stack
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.RestrictionBase
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.StackOverMap
public import StacksFrontier.CategoryTheory.FibredOneMorphism

/-!
# Spans and cocones over a commutative square of the base

Let `p : 𝒳 ⥤ 𝒞` be a category fibred in groupoids and let

```
U --g--> W
|        |
f        j
v        v
V --i--> Z
```

be a commutative square of `𝒞`. A *span* over the pair `(f, g)` is a pair of morphisms
`α : u ⟶ x` and `β : u ⟶ y` of `𝒳` lying over `f` and `g`; a *cocone* over a span, for the pair
`(i, j)`, is an object `z` together with morphisms `ξ : x ⟶ z` and `η : y ⟶ z` lying over `i` and
`j` with `α ≫ ξ = β ≫ η`. Since every morphism of a category fibred in groupoids is cartesian, a
span is the same thing as an object of the two-fibre product of the fibres over `V` and `W` over
the fibre over `U`, and a cocone over it is an object of the fibre over `Z` together with an
isomorphism of its image under the comparison functor with that object. So "every span has a
cocone" is essential surjectivity of the comparison and "cocones are unique up to unique
isomorphism" is its full faithfulness, in a form that names no choice of pullbacks.

## Main definitions

* `CategoryTheory.Functor.SquareSpan`: a span over a pair of morphisms with common source.
* `CategoryTheory.Functor.SquareSpan.Cocone`: a cocone over a span.
* `CategoryTheory.Functor.SquareSpan.Cocone.Hom`: a morphism of cocones, lying over an identity.
* `CategoryTheory.Functor.HasUniqueSquareCocones`: any two cocones over a span are related by
  exactly one morphism of cocones.
* `CategoryTheory.Functor.BaseSquare`, `CategoryTheory.Functor.BaseSquare.Hom`: commutative squares
  of the base and their morphisms, and `CategoryTheory.Functor.BaseSquare.baseChange`, the base
  change of a square along a morphism into its terminal corner.

## Main results

* `CategoryTheory.Functor.IsStackInGroupoids.existsUnique_hom_of_cover` and
  `CategoryTheory.Functor.IsStackInGroupoids.exists_glue`: morphisms out of an object, and
  objects, glue along a covering family of a stack in groupoids.
* `CategoryTheory.Functor.IsStackInGroupoids.nonempty_cocone_of_cover` and its form for a
  base-changed covering family,
  `CategoryTheory.Functor.IsStackInGroupoids.nonempty_cocone_of_baseChange`: existence of cocones
  over a span is local on the terminal corner, as soon as cocones are unique over the double and
  triple overlaps.
* `CategoryTheory.Functor.SquareSpan.nonempty_cocone_over_forget`: in a slice, spans over a
  pushout square have cocones.

## Implementation notes

Descent is taken in the family-indexed form `CategoryTheory.Functor.IsStackInGroupoids`
(Stacks 02ZI), whose double and triple overlaps are genuine fibre products: the uniqueness of
cocones is then only needed at those overlaps, which is what makes the local-to-global theorem
applicable to a comparison functor that is fully faithful only at flat base changes of a square.

## References

* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒞)

/-- A *span* of `p` over the pair `f : U ⟶ V`, `g : U ⟶ W`: morphisms `α : u ⟶ x` and
`β : u ⟶ y` lying over `f` and `g`. -/
structure SquareSpan {U V W : 𝒞} (f : U ⟶ V) (g : U ⟶ W) where
  /-- The object over the common source. -/
  u : 𝒳
  /-- The object over the target of `f`. -/
  x : 𝒳
  /-- The object over the target of `g`. -/
  y : 𝒳
  /-- The morphism over `f`. -/
  α : u ⟶ x
  /-- The morphism over `g`. -/
  β : u ⟶ y
  isHomLift_α : p.IsHomLift f α
  isHomLift_β : p.IsHomLift g β

attribute [instance] SquareSpan.isHomLift_α SquareSpan.isHomLift_β

variable {p}

namespace SquareSpan

variable {U V W Z : 𝒞} {f : U ⟶ V} {g : U ⟶ W}

/-- A *cocone* over a span, for the pair `i : V ⟶ Z`, `j : W ⟶ Z`: morphisms `ξ : x ⟶ z` and
`η : y ⟶ z` lying over `i` and `j` and agreeing on `u`. -/
structure Cocone (s : SquareSpan p f g) (i : V ⟶ Z) (j : W ⟶ Z) where
  /-- The object over `Z`. -/
  z : 𝒳
  /-- The morphism over `i`. -/
  ξ : s.x ⟶ z
  /-- The morphism over `j`. -/
  η : s.y ⟶ z
  isHomLift_ξ : p.IsHomLift i ξ
  isHomLift_η : p.IsHomLift j η
  w : s.α ≫ ξ = s.β ≫ η

attribute [instance] Cocone.isHomLift_ξ Cocone.isHomLift_η

/-- A morphism of cocones over one span: a morphism of the vertices lying over the identity of
`Z` and compatible with the two legs. -/
structure Cocone.Hom {s : SquareSpan p f g} {i : V ⟶ Z} {j : W ⟶ Z} (c c' : s.Cocone i j) where
  /-- The morphism of vertices. -/
  θ : c.z ⟶ c'.z
  isHomLift_θ : p.IsHomLift (𝟙 Z) θ
  comm_ξ : c.ξ ≫ θ = c'.ξ
  comm_η : c.η ≫ θ = c'.η

attribute [instance] Cocone.Hom.isHomLift_θ

attribute [reassoc] Cocone.Hom.comm_ξ Cocone.Hom.comm_η Cocone.w

end SquareSpan

/-- Cocones over spans over `(f, g)` for the pair `(i, j)` are *unique up to unique
isomorphism*: between any two cocones over one span there is exactly one morphism of cocones. -/
def HasUniqueSquareCocones (p : 𝒳 ⥤ 𝒞) {U V W Z : 𝒞} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z)
    (j : W ⟶ Z) : Prop :=
  ∀ (s : SquareSpan p f g) (c c' : s.Cocone i j), Nonempty (c.Hom c') ∧
    ∀ h h' : c.Hom c', h.θ = h'.θ

end CategoryTheory.Functor

/-! ### Lifts and fill-ins in a category fibred in groupoids -/

namespace CategoryTheory.Functor

open Limits

universe w v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒞}

/-- The converse of `CategoryTheory.Functor.fibreHom_of_isHomLift_id`. -/
lemma isHomLift_id_of_fibreHom {V : 𝒞} {a b : 𝒳} {ha : p.obj a = V} {hb : p.obj b = V}
    {φ : a ⟶ b} (h : FibreHom p a b ha hb φ) : p.IsHomLift (𝟙 V) φ := by
  have := h
  refine IsHomLift.of_fac' p (𝟙 V) φ ha hb ?_
  simpa using IsHomLift.fac' p (eqToHom ha ≫ eqToHom hb.symm) φ

namespace IsFiberedInGroupoids

variable (hp : p.IsFiberedInGroupoids)
include hp

/-- In a category fibred in groupoids a morphism lying over an isomorphism of the base is an
isomorphism. -/
lemma isIso_of_isHomLift_isIso {R S : 𝒞} (f : R ⟶ S) [IsIso f] {a b : 𝒳} (φ : a ⟶ b)
    [p.IsHomLift f φ] : IsIso φ := by
  have := hp.isStronglyCartesian_homLift f φ
  exact IsStronglyCartesian.isIso_of_base_isIso p f φ

/-- The fill-in of a category fibred in groupoids: a morphism `φ' : a' ⟶ b` over `g ≫ f`
factors uniquely through any morphism `φ : a ⟶ b` over `f`, by a morphism over `g`. -/
noncomputable def fill {R R' S : 𝒞} {f : R ⟶ S} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {a a' b : 𝒳} (φ : a ⟶ b) [p.IsHomLift f φ] (φ' : a' ⟶ b) [p.IsHomLift f' φ'] : a' ⟶ a :=
  haveI := hp.isStronglyCartesian_homLift f φ
  IsStronglyCartesian.map p f φ hf' φ'

lemma fill_isHomLift {R R' S : 𝒞} {f : R ⟶ S} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {a a' b : 𝒳} (φ : a ⟶ b) [p.IsHomLift f φ] (φ' : a' ⟶ b) [p.IsHomLift f' φ'] :
    p.IsHomLift g (hp.fill hf' φ φ') := by
  have := hp.isStronglyCartesian_homLift f φ
  exact IsStronglyCartesian.map_isHomLift p f φ hf' φ'

@[reassoc (attr := simp)]
lemma fill_fac {R R' S : 𝒞} {f : R ⟶ S} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {a a' b : 𝒳} (φ : a ⟶ b) [p.IsHomLift f φ] (φ' : a' ⟶ b) [p.IsHomLift f' φ'] :
    hp.fill hf' φ φ' ≫ φ = φ' := by
  have := hp.isStronglyCartesian_homLift f φ
  exact IsStronglyCartesian.fac p f φ hf' φ'

/-- Two morphisms over the same base morphism into the source of a morphism of a category
fibred in groupoids agree as soon as their composites with it agree. -/
lemma hom_ext {R R' S : 𝒞} {f : R ⟶ S} (g : R' ⟶ R) {a a' b : 𝒳} (φ : a ⟶ b)
    [p.IsHomLift f φ] {ψ ψ' : a' ⟶ a} [p.IsHomLift g ψ] [p.IsHomLift g ψ']
    (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  have := hp.isStronglyCartesian_homLift f φ
  exact IsStronglyCartesian.ext p f φ g h

/-- `hom_ext` for two morphisms lying over equal base morphisms. -/
private lemma hom_ext_of_eq {R R' S : 𝒞} {f : R ⟶ S} {g g' : R' ⟶ R} (hgg : g = g') {a a' b : 𝒳}
    (φ : a ⟶ b) [p.IsHomLift f φ] {ψ ψ' : a' ⟶ a} [p.IsHomLift g ψ] [p.IsHomLift g' ψ']
    (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  subst hgg
  exact hp.hom_ext (f := f) g φ h

/-- A chosen lift of a base morphism to a morphism with prescribed target. -/
lemma exists_lift' {R S : 𝒞} (f : R ⟶ S) (b : 𝒳) (hb : p.obj b = S) :
    ∃ (a : 𝒳) (φ : a ⟶ b), p.IsHomLift f φ :=
  hp.exists_lift f b hb

end IsFiberedInGroupoids

/-! ### Gluing morphisms out of an object along a one-member covering -/

section Glue

variable {J : GrothendieckTopology 𝒞}

/-- **Morphisms out of an object glue along a covering family.** Let `p` be a stack in groupoids,
let `e k : V₁ k ⟶ V` be a covering family with fibre products `V₂ k l = V₁ k ×_V V₁ l`, and let
`r k : x₁ k ⟶ x` lie over `e k`. A family of morphisms `ζ₁ k : x₁ k ⟶ z` over `e k ≫ m` which
agree on the overlaps is `r k ≫ ζ` for exactly one morphism `ζ : x ⟶ z` over `m`. Agreement on
the overlaps is asked for every pair of morphisms into `x₁ k` and `x₁ l` over the two projections
which agree in `x`, so no choice of restriction enters the statement. -/
theorem IsStackInGroupoids.existsUnique_hom_of_cover (hp : p.IsStackInGroupoids.{w} J)
    {V Z : 𝒞} {I : Type w} {V₁ : I → 𝒞} (e : ∀ k, V₁ k ⟶ V) (he : Sieve.ofArrows V₁ e ∈ J V)
    {V₂ : I → I → 𝒞} (π₁ : ∀ k l, V₂ k l ⟶ V₁ k) (π₂ : ∀ k l, V₂ k l ⟶ V₁ l)
    (hV₂ : ∀ k l, IsPullback (π₁ k l) (π₂ k l) (e k) (e l)) (m : V ⟶ Z) {x z : 𝒳}
    (hx : p.obj x = V) {x₁ : I → 𝒳} (r : ∀ k, x₁ k ⟶ x) [∀ k, p.IsHomLift (e k) (r k)]
    (hz : p.obj z = Z) (ζ₁ : ∀ k, x₁ k ⟶ z) [∀ k, p.IsHomLift (e k ≫ m) (ζ₁ k)]
    (hζ : ∀ k l (x₂ : 𝒳) (r₁ : x₂ ⟶ x₁ k) (r₂ : x₂ ⟶ x₁ l), p.IsHomLift (π₁ k l) r₁ →
      p.IsHomLift (π₂ k l) r₂ → r₁ ≫ r k = r₂ ≫ r l → r₁ ≫ ζ₁ k = r₂ ≫ ζ₁ l) :
    ∃! ζ : x ⟶ z, p.IsHomLift m ζ ∧ ∀ k, r k ≫ ζ = ζ₁ k := by
  have hg := hp.isFiberedInGroupoids
  have : p.IsFibered := hg.isFibered
  have hx₁ : ∀ k, p.obj (x₁ k) = V₁ k := fun k => IsHomLift.domain_eq p (e k) (r k)
  obtain ⟨y, c, hc⟩ := hg.exists_lift' m z hz
  have hy : p.obj y = V := IsHomLift.domain_eq p m c
  let xr : ∀ k, Restriction p (e k) x hx := fun k =>
    Restriction.ofCartesian (hx₁ k) hx (r k) (hg.isStronglyCartesian_homLift (e k) (r k))
  let yr : ∀ k, Restriction p (e k) y hy := fun k => Restriction.ofIsFiberedInGroupoids p hg _ y hy
  let xrij : ∀ k l, Restriction p (π₁ k l ≫ e k) x hx := fun k l =>
    Restriction.ofIsFiberedInGroupoids p hg _ x hx
  let yrij : ∀ k l, Restriction p (π₁ k l ≫ e k) y hy := fun k l =>
    Restriction.ofIsFiberedInGroupoids p hg _ y hy
  have hyr : ∀ k, p.IsHomLift (e k) (yr k).hom := fun k => (yr k).isHomLift_hom
  -- the local morphisms of the fibres over the `V₁ k`
  let φ : ∀ k, x₁ k ⟶ (yr k).pt := fun k =>
    hg.fill (f := e k ≫ m) (g := 𝟙 (V₁ k)) (f' := e k ≫ m) (by simp) ((yr k).hom ≫ c) (ζ₁ k)
  have hφ : ∀ k, p.IsHomLift (𝟙 (V₁ k)) (φ k) := fun k => hg.fill_isHomLift _ _ _
  have hφfac : ∀ k, φ k ≫ (yr k).hom ≫ c = ζ₁ k := fun k => hg.fill_fac _ _ _
  -- agreement on the overlaps
  have hcompat : ∀ k l, ∃ γ : (xrij k l).pt ⟶ (yrij k l).pt,
      FibreHom p (xrij k l).pt (yrij k l).pt (xrij k l).hpt (yrij k l).hpt γ ∧
      IsRestrictionOf p (π₁ k l) rfl rfl (xr k) (yr k) (xrij k l) (yrij k l) (φ k) γ ∧
      IsRestrictionOf p (π₂ k l) (hV₂ k l).w (hV₂ k l).w (xr l) (yr l) (xrij k l) (yrij k l)
        (φ l) γ := by
    intro k l
    let k₁ : (xrij k l).pt ⟶ x₁ k := Restriction.compTo p (π₁ k l) (e k) rfl (xr k) (xrij k l)
    let k₂ : (xrij k l).pt ⟶ x₁ l :=
      Restriction.compTo p (π₂ k l) (e l) (hV₂ k l).w (xr l) (xrij k l)
    have hk₁ : p.IsHomLift (π₁ k l) k₁ := Restriction.isHomLift_compTo _ _ _ _ _
    have hk₂ : p.IsHomLift (π₂ k l) k₂ := Restriction.isHomLift_compTo _ _ _ _ _
    have hk₁r : k₁ ≫ r k = (xrij k l).hom := Restriction.compTo_hom p _ _ rfl (xr k) _
    have hk₂r : k₂ ≫ r l = (xrij k l).hom := Restriction.compTo_hom p _ _ (hV₂ k l).w (xr l) _
    have hkζ : k₁ ≫ ζ₁ k = k₂ ≫ ζ₁ l := hζ k l _ k₁ k₂ hk₁ hk₂ (hk₁r.trans hk₂r.symm)
    let l₁ := Restriction.compTo p (π₁ k l) (e k) rfl (yr k) (yrij k l)
    let l₂ := Restriction.compTo p (π₂ k l) (e l) (hV₂ k l).w (yr l) (yrij k l)
    have hl₁ : p.IsHomLift (π₁ k l) l₁ := Restriction.isHomLift_compTo _ _ _ _ _
    have hl₂ : p.IsHomLift (π₂ k l) l₂ := Restriction.isHomLift_compTo _ _ _ _ _
    have hl₁r : l₁ ≫ (yr k).hom = (yrij k l).hom := Restriction.compTo_hom p _ _ rfl (yr k) _
    have hl₂r : l₂ ≫ (yr l).hom = (yrij k l).hom :=
      Restriction.compTo_hom p _ _ (hV₂ k l).w (yr l) _
    have : p.IsHomLift (𝟙 (V₁ k)) (φ k) := hφ k
    have : p.IsHomLift (𝟙 (V₁ l)) (φ l) := hφ l
    have hk₁φ : p.IsHomLift (π₁ k l) (k₁ ≫ φ k) := inferInstance
    let γ : (xrij k l).pt ⟶ (yrij k l).pt :=
      hg.fill (f := π₁ k l) (g := 𝟙 (V₂ k l)) (f' := π₁ k l) (by simp) l₁ (k₁ ≫ φ k)
    have hγ : p.IsHomLift (𝟙 (V₂ k l)) γ := hg.fill_isHomLift _ _ _
    have hγ₁ : γ ≫ l₁ = k₁ ≫ φ k := hg.fill_fac _ _ _
    have hγ₂ : γ ≫ l₂ = k₂ ≫ φ l := by
      have h₁ : p.IsHomLift (π₂ k l) (γ ≫ l₂) := inferInstance
      have h₂ : p.IsHomLift (π₂ k l) (k₂ ≫ φ l) := inferInstance
      have : p.IsHomLift (e l) (yr l).hom := hyr l
      refine hg.hom_ext (f := e l ≫ m) (π₂ k l) ((yr l).hom ≫ c) ?_
      calc (γ ≫ l₂) ≫ (yr l).hom ≫ c = γ ≫ (yrij k l).hom ≫ c := by
            rw [Category.assoc, reassoc_of% hl₂r]
        _ = (γ ≫ l₁) ≫ (yr k).hom ≫ c := by rw [Category.assoc, reassoc_of% hl₁r]
        _ = k₁ ≫ ζ₁ k := by rw [hγ₁, Category.assoc, hφfac]
        _ = k₂ ≫ ζ₁ l := hkζ
        _ = (k₂ ≫ φ l) ≫ (yr l).hom ≫ c := by rw [Category.assoc, hφfac]
    exact ⟨γ, fibreHom_of_isHomLift_id _ _ hγ, hγ₁, hγ₂⟩
  obtain ⟨g, ⟨hgF, -, hgfac⟩, hguniq⟩ := hp.isom_isSheaf x y hx hy V₁ e he V₂ π₁ π₂ hV₂ xr yr
    xrij yrij φ (fun k => fibreHom_of_isHomLift_id _ _ (hφ k))
    (fun k => hg.isIso_of_isHomLift_isIso (𝟙 (V₁ k)) (φ k)) hcompat
  have hgV : p.IsHomLift (𝟙 V) g := isHomLift_id_of_fibreHom hgF
  refine ⟨g ≫ c, ⟨inferInstance, fun k => ?_⟩, ?_⟩
  · have hgk : r k ≫ g = φ k ≫ (yr k).hom := hgfac k
    rw [reassoc_of% hgk, hφfac]
  · rintro ζ' ⟨hζ', hrζ'⟩
    let g' : x ⟶ y := hg.fill (f := m) (g := 𝟙 V) (f' := m) (by simp) c ζ'
    have hg' : p.IsHomLift (𝟙 V) g' := hg.fill_isHomLift _ _ _
    have hg'fac : g' ≫ c = ζ' := hg.fill_fac _ _ _
    have : g' = g := by
      refine hguniq g' ⟨fibreHom_of_isHomLift_id _ _ hg',
        hg.isIso_of_isHomLift_isIso (𝟙 V) g', fun k => ?_⟩
      change r k ≫ g' = φ k ≫ (yr k).hom
      have : p.IsHomLift (e k) (yr k).hom := hyr k
      have : p.IsHomLift (𝟙 (V₁ k)) (φ k) := hφ k
      have h₁ : p.IsHomLift (e k) (r k ≫ g') := inferInstance
      have h₂ : p.IsHomLift (e k) (φ k ≫ (yr k).hom) := inferInstance
      refine hg.hom_ext (f := m) (e k) c ?_
      rw [Category.assoc, hg'fac, hrζ', Category.assoc, hφfac]
    rw [← hg'fac, this]

/-- **Morphisms out of an object are determined locally.** Two morphisms `x ⟶ z` over the same
base morphism which agree after composing with each `r k` of a covering family are equal. -/
theorem IsStackInGroupoids.hom_ext_of_cover (hp : p.IsStackInGroupoids.{w} J)
    {V Z : 𝒞} {I : Type w} {V₁ : I → 𝒞} (e : ∀ k, V₁ k ⟶ V) (he : Sieve.ofArrows V₁ e ∈ J V)
    {V₂ : I → I → 𝒞} (π₁ : ∀ k l, V₂ k l ⟶ V₁ k) (π₂ : ∀ k l, V₂ k l ⟶ V₁ l)
    (hV₂ : ∀ k l, IsPullback (π₁ k l) (π₂ k l) (e k) (e l)) (m : V ⟶ Z) {x z : 𝒳}
    (hx : p.obj x = V) {x₁ : I → 𝒳} (r : ∀ k, x₁ k ⟶ x) [∀ k, p.IsHomLift (e k) (r k)]
    (hz : p.obj z = Z) {ζ ζ' : x ⟶ z} [p.IsHomLift m ζ] [p.IsHomLift m ζ']
    (h : ∀ k, r k ≫ ζ = r k ≫ ζ') : ζ = ζ' := by
  have : ∀ k, p.IsHomLift (e k ≫ m) (r k ≫ ζ) := fun k => inferInstance
  obtain ⟨_, -, huniq⟩ := hp.existsUnique_hom_of_cover e he π₁ π₂ hV₂ m hx r hz
    (fun k => r k ≫ ζ) (fun k l x₂ r₁ r₂ _ _ hr => by rw [reassoc_of% hr])
  exact (huniq ζ ⟨inferInstance, fun _ => rfl⟩).trans
    (huniq ζ' ⟨inferInstance, fun k => (h k).symm⟩).symm

lemma _root_.CategoryTheory.Functor.isHomLift_id_id' {R : 𝒞} {a : 𝒳} (ha : p.obj a = R) :
    p.IsHomLift (𝟙 R) (𝟙 a) := by
  subst ha; infer_instance

/-- **Objects glue along a covering family.** Let `p` be a stack in groupoids and let
`e k : V₁ k ⟶ V` be a covering family, with double and triple overlaps given by fibre products.
Gluing data for objects `z k` over the `V₁ k` are given, for each pair `(k, l)`, by an object
`t k l` over `V₂ k l` with morphisms `ρ k l : t k l ⟶ z k` and `σ k l : t k l ⟶ z l` over the two
projections — the identification of the two restrictions to the overlap — subject to the cocycle
condition, which is asked for every object over a triple overlap mapping compatibly to the three
`t`'s. Then there is an object `x` over `V` receiving morphisms `ζ k : z k ⟶ x` over `e k` which
agree on the overlaps. -/
theorem IsStackInGroupoids.exists_glue (hp : p.IsStackInGroupoids.{w} J)
    {V : 𝒞} {I : Type w} {V₁ : I → 𝒞} (e : ∀ k, V₁ k ⟶ V) (he : Sieve.ofArrows V₁ e ∈ J V)
    {V₂ : I → I → 𝒞} (π₁ : ∀ k l, V₂ k l ⟶ V₁ k) (π₂ : ∀ k l, V₂ k l ⟶ V₁ l)
    (hV₂ : ∀ k l, IsPullback (π₁ k l) (π₂ k l) (e k) (e l))
    {V₃ : I → I → I → 𝒞} (s₁₂ : ∀ k l m, V₃ k l m ⟶ V₂ k l) (s₂₃ : ∀ k l m, V₃ k l m ⟶ V₂ l m)
    (hV₃ : ∀ k l m, IsPullback (s₁₂ k l m) (s₂₃ k l m) (π₂ k l) (π₁ l m))
    (s₁₃ : ∀ k l m, V₃ k l m ⟶ V₂ k m)
    (hs₁₃₁ : ∀ k l m, s₁₃ k l m ≫ π₁ k m = s₁₂ k l m ≫ π₁ k l)
    (hs₁₃₂ : ∀ k l m, s₁₃ k l m ≫ π₂ k m = s₂₃ k l m ≫ π₂ l m)
    {z : I → 𝒳} (hz : ∀ k, p.obj (z k) = V₁ k) {t : I → I → 𝒳}
    (ρ : ∀ k l, t k l ⟶ z k) (σ : ∀ k l, t k l ⟶ z l)
    [∀ k l, p.IsHomLift (π₁ k l) (ρ k l)] [∀ k l, p.IsHomLift (π₂ k l) (σ k l)]
    (hcocycle : ∀ k l m (r : 𝒳) (m₁₂ : r ⟶ t k l) (m₂₃ : r ⟶ t l m) (m₁₃ : r ⟶ t k m),
      p.IsHomLift (s₁₂ k l m) m₁₂ → p.IsHomLift (s₂₃ k l m) m₂₃ →
      p.IsHomLift (s₁₃ k l m) m₁₃ → m₁₂ ≫ σ k l = m₂₃ ≫ ρ l m →
      m₁₂ ≫ ρ k l = m₁₃ ≫ ρ k m → m₂₃ ≫ σ l m = m₁₃ ≫ σ k m) :
    ∃ (x : 𝒳) (ζ : ∀ k, z k ⟶ x), p.obj x = V ∧ (∀ k, p.IsHomLift (e k) (ζ k)) ∧
      ∀ k l, ρ k l ≫ ζ k = σ k l ≫ ζ l := by
  have hg := hp.isFiberedInGroupoids
  have : p.IsFibered := hg.isFibered
  have ht : ∀ k l, p.obj (t k l) = V₂ k l := fun k l => IsHomLift.domain_eq p (π₁ k l) (ρ k l)
  let xrij : ∀ k l, Restriction p (π₁ k l) (z k) (hz k) := fun k l =>
    Restriction.ofCartesian (ht k l) (hz k) (ρ k l) (hg.isStronglyCartesian_homLift _ _)
  let xrji : ∀ k l, Restriction p (π₂ k l) (z l) (hz l) := fun k l =>
    Restriction.ofCartesian (ht k l) (hz l) (σ k l) (hg.isStronglyCartesian_homLift _ _)
  let q₁ : ∀ k l m, V₃ k l m ⟶ V₁ k := fun k l m => s₁₂ k l m ≫ π₁ k l
  let q₂ : ∀ k l m, V₃ k l m ⟶ V₁ l := fun k l m => s₁₂ k l m ≫ π₂ k l
  let q₃ : ∀ k l m, V₃ k l m ⟶ V₁ m := fun k l m => s₂₃ k l m ≫ π₂ l m
  let wi : ∀ k l m, Restriction p (q₁ k l m) (z k) (hz k) := fun k l m =>
    Restriction.ofIsFiberedInGroupoids p hg _ _ _
  let wj : ∀ k l m, Restriction p (q₂ k l m) (z l) (hz l) := fun k l m =>
    Restriction.ofIsFiberedInGroupoids p hg _ _ _
  let wk : ∀ k l m, Restriction p (q₃ k l m) (z m) (hz m) := fun k l m =>
    Restriction.ofIsFiberedInGroupoids p hg _ _ _
  -- the canonical comparisons of the triple-overlap restrictions with the `t`'s
  let cij : ∀ k l m, (wi k l m).pt ⟶ t k l := fun k l m =>
    Restriction.compTo p (s₁₂ k l m) (π₁ k l) rfl (xrij k l) (wi k l m)
  let cji : ∀ k l m, (wj k l m).pt ⟶ t k l := fun k l m =>
    Restriction.compTo p (s₁₂ k l m) (π₂ k l) rfl (xrji k l) (wj k l m)
  let cjk : ∀ k l m, (wj k l m).pt ⟶ t l m := fun k l m =>
    Restriction.compTo p (s₂₃ k l m) (π₁ l m) ((hV₃ k l m).w) (xrij l m) (wj k l m)
  let ckj : ∀ k l m, (wk k l m).pt ⟶ t l m := fun k l m =>
    Restriction.compTo p (s₂₃ k l m) (π₂ l m) rfl (xrji l m) (wk k l m)
  let cik : ∀ k l m, (wi k l m).pt ⟶ t k m := fun k l m =>
    Restriction.compTo p (s₁₃ k l m) (π₁ k m) (hs₁₃₁ k l m).symm (xrij k m) (wi k l m)
  let cki : ∀ k l m, (wk k l m).pt ⟶ t k m := fun k l m =>
    Restriction.compTo p (s₁₃ k l m) (π₂ k m) (hs₁₃₂ k l m).symm (xrji k m) (wk k l m)
  have hcij : ∀ k l m, p.IsHomLift (s₁₂ k l m) (cij k l m) := fun _ _ _ =>
    Restriction.isHomLift_compTo _ _ _ _ _
  have hcji : ∀ k l m, p.IsHomLift (s₁₂ k l m) (cji k l m) := fun _ _ _ =>
    Restriction.isHomLift_compTo _ _ _ _ _
  have hcjk : ∀ k l m, p.IsHomLift (s₂₃ k l m) (cjk k l m) := fun _ _ _ =>
    Restriction.isHomLift_compTo _ _ _ _ _
  have hckj : ∀ k l m, p.IsHomLift (s₂₃ k l m) (ckj k l m) := fun _ _ _ =>
    Restriction.isHomLift_compTo _ _ _ _ _
  have hcik : ∀ k l m, p.IsHomLift (s₁₃ k l m) (cik k l m) := fun _ _ _ =>
    Restriction.isHomLift_compTo _ _ _ _ _
  have hcki : ∀ k l m, p.IsHomLift (s₁₃ k l m) (cki k l m) := fun _ _ _ =>
    Restriction.isHomLift_compTo _ _ _ _ _
  have ecij : ∀ k l m, cij k l m ≫ ρ k l = (wi k l m).hom := fun _ _ _ =>
    Restriction.compTo_hom p _ _ _ _ _
  have ecji : ∀ k l m, cji k l m ≫ σ k l = (wj k l m).hom := fun _ _ _ =>
    Restriction.compTo_hom p _ _ _ _ _
  have ecjk : ∀ k l m, cjk k l m ≫ ρ l m = (wj k l m).hom := fun _ _ _ =>
    Restriction.compTo_hom p _ _ _ _ _
  have eckj : ∀ k l m, ckj k l m ≫ σ l m = (wk k l m).hom := fun _ _ _ =>
    Restriction.compTo_hom p _ _ _ _ _
  have ecik : ∀ k l m, cik k l m ≫ ρ k m = (wi k l m).hom := fun _ _ _ =>
    Restriction.compTo_hom p _ _ _ _ _
  have ecki : ∀ k l m, cki k l m ≫ σ k m = (wk k l m).hom := fun _ _ _ =>
    Restriction.compTo_hom p _ _ _ _ _
  -- the gluing morphisms over the triple overlaps
  let αij : ∀ k l m, (wi k l m).pt ⟶ (wj k l m).pt := fun k l m =>
    hg.fill (f := s₁₂ k l m) (g := 𝟙 _) (f' := s₁₂ k l m) (by simp) (cji k l m) (cij k l m)
  let αjk : ∀ k l m, (wj k l m).pt ⟶ (wk k l m).pt := fun k l m =>
    hg.fill (f := s₂₃ k l m) (g := 𝟙 _) (f' := s₂₃ k l m) (by simp) (ckj k l m) (cjk k l m)
  let αik : ∀ k l m, (wi k l m).pt ⟶ (wk k l m).pt := fun k l m =>
    hg.fill (f := s₁₃ k l m) (g := 𝟙 _) (f' := s₁₃ k l m) (by simp) (cki k l m) (cik k l m)
  have hαij : ∀ k l m, p.IsHomLift (𝟙 _) (αij k l m) := fun _ _ _ => hg.fill_isHomLift _ _ _
  have hαjk : ∀ k l m, p.IsHomLift (𝟙 _) (αjk k l m) := fun _ _ _ => hg.fill_isHomLift _ _ _
  have hαik : ∀ k l m, p.IsHomLift (𝟙 _) (αik k l m) := fun _ _ _ => hg.fill_isHomLift _ _ _
  have eαij : ∀ k l m, αij k l m ≫ cji k l m = cij k l m := fun _ _ _ => hg.fill_fac _ _ _
  have eαjk : ∀ k l m, αjk k l m ≫ ckj k l m = cjk k l m := fun _ _ _ => hg.fill_fac _ _ _
  have eαik : ∀ k l m, αik k l m ≫ cki k l m = cik k l m := fun _ _ _ => hg.fill_fac _ _ _
  have hcoc : ∀ k l m, αik k l m = αij k l m ≫ αjk k l m := by
    intro k l m
    have : p.IsHomLift (q₃ k l m) (wk k l m).hom := (wk k l m).isHomLift_hom
    have := hαij k l m
    have := hαjk k l m
    have := hαik k l m
    have := hcjk k l m
    have h := hcocycle k l m _ (cij k l m) (αij k l m ≫ cjk k l m) (cik k l m) (hcij k l m)
      inferInstance (hcik k l m) (by rw [Category.assoc, ecjk, ← eαij, Category.assoc, ecji])
      (by rw [ecij, ecik])
    refine hg.hom_ext (f := q₃ k l m) (𝟙 _) (wk k l m).hom ?_
    calc αik k l m ≫ (wk k l m).hom = cik k l m ≫ σ k m := by
          rw [← ecki, ← Category.assoc, eαik]
      _ = (αij k l m ≫ cjk k l m) ≫ σ l m := h.symm
      _ = (αij k l m ≫ αjk k l m) ≫ (wk k l m).hom := by
          rw [← eαjk, ← eckj]; simp only [Category.assoc]
  let D : DescentDatum p V₁ e V₂ π₁ π₂ hV₂ V₃ s₁₂ s₂₃ hV₃ q₁ q₂ q₃
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) :=
    { x := z
      hx := hz
      xrij := xrij
      xrji := xrji
      φ := fun k l => 𝟙 (t k l)
      φ_fibreHom := fun k l => fibreHom_of_isHomLift_id _ _ (isHomLift_id_id' (ht k l))
      φ_iso := fun k l => IsIso.id (t k l)
      wi := wi
      wj := wj
      wk := wk
      αij := αij
      αjk := αjk
      αik := αik
      αij_restr := fun k l m => by
        change αij k l m ≫ cji k l m = cij k l m ≫ 𝟙 _
        rw [eαij, Category.comp_id]
      αjk_restr := fun k l m => by
        change αjk k l m ≫ ckj k l m = cjk k l m ≫ 𝟙 _
        rw [eαjk, Category.comp_id]
      s₁₃ := s₁₃
      hs₁₃₁ := hs₁₃₁
      hs₁₃₂ := hs₁₃₂
      αik_restr := fun k l m => by
        change αik k l m ≫ cki k l m = cik k l m ≫ 𝟙 _
        rw [eαik, Category.comp_id]
      cocycle := hcoc }
  obtain ⟨x, hx, xr, ψ, hψF, hψiso, hov⟩ := hp.effective_descent V₁ e he V₂ π₁ π₂ hV₂ V₃
    s₁₂ s₂₃ hV₃ q₁ q₂ q₃ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) D
  have hψ : ∀ k, p.IsHomLift (𝟙 (V₁ k)) (ψ k) := fun k => isHomLift_id_of_fibreHom (hψF k)
  have hxr : ∀ k, p.IsHomLift (e k) (xr k).hom := fun k => (xr k).isHomLift_hom
  refine ⟨x, fun k => CategoryTheory.inv (ψ k) ≫ (xr k).hom, hx, fun k => ?_, fun k l => ?_⟩
  · have := hψ k
    have := hψiso k
    have := hxr k
    infer_instance
  · obtain ⟨xrij', ψir, ψjr, -, -, hir, hjr, h₁, h₂, h₃⟩ := hov k l
    have e₁ : ψir ≫ ρ k l = Restriction.compTo p (π₁ k l) (e k) rfl (xr k) xrij' ≫ ψ k := by
      have := h₁
      simp only [IsRestrictionOf] at this
      rw [← this]
      congr 1
      have := Restriction.compTo_hom p (π₁ k l) (𝟙 _) (by simp) (Restriction.id p (z k) (hz k))
        (xrij k l)
      simp only [Restriction.id, Category.comp_id] at this
      exact this.symm
    have e₂ : ψjr ≫ σ k l =
        Restriction.compTo p (π₂ k l) (e l) (hV₂ k l).w (xr l) xrij' ≫ ψ l := by
      have := h₂
      simp only [IsRestrictionOf] at this
      rw [← this]
      congr 1
      have := Restriction.compTo_hom p (π₂ k l) (𝟙 _) (by simp) (Restriction.id p (z l) (hz l))
        (xrji k l)
      simp only [Restriction.id, Category.comp_id] at this
      exact this.symm
    have e₃ : ψir = ψjr := (Category.comp_id ψir).symm.trans h₃
    let a : xrij'.pt ⟶ t k l := ψir
    let b : xrij'.pt ⟶ t k l := ψjr
    have ea : a ≫ ρ k l = Restriction.compTo p (π₁ k l) (e k) rfl (xr k) xrij' ≫ ψ k := e₁
    have eb : b ≫ σ k l = Restriction.compTo p (π₂ k l) (e l) (hV₂ k l).w (xr l) xrij' ≫ ψ l :=
      e₂
    have eab : a = b := e₃
    have : IsIso a := hir
    have key : a ≫ ρ k l ≫ CategoryTheory.inv (ψ k) ≫ (xr k).hom =
        a ≫ σ k l ≫ CategoryTheory.inv (ψ l) ≫ (xr l).hom := by
      calc a ≫ ρ k l ≫ CategoryTheory.inv (ψ k) ≫ (xr k).hom = xrij'.hom := by
            rw [reassoc_of% ea, IsIso.hom_inv_id_assoc, Restriction.compTo_hom]
        _ = a ≫ σ k l ≫ CategoryTheory.inv (ψ l) ≫ (xr l).hom := by
            rw [eab, reassoc_of% eb, IsIso.hom_inv_id_assoc, Restriction.compTo_hom]
    exact (cancel_epi a).1 key

end Glue

/-! ### Morphisms of squares and pulling cocones back -/

section Pull

/-- A commutative square of the base, recorded as its four morphisms and its commutativity. -/
structure BaseSquare (𝒞 : Type u₁) [Category.{v₁} 𝒞] where
  /-- The initial corner. -/
  U : 𝒞
  /-- The first middle corner. -/
  V : 𝒞
  /-- The second middle corner. -/
  W : 𝒞
  /-- The terminal corner. -/
  Z : 𝒞
  f : U ⟶ V
  g : U ⟶ W
  i : V ⟶ Z
  j : W ⟶ Z
  w : f ≫ i = g ≫ j

/-- A morphism of commutative squares of the base: four morphisms between corresponding corners
making the four side faces of the cube commute. -/
@[ext]
structure BaseSquare.Hom (S T : BaseSquare 𝒞) where
  aU : S.U ⟶ T.U
  aV : S.V ⟶ T.V
  aW : S.W ⟶ T.W
  aZ : S.Z ⟶ T.Z
  wf : S.f ≫ aV = aU ≫ T.f
  wg : S.g ≫ aW = aU ≫ T.g
  wi : S.i ≫ aZ = aV ≫ T.i
  wj : S.j ≫ aZ = aW ≫ T.j

/-- Composition of morphisms of squares. -/
@[simps]
def BaseSquare.Hom.comp {S T R : BaseSquare 𝒞} (a : S.Hom T) (b : T.Hom R) : S.Hom R where
  aU := a.aU ≫ b.aU
  aV := a.aV ≫ b.aV
  aW := a.aW ≫ b.aW
  aZ := a.aZ ≫ b.aZ
  wf := by rw [reassoc_of% a.wf, b.wf, Category.assoc]
  wg := by rw [reassoc_of% a.wg, b.wg, Category.assoc]
  wi := by rw [reassoc_of% a.wi, b.wi, Category.assoc]
  wj := by rw [reassoc_of% a.wj, b.wj, Category.assoc]

/-- A morphism of spans lying over a morphism of squares. -/
structure SquareSpan.Hom {S T : BaseSquare 𝒞} (a : S.Hom T) (s : SquareSpan p S.f S.g)
    (t : SquareSpan p T.f T.g) where
  mu : s.u ⟶ t.u
  mx : s.x ⟶ t.x
  my : s.y ⟶ t.y
  isHomLift_mu : p.IsHomLift a.aU mu
  isHomLift_mx : p.IsHomLift a.aV mx
  isHomLift_my : p.IsHomLift a.aW my
  comm_α : s.α ≫ mx = mu ≫ t.α
  comm_β : s.β ≫ my = mu ≫ t.β

attribute [instance] SquareSpan.Hom.isHomLift_mu SquareSpan.Hom.isHomLift_mx
  SquareSpan.Hom.isHomLift_my

variable (hp : p.IsFiberedInGroupoids)
include hp

/-- **Pulling a cocone back along a morphism of spans.** Given a morphism of spans `m : s ⟶ t`
over a morphism of squares `a : S ⟶ T` and a cocone `c` over `t`, there is a cocone `c'` over
`s` together with a morphism `c'.z ⟶ c.z` over `a.aZ` compatible with the two legs. -/
theorem SquareSpan.exists_pull {S T : BaseSquare 𝒞} {a : S.Hom T} {s : SquareSpan p S.f S.g}
    {t : SquareSpan p T.f T.g} (m : SquareSpan.Hom a s t) (c : t.Cocone T.i T.j) :
    ∃ (c' : s.Cocone S.i S.j) (ζ : c'.z ⟶ c.z), p.IsHomLift a.aZ ζ ∧
      c'.ξ ≫ ζ = m.mx ≫ c.ξ ∧ c'.η ≫ ζ = m.my ≫ c.η := by
  have hz : p.obj c.z = T.Z := IsHomLift.codomain_eq p T.i c.ξ
  obtain ⟨z', ζ, hζ⟩ := hp.exists_lift' a.aZ c.z hz
  have h₁ : p.IsHomLift (S.i ≫ a.aZ) (m.mx ≫ c.ξ) := by rw [a.wi]; infer_instance
  have h₂ : p.IsHomLift (S.j ≫ a.aZ) (m.my ≫ c.η) := by rw [a.wj]; infer_instance
  let ξ' := hp.fill (f := a.aZ) (g := S.i) (f' := S.i ≫ a.aZ) rfl ζ (m.mx ≫ c.ξ)
  let η' := hp.fill (f := a.aZ) (g := S.j) (f' := S.j ≫ a.aZ) rfl ζ (m.my ≫ c.η)
  have hξ' : p.IsHomLift S.i ξ' := hp.fill_isHomLift _ _ _
  have hη' : p.IsHomLift S.j η' := hp.fill_isHomLift _ _ _
  have eξ : ξ' ≫ ζ = m.mx ≫ c.ξ := hp.fill_fac _ _ _
  have eη : η' ≫ ζ = m.my ≫ c.η := hp.fill_fac _ _ _
  refine ⟨⟨z', ξ', η', hξ', hη', ?_⟩, ζ, hζ, eξ, eη⟩
  refine hp.hom_ext_of_eq (f := a.aZ) S.w ζ ?_
  rw [Category.assoc, eξ, Category.assoc, eη, reassoc_of% m.comm_α, reassoc_of% m.comm_β,
    c.w]

/-- **Restricting a span along a morphism of squares.** Over any morphism of squares into the
square of a span there is a span with a morphism to it. -/
theorem SquareSpan.exists_restrict {S T : BaseSquare 𝒞} (a : S.Hom T)
    (t : SquareSpan p T.f T.g) : ∃ (s : SquareSpan p S.f S.g), Nonempty (SquareSpan.Hom a s t) := by
  have hu : p.obj t.u = T.U := IsHomLift.domain_eq p T.f t.α
  have hx : p.obj t.x = T.V := IsHomLift.codomain_eq p T.f t.α
  have hy : p.obj t.y = T.W := IsHomLift.codomain_eq p T.g t.β
  obtain ⟨u', mu, hmu⟩ := hp.exists_lift' a.aU t.u hu
  obtain ⟨x', mx, hmx⟩ := hp.exists_lift' a.aV t.x hx
  obtain ⟨y', my, hmy⟩ := hp.exists_lift' a.aW t.y hy
  have h₁ : p.IsHomLift (S.f ≫ a.aV) (mu ≫ t.α) := by rw [a.wf]; infer_instance
  have h₂ : p.IsHomLift (S.g ≫ a.aW) (mu ≫ t.β) := by rw [a.wg]; infer_instance
  let α' := hp.fill (f := a.aV) (g := S.f) (f' := S.f ≫ a.aV) rfl mx (mu ≫ t.α)
  let β' := hp.fill (f := a.aW) (g := S.g) (f' := S.g ≫ a.aW) rfl my (mu ≫ t.β)
  have hα' : p.IsHomLift S.f α' := hp.fill_isHomLift _ _ _
  have hβ' : p.IsHomLift S.g β' := hp.fill_isHomLift _ _ _
  have eα : α' ≫ mx = mu ≫ t.α := hp.fill_fac _ _ _
  have eβ : β' ≫ my = mu ≫ t.β := hp.fill_fac _ _ _
  exact ⟨⟨u', x', y', α', β', hα', hβ'⟩, ⟨⟨mu, mx, my, hmu, hmx, hmy, eα, eβ⟩⟩⟩

/-- **Factoring a morphism of spans.** A morphism of spans over `a ≫ b` factors through any
morphism of spans over `b` with the same target, by a morphism of spans over `a`. -/
theorem SquareSpan.Hom.exists_factor {S T R : BaseSquare 𝒞} {a : S.Hom T} {b : T.Hom R}
    {a₀ : S.Hom R} (hab : a.comp b = a₀) {s : SquareSpan p S.f S.g} {t : SquareSpan p T.f T.g}
    {r : SquareSpan p R.f R.g} (h₀ : SquareSpan.Hom a₀ s r) (h₁ : SquareSpan.Hom b t r) :
    ∃ g : SquareSpan.Hom a s t, g.mu ≫ h₁.mu = h₀.mu ∧ g.mx ≫ h₁.mx = h₀.mx ∧
      g.my ≫ h₁.my = h₀.my := by
  subst hab
  have : p.IsHomLift (a.aU ≫ b.aU) h₀.mu := h₀.isHomLift_mu
  have : p.IsHomLift (a.aV ≫ b.aV) h₀.mx := h₀.isHomLift_mx
  have : p.IsHomLift (a.aW ≫ b.aW) h₀.my := h₀.isHomLift_my
  let mu := hp.fill (f := b.aU) (g := a.aU) (f' := a.aU ≫ b.aU) rfl h₁.mu h₀.mu
  let mx := hp.fill (f := b.aV) (g := a.aV) (f' := a.aV ≫ b.aV) rfl h₁.mx h₀.mx
  let my := hp.fill (f := b.aW) (g := a.aW) (f' := a.aW ≫ b.aW) rfl h₁.my h₀.my
  have hmu : p.IsHomLift a.aU mu := hp.fill_isHomLift _ _ _
  have hmx : p.IsHomLift a.aV mx := hp.fill_isHomLift _ _ _
  have hmy : p.IsHomLift a.aW my := hp.fill_isHomLift _ _ _
  have emu : mu ≫ h₁.mu = h₀.mu := hp.fill_fac _ _ _
  have emx : mx ≫ h₁.mx = h₀.mx := hp.fill_fac _ _ _
  have emy : my ≫ h₁.my = h₀.my := hp.fill_fac _ _ _
  have hα : s.α ≫ mx = mu ≫ t.α := by
    refine hp.hom_ext_of_eq (f := b.aV) a.wf h₁.mx ?_
    rw [Category.assoc, emx, Category.assoc, h₁.comm_α, reassoc_of% emu, h₀.comm_α]
  have hβ : s.β ≫ my = mu ≫ t.β := by
    refine hp.hom_ext_of_eq (f := b.aW) a.wg h₁.my ?_
    rw [Category.assoc, emy, Category.assoc, h₁.comm_β, reassoc_of% emu, h₀.comm_β]
  exact ⟨⟨mu, mx, my, hmu, hmx, hmy, hα, hβ⟩, emu, emx, emy⟩

end Pull

/-! ### Cocones exist as soon as they exist locally -/

section Local

variable {J : GrothendieckTopology 𝒞}

/-- **Existence of cocones is local on the terminal corner.** Let `p` be a stack in groupoids and
let `Q` be a commutative square of the base. Let `c k : Q₁ k ⟶ Q` be a family of morphisms of
squares whose four corner families are coverings, with double overlaps `Q₂ k l` whose four corner
squares are fibre products and triple overlaps `Q₃ k l m` whose terminal corner is the fibre
product of the two double overlaps. If every restriction of a span `s` over `Q` to a `Q₁ k` has
a cocone, and cocones over the double and triple overlaps are unique up to unique isomorphism,
then `s` has a cocone. The covering may depend on `s`. -/
theorem IsStackInGroupoids.nonempty_cocone_of_cover (hp : p.IsStackInGroupoids.{w} J)
    (Q : BaseSquare 𝒞) {I : Type w} (Q₁ : I → BaseSquare 𝒞) (c : ∀ k, (Q₁ k).Hom Q)
    (hcU : Sieve.ofArrows _ (fun k => (c k).aU) ∈ J Q.U)
    (hcV : Sieve.ofArrows _ (fun k => (c k).aV) ∈ J Q.V)
    (hcW : Sieve.ofArrows _ (fun k => (c k).aW) ∈ J Q.W)
    (hcZ : Sieve.ofArrows _ (fun k => (c k).aZ) ∈ J Q.Z)
    (Q₂ : I → I → BaseSquare 𝒞) (d₁ : ∀ k l, (Q₂ k l).Hom (Q₁ k))
    (d₂ : ∀ k l, (Q₂ k l).Hom (Q₁ l)) (hd : ∀ k l, (d₁ k l).comp (c k) = (d₂ k l).comp (c l))
    (hU : ∀ k l, IsPullback (d₁ k l).aU (d₂ k l).aU (c k).aU (c l).aU)
    (hV : ∀ k l, IsPullback (d₁ k l).aV (d₂ k l).aV (c k).aV (c l).aV)
    (hW : ∀ k l, IsPullback (d₁ k l).aW (d₂ k l).aW (c k).aW (c l).aW)
    (hZ : ∀ k l, IsPullback (d₁ k l).aZ (d₂ k l).aZ (c k).aZ (c l).aZ)
    (Q₃ : I → I → I → BaseSquare 𝒞) (e₁₂ : ∀ k l m, (Q₃ k l m).Hom (Q₂ k l))
    (e₂₃ : ∀ k l m, (Q₃ k l m).Hom (Q₂ l m)) (e₁₃ : ∀ k l m, (Q₃ k l m).Hom (Q₂ k m))
    (he₁ : ∀ k l m, (e₁₂ k l m).comp (d₂ k l) = (e₂₃ k l m).comp (d₁ l m))
    (he₂ : ∀ k l m, (e₁₃ k l m).comp (d₁ k m) = (e₁₂ k l m).comp (d₁ k l))
    (he₃ : ∀ k l m, (e₁₃ k l m).comp (d₂ k m) = (e₂₃ k l m).comp (d₂ l m))
    (hZ₃ : ∀ k l m, IsPullback (e₁₂ k l m).aZ (e₂₃ k l m).aZ (d₂ k l).aZ (d₁ l m).aZ)
    (s : SquareSpan p Q.f Q.g)
    (hloc : ∀ k (s' : SquareSpan p (Q₁ k).f (Q₁ k).g), SquareSpan.Hom (c k) s' s →
      Nonempty (s'.Cocone (Q₁ k).i (Q₁ k).j))
    (huniq₂ : ∀ k l, HasUniqueSquareCocones p (Q₂ k l).f (Q₂ k l).g (Q₂ k l).i (Q₂ k l).j)
    (huniq₃ : ∀ k l m,
      HasUniqueSquareCocones p (Q₃ k l m).f (Q₃ k l m).g (Q₃ k l m).i (Q₃ k l m).j) :
    Nonempty (s.Cocone Q.i Q.j) := by
  have hg := hp.isFiberedInGroupoids
  -- the restrictions of the span to the members of the covering, and local cocones
  choose s₁ hh₁ using fun k => SquareSpan.exists_restrict hg (c k) s
  let h₁ : ∀ k, SquareSpan.Hom (c k) (s₁ k) s := fun k => (hh₁ k).some
  let C : ∀ k, (s₁ k).Cocone (Q₁ k).i (Q₁ k).j := fun k => (hloc k (s₁ k) (h₁ k)).some
  -- the double overlaps: one span, two comparisons, and the identification of the two cocones
  have step₂ : ∀ k l, ∃ (s₂ : SquareSpan p (Q₂ k l).f (Q₂ k l).g)
      (g₁ : SquareSpan.Hom (d₁ k l) s₂ (s₁ k)) (g₂ : SquareSpan.Hom (d₂ k l) s₂ (s₁ l))
      (h₂ : SquareSpan.Hom ((d₁ k l).comp (c k)) s₂ s) (T : s₂.Cocone (Q₂ k l).i (Q₂ k l).j)
      (ρ : T.z ⟶ (C k).z) (σ : T.z ⟶ (C l).z),
      g₁.mx ≫ (h₁ k).mx = h₂.mx ∧ g₁.my ≫ (h₁ k).my = h₂.my ∧
      g₂.mx ≫ (h₁ l).mx = h₂.mx ∧ g₂.my ≫ (h₁ l).my = h₂.my ∧
      p.IsHomLift (d₁ k l).aZ ρ ∧ p.IsHomLift (d₂ k l).aZ σ ∧
      T.ξ ≫ ρ = g₁.mx ≫ (C k).ξ ∧ T.η ≫ ρ = g₁.my ≫ (C k).η ∧
      T.ξ ≫ σ = g₂.mx ≫ (C l).ξ ∧ T.η ≫ σ = g₂.my ≫ (C l).η := by
    intro k l
    obtain ⟨s₂, ⟨h₂⟩⟩ := SquareSpan.exists_restrict hg ((d₁ k l).comp (c k)) s
    obtain ⟨g₁, -, eg₁x, eg₁y⟩ := SquareSpan.Hom.exists_factor hg rfl h₂ (h₁ k)
    obtain ⟨g₂, -, eg₂x, eg₂y⟩ := SquareSpan.Hom.exists_factor hg (hd k l).symm h₂ (h₁ l)
    obtain ⟨T₁, ρ, hρ, eρx, eρy⟩ := SquareSpan.exists_pull hg g₁ (C k)
    obtain ⟨T₂, σ, hσ, eσx, eσy⟩ := SquareSpan.exists_pull hg g₂ (C l)
    let θ := (huniq₂ k l s₂ T₁ T₂).1.some
    refine ⟨s₂, g₁, g₂, h₂, T₁, ρ, θ.θ ≫ σ, eg₁x, eg₁y, eg₂x, eg₂y, hρ, ?_, eρx, eρy, ?_, ?_⟩
    · have := hσ; infer_instance
    · rw [θ.comm_ξ_assoc, eσx]
    · rw [θ.comm_η_assoc, eσy]
  choose s₂ g₁ g₂ h₂ T ρ σ eg₁x eg₁y eg₂x eg₂y hρ hσ eρx eρy eσx eσy using step₂
  have hz : ∀ k, p.obj (C k).z = (Q₁ k).Z := fun k => IsHomLift.codomain_eq p (Q₁ k).i (C k).ξ
  have : ∀ k l, p.IsHomLift (d₁ k l).aZ (ρ k l) := hρ
  have : ∀ k l, p.IsHomLift (d₂ k l).aZ (σ k l) := hσ
  -- associativity of the composite morphisms of squares into `Q`
  have hassoc : ∀ {S T R P : BaseSquare 𝒞} (a : S.Hom T) (b : T.Hom R) (c' : R.Hom P),
      (a.comp b).comp c' = a.comp (b.comp c') := by
    intro S T R P a b c'
    ext <;> simp [Category.assoc]
  -- the cocycle condition
  have hcoc : ∀ k l m (r : 𝒳) (m₁₂ : r ⟶ (T k l).z) (m₂₃ : r ⟶ (T l m).z)
      (m₁₃ : r ⟶ (T k m).z), p.IsHomLift (e₁₂ k l m).aZ m₁₂ →
      p.IsHomLift (e₂₃ k l m).aZ m₂₃ → p.IsHomLift (e₁₃ k l m).aZ m₁₃ →
      m₁₂ ≫ σ k l = m₂₃ ≫ ρ l m → m₁₂ ≫ ρ k l = m₁₃ ≫ ρ k m →
      m₂₃ ≫ σ l m = m₁₃ ≫ σ k m := by
    intro k l m r m₁₂ m₂₃ m₁₃ hm₁₂ hm₂₃ hm₁₃ h₁₂ h₁₃
    let a₀ := (e₁₂ k l m).comp ((d₁ k l).comp (c k))
    obtain ⟨s₃, ⟨h₃⟩⟩ := SquareSpan.exists_restrict hg a₀ s
    obtain ⟨f₁₂, -, ef₁₂x, ef₁₂y⟩ := SquareSpan.Hom.exists_factor hg rfl h₃ (h₂ k l)
    have ha₂₃ : (e₂₃ k l m).comp ((d₁ l m).comp (c l)) = a₀ := by
      calc (e₂₃ k l m).comp ((d₁ l m).comp (c l))
          = ((e₂₃ k l m).comp (d₁ l m)).comp (c l) := (hassoc _ _ _).symm
        _ = ((e₁₂ k l m).comp (d₂ k l)).comp (c l) := by rw [he₁]
        _ = (e₁₂ k l m).comp ((d₂ k l).comp (c l)) := hassoc _ _ _
        _ = a₀ := by rw [← hd]
    have ha₁₃ : (e₁₃ k l m).comp ((d₁ k m).comp (c k)) = a₀ := by
      calc (e₁₃ k l m).comp ((d₁ k m).comp (c k))
          = ((e₁₃ k l m).comp (d₁ k m)).comp (c k) := (hassoc _ _ _).symm
        _ = ((e₁₂ k l m).comp (d₁ k l)).comp (c k) := by rw [he₂]
        _ = a₀ := hassoc _ _ _
    obtain ⟨f₂₃, -, ef₂₃x, ef₂₃y⟩ := SquareSpan.Hom.exists_factor hg ha₂₃ h₃ (h₂ l m)
    obtain ⟨f₁₃, -, ef₁₃x, ef₁₃y⟩ := SquareSpan.Hom.exists_factor hg ha₁₃ h₃ (h₂ k m)
    have hV₁ := congrArg BaseSquare.Hom.aV (he₁ k l m)
    have hV₂ := congrArg BaseSquare.Hom.aV (he₂ k l m)
    have hV₃ := congrArg BaseSquare.Hom.aV (he₃ k l m)
    have hW₁ := congrArg BaseSquare.Hom.aW (he₁ k l m)
    have hW₂ := congrArg BaseSquare.Hom.aW (he₂ k l m)
    have hW₃ := congrArg BaseSquare.Hom.aW (he₃ k l m)
    have hZ₁ := congrArg BaseSquare.Hom.aZ (he₁ k l m)
    have hZ₂ := congrArg BaseSquare.Hom.aZ (he₂ k l m)
    have hZ₃' := congrArg BaseSquare.Hom.aZ (he₃ k l m)
    simp only [BaseSquare.Hom.comp_aV, BaseSquare.Hom.comp_aW,
      BaseSquare.Hom.comp_aZ] at hV₁ hV₂ hV₃ hW₁ hW₂ hW₃ hZ₁ hZ₂ hZ₃'
    -- the three ways from the triple-overlap span to the members agree
    have exl : (f₁₂.mx ≫ (g₂ k l).mx) = f₂₃.mx ≫ (g₁ l m).mx := by
      refine hg.hom_ext_of_eq (f := (c l).aV) hV₁ (h₁ l).mx ?_
      rw [Category.assoc, eg₂x, ef₁₂x, Category.assoc, eg₁x, ef₂₃x]
    have eyl : (f₁₂.my ≫ (g₂ k l).my) = f₂₃.my ≫ (g₁ l m).my := by
      refine hg.hom_ext_of_eq (f := (c l).aW) hW₁ (h₁ l).my ?_
      rw [Category.assoc, eg₂y, ef₁₂y, Category.assoc, eg₁y, ef₂₃y]
    have exk : (f₁₂.mx ≫ (g₁ k l).mx) = f₁₃.mx ≫ (g₁ k m).mx := by
      refine hg.hom_ext_of_eq (f := (c k).aV) hV₂.symm (h₁ k).mx ?_
      rw [Category.assoc, eg₁x, ef₁₂x, Category.assoc, eg₁x, ef₁₃x]
    have eyk : (f₁₂.my ≫ (g₁ k l).my) = f₁₃.my ≫ (g₁ k m).my := by
      refine hg.hom_ext_of_eq (f := (c k).aW) hW₂.symm (h₁ k).my ?_
      rw [Category.assoc, eg₁y, ef₁₂y, Category.assoc, eg₁y, ef₁₃y]
    have exm : (f₂₃.mx ≫ (g₂ l m).mx) = f₁₃.mx ≫ (g₂ k m).mx := by
      refine hg.hom_ext_of_eq (f := (c m).aV) hV₃.symm (h₁ m).mx ?_
      rw [Category.assoc, eg₂x, ef₂₃x, Category.assoc, eg₂x, ef₁₃x]
    have eym : (f₂₃.my ≫ (g₂ l m).my) = f₁₃.my ≫ (g₂ k m).my := by
      refine hg.hom_ext_of_eq (f := (c m).aW) hW₃.symm (h₁ m).my ?_
      rw [Category.assoc, eg₂y, ef₂₃y, Category.assoc, eg₂y, ef₁₃y]
    -- the legs of a cocone with vertex `r`, read off through `r ⟶ z k`
    have hμ : p.IsHomLift ((e₁₂ k l m).aZ ≫ (d₁ k l).aZ) (m₁₂ ≫ ρ k l) := inferInstance
    have hξk : p.IsHomLift ((Q₃ k l m).i ≫ ((e₁₂ k l m).aZ ≫ (d₁ k l).aZ))
        (f₁₂.mx ≫ (g₁ k l).mx ≫ (C k).ξ) := by
      refine isHomLift_of_eq (inferInstance : p.IsHomLift
        ((e₁₂ k l m).aV ≫ (d₁ k l).aV ≫ (Q₁ k).i) _) ?_
      rw [← (d₁ k l).wi, reassoc_of% (e₁₂ k l m).wi]
    have hηk : p.IsHomLift ((Q₃ k l m).j ≫ ((e₁₂ k l m).aZ ≫ (d₁ k l).aZ))
        (f₁₂.my ≫ (g₁ k l).my ≫ (C k).η) := by
      refine isHomLift_of_eq (inferInstance : p.IsHomLift
        ((e₁₂ k l m).aW ≫ (d₁ k l).aW ≫ (Q₁ k).j) _) ?_
      rw [← (d₁ k l).wj, reassoc_of% (e₁₂ k l m).wj]
    let ξr := hg.fill (f := (e₁₂ k l m).aZ ≫ (d₁ k l).aZ) (g := (Q₃ k l m).i) rfl
      (m₁₂ ≫ ρ k l) (f₁₂.mx ≫ (g₁ k l).mx ≫ (C k).ξ)
    let ηr := hg.fill (f := (e₁₂ k l m).aZ ≫ (d₁ k l).aZ) (g := (Q₃ k l m).j) rfl
      (m₁₂ ≫ ρ k l) (f₁₂.my ≫ (g₁ k l).my ≫ (C k).η)
    have hξr : p.IsHomLift (Q₃ k l m).i ξr := hg.fill_isHomLift _ _ _
    have hηr : p.IsHomLift (Q₃ k l m).j ηr := hg.fill_isHomLift _ _ _
    have eξr : ξr ≫ m₁₂ ≫ ρ k l = f₁₂.mx ≫ (g₁ k l).mx ≫ (C k).ξ := hg.fill_fac _ _ _
    have eηr : ηr ≫ m₁₂ ≫ ρ k l = f₁₂.my ≫ (g₁ k l).my ≫ (C k).η := hg.fill_fac _ _ _
    -- `ξr ≫ m₁₂` and `ηr ≫ m₁₂` are the pulled-back legs of the `(k, l)` cocone
    have eξ₁₂ : ξr ≫ m₁₂ = f₁₂.mx ≫ (T k l).ξ := by
      refine hg.hom_ext_of_eq (f := (d₁ k l).aZ) (e₁₂ k l m).wi (ρ k l) ?_
      rw [Category.assoc, eξr, Category.assoc, eρx]
    have eη₁₂ : ηr ≫ m₁₂ = f₁₂.my ≫ (T k l).η := by
      refine hg.hom_ext_of_eq (f := (d₁ k l).aZ) (e₁₂ k l m).wj (ρ k l) ?_
      rw [Category.assoc, eηr, Category.assoc, eρy]
    have eξ₂₃ : ξr ≫ m₂₃ = f₂₃.mx ≫ (T l m).ξ := by
      refine hg.hom_ext_of_eq (f := (d₁ l m).aZ) (e₂₃ k l m).wi (ρ l m) ?_
      rw [Category.assoc, ← h₁₂, reassoc_of% eξ₁₂, eσx, Category.assoc, eρx,
        reassoc_of% exl]
    have eη₂₃ : ηr ≫ m₂₃ = f₂₃.my ≫ (T l m).η := by
      refine hg.hom_ext_of_eq (f := (d₁ l m).aZ) (e₂₃ k l m).wj (ρ l m) ?_
      rw [Category.assoc, ← h₁₂, reassoc_of% eη₁₂, eσy, Category.assoc, eρy,
        reassoc_of% eyl]
    have eξ₁₃ : ξr ≫ m₁₃ = f₁₃.mx ≫ (T k m).ξ := by
      refine hg.hom_ext_of_eq (f := (d₁ k m).aZ) (e₁₃ k l m).wi (ρ k m) ?_
      rw [Category.assoc, ← h₁₃, eξr, Category.assoc, eρx, reassoc_of% exk]
    have eη₁₃ : ηr ≫ m₁₃ = f₁₃.my ≫ (T k m).η := by
      refine hg.hom_ext_of_eq (f := (d₁ k m).aZ) (e₁₃ k l m).wj (ρ k m) ?_
      rw [Category.assoc, ← h₁₃, eηr, Category.assoc, eρy, reassoc_of% eyk]
    -- the cocone with vertex `r`
    have hwr : (s₃).α ≫ ξr = (s₃).β ≫ ηr := by
      refine hg.hom_ext_of_eq (f := (e₁₂ k l m).aZ ≫ (d₁ k l).aZ) (Q₃ k l m).w (m₁₂ ≫ ρ k l) ?_
      rw [Category.assoc, eξr, Category.assoc, eηr, reassoc_of% f₁₂.comm_α,
        reassoc_of% (g₁ k l).comm_α, (C k).w, ← reassoc_of% (g₁ k l).comm_β,
        ← reassoc_of% f₁₂.comm_β]
    let R : (s₃).Cocone (Q₃ k l m).i (Q₃ k l m).j := ⟨r, ξr, ηr, hξr, hηr, hwr⟩
    -- the cocone pulled back from the `m`-th member
    let fm : SquareSpan.Hom ((e₂₃ k l m).comp (d₂ l m)) s₃ (s₁ m) :=
      ⟨f₂₃.mu ≫ (g₂ l m).mu, f₂₃.mx ≫ (g₂ l m).mx, f₂₃.my ≫ (g₂ l m).my,
        (inferInstance : p.IsHomLift ((e₂₃ k l m).aU ≫ (d₂ l m).aU) _),
        (inferInstance : p.IsHomLift ((e₂₃ k l m).aV ≫ (d₂ l m).aV) _),
        (inferInstance : p.IsHomLift ((e₂₃ k l m).aW ≫ (d₂ l m).aW) _),
        by rw [reassoc_of% f₂₃.comm_α, (g₂ l m).comm_α,
          Category.assoc], by rw [reassoc_of% f₂₃.comm_β, (g₂ l m).comm_β, Category.assoc]⟩
    obtain ⟨Wc, ω, hω, eωx, eωy⟩ := SquareSpan.exists_pull hg fm (C m)
    have : p.IsHomLift ((e₂₃ k l m).aZ ≫ (d₂ l m).aZ) ω := hω
    have hμa : p.IsHomLift ((e₂₃ k l m).aZ ≫ (d₂ l m).aZ) (m₂₃ ≫ σ l m) := inferInstance
    have hμb : p.IsHomLift ((e₂₃ k l m).aZ ≫ (d₂ l m).aZ) (m₁₃ ≫ σ k m) :=
      isHomLift_of_eq (n := (e₁₃ k l m).aZ ≫ (d₂ k m).aZ) inferInstance hZ₃'
    let εa := hg.fill (f := (e₂₃ k l m).aZ ≫ (d₂ l m).aZ) (g := 𝟙 (Q₃ k l m).Z)
      (f' := (e₂₃ k l m).aZ ≫ (d₂ l m).aZ) (by simp) ω (m₂₃ ≫ σ l m)
    let εb := hg.fill (f := (e₂₃ k l m).aZ ≫ (d₂ l m).aZ) (g := 𝟙 (Q₃ k l m).Z)
      (f' := (e₂₃ k l m).aZ ≫ (d₂ l m).aZ) (by simp) ω (m₁₃ ≫ σ k m)
    have hεa : p.IsHomLift (𝟙 (Q₃ k l m).Z) εa := hg.fill_isHomLift _ _ _
    have hεb : p.IsHomLift (𝟙 (Q₃ k l m).Z) εb := hg.fill_isHomLift _ _ _
    have eεa : εa ≫ ω = m₂₃ ≫ σ l m := hg.fill_fac _ _ _
    have eεb : εb ≫ ω = m₁₃ ≫ σ k m := hg.fill_fac _ _ _
    have hξω : ∀ ε : r ⟶ Wc.z, p.IsHomLift (𝟙 (Q₃ k l m).Z) ε →
        ξr ≫ ε ≫ ω = fm.mx ≫ (C m).ξ → ξr ≫ ε = Wc.ξ := by
      intro ε hε hεω
      have : p.IsHomLift ((Q₃ k l m).i) (ξr ≫ ε) := inferInstance
      refine hg.hom_ext (f := (e₂₃ k l m).aZ ≫ (d₂ l m).aZ) ((Q₃ k l m).i) ω ?_
      rw [Category.assoc, hεω, eωx]
    have hηω : ∀ ε : r ⟶ Wc.z, p.IsHomLift (𝟙 (Q₃ k l m).Z) ε →
        ηr ≫ ε ≫ ω = fm.my ≫ (C m).η → ηr ≫ ε = Wc.η := by
      intro ε hε hεω
      have : p.IsHomLift ((Q₃ k l m).j) (ηr ≫ ε) := inferInstance
      refine hg.hom_ext (f := (e₂₃ k l m).aZ ≫ (d₂ l m).aZ) ((Q₃ k l m).j) ω ?_
      rw [Category.assoc, hεω, eωy]
    have hab : εa = εb := (huniq₃ k l m s₃ R Wc).2 ⟨εa, hεa,
      hξω εa hεa (by rw [eεa, reassoc_of% eξ₂₃, eσx]; simp [fm]),
      hηω εa hεa (by rw [eεa, reassoc_of% eη₂₃, eσy]; simp [fm])⟩ ⟨εb, hεb,
      hξω εb hεb (by rw [eεb, reassoc_of% eξ₁₃, eσx]; simp [fm, reassoc_of% exm]),
      hηω εb hεb (by rw [eεb, reassoc_of% eη₁₃, eσy]; simp [fm, reassoc_of% eym])⟩
    rw [← eεa, ← eεb, hab]
  -- glue the vertices of the local cocones
  have hs₁₃₁ : ∀ k l m, (e₁₃ k l m).aZ ≫ (d₁ k m).aZ = (e₁₂ k l m).aZ ≫ (d₁ k l).aZ :=
    fun k l m => by simpa using congrArg BaseSquare.Hom.aZ (he₂ k l m)
  have hs₁₃₂ : ∀ k l m, (e₁₃ k l m).aZ ≫ (d₂ k m).aZ = (e₂₃ k l m).aZ ≫ (d₂ l m).aZ :=
    fun k l m => by simpa using congrArg BaseSquare.Hom.aZ (he₃ k l m)
  obtain ⟨z, ζ, hzZ, hζ, hζρσ⟩ := hp.exists_glue (fun k => (c k).aZ) hcZ
    (fun k l => (d₁ k l).aZ) (fun k l => (d₂ k l).aZ) hZ (fun k l m => (e₁₂ k l m).aZ)
    (fun k l m => (e₂₃ k l m).aZ) hZ₃ (fun k l m => (e₁₃ k l m).aZ) hs₁₃₁ hs₁₃₂ hz ρ σ hcoc
  have : ∀ k, p.IsHomLift (c k).aZ (ζ k) := hζ
  -- the legs, glued along the coverings of `V` and `W`
  have hlegx : ∀ k, p.IsHomLift ((c k).aV ≫ Q.i) ((C k).ξ ≫ ζ k) := fun k =>
    isHomLift_of_eq (n := (Q₁ k).i ≫ (c k).aZ) inferInstance (c k).wi
  have hlegy : ∀ k, p.IsHomLift ((c k).aW ≫ Q.j) ((C k).η ≫ ζ k) := fun k =>
    isHomLift_of_eq (n := (Q₁ k).j ≫ (c k).aZ) inferInstance (c k).wj
  have hx : p.obj s.x = Q.V := IsHomLift.codomain_eq p Q.f s.α
  have hy : p.obj s.y = Q.W := IsHomLift.codomain_eq p Q.g s.β
  have hu : p.obj s.u = Q.U := IsHomLift.domain_eq p Q.f s.α
  obtain ⟨ξ, ⟨hξ, eξ⟩, -⟩ := hp.existsUnique_hom_of_cover (fun k => (c k).aV) hcV
    (fun k l => (d₁ k l).aV) (fun k l => (d₂ k l).aV) hV Q.i hx (fun k => (h₁ k).mx) hzZ
    (fun k => (C k).ξ ≫ ζ k) (by
      intro k l x₂ r₁ r₂ hr₁ hr₂ hr
      let t := hg.fill (f := (d₁ k l).aV) (g := 𝟙 (Q₂ k l).V) (f' := (d₁ k l).aV) (by simp)
        (g₁ k l).mx r₁
      have ht : p.IsHomLift (𝟙 (Q₂ k l).V) t := hg.fill_isHomLift _ _ _
      have et : t ≫ (g₁ k l).mx = r₁ := hg.fill_fac _ _ _
      have et₂ : t ≫ (g₂ k l).mx = r₂ := by
        have : p.IsHomLift (d₂ k l).aV (t ≫ (g₂ k l).mx) := inferInstance
        refine hg.hom_ext (f := (c l).aV) (d₂ k l).aV (h₁ l).mx ?_
        rw [Category.assoc, eg₂x, ← eg₁x, ← hr, ← et, Category.assoc]
      rw [← et, ← et₂, Category.assoc, ← reassoc_of% eρx, hζρσ, Category.assoc,
        ← reassoc_of% eσx])
  obtain ⟨η, ⟨hη, eη⟩, -⟩ := hp.existsUnique_hom_of_cover (fun k => (c k).aW) hcW
    (fun k l => (d₁ k l).aW) (fun k l => (d₂ k l).aW) hW Q.j hy (fun k => (h₁ k).my) hzZ
    (fun k => (C k).η ≫ ζ k) (by
      intro k l x₂ r₁ r₂ hr₁ hr₂ hr
      let t := hg.fill (f := (d₁ k l).aW) (g := 𝟙 (Q₂ k l).W) (f' := (d₁ k l).aW) (by simp)
        (g₁ k l).my r₁
      have ht : p.IsHomLift (𝟙 (Q₂ k l).W) t := hg.fill_isHomLift _ _ _
      have et : t ≫ (g₁ k l).my = r₁ := hg.fill_fac _ _ _
      have et₂ : t ≫ (g₂ k l).my = r₂ := by
        have : p.IsHomLift (d₂ k l).aW (t ≫ (g₂ k l).my) := inferInstance
        refine hg.hom_ext (f := (c l).aW) (d₂ k l).aW (h₁ l).my ?_
        rw [Category.assoc, eg₂y, ← eg₁y, ← hr, ← et, Category.assoc]
      rw [← et, ← et₂, Category.assoc, ← reassoc_of% eρy, hζρσ, Category.assoc,
        ← reassoc_of% eσy])
  refine ⟨⟨z, ξ, η, hξ, hη, ?_⟩⟩
  -- the two composites out of `u` agree, as they do after restriction to the covering of `U`
  have : p.IsHomLift (Q.f ≫ Q.i) (s.α ≫ ξ) := inferInstance
  have : p.IsHomLift (Q.f ≫ Q.i) (s.β ≫ η) := by rw [Q.w]; infer_instance
  refine hp.hom_ext_of_cover (fun k => (c k).aU) hcU (fun k l => (d₁ k l).aU)
    (fun k l => (d₂ k l).aU) hU (Q.f ≫ Q.i) hu (fun k => (h₁ k).mu) hzZ (fun k => ?_)
  rw [← reassoc_of% (h₁ k).comm_α, eξ, ← reassoc_of% (h₁ k).comm_β, eη, reassoc_of% (C k).w]


end Local

/-! ### Base change of a square along a morphism into its terminal corner -/

section BaseChange

variable [HasPullbacks 𝒞]

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-- The base change of a commutative square `Q` along a morphism `h : Z' ⟶ Q.Z`: its corners are
the fibre products of the corners of `Q` with `Z'` over `Q.Z`. -/
noncomputable abbrev BaseSquare.baseChange (Q : BaseSquare 𝒞) {Z' : 𝒞} (h : Z' ⟶ Q.Z) :
    BaseSquare 𝒞 where
  U := pullback (Q.f ≫ Q.i) h
  V := pullback Q.i h
  W := pullback Q.j h
  Z := Z'
  f := pullback.lift (pullback.fst _ _ ≫ Q.f) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition])
  g := pullback.lift (pullback.fst _ _ ≫ Q.g) (pullback.snd _ _)
    (by rw [Category.assoc, ← Q.w, pullback.condition])
  i := pullback.snd _ _
  j := pullback.snd _ _
  w := (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- The projection of a base change of a square to the square. -/
noncomputable abbrev BaseSquare.baseChangeHom (Q : BaseSquare 𝒞) {Z' : 𝒞} (h : Z' ⟶ Q.Z) :
    (Q.baseChange h).Hom Q where
  aU := pullback.fst _ _
  aV := pullback.fst _ _
  aW := pullback.fst _ _
  aZ := h
  wf := pullback.lift_fst _ _ _
  wg := pullback.lift_fst _ _ _
  wi := pullback.condition.symm
  wj := pullback.condition.symm

/-- The comparison between two base changes of a square along composable morphisms. -/
noncomputable abbrev BaseSquare.baseChangeMap (Q : BaseSquare 𝒞) {Z₁ Z₂ : 𝒞} {h : Z₁ ⟶ Q.Z}
    {h' : Z₂ ⟶ Q.Z} (t : Z₂ ⟶ Z₁) (ht : t ≫ h = h') : (Q.baseChange h').Hom (Q.baseChange h) where
  aU := pullback.lift (pullback.fst (Q.f ≫ Q.i) h') (pullback.snd (Q.f ≫ Q.i) h' ≫ t)
    (pullback.condition.trans (by rw [← ht]; exact (Category.assoc _ _ _).symm))
  aV := pullback.lift (pullback.fst Q.i h') (pullback.snd Q.i h' ≫ t)
    (pullback.condition.trans (by rw [← ht]; exact (Category.assoc _ _ _).symm))
  aW := pullback.lift (pullback.fst Q.j h') (pullback.snd Q.j h' ≫ t)
    (pullback.condition.trans (by rw [← ht]; exact (Category.assoc _ _ _).symm))
  aZ := t
  wf := by apply pullback.hom_ext <;> simp
  wg := by apply pullback.hom_ext <;> simp
  wi := by simp
  wj := by simp

lemma BaseSquare.baseChangeMap_comp_baseChangeHom (Q : BaseSquare 𝒞) {Z₁ Z₂ : 𝒞}
    {h : Z₁ ⟶ Q.Z} {h' : Z₂ ⟶ Q.Z} (t : Z₂ ⟶ Z₁) (ht : t ≫ h = h') :
    (Q.baseChangeMap t ht).comp (Q.baseChangeHom h) = Q.baseChangeHom h' := by
  ext <;> simp [ht]

lemma BaseSquare.baseChangeMap_comp_baseChangeMap (Q : BaseSquare 𝒞) {Z₁ Z₂ Z₃ : 𝒞}
    {h : Z₁ ⟶ Q.Z} {h' : Z₂ ⟶ Q.Z} {h'' : Z₃ ⟶ Q.Z} (t : Z₂ ⟶ Z₁) (ht : t ≫ h = h')
    (t' : Z₃ ⟶ Z₂) (ht' : t' ≫ h' = h'') (t'' : Z₃ ⟶ Z₁) (ht'' : t' ≫ t = t'') :
    (Q.baseChangeMap t' ht').comp (Q.baseChangeMap t ht) =
      Q.baseChangeMap t'' (by rw [← ht'', Category.assoc, ht, ht']) := by
  subst ht''
  ext <;> simp

lemma BaseSquare.baseChangeMap_congr (Q : BaseSquare 𝒞) {Z₁ Z₂ : 𝒞} {h : Z₁ ⟶ Q.Z}
    {h' : Z₂ ⟶ Q.Z} {t t' : Z₂ ⟶ Z₁} (htt' : t = t') {ht : t ≫ h = h'} {ht' : t' ≫ h = h'} :
    Q.baseChangeMap t ht = Q.baseChangeMap t' ht' := by
  subst htt'; rfl

/-- Base change along the projections of a fibre product of two morphisms into `Z` is the
fibre product of the two base changes, at any object over `Z`. -/
lemma isPullback_lift_fst {A Z Z₁ Z₂ Z₁₂ : 𝒞} (a : A ⟶ Z) {e₁ : Z₁ ⟶ Z} {e₂ : Z₂ ⟶ Z}
    {π₁ : Z₁₂ ⟶ Z₁} {π₂ : Z₁₂ ⟶ Z₂} (hπ : IsPullback π₁ π₂ e₁ e₂) {h : Z₁₂ ⟶ Z}
    (hh₁ : π₁ ≫ e₁ = h) (hh₂ : π₂ ≫ e₂ = h) :
    IsPullback
      (pullback.lift (pullback.fst a h) (pullback.snd a h ≫ π₁)
        (by rw [Category.assoc, hh₁, pullback.condition]) : pullback a h ⟶ pullback a e₁)
      (pullback.lift (pullback.fst a h) (pullback.snd a h ≫ π₂)
        (by rw [Category.assoc, hh₂, pullback.condition]) : pullback a h ⟶ pullback a e₂)
      (pullback.fst a e₁) (pullback.fst a e₂) := by
  subst hh₁
  have hS₁ : IsPullback
      (pullback.lift (pullback.fst a (π₁ ≫ e₁)) (pullback.snd a (π₁ ≫ e₁) ≫ π₁)
        (by rw [Category.assoc, pullback.condition]) : pullback a (π₁ ≫ e₁) ⟶ pullback a e₁)
      (pullback.snd a (π₁ ≫ e₁)) (pullback.snd a e₁) π₁ :=
    IsPullback.of_right (by simpa using IsPullback.of_hasPullback a (π₁ ≫ e₁)) (by simp)
      (IsPullback.of_hasPullback a e₁)
  have hbig := hS₁.paste_vert hπ
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback a e₂)
  have e₁' : pullback.snd a e₁ ≫ e₁ = pullback.fst a e₁ ≫ a := pullback.condition.symm
  have e₂' : pullback.lift (pullback.fst a (π₁ ≫ e₁)) (pullback.snd a (π₁ ≫ e₁) ≫ π₂)
      (pullback.condition.trans (by rw [Category.assoc, hh₂])) ≫ pullback.snd a e₂ =
        pullback.snd a (π₁ ≫ e₁) ≫ π₂ := by simp
  rw [e₂', ← e₁']
  exact hbig

/-- The square formed by the first map of a base change and the first map of the square is
cartesian. -/
lemma BaseSquare.isPullback_baseChange_f (Q : BaseSquare 𝒞) {Z' : 𝒞} (h : Z' ⟶ Q.Z) :
    IsPullback (Q.baseChange h).f (Q.baseChangeHom h).aU (Q.baseChangeHom h).aV Q.f :=
  IsPullback.of_right (by simpa using (IsPullback.of_hasPullback (Q.f ≫ Q.i) h).flip)
    (by simp) (IsPullback.of_hasPullback Q.i h).flip

/-- The square formed by the second map of a base change and the second map of the square is
cartesian. -/
lemma BaseSquare.isPullback_baseChange_g (Q : BaseSquare 𝒞) {Z' : 𝒞} (h : Z' ⟶ Q.Z) :
    IsPullback (Q.baseChange h).g (Q.baseChangeHom h).aU (Q.baseChangeHom h).aW Q.g :=
  IsPullback.of_right (by simpa [Q.w] using (IsPullback.of_hasPullback (Q.f ≫ Q.i) h).flip)
    (by simp) (IsPullback.of_hasPullback Q.j h).flip

/-- The square formed by the third map of a base change and the base change map is cartesian. -/
lemma BaseSquare.isPullback_baseChange_i (Q : BaseSquare 𝒞) {Z' : 𝒞} (h : Z' ⟶ Q.Z) :
    IsPullback (Q.baseChange h).i (Q.baseChangeHom h).aV h Q.i :=
  (IsPullback.of_hasPullback Q.i h).flip

/-- The square formed by the fourth map of a base change and the base change map is cartesian. -/
lemma BaseSquare.isPullback_baseChange_j (Q : BaseSquare 𝒞) {Z' : 𝒞} (h : Z' ⟶ Q.Z) :
    IsPullback (Q.baseChange h).j (Q.baseChangeHom h).aW h Q.j :=
  (IsPullback.of_hasPullback Q.j h).flip

/-- The base change of a covering family along any morphism is a covering family. -/
lemma ofArrows_pullback_fst_mem {J : GrothendieckTopology 𝒞} {A Z : 𝒞} (a : A ⟶ Z) {I : Type*}
    {Z₁ : I → 𝒞} (e : ∀ k, Z₁ k ⟶ Z) (he : Sieve.ofArrows Z₁ e ∈ J Z) :
    Sieve.ofArrows (fun k => pullback a (e k)) (fun k => pullback.fst a (e k)) ∈ J A := by
  refine J.superset_covering ?_ (J.pullback_stable a he)
  rintro T g ⟨Y, t, _, ⟨k⟩, ht⟩
  exact ⟨_, pullback.lift g t ht.symm, _, ⟨k⟩, by simp⟩

/-- **Existence of cocones is local on the terminal corner, for base changes.** The form of
`CategoryTheory.Functor.IsStackInGroupoids.nonempty_cocone_of_cover` in which the covering of
the square is the base change of a covering family `τ k : Z₁ k ⟶ Q.Z` of its terminal corner, and
the double and triple overlaps are the base changes along the fibre products of that family. -/
theorem IsStackInGroupoids.nonempty_cocone_of_baseChange {J : GrothendieckTopology 𝒞}
    (hp : p.IsStackInGroupoids.{w} J)
    (Q : BaseSquare 𝒞) {I : Type w} {Z₁ : I → 𝒞} (τ : ∀ k, Z₁ k ⟶ Q.Z)
    (hτ : Sieve.ofArrows Z₁ τ ∈ J Q.Z) (s : SquareSpan p Q.f Q.g)
    (hloc : ∀ k (s' : SquareSpan p (Q.baseChange (τ k)).f (Q.baseChange (τ k)).g),
      SquareSpan.Hom (Q.baseChangeHom (τ k)) s' s →
      Nonempty (s'.Cocone (Q.baseChange (τ k)).i (Q.baseChange (τ k)).j))
    (huniq₂ : ∀ k l, HasUniqueSquareCocones p
      (Q.baseChange (pullback.fst (τ k) (τ l) ≫ τ k)).f
      (Q.baseChange (pullback.fst (τ k) (τ l) ≫ τ k)).g
      (Q.baseChange (pullback.fst (τ k) (τ l) ≫ τ k)).i
      (Q.baseChange (pullback.fst (τ k) (τ l) ≫ τ k)).j)
    (huniq₃ : ∀ k l m, HasUniqueSquareCocones p
      (Q.baseChange (pullback.fst (pullback.snd (τ k) (τ l)) (pullback.fst (τ l) (τ m)) ≫
        pullback.fst (τ k) (τ l) ≫ τ k)).f
      (Q.baseChange (pullback.fst (pullback.snd (τ k) (τ l)) (pullback.fst (τ l) (τ m)) ≫
        pullback.fst (τ k) (τ l) ≫ τ k)).g
      (Q.baseChange (pullback.fst (pullback.snd (τ k) (τ l)) (pullback.fst (τ l) (τ m)) ≫
        pullback.fst (τ k) (τ l) ≫ τ k)).i
      (Q.baseChange (pullback.fst (pullback.snd (τ k) (τ l)) (pullback.fst (τ l) (τ m)) ≫
        pullback.fst (τ k) (τ l) ≫ τ k)).j) :
    Nonempty (s.Cocone Q.i Q.j) := by
  -- the double and triple overlaps of the terminal corner, with their maps to `Q.Z`
  let P₂ : I → I → 𝒞 := fun k l => pullback (τ k) (τ l)
  let π₁ : ∀ k l, P₂ k l ⟶ Z₁ k := fun k l => pullback.fst (τ k) (τ l)
  let π₂ : ∀ k l, P₂ k l ⟶ Z₁ l := fun k l => pullback.snd (τ k) (τ l)
  let h₂ : ∀ k l, P₂ k l ⟶ Q.Z := fun k l => π₁ k l ≫ τ k
  have hh₂ : ∀ k l, π₂ k l ≫ τ l = h₂ k l := fun k l => pullback.condition.symm
  let P₃ : I → I → I → 𝒞 := fun k l m => pullback (π₂ k l) (π₁ l m)
  let s₁₂ : ∀ k l m, P₃ k l m ⟶ P₂ k l := fun k l m => pullback.fst _ _
  let s₂₃ : ∀ k l m, P₃ k l m ⟶ P₂ l m := fun k l m => pullback.snd _ _
  let h₃ : ∀ k l m, P₃ k l m ⟶ Q.Z := fun k l m => s₁₂ k l m ≫ h₂ k l
  have hs₂₃ : ∀ k l m, s₂₃ k l m ≫ h₂ l m = h₃ k l m := fun k l m => by
    have hc : s₁₂ k l m ≫ π₂ k l = s₂₃ k l m ≫ π₁ l m := pullback.condition
    change s₂₃ k l m ≫ π₁ l m ≫ τ l = s₁₂ k l m ≫ π₁ k l ≫ τ k
    rw [← Category.assoc, ← hc, Category.assoc, hh₂]
  let s₁₃ : ∀ k l m, P₃ k l m ⟶ P₂ k m := fun k l m =>
    pullback.lift (s₁₂ k l m ≫ π₁ k l) (s₂₃ k l m ≫ π₂ l m)
      (by rw [Category.assoc, Category.assoc, hh₂ l m]; exact (hs₂₃ k l m).symm)
  have hs₁₃ : ∀ k l m, s₁₃ k l m ≫ h₂ k m = h₃ k l m := fun k l m => by
    simp only [s₁₃, h₂, h₃]
    rw [pullback.lift_fst_assoc, Category.assoc]
  refine hp.nonempty_cocone_of_cover Q (fun k => Q.baseChange (τ k))
    (fun k => Q.baseChangeHom (τ k)) (ofArrows_pullback_fst_mem _ τ hτ)
    (ofArrows_pullback_fst_mem _ τ hτ) (ofArrows_pullback_fst_mem _ τ hτ) hτ
    (fun k l => Q.baseChange (h₂ k l)) (fun k l => Q.baseChangeMap (π₁ k l) rfl)
    (fun k l => Q.baseChangeMap (π₂ k l) (hh₂ k l))
    (fun k l => by rw [Q.baseChangeMap_comp_baseChangeHom, Q.baseChangeMap_comp_baseChangeHom])
    (fun k l => isPullback_lift_fst _ (IsPullback.of_hasPullback (τ k) (τ l)) rfl (hh₂ k l))
    (fun k l => isPullback_lift_fst _ (IsPullback.of_hasPullback (τ k) (τ l)) rfl (hh₂ k l))
    (fun k l => isPullback_lift_fst _ (IsPullback.of_hasPullback (τ k) (τ l)) rfl (hh₂ k l))
    (fun k l => IsPullback.of_hasPullback (τ k) (τ l))
    (fun k l m => Q.baseChange (h₃ k l m)) (fun k l m => Q.baseChangeMap (s₁₂ k l m) rfl)
    (fun k l m => Q.baseChangeMap (s₂₃ k l m) (hs₂₃ k l m))
    (fun k l m => Q.baseChangeMap (s₁₃ k l m) (hs₁₃ k l m))
    (fun k l m => by
      rw [Q.baseChangeMap_comp_baseChangeMap _ _ _ _ _ rfl,
        Q.baseChangeMap_comp_baseChangeMap _ _ _ _ _ rfl]
      exact Q.baseChangeMap_congr pullback.condition)
    (fun k l m => by
      rw [Q.baseChangeMap_comp_baseChangeMap _ _ _ _ _ rfl,
        Q.baseChangeMap_comp_baseChangeMap _ _ _ _ _ rfl]
      exact Q.baseChangeMap_congr (pullback.lift_fst _ _ _))
    (fun k l m => by
      rw [Q.baseChangeMap_comp_baseChangeMap _ _ _ _ _ rfl,
        Q.baseChangeMap_comp_baseChangeMap _ _ _ _ _ rfl]
      exact Q.baseChangeMap_congr (pullback.lift_snd _ _ _))
    (fun k l m => IsPullback.of_hasPullback (π₂ k l) (π₁ l m)) s hloc huniq₂ huniq₃

end BaseChange

/-! ### Transport of cocones along a functor over the base -/

section Transport

/-- The identity morphism of a square. -/
@[simps]
def BaseSquare.Hom.id (Q : BaseSquare 𝒞) : Q.Hom Q where
  aU := 𝟙 _
  aV := 𝟙 _
  aW := 𝟙 _
  aZ := 𝟙 _
  wf := by simp
  wg := by simp
  wi := by simp
  wj := by simp

variable {𝒲 : Type*} [Category 𝒲] {q : 𝒲 ⥤ 𝒞} {F : 𝒲 ⥤ 𝒳} (hF : F ⋙ p = q)
include hF

/-- The image of a span along a functor over the base. -/
@[simps]
def SquareSpan.map {U V W : 𝒞} {f : U ⟶ V} {g : U ⟶ W} (t : SquareSpan q f g) :
    SquareSpan p f g where
  u := F.obj t.u
  x := F.obj t.x
  y := F.obj t.y
  α := F.map t.α
  β := F.map t.β
  isHomLift_α := isHomLift_map_of_comp_eq hF f t.α
  isHomLift_β := isHomLift_map_of_comp_eq hF g t.β

/-- The image of a cocone along a functor over the base is a cocone over the image span. -/
def SquareSpan.Cocone.map {U V W Z : 𝒞} {f : U ⟶ V} {g : U ⟶ W} {i : V ⟶ Z} {j : W ⟶ Z}
    {t : SquareSpan q f g} (c : t.Cocone i j) : (t.map hF).Cocone i j where
  z := F.obj c.z
  ξ := F.map c.ξ
  η := F.map c.η
  isHomLift_ξ := isHomLift_map_of_comp_eq hF i c.ξ
  isHomLift_η := isHomLift_map_of_comp_eq hF j c.η
  w := (F.map_comp _ _).symm.trans ((congrArg F.map c.w).trans (F.map_comp _ _))

end Transport

/-! ### Cocones in the slice over an object -/

section Slice

/-- **Spans in a slice have cocones at pushout squares.** For the forgetful functor of the slice
over an object `T`, a span over the two first maps of a pushout square has a cocone. -/
theorem SquareSpan.nonempty_cocone_over_forget {T : 𝒞} {U V W Z : 𝒞} {f : U ⟶ V} {g : U ⟶ W}
    {i : V ⟶ Z} {j : W ⟶ Z} (hpush : IsPushout f g i j)
    (s : SquareSpan (Over.forget T) f g) : Nonempty (s.Cocone i j) := by
  have hu : s.u.left = U := IsHomLift.domain_eq (Over.forget T) f s.α
  have hx : s.x.left = V := IsHomLift.codomain_eq (Over.forget T) f s.α
  have hy : s.y.left = W := IsHomLift.codomain_eq (Over.forget T) g s.β
  have eα : s.α.left = eqToHom hu ≫ f ≫ eqToHom hx.symm := by
    simpa using IsHomLift.fac' (Over.forget T) f s.α
  have eβ : s.β.left = eqToHom hu ≫ g ≫ eqToHom hy.symm := by
    simpa using IsHomLift.fac' (Over.forget T) g s.β
  let dx : V ⟶ T := eqToHom hx.symm ≫ s.x.hom
  let dy : W ⟶ T := eqToHom hy.symm ≫ s.y.hom
  have hd : f ≫ dx = g ≫ dy := by
    have h₁ := Over.w s.α
    have h₂ := Over.w s.β
    rw [eα] at h₁
    rw [eβ] at h₂
    simp only [Category.assoc] at h₁ h₂
    have := h₁.trans h₂.symm
    simpa [dx, dy] using (eqToHom hu.symm ≫= this)
  let z : Over T := Over.mk (hpush.desc dx dy hd)
  let ξ : s.x ⟶ z := Over.homMk (eqToHom hx ≫ i) (by simp [z, dx])
  let η : s.y ⟶ z := Over.homMk (eqToHom hy ≫ j) (by simp [z, dy])
  refine ⟨⟨z, ξ, η, ?_, ?_, ?_⟩⟩
  · exact IsHomLift.of_fac' _ i ξ hx rfl (by simp [ξ])
  · exact IsHomLift.of_fac' _ j η hy rfl (by simp [η])
  · ext
    simp only [Over.comp_left, ξ, η, Over.homMk_left, eα, eβ, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, hpush.w]

end Slice

end CategoryTheory.Functor

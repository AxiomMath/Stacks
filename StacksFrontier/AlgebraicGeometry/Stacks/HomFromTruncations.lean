module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceTruncations
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpaceFiniteTruncations
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone

/-!
# Morphisms over a complete local ring from their truncations

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` whose
isomorphism presheaves `Isom(x, y)` are algebraic spaces — condition (2) of **Stacks 045G**,
which every algebraic stack satisfies. Let `x`, `y` be objects of `𝒳` over an object `U` of the
site whose scheme is the spectrum of a Noetherian complete local ring `R`. Then a morphism
`x ⟶ y` over the identity of `U` is the same thing as a compatible family of morphisms between
the restrictions of `x` and `y` to the truncations `Spec (R ⧸ J n)`, for any decreasing sequence
of ideals `J n ⊆ 𝔪` cofinal with the powers of the maximal ideal.

This is the step of the proof of **Stacks 07X8** that proves full faithfulness: "As `𝒳` is an
algebraic stack `Isom(x, x')` is representable by an algebraic space `I` over `Spec(R)`.
Applying Case II to `I` over `Spec(R)` implies immediately that (07X6) is fully faithful on
fibre categories over `Spec(R)`." Case II is **Stacks 0AQH**, here in the form
`AlgebraicGeometry.FormalSpace.existsUnique_section_of_compatible_truncations`.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.exists_section_of_span` and its companions: a
  section of the presheaf of morphisms `Mor(x, y)` over `g : V ⟶ U` is determined by, and can
  be built from, any object `z` over `V` (up to an isomorphism of the base) with morphisms to
  `x` and to `y`; restriction of sections corresponds to precomposition.
* `AlgebraicGeometry.Stack.existsUnique_hom_of_compatible_truncations`: the statement above.
* `AlgebraicGeometry.Stack.existsUnique_hom_of_compatible_truncations_of_finite`: the same over
  the spectrum of a finite algebra `A` over a Noetherian complete local ring `R`, with the
  truncations `Spec (A ⧸ 𝔪 ^ (n + 1) A)`; this is what the descent step of the essential
  surjectivity of Stacks 07X8 needs over `R' ⊗_R R'`.
* `AlgebraicGeometry.Stack.existsUnique_hom_of_existsUnique_sections`: the common core, for any
  system of objects along which sections of algebraic spaces extend uniquely.

## Implementation notes

The truncations are presented, as in the case of algebraic spaces, by arbitrary objects `W n`
of the site with isomorphisms of their schemes onto `Spec (R ⧸ J n)`, so that the levels of a
formal object, which live over the objects `Deformation.Artin.truncationOver`, apply directly.
The morphisms of the family are given as a family of objects `z n` with morphisms to `x` and to
`y` over the maps `W n ⟶ U`; this avoids choosing pullbacks of `x` and `y` and is the shape in
which the restrictions of a formal object arrive.

The isomorphism presheaf is evaluated on the slice over `U` through
`CategoryTheory.Over.iteratedSliceBackward`, whose objects are not literally the `W n` but are
isomorphic to them over `U`, which is why the span lemmas allow an isomorphism `k` of the base.

## References

* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
* [Stacks Project, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

/-! ### Sections of `Mor(x, y)` read off spans -/

namespace CategoryTheory.Functor.IsFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳] {p : 𝒳 ⥤ 𝒞}
variable (hp : p.IsFiberedInGroupoids)
include hp

omit hp in
/-- A section `s` of `Mor(x, y)` over `g` *matches* the span `x ← z → y` over `k ≫ g.hom` when
the canonical map from `z` to the pullback of `x` along `g`, lying over `k`, carries the span to
`s`. -/
def SpanMatches (p : 𝒳 ⥤ 𝒞) [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) (g : Over U)
    (s : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom) {V : 𝒞} (k : V ⟶ g.left)
    {z : 𝒳} (α : z ⟶ x.1) (β : z ⟶ y.1) : Prop :=
  ∃ θ : z ⟶ (pullbackFiber p x g.hom).1, p.IsHomLift k θ ∧
    θ ≫ IsPreFibered.pullbackMap x.2 g.hom = α ∧
    θ ≫ Fiber.fiberInclusion.map s ≫ IsPreFibered.pullbackMap y.2 g.hom = β

/-- **Existence of the section matching a span**, when the base map `k` is an isomorphism. -/
lemma exists_section_of_span [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) (g : Over U) {V : 𝒞}
    (k : V ⟶ g.left) [IsIso k] {z : 𝒳} (α : z ⟶ x.1) (β : z ⟶ y.1)
    [p.IsHomLift (k ≫ g.hom) α] [p.IsHomLift (k ≫ g.hom) β] :
    ∃ s : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom, SpanMatches p x y g s k α β := by
  let θx := hp.fill (f := g.hom) (g := k) rfl (IsPreFibered.pullbackMap x.2 g.hom) α
  let θy := hp.fill (f := g.hom) (g := k) rfl (IsPreFibered.pullbackMap y.2 g.hom) β
  have hθx : p.IsHomLift k θx := hp.fill_isHomLift _ _ _
  have hθy : p.IsHomLift k θy := hp.fill_isHomLift _ _ _
  have : IsIso θx := hp.isIso_of_isHomLift_isIso k θx
  have hs : p.IsHomLift (𝟙 g.left) (CategoryTheory.inv θx ≫ θy) := by
    have : p.IsHomLift (CategoryTheory.inv k ≫ k) (CategoryTheory.inv θx ≫ θy) := inferInstance
    rwa [IsIso.inv_hom_id] at this
  refine ⟨Fiber.homMk p g.left (CategoryTheory.inv θx ≫ θy), θx, hθx, hp.fill_fac _ _ _, ?_⟩
  change θx ≫ (CategoryTheory.inv θx ≫ θy) ≫ IsPreFibered.pullbackMap y.2 g.hom = β
  rw [Category.assoc, IsIso.hom_inv_id_assoc]
  exact hp.fill_fac _ _ _

/-- **Uniqueness of the section matching a span**, when the base map `k` is an isomorphism. -/
lemma section_eq_of_span [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) (g : Over U) {V : 𝒞}
    (k : V ⟶ g.left) [IsIso k] {z : 𝒳} (α : z ⟶ x.1) (β : z ⟶ y.1)
    {s s' : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom}
    (hs : SpanMatches p x y g s k α β) (hs' : SpanMatches p x y g s' k α β) : s = s' := by
  obtain ⟨θ, hθ, hθα, hθβ⟩ := hs
  obtain ⟨θ', hθ', hθα', hθβ'⟩ := hs'
  obtain rfl : θ = θ' :=
    hp.hom_ext (f := g.hom) k (IsPreFibered.pullbackMap x.2 g.hom) (hθα.trans hθα'.symm)
  have : IsIso θ := hp.isIso_of_isHomLift_isIso k θ
  apply Fiber.hom_ext
  change s.1 = s'.1
  have := s.2
  have := s'.2
  refine hp.hom_ext (f := g.hom) (𝟙 g.left) (IsPreFibered.pullbackMap y.2 g.hom) ?_
  rw [← cancel_epi θ]
  exact hθβ.trans hθβ'.symm

/-- A section matching two spans with the same left leg has the same right legs. -/
lemma eq_of_spanMatches [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) (g : Over U) {V : 𝒞}
    (k : V ⟶ g.left) {z : 𝒳} (α : z ⟶ x.1) {β β' : z ⟶ y.1}
    {s : pullbackFiber p x g.hom ⟶ pullbackFiber p y g.hom}
    (hs : SpanMatches p x y g s k α β) (hs' : SpanMatches p x y g s k α β') : β = β' := by
  obtain ⟨θ, hθ, hθα, hθβ⟩ := hs
  obtain ⟨θ', hθ', hθα', hθβ'⟩ := hs'
  have hθθ : θ = θ' :=
    hp.hom_ext (f := g.hom) k (IsPreFibered.pullbackMap x.2 g.hom) (hθα.trans hθα'.symm)
  rw [← hθβ, ← hθβ', hθθ]

/-- **Restriction of sections is precomposition of spans.** If `s` matches `x ← z₂ → y` and
`c : z₁ ⟶ z₂` lies over a map compatible with the base maps, then the restriction of `s` along
`h` matches the precomposed span. -/
lemma spanMatches_morRestrict [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) {g₁ g₂ : Over U}
    (h : g₁ ⟶ g₂) {V₁ V₂ : 𝒞} (k₁ : V₁ ⟶ g₁.left) (k₂ : V₂ ⟶ g₂.left) (e : V₁ ⟶ V₂)
    (he : e ≫ k₂ = k₁ ≫ h.left) {z₁ z₂ : 𝒳} (c : z₁ ⟶ z₂) [p.IsHomLift e c]
    {α₂ : z₂ ⟶ x.1} {β₂ : z₂ ⟶ y.1}
    {s : pullbackFiber p x g₂.hom ⟶ pullbackFiber p y g₂.hom}
    (hs : SpanMatches p x y g₂ s k₂ α₂ β₂) :
    SpanMatches p x y g₁ (morRestrict p x y h s) k₁ (c ≫ α₂) (c ≫ β₂) := by
  obtain ⟨θ₂, hθ₂, hθα₂, hθβ₂⟩ := hs
  have hc : p.IsHomLift (k₁ ≫ g₁.hom) (c ≫ α₂) := by
    have : p.IsHomLift (e ≫ k₂ ≫ g₂.hom) (c ≫ α₂) := by
      have : p.IsHomLift (k₂ ≫ g₂.hom) α₂ := by
        rw [← hθα₂]
        infer_instance
      infer_instance
    rwa [← Category.assoc, he, Category.assoc, Over.w h] at this
  let θ₁ := hp.fill (f := g₁.hom) (g := k₁) rfl (IsPreFibered.pullbackMap x.2 g₁.hom) (c ≫ α₂)
  have hθ₁ : p.IsHomLift k₁ θ₁ := hp.fill_isHomLift _ _ _
  have hθα₁ : θ₁ ≫ IsPreFibered.pullbackMap x.2 g₁.hom = c ≫ α₂ := hp.fill_fac _ _ _
  have key : θ₁ ≫ pullbackFiberMap p x h = c ≫ θ₂ := by
    have h₁ : p.IsHomLift (k₁ ≫ h.left) (θ₁ ≫ pullbackFiberMap p x h) := inferInstance
    have h₂ : p.IsHomLift (k₁ ≫ h.left) (c ≫ θ₂) := by
      rw [← he]
      infer_instance
    refine hp.hom_ext (f := g₂.hom) (k₁ ≫ h.left) (IsPreFibered.pullbackMap x.2 g₂.hom) ?_
    rw [Category.assoc, pullbackFiberMap_fac, hθα₁, Category.assoc, hθα₂]
  refine ⟨θ₁, hθ₁, hθα₁, ?_⟩
  calc θ₁ ≫ Fiber.fiberInclusion.map (morRestrict p x y h s) ≫
        IsPreFibered.pullbackMap y.2 g₁.hom
      = θ₁ ≫ pullbackFiberMap p x h ≫ Fiber.fiberInclusion.map s ≫
        IsPreFibered.pullbackMap y.2 g₂.hom := congrArg (θ₁ ≫ ·) (morRestrict_fac p x y h s)
    _ = c ≫ θ₂ ≫ Fiber.fiberInclusion.map s ≫ IsPreFibered.pullbackMap y.2 g₂.hom := by
        rw [← Category.assoc, key, Category.assoc]
    _ = c ≫ β₂ := by rw [hθβ₂]

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion in
/-- **Morphisms from spans over the restrictions of a unique section.** Let `kT ≫ gT.hom = 𝟙 U`
with `kT` an isomorphism, and let sections `s n` over `g n` match spans `x ← z n → y` lying over
`ι n`. If the `s n` are the restrictions along `h n` of a unique section `σ` over `gT`, then the
`ψ n` are `r n ≫ φ` for a unique morphism `φ : x ⟶ y` over the identity of `U`. -/
lemma existsUnique_hom_of_spanMatches [p.IsFibered] {U : 𝒞} (x y : p.Fiber U) (gT : Over U)
    (kT : U ⟶ gT.left) [IsIso kT] (hkT : kT ≫ gT.hom = 𝟙 U) {W : ℕ → 𝒞} (ι : ∀ n, W n ⟶ U)
    (g : ℕ → Over U) (k : ∀ n, W n ⟶ (g n).left) [∀ n, IsIso (k n)] (h : ∀ n, g n ⟶ gT)
    (hkh : ∀ n, ι n ≫ kT = k n ≫ (h n).left) {z : ℕ → 𝒳} (r : ∀ n, z n ⟶ x.1)
    [∀ n, p.IsHomLift (ι n) (r n)] (ψ : ∀ n, z n ⟶ y.1)
    (s : ∀ n, pullbackFiber p x (g n).hom ⟶ pullbackFiber p y (g n).hom)
    (hs : ∀ n, SpanMatches p x y (g n) (s n) (k n) (r n) (ψ n))
    (σ : pullbackFiber p x gT.hom ⟶ pullbackFiber p y gT.hom)
    (hσ : ∀ n, morRestrict p x y (h n) σ = s n)
    (hσuniq : ∀ σ', (∀ n, morRestrict p x y (h n) σ' = s n) → σ' = σ) :
    ∃! φ : x.1 ⟶ y.1, p.IsHomLift (𝟙 U) φ ∧ ∀ n, r n ≫ φ = ψ n := by
  -- the morphism `x ⟶ y` determined by `σ`
  have hidlift : p.IsHomLift (kT ≫ gT.hom) (𝟙 x.1) := by
    rw [hkT]
    exact IsHomLift.id x.2
  let θ := hp.fill (f := gT.hom) (g := kT) rfl (IsPreFibered.pullbackMap x.2 gT.hom) (𝟙 x.1)
  have hθ : p.IsHomLift kT θ := hp.fill_isHomLift _ _ _
  let φ : x.1 ⟶ y.1 := θ ≫ Fiber.fiberInclusion.map σ ≫ IsPreFibered.pullbackMap y.2 gT.hom
  have hφσ : SpanMatches p x y gT σ kT (𝟙 x.1) φ := ⟨θ, hθ, hp.fill_fac _ _ _, rfl⟩
  have hφlift : p.IsHomLift (𝟙 U) φ := by
    have h₁ : p.IsHomLift (𝟙 gT.left) (Fiber.fiberInclusion.map σ) := σ.2
    have h₂ : p.IsHomLift gT.hom (IsPreFibered.pullbackMap y.2 gT.hom) := inferInstance
    have h₃ : p.IsHomLift (𝟙 gT.left ≫ gT.hom) (Fiber.fiberInclusion.map σ ≫
      IsPreFibered.pullbackMap y.2 gT.hom) := IsHomLift.comp p _ _ _ _
    have : p.IsHomLift (kT ≫ 𝟙 _ ≫ gT.hom) (θ ≫ Fiber.fiberInclusion.map σ ≫
      IsPreFibered.pullbackMap y.2 gT.hom) := IsHomLift.comp p _ _ _ _
    rwa [Category.id_comp, hkT] at this
  -- restriction of a section over `gT` matching `x ← x → y` to the truncations
  have hrestr : ∀ (σ' : pullbackFiber p x gT.hom ⟶ pullbackFiber p y gT.hom) (φ' : x.1 ⟶ y.1),
      SpanMatches p x y gT σ' kT (𝟙 x.1) φ' → ∀ n,
      SpanMatches p x y (g n) (morRestrict p x y (h n) σ') (k n) (r n) (r n ≫ φ') := by
    intro σ' φ' hσ' n
    have hm := hp.spanMatches_morRestrict x y (h n) (k n) kT (ι n) (hkh n) (r n) hσ'
    rwa [Category.comp_id] at hm
  refine ⟨φ, ⟨hφlift, fun n => ?_⟩, ?_⟩
  · have h₁ := hrestr σ φ hφσ n
    rw [hσ n] at h₁
    exact hp.eq_of_spanMatches x y (g n) (k n) (r n) h₁ (hs n)
  · rintro φ' ⟨hφ'lift, hφ'⟩
    have hidlift' : p.IsHomLift (kT ≫ gT.hom) φ' := by rwa [hkT]
    obtain ⟨s', hs'⟩ := hp.exists_section_of_span x y gT kT (𝟙 x.1) φ'
    have hs'σ : s' = σ := hσuniq s' fun n => by
      have h₁ := hrestr s' φ' hs' n
      rw [hφ' n] at h₁
      exact hp.section_eq_of_span x y (g n) (k n) (r n) (ψ n) h₁ (hs n)
    rw [hs'σ] at hs'
    exact hp.eq_of_spanMatches x y gT kT (𝟙 x.1) hs' hφσ

end CategoryTheory.Functor.IsFiberedInGroupoids

/-- A morphism of `Over X` whose underlying morphism is an isomorphism is an isomorphism. -/
lemma CategoryTheory.Over.isIso_homMk {C : Type*} [Category C] {X : C} {A B : Over X}
    (f : A.left ⟶ B.left) [IsIso f] (w : f ≫ B.hom = A.hom) : IsIso (Over.homMk f w) := by
  have : IsIso ((Over.forget X).map (Over.homMk f w)) := by
    change IsIso f
    infer_instance
  exact isIso_of_reflects_iso _ (Over.forget X)

/-! ### Morphisms from truncations -/

/-- Commutation of morphisms in `Over X` gives commutation of the underlying morphisms. -/
private lemma CategoryTheory.Over.left_comp_eq_of_comp_eq {C : Type*} [Category C] {X : C}
    {A B D : Over X} (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (e : f ≫ g = h) :
    f.left ≫ g.left = h.left := by
  rw [← Over.comp_left, e]

namespace AlgebraicGeometry.Stack

universe u v w a b

-- `Fiber` and its inclusion must unfold for instance search to see the composites of fibre
-- morphisms with cartesian lifts, as in `StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf`.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- A natural isomorphism after universe lifts transports the unique-extension property of
compatible families of sections. -/
private lemma existsUnique_transport {C : Type*} [Category C] {X : Cᵒᵖ ⥤ Type a}
    {P : Cᵒᵖ ⥤ Type b} (e : X ⋙ uliftFunctor.{b} ≅ P ⋙ uliftFunctor.{a}) {T : C}
    {W : ℕ → C} (ι : ∀ n, W n ⟶ T) (τ : ∀ n, W n ⟶ W (n + 1))
    (h : ∀ x : ∀ n, X.obj (op (W n)), (∀ n, X.map (τ n).op (x (n + 1)) = x n) →
      ∃! y : X.obj (op T), ∀ n, X.map (ι n).op y = x n)
    (x : ∀ n, P.obj (op (W n))) (hx : ∀ n, P.map (τ n).op (x (n + 1)) = x n) :
    ∃! y : P.obj (op T), ∀ n, P.map (ι n).op y = x n := by
  let upX : ∀ c, X.obj c → (X ⋙ uliftFunctor.{b}).obj c := fun _ a => ULift.up a
  let upP : ∀ c, P.obj c → (P ⋙ uliftFunctor.{a}).obj c := fun _ a => ULift.up a
  let φ : ∀ c, X.obj c → P.obj c := fun c a => ULift.down (e.hom.app c (upX c a))
  let ψ : ∀ c, P.obj c → X.obj c := fun c a => ULift.down (e.inv.app c (upP c a))
  have hφψ : ∀ c a, φ c (ψ c a) = a := fun c a =>
    congrArg ULift.down (e.inv_hom_id_app_apply c (upP c a))
  have hψφ : ∀ c a, ψ c (φ c a) = a := fun c a =>
    congrArg ULift.down (e.hom_inv_id_app_apply c (upX c a))
  have hφ : ∀ {c d} (f : c ⟶ d) a, φ d (X.map f a) = P.map f (φ c a) := fun f a =>
    congrArg ULift.down (NatTrans.naturality_apply e.hom f (upX _ a))
  have hψ : ∀ {c d} (f : c ⟶ d) a, ψ d (P.map f a) = X.map f (ψ c a) := fun f a =>
    congrArg ULift.down (NatTrans.naturality_apply e.inv f (upP _ a))
  obtain ⟨y, hy, huniq⟩ := h (fun n => ψ _ (x n)) (fun n => by rw [← hψ, hx n])
  refine ⟨φ _ y, fun n => ?_, fun y' hy' => ?_⟩
  · rw [← hφ, hy n, hφψ]
  · have := huniq (ψ _ y') (fun n => by rw [← hψ, hy' n])
    rw [← this, hφψ]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Morphisms from their truncations, given the extension property of sections.** Let `p` be
fibred in groupoids over the big fppf site of `S`, and let `x`, `y` be objects over `U` whose
isomorphism presheaf is an algebraic space over `U`. Let `ι n : W n ⟶ U` be a compatible system
of morphisms such that, for every algebraic space over `U`, compatible families of sections over
the `W n` (read in the slice over `U`) extend uniquely to `U`. Given objects `z n` over `W n` with
maps `r n` to `x` compatible along transition maps `t n`, every compatible family
`ψ n : z n ⟶ y` over the same maps `W n ⟶ U` is `r n ≫ φ` for a unique morphism `φ : x ⟶ y` over
the identity of `U`.

This is the common core of `AlgebraicGeometry.Stack.existsUnique_hom_of_compatible_truncations`
(the truncations of a complete local ring) and
`AlgebraicGeometry.Stack.existsUnique_hom_of_compatible_truncations_of_finite` (those of a finite
algebra over one). -/
public theorem existsUnique_hom_of_existsUnique_sections
    {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (U : BigFppfOver B S hS) (x y : p.Fiber U)
    (hI : ∃ Fsp : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 Fsp ∧
        Nonempty (Fsp ⋙ uliftFunctor.{w, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, w}))
    (W : ℕ → BigFppfOver B S hS) (ι : ∀ n, W n ⟶ U)
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (hsec : ∀ Fsp : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 Fsp →
      ∀ xs : ∀ n, Fsp.obj (op (Over.mk (ι n).left : BigFppfOver B U.left.1 U.left.2)),
      (∀ n, Fsp.map (Over.homMk (τ n).left (by
          change (τ n).left ≫ (ι (n + 1)).left = (ι n).left
          rw [← Over.comp_left, hτ n]) :
          (Over.mk (ι n).left : BigFppfOver B U.left.1 U.left.2) ⟶
            Over.mk (ι (n + 1)).left).op (xs (n + 1)) = xs n) →
      ∃! ys : Fsp.obj (op (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2)),
        ∀ n, Fsp.map (Over.homMk (ι n).left (Category.comp_id _) :
          (Over.mk (ι n).left : BigFppfOver B U.left.1 U.left.2) ⟶ Over.mk (𝟙 U.left)).op ys =
          xs n)
    (z : ℕ → F) (r : ∀ n, z n ⟶ x.1) [∀ n, p.IsHomLift (ι n) (r n)]
    (t : ∀ n, z n ⟶ z (n + 1)) [∀ n, p.IsHomLift (τ n) (t n)]
    (ht : ∀ n, t n ≫ r (n + 1) = r n)
    (ψ : ∀ n, z n ⟶ y.1) [∀ n, p.IsHomLift (ι n) (ψ n)]
    (hψ : ∀ n, t n ≫ ψ (n + 1) = ψ n) :
    ∃! φ : x.1 ⟶ y.1, p.IsHomLift (𝟙 U) φ ∧ ∀ n, r n ≫ φ = ψ n := by
  classical
  obtain ⟨Fsp, hFsp, ⟨e⟩⟩ := hI
  -- the truncations as objects over `U.left`
  let T' : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let W' : ℕ → BigFppfOver B U.left.1 U.left.2 := fun n => Over.mk (ι n).left
  let ι' : ∀ n, W' n ⟶ T' := fun n => Over.homMk (ι n).left (Category.comp_id _)
  let τ' : ∀ n, W' n ⟶ W' (n + 1) := fun n =>
    Over.homMk (τ n).left (Over.left_comp_eq_of_comp_eq _ _ _ (hτ n))
  -- the slices over `U` attached to the truncations
  let P := (Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y
  let g : ℕ → Over U := fun n => (Over.iteratedSliceBackward U).obj (W' n)
  let gT : Over U := (Over.iteratedSliceBackward U).obj T'
  let k : ∀ n, W n ⟶ (g n).left := fun n => Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ (ι n).left ≫ U.hom = (W n).hom
    rw [Category.id_comp, Over.w])
  have hk : ∀ n, k n ≫ (g n).hom = ι n := fun n =>
    Over.OverMorphism.ext (Category.id_comp (ι n).left)
  have hkiso : ∀ n, IsIso (k n) := fun n =>
    @Over.isIso_homMk _ _ _ (W n) (g n).left (𝟙 _) (IsIso.id _) _
  let kT : U ⟶ gT.left := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ 𝟙 _ ≫ U.hom = U.hom
    simp)
  have hkT : kT ≫ gT.hom = 𝟙 U :=
    Over.OverMorphism.ext (Category.id_comp (𝟙 U.left))
  have : IsIso kT := @Over.isIso_homMk _ _ _ _ _ _ (IsIso.id _) _
  have hgroupoid := hp.fiber_isGroupoid
  -- the sections over the truncations
  have hrlift : ∀ n, p.IsHomLift (k n ≫ (g n).hom) (r n) := fun n => by
    rw [hk n]
    infer_instance
  have hψlift : ∀ n, p.IsHomLift (k n ≫ (g n).hom) (ψ n) := fun n => by
    rw [hk n]
    infer_instance
  choose s hs using fun n => hp.exists_section_of_span x y (g n) (k n) (r n) (ψ n)
  let xs : ∀ n, P.obj (op (W' n)) := fun n => ⟨s n, (hgroupoid _).all_isIso (s n)⟩
  have hxs : ∀ n, P.map (τ' n).op (xs (n + 1)) = xs n := by
    intro n
    apply Subtype.ext
    change p.morRestrict x y ((Over.iteratedSliceBackward U).map (τ' n)) (s (n + 1)) = s n
    have hm := hp.spanMatches_morRestrict x y ((Over.iteratedSliceBackward U).map (τ' n))
      (k n) (k (n + 1)) (τ n)
      (Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm)) (t n)
      (hs (n + 1))
    rw [ht n, hψ n] at hm
    exact hp.section_eq_of_span x y (g n) (k n) (r n) (ψ n) hm (hs n)
  obtain ⟨σ, hσ, hσuniq⟩ := existsUnique_transport e ι' τ' (hsec Fsp hFsp) xs hxs
  exact hp.existsUnique_hom_of_spanMatches x y gT kT hkT ι g k
    (fun n => (Over.iteratedSliceBackward U).map (ι' n))
    (fun n => Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))
    r ψ s hs σ.1 (fun n => congrArg Subtype.val (hσ n))
    (fun σ' hσ' => congrArg Subtype.val
      (hσuniq ⟨σ', (hgroupoid _).all_isIso σ'⟩ fun n => Subtype.ext (hσ' n)))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Morphisms over a complete local ring from their truncations** (the full faithfulness step
of Stacks 07X8, on fibre categories). Let `p` be fibred in groupoids over the big fppf site of
`S`, and let `x`, `y` be objects over `U` whose isomorphism presheaf is an algebraic space over
`U`. Suppose the scheme of `U` is the spectrum of a Noetherian complete local ring `R`, and let
`W n ⟶ U` present the truncations `Spec (R ⧸ J n)` for a decreasing sequence of ideals
`J n ⊆ 𝔪` cofinal with the powers of `𝔪`. Given objects `z n` over `W n` with maps `r n` to `x`
compatible along transition maps `t n`, every compatible family `ψ n : z n ⟶ y` over the same
maps `W n ⟶ U` is `r n ≫ φ` for a unique morphism `φ : x ⟶ y` over the identity of `U`. -/
public theorem existsUnique_hom_of_compatible_truncations
    {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (U : BigFppfOver B S hS) (x y : p.Fiber U)
    (hI : ∃ Fsp : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 Fsp ∧
        Nonempty (Fsp ⋙ uliftFunctor.{w, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, w}))
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsNoetherianCompleteLocalRing R)
    (J : ℕ → Ideal R) (hJm : ∀ n, J n ≤ IsLocalRing.maximalIdeal R)
    (hJmono : ∀ n, J (n + 1) ≤ J n)
    (hJ₁ : ∀ n, ∃ k, IsLocalRing.maximalIdeal R ^ k ≤ J n)
    (hJ₂ : ∀ k, ∃ n, J n ≤ IsLocalRing.maximalIdeal R ^ k)
    (eT : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of R))
    (W : ℕ → BigFppfOver B S hS)
    (eW : ∀ n, (BigFppfOver.toScheme B S hS).obj (W n) ≅ Spec (.of (R ⧸ J n)))
    (ι : ∀ n, W n ⟶ U)
    (hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J n))))
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (z : ℕ → F) (r : ∀ n, z n ⟶ x.1) [∀ n, p.IsHomLift (ι n) (r n)]
    (t : ∀ n, z n ⟶ z (n + 1)) [∀ n, p.IsHomLift (τ n) (t n)]
    (ht : ∀ n, t n ≫ r (n + 1) = r n)
    (ψ : ∀ n, z n ⟶ y.1) [∀ n, p.IsHomLift (ι n) (ψ n)]
    (hψ : ∀ n, t n ≫ ψ (n + 1) = ψ n) :
    ∃! φ : x.1 ⟶ y.1, p.IsHomLift (𝟙 U) φ ∧ ∀ n, r n ≫ φ = ψ n := by
  refine existsUnique_hom_of_existsUnique_sections p hp U x y hI W ι τ hτ
    (fun Fsp hFsp xs hxs => ?_) z r t ht ψ hψ
  exact FormalSpace.existsUnique_section_of_compatible_truncations hR J hJm hJmono hJ₁ hJ₂ hFsp
    (Over.mk (𝟙 _)) eT (fun n => Over.mk (ι n).left) eW
    (fun n => Over.homMk (ι n).left (Category.comp_id _)) hι
    (fun n => Over.homMk (τ n).left (Over.left_comp_eq_of_comp_eq _ _ _ (hτ n)))
    (fun n => Over.OverMorphism.ext
      (Over.left_comp_eq_of_comp_eq (τ n) (ι (n + 1)) (ι n) (hτ n))) xs hxs

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **Morphisms over a finite algebra over a complete local ring from their truncations.** Let `p`
be fibred in groupoids over the big fppf site of `S`, and let `x`, `y` be objects over `U` whose
isomorphism presheaf is an algebraic space over `U`. Suppose the scheme of `U` is `Spec A` for a
finite algebra `A` over a Noetherian complete local ring `R`, and let `W n ⟶ U` present the
truncations `Spec (A ⧸ 𝔪 ^ (n + 1) A)`. Given objects `z n` over `W n` with maps `r n` to `x`
compatible along transition maps `t n`, every compatible family `ψ n : z n ⟶ y` over the same
maps `W n ⟶ U` is `r n ≫ φ` for a unique morphism `φ : x ⟶ y` over the identity of `U`. -/
public theorem existsUnique_hom_of_compatible_truncations_of_finite
    {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) [p.IsFibered]
    (hp : p.IsFiberedInGroupoids) (U : BigFppfOver B S hS) (x y : p.Fiber U)
    (hI : ∃ Fsp : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u,
      IsAlgebraicSpace B U.left.1 U.left.2 Fsp ∧
        Nonempty (Fsp ⋙ uliftFunctor.{w, u} ≅
          ((Over.iteratedSliceBackward U).op ⋙ p.isomPresheaf x y) ⋙ uliftFunctor.{u, w}))
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : IsNoetherianCompleteLocalRing R)
    {A : Type u} [CommRing A] [Algebra R A] [Module.Finite R A]
    (eT : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of A))
    (W : ℕ → BigFppfOver B S hS)
    (eW : ∀ n, (BigFppfOver.toScheme B S hS).obj (W n) ≅
      Spec (.of (A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R A))))
    (ι : ∀ n, W n ⟶ U)
    (hι : ∀ n, (BigFppfOver.toScheme B S hS).map (ι n) ≫ eT.hom =
      (eW n).hom ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R A)))))
    (τ : ∀ n, W n ⟶ W (n + 1)) (hτ : ∀ n, τ n ≫ ι (n + 1) = ι n)
    (z : ℕ → F) (r : ∀ n, z n ⟶ x.1) [∀ n, p.IsHomLift (ι n) (r n)]
    (t : ∀ n, z n ⟶ z (n + 1)) [∀ n, p.IsHomLift (τ n) (t n)]
    (ht : ∀ n, t n ≫ r (n + 1) = r n)
    (ψ : ∀ n, z n ⟶ y.1) [∀ n, p.IsHomLift (ι n) (ψ n)]
    (hψ : ∀ n, t n ≫ ψ (n + 1) = ψ n) :
    ∃! φ : x.1 ⟶ y.1, p.IsHomLift (𝟙 U) φ ∧ ∀ n, r n ≫ φ = ψ n := by
  refine existsUnique_hom_of_existsUnique_sections p hp U x y hI W ι τ hτ
    (fun Fsp hFsp xs hxs => ?_) z r t ht ψ hψ
  exact FormalSpace.existsUnique_section_of_compatible_truncations_of_finite hR hFsp
    (Over.mk (𝟙 _)) eT (fun n => Over.mk (ι n).left) eW
    (fun n => Over.homMk (ι n).left (Category.comp_id _)) hι
    (fun n => Over.homMk (τ n).left (Over.left_comp_eq_of_comp_eq _ _ _ (hτ n)))
    (fun n => Over.OverMorphism.ext
      (Over.left_comp_eq_of_comp_eq (τ n) (ι (n + 1)) (ι n) (hτ n))) xs hxs

end AlgebraicGeometry.Stack

end

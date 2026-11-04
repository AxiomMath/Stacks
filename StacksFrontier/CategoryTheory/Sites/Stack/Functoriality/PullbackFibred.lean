module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackFractions

/-! # The localization `u_p 𝒮` is a fibred category over `𝒟`

Let `u : 𝒞 ⥤ 𝒟` be a functor and let `p : 𝒮 ⥤ 𝒞` be a category over `𝒞`. Stacks 04WF works with
the category `u_pp 𝒮` of triples `(U, φ : V ⟶ u(U), x ∈ 𝒮_U)`, which is the comma category
`Comma (𝟭 𝒟) (p ⋙ u)`, viewed as a category over `𝒟` through
`p_pp = Comma.fst (𝟭 𝒟) (p ⋙ u)`, and with the set `R` of morphisms `(a, id_V, α)` whose
`𝒟`-component is an identity and whose `𝒮`-component is strongly cartesian. Under the hypotheses
of 04WF — `p` fibred, `𝒞` with nonempty finite limits, `u` commuting with nonempty finite limits —
that set is a right multiplicative system.

Stacks 04WG sets `u_p 𝒮 = R⁻¹ u_pp 𝒮` and asserts that `u_p 𝒮` is a fibred category over `𝒟`.
This file constructs `u_p 𝒮`, constructs the structure functor `p_p : u_p 𝒮 ⥤ 𝒟` extending
`p_pp` over the localization, and proves that `p_p` is fibred.

## Main results

* `CategoryTheory.Comma.pullbackLocalization`: `u_p 𝒮 = R⁻¹ u_pp 𝒮` (Stacks 04WG);
* `CategoryTheory.Comma.pullbackProj`: the structure functor `p_p : u_p 𝒮 ⥤ 𝒟` (Stacks 04WG);
* `CategoryTheory.Comma.isFibered_pullbackProj`: `p_p` is a fibred category (Stacks 04WG).

## Implementation notes

`R⁻¹ u_pp 𝒮` is `MorphismProperty.Localization`, the localization of a category at an arbitrary
morphism property built by formally inverting the arrows of `R`: it exists with no hypothesis on
`R` at all, and it is a localization in the sense of `Functor.IsLocalization`, so the calculus of
fractions supplied by 04WF applies to it through `Localization.exists_rightFraction` and
`MorphismProperty.map_eq_iff_precomp`. The alternative,
`MorphismProperty.LeftFraction.Localization`, is the localization built *out of* fractions and
requires a *left* calculus of fractions, which is not what 04WF provides; and the `IsLocalization`
predicate on an arbitrary functor names no object, so it could not carry the definition of
`u_p 𝒮`. A pleasant consequence of this choice is that the objects of `u_p 𝒮` are in bijection with
those of `u_pp 𝒮` via `Localization.Construction.objEquiv`, so no essential-surjectivity transport
is needed.

Every element of `R` has `𝒟`-component an `eqToHom`, hence an isomorphism, so `p_pp` inverts `R`
and `Localization.Construction.lift` produces `p_p` with `p_pp = Q ⋙ p_p` — this is Categories
04VK of the source, and it is how `u_p 𝒮` is regarded as a category over `𝒟`.

Fibredness is `Functor.IsFibered`, as elsewhere in the tree (Stacks 04WB). By
`Functor.IsFibered.of_exists_isStronglyCartesian` it suffices to produce, for each object of
`u_p 𝒮` and each `β : V' ⟶ V` in `𝒟`, one strongly cartesian lift. The source's proof first
characterizes *all* strongly cartesian morphisms of `u_p 𝒮` — the image of `(a, b, α)` is strongly
cartesian iff `α` is — and then only uses the case `α = id`, namely that
`(id_U, β, id_x) : (U, φ ∘ β, x) ⟶ (U, φ, x)` is strongly cartesian; the source's own remark that
the converse "is not needed later in the proof" applies to the forward direction in the generality
`α` arbitrary as well. So what is proved here is exactly that special case,
`isStronglyCartesian_Q_baseChangeHom`, and this is the reason no fibre product and no equalizer of
`𝒞` occurs below: they enter the source's argument only to force `p(α₁) = p(α₁')` when `α` is a
general strongly cartesian morphism, whereas for `α = id` the two legs are compared directly. The
hypotheses of 04WF are still all used, through the right calculus of fractions.

Faithfulness. (1) `u_p 𝒮` is the localization of the *same* `u_pp 𝒮` at the *same* `R` of 04WF,
which is reused from `CategoryTheory.Comma.hasRightCalculusOfFractions_stronglyCartesianOver`
and not restated. (2) `p_p` is pinned down as a functor
extending `p_pp`, i.e. `Q ⋙ p_p = Comma.fst (𝟭 𝒟) (p ⋙ u)` (`pullbackProj_fac`), not merely
asserted to exist. (3) The conclusion is `Functor.IsFibered p_p`, the tree's notion of a fibred
category, applied to that functor; it is not a `Prop`-valued abbreviation and produces the
cartesian lifts as data. (4) The instantiation is not degenerate: with `𝒮 = 𝒞 = 𝒟`,
`p = u = 𝟭 𝒞` and `𝒞 = Type`, `R` consists of all morphisms `a : x ⟶ x'` over a fixed `V`, so
`u_p 𝒮` is a genuine localization and not `u_pp 𝒮` itself.

Universes. `𝒞 : Type u₁` with `Category.{v₁}`, `𝒟 : Type u₂` with `Category.{v₂}` and
`𝒮 : Type u₃` with `Category.{v₃}` are independent, exactly as in the Tag 04WF statement.
No further universe is introduced and none needs bounding: `Comma (𝟭 𝒟) (p ⋙ u)` lands in
`Type (max u₂ u₃ v₂)` with homs in `Type (max v₂ v₃)`, its localization lands in the same universe
with homs in `Type (max u₂ u₃ v₂ v₃)`, and `Functor.IsFibered` places no constraint between the
universes of a functor's source and target. The general helper
`Localization.exists_common_denominator` carries its own two independent universe pairs.

## References

* [StacksProject 04WG](https://stacks.math.columbia.edu/tag/04WG)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

/-- Two morphisms `χ₁, χ₂ : L(Z) ⟶ L(Y)` of a localization at a morphism property with right
calculus of fractions can be written as right fractions with a *common* denominator: there is a
single `σ : T ⟶ Z` in `W` with `L(σ) ≫ χᵢ = L(hᵢ)` for morphisms `hᵢ : T ⟶ Y` of the original
category. This is Categories 04VI of the source. -/
lemma Localization.exists_common_denominator {C : Type u₄} [Category.{v₄} C] {D : Type u₅}
    [Category.{v₅} D] (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.HasRightCalculusOfFractions] {Z Y : C} (χ₁ χ₂ : L.obj Z ⟶ L.obj Y) :
    ∃ (T : C) (σ : T ⟶ Z) (_ : W σ) (h₁ h₂ : T ⟶ Y),
      L.map σ ≫ χ₁ = L.map h₁ ∧ L.map σ ≫ χ₂ = L.map h₂ := by
  obtain ⟨ϕ₁, hϕ₁⟩ := Localization.exists_rightFraction L W χ₁
  obtain ⟨ϕ₂, hϕ₂⟩ := Localization.exists_rightFraction L W χ₂
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.LeftFraction.mk (W := W) ϕ₁.s ϕ₂.s ϕ₂.hs).exists_rightFraction
  replace hψ : ψ.s ≫ ϕ₁.s = ψ.f ≫ ϕ₂.s := hψ
  refine ⟨ψ.X', ψ.s ≫ ϕ₁.s, W.comp_mem _ _ ψ.hs ϕ₁.hs, ψ.s ≫ ϕ₁.f, ψ.f ≫ ϕ₂.f, ?_, ?_⟩
  · rw [hϕ₁]
    simp
  · rw [hϕ₂, hψ]
    simp

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

namespace Comma

/-- The set `R` of Stacks 04WF as a morphism property on `u_pp 𝒮 = Comma (𝟭 𝒟) (p ⋙ u)`: the
morphisms `(a, id_V, α)` whose `𝒟`-component is an identity and whose `𝒮`-component `α` is
strongly cartesian. This is the property whose right calculus of fractions is
`Comma.hasRightCalculusOfFractions_stronglyCartesianOver`. -/
def idBaseStronglyCartesian (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) :
    MorphismProperty (Comma (𝟭 𝒟) (p ⋙ u)) :=
  fun X Y f => (∃ h : X.left = Y.left, f.left = eqToHom h) ∧ stronglyCartesianOver p f.right

variable (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)

/-- **`u_p 𝒮 = R⁻¹ u_pp 𝒮`**, the localization of `u_pp 𝒮 = Comma (𝟭 𝒟) (p ⋙ u)` at the set `R`
of Stacks 04WF. -/
@[stacks 04WG]
abbrev pullbackLocalization := (idBaseStronglyCartesian p u).Localization

/-- The structure functor `p_pp : u_pp 𝒮 ⥤ 𝒟` sends every element of `R` to an isomorphism: its
`𝒟`-component is an `eqToHom`. -/
lemma isInvertedBy_fst :
    (idBaseStronglyCartesian p u).IsInvertedBy (Comma.fst (𝟭 𝒟) (p ⋙ u)) := by
  intro X Y f hf
  obtain ⟨⟨h, hl⟩, -⟩ := hf
  rw [show (Comma.fst (𝟭 𝒟) (p ⋙ u)).map f = f.left from rfl, hl]
  infer_instance

/-- **The structure functor `p_p : u_p 𝒮 ⥤ 𝒟`**, the extension of `p_pp` to the localization
`u_p 𝒮` obtained from the universal property because `p_pp` inverts `R`. This is how `u_p 𝒮` is
regarded as a category over `𝒟`. -/
@[stacks 04WG]
noncomputable def pullbackProj : pullbackLocalization p u ⥤ 𝒟 :=
  Localization.Construction.lift (Comma.fst (𝟭 𝒟) (p ⋙ u)) (isInvertedBy_fst p u)

/-- `p_p` extends `p_pp` along the localization functor. -/
lemma pullbackProj_fac :
    (idBaseStronglyCartesian p u).Q ⋙ pullbackProj p u = Comma.fst (𝟭 𝒟) (p ⋙ u) :=
  Localization.Construction.fac _ (isInvertedBy_fst p u)

/-- `p_p` is the *only* functor on `u_p 𝒮` extending `p_pp`, so the way `u_p 𝒮` is regarded as a
category over `𝒟` is forced by `p_pp` and not a choice. -/
lemma pullbackProj_uniq (F : pullbackLocalization p u ⥤ 𝒟)
    (hF : (idBaseStronglyCartesian p u).Q ⋙ F = Comma.fst (𝟭 𝒟) (p ⋙ u)) :
    F = pullbackProj p u :=
  Localization.Construction.uniq _ _ (by rw [hF, pullbackProj_fac])

/-- `p_p` sends the image of an object `X` of `u_pp 𝒮` in `u_p 𝒮` to `X.left`. -/
@[simp]
lemma pullbackProj_obj (X : Comma (𝟭 𝒟) (p ⋙ u)) :
    (pullbackProj p u).obj ((idBaseStronglyCartesian p u).Q.obj X) = X.left :=
  Functor.congr_obj (pullbackProj_fac p u) X

/-- `p_p` sends the image of a morphism `f` of `u_pp 𝒮` in `u_p 𝒮` to `f.left`. -/
@[simp]
lemma pullbackProj_map {X Y : Comma (𝟭 𝒟) (p ⋙ u)} (f : X ⟶ Y) :
    (pullbackProj p u).map ((idBaseStronglyCartesian p u).Q.map f) = f.left := by
  simpa using Functor.congr_hom (pullbackProj_fac p u) f

/-- The morphism `(id_U, β, id_x) : (U, φ ∘ β : V' ⟶ u(U), x) ⟶ (U, φ : V ⟶ u(U), x)` of
`u_pp 𝒮` reindexing the `𝒟`-component of an object along `β : V' ⟶ V`. -/
def baseChangeHom (X : Comma (𝟭 𝒟) (p ⋙ u)) {V' : 𝒟} (β : V' ⟶ X.left) :
    Comma.mk V' X.right (β ≫ X.hom) ⟶ X where
  left := β
  right := 𝟙 X.right
  w := by simp

/-- The `𝒟`-component of `baseChangeHom p u X β` is `β`. -/
@[simp]
lemma baseChangeHom_left (X : Comma (𝟭 𝒟) (p ⋙ u)) {V' : 𝒟} (β : V' ⟶ X.left) :
    (baseChangeHom p u X β).left = β := rfl

/-- The `𝒮`-component of `baseChangeHom p u X β` is the identity of `X.right`. -/
@[simp]
lemma baseChangeHom_right (X : Comma (𝟭 𝒟) (p ⋙ u)) {V' : 𝒟} (β : V' ⟶ X.left) :
    (baseChangeHom p u X β).right = 𝟙 X.right := rfl

/-- Applying `p_p` to `Q(s) ≫ χ = Q(f)` gives `s.left ≫ p_p(χ) = f.left`. -/
private theorem left_comp_pullbackProj_map {X Y Z : Comma (𝟭 𝒟) (p ⋙ u)} {s : X ⟶ Y} {f : X ⟶ Z}
    {χ : (idBaseStronglyCartesian p u).Q.obj Y ⟶ (idBaseStronglyCartesian p u).Q.obj Z}
    (h : (idBaseStronglyCartesian p u).Q.map s ≫ χ = (idBaseStronglyCartesian p u).Q.map f) :
    s.left ≫ (pullbackProj p u).map χ = f.left := by
  simpa using congrArg (pullbackProj p u).map h

/-- Every object of `u_p 𝒮` is the image of an object of `u_pp 𝒮`. -/
private theorem exists_Q_obj_eq (a : pullbackLocalization p u) :
    ∃ X, (idBaseStronglyCartesian p u).Q.obj X = a :=
  ⟨_, (Localization.Construction.objEquiv (idBaseStronglyCartesian p u)).apply_symm_apply a⟩

section

variable [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]

/-- Stacks 04WF, restated for `Comma.idBaseStronglyCartesian`. -/
lemma hasRightCalculusOfFractions_idBaseStronglyCartesian
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u) :
    (idBaseStronglyCartesian p u).HasRightCalculusOfFractions :=
  Comma.hasRightCalculusOfFractions_stronglyCartesianOver p u hu

/-- The uniqueness half of the universal property of the reindexing morphism: two morphisms of
`u_p 𝒮` out of `Q(Z)` into the reindexed object which have the same image in `𝒟` and agree after
composition with `(id_U, β, id_x)` are equal.

Both are written over a common denominator `σ ∈ R` (Categories 04VI), and the assumptions say that
the numerators `h₁, h₂` have equal `𝒟`-components and that `Q(h₁ ∘ f₀) = Q(h₂ ∘ f₀)`; the latter
gives (Categories 04VJ) an `r ∈ R` with `r ∘ h₁ ∘ f₀ = r ∘ h₂ ∘ f₀`, whose `𝒮`-component is
`r ∘ h₁ = r ∘ h₂` on the nose because the `𝒮`-component of `f₀` is an identity. -/
lemma hom_ext_of_baseChange
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    {X : Comma (𝟭 𝒟) (p ⋙ u)} {V' : 𝒟} (β : V' ⟶ X.left) {Z : Comma (𝟭 𝒟) (p ⋙ u)}
    (χ₁ χ₂ : (idBaseStronglyCartesian p u).Q.obj Z ⟶
      (idBaseStronglyCartesian p u).Q.obj (Comma.mk V' X.right (β ≫ X.hom)))
    (hmap : (pullbackProj p u).map χ₁ = (pullbackProj p u).map χ₂)
    (hcomp : χ₁ ≫ (idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X β) =
      χ₂ ≫ (idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X β)) :
    χ₁ = χ₂ := by
  have := hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  obtain ⟨T, σ, hσ, h₁, h₂, e₁, e₂⟩ := Localization.exists_common_denominator
    (idBaseStronglyCartesian p u).Q (idBaseStronglyCartesian p u) χ₁ χ₂
  have : IsIso ((idBaseStronglyCartesian p u).Q.map σ) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _ hσ
  have hl : h₁.left = h₂.left := by
    rw [← left_comp_pullbackProj_map p u e₁, ← left_comp_pullbackProj_map p u e₂, hmap]
  have hQ : (idBaseStronglyCartesian p u).Q.map (h₁ ≫ baseChangeHom p u X β) =
      (idBaseStronglyCartesian p u).Q.map (h₂ ≫ baseChangeHom p u X β) := by
    rw [Functor.map_comp, Functor.map_comp, ← e₁, ← e₂, Category.assoc, Category.assoc, hcomp]
  rw [MorphismProperty.map_eq_iff_precomp (idBaseStronglyCartesian p u).Q
    (idBaseStronglyCartesian p u)] at hQ
  obtain ⟨T', r, hr, hrfac⟩ := hQ
  rw [← cancel_epi ((idBaseStronglyCartesian p u).Q.map σ), e₁, e₂,
    MorphismProperty.map_eq_iff_precomp (idBaseStronglyCartesian p u).Q
      (idBaseStronglyCartesian p u)]
  refine ⟨T', r, hr, Comma.hom_ext _ _ ?_ ?_⟩
  · simp [hl]
  · simpa using congrArg CommaMorphism.right hrfac

/-- **The reindexing morphism `(id_U, β, id_x)` becomes strongly cartesian in `u_p 𝒮`.** This is
the case `α = id` of the claim of Stacks 04WG, and it is the case the source uses to conclude.

For existence, a morphism `φ' : Q(Z) ⟶ Q(X)` is `Q(s)⁻¹ ∘ Q(f₂)` for some `s ∈ R` and some
`f₂ : Z₁ ⟶ X` of `u_pp 𝒮`, and the lift is `Q(s)⁻¹ ∘ Q(χ₂)` where `χ₂ : Z₁ ⟶ (U, φ ∘ β, x)` has
the `𝒟`-component prescribed by the required image in `𝒟` and the same `𝒮`-component as `f₂`; no
fibre product is needed because the `𝒞`-part of the object is not changed. -/
lemma isStronglyCartesian_Q_baseChangeHom
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u)
    (X : Comma (𝟭 𝒟) (p ⋙ u)) {V' : 𝒟} (β : V' ⟶ X.left) :
    (pullbackProj p u).IsStronglyCartesian β
      ((idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X β)) := by
  have := hasRightCalculusOfFractions_idBaseStronglyCartesian p u hu
  have hlift : (pullbackProj p u).IsHomLift β
      ((idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X β)) :=
    IsHomLift.of_fac' (pullbackProj p u) β _
      (pullbackProj_obj p u (Comma.mk V' X.right (β ≫ X.hom))) (pullbackProj_obj p u X) (by simp)
  refine { toIsHomLift := hlift, universal_property' := ?_ }
  intro a' g φ' hφ'
  obtain ⟨Z, rfl⟩ := exists_Q_obj_eq p u a'
  -- `g ≫ β` is the image of `φ'` in `𝒟`.
  have hφ'eq : g ≫ β = (pullbackProj p u).map φ' :=
    IsHomLift.eq_of_isHomLift (pullbackProj p u)
      (a := (idBaseStronglyCartesian p u).Q.obj Z)
      (b := (idBaseStronglyCartesian p u).Q.obj X) (g ≫ β) φ'
  -- Write `φ'` as a right fraction.
  obtain ⟨ϕ, hϕ⟩ := Localization.exists_rightFraction
    (idBaseStronglyCartesian p u).Q (idBaseStronglyCartesian p u) φ'
  have hϕs : (idBaseStronglyCartesian p u).Q.map ϕ.s ≫ φ' =
      (idBaseStronglyCartesian p u).Q.map ϕ.f := by
    rw [hϕ]
    exact MorphismProperty.RightFraction.map_s_comp_map ϕ _ _
  obtain ⟨⟨hsl, hsleft⟩, -⟩ := ϕ.hs
  have hstar : eqToHom hsl ≫ g ≫ β = ϕ.f.left := by
    rw [hφ'eq, ← hsleft]
    simpa using congrArg (pullbackProj p u).map hϕs
  -- The numerator of the lift.
  obtain ⟨χ₂, hχ₂left, hχ₂right⟩ :
      ∃ χ₂ : ϕ.X' ⟶ Comma.mk V' X.right (β ≫ X.hom),
        χ₂.left = eqToHom hsl ≫ g ∧ χ₂.right = ϕ.f.right := by
    have hst : (eqToHom hsl ≫ g) ≫ β = ϕ.f.left := by rw [Category.assoc]; exact hstar
    refine ⟨⟨eqToHom hsl ≫ g, ϕ.f.right, ?_⟩, rfl, rfl⟩
    calc (𝟭 𝒟).map (eqToHom hsl ≫ g) ≫ (Comma.mk V' X.right (β ≫ X.hom)).hom
        = ((eqToHom hsl ≫ g) ≫ β) ≫ X.hom := by simp
      _ = ϕ.f.left ≫ X.hom := by rw [hst]
      _ = ϕ.X'.hom ≫ (p ⋙ u).map ϕ.f.right := ϕ.f.w
  have hχ₂f₀ : χ₂ ≫ baseChangeHom p u X β = ϕ.f := by
    refine Comma.hom_ext _ _ ?_ ?_
    · rw [Comma.comp_left, hχ₂left, baseChangeHom_left, Category.assoc]
      exact hstar
    · simp [hχ₂right]
  -- The lift itself, as the right fraction with numerator `χ₂` and denominator `ϕ.s`.
  obtain ⟨χ, hχs⟩ : ∃ χ, (idBaseStronglyCartesian p u).Q.map ϕ.s ≫ χ =
      (idBaseStronglyCartesian p u).Q.map χ₂ :=
    ⟨_, MorphismProperty.RightFraction.map_s_comp_map
      (MorphismProperty.RightFraction.mk ϕ.s ϕ.hs χ₂) _ (Localization.inverts _ _)⟩
  have : IsIso ((idBaseStronglyCartesian p u).Q.map ϕ.s) :=
    Localization.inverts _ (idBaseStronglyCartesian p u) _ ϕ.hs
  have hgχ : (pullbackProj p u).map χ = g := by
    have d := left_comp_pullbackProj_map p u hχs
    rw [hsleft, hχ₂left] at d
    simpa using congrArg (eqToHom hsl.symm ≫ ·) d
  have hχf : χ ≫ (idBaseStronglyCartesian p u).Q.map (baseChangeHom p u X β) = φ' := by
    rw [← cancel_epi ((idBaseStronglyCartesian p u).Q.map ϕ.s), hϕs, ← Category.assoc, hχs,
      ← Functor.map_comp, hχ₂f₀]
  refine ⟨χ, ⟨IsHomLift.of_fac' (pullbackProj p u) g χ rfl
      (pullbackProj_obj p u (Comma.mk V' X.right (β ≫ X.hom))) (by simp [hgχ]), hχf⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have h1 : g = (pullbackProj p u).map y :=
    IsHomLift.eq_of_isHomLift (pullbackProj p u)
      (a := (idBaseStronglyCartesian p u).Q.obj Z)
      (b := (idBaseStronglyCartesian p u).Q.obj (Comma.mk V' X.right (β ≫ X.hom))) g y
  exact hom_ext_of_baseChange p u hu β y χ (by rw [← h1, hgχ]) (by rw [hy2, hχf])

/-- **`u_p 𝒮` is a fibred category over `𝒟`** (Stacks 04WG). Let `u : 𝒞 ⥤ 𝒟` be a functor, let
`p : 𝒮 ⥤ 𝒞` be a fibred category, assume `𝒞` has nonempty finite limits and that `u` commutes
with nonempty finite limits, so that the set `R` of Stacks 04WF is a right multiplicative system.
Then the structure functor `p_p : u_p 𝒮 ⥤ 𝒟` of the localization `u_p 𝒮 = R⁻¹ u_pp 𝒮` is a fibred
category: every morphism `β : V' ⟶ V` of `𝒟` and every object of `u_p 𝒮` over `V` admit a
strongly cartesian lift, namely the image of the reindexing morphism `(id_U, β, id_x)`. -/
@[stacks 04WG]
theorem isFibered_pullbackProj
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u) :
    (pullbackProj p u).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian fun a V' β => ?_
  obtain ⟨X, rfl⟩ := exists_Q_obj_eq p u a
  exact ⟨_, _, isStronglyCartesian_Q_baseChangeHom p u hu X β⟩

end

end Comma

end CategoryTheory

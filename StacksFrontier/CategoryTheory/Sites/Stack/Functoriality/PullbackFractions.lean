module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.MultiplicativeClass
public import StacksFrontier.CategoryTheory.Limits.Finite.Nonempty

/-! # A right multiplicative system on the comma category of a fibred category

Let `u : 𝒞 ⥤ 𝒟` be a functor and let `p : 𝒮 ⥤ 𝒞` be a category over `𝒞`. Stacks 04WF works with
the category `u_pp 𝒮` whose objects are the triples `(U, φ : V ⟶ u(U), x)` with `U` an object of
`𝒞`, `V` an object of `𝒟` and `x` an object of the fibre `𝒮_U`, and whose morphisms
`(U₁, φ₁, x₁) ⟶ (U₂, φ₂, x₂)` are the triples `(a, b, α)` with `a : U₁ ⟶ U₂` in `𝒞`,
`b : V₁ ⟶ V₂` in `𝒟` and `α : x₁ ⟶ x₂` in `𝒮` lying over `a`, such that
`b ≫ φ₂ = φ₁ ≫ u(a)`. Inside it sits the set `R` of morphisms `(a, id_V, α)` whose `𝒟`-component
is an identity and whose `𝒮`-component is strongly cartesian; the localization `R⁻¹ u_pp 𝒮` is the
category `u_p 𝒮` out of which the pullback of a fibred category along a morphism of sites is built
(Stacks 04WG).

The result of this file is that `R` is a right multiplicative system, that is, that it satisfies
RMS1, RMS2 and RMS3 of Stacks 04VC, when `p` is a fibred category, `𝒞` has nonempty finite limits
and `u` commutes with nonempty finite limits. RMS1 is that strongly cartesian morphisms contain the
identities and compose; RMS2 completes a morphism `(a, b, α)` into `(U, φ, x)` and an element
`(c, id_V, γ)` of `R` over it by the fibre product `U₁ ×_U U'`, whose image under `u` is
`u(U₁) ×_{u(U)} u(U')` because `u` commutes with fibre products, so that `(φ₁, φ')` is a morphism
`V₁ ⟶ u(U₁ ×_U U')` of `𝒟`; and RMS3 replaces `U₁` by the equalizer of `a, a'`, whose image under
`u` is the equalizer of `u(a), u(a')` for the same reason.

## Main results

* `CategoryTheory.Comma.hasRightCalculusOfFractions_stronglyCartesianOver`: the morphisms of
  `u_pp 𝒮` with identity `𝒟`-component and strongly cartesian `𝒮`-component form a right
  multiplicative system (Stacks 04WF).

## Implementation notes

The category `u_pp 𝒮` needs no new definition: it is the comma category
`CategoryTheory.Comma (𝟭 𝒟) (p ⋙ u)`, whose objects are the triples `(V, x, φ : V ⟶ u(p(x)))` and
whose morphisms are the pairs `(b, α)` subject to `b ≫ φ₂ = φ₁ ≫ u(p(α))`. Two features of the
source's presentation are absorbed by this: an object `x` of the fibre `𝒮_U` is an object `x` of
`𝒮` with `U = p(x)`, and the component `a` of a morphism is not extra data, being `p.map α` by the
source's condition `p(α) = a`. The functor `p_pp : u_pp 𝒮 ⥤ 𝒟` of the source, which plays no part
in this statement, is `CategoryTheory.Comma.fst (𝟭 𝒟) (p ⋙ u)`.

The source's `id_V` is a morphism between two objects with the *same* `V`, so membership of `R` is
spelled `∃ h : X.left = Y.left, f.left = eqToHom h`; on the `𝒮`-side, `α` strongly cartesian over
its own image is `stronglyCartesianOver p` (Stacks 03WQ), which is
`p.IsStronglyCartesian (p.map α) α`.

"Right multiplicative system" is Mathlib's `MorphismProperty.HasRightCalculusOfFractions`: it
extends `MorphismProperty.IsMultiplicative`, which is RMS1, its field `exists_rightFraction` is
RMS2 and its field `ext` is RMS3, so the conclusion is Stacks 04VC on the nose and not a variant.
Hypothesis (2) is `HasNonemptyFiniteLimits` (Stacks 04AU); the tree has no class for a functor
commuting with nonempty finite limits, so hypothesis (3) is spelled out as
`Limits.PreservesLimitsOfShape J u` for every small finite nonempty shape `J`, which is the same
quantification `HasNonemptyFiniteLimits` uses.

Faithfulness. (1) Every hypothesis is used: `p.IsFibered` provides the strongly cartesian lifts
`γ₁` of RMS2 and `δ` of RMS3, `HasNonemptyFiniteLimits 𝒞` provides the fibre product `U₁ ×_U U'`
of RMS2 and the equalizer of `a, a'` of RMS3, and `hu` is what makes `(φ₁, φ')` a morphism of `𝒟`
into `u(U₁ ×_U U')` and `u(d)` the equalizer of `u(a), u(a')`; none is decoration. (2) The base and
the functors are the source's: `R` is a property on the comma category of the *same* `p` over `𝒞`
and the *same* `u : 𝒞 ⥤ 𝒟`, and "strongly cartesian" is taken over `p`, relative to `𝒞`, not over
`p ⋙ u` or over the projection to `𝒟`. (3) The set the source names is pinned, not merely asserted
to exist: `R` is written out as the morphism property cutting out identity `𝒟`-component together
with strongly cartesian `𝒮`-component, and the conclusion is the conjunction RMS1 + RMS2 + RMS3
about that property. (4) The instantiation is not degenerate: take `𝒮 = 𝒞 = 𝒟` with `p = u = 𝟭 𝒞`
for any `𝒞` with binary products and equalizers, say `Type`; all three hypotheses hold, every
morphism of `𝒞` is strongly cartesian over `𝟭 𝒞`, and `R` then consists of the morphisms
`a : x ⟶ x'` with `φ ≫ a = φ'` between objects `φ : V ⟶ x` and `φ' : V ⟶ x'`, which is far larger
than the set of identities, so the system is a witness rather than an empty one.

## References

* [StacksProject 04WF](https://stacks.math.columbia.edu/tag/04WF)
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒟 : Type u₂} [Category.{v₂} 𝒟]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]

/-- Prepending an `eqToHom` to the base morphism preserves `IsStronglyCartesian`: the decoration
is erased by `subst`. The cartesian lifts produced by `p.IsFibered` lie over a morphism out of
the chosen limit rather than out of `p` of the lifted object, so this moves them across. -/
private lemma isStronglyCartesian_eqToHom_comp {p : 𝒮 ⥤ 𝒞} {R R' S : 𝒞} {a b : 𝒮}
    (hR : R' = R) (f : R ⟶ S) (φ : a ⟶ b) (hf : p.IsStronglyCartesian f φ) :
    p.IsStronglyCartesian (eqToHom hR ≫ f) φ := by
  subst hR; simpa using hf

/-- A strongly cartesian lift of a morphism `f : R ⟶ p(x)` of a fibred category, with source
`z` such that `p(z) = R`, lies over `f` up to the `eqToHom` of that equality. -/
private lemma exists_stronglyCartesianOver_lift (p : 𝒮 ⥤ 𝒞) [p.IsFibered] {x : 𝒮} {R : 𝒞}
    (f : R ⟶ p.obj x) :
    ∃ (z : 𝒮) (γ : z ⟶ x) (hz : p.obj z = R),
      p.map γ = eqToHom hz ≫ f ∧ stronglyCartesianOver p γ := by
  obtain ⟨z, γ, _⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) (a := x) f
  have hz : p.obj z = R := IsHomLift.domain_eq p f γ
  have hγmap : p.map γ = eqToHom hz ≫ f := by simpa using IsHomLift.fac' p f γ
  refine ⟨z, γ, hz, hγmap, ?_⟩
  dsimp only [stronglyCartesianOver]
  rw [hγmap]
  exact isStronglyCartesian_eqToHom_comp hz _ γ inferInstance

/-- Applying `F` to the `eqToHom` that cancels the one in `g = eqToHom h ≫ f` gives `F.map f`. -/
private lemma map_eqToHom_symm_comp_map {F : 𝒞 ⥤ 𝒟} {A B C : 𝒞} (h : A = B) (f : B ⟶ C)
    (g : A ⟶ C) (hg : g = eqToHom h ≫ f) : F.map (eqToHom h.symm) ≫ F.map g = F.map f := by
  subst h; simp [hg]

/-- RMS1 for the set `R`: it contains the identities and is stable under composition. The
`𝒟`-component of a composite of two `eqToHom`s is the `eqToHom` of the composite equality, and
strongly cartesian morphisms compose (Stacks 02XL). -/
private lemma isMultiplicative_stronglyCartesianOver (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) :
    MorphismProperty.IsMultiplicative
      (fun (X Y : Comma (𝟭 𝒟) (p ⋙ u)) (f : X ⟶ Y) =>
        (∃ h : X.left = Y.left, f.left = eqToHom h) ∧ stronglyCartesianOver p f.right) :=
  have : MorphismProperty.ContainsIdentities
      (fun (X Y : Comma (𝟭 𝒟) (p ⋙ u)) (f : X ⟶ Y) =>
        (∃ h : X.left = Y.left, f.left = eqToHom h) ∧ stronglyCartesianOver p f.right) :=
    ⟨fun X => ⟨⟨rfl, by simp⟩, stronglyCartesianOver_id p X.right⟩⟩
  have : MorphismProperty.IsStableUnderComposition
      (fun (X Y : Comma (𝟭 𝒟) (p ⋙ u)) (f : X ⟶ Y) =>
        (∃ h : X.left = Y.left, f.left = eqToHom h) ∧ stronglyCartesianOver p f.right) :=
    ⟨fun f g hf hg => by
      obtain ⟨⟨h₁, hf₁⟩, hf₂⟩ := hf
      obtain ⟨⟨h₂, hg₁⟩, hg₂⟩ := hg
      exact ⟨⟨h₁.trans h₂, by rw [Comma.comp_left, hf₁, hg₁, eqToHom_trans]⟩,
        stronglyCartesianOver_comp p f.right g.right hf₂ hg₂⟩⟩
  ⟨⟩

/-- RMS2 for the set `R`. Given `f : X ⟶ Y'` and an element `s : Y ⟶ Y'` of `R`, the fibre
product `p(X) ×_{p(Y')} p(Y)` in `𝒞` carries a strongly cartesian lift `γ`, and because `u`
commutes with the fibre product the pair `(X.hom, f.left ≫ Y.hom)` is a morphism of `𝒟` into
`u(p(X) ×_{p(Y')} p(Y))`. That produces the object `X'` and the element `t = (γ, id)` of `R`
over `X`; the second leg `g` is the factorization of `γ ≫ f.right` through the strongly
cartesian `s.right`. -/
private lemma exists_rightFraction_stronglyCartesianOver (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)
    [p.IsFibered] [Limits.HasPullbacks 𝒞]
    [Limits.PreservesLimitsOfShape Limits.WalkingCospan u]
    {X Y Y' : Comma (𝟭 𝒟) (p ⋙ u)} (f : X ⟶ Y') (s : Y ⟶ Y')
    (hs : Y.left = Y'.left) (hsl : s.left = eqToHom hs)
    (hsc : stronglyCartesianOver p s.right) :
    ∃ (X' : Comma (𝟭 𝒟) (p ⋙ u)) (t : X' ⟶ X) (g : X' ⟶ Y),
      ((∃ h : X'.left = X.left, t.left = eqToHom h) ∧ stronglyCartesianOver p t.right) ∧
        t ≫ f = g ≫ s := by
  have : p.IsStronglyCartesian (p.map s.right) s.right := hsc
  -- A strongly cartesian lift `γ` of the first projection of `p(X) ×_{p(Y')} p(Y)`.
  obtain ⟨z, γ, hz, hγmap, hγ⟩ := exists_stronglyCartesianOver_lift (x := X.right) p
    (Limits.pullback.fst (p.map f.right) (p.map s.right))
  -- The second leg, from the universal property of the strongly cartesian `s.right`.
  have hβ' : p.map (γ ≫ f.right) =
      (eqToHom hz ≫ Limits.pullback.snd (p.map f.right) (p.map s.right)) ≫ p.map s.right := by
    rw [p.map_comp, hγmap, Category.assoc, Category.assoc, Limits.pullback.condition]
  obtain ⟨β, ⟨hβlift, hβfac⟩, -⟩ :=
    Functor.IsStronglyCartesian.universal_property p (p.map s.right) s.right
      (eqToHom hz ≫ Limits.pullback.snd (p.map f.right) (p.map s.right))
      (p.map (γ ≫ f.right)) hβ' (γ ≫ f.right)
  have hβmap : p.map β =
      eqToHom hz ≫ Limits.pullback.snd (p.map f.right) (p.map s.right) := by
    have := hβlift
    exact (IsHomLift.eq_of_isHomLift p _ β).symm
  -- `u` commutes with the fibre product, so `(X.hom, f.left ≫ Y.hom)` lifts to it.
  have hfw : X.hom ≫ u.map (p.map f.right) = f.left ≫ Y'.hom := f.w.symm
  have hsw : Y.hom ≫ u.map (p.map s.right) = eqToHom hs ≫ Y'.hom := by
    rw [← hsl]; exact s.w.symm
  obtain ⟨ψ, hψ₁, hψ₂⟩ :
      ∃ ψ : X.left ⟶ u.obj (Limits.pullback (p.map f.right) (p.map s.right)),
        ψ ≫ u.map (Limits.pullback.fst (p.map f.right) (p.map s.right)) = X.hom ∧
          ψ ≫ u.map (Limits.pullback.snd (p.map f.right) (p.map s.right)) =
            f.left ≫ eqToHom hs.symm ≫ Y.hom := by
    obtain ⟨ψ, hψ₁, hψ₂⟩ := Limits.PullbackCone.IsLimit.lift'
      (Limits.isLimitOfHasPullbackOfPreservesLimit u (p.map f.right) (p.map s.right))
      X.hom (f.left ≫ eqToHom hs.symm ≫ Y.hom) (by
        rw [hfw, Category.assoc, Category.assoc, hsw, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp])
    exact ⟨ψ, hψ₁, hψ₂⟩
  -- The two `eqToHom` cancellations that make the comma-square conditions hold.
  refine ⟨Comma.mk X.left z (ψ ≫ u.map (eqToHom hz.symm)), ⟨𝟙 X.left, γ, ?_⟩,
    ⟨f.left ≫ eqToHom hs.symm, β, ?_⟩, ⟨⟨rfl, by simp⟩, ?_⟩, ?_⟩
  · dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
    rw [Category.id_comp, Category.assoc, map_eqToHom_symm_comp_map hz _ _ hγmap, hψ₁]
  · dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
    rw [Category.assoc, Category.assoc, map_eqToHom_symm_comp_map hz _ _ hβmap, hψ₂]
  · exact hγ
  · refine Comma.hom_ext _ _ ?_ ?_
    · dsimp only [Functor.id_obj, Functor.comp_obj, Comma.comp_left]
      rw [Category.id_comp, hsl, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    · dsimp only
      exact hβfac.symm

/-- RMS3 for the set `R`. Two morphisms `f₁, f₂ : X ⟶ Y` equalized by postcomposition with an
element `s` of `R` have equal `𝒟`-components, and their base components `a₁, a₂` are equalized
by `p(s.right)`. The equalizer `E` of `a₁, a₂` in `𝒞` carries a strongly cartesian lift `δ`, and
`u(E)` is the equalizer of `u(a₁), u(a₂)`, so `X.hom` factors through it. Precomposing with
`t = (δ, id)` equalizes `f₁, f₂` by the uniqueness half of the universal property of the
strongly cartesian `s.right`. -/
private lemma ext_stronglyCartesianOver (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟)
    [p.IsFibered] [Limits.HasEqualizers 𝒞]
    [Limits.PreservesLimitsOfShape Limits.WalkingParallelPair u]
    {X Y Y' : Comma (𝟭 𝒟) (p ⋙ u)} (f₁ f₂ : X ⟶ Y) (s : Y ⟶ Y')
    (hs : Y.left = Y'.left) (hsl : s.left = eqToHom hs)
    (hsc : stronglyCartesianOver p s.right) (hfs : f₁ ≫ s = f₂ ≫ s) :
    ∃ (X' : Comma (𝟭 𝒟) (p ⋙ u)) (t : X' ⟶ X),
      ((∃ h : X'.left = X.left, t.left = eqToHom h) ∧ stronglyCartesianOver p t.right) ∧
        t ≫ f₁ = t ≫ f₂ := by
  have : p.IsStronglyCartesian (p.map s.right) s.right := hsc
  -- The two components of `f₁ ≫ s = f₂ ≫ s`.
  have hleft : f₁.left = f₂.left := by
    have h : (f₁ ≫ s).left = (f₂ ≫ s).left := by rw [hfs]
    rw [Comma.comp_left, Comma.comp_left, hsl] at h
    exact (cancel_mono (eqToHom hs)).mp h
  have hright : f₁.right ≫ s.right = f₂.right ≫ s.right := by
    have h : (f₁ ≫ s).right = (f₂ ≫ s).right := by rw [hfs]
    rwa [Comma.comp_right, Comma.comp_right] at h
  -- A strongly cartesian lift `δ` of the equalizer of the two base components.
  obtain ⟨w, δ, hw, hδmap, hδ⟩ := exists_stronglyCartesianOver_lift (x := X.right) p
    (Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right))
  -- `u` commutes with the equalizer, so `X.hom` factors through `u(E)`.
  have hf₁w : X.hom ≫ u.map (p.map f₁.right) = f₁.left ≫ Y.hom := f₁.w.symm
  have hf₂w : X.hom ≫ u.map (p.map f₂.right) = f₂.left ≫ Y.hom := f₂.w.symm
  obtain ⟨ψ, hψ⟩ :
      ∃ ψ : X.left ⟶ u.obj (Limits.equalizer (p.map f₁.right) (p.map f₂.right)),
        ψ ≫ u.map (Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right)) = X.hom := by
    obtain ⟨ψ, hψ⟩ := Limits.Fork.IsLimit.lift'
      (Limits.isLimitOfHasEqualizerOfPreservesLimit u (p.map f₁.right) (p.map f₂.right))
      X.hom (by rw [hf₁w, hf₂w, hleft])
    exact ⟨ψ, hψ⟩
  refine ⟨Comma.mk X.left w (ψ ≫ u.map (eqToHom hw.symm)), ⟨𝟙 X.left, δ, ?_⟩,
    ⟨⟨rfl, by simp⟩, ?_⟩, ?_⟩
  · dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map]
    rw [Category.id_comp, Category.assoc, map_eqToHom_symm_comp_map hw _ _ hδmap, hψ]
  · exact hδ
  · refine Comma.hom_ext _ _ ?_ ?_
    · dsimp only [Functor.id_obj, Functor.comp_obj, Comma.comp_left]
      rw [hleft]
    · dsimp only [Functor.id_obj, Functor.comp_obj, Comma.comp_right]
      have h₁ : p.IsHomLift (eqToHom hw ≫
          Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right) ≫ p.map f₁.right)
          (δ ≫ f₁.right) := by
        have h : p.map (δ ≫ f₁.right) = eqToHom hw ≫
            Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right) ≫ p.map f₁.right := by
          rw [p.map_comp, hδmap, Category.assoc]
        rw [← h]; infer_instance
      have h₂ : p.IsHomLift (eqToHom hw ≫
          Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right) ≫ p.map f₁.right)
          (δ ≫ f₂.right) := by
        have h : p.map (δ ≫ f₂.right) = eqToHom hw ≫
            Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right) ≫ p.map f₁.right := by
          rw [p.map_comp, hδmap, Category.assoc,
            Limits.equalizer.condition (p.map f₁.right) (p.map f₂.right)]
        rw [← h]; infer_instance
      have := h₁
      have := h₂
      exact Functor.IsStronglyCartesian.ext p (p.map s.right) s.right
        (eqToHom hw ≫ Limits.equalizer.ι (p.map f₁.right) (p.map f₂.right) ≫ p.map f₁.right)
        (by rw [Category.assoc, Category.assoc, hright])

/-- **The morphisms with identity base component and strongly cartesian fibre component form a
right multiplicative system.** Let `u : 𝒞 ⥤ 𝒟` be a functor, let `p : 𝒮 ⥤ 𝒞` be a fibred category,
assume `𝒞` has nonempty finite limits and that `u` commutes with nonempty finite limits. In the
category `u_pp 𝒮 = Comma (𝟭 𝒟) (p ⋙ u)`, whose objects are the triples
`(U, φ : V ⟶ u(U), x ∈ 𝒮_U)`, consider the set `R` of morphisms
`(a, id_V, α) : (U', φ' : V ⟶ u(U'), x') ⟶ (U, φ : V ⟶ u(U), x)` whose `𝒟`-component is an
identity and whose `α` is strongly cartesian. Then `R` is a right multiplicative system: it
contains the identities and is stable under composition (RMS1), every left fraction over `R` can
be turned into a right fraction (RMS2), and two morphisms equalized by postcomposition with an
element of `R` are equalized by precomposition with an element of `R` (RMS3). -/
@[stacks 04WF]
public theorem Comma.hasRightCalculusOfFractions_stronglyCartesianOver
    (p : 𝒮 ⥤ 𝒞) (u : 𝒞 ⥤ 𝒟) [p.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (hu : ∀ (J : Type) [SmallCategory J] [FinCategory J] [Nonempty J],
      Limits.PreservesLimitsOfShape J u) :
    MorphismProperty.HasRightCalculusOfFractions
      (fun (X Y : Comma (𝟭 𝒟) (p ⋙ u)) (f : X ⟶ Y) =>
        (∃ h : X.left = Y.left, f.left = eqToHom h) ∧ stronglyCartesianOver p f.right) := by
  have : Limits.HasBinaryProducts 𝒞 := hasBinaryProducts_of_hasNonemptyFiniteLimits 𝒞
  have : Limits.HasEqualizers 𝒞 := hasEqualizers_of_hasNonemptyFiniteLimits 𝒞
  have : Limits.HasPullbacks 𝒞 :=
    Limits.hasPullbacks_of_hasBinaryProducts_of_hasEqualizers 𝒞
  have : Nonempty Limits.WalkingCospan := ⟨Limits.WalkingCospan.one⟩
  have : Nonempty Limits.WalkingParallelPair := ⟨Limits.WalkingParallelPair.zero⟩
  have := hu Limits.WalkingCospan
  have := hu Limits.WalkingParallelPair
  have := isMultiplicative_stronglyCartesianOver p u
  exact
    { exists_rightFraction := fun {X Y} φ => by
        obtain ⟨⟨hs, hsl⟩, hsc⟩ := φ.hs
        obtain ⟨X', t, g, ht, hcomm⟩ :=
          exists_rightFraction_stronglyCartesianOver p u φ.f φ.s hs hsl hsc
        exact ⟨MorphismProperty.RightFraction.mk t ht g, hcomm⟩
      ext := fun {X Y Y'} f₁ f₂ s hs hfs => by
        obtain ⟨⟨hsl, hsl'⟩, hsc⟩ := hs
        obtain ⟨X', t, ht, hcomm⟩ :=
          ext_stronglyCartesianOver p u f₁ f₂ s hsl hsl' hsc hfs
        exact ⟨X', t, ht, hcomm⟩ }

end CategoryTheory

end

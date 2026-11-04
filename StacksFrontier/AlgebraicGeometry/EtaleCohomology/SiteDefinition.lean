module

public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite
import StacksCore.Tactic.StacksAttribute

/-!
# The definition of a site

A *site* consists of a category `C` together with a class `Cov(C)` of families of morphisms with
fixed target, called *coverings*, such that

1. (isomorphism) if `φ : V ⟶ U` is an isomorphism, then `{φ : V ⟶ U}` is a covering;
2. (locality) if `{φᵢ : Uᵢ ⟶ U}_{i ∈ I}` is a covering and for every `i ∈ I` we are given a
   covering `{ψᵢⱼ : Uᵢⱼ ⟶ Uᵢ}_{j ∈ Iᵢ}`, then `{φᵢ ∘ ψᵢⱼ : Uᵢⱼ ⟶ U}` indexed by
   `∐_{i ∈ I} Iᵢ = ⋃_{i ∈ I} {i} × Iᵢ` is again a covering;
3. (base change) if `{Uᵢ ⟶ U}_{i ∈ I}` is a covering and `V ⟶ U` is a morphism of `C`, then
   the fibre products `Uᵢ ×_U V` exist in `C` and `{Uᵢ ×_U V ⟶ V}_{i ∈ I}` is a covering.

A covering family is `Covering.{u, v, w} C`, an object of `C` bundled with a
`CategoryTheory.PreZeroHypercover.{w}` over it, so that the index universe `w` is independent of
the object and morphism universes of `C`. The three axioms are `IsoCond`, `CompositionCond` and
`BaseChangeCond`, conjoined in `IsSite`; the base change axiom carries the existence of the
fibre products as an `IsPullback` statement, so no `HasPullbacks` instance is assumed.

## Main results

* `isSite_iff`: `IsSite IsCov` holds exactly when the three axioms hold in the element-wise
  shape the definition states them in. The two formulations package the locality axiom
  differently: `CompositionCond` takes each refining covering with its own target together with
  an equality identifying that target with `Uᵢ`, composes with `PreZeroHypercover.bind` and
  pushes forward along the resulting `eqToHom`, whereas the definition composes the morphisms
  `φᵢ ∘ ψᵢⱼ` directly. The lemma shows the two agree, so the transports cost nothing.

## References

* [Stacks Project, Tag 03NH](https://stacks.math.columbia.edu/tag/03NH)
* [SGA 4, Exposé II, Définition 1.3][SGA4]
* [M. Artin, *Grothendieck Topologies*][ArtinTopologies]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- **The definition of a site, element-wise.** A class `IsCov` of covering families of `C`
satisfies `IsSite` if and only if it satisfies the isomorphism, locality and base change axioms
written out on families `{φᵢ : Uᵢ ⟶ U}_{i ∈ I}`: the one-element family on an isomorphism is a
covering, a covering refined by coverings composes to the covering `{φᵢ ∘ ψᵢⱼ}` indexed by
`Σ i, Iᵢ`, and a covering admits base change along any `g : V ⟶ U`, the fibre products
`Uᵢ ×_U V` being asserted to exist as part of the axiom. -/
theorem isSite_iff (IsCov : Covering.{u, v, w} C → Prop) :
    IsSite IsCov ↔
      (∀ (U V : C) (φ : V ⟶ U), IsIso φ →
          IsCov ⟨U, ⟨PUnit.{w + 1}, fun _ => V, fun _ => φ⟩⟩) ∧
      (∀ (U : C) (I : Type w) (Uᵢ : I → C) (φ : ∀ i, Uᵢ i ⟶ U), IsCov ⟨U, ⟨I, Uᵢ, φ⟩⟩ →
          ∀ (I' : I → Type w) (Uᵢⱼ : ∀ i, I' i → C) (ψ : ∀ i (j : I' i), Uᵢⱼ i j ⟶ Uᵢ i),
            (∀ i, IsCov ⟨Uᵢ i, ⟨I' i, Uᵢⱼ i, ψ i⟩⟩) →
            IsCov ⟨U, ⟨(i : I) × I' i, fun p => Uᵢⱼ p.1 p.2, fun p => ψ p.1 p.2 ≫ φ p.1⟩⟩) ∧
      (∀ (U : C) (I : Type w) (Uᵢ : I → C) (φ : ∀ i, Uᵢ i ⟶ U), IsCov ⟨U, ⟨I, Uᵢ, φ⟩⟩ →
          ∀ (V : C) (g : V ⟶ U),
            ∃ (P : I → C) (p : ∀ i, P i ⟶ Uᵢ i) (q : ∀ i, P i ⟶ V),
              (∀ i, IsPullback (p i) (q i) (φ i) g) ∧ IsCov ⟨V, ⟨I, P, q⟩⟩) := by
  constructor
  · rintro ⟨hIso, hComp, hBC⟩
    refine ⟨fun U V φ _ => hIso φ, fun U I Uᵢ φ hU I' Uᵢⱼ ψ hψ => ?_,
      fun U I Uᵢ φ hU => hBC ⟨U, ⟨I, Uᵢ, φ⟩⟩ hU⟩
    -- The refining coverings have target `Uᵢ` on the nose, so the transport is `eqToHom rfl`.
    simpa [PreZeroHypercover.bind, PreZeroHypercover.pushforward] using
      hComp ⟨U, ⟨I, Uᵢ, φ⟩⟩ hU (fun i => ⟨Uᵢ i, ⟨I' i, Uᵢⱼ i, ψ i⟩⟩) hψ fun _ => rfl
  · rintro ⟨kIso, kComp, kBC⟩
    -- Transporting a covering of `W` along an equality `W = V` leaves it a covering of `V`.
    have key : ∀ (V : C) (𝒲 : Covering.{u, v, w} C) (e : 𝒲.1 = V), IsCov 𝒲 →
        IsCov ⟨V, 𝒲.2.pushforward (eqToHom e)⟩ := by
      rintro V ⟨W, F⟩ rfl hF
      simpa [PreZeroHypercover.pushforward] using hF
    refine ⟨?_, ?_, ?_⟩
    · intro U V φ _
      simpa [PreZeroHypercover.singleton] using kIso U V φ ‹IsIso φ›
    · rintro ⟨U, E⟩ hU 𝒱 h𝒱 h
      exact kComp U E.I₀ E.X E.f hU (fun i => (𝒱 i).2.I₀) (fun i j => (𝒱 i).2.X j)
        (fun i j => (𝒱 i).2.f j ≫ eqToHom (h i)) fun i => key _ (𝒱 i) (h i) (h𝒱 i)
    · rintro ⟨U, E⟩ hU V g
      exact kBC U E.I₀ E.X E.f hU V g

add_to_stacks 03NH IsSite

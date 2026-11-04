module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Localized
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.Pushforward
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.SupportedIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.PerfectChernProperties

/-!
# Capping localized Chern classes with classes from `Z` and from away from `Z`

Let `(S, δ)`, `X`, `i : Z ⟶ X`, `E ∈ D(𝒪_X)` and `p ≥ 0` be as in Situation 0GUJ
(`Stacks.Chow.LocalizedSituation`), and let `P_p(Z ⟶ X, E)`, resp. `c_p(Z ⟶ X, E)`, in
`A^p(Z ⟶ X)` be the localized classes of Stacks 0FB2. This file proves the two computations of
their cap products which characterize them on the two members of a closed cover.

* **Stacks 0FB4.** For `α ∈ CH_*(Z)`,
  `P_p(Z ⟶ X, E) ∩ i_* α = P_p(E|_Z) ∩ α`, resp. `c_p(Z ⟶ X, E) ∩ i_* α = c_p(E|_Z) ∩ α`.
  This holds for every bivariant class `c ∈ A^p(Z ⟶ X)` of a closed immersion and every
  `a ∈ A^p(Z)` restricting `i_* ∘ c ∈ A^p(X)`: by proper naturality `c ∩ i_* α` is computed on
  the test scheme `Z` itself, where it is `(i_* ∘ c) ∩ α`, the base change of `i` along `i` being
  the identity. By `i_* ∘ P_p(Z ⟶ X, E) = P_p(E)` (Stacks 0FB2) and `P_p(E)|_Z = P_p(E|_Z)`, the
  class `a = P_p(E|_Z)` is such a restriction.
* **Stacks 0FB6.** If `α ∈ CH_k(X)` has support disjoint from `Z`, then
  `P_p(Z ⟶ X, E) ∩ α = 0`, resp. `c_p(Z ⟶ X, E) ∩ α = 0`. This holds for every bivariant
  class `c ∈ A^p(W ⟶ X)`: if `α` is pushed forward from a scheme `V` over `X` whose image misses
  that of `W`, proper naturality computes `c ∩ α` from a class on `V ×_X W = ∅`.

Both are proved after every base change `X' ⟶ X` locally of finite type, in the form in which
they enter the characterization of Stacks 0F9H (`Stacks.Chow.IsClosedCoverExtension`): on every
test scheme `g : T ⟶ X`, for classes pushed forward from `T ×_X Z`, resp. for classes pushed
forward along a proper `e : T₀ ⟶ T` such that `T₀ ⟶ X` factors through a scheme with image
disjoint from `Z` (`Stacks.Chow.BivariantClass.CapVanishesOver`).

## Main results

* `Stacks.Chow.BivariantClass.cap_chowPush_pullbackSnd_of_isRestriction` — for a closed
  immersion `i : Z ⟶ X`, `c ∈ A^p(Z ⟶ X)` and a restriction `a ∈ A^p(Z)` of `i_* ∘ c`, on every
  test scheme `c ∩ i_* α = a ∩ α`.
* `Stacks.Chow.BivariantClass.capVanishesOver_of_disjoint` — a class of `A^p(W ⟶ X)` caps to
  zero over every morphism whose image is disjoint from that of `W`.
* `Stacks.Chow.BivariantClass.CapVanishesOver.bivariantProperPushforward`,
  `Stacks.Chow.BivariantClass.CapVanishesOver.congrHom` — capping to zero over a morphism is
  preserved by the pushforward of Stacks 0EPK.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_cap_chowPush`,
  `Stacks.Chow.LocalizedSituation.localizedChern_cap_chowPush` — Stacks 0FB4.
* `Stacks.Chow.LocalizedSituation.localizedPowerSum_capVanishesOver`,
  `Stacks.Chow.LocalizedSituation.localizedChern_capVanishesOver` — Stacks 0FB6.

## Implementation notes

The source proves Stacks 0FB4 through Stacks 0FB3, by identifying the restriction of
`c_p(Z ⟶ X, E)` to `Z` with the localized class of `id : Z ⟶ Z` and `E|_Z`. The argument here
uses only the identity `i_* ∘ c_p(Z ⟶ X, E) = c_p(E)` of Stacks 0FB2, read on test schemes over
`Z`: there the base change of `i` is an isomorphism, so the bivariant class and its pushforward
have the same cap product.

A class `α ∈ CH_k(X)` with support disjoint from `Z` is the pushforward of a class on a closed
subscheme `X₁ ⊆ X` with `X₁ ∩ Z = ∅`; the statement of Stacks 0FB6 here allows any scheme
`V ⟶ X` with image disjoint from `Z` in place of `X₁`, and every test scheme.

## References

* [Stacks Project, Tag 0FB4](https://stacks.math.columbia.edu/tag/0FB4)
* [Stacks Project, Tag 0FB6](https://stacks.math.columbia.edu/tag/0FB6)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0F9H](https://stacks.math.columbia.edu/tag/0F9H)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Capping with classes pushed forward from `Z` -/

section Restriction

variable {C : ChowSituation.{u}} {X Z : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {i : Z ⟶ X} [IsClosedImmersion i] {hi : i ≫ sX = sZ}
  {p : ℤ}

/-- **`c ∩ i_* α = a ∩ α` for a restriction `a` of `i_* ∘ c`.** Let `i : Z ⟶ X` be a closed
immersion, `c ∈ A^p(Z ⟶ X)`, and let `a ∈ A^p(Z)` operate on test schemes over `Z` as
`i_* ∘ c ∈ A^p(X)` does (Stacks 0EPK). On every test scheme `g : T ⟶ X`, the cap product of `c`
with a class pushed forward from `T ×_X Z` is the operation of `a` on it. By proper naturality the
cap product is computed on the test scheme `T ×_X Z ⟶ X`, which factors through `i`, so that the
base change of `i` along it is an isomorphism and `c` caps there as `i_* ∘ c` does. -/
theorem BivariantClass.cap_chowPush_pullbackSnd_of_isRestriction
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sX i hi p)
    {a : chowCohomologyComponent C (gysinSystemOfInvertible C) sZ p}
    (ha : a.IsRestriction (properPushforwardChowCohomology C sX sZ i hi c) i) {T : Scheme.{u}}
    (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (pullback.fst i g ≫ sZ) k) :
    c.cap g k (chowPush C _ _ (pullback.snd i g) (pullbackSnd_comp_structureMorphism hi g) k α) =
      a.idRule C sZ (gysinSystemOfInvertible C) (pullback.fst i g) k α := by
  have hm : pullback.snd i g ≫ g = pullback.fst i g ≫ i := pullback.condition.symm
  have hs : pullback.fst i g ≫ sZ = (pullback.snd i g ≫ g) ≫ sX := by
    rw [hm, Category.assoc, hi]
  have hy : pullback.fst i g ≫ sZ = (pullback.fst i g ≫ i) ≫ sX := by
    rw [Category.assoc, hi]
  have hfst : pullback.snd i (pullback.snd i g ≫ g) ≫ pullback.fst i g =
      pullback.fst i (pullback.snd i g ≫ g) := by
    rw [← cancel_mono i, Category.assoc, pullback.condition (f := i) (g := g)]
    exact pullback.condition.symm
  have hbc : bivariantBaseChangeMap i g (pullback.snd i g) =
      pullback.snd i (pullback.snd i g ≫ g) := by
    refine pullback.hom_ext ?_ ?_
    · simp [bivariantBaseChangeMap, hfst]
    · simp [bivariantBaseChangeMap]
  have sq : IsPullback (pullback.snd i (pullback.snd i g ≫ g))
      (pullback.snd i (pullback.snd i g ≫ g)) (pullback.snd i g) (pullback.snd i g) :=
    hbc ▸ isPullback_bivariantBaseChangeMap i g (pullback.snd i g)
  set α' : chowGroup C ((pullback.snd i g ≫ g) ≫ sX) k := chowGroupCongr C hs k α
  have hα' : α' ≍ α := chowGroupCongr_heq C hs k α
  have h1 := c.proper_naturality g (pullback.snd i g) _ sq hfst k
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) α'
  have h2 := idRule_properPushforwardChowCohomology C sX sZ i hi c (pullback.snd i g ≫ g) k α'
  have h3 := ha (pullback.fst i g) k α (chowGroupCongr C hy k α)
    (chowGroupCongr_heq C hy k α).symm
  have h4 := IdentityCapRule.heq_congr C sX
    ((properPushforwardChowCohomology C sX sZ i hi c).idRule C sX (gysinSystemOfInvertible C))
    hm rfl (hα'.trans (chowGroupCongr_heq C hy k α).symm)
  refine eq_of_heq ((HEq.trans ?_ (heq_of_eq h2.symm)).trans (h4.trans h3.symm))
  refine HEq.trans (heq_of_eq ?_) (HEq.trans (heq_of_eq h1) ?_)
  · exact congrArg _ (eq_of_heq (chowPush_heq C _ _ _ hs rfl rfl hα'.symm))
  · exact chowPush_heq C _ _ _ rfl hs rfl HEq.rfl

end Restriction

/-! ### Capping with classes supported away from `W` -/

section Disjoint

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X W V : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sW : W ⟶ C.S} [LocallyOfFiniteType sW] {f : W ⟶ X}
  [LocallyOfFiniteType f] {hf : f ≫ sX = sW} {p : ℤ}

/-- **A bivariant class kills the classes supported away from its source.** A class
`c ∈ A^p(W ⟶ X)` caps to zero over every `z : V ⟶ X` whose image is disjoint from that of
`f : W ⟶ X`: by proper naturality, the cap product of a class pushed forward along `e : T₀ ⟶ T`
is pushed forward from the Chow group of `T₀ ×_X W`, and this scheme is empty. -/
theorem BivariantClass.capVanishesOver_of_disjoint (c : BivariantClass C G sW sX f hf p)
    (z : V ⟶ X) (hz : Disjoint (Set.range z) (Set.range f)) : c.CapVanishesOver z := by
  intro T T₀ g _ e _ m hm sT₀ _ he k γ
  have hs : (e ≫ g) ≫ sX = sT₀ := by rw [Category.assoc, he]
  subst hs
  have : IsEmpty ↥(pullback f (e ≫ g)) := by
    refine ⟨fun (w : ↥(pullback f (e ≫ g))) ↦
      Set.disjoint_left.1 hz ⟨m (pullback.snd f (e ≫ g) w), ?_⟩ ⟨pullback.fst f (e ≫ g) w, rfl⟩⟩
    rw [← Scheme.Hom.comp_apply, hm, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      pullback.condition]
  have := subsingleton_chowGroup_of_isEmpty C (pullback.fst f (e ≫ g) ≫ sW) (k - p)
  refine (c.proper_naturality g e (bivariantBaseChangeMap f g e)
    (isPullback_bivariantBaseChangeMap f g e) (by simp [bivariantBaseChangeMap]) k
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence C _ _ _ _ _) γ).trans ?_
  rw [Subsingleton.elim (c.cap (e ≫ g) k γ) 0, map_zero]

end Disjoint

/-! ### Capping to zero and the pushforward of Stacks 0EPK -/

section Pushforward

variable {C : ChowSituation.{u}} {E X Y V : Scheme.{u}} {sE : E ⟶ C.S} [LocallyOfFiniteType sE]
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {p : ℤ}
  {z : V ⟶ X}

/-- **Capping to zero is preserved by proper pushforward.** If `c ∈ A^p(E ⟶ X)` caps to zero
over `z : V ⟶ X`, so does `f₁_* ∘ c ∈ A^p(Y ⟶ X)` (Stacks 0EPK) for every proper `f₁ : E ⟶ Y`:
its cap product is the pushforward of that of `c`. -/
theorem BivariantClass.CapVanishesOver.bivariantProperPushforward (f₁ : E ⟶ Y) [IsProper f₁]
    (f : Y ⟶ X) [LocallyOfFiniteType f] (hf₁ : f₁ ≫ sY = sE) (hf : f ≫ sX = sY)
    {c : BivariantClass C (gysinSystemOfInvertible C) sE sX (f₁ ≫ f)
      (comp_comp_structureMorphism_eq hf₁ hf) p}
    (hc : c.CapVanishesOver z) :
    (Stacks.Chow.bivariantProperPushforwardOfInvertible C sE sY sX f₁ f hf₁ hf p
      c).CapVanishesOver z := by
  intro T T₀ g _ e _ m hm sT₀ _ he k γ
  rw [bivariantProperPushforwardOfInvertible_cap, bivariantProperPushforwardCap_apply,
    hc g e m hm sT₀ he k γ, map_zero]

/-- **Capping to zero is preserved by transport along an equality of morphisms.** -/
theorem BivariantClass.CapVanishesOver.congrHom {G : GysinSystem C} {f f' : E ⟶ X}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] {hf : f ≫ sX = sE} (e : f = f')
    (hf' : f' ≫ sX = sE) {c : BivariantClass C G sE sX f hf p} (hc : c.CapVanishesOver z) :
    (c.congrHom e hf').CapVanishesOver z := by
  intro T T₀ g _ e' _ m hm sT₀ _ he k γ
  rw [BivariantClass.congrHom_cap, hc g e' m hm sT₀ he k γ, map_zero]

end Pushforward

/-! ### Stacks 0FB4 and Stacks 0FB6 -/

namespace LocalizedSituation

variable (S : LocalizedSituation.{u})

/-- **Stacks 0FB4, for `P_p(Z ⟶ X, E)`.** In Situation 0GUJ, when `E|_{X ∖ Z}` is zero,
`P_p(Z ⟶ X, E) ∩ i_* α = P_p(E|_Z) ∩ α` for `α ∈ CH_*(Z)`, and similarly after every base change:
on every test scheme `g : T ⟶ X`, the cap product of `P_p(Z ⟶ X, E)` with a class pushed forward
from `T ×_X Z` is the operation of `P_p(Li^*E) ∈ A^p(Z)` on it. This is the first formula of the
characterization of Stacks 0F9H. The Chern classes of `Li^*E` are defined by Stacks 0GUE (5), from
those of `E` (`Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_E`). -/
@[stacks 0FB4 "P_p(Z ⟶ X, E) ∩ i_* α = P_p(E|_Z) ∩ α, after every base change"]
theorem localizedPowerSum_cap_chowPush (h : S.IsZeroOnComplement) (p : ℕ)
    {T : Scheme.{u}} (g : T ⟶ S.X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup S.base (pullback.fst S.i g ≫ (S.i ≫ S.a)) k) :
    (S.localizedPowerSum h p).cap g k
        (chowPush S.base _ _ (pullback.snd S.i g) (pullbackSnd_comp_structureMorphism rfl g) k
          α) =
      (perfectPowerSumComponent S.base (S.i ≫ S.a)
          (hasDefinedChernClasses_of_derivedPullback S.i _ S.E S.hasDefinedChernClasses_E
            (Iso.refl _)) p).idRule S.base (S.i ≫ S.a)
        (gysinSystemOfInvertible S.base) (pullback.fst S.i g) k α := by
  refine BivariantClass.cap_chowPush_pullbackSnd_of_isRestriction _ ?_ g k α
  rw [properPushforwardChowCohomology_localizedPowerSum]
  have hres := TotalChowClass.isRestriction_res
    (perfectPowerSum S.base S.a S.hasDefinedChernClasses_E p) S.i rfl p
  rwa [res_perfectPowerSum_derivedPullback S.base S.a _ S.i rfl
    (hasDefinedChernClasses_of_derivedPullback S.i _ S.E S.hasDefinedChernClasses_E
      (Iso.refl _)) p] at hres

/-- **Stacks 0FB4, for `c_p(Z ⟶ X, E)`.** In Situation 0GUJ, when `E|_{X ∖ Z}` is finite locally
free of rank `< p` in degree `0`, `c_p(Z ⟶ X, E) ∩ i_* α = c_p(E|_Z) ∩ α` for `α ∈ CH_*(Z)`, and
similarly after every base change: on every test scheme `g : T ⟶ X`, the cap product of
`c_p(Z ⟶ X, E)` with a class pushed forward from `T ×_X Z` is the operation of
`c_p(Li^*E) ∈ A^p(Z)` on it. This is the first formula of the characterization of Stacks 0F9H.
The Chern classes of `Li^*E` are defined by Stacks 0GUE (5), from those of `E`
(`Stacks.Chow.LocalizedSituation.hasDefinedChernClasses_E`). -/
@[stacks 0FB4 "c_p(Z ⟶ X, E) ∩ i_* α = c_p(E|_Z) ∩ α, after every base change"]
theorem localizedChern_cap_chowPush (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    {T : Scheme.{u}} (g : T ⟶ S.X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup S.base (pullback.fst S.i g ≫ (S.i ≫ S.a)) k) :
    (S.localizedChern h).cap g k
        (chowPush S.base _ _ (pullback.snd S.i g) (pullbackSnd_comp_structureMorphism rfl g) k
          α) =
      (perfectChernClass S.base (S.i ≫ S.a)
          (hasDefinedChernClasses_of_derivedPullback S.i _ S.E S.hasDefinedChernClasses_E
            (Iso.refl _)) S.p).idRule S.base (S.i ≫ S.a)
        (gysinSystemOfInvertible S.base) (pullback.fst S.i g) k α := by
  refine BivariantClass.cap_chowPush_pullbackSnd_of_isRestriction _ ?_ g k α
  rw [properPushforwardChowCohomology_localizedChern]
  have hres := TotalChowClass.isRestriction_res
    (perfectChernClass S.base S.a S.hasDefinedChernClasses_E) S.i rfl S.p
  rwa [res_perfectChernClass_derivedPullback_of_comp_eq S.base S.a _ S.i rfl
    (hasDefinedChernClasses_of_derivedPullback S.i _ S.E S.hasDefinedChernClasses_E
      (Iso.refl _))] at hres

variable {S}

/-- **Stacks 0FB6, for `P_p(Z ⟶ X, E)`.** In Situation 0GUJ, when `E|_{X ∖ Z}` is zero: if
`α ∈ CH_k(X)` has support disjoint from `Z`, then `P_p(Z ⟶ X, E) ∩ α = 0`, and similarly after
every base change: the class caps to zero over every `z : V ⟶ X` whose image is disjoint from `Z`.
This is the second formula of the characterization of Stacks 0F9H. -/
@[stacks 0FB6 "P_p(Z ⟶ X, E) ∩ α = 0 for α supported away from Z, after every base change"]
theorem localizedPowerSum_capVanishesOver (h : S.IsZeroOnComplement) (p : ℕ)
    {V : Scheme.{u}} (z : V ⟶ S.X) (hz : Disjoint (Set.range z) (Set.range S.i)) :
    (S.localizedPowerSum h p).CapVanishesOver z :=
  BivariantClass.capVanishesOver_of_disjoint _ z hz

/-- **Stacks 0FB6, for `c_p(Z ⟶ X, E)`.** In Situation 0GUJ, when `E|_{X ∖ Z}` is finite locally
free of rank `< p` in degree `0`: if `α ∈ CH_k(X)` has support disjoint from `Z`, then
`c_p(Z ⟶ X, E) ∩ α = 0`, and similarly after every base change: the class caps to zero over every
`z : V ⟶ X` whose image is disjoint from `Z`. This is the second formula of the characterization
of Stacks 0F9H. -/
@[stacks 0FB6 "c_p(Z ⟶ X, E) ∩ α = 0 for α supported away from Z, after every base change"]
theorem localizedChern_capVanishesOver (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)
    {V : Scheme.{u}} (z : V ⟶ S.X) (hz : Disjoint (Set.range z) (Set.range S.i)) :
    (S.localizedChern h).CapVanishesOver z :=
  BivariantClass.capVanishesOver_of_disjoint _ z hz

end LocalizedSituation

end Stacks.Chow

end

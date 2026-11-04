module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.EnvelopeDescent
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange

/-!
# Injectivity of restriction on Chow cohomology along a universally injective flat morphism

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `π : P ⟶ X` be flat and locally of finite type of
relative dimension `d`. Call `π` *universally Chow injective* if for every cartesian square

      Q --g--> P
      |        |
      q        π
      v        v
      T --f--> X

over a scheme `T` locally of finite type over `S`, flat pullback `q^* : A_k(T) ⟶ A_{k+d}(Q)` is
injective in every degree. The result proved here is that restriction of Chow cohomology classes
along such a `π` is injective:

  `res : A^p(X) ⟶ A^p(P)`  is injective for every `p`.

The argument is the one of Stacks 02UL. Given `c ∈ A^p(X)` with `res(c) = 0`, the cap formula of
Stacks 0B7F (`Stacks.Chow.chowCohomologyRestriction_cap`) makes `c ∩ β` vanish on every test
scheme whose structure morphism to `X` factors through `π`. For an arbitrary test scheme
`h : T ⟶ X` one base-changes `π` to `q : T ×_X P ⟶ T`; the flat axiom of Stacks 0B76 identifies
`q^*(c ∩ α)` with `c ∩ q^*α`, which lies on a test scheme factoring through `π` and is therefore
zero, and injectivity of `q^*` gives `c ∩ α = 0`. Extensionality of bivariant classes finishes.

## Main definitions

* `Stacks.Chow.UniversallyChowInjective` — part (1) of Stacks 02UL as a property of `π`:
  injectivity of flat pullback along every base change of `π`.

## Main results

* `Stacks.Chow.cap_eq_zero_of_chowCohomologyRestriction_eq_zero` — a Chow cohomology class whose
  restriction along `π` vanishes caps to zero on every test scheme factoring through `π`.
* `Stacks.Chow.cap_eq_zero_of_universallyChowInjective` — such a class caps to zero on *every*
  test scheme, once `π` is universally Chow injective.
* `Stacks.Chow.chowCohomologyRestriction_injective` — part (2) of Stacks 02UL: restriction
  `A^p(X) ⟶ A^p(P)` along a universally Chow injective `π` is injective.

## Implementation notes

Universal Chow injectivity is an assumption here, not a theorem: no morphism is shown to have the
property, so no Stacks tag is claimed. The two statements about `π` that chapter 42 proves — that
a projective bundle projection, or a splitting tower, is universally Chow injective — are what
would turn this into the full tag, and neither is available in this repository.

The bivariant classes are those of `Stacks.Chow.BivariantClass`, so the Stacks 02S1 descent for
flat pullback occurs explicitly as a `FlatPullbackFactorsThroughRationalEquivalence` argument at
each use. Every such argument is discharged by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`, the general case of Stacks
02S1, and the morphism `q^*` the injectivity hypothesis speaks about is accordingly the
unconditional `Stacks.Chow.flatPullbackChowOfRelativeDimension`.

The comparison between the base change `T ×_X P ⟶ T` of `π` and the base change
`X ×_X (T ×_X P) ⟶ X ×_X T` appearing in the flat axiom of Stacks 0B76 uses only the isomorphism
case of Stacks 02RG, `Stacks.Chow.flatPullbackChow_chowPushforwardOfIso`: both horizontal legs of
the comparison square are the canonical isomorphisms `X ×_X T ≅ T`. The general case of
Stacks 02RG, which carries the unproved hypotheses of Stacks 02KH and 02O5, is not needed.

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Universal injectivity of flat pullback -/

/-- **Part (1) of Stacks 02UL** as a property of a morphism `π : P ⟶ X` flat and locally of
finite type of relative dimension `d`: for every cartesian square with right-hand leg `π` over a
scheme `T` locally of finite type over the base, flat pullback along the left-hand leg
`q : Q ⟶ T` is injective on Chow groups in every degree. -/
def UniversallyChowInjective (C : ChowSituation.{u}) {P X : Scheme.{u}} (π : P ⟶ X)
    [LocallyOfFiniteType π] [Flat π] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension π d) : Prop :=
  ∀ {T Q : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {f : T ⟶ X} {g : Q ⟶ P}
    (q : Q ⟶ T) [LocallyOfFiniteType q] [Flat q] (hsq : IsPullback g q π f) (k : ℤ),
    Function.Injective (flatPullbackChowOfRelativeDimension C (q ≫ sT) sT q rfl d
      (AlgebraicGeometry.RelativeDimension.of_isPullback hsq hd) k)

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X P : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (π : P ⟶ X) [LocallyOfFiniteType π] (p : ℤ)

/-! ### Vanishing of the cap products on test schemes factoring through `π` -/

/-- A Chow cohomology class whose restriction along `π : P ⟶ X` vanishes caps to zero on every
test scheme `m : W ⟶ X` that factors through `π`. -/
theorem cap_eq_zero_of_chowCohomologyRestriction_eq_zero (hgys : G.IsNaturalUnderBaseChangeIso)
    (c : chowCohomologyComponent C G sX p)
    (hzero : chowCohomologyRestriction C G sX π p hgys c = 0)
    {W : Scheme.{u}} (g : W ⟶ P) [LocallyOfFiniteType g] (m : W ⟶ X) [LocallyOfFiniteType m]
    (hm : m = g ≫ π) (k : ℤ) (α : chowGroup C (m ≫ sX) k) :
    c.cap m k α = 0 := by
  subst hm
  have hcongr : chowGroupCongr C (Category.assoc g π sX).symm k
      (chowGroupCongr C (Category.assoc g π sX) k α) = α := by
    rw [chowGroupCongr_chowGroupCongr]
    exact eq_of_heq (chowGroupCongr_heq C _ k α)
  have hkey := chowCohomologyRestriction_cap C G sX π p hgys c g k
    (chowGroupCongr C (Category.assoc g π sX) k α)
  rw [hzero, BivariantClass.zero_cap, map_zero, hcongr] at hkey
  exact chowPushforwardOfIso_injective C (pullback.fst (𝟙 X) (g ≫ π) ≫ sX) (g ≫ (π ≫ sX))
    (identityBaseChangeIso (g ≫ π)).hom
    (by rw [← Category.assoc]; exact identityBaseChangeIso_hom_comp_base C sX (g ≫ π)) (k - p)
    (hkey.symm.trans (map_zero _).symm)

/-! ### Vanishing of all cap products -/

/-- A Chow cohomology class capping to zero on every test scheme that factors through a
universally Chow injective `π : P ⟶ X` caps to zero on every test scheme at all.

For a test scheme `h : T ⟶ X` the flat axiom of Stacks 0B76 turns `q^*(c ∩ α)` into `c ∩ q^*α`,
where `q : T ×_X P ⟶ T` is the base change of `π`; the latter vanishes by hypothesis, and `q^*`
is injective. -/
theorem cap_eq_zero_of_universallyChowInjective [Flat π] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension π d) (hπ : UniversallyChowInjective C π d hd)
    (c : chowCohomologyComponent C G sX p)
    (hcap : ∀ {W : Scheme.{u}} (g : W ⟶ P) [LocallyOfFiniteType g] (m : W ⟶ X)
      [LocallyOfFiniteType m], m = g ≫ π → ∀ (j : ℤ) (β : chowGroup C (m ≫ sX) j),
      c.cap m j β = 0)
    {T : Scheme.{u}} (h : T ⟶ X) [LocallyOfFiniteType h] (k : ℤ)
    (α : chowGroup C (h ≫ sX) k) :
    c.cap h k α = 0 := by
  -- The base change `q : T ×_X P ⟶ T` of `π` along the test scheme `h`.
  have hbc : IsPullback (pullback.snd h π) (pullback.fst h π) π h :=
    (IsPullback.of_hasPullback h π).flip
  have hgft : LocallyOfFiniteType (pullback.snd h π) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback h π)
      (P := @LocallyOfFiniteType) inferInstance
  have hqft : LocallyOfFiniteType (pullback.fst h π) :=
    MorphismProperty.of_isPullback hbc (P := @LocallyOfFiniteType) inferInstance
  have hqflat : Flat (pullback.fst h π) :=
    MorphismProperty.of_isPullback hbc (P := @Flat) inferInstance
  have hq : AlgebraicGeometry.RelativeDimension (pullback.fst h π) d :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hbc hd
  -- Its base change along `X ×_X T ⟶ T`, which is what the flat axiom of Stacks 0B76 sees.
  have hsq : IsPullback (pullback.snd (𝟙 X) (pullback.fst h π ≫ h))
      (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) (pullback.fst h π)
      (pullback.snd (𝟙 X) h) :=
    isPullback_bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)
  have hjft : LocallyOfFiniteType (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) :=
    MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
  have hjflat : Flat (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) :=
    MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
  have hjdim : AlgebraicGeometry.RelativeDimension
      (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) d :=
    AlgebraicGeometry.RelativeDimension.of_isPullback hsq hq
  -- The two canonical isomorphisms `X ×_X (-) ≅ (-)` and their compatibility with the base.
  have hcond : ∀ {Z : Scheme.{u}} (t : Z ⟶ X),
      pullback.fst (𝟙 X) t = pullback.snd (𝟙 X) t ≫ t := fun t => by
    simpa using pullback.condition (f := 𝟙 X) (g := t)
  have hu : ∀ {Z : Scheme.{u}} (t : Z ⟶ X) (u : Z ⟶ C.S), t ≫ sX = u →
      pullback.snd (𝟙 X) t ≫ u = pullback.fst (𝟙 X) t ≫ sX := fun t u htu => by
    rw [hcond t, Category.assoc, htu]
  have hu₀ := hu h (h ≫ sX) rfl
  have hu₁ := hu (pullback.fst h π ≫ h) (pullback.fst h π ≫ (h ≫ sX)) (Category.assoc _ _ _)
  have hjbase : bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π) ≫
      (pullback.fst (𝟙 X) h ≫ sX) =
      pullback.fst (𝟙 X) (pullback.fst h π ≫ h) ≫ sX := by
    rw [← Category.assoc, bivariantBaseChangeMap_fst]
  -- Stacks 02S1 for the three flat pullbacks occurring below.
  have hfacq := flatPullbackFactorsThroughRationalEquivalence_general C
    ((pullback.fst h π ≫ h) ≫ sX) (h ≫ sX) (pullback.fst h π)
    (Category.assoc (pullback.fst h π) h sX).symm d hq k
  have hfacj := flatPullbackFactorsThroughRationalEquivalence_general C
    (pullback.fst (𝟙 X) (pullback.fst h π ≫ h) ≫ sX) (pullback.fst (𝟙 X) h ≫ sX)
    (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) hjbase d hjdim (k - p)
  have hfacv := flatPullbackFactorsThroughRationalEquivalence_general C
    (pullback.fst h π ≫ (h ≫ sX)) (h ≫ sX) (pullback.fst h π) rfl d hq (k - p)
  -- The cap product upstairs vanishes: its test scheme factors through `π`.
  have hupstairs : c.cap (pullback.fst h π ≫ h) (k + (d : ℤ))
      (flatPullbackChow C ((pullback.fst h π ≫ h) ≫ sX) (h ≫ sX) (pullback.fst h π)
        (Category.assoc (pullback.fst h π) h sX).symm d hq k hfacq α) = 0 :=
    hcap (pullback.snd h π) (pullback.fst h π ≫ h) pullback.condition (k + (d : ℤ)) _
  -- Hence so does the flat pullback of `c ∩ α` along the comparison morphism.
  have hzero : flatPullbackChow C (pullback.fst (𝟙 X) (pullback.fst h π ≫ h) ≫ sX)
      (pullback.fst (𝟙 X) h ≫ sX) (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π))
      hjbase d hjdim (k - p) hfacj (c.cap h k α) = 0 := by
    have hnat := c.flat_naturality h (pullback.fst h π) d hq
      (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) hsq
      (bivariantBaseChangeMap_fst (𝟙 X) h (pullback.fst h π)) k hjdim hfacq hfacj α
    have hz : HEq
        (0 : chowGroup C (pullback.fst (𝟙 X) (pullback.fst h π ≫ h) ≫ sX)
          (k + (d : ℤ) - p))
        (0 : chowGroup C (pullback.fst (𝟙 X) (pullback.fst h π ≫ h) ≫ sX)
          (k - p + (d : ℤ))) := by
      rw [show k + (d : ℤ) - p = k - p + (d : ℤ) by omega]
    exact eq_of_heq (hnat.symm.trans ((heq_of_eq hupstairs).trans hz))
  -- Stacks 02RG for two isomorphism legs transports that vanishing down to `q`.
  have h02RG := flatPullbackChow_chowPushforwardOfIso C (pullback.fst (𝟙 X) h ≫ sX)
    (pullback.fst (𝟙 X) (pullback.fst h π ≫ h) ≫ sX) (h ≫ sX)
    (pullback.fst h π ≫ (h ≫ sX)) (pullback.snd (𝟙 X) h) hu₀
    (pullback.snd (𝟙 X) (pullback.fst h π ≫ h)) hu₁
    (bivariantBaseChangeMap (𝟙 X) h (pullback.fst h π)) hjbase (pullback.fst h π) rfl
    hsq.w.symm d hjdim hq (k - p) hfacj hfacv (c.cap h k α)
  rw [hzero, map_zero] at h02RG
  -- Flat pullback along the base change of `π` is injective, by hypothesis.
  have hpush : chowPushforwardOfIso C (pullback.fst (𝟙 X) h ≫ sX) (h ≫ sX)
      (pullback.snd (𝟙 X) h) hu₀ (k - p) (c.cap h k α) = 0 :=
    hπ (h ≫ sX) (pullback.fst h π) hbc (k - p) (h02RG.trans (map_zero _).symm)
  exact chowPushforwardOfIso_injective C (pullback.fst (𝟙 X) h ≫ sX) (h ≫ sX)
    (pullback.snd (𝟙 X) h) hu₀ (k - p) (hpush.trans (map_zero _).symm)

/-! ### Injectivity of restriction on Chow cohomology -/

/-- **Part (2) of Stacks 02UL.** If flat pullback along `π : P ⟶ X` remains injective on Chow
groups after every base change, then restriction `A^p(X) ⟶ A^p(P)` of Chow cohomology classes
along `π` is injective in every degree.

Universal Chow injectivity is a hypothesis: nothing here proves that any particular `π` has
it. -/
theorem chowCohomologyRestriction_injective [Flat π] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension π d) (hπ : UniversallyChowInjective C π d hd)
    (hgys : G.IsNaturalUnderBaseChangeIso) :
    Function.Injective (chowCohomologyRestriction C G sX π p hgys) := by
  intro c₁ c₂ hres
  have hzero : chowCohomologyRestriction C G sX π p hgys (c₁ - c₂) = 0 := by
    rw [map_sub, hres, sub_self]
  apply sub_eq_zero.mp
  apply BivariantClass.ext
  intro W g hg k α
  rw [BivariantClass.zero_cap]
  exact cap_eq_zero_of_universallyChowInjective C G sX π p d hd hπ (c₁ - c₂)
    (cap_eq_zero_of_chowCohomologyRestriction_eq_zero C G sX π p hgys (c₁ - c₂) hzero) g k α

end Stacks.Chow

end

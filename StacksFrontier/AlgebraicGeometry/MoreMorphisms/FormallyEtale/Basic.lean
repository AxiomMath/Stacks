module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Etale.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleAffine
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleScheme
public import StacksFrontier.AlgebraicGeometry.Etale.FormallyEtaleSmoothUnramified
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Basic

/-!
# Formally étale morphisms of schemes

A morphism of schemes is formally étale, `AlgebraicGeometry.FormallyEtale`, when every morphism to
its source from the closed subscheme of a first-order thickening of affine schemes extends, over
the target, to the whole thickening in exactly one way. This file proves that the condition is
stable under composition, under arbitrary base change and under restriction to compatible open
subschemes.

## Main results

* `AlgebraicGeometry.FormallyEtale.comp`: a composition of formally étale morphisms is formally
  étale.
* `AlgebraicGeometry.FormallyEtale.pullback_snd`: a base change of a formally étale morphism is
  formally étale.
* `AlgebraicGeometry.FormallyEtale.resLE`: formal étaleness is preserved by restriction to
  compatible open subschemes.

## References

* [Stacks Project, Tag 02HH](https://stacks.math.columbia.edu/tag/02HH)
* [Stacks Project, Tag 02HI](https://stacks.math.columbia.edu/tag/02HI)
* [Stacks Project, Tag 02HJ](https://stacks.math.columbia.edu/tag/02HJ)
* [Stacks Project, Tag 02HK](https://stacks.math.columbia.edu/tag/02HK)
* [Stacks Project, Tag 02HL](https://stacks.math.columbia.edu/tag/02HL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A composition of formally étale morphisms is formally étale. -/
@[stacks 02HI]
theorem FormallyEtale.comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (hf : FormallyEtale f) (hg : FormallyEtale g) :
    FormallyEtale (f ≫ g) := by
  intro T T' hT hT' i hi p k hk
  obtain ⟨v, ⟨hv₁, hv₂⟩, huv⟩ := hg i hi p (k ≫ f) (by simpa [Category.assoc] using hk)
  obtain ⟨h, ⟨hh₁, hh₂⟩, huh⟩ := hf i hi v k hv₁.symm
  refine ⟨h, ⟨hh₁, by simpa only [← hh₂, Category.assoc] using hv₂⟩, fun h' ⟨hh'₁, hh'₂⟩ =>
    huh h' ⟨hh'₁, huv (h' ≫ f) ⟨by simp only [← Category.assoc, hh'₁],
      by simpa only [Category.assoc] using hh'₂⟩⟩⟩

/-- A base change of a formally étale morphism is formally étale. -/
@[stacks 02HJ]
theorem FormallyEtale.pullback_snd {X S S' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (hf : FormallyEtale f) :
    FormallyEtale (pullback.snd f g) := by
  intro T T' _ _ i hi p q hh
  obtain ⟨h₁, ⟨h₁i, h₁f⟩, h₁uniq⟩ :=
    hf i hi (p ≫ g) (q ≫ pullback.fst f g) (by
      simpa only [Category.assoc, pullback.condition] using
        eq_whisker hh g)
  refine ⟨pullback.lift h₁ p h₁f, ⟨pullback.hom_ext ?_ ?_, pullback.lift_snd ..⟩, ?_⟩
  · simpa only [Category.assoc, pullback.lift_fst] using h₁i
  · simpa only [Category.assoc, pullback.lift_snd] using hh.symm
  · intro y hy; apply pullback.hom_ext
    · rw [pullback.lift_fst]; apply h₁uniq
      constructor
      · simpa only [Category.assoc] using eq_whisker hy.1 (pullback.fst f g)
      · simpa only [Category.assoc, pullback.condition] using
          eq_whisker hy.2 g
    · simpa only [pullback.lift_snd] using hy.2

/-- Formal étaleness is preserved when a morphism is restricted to compatible open subschemes of
its source and target. -/
@[stacks 02HK]
lemma FormallyEtale.resLE {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    (hf : FormallyEtale f) :
    FormallyEtale (f.resLE V U hUV) := by
  intro T T' _ _ i hi p g hg
  let gX : T ⟶ X := g ≫ (U.ι : U.toScheme ⟶ X)
  let pS : T' ⟶ S := p ≫ (V.ι : V.toScheme ⟶ S)
  have hcomm : gX ≫ f = i ≫ pS := by
    simpa [gX, pS, Category.assoc, Scheme.Hom.resLE_comp_ι] using eq_whisker hg V.ι
  obtain ⟨h, hh, huniq⟩ := hf i hi pS gX hcomm
  have hrange : Set.range h ⊆ Set.range U.ι := by
    rintro y ⟨y', rfl⟩
    obtain ⟨x, hx⟩ := hi.isThickening.2 y'
    refine ⟨g x, ?_⟩
    have heval := congrArg (fun k : T ⟶ X => k x) hh.1
    rw [← hx]; simpa [gX, Scheme.Hom.comp_apply] using heval.symm
  let hU : T' ⟶ U.toScheme := IsOpenImmersion.lift U.ι h hrange
  refine ⟨hU, ⟨?_, ?_⟩, ?_⟩
  · apply (cancel_mono U.ι).1
    simpa [hU, gX, Category.assoc, IsOpenImmersion.lift_fac] using hh.1
  · apply (cancel_mono V.ι).1
    simpa [hU, pS, Category.assoc, Scheme.Hom.resLE_comp_ι, IsOpenImmersion.lift_fac] using hh.2
  · intro k hk
    apply (cancel_mono U.ι).1
    exact (huniq (k ≫ U.ι) ⟨by
      simpa [gX, Category.assoc] using eq_whisker hk.1 U.ι, by
      simpa [pS, Category.assoc, Scheme.Hom.resLE_comp_ι] using
        eq_whisker hk.2 V.ι⟩).trans (IsOpenImmersion.lift_fac U.ι h hrange).symm



/-! ### Formal étaleness as formal smoothness and formal unramifiedness

`AlgebraicGeometry.formallyEtale_iff_formallySmooth_and_formallyUnramified`: a morphism of schemes
is formally étale if and only if it is formally smooth and formally unramified. -/

add_to_stacks 061G "the same equivalence for a morphism of schemes"
  AlgebraicGeometry.formallyEtale_iff_formallySmooth_and_formallyUnramified

end AlgebraicGeometry

end

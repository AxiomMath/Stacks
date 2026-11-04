module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardInvertible

/-!
# Naturality of the Gysin operation of a Gysin system under proper pushforward

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `G` be a
`Stacks.Chow.GysinSystem` for it, so that `G.onChow` is the Gysin map
`i^* : A_{k+1}(B) ⟶ A_k(Z(s))` of a global section `s` of an invertible module `L` on `B`. Let
`u : A ⟶ B` be proper over `S`, put `L' = u^*L` and `s' = u^*s`, and let `j : Z(s') ⟶ Z(s)` be a
morphism filling the square of [Stacks, Tag 0B6Y]

  `Z(s') --i'--> A`
  `|j             |u`
  `Z(s)  --i-->   B`

The identity of [Stacks, Tag 02TA] for `G` is `i^* u_* α = j_* (i')^* α` in `A_k(Z(s))`, for
classes `α ∈ A_{k+1}(A)`. This file states it as a predicate on `G` and proves it for the Gysin
system of the first Chern class rule of an invertible module.

## Main definitions

* `Stacks.Chow.GysinSystem.IsNaturalUnderProperPushforward` — the identity of [Stacks, Tag 02TA]
  for the Gysin operation of a Gysin system, along a general proper morphism over the base.

## Main results

* `Stacks.Chow.gysinSystemOfInvertible_isNaturalUnderProperPushforward` — the Gysin system of the
  first Chern class rule of an invertible module satisfies that naturality.
* `Stacks.Chow.properChowPushforward_congr_hom` — proper pushforward on Chow groups along equal
  morphisms agrees.

## References

* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry hiding zeroScheme
open CategoryTheory

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### The square of Remark 0B6Y over the base -/

/-- A morphism of zero schemes filling the square of [Stacks, Tag 0B6Y] commutes over the base
scheme of the Chow situation: if `j ≫ i = i' ≫ u` and `u ≫ pB = pA`, then
`j ≫ (i ≫ pB) = i' ≫ pA`. -/
theorem zeroSchemeSquare_comp_structureMorphism (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (pA : A ⟶ C.S) (pB : B ⟶ C.S) (u : A ⟶ B) (hu : u ≫ pB = pA) (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (j : (pullbackZeroScheme u L s).subscheme ⟶ (zeroScheme B L s).subscheme)
    (hj : j ≫ (zeroScheme B L s).subschemeι = (pullbackZeroScheme u L s).subschemeι ≫ u) :
    j ≫ ((zeroScheme B L s).subschemeι ≫ pB) = (pullbackZeroScheme u L s).subschemeι ≫ pA := by
  rw [← Category.assoc, hj, Category.assoc, hu]

/-! ### Proper pushforward on Chow groups along equal morphisms -/

/-- Proper pushforward on Chow groups along two equal morphisms `g = g'` over the base agrees,
for any choice of the properness instances and of the witnesses `hfac`, `hfac'` of
[Stacks, Tag 02S2]. -/
theorem properChowPushforward_congr_hom (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {g g' : A ⟶ B} [IsProper g] [IsProper g'] (h : g = g') (hg : g ≫ sB = sA)
    (hg' : g' ≫ sB = sA) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB g hg k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA sB g' hg' k)
    (α : chowGroup C sA k) :
    properChowPushforward C sA sB g hg k hfac α =
      properChowPushforward C sA sB g' hg' k hfac' α := by
  subst h
  rfl

/-! ### Naturality of a Gysin system under proper pushforward -/

/-- **Naturality of the Gysin operation of a Gysin system under proper pushforward**
([Stacks, Tag 02TA]). The Gysin operation of `G` at `B` composed with proper pushforward along a
morphism `u : A ⟶ B` proper over the base agrees with pushforward along a morphism
`j : Z(u^*s) ⟶ Z(s)` composed with the Gysin operation of `G` at `A` for the pulled-back module and
section: `i^* u_* α = j_* (i')^* α` in `A_k(Z(s))`.

The predicate quantifies over the proper morphism `j` subject to the square
`j ≫ i = i' ≫ u` of [Stacks, Tag 0B6Y], and over the two witnesses `hfacu`, `hfacj` of
[Stacks, Tag 02S2] that proper pushforward on Chow groups along `u` and `j` takes. -/
def GysinSystem.IsNaturalUnderProperPushforward {C : ChowSituation.{u}} (G : GysinSystem C) :
    Prop :=
  ∀ {A B : Scheme.{u}} (pA : A ⟶ C.S) [LocallyOfFiniteType pA] (pB : B ⟶ C.S)
    [LocallyOfFiniteType pB] (u : A ⟶ B) [IsProper u] (hu : u ≫ pB = pA) (L : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (k : ℤ)
    (j : (pullbackZeroScheme u L s).subscheme ⟶ (zeroScheme B L s).subscheme) [IsProper j]
    (hj : j ≫ (zeroScheme B L s).subschemeι = (pullbackZeroScheme u L s).subschemeι ≫ u)
    (hfacu : ProperPushforwardFactorsThroughRationalEquivalence C pA pB u hu (k + 1))
    (hfacj : ProperPushforwardFactorsThroughRationalEquivalence C
      ((pullbackZeroScheme u L s).subschemeι ≫ pA) ((zeroScheme B L s).subschemeι ≫ pB) j
      (zeroSchemeSquare_comp_structureMorphism C pA pB u hu L s j hj) k)
    (α : chowGroup C pA (k + 1)),
    G.onChow pB L s k (properChowPushforward C pA pB u hu (k + 1) hfacu α) =
      properChowPushforward C ((pullbackZeroScheme u L s).subschemeι ≫ pA)
        ((zeroScheme B L s).subschemeι ≫ pB) j
        (zeroSchemeSquare_comp_structureMorphism C pA pB u hu L s j hj) k hfacj
        (G.onChow pA ((Scheme.Modules.pullback u).obj L)
          (AlgebraicGeometry.pullbackGlobalSections u L s) k α)

/-! ### The Gysin system of the first Chern class rule satisfies it -/

/-- The Gysin system of the first Chern class rule of an invertible module is natural under
pushforward along an arbitrary proper morphism over the base. -/
@[stacks 02TA "the naturality of the Gysin operation of a Gysin system under pushforward along \
a general proper morphism"]
theorem gysinSystemOfInvertible_isNaturalUnderProperPushforward (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).IsNaturalUnderProperPushforward := by
  intro A B pA _ pB _ u _ hu L _ s k j _ hj hfacu hfacj α
  induction α using QuotientAddGroup.induction_on with
  | H α =>
    show gysinHomomorphismOfInvertible C pB k L s
        (properPushforward C pA pB u hu (k + 1) α) =
      properChowPushforward C ((pullbackZeroScheme u L s).subschemeι ≫ pA)
        ((zeroScheme B L s).subschemeι ≫ pB) j
        (zeroSchemeSquare_comp_structureMorphism C pA pB u hu L s j hj) k hfacj
        (gysinHomomorphismOfInvertible C pA k ((Scheme.Modules.pullback u).obj L)
          (AlgebraicGeometry.pullbackGlobalSections u L s) α)
    rw [gysinHomomorphismOfInvertible_properPushforward_of_gysinCompatible u L s C pB pA k hu α]
    exact properChowPushforward_congr_hom C _ _ (eq_zeroSchemePullbackHom u L s j hj).symm _ _ k
      _ _ _

end Stacks.Chow

end

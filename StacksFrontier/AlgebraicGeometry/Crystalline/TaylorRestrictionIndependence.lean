module

public import StacksFrontier.AlgebraicGeometry.Crystalline.PointedTaylorComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormulaMonomials

/-!
# The restriction maps of [Stacks, Tag 07JH] do not depend on the chosen pointing

The proof of [Stacks, Proposition 60.17.4, Tag 07JH] sends an affine object `(U, T, δ)` of
`Cris(X/S)`, with `T = Spec(B)`, to `ℱ_T = M ⊗_{D,f} B` for a chosen divided power map
`f : D → B`, and for a morphism `a : (U', T', δ') → (U, T, δ)` it takes the restriction map to be
the canonical `a^*ℱ_T → ℱ_{T'}` obtained from the choice `f' = f ∘ a`.  It then says:

> We omit the verification that this map is independent of the choice of `f`.

This module performs that verification.  Its content is that the comparison `c_{f,g}` of two
pointings is carried by the restriction maps to the comparison `c_{f ∘ a, g ∘ a}` of the two
pointings pushed along `a`, so the identifications of `ℱ_T` coming from two choices of `f` match
up with the identifications of `ℱ_{T'}`.

## This is an algebraic identity and not a convergence statement

The verification looks as though it should need the `p`-adic convergence of the Taylor series —
the series is where the choice of `f` is compared at all — and so the nilpotence of `p` and the
quasi-nilpotence condition (07JE).  It does not.  Two facts carry it, and neither is topological:

* `ξ_i` is **natural in the target**: the differences of the pushed pointings are the images of
  the differences, `a(f(x_i) - g(x_i)) = (f ∘ a)(x_i) - (g ∘ a)(x_i)`, which is
  `Crystalline.pointedDiff_comp` and is additivity of `a`;
* the divided power coefficients are natural too: `a(ξ^{[K]}) = a(ξ)^{[K]}`, which is
  `Crystalline.map_taylorMonomial` — the defining property of a divided power homomorphism, taken
  over the finitely many factors of `Crystalline.taylorMonomial`.

So the square `Crystalline.pointedRestriction_pointedComparison` is proved with **no hypotheses at
all**: it holds for any semilinear datum, convergent or not, because the restriction map is the
base change of a ring map and the comparison is the base change of a semilinear map, and the two
base changes commute.  Where the series does enter is only in
`Crystalline.hasPointedTaylorSum_pointedRestriction`, which identifies the pushed datum as the
Taylor comparison *of the pushed difference family* — and there the hypotheses are the source's
own (`p^N = 0` in both thickenings, [Stacks, Tag 07HM]) together with the finiteness the
quasi-nilpotence condition supplies, in exactly the form
`Crystalline.hasPointedTaylorSum_eq_sum` already consumes.

## Main definitions

* `Crystalline.pushPoint` — a pointing pushed along a morphism of thickenings, as a morphism of
  the pointed site.  This is the source's `f' = f ∘ a`.
* `Crystalline.pushedPointedComparisonMap` — the semilinear datum of `c_{f,g}` pushed along such
  a morphism.

## Main results

* `Crystalline.pointedDiff_comp` — `ξ_{f ∘ a, g ∘ a} = a(ξ_{f, g})`.
* `Crystalline.taylorMonomial_pointedDiff_comp` — `ξ_{f ∘ a, g ∘ a}^{[K]} = a(ξ_{f,g}^{[K]})`.
* `Crystalline.pointedRestriction_pointedComparison` — **the square: the restriction maps carry
  `c_{f,g}` to `c_{f ∘ a, g ∘ a}`**, with no hypotheses.
* `Crystalline.hasPointedTaylorSum_pointedRestriction` — **the pushed datum is the Taylor
  comparison of the pushed differences**, so the `c_{f ∘ a, g ∘ a}` of the square is the source's
  own comparison over `T'` and not merely some map.
* `Crystalline.pointedRestriction_pointedComparison_self` — the restriction map commutes with
  `c_{f,f} = 1`, the degenerate case, which is the statement that one choice of `f` is carried to
  the corresponding choice over `T'`.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
The tag is an equivalence of categories; this module is one commuting square of modules.  The tag
is registered, for the functor of [Stacks, Lemma 60.17.3, Tag 07JG] that this chapter carries that
lemma on, by `Crystalline.taylorCrystalsToPairs_isEquivalence` of
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorCrystalEquivalence.lean`, whose route does not
descend along the choice of `f` at all; this module closes the step the source's own route needs
and omits.

What is **not** closed by it are the source's other two omissions — that the resulting assignment
extends from the affine objects to all of `Cris(X/S)`, and that it is a functor quasi-inverse to
the one of Tag 07JG.  Neither is a statement about one square, and the second needs the passage
from the pointed site to `Cris(X/S)` recorded in the "What is and is not proved" section of
`StacksFrontier/AlgebraicGeometry/Crystalline/PairToCrystal.lean`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u uI v w

namespace Crystalline

/-! ### A pointing pushed along a morphism of thickenings -/

section Push

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X X' : DividedPowerThickening.{u, v, w} S}

/-- **A pointing pushed along a morphism `a : T → T'` of thickenings**, as a morphism of the
pointed crystalline site: the object `X` pointed by `f` maps to the object `X'` pointed by
`f ∘ a`.  This is the source's "choosing `f' = f ∘ a`", and it is a morphism of pointed objects by
construction, the triangle being an identity. -/
abbrev pushPoint (f : Dt ⟶ X) (u : X ⟶ X') : pointedOfHom f ⟶ pointedOfHom (f ≫ u) :=
  Under.homMk u

/-- The ring homomorphism underlying a pushed pointing is the one of the morphism pushed along. -/
@[simp] theorem pointedHomRingHom_pushPoint (f : Dt ⟶ X) (u : X ⟶ X') (b : X.ring.carrier) :
    pointedHomRingHom (pushPoint f u) b = u.hom b := rfl

variable {ι : Type uI}

/-- **The difference family is natural in the thickening**: `ξ_{f ∘ a, g ∘ a} = a(ξ_{f,g})`.

This is additivity of `a` and nothing else, and it is the first of the two identities that make
the choice of `f` immaterial for the restriction maps. -/
theorem pointedDiff_comp (f g : Dt ⟶ X) (u : X ⟶ X') (x : ι → Dt.ring.carrier) (i : ι) :
    pointedDiff (f ≫ u) (g ≫ u) x i = u.hom (pointedDiff f g x i) := by
  change _ = u.hom.toRingHom (pointedDiff f g x i)
  simp only [pointedDiff_apply, map_sub]
  rfl

/-- **The difference family is natural in the thickening**, as an identity of families. -/
theorem pointedDiff_comp_eq (f g : Dt ⟶ X) (u : X ⟶ X') (x : ι → Dt.ring.carrier) :
    pointedDiff (f ≫ u) (g ≫ u) x = fun i ↦ u.hom (pointedDiff f g x i) :=
  funext fun i ↦ pointedDiff_comp f g u x i

/-- **The divided power coefficients of the Taylor series are natural in the thickening**:
`ξ_{f ∘ a, g ∘ a}^{[K]} = a(ξ_{f,g}^{[K]})`.

This is `Crystalline.map_taylorMonomial`, the defining property of a divided power homomorphism
taken over the finitely many factors of the monomial, applied to the previous identity.  Its
hypothesis is that the differences lie in the divided power ideal, which is
`Crystalline.pointedDiff_mem` — the source's "the image of `f - g` is contained in `J_B`".

No convergence enters: this is an identity between two elements of `B'`, for one multi-index. -/
theorem taylorMonomial_pointedDiff_comp (hDt : Function.Surjective Dt.toQuotient)
    (f g : Dt ⟶ X) (u : X ⟶ X') (x : ι → Dt.ring.carrier) (K : ι →₀ ℕ) :
    taylorMonomial X'.ring (pointedDiff (f ≫ u) (g ≫ u) x) K =
      u.hom (taylorMonomial X.ring (pointedDiff f g x) K) := by
  classical
  have h := map_taylorMonomial
    (f := (u.hom : DividedPowers.DPMorphism X.ring.dividedPowers X'.ring.dividedPowers))
    (fun i ↦ pointedDiff_mem hDt f g x i) K
  rw [pointedDiff_comp_eq f g u x]
  exact h.symm

end Push

/-! ### The square: the restriction maps carry `c_{f,g}` to `c_{f ∘ a, g ∘ a}` -/

section Square

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X X' : DividedPowerThickening.{u, v, w} S} (M : Type w) [AddCommGroup M]
  [Module Dt.ring.carrier M]

/-- **The semilinear datum of `c_{f,g}` pushed along a morphism `a : T → T'` of thickenings.**
Composing with the restriction map turns an `f`-semilinear map into an `f ∘ a`-semilinear one,
because the restriction map is `a`-semilinear by `Crystalline.pointedRestriction_smul`.

This is the datum of the comparison `c_{f ∘ a, g ∘ a}` that the square below produces; that it is
the Taylor comparison of the pushed difference family, and so the source's own comparison over
`T'`, is `Crystalline.hasPointedTaylorSum_pointedRestriction`. -/
noncomputable def pushedPointedComparisonMap (f g : Dt ⟶ X) (u : X ⟶ X')
    (T : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g)) :
    M →ₛₗ[pointRingHom (pointedOfHom (f ≫ u))] pointedSections M (pointedOfHom (g ≫ u)) where
  toFun m := pointedRestriction M (pushPoint g u) (T m)
  map_add' m m' := by
    change pointedRestriction M (pushPoint g u) (T (m + m')) = _
    rw [map_add, map_add]
  map_smul' a m := by
    change pointedRestriction M (pushPoint g u) (T (a • m)) = _
    rw [map_smulₛₗ, pointedRestriction_smul]
    rfl

/-- The pushed comparison map sends `m` to the restriction along `u` of `T m`. -/
@[simp] theorem pushedPointedComparisonMap_apply (f g : Dt ⟶ X) (u : X ⟶ X')
    (T : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g)) (m : M) :
    pushedPointedComparisonMap M f g u T m =
      pointedRestriction M (pushPoint g u) (T m) := rfl

/-- **The verification the source omits: the restriction maps carry `c_{f,g}` to
`c_{f ∘ a, g ∘ a}`.**

For two pointings `f, g` of an object `T` of the pointed crystalline site and a morphism
`a : T → T'` of thickenings, the square

```
M ⊗_{D,f} B   --- c_{f,g} --->   M ⊗_{D,g} B
     |                                |
     a                                a
     v                                v
M ⊗_{D,f∘a} B' - c_{f∘a,g∘a} -> M ⊗_{D,g∘a} B'
```

commutes, the bottom map being the comparison of the pushed datum
`Crystalline.pushedPointedComparisonMap`.  This is the statement that the identification of
`ℱ_{T'}` produced from the choice `f` agrees with the one produced from the choice `g`, which is
what "independent of the choice of `f`" means for the restriction maps.

**There are no hypotheses.**  Both composites are additive maps out of a tensor product, so it is
enough to compare them on a generator `b ⊗ m`, where both give `a(b) · a(T m)`: the comparison is
the base change of the semilinear map along the first pointing
(`Crystalline.semilinearBaseChange_tmul`) and the restriction map is the base change of `a`
(`Crystalline.pointedRestriction_tmul`), and the two base changes commute because the restriction
map is `a`-semilinear.  Neither the divided power structure nor the convergence of the Taylor
series is used; they enter only in identifying the bottom map with the source's comparison over
`T'`, which is `Crystalline.hasPointedTaylorSum_pointedRestriction`. -/
theorem pointedRestriction_pointedComparison (f g : Dt ⟶ X) (u : X ⟶ X')
    (T : M →ₛₗ[pointRingHom (pointedOfHom f)] pointedSections M (pointedOfHom g))
    (z : pointedSections M (pointedOfHom f)) :
    pointedRestriction M (pushPoint g u) (pointedComparison M f g T z) =
      pointedComparison M (f ≫ u) (g ≫ u) (pushedPointedComparisonMap M f g u T)
        (pointedRestriction M (pushPoint f u) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul b m =>
      rw [pointedRestriction_tmul, pointedComparison, pointedComparison,
        semilinearBaseChange_tmul, semilinearBaseChange_tmul, pointedRestriction_smul,
        pushedPointedComparisonMap_apply, pointedScalarsMap_val]
      rfl
  | add z z' hz hz' => rw [map_add, map_add, map_add, map_add, hz, hz']

/-- **The restriction map commutes with `c_{f,f} = 1`.**  This is the square at one pointing,
where `Crystalline.pointedComparison_self` identifies the comparison with the identity: the
restriction map along `a` of the tautological identification of `ℱ_T` is the tautological
identification of `ℱ_{T'}`.

It is the degenerate case of the independence verification, and the one the source states
separately as "It is also true that `c_{f,f} = 1`". -/
theorem pointedRestriction_pointedComparison_self (f : Dt ⟶ X) (u : X ⟶ X')
    (z : pointedSections M (pointedOfHom f)) :
    pointedRestriction M (pushPoint f u)
        (pointedComparison M f f (pointedUnitComparison M f) z) =
      pointedComparison M (f ≫ u) (f ≫ u) (pointedUnitComparison M (f ≫ u))
        (pointedRestriction M (pushPoint f u) z) := by
  rw [pointedComparison_self, pointedComparison_self, LinearMap.id_apply, LinearMap.id_apply]

end Square

/-! ### The pushed datum carries the Taylor series of the pushed differences -/

section Series

variable {S : AffineCrystallineSituation.{u, v}} {Dt : DividedPowerThickening.{u, v, w} S}
  {X X' : DividedPowerThickening.{u, v, w} S} (M : Type w) [AddCommGroup M]
  [Module Dt.ring.carrier M] (p : ℕ) {ι : Type uI} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The Taylor sum pushes forward along a morphism of thickenings.**

If the series `∑_K ξ_{f,g}^{[K]} ⊗ θ_K(m)` converges to `t` in `M ⊗_{D,g} B`, then the series of
the pushed differences `ξ_{f ∘ a, g ∘ a}` converges, in `M ⊗_{D,g∘a} B'`, to the restriction of
`t`.  So the pushed datum `Crystalline.pushedPointedComparisonMap` is the Taylor comparison of the
pushed family, and the bottom map of `Crystalline.pointedRestriction_pointedComparison` is the
source's own `c_{f∘a, g∘a}` over `T'` rather than some map that happens to make a square commute.

The proof is the reindexing of the sum and nothing more: by
`Crystalline.hasPointedTaylorSum_eq_sum` the sum is the finite sum over `s` of its surviving
terms, the restriction map takes that term by term to the finite sum of the pushed terms by
`Crystalline.taylorMonomial_pointedDiff_comp`, and `Crystalline.hasPointedTaylorSum_sum` reads the
result back as a convergent series over `T'`.

The hypotheses are the source's own.  `hpB` and `hpB'` are nilpotence of `p` in the two
thickenings, which [Stacks, Tag 07HM] requires of every object of `Cris(X/S)` — taken at a common
exponent, which costs nothing since `p^N = 0` gives `p^{N'} = 0` for every `N' ≥ N`.  `hvanish` is
the source's "the sum is finite!", the form in which the quasi-nilpotence condition (07JE) of
[Stacks, Tag 07JE] is consumed by `Crystalline.hasPointedTaylorSum_eq_sum`; it is a condition on
`θ_K(m)` alone and so is the same condition over `T` and over `T'`.  `hDt` is surjectivity of
`C → D/J_D`, which holds because the fixed object is one of `Cris(C/A)`. -/
theorem hasPointedTaylorSum_pointedRestriction (hDt : Function.Surjective Dt.toQuotient)
    (f g : Dt ⟶ X) (u : X ⟶ X') (x : ι → Dt.ring.carrier) {N : ℕ}
    (hpB : ((p : X.ring.carrier)) ^ N = 0) (hpB' : ((p : X'.ring.carrier)) ^ N = 0)
    (m : M) (s : Finset (ι →₀ ℕ))
    (hvanish : ∀ K ∉ s, thetaPow K m ∈ pPowSmul p Dt.ring.carrier M N)
    {t : pointedSections M (pointedOfHom g)}
    (ht : HasPointedTaylorSum M p thetaPow g (pointedDiff f g x) m t) :
    HasPointedTaylorSum M p thetaPow (g ≫ u) (pointedDiff (f ≫ u) (g ≫ u) x) m
      (pointedRestriction M (pushPoint g u) t) := by
  have hsum := hasPointedTaylorSum_sum M p thetaPow (g ≫ u)
    (pointedDiff (f ≫ u) (g ≫ u) x) hpB' m s hvanish
  have heq : pointedRestriction M (pushPoint g u) t =
      ∑ K ∈ s, TwistedScalars.mk (pointRingHom (pointedOfHom (g ≫ u)))
        (taylorMonomial X'.ring (pointedDiff (f ≫ u) (g ≫ u) x) K)
          ⊗ₜ[Dt.ring.carrier] thetaPow K m := by
    rw [hasPointedTaylorSum_eq_sum M p thetaPow g (pointedDiff f g x) hpB m s hvanish ht,
      map_sum]
    refine Finset.sum_congr rfl fun K _ ↦ ?_
    rw [pointedRestriction_tmul, taylorMonomial_pointedDiff_comp hDt f g u x K]
    rfl
  rw [heq]
  exact hsum

end Series

end Crystalline

end

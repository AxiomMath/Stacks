module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation

/-!
# Flat pullback and the Chern class cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X ⟶ Y` be a flat
morphism of relative dimension `d` between schemes locally of finite type over `S`, and let `ℰ`
be a finite locally free `O_Y`-module of rank `r`. Then

  `f^*(c_j(ℰ) ∩ α) = c_j(f^*ℰ) ∩ f^*α`

for every `k`-cycle `α` on `Y`.

The projective bundles `π_X : P_X ⟶ X` and `π : P ⟶ Y`, the flat morphism `f' : P_X ⟶ P` of
relative dimension `d` and the first Chern class cap operators of the two twists are parameters.
The statements take as hypotheses the compatibility
`Stacks.Chow.ChernTermsCompatibleWithFlatPullback` of flat pullback along `f'` with the summands
`c₁(O_P(1))^i ∩ π^*(-)` of the projective-bundle relation, and, for the uniqueness, the
injectivity `Stacks.Chow.ProjectiveBundleRelationInjective` over `X`.

## Main definitions

* `Stacks.Chow.ChernTermsCompatibleWithFlatPullback`: flat pullback along `f'` carries each
  summand of the relation over `Y` to the corresponding summand over `X`.
* `Stacks.Chow.flatPullbackChernFamily`: the flat pullback of a family of Chow classes, read in
  the degrees of a family based at `k + d`.

## Main results

* `Stacks.Chow.flatPullbackChow_chowGroupCast`: flat pullback commutes with transport along an
  equality of degrees.
* `Stacks.Chow.flatPullback_projectiveBundleChernRelation`: the flat pullback of a family
  satisfying the relation over `Y` satisfies the relation over `X`.
* `Stacks.Chow.flatPullback_isChernCapFamily`: the flat pullback of a characterizing family is a
  characterizing family of the flat pullback of the class.
* `Stacks.Chow.isChernCapFamily_flatPullback`: flat pullback commutes with the Chern class cap
  products.

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Flat pullback and transport of degrees -/

/-- Flat pullback on Chow groups commutes with transport along an equality of degrees. -/
theorem flatPullbackChow_chowGroupCast (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) {k l : ℤ} (h : k = l)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf d hd k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf d hd l)
    (x : chowGroup C sY k) :
    chowGroupCast C sX (show k + (d : ℤ) = l + (d : ℤ) from by rw [h])
        (flatPullbackChow C sX sY f hf d hd k hfac x) =
      flatPullbackChow C sX sY f hf d hd l hfac' (chowGroupCast C sY h x) := by
  subst h; rfl

/-! ### The two bundles and the compatibility of their relations -/

variable (C : ChowSituation.{u}) {X Y PX PY : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sPX : PX ⟶ C.S) [LocallyOfFiniteType sPX] (sPY : PY ⟶ C.S) [LocallyOfFiniteType sPY]
  (πX : PX ⟶ X) [LocallyOfFiniteType πX] [Flat πX] (hsPX : πX ≫ sX = sPX)
  (πY : PY ⟶ Y) [LocallyOfFiniteType πY] [Flat πY] (hsPY : πY ≫ sY = sPY)
  (r : ℕ) (hπX : AlgebraicGeometry.RelativeDimension πX (r - 1))
  (hπY : AlgebraicGeometry.RelativeDimension πY (r - 1))
  (hfacX : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPX sX πX hsPX (r - 1) hπX k)
  (hfacY : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPY sY πY hsPY (r - 1) hπY k)
  (twistX : ChernCapOperator C sPX) (twistY : ChernCapOperator C sPY)
  (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (d : ℕ)
  (hd : AlgebraicGeometry.RelativeDimension f d)
  (hfacf : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf d hd k)
  (f' : PX ⟶ PY) [LocallyOfFiniteType f'] [Flat f'] (hf' : f' ≫ sPY = sPX)
  (hd' : AlgebraicGeometry.RelativeDimension f' d)
  (hfacf' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPX sPY f' hf' d hd' k)

/-- Flat pullback along `f' : P_X ⟶ P` carries the `i`-th summand `c₁(O_P(1))^i ∩ π^*(-)` of the
relation over `Y` to the `i`-th summand `c₁(O_{P_X}(1))^i ∩ π_X^*(-)` of the relation over `X`,
precomposed with flat pullback along `f`. -/
def ChernTermsCompatibleWithFlatPullback : Prop :=
  ∀ (k : ℤ) (i : ℕ) (hi : i ≤ r) (x : chowGroup C sY (k - ((r - i : ℕ) : ℤ))),
    flatPullbackChow C sPX sPY f' hf' d hd' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (hfacf' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))
        (projectiveBundleChernTerm C sY sPY πY hsPY r hπY hfacY twistY k i hi x) =
      chowGroupCast C sPX
        (show k + (d : ℤ) + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
            k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (d : ℤ) from by omega)
        (projectiveBundleChernTerm C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ)) i hi
          (chowGroupCast C sX
            (show k - ((r - i : ℕ) : ℤ) + (d : ℤ) = k + (d : ℤ) - ((r - i : ℕ) : ℤ) from by omega)
            (flatPullbackChow C sX sY f hf d hd (k - ((r - i : ℕ) : ℤ))
              (hfacf (k - ((r - i : ℕ) : ℤ))) x)))

/-- The flat pullback of a family of Chow classes on `Y`, read in the degrees of a family on `X`
based at `k + d`. -/
def flatPullbackChernFamily (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sY (k - (j : ℤ))) (j : Fin (r + 1)) :
    chowGroup C sX (k + (d : ℤ) - (j : ℤ)) :=
  chowGroupCast C sX
    (show k - (j : ℤ) + (d : ℤ) = k + (d : ℤ) - (j : ℤ) from by omega)
    (flatPullbackChow C sX sY f hf d hd (k - (j : ℤ)) (hfacf (k - (j : ℤ))) (c j))

/-- The flat pullback of a family satisfying the projective-bundle relation over `Y` satisfies
the projective-bundle relation over `X`, given the compatibility `hcompat` of the summands with
flat pullback. -/
theorem flatPullback_projectiveBundleChernRelation
    (hcompat : ChernTermsCompatibleWithFlatPullback C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY f hf d hd hfacf f' hf' hd' hfacf') (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sY (k - (j : ℤ)))
    (hc : ProjectiveBundleChernRelation C sY sPY πY hsPY r hπY hfacY twistY k c) :
    ProjectiveBundleChernRelation C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ))
      (flatPullbackChernFamily C sX sY r f hf d hd hfacf k c) := by
  have hrel : ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sY sPY πY hsPY r hπY hfacY twistY k i.val
        (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩) = 0 := hc
  have hterm : ∀ i : Fin (r + 1),
      chowGroupCast C sPX
          (show k + (d : ℤ) + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
            k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (d : ℤ) from by omega)
          ((-1 : ℤ) ^ i.val •
            projectiveBundleChernTerm C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ)) i.val
              (Nat.lt_succ_iff.mp i.isLt)
              (flatPullbackChernFamily C sX sY r f hf d hd hfacf k c ⟨r - i.val, by omega⟩)) =
        flatPullbackChow C sPX sPY f' hf' d hd' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
          (hfacf' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))
          ((-1 : ℤ) ^ i.val •
            projectiveBundleChernTerm C sY sPY πY hsPY r hπY hfacY twistY k i.val
              (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)) := by
    intro i
    rw [map_zsmul, map_zsmul,
      hcompat k i.val (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)]
    rfl
  show ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
    projectiveBundleChernTerm C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ)) i.val
      (Nat.lt_succ_iff.mp i.isLt)
      (flatPullbackChernFamily C sX sY r f hf d hd hfacf k c ⟨r - i.val, by omega⟩) = 0
  refine (chowGroupCast C sPX
    (show k + (d : ℤ) + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
      k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (d : ℤ) from by omega)).injective ?_
  rw [map_zero, map_sum]
  have hsum : ∑ i : Fin (r + 1), chowGroupCast C sPX
        (show k + (d : ℤ) + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
          k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (d : ℤ) from by omega)
        ((-1 : ℤ) ^ i.val •
          projectiveBundleChernTerm C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ)) i.val
            (Nat.lt_succ_iff.mp i.isLt)
            (flatPullbackChernFamily C sX sY r f hf d hd hfacf k c ⟨r - i.val, by omega⟩)) =
      flatPullbackChow C sPX sPY f' hf' d hd' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (hfacf' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))
        (∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
          projectiveBundleChernTerm C sY sPY πY hsPY r hπY hfacY twistY k i.val
            (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hterm i
  rw [hsum, hrel, map_zero]

/-- The flat pullback of a family characterizing the Chern class cap products of `α` is a family
characterizing the Chern class cap products of `f^*α`. -/
theorem flatPullback_isChernCapFamily
    (hcompat : ChernTermsCompatibleWithFlatPullback C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY f hf d hd hfacf f' hf' hd' hfacf') (k : ℤ)
    (α : chowGroup C sY k) (c : ∀ j : Fin (r + 1), chowGroup C sY (k - (j : ℤ)))
    (hc : IsChernCapFamily C sY sPY πY hsPY r hπY hfacY twistY k α c) :
    IsChernCapFamily C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ))
      (flatPullbackChow C sX sY f hf d hd k (hfacf k) α)
      (flatPullbackChernFamily C sX sY r f hf d hd hfacf k c) := by
  refine ⟨?_, flatPullback_projectiveBundleChernRelation C sX sY sPX sPY πX hsPX πY hsPY r hπX
    hπY hfacX hfacY twistX twistY f hf d hd hfacf f' hf' hd' hfacf' hcompat k c hc.2⟩
  simp only [flatPullbackChernFamily, chowGroupCast_chowGroupCast]
  rw [flatPullbackChow_chowGroupCast C sX sY f hf d hd
    (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)
    (hfacf _) (hfacf k), hc.1]

/-- Flat pullback commutes with the Chern class cap products. Assume the injectivity `hinjX` of
the projective-bundle relation over `X` and the compatibility `hcompat` of its summands with flat
pullback. If `c` is the family of Chern class cap products of `α ∈ A_k(Y)` for `ℰ` and `e` is the
family of Chern class cap products of `f^*α ∈ A_{k+d}(X)` for `f^*ℰ`, then `e_j = f^*(c_j)`, that
is

  `c_j(f^*ℰ) ∩ f^*α = f^*(c_j(ℰ) ∩ α)`. -/
@[stacks 02U8 "carries both projective bundles as flat morphisms of relative dimension r - 1 with
first Chern class cap operators for their twists (Stacks 01O4, 02SO, 02TI), Stacks 02S1 for the
three flat morphisms, the injectivity half of Stacks 02TX over X, the compatibility of the
summands with flat pullback (Stacks 02SS and 02RD), and the cap products of Stacks 02U5 as
families satisfying the characterization of Stacks 02U6"]
theorem isChernCapFamily_flatPullback
    (hinjX : ProjectiveBundleRelationInjective C sX sPX πX hsPX r hπX hfacX twistX)
    (hcompat : ChernTermsCompatibleWithFlatPullback C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY f hf d hd hfacf f' hf' hd' hfacf') (k : ℤ)
    (α : chowGroup C sY k) (c : ∀ j : Fin (r + 1), chowGroup C sY (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 1), chowGroup C sX (k + (d : ℤ) - (j : ℤ)))
    (hc : IsChernCapFamily C sY sPY πY hsPY r hπY hfacY twistY k α c)
    (he : IsChernCapFamily C sX sPX πX hsPX r hπX hfacX twistX (k + (d : ℤ))
      (flatPullbackChow C sX sY f hf d hd k (hfacf k) α) e) :
    e = flatPullbackChernFamily C sX sY r f hf d hd hfacf k c :=
  eq_of_isChernCapFamily C sX sPX πX hsPX r hπX hfacX twistX hinjX (k + (d : ℤ))
    (flatPullbackChow C sX sY f hf d hd k (hfacf k) α) he
    (flatPullback_isChernCapFamily C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY hfacX hfacY twistX
      twistY f hf d hd hfacf f' hf' hd' hfacf' hcompat k α c hc)

end Stacks.Chow

end


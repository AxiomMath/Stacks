module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.IteratedCap
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback

/-!
# The summands of the relation of Stacks 02U6 commute with flat pullback

`Stacks.Chow.isChernCapFamily_flatPullback` is [Stacks, Tag 02U8] for two projective bundle data
over `f : X ⟶ Y` and a flat `f' : P_X ⟶ P_Y` over `f`, given the hypothesis
`Stacks.Chow.ChernTermsCompatibleWithFlatPullback`: flat pullback along `f'` carries each summand
`c₁(𝒪_{P_Y}(1))^i ∩ π_Y^*(-)` of the relation over `Y` to the corresponding summand over `X`.

This file proves that hypothesis when the square `f' ≫ π_Y = π_X ≫ f` commutes (Stacks 02RD, on
Chow groups `Stacks.Chow.flatPullbackChow_comm_of_comp_eq`) and flat pullback along `f'` carries
the cap with the twist of `P_Y` to the cap with the twist of `P_X` (Stacks 02SS).

## Main results

* `Stacks.Chow.flatPullbackChow_heq` — flat pullback on Chow groups respects heterogeneous equality
  of arguments in equal degrees.
* `Stacks.Chow.flatPullbackChow_iteratedChernCapOnChow_heq` — iterated caps commute with flat
  pullback when single caps do.
* `Stacks.Chow.chernTermsCompatibleWithFlatPullback_of_square` — the compatibility hypothesis of
  Stacks 02U8.

## References

* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Flat pullback on Chow groups, at heterogeneously equal arguments in equal degrees. -/
theorem flatPullbackChow_heq (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf d hd k)
    {k₁ k₂ : ℤ} (hk : k₁ = k₂) {x : chowGroup C sY k₁} {y : chowGroup C sY k₂} (hxy : x ≍ y) :
    flatPullbackChow C sX sY f hf d hd k₁ (hfac k₁) x ≍
      flatPullbackChow C sX sY f hf d hd k₂ (hfac k₂) y :=
  heq_apply_of_degree C sY sX (fun k => k) (fun k => k + (d : ℤ))
    (fun k => flatPullbackChow C sX sY f hf d hd k (hfac k)) hk hxy

/-- **Iterated caps commute with flat pullback** along a morphism with which the single caps
commute. -/
theorem flatPullbackChow_iteratedChernCapOnChow_heq (C : ChowSituation.{u}) {PX PY : Scheme.{u}}
    (sPX : PX ⟶ C.S) [LocallyOfFiniteType sPX] (sPY : PY ⟶ C.S) [LocallyOfFiniteType sPY]
    (f' : PX ⟶ PY) [LocallyOfFiniteType f'] [Flat f'] (hf' : f' ≫ sPY = sPX) (d : ℕ)
    (hd' : AlgebraicGeometry.RelativeDimension f' d)
    (hfacf' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPX sPY f' hf' d hd' k)
    (OX : ChernCapOperator C sPX) (OY : ChernCapOperator C sPY)
    (hξ : ∀ (e : ℤ) (y : chowGroup C sPY (e + 1)) (y' : chowGroup C sPX (e + (d : ℤ) + 1))
      (_ : y' ≍ flatPullbackChow C sPX sPY f' hf' d hd' (e + 1) (hfacf' (e + 1)) y),
      flatPullbackChow C sPX sPY f' hf' d hd' e (hfacf' e) (OY.capOnChow C sPY e y) ≍
        OX.capOnChow C sPX (e + (d : ℤ)) y')
    (n : ℕ) (e : ℤ) (y : chowGroup C sPY (e + ((List.replicate n OY).length : ℤ)))
    (y' : chowGroup C sPX (e + (d : ℤ) + ((List.replicate n OX).length : ℤ)))
    (hy : y' ≍ flatPullbackChow C sPX sPY f' hf' d hd' _ (hfacf' _) y) :
    flatPullbackChow C sPX sPY f' hf' d hd' e (hfacf' e)
        (iteratedChernCapOnChow C sPY (List.replicate n OY) e y) ≍
      iteratedChernCapOnChow C sPX (List.replicate n OX) (e + (d : ℤ)) y' := by
  induction n generalizing e with
  | zero =>
    refine HEq.trans ?_ (iteratedChernCapOnChow_replicate_zero_heq C sPX OX _ y').symm
    refine HEq.trans ?_ hy.symm
    exact flatPullbackChow_heq C sPX sPY f' hf' d hd' hfacf' (by simp)
      (iteratedChernCapOnChow_replicate_zero_heq C sPY OY e y)
  | succ n ih =>
    rw [iteratedChernCapOnChow_replicate_succ_heq C sPY OY n e y
      (chowGroupCast C sPY (by simp; ring) y) (chowGroupCast_heq C sPY _ y).symm,
      iteratedChernCapOnChow_replicate_succ_heq C sPX OX n (e + (d : ℤ)) y'
      (chowGroupCast C sPX (by simp; ring) y') (chowGroupCast_heq C sPX _ y').symm]
    refine (hξ e _ _ ?_).trans (capOnChow_heq C sPX OX rfl HEq.rfl)
    have := ih (e + 1) (chowGroupCast C sPY (by simp; ring) y)
      (chowGroupCast C sPX (by simp; ring) y')
      ((chowGroupCast_heq C sPX _ y').trans (hy.trans (flatPullbackChow_heq C sPX sPY f' hf' d
        hd' hfacf' (by simp; ring) (chowGroupCast_heq C sPY _ y).symm)))
    exact (iteratedChernCapOnChow_heq C sPX _ (show e + (d : ℤ) + 1 = e + 1 + (d : ℤ) by ring)
      ((chowGroupCast_heq C sPX _ _).trans (chowGroupCast_heq C sPX _ _).symm)).trans this.symm

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

/-- **The compatibility hypothesis of Stacks 02U8**, from the commuting square and the
compatibility of the twists. -/
theorem chernTermsCompatibleWithFlatPullback_of_square (hsq : f' ≫ πY = πX ≫ f)
    (hξ : ∀ (e : ℤ) (y : chowGroup C sPY (e + 1)) (y' : chowGroup C sPX (e + (d : ℤ) + 1))
      (_ : y' ≍ flatPullbackChow C sPX sPY f' hf' d hd' (e + 1) (hfacf' (e + 1)) y),
      flatPullbackChow C sPX sPY f' hf' d hd' e (hfacf' e) (twistY.capOnChow C sPY e y) ≍
        twistX.capOnChow C sPX (e + (d : ℤ)) y') :
    ChernTermsCompatibleWithFlatPullback C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY f hf d hd hfacf f' hf' hd' hfacf' := by
  intro k i hi x
  refine chowGroup_eq_of_heq C sPX ?_
  refine HEq.trans ?_ (chowGroupCast_heq C sPX _ _).symm
  simp only [projectiveBundleChernTerm, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, projectiveBundlePullback]
  set y' : chowGroup C sPX (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + (d : ℤ) +
      ((List.replicate i twistX).length : ℤ)) :=
    chowGroupCast C sPX (by simp only [List.length_replicate]; omega)
      (flatPullbackChow C sPX sX πX hsPX (r - 1) hπX _ (hfacX _)
        (chowGroupCast C sX (show k - ((r - i : ℕ) : ℤ) + (d : ℤ) =
          k + (d : ℤ) - ((r - i : ℕ) : ℤ) by omega)
          (flatPullbackChow C sX sY f hf d hd _ (hfacf _) x)))
  refine (flatPullbackChow_iteratedChernCapOnChow_heq C sPX sPY f' hf' d hd' hfacf' twistX twistY
    hξ i _ _ y' ?_).trans (iteratedChernCapOnChow_heq C sPX _ (by omega)
      ((chowGroupCast_heq C sPX _ _).trans (chowGroupCast_heq C sPX _ _).symm))
  refine (chowGroupCast_heq C sPX _ _).trans ?_
  refine HEq.trans ?_ (flatPullbackChow_heq C sPX sPY f' hf' d hd' hfacf' (by simp; omega)
    (chowGroupCast_heq C sPY _ _)).symm
  refine HEq.trans (flatPullbackChow_heq C sPX sX πX hsPX (r - 1) hπX hfacX (by omega)
    (chowGroupCast_heq C sX _ _)) ?_
  exact (flatPullbackChow_comm_of_comp_eq C sPX sPY sX sY f' πY πX f hf' hsPY hsPX hf d (r - 1)
    hd' hπY hπX hd hsq _ (hfacf' _) (hfacY _) (hfacX _) (hfacf _) x).symm

end Stacks.Chow

end

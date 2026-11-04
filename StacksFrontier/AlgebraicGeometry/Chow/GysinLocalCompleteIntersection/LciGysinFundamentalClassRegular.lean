module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.RegularFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinSystemOfInvertible

/-!
# `f^![Y] = [X]` for the Gysin map of a regular immersion followed by a flat morphism

Let `(S, δ)` be as in Situation 02QL and let `f = i ≫ g` with `i : X ⟶ P` a regular closed
immersion whose normal sheaf has constant rank `r` and `g : P ⟶ Y` flat of constant relative
dimension `d`, all locally of finite type over `S`. With `i^! = c(X ⟶ P, 𝒩_{X/P})` the class of
Stacks 0FBK and `g^*` the class of Stacks 0B78, the Gysin map `f^! = i^! ∘ g^*` of Stacks 0FF3
satisfies

  `f^![Y]_m = [X]_{m + d - r}`

whenever `dim_δ(Y) ≤ m` and `dim_δ(X) ≤ m + d - r`. This is the δ-equidimensional case of
Stacks 0FF7 at `Y' = Y` with nothing assumed: `g^*[Y]_m = [P]_{m+d}` (Stacks 02RE) and
`i^![P]_{m+d} = [X]_{m+d-r}` (in the namespace `Stacks.Chow`,
`VirtualNormalBundle.virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection_of_isIso`,
the case `Y = X` of Stacks 0FBM).

## Main results

* `Stacks.Chow.lciGysinComposite_cap_fundamentalChowClass` — `f^![Y]_m = [X ×_Y Y]_{m+d-r}`.

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X P Y : Scheme.{u}} [IsLocallyNoetherian X] (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sY : Y ⟶ C.S)
  [LocallyOfFiniteType sY] {i : X ⟶ P} [IsClosedImmersion i] (hi : IsRegularImmersion i)
  (hiP : i ≫ sP = sX) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle r]
  (g : P ⟶ Y) [LocallyOfFiniteType g] [Flat g] (hg : g ≫ sY = sP) (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d)

/-- **`f^![Y]_m = [X]_{m+d-r}`** for `f = i ≫ g` with `i` a regular closed immersion of constant
codimension `r` and `g` flat of constant relative dimension `d`: the composite
`f^! = i^! ∘ g^* ∈ A^{r-d}(X ⟶ Y)` of the class of Stacks 0FBK and the flat pullback class of
Stacks 0B78 caps the fundamental class `[Y]_m` to the fundamental class of `X ×_Y Y` in degree
`m - (r - d)`, provided `dim_δ(Y) ≤ m` and `dim_δ(X) ≤ m + d - r`. -/
theorem lciGysinComposite_cap_fundamentalChowClass (m : ℤ)
    (hY : schemeDeltaDimension C sY ≤ (m : EInt))
    (hX : schemeDeltaDimension C sX ≤ ((m + d - r : ℤ) : EInt)) :
    (bivariantCompositeOfInvertible C sX sP sY i g hiP hg (r : ℤ) (-(d : ℤ))
        ((VirtualNormalBundle.ofIsRegularImmersion i hi).virtualNormalClass C sP sX hiP r)
        (flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd)).cap (𝟙 Y) m
        (fundamentalChowClass C (𝟙 Y ≫ sY) m) =
      fundamentalChowClass C (pullback.fst (i ≫ g) (𝟙 Y) ≫ sX) (m - ((r : ℤ) + -(d : ℤ))) := by
  have hP : schemeDeltaDimension C sP ≤ ((m + d : ℤ) : EInt) := by
    have h := Stacks.Chow.SectionZeroScheme.schemeDeltaDimension_le_of_flat C sY g d hgd hY
    exact (schemeDeltaDimension_congr C hg).symm.trans_le h
  have hY' : schemeDeltaDimension C (𝟙 Y ≫ sY) ≤ (m : EInt) :=
    (schemeDeltaDimension_congr C (Category.id_comp sY)).trans_le hY
  have hb : (flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd).cap (𝟙 Y) m
      (fundamentalChowClass C (𝟙 Y ≫ sY) m) =
      fundamentalChowClass C (pullback.fst g (𝟙 Y) ≫ sP) (m - -(d : ℤ)) :=
    (flatPullbackBivariantCap_apply C sP sY g hg d hgd (flatPullbackDescends C) (𝟙 Y) m _).trans
      ((congrArg (chowGroupDegreeEquiv C _ _)
        (flatPullbackChow_fundamentalChowClass C _ _ _ _ d _ m _ hY')).trans
        (chowGroupDegreeEquiv_fundamentalChowClass C _ _))
  have hQ : IsQuasiRegularImmersion i :=
    isQuasiRegularImmersion_of_isH1RegularImmersion i
      (isH1RegularImmersion_of_isKoszulRegularImmersion i
        (isKoszulRegularImmersion_of_isRegularImmersion i hi))
  have ha :=
    VirtualNormalBundle.virtualNormalClass_cap_fundamentalChowClass_of_isIso_surjection_of_isIso
    (VirtualNormalBundle.ofIsRegularImmersion i hi) hQ C sP sX hiP r (pullback.fst g (𝟙 Y))
    (m - -(d : ℤ))
    (hP.trans (WithBotTop.coe_le_coe.mpr (by omega)))
    (hX.trans (WithBotTop.coe_le_coe.mpr (by omega)))
  rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply]
  refine (congrArg (chowGroupDegreeEquiv C _ _) ((congrArg (properChowPushforward C _ _ _ _ _ _)
    ((congrArg (DFunLike.coe (((VirtualNormalBundle.ofIsRegularImmersion i hi).virtualNormalClass
      C sP sX hiP r).cap (pullback.fst g (𝟙 Y)) (m - -(d : ℤ)))) hb).trans ha)).trans
    (properChowPushforward_fundamentalChowClass_of_isIso C _ _ _ _ _ _))).trans ?_
  exact chowGroupDegreeEquiv_fundamentalChowClass C _ _

end Stacks.Chow

end

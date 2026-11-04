module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionDivision
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClassCharacterized

/-!
# A composite `i^! ∘ g^*` on a fundamental class, for the class of Stacks 0FBK

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : X ⟶ P` be a
closed immersion carrying a virtual normal bundle `𝒩` of constant rank `r`, and let `g : P ⟶ Y`
be smooth of constant relative dimension `d`. This file computes, for a test scheme `Y' ⟶ Y` of
`δ`-dimension at most `n`, the cap product with `[Y']_n` of a bivariant class `cf` of degree
`r - d` for `i ≫ g` that is the composite `ci ∘ g^*` (Stacks 0FE0) of a class `ci` satisfying the
relation of Stacks 0FBK for `𝒩` (`Stacks.Chow.IsVirtualNormalBundleClass`) with the flat pullback
class of `g` (Stacks 0B78): it is `[X ×_Y Y']_{n + d - r}`, under the value of the virtual normal
cone class on the fundamental class of `P ×_Y Y'` (Stacks 0FBM at vanishing excess) and the
dimension bound on `X ×_Y Y'`.

This is the computation `f^![Y'] = [X']` of the proof of Stacks 0FF7 in the case of a single
factorization of constant ranks, stated for the class `c(X ⟶ P, 𝒩)` of Stacks 0FBK that
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassConstruction` builds.
Stacks 0FF7 itself, for the Gysin map `Stacks.Chow.lciGysinMap` of Stacks 0FF3, is
`Stacks.Chow.completedCapFundamentalClass_completedBivariantRestriction_lciGysinMap` in
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalCycle`.

## Main results

* `Stacks.Chow.lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass` —
  `cf ∩ [Y']_n = [X']_{n - (r + (-d))}` for a class `cf` characterized as the composite of a class
  satisfying the relation of Stacks 0FBK for `i` with the flat pullback class of `g`.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass_virtualNormalBundleClass` — the same, with the
  class of `i` taken to be `Stacks.Chow.virtualNormalBundleClass`.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass_id_of_isVirtualNormalBundleClass` — part (b) of
  Stacks 0FF8 in this setting: `f^![Y]_n = [X]_{n - (r - d)}` on `X` itself.

## Implementation notes

The class `cf` enters through two characterizing hypotheses: `hcf`, that `cf` is the composite
`ci ∘ g^*` (`Stacks.Chow.IsBivariantClassComposition`), which determines `cf` from `ci` by
`Stacks.Chow.eq_of_isBivariantClassComposition`; and `hci`, that `ci` satisfies the relation of
Stacks 0FBK for `𝒩` (`Stacks.Chow.IsVirtualNormalBundleClass`). The remaining hypotheses are inputs
of the constructions used: `hdesc` (Stacks 02S1) and `hcg`, that the flat pullback class `cg`
satisfies the characterization of Stacks 0B78 (`Stacks.Chow.IsBivariantFlatPullback`), for the
flat pullback, `hpp` (Stacks 02S2) for the composite, and `hcone`, the
value of `ι_* ∘ j^* ∘ C` on a fundamental class, for Stacks 0FBM at vanishing excess
(`Stacks.Chow.cap_fundamentalChowClass_of_isVirtualNormalBundleClass`).

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FF8](https://stacks.math.columbia.edu/tag/0FF8)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section LciComposite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X P Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX)
  (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (hg : g ≫ sY = sP) (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d)
  (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
  (hdesc : FlatPullbackDescends C)
  (hpp : ProperPushforwardDescends C) {cg : BivariantClass C G sP sY g hg (-(d : ℤ))}
  (hcg : IsBivariantFlatPullback C G sP sY g hg d hgd hdesc cg)

include hcg in
/-- **A composite `i^! ∘ g^*` on a fundamental class.** Let `f = i ≫ g` with `i : X ⟶ P` a
closed immersion carrying a virtual normal bundle of constant rank `r` and `g : P ⟶ Y` smooth of
constant relative dimension `d`, and let `g' : Y' ⟶ Y` be a test scheme of δ-dimension at most
`n`. Assume

* `ci` satisfies the characterizing relation of Stacks 0FBK for the virtual normal bundle of `i`;
* `cf` is the composite `ci ∘ g^*` in the sense of Stacks 0FE0; and
* `dim_δ(X ×_Y Y') ≤ n + d - r`.

Then `cf ∩ [Y']_n = [X']_{n - (r + (-d))}`: the flat pullback class takes `[Y']_n` to
`[P ×_Y Y']_{n+d}` (`Stacks.Chow.IsBivariantFlatPullback.cap_fundamentalChowClass`), the class
`ci` takes that to `[X ×_P (P ×_Y Y')]_{n+d-r}` by Stacks 0FBM at vanishing excess
(`Stacks.Chow.cap_fundamentalChowClass_of_isVirtualNormalBundleClass`), and the composite of
Stacks 0FE0 pushes the result forward along the associativity isomorphism
`X ×_P (P ×_Y Y') ≅ X ×_Y Y'` (`Stacks.Chow.chowPushforwardOfIso_fundamentalChowClass`). -/
theorem lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass
    {ci : BivariantClass C G sX sP i hi (r : ℤ)}
    (hci : IsVirtualNormalBundleClass C sX sP i hi G 𝒩 r ci)
    {cf : BivariantClass C G sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg)
      ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
      cg cf)
    {Y' : Scheme.{u}} (g' : Y' ⟶ Y) [LocallyOfFiniteType g'] (n : ℤ)
    (hY' : schemeDeltaDimension C (g' ≫ sY) ≤ (n : EInt))
    (hX' : schemeDeltaDimension C (pullback.fst i (pullback.fst g g') ≫ sX) ≤
      (((n + (d : ℤ)) - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C
        (pullback.fst (𝒩.projection ≫ i) (pullback.fst g g') ≫ 𝒩.projection ≫ sX)
        (by omega : (n + (d : ℤ)) - (0 : ℤ) = ((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))
        ((virtualNormalConeClass C sX sP i hi 𝒩).cap (pullback.fst g g') (n + (d : ℤ))
          (fundamentalChowClass C (pullback.fst g g' ≫ sP) (n + (d : ℤ)))) =
      fundamentalChowClass C
        (pullback.fst (𝒩.projection ≫ i) (pullback.fst g g') ≫ 𝒩.projection ≫ sX)
        (((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))) :
    cf.cap g' n (fundamentalChowClass C (g' ≫ sY) n) =
      fundamentalChowClass C (pullback.fst (i ≫ g) g' ≫ sX) (n - ((r : ℤ) + -(d : ℤ))) := by
  have _ : IsIso (pullbackRightPullbackFstIso g g' i).hom := inferInstance
  have hdeg : n - ((r : ℤ) + -(d : ℤ)) = n - -(d : ℤ) - (r : ℤ) := by ring
  -- The smooth half: `g^*[Y']_n = [P ×_Y Y']_{n - (-d)}`.
  have hsmooth := hcg.cap_fundamentalChowClass g' n hY'
  -- Stacks 0FBM at vanishing excess, in degree `n + d`.
  have hgysin := cap_fundamentalChowClass_of_isVirtualNormalBundleClass C G sX sP i hi 𝒩 r hci
    (pullback.fst g g') (n + (d : ℤ)) hX' hcone
  -- The same, transported to the degree `n - (-d)` the composite's cap operation uses.
  have hgysin' : ci.cap (pullback.fst g g') (n - -(d : ℤ))
        (fundamentalChowClass C (pullback.fst g g' ≫ sP) (n - -(d : ℤ))) =
      fundamentalChowClass C (pullback.fst i (pullback.fst g g') ≫ sX)
        (n - -(d : ℤ) - (r : ℤ)) :=
    eq_of_heq ((cap_fundamentalChowClass_heq C G sX sP i hi (r : ℤ) ci (pullback.fst g g')
        (show n - -(d : ℤ) = n + (d : ℤ) by ring)).trans
      ((heq_of_eq hgysin).trans (fundamentalChowClass_heq C _ (by ring))))
  -- Assemble through the composition formula of Stacks 0FE0.
  have hcomp := (isBivariantClassComposition_iff C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
    cg cf).1 hcf g' n
    (fundamentalChowClass C (g' ≫ sY) n)
  rw [bivariantCompositeCap_apply, hsmooth, hgysin',
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_fundamentalChowClass]
    at hcomp
  refine (chowGroupDegreeEquiv C (pullback.fst (i ≫ g) g' ≫ sX) hdeg).injective
    (hcomp.trans ?_)
  exact (chowGroupDegreeEquiv_fundamentalChowClass C (pullback.fst (i ≫ g) g' ≫ sX) hdeg).symm

end LciComposite

section LciCompositeClass

variable (C : ChowSituation.{u}) {X P Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX)
  (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (hg : g ≫ sY = sP) (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d)
  (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]

/-- **Stacks 0FF7 for the class `c(X ⟶ P, 𝒩)` of Stacks 0FBK.** The same conclusion as
`Stacks.Chow.lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass`, with the abstract
class `ci` replaced by
`Stacks.Chow.virtualNormalBundleClass`, the element of `A^r(X ⟶ P)` built for the virtual normal
bundle of `i`, and with the characterizing relation discharged by
`Stacks.Chow.isVirtualNormalBundleClass_virtualNormalBundleClass`. -/
theorem lciGysinCap_fundamentalChowClass_virtualNormalBundleClass
    {cf : BivariantClass C (gysinSystemOfInvertible C) sX sY (i ≫ g)
      (comp_comp_structureMorphism_eq hi hg) ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C (gysinSystemOfInvertible C) sX sP sY i g hi hg
      (properPushforwardDescends C) (r : ℤ) (-(d : ℤ))
      (virtualNormalBundleClass C sX sP i hi 𝒩 r)
      (flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd) cf)
    {Y' : Scheme.{u}} (g' : Y' ⟶ Y) [LocallyOfFiniteType g'] (n : ℤ)
    (hY' : schemeDeltaDimension C (g' ≫ sY) ≤ (n : EInt))
    (hX' : schemeDeltaDimension C (pullback.fst i (pullback.fst g g') ≫ sX) ≤
      (((n + (d : ℤ)) - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C
        (pullback.fst (𝒩.projection ≫ i) (pullback.fst g g') ≫ 𝒩.projection ≫ sX)
        (by omega : (n + (d : ℤ)) - (0 : ℤ) = ((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))
        ((virtualNormalConeClass C sX sP i hi 𝒩).cap (pullback.fst g g') (n + (d : ℤ))
          (fundamentalChowClass C (pullback.fst g g' ≫ sP) (n + (d : ℤ)))) =
      fundamentalChowClass C
        (pullback.fst (𝒩.projection ≫ i) (pullback.fst g g') ≫ 𝒩.projection ≫ sX)
        (((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))) :
    cf.cap g' n (fundamentalChowClass C (g' ≫ sY) n) =
      fundamentalChowClass C (pullback.fst (i ≫ g) g' ≫ sX) (n - ((r : ℤ) + -(d : ℤ))) :=
  lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass C (gysinSystemOfInvertible C)
    sX sP sY i hi g hg d hgd 𝒩 r
    (flatPullbackDescends C) (properPushforwardDescends C)
    (isBivariantFlatPullback_flatPullbackBivariantClassOfInvertible C sP sY g hg d hgd)
    (isVirtualNormalBundleClass_virtualNormalBundleClass C sX sP i hi 𝒩 r) hcf g' n hY' hX' hcone

end LciCompositeClass

section PartBComposite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X P Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (i : X ⟶ P) [IsClosedImmersion i] (hi : i ≫ sP = sX)
  (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (hg : g ≫ sY = sP) (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d)
  (𝒩 : VirtualNormalBundle i) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒩.bundle r]
  (hdesc : FlatPullbackDescends C)
  (hpp : ProperPushforwardDescends C) {cg : BivariantClass C G sP sY g hg (-(d : ℤ))}
  (hcg : IsBivariantFlatPullback C G sP sY g hg d hgd hdesc cg)

include hcg in
/-- **Stacks 0FF8 (b).** Let `f = i ≫ g` with `i : X ⟶ P` an immersion carrying a virtual normal
bundle of constant rank `r` and `g : P ⟶ Y` smooth of constant relative dimension `d`, so that
the Gysin map exists for `f` in the sense of Stacks 0FF3, and let `f^!` be the Gysin map, entering
as a bivariant class `cf` characterized as `i^! ∘ g^*`. If `dim_δ(Y) ≤ n` and
`dim_δ(X ×_P (P ×_Y Y)) ≤ n + d - r`, then

  `f^![Y]_n = [X]_{n - (r - d)}`

in the Chow group of `X` itself.

This is `Stacks.Chow.lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass` — a special
case of Stacks 0FF7 for a
class `cf` characterized as `i^! ∘ g^*`, with constant ranks and the excess vanishing as the
hypothesis `hcone`; the full Stacks 0FF7, for the constructed Gysin map `Stacks.Chow.lciGysinMap`,
is `Stacks.Chow.completedCapFundamentalClass_completedBivariantRestriction_lciGysinMap` — at the
test scheme `g' = 𝟙 Y`, followed by the identification of `X ×_Y Y` with `X`:
the projection `pullback.fst f (𝟙 Y)` is an isomorphism, and pushforward along an isomorphism
over the base carries a fundamental class to a fundamental class by
`Stacks.Chow.chowPushforwardOfIso_fundamentalChowClass`.

The hypotheses are those of
`Stacks.Chow.lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass`, whose implementation
notes say what each one is and why none of them is the conclusion; see also the implementation
notes above for how the Cohen-Macaulay hypothesis and the conditions of Stacks 0FE3 enter. -/
@[stacks 0FF8 "part (b): `f^![Y]_n = [X]_{n-(r-d)}` on `X` itself, from 0FF7 at `Y' = Y`. The \
0FE3 conditions enter as the two δ-dimension bounds and the Cohen-Macaulay hypothesis as the \
vanishing excess `hcone`, exactly as in 0FF7's carrier; no clopen reduction"]
theorem lciGysinCap_fundamentalChowClass_id_of_isVirtualNormalBundleClass
    {ci : BivariantClass C G sX sP i hi (r : ℤ)}
    (hci : IsVirtualNormalBundleClass C sX sP i hi G 𝒩 r ci)
    {cf : BivariantClass C G sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg)
      ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
      cg cf)
    (n : ℤ) (hY : schemeDeltaDimension C (𝟙 Y ≫ sY) ≤ (n : EInt))
    (hX : schemeDeltaDimension C (pullback.fst i (pullback.fst g (𝟙 Y)) ≫ sX) ≤
      (((n + (d : ℤ)) - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C
        (pullback.fst (𝒩.projection ≫ i) (pullback.fst g (𝟙 Y)) ≫ 𝒩.projection ≫ sX)
        (by omega : (n + (d : ℤ)) - (0 : ℤ) = ((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))
        ((virtualNormalConeClass C sX sP i hi 𝒩).cap (pullback.fst g (𝟙 Y)) (n + (d : ℤ))
          (fundamentalChowClass C (pullback.fst g (𝟙 Y) ≫ sP) (n + (d : ℤ)))) =
      fundamentalChowClass C
        (pullback.fst (𝒩.projection ≫ i) (pullback.fst g (𝟙 Y)) ≫ 𝒩.projection ≫ sX)
        (((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))) :
    chowPushforwardOfIso C (pullback.fst (i ≫ g) (𝟙 Y) ≫ sX) sX
        (pullback.fst (i ≫ g) (𝟙 Y)) rfl (n - ((r : ℤ) + -(d : ℤ)))
        (cf.cap (𝟙 Y) n
          (chowGroupCongr C (Category.id_comp sY).symm n (fundamentalChowClass C sY n))) =
      fundamentalChowClass C sX (n - ((r : ℤ) + -(d : ℤ))) := by
  rw [chowGroupCongr_fundamentalChowClass C (Category.id_comp sY).symm n,
    lciGysinCap_fundamentalChowClass_of_isVirtualNormalBundleClass C G sX sP sY i hi g hg d hgd 𝒩 r
      hdesc hpp hcg hci hcf (𝟙 Y) n hY hX hcone]
  exact chowPushforwardOfIso_fundamentalChowClass C (pullback.fst (i ≫ g) (𝟙 Y) ≫ sX) sX
    (pullback.fst (i ≫ g) (𝟙 Y)) rfl (n - ((r : ℤ) + -(d : ℤ)))

end PartBComposite

end Stacks.Chow

end

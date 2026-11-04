module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin map of a local complete intersection morphism on a fundamental class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and consider a cartesian
square

  `X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `Y' ⟶ Y`

of schemes locally of finite type over `S`, with `f = i ≫ g` for an immersion `i : X ⟶ P`
carrying a virtual normal bundle of constant rank `r` and a smooth morphism `g : P ⟶ Y` of
constant relative dimension `d`. In the δ-equidimensional case, with the excess of `i` vanishing,
the Gysin map of `f` carries the fundamental class of `Y'` to that of `X'`:

  `f^![Y'] = [X']`.

## Main results

* `Stacks.Chow.properPushforward_fundamentalCycle_of_isIso` and
  `Stacks.Chow.chowPushforwardOfIso_fundamentalChowClass` — pushforward along an isomorphism over
  the base carries a fundamental cycle, resp. a fundamental class, to the fundamental cycle, resp.
  the fundamental class, of the target.
* `Stacks.Chow.flatPullbackBivariantClass_cap_fundamentalChowClass` — the bivariant class
  attached to a flat morphism `g : P ⟶ Y` of relative dimension `d` carries the fundamental class
  of a test scheme `Y'` of δ-dimension at most `n` to the fundamental class of `P ×_Y Y'` in
  degree `n + d`.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass` — `f^![Y'] = [X']` in the δ-equidimensional
  case, for a bivariant class `f^!` characterized as the composite of a virtual normal Gysin
  class of `i` with the flat pullback class of `g`.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass_virtualNormalGysinClass` — the same, with the
  Gysin class of `i` taken to be `Stacks.Chow.virtualNormalGysinClass`.

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0FEA](https://stacks.math.columbia.edu/tag/0FEA)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
* [Stacks Project, Tag 0FE4](https://stacks.math.columbia.edu/tag/0FE4)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Fundamental classes and degree transports -/

/-- Transport of a fundamental class along an equality of degrees is the fundamental class in the
other degree. -/
theorem chowGroupDegreeEquiv_fundamentalChowClass (C : ChowSituation.{u}) {T : Scheme.{u}}
    (sT : T ⟶ C.S) [LocallyOfFiniteType sT] {k l : ℤ} (h : k = l) :
    chowGroupDegreeEquiv C sT h (fundamentalChowClass C sT k) = fundamentalChowClass C sT l := by
  subst h
  rfl

/-- Fundamental classes in two degrees that are the same integer written two ways are
heterogeneously equal. -/
theorem fundamentalChowClass_heq (C : ChowSituation.{u}) {T : Scheme.{u}} (sT : T ⟶ C.S)
    [LocallyOfFiniteType sT] {k l : ℤ} (h : k = l) :
    fundamentalChowClass C sT k ≍ fundamentalChowClass C sT l := by
  subst h
  rfl

/-- A cap operation applied to the fundamental class depends on the degree only up to
heterogeneous equality. -/
theorem cap_fundamentalChowClass_heq (C : ChowSituation.{u}) (G : GysinSystem C)
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (f : A ⟶ B) [LocallyOfFiniteType f] (hf : f ≫ sB = sA) (p : ℤ)
    (c : BivariantClass C G sA sB f hf p) {T : Scheme.{u}} (t : T ⟶ B) [LocallyOfFiniteType t]
    {k l : ℤ} (h : k = l) :
    c.cap t k (fundamentalChowClass C (t ≫ sB) k) ≍
      c.cap t l (fundamentalChowClass C (t ≫ sB) l) := by
  subst h
  rfl

/-! ### Pushforward along an isomorphism -/

/-- Proper pushforward along an isomorphism over the base carries the fundamental cycle to the
fundamental cycle. -/
theorem properPushforward_fundamentalCycle_of_isIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B)
    [IsIso u] (hu : u ≫ sB = sA) (k : ℤ) :
    properPushforward C sA sB u hu k (fundamentalCycle C sA k) = fundamentalCycle C sB k := by
  rw [properPushforward_fundamentalCycle_of_isClosedImmersion C sA sB u hu k, fundamentalCycle]
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C sB u (𝟙 B) (asIso u) (by simp) k

/-- Pushforward on Chow groups along an isomorphism over the base carries the fundamental class to
the fundamental class. -/
theorem chowPushforwardOfIso_fundamentalChowClass (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (u : A ⟶ B)
    [IsIso u] (hu : u ≫ sB = sA) (k : ℤ) :
    chowPushforwardOfIso C sA sB u hu k (fundamentalChowClass C sA k) =
      fundamentalChowClass C sB k := by
  rw [fundamentalChowClass, chowPushforwardOfIso_mk,
    properPushforward_fundamentalCycle_of_isIso C sA sB u hu k, fundamentalChowClass]

/-! ### The smooth half of the factorization on a fundamental class -/

/-- The bivariant class attached to a flat morphism `g : P ⟶ Y` of relative dimension `d`
carries the fundamental class of a test scheme `Y'` of δ-dimension at most `n` to the fundamental
class of `P ×_Y Y'`, in the degree `n - (-d)` that a class of degree `-d` produces:
`(g')^*[Y'] = [Y' ×_Y P]`. -/
theorem flatPullbackBivariantClass_cap_fundamentalChowClass (C : ChowSituation.{u})
    (G : GysinSystem C) {P Y : Scheme.{u}} (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : P ⟶ Y) [LocallyOfFiniteType g]
    [AlgebraicGeometry.Flat g] (hg : g ≫ sY = sP) (d : ℕ)
    (hgd : AlgebraicGeometry.RelativeDimension g d) (hdesc : FlatPullbackDescends C)
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (h71 : G.FlatPullbackNaturality d)
    {Y' : Scheme.{u}} (g' : Y' ⟶ Y) [LocallyOfFiniteType g'] (n : ℤ)
    (hdim : schemeDeltaDimension C (g' ≫ sY) ≤ (n : EInt)) :
    (flatPullbackBivariantClass C G sP sY g hg d hgd hdesc hRG h71).cap g' n
        (fundamentalChowClass C (g' ≫ sY) n) =
      fundamentalChowClass C (pullback.fst g g' ≫ sP) (n - -(d : ℤ)) := by
  have h1 := flatPullbackBivariantClass_cap C G sP sY g hg d hgd hdesc hRG h71 g' n
    (fundamentalChowClass C (g' ≫ sY) n)
  rw [flatPullbackChow_fundamentalChowClass C (pullback.fst g g' ≫ sP) (g' ≫ sY)
    (pullback.snd g g') (pullbackSnd_comp_structureMorphism hg g') d
    (relativeDimension_pullbackSnd g hgd g') n _ hdim] at h1
  exact eq_of_heq (h1.trans (fundamentalChowClass_heq C _ (by ring)))

/-! ### The Gysin map of `f = i ≫ g` on a fundamental class -/

section Lci

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X P Y N : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : X ⟶ P) [IsImmersion i] [LocallyOfFiniteType i] (hi : i ≫ sP = sX)
  (g : P ⟶ Y) [Smooth g] [LocallyOfFiniteType g] (hg : g ≫ sY = sP) (d : ℕ)
  (hgd : AlgebraicGeometry.RelativeDimension g d)
  (q : N ⟶ X) [LocallyOfFiniteType q] (hq : q ≫ sX = sN) (r : ℕ)
  (E : BivariantClass C G sN sP (q ≫ i) (comp_comp_structureMorphism_eq hq hi) 0)
  (NP : VirtualNormalBundleProjection i q r) (hdesc : FlatPullbackDescends C)
  (hpp : ProperPushforwardDescends C) (hRG : ProperPushforwardFlatPullbackBaseChange C)
  (h71 : G.FlatPullbackNaturality d)

omit [LocallyOfFiniteType i] [LocallyOfFiniteType g] in
/-- The Gysin map exists for the composite of an immersion with a smooth morphism. -/
theorem gysinMapExists_of_immersion_comp_smooth : GysinMapExists (i ≫ g) :=
  GysinMapExists.of_comp i g

/-- **The Gysin map of a local complete intersection on a fundamental class, δ-equidimensional
case.** Let `f = i ≫ g` with `i : X ⟶ P` an immersion carrying a virtual normal bundle of
constant rank `r` and `g : P ⟶ Y` smooth of constant relative dimension `d`, and let
`g' : Y' ⟶ Y` be a test scheme of δ-dimension at most `n`. Assume

* `ci` satisfies the characterizing relation `Stacks.Chow.IsVirtualNormalGysinClass` for the
  virtual normal bundle of `i`, so that `ci` is the Gysin class `i^! = c(X ⟶ P, 𝒩)`;
* `cf` is the composite `ci ∘ g^*` in the sense of `Stacks.Chow.IsBivariantClassComposition`,
  so that `cf` is the Gysin map `f^! = i^! ∘ g^*`; and
* `dim_δ(X ×_Y Y') ≤ n + d - r`.

Then `f^![Y']_n = [X']_{n - (r + (-d))}`. -/
@[stacks 0FF7 "δ-equidimensional case: `f^![Y']_n = [X']_n'` for `f = i ≫ g`, `g` smooth, with \
`f^!` characterized as `i^! ∘ g^*` (0FF3, 0FE0) and `i^!` by 0FBK; `g^*[Y'] = [P ×_Y Y']` proved \
here; carried: 0FEA's regular-sequence step as vanishing excess (so hypothesis (4) is replaced by \
its consequence), 0FBM's hcone and hinj, 02S1, 02S2, 02RG, 0B71; no clopen reduction"]
theorem lciGysinCap_fundamentalChowClass
    (hinj : ∀ {T : Scheme.{u}} (t : T ⟶ P) [LocallyOfFiniteType t] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc t k))
    {ci : BivariantClass C G sX sP i hi (r : ℤ)}
    (hci : IsVirtualNormalGysinClass C G sX sP sN i hi q hq r 0 E
      (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) NP ci)
    {cf : BivariantClass C G sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg)
      ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
      (flatPullbackBivariantClass C G sP sY g hg d hgd hdesc hRG h71) cf)
    {Y' : Scheme.{u}} (g' : Y' ⟶ Y) [LocallyOfFiniteType g'] (n : ℤ)
    (hY' : schemeDeltaDimension C (g' ≫ sY) ≤ (n : EInt))
    (hX' : schemeDeltaDimension C (pullback.fst i (pullback.fst g g') ≫ sX) ≤
      (((n + (d : ℤ)) - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) (pullback.fst g g') ≫ sN)
        (by omega : (n + (d : ℤ)) - (0 : ℤ) = ((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))
        (E.cap (pullback.fst g g') (n + (d : ℤ))
          (fundamentalChowClass C (pullback.fst g g' ≫ sP) (n + (d : ℤ)))) =
      fundamentalChowClass C (pullback.fst (q ≫ i) (pullback.fst g g') ≫ sN)
        (((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))) :
    cf.cap g' n (fundamentalChowClass C (g' ≫ sY) n) =
      fundamentalChowClass C (pullback.fst (i ≫ g) g' ≫ sX) (n - ((r : ℤ) + -(d : ℤ))) := by
  have _ : IsIso (pullbackRightPullbackFstIso g g' i).hom := inferInstance
  have hdeg : n - ((r : ℤ) + -(d : ℤ)) = n - -(d : ℤ) - (r : ℤ) := by ring
  have hsmooth := flatPullbackBivariantClass_cap_fundamentalChowClass C G sP sY g hg d hgd hdesc
    hRG h71 g' n hY'
  have hgysin := virtualNormalGysinCap_fundamentalChowClass C G sX sP sN i hi q hq r E NP hdesc
    hinj hci (pullback.fst g g') (n + (d : ℤ)) hX' hcone
  have hgysin' : ci.cap (pullback.fst g g') (n - -(d : ℤ))
        (fundamentalChowClass C (pullback.fst g g' ≫ sP) (n - -(d : ℤ))) =
      fundamentalChowClass C (pullback.fst i (pullback.fst g g') ≫ sX)
        (n - -(d : ℤ) - (r : ℤ)) :=
    eq_of_heq ((cap_fundamentalChowClass_heq C G sX sP i hi (r : ℤ) ci (pullback.fst g g')
        (show n - -(d : ℤ) = n + (d : ℤ) by ring)).trans
      ((heq_of_eq hgysin).trans (fundamentalChowClass_heq C _ (by ring))))
  have hcomp := (isBivariantClassComposition_iff C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
    (flatPullbackBivariantClass C G sP sY g hg d hgd hdesc hRG h71) cf).1 hcf g' n
    (fundamentalChowClass C (g' ≫ sY) n)
  rw [bivariantCompositeCap_apply, hsmooth, hgysin',
    properChowPushforward_eq_chowPushforwardOfIso, chowPushforwardOfIso_fundamentalChowClass]
    at hcomp
  refine (chowGroupDegreeEquiv C (pullback.fst (i ≫ g) g' ≫ sX) hdeg).injective
    (hcomp.trans ?_)
  exact (chowGroupDegreeEquiv_fundamentalChowClass C (pullback.fst (i ≫ g) g' ≫ sX) hdeg).symm

/-- The conclusion of `Stacks.Chow.lciGysinCap_fundamentalChowClass`, with the class `ci`
taken to be `Stacks.Chow.virtualNormalGysinClass`, the element of `A^r(X ⟶ P)` attached to the
virtual normal bundle of `i`. -/
theorem lciGysinCap_fundamentalChowClass_virtualNormalGysinClass
    (hbij : ∀ {T : Scheme.{u}} (t : T ⟶ P) [LocallyOfFiniteType t] (k : ℤ),
      Function.Bijective
        (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc t k))
    (hproper : PiProperNaturality C sX sN i q r 0
      (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc))
    (hflat : TransportFlatNaturality C G sX sP sN i hi q hq r 0 E
      (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) hbij)
    (hgysin : TransportGysinNaturality C G sX sP sN i hi q hq r 0 E
      (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) hbij)
    {cf : BivariantClass C G sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg)
      ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ))
      (virtualNormalGysinClass C G sX sP sN i hi q hq r 0 E
        (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) NP hpp hbij
        hproper hflat hgysin)
      (flatPullbackBivariantClass C G sP sY g hg d hgd hdesc hRG h71) cf)
    {Y' : Scheme.{u}} (g' : Y' ⟶ Y) [LocallyOfFiniteType g'] (n : ℤ)
    (hY' : schemeDeltaDimension C (g' ≫ sY) ≤ (n : EInt))
    (hX' : schemeDeltaDimension C (pullback.fst i (pullback.fst g g') ≫ sX) ≤
      (((n + (d : ℤ)) - (r : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C (pullback.fst (q ≫ i) (pullback.fst g g') ≫ sN)
        (by omega : (n + (d : ℤ)) - (0 : ℤ) = ((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))
        (E.cap (pullback.fst g g') (n + (d : ℤ))
          (fundamentalChowClass C (pullback.fst g g' ≫ sP) (n + (d : ℤ)))) =
      fundamentalChowClass C (pullback.fst (q ≫ i) (pullback.fst g g') ≫ sN)
        (((n + (d : ℤ)) - (r : ℤ)) + (r : ℤ))) :
    cf.cap g' n (fundamentalChowClass C (g' ≫ sY) n) =
      fundamentalChowClass C (pullback.fst (i ≫ g) g' ≫ sX) (n - ((r : ℤ) + -(d : ℤ))) := by
  refine lciGysinCap_fundamentalChowClass C G sX sP sY sN i hi g hg d hgd q hq r E NP hdesc hpp
    hRG h71 (fun t _ k => (hbij t k).1) ?_ hcf g' n hY' hX' hcone
  exact isVirtualNormalGysinClass_virtualNormalGysinClass C G sX sP sN i hi q hq r 0 E
    (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) NP hpp hbij hproper
    hflat hgysin

end Lci

end Stacks.Chow

end

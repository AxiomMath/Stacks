module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommutingField
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass

/-!
# Stacks 0FF7 on a fundamental class, for any class characterized by the rule of Stacks 0B78

The statements of
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass`, made
for an arbitrary bivariant class `cg ∈ A^{-d}(P ⟶ Y)` with
`Stacks.Chow.IsBivariantFlatPullback cg` in place of the class
`Stacks.Chow.flatPullbackBivariantClass` built from Stacks 02RG and 0B71. Only the cap operation of
the flat-pullback class enters the proofs, so the inputs of that construction are not needed: the
statements apply in particular to `Stacks.Chow.flatPullbackBivariantClassOfInvertible`, over the
Gysin system of an invertible module, with nothing assumed.

## Main results

* `Stacks.Chow.IsBivariantFlatPullback.cap_fundamentalChowClass` — the source's step
  `(g')^*[Y'] = [Y' ×_Y P]` in the proof of Stacks 0FF7.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass_of_isBivariantFlatPullback` — Stacks 0FF7 in the
  δ-equidimensional case, `f^![Y']_n = [X']`, for `f = i ≫ g` with `g` smooth.
* `Stacks.Chow.lciGysinCap_fundamentalChowClass_virtualNormalGysinClass_of_isBivariantFlatPullback`
  — the same with `i^!` the class `Stacks.Chow.virtualNormalGysinClass`.

## References

* [Stacks Project, Tag 0FF7](https://stacks.math.columbia.edu/tag/0FF7)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **The source's step `(g')^*[Y'] = [Y' ×_Y P]` in the proof of Stacks 0FF7.** A bivariant class
characterized by the rule of Stacks 0B78 for a flat morphism `g : P ⟶ Y` of relative dimension `d`
carries the fundamental class of a test scheme `Y'` of δ-dimension at most `n` to the fundamental
class of `P ×_Y Y'`, in the degree `n - (-d)` that a class of degree `-d` produces: this is
`Stacks.Chow.flatPullbackChow_fundamentalChowClass` read through
`Stacks.Chow.IsBivariantFlatPullback.cap_heq`. -/
theorem IsBivariantFlatPullback.cap_fundamentalChowClass {C : ChowSituation.{u}}
    {G : GysinSystem C} {P Y : Scheme.{u}} {sP : P ⟶ C.S} [LocallyOfFiniteType sP]
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {g : P ⟶ Y} [LocallyOfFiniteType g]
    [AlgebraicGeometry.Flat g] {hg : g ≫ sY = sP} {d : ℕ}
    {hgd : AlgebraicGeometry.RelativeDimension g d} {hdesc : FlatPullbackDescends C}
    {cg : BivariantClass C G sP sY g hg (-(d : ℤ))}
    (hcg : IsBivariantFlatPullback C G sP sY g hg d hgd hdesc cg)
    {Y' : Scheme.{u}} (g' : Y' ⟶ Y) [LocallyOfFiniteType g'] (n : ℤ)
    (hdim : schemeDeltaDimension C (g' ≫ sY) ≤ (n : EInt)) :
    cg.cap g' n (fundamentalChowClass C (g' ≫ sY) n) =
      fundamentalChowClass C (pullback.fst g g' ≫ sP) (n - -(d : ℤ)) := by
  have h1 := hcg.cap_heq g' n (fundamentalChowClass C (g' ≫ sY) n)
  rw [flatPullbackChow_fundamentalChowClass C (pullback.fst g g' ≫ sP) (g' ≫ sY)
    (pullback.snd g g') (pullbackSnd_comp_structureMorphism hg g') d
    (relativeDimension_pullbackSnd g hgd g') n _ hdim] at h1
  exact eq_of_heq (h1.trans (fundamentalChowClass_heq C _ (by ring)))

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
  (hpp : ProperPushforwardDescends C)
  {cg : BivariantClass C G sP sY g hg (-(d : ℤ))}
  (hcg : IsBivariantFlatPullback C G sP sY g hg d hgd hdesc cg)

include hcg in
/-- **Stacks 0FF7, the δ-equidimensional case, for any flat-pullback class.** Let `f = i ≫ g`
with `i : X ⟶ P` an immersion carrying a virtual normal bundle of constant rank `r` and
`g : P ⟶ Y` smooth of constant relative dimension `d`, let `cg` be a class characterized by the
rule of Stacks 0B78 for `g`, and let `g' : Y' ⟶ Y` be a test scheme of δ-dimension at most `n`.
If `ci` satisfies the characterizing relation of Stacks 0FBK for the virtual normal bundle of
`i`, `cf` is the composite `ci ∘ cg` of Stacks 0FE0, and `dim_δ(X ×_Y Y') ≤ n + d - r`, then
`f^![Y']_n = [X']_{n - (r + (-d))}`.

The proof is that of `Stacks.Chow.lciGysinCap_fundamentalChowClass`, with
`Stacks.Chow.IsBivariantFlatPullback.cap_fundamentalChowClass` for the smooth half. -/
theorem lciGysinCap_fundamentalChowClass_of_isBivariantFlatPullback
    (hinj : ∀ {T : Scheme.{u}} (t : T ⟶ P) [LocallyOfFiniteType t] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc t k))
    {ci : BivariantClass C G sX sP i hi (r : ℤ)}
    (hci : IsVirtualNormalGysinClass C G sX sP sN i hi q hq r 0 E
      (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) NP ci)
    {cf : BivariantClass C G sX sY (i ≫ g) (comp_comp_structureMorphism_eq hi hg)
      ((r : ℤ) + -(d : ℤ))}
    (hcf : IsBivariantClassComposition C G sX sP sY i g hi hg hpp (r : ℤ) (-(d : ℤ)) ci
      cg cf)
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
  -- The smooth half: `g^*[Y']_n = [P ×_Y Y']_{n - (-d)}`.
  have hsmooth := hcg.cap_fundamentalChowClass g' n hY'
  -- Stacks 0FBM at vanishing excess, in degree `n + d`.
  have hgysin := virtualNormalGysinCap_fundamentalChowClass C G sX sP sN i hi q hq r E NP hdesc
    hinj hci (pullback.fst g g') (n + (d : ℤ)) hX' hcone
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

include hcg in
/-- **Stacks 0FF7 for the class of Stacks 0FBK that this repository constructs, and any
flat-pullback class.** The same conclusion as
`Stacks.Chow.lciGysinCap_fundamentalChowClass_of_isBivariantFlatPullback`, with `ci` the class
`Stacks.Chow.virtualNormalGysinClass` and its characterizing relation discharged by
`Stacks.Chow.isVirtualNormalGysinClass_virtualNormalGysinClass`. -/
theorem lciGysinCap_fundamentalChowClass_virtualNormalGysinClass_of_isBivariantFlatPullback
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
      cg cf)
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
  have hinj : ∀ {T : Scheme.{u}} (t : T ⟶ P) [LocallyOfFiniteType t] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc t k) := by
    intro T t _ k
    exact (hbij t k).1
  refine lciGysinCap_fundamentalChowClass_of_isBivariantFlatPullback C G sX sP sY sN i hi g hg d
    hgd q hq r E NP hdesc hpp hcg hinj ?_ hcf g' n hY' hX' hcone
  exact isVirtualNormalGysinClass_virtualNormalGysinClass C G sX sP sN i hi q hq r 0 E
    (bundleFlatPullback C sX sN i q hq r NP.flat NP.relativeDimension hdesc) NP hpp hbij hproper
    hflat hgysin

end Lci

end Stacks.Chow

end

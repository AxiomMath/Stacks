module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor

/-!
# Flat pullback and a relative effective Cartier divisor

Let `X` and `Y` be locally of finite type over the base scheme of chapter 42 of the Stacks
Project, let `p : X ⟶ Y` be flat of relative dimension `r + 1`, and let `i : D ⟶ X` be a
relative effective Cartier divisor on `X/Y` (Stacks 062T) cut out as the zero scheme of a
section `s` of an invertible module `L`. For an integral closed subscheme `W ⊆ Y` of
delta-dimension `k + 1` the Gysin pullback of `p^*[W]` is the flat pullback of `[W]` to `D`:

  `i^* p^* [W]_{k+1} = (p|_D)^* [W]_{k+1}`  in  `A_{k+1+r}(D)`.

The source's argument is reproduced: `D ∩ p^{-1}W` is an effective Cartier divisor on `p^{-1}W`
because `D` is flat over `Y` (Stacks 056Q), so Stacks 02TB computes `i^* [p^{-1}W]` as the
fundamental cycle of that intersection, and `D ∩ p^{-1}W` and `(p|_D)^{-1}W` are the same closed
subscheme of `D` because `comap` is functorial.

## Main results

* `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_primeCycle` — **Stacks 02TR**, first
  equality, on the fundamental cycle of an integral closed subscheme.
* `Stacks.Chow.firstChernClassCapOfInvertible_flatPullback_primeCycle` — **Stacks 02TR**, second
  equality, in the same case, in the source's `c₁(L) ∩ −` form.
* `Stacks.Chow.effectiveCartierIntersectionOfInvertible_flatPullback_primeCycle` — **Stacks
  02TR**, second equality, in the same case, as intersection with `D` (Stacks 02T8); the
  `c₁` form above is one rewrite of it through Stacks 02T9.
* `Stacks.Chow.isEffectiveCartierDivisor_comap_comap_subschemeι` — Stacks 056Q read on the
  scheme-theoretic inverse image `p^{-1}W` presented as an ideal sheaf: the restriction of a
  relative effective Cartier divisor to `p^{-1}W` is an effective Cartier divisor there.
* `Stacks.Chow.schemeDeltaDimension_comap_le_of_relativeDimension` — Stacks 02RE part (1) in the
  same presentation.

## Implementation notes

### Two presentations of the inverse image

`Stacks.Chow.flatPullback_cycleAssociatedToClosedSubscheme` and
`Stacks.Chow.schemeDeltaDimension_pullback_le` present the inverse image of `W` as the
categorical pullback `X ×_Y W`, while the Gysin map of Stacks 02TB consumes a closed subscheme
given by an ideal sheaf. The two are matched by `Scheme.IdealSheafData.comapIso`, whose
compatibility `comapIso_inv_subschemeι` is exactly the hypothesis of
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_of_iso`; for delta-dimensions the comparison is
`Stacks.Chow.schemeDeltaDimension_eq_of_equal_ranges`, the two closed immersions having the same
range.

### The relative dimension of `D ⟶ Y` is a parameter here

Writing `(p|_D)^*` presupposes that `D ⟶ Y` is flat of relative dimension `r`. Flatness is part
of Definition 062T, but the relative dimension is not; it is carried here as the hypothesis `hq`.
It is a theorem — `AlgebraicGeometry.relativeDimension_of_isRelativeEffectiveCartierDivisor` in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierDivisorDimension` — and the
statements of Stacks 02TR that carry the tag unrestricted, in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullbackChow`, supply it from
there rather than assuming it.

### The divisor is presented by a section, so `ℒ` is `L` and not literally `𝒪_X(D)`

The source writes `ℒ = 𝒪_X(D)`. Here, as throughout this chapter's treatment of Stacks 02T8,
02TB and 02T9, the divisor is presented as the zero scheme `D = Z(s)` of a global section `s` of
an invertible module `L`, and the cap product is taken with `c₁(L)`. The two agree because `L` is
canonically `𝒪_X(D)` — `AlgebraicGeometry.invertibleSheafIsoZeroScheme` — and this is the same
generalization of the "in particular" clause of Stacks 02T9 that
`Stacks.Chow.effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible` makes.

### What of the tag is here

Both equalities of Stacks 02TR, and the second one in the source's `c₁` form, but only on the
fundamental cycle of a single integral closed subscheme — which is the case the source proves
before extending by linearity. The extension to every `(k+1)`-cycle reindexes a locally finite
sum over the points of `X` along the fibres of `p`; it is carried out in
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullbackChow`, which is where
the unrestricted `@[stacks 02TR]` sits.

### No unrestricted `@[stacks 02TR]`

Each attribute below carries a restriction string naming the part of the tag it covers: the
first or the second equality, each only on a fundamental cycle, and for the second equality also
whether it is read through `c₁(L) ∩ −` or through intersection with `D`. No declaration here
carries the bare tag.

## References

* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 056Q](https://stacks.math.columbia.edu/tag/056Q)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The inverse image of a closed subscheme as an ideal sheaf -/

/-- The inverse image of a closed subscheme, taken as an ideal sheaf, has the same range as the
first projection of the categorical pullback presenting it. -/
theorem range_comap_subschemeι_eq_range_pullbackFst {X Y : Scheme.{u}} (p : X ⟶ Y)
    (W : Y.IdealSheafData) :
    Set.range (W.comap p).subschemeι = Set.range (pullback.fst p W.subschemeι) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Pullback.range_fst,
    Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
  rfl

/-- The fundamental cycle of the inverse image of a closed subscheme, taken as an ideal sheaf, is
the fundamental cycle of the categorical pullback presenting it. -/
theorem cycleAssociatedToClosedSubscheme_pullbackFst_eq_comap (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : X ⟶ Y)
    (W : Y.IdealSheafData) (k : ℤ) :
    cycleAssociatedToClosedSubscheme C sX (pullback.fst p W.subschemeι) k =
      cycleAssociatedToClosedSubscheme C sX (W.comap p).subschemeι k :=
  cycleAssociatedToClosedSubscheme_eq_of_iso C sX (pullback.fst p W.subschemeι)
    (W.comap p).subschemeι (W.comapIso p).symm (W.comapIso_inv_subschemeι p) k

/-- **Stacks 02RE, part (1), in the ideal-sheaf presentation of the inverse image.** The
scheme-theoretic inverse image of a closed subscheme of delta-dimension at most `k` along a flat
morphism of relative dimension `r` has delta-dimension at most `k + r`. -/
theorem schemeDeltaDimension_comap_le_of_relativeDimension (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p]
    (hbase : p ≫ sY = sX) (r : ℕ) (hp : AlgebraicGeometry.RelativeDimension p r)
    (W : Y.IdealSheafData) (k : ℤ)
    (hW : schemeDeltaDimension C (W.subschemeι ≫ sY) ≤ (k : EInt)) :
    schemeDeltaDimension C ((W.comap p).subschemeι ≫ sX) ≤ ((k + (r : ℤ) : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_of_equal_ranges C sX (W.comap p).subschemeι
    (pullback.fst p W.subschemeι) (range_comap_subschemeι_eq_range_pullbackFst p W)]
  exact schemeDeltaDimension_pullback_le C sX sY p hbase r hp W.subschemeι k hW

/-- **Stacks 056Q on the inverse image of a closed subscheme.** The restriction of a relative
effective Cartier divisor on `X/Y` to the scheme-theoretic inverse image of a closed subscheme
`W ⊆ Y` is an effective Cartier divisor there. -/
theorem isEffectiveCartierDivisor_comap_comap_subschemeι {X Y : Scheme.{u}} (p : X ⟶ Y)
    (D : X.IdealSheafData) [Flat (D.subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) (W : Y.IdealSheafData) :
    Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (W.comap p).subschemeι) := by
  have hsnd : Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap (pullback.snd W.subschemeι p)) :=
    AlgebraicGeometry.isEffectiveCartierDivisor_comap_pullback p W.subschemeι D hD
  have hcomp : (W.comapIso p ≪≫ pullbackSymmetry p W.subschemeι).hom ≫
      pullback.snd W.subschemeι p = (W.comap p).subschemeι := by
    rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
      Scheme.IdealSheafData.comapIso_hom_fst]
  have hrw : D.comap (W.comap p).subschemeι =
      (D.comap (pullback.snd W.subschemeι p)).comap
        (W.comapIso p ≪≫ pullbackSymmetry p W.subschemeι).hom := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp]
  rw [hrw]
  exact Stacks.Divisors.isPullbackDefined_of_flat
    (W.comapIso p ≪≫ pullbackSymmetry p W.subschemeι).hom _ hsnd

/-! ### Stacks 02TR on an integral component -/

/-- **Stacks 02TR, first equality, on an integral component.** Let `p : X ⟶ Y` be flat of
relative dimension `r + 1` over the base scheme of chapter 42, let `i : D ⟶ X` be a relative
effective Cartier divisor on `X/Y` presented as the zero scheme of a section `s` of an invertible
module `L`, and let `W ⊆ Y` be an integral closed subscheme of delta-dimension `k + 1`. Then

  `i^* p^* [W]_{k+1} = (p|_D)^* [W]_{k+1}`  in  `A_{k+1+r}(D)`.

The relative dimension `hq` of `D ⟶ Y` is a parameter; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierFlatPullback`. The flatness of
`D ⟶ Y` is both the second conjunct of `hD` and an instance binder, because stating
`(p|_D)^*` needs it before `hD` is available. -/
@[stacks 02TR "first equality, on the fundamental cycle of an integral closed subscheme"]
theorem gysinHomomorphismOfInvertible_flatPullback_primeCycle
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) r)
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hWdim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1) :
    gysinHomomorphismOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1))) =
      QuotientAddGroup.mk
        (flatPullback C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r hq (k + 1)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1))) := by
  -- the flat pullback of `[W]` is the fundamental cycle of `p^{-1}W`
  have hin : (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
        (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)) :
          CycleGroup C sX (k + 1 + (r : ℤ) + 1)) =
      cycleAssociatedToClosedSubscheme C sX (W.comap p).subschemeι (k + 1 + (r : ℤ) + 1) := by
    refine Subtype.ext ((val_cycleGroup_cast C sX hcast _).trans ?_)
    rw [flatPullback_cycleAssociatedToClosedSubscheme C sX sY p hbase (r + 1) hp (k + 1)
      W.subschemeι hWdim, cycleAssociatedToClosedSubscheme_pullbackFst_eq_comap C sX p W, hcast]
  -- the dimension bound of Stacks 02RE
  have hZdim : schemeDeltaDimension C ((W.comap p).subschemeι ≫ sX) ≤
      ((k + 1 + (r : ℤ) + 1 : ℤ) : EInt) := by
    have h := schemeDeltaDimension_comap_le_of_relativeDimension C sX sY p hbase (r + 1) hp W
      (k + 1) hWdim.le
    rwa [hcast] at h
  -- the restriction of `D` to `p^{-1}W` is an effective Cartier divisor, by Stacks 056Q
  have hDZ := isEffectiveCartierDivisor_comap_comap_subschemeι p
    (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))) hD.1 W
  rw [hin, gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme C sX
    (k + 1 + (r : ℤ)) L s (W.comap p) hZdim hDZ,
    flatPullback_cycleAssociatedToClosedSubscheme C
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
      (by rw [Category.assoc, hbase]) r hq (k + 1) W.subschemeι hWdim,
    cycleAssociatedToClosedSubscheme_pullbackFst_eq_comap C
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) W,
    Scheme.IdealSheafData.comap_comp W
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι p]

/-- **Stacks 02TR, second equality, on an integral component, as intersection with `D`.** In the
situation of `Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_primeCycle`,

  `D · p^* [W]_{k+1} = i_* ((p|_D)^* [W]_{k+1})`  in  `A_{k+1+r}(X)`,

where `D · −` is intersection with the effective Cartier divisor `D` (Stacks 02T8). The source
writes the left side as `c₁(ℒ) ∩ p^* α`; that form is
`Stacks.Chow.firstChernClassCapOfInvertible_flatPullback_primeCycle` below, one rewrite of this
through Stacks 02T9. -/
@[stacks 02TR "second equality, as intersection with D, on a fundamental cycle"]
theorem effectiveCartierIntersectionOfInvertible_flatPullback_primeCycle
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) r)
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hWdim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1) :
    effectiveCartierIntersectionOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤)) hD.1
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1))) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX rfl
          (k + 1 + (r : ℤ)))
        (QuotientAddGroup.mk
          (flatPullback C
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
            (by rw [Category.assoc, hbase]) r hq (k + 1)
            (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)))) := by
  refine (effectiveCartierIntersectionOfInvertible_apply C sX (k + 1 + (r : ℤ)) L
    (s.eval (.op ⊤)) hD.1 _).trans (congrArg _
      (gysinHomomorphismOfInvertible_flatPullback_primeCycle C sX sY p hbase
        r hp k L s hD hq W hWint hWdim hcast))

/-- **Stacks 02TR, second equality, on an integral component.** In the situation of
`Stacks.Chow.gysinHomomorphismOfInvertible_flatPullback_primeCycle`,

  `c₁(L) ∩ p^* [W]_{k+1} = i_* ((p|_D)^* [W]_{k+1})`  in  `A_{k+1+r}(X)`,

the source's second equality: the left side is the cap product of Stacks 02SO and `L` is
canonically `𝒪_X(D)`, the divisor being the zero scheme of `s`.

This is `Stacks.Chow.effectiveCartierIntersectionOfInvertible_flatPullback_primeCycle` read
through Stacks 02T9, in the form
`Stacks.Chow.effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible`. -/
@[stacks 02TR "second equality, in the c₁(L) ∩ − form, on a fundamental cycle"]
theorem firstChernClassCapOfInvertible_flatPullback_primeCycle
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) r)
    (W : Y.IdealSheafData) (hWint : IsIntegral W.subscheme)
    (hWdim : schemeDeltaDimension C (W.subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt))
    (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1) :
    firstChernClassCapOfInvertible C sX (k + 1 + (r : ℤ)) L
        (hcast ▸ flatPullback C sX sY p hbase (r + 1) hp (k + 1)
          (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1))) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX rfl
          (k + 1 + (r : ℤ)))
        (QuotientAddGroup.mk
          (flatPullback C
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
            ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
            (by rw [Category.assoc, hbase]) r hq (k + 1)
            (cycleAssociatedToClosedSubscheme C sY W.subschemeι (k + 1)))) :=
  (effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible C sX
      (k + 1 + (r : ℤ)) L (s.eval (.op ⊤)) hD.1 _).symm.trans
    (effectiveCartierIntersectionOfInvertible_flatPullback_primeCycle C sX sY p hbase r hp k L s
      hD hq W hWint hWdim hcast)

end Stacks.Chow

end

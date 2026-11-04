module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Composition of flat pullbacks of cycles

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X`, `Y` and `Z`
be schemes locally of finite type over `S` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be flat of
relative dimensions `r` and `s`. Stacks 02RD asserts three things: that `g ∘ f` is flat, that it
has relative dimension `r + s`, and that

  `f^* ∘ g^* = (g ∘ f)^*`   as maps `Z_k(Z) ⟶ Z_{k+r+s}(X)`.

The first is Mathlib's `AlgebraicGeometry.Flat.comp` and the second is Stacks 02NL,
`AlgebraicGeometry.RelativeDimension.comp_of_flat`; both are recorded against this tag below.
The third is `Stacks.Chow.flatPullback_comp`.

## Main results

* `Stacks.Chow.flatPullbackWeight_comp` — the flat pullback multiplicities are multiplicative
  along a composition, which is where the mathematics of the tag sits.
* `Stacks.Chow.flatPullback_comp_apply` — the identity of the tag, coefficientwise at a point.
* `Stacks.Chow.flatPullback_comp` — **Stacks 02RD**: the identity of the tag.

## Implementation notes

Composition is written in categorical order, so `f ≫ g` is the morphism called `g ∘ f` in the
source, and the three morphisms to the base satisfy `f ≫ sY = sX` and `g ≫ sZ = sY`.

The source reduces to three nested integral closed subschemes `W ⊆ Z`, `W' ⊆ g^{-1}(W)` and
`W'' ⊆ f^{-1}(W')` of delta-dimensions `k`, `k + s` and `k + s + r`, and then compares two
multiplicities at their generic points. In the coefficientwise formulation of flat pullback used
here that reduction is not needed: the three multiplicities being compared are already
`Stacks.Chow.flatPullbackWeight`s at one point `x` of `X`, and the only case distinction left is
whether `x` has the relative dimension that the pullback of a `k`-cycle can occupy.

* If it does not, then the multiplicity along `f` and the multiplicity along `f ≫ g` both vanish
  outright, because the relative dimension of `x` is part of the condition defining a
  multiplicity (`Stacks.Chow.flatPullbackWeight_eq_zero_of_relativeDimension_ne`), and both
  sides of the identity are zero.
* If it does, then the relative dimension of `f x` is forced to be `k + s`. This replaces the
  reduction of the source: along a morphism of relative dimension at most `r` the relative
  dimension grows by the transcendence degree of the residue field extension, which is at most
  `r` (`Stacks.Chow.toNat_residueTrdeg_le_of_relativeDimension`), so the growth `r + s` across
  `f` and then `g` can only be `r` and then `s`. With the three relative dimensions known,
  Stacks 02QT (`Stacks.Chow.exists_genericPoints_comap_integralComponentAt`) supplies the three
  generic points, each multiplicity becomes a colength of an extended maximal ideal of stalks
  (`Stacks.Chow.flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal`), and the identity is
  Stacks 02M2 for the flat local ring maps `𝒪_{Z, g f x} → 𝒪_{Y, f x} → 𝒪_{X, x}`.

The final statement transports the left hand side along the equality `(k + s) + r = k + (r + s)`
of delta-dimensions, which is the degree the pullback along `f ≫ g` produces; that equality is
taken as a hypothesis so that the statement typechecks, exactly as in
`Stacks.Chow.flatPullback_gysinRule_extendCycleGroup`.

## References

* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02NL](https://stacks.math.columbia.edu/tag/02NL)
* [Stacks Project, Tag 02M2](https://stacks.math.columbia.edu/tag/02M2)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Multiplicativity of the flat pullback multiplicity -/

/-- The flat pullback multiplicity in degree `j` vanishes at a point of relative dimension other
than `j`: that relative dimension is part of the condition defining the multiplicity. -/
theorem flatPullbackWeight_eq_zero_of_relativeDimension_ne (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X ⟶ Y) (j : ℤ) (x : X)
    (hdim : relativeDimension C.dimensionFunction sX x ≠ j) :
    flatPullbackWeight C sX f j x = 0 := by
  classical
  unfold flatPullbackWeight closedSubschemeCycleCoeff
  rw [dite_eq_right_iff]
  rintro ⟨-, -, hj⟩
  exact absurd hj hdim

/-- Along `f` of relative dimension `r` followed by `g` of relative dimension `s`, a point whose
relative dimension exceeds that of its image under the composition by exactly `r + s` has its
image under `f` of relative dimension exactly `s` more than that image.

Relative dimension grows along a morphism by the transcendence degree of the residue field
extension, and that degree is at most the relative dimension of the morphism; so a total growth
of `r + s` across the two steps leaves no slack in either. -/
theorem relativeDimension_map_of_relativeDimension_comp_eq (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (g : Y ⟶ Z) [LocallyOfFiniteType g]
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (r s : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (x : X)
    (hdim : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sZ (g.base (f.base x)) + (s : ℤ) + (r : ℤ)) :
    relativeDimension C.dimensionFunction sY (f.base x) =
      relativeDimension C.dimensionFunction sZ (g.base (f.base x)) + (s : ℤ) := by
  have hstepf := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sY f x
  have hstepg := relativeDimension_comp_eq_add_trdeg C.dimensionFunction sZ g (f.base x)
  rw [hfbase] at hstepf
  rw [hgbase] at hstepg
  have htf := toNat_residueTrdeg_le_of_relativeDimension f r hf x
  have htg := toNat_residueTrdeg_le_of_relativeDimension g s hg (f.base x)
  omega

/-- The flat pullback multiplicities are multiplicative along a composition of flat morphisms:
at a point `x` of `X` lying over a point of relative dimension `k` of `Z`, the multiplicity
along `g` at `f x` times the multiplicity along `f` at `x` is the multiplicity along `f ≫ g` at
`x`.

Off relative dimension `k + s + r` both sides vanish. On it, the three multiplicities are the
colengths of the extended maximal ideals of the flat local ring maps
`𝒪_{Z, g f x} → 𝒪_{Y, f x} → 𝒪_{X, x}`, and the identity is Stacks 02M2. -/
theorem flatPullbackWeight_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (k : ℤ) (x : X)
    (hk : relativeDimension C.dimensionFunction sZ (g.base (f.base x)) = k) :
    flatPullbackWeight C sY g (k + (s : ℤ)) (f.base x) *
        flatPullbackWeight C sX f (k + (s : ℤ) + (r : ℤ)) x =
      flatPullbackWeight C sX (f ≫ g) (k + ((r + s : ℕ) : ℤ)) x := by
  have hbasec : (f ≫ g) ≫ sZ = sX := by rw [Category.assoc, hgbase, hfbase]
  have hcomp : AlgebraicGeometry.RelativeDimension (f ≫ g) (r + s) :=
    AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg
  have hpt : (f ≫ g).base x = g.base (f.base x) := rfl
  have hcast : k + (s : ℤ) + (r : ℤ) = k + ((r + s : ℕ) : ℤ) := by push_cast; ring
  by_cases hdim : relativeDimension C.dimensionFunction sX x = k + (s : ℤ) + (r : ℤ)
  · -- The point contributes: all three multiplicities are colengths, and 02M2 multiplies them.
    have hdimc : relativeDimension C.dimensionFunction sX x = k + ((r + s : ℕ) : ℤ) :=
      hdim.trans hcast
    have hy : relativeDimension C.dimensionFunction sY (f.base x) = k + (s : ℤ) := by
      rw [← hk]
      exact relativeDimension_map_of_relativeDimension_comp_eq C sX sY sZ f g hfbase hgbase r s
        hf hg x (by rw [hdim, hk])
    have hexg : ∃ η : genericPoints
        ((integralComponentAt (g.base (f.base x))).comap g).subscheme,
        ((integralComponentAt (g.base (f.base x))).comap g).subschemeι.base η.1 = f.base x :=
      exists_genericPoints_comap_integralComponentAt C sY sZ g hgbase s hg (f.base x)
        (by rw [hy, hk])
    have hexf : ∃ ζ : genericPoints ((integralComponentAt (f.base x)).comap f).subscheme,
        ((integralComponentAt (f.base x)).comap f).subschemeι.base ζ.1 = x :=
      exists_genericPoints_comap_integralComponentAt C sX sY f hfbase r hf x
        (by rw [hdim, hy])
    have hexc : ∃ ξ : genericPoints
        ((integralComponentAt ((f ≫ g).base x)).comap (f ≫ g)).subscheme,
        ((integralComponentAt ((f ≫ g).base x)).comap (f ≫ g)).subschemeι.base ξ.1 = x :=
      exists_genericPoints_comap_integralComponentAt C sX sZ (f ≫ g) hbasec (r + s) hcomp x
        (by rw [hdimc, ← hk]; rfl)
    rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sY g (k + (s : ℤ))
        (f.base x) hexg hy,
      flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX f
        (k + (s : ℤ) + (r : ℤ)) x hexf hdim,
      flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX (f ≫ g)
        (k + ((r + s : ℕ) : ℤ)) x hexc hdimc]
    have hlen := length_quotient_maximalIdeal_map_mul_eq
      (g.stalkMap (f.base x)).hom (f.stalkMap x).hom inferInstance inferInstance
      (AlgebraicGeometry.Flat.stalkMap g (f.base x)) (AlgebraicGeometry.Flat.stalkMap f x)
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp] at hlen
    have hnat := congrArg (fun n : ℕ∞ ↦ ((n.toNat : ℕ) : ℤ)) hlen
    rwa [ENat.toNat_mul, Nat.cast_mul] at hnat
  · -- The point cannot contribute: the multiplicities along `f` and along `f ≫ g` both vanish.
    rw [flatPullbackWeight_eq_zero_of_relativeDimension_ne C sX f _ x hdim,
      flatPullbackWeight_eq_zero_of_relativeDimension_ne C sX (f ≫ g) _ x
        fun h ↦ hdim (h.trans hcast.symm), mul_zero]

/-! ### Stacks 02RD -/

add_to_stacks 02RD "flatness of the composite" AlgebraicGeometry.Flat.comp
add_to_sga "3 VIIB 1.3.3" "(i), special case" AlgebraicGeometry.Flat.comp
add_to_ega "0 6.7.5" "Schemes (EGA preschemes)" AlgebraicGeometry.Flat.comp
add_to_ega "IV 2.1.5" "global case Y' = Y" AlgebraicGeometry.Flat.comp
add_to_ega "IV 2.1.6" AlgebraicGeometry.Flat.comp
add_to_ega "IV 2.2.11" "(iii), special case" AlgebraicGeometry.Flat.comp
add_to_ega "IV 2.2.13" "(iii)" AlgebraicGeometry.Flat.comp
add_to_ega "IV 6.6.1" "(i): flatness of h = g∘f" AlgebraicGeometry.Flat.comp
add_to_ega "IV 7.3.5" "partial" AlgebraicGeometry.Flat.comp
add_to_stacks 02RD "relative dimension of the composite"
  AlgebraicGeometry.RelativeDimension.comp_of_flat

/-- **Stacks 02RD, coefficientwise.** Flat pullback of cycles is compatible with composition,
read off at a single point of `X`.

At a point where the cycle's coefficient below vanishes both sides vanish; elsewhere the
coefficient below pins down the relative dimension of `g f x`, and
`Stacks.Chow.flatPullbackWeight_comp` multiplies the two multiplicities. -/
theorem flatPullback_comp_apply (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (k : ℤ) (c : CycleGroup C sZ k) (x : X) :
    (flatPullback C sX sY f hfbase r hf (k + (s : ℤ))
          (flatPullback C sY sZ g hgbase s hg k c)).1 x =
      (flatPullback C sX sZ (f ≫ g) (by rw [Category.assoc, hgbase, hfbase]) (r + s)
        (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg) k c).1 x := by
  have hpt : (f ≫ g).base x = g.base (f.base x) := rfl
  rw [flatPullback_apply, flatPullback_apply, flatPullback_apply, hpt]
  by_cases hc : c.1 (g.base (f.base x)) = 0
  · rw [hc, zero_mul, zero_mul, zero_mul]
  · have hk : relativeDimension C.dimensionFunction sZ (g.base (f.base x)) = k :=
      (mem_cyclesOfDimension_iff_forall_point C sZ k c.1).1 c.2 _ hc
    rw [mul_assoc, flatPullbackWeight_comp C sX sY sZ f g hfbase hgbase r s hf hg k x hk]

/-- **Stacks 02RD.** For flat morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of relative dimensions `r`
and `s`, flat pullback of cycles satisfies `f^* ∘ g^* = (g ∘ f)^*` as maps
`Z_k(Z) ⟶ Z_{k+r+s}(X)`.

That `f ≫ g` is flat is `AlgebraicGeometry.Flat.comp` and that it has relative dimension
`r + s` is Stacks 02NL, `AlgebraicGeometry.RelativeDimension.comp_of_flat`; both are recorded
against this tag in this file. -/
@[stacks 02RD "composition of flat pullbacks"]
theorem flatPullback_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g] (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY)
    (r s : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (k : ℤ)
    (hcast : k + (s : ℤ) + (r : ℤ) = k + ((r + s : ℕ) : ℤ)) (c : CycleGroup C sZ k) :
    (hcast ▸ flatPullback C sX sY f hfbase r hf (k + (s : ℤ))
          (flatPullback C sY sZ g hgbase s hg k c) :
        CycleGroup C sX (k + ((r + s : ℕ) : ℤ))) =
      flatPullback C sX sZ (f ≫ g) (by rw [Category.assoc, hgbase, hfbase]) (r + s)
        (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg) k c := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [val_cycleGroup_cast C sX hcast]
  exact flatPullback_comp_apply C sX sY sZ f g hfbase hgbase r s hf hg k c x

end Stacks.Chow

end

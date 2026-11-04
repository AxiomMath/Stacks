module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a fibre of a finite locally free morphism

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
schemes locally of finite type over `S` and let `f : X ⟶ Y` be finite locally free of degree `d`.
`Stacks.Chow.properPushforward_flatPullback` reduces the push-pull identity `f_* f^* α = d α` of
Stacks 02RH to a single statement about one fibre, `Stacks.Chow.FibreDegreeIsRank`: that above a
point of relative dimension `k` the flat pullback multiplicities, weighted by the residue degrees
of the points of the fibre, sum to `d`. This file proves that statement, so the identity of
Stacks 02RH becomes unconditional.

## Main results

* `Stacks.Chow.fibreDegreeIsRank_of_isFiniteLocallyFreeOfRank` — the fibre-degree statement
  `Stacks.Chow.FibreDegreeIsRank` holds for a morphism finite locally free of rank `d`.
* `Stacks.Chow.properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank` — **Stacks 02RH, the
  second assertion**, with no hypothesis beyond `f` being finite locally free of rank `d`.

## Implementation notes

The fibre sum is already proved, in a different spelling, by
`AlgebraicGeometry.separableDegreeWeightedFiberSum_flatQuasiFiniteWeight`: for a finite flat
morphism the fibre sum of `AlgebraicGeometry.flatQuasiFiniteWeight`, each term weighted by the
separable degree of its residue-field extension, is `AlgebraicGeometry.Scheme.Hom.finrank`. Three
rewritings turn that into the statement wanted here.

* The weight. `AlgebraicGeometry.flatQuasiFiniteWeight f x` is the length of
  `𝒪_{X, x} / 𝔪_{f x} 𝒪_{X, x}` times the *inseparable* degree of `κ(x)/κ(f x)`, and
  `Stacks.Chow.flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal` says the flat pullback
  multiplicity is that same length. So the two weights differ by the inseparable degree, and the
  inseparable degree times the separable degree is `[κ(x) : κ(f x)]`, which is the residue degree
  this file sums against: `Field.finSepDegree_mul_finInsepDegree`.

* The side conditions of that length identity. It wants the point to carry relative dimension
  equal to the index of the cycle group, and to be the image of a generic point of the
  scheme-theoretic inverse image of the reduced closure of its image. The first is
  `Stacks.Chow.relativeDimension_eq_of_relativeDimension_zero`, relative dimension being
  unchanged along a morphism of relative dimension zero; the second is then
  `Stacks.Chow.exists_genericPoints_comap_integralComponentAt`.

* The shape of the sum. `AlgebraicGeometry.separableDegreeWeightedFiberSum` is a sum over the
  whole source of a function supported on the fibre, and `Stacks.Chow.FibreDegreeIsRank` is a sum
  over the fibre; `finsum_mem_def` identifies the two, the indicator of the fibre being the
  case distinction of the former.

* The rank. `Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq` turns finite local
  freeness of rank `d` into the rank function being constantly `d`, which is the right-hand side
  of the fibre sum.

## References

* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
* [Stacks Project, Tag 0397](https://stacks.math.columbia.edu/tag/0397)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- **The degree of a fibre of a finite locally free morphism.** For `f : X ⟶ Y` finite locally
free of rank `d` over the base, the flat pullback multiplicities on the fibre above a point of
relative dimension `k`, weighted by the residue degrees of the points of that fibre, sum to `d`.

This is `Stacks.Chow.FibreDegreeIsRank`, the one statement that
`Stacks.Chow.properPushforward_flatPullback` carries as a hypothesis, and with it the identity
of Stacks 02RH is unconditional. -/
theorem fibreDegreeIsRank_of_isFiniteLocallyFreeOfRank (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (hbase : f ≫ sY = sX) (k : ℤ) :
    FibreDegreeIsRank C sX sY f d k := by
  classical
  have hlft : LocallyOfFiniteType f :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank f d
  have hflat : Flat f := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank f d
  have hfin : IsFinite f := Stacks.Morphisms.isFinite_of_isFiniteLocallyFreeOfRank f d
  have hf0 : AlgebraicGeometry.RelativeDimension f 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank f d
  have hlqf : LocallyQuasiFinite f := (locallyQuasiFinite_iff_relativeDimension_zero f).2 hf0
  intro y hy
  have hrank : f.finrank y = d :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq f d).1 inferInstance y
  have hsum := congrFun (separableDegreeWeightedFiberSum_flatQuasiFiniteWeight f) y
  rw [hrank] at hsum
  rw [← hsum, finsum_mem_def]
  refine finsum_congr fun x ↦ ?_
  by_cases hx : f.base x = y
  · have hxmem : x ∈ f.base ⁻¹' {y} := hx
    have hdimY : relativeDimension C.dimensionFunction sY (f.base x) = k := by
      rw [hx]; exact hy
    have hdimX : relativeDimension C.dimensionFunction sX x = k :=
      (relativeDimension_eq_of_relativeDimension_zero C sX sY f hbase hf0 x).trans hdimY
    have hdimcast : relativeDimension C.dimensionFunction sX x = k + ((0 : ℕ) : ℤ) := by
      rw [hdimX]; simp
    have hex : ∃ ξ : genericPoints ((integralComponentAt (f.base x)).comap f).subscheme,
        ((integralComponentAt (f.base x)).comap f).subschemeι.base ξ.1 = x :=
      exists_genericPoints_comap_integralComponentAt C sX sY f hbase 0 hf0 x
        (by rw [hdimX, hdimY]; simp)
    have hweight := flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sX f
      (k + ((0 : ℕ) : ℤ)) x hex hdimcast
    let _ : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    have hdeg : (f.residueDegree x : ℤ) =
        (Field.finSepDegree (Y.residueField (f.base x)) (X.residueField x) : ℤ) *
          (Field.finInsepDegree (Y.residueField (f.base x)) (X.residueField x) : ℤ) := by
      rw [← Nat.cast_mul, Field.finSepDegree_mul_finInsepDegree]
      rfl
    rw [Set.indicator_of_mem hxmem, ite_eq_left hx, hweight, hdeg, flatQuasiFiniteWeight]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ f.base ⁻¹' {y} from hx), ite_eq_right hx]

/-- **Stacks 02RH, the second assertion.** For `f : X ⟶ Y` finite locally free of degree `d` over
the base,

  `f_* f^* α = d α`   in `Z_k(Y)`.

The statement transports the left hand side along the equality `k + 0 = k` of delta-dimensions,
which is the degree that pullback and pushforward along `f` produce; that equality is taken as a
hypothesis so that the statement typechecks, exactly as in
`Stacks.Chow.properPushforward_flatPullback`.

This is `Stacks.Chow.properPushforward_flatPullback` with its fibre-degree hypothesis discharged
by `Stacks.Chow.fibreDegreeIsRank_of_isFiniteLocallyFreeOfRank`. -/
@[stacks 02RH "push-pull formula"]
theorem properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] (hbase : f ≫ sY = sX) (k : ℤ)
    (hcast : k + ((0 : ℕ) : ℤ) = k) (α : CycleGroup C sY k) :
    letI : LocallyOfFiniteType f :=
      Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank f d
    letI : Flat f := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank f d
    letI : IsProper f := Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank f d
    (hcast ▸ properPushforward C sX sY f hbase (k + ((0 : ℕ) : ℤ))
          (flatPullback C sX sY f hbase 0
            (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank f d) k α) :
        CycleGroup C sY k) = (d : ℤ) • α := by
  have hlft : LocallyOfFiniteType f :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank f d
  have hflat : Flat f := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank f d
  have hproper : IsProper f := Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank f d
  exact properPushforward_flatPullback C sX sY f hbase
    (Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank f d) d k
    (fibreDegreeIsRank_of_isFiniteLocallyFreeOfRank C sX sY f d hbase k) hcast α

end Stacks.Chow

end

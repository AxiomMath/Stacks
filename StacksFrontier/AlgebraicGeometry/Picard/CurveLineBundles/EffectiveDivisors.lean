module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinZeroSectionDischarge
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.Divisors.IntegralDivisorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Picard.DegreeAtLeastGenus
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree

/-!
# Classes of effective divisors in the Picard group of a curve

Let `k` be an algebraically closed field and `X` a proper curve over `k` of genus `g`, with
Picard group `Pic(X) = Stacks.Picard.ofScheme X` and degree `deg : Pic(X) ⟶ ℤ`
(`Stacks.Picard.ofSchemeDegree`). For an effective Cartier divisor `D` on `X` write `[D]` for the
class of `𝒪_X(D)` (`Stacks.Divisors.picardClass`). This file proves:

* `deg [D]` is the degree of `D` over `k`, the rank of the finite locally free morphism
  `D ⟶ Spec k`;
* the class of a `k`-rational point has degree one, with no smoothness assumption (the
  surjectivity of `deg` for a smooth curve is `Stacks.Picard.surjective_ofSchemeDegree`);
* every class of degree `d ≥ g` is `[D]` for an effective Cartier divisor of degree `d`: on
  `k`-points the Abel map `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` is onto for `d ≥ g`;
* every class of degree zero is `[D] - [D']` for effective Cartier divisors `D`, `D'` of degree
  `g`.

The third statement is
`AlgebraicGeometry.exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree` read on
classes: an invertible module of degree at least the genus has a nonzero section, by Riemann-Roch,
and is the sheaf of the zero scheme of that section. The fourth follows from the third: adding `g`
times the class of a point to a class of degree zero gives a class of degree `g`.

## Main results

* `Stacks.Picard.ofSchemeDegree_divisorPicardClass`: `deg [D]` is the degree of `D`.
* `Stacks.Picard.exists_isEffectiveCartierDivisor_ofSchemeDegree_divisorPicardClass_eq_one`: a
  `k`-rational point is an effective divisor of degree one.
* `Stacks.Picard.exists_eq_picardClass_of_genus_le_ofSchemeDegree`: classes of degree at least
  `g` are effective.
* `Stacks.Picard.exists_eq_sub_of_mem_ofSchemeDegreeZero`: classes of degree zero are
  differences of effective classes of degree `g`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.RingedSpace (structureIsSheaf)
open Stacks.Divisors (IsEffectiveCartierDivisor invertibleSheaf' divisorSheaf
  divisorSheafGlobalSection canonicalSection')

universe u

namespace Stacks.Picard

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The canonical section of `𝒪_X(D)` is nonzero on an integral scheme: its zero scheme is `D`,
which is not the zero ideal sheaf. Alias of
`AlgebraicGeometry.divisorSheafGlobalSection_ne_zero`. -/
private alias divisorSheafGlobalSection_ne_zero' :=
  AlgebraicGeometry.divisorSheafGlobalSection_ne_zero

/-- **The degree of the class of an effective Cartier divisor is the degree of the divisor**: on
a proper integral scheme of dimension at most one over `k`, `deg [D] = dim_k Γ(D, 𝒪_D)`, which is
the rank of the finite locally free morphism `D ⟶ Spec k`
(`AlgebraicGeometry.isFiniteLocallyFreeOfRank_divisorSubscheme`). -/
theorem ofSchemeDegree_divisorPicardClass [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    ofSchemeDegree k f hdim (Stacks.Divisors.picardClass D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) :=
  (ofSchemeDegree_picardClass k f hdim (invertibleSheaf' D)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard D)).trans
    (@invertibleCurveDegree_eq_finrank_globalSections_zeroScheme k _ X f _ hdim _
      (divisorSheaf D) (Stacks.Divisors.isInvertible_divisorSheaf D) (canonicalSection' D)
      (divisorSheafGlobalSection_ne_zero' D) D (Stacks.Divisors.zeroScheme_canonicalSection D))

/-- **A `k`-rational point has degree one**: on a proper curve over an algebraically closed field
there is an effective Cartier divisor, the reduced subscheme on a closed point at which `X` is
smooth ([Stacks, Tag 0B8Y]), finite locally free of rank one over `k`, whose class has degree
one. No smoothness of `X` is assumed: a curve over a perfect field is smooth at some closed
point. -/
theorem exists_isEffectiveCartierDivisor_ofSchemeDegree_divisorPicardClass_eq_one [IsAlgClosed k]
    [IsProper f] [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (D : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) 1 ∧
        ofSchemeDegree k f hdim (Stacks.Divisors.picardClass D) = 1 := by
  obtain ⟨y, -, hys, hyc⟩ :=
    exists_closedPoint_smoothAt_mem k f isOpen_univ Set.univ_nonempty
  let D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
  have hD : IsEffectiveCartierDivisor D :=
    isEffectiveCartierDivisor_vanishingIdeal_of_smoothAt k f hyc hys
  have : IsIntegral D.subscheme := isIntegral_subscheme_vanishingIdeal hyc
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have hone : Module.finrank k Γ(D.subscheme, ⊤) = 1 :=
    finrank_globalSections_eq_one k (D.subschemeι ≫ f)
  have hrank := isFiniteLocallyFreeOfRank_divisorSubscheme k f hdim D
  rw [hone] at hrank
  refine ⟨D, hD, hrank, ?_⟩
  rw [ofSchemeDegree_divisorPicardClass k f hdim D, hone, Nat.cast_one]

/-- **A class of degree at least the genus is the class of an effective divisor**: on a proper
curve of genus `g` over an algebraically closed field, every `x ∈ Pic(X)` with `deg x ≥ g` is
`[D]` for an effective Cartier divisor `D` that is finite locally free of rank `deg x` over `k`.

This is the surjectivity on `k`-points of the Abel map `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}` for
`d ≥ g` of clause (5) of [Stacks, Tag 0BA0], read on the classes of `Pic(X)`: it is
`AlgebraicGeometry.exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree` applied to
a representative of `x`. -/
theorem exists_eq_picardClass_of_genus_le_ofSchemeDegree [IsAlgClosed k] [IsProper f]
    [IsCurve k f] (hdim : topologicalKrullDim X ≤ 1) (x : ofScheme X)
    (hx : (genus f : ℤ) ≤ ofSchemeDegree k f hdim x) :
    ∃ (D : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D) (d : ℕ),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) d ∧
        (d : ℤ) = ofSchemeDegree k f hdim x ∧ x = Stacks.Divisors.picardClass D := by
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed k f
  set L := (picardRepresentative X.toRingedSpace x).obj
  let hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    isInvertible_ringCatSheaf_of_isInvertible L (picardRepresentative X.toRingedSpace x).property
  have hdegx : ofSchemeDegree k f hdim x = invertibleCurveDegree k f hdim L := rfl
  obtain ⟨D, d, hD, ⟨e⟩, hrank, hd⟩ :=
    exists_isEffectiveCartierDivisor_of_genus_le_invertibleCurveDegree k f hdim L
      (hdegx ▸ hx)
  refine ⟨D, hD, d, hrank, hd.trans hdegx.symm, ?_⟩
  rw [← classOf_picardRepresentative X.toRingedSpace x]
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩

/-- **A class of degree zero is a difference of two effective classes of degree `g`**: on a
proper curve of genus `g` over an algebraically closed field, every `x ∈ Pic⁰(X)` is
`[D] - [D']` for effective Cartier divisors `D`, `D'` that are finite locally free of rank `g`
over `k`.

Let `y` be `g` times the class of a `k`-rational point; then `y` and `x + y` both
have degree `g`, so both are effective by
`Stacks.Picard.exists_eq_picardClass_of_genus_le_ofSchemeDegree`. -/
theorem exists_eq_sub_of_mem_ofSchemeDegreeZero [IsAlgClosed k] [IsProper f] [IsCurve k f]
    (hdim : topologicalKrullDim X ≤ 1) (x : ofScheme X) (hx : x ∈ ofSchemeDegreeZero k f hdim) :
    ∃ (D D' : X.IdealSheafData) (_ : IsEffectiveCartierDivisor D)
      (_ : IsEffectiveCartierDivisor D'),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) (genus f) ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D'.subschemeι ≫ f) (genus f) ∧
          x = Stacks.Divisors.picardClass D - Stacks.Divisors.picardClass D' := by
  have hx0 : ofSchemeDegree k f hdim x = 0 := hx
  obtain ⟨P, _, -, hP⟩ :=
    exists_isEffectiveCartierDivisor_ofSchemeDegree_divisorPicardClass_eq_one k f hdim
  set y := (genus f : ℤ) • Stacks.Divisors.picardClass P
  have hy : ofSchemeDegree k f hdim y = genus f := by
    rw [map_zsmul, hP, smul_eq_mul, mul_one]
  obtain ⟨D', hD', d', hrank', hd', hy'⟩ :=
    exists_eq_picardClass_of_genus_le_ofSchemeDegree k f hdim y hy.ge
  have hxy : ofSchemeDegree k f hdim (x + y) = genus f := by rw [map_add, hx0, hy, zero_add]
  obtain ⟨D, hD, d, hrank, hd, hxy'⟩ :=
    exists_eq_picardClass_of_genus_le_ofSchemeDegree k f hdim (x + y) hxy.ge
  obtain rfl : d' = genus f := by exact_mod_cast hd'.trans hy
  obtain rfl : d = genus f := by exact_mod_cast hd.trans hxy
  refine ⟨D, D', hD, hD', hrank, hrank', ?_⟩
  rw [← hxy', ← hy', add_sub_cancel_right]

end Stacks.Picard

end

module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.RingTheory.Etale.StandardEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard tamely ramified morphisms

Given a ring `A`, an element `f : A` and a natural number `e`, the standard tamely ramified
algebra is `A[X] / (X ^ e - f)`. Its spectrum maps canonically to `Spec(A)`, and localizing both
rings away from `f` gives the associated cover. That cover is étale as soon as `e` is positive
and invertible in `A`.

## Main definitions

* `AlgebraicGeometry.standardTamelyRamifiedAlgebra` is the quotient `A[X] / (X ^ e - f)`.
* `AlgebraicGeometry.standardTamelyRamifiedMorphism` is its canonical morphism to `Spec(A)`.
* `AlgebraicGeometry.standardTamelyRamifiedCover` is the induced morphism after localizing away
  from `f`.

## Main results

* `AlgebraicGeometry.standardTamelyRamifiedCover_etale` states étaleness of the standard cover
  after inverting `f`.
* `AlgebraicGeometry.standardTamelyRamifiedCover_isFinite` states finiteness of that cover,
  which together with étaleness is the assertion of the tag that `Spec(C_f) ⟶ Spec(A_f)` is a
  finite étale morphism.

## Implementation notes

The algebra and both spectrum morphisms are abbreviations, so the existing APIs for polynomial
quotients, localizations and affine schemes apply directly. The construction makes sense without
the Noetherian, reducedness, nonzerodivisor, positivity and invertibility assumptions; those
assumptions characterize the situation in which the construction is used as a standard tamely
ramified morphism and occur in the subsequent results. The associated cover is written as
`Spec(C[1/f]) ⟶ Spec(A[1/f])`, using the canonical map on away localizations; this is the
affine-coordinate description of the restriction over `Spec(A_f)`. For étaleness, the source also
assumes that `A` is Noetherian, that `f` is a nonzerodivisor and that `A/fA` is reduced; these
hypotheses are not used away from `f` and are omitted, while positivity is expressed by
`NeZero e`.

## References

* [Stacks Project, Tag 0EYF](https://stacks.math.columbia.edu/tag/0EYF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The standard tamely ramified algebra `A[X] / (X ^ e - f)`. -/
@[stacks 0EYF "standard_tamely_ramified_morphism"]
public abbrev standardTamelyRamifiedAlgebra (A : Type u) [CommRing A] (f : A) (e : ℕ) :=
  Polynomial A ⧸ Ideal.span ({Polynomial.X ^ e - Polynomial.C f} : Set (Polynomial A))

/-- The canonical morphism `Spec(A[X] / (X ^ e - f)) ⟶ Spec(A)`. -/
@[stacks 0EYF "standard_tamely_ramified_morphism"]
public noncomputable abbrev standardTamelyRamifiedMorphism
    (A : Type u) [CommRing A] (f : A) (e : ℕ) :
    Scheme.Spec.obj (Opposite.op (CommRingCat.of (standardTamelyRamifiedAlgebra A f e))) ⟶
      Scheme.Spec.obj (Opposite.op (CommRingCat.of A)) :=
  Scheme.Spec.map
    (CommRingCat.ofHom (algebraMap A (standardTamelyRamifiedAlgebra A f e))).op

/-- The associated cover, obtained by restricting the standard morphism over
`Spec(A_f)`. -/
@[stacks 0EYF "standard_tamely_ramified_morphism"]
public noncomputable abbrev standardTamelyRamifiedCover
    (A : Type u) [CommRing A] (f : A) (e : ℕ) :
    Scheme.Spec.obj (Opposite.op (CommRingCat.of
        (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f)))) ⟶
      Scheme.Spec.obj (Opposite.op (CommRingCat.of (Localization.Away f))) :=
  Scheme.Spec.map
    (CommRingCat.ofHom
      (Localization.awayMap (algebraMap A (standardTamelyRamifiedAlgebra A f e)) f)).op

/-- Away from `f`, the standard cover defined by `X ^ e = f` is étale when
`e` is a unit in the base ring. -/
@[stacks 0EYF "standard_cover_etale_away", sga "1 XIII 5.1" "r = 1, étale part"]
public theorem standardTamelyRamifiedCover_etale
    (A : Type u) [CommRing A] (f : A) (e : ℕ) [NeZero e]
    (he : IsUnit (e : A)) :
    Etale (standardTamelyRamifiedCover A f e) := by
  let C := standardTamelyRamifiedAlgebra A f e
  let R := Localization.Away f
  let T := Localization.Away (algebraMap A C f)
  let : Algebra R T :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  let : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq' (by
    show (algebraMap C T).comp (algebraMap A C) =
      (Localization.awayMap (algebraMap A C) f).comp (algebraMap A R)
    exact (IsLocalization.map_comp _).symm)
  obtain ⟨u, hu, _⟩ := (isUnit_iff_exists).mp he
  let P : StandardEtalePair A :=
    ⟨Polynomial.X ^ e - Polynomial.C f,
      Polynomial.monic_X_pow_sub_C f (NeZero.ne e), Polynomial.C f,
      ⟨Polynomial.C u * Polynomial.X,
        -1, 1, by
          rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
            Polynomial.derivative_C, sub_zero]
          rw [show (Polynomial.C (e : A) * Polynomial.X ^ (e - 1)) *
              (Polynomial.C u * Polynomial.X) =
              Polynomial.C ((e : A) * u) * (Polynomial.X ^ (e - 1) * Polynomial.X) by
                rw [Polynomial.C_mul]; ring,
            hu, show (Polynomial.X : Polynomial A) ^ (e - 1) * Polynomial.X =
              Polynomial.X ^ e by
                rw [← pow_succ, Nat.sub_add_cancel
                  (Nat.one_le_iff_ne_zero.mpr (NeZero.ne e))]]
          simp [pow_one]⟩⟩
  let : Algebra.Etale A T := by
    show Algebra.Etale A
      (Localization.Away
        (AdjoinRoot.mk (Polynomial.X ^ e - Polynomial.C f) (Polynomial.C f)))
    exact Algebra.Etale.of_equiv P.equivAwayAdjoinRoot
  let : Algebra.Etale A R := Algebra.Etale.of_isLocalizationAway f
  unfold standardTamelyRamifiedCover
  simp only [Scheme.Spec_map]
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_restrictScalars A R T)

/-! ### The standard morphism is finite locally free -/

/-- The power basis `1, x, …, x ^ (e - 1)` of `A[X] / (X ^ e - f)` over `A`, given by the
image `x` of `X`. It exists because `X ^ e - f` is monic of degree `e`. -/
public noncomputable def standardTamelyRamifiedPowerBasis
    (A : Type u) [CommRing A] (f : A) (e : ℕ) [NeZero e] :
    PowerBasis A (standardTamelyRamifiedAlgebra A f e) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C f (NeZero.ne e))

/-- Over a nontrivial ring, the power basis `standardTamelyRamifiedPowerBasis A f e` has
dimension `e`. -/
@[simp]
public theorem standardTamelyRamifiedPowerBasis_dim
    (A : Type u) [CommRing A] [Nontrivial A] (f : A) (e : ℕ) [NeZero e] :
    (standardTamelyRamifiedPowerBasis A f e).dim = e :=
  Polynomial.natDegree_X_pow_sub_C

/-- The standard tamely ramified algebra is a free `A`-module. -/
public theorem standardTamelyRamifiedAlgebra_free
    (A : Type u) [CommRing A] (f : A) (e : ℕ) [NeZero e] :
    Module.Free A (standardTamelyRamifiedAlgebra A f e) :=
  (Polynomial.monic_X_pow_sub_C f (NeZero.ne e)).free_quotient

/-- The standard tamely ramified algebra is a finite `A`-module. -/
public theorem standardTamelyRamifiedAlgebra_finite
    (A : Type u) [CommRing A] (f : A) (e : ℕ) [NeZero e] :
    Module.Finite A (standardTamelyRamifiedAlgebra A f e) :=
  (Polynomial.monic_X_pow_sub_C f (NeZero.ne e)).finite_quotient

/-- The standard tamely ramified algebra is free of rank `e` over `A`. -/
public theorem standardTamelyRamifiedAlgebra_finrank
    (A : Type u) [CommRing A] [Nontrivial A] (f : A) (e : ℕ) [NeZero e] :
    Module.finrank A (standardTamelyRamifiedAlgebra A f e) = e := by
  rw [(standardTamelyRamifiedPowerBasis A f e).finrank,
    standardTamelyRamifiedPowerBasis_dim]

/-- The standard tamely ramified algebra is a finitely presented `A`-algebra: it is the
quotient of `A[X]` by the principal ideal generated by `X ^ e - f`. -/
public theorem standardTamelyRamifiedAlgebra_finitePresentation
    (A : Type u) [CommRing A] (f : A) (e : ℕ) :
    Algebra.FinitePresentation A (standardTamelyRamifiedAlgebra A f e) :=
  Algebra.FinitePresentation.quotient
    (Submodule.fg_span_singleton (Polynomial.X ^ e - Polynomial.C f))

/-- The standard morphism `Spec(A[X] / (X ^ e - f)) ⟶ Spec(A)` is finite locally free: it is
finite, flat and locally of finite presentation. In fact `A[X] / (X ^ e - f)` is free of rank
`e` over `A` (`standardTamelyRamifiedAlgebra_free`,
`standardTamelyRamifiedAlgebra_finrank`), so the morphism is even finite free. -/
@[stacks 0EYF "standard_morphism_finite_locally_free", sga "1 XIII 5.1" "r = 1, finite part"]
public theorem standardTamelyRamifiedMorphism_finiteLocallyFree
    (A : Type u) [CommRing A] (f : A) (e : ℕ) [NeZero e] :
    IsFinite (standardTamelyRamifiedMorphism A f e) ∧
      Flat (standardTamelyRamifiedMorphism A f e) ∧
      LocallyOfFinitePresentation (standardTamelyRamifiedMorphism A f e) := by
  have hfree := standardTamelyRamifiedAlgebra_free A f e
  have hfin := standardTamelyRamifiedAlgebra_finite A f e
  have hfp := standardTamelyRamifiedAlgebra_finitePresentation A f e
  unfold standardTamelyRamifiedMorphism
  simp only [Scheme.Spec_map]
  refine ⟨?_, ?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hfin
  · rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_free)
  · rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact RingHom.finitePresentation_algebraMap.mpr hfp

/-- **Stacks 0EYF, finiteness of the standard cover.** The restriction
`Spec(C_f) ⟶ Spec(A_f)` of the standard morphism over `Spec(A_f)` is finite. The ring `C_f` is
the localization of `C = A[X] / (X ^ e - f)` at the image of `f`, so it is a finite module over
`A_f` because `C` is a finite `A`-module (`standardTamelyRamifiedAlgebra_finite`); finiteness of
a ring map is preserved by localizing source and target at the same element. Together with
`standardTamelyRamifiedCover_etale` this is the assertion of the tag that
`Spec(C_f) ⟶ Spec(A_f)` is a *finite* étale morphism. As for étaleness, the Noetherian,
nonzerodivisor, reducedness and invertibility hypotheses of the tag are not needed away from
`f` and are omitted; only positivity of `e`, expressed by `NeZero e`, is used. -/
@[stacks 0EYF "the restriction of the standard morphism over Spec(A_f), that is the standard \
cover, is finite"]
public theorem standardTamelyRamifiedCover_isFinite
    (A : Type u) [CommRing A] (f : A) (e : ℕ) [NeZero e] :
    IsFinite (standardTamelyRamifiedCover A f e) := by
  unfold standardTamelyRamifiedCover
  simp only [Scheme.Spec_map]
  rw [IsFinite.SpecMap_iff]
  exact RingHom.localization_away_map_finite A (standardTamelyRamifiedAlgebra A f e)
    (Localization.Away f)
    (Localization.Away (algebraMap A (standardTamelyRamifiedAlgebra A f e) f))
    (algebraMap A (standardTamelyRamifiedAlgebra A f e)) f
    (RingHom.finite_algebraMap.mpr (standardTamelyRamifiedAlgebra_finite A f e))

end AlgebraicGeometry

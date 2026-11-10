module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.IntegralClosure.AlmostIntegral
public import StacksFrontier.RingTheory.Nagata.Japanese
import StacksCore.Tactic.EgaSgaAttribute

/-!
# N-1 descends from the Laurent polynomial ring

All rings are commutative with `1`, and a *domain* is a nonzero integral domain.
For a domain `R` we write `K = Frac R` for its field of fractions, viewed as a ring
containing `R`. The *integral closure of `R` in `K`* is the set
`R' = {x ∈ K | x integral over R}` of those `x ∈ K` satisfying a monic equation
`xⁿ + c_{n-1} x^{n-1} + ⋯ + c₀ = 0` with coefficients in `R`; it is a subring of `K`
containing `R`, and naturally an `R`-module.

A domain `R` with fraction field `K` is *N-1* when the integral closure `R'` of `R`
in `K` is a finite, that is finitely generated, `R`-module.

For a domain `R`, the Laurent polynomial ring `R[z, z⁻¹]` is the ring of Laurent
polynomials in `z` over `R`, equivalently the localization `R[z]_z` of the polynomial
ring at the powers of `z`; its elements are the finite sums `∑_j a_j zʲ` with
`a_j ∈ R` and `j` ranging over a finite set of possibly negative integers. Since `R`
is a domain so is `R[z, z⁻¹]`, so the notion of N-1 applies to it. It is realized by
Mathlib's `LaurentPolynomial R`, written `R[T;T⁻¹]`.

The main result is that for a Noetherian domain `R`, if `R[z, z⁻¹]` is N-1 then so is
`R`: if the integral closure of `R[z, z⁻¹]` in its fraction field
`Frac (R[z, z⁻¹]) = K(z)` is a finite `R[z, z⁻¹]`-module, then the integral closure
`R'` of `R` in `K` is a finite `R`-module.

## Conventions and the shape of the argument

Since `R` is a domain, `K = Frac R` is a field, and the fraction field of `R[z, z⁻¹]`
is `K(z)`, the field of rational functions in `z` over `K`, giving the chain
`R ⊂ R[z, z⁻¹] ⊂ K[z, z⁻¹] ⊂ K(z)`.

Write `S'` for the integral closure of `R[z, z⁻¹]` in `K(z)`. The field `K(z)` is also
the fraction field of the normal domain `K[z, z⁻¹]`, a localization of the principal
ideal domain `K[z]`, hence a unique factorization domain and so integrally closed in
its fraction field. Any element of `K(z)` integral over `R[z, z⁻¹]` is in particular
integral over `K[z, z⁻¹]` and therefore lies in `K[z, z⁻¹]`. Thus `S' ⊂ K[z, z⁻¹]`,
and clearly `R' ⊂ S'`.

Suppose `f₁, …, f_n ∈ S'` generate `S'` as an `R[z, z⁻¹]`-module and write each
`f_i = ∑_j a_{ij} zʲ` as a finite sum with `a_{ij} ∈ K`. For `x ∈ R'` we have `x ∈ S'`,
so `x = ∑_i h_i f_i` with `h_i ∈ R[z, z⁻¹]`; comparing coefficients of powers of `z`
shows that `x` lies in the finitely generated `R`-submodule `∑_{i,j} R a_{ij} ⊂ K`.
Hence `R'` is contained in a finite `R`-submodule of `K`, and since `R` is Noetherian
every submodule of a finite `R`-module is finite, so `R'` is a finite `R`-module.

The Noetherian hypothesis on `R` is used precisely to conclude that the `R`-submodule
`R'` of the finite `R`-module `∑_{i,j} R a_{ij}` is itself finitely generated, and the
N-1 hypothesis on `R[z, z⁻¹]` supplies the finite generating set of `S'`.
-/

@[expose] public section

open scoped Polynomial LaurentPolynomial

/-- Reduction lemma: over a Noetherian ring, if the integral closure of `R` in
`K` is contained (as an `R`-submodule) in a finitely generated `R`-submodule of
`K`, then the integral closure is itself a finite `R`-module. -/
theorem isN1_of_le_fg {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    [IsNoetherianRing R] (M : Submodule R K) (hM : M.FG)
    (hsub : (integralClosure R K).toSubmodule ≤ M) :
    Module.Finite R (integralClosure R K) := by
  have hMnoeth : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M hM
  exact Module.Finite.iff_fg.mpr (Submodule.FG.of_le_of_isNoetherian hsub)

/-! ## Decomposition of the main containment

Notation throughout: `K = Frac R`, `S = R[z,z⁻¹]`, `L = Frac S`,
`T = K[z,z⁻¹] = LaurentPolynomial K`, `S' = integralClosure S L` and
`R' = integralClosure R K`. The argument factors into four mathematically
independent pieces, which are the sub-lemmas below.
-/

/-- **Sub-lemma (A): finite spanning set of `S'`.**  If `S = R[z,z⁻¹]` is N-1,
then the integral closure of `S` in its fraction field `L` is a finitely
generated `S`-submodule of `L`.

This is a direct unfolding of the N-1 hypothesis: `IsN1 S` is by definition
`Module.Finite S (integralClosure S (FractionRing S))`, and `Module.Finite`
of a subalgebra is equivalent to finite generation of its underlying submodule
via `Module.Finite.iff_fg`.  No real content; recorded so the main proof can
name the spanning set. -/
theorem exists_fg_containing.span_of_isN1 (R : Type*) [CommRing R] [IsDomain R]
    (h : IsN1 (LaurentPolynomial R)) :
    (integralClosure (LaurentPolynomial R)
        (FractionRing (LaurentPolynomial R))).toSubmodule.FG := by
  -- HINT (directly closable): `Module.Finite.iff_fg.mp h`.  `IsN1 (LaurentPolynomial R)`
  -- unfolds definitionally to `Module.Finite (LaurentPolynomial R) (integralClosure …)`.
  exact Module.Finite.iff_fg.mp h

/-- **Sub-lemma (B): `LaurentPolynomial K` is integrally closed.**  For a field
`K`, the Laurent polynomial ring `K[z,z⁻¹]` is integrally closed in its fraction
field.

Argument: `LaurentPolynomial K` is the localization of the polynomial ring
`K[X]` at the powers of `X` (`LaurentPolynomial K ≃ₐ Localization.Away X`, cf.
`Polynomial.toLaurent`/`LaurentPolynomial.algEquivPolynomialAway`-style maps).
`K[X]` is a PID (`Polynomial.instIsPrincipalIdealRing` since `K` is a field),
hence a UFD, hence integrally closed (`UniqueFactorizationMonoid.instIsIntegrallyClosed`
/ `IsPrincipalIdealRing → IsIntegrallyClosed`).  Integral closedness is preserved
under localization (`IsLocalization.isIntegrallyClosed`), so `K[z,z⁻¹]` is
integrally closed.  Mathlib hints: `IsIntegrallyClosed` for PIDs, and the
localization-stability lemma `IsIntegrallyClosed` of a localization of an
integrally closed domain. -/
theorem exists_fg_containing.laurentField_isIntegrallyClosed
    (K : Type*) [Field K] : IsIntegrallyClosed (LaurentPolynomial K) := by
  -- `K[X]` is a PID (hence integrally closed, `IsDomain`), and `LaurentPolynomial K`
  -- is the localization of `K[X]` at the powers of `X` (instance found by
  -- `infer_instance`). The localization-stability lemma
  -- `isIntegrallyClosed_of_isLocalization` then applies; its side goal is
  -- `Submonoid.powers X ≤ nonZeroDivisors K[X]`, true since `X ≠ 0`.
  exact isIntegrallyClosed_of_isLocalization (LaurentPolynomial K)
    (Submonoid.powers (Polynomial.X : K[X]))
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero Polynomial.X_ne_zero))

/-! ### The containment `S' ⊆ K[z,z⁻¹]`

Every element of `L = Frac (R[z,z⁻¹])` integral over `S = R[z,z⁻¹]` lies in
`T = K[z,z⁻¹]`. Indeed `L = Frac S` is also the fraction field of `T`, both being
`K(z)`, because `T` is the localization of `S` obtained by inverting the nonzero
elements of `R`. Any element of `L` integral over `S` is a fortiori integral over
the larger ring `T`, and `T` is integrally closed in its fraction field `L`, so such
an element lies in `T`. Concretely a generator `f ∈ S'`, written in `L = K(z)`, is a
Laurent polynomial with coefficients in `K`, which turns a spanning set in `L` into
Laurent polynomials with `K`-coefficients and so allows coefficient extraction.

This step has no standalone statement of its own: a faithful one would first have to
fix the identification `Frac (R[z,z⁻¹]) ≃ K(z)` and the embedding `T ↪ L`, which are
set up inside `exists_fg_containing` itself.
-/

/-! ### The fraction-field identification `Frac(R[z,z⁻¹]) = Frac(K[z,z⁻¹]) = K(z)`

This namespace builds:
* the coefficient-change algebra `R[T;T⁻¹] → K[T;T⁻¹]` (`instAlg_S_T`) with its
  coefficient formula (`algST_coeff`);
* the scalar towers through `R[X]` (`instST1`, `instST2`);
* the fact that `K[T;T⁻¹]` is the localization of `R[T;T⁻¹]` obtained by inverting
  the nonzero constants of `R` (`instLoc_main`), by applying `IsLocalization.commutes`
  to the coefficient and `Away X` localizations of `R[X]`;
* the transfer lemma `isFractionRing_of_isLocalization_le`, that a fraction ring of a
  localization at `M ≤ nonZeroDivisors` is a fraction ring of the base;
* and hence that `Frac(K[T;T⁻¹])` is a fraction ring of `R[T;T⁻¹]`
  (`instFracRing_S_L`), the common field `L = K(z)`.

On top of these come the transfer of N-1 finiteness to `L`, the integral closure
containment `S' ⊆ K[T;T⁻¹]`, and the comparison of `z⁰`-coefficients.
-/
namespace exists_fg_containing

variable (R : Type*) [CommRing R] [IsDomain R]

/-- Coefficient-change algebra `R[T;T⁻¹] → K[T;T⁻¹]` (where `K = Frac R`). -/
noncomputable instance instAlg_S_T :
    Algebra (LaurentPolynomial R) (LaurentPolynomial (FractionRing R)) :=
  (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R (FractionRing R))).toAlgebra

/-- The algebra `R[X] → K[T;T⁻¹]` given by the composite `R[X] → K[X] → K[T;T⁻¹]`
(where `K = Frac R`). -/
noncomputable instance instAlg_RX_T :
    Algebra (Polynomial R) (LaurentPolynomial (FractionRing R)) :=
  ((algebraMap (Polynomial (FractionRing R)) (LaurentPolynomial (FractionRing R))).comp
    (Polynomial.mapRingHom (algebraMap R (FractionRing R)))).toAlgebra

/-- The scalar tower `R[X] → K[X] → K[T;T⁻¹]`. -/
instance instST1 :
    IsScalarTower (Polynomial R) (Polynomial (FractionRing R))
    (LaurentPolynomial (FractionRing R)) := by
  apply IsScalarTower.of_algebraMap_eq; intro x; rfl

omit [IsDomain R] in
/-- The `n`-th coefficient of `algebraMap (R[T;T⁻¹]) (K[T;T⁻¹]) p` is the image of
the `n`-th coefficient of `p`. -/
lemma algST_coeff (p : LaurentPolynomial R) (n : ℤ) :
    (algebraMap (LaurentPolynomial R) (LaurentPolynomial (FractionRing R)) p).coeff n
      = algebraMap R (FractionRing R) (p.coeff n) := by
  change (AddMonoidAlgebra.mapRingHom ℤ (algebraMap R (FractionRing R)) p).coeff n = _
  rw [AddMonoidAlgebra.coeff_mapRingHom]

/-- The scalar tower `R[X] → R[T;T⁻¹] → K[T;T⁻¹]`. -/
instance instST2 :
    IsScalarTower (Polynomial R) (LaurentPolynomial R)
    (LaurentPolynomial (FractionRing R)) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply Polynomial.ringHom_ext
  · intro a
    change (algebraMap (Polynomial (FractionRing R)) _).comp (Polynomial.mapRingHom _)
      (Polynomial.C a) = _
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C, RingHom.comp_apply]
    change _ = (algebraMap (LaurentPolynomial R) (LaurentPolynomial (FractionRing R)))
      ((algebraMap (Polynomial R) (LaurentPolynomial R)) (Polynomial.C a))
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
    ext n; rw [algST_coeff]; simp only [LaurentPolynomial.C_apply]; split_ifs <;> simp
  · change (algebraMap (Polynomial (FractionRing R)) _).comp (Polynomial.mapRingHom _)
      Polynomial.X = _
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
      LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X, RingHom.comp_apply]
    change _ = (algebraMap (LaurentPolynomial R) (LaurentPolynomial (FractionRing R)))
      ((algebraMap (Polynomial R) (LaurentPolynomial R)) Polynomial.X)
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X]
    ext n; rw [algST_coeff]; simp [LaurentPolynomial.T_apply]

/-- `K[X]` is the localization of `R[X]` obtained by inverting the nonzero constants
of `R`. -/
instance instLoc_KX :
    IsLocalization (Submonoid.map (Polynomial.C : R →+* Polynomial R) (nonZeroDivisors R))
      (Polynomial (FractionRing R)) :=
  Polynomial.isLocalization (nonZeroDivisors R) (FractionRing R)

/-- `K[T;T⁻¹]` is the localization of `K[X]` at the powers of `X`, transported along
the algebra map from `R[X]`. -/
instance instLoc_hyp :
    IsLocalization (Algebra.algebraMapSubmonoid (Polynomial (FractionRing R))
    (Submonoid.powers (Polynomial.X : (Polynomial R)))) (LaurentPolynomial (FractionRing R)) := by
  have heq : Algebra.algebraMapSubmonoid (Polynomial (FractionRing R))
      (Submonoid.powers (Polynomial.X : (Polynomial R)))
      = Submonoid.powers (Polynomial.X : Polynomial (FractionRing R)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; congr 1
    change (algebraMap (Polynomial R) (Polynomial (FractionRing R))) Polynomial.X = _
    simp
  rw [heq]; exact LaurentPolynomial.isLocalization

/-- `K[T;T⁻¹]` is the localization of `R[T;T⁻¹]` inverting (the image of) the
nonzero constants of `R`. Proved via `IsLocalization.commutes`. -/
instance instLoc_main :
    IsLocalization (Algebra.algebraMapSubmonoid (LaurentPolynomial R)
      (Submonoid.map (Polynomial.C : R →+* Polynomial R) (nonZeroDivisors R)))
      (LaurentPolynomial (FractionRing R)) :=
  IsLocalization.commutes (LaurentPolynomial R) (Polynomial (FractionRing R))
    (LaurentPolynomial (FractionRing R)) (Submonoid.powers (Polynomial.X : Polynomial R))
    (Submonoid.map (Polynomial.C : R →+* Polynomial R) (nonZeroDivisors R))

/-- The submonoid of (images of) nonzero constants is contained in the nonzero
divisors of `R[T;T⁻¹]`. -/
lemma map_C_nzd_le :
    Algebra.algebraMapSubmonoid (LaurentPolynomial R)
      (Submonoid.map (Polynomial.C : R →+* Polynomial R) (nonZeroDivisors R))
    ≤ nonZeroDivisors (LaurentPolynomial R) := by
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨r, hr, rfl⟩ := hc
  rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C]
  rw [mem_nonZeroDivisors_iff_ne_zero, Ne, LaurentPolynomial.C_eq_algebraMap,
    (injective_iff_map_eq_zero' _).mp (FaithfulSMul.algebraMap_injective R (LaurentPolynomial R))]
  exact mem_nonZeroDivisors_iff_ne_zero.mp hr

/-- General transfer: if `S` is a localization of a domain `R` at a submonoid
`M ≤ nonZeroDivisors R`, and a field `T` is a fraction ring of `S`, then `T` is a
fraction ring of `R`. -/
lemma isFractionRing_of_isLocalization_le
    {R S T : Type*} [CommRing R] [CommRing S] [Field T] [IsDomain R]
    (M : Submonoid R) [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) [IsFractionRing S T] :
    IsFractionRing R T := by
  have hSdom : IsDomain S := (IsFractionRing.injective S T).isDomain _
  have hinj : Function.Injective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]
    exact (IsFractionRing.injective S T).comp (IsLocalization.injective S hM)
  have hFS : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr hinj
  have hMne : ∀ c : M, algebraMap R T (c : R) ≠ 0 := by
    intro c; rw [map_ne_zero_iff _ hinj]
    exact mem_nonZeroDivisors_iff_ne_zero.mp (hM c.property)
  have key : ∀ (x : S) (a : R) (m : M), x * (algebraMap R S) (m : R) = (algebraMap R S) a →
      algebraMap S T x = algebraMap R T a / algebraMap R T (m : R) := by
    intro x a m hxa
    rw [eq_div_iff (hMne m), IsScalarTower.algebraMap_apply R S T (m : R),
      ← map_mul, hxa, ← IsScalarTower.algebraMap_apply R S T]
  apply IsFractionRing.of_field R T
  intro z
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) z
  obtain ⟨⟨a, m⟩, hxa⟩ := IsLocalization.surj M x
  obtain ⟨⟨b, n⟩, hyb⟩ := IsLocalization.surj M y
  simp only at hxa hyb
  refine ⟨a * (n : R), b * (m : R), ?_⟩
  have hb0 : algebraMap S T y ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective S T)]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hy
  rw [key x a m hxa, key y b n hyb]
  rw [key y b n hyb] at hb0
  rw [map_mul, map_mul]; field_simp

/-- `Frac(K[T;T⁻¹])` is a fraction ring of `R[T;T⁻¹]`: both are the field `K(z)`. -/
instance instFracRing_S_L :
    IsFractionRing (LaurentPolynomial R)
      (FractionRing (LaurentPolynomial (FractionRing R))) :=
  isFractionRing_of_isLocalization_le
    (R := LaurentPolynomial R) (S := LaurentPolynomial (FractionRing R))
    (T := FractionRing (LaurentPolynomial (FractionRing R)))
    (Algebra.algebraMapSubmonoid (LaurentPolynomial R)
      (Submonoid.map (Polynomial.C : R →+* Polynomial R) (nonZeroDivisors R)))
    (map_C_nzd_le R)

/-! ### The three intermediate pieces

With `K = FractionRing R`, `S = LaurentPolynomial R`, `T = LaurentPolynomial K` and
`L = FractionRing T` the common field `K(z)`, a fraction ring of `S` by
`instFracRing_S_L`, the three mathematical pieces of the argument are captured below,
and `exists_fg_containing` combines them.
-/

-- `IsDomain R` is used only via instance synthesis in the proof (to build the
-- `Field (FractionRing …)` instance); the section-var linter is a false positive here.
set_option linter.unusedSectionVars false in
/-- **Piece (1)→(4a): integral over `R` ⇒ integral over `S` inside `L`.**
Every element `x` of the integral closure of `R` in `K = FractionRing R`,
transported into `L = FractionRing (LaurentPolynomial K)` via the (injective)
algebra map `K → L`, is integral over `S = LaurentPolynomial R`, i.e. lies in
`integralClosure S L`.

Intended Mathlib approach: `x` satisfies a monic polynomial with coefficients in
`R`; pushing this equation forward along the ring maps `R → S → L` (using
`IsScalarTower R S L` and that `algebraMap K L` is an algebra map over `R`)
exhibits `algebraMap K L x` as a root of the same monic polynomial now viewed
over `S`. Concretely use `IsIntegral.map`/`IsIntegral.tower_top`-style transfer:
`x` integral over `R` gives `IsIntegral R (algebraMap K L x)` (via
`IsScalarTower.toAlgHom R K L` and `IsIntegral.map`), then `IsIntegral.tower_top`
(over the scalar tower `R → S → L`) upgrades it to `IsIntegral S _`. -/
theorem closureR_le_closureS_in_L
    (x : FractionRing R)
    (hx : x ∈ integralClosure R (FractionRing R)) :
    algebraMap (FractionRing R) (FractionRing (LaurentPolynomial (FractionRing R))) x
      ∈ integralClosure (LaurentPolynomial R)
          (FractionRing (LaurentPolynomial (FractionRing R))) := by
  -- `x` integral over `R` ⇒ its image in `L` is integral over `R` (push forward
  -- the monic equation along `K → L`), and then `IsIntegral.tower_top` along
  -- `R → S → L` makes it integral over `S`.
  have hSTRS_L : IsScalarTower R (LaurentPolynomial R)
      (FractionRing (LaurentPolynomial (FractionRing R))) := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro r
    rw [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply R (FractionRing R)
        (FractionRing (LaurentPolynomial (FractionRing R))) r]
    rw [IsScalarTower.algebraMap_apply (LaurentPolynomial R)
        (LaurentPolynomial (FractionRing R))
        (FractionRing (LaurentPolynomial (FractionRing R)))]
    rw [IsScalarTower.algebraMap_apply (FractionRing R)
        (LaurentPolynomial (FractionRing R))
        (FractionRing (LaurentPolynomial (FractionRing R)))]
    congr 1
    have : algebraMap (FractionRing R) (LaurentPolynomial (FractionRing R))
        (algebraMap R (FractionRing R) r)
        = algebraMap (LaurentPolynomial R) (LaurentPolynomial (FractionRing R))
          (algebraMap R (LaurentPolynomial R) r) := by
      ext n
      rw [algST_coeff]
      rw [show (algebraMap (FractionRing R) (LaurentPolynomial (FractionRing R)))
            = (LaurentPolynomial.C : FractionRing R →+* LaurentPolynomial (FractionRing R))
          from rfl,
        show (algebraMap R (LaurentPolynomial R))
            = (LaurentPolynomial.C : R →+* LaurentPolynomial R) from rfl]
      simp only [LaurentPolynomial.C_apply]
      split_ifs with h <;> simp
    exact this
  have hxR : IsIntegral R (algebraMap (FractionRing R)
      (FractionRing (LaurentPolynomial (FractionRing R))) x) :=
    hx.map (IsScalarTower.toAlgHom R (FractionRing R)
      (FractionRing (LaurentPolynomial (FractionRing R))))
  rw [mem_integralClosure_iff]
  exact hxR.tower_top

omit [IsDomain R] in
/-- Convolution-closure: if every coefficient of `t : K[T;T⁻¹]` lies in an
`R`-submodule `M` of `K`, then so does every coefficient of
`(algebraMap S T a) * t` for any `a : S = R[T;T⁻¹]`. -/
lemma conv_mem (M : Submodule R (FractionRing R)) (a : LaurentPolynomial R)
    (t : LaurentPolynomial (FractionRing R)) (ht : ∀ j, t.coeff j ∈ M) (n : ℤ) :
    (algebraMap (LaurentPolynomial R) (LaurentPolynomial (FractionRing R)) a * t).coeff n ∈ M := by
  rw [AddMonoidAlgebra.coeff_mul]
  apply Submodule.sum_mem
  intro m₁ hm₁
  apply Submodule.sum_mem
  intro m₂ hm₂
  simp only
  split_ifs with hcond
  · rw [algST_coeff, ← Algebra.smul_def]
    exact M.smul_mem _ (ht m₂)
  · exact M.zero_mem

/-- The `S`-submodule of `T = K[T;T⁻¹]` consisting of Laurent polynomials all of
whose coefficients lie in a given `R`-submodule `M` of `K`. -/
noncomputable def coeffSubmodule (M : Submodule R (FractionRing R)) :
    Submodule (LaurentPolynomial R) (LaurentPolynomial (FractionRing R)) where
  carrier := {t | ∀ n, t.coeff n ∈ M}
  add_mem' := by
    intro s t hs ht n
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact M.add_mem (hs n) (ht n)
  zero_mem' := by
    intro n
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    exact M.zero_mem
  smul_mem' := by
    intro a t ht n
    rw [Algebra.smul_def]
    exact conv_mem R M a t ht n

omit [IsDomain R] in
/-- A Laurent polynomial lies in `coeffSubmodule R M` exactly when all of its
coefficients lie in `M`. -/
lemma mem_coeffSubmodule {M : Submodule R (FractionRing R)}
    {t : LaurentPolynomial (FractionRing R)} :
    t ∈ coeffSubmodule R M ↔ ∀ n, t.coeff n ∈ M := Iff.rfl

/-- **Pieces (1)+(2)+(3): the finitely generated `R`-module of coefficients.**
There is a finitely generated `R`-submodule `M` of `K = FractionRing R` such
that every `x : K` whose image in `L` is integral over `S = LaurentPolynomial R`
already lies in `M`.

This is the substantive content. Intended Mathlib approach:
* By Sub-lemma A (`exists_fg_containing.span_of_isN1`) and the fraction-ring
  identification `instFracRing_S_L`, transport a finite `S`-spanning set
  `f₁,…,fₙ` of `integralClosure S L` across the isomorphism
  `FractionRing S ≃ L` (`IsFractionRing` uniqueness, `IsLocalization.algEquiv`).
* By Sub-lemma B (`laurentField_isIntegrallyClosed`) plus `instLoc_main`/
  `IsIntegrallyClosed`-localization stability, `integralClosure S L` is contained
  in the image of `T = LaurentPolynomial K` in `L`; so each `fᵢ` is (the image
  of) a Laurent polynomial with `K`-coefficients `aᵢⱼ`.
* Set `M := Submodule.span R {aᵢⱼ}` (a finite set), which is `FG` by
  `Submodule.fg_span` of a finite set.
* For `x : K` with `algebraMap K L x ∈ integralClosure S L`, write
  `algebraMap K L x = ∑ᵢ hᵢ · fᵢ` with `hᵢ ∈ S` (membership in the `S`-span);
  view both sides in `T = LaurentPolynomial K` and compare the `z⁰` coefficient
  (`LaurentPolynomial` coefficient API) to express `x` as an `R`-linear
  combination of the `aᵢⱼ`, hence `x ∈ M`. -/
theorem exists_fg_coeffModule (h : IsN1 (LaurentPolynomial R)) :
    ∃ M : Submodule R (FractionRing R), M.FG ∧
      ∀ x : FractionRing R,
        algebraMap (FractionRing R)
            (FractionRing (LaurentPolynomial (FractionRing R))) x
          ∈ integralClosure (LaurentPolynomial R)
              (FractionRing (LaurentPolynomial (FractionRing R))) →
        x ∈ M := by
  -- Build `M` as the `R`-span of the finitely many `K`-coefficients of a finite
  -- `S`-spanning set of `S'`, then perform the `z⁰`-coefficient comparison.
  -- Abbreviations: K = FractionRing R, S = LaurentPolynomial R,
  -- T = LaurentPolynomial K, L = FractionRing T.
  set K := FractionRing R with hK
  set S := LaurentPolynomial R with hS
  set T := LaurentPolynomial K with hT
  set L := FractionRing T with hL
  -- Scalar tower S → T → L.
  have hST_L : IsScalarTower S T L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro p
    rw [RingHom.comp_apply]
    rw [show (algebraMap S L) = (algebraMap T L).comp (algebraMap S T) from rfl,
      RingHom.comp_apply]
  -- (1) integralClosure S L is FG over S.
  have hFG : (integralClosure S L).toSubmodule.FG := by
    have hA := exists_fg_containing.span_of_isN1 R h
    have e := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
    rw [← integralClosure_map_algEquiv e, Subalgebra.map_toSubmodule]
    exact hA.map e.toAlgHom.toLinearMap
  classical
  -- Extract a finite spanning family s : Fin n → L of integralClosure S L.
  obtain ⟨n, s, hspan⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hFG
  -- (2) each generator s i comes from a Laurent polynomial g i over K.
  have : IsIntegrallyClosed T := exists_fg_containing.laurentField_isIntegrallyClosed K
  have hgen : ∀ i, ∃ g : T, algebraMap T L g = s i := by
    intro i
    have hmem : s i ∈ integralClosure S L := by
      rw [← Subalgebra.mem_toSubmodule, ← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hInt : IsIntegral S (s i) := hmem
    have hIntT : IsIntegral T (s i) := hInt.tower_top
    exact (IsIntegrallyClosed.isIntegral_iff).mp hIntT
  choose g hg using hgen
  -- (3) Define M as the R-span of all K-coefficients of the g i.
  set M : Submodule R K :=
    Submodule.span R
      (↑(Finset.univ.biUnion (fun i => (g i).coeff.support.image (fun j => (g i).coeff j))))
    with hMdef
  have hFGM : M.FG := by
    rw [hMdef]; exact Submodule.fg_span (Finset.finite_toSet _)
  have hcoeffM : ∀ (i : Fin n) (j : ℤ), (g i).coeff j ∈ M := by
    intro i j
    by_cases hj : (g i).coeff j = 0
    · rw [hj]; exact M.zero_mem
    · apply Submodule.subset_span
      rw [Finset.coe_biUnion]
      simp only [Set.mem_iUnion, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finsupp.mem_support_iff]
      exact ⟨i, Finset.mem_univ i, j, hj, rfl⟩
  -- Each g i lies in the coefficient submodule of T.
  have hgN : ∀ i, g i ∈ coeffSubmodule R M := fun i j => hcoeffM i j
  refine ⟨M, hFGM, ?_⟩
  -- (4) Membership argument.
  intro x hx
  -- write algebraMap K L x as an S-combination of the s i.
  rw [← Subalgebra.mem_toSubmodule, ← hspan,
    Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  -- Transport into T: C x = ∑ i, c i • g i.
  have hCx : (LaurentPolynomial.C x : T) = ∑ i, c i • g i := by
    apply IsFractionRing.injective T L
    rw [map_sum]
    rw [show algebraMap T L (LaurentPolynomial.C x)
          = algebraMap K L x from ?_]
    · rw [← hc]
      apply Finset.sum_congr rfl
      intro i _
      rw [Algebra.smul_def, Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply S T L, hg i]
    · -- algebraMap T L (C x) = algebraMap K L x via tower K → T → L
      rw [show (LaurentPolynomial.C x : T) = algebraMap K T x from rfl,
        ← IsScalarTower.algebraMap_apply K T L x]
  -- C x ∈ coeffSubmodule R M, so its 0-coefficient (= x) ∈ M.
  have hCxN : (LaurentPolynomial.C x : T) ∈ coeffSubmodule R M := by
    rw [hCx]
    exact Submodule.sum_mem _ (fun i _ => (coeffSubmodule R M).smul_mem _ (hgN i))
  have := hCxN 0
  rwa [show (LaurentPolynomial.C x : T).coeff 0 = x by simp [LaurentPolynomial.C_apply]] at this

end exists_fg_containing

/-- The heart of Stacks Tag 032J: if `R[z,z⁻¹]` is N-1 then the integral closure
of `R` in `K = Frac(R)` is contained in a finitely generated `R`-submodule of
`K`. This is the substantive geometric content of the theorem: writing a finite
set of generators `f₁,…,fₙ` of the integral closure `S'` of `S = R[z,z⁻¹]` in
`K(z)` as Laurent polynomials with coefficients `aᵢⱼ ∈ K`, every element of `R'`
expands as an `S`-linear combination of the `fᵢ`, and comparing the constant
coefficient shows it lies in the `R`-span of the (finitely many) `aᵢⱼ`. -/
theorem exists_fg_containing (R : Type*) [CommRing R] [IsDomain R]
    (h : IsN1 (LaurentPolynomial R)) :
    ∃ M : Submodule R (FractionRing R), M.FG ∧
      (integralClosure R (FractionRing R)).toSubmodule ≤ M := by
  -- Proof outline (Stacks 032J), with `K = Frac R`, `S = R[z,z⁻¹]`,
  -- `L = Frac S = K(z)`, `T = K[z,z⁻¹]`, `S' = integralClosure S L`:
  --
  -- (1) [Sub-lemma A] `h : Module.Finite S S'`, so `S'.toSubmodule` is f.g.:
  --     there is a finite set `t ⊆ L` spanning `S'` over `S`.
  -- (2) [Sub-lemmas B, C] `T = K[z,z⁻¹]` is a localization of `S = R[z,z⁻¹]`
  --     (invert the nonzero constants of `R`); hence `Frac T = Frac S = L`, and
  --     `T` is integrally closed in `L` (localization of the PID `K[X]`).
  --     Therefore `S' ⊆ T`, i.e. each generator `f ∈ t` is a Laurent polynomial
  --     `f = ∑ⱼ aⱼ zʲ` with coefficients `aⱼ ∈ K`.
  -- (3) Let `M ⊆ K` be the `R`-span of the finite set of all coefficients `aᵢⱼ`
  --     of the (finitely many) generators. `M` is finitely generated by
  --     construction (finite spanning set of coefficients).
  -- (4) For `x ∈ R' = integralClosure R K`, the embedding `K ↪ L` carries `x`
  --     into `S'` (integral over `R` ⇒ integral over `S`), so
  --     `x = ∑ᵢ hᵢ fᵢ` with `hᵢ ∈ S`. As elements of `T`, comparing the
  --     coefficient of `z⁰` gives `x = ∑ᵢ ∑ₖ (hᵢ.coeff k)·(fᵢ.coeff (-k))`,
  --     an `R`-linear combination of the `aᵢⱼ`, so `x ∈ M`.
  --
  -- This last paragraph (steps 3–4: define `M` as the `R`-span of the coefficient
  -- set, then the coefficient-comparison membership argument) is the remaining
  -- content of THIS lemma, on top of Sub-lemmas A–C above. It requires the
  -- LaurentPolynomial coefficient API (`LaurentPolynomial.coeff`, support
  -- finiteness) and the `z⁰`-coefficient extraction.
  --
  -- ASSEMBLY (no open goals here): obtain the finitely generated coefficient module
  -- `M ⊆ K` and its capturing property from `exists_fg_coeffModule`; for any
  -- `x ∈ R'`, transport `x` into `L`, where it lands in `S'` by
  -- `closureR_le_closureS_in_L`, hence `x ∈ M`.
  obtain ⟨M, hMfg, hM⟩ := exists_fg_containing.exists_fg_coeffModule R h
  refine ⟨M, hMfg, ?_⟩
  intro x hx
  exact hM x (exists_fg_containing.closureR_le_closureS_in_L R x hx)

/-- Theorem (Stacks Tag 032J). Let `R` be a Noetherian domain. If the Laurent
polynomial ring `R[z, z^{-1}]` is N-1, then `R` is N-1. -/
@[stacks 032J]
theorem main_theorem_032j (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h : IsN1 (LaurentPolynomial R)) : IsN1 R := by
  obtain ⟨M, hM, hsub⟩ := exists_fg_containing R h
  exact isN1_of_le_fg M hM hsub

-- ===== merged from Sec161/Tag032K =====

/-!
# N-1 and N-2 descend along a finite extension of domains

All rings are commutative with unit. A *domain* is an integral domain, a nonzero
commutative ring with no zero divisors, and `Frac R` denotes the field of fractions of
a domain `R`.

For a ring extension `A ⊂ B` and a subset `C` with `A ⊂ C`, the *integral closure of
`A` in `C`* is the set of `c ∈ C` satisfying a monic equation
`cⁿ + a_{n-1} c^{n-1} + ⋯ + a₀ = 0` with all `aᵢ ∈ A`; it is a subring of `C`
containing `A`, and is `integralClosure A C : Subalgebra A C`. A ring map `A → B` is
*finite* when `B` is a finitely generated `A`-module. A *finite extension of domains*
is an inclusion `R ⊂ S` of domains making `S` a finitely generated `R`-module, modelled
below by an injective algebra map `R → S`.

A domain `R` is *N-1* when the integral closure of `R` in `K = Frac R` is a finite
`R`-module, and *N-2*, or *Japanese*, when for every finite field extension `L/K` the
integral closure of `R` in `L` is a finite `R`-module.

The main results: let `R` be a Noetherian domain and `R ⊂ S` a finite extension of
domains. If `S` is N-1 then `R` is N-1, and if `S` is N-2 then `R` is N-2.

The role of `K = Frac R` is played by Mathlib's `FractionRing R`. A finite field
extension `L/K` is modelled by a field `L` with a finite-dimensional
`(FractionRing R)`-algebra structure together with a compatible `R`-algebra structure,
the integral closure of `R` in `L` being taken along the tower `R ⊂ K ⊂ L`.
-/

@[expose] public section

universe u v w uR uS

/-- Core lemma: integral closure of `R` in a field `K` injects (as `R`-module) into the
integral closure of `S` in `L`, given an injective `R`-algebra map `K →ₐ[R] L`. -/
theorem isN_core
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K]
    [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    (hfin : Module.Finite R S)
    (φ : K →ₐ[R] L) (hφ : Function.Injective φ)
    (hS : Module.Finite S (integralClosure S L)) :
    Module.Finite R (integralClosure R K) := by
  -- `integralClosure S L` is finite over `R`, hence Noetherian over `R`.
  have : Module.Finite R (integralClosure S L) :=
    Module.Finite.trans S (integralClosure S L)
  have : IsNoetherian R (integralClosure S L) :=
    isNoetherian_of_isNoetherianRing_of_finite R (integralClosure S L)
  -- Membership: `φ` maps `integralClosure R K` into `integralClosure S L`.
  -- Build the `R`-linear map.
  let g : (integralClosure R K) →ₗ[R] L :=
    φ.toLinearMap.comp (integralClosure R K).val.toLinearMap
  have hmem (c : integralClosure R K) : g c ∈ Subalgebra.toSubmodule (integralClosure S L) :=
    (show IsIntegral S (φ c) from (IsIntegral.map φ c.property).tower_top)
  let f : (integralClosure R K) →ₗ[R] ↥(Subalgebra.toSubmodule (integralClosure S L)) :=
    { toFun := fun c => ⟨g c, hmem c⟩
      map_add' := by
        intro a b
        ext
        simp [g]
      map_smul' := by
        intro r a
        ext
        simp [g] }
  have hinjf : Function.Injective f := fun a b hab =>
    Subtype.ext (hφ (show φ a = φ b from congrArg Subtype.val hab))
  have : IsNoetherian R ↥(Subalgebra.toSubmodule (integralClosure S L)) := this
  exact Module.Finite.of_injective f hinjf

/-- An injective algebra map `R → S` of domains lifts to an injective `R`-algebra map
`Frac R → Frac S`. -/
private theorem exists_injective_algHom_fractionRing (R S : Type*) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S)) :
    ∃ φ : FractionRing R →ₐ[R] FractionRing S, Function.Injective φ := by
  have halg : Function.Injective (algebraMap R (FractionRing S)) := by
    rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
    exact (FaithfulSMul.algebraMap_injective S (FractionRing S)).comp hinj
  exact ⟨IsFractionRing.liftAlgHom (g := Algebra.ofId R (FractionRing S)) halg,
    RingHom.injective _⟩

/-- **Statement 1 (N-1 descends, part of Stacks Tag 032K).**
Let `R` be a Noetherian domain and `R ⊂ S` a finite extension of domains
(modelled by an injective algebra map `R → S` with `S` finite over `R`).
If `S` is N-1, then `R` is N-1. -/
@[stacks 032K "(1)"]
theorem isN1_of_finite_of_isN1
    (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S))
    (hfin : Module.Finite R S)
    (hS : IsN1 S) : IsN1 R := by
  -- `L = FractionRing S` is an `R`-algebra and an `S`-algebra with a scalar tower.
  -- The fraction field `K = FractionRing R` embeds into `L` as an `R`-algebra map.
  obtain ⟨φ, hφ⟩ := exists_injective_algHom_fractionRing R S hinj
  exact isN_core R S (FractionRing R) (FractionRing S) hfin φ hφ hS

-- `small_of_finite_field` and `shrink_isScalarTower`, used just below, moved to
-- `StacksFrontier.RingTheory.Nagata.Shrink`: the transport lemmas of `Nagata.Japanese` came to need
-- them, and that file is upstream of this one.

-- this proof's elaboration needs more than the default heartbeat budget
open scoped TensorProduct in
/-- **Per-extension reduction step for Statement 2 (Stacks Tag 032K, N-2 case).**

Fix a single finite field extension `L / K`, where `K = FractionRing R`.  This lemma
is the heart of the N-2 descent: it produces, for this `L`, the conclusion
`Module.Finite R (integralClosure R L)`.  Quantifying over all such `L` (done in
`isN2_of_finite_of_isN2` below by `intro`) gives `IsN2_032k R`.

Let `K = FractionRing R` and `E = FractionRing S`. The structure map `R → S → E` lifts
to an injective `R`-algebra, hence `K`-algebra, embedding `φ₀ : K →ₐ[R] E`, exactly as in
the N-1 case, making `E` a finite field extension of `K`. One then builds a compositum
`M` of `L` and `E` over `K`:

* form the finite `E`-algebra `T = E ⊗[K] L`, finite over `E` by base change of the
  finite `K`-module `L`;
* `T` is a nonzero commutative ring, so it has a maximal ideal `I`; set `M = T ⧸ I`, a
  field finite-dimensional over `E`;
* the right inclusion `L → T → M` gives an injective `K`-algebra, hence `R`-algebra,
  map `φ : L →ₐ[R] M`, injective because it is a ring homomorphism out of the field `L`.

Since `S` is N-2 and `M/E` is a finite field extension, `integralClosure S M` is a
finite `S`-module. The core lemma `isN_core` then transports finiteness back down:
`integralClosure R L` embeds as an `R`-submodule of `integralClosure S M`, which is
`R`-finite because it is `S`-finite and `S` is `R`-finite, and `R` Noetherian makes the
submodule finite. Hence `integralClosure R L` is a finite `R`-module. -/
theorem isN2_step
    (R S L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field L] [Algebra (FractionRing R) L]
    [Algebra R L] [IsScalarTower R (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L]
    (hinj : Function.Injective (algebraMap R S))
    (hfin : Module.Finite R S)
    (hS : IsN2_032k S) : Module.Finite R (integralClosure R L) := by
  -- `IsN2_032k S` unfolds to the universe-coupled `IsN2Aux S`, which quantifies over
  -- fields in `S`'s own universe -- exactly what the shrunk compositum `N` needs.
  change IsN2Aux S at hS
  -- E := FractionRing S receives K = FractionRing R via the lifted structure map (as in N-1).
  obtain ⟨φ₀, -⟩ := exists_injective_algHom_fractionRing R S hinj
  let : Algebra (FractionRing R) (FractionRing S) := φ₀.toRingHom.toAlgebra
  have htow : IsScalarTower R (FractionRing R) (FractionRing S) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap R (FractionRing S) x = φ₀ (algebraMap R (FractionRing R) x)
    rw [AlgHom.commutes φ₀ x]
  -- Compositum T := E ⊗[K] L, finite over E; M := T ⧸ (maximal ideal) is a field.
  have : Module.Finite (FractionRing S) ((FractionRing S) ⊗[FractionRing R] L) :=
    Module.Finite.base_change (FractionRing R) (FractionRing S) L
  obtain ⟨I, hI⟩ := Ideal.exists_maximal ((FractionRing S) ⊗[FractionRing R] L)
  have : I.IsMaximal := hI
  let : Field (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) := Ideal.Quotient.field I
  -- Embedding φ : L →ₐ[R] M (right inclusion into the tensor product, then quotient).
  let incR : L →ₐ[FractionRing R] ((FractionRing S) ⊗[FractionRing R] L) :=
    Algebra.TensorProduct.includeRight
  let φ : L →ₐ[R] (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    ((Ideal.Quotient.mkₐ (FractionRing R) I).comp incR).restrictScalars R
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  -- `M := T ⧸ I` lives in universe `max u_S u_L`, so `hS M` would fail the (monomorphic)
  -- universe check of `IsN2_032k S` (which only quantifies over fields in S's own universe).
  -- Since `M` is finite-dimensional over `FractionRing S : Type u_S`, it is `Small.{u_S}`;
  -- shrink it to `N : Type u_S` (a `FractionRing S`-algebra-isomorphic copy), apply `hS`
  -- there, and transport the embedding `φ` and the finiteness conclusion across the equiv.
  have hMfin : Module.Finite (FractionRing S)
      (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ (FractionRing S) I).toLinearMap Ideal.Quotient.mk_surjective
  have hsmall : Small.{_} (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    small_of_finite_field (E := FractionRing S) (((FractionRing S) ⊗[FractionRing R] L) ⧸ I)
  -- universe-`u_S` model `N`, with the `FractionRing R`-algebra equivalence to `M`.
  let N := Shrink.{_} (((FractionRing S) ⊗[FractionRing R] L) ⧸ I)
  -- scalar towers on `N`, transported from the (universe-`max u_S u_L`) compositum.
  have towRFRN : IsScalarTower R (FractionRing R) N :=
    shrink_isScalarTower (R := R) (S := FractionRing R)
      (M := (((FractionRing S) ⊗[FractionRing R] L) ⧸ I))
  have towRSN : IsScalarTower R S N :=
    shrink_isScalarTower (R := R) (S := S) (M := (((FractionRing S) ⊗[FractionRing R] L) ⧸ I))
  have towSFSN : IsScalarTower S (FractionRing S) N :=
    shrink_isScalarTower (R := S) (S := FractionRing S)
      (M := (((FractionRing S) ⊗[FractionRing R] L) ⧸ I))
  let eFR : N ≃ₐ[FractionRing R] (((FractionRing S) ⊗[FractionRing R] L) ⧸ I) :=
    Shrink.algEquiv (FractionRing R) _
  -- transport the embedding `φ : L →ₐ[R] M` to `φN : L →ₐ[R] N`
  let φN : L →ₐ[R] N := (eFR.symm.toAlgHom.restrictScalars R).comp φ
  have hφNinj : Function.Injective φN := eFR.symm.injective.comp hφinj
  -- `N` is `FractionRing S`-algebra-isomorphic to the compositum, so it inherits its
  -- finite-dimensionality; this is the `[FiniteDimensional (FractionRing S) _]` argument
  -- of `IsN2Aux S`, which is not synthesized through `Shrink` on its own.
  have hNfin : Module.Finite (FractionRing S) N :=
    Module.Finite.equiv
      (Shrink.algEquiv (FractionRing S)
        (((FractionRing S) ⊗[FractionRing R] L) ⧸ I)).symm.toLinearEquiv
  -- now `N : Type u_S`, so S's N-2 hypothesis applies, and `isN_core` descends to `R ⊂ L`.
  have hSN : Module.Finite S (integralClosure S N) := @hS N _ _ _ towSFSN hNfin
  exact isN_core R S L N hfin φN hφNinj hSN

/-- **Statement 2 (N-2 descends, part of Stacks Tag 032K).**
Let `R` be a Noetherian domain and `R ⊂ S` a finite extension of domains
(modelled by an injective algebra map `R → S` with `S` finite over `R`).
If `S` is N-2, then `R` is N-2. -/
@[stacks 032K "(2)"]
theorem isN2_of_finite_of_isN2
    (R S : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S))
    (hfin : Module.Finite R S)
    (hS : IsN2_032k S) : IsN2_032k R := by
  -- N-2 means: for every finite field extension `L / FractionRing R`, the integral
  -- closure of `R` in `L` is `R`-finite.  Fix such an `L` and apply `isN2_step`.
  change IsN2Aux R
  intro L _ _ _ _ _
  exact isN2_step R S L hinj hfin hS

-- ===== merged from Sec161/Tag032M =====

/-!
# In characteristic zero, N-1 and N-2 agree

Let `R` be an integral domain with field of fractions `K = Frac R`.

`R` is *N-1* when the integral closure of `R` in `K` is a finite `R`-module, that is,
finitely generated as an `R`-module. The integral closure of a domain in its own
fraction field is its normalization, so `R` is N-1 exactly when its normalization is
module-finite over `R`. `R` is *N-2*, also called *Japanese*, when for every finite
field extension `L/K` the integral closure of `R` in `L` is a finite `R`-module.

The main result: let `R` be a Noetherian domain whose fraction field `K` has
characteristic zero. Then `R` is N-1 if and only if `R` is N-2.

That N-2 implies N-1 holds for any domain, by taking `L = K`. For the converse,
replace `R` by its normalization `R'`, which is finite over `R` by N-1; then `R'` is a
Noetherian normal domain with fraction field `K`, and for a finite extension `L/K` the
integral closure of `R` in `L` equals that of `R'` in `L`. Since `K` has characteristic
zero every finite extension `L/K` is separable, so the integral closure of `R'` in `L`
is finite over `R'`, hence over `R`.

Being a finite `R`-module is `Module.Finite R M`, and the integral closure of `R` in an
extension ring or field is the subalgebra `integralClosure R L` of elements integral
over `R`. The characteristic-zero hypothesis is placed on the fraction field `K`,
equivalently on `R`, and is used solely to guarantee separability of every finite
extension of `K`.
-/

@[expose] public section


-- Main Statement(s)

/-- Stacks Tag 032M, Lemma 10.161.11. For a Noetherian domain `R` whose fraction
field `K` has characteristic zero, `R` is N-1 if and only if `R` is N-2 (Japanese). -/
@[stacks 032M, ega "0 23.1.2" "special case"]
theorem N1_iff_N2 (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K] :
    IsN1_032m R K ↔ IsN2_032m R K := by
  constructor
  · -- N1 → N2. Replace R by its normalization R' = integralClosure R K, which is
    -- module-finite over R (the N-1 hypothesis), hence integral over R, integrally
    -- closed in K, and Noetherian. For a finite extension L/K, the integral closure
    -- C' = integralClosure R' L is finite over R' (Stacks 032L,
    -- `IsIntegralClosure.finite`; char 0 supplies separability), hence finite over R.
    -- The inclusion `integralClosure R L ↪ C'` is an injective R-linear map, so
    -- `Module.Finite.of_injective` gives the result.
    intro h L _ _ _ _ _
    set R' := integralClosure R K with hR'
    have hfin : Module.Finite R R' := h
    have hint : Algebra.IsIntegral R R' := Algebra.IsIntegral.of_finite R R'
    have hic : IsIntegrallyClosed R' := by
      rw [isIntegrallyClosed_iff K]
      exact fun {x} hx => ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
    have hnoeth : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
    exact isN_core R R' L L hfin (AlgHom.id R L) Function.injective_id
      (IsIntegralClosure.finite R' K L _)
  · -- N2 → N1: instantiate the N-2 hypothesis at L = K.
    exact fun h => h K

end
end
end

@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.show false


/-- The integral closure of a Noetherian normal domain in a finite separable
extension is finite over the base ring. -/
@[stacks 032L,
  ega "II 6.3.10" "special case",
  ega "II 7.3.12" "special case",
  ega "IV 14.5.5" "finiteness of A₁ over A",
  ega "IV 18.10.15" "partial"]
theorem Noetherian_normal_domain_finite_separable_extension
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L] :
    Module.Finite R (integralClosure R L) :=
  have : IsNoetherian R (integralClosure R L) :=
    IsIntegralClosure.isNoetherian R K L _
  Module.IsNoetherian.finite R _

end

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.LocalStructure
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
public import Mathlib.Topology.Sheaves.Init
public import StacksCore.Tactic.EgaSgaAttribute
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard étale ring maps

A ring map `R → S` is *standard étale* ([Stacks, Tag 00UB]) if `S ≅ R[x]_g/(f)` as `R`-algebras
for some `f, g : R[x]` with `f` monic and `f'` invertible in `R[x]_g/(f)`; this is Mathlib's
`Algebra.IsStandardEtale`. This file proves that an étale ring map is Zariski locally standard
étale ([Stacks, Tag 00UE]): if `R → S_{g₀}` is étale for some `g₀ ∉ q`, with `q ⊂ S` a prime,
then `R → S_g` is standard étale for some `g ∉ q`. The hypothesis is étaleness at `q` in the
sense of [Stacks, Tag 00U1], not Mathlib's `Algebra.IsEtaleAt`, which agrees with it only when `S`
is finitely presented over `R`. It also records the properties of standard étale ring maps listed
in [Stacks, Tag 00UC].

## Main definitions

* `StandardEtale.StandardEtaleAlg`: the ring `R[x]_g/(f)` presented by `f g : R[X]`.
* `StandardEtale.standardEtaleMap`: the structure map `R → R[x]_g/(f)`.

## Main results

* `Algebra.exists_isStandardEtale_of_exists_etale`: if `R → S_{g₀}` is étale for some `g₀ ∉ q`,
  then `R → S_g` is standard étale for some `g ∉ q`.
* `standardEtalePair_isEtale`: a standard étale ring map is étale.
* `standardEtalePair_baseChange_iso` and `standardEtalePair_baseChange_isStandardEtale`: the base
  change of `R[x]_g/(f)` along `R → T` is `T[x]_{g'}/(f')`, hence standard étale over `T`.
* `standardEtalePair_localizationAway`: a principal localization of a standard étale algebra is
  standard étale over the base.
* `standardEtale_not_isStableUnderComposition`: a composite of standard étale ring maps need not
  be standard étale; the composite `F₂ → F₄ → F₄ × F₄ × F₄ × F₄` is not.

## References

* [Stacks Project, Tag 00UE](https://stacks.math.columbia.edu/tag/00UE)
* [Stacks Project, Tag 00U1](https://stacks.math.columbia.edu/tag/00U1)
* [Stacks Project, Tag 00UB](https://stacks.math.columbia.edu/tag/00UB)
* [Stacks Project, Tag 00UC](https://stacks.math.columbia.edu/tag/00UC)

## Tags

étale, standard étale, étale locally, localization
-/

@[expose] public section

universe u v

namespace Stacks.Etale.LocallyStandardEtale

/-- Standard étaleness of a localization depends only on the submonoid inverted, not on the model:
if `T` and `T'` are both localizations of `S` at `M`, and `R → T` is standard étale, then so is
`R → T'`. -/
private lemma isStandardEtale_of_isLocalization {R S T T' : Type*} [CommRing R] [CommRing S]
    [CommRing T] [CommRing T'] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra S T'] [Algebra R T'] [IsScalarTower R S T'] (M : Submonoid S) [IsLocalization M T]
    [IsLocalization M T'] [Algebra.IsStandardEtale R T] : Algebra.IsStandardEtale R T' :=
  .of_equiv ((IsLocalization.algEquiv M T T').restrictScalars R)

/-- Let `T` be a localization of `S` away from `g`, let `Q ⊂ S` be a prime with `g ∉ Q`, and let
`f : T` lie outside `Q · T`. If `R → T_f` is standard étale, then `R → S_h` is standard étale for
some `h ∉ Q`. -/
private lemma exists_isStandardEtale_away_of_notMem_map {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (g : S)
    [IsLocalization.Away g T] (Q : Ideal S) [Q.IsPrime] (hg : g ∉ Q) {f : T}
    (hf : f ∉ Q.map (algebraMap S T)) [Algebra.IsStandardEtale R (Localization.Away f)] :
    ∃ h ∉ Q, Algebra.IsStandardEtale R (Localization.Away h) := by
  obtain ⟨a, hassoc⟩ : ∃ a : S, Associated (algebraMap S T a) f :=
    ⟨_, IsLocalization.Away.associated_sec_fst g f⟩
  have : IsLocalization.Away (g * a) (Localization.Away f) :=
    IsLocalization.Away.mul_of_associated (S := T) g a f hassoc
  exact ⟨g * a, ‹Q.IsPrime›.mul_notMem hg fun ha ↦
      hf ((Ideal.mem_iff_of_associated hassoc).1 (Ideal.mem_map_of_mem _ ha)),
    isStandardEtale_of_isLocalization (T := Localization.Away f) (.powers (g * a))⟩

/-- If `R → S_{g₀}` is étale for some `g₀ ∉ Q`, then `R → S_g` is standard étale for some
`g ∉ Q`. -/
public theorem solution {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (Q : Ideal S) [Q.IsPrime]
    (hQ : ∃ g ∉ Q, Algebra.Etale R (Localization.Away g)) :
    ∃ g ∉ Q, Algebra.IsStandardEtale R (Localization.Away g) := by
  obtain ⟨g₀, hg₀, _⟩ := hQ
  have : (Q.map (algebraMap S (Localization.Away g₀))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers g₀) _ _ ‹Q.IsPrime›
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg₀)
  obtain ⟨f, hf, _⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R)
    (Q.map (algebraMap S (Localization.Away g₀)))
  exact exists_isStandardEtale_away_of_notMem_map g₀ Q hg₀ hf

end Stacks.Etale.LocallyStandardEtale

@[expose] public section

/-- Let `R → S` be a ring map and `q ⊂ S` a prime. If `R → S` is étale at `q`, that is, if
`R → S_g` is étale for some `g ∈ S` with `g ∉ q`, then there is a `g ∈ S`, `g ∉ q`,
such that `R → S_g` is standard étale. -/
@[stacks 00UE "The hypothesis \"étale at `q`\" is Definition 00U1 verbatim,
`∃ g ∉ Q, Algebra.Etale R (Localization.Away g)`, rather than Mathlib's `Algebra.IsEtaleAt`, which
is `Algebra.FormallyEtale R S_Q` and agrees with it only for `S` finitely presented over `R`; the
source assumes no finiteness on `S`, so this is strictly more general than Mathlib's
`Algebra.IsEtaleAt.exists_isStandardEtale` and implies it. `S_g` is `Localization.Away g` with its
`R`-algebra structure the composite `R → S → S_g`. See the module docstring."]
public theorem Algebra.exists_isStandardEtale_of_exists_etale {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] (Q : Ideal S) [Q.IsPrime]
    (hQ : ∃ g ∉ Q, Algebra.Etale R (Localization.Away g)) :
    ∃ g ∉ Q, Algebra.IsStandardEtale R (Localization.Away g) :=
  Stacks.Etale.LocallyStandardEtale.solution Q hQ

end

end

/-!
### Standard étale ring maps

`R → S` is standard étale when `S ≅ R[x]_g/(f)` over `R` for some monic
`f : R[X]` and some `g : R[X]` making `f'` invertible in `R[x]_g/(f)` — is Mathlib's
vocabulary: `StandardEtalePair` is the pair `(f, g)` (its `cond` field, a Bézout identity
`f' p₁ + f p₂ = gⁿ`, is equivalent to `f'` being a unit in `R[x]_g/(f)`),
`StandardEtalePair.equivAwayQuotient` identifies its `Ring` with `R[X][1/g]/(f)`, and
`Algebra.IsStandardEtale` is the resulting property of an `R`-algebra.
-/

@[expose] public section

add_to_stacks 00UB "the property of an `R`-algebra" Algebra.IsStandardEtale
add_to_stacks 00UB "the pair `(f, g)`" StandardEtalePair
add_to_stacks 00UB "its ring, as `R[x]_g/(f)`" StandardEtalePair.equivAwayQuotient

namespace StandardEtale

open Polynomial

/-- The ring `R[x]_g/(f)` presented by a pair of polynomials `f g : R[X]`, as the quotient of
the localization `R[X][1/g]` by the ideal generated by the image of `f`. -/
public abbrev StandardEtaleAlg (R : Type*) [CommRing R] (f g : R[X]) : Type _ :=
  (Localization.Away g) ⧸ Ideal.span {(algebraMap R[X] (Localization.Away g)) f}

/-- The structure map `R → R[x]_g/(f)`, the composite of the coefficient inclusion
`R → R[X]`, the localization map and the quotient map. -/
public noncomputable def standardEtaleMap (R : Type*) [CommRing R] (f g : R[X]) :
    R →+* StandardEtaleAlg R f g :=
  (Ideal.Quotient.mk _).comp ((algebraMap R[X] (Localization.Away g)).comp (algebraMap R R[X]))

end StandardEtale

end

@[expose] public section

open Algebra Polynomial
open scoped TensorProduct Bivariate

/-!
### The vocabulary

The relevant definitions live in `Mathlib.RingTheory.Etale.StandardEtale`.

* `StandardEtalePair R` packages a monic polynomial `f : R[X]` (field `monic_f`) together with
  `g : R[X]` such that the formal derivative `f'` is invertible in `R[X][1/g]/(f)`, encoded by
  the Bézout-type condition `cond : ∃ p₁ p₂ n, derivative f * p₁ + f * p₂ = g ^ n`. Its
  associated ring `(P : StandardEtalePair R).Ring` is `R[X][Y]/(C f, Y * C g - 1)`, canonically
  the ring `R[x]_g/(f)`: `StandardEtalePair.equivAwayQuotient` exhibits it as `R[X][1/g]/(f)`
  and `StandardEtalePair.equivAwayAdjoinRoot` exhibits it as `(R[X]/(f))[1/ḡ]`.

* `StandardEtalePair.map (φ : R →+* S) : StandardEtalePair S` transports a pair along a ring
  map, with `(P.map φ).f = P.f.map φ` and `(P.map φ).g = P.g.map φ`, modelling the base-changed
  pair `(f', g')` of statement (2).

* `Algebra.IsStandardEtale R S` says that `S` is `R`-algebra isomorphic to the ring of some
  standard étale pair over `R`.

* `Algebra.Etale R S` is étaleness.
-/

-- The polynomial `f` of a standard étale pair `(f, g)` is monic.
example {R : Type*} [CommRing R] (P : StandardEtalePair R) : P.f.Monic := P.monic_f

-- The associated `R`-algebra `R[x]_g/(f)`, realized as `R[X][1/g]/(f)`.
noncomputable example {R : Type*} [CommRing R] (P : StandardEtalePair R) :
    P.Ring ≃ₐ[R] Localization.Away P.g ⧸
      Ideal.span {algebraMap _ (Localization.Away P.g) P.f} :=
  P.equivAwayQuotient

-- Standard étaleness as a property of an `R`-algebra `S`.
example {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Algebra.IsStandardEtale R S

/-! ### Standard étale implies étale -/

/-- For an explicit standard étale pair `(f, g)` over `R`, the canonical map
`R → R[x]_g/(f)` is étale. -/
@[stacks 00UC "(1)", ega "IV 18.4.3" "(F)", sga "1 I 7.3" "partial", sga "1 I 7.4" "partial"]
theorem standardEtalePair_isEtale {R : Type*} [CommRing R] (P : StandardEtalePair R) :
    Algebra.Etale R P.Ring :=
  StandardEtalePair.instEtaleRing P

/-! ### Base change of standard étale is standard étale -/

/-- For a standard étale pair `(f, g)` over `R` and an `R`-algebra `T`, there is a `T`-algebra
isomorphism `T ⊗[R] (R[x]_g/(f)) ≅ T[x]_{g'}/(f')`, where `f', g' : T[x]` are the images of
`f, g`, that is, the ring of the pair `P.map (algebraMap R T)`. -/
theorem standardEtalePair_baseChange_iso {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] (P : StandardEtalePair R) :
    Nonempty ((T ⊗[R] P.Ring) ≃ₐ[T] (P.map (algebraMap R T)).Ring) := by
  let pres : StandardEtalePresentation R P.Ring :=
    { P := P, x := P.X, hasMap := StandardEtalePair.hasMap_X,
      lift_bijective := by
        rw [StandardEtalePair.lift_X_left P]; exact Function.bijective_id }
  exact ⟨(pres.baseChange (T := T)).equivRing⟩

/-- The base change `T ⊗[R] (R[x]_g/(f))` is standard étale over `T`. -/
@[stacks 00UC "(2)", sga "1 IX 1.3" "standard étale case"]
theorem standardEtalePair_baseChange_isStandardEtale {R T : Type*} [CommRing R]
    [CommRing T] [Algebra R T] (P : StandardEtalePair R) :
    Algebra.IsStandardEtale T (T ⊗[R] P.Ring) :=
  instIsStandardEtaleTensorProduct

/-! ### Principal localizations of a standard étale algebra -/

/-- For a standard étale pair `(f, g)` over `R` with ring `A = R[x]_g/(f)` and any `α : A`, the
composite `R → A → A[1/α]` is standard étale. -/
@[stacks 00UC "(3)"]
theorem standardEtalePair_localizationAway {R : Type*} [CommRing R]
    (P : StandardEtalePair R) (α : P.Ring)
    (Aα : Type*) [CommRing Aα] [Algebra P.Ring Aα] [Algebra R Aα]
    [IsScalarTower R P.Ring Aα] [IsLocalization.Away α Aα] :
    Algebra.IsStandardEtale R Aα :=
  IsStandardEtale.of_isLocalizationAway α

/-! ### Composites of standard étale ring maps -/

/-- An étale algebra generated by a root of a monic separable polynomial is standard étale. -/
private theorem isStandardEtale_of_adjoin_root {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] {f : R[X]} (hfmonic : f.Monic) (hsep : f.Separable) {x : S}
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) : Algebra.IsStandardEtale R S := by
  obtain ⟨a, b, hab⟩ := hsep
  let P : StandardEtalePair R :=
    { f := f
      monic_f := hfmonic
      g := 1
      cond := ⟨b, a, 1, by linear_combination hab⟩ }
  have hmap : P.HasMap x := ⟨hx, by simp [P]⟩
  refine Algebra.IsStandardEtale.of_surjective (P.lift x hmap) ?_
  rw [← AlgHom.range_eq_top, _root_.eq_top_iff, ← hadj, Algebra.adjoin_le_iff,
    Set.singleton_subset_iff]
  exact ⟨P.X, P.lift_X x hmap⟩

/-- `F₂ → F₄` (i.e. `ZMod 2 → GaloisField 2 2`) is standard étale. -/
theorem isStandardEtale_F2_F4 :
    Algebra.IsStandardEtale (ZMod 2) (GaloisField 2 2) := by
  set pb := Field.powerBasisOfFiniteOfSeparable (ZMod 2) (GaloisField 2 2)
  have hint : IsIntegral (ZMod 2) pb.gen := Algebra.IsIntegral.isIntegral pb.gen
  set f : (ZMod 2)[X] := minpoly (ZMod 2) pb.gen with hf
  have hfmonic : f.Monic := minpoly.monic hint
  have hsep : f.Separable := Algebra.IsSeparable.isSeparable (ZMod 2) pb.gen
  have : Algebra.Etale (ZMod 2) (GaloisField 2 2) :=
    ⟨Algebra.FormallyEtale.of_isSeparable _ _,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact isStandardEtale_of_adjoin_root hfmonic hsep (minpoly.aeval _ _) pb.adjoin_gen_eq_top

/-- For an injective `e : ι → K` into a field, `e` generates `ι → K` as a `K`-algebra. -/
theorem adjoin_singleton_eq_top_of_injective {K ι : Type*} [Field K] [Finite ι]
    {e : ι → K} (he : Function.Injective e) : Algebra.adjoin K {e} = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  have hinjon : Set.InjOn e (Finset.univ : Finset ι) := Set.injOn_of_injective he
  have hlag : ∀ j, (aeval e) (Lagrange.basis Finset.univ e j) = Pi.single j 1 := by
    intro j
    funext i
    rw [Polynomial.aeval_pi_apply₂]
    have hev : (aeval (e i)) (Lagrange.basis Finset.univ e j)
        = eval (e i) (Lagrange.basis Finset.univ e j) := by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [hev, Pi.single_apply]
    by_cases hij : i = j
    · subst hij
      rw [Lagrange.eval_basis_self hinjon (Finset.mem_univ i)]
      simp
    · rw [Lagrange.eval_basis_of_ne (fun h => hij h.symm) (Finset.mem_univ i), ite_eq_right hij]
  have hsingle : ∀ j, Pi.single j 1 ∈ Algebra.adjoin K {e} := fun j =>
    hlag j ▸ aeval_mem_adjoin_singleton K e
  rw [_root_.eq_top_iff]
  rintro v -
  rw [← Finset.univ_sum_single v]
  refine Subalgebra.sum_mem _ fun j _ => ?_
  have heq : Pi.single j (v j) = (algebraMap K (ι → K) (v j)) * Pi.single j (1 : K) := by
    funext i
    simp only [Pi.mul_apply, Pi.single_apply, Pi.algebraMap_apply]
    by_cases h : i = j <;> simp [h]
  rw [heq]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hsingle j)

/-- The diagonal map `F₄ → F₄^{×4}` (`GaloisField 2 2 → Fin 4 → GaloisField 2 2`) is
standard étale. -/
theorem isStandardEtale_F4_F4pow4 :
    Algebra.IsStandardEtale (GaloisField 2 2) (Fin 4 → GaloisField 2 2) := by
  set K := GaloisField 2 2
  have : Fintype K := Fintype.ofFinite _
  have hcard : Fintype.card K = 4 := by
    simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 2 (by norm_num)
  set e : Fin 4 ≃ K := (Fintype.equivFinOfCardEq hcard).symm
  set f : K[X] := ∏ i : Fin 4, (X - C (e i)) with hf
  have hfmonic : f.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (e i)
  have hsep : f.Separable := Polynomial.separable_prod_X_sub_C_iff.2 e.injective
  set x : Fin 4 → K := ⇑e with hx
  refine isStandardEtale_of_adjoin_root (x := x) hfmonic hsep ?_
    (adjoin_singleton_eq_top_of_injective e.injective)
  funext j
  rw [Polynomial.aeval_pi_apply₂]
  show (aeval (x j)) f = 0
  rw [hf, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hx])

/-- In `R[X][X]`, the two variables `C X` and `X` generate everything as an `R`-algebra. -/
theorem Polynomial.adjoin_C_X_X_eq_top {R : Type*} [CommRing R] :
    Algebra.adjoin R ({C X, X} : Set R[X][X]) = ⊤ := by
  rw [_root_.eq_top_iff]
  rintro p -
  induction p using Polynomial.induction_on with
  | C a =>
    induction a using Polynomial.induction_on with
    | C r => exact Subalgebra.algebraMap_mem _ r
    | add p q hp hq => rw [map_add]; exact Subalgebra.add_mem _ hp hq
    | monomial n r ih =>
      have heq : (C (C r * X ^ (n + 1)) : R[X][X]) = C (C r * X ^ n) * C X := by
        rw [← map_mul]; congr 1; ring
      rw [heq]
      exact Subalgebra.mul_mem _ ih (Algebra.subset_adjoin (by simp))
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | monomial n r ih =>
    rw [show (C r * X ^ (n + 1) : R[X][X]) = C r * X ^ n * X by ring]
    exact Subalgebra.mul_mem _ ih (Algebra.subset_adjoin (by simp))

/-- Over a field, a right inverse of an integral element `u` lies in `Algebra.adjoin R {u}`. -/
theorem mem_adjoin_singleton_of_mul_eq_one {R S : Type*} [Field R] [CommRing S] [Nontrivial S]
    [Algebra R S] {u v : S} (hu : IsIntegral R u) (hv : u * v = 1) :
    v ∈ Algebra.adjoin R {u} := by
  set m := minpoly R u
  have hsplit : m = X * m.divX + C (m.coeff 0) := (Polynomial.X_mul_divX_add m).symm
  set a0 := m.coeff 0
  have key : u * (aeval u m.divX) + algebraMap R S a0 = 0 := by
    have hh : aeval u m = 0 := minpoly.aeval R u
    rw [hsplit] at hh
    simpa [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] using hh
  have hdeg_pos : 0 < m.natDegree := minpoly.natDegree_pos hu
  have ha0ne : a0 ≠ 0 := by
    intro h0
    rw [h0] at key
    simp only [map_zero, add_zero] at key
    have hdiv0 : aeval u m.divX = 0 := by
      have hh : v * (u * aeval u m.divX) = v * 0 := by rw [key]
      rwa [mul_zero, ← mul_assoc, mul_comm v u, hv, one_mul] at hh
    have hdivne : m.divX ≠ 0 := by
      intro hc
      have hmc : m = C a0 := by rw [hsplit, hc]; ring
      simp [hmc] at hdeg_pos
    exact (Polynomial.degree_divX_lt (minpoly.monic hu).ne_zero).not_ge
      (Polynomial.degree_le_of_dvd (minpoly.dvd R u hdiv0) hdivne)
  set w : S := - aeval u m.divX with hw
  have key2 : u * w = algebraMap R S a0 := by
    rw [hw, mul_neg, eq_neg_of_add_eq_zero_left key, neg_neg]
  have hinv : algebraMap R S a0⁻¹ * algebraMap R S a0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha0ne, map_one]
  have hveq : v = algebraMap R S a0⁻¹ * w := by
    linear_combination (-v) * hinv - (algebraMap R S a0⁻¹ * v) * key2 +
      (algebraMap R S a0⁻¹ * w) * hv
  rw [hveq, hw]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.neg_mem _ (aeval_mem_adjoin_singleton R u))

/-- If `F₄^{×4}` is standard étale over `F₂` then it is generated by a single integral
element. -/
theorem exists_adjoin_singleton_eq_top_of_isStandardEtale_F2
    (h : Algebra.IsStandardEtale (ZMod 2) (Fin 4 → GaloisField 2 2)) :
    ∃ x : (Fin 4 → GaloisField 2 2),
      Algebra.adjoin (ZMod 2) {x} = ⊤ ∧ IsIntegral (ZMod 2) x := by
  obtain ⟨pres⟩ := h.nonempty_standardEtalePresentation
  set P := pres.P
  set x := pres.x
  have hmap := pres.hasMap
  have hf0 : (aeval x) P.f = 0 := hmap.left
  have hint : IsIntegral (ZMod 2) x := ⟨P.f, P.monic_f, hf0⟩
  set φ := P.lift x hmap
  have hsurj : Function.Surjective φ := pres.lift_bijective.surjective
  refine ⟨x, ?_, hint⟩
  set theY : P.Ring := Ideal.Quotient.mk (Ideal.span {C P.f, X * C P.g - 1}) X with hY
  set y : (Fin 4 → GaloisField 2 2) := φ theY with hyDef
  have hYrel : (aeval x) P.g * y = 1 := by
    have : φ ((aeval P.X) P.g * theY) = φ 1 := congrArg φ P.aeval_X_g_mul_mk_X
    rwa [map_mul, map_one, ← Polynomial.aeval_algHom_apply, P.lift_X x hmap] at this
  have huint : IsIntegral (ZMod 2) ((aeval x) P.g) :=
    Algebra.adjoin_le (R := ZMod 2) (S := integralClosure (ZMod 2) _)
      (Set.singleton_subset_iff.2 hint) (aeval_mem_adjoin_singleton _ x)
  have hyadj : y ∈ Algebra.adjoin (ZMod 2) {x} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 (aeval_mem_adjoin_singleton _ x))
      (mem_adjoin_singleton_of_mul_eq_one huint hYrel)
  have hgenP : Algebra.adjoin (ZMod 2) ({P.X, theY} : Set P.Ring) = ⊤ := by
    have hmap2 := AlgHom.map_adjoin (Ideal.Quotient.mkₐ (ZMod 2)
      (Ideal.span {C P.f, X * C P.g - 1})) ({C X, X} : Set ((ZMod 2)[X][X]))
    rw [Polynomial.adjoin_C_X_X_eq_top, Algebra.map_top] at hmap2
    rw [(AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective (ZMod 2) _),
      Set.image_pair] at hmap2
    exact hmap2.symm
  have hxy : Algebra.adjoin (ZMod 2) ({x, y} : Set (Fin 4 → GaloisField 2 2)) = ⊤ := by
    have hPX : φ P.X = x := P.lift_X x hmap
    have hmap3 := AlgHom.map_adjoin φ ({P.X, theY} : Set P.Ring)
    rw [hgenP, Algebra.map_top, (AlgHom.range_eq_top φ).mpr hsurj, Set.image_pair, hPX] at hmap3
    exact hmap3.symm
  rw [_root_.eq_top_iff, ← hxy]
  exact Algebra.adjoin_le (Set.pair_subset (Algebra.self_mem_adjoin_singleton _ x) hyadj)

/-- If `x` is integral over a field `K` and generates `A`, then `finrank K A` is at most the
degree of the minimal polynomial of `x`. -/
theorem finrank_le_natDegree_minpoly_of_adjoin_eq_top {K A : Type*} [Field K] [CommRing A]
    [Nontrivial A] [Algebra K A] {x : A} (hx_top : Algebra.adjoin K {x} = ⊤)
    (hx_int : IsIntegral K x) : Module.finrank K A ≤ (minpoly K x).natDegree := by
  set d := (minpoly K x).natDegree with hd
  have hdpos := minpoly.natDegree_pos hx_int
  have hd0 : d ≠ 0 := by omega
  have hmonic := minpoly.monic hx_int
  have hne1 : minpoly K x ≠ 1 := by
    intro hcon; rw [hcon] at hd; simp at hd; omega
  have hspan : Submodule.span K (Set.range (fun i : Fin d => x ^ (i : ℕ))) = ⊤ := by
    rw [_root_.eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin K ({x} : Set _) := by rw [hx_top]; trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := hy
    rw [show (aeval x).toRingHom f = (aeval x) (f %ₘ minpoly K x) by simp,
      PowerBasis.mem_span_pow hd0]
    exact ⟨f %ₘ minpoly K x, Polynomial.natDegree_modByMonic_lt f hmonic hne1, rfl⟩
  simpa using finrank_le_of_span_eq_top hspan

/-- With `F₂ = ZMod 2`, `F₄ = GaloisField 2 2` and `F₄ → F₄^{×4} = (Fin 4 → GaloisField 2 2)` the
diagonal map, `F₂ → F₄` and `F₄ → F₄^{×4}` are standard étale but the composite `F₂ → F₄^{×4}` is
not. -/
theorem standardEtale_F2_F4_counterexample :
    Algebra.IsStandardEtale (ZMod 2) (GaloisField 2 2) ∧
    Algebra.IsStandardEtale (GaloisField 2 2) (Fin 4 → GaloisField 2 2) ∧
    ¬ Algebra.IsStandardEtale (ZMod 2) (Fin 4 → GaloisField 2 2) := by
  refine ⟨isStandardEtale_F2_F4, isStandardEtale_F4_F4pow4, fun h => ?_⟩
  obtain ⟨x, hx_top, hx_int⟩ := exists_adjoin_singleton_eq_top_of_isStandardEtale_F2 h
  have hpow : x ^ 4 = x := by
    funext i
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have hc : Fintype.card (GaloisField 2 2) = 4 := by
      simpa [Nat.card_eq_fintype_card] using GaloisField.card 2 2 (by norm_num)
    rw [Pi.pow_apply, ← hc]
    exact FiniteField.pow_card _
  have hdeg : (minpoly (ZMod 2) x).natDegree ≤ 4 := by
    have hroot : (Polynomial.aeval x) (X ^ 4 - X : (ZMod 2)[X]) = 0 := by simp [hpow]
    have hdeg4 : (X ^ 4 - X : (ZMod 2)[X]).natDegree = 4 := by compute_degree!
    have hne : (X ^ 4 - X : (ZMod 2)[X]) ≠ 0 := fun hh => by simp [hh] at hdeg4
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd (ZMod 2) x hroot) hne).trans_eq hdeg4
  have hfr_le := finrank_le_natDegree_minpoly_of_adjoin_eq_top hx_top hx_int
  have hfr_eq : Module.finrank (ZMod 2) (Fin 4 → GaloisField 2 2) = 8 := by
    rw [Module.finrank_pi_fintype]
    simp [GaloisField.finrank (p := 2) (n := 2) (by norm_num)]
  omega

/-- There exist commutative rings `R, S, T` with algebra structures forming a scalar tower
`R → S → T` such that `R → S` and `S → T` are standard étale but the composite `R → T` is not. -/
@[stacks 00UC "(4)"]
theorem standardEtale_not_isStableUnderComposition :
    ∃ (R S T : Type) (_ : CommRing R) (_ : CommRing S) (_ : CommRing T)
      (_ : Algebra R S) (_ : Algebra S T) (_ : Algebra R T) (_ : IsScalarTower R S T),
      Algebra.IsStandardEtale R S ∧ Algebra.IsStandardEtale S T ∧
        ¬ Algebra.IsStandardEtale R T :=
  ⟨ZMod 2, GaloisField 2 2, Fin 4 → GaloisField 2 2, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, standardEtale_F2_F4_counterexample⟩

end

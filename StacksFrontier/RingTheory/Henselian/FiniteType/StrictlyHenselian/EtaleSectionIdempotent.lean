module

import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.Away.Lemmas
import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksFrontier.RingTheory.Henselian.FiniteType.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale sections and idempotents over a henselian local ring

Hensel root lifts for standard-étale pairs, sections of étale algebras with trivial residue
extension, and the resulting idempotents `e ∉ q` cutting out a finite corner at a prime `q`
at which `R → S` is quasi-finite; the finiteness of the set of such primes over `m`.
-/

section

universe u

@[expose] public section

open IsLocalRing

/-- **Hensel root lift for a standard-étale pair.**
Given a henselian local ring `R` and a standard-étale pair `Pair : StandardEtalePair R`
(`Pair.f` monic, `Pair.g` with the standard-étale condition `f' p₁ + f p₂ = g^n`),
together with a residue point `xbar ∈ κ = ResidueField R` satisfying `Pair.HasMap xbar`
(i.e. `aeval xbar Pair.f = 0 ∧ IsUnit (aeval xbar Pair.g)`), there is a genuine element
`a ∈ R` with `Pair.HasMap a` (`aeval a Pair.f = 0 ∧ IsUnit (aeval a Pair.g)`).

The proof is a single application of `HenselianLocalRing.is_henselian`: lift `xbar` to
`a₀ ∈ R` (residue map surjective); `aeval xbar Pair.f = 0` gives `eval a₀ Pair.f ∈ m` (mk
commutes with aeval); the standard-étale condition
`f' p₁ + f p₂ = g^n` with `IsUnit (aeval xbar g)` and `aeval xbar f = 0` forces
`aeval xbar f' ≠ 0`, i.e. `eval a₀ Pair.f.derivative ∉ m`, so `IsUnit (eval a₀ f')`
(`R` local). `HenselianLocalRing.is_henselian Pair.f Pair.monic_f a₀` then yields a root
`a` with `Pair.f.IsRoot a` and `a - a₀ ∈ m`; `IsUnit (aeval a Pair.g)` follows since
`a ≡ a₀ ≡ xbar (mod m)` and `aeval xbar Pair.g` is a unit (units lift along `R → κ`). -/
@[ega "IV 18.5.11" "(f), special case",
  ega "IV 18.5.17" "special case",
  sga "3 X 8.9" "special case",
  sga "3 XI 1.11" "special case",
  sga "7 XV 1.1.2" "special case"]
theorem henselian_standardEtale_root (R : Type u) [CommRing R] [HenselianLocalRing R]
    (Pair : StandardEtalePair R) (xbar : ResidueField R) (hx : Pair.HasMap xbar) :
    ∃ a : R, Pair.HasMap a ∧ algebraMap R (ResidueField R) a = xbar := by
  -- The standard-étale condition forces `f'(xbar)` to be a unit in `κ`, so ordinary
  -- `HenselianLocalRing.is_henselian` suffices (no strict henselianness needed). The
  -- conclusion also returns `algebraMap R κ a = xbar`, the residue link that pins `a` to
  -- `P`'s fibre point.
  -- `aeval` over the residue field commutes with `eval` via the residue map.
  have comm :
    ∀ (b : R) (q : Polynomial R),
      Polynomial.aeval (algebraMap R (ResidueField R) b) q =
        algebraMap R (ResidueField R) (Polynomial.eval b q) := by
    intro b q
    rw [Polynomial.aeval_algebraMap_apply]
    congr 1
  have zero_iff : ∀ (x : R), algebraMap R (ResidueField R) x = 0 ↔ x ∈ maximalIdeal R := fun x =>
    Ideal.Quotient.eq_zero_iff_mem
  -- Lift `xbar` to `a₀ ∈ R`.
  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective xbar
  have hxa : algebraMap R (ResidueField R) a₀ = xbar := ha₀
  obtain ⟨hf0, hgu⟩ := hx
  -- `f(a₀) ∈ m`.
  have hfmem : Polynomial.eval a₀ Pair.f ∈ maximalIdeal R := by
    rw [← zero_iff]
    have h := comm a₀ Pair.f
    rw [hxa, hf0] at h
    exact h.symm
  -- The standard-étale condition forces `f'(xbar)` to be a unit in `κ`.
  obtain ⟨p₁, p₂, n, hcond⟩ := Pair.cond
  have hderiv_unit : IsUnit (Polynomial.aeval xbar (Polynomial.derivative Pair.f)) := by
    have key :
      Polynomial.aeval xbar (Polynomial.derivative Pair.f) * Polynomial.aeval xbar p₁ =
        (Polynomial.aeval xbar Pair.g) ^ n := by
      have := congrArg (Polynomial.aeval xbar) hcond
      simp only [map_add, map_mul, map_pow] at this
      rw [hf0] at this
      simpa using this
    have hrhs : IsUnit ((Polynomial.aeval xbar Pair.g) ^ n) := hgu.pow n
    rw [← key] at hrhs
    exact isUnit_of_mul_isUnit_left hrhs
  -- Hence `f'(a₀) ∉ m`, so `IsUnit (eval a₀ f')`.
  have lift_unit : ∀ (b : R) (q : Polynomial R), algebraMap R (ResidueField R) b = xbar →
      IsUnit (Polynomial.aeval xbar q) → IsUnit (Polynomial.eval b q) := by
    intro b q hb hq
    rw [← notMem_maximalIdeal, ← zero_iff]
    intro hzero
    rw [← hb, comm, hzero] at hq
    exact not_isUnit_zero hq
  have hderiv_eval_unit : IsUnit (Polynomial.eval a₀ (Polynomial.derivative Pair.f)) :=
    lift_unit a₀ _ hxa hderiv_unit
  -- The single henselian root lift.
  obtain ⟨a, haroot, hadiff⟩ :=
    HenselianLocalRing.is_henselian Pair.f Pair.monic_f a₀ hfmem hderiv_eval_unit
  have hmk : algebraMap R (ResidueField R) a = xbar := by
    rw [← hxa, ← sub_eq_zero, ← map_sub, zero_iff]
    exact hadiff
  refine ⟨a, ⟨?_, ?_⟩, hmk⟩
  · -- `aeval a Pair.f = 0`.
    exact haroot
  · -- `IsUnit (aeval a Pair.g)`: since `a ≡ a₀ ≡ xbar (mod m)`.
    exact lift_unit a _ hmk hgu

/-- **Existence of the residue point, with the fibre-uniqueness link.**
The bijective residue map `κ ≅ κ(P)` provides a residue value `xbar ∈ κ` of the
presentation generator `pres.x` such that `pres.P.HasMap xbar`, together with the link to
`P`: `xbar` equals the value at `P` of `pres.x` transported to `κ` along `hbij⁻¹` and the
localization-stable residue. The ingredients are that localization survives `LiesOver`, that
the residue field is unchanged under `Localization.Away f` for `f ∉ P`, and `HasMap.map`
along the residue `AlgHom`. The witness `xbar` is the residue of `pres.x` at `P`, so any
root `a` with `residue a = xbar` agrees with `P`'s residue point on the generator. -/
theorem standardEtale_pres_residue_hasMap_linked (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (f : R')
    (pres : StandardEtalePresentation R (Localization.Away f)) (P : Ideal R') [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] (hfP : f ∉ P)
    (hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R') (Ideal.LiesOver.over))) :
    ∃ xbar : ResidueField R,
      pres.P.HasMap xbar ∧
        ∀ (a : R) (ha : pres.P.HasMap a),
          algebraMap R (ResidueField R) a = xbar →
            ∀ y : R',
              (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
                  ((algebraMap R (ResidueField R))
                    ((((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
                        (IsScalarTower.toAlgHom R R' (Localization.Away f)))
                      y)) =
                ((AlgEquiv.ofBijective
                        (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R')
                          (Ideal.LiesOver.over))
                        hbij).symm.toRingHom.comp
                    (algebraMap R' P.ResidueField))
                  y := by
  -- Fibre-point uniqueness: the residue link `algebraMap R κ a = xbar` makes residue-equal
  -- roots induce the SAME κ-point on the single standard-étale generator, hence the same
  -- map. Both sides of the resulting equality land in `(maximalIdeal R).ResidueField`.
  -- f is a unit in P.ResidueField
  have hu : IsUnit ((algebraMap R' P.ResidueField) f) := by
    have hfP' := hfP
    rw [← Ideal.ker_algebraMap_residueField P, RingHom.mem_ker] at hfP'
    exact Ne.isUnit hfP'
  set φ :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R') (Ideal.LiesOver.over))
      hbij with
    hφ
  -- the bridge βAlg : ResidueField R ≃ₐ[R] (maximalIdeal R).ResidueField
  let βAlg : ResidueField R ≃ₐ[R] (maximalIdeal R).ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (ResidueField R) (maximalIdeal R).ResidueField)
      (by
        rw [IsScalarTower.coe_toAlgHom']
        exact Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))
  have hβ :
    ∀ x : ResidueField R,
      βAlg x = algebraMap (ResidueField R) (maximalIdeal R).ResidueField x := by
    intro x; change (IsScalarTower.toAlgHom R (ResidueField R) (maximalIdeal R).ResidueField) x = _
    rw [IsScalarTower.coe_toAlgHom']
  -- ρ' : Localization.Away f →ₐ[R] P.ResidueField, factoring algebraMap R' P.ResidueField
  let ρ' : Localization.Away f →ₐ[R] P.ResidueField :=
    IsLocalization.liftAlgHom (A := R) (f := IsScalarTower.toAlgHom R R' P.ResidueField) (M :=
      Submonoid.powers f)
      (by
        intro y
        obtain ⟨n, hn⟩ := y.property
        simp only [IsScalarTower.coe_toAlgHom']
        rw [← hn]
        show IsUnit ((algebraMap R' P.ResidueField) (f ^ n))
        rw [map_pow]; exact hu.pow n)
  have hρ'comm :
    ∀ y : R', ρ' (algebraMap R' (Localization.Away f) y) = algebraMap R' P.ResidueField y := by
    intro y
    show IsLocalization.liftAlgHom _ _ = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]; rfl
  -- g₂ : Localization.Away f →ₐ[R] ResidueField R
  let g₂ : Localization.Away f →ₐ[R] ResidueField R :=
    βAlg.symm.toAlgHom.comp (φ.symm.toAlgHom.comp ρ')
  refine ⟨g₂ pres.x, ?_, ?_⟩
  · -- HasMap (g₂ pres.x)
    exact pres.hasMap.map g₂
  · intro a ha hax y
    -- Φ₁ : Localization.Away f →ₐ[R] ResidueField R
    let Φ₁ : Localization.Away f →ₐ[R] ResidueField R :=
      (Algebra.ofId R (ResidueField R)).comp ((pres.P.lift a ha).comp pres.equivRing.toAlgHom)
    -- Φ₁ = g₂  via hom_ext on the generator pres.x
    have hΦ : Φ₁ = g₂ := by
      apply pres.hom_ext
      change
        (Algebra.ofId R (ResidueField R)) ((pres.P.lift a ha) (pres.equivRing pres.x)) = g₂ pres.x
      rw [pres.equivRing_x, StandardEtalePair.lift_X]
      show algebraMap R (ResidueField R) a = g₂ pres.x
      rw [hax]
    -- evaluate Φ₁ at loc y
    have hΦ₁eval :
      Φ₁ (algebraMap R' (Localization.Away f) y) =
        algebraMap R (ResidueField R)
          (((pres.P.lift a ha).comp pres.equivRing.toAlgHom)
            (algebraMap R' (Localization.Away f) y)) :=
      rfl
    -- g₂ at loc y
    have hg₂eval :
      g₂ (algebraMap R' (Localization.Away f) y) =
        βAlg.symm (φ.symm (algebraMap R' P.ResidueField y)) := by
      show βAlg.symm.toAlgHom (φ.symm.toAlgHom (ρ' (algebraMap R' (Localization.Away f) y))) = _
      rw [hρ'comm]; rfl
    -- key equality
    have key :
      algebraMap R (ResidueField R)
          (((pres.P.lift a ha).comp pres.equivRing.toAlgHom)
            (algebraMap R' (Localization.Away f) y)) =
        βAlg.symm (φ.symm (algebraMap R' P.ResidueField y)) := by
      rw [← hΦ₁eval, ← hg₂eval, hΦ]
    -- finish
    change
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
          ((algebraMap R (ResidueField R))
            (((pres.P.lift a ha).comp pres.equivRing.toAlgHom)
              (algebraMap R' (Localization.Away f) y))) =
        (φ.symm.toRingHom.comp (algebraMap R' P.ResidueField)) y
    rw [key, ← hβ, βAlg.apply_symm_apply]
    rfl

/-- **Residue point together with section membership.**
Produces a residue value `xbar ∈ κ` with `pres.P.HasMap xbar`, together with the
fibre-point uniqueness conclusion: for any root `a` lifting `xbar`
(`algebraMap R κ a = xbar`, `pres.P.HasMap a`), the section
`σ₀ = (pres.P.lift a) ∘ pres.equivRing ∘ (loc)` has `residue ∘ σ₀` killing only elements
of `P`. Assembled from `standardEtale_pres_residue_hasMap_linked` (existence together with
the fibre-uniqueness equality `residue ∘ σ₀ = ρ`) and the fact `ker ρ = P`
(`Ideal.ker_algebraMap_residueField`, `RingHom.ker_comp_of_injective`). -/
theorem standardEtale_pres_residue_section_mem (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (f : R')
    (pres : StandardEtalePresentation R (Localization.Away f)) (P : Ideal R') [P.IsPrime]
    [P.LiesOver (maximalIdeal R)] (hfP : f ∉ P)
    (hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R') (Ideal.LiesOver.over))) :
    ∃ xbar : ResidueField R,
      pres.P.HasMap xbar ∧
        ∀ (a : R) (ha : pres.P.HasMap a),
          algebraMap R (ResidueField R) a = xbar →
            ∀ y : R',
              (algebraMap R (ResidueField R))
                    ((((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
                        (IsScalarTower.toAlgHom R R' (Localization.Away f)))
                      y) =
                  0 →
                y ∈ P := by
  -- The residue map ρ : R' → κ at P (transported via hbij⁻¹), with ker ρ = P.
  set φ :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R') (Ideal.LiesOver.over))
      hbij with
    hφ
  set ρ := (φ.symm.toRingHom).comp (algebraMap R' P.ResidueField) with hρ
  have hkerρ : RingHom.ker ρ = P := by
    rw [hρ, RingHom.ker_comp_of_injective _ φ.symm.injective]
    exact Ideal.ker_algebraMap_residueField P
  -- Existence of the linked residue point, and the fibre-uniqueness equality.
  obtain ⟨xbar, hxbar, heq⟩ := standardEtale_pres_residue_hasMap_linked R R' f pres P hfP hbij
  refine ⟨xbar, hxbar, ?_⟩
  intro a ha hax y hy
  -- bridge κ → κ(m) is injective; from hy : residue(σ₀ y) = 0 we get ρ y = 0.
  have hbridge :
    (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)
        ((algebraMap R (ResidueField R))
          ((((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
              (IsScalarTower.toAlgHom R R' (Localization.Away f)))
            y)) =
      0 := by
    rw [hy, map_zero]
  have hρy : ρ y = 0 := by
    rw [← heq a ha hax y]; exact hbridge
  rw [← hkerρ]
  exact hρy

/-- **Kernel inclusion `ker σ₀ ≤ P`.**
Given the residue-membership certificate `hres` (produced by
`standardEtale_pres_residue_section_mem`), `ker σ₀ ≤ P` is immediate: `σ₀ y = 0` implies
`algebraMap R κ (σ₀ y) = 0`, hence `y ∈ P`. All the étale-fibre uniqueness content lives
in `hres`, so this statement is purely kernel-theoretic. -/
theorem standardEtale_section_ker_le (R : Type u) [CommRing R] [IsLocalRing R] (R' : Type u)
    [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (f : R')
    (pres : StandardEtalePresentation R (Localization.Away f)) (P : Ideal R') [P.IsPrime] (a : R)
    (ha : pres.P.HasMap a)
    (hres :
      ∀ y : R',
        (algebraMap R (ResidueField R))
              ((((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
                  (IsScalarTower.toAlgHom R R' (Localization.Away f)))
                y) =
            0 →
          y ∈ P) :
    RingHom.ker
        (((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
            (IsScalarTower.toAlgHom R R' (Localization.Away f))).toRingHom ≤
      P := by
  intro y hy
  rw [RingHom.mem_ker] at hy
  apply hres y
  show (algebraMap R (ResidueField R)) _ = 0
  rw [show
      ((((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
            (IsScalarTower.toAlgHom R R' (Localization.Away f)))
          y) =
        0
      from hy]
  exact map_zero _

/-- **Existence of the henselian-étale section.**
For `(R, m, κ)` henselian local and `R'` étale over `R` with a prime `P` over `m` whose
residue extension `κ → κ(P)` is an ISOMORPHISM (`hbij`), there is an `R`-algebra
*retraction* (section) `σ₀ : R' →ₐ[R] R` whose kernel is contained in `P`; equivalently,
the closed point `Spec σ₀ ⊆ Spec R'` passes through `P`.

This is the genuine henselian content of Stacks 04GG / EGA IV §18, and the single place
where henselianness is used: over a non-henselian local base the section need not exist.
The argument has two steps.
1. (standard-étale model) Localize `R'` to a standard-étale model near `P`
   (`Algebra.IsEtaleAt.exists_isStandardEtale`, 00UE;
   `Algebra.IsStandardEtale.nonempty_standardEtalePresentation`):
   `R'_f ≅ R[X,Y]/(p(X), Y·h(X)-1)` with `p` monic and `p'` a unit after inverting `h`.
   `LiesOver` and the residue isomorphism are preserved under `Localization.Away f` for
   `f ∉ P`, since the local ring at `P` is unchanged.
2. (Hensel root lift, the deep step) The bijective residue map `hbij` makes the image
   `x̄ ∈ κ(P) = κ` of `X` an honest element of `κ`; lift it to `a₀ ∈ R`. Then `p(a₀) ∈ m`
   (since `p̄(x̄) = 0`) and `p'(a₀) ∉ m` (since `p'(x)` is a unit in `R'_f`, hence nonzero
   in `κ(P) = κ`). `HenselianLocalRing.is_henselian` lifts `a₀` to a true root `a ∈ R`
   with `p(a) = 0` and `a ≡ a₀ (mod m)`. The assignment `X ↦ a`, `Y ↦ h(a)⁻¹` (with
   `h(a) ∈ Rˣ`, since `h(x)` is a unit and hence nonzero mod `m`) defines an `R`-algebra
   map `R'_f → R`; precomposing with `R' → R'_f` gives `σ₀ : R' →ₐ[R] R`. It is a
   retraction (`σ₀|_R = id`), and `ker σ₀ ≤ P` because the residue point of `σ₀` is `x̄`,
   the same as `P`'s, by uniqueness of the fibre point with a prescribed residue map
   (étale over a field is a product of separable fields). -/
@[ega "IV 18.5.11" "special case",
  ega "IV 18.5.12" "Necessity",
  ega "IV 18.5.17" "affine étale morphisms",
  ega "IV 18.6.2" "partial",
  ega "IV 18.8.1" "(a)⇒(c), special case",
  ega "IV 18.8.4" "Existence when B = A",
  sga "1 III 3.3" "special case",
  sga "3 VIB 5.6.1" "special case",
  sga "3 X 4.5" "special case",
  sga "3 X 8.9" "special case",
  sga "3 XI 1.11" "special case",
  sga "4 VIII 4.1" "(iii)",
  sga "4 XII 6.13" "partial"]
theorem henselian_etale_exists_section (R : Type u) [CommRing R] [HenselianLocalRing R]
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R') [P.IsPrime]
    [P.LiesOver (maximalIdeal R)]
    (hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R') (Ideal.LiesOver.over))) :
    ∃ (σ₀ : R' →ₐ[R] R), RingHom.ker σ₀.toRingHom ≤ P := by
  -- Step 1 (standard-étale model near P):
  obtain ⟨f, hfP, hSE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := R') P
  obtain ⟨pres⟩ :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := Localization.Away f)
  -- The residue point xbar together with the per-root residue-membership certificate:
  obtain ⟨xbar, hxbar, hmem⟩ := standardEtale_pres_residue_section_mem R R' f pres P hfP hbij
  -- The henselian root a ∈ R with the residue link `algebraMap R κ a = xbar`:
  obtain ⟨a, ha, hlink⟩ := henselian_standardEtale_root R pres.P xbar hxbar
  -- Step 2: assemble σ₀ : R' → R'_f → pres.P.Ring → R:
  refine
    ⟨((pres.P.lift a ha).comp pres.equivRing.toAlgHom).comp
        (IsScalarTower.toAlgHom R R' (Localization.Away f)),
      ?_⟩
  -- ker σ₀ ≤ P via the wrapper, fed the residue-membership for this linked `a`:
  exact standardEtale_section_ker_le R R' f pres P a ha (hmem a ha hlink)

/-- **From the henselian section to the clopen idempotent.**
Given an étale `R`-algebra `R'`, a prime `P`, and an `R`-algebra section (retraction)
`σ₀ : R' →ₐ[R] R` with `ker σ₀ ≤ P` (so `P` lies in the image `Spec σ₀ = V(ker σ₀)`), there
is an idempotent `ε ∈ R'` with `ε ∉ P` and `Localization.Away ε ≃ₐ[R] R`.

Geometrically, a section of an unramified map is an open and closed immersion, so its image
`Z = V(ker σ₀) ⊆ Spec R'` is clopen and therefore cut out by an idempotent, whose corner
ring is `R`. The proof given here is the purely algebraic form of that argument: `ker σ₀`
is an idempotent finitely generated ideal, hence `span {1 - ε}` for an idempotent `ε`, and
`Localization.Away ε ≃ₐ[R'] R' ⧸ ker σ₀ ≃ₐ[R] R`. -/
theorem etale_section_to_idempotent (R : Type) [CommRing R] [IsLocalRing R] (R' : Type)
    [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R') [P.IsPrime] (σ₀ : R' →ₐ[R] R)
    (hker : RingHom.ker σ₀.toRingHom ≤ P) :
    ∃ (ε : R'), IsIdempotentElem ε ∧ ε ∉ P ∧ Nonempty (Localization.Away ε ≃ₐ[R] R) := by
  -- Purely algebraic proof (no scheme theory): σ₀ is a retraction hence surjective,
  -- so R'/ker σ₀ ≃ₐ[R] R. Viewing R as an R'-algebra via σ₀, R is formally étale over
  -- R' (FormallyEtale.of_restrictScalars), and the structure map algebraMap R' R = σ₀
  -- is surjective, so FormallyEtale.iff_of_surjective gives that ker σ₀ is an idempotent
  -- ideal. It is finitely generated (étale ⇒ finitely presented), hence ker σ₀ = span{e'}
  -- for an idempotent e'. Take ε = 1 - e'; then ker σ₀ = span{1 - ε}, so
  -- IsLocalization.Away.quotient_of_isIdempotentElem gives Localization.Away ε ≃ₐ[R'] R'/ker σ₀,
  -- and the first isomorphism theorem closes Localization.Away ε ≃ₐ[R] R. ε ∉ P since
  -- e' = 1 - ε ∈ ker σ₀ ≤ P and P is prime.
  -- σ₀ is surjective (it's a retraction)
  have hsurj : Function.Surjective σ₀ := by
    intro r
    exact ⟨algebraMap R R' r, by simp⟩
  -- I = ker σ₀ is idempotent
  have hidem : IsIdempotentElem (RingHom.ker σ₀.toRingHom) := by
    let : Algebra R' R := σ₀.toRingHom.toAlgebra
    have : IsScalarTower R R' R := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      show algebraMap R R x = σ₀ (algebraMap R R' x)
      simp
    have : Algebra.FormallyEtale R' R :=
      Algebra.FormallyEtale.of_restrictScalars (R := R) (A := R') (B := R)
    have hsurj' : Function.Surjective (algebraMap R' R) := hsurj
    have h := (Algebra.FormallyEtale.iff_of_surjective hsurj').mp inferInstance
    have he : (algebraMap R' R) = σ₀.toRingHom := rfl
    rw [he] at h
    exact h
  -- I is finitely generated
  have hfg : (RingHom.ker σ₀.toRingHom).FG :=
    Algebra.FinitePresentation.ker_fG_of_surjective σ₀ hsurj
  -- so I = span {e'} for an idempotent e'
  obtain ⟨e', he'idem, hspan⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hidem
  -- ε = 1 - e' is idempotent, and ker σ₀ = span {1 - ε}
  refine ⟨1 - e', he'idem.one_sub, ?_, ?_⟩
  · -- 1 - e' ∉ P
    intro hmem
    -- e' ∈ ker σ₀ ≤ P  (since span{e'} = ker σ₀)
    have he'P : e' ∈ P := hker (hspan ▸ Ideal.mem_span_singleton_self e')
    exact P.ne_top_iff_one.mp (Ideal.IsPrime.ne_top inferInstance)
      (by simpa using P.add_mem he'P hmem)
  · -- the AlgEquiv
    have hkereq : RingHom.ker σ₀.toRingHom = Ideal.span {1 - (1 - e')} := by
      rw [hspan]; simp
    -- IsLocalization.Away (1-e') (R' ⧸ span {1 - (1-e')})
    have hloc : IsLocalization.Away (1 - e') (R' ⧸ RingHom.ker σ₀.toRingHom) := by
      rw [hkereq]
      exact IsLocalization.Away.quotient_of_isIdempotentElem he'idem.one_sub
    -- Localization.Away (1-e') ≃ₐ[R'] R' ⧸ ker σ₀
    have e1 : Localization.Away (1 - e') ≃ₐ[R'] (R' ⧸ RingHom.ker σ₀.toRingHom) :=
      IsLocalization.algEquiv (Submonoid.powers (1 - e')) _ _
    -- R' ⧸ ker σ₀ ≃ₐ[R] R
    have e2 : (R' ⧸ RingHom.ker σ₀.toRingHom) ≃ₐ[R] R :=
      Ideal.quotientKerAlgEquivOfSurjective hsurj
    exact ⟨(e1.restrictScalars R).trans e2⟩

/-- **Henselian étale section: the clopen component of a trivial-residue prime.**
For `(R, m, κ)` henselian local and `R'` an étale `R`-algebra with a prime `P` over `m`
whose residue extension `κ → κ(P)` is an ISOMORPHISM (a *pointed* étale neighborhood with
trivial residue extension), the clopen component of `P` in `Spec R'` is `R`-isomorphic to
`R`: there is an idempotent `ε ∈ R'` with `ε ∉ P` and an `R`-algebra isomorphism
`Localization.Away ε ≃ₐ[R] R`, equivalently a section (retraction) of `R → R'` onto the
component of `P`.

This is the structure theorem for étale algebras over a henselian local ring: every
connected finite-étale factor with trivial residue field is `≅ R`, or equivalently a
pointed étale neighborhood over a henselian base has a section. It is the genuine henselian
content beyond the polynomial-root form of `HenselianLocalRing.TFAE`.

The proof (Stacks 04GG / EGA IV 18) localizes `R'` to a *standard-étale* model around `P`
(`Algebra.IsEtaleAt.exists_isStandardEtale`, 00UE), so that near `P` it has the form
`(R[x]_g/(f))_h` with `f` monic and `f'` a unit at `P`. The bijective residue condition
`κ ≅ κ(P)` says the image `f̄ ∈ κ[x]` has a root `ā ∈ κ` that is SIMPLE (`f̄'(ā) ≠ 0`).
Henselianness lifts `ā` to a unique `a ∈ R` with `f(a) = 0` and `a ≡ ā mod m`
(`HenselianLocalRing.TFAE`, `IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub`, 06RR); the
assignment `x ↦ a` gives an `R`-algebra map `R[x]/(f) → R`, and on the clopen component of
`P` (`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`, 00EE) the section
`R'_ε ≃ₐ[R] R`. -/
@[ega "IV 18.5.11" "special case", sga "3 X 4.5" "special case", sga "3 XI 1.11" "special case"]
theorem exists_section_of_etale_of_bijective_residueField (R : Type) [CommRing R]
  [HenselianLocalRing R]
    (R' : Type) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R') [P.IsPrime]
    [P.LiesOver (maximalIdeal R)]
    (hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal R) P (Algebra.ofId R R') (Ideal.LiesOver.over))) :
    ∃ (ε : R'), IsIdempotentElem ε ∧ ε ∉ P ∧ Nonempty (Localization.Away ε ≃ₐ[R] R) := by
  -- The `Localization.Away ε` phrasing is the right one for an idempotent `ε`:
  -- `IsLocalization.Away.quotient_of_isIdempotentElem he : IsLocalization.Away ε (R'⧸span{1-ε})`
  -- gives `Localization.Away ε ≃ₐ[R'] R'⧸span{1-ε}` via `IsLocalization.algEquiv`.
  obtain ⟨σ₀, hker⟩ := henselian_etale_exists_section R R' P hbij
  exact etale_section_to_idempotent R R' P σ₀ hker

open TensorProduct in
/-- **Descent of the étale idempotent along the henselian section.**
Given the full output of `Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (an
étale `R'`, a prime `P | m`, an idempotent `e ∈ R' ⊗ S` with
`Module.Finite R' (Localization.Away e)`, a prime `P'` over `P` cutting out `q`, and
`e ∉ P'`), together with the henselian section `σ : Localization.Away ε ≃ₐ[R] R` of the
clopen component of `P` for the idempotent `ε ∉ P`, the idempotent `e` descends to an
honest idempotent `c ∈ S` with `c ∉ q` and `S·c = S ⧸ span {1 - c}` module-finite over `R`.

The section `σ` realizes `R' → R` on the component of `P`, inducing an `R`-algebra map
`Φ : R' ⊗_R S → S`, namely `σ ⊗ id` localized to the `ε`-component. Set `c := Φ e`. Then:
* `c` is idempotent, since `Φ` is a ring homomorphism and `e` is idempotent;
* `c ∉ q`, since `e ∉ P'` and `comap includeRight P' = q`, and the section is compatible
  with `P ↦ m`, so `Φ` sends the point `q` to the relevant prime;
* `Module.Finite R (S ⧸ span {1 - c})`, because the split-off factor `S·c` is the base
  change of `Localization.Away e` along `R' → R`, an isomorphism onto the component, so
  `Module.Finite R' (Localization.Away e)` descends to `Module.Finite R (S·c)`
  (`Module.Finite.of_restrictScalars_finite`, `Module.Finite.trans`). -/
theorem exists_isIdempotentElem_notMem_of_etale_section (R : Type) [CommRing R] [HenselianLocalRing
  R] (S : Type)
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)] (R' : Type) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (P : Ideal R') [P.IsPrime] [P.LiesOver (maximalIdeal R)] (e : TensorProduct R R' S)
    (he : IsIdempotentElem e) (P' : Ideal (TensorProduct R R' S)) [P'.IsPrime] [P'.LiesOver P]
    (hcomap : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom P' = q) (heP' : e ∉ P')
    (hefin : Module.Finite R' (Localization.Away e)) (ε : R') (hε : IsIdempotentElem ε)
    (hεP : ε ∉ P) (σ : Localization.Away ε ≃ₐ[R] R) :
    ∃ (c : S), IsIdempotentElem c ∧ c ∉ q ∧ Module.Finite R (S ⧸ Ideal.span {1 - c}) := by
  -- All hypotheses (the henselian section σ, the étale idempotent e cutting out q, and
  -- finiteness of Localization.Away e) are the outputs of Stacks 00UK together with the
  -- section lemmas above; what remains is base-change and `AlgEquiv` bookkeeping.
  let ρ : R' →ₐ[R] R := σ.toAlgHom.comp (IsScalarTower.toAlgHom R R' (Localization.Away ε))
  let Φ : TensorProduct R R' S →ₐ[R] S :=
    (Algebra.TensorProduct.lid R S).toAlgHom.comp (Algebra.TensorProduct.map ρ (AlgHom.id R S))
  set c : S := Φ e with hc_def
  have hc : IsIdempotentElem c := he.map Φ
  refine ⟨c, hc, ?_, ?_⟩
  · -- c ∉ q
    have hkey : ∀ r' : R', r' - algebraMap R R' (ρ r') ∈ P := by
      intro r'
      have h0 : algebraMap R' (Localization.Away ε) (r' - algebraMap R R' (ρ r')) = 0 := by
        rw [map_sub]
        have hstep :
          algebraMap R' (Localization.Away ε) (algebraMap R R' (ρ r')) =
            algebraMap R' (Localization.Away ε) r' := by
          rw [← IsScalarTower.algebraMap_apply R R' (Localization.Away ε)]
          have hh : algebraMap R (Localization.Away ε) (ρ r') = σ.symm (ρ r') := by
            apply σ.injective
            rw [σ.apply_symm_apply, AlgEquiv.commutes]; simp
          rw [hh]
          show σ.symm (ρ r') = algebraMap R' (Localization.Away ε) r'
          have : ρ r' = σ (algebraMap R' (Localization.Away ε) r') := rfl
          rw [this, σ.symm_apply_apply]
        rw [hstep, sub_self]
      rw [IsLocalization.map_eq_zero_iff (Submonoid.powers ε)] at h0
      obtain ⟨⟨m, n, hmn⟩, hm⟩ := h0
      simp only at hm
      subst hmn
      have hεn : ε ^ n ∉ P := fun h => hεP (‹P.IsPrime›.mem_of_pow_mem n h)
      rcases
        ‹P.IsPrime›.mem_or_mem (hm ▸ P.zero_mem : ε ^ n * (r' - algebraMap R R' (ρ r')) ∈ P) with
        h | h
      · exact absurd h hεn
      · exact h
    have hPP' :
      ∀ x ∈ P,
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S)) x ∈ P' := by
      intro x hx
      rw [show
          (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S)) x =
            algebraMap R' (TensorProduct R R' S) x
          from rfl]
      exact (Ideal.mem_of_liesOver (P := P') (p := P) x).mp hx
    have swap :
      ∀ a : R, (1 : R') ⊗ₜ[R] (algebraMap R S a) = (algebraMap R R' a) ⊗ₜ[R] (1 : S) := by
      intro a
      have h2 :=
        RingHom.congr_fun
          (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := R') (B := S)) a
      simp only [RingHom.comp_apply, Algebra.TensorProduct.includeLeftRingHom_apply] at h2
      exact h2.symm
    have hdesc :
      ∀ x : TensorProduct R R' S, Algebra.TensorProduct.includeRight (Φ x) - x ∈ P' := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r'
        s =>
        have hΦ : Φ (r' ⊗ₜ s) = algebraMap R S (ρ r') * s := by
          simp [Φ, Algebra.TensorProduct.map_tmul, Algebra.smul_def]
        rw [hΦ]
        have e1 :
          Algebra.TensorProduct.includeRight (algebraMap R S (ρ r') * s) =
            (algebraMap R R' (ρ r')) ⊗ₜ[R] s := by
          rw [map_mul, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.includeRight_apply, swap, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, mul_one]
        rw [e1]
        have e2 :
          (algebraMap R R' (ρ r')) ⊗ₜ[R] s - r' ⊗ₜ[R] s =
            -((r' - algebraMap R R' (ρ r')) ⊗ₜ[R] s) := by
          rw [sub_tmul, neg_sub]
        rw [e2]
        apply neg_mem
        have e3 :
          (r' - algebraMap R R' (ρ r')) ⊗ₜ[R] s =
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S))
                (r' - algebraMap R R' (ρ r')) *
              Algebra.TensorProduct.includeRight s := by
          rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rw [e3]
        exact Ideal.mul_mem_right _ _ (hPP' _ (hkey r'))
      | add a b ha hb =>
        rw [map_add, map_add]
        have hr :
          Algebra.TensorProduct.includeRight (Φ a) + Algebra.TensorProduct.includeRight (Φ b) -
              (a + b) =
            (Algebra.TensorProduct.includeRight (Φ a) - a) +
              (Algebra.TensorProduct.includeRight (Φ b) - b) := by
          ring
        rw [hr]
        exact Ideal.add_mem _ ha hb
    intro hcq
    have hicq : Algebra.TensorProduct.includeRight c ∈ P' :=
      (by rwa [hcomap] : c ∈ Ideal.comap Algebra.TensorProduct.includeRight.toRingHom P')
    have hde := hdesc e
    rw [← hc_def] at hde
    exact heP' (by simpa using P'.sub_mem hicq hde)
  · -- finiteness
    have hρsurj : Function.Surjective ρ :=
      σ.surjective.comp (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem ε hε)
    have : IsLocalization.Away c (S ⧸ Ideal.span {1 - c}) :=
      IsLocalization.Away.quotient_of_isIdempotentElem hc
    let mk : S →+* (S ⧸ Ideal.span {1 - c}) := algebraMap S (S ⧸ Ideal.span {1 - c})
    let g : TensorProduct R R' S →+* (S ⧸ Ideal.span {1 - c}) := mk.comp Φ.toRingHom
    have hunit : IsUnit (g e) := by
      have hz : mk (1 - c) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [map_sub, map_one, sub_eq_zero] at hz
      show IsUnit (mk c)
      exact hz ▸ isUnit_one
    let Φbar : Localization.Away e →+* (S ⧸ Ideal.span {1 - c}) :=
      IsLocalization.Away.lift (S := Localization.Away e) e hunit
    have hΦsurj : Function.Surjective Φ := fun s =>
      ⟨Algebra.TensorProduct.includeRight s, by simp [Φ]⟩
    have hgsurj : Function.Surjective g := (Ideal.Quotient.mk_surjective).comp hΦsurj
    have hΦbarsurj : Function.Surjective Φbar := by
      intro y
      obtain ⟨x, hx⟩ := hgsurj y
      exact ⟨algebraMap _ _ x, (IsLocalization.Away.lift_eq e hunit x).trans hx⟩
    have hsemi :
      ∀ (r' : R') (m : Localization.Away e),
        Φbar (algebraMap R' (Localization.Away e) r' * m) = ρ r' • Φbar m := by
      intro r' m
      rw [map_mul]
      have hstep :
        algebraMap R' (Localization.Away e) r' =
          algebraMap (TensorProduct R R' S) (Localization.Away e)
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S) r') := by
        rw [show
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S) r') =
              algebraMap R' (TensorProduct R R' S) r'
            from rfl]
        rw [← IsScalarTower.algebraMap_apply R' (TensorProduct R R' S) (Localization.Away e)]
      rw [hstep, IsLocalization.Away.lift_eq e hunit]
      have hg2 :
        g (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S) r') =
          mk (algebraMap R S (ρ r')) := by
        change
          mk (Φ (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := R') (B := S) r')) = _
        congr 1
        simp [Φ, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul,
          Algebra.smul_def]
      rw [hg2, Algebra.smul_def]
      change
        mk (algebraMap R S (ρ r')) * Φbar m = algebraMap R (S ⧸ Ideal.span {1 - c}) (ρ r') * Φbar m
      rw [IsScalarTower.algebraMap_apply R S (S ⧸ Ideal.span {1 - c})]
    have : RingHomSurjective ρ.toRingHom := ⟨hρsurj⟩
    let f : Localization.Away e →ₛₗ[ρ.toRingHom] (S ⧸ Ideal.span {1 - c}) :=
      { toFun := Φbar
        map_add' := map_add Φbar
        map_smul' := fun r' m => by
          rw [Algebra.smul_def r' m]
          exact hsemi r' m }
    have hfsurj : Function.Surjective f := hΦbarsurj
    have htop : (⊤ : Submodule R' (Localization.Away e)).FG := Module.Finite.fg_top
    have hmap := Submodule.FG.map (f := f) htop
    rw [Submodule.map_top, LinearMap.range_eq_top_of_surjective f hfsurj] at hmap
    exact Module.finite_def.mpr hmap

/-- **Single-point henselian descent** (a step of the first half of Stacks 04GE).
For `(R, m, κ)` henselian local, `S` of finite type over `R`, and a prime `q` of `S`
lying over `m` at which `R → S` is *quasi-finite*, there is an idempotent `c ∈ S`
with `c ∉ q`, so that `c` is `1` at the point `q`, and with the component
`S·c = S ⧸ span {1 - c}` module-FINITE over `R`.

This is the henselian form of Zariski's main theorem.
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq` (Stacks 00UK) yields an
étale `R'`, a prime `P | m` with `Function.Bijective (ResidueField.mapₐ …)`
(κ ≅ κ(P), the *pointed* étale neighborhood) and an idempotent `e ∈ R' ⊗ S` with
`Module.Finite R' (Localization.Away e)` and `e` cutting out exactly `q`. Because
`R` is HENSELIAN and `(R', P)` is a pointed étale neighborhood with trivial residue
extension, `R'` admits a section onto the clopen component of `P`
(`exists_section_of_etale_of_bijective_residueField`); base-changing `e` along the induced section
descends it to an honest idempotent `c ∈ S` (`exists_isIdempotentElem_notMem_of_etale_section`).

The proof applies, to the étale data of Stacks 00UK,
* `exists_section_of_etale_of_bijective_residueField`, the henselian-étale section (structure)
  theorem, and then
* `exists_isIdempotentElem_notMem_of_etale_section`, the base change of the idempotent. -/
theorem exists_isIdempotentElem_notMem_finite_of_quasiFiniteAt (R : Type) [CommRing R]
  [HenselianLocalRing R] (S : Type)
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (q : Ideal S) [hq : q.IsPrime]
    [q.LiesOver (maximalIdeal R)] [Algebra.QuasiFiniteAt R q] :
    ∃ (c : S), IsIdempotentElem c ∧ c ∉ q ∧ Module.Finite R (S ⧸ Ideal.span {1 - c}) := by
  -- Obtain the étale neighborhood and the étale-local idempotent (Stacks 00UK).
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hcomap, heP', hbij, hefin, _⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (maximalIdeal R) q
  -- Henselian section of the pointed étale neighborhood.
  obtain ⟨ε, hε, hεP, ⟨σ⟩⟩ := exists_section_of_etale_of_bijective_residueField R R' P hbij
  -- Descend e along the section to an honest idempotent c ∈ S.
  exact exists_isIdempotentElem_notMem_of_etale_section R S q R' P e he P' hcomap heP' hefin ε hε
    hεP σ

/-- In a Noetherian `T0` space, the points whose singleton is open (the isolated /
generic points of irreducible components) form a finite set: the map `x ↦ closure {x}`
injects them into the finite set of irreducible components. -/
theorem opensingleton_finite (α : Type) [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α]
    [T0Space α] : {x : α | IsOpen ({x} : Set α)}.Finite := by
  have hfin : (irreducibleComponents α).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  apply Set.Finite.of_finite_image (f := fun x => closure ({x} : Set α))
  · apply hfin.subset
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_ofPred_eq] at hx
    refine ⟨isIrreducible_singleton.closure, ?_⟩
    intro C hC hsub
    have hxC : x ∈ C := hsub (subset_closure (Set.mem_singleton x))
    intro y hyC
    rw [mem_closure_iff]
    intro U hU hyU
    obtain ⟨z, hz⟩ := hC.isPreirreducible U {x} hU hx ⟨y, hyC, hyU⟩ ⟨x, hxC, rfl⟩
    exact ⟨z, hz.right.left, hz.right.right⟩
  · intro x _ y _ h
    exact (inseparable_iff_closure_eq.mpr h).eq

/-- **Finiteness of the quasi-finite locus over `m`.** The primes `q` of `S` lying over `m`
at which `R → S` is quasi-finite form a FINITE set.

The closed fibre `A = S/mS = S ⊗_R κ` is of finite type over the residue field `κ`, hence
Noetherian, and the primes of `S` over `m` biject with `Spec A` by pullback along `S ↠ A`.
Quasi-finiteness at such a `q` over `R` is detected on the fibre
(`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`), where it says that the corresponding
point of `Spec A` is an open singleton. Open singletons in a Noetherian space are finite in
number (`opensingleton_finite`), so the quasi-finite locus is finite. -/
theorem finite_setOf_quasiFiniteAt_liesOver_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R] (S
  : Type) [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] :
    {q : Ideal S |
        q.IsPrime ∧
          q.LiesOver (maximalIdeal R) ∧
          ∀ hq : q.IsPrime, @Algebra.QuasiFiniteAt R S _ _ _ q hq}.Finite := by
  -- The primes over `m` biject with `Spec` of the closed fibre `F = κ(m) ⊗_R S`,
  -- which is finite-type over the field `κ(m)` hence Noetherian. Quasi-finiteness at
  -- such a prime `q` over `m` says the corresponding point of `Spec F` is an open
  -- singleton (`quasiFiniteAt_iff_isOpen_singleton_fiber` transported through the
  -- homeomorphism `preimageHomeomorphFiber`). Open singletons in a Noetherian space
  -- are finite (`opensingleton_finite`), so the qf-locus is finite.
  obtain ⟨pm, hpmeq⟩ : ∃ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R :=
    ⟨⟨maximalIdeal R, inferInstance⟩, rfl⟩
  let F := pm.asIdeal.Fiber S
  have : IsNoetherianRing F := Algebra.FiniteType.isNoetherianRing pm.asIdeal.ResidueField F
  have : TopologicalSpace.NoetherianSpace (PrimeSpectrum F) := inferInstance
  have htgt : {x : PrimeSpectrum F | IsOpen ({x} : Set _)}.Finite := opensingleton_finite _
  let e := PrimeSpectrum.preimageHomeomorphFiber R S pm
  rw [← Set.finite_coe_iff] at htgt ⊢
  apply
    Finite.of_injective (β := {x : PrimeSpectrum F | IsOpen ({x} : Set _)}) (f := fun w =>
      ⟨e
          ⟨⟨w.val, w.property.left⟩,
            show
              (⟨w.val, w.property.left⟩ : PrimeSpectrum S) ∈
                PrimeSpectrum.comap (algebraMap R S) ⁻¹' {pm}
              from PrimeSpectrum.ext (w.property.right.left.over.symm.trans hpmeq.symm)⟩,
        by
        obtain ⟨q, hq, hover, hqf⟩ := w
        let qS : PrimeSpectrum S := ⟨q, hq⟩
        have hc : PrimeSpectrum.comap (algebraMap R S) qS = pm :=
          PrimeSpectrum.ext (hover.over.symm.trans hpmeq.symm)
        have hmem : qS ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹' {pm} := hc
        have hopen0 :
          IsOpen (X :=
            ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹'
                {PrimeSpectrum.comap (algebraMap R S) qS})) {⟨qS, rfl⟩} :=
          (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber (R := R) qS).mp (hqf hq)
        have hopen :
          IsOpen (X := ↑(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {pm})) {⟨qS, hmem⟩} := by
          clear_value e
          subst hc
          exact hopen0
        show IsOpen ({e ⟨qS, hmem⟩} : Set (PrimeSpectrum F))
        simpa [Set.image_singleton] using e.isOpenMap _ hopen⟩)
  intro w₁ w₂ h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (congrArg (·.asIdeal) (Subtype.ext_iff.mp (e.injective h)))

end
end

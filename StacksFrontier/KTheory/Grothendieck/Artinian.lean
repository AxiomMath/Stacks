module

public import StacksCore.Tactic.StacksAttribute
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
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# `K'_0` of an Artinian local ring

Stacks tag 00JI (algebra-lemma-K0prime-Artinian): for an Artinian local ring `R`,
the homomorphism `length_R : K'_0(R) → ℤ` of Stacks 00JD is an isomorphism.

Here `K'_0(R)` is `K0prime R`, the Grothendieck group of finite `R`-modules modulo
isomorphisms and short exact sequences, and `length_R` is `lengthHom R`
(both from `StacksFrontier.KTheory.Grothendieck.Defs`). Surjectivity comes from the modules
`Fin n → ResidueField R` of length `n`; injectivity from the fact that the class of a
finite module of length `n` is `n` times the class of the residue field, proved by
splitting off a simple quotient `M ⧸ N ≅ ResidueField R` along a maximal submodule `N`.

## Main results

* `exists_finite_module_length_eq`: every `n : ℕ` is the length of a finite `R`-module.

The isomorphism itself, `K0prime.lengthHom_isIso` (Stacks 00JI), and the diagram
`K0.toK0prime_comm` (Stacks 00JK) are in `StacksFrontier.KTheory.Grothendieck.LengthIso`.
-/

@[expose] public section


open IsLocalRing Module

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The residue field of a local ring `R` is a simple `R`-module. -/
instance isSimpleModule_residueField : IsSimpleModule R (ResidueField R) :=
  isSimpleModule_iff_quot_maximal.mpr
    ⟨maximalIdeal R, maximalIdeal.isMaximal R, ⟨LinearEquiv.refl _ _⟩⟩

/-- The residue field of a local ring `R` has length one as an `R`-module. -/
@[simp]
lemma length_residueField_eq_one : Module.length R (ResidueField R) = 1 :=
  Module.length_eq_one R (ResidueField R)

/-- For any local ring `R` and any `n : ℕ`, `Fin n → ResidueField R` has length `n` as an
`R`-module. -/
lemma length_pi_residueField (n : ℕ) :
    Module.length R (Fin n → ResidueField R) = n := by
  rw [Module.length_pi_of_fintype]
  simp

/-- For an Artinian local ring `R`, the length map on finitely generated `R`-modules hits
every natural number: for each `n : ℕ` there is a finitely generated `R`-module `M` with
`Module.length R M = n`, namely `M = (ResidueField R)^n`.

The hypothesis `[IsArtinianRing R]` is not used by the proof, which only needs `R` to be
local (through `length_pi_residueField`); it is kept so the lemma reads in the setting of
Stacks 00JI. This is only the surjectivity ingredient of 00JI; the full statement, that
`length_R : K'_0(R) → ℤ` is an isomorphism, is `K0prime.lengthHom_isIso` in
`StacksFrontier.KTheory.Grothendieck.LengthIso`. -/
theorem exists_finite_module_length_eq.{u} {R : Type u} [CommRing R] [IsLocalRing R]
    [IsArtinianRing R] (n : ℕ) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M) (_ : Module.Finite R M),
      Module.length R M = n :=
  ⟨Fin n → ResidueField R, inferInstance, inferInstance, inferInstance,
    length_pi_residueField R n⟩

-- ===== merged from StacksDraft.Ch10.Sec55.Tag00JK =====

/-!
# K₀ and K'₀ of an Artinian local ring

Let `R` be a local Artinian ring. The commutative diagram
$$
\begin{array}{ccc}
K_0(R) & \to & K_0'(R) \\
\text{rank}_R \downarrow & & \downarrow \text{length}_R \\
\mathbf{Z} & \xrightarrow{\text{length}_R(R)} & \mathbf{Z}
\end{array}
$$
records the basic fact that for any finite projective `R`-module `P`,
the length of `P` equals the rank of `P` times the length of `R`:
`length R P = finrank R P * length R R`.

Indeed, over a local ring every finite projective module is free of finite
rank (`Module.free_of_flat_of_isLocalRing`), and on a finite free module of
rank `n`, the length is `n` times the length of the base ring
(`Module.length_of_free_of_finite`). This is the commutativity statement
of the diagram, since the upper-right composite sends the class of `P` to
`length R P` while the lower-left composite sends it to
`(finrank R P) • length R R`. The diagram itself, with the map
`K0.toK0prime : K_0(R) → K'_0(R)`, is `K0.toK0prime_comm` (Stacks 00JK) in
`StacksFrontier.KTheory.Grothendieck.LengthIso`.
-/

@[expose] public section


open Module

/-- Over a local Artinian ring `R`, the length of any finite projective
`R`-module `P` equals the rank of `P` times the length of `R`. This is the
value on the class of `P` of the commutative diagram `K0.toK0prime_comm`.

Proof sketch. Since `R` is a local ring and `P` is finitely generated and
projective (hence flat), `P` is free of finite rank by
`Module.free_of_flat_of_isLocalRing`. Then
`Module.length_of_free_of_finite` gives the desired identity. -/
theorem length_eq_finrank_mul_length_self
    (R : Type*) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    Module.length R P = Module.finrank R P * Module.length R R := by
  have : Module.Flat R P := Module.Flat.of_projective
  have : Module.Free R P := Module.free_of_flat_of_isLocalRing
  exact Module.length_of_free_of_finite R P

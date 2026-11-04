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
Stacks tag 00JI (algebra-lemma-K0prime-Artinian): for an Artinian local ring `R`,
the homomorphism `length_R : K'_0(R) → ℤ` from Stacks 00JH is an isomorphism.

`K'_0(R)`, the Grothendieck group of finitely generated `R`-modules modulo short exact
sequences and isomorphisms, is not (yet) part of Mathlib. Rather than redevelop that
construction here, this file lands the *surjectivity ingredient* of the iso, framed
entirely in terms of `Module.length`: for every `n : ℕ` there is a finitely generated
`R`-module of length exactly `n`. Concretely the witness is the free module
`Fin n → ResidueField R` on the residue field, whose length is computed by the
Mathlib lemma `Module.length_pi_of_fintype` together with the fact that the residue
field of a local ring is a simple `R`-module.
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

/-- **Stacks 00JI (length-surjectivity form).**

For an Artinian local ring `R`, the length map on finitely generated `R`-modules
hits every natural number: for each `n : ℕ` there is a finitely generated
`R`-module `M` with `Module.length R M = n`.

This is the surjectivity ingredient of the Stacks statement that
`length_R : K'_0(R) → ℤ` is an isomorphism. The full Stacks statement also needs
the construction of `K'_0(R)` (Stacks 00JH) and the injectivity of `length_R`;
those rely on the composition-series structure of Artinian local rings and are
left to a follow-up file once Mathlib has `K'_0(R)`. The witness here is the
standard one: `M = (ResidueField R)^n`. -/
@[stacks 00JI "Surjectivity ingredient only: every n : ℕ is the length of a finite \
module. K'_0(R) and the isomorphism length_R : K'_0(R) ≃ ℤ are not formalized."]
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
`(finrank R P) • length R R`.
-/

@[expose] public section


open Module

/-- Over a local Artinian ring `R`, the length of any finite projective
`R`-module `P` equals the rank of `P` times the length of `R`. This is the
mathematical content of the commutative diagram relating `K₀(R)` and
`K'₀(R)` for a local Artinian ring `R`: the rank-of-`R` length factor is
exactly the bottom map of the diagram, and both vertical maps (rank and
length) are isomorphisms with `ℤ`.

Proof sketch. Since `R` is a local ring and `P` is finitely generated and
projective (hence flat), `P` is free of finite rank by
`Module.free_of_flat_of_isLocalRing`. Then
`Module.length_of_free_of_finite` gives the desired identity. -/
@[stacks 00JK "Numerical identity length P = rank P * length R only; the commutative \
diagram K_0(R) → K'_0(R) → ℤ is not formalized."]
theorem length_eq_finrank_mul_length_self
    (R : Type*) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (P : Type*) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] :
    Module.length R P = Module.finrank R P * Module.length R R := by
  have : Module.Flat R P := Module.Flat.of_projective
  have : Module.Free R P := Module.free_of_flat_of_isLocalRing
  exact Module.length_of_free_of_finite R P


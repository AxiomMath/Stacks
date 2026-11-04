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
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Length under restriction of scalars

Let `φ : R → S` be a ring map and let `M` be an `S`-module, regarded also as an `R`-module by
restriction of scalars along `φ`, so that `r • m = φ r • m` (`Module.compHom M φ`). Every
`S`-submodule of `M` is an `R`-submodule with the same carrier, so `length_S(M) ≤ length_R(M)`.
If `φ` is surjective the operators `r • -` are exactly the operators `s • -`, so the two
submodule lattices coincide and the two lengths are equal. Lengths are taken in `ℕ∞`.
-/

@[expose] public section

/-- If every submodule for one module structure on `M` is stable under the scalars of another,
the length for the first structure is at most that for the second. -/
private theorem length_le_of_smul_mem {R S : Type*} [CommRing R] [CommRing S]
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M]
    (h : ∀ (N : Submodule S M) (r : R) (x : M), x ∈ N → r • x ∈ N) :
    Module.length S M ≤ Module.length R M :=
  WithBot.unbot_mono _ _ (Order.krullDim_le_of_strictMono
    (fun N : Submodule S M => { N.toAddSubmonoid with smul_mem' := fun r _ hm => h N r _ hm } :
      Submodule S M → Submodule R M)
    fun _ _ hab => ⟨fun _ hx => hab.le hx, fun h => hab.not_ge fun _ hx => h hx⟩)

/-- For a ring map `φ : R → S` and an `S`-module `M`, viewed as an `R`-module by restriction of
scalars along `φ`, the length over `R` is at least the length over `S`. -/
@[stacks 00IX "(1)"]
theorem Module.length_le_length_restrictScalars
    (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Type*) [AddCommGroup M] [Module S M] :
    letI : Module R M := Module.compHom M φ
    Module.length S M ≤ Module.length R M := by
  let iR : Module R M := Module.compHom M φ
  exact length_le_of_smul_mem fun N r _ hm => N.smul_mem (φ r) hm

/-- For a surjective ring map `φ : R → S` and an `S`-module `M`, viewed as an `R`-module by
restriction of scalars along `φ`, the length over `R` equals the length over `S`. -/
@[stacks 00IX "(2)"]
theorem length_restrictScalars_eq_of_surjective
    (R S : Type*) [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Surjective φ)
    (M : Type*) [AddCommGroup M] [Module S M] :
    letI : Module R M := Module.compHom M φ
    Module.length R M = Module.length S M := by
  let iR : Module R M := Module.compHom M φ
  refine le_antisymm ?_ (Module.length_le_length_restrictScalars R S φ M)
  exact length_le_of_smul_mem fun N s _ hm => by
    obtain ⟨r, rfl⟩ := hφ s
    exact N.smul_mem r hm

/-!
# Length equals dimension over the residue field

Let `R` be a commutative ring with maximal ideal `m`, and let `M` be an
`R`-module annihilated by `m`. Then the `R`-module length of `M` equals
the `R⧸m`-vector space dimension of `M`. Moreover, the length is finite
iff `M` is a finite `R`-module.
-/

@[expose] public section


/-- The `R`-module length of `M` equals its `R ⧸ m`-module length when `M` is annihilated
by `m`, since the two submodule lattices coincide as orders. -/
private lemma length_eq_length_quot
    (R : Type*) [CommRing R] (m : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M]
    (hTors : Module.IsTorsionBySet R M (m : Set R)) :
    letI : Module (R ⧸ m) M := hTors.module
    Module.length R M = Module.length (R ⧸ m) M := by
  let : Module (R ⧸ m) M := hTors.module
  have : IsScalarTower R (R ⧸ m) M := hTors.isScalarTower
  let φ : Submodule (R ⧸ m) M ≃o Submodule R M :=
    { toFun := Submodule.restrictScalars R
      invFun N :=
        { __ := N
          smul_mem' q x hx := by
            obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
            exact (IsScalarTower.algebraMap_smul (R ⧸ m) r x) ▸ N.smul_mem r hx }
      left_inv _ := by ext; rfl
      right_inv _ := by ext; rfl
      map_rel_iff' := by intros; rfl }
  unfold Module.length
  congr 1
  exact (Order.krullDim_eq_of_orderIso φ).symm

/-- Length of `M` as an `R`-module equals the dimension of `M` as an
`R ⧸ m`-vector space, when `m M = 0` for a maximal ideal `m`. -/
@[stacks 00IY "(1)"]
theorem length_eq_rank_of_maximal_smul_eq_zero
    (R : Type*) [CommRing R] (m : Ideal R) [m.IsMaximal]
    (M : Type*) [AddCommGroup M] [Module R M]
    (hM : ∀ r ∈ m, ∀ x : M, r • x = 0) :
    letI hTors : Module.IsTorsionBySet R M (m : Set R) :=
      fun x a => hM a.1 a.2 x
    letI : Module (R ⧸ m) M := hTors.module
    Module.length R M = Cardinal.toENat (Module.rank (R ⧸ m) M) := by
  let hTors : Module.IsTorsionBySet R M (m : Set R) := fun x a => hM a.val a.property x
  let : Module (R ⧸ m) M := hTors.module
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  exact (length_eq_length_quot R m M hTors).trans (Module.length_eq_rank (R ⧸ m) M)

/-- The length of `M` is finite if and only if `M` is a finite `R`-module,
when `m M = 0` for a maximal ideal `m`. -/
@[stacks 00IY "(2)"]
theorem length_lt_top_iff_finite_of_smul_eq_zero
    (R : Type*) [CommRing R] (m : Ideal R) [m.IsMaximal]
    (M : Type*) [AddCommGroup M] [Module R M]
    (hM : ∀ r ∈ m, ∀ x : M, r • x = 0) :
    Module.length R M < ⊤ ↔ Module.Finite R M := by
  let hTors : Module.IsTorsionBySet R M (m : Set R) := fun x a => hM a.val a.property x
  let : Module (R ⧸ m) M := hTors.module
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have : IsScalarTower R (R ⧸ m) M := hTors.isScalarTower
  rw [length_eq_length_quot R m M hTors, Module.length_eq_rank (R ⧸ m) M,
    Cardinal.toENat_lt_top, Module.rank_lt_aleph0_iff (R := R ⧸ m) (M := M)]
  exact ⟨fun _ => Module.Finite.trans (R ⧸ m) M,
    fun _ => Module.Finite.of_restrictScalars_finite R (R ⧸ m) M⟩

/-!
# Length of a localization

For a multiplicative subset `S` of a commutative ring `R` and an `R`-module `M`, contraction
along the localization map embeds the lattice of `S⁻¹R`-submodules of `S⁻¹M` into the lattice
of `R`-submodules of `M`, so `length_{S⁻¹R}(S⁻¹M) ≤ length_R(M)`.
-/

@[expose] public section

open Submodule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (S : Submonoid R)

/-- The order embedding of the lattice of `Localization S`-submodules of `LocalizedModule S M`
into the lattice of `R`-submodules of `M`, sending `N` to its preimage under
`LocalizedModule.mkLinearMap S M`. It is the upper adjoint of `Submodule.localized'gi`. -/
noncomputable def LocalizedModule.comapSubmoduleOrderEmbedding :
    Submodule (Localization S) (LocalizedModule S M) ↪o Submodule R M :=
  OrderEmbedding.ofMapLEIff
    (fun N => (N.restrictScalars R).comap (LocalizedModule.mkLinearMap S M))
    (fun _ _ => (localized'gi (Localization S) S (LocalizedModule.mkLinearMap S M)).u_le_u_iff)

/-- The embedding `LocalizedModule.comapSubmoduleOrderEmbedding S` sends a submodule `N` to its
preimage under `LocalizedModule.mkLinearMap S M`, viewed as an `R`-submodule. -/
@[simp]
theorem LocalizedModule.comapSubmoduleOrderEmbedding_apply
    (N : Submodule (Localization S) (LocalizedModule S M)) :
    comapSubmoduleOrderEmbedding S N =
      (N.restrictScalars R).comap (LocalizedModule.mkLinearMap S M) :=
  rfl

/-- **Stacks Tag 00IZ.** Let `R` be a ring, `M` an `R`-module, and `S ⊆ R` a multiplicative
subset. Then `length_R(M) ≥ length_{S⁻¹R}(S⁻¹M)`. -/
@[stacks 00IZ]
theorem Module.length_localizedModule_le :
    Module.length (Localization S) (LocalizedModule S M) ≤ Module.length R M := by
  rw [← WithBot.coe_le_coe, Module.coe_length, Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (LocalizedModule.comapSubmoduleOrderEmbedding S)

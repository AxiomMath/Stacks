module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import StacksCore.LinearAlgebra.Matrix.CommSemiring

/-!
# The distance between a lattice and its image is the order of the determinant

Let `R` be a Noetherian local domain of Krull dimension `1` with fraction field `K`, and let
`V` be a finite-dimensional `K`-vector space; all lengths are lengths of `R`-modules.

The main result is that for a `K`-linear isomorphism `φ : V → V` and any lattice `M ⊆ V`,
the distance `d(M, φ(M))` equals the order of vanishing `ord_R (det φ)`.

The supporting notions are the order of vanishing, the notion of lattice, and the distance
between two lattices.
-/

@[expose] public section

namespace Stacks.OrderOfVanishing

/-! ## Setup

`R` is a Noetherian local domain (dimension one is imposed where needed, but the
length-finiteness facts used by the Stacks proof require it).  `K` is its
fraction field, and `V` is a finite dimensional `K`-vector space, regarded also
as an `R`-module via restriction of scalars. -/

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Module R V] [IsScalarTower R K V]

/-! ## Definition 1: Order of vanishing (Tag 02MD)

For a nonzero `x ∈ R`, `ord_R(x) = length_R(R/(x))`, which is finite since `R` is
a Noetherian local domain of dimension `1` and `x` is a nonzerodivisor.  We
record this length first (using `ENat.toNat`, which gives the correct value when
the length is finite). -/

/-- The length of `R/(x)` as an `R`-module, as a natural number. For nonzero `x`
in a one-dimensional Noetherian local domain this is finite and equals
`ord_R(x)`. -/
noncomputable def ordOnRing (x : R) : ℕ :=
  (Module.length R (R ⧸ Ideal.span {x})).toNat

/-- The order of vanishing `ord_R : K^* → ℤ`.  Writing a unit `z ∈ K^*` as
`x/y` with `x, y ∈ R` nonzero (via the localization section), we set
`ord_R(z) = length_R(R/(x)) - length_R(R/(y))`.  Its mathematical
characterization is captured by `ordR_apply_algebraMap` and `ordR_mul` below. -/
noncomputable def ordR (z : Kˣ) : ℤ :=
  if ringKrullDim R = 1 then
    let s := IsLocalization.sec (nonZeroDivisors R) (z : K)
    (ordOnRing (R := R) s.fst : ℤ) - (ordOnRing (R := R) (s.snd : R) : ℤ)
  else 0

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] in
/-- Under the dimension-one hypothesis, `ordR` unfolds to the section-based
formula `length_R(R/(num)) - length_R(R/(den))`. -/
theorem ordR_def (hdim : ringKrullDim R = 1) (z : Kˣ) :
    ordR (R := R) z
      = (ordOnRing (R := R) (IsLocalization.sec (nonZeroDivisors R) (z : K)).1 : ℤ)
        - (ordOnRing (R := R) ((IsLocalization.sec (nonZeroDivisors R) (z : K)).2 : R) : ℤ) := by
  rw [ordR, ite_eq_left hdim]

/-! ## Definition 2: Lattice (Tag 02ME)

A *lattice in `V`* is a finitely generated `R`-submodule `M ⊆ V` such that the
natural map `K ⊗_R M → V` is an isomorphism.  Since `M` is a finitely generated
torsion-free `R`-module and `K` is flat over `R`, that map is automatically
injective, so the condition is equivalent to surjectivity, i.e. to the
`K`-linear span of `M` being all of `V` (equivalently, `M` contains a
`K`-basis of `V`). -/

/-- `M` is a lattice in `V`: a finitely generated `R`-submodule whose
`K`-span is all of `V`. -/
def IsLattice (M : Submodule R V) : Prop :=
  M.FG ∧ Submodule.span K (M : Set V) = ⊤

/-! ## Definition 3: Distance between lattices (Tag 02MG)

For lattices `M, M'`, the intersection `M ⊓ M'` is a lattice and both quotients
`M/(M ⊓ M')` and `M'/(M ⊓ M')` have finite `R`-length.  The distance is
`d(M, M') = length_R(M/(M ⊓ M')) - length_R(M'/(M ⊓ M'))`. -/

/-- `length_R (M / (M ⊓ M'))`, where the quotient is taken inside `M` (as a
natural number via `ENat.toNat`). -/
noncomputable def lenQuot (M M' : Submodule R V) : ℕ :=
  (Module.length R (↥M ⧸ Submodule.comap M.subtype (M ⊓ M'))).toNat

/-- The distance `d(M, M') = length_R(M/(M ⊓ M')) - length_R(M'/(M ⊓ M'))`. -/
noncomputable def latticeDist (M M' : Submodule R V) : ℤ :=
  (lenQuot M M' : ℤ) - (lenQuot M' M : ℤ)

/-! ## Definition 4: Image lattice

For a `K`-linear isomorphism `φ : V → V`, the image `φ(M)` of an `R`-submodule
`M` is again an `R`-submodule (`φ` is `R`-linear by restriction of scalars). -/

/-- The image `φ(M)` of an `R`-submodule `M` under a `K`-linear equivalence
`φ`, viewed as an `R`-submodule. -/
noncomputable def mapLattice (φ : V ≃ₗ[K] V) (M : Submodule R V) : Submodule R V :=
  M.map ((φ : V →ₗ[K] V).restrictScalars R)

/-! ## Correctness statements for `ord_R` (Tag 02MD)

These uniquely characterize `ordR`: it agrees with `length_R(R/(x))` on nonzero
elements of `R` and is a group homomorphism `K^* → ℤ`. -/

/-- Length is additive along `S ≤ T ≤ M`: `ℓ(M/S) = ℓ(T/S) + ℓ(M/T)`, with `T/S = map S.mkQ T`. -/
private theorem length_quotient_eq_add_map {A M : Type*} [Ring A] [AddCommGroup M] [Module A M]
    {S T : Submodule A M} (hST : S ≤ T) :
    Module.length A (M ⧸ S)
      = Module.length A (Submodule.map S.mkQ T) + Module.length A (M ⧸ T) := by
  rw [Module.length_eq_add_of_exact (Submodule.map S.mkQ T).subtype (Submodule.map S.mkQ T).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
    (Submodule.quotientQuotientEquivQuotient S T hST).length_eq]

/-- Length additivity of `A/(·)` on products: `ℓ(A/(x)) + ℓ(A/(y)) = ℓ(A/(xy))`. -/
private theorem length_span_mul_add {A : Type*} [CommRing A] [IsDomain A] (x y : A) (hx : x ≠ 0) :
    Module.length A (A ⧸ Ideal.span {x}) + Module.length A (A ⧸ Ideal.span {y})
      = Module.length A (A ⧸ Ideal.span {x * y}) := by
  set S : Ideal A := Ideal.span {x * y} with hSdef
  set T : Ideal A := Ideal.span {x} with hTdef
  have hST : S ≤ T := by
    rw [hSdef, hTdef, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    exact ⟨y, by ring⟩
  let f : A →ₗ[A] (A ⧸ S) := (S.mkQ).comp (LinearMap.mulLeft A x)
  have hker : LinearMap.ker f = Ideal.span {y} := by
    ext r
    simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hSdef, Ideal.mem_span_singleton]
    rw [mul_comm x r, mul_comm x y]
    exact mul_dvd_mul_iff_right hx
  have hrange : LinearMap.range f = Submodule.map S.mkQ T := by
    rw [hTdef]
    ext w
    simp only [f, LinearMap.mem_range, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      Submodule.mkQ_apply, Submodule.mem_map, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨x * r, ⟨r, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [mul_comm]⟩
  have step2 :
      Module.length A (↥(Submodule.map S.mkQ T)) = Module.length A (A ⧸ Ideal.span {y}) := by
    have e := LinearMap.quotKerEquivRange f
    rw [hker, hrange] at e
    exact e.length_eq.symm
  rw [length_quotient_eq_add_map hST, step2, add_comm]

/-- In a one-dimensional Noetherian domain, `A/(z)` is an Artinian ring for `z ≠ 0`. -/
private theorem isArtinianRing_quotient_span_singleton {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 1) {z : A} (hz : z ≠ 0) :
    IsArtinianRing (A ⧸ Ideal.span {z}) := by
  have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hz)
  rw [hdim] at h
  have hdimq : ringKrullDim (A ⧸ Ideal.span {z}) ≤ (0 : ℕ) :=
    ENat.WithBot.add_le_add_natCast_right_iff.mp h
  rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  exact ⟨Ideal.Quotient.isNoetherianRing _, Ring.krullDimLE_iff.mpr (by exact_mod_cast hdimq)⟩

/-- In a one-dimensional Noetherian domain, `A/(z)` has finite length for `z ≠ 0`. -/
private theorem length_quotient_span_ne_top {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 1) {z : A} (hz : z ≠ 0) :
    Module.length A (A ⧸ Ideal.span {z}) ≠ ⊤ := by
  have := isArtinianRing_quotient_span_singleton hdim hz
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_isNoetherianRing_of_finite A _,
    isArtinian_of_surjective_algebraMap (R := A ⧸ Ideal.span {z}) Ideal.Quotient.mk_surjective⟩

/-- `ordOnRing` is additive on products of nonzero elements of a one-dimensional domain. -/
private theorem ordOnRing_mul_of_ne_zero {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] (hdim : ringKrullDim A = 1) {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordOnRing (x * y) = ordOnRing x + ordOnRing y := by
  unfold ordOnRing
  rw [← length_span_mul_add x y hx]
  exact ENat.toNat_add (length_quotient_span_ne_top hdim hx) (length_quotient_span_ne_top hdim hy)

/-- On a nonzero `x ∈ R`, `ord_R(x) = length_R(R/(x))`. -/
theorem ordR_apply_algebraMap (hdim : ringKrullDim R = 1) (x : R) (hx : x ≠ 0)
    (u : Kˣ) (hu : (u : K) = algebraMap R K x) :
    ordR (R := R) u = (ordOnRing (R := R) x : ℤ) := by
  -- STRATEGY (formal phase): unfold `ordR`. Let `s = IsLocalization.sec (nonZeroDivisors R) u`,
  -- so by `IsLocalization.sec_spec` we have `algebraMap s.2 * (u:K) = algebraMap s.1`, i.e.
  -- `u = s.1 / s.2`. With `u = algebraMap R K x` this gives
  -- `algebraMap (s.2 * x) = algebraMap s.1`
  -- in `K`; since `algebraMap R K` is injective (`IsFractionRing.injective`/`IsLocalization`),
  -- `s.1 = s.2 * x` in `R`. Then `ordR u = ord(s.1) - ord(s.2) = ord(s.2 * x) - ord(s.2)`.
  -- Reduce via the additivity of `ordOnRing` on products of nonzerodivisors
  -- (`length_R (R/(ab)) = length_R(R/(a)) + length_R(R/(b))`, a special case of the
  -- multiplicativity used in `ordR_mul`; for `R` of dim 1 this is Stacks 02MC/length additivity
  -- on the filtration `(ab) ⊆ (b) ⊆ R`), giving `ord(s.2 * x) - ord(s.2) = ord(x) = ordOnRing x`.
  -- Additivity of `ordOnRing` on nonzero products is `ordOnRing_mul_of_ne_zero`.
  -- Main argument.
  rw [ordR_def hdim u]
  set s := IsLocalization.sec (nonZeroDivisors R) (u : K) with hs
  have hspec : (u : K) * (algebraMap R K) (s.snd : R) = (algebraMap R K) s.fst :=
    IsLocalization.sec_spec (nonZeroDivisors R) (u : K)
  rw [hu] at hspec
  have heq : (algebraMap R K) (x * (s.snd : R)) = (algebraMap R K) s.fst := by
    rwa [map_mul]
  have hinj : x * (s.snd : R) = s.fst := IsFractionRing.injective R K heq
  have hs2ne : (s.snd : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s.snd
  have hord : ordOnRing (R := R) s.fst = ordOnRing (R := R) x + ordOnRing (R := R) (s.snd : R) := by
    rw [← hinj]
    exact ordOnRing_mul_of_ne_zero hdim hx hs2ne
  rw [hord]
  push_cast
  ring

omit [IsLocalRing R] in
/-- For nonzero `z` in a one-dimensional Noetherian local domain, `R/(z)` is a
finite-length `R`-module (its support is the closed point). -/
theorem ordOnRing_length_ne_top (hdim : ringKrullDim R = 1) (z : R) (hz : z ≠ 0) :
    Module.length R (R ⧸ Ideal.span {z}) ≠ ⊤ :=
  length_quotient_span_ne_top hdim hz

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Length additivity of `R/(·)` on products: as `ℕ∞` values,
`length_R(R/(x)) + length_R(R/(y)) = length_R(R/(xy))` (no finiteness needed). -/
theorem ordOnRing_length_add (x y : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x}) + Module.length R (R ⧸ Ideal.span {y})
      = Module.length R (R ⧸ Ideal.span {x * y}) :=
  length_span_mul_add x y hx

omit [IsLocalRing R] in
/-- Additivity of `ordOnRing` on a product of nonzero elements, for a one-dimensional base. -/
theorem ordOnRing_mul_nonzero (hdim : ringKrullDim R = 1) (x y : R)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ordOnRing (R := R) (x * y) = ordOnRing (R := R) x + ordOnRing (R := R) y :=
  ordOnRing_mul_of_ne_zero hdim hx hy

/-- The numerator of the `IsLocalization.sec` of a nonzero element is nonzero. -/
private theorem sec_fst_ne_zero {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] {z : K} (hz : z ≠ 0) :
    (IsLocalization.sec (nonZeroDivisors A) z).1 ≠ 0 := by
  intro h
  have hspec := IsLocalization.sec_spec (nonZeroDivisors A) z
  rw [h, map_zero, mul_eq_zero] at hspec
  exact hspec.elim hz fun h2 => nonZeroDivisors.coe_ne_zero _
    ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h2)

/-- `ord_R` is a homomorphism: `ord_R(a·b) = ord_R(a) + ord_R(b)`. -/
theorem ordR_mul (a b : Kˣ) :
    ordR (R := R) (a * b) = ordR (R := R) a + ordR (R := R) b := by
  -- When `ringKrullDim R ≠ 1` all three `ordR` values are `0` by definition, so the identity
  -- is `0 = 0 + 0`. Under `hdim : ringKrullDim R = 1` we unfold via `ordR_def` and run the
  -- representative-independence argument below.
  by_cases hdim : ringKrullDim R = 1
  · rw [ordR_def hdim (a * b), ordR_def hdim a, ordR_def hdim b]
    set sa := IsLocalization.sec (nonZeroDivisors R) (a : K) with hsa
    set sb := IsLocalization.sec (nonZeroDivisors R) (b : K) with hsb
    set sc := IsLocalization.sec (nonZeroDivisors R) ((a * b : Kˣ) : K) with hsc
    -- sec specifications.
    have hspeca : (a : K) * (algebraMap R K) (sa.snd : R) = (algebraMap R K) sa.fst :=
      IsLocalization.sec_spec (nonZeroDivisors R) (a : K)
    have hspecb : (b : K) * (algebraMap R K) (sb.snd : R) = (algebraMap R K) sb.fst :=
      IsLocalization.sec_spec (nonZeroDivisors R) (b : K)
    have hspecc : ((a * b : Kˣ) : K) * (algebraMap R K) (sc.snd : R) = (algebraMap R K) sc.fst :=
      IsLocalization.sec_spec (nonZeroDivisors R) ((a * b : Kˣ) : K)
    -- denominators are nonzero.
    have hsa2ne : (sa.snd : R) ≠ 0 := nonZeroDivisors.coe_ne_zero sa.snd
    have hsb2ne : (sb.snd : R) ≠ 0 := nonZeroDivisors.coe_ne_zero sb.snd
    have hsc2ne : (sc.snd : R) ≠ 0 := nonZeroDivisors.coe_ne_zero sc.snd
    -- numerators are nonzero: a,b,a*b are units of K, so their values are nonzero.
    have hsa1ne : sa.fst ≠ 0 := sec_fst_ne_zero a.ne_zero
    have hsb1ne : sb.fst ≠ 0 := sec_fst_ne_zero b.ne_zero
    have hsc1ne : sc.fst ≠ 0 := sec_fst_ne_zero (a * b).ne_zero
    -- The cross-multiplication identity in K.
    have hKeq : (algebraMap R K) (sc.fst * (sa.snd * sb.snd))
        = (algebraMap R K) (sa.fst * sb.fst * sc.snd) := by
      have hab : ((a * b : Kˣ) : K) = (a : K) * (b : K) := by rw [Units.val_mul]
      rw [map_mul, map_mul, map_mul, map_mul]
      -- goal: am sc.1 * (am sa.2 * am sb.2) = am sa.1 * am sb.1 * am sc.2
      rw [← hspeca, ← hspecb, ← hspecc, hab]
      ring
    -- Transfer to R via injectivity.
    have hReq : sc.fst * (sa.snd * sb.snd) = sa.fst * sb.fst * sc.snd :=
      IsFractionRing.injective R K hKeq
    -- Take ordOnRing of both sides.
    have hord : ordOnRing (R := R) (sc.fst * (sa.snd * sb.snd))
        = ordOnRing (R := R) (sa.fst * sb.fst * sc.snd) := by rw [hReq]
    rw [ordOnRing_mul_nonzero hdim sc.fst (sa.snd * sb.snd) hsc1ne (mul_ne_zero hsa2ne hsb2ne),
      ordOnRing_mul_nonzero hdim (sa.snd : R) (sb.snd : R) hsa2ne hsb2ne,
      ordOnRing_mul_nonzero hdim (sa.fst * sb.fst) (sc.snd : R) (mul_ne_zero hsa1ne hsb1ne) hsc2ne,
      ordOnRing_mul_nonzero hdim sa.fst sb.fst hsa1ne hsb1ne] at hord
    -- Now hord is a ℕ equation; cast and finish.
    have hZ : (ordOnRing (R := R) sc.fst : ℤ) + ((ordOnRing (R := R) (sa.snd : R) : ℤ)
          + (ordOnRing (R := R) (sb.snd : R) : ℤ))
        = ((ordOnRing (R := R) sa.fst : ℤ) + (ordOnRing (R := R) sb.fst : ℤ))
          + (ordOnRing (R := R) (sc.snd : R) : ℤ) := by
      have := congrArg (Nat.cast (R := ℤ)) hord
      push_cast at this
      linarith
    linarith
  · -- `ringKrullDim R ≠ 1`: all three `ordR` values are `0` by definition.
    rw [ordR, ordR, ordR, ite_eq_right hdim, ite_eq_right hdim, ite_eq_right hdim]
    ring

/-! ## Main Statement (Tag 02MI, Lemma 10.121.7) -/

/-! ### Structural sub-lemmas for the main theorem

The Stacks 02MI proof has four steps (independence of `M`, additivity in `φ`,
reduction to elementary generators of `GL(V)`, base cases). We expose each as a
named sub-lemma carrying its informal argument, and assemble the main theorem
from them. -/

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] [FiniteDimensional K V]
    in
/-- `φ(M)` is again a lattice when `M` is (image of a f.g. module under a
`K`-linear iso whose `K`-span is everything). -/
theorem mapLattice_isLattice (φ : V ≃ₗ[K] V) (M : Submodule R V)
    (hM : IsLattice (K := K) M) : IsLattice (K := K) (mapLattice φ M) := by
  -- STRATEGY: `mapLattice φ M = M.map (φ.restrictScalars R)`.
  -- FG: image of FG is FG (`Submodule.FG.map`).
  -- K-span = ⊤: `φ` is a `K`-linear iso, and image commutes with `K`-span;
  -- `span K (φ '' M) = φ '' (span K M) = φ '' ⊤ = ⊤` (use `Submodule.map_span` /
  -- `LinearEquiv.map_eq_top_iff` and `hM.2`). Note `φ.restrictScalars R` and `φ` have the
  -- same underlying set-map, so the `R`-image equals the `K`-image as a set.
  refine ⟨hM.left.map _, ?_⟩
  have hset : (mapLattice φ M : Set V) = (φ : V →ₗ[K] V) '' (M : Set V) := by
    simp only [mapLattice, Submodule.map_coe, LinearMap.coe_restrictScalars]
  rw [hset, Submodule.span_image, hM.right, Submodule.map_top]
  exact LinearEquiv.range φ

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] [FiniteDimensional K V]
    in
/-- `mapLattice` respects composition: `(φ ∘ ψ)(M) = φ(ψ(M))`. -/
theorem mapLattice_trans (φ ψ : V ≃ₗ[K] V) (M : Submodule R V) :
    mapLattice (ψ.trans φ) M = mapLattice φ (mapLattice ψ M) := by
  -- STRATEGY: unfold `mapLattice`; both sides are `Submodule.map` of the composite linear map.
  -- `Submodule.map_comp` and `LinearEquiv.coe_trans` / `restrictScalars` compatibility.
  unfold mapLattice
  rw [← Submodule.map_comp]
  rfl

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] [FiniteDimensional K V]
    in
/-- `mapLattice` of the identity is the identity. -/
theorem mapLattice_refl (M : Submodule R V) :
    mapLattice (LinearEquiv.refl K V) M = M := by
  -- STRATEGY: `simp [mapLattice]`; `(refl).restrictScalars` is the identity map, and
  -- `Submodule.map_id`.
  simp [mapLattice]

/-- Denominator clearing: every vector has a nonzero `A`-multiple lying in a lattice `Y`. -/
private theorem exists_ne_zero_smul_mem {A F W : Type*} [CommRing A] [Nontrivial A] [Field F]
    [Algebra A F] [IsFractionRing A F] [AddCommGroup W] [Module F W] [Module A W]
    [IsScalarTower A F W] (Y : Submodule A W) (hY : IsLattice (K := F) Y) (v : W) :
    ∃ r : A, r ≠ 0 ∧ r • v ∈ Y := by
  have hv : v ∈ Submodule.span F (Y : Set W) := by rw [hY.right]; trivial
  rw [Submodule.mem_span_set] at hv
  obtain ⟨c, hcsupp, hcsum⟩ := hv
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) c.support c
  refine ⟨(b : A), nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← hcsum, Finsupp.smul_sum]
  apply Submodule.sum_mem
  intro i hi
  obtain ⟨ri, hri⟩ := hb i hi
  show (b : A) • (c i • i) ∈ Y
  have key : (b : A) • (c i • i) = ri • i := by
    rw [← IsScalarTower.algebraMap_smul F (b : A) (c i • i), smul_smul,
      ← Algebra.smul_def, ← hri, IsScalarTower.algebraMap_smul F ri i]
  rw [key]
  exact Y.smul_mem ri (hcsupp hi)

omit [IsDomain R] [FiniteDimensional K V] in
/-- **Intersection of two lattices is a lattice (Stacks 02MF).** -/
theorem latticeInf_isLattice (M M' : Submodule R V)
    (hM : IsLattice (K := K) M) (hM' : IsLattice (K := K) M') :
    IsLattice (K := K) (M ⊓ M') := by
  refine ⟨?_, ?_⟩
  · -- FG: `M ⊓ M' ≤ M`, and `M` is a Noetherian `R`-module (f.g. over Noetherian `R`),
    -- so every submodule of `M` — in particular `M ⊓ M'` — is f.g.
    have : Module.Finite R M := Module.Finite.iff_fg.mpr hM.left
    have : IsNoetherian R M := inferInstance
    exact Submodule.FG.of_le_of_isNoetherian inf_le_left
  · -- `span K (M ⊓ M') = ⊤`: it suffices that `M ≤ span K (M ⊓ M')`, since `span K M = ⊤`.
    rw [eq_top_iff, ← hM.right, Submodule.span_le]
    intro v hv
    have hvM : v ∈ M := hv
    obtain ⟨r, hr0, hrM'⟩ := exists_ne_zero_smul_mem M' hM' v
    have hin : r • v ∈ M ⊓ M' := ⟨M.smul_mem r hvM, hrM'⟩
    have hspan : r • v ∈ Submodule.span K ((M ⊓ M' : Submodule R V) : Set V) :=
      Submodule.subset_span hin
    have hrne : (algebraMap R K r) ≠ 0 := by
      rwa [Ne, IsFractionRing.to_map_eq_zero_iff (K := K)]
    have hv_eq : v = (algebraMap R K r)⁻¹ • (r • v) := by
      rw [← IsScalarTower.algebraMap_smul K r v, smul_smul,
        inv_mul_cancel₀ hrne, one_smul]
    rw [SetLike.mem_coe, hv_eq]
    exact Submodule.smul_mem _ _ hspan

omit [FiniteDimensional K V] in
/-- **Finiteness of relative covolume (dimension-one content; Stacks 02MG).**
For lattices `A` and `Y ≤ A`, the quotient `A / Y` is a finitely generated
torsion `R`-module, hence has finite `R`-length. This is exactly where
`ringKrullDim R = 1` is used. -/
theorem latticeQuot_length_finite (hdim : ringKrullDim R = 1)
    (A Y : Submodule R V) (hA : IsLattice (K := K) A) (hY : IsLattice (K := K) Y) :
    Module.length R (↥A ⧸ Submodule.comap A.subtype Y) ≠ ⊤ := by
  -- STRATEGY (Stacks 02MG): `A` and `Y` are both lattices, so `A` is f.g. over `R` and
  -- `A/Y` is a f.g. `R`-module. Moreover `A/Y` is torsion: since `span K Y = ⊤ = span K A`,
  -- for any `a ∈ A` there is `0 ≠ r ∈ R` with `r • a ∈ Y` (clear denominators). A f.g.
  -- torsion module over a 1-dim Noetherian local domain has finite length (its support is
  -- the closed point only; `Module.length` finite ⇔ Artinian + Noetherian, and a f.g.
  -- torsion module over a 1-dim Noetherian domain is Artinian).
  set Q := ↥A ⧸ Submodule.comap A.subtype Y with hQ
  -- A is f.g.: pick a finite generating set in V.
  obtain ⟨s, hs⟩ := hA.left
  -- per-generator denominators
  choose f hf0 hfY using exists_ne_zero_smul_mem Y hY
  set r : R := ∏ v ∈ s, f v with hrdef
  have hr0 : r ≠ 0 := by
    rw [hrdef, Finset.prod_ne_zero_iff]
    intro v _; exact hf0 v
  -- r annihilates A modulo Y: for v ∈ A, r • v ∈ Y.
  have rAY : ∀ v ∈ A, r • v ∈ Y := by
    intro v hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        -- x ∈ s, so f x divides r; r • x = (r/f x) • (f x • x) ∈ Y
        have hdvd : f x ∣ r := by
          rw [hrdef]; exact Finset.dvd_prod_of_mem f hx
        obtain ⟨t, ht⟩ := hdvd
        have : r • x = t • (f x • x) := by rw [ht, smul_smul, mul_comm]
        rw [this]
        exact Y.smul_mem t (hfY x)
    | zero => simp
    | add x y hx hy ihx ihy =>
        rw [smul_add]; exact Y.add_mem ihx ihy
    | smul a x hx ih =>
        rw [smul_comm]; exact Y.smul_mem a ih
  -- Q is torsion by the ideal (r).
  have htor : Module.IsTorsionBySet R Q (Ideal.span {r} : Set R) := by
    intro q c
    obtain ⟨c, hc⟩ := c
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show (d * r) • (Submodule.Quotient.mk a) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show (d * r) • (a : V) ∈ Y
    rw [mul_smul]
    exact Y.smul_mem d (rAY a a.property)
  -- finiteness endgame
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]
  have : Module.Finite R ↥A := Module.Finite.iff_fg.mpr hA.left
  have hnoeth : IsNoetherian R Q := isNoetherian_of_isNoetherianRing_of_finite R _
  refine ⟨hnoeth, ?_⟩
  have hartRing := isArtinianRing_quotient_span_singleton hdim hr0
  set I := Ideal.span {r} with hIdef
  let hmod : Module (R ⧸ I) Q := htor.module
  have htower : IsScalarTower R (R ⧸ I) Q := htor.isScalarTower
  -- Q is f.g. over R/I, R/I Artinian ⇒ IsArtinian (R/I) Q
  have : Module.Finite (R ⧸ I) Q :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I) Q
  have : IsArtinian (R ⧸ I) Q := isArtinian_of_fg_of_artinian'
  -- transfer IsArtinian (R/I) Q → IsArtinian R Q
  exact isArtinian_of_surjective_algebraMap (R := R ⧸ I) Ideal.Quotient.mk_surjective

omit [FiniteDimensional K V] in
/-- **Additivity of distance (Stacks 02MH).** For lattices `M, M', M''`,
`d(M, M'') = d(M, M') + d(M', M'')`. -/
theorem latticeDist_additivity (hdim : ringKrullDim R = 1)
    (M M' M'' : Submodule R V)
    (hM : IsLattice (K := K) M) (hM' : IsLattice (K := K) M')
    (hM'' : IsLattice (K := K) M'') :
    latticeDist M M'' = latticeDist M M' + latticeDist M' M'' := by
  -- PROOF: Let `A = M ⊔ M' ⊔ M''` be a common ambient lattice and define the "covolume"
  -- `c Y = (length_R (A / Y)).toNat` for `Y ≤ A`.  Using additivity of `Module.length` in the
  -- nested tower `Y ⊓ Z ≤ Y ≤ A` (the `nested` have, proved unconditionally via the third
  -- isomorphism theorem and `Module.length_eq_add_of_exact`), one gets
  --   `c (B₁ ⊓ B₂) = c B₁ + lenQuot B₁ B₂`  and  `c (B₁ ⊓ B₂) = c B₂ + lenQuot B₂ B₁`,
  -- hence `latticeDist B₁ B₂ = c B₂ - c B₁`.  The identity then telescopes:
  --   `d(M,M'') = c M'' - c M = (c M' - c M) + (c M'' - c M') = d(M,M') + d(M',M'')`.
  -- Finiteness of the relevant lengths is `latticeQuot_length_finite` (the dim-one input).
  set A : Submodule R V := M ⊔ M' ⊔ M'' with hA
  have hMA : M ≤ A := le_sup_of_le_left le_sup_left
  have hM'A : M' ≤ A := le_sup_of_le_left le_sup_right
  have hM''A : M'' ≤ A := le_sup_right
  -- `A` is a lattice (FG: sup of FG; span = ⊤ since it contains the lattice `M`).
  have hAlat : IsLattice (K := K) A := by
    refine ⟨(hM.left.sup hM'.left).sup hM''.left, ?_⟩
    have hle : Submodule.span K (M : Set V) ≤ Submodule.span K (A : Set V) :=
      Submodule.span_mono hMA
    rw [hM.right] at hle
    exact top_le_iff.mp hle
  -- Unconditional length-additivity in a nested tower `Z ≤ Y ≤ A`.
  have nested : ∀ (Y Z : Submodule R V), Z ≤ Y → Y ≤ A →
      Module.length R (↥A ⧸ Submodule.comap A.subtype Z)
        = Module.length R (↥A ⧸ Submodule.comap A.subtype Y)
          + Module.length R (↥Y ⧸ Submodule.comap Y.subtype Z) := by
    intro Y Z hZY hYA
    set S := Submodule.comap A.subtype Z with hS
    set T := Submodule.comap A.subtype Y with hT
    have hST : S ≤ T := Submodule.comap_mono hZY
    have step2 : Module.length R (↥(Submodule.map S.mkQ T))
        = Module.length R (↥T ⧸ Submodule.comap T.subtype S) := by
      set f : ↥T →ₗ[R] (↥A ⧸ S) := S.mkQ.comp T.subtype with hf
      have hker : LinearMap.ker f = Submodule.comap T.subtype S := by
        rw [hf, LinearMap.ker_comp, Submodule.ker_mkQ]
      have hrange : LinearMap.range f = Submodule.map S.mkQ T := by
        rw [hf, LinearMap.range_comp, Submodule.range_subtype]
      have e := LinearMap.quotKerEquivRange f
      rw [hker, hrange] at e
      exact e.length_eq.symm
    have step3 : Module.length R (↥T ⧸ Submodule.comap T.subtype S)
        = Module.length R (↥Y ⧸ Submodule.comap Y.subtype Z) := by
      have hmap : Submodule.map
          ((Submodule.comapSubtypeEquivOfLe hYA) : ↥(Submodule.comap A.subtype Y) →ₗ[R] ↥Y)
          (Submodule.comap (Submodule.comap A.subtype Y).subtype (Submodule.comap A.subtype Z))
            = Submodule.comap Y.subtype Z := by
        ext x
        simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
          Submodule.comapSubtypeEquivOfLe, LinearMap.coe_mk, AddHom.coe_mk]
        constructor
        · rintro ⟨y, hy, rfl⟩; exact hy
        · intro hx
          refine ⟨⟨⟨(x : V), hYA x.property⟩, ?_⟩, hx, by ext; rfl⟩
          show (⟨(x : V), hYA x.property⟩ : ↥A) ∈ Submodule.comap A.subtype Y
          rw [Submodule.mem_comap]; exact x.property
      exact (Submodule.Quotient.equiv
        (Submodule.comap (Submodule.comap A.subtype Y).subtype (Submodule.comap A.subtype Z))
        (Submodule.comap Y.subtype Z) (Submodule.comapSubtypeEquivOfLe hYA) hmap).length_eq
    rw [length_quotient_eq_add_map hST, step2, step3, add_comm]
  -- Finiteness (dimension-one content; Stacks 02MG) via `latticeQuot_length_finite`.
  have hfin : ∀ Y : Submodule R V, IsLattice (K := K) Y → Y ≤ A →
      Module.length R (↥A ⧸ Submodule.comap A.subtype Y) ≠ ⊤ :=
    fun Y hY _ => latticeQuot_length_finite hdim A Y hAlat hY
  set c : Submodule R V → ℕ :=
    fun Y => (Module.length R (↥A ⧸ Submodule.comap A.subtype Y)).toNat with hc
  have hlen : ∀ (B₁ B₂ : Submodule R V), IsLattice (K := K) B₁ → IsLattice (K := K) B₂ →
      B₁ ≤ A → B₂ ≤ A → (lenQuot B₁ B₂ : ℤ) = (c (B₁ ⊓ B₂) : ℤ) - (c B₁ : ℤ) := by
    intro B₁ B₂ hB₁ hB₂ h1 h2
    have e1 := nested B₁ (B₁ ⊓ B₂) inf_le_left h1
    have hfA1 : Module.length R (↥A ⧸ Submodule.comap A.subtype B₁) ≠ ⊤ := hfin B₁ hB₁ h1
    have hfinf1 : Module.length R (↥A ⧸ Submodule.comap A.subtype (B₁ ⊓ B₂)) ≠ ⊤ :=
      hfin (B₁ ⊓ B₂) (latticeInf_isLattice B₁ B₂ hB₁ hB₂) (le_trans inf_le_left h1)
    have hLfin1 : Module.length R (↥B₁ ⧸ Submodule.comap B₁.subtype (B₁ ⊓ B₂)) ≠ ⊤ := by
      intro h; rw [e1, h, add_top] at hfinf1; exact hfinf1 rfl
    have t1 : c (B₁ ⊓ B₂) = c B₁ + lenQuot B₁ B₂ := by
      show (Module.length R (↥A ⧸ Submodule.comap A.subtype (B₁ ⊓ B₂))).toNat
        = (Module.length R (↥A ⧸ Submodule.comap A.subtype B₁)).toNat + lenQuot B₁ B₂
      rw [e1, ENat.toNat_add hfA1 hLfin1]; rfl
    have := congrArg (Nat.cast (R := ℤ)) t1
    push_cast at this ⊢; linarith
  have key : ∀ (B₁ B₂ : Submodule R V), IsLattice (K := K) B₁ → IsLattice (K := K) B₂ →
      B₁ ≤ A → B₂ ≤ A →
      latticeDist B₁ B₂ = (c B₂ : ℤ) - (c B₁ : ℤ) := by
    intro B₁ B₂ hB₁ hB₂ h1 h2
    unfold latticeDist
    rw [hlen B₁ B₂ hB₁ hB₂ h1 h2, hlen B₂ B₁ hB₂ hB₁ h2 h1, inf_comm B₂ B₁]
    ring
  rw [key M M'' hM hM'' hMA hM''A, key M M' hM hM' hMA hM'A, key M' M'' hM' hM'' hM'A hM''A]
  ring

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] [FiniteDimensional K V]
    in
/-- A `K`-linear iso preserves distance between lattices: `d(φ(M), φ(M')) = d(M, M')`. -/
theorem latticeDist_map_map (φ : V ≃ₗ[K] V) (M M' : Submodule R V) :
    latticeDist (mapLattice φ M) (mapLattice φ M') = latticeDist M M' := by
  -- STRATEGY: `φ.restrictScalars R` is an `R`-linear iso `V ≃ₗ[R] V`. It carries `M ⊓ M'` to
  -- `φ(M) ⊓ φ(M')` (image of inf under an iso = inf of images: `Submodule.map_inf_eq` for an
  -- injective/iso map), and induces `R`-linear isos `M/(M⊓M') ≅ φ(M)/(φ(M)⊓φ(M'))`, hence
  -- equal `Module.length`. So `lenQuot (φM) (φM') = lenQuot M M'` and likewise swapped,
  -- giving equal `latticeDist`. Mathlib: `Submodule.equivMapOfInjective`,
  -- `LinearEquiv.length_eq` / `Module.length` is an isomorphism invariant.
  have key : ∀ A B : Submodule R V,
      lenQuot (mapLattice φ A) (mapLattice φ B) = lenQuot A B := by
    intro A B
    unfold lenQuot mapLattice
    set ψ := (φ : V →ₗ[K] V).restrictScalars R with hψ
    set e : V ≃ₗ[R] V := φ.restrictScalars R with he
    have hinj : Function.Injective ψ := e.injective
    congr 1
    set e1 := Submodule.equivMapOfInjective ψ hinj A with he1
    have hmap : Submodule.map (e1 : ↥A →ₗ[R] ↥(Submodule.map ψ A))
        (Submodule.comap A.subtype (A ⊓ B)) =
        Submodule.comap (Submodule.map ψ A).subtype (Submodule.map ψ A ⊓ Submodule.map ψ B) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx ⊢
        simp only [he1]
        obtain ⟨hxA, hxB⟩ := hx
        exact ⟨⟨x, hxA, rfl⟩, ⟨x, hxB, rfl⟩⟩
      · intro hy
        simp only [Submodule.mem_comap, Submodule.coe_subtype] at hy
        obtain ⟨hyA, hyB⟩ := hy
        obtain ⟨a, haA, hay⟩ := hyA
        obtain ⟨z, hzB, hzy⟩ := hyB
        have haz : a = z := hinj (by rw [hay, hzy])
        refine ⟨⟨a, haA⟩, ?_, ?_⟩
        · rw [SetLike.mem_coe, Submodule.mem_comap]
          simp only [Submodule.coe_subtype, Submodule.mem_inf]
          exact ⟨haA, haz ▸ hzB⟩
        · apply Subtype.ext
          simp only [he1]
          exact hay
    exact (Submodule.Quotient.equiv (R := R) (Submodule.comap A.subtype (A ⊓ B))
      (Submodule.comap (Submodule.map ψ A).subtype (Submodule.map ψ A ⊓ Submodule.map ψ B))
      e1 hmap).length_eq.symm
  unfold latticeDist
  rw [key M M', key M' M]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] in
/-- `d(M, M) = 0`. -/
theorem latticeDist_self (M : Submodule R V) : latticeDist M M = 0 := by
  -- STRATEGY: `M ⊓ M = M`, so `comap M.subtype (M ⊓ M) = ⊤`, the quotient `↥M/⊤` is trivial,
  -- `Module.length = 0`, hence `lenQuot M M = 0` and `latticeDist M M = 0 - 0 = 0`.
  -- `simp [latticeDist, lenQuot]` after rewriting `M ⊓ M`.
  simp only [latticeDist, sub_self]

omit [FiniteDimensional K V] in
/-- **Independence of the chosen lattice (Stacks 02MI step 1).**
`d(M, φ(M)) = d(M', φ(M'))` for any two lattices `M, M'`. -/
theorem dist_map_indep (hdim : ringKrullDim R = 1) (φ : V ≃ₗ[K] V) (M M' : Submodule R V)
    (hM : IsLattice (K := K) M) (hM' : IsLattice (K := K) M') :
    latticeDist M (mapLattice φ M) = latticeDist M' (mapLattice φ M') := by
  -- STRATEGY (Stacks 02MI step 1): using additivity (`latticeDist_additivity`) and
  -- antisymmetry `d(A,B) = -d(B,A)` (a consequence of additivity + `latticeDist_self`):
  --   d(M, φM) - d(M', φM')
  --     = [d(M,M') + d(M',φM)] - [d(M',φM) + d(φM, φM')]   (additivity, regroup)
  --     = d(M,M') - d(φM, φM')
  --     = d(M,M') - d(M,M')                                 (latticeDist_map_map)
  --     = 0.
  -- All sub-lattices involved (M, M', φM, φM') are lattices by `mapLattice_isLattice`/02MF.
  set φM := mapLattice φ M with hφMdef
  set φM' := mapLattice φ M' with hφM'def
  have hφM : IsLattice (K := K) φM := mapLattice_isLattice φ M hM
  have hφM' : IsLattice (K := K) φM' := mapLattice_isLattice φ M' hM'
  have antisymm : ∀ A B : Submodule R V, latticeDist B A = - latticeDist A B := by
    intro A B; unfold latticeDist; ring
  have hmap : latticeDist φM φM' = latticeDist M M' := latticeDist_map_map φ M M'
  have a1 : latticeDist M φM = latticeDist M M' + latticeDist M' φM :=
    latticeDist_additivity hdim M M' φM hM hM' hφM
  have a2 : latticeDist M' φM = latticeDist M' φM' + latticeDist φM' φM :=
    latticeDist_additivity hdim M' φM' φM hM' hφM' hφM
  have h3 : latticeDist φM' φM = - latticeDist M M' := by
    rw [antisymm φM φM', hmap]
  rw [a1, a2, h3]; ring

omit [FiniteDimensional K V] in
/-- **Additivity in `φ` (Stacks 02MI step 2, LHS).**
`d(M, (φ∘ψ)(M)) = d(M, φ(M)) + d(M, ψ(M))`. -/
theorem dist_map_comp (hdim : ringKrullDim R = 1) (φ ψ : V ≃ₗ[K] V) (M : Submodule R V)
    (hM : IsLattice (K := K) M) :
    latticeDist M (mapLattice (φ.trans ψ) M)
      = latticeDist M (mapLattice φ M) + latticeDist M (mapLattice ψ M) := by
  -- additivity bookkeeping verified consistent; needs hdim for additivity/independence route).
  -- STRATEGY (Stacks 02MI step 2): `mapLattice (φ.trans ψ) M = ψ(φ(M))` by `mapLattice_trans`.
  -- By additivity, `d(M, ψ(φ(M))) = d(M, φ(M)) + d(φ(M), ψ(φ(M)))`. The second term:
  -- `d(φ(M), ψ(φ(M))) = d(M', ψ(M'))` with `M' = φ(M)` a lattice, which by independence
  -- (`dist_map_indep`) equals `d(M, ψ(M))`. Hence the sum. (Note: order of trans vs ∘ must be
  -- matched to `LinearEquiv.det_trans`; `φ.trans ψ` is `ψ ∘ φ`.)
  set φM := mapLattice φ M with hφMdef
  have hφM : IsLattice (K := K) φM := mapLattice_isLattice φ M hM
  have htrans : mapLattice (φ.trans ψ) M = mapLattice ψ φM := mapLattice_trans ψ φ M
  rw [htrans]
  have hadd : latticeDist M (mapLattice ψ φM)
      = latticeDist M φM + latticeDist φM (mapLattice ψ φM) :=
    latticeDist_additivity hdim M φM (mapLattice ψ φM) hM hφM
      (mapLattice_isLattice ψ φM hφM)
  have hindep : latticeDist M (mapLattice ψ M) = latticeDist φM (mapLattice ψ φM) :=
    dist_map_indep hdim ψ M φM hM hφM
  rw [hadd, hindep]

/-! ## Glue lemmas for the `GL_n` reduction (Stacks 02MI steps 3–4)

The core `dist_map_eq_ord_det_std` reduces, via a choice of `K`-basis `b` of `V`
and the standard lattice `N = span R (range b)`, to checking the identity on the
matrix generators of `GL_n(K)` (transvections and diagonal matrices), using
`Matrix.diagonal_transvection_induction`.  The three lemmas below provide the
required dictionary between matrices and the `K`-linear equivalences
`Matrix.toLinearEquiv b · ·`. -/

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra R K] [IsFractionRing R K]
    [FiniteDimensional K V] [IsScalarTower R K V] in
/-- The standard lattice `N = span_R (range b)` of a `K`-basis `b` is a lattice:
finitely generated (span of a finite set) with `K`-span all of `V`. -/
theorem stdLattice_isLattice (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    IsLattice (K := K) (Submodule.span R (Set.range b)) := by
  constructor
  · exact Submodule.fg_span (Set.finite_range b)
  · rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩)

omit [FiniteDimensional K V] in
/-- `det` of the `K`-linear equivalence built from a unit matrix `C` is `C.det`
(at the level of the underlying field element). -/
theorem toLinearEquiv_det_coe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (C : Matrix ι ι K) (hC : IsUnit C.det) :
    ((LinearEquiv.det (Matrix.toLinearEquiv b C hC)) : K) = C.det := by
  rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix b]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [LinearEquiv.coe_coe, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  simp [map_sum, map_smul, Finsupp.single_apply, b.repr_self, Finset.sum_ite_eq']

omit [FiniteDimensional K V] in
/-- The matrix-to-equivalence map is multiplicative: the equivalence of a product
`C * D` is the composite of the equivalences of `D` then `C`. -/
theorem toLinearEquiv_trans {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (C D : Matrix ι ι K) (hC : IsUnit C.det) (hD : IsUnit D.det)
    (hCD : IsUnit (C * D).det) :
    Matrix.toLinearEquiv b (C * D) hCD
      = (Matrix.toLinearEquiv b D hD) ≪≫ₗ (Matrix.toLinearEquiv b C hC) := by
  apply LinearEquiv.toLinearMap_injective
  ext x
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  rw [Matrix.toLinearEquiv_apply, Matrix.toLinearEquiv_apply, Matrix.toLinearEquiv_apply]
  rw [Matrix.toLin_mul b b b C D]; rfl

omit [FiniteDimensional K V] in
/-- The transvection matrix `transvection i j c` acts on the basis vector `b m` by adding
`c • b i` when `m = j`, and fixes it otherwise. -/
theorem toLinearEquiv_transvection_apply
    (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (i j : Fin (Module.finrank K V)) (c : K)
    (hC : IsUnit (Matrix.transvection i j c).det) (m : Fin (Module.finrank K V)) :
    (Matrix.toLinearEquiv b (Matrix.transvection i j c) hC) (b m)
      = b m + (if m = j then c • b i else 0) := by
  rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  have hentry : ∀ k, (Matrix.transvection i j c) k m
      = (if k = m then 1 else 0) + (if k = i ∧ m = j then c else 0) := by
    intro k
    rw [Matrix.transvection]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    split_ifs with h1 h2 h3 h4 h5 <;> first | rfl | (exfalso; tauto)
  simp_rw [hentry, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, one_smul]
  rw [Finset.sum_ite_eq' Finset.univ m b]
  congr 1
  · simp
  · by_cases hmj : m = j
    · subst hmj
      simp only [and_true, ite_eq_left]
      rw [Finset.sum_ite_eq' Finset.univ i (fun k => c • b k)]
      simp
    · simp only [hmj, and_false, ite_false, Finset.sum_const_zero]

/-- `ord_R(1) = 0`, stated before its first use. -/
private theorem ordR_one_aux (hdim : ringKrullDim R = 1) : ordR (R := R) (1 : Kˣ) = 0 := by
  rw [ordR_apply_algebraMap hdim (1 : R) one_ne_zero 1 (by simp), ordOnRing,
    Ideal.span_singleton_one]
  simp

omit [FiniteDimensional K V] in
/-- **Transvection base case (Stacks 02MI step 4).** For a transvection
`t : TransvectionStruct (Fin n) K` (which has determinant `1`), the associated
`K`-linear equivalence `e_t = toLinearEquiv b t.toMatrix` maps the standard
lattice `N = span_R (range b)` to itself, so `d(N, e_t(N)) = 0`; on the other
side `ord_R(det e_t) = ord_R(1) = 0`.

STRATEGY: `e_t` sends each basis vector `b j` to `b j + t.c • b t.i` (for the
column `t.j = j`) or to `b j` (otherwise), all of which lie in `N`; the same
holds for `e_t⁻¹` (a transvection with parameter `-t.c`). Hence
`mapLattice e_t N = N` (show `⊆` both ways via `Submodule.map_le_iff_le_comap`
and generators), giving `d(N, N) = 0` by `latticeDist_self`. For the RHS,
`det e_t = 1` because `t.toMatrix.det = 1` (`TransvectionStruct.det`) and
`toLinearEquiv_det_coe`; then `ord_R(1) = 0` (a unit `1 : Kˣ`: `ordR_apply_algebraMap`
with `x = 1`, or directly `ordR 1 = 0` since `1 = 1/1`).
KEY NAMES: `Matrix.TransvectionStruct.toMatrix`, `Matrix.transvection`,
`Matrix.transvection_mulVec` / explicit action on basis, `Submodule.map_span`,
`Matrix.TransvectionStruct.det`. -/
theorem dist_map_eq_ord_det_transvection (hdim : ringKrullDim R = 1)
    (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (t : Matrix.TransvectionStruct (Fin (Module.finrank K V)) K)
    (hC : IsUnit t.toMatrix.det) :
    latticeDist (Submodule.span R (Set.range b))
        (mapLattice (Matrix.toLinearEquiv b t.toMatrix hC) (Submodule.span R (Set.range b)))
      = ordR (R := R) (LinearEquiv.det (Matrix.toLinearEquiv b t.toMatrix hC)) := by
  set i := t.i with hi
  set j := t.j with hj
  set c := t.c with hc
  have hij : i ≠ j := t.hij
  have htm : t.toMatrix = Matrix.transvection i j c := rfl
  set e_t := Matrix.toLinearEquiv b t.toMatrix hC with he_t
  -- RHS = 0: `det e_t = 1`, so `ord_R(1) = 0`.
  have hRHS : ordR (R := R) (LinearEquiv.det e_t) = 0 := by
    have hdetcoe : ((LinearEquiv.det e_t : Kˣ) : K) = 1 := by
      rw [he_t, toLinearEquiv_det_coe b t.toMatrix hC, t.det]
    have hdet1 : LinearEquiv.det e_t = (1 : Kˣ) := by
      apply Units.ext; rw [hdetcoe]; rfl
    rw [hdet1, ordR_one_aux hdim]
  rw [hRHS]
  -- LHS = 0.  We build a lattice `M'` adapted to the transvection, fixed by `e_t`,
  -- then transfer via `dist_map_indep`.
  set N := Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)) with hN
  have hNlat : IsLattice (K := K) N := stdLattice_isLattice b
  -- write the (arbitrary) parameter `c ∈ K` as `p / q` with `p, q ∈ R`, `q ≠ 0`.
  obtain ⟨p, q, hq, hcpq⟩ := IsFractionRing.div_surjective (A := R) c
  have hqK : algebraMap R K q ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact nonZeroDivisors.ne_zero hq
  set qinv : K := (algebraMap R K q)⁻¹ with hqinv
  -- adapted basis scaling: scale the `i`-th coordinate by `1/q`.
  set D : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K :=
    Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i qinv) with hD
  have hDunit : IsUnit D.det := by
    rw [hD, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro a _
    by_cases ha : a = i
    · subst ha; simp [Function.update_self, hqinv, inv_ne_zero hqK]
    · simp [Function.update_of_ne ha]
  set g := Matrix.toLinearEquiv b D hDunit with hg
  set M' := mapLattice g N with hM'
  have hM'lat : IsLattice (K := K) M' := mapLattice_isLattice g N hNlat
  -- `g (b m) = (update 1 i qinv) m • b m`
  have hgb : ∀ m, g (b m)
      = (Function.update (1 : Fin (Module.finrank K V) → K) i qinv) m • b m := by
    intro m
    rw [hg, Matrix.toLinearEquiv_apply, Matrix.toLin_self, hD, Finset.sum_eq_single m]
    · simp [Matrix.diagonal_apply_eq]
    · intro k _ hk
      rw [Matrix.diagonal_apply_ne _ hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  -- the generators of `M'`
  set w : Fin (Module.finrank K V) → V :=
    fun m => (Function.update (1 : Fin (Module.finrank K V) → K) i qinv) m • b m with hw
  have hgw : ∀ m, g (b m) = w m := hgb
  have hMw : M' = Submodule.span R (Set.range w) := by
    rw [hM', mapLattice, hN, Submodule.map_span, ← Set.range_comp]
    exact congrArg (fun s => Submodule.span R (Set.range s)) (funext hgw)
  -- action of `e_t` on basis vectors
  have hetb : ∀ m, e_t (b m) = b m + (if m = j then c • b i else 0) := by
    intro m
    rw [he_t]
    have key := toLinearEquiv_transvection_apply b i j c (htm ▸ hC) m
    rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self] at key ⊢
    rw [htm]
    convert key using 3
  have hwi : w i = qinv • b i := by simp [hw, Function.update_self]
  have hwm : ∀ m, m ≠ i → w m = b m := by
    intro m hm; simp [hw, Function.update_of_ne hm]
  have hwi_mem : w i ∈ Submodule.span R (Set.range w) := Submodule.subset_span ⟨i, rfl⟩
  -- `p • w i = c • b i`, the integral relation that makes `M'` adapted.
  have hpwi : (p : R) • w i = c • b i := by
    rw [hwi, ← IsScalarTower.algebraMap_smul K p (qinv • b i), smul_smul, hqinv, ← hcpq,
      div_eq_mul_inv]
  -- an equivalence acting as the transvection with parameter `c'` maps `M'`'s generators into `M'`.
  have hmaps : ∀ (f : V ≃ₗ[K] V) (c' : K) (p' : R), p' • w i = c' • b i →
      (∀ m, f (b m) = b m + (if m = j then c' • b i else 0)) →
      ∀ m, f (w m) ∈ Submodule.span R (Set.range w) := by
    intro f c' p' hp hf m
    by_cases hm : m = i
    · subst hm
      rwa [hwi, map_smul, hf i, ite_eq_right hij, add_zero, ← hwi]
    · rw [hwm m hm, hf m]
      by_cases hmj : m = j
      · subst hmj
        rw [ite_eq_left rfl, ← hp]
        refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hwi_mem)
        exact Submodule.subset_span ⟨j, (hwm j hm)⟩
      · rw [ite_eq_right hmj, add_zero]
        exact Submodule.subset_span ⟨m, hwm m hm⟩
  have het_w := hmaps e_t c p hpwi hetb
  -- `e_t⁻¹` acts like the transvection with parameter `-c`.
  have hetinv : ∀ m, e_t.symm (b m) = b m + (if m = j then (-c) • b i else 0) := by
    intro m
    apply e_t.injective
    rw [LinearEquiv.apply_symm_apply]
    by_cases hmj : m = j
    · subst hmj
      rw [ite_eq_left rfl, map_add, hetb j, ite_eq_left rfl, map_smul, hetb i,
          ite_eq_right hij, add_zero,
        neg_smul]
      abel
    · rw [ite_eq_right hmj, add_zero, hetb m, ite_eq_right hmj, add_zero]
  have hetinv_w := hmaps e_t.symm (-c) (-p) (by rw [neg_smul, neg_smul, hpwi]) hetinv
  -- hence `e_t` stabilizes `M'`.
  have hstable : mapLattice e_t M' = M' := by
    apply le_antisymm
    · rw [mapLattice, hMw, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact het_w m
    · rw [hMw, Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact ⟨e_t.symm (w m), hetinv_w m, by simp [LinearEquiv.apply_symm_apply]⟩
  -- transfer from `N` to the adapted lattice `M'`, where the distance is `0`.
  rw [dist_map_indep hdim e_t N M' hNlat hM'lat, hstable, latticeDist_self]

/-! ### The diagonal base case: single-coordinate dilations -/

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [FiniteDimensional K V] in
open Module in
/-- The basis `b` is `R`-linearly independent (since `R ↪ K`). -/
theorem b_li_R (b : Module.Basis (Fin (Module.finrank K V)) K V) :
    LinearIndependent R (b : Fin (Module.finrank K V) → V) := by
  apply LinearIndependent.restrict_scalars ?_ b.linearIndependent
  intro x y hxy; simp only [Algebra.smul_def, mul_one] at hxy
  exact IsFractionRing.injective R K hxy

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [FiniteDimensional K V] in
/-- `R`-coordinates of a vector w.r.t. the basis `b` are unique. -/
theorem coords_unique (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (c d : Fin (Module.finrank K V) → R)
    (h : ∑ j, c j • b j = ∑ j, d j • b j) : c = d := by
  have hzero : ∑ j, (algebraMap R K (c j) - algebraMap R K (d j)) • b j = 0 := by
    have hK : ∑ j, (algebraMap R K (c j)) • b j = ∑ j, (algebraMap R K (d j)) • b j := by
      simpa only [IsScalarTower.algebraMap_smul] using h
    simp only [sub_smul, Finset.sum_sub_distrib, hK, sub_self]
  have hli := (Fintype.linearIndependent_iff.mp b.linearIndependent)
    (fun j => algebraMap R K (c j) - algebraMap R K (d j)) hzero
  funext j; exact IsFractionRing.injective R K (sub_eq_zero.mp (hli j))

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [FiniteDimensional K V] in
/-- Membership characterization for the image of the standard lattice under a single-coordinate
integral dilation: `∑ c j • b j` lies in the dilated lattice iff its `i`-th coordinate is in `(r)`.
-/
theorem memEN_iff (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (i : Fin (Module.finrank K V)) (r : R) (c : Fin (Module.finrank K V) → R) :
    (∑ j, c j • b j) ∈ Submodule.span R (Set.range (fun j =>
        (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap R K r)) j • b j))
      ↔ c i ∈ Ideal.span {r} := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨d, hd⟩
    have hLHS : ∑ j, d j • ((Function.update (1 : Fin (Module.finrank K V) → K) i
        (algebraMap R K r)) j • b j) = ∑ j, (Function.update d i (d i * r)) j • b j := by
      apply Finset.sum_congr rfl; intro j _
      by_cases hj : j = i
      · subst hj; simp only [Function.update_self]; rw [IsScalarTower.algebraMap_smul, smul_smul]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, Pi.one_apply, one_smul]
    rw [hLHS] at hd
    have hcd := coords_unique b _ _ hd
    have hci : c i = d i * r := by rw [← hcd, Function.update_self]
    rw [hci]; exact Ideal.mem_span_singleton'.mpr ⟨d i, by ring⟩
  · rintro hmem
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨Function.update c i e, ?_⟩
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; rw [IsScalarTower.algebraMap_smul, smul_smul, he]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Pi.one_apply, one_smul]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [FiniteDimensional K V] in
open Module in
/-- A vector of `N = span_R (range b)` written in its `R`-coordinates over `b`. -/
theorem coe_sum_repr (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (x : ↥(Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)))) :
    (x : V) = ∑ j, ((Basis.span (b_li_R b)).repr x j) • b j := by
  have h := (Basis.span (b_li_R b)).sum_repr x
  apply_fun (fun y : ↥(Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V))) => (y : V))
    at h
  rw [← h]; push_cast
  apply Finset.sum_congr rfl; intro j _; rw [Basis.span_apply]

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [FiniteDimensional K V] in
open Module in
/-- Core length computation: the quotient of the standard lattice by the image of a
single-coordinate
integral dilation has length equal to `length_R (R/(r))`. -/
theorem core_length (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (i : Fin (Module.finrank K V)) (r : R) :
    Module.length R (↥(Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V))) ⧸
        Submodule.comap (Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V))).subtype
          (Submodule.span R (Set.range (fun j =>
            (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap R K r)) j • b j))))
      = Module.length R (R ⧸ Ideal.span {r}) := by
  set N := Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)) with hN
  let bN : Module.Basis (Fin (Module.finrank K V)) R N := Basis.span (b_li_R b)
  let f : ↥N →ₗ[R] R ⧸ Ideal.span {r} := (Ideal.span {r}).mkQ.comp (bN.coord i)
  have hsurj : Function.Surjective f := by
    apply Function.Surjective.comp (Submodule.mkQ_surjective _)
    intro s
    refine ⟨bN.repr.symm (Finsupp.single i s), ?_⟩
    simp [bN, Basis.coord_apply]
  have hker : LinearMap.ker f = Submodule.comap N.subtype
      (Submodule.span R (Set.range (fun j =>
        (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap R K r)) j • b j))) := by
    ext x
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Basis.coord_apply, Submodule.mem_comap, Submodule.coe_subtype]
    rw [coe_sum_repr b x]
    rw [memEN_iff b i r (fun j => bN.repr x j)]
  have e := LinearMap.quotKerEquivRange f
  rw [hker] at e
  rw [LinearMap.range_eq_top.mpr hsurj] at e
  rw [e.length_eq]
  exact (Submodule.topEquiv).length_eq

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsFractionRing R K] [FiniteDimensional K V]
    in
/-- The image of `N = span_R (range b)` under the diagonal dilation
`diagonal (update 1 i a)` is the span of the dilated basis family. -/
theorem mapLattice_diag_eq (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (a : K) (i : Fin (Module.finrank K V))
    (hC : IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a)).det) :
    mapLattice (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K
        V) → K) i a)) hC) (Submodule.span R (Set.range b))
      = Submodule.span R (Set.range (fun j =>
          (Function.update (1 : Fin (Module.finrank K V) → K) i a) j • b j)) := by
  unfold mapLattice
  rw [Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1
  funext j
  simp only [Function.comp_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  rw [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  rw [Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hk; rw [Matrix.diagonal_apply_ne _ hk, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

omit [FiniteDimensional K V] in
/-- `det (diagonal (update 1 i a)) = a`. -/
theorem det_diag_single (a : K) (i : Fin (Module.finrank K V)) :
    (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a)).det = a := by
  rw [Matrix.det_diagonal, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Function.update_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [FiniteDimensional K V] in
/-- The determinant of the single-coordinate dilation `diagonal (update 1 i a)` is a unit
whenever `a ≠ 0`. -/
theorem isUnit_det_diag_single {a : K} (ha : a ≠ 0) (i : Fin (Module.finrank K V)) :
    IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a)).det := by
  rw [det_diag_single]; exact ha.isUnit

omit [FiniteDimensional K V] in
/-- `toLinearEquiv` is congruent under matrix equality. -/
theorem toLinearEquiv_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) {C C' : Matrix ι ι K} (h : C = C')
    (hC : IsUnit C.det) (hC' : IsUnit C'.det) :
    Matrix.toLinearEquiv b C hC = Matrix.toLinearEquiv b C' hC' := by subst h; rfl

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [FiniteDimensional K V] in
/-- Integral single-coordinate dilation: `d(N, e_{r} N) = length_R(R/(r))`. -/
theorem latticeDist_integral'
    (b : Module.Basis (Fin (Module.finrank K V)) K V) (i : Fin (Module.finrank K V)) (r : R)
    (hC : IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap
        R K r))).det) :
    latticeDist (Submodule.span R (Set.range b))
        (mapLattice (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin
            (Module.finrank K V) → K) i (algebraMap R K r))) hC) (Submodule.span R (Set.range b)))
      = (ordOnRing (R := R) r : ℤ) := by
  set N := Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)) with hN
  set eN := Submodule.span R (Set.range (fun j =>
      (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap R K r)) j • b j)) with heN
  rw [mapLattice_diag_eq b (algebraMap R K r) i hC]
  have heNle : eN ≤ N := by
    rw [heN, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    simp only []
    by_cases hj : j = i
    · subst hj
      simp only [Function.update_self]
      rw [SetLike.mem_coe, IsScalarTower.algebraMap_smul]
      exact N.smul_mem r (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Function.update_of_ne hj, Pi.one_apply, one_smul]
      exact Submodule.subset_span ⟨j, rfl⟩
  have hinfNeN : N ⊓ eN = eN := inf_eq_right.mpr heNle
  have hinfeNN : eN ⊓ N = eN := inf_eq_left.mpr heNle
  show (lenQuot N eN : ℤ) - (lenQuot eN N : ℤ) = (ordOnRing r : ℤ)
  have hq2 : lenQuot eN N = 0 := by
    unfold lenQuot
    rw [hinfeNN, Submodule.comap_subtype_self]
    simp
  have hq1 : lenQuot N eN = ordOnRing r := by
    unfold lenQuot ordOnRing
    rw [hinfNeN, hN, heN, core_length b i r]
  rw [hq1, hq2]
  simp

/-- `ord_R(1) = 0`. -/
theorem ordR_one (hdim : ringKrullDim R = 1) : ordR (R := R) (1 : Kˣ) = 0 :=
  ordR_one_aux hdim

omit [FiniteDimensional K V] in
/-- **Single-coordinate dilation base case.** For any nonzero `a ∈ K`,
`d(N, e_{diag(update 1 i a)}(N)) = ord_R(det e)`. -/
theorem dist_map_single (hdim : ringKrullDim R = 1)
    (b : Module.Basis (Fin (Module.finrank K V)) K V) (i : Fin (Module.finrank K V))
    (a : K) (ha : a ≠ 0)
    (hC : IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a)).det) :
    latticeDist (Submodule.span R (Set.range b))
        (mapLattice (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin
            (Module.finrank K V) → K) i a)) hC) (Submodule.span R (Set.range b)))
      = ordR (R := R) (LinearEquiv.det (Matrix.toLinearEquiv b
          (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a)) hC)) := by
  have hNlat : IsLattice (K := K) (Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)))
      := stdLattice_isLattice b
  set s := IsLocalization.sec (nonZeroDivisors R) a with hs
  have hspec : a * (algebraMap R K) (s.snd : R) = (algebraMap R K) s.fst :=
    IsLocalization.sec_spec (nonZeroDivisors R) a
  have hs2ne : (s.snd : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s.snd
  have hs1ne : s.fst ≠ 0 := sec_fst_ne_zero ha
  have hxne : (algebraMap R K s.fst) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff (K := K)]; exact hs1ne
  have hyne : (algebraMap R K (s.snd:R)) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff (K := K)]; exact hs2ne
  have hCyU : IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i
      (algebraMap R K (s.snd:R)))).det := isUnit_det_diag_single hyne i
  have hCxU : IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i
      (algebraMap R K s.fst))).det := isUnit_det_diag_single hxne i
  have hmatprod : (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a))
      * (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap R K
          (s.snd:R))))
      = Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i
          (algebraMap R K s.fst)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext j
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact hspec
    · simp [Function.update_of_ne hj]
  have hCaCyU : IsUnit ((Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i a))
      * (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i
          (algebraMap R K (s.snd:R))))).det := by
    rw [hmatprod]; exact hCxU
  have hcomp := dist_map_comp hdim
    (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i
        (algebraMap R K (s.snd:R)))) hCyU)
    (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i
        a)) hC)
    (Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V))) hNlat
  rw [← toLinearEquiv_trans b (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K)
      i a))
      (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i (algebraMap R K
          (s.snd:R)))) hC hCyU hCaCyU] at hcomp
  rw [toLinearEquiv_congr b hmatprod hCaCyU hCxU] at hcomp
  rw [latticeDist_integral' b i s.fst hCxU, latticeDist_integral' b i (s.snd:R) hCyU] at hcomp
  have hLHS : latticeDist (Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)))
        (mapLattice (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin
            (Module.finrank K V) → K) i a)) hC) (Submodule.span R (Set.range b)))
      = (ordOnRing (R := R) s.fst : ℤ) - (ordOnRing (R := R) (s.snd:R) : ℤ) := by linarith
  rw [hLHS]
  have hdetcoe :
      ((LinearEquiv.det (Matrix.toLinearEquiv b (Matrix.diagonal
          (Function.update (1 : Fin (Module.finrank K V) → K) i a)) hC)) : K) = a := by
    rw [toLinearEquiv_det_coe, det_diag_single]
  rw [ordR_def hdim
      (LinearEquiv.det (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin
          (Module.finrank K V) → K) i a)) hC))]
  rw [hdetcoe, ← hs]

omit [FiniteDimensional K V] in
/-- **Diagonal/dilation base case (Stacks 02MI step 4).** For a diagonal matrix
`diagonal D` with unit determinant, the associated equivalence `e_D` scales each
basis vector `b j` by `D j`, so `e_D(N) = ⊕_j (D j · R) b j`.  The distance
`d(N, e_D(N))` telescopes (over the `Fin n` coordinates) to `∑_j ord_R(D j)`,
and `ord_R(det e_D) = ord_R(∏_j D j) = ∑_j ord_R(D j)` by multiplicativity of
`ord_R` (`ordR_mul`) and `det (diagonal D) = ∏ D`.  For the single-coordinate
dilation `D = update 1 i a`, this is exactly `d(N, aR ⊕ Rⁿ⁻¹) = ord_R(a)`.

STRATEGY: reduce a general diagonal to a product of single-coordinate dilations
(diagonal `D = ∏_j diagonal (update 1 j (D j))`), or argue directly with a
coordinate decomposition `N ≅ ⊕_j R` and `e_D(N) ≅ ⊕_j (D j) R`, then
`latticeDist` is the sum of one-dimensional contributions `ord_R(D j)`
(`Module.length` additivity over the direct sum; each summand is
`length_R(R/(x_j)) - length_R(R/(y_j))` for `D j = x_j / y_j`, i.e.
`ord_R(D j)` by `ordR_apply_algebraMap`/`ordOnRing_mul_nonzero`).  RHS:
`det (diagonal D) = ∏_j D j` (`Matrix.det_diagonal`), `ord_R(∏) = ∑ ord_R`
(`ordR_mul` + `map_prod`), and `toLinearEquiv_det_coe`.
KEY NAMES: `Matrix.det_diagonal`, `Matrix.diagonal_mulVec` / action on basis,
`ordR_apply_algebraMap`, `ordR_mul`, `Finset.prod`, `Submodule.iSup`/`pi` lattice
decomposition.  This is the genuinely length-bearing computation. -/
theorem dist_map_eq_ord_det_diagonal (hdim : ringKrullDim R = 1)
    (b : Module.Basis (Fin (Module.finrank K V)) K V)
    (D : Fin (Module.finrank K V) → K) (hC : IsUnit (Matrix.diagonal D).det) :
    latticeDist (Submodule.span R (Set.range b))
        (mapLattice (Matrix.toLinearEquiv b (Matrix.diagonal D) hC)
          (Submodule.span R (Set.range b)))
      = ordR (R := R) (LinearEquiv.det (Matrix.toLinearEquiv b (Matrix.diagonal D) hC)) := by
  -- D=1 ⇒ 0, single dilation D=a ⇒ ord_R(a), det(diagonal D)=∏ D_j; no counterexample).
  -- PROOF: write `diagonal D = ∏_j diagonal (update 1 j (D j))`, telescope both sides over the
  -- coordinates via `dist_map_comp` (LHS) and `LinearEquiv.det_trans` + `ordR_mul` (RHS), and
  -- close each single-coordinate factor with `dist_map_single`.
  have hDne : ∀ j, D j ≠ 0 := by
    rw [Matrix.det_diagonal] at hC
    intro j hj
    exact hC.ne_zero (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  set N := Submodule.span R (Set.range (b : Fin (Module.finrank K V) → V)) with hN
  have hNlat : IsLattice (K := K) N := stdLattice_isLattice b
  have key : ∀ (s : Finset (Fin (Module.finrank K V)))
      (hCs : IsUnit (Matrix.diagonal (fun j => if j ∈ s then D j else 1)).det),
      latticeDist N (mapLattice
        (Matrix.toLinearEquiv b (Matrix.diagonal (fun j => if j ∈ s then D j else 1)) hCs) N)
        = ordR (R := R) (LinearEquiv.det (Matrix.toLinearEquiv b
            (Matrix.diagonal (fun j => if j ∈ s then D j else 1)) hCs)) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro hCs
        have hone :
            (Matrix.diagonal
              (fun j => if j ∈ (∅ : Finset (Fin (Module.finrank K V))) then D j else 1))
            = (1 : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) := by
          rw [show (fun j => if j ∈ (∅ : Finset (Fin (Module.finrank K V))) then D j else 1)
            = (1 : Fin (Module.finrank K V) → K) by funext j; simp]
          exact Matrix.diagonal_one
        rw [hN]
        rw [toLinearEquiv_congr b hone hCs (by simp : IsUnit (1 : Matrix (Fin (Module.finrank K V))
            (Fin (Module.finrank K V)) K).det)]
        have hrefl :
            Matrix.toLinearEquiv b
              (1 : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) (by simp)
              = LinearEquiv.refl K V := by
          apply LinearEquiv.toLinearMap_injective
          ext x
          simp only [LinearEquiv.coe_coe, Matrix.toLinearEquiv_apply, Matrix.toLin_one,
              LinearMap.id_coe, id_eq, LinearEquiv.refl_apply]
        rw [hrefl, mapLattice_refl, latticeDist_self]
        have hdet1 : LinearEquiv.det (LinearEquiv.refl K V) = 1 := by simp
        rw [hdet1, ordR_one hdim]
    | @insert i s hi ih =>
        intro hCs
        have hfact : Matrix.diagonal (fun j => if j ∈ insert i s then D j else 1)
            = Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K) i (D i))
              * Matrix.diagonal (fun j => if j ∈ s then D j else 1) := by
          rw [Matrix.diagonal_mul_diagonal]
          congr 1; funext j
          by_cases hj : j = i
          · subst hj; simp [hi]
          · simp [hj, Finset.mem_insert]
        have hCsingle : IsUnit (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K)
            i (D i))).det := isUnit_det_diag_single (hDne i) i
        have hCs' : IsUnit (Matrix.diagonal (fun j => if j ∈ s then D j else 1)).det := by
          rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
          intro j _
          by_cases hj : j ∈ s
          · simp only [hj, ite_true]; exact hDne j
          · simp only [hj, ite_false]; exact one_ne_zero
        have hCprod : IsUnit ((Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) → K)
            i (D i)))
            * (Matrix.diagonal (fun j => if j ∈ s then D j else 1))).det := by
          rw [← hfact]; exact hCs
        have hcomp := dist_map_comp hdim
          (Matrix.toLinearEquiv b (Matrix.diagonal (fun j => if j ∈ s then D j else 1)) hCs')
          (Matrix.toLinearEquiv b (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V) →
              K) i (D i))) hCsingle)
          N hNlat
        rw [← toLinearEquiv_trans b (Matrix.diagonal (Function.update (1 : Fin (Module.finrank K V)
            → K) i (D i)))
            (Matrix.diagonal (fun j => if j ∈ s then D j else 1)) hCsingle hCs' hCprod] at hcomp
        rw [toLinearEquiv_congr b hfact.symm hCprod hCs] at hcomp
        have htrans := toLinearEquiv_trans b (Matrix.diagonal (Function.update (1 : Fin
            (Module.finrank K V) → K) i (D i)))
            (Matrix.diagonal (fun j => if j ∈ s then D j else 1)) hCsingle hCs' hCprod
        rw [toLinearEquiv_congr b hfact.symm hCprod hCs] at htrans
        rw [hcomp, htrans, LinearEquiv.det_trans, ordR_mul,
          dist_map_single hdim b i (D i) (hDne i) hCsingle, ih hCs']
        ring
  have huniv :
      (fun j => if j ∈ (Finset.univ : Finset (Fin (Module.finrank K V))) then D j else 1) = D := by
    funext j; simp
  have hk := key Finset.univ (by rwa [huniv])
  rw [toLinearEquiv_congr b (congrArg Matrix.diagonal huniv) (by rwa [huniv]) hC] at hk
  rwa [hN]

/-- **The identity holds for the standard lattice and elementary generators
(Stacks 02MI steps 3–4).** With `V` identified with `Kⁿ` via a basis and `M`
taken to be the standard lattice `Rⁿ`, the equality `d(M, φ(M)) = ord_R(det φ)`
holds for every elementary generator `φ` of `GL(V)` (transvections and
dilations), and hence — `GL_n(K)` being generated by elementary matrices,
together with additivity of both sides (`dist_map_comp`, `ordR_mul`,
`LinearEquiv.det_trans`) — for every `φ`, at the standard lattice. -/
theorem dist_map_eq_ord_det_std (hdim : ringKrullDim R = 1) (φ : V ≃ₗ[K] V)
    (M : Submodule R V) (hM : IsLattice (K := K) M) :
    latticeDist M (mapLattice φ M) = ordR (R := R) (LinearEquiv.det φ) := by
  -- STRATEGY (Stacks 02MI steps 3–4): pick a `K`-basis `b` of `V` (exists, `FiniteDimensional`)
  -- and let `N = span R (range b)` be the standard `R`-lattice. By `dist_map_indep` it suffices
  -- to prove the identity for `M = N`. Identify `GL(V) ≅ GL_n(K)` via `b`. `GL_n(K)` is
  -- generated by elementary matrices (transvections and diagonal matrices); both sides are
  -- multiplicative/additive under composition (`dist_map_comp` on the LHS;
  -- `LinearEquiv.det_trans` + `ordR_mul` on the RHS). We run
  -- `Matrix.diagonal_transvection_induction` on the matrix `A = toMatrix b b φ`; the diagonal
  -- and transvection base cases are `dist_map_eq_ord_det_diagonal` /
  -- `dist_map_eq_ord_det_transvection`, and the product step is pure multiplicativity glue.
  -- choose a basis and the standard lattice N
  set n := Module.finrank K V with hn
  let b : Module.Basis (Fin n) K V := Module.finBasis K V
  set N : Submodule R V := Submodule.span R (Set.range b) with hN
  have hNlat : IsLattice (K := K) N := stdLattice_isLattice b
  -- Step 1: reduce to the standard lattice
  rw [dist_map_indep hdim φ M N hM hNlat]
  -- Step 2: write φ via its matrix; set A and reduce φ to `toLinearEquiv b A`
  set A : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix b b φ with hA
  have hAunit : IsUnit A.det := by
    rw [hA, LinearMap.det_toMatrix b]
    exact LinearEquiv.isUnit_det' φ
  have hφ : φ = Matrix.toLinearEquiv b A hAunit := by
    apply LinearEquiv.toLinearMap_injective
    ext x
    simp only [LinearEquiv.coe_coe, Matrix.toLinearEquiv_apply]
    rw [hA, Matrix.toLin_toMatrix b b]
    rfl
  rw [hφ]
  -- Step 3: matrix induction.  Predicate: the identity at N for the equiv of any unit matrix.
  set P : Matrix (Fin n) (Fin n) K → Prop := fun C =>
    ∀ (hC : IsUnit C.det),
      latticeDist N (mapLattice (Matrix.toLinearEquiv b C hC) N)
        = ordR (R := R) (LinearEquiv.det (Matrix.toLinearEquiv b C hC)) with hP
  have hind : P A := by
    refine Matrix.diagonal_transvection_induction P A ?_ ?_ ?_
    · -- diagonal base case
      exact fun D _ hC ↦ dist_map_eq_ord_det_diagonal hdim b D hC
    · -- transvection base case
      exact fun t hC ↦ dist_map_eq_ord_det_transvection hdim b t hC
    · -- product step: multiplicativity
      intro X Y hX hY hXY
      have hXu : IsUnit X.det := by
        rw [Matrix.det_mul] at hXY; exact isUnit_of_mul_isUnit_left hXY
      have hYu : IsUnit Y.det := by
        rw [Matrix.det_mul] at hXY; exact isUnit_of_mul_isUnit_right hXY
      rw [toLinearEquiv_trans b X Y hXu hYu hXY,
        dist_map_comp hdim (Matrix.toLinearEquiv b Y hYu) (Matrix.toLinearEquiv b X hXu) N hNlat,
        LinearEquiv.det_trans, ordR_mul, hX hXu, hY hYu]
      ring
  exact hind hAunit

/-- **Stacks 02MI.** Let `R` be a Noetherian local domain of dimension `1` with
fraction field `K`, let `V` be a finite dimensional `K`-vector space, and let
`φ : V → V` be a `K`-linear isomorphism. Then for any lattice `M ⊆ V`,
`d(M, φ(M)) = ord_R(det φ)`. -/
@[stacks 02MI]
alias dist_map_eq_ord_det := Stacks.OrderOfVanishing.dist_map_eq_ord_det_std

end Stacks.OrderOfVanishing

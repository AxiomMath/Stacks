module

public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Degreewise isomorphism for the graded base change to `lim_n A/Iⁿ`

Let `A` be a graded ring, let `I ⊆ A₊` be a homogeneous ideal, and write `A' = lim_n A/Iⁿ`.
Let `(Gₙ)` be an inverse system of graded `A`-modules with `Gₙ` annihilated by `Iⁿ`, let `M`
be a graded `A`-module, and let `φₙ : M → Gₙ` be a compatible system of graded `A`-module
maps.  If the induced map `φ : M ⊗_A A' → lim_n Gₙ` is an isomorphism, then
`φ^(d) : M_d → lim_n G_{n,d}` is an isomorphism for every `d ∈ ℤ`.  This is Stacks tag 0EKD,
following the conventions on graded rings of Stacks tag 00JL.

## Setup

* `A` is graded over `ℕ` (no nonzero elements in negative degrees) by
  `𝒜 : ℕ → AddSubmonoid A` with `[GradedRing 𝒜]`, which extends
  `DirectSum.Decomposition 𝒜` and so provides the internal decomposition
  `A = ⨁_{d ≥ 0} A_d`.
* `I` is a homogeneous ideal concentrated in strictly positive degrees.  This is encoded by
  the hypothesis that the degree-`0` component of every element of `I` vanishes, which for a
  homogeneous ideal is exactly the condition `I ∩ A₀ = 0`.
* `A' = lim_n A/Iⁿ` (`invLimRing`) is the inverse limit of the quotient rings taken in the
  category of rings, with projections `invLimProj : A' → A/Iⁿ` and canonical ring
  homomorphism `toInvLimRing : A → A'`, which makes `A'` an `A`-algebra.
* `M` is a graded `A`-module, graded over `ℤ` (nonzero components in any integer degree are
  allowed) by `ℳ : ℤ → AddSubgroup M` with an internal decomposition
  `[DirectSum.Decomposition ℳ]`.
* Each `Gₙ` is a genuine graded module: it carries an `ℤ`-grading
  `𝒢 n : ℤ → AddSubgroup (G n)` with an internal decomposition.  The annihilation condition
  `Iⁿ · Gₙ = 0` is encoded faithfully by giving each `Gₙ` an `A/Iⁿ`-module structure
  compatible with the `A`-action via `[IsScalarTower A (A/Iⁿ) (G n)]`, which forces `Iⁿ` to
  act as `0`.  The transition maps `Gₙ₊₁ → Gₙ` are `A`-linear, degree preserving, and
  semilinear over the ring transition `quotTrans : A/Iⁿ⁺¹ → A/Iⁿ`.  Then `lim_n Gₙ` carries
  the canonical `A'`-module structure `invLimModule`, in which `A'` acts coordinatewise via
  the projections `A' → A/Iⁿ`; it is *defined* from the per-stage `A/Iⁿ`-module structures,
  not bundled as extra data.

## Conventions

1. Graded *rings* are concentrated in degrees `≥ 0` (index `ℕ`), while graded *modules* may
   have nonzero components in any integer degree (index `ℤ`).  The mixed `ℕ`/`ℤ` graded
   action `A_i · M_e ⊆ M_{i + e}` is recorded as a hypothesis on the gradings.
2. All inverse limits `lim_n` are over the cofiltered system `n = 1, 2, 3, …` with `n+1 → n`
   transition maps.  Indexing by `n : ℕ` is harmless: `A/I⁰ = 0`, so the `n = 0` term is the
   zero module and does not affect any inverse limit.
3. `φ` is bundled as an `A'`-linear map together with the equation `φ(m ⊗ 1) = (φₙ m)ₙ`
   characterizing it on simple tensors; combined with `A'`-linearity this determines `φ`
   uniquely.
4. The statement reads `M ⊗_A A'`; we model it as `TensorProduct A A' M`, which since `A` is
   commutative is canonically the same `A'`-module.
-/

@[expose] public section

universe u

/-! ### The inverse limit of the quotient rings `A/Iⁿ` -/

/-- The transition ring homomorphism `A/I^(n+1) → A/Iⁿ`. -/
@[ega "0 19.5.6.2" "special case"]
noncomputable def quotTrans {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    (A ⧸ I ^ (n + 1)) →+* (A ⧸ I ^ n) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))

/-- The transition map `quotTrans I n` sends the class of `a` modulo `I^(n+1)` to its class
modulo `Iⁿ`. -/
@[simp] lemma quotTrans_mk {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) (a : A) :
    quotTrans I n (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (I ^ n) a :=
  Ideal.Quotient.factor_mk _ a

/-- `A' = lim_n A/Iⁿ`, the inverse limit of the quotient rings, realized as a
subring of the product `∏ n, A/Iⁿ`. -/
@[ega "IV 18.3.2.1"]
def invLimRing {A : Type u} [CommRing A] (I : Ideal A) : Subring (∀ n, A ⧸ I ^ n) where
  carrier := { a | ∀ n, quotTrans I n (a (n + 1)) = a n }
  zero_mem' := by intro n; simp
  one_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; simp [map_add, ha n, hb n]
  mul_mem' := by intro a b ha hb n; simp [map_mul, ha n, hb n]
  neg_mem' := by intro a ha n; simp [map_neg, ha n]

/-- The projection `A' → A/Iⁿ`. -/
def invLimProj {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    invLimRing I →+* (A ⧸ I ^ n) where
  toFun a := (a : ∀ n, A ⧸ I ^ n) n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The canonical ring homomorphism `A → A'`. -/
@[ega "0 7.2.1" "special case", ega "0 7.2.3", ega "IV 18.3.2.1"]
noncomputable def toInvLimRing {A : Type u} [CommRing A] (I : Ideal A) : A →+* invLimRing I :=
  (RingHom.pi (fun n => Ideal.Quotient.mk (I ^ n))).codRestrict (invLimRing I) (fun a n => by
    change quotTrans I n (Ideal.Quotient.mk (I ^ (n + 1)) a) = Ideal.Quotient.mk (I ^ n) a
    simp)

/-- `A'` is an `A`-algebra via the canonical map `A → A'`. -/
noncomputable instance algInvLim {A : Type u} [CommRing A] (I : Ideal A) :
    Algebra A (invLimRing I) := (toInvLimRing I).toAlgebra

/-! ### Inverse limits of abelian groups -/

/-- `lim_n Gₙ`, the inverse limit of an inverse system of abelian groups, as an
`AddSubgroup` of the product. -/
@[ega "0 13.1.1"]
def invLimAb (G : ℕ → Type u) [∀ n, AddCommGroup (G n)] (t : ∀ n, G (n + 1) →+ G n) :
    AddSubgroup (∀ n, G n) where
  carrier := { g | ∀ n, t n (g (n + 1)) = g n }
  zero_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; simp [map_add, ha n, hb n]
  neg_mem' := by intro a ha n; simp [map_neg, ha n]

/-- The canonical `A' = lim A/Iⁿ`-module structure on `lim_n G_n`, where each
`G n` is an `A/Iⁿ`-module and the transition maps `t n` are semilinear over
`quotTrans I n`.  `A'` acts coordinatewise via the projections `A' → A/Iⁿ`. -/
@[reducible,
  ega "IV 18.3.2.1"]
noncomputable def invLimModule {A : Type u} [CommRing A] (I : Ideal A)
    (G : ℕ → Type u) [∀ n, AddCommGroup (G n)] [∀ n, Module (A ⧸ I ^ n) (G n)]
    (t : ∀ n, G (n + 1) →+ G n)
    (ht : ∀ (n : ℕ) (c : A ⧸ I ^ (n + 1)) (x : G (n + 1)),
      t n (c • x) = quotTrans I n c • t n x) :
    Module (invLimRing I) (invLimAb G t) where
  smul a' g := ⟨fun n => invLimProj I n a' • (g : ∀ n, G n) n, by
    intro n
    change t n (invLimProj I (n + 1) a' • (g : ∀ n, G n) (n + 1)) =
      invLimProj I n a' • (g : ∀ n, G n) n
    rw [ht n, show quotTrans I n (invLimProj I (n + 1) a') = invLimProj I n a' from a'.property n,
      g.property n]⟩
  one_smul g := by
    apply Subtype.ext; funext n
    change invLimProj I n 1 • (g : ∀ n, G n) n = (g : ∀ n, G n) n
    rw [map_one, one_smul]
  mul_smul a b g := by
    apply Subtype.ext; funext n
    change invLimProj I n (a * b) • (g : ∀ n, G n) n
        = invLimProj I n a • invLimProj I n b • (g : ∀ n, G n) n
    rw [map_mul, mul_smul]
  smul_zero a := by apply Subtype.ext; funext n; exact smul_zero _
  smul_add a g h := by
    apply Subtype.ext; funext n; exact smul_add _ _ _
  add_smul a b g := by
    apply Subtype.ext; funext n
    change invLimProj I n (a + b) • (g : ∀ n, G n) n
        = invLimProj I n a • (g : ∀ n, G n) n + invLimProj I n b • (g : ∀ n, G n) n
    rw [map_add, add_smul]
  zero_smul g := by
    apply Subtype.ext; funext n
    change invLimProj I n 0 • (g : ∀ n, G n) n = 0
    rw [map_zero, zero_smul]

/-- `lim_n G_{n,d}`, the inverse limit of the degree-`d` parts `G_{n,d} = 𝒢 n d`
of an inverse system of graded abelian groups, as an `AddSubgroup` of
`∀ n, 𝒢 n d`.  The transition `t` is assumed (via `tgraded` in the data) to
preserve the degree-`d` parts; here we record the inverse-limit condition using
the inclusions `𝒢 n d ↪ G n`. -/
def invLimGradedPart (G : ℕ → Type u) [∀ n, AddCommGroup (G n)]
    (𝒢 : ∀ n, ℤ → AddSubgroup (G n)) (t : ∀ n, G (n + 1) →+ G n) (d : ℤ) :
    AddSubgroup (∀ n, 𝒢 n d) where
  carrier := { g | ∀ n, t n (g (n + 1) : G (n + 1)) = (g n : G n) }
  zero_mem' := by intro n; simp
  add_mem' := by intro a b ha hb n; simp [map_add, ha n, hb n]
  neg_mem' := by intro a ha n; simp [map_neg, ha n]

/-! ### Bundled data for the lemma -/

/-- The data of the lemma, bundled together.

* `A` is a graded ring graded over `ℕ`, with `[GradedRing 𝒜]` (which provides the
  internal direct-sum decomposition `A = ⨁_{d ≥ 0} A_d`).
* `I` is a homogeneous ideal with `hI` saying its degree-`0` component vanishes,
  i.e. `I ⊆ A₊`.
* `M` is a graded `A`-module graded over `ℤ` with `[DirectSum.Decomposition ℳ]`.
* Each `G n` is a genuine graded `A`-module: it is an `A/Iⁿ`-module
  (`moduleQuotG`), compatible with the `A`-action (`towerG`, which encodes
  `Iⁿ Gₙ = 0`), with `ℤ`-grading `𝒢 n` and `[DirectSum.Decomposition (𝒢 n)]`
  (`decomposeG`).  The transition maps `tG` are `A`-linear, degree preserving
  (`tG_graded`), and `quotTrans`-semilinear (`tG_semilinear`).  This makes
  `lim_n Gₙ` an `A'`-module via the canonical `invLimModule`.
* `φₙ` is a compatible system of degree-preserving `A`-linear maps `M → Gₙ`.
* `φ` is the canonical induced `A'`-linear map, bundled with the equation
  characterizing it on simple tensors `1 ⊗ m`. -/
structure GradedCompletionData where
  /-- Carrier of the graded ring `A`. -/
  A : Type u
  [commRingA : CommRing A]
  /-- The grading of `A` by `ℕ` (degrees `≥ 0`). -/
  𝒜 : ℕ → AddSubmonoid A
  /-- `[GradedRing 𝒜]` provides the direct-sum decomposition `A = ⨁_{d ≥ 0} A_d`. -/
  [gradedRingA : GradedRing 𝒜]
  /-- The homogeneous ideal `I`. -/
  I : HomogeneousIdeal 𝒜
  /-- `I ⊆ A₊`: the degree-`0` component of every element of `I` vanishes,
  equivalently `I ∩ A₀ = 0`. -/
  hI : ∀ a ∈ I.toIdeal, (DirectSum.decompose 𝒜 a 0 : A) = 0
  /-- Carrier of the graded `A`-module `M`. -/
  M : Type u
  [addCommM : AddCommGroup M]
  [moduleM : Module A M]
  /-- The grading of `M` by `ℤ`. -/
  ℳ : ℤ → AddSubgroup M
  /-- The graded action: `A_i · M_e ⊆ M_{i + e}`. -/
  hℳ_smul : ∀ (i : ℕ) (e : ℤ) (a : A) (m : M), a ∈ 𝒜 i → m ∈ ℳ e → a • m ∈ ℳ (i + e)
  /-- `M` is the (internal) direct sum of its graded parts. -/
  [decomposeM : DirectSum.Decomposition ℳ]
  /-- The inverse system of graded `A`-modules `(Gₙ)`. -/
  G : ℕ → Type u
  [addCommG : ∀ n, AddCommGroup (G n)]
  [moduleG : ∀ n, Module A (G n)]
  /-- Each `Gₙ` is a module over `A/Iⁿ`. -/
  [moduleQuotG : ∀ n, Module (A ⧸ I.toIdeal ^ n) (G n)]
  /-- The `A/Iⁿ`-action on `Gₙ` is compatible with the `A`-action; this encodes
  `Iⁿ · Gₙ = 0` faithfully (the `A`-action factors through `A/Iⁿ`). -/
  [towerG : ∀ n, IsScalarTower A (A ⧸ I.toIdeal ^ n) (G n)]
  /-- The grading of each `Gₙ` by `ℤ`. -/
  𝒢 : ∀ n, ℤ → AddSubgroup (G n)
  /-- Each `Gₙ` is the (internal) direct sum of its graded parts: a genuine
  graded module. -/
  [decomposeG : ∀ n, DirectSum.Decomposition (𝒢 n)]
  /-- The graded action on each `Gₙ`: `A_i · G_{n,e} ⊆ G_{n, i + e}`. -/
  h𝒢_smul : ∀ (n : ℕ) (i : ℕ) (e : ℤ) (a : A) (g : G n),
    a ∈ 𝒜 i → g ∈ 𝒢 n e → a • g ∈ 𝒢 n (i + e)
  /-- The `A`-linear transition maps `Gₙ₊₁ → Gₙ`. -/
  tG : ∀ n, G (n + 1) →ₗ[A] G n
  /-- The transition maps preserve the degree-`d` parts. -/
  tG_graded : ∀ (n : ℕ) (d : ℤ) (g : G (n + 1)), g ∈ 𝒢 (n + 1) d → tG n g ∈ 𝒢 n d
  /-- The transition maps are semilinear over the ring transition `quotTrans`. -/
  tG_semilinear : ∀ (n : ℕ) (c : A ⧸ I.toIdeal ^ (n + 1)) (x : G (n + 1)),
    tG n (c • x) = quotTrans I.toIdeal n c • tG n x
  /-- The compatible system of degree-preserving `A`-linear maps `φₙ : M → Gₙ`. -/
  φn : ∀ n, M →ₗ[A] G n
  /-- Each `φₙ` is degree preserving. -/
  φn_graded : ∀ (n : ℕ) (d : ℤ) (m : M), m ∈ ℳ d → φn n m ∈ 𝒢 n d
  /-- Compatibility: `(Gₙ₊₁ → Gₙ) ∘ φₙ₊₁ = φₙ`. -/
  φn_compat : ∀ (n : ℕ) (m : M), tG n (φn (n + 1) m) = φn n m
  /-- The induced `A'`-linear map `φ : M ⊗_A A' → lim_n Gₙ`, where `lim_n Gₙ`
  carries the *canonical* `A'`-module structure `invLimModule`.  We model the
  base change `M ⊗_A A'` as `A' ⊗_A M` (canonically the same `A'`-module). -/
  φ : letI := invLimModule I.toIdeal G (fun n => (tG n).toAddMonoidHom) tG_semilinear
      TensorProduct A (invLimRing I.toIdeal) M →ₗ[invLimRing I.toIdeal]
        invLimAb G (fun n => (tG n).toAddMonoidHom)
  /-- `φ` is characterized on simple tensors `1 ⊗ m` (corresponding to `m ⊗ 1`)
  by the system `(φₙ)`: the `n`-th component of `φ (1 ⊗ m)` is `φₙ m`. -/
  φ_spec : ∀ (m : M) (n : ℕ),
    (φ (TensorProduct.tmul A (1 : invLimRing I.toIdeal) m) : ∀ n, G n) n = φn n m

attribute [instance] GradedCompletionData.commRingA GradedCompletionData.gradedRingA
  GradedCompletionData.addCommM GradedCompletionData.moduleM GradedCompletionData.decomposeM
  GradedCompletionData.addCommG GradedCompletionData.moduleG
  GradedCompletionData.moduleQuotG GradedCompletionData.towerG GradedCompletionData.decomposeG

namespace GradedCompletionData

variable (D : GradedCompletionData)

/-- `A' = lim_n A/Iⁿ` for the bundled data. -/
abbrev A' := invLimRing D.I.toIdeal

/-- `lim_n Gₙ`, the inverse limit module. -/
abbrev limG := invLimAb D.G (fun n => (D.tG n).toAddMonoidHom)

/-- The canonical `A'`-module structure on `lim_n Gₙ`. -/
noncomputable instance moduleLimG : Module D.A' D.limG :=
  invLimModule D.I.toIdeal D.G (fun n => (D.tG n).toAddMonoidHom) D.tG_semilinear

/-- `lim_n G_{n,d}`, the inverse limit of the degree-`d` parts. -/
abbrev limGd (d : ℤ) := invLimGradedPart D.G D.𝒢 (fun n => (D.tG n).toAddMonoidHom) d

/-- The induced map `φ^(d) : M_d → lim_n G_{n,d}` on degree-`d` parts. -/
def phiD (d : ℤ) : D.ℳ d →+ D.limGd d where
  toFun m :=
    ⟨fun n => ⟨D.φn n (m : D.M), D.φn_graded n d (m : D.M) m.property⟩, by
      intro n
      change (D.tG n).toAddMonoidHom (D.φn (n + 1) (m : D.M)) = D.φn n (m : D.M)
      simpa using D.φn_compat n (m : D.M)⟩
  map_zero' := by
    apply Subtype.ext; funext n; apply Subtype.ext; simp
  map_add' x y := by
    apply Subtype.ext; funext n; apply Subtype.ext; simp

/-- The inclusion of the degree-`d` inverse limit `lim_n G_{n,d}` into the full
inverse limit `lim_n G_n`, forgetting the grading information.  This realizes the
first inclusion of the Stacks chain
`⊕_d lim_n G_{n,d} ⊆ lim_n G_n ⊆ ∏_d lim_n G_{n,d}`. -/
def limGdIncl (D : GradedCompletionData) (d : ℤ) : D.limGd d →+ D.limG where
  toFun g := ⟨fun n => ((g : ∀ n, D.𝒢 n d) n : D.G n), g.property⟩
  map_zero' := by apply Subtype.ext; funext n; simp
  map_add' x y := by apply Subtype.ext; funext n; simp

/-- The `n`-th component of `limGdIncl d g` is the `n`-th component of `g`, viewed in `G n`. -/
@[simp] lemma limGdIncl_apply (D : GradedCompletionData) (d : ℤ)
    (g : D.limGd d) (n : ℕ) :
    ((D.limGdIncl d g : ∀ n, D.G n) n) = ((g : ∀ n, D.𝒢 n d) n : D.G n) := rfl

/-- The inclusion is injective. -/
lemma limGdIncl_injective (D : GradedCompletionData) (d : ℤ) :
    Function.Injective (D.limGdIncl d) := by
  intro x y h
  apply Subtype.ext; funext n; apply Subtype.ext
  have : ((D.limGdIncl d x : ∀ n, D.G n) n) = ((D.limGdIncl d y : ∀ n, D.G n) n) := by
    rw [h]
  simpa using this

/-- The key compatibility: the inclusion of `φ^(d) m` into `lim_n G_n` agrees with
`φ (1 ⊗ m)`.  In words, `phiD d` is exactly the degree-`d` restriction of `φ` post-composed
with the injective inclusion `limGdIncl`. -/
lemma limGdIncl_phiD (D : GradedCompletionData) (d : ℤ) (m : D.ℳ d) :
    D.limGdIncl d (D.phiD d m)
      = D.φ (TensorProduct.tmul D.A (1 : D.A') (m : D.M)) := by
  apply Subtype.ext; funext n
  change ((D.phiD d m : ∀ n, D.𝒢 n d) n : D.G n)
      = (D.φ (TensorProduct.tmul D.A (1 : D.A') (m : D.M)) : ∀ n, D.G n) n
  rw [D.φ_spec (m : D.M) n]
  rfl

/-! ### Reduction of the lemma to injectivity and surjectivity in degree `d`

Following the Stacks proof of tag 0EKD, with `φ` an isomorphism the bijectivity of `φ^(d)`
reduces, through `limGdIncl`, `limGdIncl_injective` and `limGdIncl_phiD`, to two facts about
the base change in a single degree: `baseChange_degree_injective` and
`baseChange_degree_surjective`.

Both halves rest on the elementary degree-stabilization fact: since `I ⊆ A₊`, we have
`Iⁿ ⊆ ⊕_{e ≥ n} A_e`, so the quotient map `A → A/Iⁿ` is an isomorphism in degrees `≤ n − 1`;
consequently `A = ⊕_{e ≥ 0} A_e ⊆ A' ⊆ ∏_{e ≥ 0} A_e`, and every `a' ∈ A'` has well-defined
homogeneous components `a'_e ∈ A_e`. -/

/-- A power of `I` vanishes in low degrees: since `I ⊆ A₊` (every element of `I` has zero
degree-`0` component), we have `Iⁿ ⊆ ⊕_{e ≥ n} A_e`; equivalently, the degree-`e` homogeneous
component of any element of `Iⁿ` vanishes whenever `e < n`.

This is the elementary graded-algebra degree-stabilization fact: `I` homogeneous and
concentrated in degrees `≥ 1` forces `Iⁿ` to be concentrated in degrees `≥ n`.  The proof is
by induction on `n`, using that `I` is homogeneous, that the degree-`0` part of an element of
`I` vanishes, and that `A_i · A_j ⊆ A_{i+j}`. -/
lemma Ipow_lowdeg_zero (D : GradedCompletionData) (n : ℕ) (a : D.A)
    (ha : a ∈ (D.I.toIdeal) ^ n) (e : ℕ) (he : e < n) :
    (DirectSum.decompose D.𝒜 a e : D.A) = 0 := by
  classical
  -- Generalize over `a` and `e`, induct on `n`.
  induction n generalizing a e with
  | zero => exact absurd he (Nat.not_lt_zero e)
  | succ n ih =>
    -- `a ∈ I^(n+1) = I^n * I`.
    rw [pow_succ] at ha
    -- Induct over the product ideal `I^n * I`, reducing to single products `b * c`.
    refine Submodule.mul_induction_on'
      (C := fun x _ => ∀ e, e < n + 1 → (DirectSum.decompose D.𝒜 x e : D.A) = 0)
      ?_ ?_ ha e he
    · -- Single product `b * c`, `b ∈ I^n`, `c ∈ I`.
      intro b hb c hc e he
      -- Decompose `c` as the sum of its homogeneous components.
      rw [← DirectSum.sum_support_decompose D.𝒜 c, Finset.mul_sum, DirectSum.decompose_sum,
        DFinsupp.finsetSum_apply, AddSubmonoid.coe_finsetSum]
      refine Finset.sum_eq_zero fun j hj => ?_
      -- `c_j := decompose c j ∈ 𝒜 j`.
      have hcj_mem : (DirectSum.decompose D.𝒜 c j : D.A) ∈ D.𝒜 j :=
        (DirectSum.decompose D.𝒜 c j).property
      -- degree-`e` component of `b * c_j`.
      rw [DirectSum.coe_decompose_mul_of_right_mem D.𝒜 e hcj_mem]
      split_ifs with hje
      · -- `j ≤ e`.  Show `j ≥ 1`, so `e - j < n`, hence `decompose b (e-j) = 0` by IH.
        have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr <| by
          -- `j = 0`: then `c_0 = 0` since `c ∈ I` and `D.hI`.
          rintro rfl
          exact DFinsupp.mem_support_iff.mp hj (Subtype.ext (D.hI c hc))
        rw [ih b hb (e - j) (by omega), zero_mul]
      · rfl
    · -- Additive closure.
      intro x _ y _ hx hy e he
      rw [DirectSum.decompose_add, DFinsupp.add_apply, AddSubmonoid.coe_add, hx e he, hy e he,
        add_zero]

/-- Reduction of `1 ⊗ z = 0` to infinite divisibility `z ∈ Iⁿ M'`: given `z ∈ M` with
`1 ⊗ z = 0` in `A' ⊗_A M`, there is a *finitely generated* `A`-submodule `M' ⊆ M` with
`z ∈ M'` and `z ∈ Iⁿ • M'` for every `n ≥ 1`.

A tensor relation over `A` is already witnessed in a finitely generated submodule, giving a
finitely generated `M' ∋ z` with `1 ⊗ z = 0` in `A' ⊗_A M'`.  Projecting along the ring map
`A' → A/Iⁿ` and using `TensorProduct.quotTensorEquivQuotSMul`, which identifies
`(A/Iⁿ) ⊗_A M'` with `M'/(Iⁿ M')`, the image of `1 ⊗ z` is the class of `z`; its vanishing
means `z ∈ Iⁿ • (⊤ : Submodule A M')`. -/
lemma exists_fg_mem_Ipow_smul (D : GradedCompletionData) (z : D.M)
    (h0 : TensorProduct.tmul D.A (1 : D.A') z
        = (0 : TensorProduct D.A D.A' D.M)) :
    ∃ (M' : Submodule D.A D.M), M'.FG ∧ z ∈ M' ∧
      ∀ n : ℕ, 1 ≤ n → z ∈ ((D.I.toIdeal) ^ n) • M' := by
  classical
  -- `z ⊗ 1 = 0` in `M ⊗_A A'` (commute the given `1 ⊗ z = 0`).
  have hzcomm : TensorProduct.tmul D.A z (1 : D.A') = (0 : TensorProduct D.A D.M D.A') := by
    simpa [TensorProduct.comm_tmul] using congrArg (TensorProduct.comm D.A D.A' D.M) h0
  -- Start with `N₀ = span {z}`, finitely generated.
  set N₀ : Submodule D.A D.M := Submodule.span D.A {z} with hN₀
  have hzN₀ : z ∈ N₀ := Submodule.mem_span_singleton_self z
  have hN₀fg : N₀.FG := Submodule.fg_span_singleton z
  -- The element `x = ⟨z⟩ ⊗ 1 : N₀ ⊗ A'`.
  set x : TensorProduct D.A N₀ D.A' := TensorProduct.tmul D.A ⟨z, hzN₀⟩ (1 : D.A') with hx
  -- Its image in `M ⊗ A'` is `z ⊗ 1 = 0`.
  have himg : N₀.subtype.rTensor D.A' x = N₀.subtype.rTensor D.A' 0 := by
    rw [hx, map_zero]
    rw [LinearMap.rTensor_tmul]
    simp [hzcomm]
  -- Witness in a bigger f.g. submodule.
  obtain ⟨N', hN'fg, h, hzero⟩ := hN₀fg.exists_rTensor_fg_inclusion_eq himg
  -- `z ∈ N'`.
  have hzN' : z ∈ N' := h hzN₀
  -- In `N' ⊗ A'`, the tensor `⟨z⟩ ⊗ 1 = 0`.
  have hzero' : TensorProduct.tmul D.A (⟨z, hzN'⟩ : N') (1 : D.A') = 0 := by
    have : (LinearMap.rTensor (D.A') (Submodule.inclusion h)) x = 0 := by
      rw [hzero, map_zero]
    rw [hx, LinearMap.rTensor_tmul] at this
    exact this
  -- Hence `1 ⊗ ⟨z⟩ = 0` in `A' ⊗ N'`.
  have hzero'' : TensorProduct.tmul D.A (1 : D.A') (⟨z, hzN'⟩ : N') = 0 := by
    have := congrArg (TensorProduct.comm D.A N' D.A') hzero'
    rw [TensorProduct.comm_tmul, map_zero] at this
    -- `this : 1 ⊗ ⟨z⟩ = 0`
    exact this
  refine ⟨N', hN'fg, hzN', ?_⟩
  intro n hn
  -- The A-linear projection `A' →ₗ[A] A/Iⁿ`.
  set In : Ideal D.A := (D.I.toIdeal) ^ n with hIn
  -- A-linear map from `A'` to `A/Iⁿ`.
  set projLin : D.A' →ₗ[D.A] (D.A ⧸ In) :=
    { toFun := fun a' => invLimProj D.I.toIdeal n a'
      map_add' := by intro a b; simp [map_add]
      map_smul' := by
        intro c a'
        change invLimProj D.I.toIdeal n (c • a') = c • invLimProj D.I.toIdeal n a'
        have hsm : (c • a' : D.A') = (toInvLimRing D.I.toIdeal c) * a' := rfl
        rw [hsm, map_mul]
        have hcoord : invLimProj D.I.toIdeal n (toInvLimRing D.I.toIdeal c)
            = Ideal.Quotient.mk In c := rfl
        rw [hcoord]
        change Ideal.Quotient.mk In c * _ = c • _
        rw [Algebra.smul_def]
        rfl } with hprojLin
  -- Push `1 ⊗ ⟨z⟩ = 0` along `projLin ⊗ id` to `(A/Iⁿ) ⊗ N'`.
  have hpush : TensorProduct.tmul D.A (Ideal.Quotient.mk In 1) (⟨z, hzN'⟩ : N') = 0 := by
    have hcalc := congrArg (LinearMap.rTensor (N' : Submodule D.A D.M) projLin) hzero''
    rw [map_zero, LinearMap.rTensor_tmul] at hcalc
    have hp1 : projLin 1 = Ideal.Quotient.mk In 1 := by
      change invLimProj D.I.toIdeal n 1 = Ideal.Quotient.mk In 1
      rw [map_one, map_one]
    rw [hp1] at hcalc
    exact hcalc
  -- Apply `quotTensorEquivQuotSMul` to deduce `⟨z⟩ ∈ Iⁿ • ⊤` in `N'`.
  have hmk : Submodule.Quotient.mk (⟨z, hzN'⟩ : N') = (0 : N' ⧸ (In • (⊤ : Submodule D.A N'))) := by
    have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul (N' : Submodule D.A D.M) In) hpush
    rw [map_zero] at hq
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul] at hq
    simpa using hq
  -- So `⟨z⟩ ∈ Iⁿ • ⊤`.
  have hmem_top : (⟨z, hzN'⟩ : N') ∈ In • (⊤ : Submodule D.A N') :=
    (Submodule.Quotient.mk_eq_zero _).mp hmk
  -- Transport to `z ∈ Iⁿ • N'` in `M`.
  have hfin : z ∈ In • N' :=
    (Submodule.mem_smul_top_iff In N' (⟨z, hzN'⟩ : N')).mp hmem_top
  simpa [hIn] using hfin

/-- Acting by a homogeneous element `a ∈ A_i` raises the lower degree bound by
`i`: if every homogeneous component of `m` in degree `< δ` vanishes, then every
component of `a • m` in degree `< i + δ` vanishes. -/
lemma homog_smul_lowdeg (D : GradedCompletionData) (i : ℕ) (a : D.A) (ha : a ∈ D.𝒜 i)
    (δ : ℤ) (m : D.M) (hm : ∀ e : ℤ, e < δ → (DirectSum.decompose D.ℳ m e : D.M) = 0)
    (f : ℤ) (hf : f < (i : ℤ) + δ) :
    (DirectSum.decompose D.ℳ (a • m) f : D.M) = 0 := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose D.ℳ m]
  rw [Finset.smul_sum, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubgroup.val_finsetSum]
  apply Finset.sum_eq_zero
  intro e he
  have hme_mem : (DirectSum.decompose D.ℳ m e : D.M) ∈ D.ℳ e :=
    (DirectSum.decompose D.ℳ m e).property
  have hedelta : δ ≤ e := by
    by_contra hlt
    push Not at hlt
    have := hm e hlt
    exact (DFinsupp.mem_support_iff.mp he) (by apply Subtype.ext; rw [this]; rfl)
  have hsmul_mem : a • (DirectSum.decompose D.ℳ m e : D.M) ∈ D.ℳ ((i : ℤ) + e) :=
    D.hℳ_smul i e a _ ha hme_mem
  have hne : ((i : ℤ) + e) ≠ f := by omega
  exact DirectSum.decompose_of_mem_ne D.ℳ hsmul_mem hne

/-- If the components of `a` below degree `k` vanish and those of `m` below degree `δ` vanish,
then the components of `a • m` below degree `k + δ` vanish. -/
private lemma decompose_smul_eq_zero_of_lowdeg (D : GradedCompletionData) (k : ℕ) (a : D.A)
    (ha : ∀ i < k, (DirectSum.decompose D.𝒜 a i : D.A) = 0) (δ : ℤ) (m : D.M)
    (hm : ∀ e : ℤ, e < δ → (DirectSum.decompose D.ℳ m e : D.M) = 0)
    (f : ℤ) (hf : f < (k : ℤ) + δ) :
    (DirectSum.decompose D.ℳ (a • m) f : D.M) = 0 := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose D.𝒜 a]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubgroup.val_finsetSum]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hki : k ≤ i := by
    by_contra hlt
    exact (DFinsupp.mem_support_iff.mp hi) (Subtype.ext (ha i (not_le.mp hlt)))
  exact D.homog_smul_lowdeg i _ (DirectSum.decompose D.𝒜 a i).property δ m hm f (by omega)

/-- Acting by an arbitrary `a : A` preserves a lower degree bound: if every
component of `m` in degree `< δ` vanishes, then every component of `a • m` in
degree `< δ` vanishes (since `A` is concentrated in degrees `≥ 0`). -/
@[ega "II 8.2.1" "partial", ega "II 8.2.8" "m = 0 clause"]
lemma smul_lowdeg (D : GradedCompletionData) (a : D.A) (δ : ℤ) (m : D.M)
    (hm : ∀ e : ℤ, e < δ → (DirectSum.decompose D.ℳ m e : D.M) = 0)
    (f : ℤ) (hf : f < δ) :
    (DirectSum.decompose D.ℳ (a • m) f : D.M) = 0 :=
  D.decompose_smul_eq_zero_of_lowdeg 0 a (fun _ hi => absurd hi (Nat.not_lt_zero _)) δ m hm f
    (by simpa using hf)

/-- A finitely generated submodule `M'` is bounded below in degree: there is a
`δ : ℤ` such that every component of every element of `M'` in degree `< δ`
vanishes. -/
@[ega "II 2.1.6" "(i)", sga "6 VI 1.5.1" "partial"]
lemma submodule_fg_lowdeg (D : GradedCompletionData) (M' : Submodule D.A D.M)
    (hfg : M'.FG) :
    ∃ δ : ℤ, ∀ m ∈ M', ∀ e : ℤ, e < δ → (DirectSum.decompose D.ℳ m e : D.M) = 0 := by
  classical
  obtain ⟨s, hs⟩ := hfg
  -- δ = min over the union of supports of generators (or 0 if empty).
  set T : Finset ℤ := s.biUnion (fun g => (DirectSum.decompose D.ℳ g).support) with hT
  refine ⟨if hT0 : T.Nonempty then T.min' hT0 else 0, ?_⟩
  -- The property P δ m = ∀ e < δ, comp = 0, closed under the span operations.
  set δ : ℤ := if hT0 : T.Nonempty then T.min' hT0 else 0 with hδ
  have hgen : ∀ g ∈ s, ∀ e : ℤ, e < δ → (DirectSum.decompose D.ℳ g e : D.M) = 0 := by
    intro g hg e he
    by_contra hne
    have hmem : e ∈ (DirectSum.decompose D.ℳ g).support := by
      rw [DFinsupp.mem_support_iff]
      intro hc
      exact hne (by rw [hc]; rfl)
    have heT : e ∈ T := by
      rw [hT]; rw [Finset.mem_biUnion]; exact ⟨g, hg, hmem⟩
    have hT0 : T.Nonempty := ⟨e, heT⟩
    have : δ ≤ e := by
      rw [hδ]; simp only [hT0, dite_eq_left]; exact Finset.min'_le T e heT
    omega
  intro m hm
  rw [← hs, Submodule.mem_span_finset] at hm
  obtain ⟨c, hc, rfl⟩ := hm
  -- m = ∑ g ∈ s, c g • g
  intro e he
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubgroup.val_finsetSum]
  exact Finset.sum_eq_zero fun g hg => D.smul_lowdeg (c g) δ g (hgen g hg) e he

/-- The submodule `Iⁿ • M'` is bounded below by `n + δ` in degree, when `M'` is
bounded below by `δ`. -/
lemma Ipow_smul_lowdeg (D : GradedCompletionData) (n : ℕ) (M' : Submodule D.A D.M)
    (δ : ℤ) (hδ : ∀ m ∈ M', ∀ e : ℤ, e < δ → (DirectSum.decompose D.ℳ m e : D.M) = 0)
    (w : D.M) (hw : w ∈ ((D.I.toIdeal) ^ n) • M')
    (f : ℤ) (hf : f < (n : ℤ) + δ) :
    (DirectSum.decompose D.ℳ w f : D.M) = 0 := by
  classical
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro a ha m hm
    exact D.decompose_smul_eq_zero_of_lowdeg n a (D.Ipow_lowdeg_zero n a ha) δ m (hδ m hm) f hf
  · intro x y hx hy
    rw [DirectSum.decompose_add, DFinsupp.add_apply, AddSubgroup.coe_add, hx, hy, add_zero]

/-- A homogeneous element of `⋂ₙ Iⁿ M'` vanishes, for `M'` finitely generated: if `M' ⊆ M` is
a *finitely generated* `A`-submodule, `z ∈ M_d` is homogeneous of degree `d`, and `z ∈ Iⁿ M'`
for every `n ≥ 1`, then `z = 0`.

The finitely many generators of `M'` have homogeneous components in degrees `≥ δ` for some
`δ`.  Since `Iⁿ ⊆ ⊕_{f ≥ n} A_f` and the action is graded, `Iⁿ M' ⊆ ⊕_{e ≥ n + δ} M_e`.
Choosing `n` with `n + δ > d`, membership `z ∈ Iⁿ M'` forces the degree-`d` component of `z`
to vanish; by homogeneity that component is `z` itself. -/
lemma Ipow_smul_fg_lowdeg_zero (D : GradedCompletionData) (d : ℤ) (z : D.M)
    (hz : z ∈ D.ℳ d) (M' : Submodule D.A D.M) (hM'fg : M'.FG)
    (hdiv : ∀ n : ℕ, 1 ≤ n → z ∈ ((D.I.toIdeal) ^ n) • M') :
    z = 0 := by
  classical
  -- A lower degree bound `δ` for `M'`.
  obtain ⟨δ, hδ⟩ := D.submodule_fg_lowdeg M' hM'fg
  -- Choose `n : ℕ` with `1 ≤ n` and `(n : ℤ) + δ > d`.
  set n : ℕ := max 1 ((d - δ + 1).toNat) with hn
  have hn1 : 1 ≤ n := le_max_left _ _
  have hnδ : d < (n : ℤ) + δ := by
    have h2 : ((d - δ + 1).toNat : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast le_max_right 1 ((d - δ + 1).toNat)
    have h3 : d - δ + 1 ≤ ((d - δ + 1).toNat : ℤ) := Int.self_le_toNat _
    omega
  -- z lies in Iⁿ • M'.
  have hzmem : z ∈ ((D.I.toIdeal) ^ n) • M' := hdiv n hn1
  -- So its degree-d component vanishes.
  have hcomp : (DirectSum.decompose D.ℳ z d : D.M) = 0 :=
    D.Ipow_smul_lowdeg n M' δ hδ z hzmem d hnδ
  -- But z is homogeneous of degree d, so its degree-d component is z.
  have hself : (DirectSum.decompose D.ℳ z d : D.M) = z :=
    DirectSum.decompose_of_mem_same D.ℳ hz
  rw [hself] at hcomp
  exact hcomp

/-- Degree-`d` faithfulness of the base change: if `x, y ∈ M_d` have `1 ⊗ x = 1 ⊗ y` in
`A' ⊗_A M`, then `x = y`.

Replacing `x` by `x − y`, it suffices to show that `1 ⊗ z = 0` for `z ∈ M_d` forces `z = 0`.
A tensor relation over `A` is witnessed in a finitely generated submodule, so there is a
finitely generated `M' ⊆ M` with `z ∈ M'` and `1 ⊗ z = 0` already in `A' ⊗_A M'`.  Its
homogeneous generators have degrees `d₁, …, d_r`; set `n = d − min_i dᵢ + 1`.  Because
`A → A/Iⁿ` is an isomorphism in degrees `≤ n − 1` (the `I ⊆ A₊` stabilization fact) and `A'`
maps to `A/Iⁿ`, the map `M' → M' ⊗_A A'` is injective in degrees `≤ n − 1`; as `z` has degree
`d ≤ n − 1`, we get `z = 0`. -/
lemma baseChange_degree_injective (D : GradedCompletionData) (d : ℤ)
    (x y : D.ℳ d)
    (h : TensorProduct.tmul D.A (1 : D.A') (x : D.M)
        = TensorProduct.tmul D.A (1 : D.A') (y : D.M)) :
    x = y := by
  -- Reduce to `z := x - y ∈ M_d` with `1 ⊗ z = 0 ⟹ z = 0`.
  rw [Subtype.ext_iff, ← sub_eq_zero]
  set z : D.M := (x : D.M) - (y : D.M) with hzdef
  have hz : z ∈ D.ℳ d := by
    simpa [hzdef] using (D.ℳ d).sub_mem x.property y.property
  -- `1 ⊗ z = 0` in `A' ⊗_A M` (which is `D.limG`'s domain `TensorProduct A A' M`).
  have h0 : TensorProduct.tmul D.A (1 : D.A') z = 0 := by
    rw [hzdef, TensorProduct.tmul_sub, h, sub_self]
  -- Suffices to show `z = 0`.
  suffices hzero : z = 0 by simpa [hzdef] using hzero
  -- Obtain the finitely generated submodule `M'` with `z ∈ Iⁿ M'` for all `n`.
  -- (`exists_fg_mem_Ipow_smul`.)
  obtain ⟨M', hM'fg, hzM', hdiv⟩ := D.exists_fg_mem_Ipow_smul z h0
  -- Degree estimate: with homogeneous generators of `M'` of degrees `≥ δ`,
  -- `Iⁿ M' ⊆ ⊕_{e ≥ n + δ} M'_e` (uses `Ipow_lowdeg_zero` and the graded action
  -- `hℳ_smul`).  Picking `n` with `n + δ > d` and using `deg z = d` gives `z = 0`.
  exact D.Ipow_smul_fg_lowdeg_zero d z hz M' hM'fg hdiv

/-- Coordinatewise description of `φ` on a simple tensor:
for `a' ∈ A'` and `m ∈ M`, the `n`-th component of `φ (a' ⊗ m)` is
`(invLimProj n a') • φₙ(m)`, the `A/Iⁿ`-action on `Gₙ`.  This follows from
`A'`-linearity of `φ` (so `φ (a' ⊗ m) = a' • φ (1 ⊗ m)`) together with the
coordinatewise definition of the `A'`-action on `lim_n Gₙ` (`invLimModule`) and
the characterization `φ_spec` of `φ` on `1 ⊗ m`. -/
lemma phi_tmul_coord (D : GradedCompletionData) (a' : D.A') (m : D.M) (n : ℕ) :
    (D.φ (TensorProduct.tmul D.A a' m) : ∀ n, D.G n) n
      = invLimProj D.I.toIdeal n a' • D.φn n m := by
  -- `a' ⊗ m = a' • (1 ⊗ m)` in `A' ⊗_A M`.
  have htm : TensorProduct.tmul D.A a' m
      = a' • TensorProduct.tmul D.A (1 : D.A') m := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [htm, map_smul]
  -- The `n`-th component of `a' • y` (for `y : lim Gₙ`) is `invLimProj n a' • yₙ`.
  change invLimProj D.I.toIdeal n a' • (D.φ (TensorProduct.tmul D.A (1 : D.A') m) : ∀ n, D.G n) n
      = invLimProj D.I.toIdeal n a' • D.φn n m
  rw [D.φ_spec m n]

/-- Compatibility of the projections `invLimProj` with the quotient transition
maps: for `m ≤ k`, the factor map `A/Iᵏ → A/Iᵐ` sends the `k`-th projection of
`a'` to its `m`-th projection. -/
lemma invLimProj_factor {A : Type u} [CommRing A] (I : Ideal A) (m k : ℕ) (hmk : m ≤ k)
    (a' : invLimRing I) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmk) (invLimProj I k a')
      = invLimProj I m a' := by
  induction k with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmk
    rw [Ideal.Quotient.factor_eq]; rfl
  | succ k ih =>
    rcases eq_or_lt_of_le hmk with h | h
    · subst h
      rw [Ideal.Quotient.factor_eq]; rfl
    · have hmk' : m ≤ k := Nat.lt_succ_iff.mp h
      have hcomp : Ideal.Quotient.factor (Ideal.pow_le_pow_right hmk) (invLimProj I (k+1) a')
          = Ideal.Quotient.factor (Ideal.pow_le_pow_right hmk')
              (quotTrans I k (invLimProj I (k+1) a')) := by
        have : (invLimProj I (k+1) a')
            = Ideal.Quotient.mk (I ^ (k+1))
              (Classical.choose (Ideal.Quotient.mk_surjective (invLimProj I (k+1) a'))) := by
          rw [Classical.choose_spec (Ideal.Quotient.mk_surjective (invLimProj I (k+1) a'))]
        rw [this]
        rw [quotTrans_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
      rw [hcomp]
      have hstep : quotTrans I k (invLimProj I (k+1) a') = invLimProj I k a' := a'.property k
      rw [hstep, ih hmk']

/-- Degree-`d` homogeneous component (in `G n`) of `b • y`, where `b : A` and
`y ∈ G_{n,e}` is homogeneous: it picks out the degree-`(d-e)` component of `b`
acting on `y` (and is `0` when `d < e`, since `A` is concentrated in degrees
`≥ 0`). -/
lemma decompose_smul_homog (D : GradedCompletionData) (n : ℕ) (b : D.A)
    (e d : ℤ) (y : D.G n) (hy : y ∈ D.𝒢 n e) :
    (DirectSum.decompose (D.𝒢 n) (b • y) d : D.G n)
      = if _ : e ≤ d then (DirectSum.decompose D.𝒜 b (d - e).toNat : D.A) • y else 0 := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose D.𝒜 b]
  rw [Finset.sum_smul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply,
    AddSubgroup.val_finsetSum]
  -- each piece `bⱼ • y ∈ 𝒢 n (j + e)`; its degree-`d` component is `bⱼ • y` iff `j + e = d`.
  have hpiece : ∀ j : ℕ,
      (DirectSum.decompose (D.𝒢 n) ((DirectSum.decompose D.𝒜 b j : D.A) • y) d : D.G n)
        = if (j : ℤ) + e = d then (DirectSum.decompose D.𝒜 b j : D.A) • y else 0 := by
    intro j
    have hmem : (DirectSum.decompose D.𝒜 b j : D.A) • y ∈ D.𝒢 n ((j : ℤ) + e) :=
      D.h𝒢_smul n j e _ y (DirectSum.decompose D.𝒜 b j).property hy
    split_ifs with hje
    · rw [hje] at hmem
      exact DirectSum.decompose_of_mem_same (D.𝒢 n) hmem
    · exact DirectSum.decompose_of_mem_ne (D.𝒢 n) hmem hje
  rw [Finset.sum_congr rfl (fun j _ => hpiece j)]
  split_ifs with hed
  · -- `e ≤ d`: only `j = (d - e).toNat` contributes.
    by_cases hsupp : (d - e).toNat ∈ (DirectSum.decompose D.𝒜 b).support
    · rw [Finset.sum_eq_single (d - e).toNat]
      · rw [ite_eq_left]; omega
      · intro j _ hjne
        rw [ite_eq_right]
        intro hc; apply hjne; omega
      · intro hns; exact absurd hsupp hns
    · -- the relevant component is zero
      have hzero : (DirectSum.decompose D.𝒜 b (d - e).toNat : D.A) = 0 := by
        by_contra hne
        exact hsupp (DFinsupp.mem_support_iff.mpr (by
          intro hc; exact hne (by rw [hc]; rfl)))
      rw [hzero, zero_smul]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hjval : (j : ℤ) + e = d
      · rw [ite_eq_left hjval]
        have : j = (d - e).toNat := by omega
        rw [this, hzero, zero_smul]
      · rw [ite_eq_right hjval]
  · -- `d < e`: no `j ≥ 0` gives `j + e = d`.
    apply Finset.sum_eq_zero
    intro j _
    rw [ite_eq_right]
    have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
    omega

/-- The contribution of a single homogeneous element.  Given `a' ∈ A'` and
a homogeneous `x ∈ M_e`, there is a single `f ∈ A` (the degree-`(d-e)` homogeneous
component of `a'`, or `0` if `d < e`) with `f • x ∈ M_d` and such that for every
`n`, the degree-`d` homogeneous component (in `G_n`) of `(invLimProj n a') • φₙ x`
equals `φₙ (f • x)`. -/
lemma surj_homog_component (D : GradedCompletionData) (d : ℤ) (a' : D.A')
    (e : ℤ) (x : D.M) (hx : x ∈ D.ℳ e) :
    ∃ f : D.A, f • x ∈ D.ℳ d ∧
      ∀ n : ℕ, (DirectSum.decompose (D.𝒢 n)
          (invLimProj D.I.toIdeal n a' • D.φn n x) d : D.G n)
        = D.φn n (f • x) := by
  classical
  -- The `A/Iⁿ`-action on `G n` agrees with the `A`-action.
  have hmk_smul : ∀ (n : ℕ) (b : D.A) (y : D.G n),
      Ideal.Quotient.mk ((D.I.toIdeal) ^ n) b • y = b • y := fun n b y => by
    rw [← Ideal.Quotient.algebraMap_eq]
    exact IsScalarTower.algebraMap_smul (D.A ⧸ (D.I.toIdeal) ^ n) b y
  -- `Iⁿ G_n = 0`: if `b ∈ Iⁿ` then `b • y = 0` for any `y : G n`.
  have hann : ∀ (n : ℕ) (b : D.A), b ∈ (D.I.toIdeal) ^ n → ∀ y : D.G n, b • y = 0 := by
    intro n b hb y
    rw [← hmk_smul, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_smul]
  -- `φₙ x` is homogeneous of degree `e`.
  have hφx : ∀ n : ℕ, D.φn n x ∈ D.𝒢 n e := fun n => D.φn_graded n e x hx
  -- For each `n`, choose a lift `bₙ ∈ A` of `invLimProj n a'`.
  have hlift : ∀ n : ℕ, ∃ b : D.A, Ideal.Quotient.mk ((D.I.toIdeal) ^ n) b = invLimProj D.I.toIdeal
      n a' :=
    fun n => Ideal.Quotient.mk_surjective (invLimProj D.I.toIdeal n a')
  choose bb hbb using hlift
  -- The action of `invLimProj n a'` on `φₙ x` equals `bₙ • φₙ x`.
  have hact : ∀ n : ℕ, invLimProj D.I.toIdeal n a' • D.φn n x = bb n • D.φn n x := by
    intro n
    rw [← hbb n, hmk_smul]
  by_cases hed : e ≤ d
  · -- `e ≤ d`.  Build `f` from a lift at level `nδ = (d-e).toNat + 1`.
    set δ : ℤ := d - e with hδdef
    set nδ : ℕ := (d - e).toNat + 1 with hnδ
    have hδnn : 0 ≤ δ := by omega
    set f : D.A := (DirectSum.decompose D.𝒜 (bb nδ) (d - e).toNat : D.A) with hf
    have hfmem : f ∈ D.𝒜 (d - e).toNat :=
      (DirectSum.decompose D.𝒜 (bb nδ) (d - e).toNat).property
    have hfx : f • x ∈ D.ℳ d := by
      have := D.hℳ_smul (d - e).toNat e f x hfmem hx
      have heq : ((d - e).toNat : ℤ) + e = d := by omega
      rwa [heq] at this
    refine ⟨f, hfx, ?_⟩
    intro n
    rw [hact n]
    rw [D.decompose_smul_homog n (bb n) e d (D.φn n x) (hφx n)]
    rw [dite_eq_left hed]
    -- Goal: `(decompose 𝒜 (bb n) (d-e).toNat) • φₙ x = φₙ (f • x)`.
    rw [(D.φn n).map_smul]
    -- Suffices: `(decompose 𝒜 (bb n) (d-e).toNat) • φₙ x = f • φₙ x`.
    -- i.e. `(decompose 𝒜 (bb n) (d-e).toNat - f) • φₙ x = 0`, with the diff in `Iⁿ`.
    have hdiffmem : (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f
        ∈ (D.I.toIdeal) ^ n := by
      -- `bₙ - b_{nδ} ∈ I^{min n nδ}`.  Take the degree-`(d-e)` component.
      set k : ℕ := min n nδ with hk
      have hkn : k ≤ n := min_le_left _ _
      have hknδ : k ≤ nδ := min_le_right _ _
      -- `mk_k (bb n) = mk_k (bb nδ)` (both project to `invLimProj k a'`).
      have hmkk : Ideal.Quotient.mk ((D.I.toIdeal) ^ k) (bb n)
          = Ideal.Quotient.mk ((D.I.toIdeal) ^ k) (bb nδ) := by
        have hproj : ∀ j, k ≤ j →
            Ideal.Quotient.mk ((D.I.toIdeal) ^ k) (bb j) = invLimProj D.I.toIdeal k a' :=
          fun j hkj => by
            rw [← invLimProj_factor D.I.toIdeal k j hkj a', ← hbb j, Ideal.Quotient.factor_mk]
        rw [hproj n hkn, hproj nδ hknδ]
      have hbdiff : (bb n) - (bb nδ) ∈ (D.I.toIdeal) ^ k :=
        (Ideal.Quotient.eq).mp hmkk
      -- Its degree-`(d-e)` component is in `I^k` (homogeneous power ideal).
      have hpowhom : ∀ j : ℕ, ((D.I.toIdeal) ^ j).IsHomogeneous D.𝒜 := by
        intro j
        induction j with
        | zero => rw [pow_zero, Ideal.one_eq_top]; exact Ideal.IsHomogeneous.top _
        | succ j ih => rw [pow_succ]; exact ih.mul D.I.isHomogeneous
      have hcompmem : (DirectSum.decompose D.𝒜 ((bb n) - (bb nδ)) (d - e).toNat : D.A)
          ∈ (D.I.toIdeal) ^ k :=
        ((hpowhom k).mem_iff).mp hbdiff (d - e).toNat
      -- `decompose (bₙ - b_{nδ}) = decompose bₙ - decompose b_{nδ}`.
      have hsub : (DirectSum.decompose D.𝒜 ((bb n) - (bb nδ)) (d - e).toNat : D.A)
          = (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f := by
        have hadd : (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A)
            = (DirectSum.decompose D.𝒜 ((bb n) - (bb nδ)) (d - e).toNat : D.A)
              + (DirectSum.decompose D.𝒜 (bb nδ) (d - e).toNat : D.A) := by
          conv_lhs => rw [show bb n = ((bb n) - (bb nδ)) + (bb nδ) by ring]
          rw [DirectSum.decompose_add, DFinsupp.add_apply, AddSubmonoid.coe_add]
        rw [hf, hadd]; ring
      rw [hsub] at hcompmem
      -- Now decide whether `k = n` or `k = nδ`.
      rcases Nat.le_total n nδ with hcase | hcase
      · -- `k = n`, so done directly.
        have : k = n := by omega
        rwa [this] at hcompmem
      · -- `k = nδ ≤ n`; but the component lives in degree `(d-e) < nδ`, so it's `0`.
        have hknδ' : k = nδ := by omega
        rw [hknδ'] at hcompmem
        have hzero : (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f = 0 := by
          have hlow : ((d - e).toNat) < nδ := by omega
          -- the element is homogeneous of degree `(d-e).toNat`, equal to its own component
          have hwmem : (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f
              ∈ D.𝒜 (d - e).toNat := by
            rw [← hsub]
            exact (DirectSum.decompose D.𝒜 ((bb n) - (bb nδ)) (d - e).toNat).property
          have hself : (DirectSum.decompose D.𝒜
              ((DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f) (d - e).toNat : D.A)
              = (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f :=
            DirectSum.decompose_of_mem_same D.𝒜 hwmem
          have hcomp0 := D.Ipow_lowdeg_zero nδ _ hcompmem (d - e).toNat hlow
          rw [hself] at hcomp0
          exact hcomp0
        rw [hzero]
        exact Submodule.zero_mem _
    -- Conclude: difference acts as `0`.
    have : (DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) • D.φn n x
        = f • D.φn n x := by
      have h0 : ((DirectSum.decompose D.𝒜 (bb n) (d - e).toNat : D.A) - f) • D.φn n x = 0 :=
        hann n _ hdiffmem (D.φn n x)
      rw [sub_smul, sub_eq_zero] at h0
      exact h0
    rw [this]
  · -- `d < e`.  Take `f = 0`; everything vanishes.
    refine ⟨0, ?_, ?_⟩
    · rw [zero_smul]; exact (D.ℳ d).zero_mem
    · intro n
      rw [hact n]
      rw [D.decompose_smul_homog n (bb n) e d (D.φn n x) (hφx n)]
      rw [dite_eq_right hed, zero_smul, map_zero]

/-- For a single simple tensor `a' ⊗ x` (with `x` arbitrary), there is a genuine
degree-`d` element `m` whose image under each `φₙ` is the degree-`d` homogeneous
component of `(φ (a' ⊗ x))ₙ = (invLimProj n a') • φₙ x`.  Obtained by summing the
per-homogeneous-component contributions from `surj_homog_component`. -/
lemma surj_tmul (D : GradedCompletionData) (d : ℤ) (a' : D.A') (x : D.M) :
    ∃ m : D.ℳ d, ∀ n : ℕ,
      D.φn n (m : D.M)
        = (DirectSum.decompose (D.𝒢 n) (invLimProj D.I.toIdeal n a' • D.φn n x) d : D.G n) := by
  classical
  have H : ∀ e : ℤ, ∃ w : D.M, w ∈ D.ℳ d ∧ ∀ n : ℕ,
      (DirectSum.decompose (D.𝒢 n)
          (invLimProj D.I.toIdeal n a' • D.φn n (DirectSum.decompose D.ℳ x e : D.M)) d : D.G n)
        = D.φn n w := by
    intro e
    obtain ⟨f, hfmem, hf⟩ :=
      D.surj_homog_component d a' e (DirectSum.decompose D.ℳ x e : D.M)
        (DirectSum.decompose D.ℳ x e).property
    exact ⟨f • (DirectSum.decompose D.ℳ x e : D.M), hfmem, hf⟩
  choose w hwmem hw using H
  set s := (DirectSum.decompose D.ℳ x).support with hs
  have hxsum : x = ∑ e ∈ s, (DirectSum.decompose D.ℳ x e : D.M) := by
    rw [hs]; exact (DirectSum.sum_support_decompose D.ℳ x).symm
  refine ⟨⟨∑ e ∈ s, w e, AddSubgroup.sum_mem _ (fun e _ => hwmem e)⟩, ?_⟩
  intro n
  -- LHS
  change D.φn n (∑ e ∈ s, w e) = _
  rw [map_sum]
  -- RHS
  have hpx : D.φn n x = ∑ e ∈ s, D.φn n (DirectSum.decompose D.ℳ x e : D.M) := by
    conv_lhs => rw [hxsum]
    rw [map_sum]
  have hsmul : invLimProj D.I.toIdeal n a' • D.φn n x
      = ∑ e ∈ s, invLimProj D.I.toIdeal n a' • D.φn n (DirectSum.decompose D.ℳ x e : D.M) := by
    rw [hpx, Finset.smul_sum]
  rw [hsmul, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubgroup.val_finsetSum]
  exact (Finset.sum_congr rfl (fun e _ => (hw e n).symm))

/-- Coordinatewise surjectivity in degree `d`: given `g ∈ lim_n G_{n,d}` and surjectivity of
`φ`, there is a genuine degree-`d` element `m ∈ M_d` whose image under each `φₙ` is exactly
the `n`-th component `gₙ ∈ G_{n,d} ⊆ G_n` of `g`.

Lift `limGdIncl d g` along the surjection `φ` to a finite sum `∑ᵢ xᵢ ⊗ f'ᵢ`, each `xᵢ` taken
homogeneous of degree `dᵢ`.  Using `A ⊆ A' ⊆ ∏_{j≥0} A_j`, split each `f'ᵢ = Lᵢ + fᵢ + g'ᵢ`
with `Lᵢ` of degree `< d − dᵢ` (so `Lᵢ·xᵢ` has degree `< d`), `fᵢ ∈ A_{d−dᵢ}` (so
`fᵢ·xᵢ ∈ M_d`), and `g'ᵢ` whose homogeneous components in degrees `≤ d − dᵢ` vanish (so its
contribution has all degree-`≤ d` components zero).  With `m := ∑ᵢ fᵢ·xᵢ ∈ M_d`, the
degree-`d` component of `(limGdIncl d g)ₙ` is `gₙ` and the low and tail parts contribute `0`
in degree `d`, so `φₙ(m) = gₙ` for every `n`. -/
lemma baseChange_degree_surjective_coord (D : GradedCompletionData)
    (hφsurj : Function.Surjective D.φ) (d : ℤ) (g : D.limGd d) :
    ∃ m : D.ℳ d, ∀ n : ℕ,
      D.φn n (m : D.M) = ((g : ∀ n, D.𝒢 n d) n : D.G n) := by
  classical
  -- General claim by tensor induction: for any `t : A' ⊗ M`, there is a genuine
  -- degree-`d` element `m` with `φₙ m = (φ t)ₙ`'s degree-`d` component for all `n`.
  have Key : ∀ t : TensorProduct D.A D.A' D.M, ∃ m : D.ℳ d, ∀ n : ℕ,
      D.φn n (m : D.M)
        = (DirectSum.decompose (D.𝒢 n) ((D.φ t : ∀ n, D.G n) n) d : D.G n) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a' x =>
      obtain ⟨m, hm⟩ := D.surj_tmul d a' x
      refine ⟨m, ?_⟩
      intro n
      rw [hm n, D.phi_tmul_coord a' x n]
    | add t₁ t₂ ih₁ ih₂ =>
      obtain ⟨m₁, hm₁⟩ := ih₁
      obtain ⟨m₂, hm₂⟩ := ih₂
      refine ⟨m₁ + m₂, ?_⟩
      intro n
      have hcoe : ((m₁ + m₂ : D.ℳ d) : D.M) = (m₁ : D.M) + (m₂ : D.M) := rfl
      rw [hcoe, map_add, hm₁ n, hm₂ n]
      have hφadd : (D.φ (t₁ + t₂) : ∀ n, D.G n) n
          = (D.φ t₁ : ∀ n, D.G n) n + (D.φ t₂ : ∀ n, D.G n) n := by
        rw [map_add]; rfl
      rw [hφadd, DirectSum.decompose_add, DFinsupp.add_apply, AddSubgroup.coe_add]
  -- Lift `limGdIncl d g` via surjectivity of `φ`.
  obtain ⟨t, ht⟩ := hφsurj (D.limGdIncl d g)
  obtain ⟨m, hm⟩ := Key t
  refine ⟨m, ?_⟩
  intro n
  rw [hm n]
  -- `(φ t)ₙ = (limGdIncl d g)ₙ = ↑(gₙ)`, and its degree-`d` component is itself.
  have hval : (D.φ t : ∀ n, D.G n) n = ((g : ∀ n, D.𝒢 n d) n : D.G n) := by
    rw [ht]; rfl
  rw [hval]
  exact DirectSum.decompose_of_mem_same (D.𝒢 n) ((g : ∀ n, D.𝒢 n d) n).property

/-- Graded surjectivity of the base change, assembled from the coordinatewise form
`baseChange_degree_surjective_coord`: a genuine degree-`d`
`m` with `φₙ(m) = gₙ` for all `n` gives `φ (1 ⊗ m) = limGdIncl d g`, because
`(φ (1 ⊗ m))ₙ = φₙ(m)` (`phi_tmul_coord` with `a' = 1`) and
`(limGdIncl d g)ₙ = gₙ` (`limGdIncl_apply`). -/
lemma baseChange_degree_surjective (D : GradedCompletionData)
    (hφsurj : Function.Surjective D.φ) (d : ℤ) (g : D.limGd d) :
    ∃ m : D.ℳ d, D.φ (TensorProduct.tmul D.A (1 : D.A') (m : D.M))
        = D.limGdIncl d g := by
  obtain ⟨m, hm⟩ := D.baseChange_degree_surjective_coord hφsurj d g
  refine ⟨m, ?_⟩
  -- Compare the two elements of `lim_n G_n` coordinatewise.
  apply Subtype.ext
  funext n
  -- LHS coordinate: `(φ (1 ⊗ m))ₙ = (invLimProj n 1) • φₙ(m) = φₙ(m)`.
  have hlhs : (D.φ (TensorProduct.tmul D.A (1 : D.A') (m : D.M)) : ∀ n, D.G n) n
      = D.φn n (m : D.M) := by
    rw [D.phi_tmul_coord (1 : D.A') (m : D.M) n, map_one, one_smul]
  -- RHS coordinate: `(limGdIncl d g)ₙ = (gₙ : G n)`.
  rw [hlhs, hm]
  rfl

/-- Stacks tag 0EKD (Lemma 10.98.4): if the induced map `φ : M ⊗_A A' → lim_n Gₙ` is an
isomorphism, then for every `d ∈ ℤ` the induced map `φ^(d) : M_d → lim_n G_{n,d}` is an
isomorphism.

Bijectivity of `φ^(d)` splits into injectivity and surjectivity, each reduced through
`limGdIncl` to `baseChange_degree_injective` and `baseChange_degree_surjective`. -/
@[stacks 0EKD]
theorem main_theorem (D : GradedCompletionData)
    (hφ : Function.Bijective D.φ) (d : ℤ) :
    Function.Bijective (D.phiD d) := by
  obtain ⟨hφinj, hφsurj⟩ := hφ
  -- Injectivity of `φ` translates, via `limGdIncl_phiD`, into a statement about
  -- simple tensors: `φ^(d) x = φ^(d) y → 1 ⊗ x = 1 ⊗ y`.
  have htensor : ∀ x y : D.ℳ d,
      D.phiD d x = D.phiD d y →
      TensorProduct.tmul D.A (1 : D.A') (x : D.M)
        = TensorProduct.tmul D.A (1 : D.A') (y : D.M) := by
    intro x y hxy
    apply hφinj
    rw [← D.limGdIncl_phiD d x, ← D.limGdIncl_phiD d y, hxy]
  refine ⟨?_, ?_⟩
  · -- Injectivity of `φ^(d)`: reduce to `1 ⊗ x = 1 ⊗ y`, then apply (A).
    intro x y hxy
    exact D.baseChange_degree_injective d x y (htensor x y hxy)
  · -- Surjectivity of `φ^(d)`: lift `g` to a degree-`d` simple tensor via (B),
    -- then transport along the injective inclusion `limGdIncl`.
    intro g
    obtain ⟨m, hm⟩ := D.baseChange_degree_surjective hφsurj d g
    refine ⟨m, ?_⟩
    apply D.limGdIncl_injective d
    rw [D.limGdIncl_phiD d m, hm]

end GradedCompletionData

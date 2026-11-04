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
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

/-!
# A finite flat module that is not projective

Let `R = C^∞(ℝ)` be the ring of smooth functions `ℝ → ℝ` and let `I` be the ideal of those
`f ∈ R` which vanish identically on some open neighborhood `(-ε, ε)` of `0`. The quotient
`M = R / I` is a finite and flat `R`-module which is not projective, so "finite and flat implies
projective" fails over a general commutative ring. In contrast, over local rings finite
projectivity of a finite module descends along a flat local homomorphism.

## Main definitions

* `Stacks.FiniteFlatNotProjective.smoothSubring`: the ring `C^∞(ℝ)`, as a subring of `ℝ → ℝ`.
* `Stacks.FiniteFlatNotProjective.vanishNearZero`: the ideal `I`.
* `Stacks.FiniteFlatNotProjective.QuotientModule`: the module `M = R / I`.

## Main results

* `Stacks.FiniteFlatNotProjective.quotientModule_flat`: `M` is a flat `R`-module.
* `Stacks.FiniteFlatNotProjective.quotientModule_not_projective`: `M` is not a projective
  `R`-module.
* `finite_projective_iff_baseChange`: for a flat local homomorphism `R → S` of local rings and a
  finite `R`-module `M`, `M` is finite projective over `R` if and only if `S ⊗[R] M` is finite
  projective over `S`.
-/

@[expose] public section

open scoped Topology

namespace Stacks.FiniteFlatNotProjective

/-- The ring `R = C^∞(ℝ)` of smooth functions `ℝ → ℝ`, realized as a subring
of the ring `ℝ → ℝ` of all functions under pointwise operations. -/
def smoothSubring : Subring (ℝ → ℝ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  mul_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq] at *; exact ha.mul hb
  one_mem' := by simp only [Set.mem_ofPred_eq]; exact contDiff_const
  add_mem' := by intro a b ha hb; simp only [Set.mem_ofPred_eq] at *; exact ha.add hb
  zero_mem' := by simp only [Set.mem_ofPred_eq]; exact contDiff_const
  neg_mem' := by intro a ha; simp only [Set.mem_ofPred_eq] at *; exact ha.neg

/-- `R`, the ring of smooth functions, as a type. -/
abbrev SmoothFunReal := ↥smoothSubring

/-- The ideal `I` of smooth functions vanishing identically on some open
neighborhood `(-ε, ε)` of `0`. -/
def vanishNearZero : Ideal SmoothFunReal where
  carrier := {f | ∃ ε > 0, ∀ x : ℝ, |x| < ε → (f : ℝ → ℝ) x = 0}
  add_mem' := by
    rintro a b ⟨εa, hεa, ha⟩ ⟨εb, hεb, hb⟩
    refine ⟨min εa εb, lt_min hεa hεb, fun x hx ↦ ?_⟩
    change (a : ℝ → ℝ) x + (b : ℝ → ℝ) x = 0
    rw [ha x (hx.trans_le (min_le_left _ _)), hb x (hx.trans_le (min_le_right _ _)), add_zero]
  zero_mem' := ⟨1, one_pos, fun x _ ↦ rfl⟩
  smul_mem' := by
    rintro c a ⟨ε, hε, ha⟩
    refine ⟨ε, hε, fun x hx ↦ ?_⟩
    change (c : ℝ → ℝ) x * (a : ℝ → ℝ) x = 0
    rw [ha x hx, mul_zero]

/-- Evaluation at `0` as a ring homomorphism `R → ℝ`. -/
def evalZero : SmoothFunReal →+* ℝ :=
  (Pi.evalRingHom (fun _ : ℝ ↦ ℝ) 0).comp (Subring.subtype smoothSubring)

/-- The maximal ideal `m` of smooth functions vanishing at `0`, the kernel of evaluation
at `0`. -/
def vanishAtZero : Ideal SmoothFunReal := RingHom.ker evalZero

/-- The quotient module `M = R / I`. -/
abbrev QuotientModule := SmoothFunReal ⧸ vanishNearZero

/-! ### Basic API -/

/-- A function `ℝ → ℝ` lies in `smoothSubring` if and only if it is smooth. -/
@[simp]
theorem mem_smoothSubring {f : ℝ → ℝ} : f ∈ smoothSubring ↔ ContDiff ℝ (⊤ : ℕ∞) f := Iff.rfl

/-- `evalZero` sends a smooth function `f` to its value `f 0`. -/
@[simp]
theorem evalZero_apply (f : SmoothFunReal) : evalZero f = (f : ℝ → ℝ) 0 := rfl

/-- Membership characterization of `I`. -/
theorem mem_vanishNearZero {f : SmoothFunReal} :
    f ∈ vanishNearZero ↔ ∃ ε > 0, ∀ x : ℝ, |x| < ε → (f : ℝ → ℝ) x = 0 := Iff.rfl

/-- Membership characterization of `m`. -/
@[simp]
theorem mem_vanishAtZero {f : SmoothFunReal} :
    f ∈ vanishAtZero ↔ (f : ℝ → ℝ) 0 = 0 := Iff.rfl

/-- `m` is a maximal ideal. -/
theorem vanishAtZero_isMaximal : vanishAtZero.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective evalZero fun r ↦
    ⟨⟨fun _ ↦ r, (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ ↦ r)⟩, rfl⟩

/-- `I` is strictly contained in `m`. -/
theorem vanishNearZero_lt_vanishAtZero : vanishNearZero < vanishAtZero := by
  refine SetLike.lt_iff_le_and_exists.2 ⟨fun f ⟨ε, hε, hf⟩ ↦ hf 0 (by simpa using hε),
    ⟨fun x ↦ x, (contDiff_id : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ ↦ x)⟩, rfl, ?_⟩
  rintro ⟨ε, hε, hg⟩
  linarith [(hg (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith) : ε / 2 = 0)]

/-! ### Flatness -/

/-- `1 - b` is a smooth function vanishing near `0`, for any bump function `b` at `0`. -/
private theorem exists_mem_vanishNearZero_apply_eq_one_sub (b : ContDiffBump (0 : ℝ)) :
    ∃ g ∈ vanishNearZero, ∀ x, (g : ℝ → ℝ) x = 1 - b x :=
  ⟨⟨fun x ↦ 1 - b x, contDiff_const.sub b.contDiff⟩, ⟨b.rIn, b.rIn_pos, fun x hx ↦ by
    change 1 - b x = 0
    rw [b.one_of_mem_closedBall (by simpa [Real.dist_eq] using hx.le), sub_self]⟩, fun _ ↦ rfl⟩

/-- Every `f ∈ I` satisfies `f = f * g` for some `g ∈ I`. -/
theorem exists_mem_vanishNearZero_eq_mul {f : SmoothFunReal} (hf : f ∈ vanishNearZero) :
    ∃ g ∈ vanishNearZero, f = f * g := by
  obtain ⟨ε, hε, hf0⟩ := hf
  set b : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by linarith, by linarith⟩
  obtain ⟨g, hg, hgb⟩ := exists_mem_vanishNearZero_apply_eq_one_sub b
  refine ⟨g, hg, Subtype.ext (funext fun x ↦ ?_)⟩
  change (f : ℝ → ℝ) x = (f : ℝ → ℝ) x * (g : ℝ → ℝ) x
  rw [hgb]
  rcases lt_or_ge |x| ε with hlt | hge
  · rw [hf0 x hlt, zero_mul]
  · rw [b.zero_of_le_dist (by rwa [Real.dist_eq, sub_zero]), sub_zero, mul_one]

/-- `I` is a pure ideal. -/
theorem vanishNearZero_pure : vanishNearZero.Pure := by
  refine Ideal.Pure.of_inf_eq_mul _ fun J _ ↦ le_antisymm ?_ Ideal.mul_le_inf
  rintro x ⟨hxI, hxJ⟩
  obtain ⟨g, hgI, hfg⟩ := exists_mem_vanishNearZero_eq_mul hxI
  rw [hfg, mul_comm x g]
  exact Ideal.mul_mem_mul hgI hxJ

/-- `M = R/I` is a flat `R`-module. -/
theorem quotientModule_flat : Module.Flat SmoothFunReal QuotientModule :=
  vanishNearZero_pure

/-! ### Non-projectivity -/

/-- The only idempotents of `C^∞(ℝ)` are `0` and `1`. -/
theorem SmoothFunReal.eq_zero_or_one_of_isIdempotentElem {e : SmoothFunReal}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  have hcont : Continuous (e : ℝ → ℝ) := (mem_smoothSubring.mp e.property).continuous
  have hpt (x : ℝ) : (e : ℝ → ℝ) x = 0 ∨ (e : ℝ → ℝ) x = 1 :=
    IsIdempotentElem.iff_eq_zero_or_one.mp (congrFun (congrArg Subtype.val he) x)
  have hA : {x | (e : ℝ → ℝ) x = 0} = {x | (e : ℝ → ℝ) x ≠ 1} := by
    ext x
    rcases hpt x with h | h <;> simp [h]
  rcases isClopen_iff.mp ⟨isClosed_eq hcont continuous_const,
    hA ▸ isOpen_ne_fun hcont continuous_const⟩ with h | h
  · refine .inr (Subtype.ext (funext fun x ↦ (hpt x).resolve_left fun hx ↦ ?_))
    exact (h ▸ hx : x ∈ (∅ : Set ℝ))
  · exact .inl (Subtype.ext (funext fun x ↦ (h ▸ Set.mem_univ x : x ∈ {x | (e : ℝ → ℝ) x = 0})))

/-- `I` is nonzero: some nonzero smooth function vanishes near `0`. -/
theorem vanishNearZero_ne_bot : vanishNearZero ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  set b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩ with hb
  obtain ⟨g, hg, hgb⟩ := exists_mem_vanishNearZero_apply_eq_one_sub b
  refine ⟨g, hg, fun hzero ↦ ?_⟩
  have hb3 : b 3 = 0 := b.zero_of_le_dist (by rw [Real.dist_eq]; norm_num [hb])
  simpa [hgb, hb3] using congrFun (congrArg Subtype.val hzero) 3

/-- `I` is a proper ideal. -/
theorem vanishNearZero_ne_top : vanishNearZero ≠ ⊤ := fun h ↦
  vanishAtZero_isMaximal.ne_top (top_le_iff.mp (h ▸ vanishNearZero_lt_vanishAtZero).le)

/-- `M = R/I` is not a projective `R`-module, although it is finite and flat. -/
@[stacks 00NY]
theorem quotientModule_not_projective : ¬ Module.Projective SmoothFunReal QuotientModule := by
  intro hproj
  have hidem : IsIdempotentElem vanishNearZero := Ideal.isIdempotentElem_of_pure vanishNearZero
  have hfp : Module.FinitePresentation SmoothFunReal QuotientModule :=
    Module.finitePresentation_of_projective SmoothFunReal QuotientModule
  have hfg : (vanishNearZero : Submodule SmoothFunReal SmoothFunReal).FG := by
    have h := Module.FinitePresentation.fg_ker (R := SmoothFunReal) (M := SmoothFunReal)
      (N := QuotientModule) (vanishNearZero.mkQ) (Submodule.mkQ_surjective _)
    rwa [Submodule.ker_mkQ] at h
  obtain ⟨e, he, hIe⟩ := (Ideal.isIdempotentElem_iff_of_fg vanishNearZero hfg).mp hidem
  rcases SmoothFunReal.eq_zero_or_one_of_isIdempotentElem he with he0 | he1
  · exact vanishNearZero_ne_bot (by simp [hIe, he0])
  · exact vanishNearZero_ne_top (by simp [hIe, he1])

end Stacks.FiniteFlatNotProjective

/-! ### Finite projectivity along a flat local homomorphism -/

@[expose] public section

open scoped TensorProduct

/-- Let `R → S` be a flat local homomorphism of local rings and let `M` be a finite `R`-module.
Then `M` is projective over `R` if and only if `S ⊗[R] M` is projective over `S`. -/
theorem projective_iff_baseChange {R : Type*} {S : Type*} {M : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)]
    [Module.Flat R S]
    [Module.Finite R M] :
    Module.Projective R M ↔ Module.Projective S (S ⊗[R] M) := by
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  refine ⟨fun _ ↦ .tensorProduct, fun _ ↦ ?_⟩
  have : Module.Flat R M := (Module.Flat.iff_flat_tensorProduct R M S).mp .of_projective
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  exact .of_free

/-- **Stacks 00O1 (Lemma 10.78.6).** Let `R → S` be a flat local homomorphism of
local rings, and let `M` be a finite `R`-module. Then `M` is finite projective
over `R` if and only if `M ⊗_R S` is finite projective over `S`. -/
@[stacks 00O1, sga "3 VIB 11.8.2" "special case"]
theorem finite_projective_iff_baseChange {R : Type*} {S : Type*} {M : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)]
    [Module.Flat R S]
    [Module.Finite R M] :
    (Module.Finite R M ∧ Module.Projective R M) ↔
      (Module.Finite S (S ⊗[R] M) ∧ Module.Projective S (S ⊗[R] M)) :=
  ⟨fun ⟨_, h⟩ ↦ ⟨inferInstance, projective_iff_baseChange.mp h⟩,
    fun ⟨_, h⟩ ↦ ⟨inferInstance, projective_iff_baseChange.mpr h⟩⟩

module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
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

/-!
# One-point compactification

Let `X` be a Hausdorff, locally quasi-compact space. There is a map `X → X*` identifying `X` as
an open subspace of a quasi-compact Hausdorff space `X*` whose complement `X* ∖ X` is a
singleton; the witness is Mathlib's `OnePoint X` together with the coercion
`(↑) : X → OnePoint X`. The canonical map `X → StoneCech X` is an open embedding as well.

## Main results

* `exists_onePointCompactification`: there is a quasi-compact Hausdorff `X*` and an open
  embedding `X → X*` whose range has singleton complement.
* `isOpenEmbedding_stoneCechUnit`: `stoneCechUnit : X → StoneCech X` is an open embedding.
* `exists_compactification_and_isOpenEmbedding_stoneCechUnit` (Stacks 090A): the conjunction of the
  two.
-/

@[expose] public section

universe u

open Set Topology Filter

variable {X : Type u} [TopologicalSpace X]

/-- `OnePoint X` is compact (quasi-compact in Stacks/Bourbaki terminology),
without any assumption on `X`. -/
instance : CompactSpace (OnePoint X) := inferInstance

/-- For Hausdorff weakly-locally-compact `X`, the space `OnePoint X` is
Hausdorff. -/
instance t2Space_onePoint [WeaklyLocallyCompactSpace X] [T2Space X] :
    T2Space (OnePoint X) := inferInstance

/-- **Stacks 090A, main statement.**  For a Hausdorff, locally quasi-compact
(i.e. `WeaklyLocallyCompactSpace`) space `X`, there exists a topological space
`X*`, equipped with `CompactSpace` and `T2Space` instances, a continuous map
`f : X → X*`, and a point `p : X*`, such that `f` is an open embedding and the
complement of the range of `f` is the singleton `{p}`. -/
theorem exists_onePointCompactification
    [WeaklyLocallyCompactSpace X] [T2Space X] :
    ∃ (Xstar : Type u) (_ : TopologicalSpace Xstar)
      (_ : CompactSpace Xstar) (_ : T2Space Xstar)
      (f : X → Xstar) (p : Xstar),
        IsOpenEmbedding f ∧ (range f)ᶜ = {p} :=
  ⟨OnePoint X, inferInstance, inferInstance, inferInstance,
    ((↑) : X → OnePoint X), OnePoint.infty,
    OnePoint.isOpenEmbedding_coe, OnePoint.compl_range_coe⟩

/-! ### The Stone-Čech corollary

For Hausdorff locally quasi-compact `X`, the canonical map
`stoneCechUnit : X → StoneCech X` is also an open embedding.  The proof
follows the Stacks argument: extend the continuous map `(↑) : X → OnePoint X`
along `stoneCechUnit` to obtain `φ : StoneCech X → OnePoint X`; then
`stoneCechUnit` has image `φ⁻¹(range (↑))`, which is open in `StoneCech X`.

The bulk of the work is showing the equality
`range stoneCechUnit = φ⁻¹(range (↑))`.  The inclusion `⊆` is immediate.  For
`⊇` we observe that `range stoneCechUnit`, viewed inside the open subspace
`U := φ⁻¹(range (↑))`, is both **closed** (it is the image of a continuous
section into a Hausdorff retract `X`) and **dense** (because `stoneCechUnit`
has dense range in `StoneCech X` and `U` is open). -/

section StoneCech

variable [WeaklyLocallyCompactSpace X] [T2Space X]

/-- `X` is `T3.5` (completely regular Hausdorff): transport `T35Space` from
`OnePoint X` (which is `T4`, hence `T35`) through the embedding
`(↑) : X → OnePoint X`. -/
instance t35Space_of_weaklyLocallyCompact : T35Space X :=
  (OnePoint.isOpenEmbedding_coe (X := X)).toIsEmbedding.t35Space

/-- The Stone-Čech extension of `(↑) : X → OnePoint X` to `StoneCech X`. -/
private noncomputable def phi : StoneCech X → OnePoint X :=
  stoneCechExtend OnePoint.continuous_coe

private lemma phi_continuous : Continuous (phi (X := X)) :=
  continuous_stoneCechExtend _

@[simp] private lemma phi_stoneCechUnit (x : X) :
    phi (stoneCechUnit x) = ((x : OnePoint X)) :=
  stoneCechExtend_stoneCechUnit OnePoint.continuous_coe x

/-- The candidate open set: the preimage under `phi` of the range of
`(↑) : X → OnePoint X`. -/
private def U : Set (StoneCech X) :=
  phi ⁻¹' (range ((↑) : X → OnePoint X))

private lemma isOpen_U : IsOpen (U (X := X)) :=
  OnePoint.isOpen_range_coe.preimage phi_continuous

private lemma stoneCechUnit_mem_U (x : X) : stoneCechUnit x ∈ U (X := X) :=
  ⟨x, (phi_stoneCechUnit x).symm⟩

/-- The homeomorphism `range (↑) ≃ₜ X` inverting the open embedding `(↑) : X → OnePoint X`. -/
private noncomputable def e : range ((↑) : X → OnePoint X) ≃ₜ X :=
  (OnePoint.isOpenEmbedding_coe (X := X)).toIsEmbedding.toHomeomorph.symm

/-- The retraction `r : U → X` sending `y ∈ U` to the unique `x : X` with `phi y = ↑x`. -/
private noncomputable def r : U (X := X) → X :=
  fun y => e ⟨phi y.1, y.2⟩

private lemma r_continuous : Continuous (r (X := X)) :=
  e.continuous.comp (continuous_induced_rng.2 (phi_continuous.comp continuous_subtype_val))

/-- The section `s : X → U` corresponding to `stoneCechUnit`. -/
private noncomputable def s : X → U (X := X) :=
  fun x => ⟨stoneCechUnit x, stoneCechUnit_mem_U x⟩

private lemma s_continuous : Continuous (s (X := X)) :=
  continuous_induced_rng.2 continuous_stoneCechUnit

private lemma r_s_eq (x : X) : r (s x) = x := by
  simp [r, s, e, phi_stoneCechUnit]

/-- `range s` is closed in `U`, as the image of a section of a continuous
retraction into the Hausdorff space `X`. -/
private lemma isClosed_range_s : IsClosed (range (s (X := X))) :=
  Function.LeftInverse.isClosed_range (f := r) (g := s) r_s_eq r_continuous s_continuous

/-- `range s` is dense in `U`.  We use that `range stoneCechUnit` is dense in
`StoneCech X` and that `U` is open. -/
private lemma denseRange_s : DenseRange (s (X := X)) := by
  rw [DenseRange, Dense]
  rintro ⟨y, hy⟩
  rw [mem_closure_iff]
  intro V hVopen hyV
  -- Lift `V` (open in `U`) to an open set `W` in `StoneCech X` with
  -- `V = Subtype.val ⁻¹' W` and `y ∈ W`.
  obtain ⟨W, hWopen, hVW⟩ := isOpen_induced_iff.mp hVopen
  have hyW : y ∈ W := by rw [← hVW] at hyV; exact hyV
  -- `range stoneCechUnit` is dense; pick a point of `range stoneCechUnit` in `W`.
  have hdense : Dense (range (stoneCechUnit : X → StoneCech X)) :=
    denseRange_stoneCechUnit
  obtain ⟨z, hzRange, hzW⟩ :=
    hdense.exists_mem_open hWopen ⟨y, hyW⟩
  obtain ⟨x, rfl⟩ := hzRange
  -- Build the witness in `range s` and `V`.
  refine ⟨s x, ?_, x, rfl⟩
  -- Membership in `V = Subtype.val ⁻¹' W`.
  rw [← hVW]; exact hzW

/-- The key set-level equality: `range stoneCechUnit = U`. -/
private lemma range_stoneCechUnit_eq_U :
    range (stoneCechUnit : X → StoneCech X) = U (X := X) := by
  apply Set.Subset.antisymm (range_subset_iff.2 stoneCechUnit_mem_U)
  -- For (⊇): `range s = univ` in `U` by closed + dense.
  intro y hy
  have hclose : closure (range (s (X := X))) = range s :=
    (isClosed_range_s).closure_eq
  have hdense : closure (range (s (X := X))) = univ :=
    (denseRange_s).closure_range
  have h_univ : range (s (X := X)) = univ := hclose.symm.trans hdense
  -- `⟨y, hy⟩ ∈ range s`, so `y = stoneCechUnit x` for some `x`.
  have hmem : (⟨y, hy⟩ : U) ∈ range (s (X := X)) := by
    rw [h_univ]; trivial
  obtain ⟨x, hx⟩ := hmem
  -- Extract the equality at the underlying type.
  refine ⟨x, ?_⟩
  have := congrArg (Subtype.val (α := StoneCech X) (p := fun z => z ∈ U)) hx
  -- LHS: `(s x).val = stoneCechUnit x`; RHS: `(⟨y, hy⟩).val = y`.
  simpa [s] using this

/-- **Stacks 090A, "in particular" clause.**  For a Hausdorff, locally
quasi-compact space `X`, the canonical map `stoneCechUnit : X → StoneCech X`
is an open embedding. -/
theorem isOpenEmbedding_stoneCechUnit :
    IsOpenEmbedding (stoneCechUnit : X → StoneCech X) where
  toIsEmbedding := (_root_.isEmbedding_stoneCechUnit (X := X))
  isOpen_range := by
    rw [range_stoneCechUnit_eq_U]; exact isOpen_U

end StoneCech

/-! ### Combined Stacks 090A statement -/

/-- **Stacks 090A.**  For a Hausdorff, locally quasi-compact space `X`:
  (1) there exists a compact Hausdorff space `X*` and an open embedding
      `f : X → X*` whose range has singleton complement, and
  (2) the canonical map `X → StoneCech X` is also an open embedding. -/
@[stacks 090A]
theorem exists_compactification_and_isOpenEmbedding_stoneCechUnit [WeaklyLocallyCompactSpace X]
  [T2Space X] :
    (∃ (Xstar : Type u) (_ : TopologicalSpace Xstar)
      (_ : CompactSpace Xstar) (_ : T2Space Xstar)
      (f : X → Xstar) (p : Xstar),
        IsOpenEmbedding f ∧ (range f)ᶜ = {p}) ∧
    IsOpenEmbedding (stoneCechUnit : X → StoneCech X) :=
  ⟨exists_onePointCompactification, isOpenEmbedding_stoneCechUnit⟩

end

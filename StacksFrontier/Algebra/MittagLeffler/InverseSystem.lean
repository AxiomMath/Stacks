module

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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Mittag-Leffler condition on inverse systems
-/

/-!
# The Mittag-Leffler condition for directed inverse systems

A directed inverse system of sets `(Aᵢ, φⱼᵢ)` over an index set `I` is
*Mittag-Leffler* if for each `i ∈ I` the family of images `φⱼᵢ(Aⱼ) ⊆ Aᵢ`, for
`j ≥ i`, stabilizes: there is a `j ≥ i` such that `φₖᵢ(Aₖ) = φⱼᵢ(Aⱼ)` for all
`k ≥ j`. A directed inverse system of modules over a ring `R` is Mittag-Leffler
when its underlying inverse system of sets is.

## Main definitions

* `MittagLeffler.IsMittagLefflerSet`: the condition for a system of sets.
* `MittagLeffler.IsMittagLefflerModule`: the condition for a system of
  `R`-modules.
-/

@[expose] public section

namespace MittagLeffler

/-- A directed inverse system of sets `(F_i, φ_{ji})` is *Mittag-Leffler*
if for every index `i`, there exists some `j ≥ i` such that for all
`k ≥ j`, the image of `F_k` in `F_i` (via the transition map) equals
the image of `F_j` in `F_i`. -/
@[stacks 0595,
  ega "0 13.1.2" "inverse systems of sets",
  ega "0 13.1.3",
  ega "III 4.1.7",
  sga "4½ Rapport 4.11"]
def IsMittagLefflerSet {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] {F : ι → Type*}
    (φ : ⦃i j : ι⦄ → i ≤ j → F j → F i) [InverseSystem φ] : Prop :=
  ∀ i : ι, ∃ j : ι, ∃ hij : i ≤ j,
    ∀ k : ι, ∀ hjk : j ≤ k,
      Set.range (φ (le_trans hij hjk)) = Set.range (φ hij)

/-- A directed inverse system of `R`-modules `(M_i, φ_{ji})` is
*Mittag-Leffler* if the underlying directed inverse system of sets is
Mittag-Leffler. -/
@[stacks 0595, ega "0 13.1.2" "modules over a ring", ega "III 4.1.7", sga "4½ Rapport 4.11"]
def IsMittagLefflerModule {R : Type*} [Ring R] {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (φ : ⦃i j : ι⦄ → i ≤ j → M j →ₗ[R] M i)
    [InverseSystem (fun _ _ h => (φ h : M _ → M _))] : Prop :=
  IsMittagLefflerSet (fun _ _ h => (φ h : M _ → M _))

/-- `IsMittagLefflerModule φ` holds iff the underlying inverse system of sets is Mittag-Leffler. -/
theorem isMittagLefflerModule_iff {R : Type*} [Ring R] {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (φ : ⦃i j : ι⦄ → i ≤ j → M j →ₗ[R] M i) [InverseSystem (fun _ _ h => (φ h : M _ → M _))] :
    IsMittagLefflerModule φ ↔ IsMittagLefflerSet (fun _ _ h => (φ h : M _ → M _)) :=
  Iff.rfl

end MittagLeffler

end

/-!
# Countable Mittag-Leffler systems have a nonempty limit

Let `(Aᵢ, φⱼᵢ)` be a directed inverse system of sets over a directed set `I`. If
`I` is countable, the system is Mittag-Leffler, and every `Aᵢ` is nonempty, then
the limit `lim Aᵢ` is nonempty: there is a compatible family `(aᵢ)ᵢ ∈ ∏ᵢ Aᵢ` with
`φⱼᵢ(aⱼ) = aᵢ` for all `i ≤ j`.

A directed set is a nonempty preordered set `(I, ≤)` in which any two elements
`i₁, i₂` admit a common upper bound; antisymmetry is not required. It is modelled
here by `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`, and countability —
the existence of a surjection `ℕ → I`, equivalently an enumeration of `I` — by
`[Countable I]`.

## Main definitions

* `DirInvSystem`: a directed inverse system of sets.
* `DirInvSystem.limit`: the set of compatible families of such a system.
* `DirInvSystem.IsMittagLeffler`: the Mittag-Leffler condition.
* `DirInvSystem.Stable`: the elements of `Aᵢ` lying in every image `φⱼᵢ(Aⱼ)`.

## Main results

* `DirInvSystem.nonempty_limit_of_isMittagLeffler`: the theorem above.

The proof passes to the *stable* subsets `A'ᵢ ⊆ Aᵢ`, on which every transition
map is surjective, then uses countability to extract a monotone cofinal chain
`c : ℕ → I` and builds a compatible stable family along it by recursion. The
statement for systems of modules follows, a Mittag-Leffler inverse system of
modules being one whose underlying system of sets is Mittag-Leffler.
-/

@[expose] public section

variable {I : Type*} [Preorder I]

/-- A directed inverse system of sets over a (pre)ordered set `I` consists of a set
`A i` for each `i`, together with a *transition map* `φ : A j → A i` for each
pair `i ≤ j` (note: from the larger index `j` to the smaller index `i`),
satisfying the functoriality conditions
`φ_{ii} = id` and `φ_{ki} = φ_{ji} ∘ φ_{kj}` whenever `i ≤ j ≤ k`. -/
@[ega "0 8.1.9" "special case"]
structure DirInvSystem (A : I → Type*) where
  /-- The transition map `A j → A i` associated to a relation `i ≤ j`. -/
  φ : ∀ ⦃i j : I⦄, i ≤ j → A j → A i
  /-- The transition map for `i ≤ i` is the identity. -/
  φ_self : ∀ (i : I) (x : A i), φ (le_refl i) x = x
  /-- Functoriality: `φ_{ki} = φ_{ji} ∘ φ_{kj}` whenever `i ≤ j ≤ k`. -/
  φ_comp : ∀ ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : A k),
    φ hij (φ hjk x) = φ (hij.trans hjk) x

/-- The limit of `(A_i, φ_{ji})` is the set of compatible families `(a_i)_{i ∈ I}`,
i.e. choices of `a_i ∈ A_i` for every `i` such that `φ_{ji}(a_j) = a_i` whenever
`i ≤ j`. -/
@[ega "0 8.1.9" "partial"]
def DirInvSystem.limit {A : I → Type*} (S : DirInvSystem A) : Set (∀ i, A i) :=
  {a | ∀ ⦃i j : I⦄ (h : i ≤ j), S.φ h (a j) = a i}

/-- The system `(A_i, φ_{ji})` is *Mittag-Leffler* if for each `i` the decreasingly
directed family of images `{φ_{ji}(A_j)}_{j ≥ i}` stabilizes: for each `i` there
exists `j ≥ i` such that `φ_{ki}(A_k) = φ_{ji}(A_j)` for all `k ≥ j`.
Here `Set.range (S.φ h)` is the image `φ_{ji}(A_j)`. -/
@[ega "0 13.1.2", ega "0 13.1.3", ega "III 4.1.7", sga "4½ Rapport 4.11"]
def DirInvSystem.IsMittagLeffler {A : I → Type*} (S : DirInvSystem A) : Prop :=
  ∀ i : I, ∃ j, ∃ h : i ≤ j, ∀ k, ∀ hk : j ≤ k,
    Set.range (S.φ (h.trans hk)) = Set.range (S.φ h)

/-- A countable nonempty directed preorder admits a monotone cofinal sequence. -/
theorem exists_monotone_cofinal_nat [Countable I] [Nonempty I] [IsDirected I (· ≤ ·)] :
    ∃ c : ℕ → I, Monotone c ∧ ∀ i, ∃ n, i ≤ c n := by
  obtain ⟨e, he⟩ := exists_surjective_nat I
  let c : ℕ → I := fun n =>
    Nat.rec (e 0) (fun n cn => (directed_of (· ≤ ·) cn (e (n + 1))).choose) n
  have hce : ∀ n, e n ≤ c n
    | 0 => le_rfl
    | m + 1 => (directed_of (· ≤ ·) (c m) (e (m + 1))).choose_spec.right
  refine ⟨c, monotone_nat_of_le_succ fun n =>
    (directed_of (· ≤ ·) (c n) (e (n + 1))).choose_spec.left, fun i => ?_⟩
  obtain ⟨n, rfl⟩ := he i
  exact ⟨n, hce n⟩

namespace DirInvSystem

variable {A : I → Type*} (S : DirInvSystem A)

/-- An element `x : A i` is *stable* if it lies in the image of every transition
map into `A i`, i.e. `x ∈ φ_{ji}(A j)` for all `j ≥ i`.  The set of stable
elements is the stable image `A'_i` of the Stacks proof. -/
@[ega "0 13.1.3"]
def Stable {i : I} (x : A i) : Prop :=
  ∀ ⦃j : I⦄ (h : i ≤ j), x ∈ Set.range (S.φ h)

/-- Images are decreasingly directed: if `i ≤ j ≤ k` then
`φ_{ki}(A k) ⊆ φ_{ji}(A j)`. -/
theorem range_mono {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) :
    Set.range (S.φ (hij.trans hjk)) ⊆ Set.range (S.φ hij) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨S.φ hjk x, S.φ_comp hij hjk x⟩

/-- If `j₁` stabilizes the index `i` (in the Mittag-Leffler sense), then the
stable elements of `A i` are exactly the image `φ_{j₁ i}(A j₁)`. -/
@[ega "0 13.1.2" "special case", ega "0 13.1.3" "partial"]
theorem stable_eq_range {i j₁ : I} (h : i ≤ j₁)
    (hstab : ∀ k, ∀ hk : j₁ ≤ k, Set.range (S.φ (h.trans hk)) = Set.range (S.φ h))
    [IsDirected I (· ≤ ·)] :
    {x : A i | S.Stable x} = Set.range (S.φ h) := by
  refine Set.ext fun x => ⟨fun hx => hx h, fun hx j hj => ?_⟩
  obtain ⟨k, hjk, hj₁k⟩ := directed_of (· ≤ ·) j j₁
  exact S.range_mono hj hjk (by rwa [hstab k hj₁k])

/-- From the Mittag-Leffler condition, choose for each `i` a stabilizing index
`stab i ≥ i`. -/
noncomputable def stab (hML : S.IsMittagLeffler) (i : I) : I :=
  (hML i).choose

/-- The chosen stabilizing index `stab i` lies above `i`. -/
theorem le_stab (hML : S.IsMittagLeffler) (i : I) : i ≤ S.stab hML i :=
  (hML i).choose_spec.choose

/-- Beyond `stab i` the images in `A i` no longer shrink: `φ_{ki}(A k)` equals
`φ_{stab i, i}(A (stab i))` for every `k ≥ stab i`. -/
theorem stab_spec (hML : S.IsMittagLeffler) (i : I) :
    ∀ k, ∀ hk : S.stab hML i ≤ k,
      Set.range (S.φ ((S.le_stab hML i).trans hk)) = Set.range (S.φ (S.le_stab hML i)) :=
  (hML i).choose_spec.choose_spec

/-- The stable set over `i` equals the image from its stabilizer. -/
@[ega "0 13.1.2" "special case", ega "0 13.1.3" "under (ML)"]
theorem stable_eq_range_stab (hML : S.IsMittagLeffler) (i : I) [IsDirected I (· ≤ ·)] :
    {x : A i | S.Stable x} = Set.range (S.φ (S.le_stab hML i)) :=
  S.stable_eq_range (S.le_stab hML i) (S.stab_spec hML i)

/-- The stable set over `i` is nonempty (given each `A i` nonempty). -/
theorem stable_nonempty (hML : S.IsMittagLeffler) (hne : ∀ i, Nonempty (A i))
    (i : I) [IsDirected I (· ≤ ·)] :
    ∃ x : A i, S.Stable x := by
  obtain ⟨z⟩ := hne (S.stab hML i)
  exact ⟨_, (S.stable_eq_range_stab hML i).ge ⟨z, rfl⟩⟩

/-- Transition maps preserve stability: if `x : A j` is stable and `i ≤ j`, then
`φ_{ji}(x)` is stable. -/
@[ega "0 13.1.3" "partial"]
theorem Stable.map {i j : I} (hij : i ≤ j) {x : A j} (hx : S.Stable x)
    [IsDirected I (· ≤ ·)] : S.Stable (S.φ hij x) := by
  intro m hm
  obtain ⟨n, hmn, hjn⟩ := directed_of (· ≤ ·) m j
  obtain ⟨w, rfl⟩ := hx hjn
  exact ⟨S.φ hmn w, by rw [S.φ_comp hm hmn, S.φ_comp hij hjn]⟩

/-- The stable transition map is surjective: for `i ≤ j` and stable `x : A i`,
there is a stable `y : A j` with `φ_{ji}(y) = x`. -/
@[ega "0 13.1.2" "special case", ega "0 13.1.3" "under (ML)", ega "0 13.4.2" "partial"]
theorem stable_surjective (hML : S.IsMittagLeffler) {i j : I} (hij : i ≤ j)
    {x : A i} (hx : S.Stable x) [IsDirected I (· ≤ ·)] :
    ∃ y : A j, S.Stable y ∧ S.φ hij y = x := by
  obtain ⟨z, rfl⟩ := hx (hij.trans (S.le_stab hML j))
  exact ⟨S.φ (S.le_stab hML j) z, (S.stable_eq_range_stab hML j).ge ⟨z, rfl⟩,
    S.φ_comp _ _ z⟩

/-- If `c : ℕ → I` is a monotone cofinal sequence and the system is Mittag-Leffler with
nonempty terms, then its limit is nonempty. -/
theorem nonempty_limit_of_monotone_cofinal (hML : S.IsMittagLeffler)
    (hne : ∀ i, Nonempty (A i)) [IsDirected I (· ≤ ·)] {c : ℕ → I} (hc : Monotone c)
    (hcof : ∀ i, ∃ n, i ≤ c n) : S.limit.Nonempty := by
  obtain ⟨b₀, hb₀⟩ := S.stable_nonempty hML hne (c 0)
  let g : (n : ℕ) → {x : A (c n) // S.Stable x} :=
    fun n => Nat.rec ⟨b₀, hb₀⟩
      (fun n gn => ⟨(S.stable_surjective hML (hc n.le_succ) gn.property).choose,
        (S.stable_surjective hML (hc n.le_succ) gn.property).choose_spec.left⟩) n
  have hglink : ∀ n, S.φ (hc n.le_succ) (g (n + 1)).val = (g n).val := fun n =>
    (S.stable_surjective hML (hc n.le_succ) (g n).property).choose_spec.right
  have hgchain : ∀ {m n : ℕ} (h : m ≤ n), S.φ (hc h) (g n).val = (g m).val := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => exact S.φ_self _ _
    | succ k hmk ih => rw [← ih, ← hglink k, S.φ_comp]
  have hwd : ∀ (i : I) (m n : ℕ) (hm : i ≤ c m) (hn : i ≤ c n),
      S.φ hm (g m).val = S.φ hn (g n).val := fun i m n hm hn => by
    rw [← hgchain (le_max_left m n), ← hgchain (le_max_right m n), S.φ_comp, S.φ_comp]
  refine ⟨fun i => S.φ (hcof i).choose_spec (g (hcof i).choose).val, fun i j hij => ?_⟩
  obtain ⟨n, hjn⟩ := hcof j
  beta_reduce
  rw [hwd i _ n (hcof i).choose_spec (hij.trans hjn), hwd j _ n (hcof j).choose_spec hjn,
    S.φ_comp hij hjn]

end DirInvSystem

/-- Let `(A_i, φ_{ji})` be a directed inverse system of sets over a directed set `I`.
If `I` is countable, the system is Mittag-Leffler, and each `A_i` is nonempty,
then the limit `lim A_i` is nonempty. -/
@[stacks 0597, sga "4 I App.Lemma3" "more general"]
theorem DirInvSystem.nonempty_limit_of_isMittagLeffler
    [Countable I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {A : I → Type*} (S : DirInvSystem A)
    (hML : S.IsMittagLeffler) (hne : ∀ i, Nonempty (A i)) :
    S.limit.Nonempty :=
  let ⟨_, hc, hcof⟩ := exists_monotone_cofinal_nat (I := I)
  S.nonempty_limit_of_monotone_cofinal hML hne hc hcof

end

/-!
# Exactness of inverse limits under the Mittag-Leffler condition

Let `I` be a countable directed set and let
`0 → (A i) →[f] (B i) →[g] (C i) → 0` be an exact sequence of directed inverse
systems of abelian groups over `I`. If the system `(A i)` is Mittag-Leffler, then
the induced sequence of inverse limits `0 → lim A → lim B → lim C → 0` is exact;
the essential content is that `lim g : lim B → lim C` is surjective.

Throughout, `I` is a directed set: a nonempty preorder in which any `i, j` admit a
`k` with `i ≤ k` and `j ≤ k`. A directed inverse system of abelian groups over `I`
is a family of abelian groups `(A i)` together with transition homomorphisms
`φ_{ji} : A j → A i` for each `i ≤ j`, satisfying `φ_{ii} = id` and
`φ_{ki} = φ_{ji} ∘ φ_{kj}` whenever `i ≤ j ≤ k`. The transition maps are modelled
as a family `φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)`, going from the larger index `j`
to the smaller index `i`, with the coherence conditions packaged by Mathlib's
`InverseSystem` class on the underlying functions.

## Main definitions

* `addInvLimit`: the inverse limit, as an additive subgroup of `∀ i, A i`.
* `IsInverseSystemMorphism`, `addInvLimit.map`: morphisms of systems and the
  induced map on limits.
* `IsMittagLefflerSystem`: the Mittag-Leffler condition on `(A, φ)`.
* `IsExactSeq`: a short exact sequence of inverse systems.

## Main results

* `invLimit_exact`: the three-part exactness statement.
* `invLimit_map_surjective`: surjectivity of `lim g`, the essential content.

Left-exactness is formal. Surjectivity is reduced to a purely set-theoretic
statement about set-valued inverse systems over a countable directed index: a
nonempty Mittag-Leffler system has a compatible section (`exists_section_of_ML`).
Mathlib's `CategoryTheory.Functor.IsMittagLeffler`, in
`Mathlib.CategoryTheory.CofilteredSystem`, is the related API for `Type`-valued
cofiltered systems.
-/

@[expose] public section
set_option linter.unusedVariables false

open Function

section Defs

variable {I : Type*} [Preorder I]

/-- The inverse limit of a directed inverse system `A` of abelian groups with transition maps
`φ`, realised as the additive subgroup of the product `∀ i, A i` consisting of the
compatible families `(a i)` (i.e. `φ_{ji}(a j) = a i` for all `i ≤ j`).  Group operations
are coordinatewise. -/
@[ega "0 13.1.1"]
def addInvLimit (A : I → Type*) [∀ i, AddCommGroup (A i)]
    (φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)) : AddSubgroup (∀ i, A i) where
  carrier := {a | ∀ ⦃i j : I⦄ (h : i ≤ j), φ h (a j) = a i}
  zero_mem' := by
    intro i j h
    simp
  add_mem' := by
    intro a b ha hb i j h
    simp [ha h, hb h]
  neg_mem' := by
    intro a ha i j h
    simp [ha h]

/-- The `i`-th projection homomorphism `π_i : lim A → A i`. -/
def addInvLimit.proj (A : I → Type*) [∀ i, AddCommGroup (A i)]
    (φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)) (i : I) :
    addInvLimit A φ →+ A i where
  toFun a := (a : ∀ i, A i) i
  map_zero' := rfl
  map_add' _ _ := rfl

variable (A : I → Type*) [∀ i, AddCommGroup (A i)]
  (φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i))
variable (B : I → Type*) [∀ i, AddCommGroup (B i)]
  (ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i))

/-- `IsInverseSystemMorphism φ ψ f` says that the family of homomorphisms `f i : A i → B i`
commutes with the transition maps: `f_i ∘ φ_{ji} = ψ_{ji} ∘ f_j` for all `i ≤ j`. -/
def IsInverseSystemMorphism (f : ⦃i : I⦄ → (A i →+ B i)) : Prop :=
  ∀ ⦃i j : I⦄ (h : i ≤ j), (f (i := i)).comp (φ h) = (ψ h).comp (f (i := j))

/-- A morphism `f` of inverse systems induces the homomorphism `lim f : lim A → lim B`,
`(a i) ↦ (f_i (a i))`. -/
@[ega "0 13.1.1"]
def addInvLimit.map (f : ⦃i : I⦄ → (A i →+ B i)) (hf : IsInverseSystemMorphism A φ B ψ f) :
    addInvLimit A φ →+ addInvLimit B ψ where
  toFun a := ⟨fun i => f ((a : ∀ i, A i) i), by
    intro i j h
    simpa [a.property h] using (DFunLike.congr_fun (hf h) ((a : ∀ i, A i) j)).symm⟩
  map_zero' := by
    ext i
    simp
  map_add' a b := by
    ext i
    simp

/-- The system `(A, φ)` is *Mittag-Leffler* if for each `i` the decreasing family of images
`{φ_{ji}(A j) : j ≥ i}` stabilizes: there is some `j ≥ i` such that for all `k ≥ j`,
`range φ_{ki} = range φ_{ji}` as subsets of `A i`. -/
@[ega "0 13.1.2", ega "III 4.1.7", sga "4½ Rapport 4.11"]
def IsMittagLefflerSystem : Prop :=
  ∀ i : I, ∃ (j : I) (h : i ≤ j),
    ∀ ⦃k : I⦄ (hjk : j ≤ k), Set.range (φ (le_trans h hjk)) = Set.range (φ h)

end Defs

section Helpers

variable {I : Type*} [Preorder I]
variable {A : I → Type*} [∀ i, AddCommGroup (A i)]
  {φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)}
variable {B : I → Type*} [∀ i, AddCommGroup (B i)]
  {ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i)}
variable {C : I → Type*} [∀ i, AddCommGroup (C i)]
  {χ : ⦃i j : I⦄ → i ≤ j → (C j →+ C i)}

/-- Membership in the inverse limit: the defining compatibility condition. -/
theorem addInvLimit.mem_iff {a : ∀ i, A i} :
    a ∈ addInvLimit A φ ↔ ∀ ⦃i j : I⦄ (h : i ≤ j), φ h (a j) = a i := Iff.rfl

/-- A morphism of inverse systems commutes with the transition maps, pointwise. -/
private theorem IsInverseSystemMorphism.map_apply {f : ⦃i : I⦄ → (A i →+ B i)}
    (hf : IsInverseSystemMorphism A φ B ψ f) ⦃i j : I⦄ (h : i ≤ j) (a : A j) :
    f (φ h a) = ψ h (f a) := by
  simpa using DFunLike.congr_fun (hf h) a

/-- The `i`-th coordinate of `lim f a` is `f_i (a i)`. -/
@[simp] theorem addInvLimit.map_coe (f : ⦃i : I⦄ → (A i →+ B i))
    (hf : IsInverseSystemMorphism A φ B ψ f)
    (a : addInvLimit A φ) (i : I) :
    ((addInvLimit.map A φ B ψ f hf a : ∀ i, B i) i) = f ((a : ∀ i, A i) i) := rfl

/-- Injectivity of `lim f` follows from injectivity of each `f_i`. -/
@[ega "0 13.1.1" "left exactness", ega "III 4.1.7.21" "partial"]
theorem addInvLimit.map_injective (f : ⦃i : I⦄ → (A i →+ B i))
    (hf : IsInverseSystemMorphism A φ B ψ f)
    (hf_inj : ∀ i, Function.Injective (f (i := i))) :
    Function.Injective (addInvLimit.map A φ B ψ f hf) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  ext i
  exact hf_inj i (by simpa using congrArg (fun x : addInvLimit B ψ => (x : ∀ i, B i) i) ha)

/-- Exactness in the middle of the limit sequence (does not need Mittag-Leffler). -/
@[ega "0 13.1.1" "left exactness",
  ega "0 13.2.2" "exactness at lim B",
  ega "0 7.2.2" "more general",
  ega "III 4.1.7.21" "partial"]
theorem addInvLimit.range_map_eq_ker_map
    (f : ⦃i : I⦄ → (A i →+ B i)) (g : ⦃i : I⦄ → (B i →+ C i))
    (hf : IsInverseSystemMorphism A φ B ψ f) (hg : IsInverseSystemMorphism B ψ C χ g)
    (hf_inj : ∀ i, Function.Injective (f (i := i)))
    (h_exact : ∀ i, (f (i := i)).range = (g (i := i)).ker) :
    (addInvLimit.map A φ B ψ f hf).range = (addInvLimit.map B ψ C χ g hg).ker := by
  refine le_antisymm ?_ fun b hb => ?_
  · rintro _ ⟨a, rfl⟩
    ext i
    change g (f ((a : ∀ i, A i) i)) = 0
    exact (h_exact i).le ⟨_, rfl⟩
  · have hexist i : ∃ x : A i, f x = (b : ∀ i, B i) i := (h_exact i).ge <| by
      simpa using congrArg (fun x : addInvLimit C χ => (x : ∀ i, C i) i)
        (AddMonoidHom.mem_ker.mp hb)
    choose a ha using hexist
    refine ⟨⟨a, fun i j h => hf_inj i ?_⟩, Subtype.ext (funext ha)⟩
    simp [ha, b.property h, hf.map_apply]

end Helpers

section Surjectivity

variable {I : Type*} [Preorder I]
variable {A : I → Type*} [∀ i, AddCommGroup (A i)]
  {φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)}
variable {B : I → Type*} [∀ i, AddCommGroup (B i)]
  {ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i)}
variable {C : I → Type*} [∀ i, AddCommGroup (C i)]
  {χ : ⦃i j : I⦄ → i ≤ j → (C j →+ C i)}

/-! ### Surjectivity of `lim g`

Fix `c ∈ lim C`. For each `i` form the fiber
`E i = g_i⁻¹(c i) ⊆ B i`, a *nonempty* coset of `ker g_i = range f_i`. The transition maps
`ψ h` restrict to maps `E j → E i` (using that `g` is a morphism and that `c` is compatible),
so `(E i)` is a directed inverse system of nonempty sets. The Mittag-Leffler condition on the
kernel system `(A, φ)` transfers to `(E i)` (the difference of two elements of a fiber lies in
`range f_i`, so the image-stabilisation of `(A, φ)` forces the affine image family of `E` to
stabilise). Stacks Tag 0597 — the limit of a nonempty Mittag-Leffler inverse system of sets
over a *countable* directed index set is nonempty — then provides a compatible section
`(b i) ∈ ∏ E i`, i.e. `b ∈ lim B` with `g_i (b i) = c i`, hence `lim g b = c`.

`mittagLeffler_section` is the abelian-group form of Stacks Tag 0597 applied to the fiber
system: it produces the compatible family of preimages directly. Assembling that family into
`lim B` and checking `lim g b = c` is then `invLimit_map_surjective`. -/

/-! #### Set-theoretic core (Stacks Tag 0597)

The substantive content is purely set-theoretic, and lives below in three standalone lemmas
about set-valued inverse systems over a countable directed index `I`:

* `cofinal_monotone_seq` — countability, directedness and nonemptiness yield a monotone
  `n : ℕ → I` that is cofinal (`∀ i, ∃ m, i ≤ n m`).
* `section_of_surjective_invsystem` — a set-valued inverse system over `I` with all
  transition maps surjective and all fibers nonempty has a nonempty inverse limit
  (a compatible section): dependent choice along the cofinal chain, then extension to all
  of `I`.
* `exists_section_of_ML` — the full Stacks 0597: a *Mittag-Leffler* set-valued inverse
  system of nonempty sets over `I` has a section. One passes to the eventual-range
  subsystem, whose transition maps are surjective, and applies
  `section_of_surjective_invsystem`.

`mittagLeffler_section` then builds the fiber system `E i = g_i⁻¹(c i)` and applies
`exists_section_of_ML` to it. -/

/-- A countable, nonempty, directed preorder admits a monotone sequence `n : ℕ → I` that is
cofinal: every `i` lies below some `n m`.  Construction: enumerate `I` by a surjection
`e : ℕ → I` (`exists_surjective_nat`, from `Countable I` and `Nonempty I`), then set
`n 0 = e 0` and `n (m+1) =` an upper bound of `n m` and `e (m+1)` (via `IsDirected`).
Monotonicity is `monotone_nat_of_le_succ`; cofinality holds because `e (m) ≤ n m`. -/
theorem cofinal_monotone_seq (I : Type*) [Preorder I] [Countable I] [Nonempty I]
    [IsDirected I (· ≤ ·)] :
    ∃ n : ℕ → I, Monotone n ∧ ∀ i : I, ∃ m, i ≤ n m :=
  exists_monotone_cofinal_nat

/-- A set-valued inverse system `(S i, t)` over a countable directed `I`, with every transition
map `t h : S j → S i` surjective and every fiber `S i` nonempty, has a nonempty inverse
limit: there is a compatible family `s : ∀ i, S i` with `t h (s j) = s i` for all `i ≤ j`.

Proof sketch:
* Take a cofinal monotone `n : ℕ → I` from `cofinal_monotone_seq`.
* Build a thread `x : ∀ k, S (n k)` with `t (s_k) (x (k+1)) = x k` by `Nat.rec`, choosing
  preimages with `Function.surjInv` of the (surjective) transition maps `S (n (k+1)) → S (n k)`.
  Compatibility along the chain (`t (x b) = x a` for `a ≤ b`) is `Nat.le_induction` + `hcomp`.
* Define `s i := t (i ≤ n m) (x m)` for some/any `m` with `i ≤ n m` (cofinality).
  Well-definedness (independence of `m`, using that `ℕ` is linear and the chain
  compatibility) and the compatibility of `s` follow from `hcomp` and `hid`. -/
theorem section_of_surjective_invsystem (I : Type*) [Preorder I] [Countable I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (S : I → Type*)
    (t : ⦃i j : I⦄ → i ≤ j → S j → S i)
    (hid : ∀ (i : I) (x : S i), t (le_refl i) x = x)
    (hcomp : ∀ ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      t hij (t hjk x) = t (le_trans hij hjk) x)
    (hsurj : ∀ ⦃i j : I⦄ (h : i ≤ j), Function.Surjective (t h))
    (hne : ∀ i, Nonempty (S i)) :
      ∃ s : ∀ i, S i, ∀ ⦃i j : I⦄ (h : i ≤ j), t h (s j) = s i :=
  DirInvSystem.nonempty_limit_of_isMittagLeffler ⟨t, hid, hcomp⟩
    (fun i => ⟨i, le_rfl, fun _ _ => (hsurj _).range_eq.trans (hsurj le_rfl).range_eq.symm⟩) hne

/-- Mittag-Leffler implies a nonempty limit, in set form.
A set-valued inverse system `(S i, t)` over a countable directed `I` with nonempty fibers
that is Mittag-Leffler (the decreasing image family `{ range (t (i ≤ k)) : k ≥ i }`
stabilizes for each `i`) has a compatible section.

Proof sketch:
* For each `i`, the eventual range `E i := range (t (i ≤ j₀))` (any stabilizing `j₀`, given
  by `hML i`) is nonempty (image of a nonempty `S j₀`) and the transition maps restrict to
  *surjective* maps `E j → E i`, using directedness and the stabilization.
* The restricted system `(E i)` has nonempty fibers and surjective transitions, so
  `section_of_surjective_invsystem` gives a section of `(E i)`, which (via the inclusions
  `E i ↪ S i`) is a section of `(S i)`. -/
@[sga "4 I App.Lemma3" "more general"]
theorem exists_section_of_ML (I : Type*) [Preorder I] [Countable I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (S : I → Type*)
    (t : ⦃i j : I⦄ → i ≤ j → S j → S i)
    (hid : ∀ (i : I) (x : S i), t (le_refl i) x = x)
    (hcomp : ∀ ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      t hij (t hjk x) = t (le_trans hij hjk) x)
    (hne : ∀ i, Nonempty (S i))
    (hML : ∀ i : I, ∃ (j : I) (h : i ≤ j),
      ∀ ⦃k : I⦄ (hjk : j ≤ k), Set.range (t (le_trans h hjk)) = Set.range (t h)) :
    ∃ s : ∀ i, S i, ∀ ⦃i j : I⦄ (h : i ≤ j), t h (s j) = s i :=
  DirInvSystem.nonempty_limit_of_isMittagLeffler ⟨t, hid, hcomp⟩
    (fun i => let ⟨j, h, hk⟩ := hML i; ⟨j, h, fun _ hk' => hk hk'⟩) hne

/-- Lifting along the fibers of `g`: if `range φ_{ki} = range φ_{ji}` for `i ≤ j ≤ k`, then
every `d ∈ g_j⁻¹(c j)` has `ψ_{ji}(d) = ψ_{ki}(e)` for some `e ∈ g_k⁻¹(c k)`. This is the step
transferring the Mittag-Leffler condition from `(A, φ)` to the fibers of `g`. -/
theorem exists_fiber_lift_of_range_eq
    (hψ : InverseSystem (fun _ _ h => (ψ h : _ → _)))
    {f : ⦃i : I⦄ → (A i →+ B i)} {g : ⦃i : I⦄ → (B i →+ C i)}
    (hf_mor : IsInverseSystemMorphism A φ B ψ f)
    (hg_mor : IsInverseSystemMorphism B ψ C χ g)
    (h_exact : ∀ i, (f (i := i)).range = (g (i := i)).ker)
    (hg_surj : ∀ i, Function.Surjective (g (i := i)))
    (c : addInvLimit C χ) {i j k : I} (h : i ≤ j) (hjk : j ≤ k)
    (hstab : Set.range (φ (h.trans hjk)) = Set.range (φ h))
    (d : B j) (hd : g d = (c : ∀ i, C i) j) :
    ∃ e : B k, g e = (c : ∀ i, C i) k ∧ ψ (h.trans hjk) e = ψ h d := by
  have hc : ∀ ⦃i j : I⦄ (h : i ≤ j), χ h ((c : ∀ i, C i) j) = (c : ∀ i, C i) i := c.property
  obtain ⟨b₀, hb₀⟩ := hg_surj k ((c : ∀ i, C i) k)
  have hgb : g (ψ hjk b₀) = (c : ∀ i, C i) j := by
    rw [hg_mor.map_apply, hb₀, hc hjk]
  obtain ⟨a, ha⟩ : d - ψ hjk b₀ ∈ (f (i := j)).range := by
    rw [h_exact j, AddMonoidHom.mem_ker, map_sub, hd, hgb, sub_self]
  obtain ⟨a', ha'⟩ : φ h a ∈ Set.range (φ (h.trans hjk)) := hstab ▸ ⟨a, rfl⟩
  have e₂ : ψ (h.trans hjk) b₀ = ψ h (ψ hjk b₀) := (hψ.map_map h hjk b₀).symm
  refine ⟨b₀ + f a', by
    rw [map_add, hb₀, AddMonoidHom.mem_ker.mp ((h_exact k).le ⟨a', rfl⟩), add_zero], ?_⟩
  rw [map_add, ← hf_mor.map_apply, ha', hf_mor.map_apply, ha, map_sub, e₂]
  abel

/-- Existence of a Mittag-Leffler section, in abelian-group fiber form.

Given the exact sequence data with `(A, φ)` Mittag-Leffler over a countable directed `I`, and a
compatible family `c ∈ lim C`, there is a compatible family `b ∈ ∏ i, B i` with `ψ h (b j) = b i`
for `i ≤ j` and `g_i (b i) = c i` for all `i`.

This is the set-theoretic heart of the exactness theorem: build the fiber system
`E i = g_i⁻¹(c i)`, show it is a nonempty Mittag-Leffler inverse system of sets, and apply
`exists_section_of_ML`. The countability hypothesis enters only here, via a cofinal `ℕ`-chain
in `I` and dependent choice down the stabilised eventual-range fibers. -/
@[ega "0 13.2.2" "partial"]
theorem mittagLeffler_section
    [IsDirected I (· ≤ ·)] [Nonempty I] [Countable I]
    (hφ : InverseSystem (fun _ _ h => (φ h : _ → _)))
    (hψ : InverseSystem (fun _ _ h => (ψ h : _ → _)))
    (hχ : InverseSystem (fun _ _ h => (χ h : _ → _)))
    {f : ⦃i : I⦄ → (A i →+ B i)} {g : ⦃i : I⦄ → (B i →+ C i)}
    (hf_mor : IsInverseSystemMorphism A φ B ψ f)
    (hg_mor : IsInverseSystemMorphism B ψ C χ g)
    (h_exact : ∀ i, (f (i := i)).range = (g (i := i)).ker)
    (hg_surj : ∀ i, Function.Surjective (g (i := i)))
    (hML : IsMittagLefflerSystem A φ)
    (c : addInvLimit C χ) :
    ∃ b : ∀ i, B i, (∀ ⦃i j : I⦄ (h : i ≤ j), ψ h (b j) = b i) ∧
      (∀ i, g (b i) = (c : ∀ i, C i) i) := by
  have hc : ∀ ⦃i j : I⦄ (h : i ≤ j), χ h ((c : ∀ i, C i) j) = (c : ∀ i, C i) i := c.property
  let E : I → Type _ := fun i => {b : B i // g b = (c : ∀ i, C i) i}
  let tE : ⦃i j : I⦄ → i ≤ j → E j → E i := fun _ _ h e =>
    ⟨ψ h e.1, by rw [hg_mor.map_apply, e.2, hc]⟩
  have htE_comp ⦃i j k : I⦄ (hij : i ≤ j) (hjk : j ≤ k) (e : E k) :
      tE hij (tE hjk e) = tE (hij.trans hjk) e :=
    Subtype.ext (hψ.map_map hij hjk e.1)
  have hEML : ∀ i : I, ∃ (j : I) (h : i ≤ j),
      ∀ ⦃k : I⦄ (hjk : j ≤ k), Set.range (tE (le_trans h hjk)) = Set.range (tE h) := by
    intro i
    obtain ⟨j, h, hstab⟩ := hML i
    refine ⟨j, h, fun k hjk => le_antisymm ?_ ?_⟩
    · rintro _ ⟨e, rfl⟩
      exact ⟨tE hjk e, htE_comp h hjk e⟩
    · rintro _ ⟨d, rfl⟩
      obtain ⟨e, he, he'⟩ := exists_fiber_lift_of_range_eq hψ hf_mor hg_mor h_exact hg_surj c h
        hjk (hstab hjk) d.1 d.2
      exact ⟨⟨e, he⟩, Subtype.ext he'⟩
  obtain ⟨s, hs⟩ := exists_section_of_ML I E tE (fun i e => Subtype.ext (hψ.map_self e.1))
    htE_comp (fun i => (hg_surj i ((c : ∀ i, C i) i)).elim fun b hb => ⟨⟨b, hb⟩⟩) hEML
  exact ⟨fun i => (s i).1, fun _ _ h => congrArg Subtype.val (hs h), fun i => (s i).2⟩

/-- Given the exactness data and a Mittag-Leffler kernel system, the induced map
`lim g : lim B → lim C` is surjective. The exactness hypotheses are taken one by one
rather than bundled as an `IsExactSeq`. -/
@[ega "III 4.1.7.21" "partial"]
theorem invLimit_map_surjective_aux
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] [Countable I]
    {A : I → Type*} [∀ i, AddCommGroup (A i)]
    {φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)}
    (hφ : InverseSystem (fun _ _ h => (φ h : _ → _)))
    {B : I → Type*} [∀ i, AddCommGroup (B i)]
    {ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i)}
    (hψ : InverseSystem (fun _ _ h => (ψ h : _ → _)))
    {C : I → Type*} [∀ i, AddCommGroup (C i)]
    {χ : ⦃i j : I⦄ → i ≤ j → (C j →+ C i)}
    (hχ : InverseSystem (fun _ _ h => (χ h : _ → _)))
    {f : ⦃i : I⦄ → (A i →+ B i)} {g : ⦃i : I⦄ → (B i →+ C i)}
    (hf_mor : IsInverseSystemMorphism A φ B ψ f)
    (hg_mor : IsInverseSystemMorphism B ψ C χ g)
    (h_exact : ∀ i, (f (i := i)).range = (g (i := i)).ker)
    (hg_surj : ∀ i, Function.Surjective (g (i := i)))
    (hML : IsMittagLefflerSystem A φ) :
    Function.Surjective (addInvLimit.map B ψ C χ g hg_mor) := by
  intro c
  obtain ⟨b, hb, hgb⟩ := mittagLeffler_section hφ hψ hχ hf_mor hg_mor h_exact hg_surj hML c
  exact ⟨⟨b, hb⟩, Subtype.ext (funext hgb)⟩

end Surjectivity

section Exactness

variable {I : Type*} [Preorder I]
variable {A : I → Type*} [∀ i, AddCommGroup (A i)]
  {φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)}
variable {B : I → Type*} [∀ i, AddCommGroup (B i)]
  {ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i)}
variable {C : I → Type*} [∀ i, AddCommGroup (C i)]
  {χ : ⦃i j : I⦄ → i ≤ j → (C j →+ C i)}

/-- The sequence `0 → A →[f] B →[g] C → 0` of morphisms of inverse systems is *exact* if for
every index `i` the sequence of abelian groups
`0 → A i →[f_i] B i →[g_i] C i → 0` is exact: `f_i` is injective,
`range f_i = ker g_i`, and `g_i` is surjective. -/
structure IsExactSeq
    (f : ⦃i : I⦄ → (A i →+ B i)) (g : ⦃i : I⦄ → (B i →+ C i)) : Prop where
  /-- `f` is a morphism of inverse systems. -/
  hf_mor : IsInverseSystemMorphism A φ B ψ f
  /-- `g` is a morphism of inverse systems. -/
  hg_mor : IsInverseSystemMorphism B ψ C χ g
  /-- Each `f_i` is injective. -/
  hf_inj : ∀ i, Function.Injective (f (i := i))
  /-- Exactness in the middle: `range f_i = ker g_i`. -/
  h_exact : ∀ i, (f (i := i)).range = (g (i := i)).ker
  /-- Each `g_i` is surjective. -/
  hg_surj : ∀ i, Function.Surjective (g (i := i))

end Exactness

/-- Let `I` be a countable directed set and let
`0 → A →[f] B →[g] C → 0` be an exact sequence of directed inverse systems of abelian
groups over `I`.  If the system `(A, φ)` is Mittag-Leffler, then the induced sequence of
inverse limits
`0 → lim A →[lim f] lim B →[lim g] lim C → 0`
is exact:

1. `lim f` is injective;
2. `range (lim f) = ker (lim g)`;
3. `lim g` is surjective.

Left-exactness (parts 1 and 2) holds for any exact sequence of inverse systems; the
Mittag-Leffler hypothesis and countability are used for part 3, the surjectivity of
`lim g`. -/
@[stacks 0598, ega "0 13.2.2", ega "III 4.1.7.21" "more general"]
theorem invLimit_exact
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] [Countable I]
    {A : I → Type*} [∀ i, AddCommGroup (A i)]
    {φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)}
    (hφ : InverseSystem (fun _ _ h => (φ h : _ → _)))
    {B : I → Type*} [∀ i, AddCommGroup (B i)]
    {ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i)}
    (hψ : InverseSystem (fun _ _ h => (ψ h : _ → _)))
    {C : I → Type*} [∀ i, AddCommGroup (C i)]
    {χ : ⦃i j : I⦄ → i ≤ j → (C j →+ C i)}
    (hχ : InverseSystem (fun _ _ h => (χ h : _ → _)))
    {f : ⦃i : I⦄ → (A i →+ B i)} {g : ⦃i : I⦄ → (B i →+ C i)}
    (hexact : IsExactSeq (φ := φ) (ψ := ψ) (χ := χ) f g)
    (hML : IsMittagLefflerSystem A φ) :
    Function.Injective (addInvLimit.map A φ B ψ f hexact.hf_mor) ∧
      (addInvLimit.map A φ B ψ f hexact.hf_mor).range =
        (addInvLimit.map B ψ C χ g hexact.hg_mor).ker ∧
      Function.Surjective (addInvLimit.map B ψ C χ g hexact.hg_mor) :=
  ⟨addInvLimit.map_injective f hexact.hf_mor hexact.hf_inj,
    addInvLimit.range_map_eq_ker_map f g hexact.hf_mor hexact.hg_mor hexact.hf_inj hexact.h_exact,
    invLimit_map_surjective_aux hφ hψ hχ hexact.hf_mor hexact.hg_mor hexact.h_exact
      hexact.hg_surj hML⟩

/-- Under the same hypotheses, the induced map `lim g : lim B → lim C` is surjective.
This is the essential content of the exactness theorem. -/
@[ega "0 13.2.2" "partial", ega "III 4.1.7.21" "partial"]
theorem invLimit_map_surjective
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] [Countable I]
    {A : I → Type*} [∀ i, AddCommGroup (A i)]
    {φ : ⦃i j : I⦄ → i ≤ j → (A j →+ A i)}
    (hφ : InverseSystem (fun _ _ h => (φ h : _ → _)))
    {B : I → Type*} [∀ i, AddCommGroup (B i)]
    {ψ : ⦃i j : I⦄ → i ≤ j → (B j →+ B i)}
    (hψ : InverseSystem (fun _ _ h => (ψ h : _ → _)))
    {C : I → Type*} [∀ i, AddCommGroup (C i)]
    {χ : ⦃i j : I⦄ → i ≤ j → (C j →+ C i)}
    (hχ : InverseSystem (fun _ _ h => (χ h : _ → _)))
    {f : ⦃i : I⦄ → (A i →+ B i)} {g : ⦃i : I⦄ → (B i →+ C i)}
    (hexact : IsExactSeq (φ := φ) (ψ := ψ) (χ := χ) f g)
    (hML : IsMittagLefflerSystem A φ) :
    Function.Surjective (addInvLimit.map B ψ C χ g hexact.hg_mor) :=
  invLimit_map_surjective_aux hφ hψ hχ hexact.hf_mor hexact.hg_mor hexact.h_exact
    hexact.hg_surj hML

end

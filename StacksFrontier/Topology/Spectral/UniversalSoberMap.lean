module

public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

/-
# Problem: Universal sober map preserves quasi-compactness, spectral, and Noetherian spectral
properties (Stacks Project tag `0A2T`, Lemma 5.23.15).

## Background

Throughout, "topological space" means a (not necessarily Hausdorff) topological space, and all
maps between topological spaces are assumed continuous unless otherwise stated. "Quasi-compact"
is used in the Bourbaki / Stacks Project sense: every open cover admits a finite subcover, with
no Hausdorffness assumption. In Mathlib this corresponds to `CompactSpace` / `IsCompact`.

A topological space is *Noetherian* iff every ascending chain of open subsets stabilizes.
In Mathlib this is `TopologicalSpace.NoetherianSpace`.

A topological space is *sober* iff every irreducible closed subset has a unique generic point.
In Mathlib this is captured by `T0Space` together with `QuasiSober` (`QuasiSober` gives
existence of a generic point and `T0Space` gives uniqueness).

A topological space is *spectral* iff it is sober, quasi-compact, has a basis of quasi-compact
opens, and the intersection of any two quasi-compact opens is quasi-compact. In Mathlib this is
`SpectralSpace`, which bundles `T0Space`, `QuasiSober`, `CompactSpace`, `PrespectralSpace`
(basis of quasi-compact opens) and `QuasiSeparatedSpace` (intersections of quasi-compact opens
are quasi-compact).

## The universal map to a sober space (Definition 7)

A *universal map from $X$ to a sober topological space* is a continuous map $c : X \to X'$ with
$X'$ sober, satisfying the universal property: every continuous $f : X \to Y$ with $Y$ sober
factors uniquely through $c$. The Stacks Project records two additional properties of $c$:

(a) The assignment $U' \mapsto c^{-1}(U')$ is a bijection from opens of $X'$ to opens of $X$.

(b) This bijection commutes with finite intersections and arbitrary unions of opens, and so does
its inverse. (In Lean, the forward direction is automatic from continuity:
`TopologicalSpace.Opens.comap` is a `FrameHom`, which preserves finite meets and arbitrary
joins. Combined with bijectivity, the inverse is automatically a `FrameHom` too.)

We bundle the data of a universal map together with the universal property (Definition 7),
property (a) (bijection of opens), and property (b) (compatibility with finite intersections
and arbitrary unions for both the bijection and its inverse) into the structure
`UniversalSoberMap` below.

## Main statements

Let $X$ be a topological space and let $c : X \to X'$ be a universal map from $X$ to a sober
topological space (in the sense of Definition 7, with the properties (a) and (b)).

(1) If $X$ is quasi-compact, then $X'$ is quasi-compact.
(2) If $X$ is quasi-compact, has a basis of quasi-compact opens, and the intersection of any
    two quasi-compact opens of $X$ is quasi-compact, then $X'$ is spectral.
(3) If $X$ is Noetherian, then $X'$ is a Noetherian spectral space.
-/

open TopologicalSpace

universe u v

-- Main Definition(s)

/--
`UniversalSoberMap X X'` bundles the data of a *universal map from `X` to a sober topological
space* (in the sense of Stacks Project tag `0A2N`, Definition 7 of the problem).

It consists of:

* a continuous function `toFun : X → X'`;
* witnesses that `X'` is sober (`isT0 : T0Space X'` and `isQuasiSober : QuasiSober X'`);
* the **universal property** (Definition 7): for every sober topological space `Y` (i.e.
  `T0Space Y` and `QuasiSober Y`) and every continuous map `f : X → Y`, there is a *unique*
  continuous map `f' : X' → Y` with `f' ∘ c = f`;
* property (a): the induced map on opens `U' ↦ c⁻¹(U')` from `Opens X'` to `Opens X` is a
  bijection (`bijective_opens`);
* property (b): this bijection and its inverse both commute with finite intersections and
  arbitrary unions of opens (`comap_inf`, `comap_iSup`, `invFun_opens_inf`,
  `invFun_opens_iSup`).

In Lean, `TopologicalSpace.Opens.comap` is already a `FrameHom`, so the forward compatibility
in (b) is automatic; we record the explicit statements in this structure so that the
formalized data faithfully matches the problem's definition.
-/
structure UniversalSoberMap (X : Type u) (X' : Type v) [TopologicalSpace X] [TopologicalSpace X']
    where
  /-- The underlying function `c : X → X'`. -/
  toFun : X → X'
  /-- The map `c` is continuous. -/
  continuous_toFun : Continuous toFun
  /-- `X'` is `T0` (uniqueness of generic points of irreducible closed subsets). -/
  isT0 : T0Space X'
  /-- `X'` is quasi-sober (existence of generic points of irreducible closed subsets).
      Together with `isT0`, this says that `X'` is sober (Definition 4). -/
  isQuasiSober : QuasiSober X'
  /-- **Universal property (Definition 7).**
      For every sober topological space `Y` (that is, `T0Space Y` and `QuasiSober Y`) and
      every continuous map `f : X → Y`, there exists a *unique* continuous map `f' : X' → Y`
      such that `f' ∘ c = f`. -/
  universal_property :
    ∀ {Y : Type*} [TopologicalSpace Y] [T0Space Y] [QuasiSober Y]
      (f : X → Y), Continuous f →
      ∃! f' : X' → Y, Continuous f' ∧ f' ∘ toFun = f
  /-- **Property (a) (bijection of opens).**
      The map `U' ↦ c⁻¹(U')` from `Opens X'` to `Opens X` is a bijection. -/
  bijective_opens :
    Function.Bijective
      (Opens.comap ⟨toFun, continuous_toFun⟩ : Opens X' → Opens X)
  /-- **Property (b), forward, finite intersections.**
      The bijection `U' ↦ c⁻¹(U')` commutes with binary intersections of opens. -/
  comap_inf : ∀ U' V' : Opens X',
      (Opens.comap ⟨toFun, continuous_toFun⟩) (U' ⊓ V') =
        (Opens.comap ⟨toFun, continuous_toFun⟩) U' ⊓
          (Opens.comap ⟨toFun, continuous_toFun⟩) V'
  /-- **Property (b), forward, arbitrary unions.**
      The bijection `U' ↦ c⁻¹(U')` commutes with arbitrary unions of opens. -/
  comap_iSup : ∀ {ι : Type u} (U' : ι → Opens X'),
      (Opens.comap ⟨toFun, continuous_toFun⟩) (⨆ i, U' i) =
        ⨆ i, (Opens.comap ⟨toFun, continuous_toFun⟩) (U' i)
  /-- **Property (b), inverse, finite intersections.**
      The inverse bijection (sending an open `U ⊂ X` to the unique open `U' ⊂ X'` with
      `c⁻¹(U') = U`) also commutes with binary intersections: if `c⁻¹(U₁') = U₁` and
      `c⁻¹(U₂') = U₂`, then the unique open of `X'` whose preimage is `U₁ ⊓ U₂` is
      `U₁' ⊓ U₂'`, i.e. `c⁻¹(U₁' ⊓ U₂') = U₁ ⊓ U₂`. -/
  invFun_opens_inf : ∀ (U₁' U₂' : Opens X') (U₁ U₂ : Opens X),
      (Opens.comap ⟨toFun, continuous_toFun⟩) U₁' = U₁ →
      (Opens.comap ⟨toFun, continuous_toFun⟩) U₂' = U₂ →
      (Opens.comap ⟨toFun, continuous_toFun⟩) (U₁' ⊓ U₂') = U₁ ⊓ U₂
  /-- **Property (b), inverse, arbitrary unions.**
      The inverse bijection also commutes with arbitrary unions: if `c⁻¹(U'_i) = U_i` for all
      `i`, then the unique open of `X'` whose preimage is `⨆ i, U_i` is `⨆ i, U'_i`. -/
  invFun_opens_iSup : ∀ {ι : Type u} (U' : ι → Opens X') (U : ι → Opens X),
      (∀ i, (Opens.comap ⟨toFun, continuous_toFun⟩) (U' i) = U i) →
      (Opens.comap ⟨toFun, continuous_toFun⟩) (⨆ i, U' i) = ⨆ i, U i

-- Main Statement(s)

namespace UniversalSoberMap

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
variable (c : UniversalSoberMap X X')

/-- Abbreviation for the comap on opens: `c.φ U' = c⁻¹(U')` -/
abbrev φ : Opens X' → Opens X := Opens.comap ⟨c.toFun, c.continuous_toFun⟩

/-- The comap on opens is injective -/
lemma φ_injective : Function.Injective c.φ := c.bijective_opens.1

/-- The comap on opens is surjective -/
lemma φ_surjective : Function.Surjective c.φ := c.bijective_opens.2

/-- The comap on opens is monotone (it's a FrameHom) -/
lemma φ_monotone : Monotone c.φ :=
  OrderHomClass.mono (Opens.comap ⟨c.toFun, c.continuous_toFun⟩)

/-- φ maps ⊤ to ⊤ (preimage of the whole space is the whole space) -/
lemma φ_top : c.φ ⊤ = ⊤ := Opens.coe_eq_univ.mp rfl

/-! ### Quasi-compactness transfer principle

The key lemma: an open U' ⊆ X' is quasi-compact iff its preimage c⁻¹(U') ⊆ X is
quasi-compact. This follows from the bijection on opens plus the ⨆-compatibility
in both directions.
-/

/-- φ reflects ≤: if φ(A) ≤ φ(B) then A ≤ B. Uses injectivity + invFun_opens_iSup. -/
lemma φ_reflects_le {A B : Opens X'} (h : c.φ A ≤ c.φ B) : A ≤ B := by
  have key := c.invFun_opens_iSup (ι := ULift Bool)
    (fun (j : ULift Bool) => if j.down then A else B)
    (fun (j : ULift Bool) => c.φ (if j.down then A else B))
    (fun _ => rfl)
  simp only [iSup_ulift, iSup_bool_eq, ite_true, Bool.false_eq_true, ite_false] at key
  have hab : c.φ (A ⊔ B) = c.φ B := by
    have : c.φ (A ⊔ B) = c.φ A ⊔ c.φ B := key
    rw [this, sup_eq_right.mpr h]
  exact (c.φ_injective hab) ▸ le_sup_left

/-- Forward direction of transfer: if U' is compact then c⁻¹(U') is compact.
    Given an open cover (Vᵢ) of c⁻¹(U') in X:
    1. Lift each Vᵢ to V'ᵢ in X' via surjectivity of φ
    2. Show (V'ᵢ) covers U' using monotonicity + φ_reflects_le
    3. Extract finite subcover of U' by compactness
    4. Pull back to finite subcover of c⁻¹(U') -/
lemma isCompact_of_isCompact_preimage (U' : Opens X')
    (hU' : IsCompact (U' : Set X')) :
    IsCompact ((c.φ U' : Opens X) : Set X) := by
  apply isCompact_of_finite_subcover
  intro ι V hV_open hcover
  choose V' hV' using fun i => c.φ_surjective ⟨V i, hV_open i⟩
  have hV'_eq : ∀ i, (c.φ (V' i) : Set X) = V i :=
    fun i => congr_arg Opens.carrier (hV' i)
  -- φ U' ≤ ⨆ i, φ(V' i) ≤ φ(⨆ i, V' i) by monotonicity, hence U' ≤ ⨆ i, V' i
  have h_cover_le : c.φ U' ≤ c.φ (⨆ i, V' i) :=
    calc c.φ U' ≤ ⨆ i, c.φ (V' i) := by
            intro x hx
            obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
            exact Opens.mem_iSup.mpr ⟨i, show x ∈ (c.φ (V' i) : Set X) from (hV'_eq i).symm ▸ hi⟩
         _ ≤ c.φ (⨆ i, V' i) :=
            iSup_le (fun i => c.φ_monotone (le_iSup V' i))
  have h4 : U' ≤ ⨆ i, V' i := c.φ_reflects_le h_cover_le
  have hcover_X' : (U' : Set X') ⊆ ⋃ i, (V' i : Set X') := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (h4 hx)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨F, hF⟩ := hU'.elim_finite_subcover
    (fun i => (V' i : Set X')) (fun i => (V' i).isOpen) hcover_X'
  refine ⟨F, fun x hx => ?_⟩
  obtain ⟨i, hiF, hi⟩ := Set.mem_iUnion₂.mp (hF hx)
  have hmem : x ∈ (c.φ (V' i) : Set X) := hi
  rw [show (c.φ (V' i) : Set X) = V i from hV'_eq i] at hmem
  exact Set.mem_iUnion₂.mpr ⟨i, hiF, hmem⟩

/-- Reverse direction of transfer: if c⁻¹(U') is compact then U' is compact.
    Given an open cover (W'ⱼ) of U' in X':
    1. Pull back to cover (c⁻¹(W'ⱼ)) of c⁻¹(U') via comap_iSup
    2. Extract finite subcover of c⁻¹(U') by compactness
    3. Lift back to finite subcover of U' via injectivity of φ -/
lemma isCompact_preimage_of_isCompact (U' : Opens X')
    (hU : IsCompact ((c.φ U' : Opens X) : Set X)) :
    IsCompact (U' : Set X') := by
  apply isCompact_of_finite_subcover
  intro ι W' hW'_open hcover'
  let W'o : ι → Opens X' := fun i => ⟨W' i, hW'_open i⟩
  have h_cover_X : (c.φ U' : Set X) ⊆ ⋃ i, (c.φ (W'o i) : Set X) := by
    intro x hx
    have hx' : c.toFun x ∈ (U' : Set X') := hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover' hx')
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨F, hF⟩ := hU.elim_finite_subcover
    (fun i => (c.φ (W'o i) : Set X)) (fun i => (c.φ (W'o i)).isOpen) h_cover_X
  have h_fin_cover : c.φ U' ≤ c.φ (⨆ i ∈ F, W'o i) :=
    calc c.φ U' ≤ ⨆ (i : ι) (_ : i ∈ F), c.φ (W'o i) := by
          intro x hx
          obtain ⟨i, hiF, hi⟩ := Set.mem_iUnion₂.mp (hF hx)
          exact Opens.mem_iSup.mpr ⟨i, Opens.mem_iSup.mpr ⟨hiF, hi⟩⟩
      _ ≤ c.φ (⨆ i ∈ F, W'o i) := by
          apply iSup₂_le
          intro i hiF
          exact c.φ_monotone (le_iSup_of_le i (le_iSup_of_le hiF le_rfl))
  refine ⟨F, fun x' hx' => ?_⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (c.φ_reflects_le h_fin_cover hx')
  obtain ⟨hiF, hi⟩ := Opens.mem_iSup.mp hi
  exact Set.mem_iUnion₂.mpr ⟨i, hiF, hi⟩

/-- Key transfer lemma (iff version) -/
lemma isCompact_iff_preimage (U' : Opens X') :
    IsCompact (U' : Set X') ↔ IsCompact ((c.φ U' : Opens X) : Set X) :=
  ⟨c.isCompact_of_isCompact_preimage U', c.isCompact_preimage_of_isCompact U'⟩

end UniversalSoberMap

/--
**Statement (1).** If `X` is quasi-compact, then so is `X'`.
This is the first part of Stacks Project Lemma 5.23.15 (tag `0A2T`).
-/
@[stacks 0A2T "part (1): quasi-compactness"]
theorem UniversalSoberMap.compactSpace
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (c : UniversalSoberMap X X') [CompactSpace X] :
    CompactSpace X' := by
  -- Apply transfer principle to the whole space: φ(⊤) = ⊤ and ⊤ in X is compact
  rw [← isCompact_univ_iff, ← Opens.coe_top, c.isCompact_iff_preimage ⊤, c.φ_top]
  exact isCompact_univ

/-- X' has a basis of quasi-compact opens, transferred from the basis of X via
    the inverse of the bijection φ.
    Key idea: For each compact open B in X, φ⁻¹(B) = B' is compact open in X'
    (compact by isCompact_preimage_of_isCompact). The collection of such B' forms
    a topological basis, verified using isTopologicalBasis_of_isOpen_of_nhds. -/
lemma UniversalSoberMap.prespectralSpace
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (c : UniversalSoberMap X X')
    [CompactSpace X] [PrespectralSpace X] :
    PrespectralSpace X' := by
  classical
  refine ⟨isTopologicalBasis_of_isOpen_of_nhds (fun _ hU => hU.1) fun x' U' hx'U' hU'_open => ?_⟩
  let U'o : Opens X' := ⟨U', hU'_open⟩
  choose ψ hψ using fun (V : Opens X) => c.φ_surjective V
  let F : Opens X → Opens X' := fun V =>
    if IsCompact (V : Set X) ∧ V ≤ c.φ U'o then ψ V else ⊥
  let G : Opens X → Opens X := fun V =>
    if IsCompact (V : Set X) ∧ V ≤ c.φ U'o then V else ⊥
  have hFG : ∀ V, c.φ (F V) = G V := by
    intro V
    simp only [F, G]
    split_ifs with h
    · exact hψ V
    · exact le_antisymm (fun _ hx => hx) fun _ hx => hx
  have h_sup_G : (⨆ V : Opens X, G V) = c.φ U'o := by
    apply le_antisymm
    · refine iSup_le fun V => ?_
      simp only [G]
      split_ifs with h
      · exact h.2
      · exact bot_le
    · intro x hx
      obtain ⟨B, ⟨hB_open, hB_compact⟩, hxB, hBU⟩ :=
        PrespectralSpace.isTopologicalBasis.isOpen_iff.mp (c.φ U'o).isOpen x hx
      exact Opens.mem_iSup.mpr ⟨⟨B, hB_open⟩, by
        rwa [show G ⟨B, hB_open⟩ = ⟨B, hB_open⟩ from if_pos ⟨hB_compact, hBU⟩]⟩
  have h_eq : (⨆ V : Opens X, F V) = U'o :=
    c.φ_injective ((c.invFun_opens_iSup F G hFG).trans h_sup_G)
  have hx'_mem : x' ∈ (⨆ V : Opens X, F V : Opens X') := h_eq ▸ (show x' ∈ U'o from hx'U')
  obtain ⟨V₀, hx'V₀⟩ := Opens.mem_iSup.mp hx'_mem
  have hcond : IsCompact (V₀ : Set X) ∧ V₀ ≤ c.φ U'o := by
    by_contra h
    have hbot : F V₀ = ⊥ := ite_eq_right h
    rw [hbot] at hx'V₀
    exact absurd hx'V₀ id
  have hFV₀ : F V₀ = ψ V₀ := ite_eq_left hcond
  refine ⟨(ψ V₀ : Set X'), ⟨(ψ V₀).isOpen, c.isCompact_preimage_of_isCompact _ ?_⟩,
    hFV₀ ▸ hx'V₀, (c.φ_reflects_le ?_ : ψ V₀ ≤ U'o)⟩
  · rw [hψ V₀]
    exact hcond.1
  · rw [hψ V₀]
    exact hcond.2

/-- X' is quasi-separated: the intersection of any two quasi-compact opens is quasi-compact.
    Proof: For compact opens U'₁, U'₂ in X':
    - φ(U'₁), φ(U'₂) are compact opens in X (by isCompact_of_isCompact_preimage)
    - φ(U'₁) ⊓ φ(U'₂) = φ(U'₁ ⊓ U'₂) (by comap_inf) is compact (QuasiSeparatedSpace X)
    - Hence U'₁ ⊓ U'₂ is compact (by isCompact_preimage_of_isCompact) -/
lemma UniversalSoberMap.quasiSeparatedSpace
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (c : UniversalSoberMap X X')
    [QuasiSeparatedSpace X] :
    QuasiSeparatedSpace X' := by
  apply QuasiSeparatedSpace.mk
  intro U' V' hU'_open hU'_compact hV'_open hV'_compact
  let U'o : Opens X' := ⟨U', hU'_open⟩
  let V'o : Opens X' := ⟨V', hV'_open⟩
  have hφU : IsCompact ((c.φ U'o : Opens X) : Set X) :=
    c.isCompact_of_isCompact_preimage U'o hU'_compact
  have hφV : IsCompact ((c.φ V'o : Opens X) : Set X) :=
    c.isCompact_of_isCompact_preimage V'o hV'_compact
  have hφUV : IsCompact (((c.φ U'o : Opens X) : Set X) ∩ ((c.φ V'o : Opens X) : Set X)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ (c.φ U'o).isOpen hφU (c.φ V'o).isOpen hφV
  have hinf : c.φ (U'o ⊓ V'o) = c.φ U'o ⊓ c.φ V'o := c.comap_inf U'o V'o
  have hset : ((c.φ (U'o ⊓ V'o) : Opens X) : Set X) = ((c.φ U'o : Opens X) : Set X) ∩ ((c.φ V'o :
      Opens X) : Set X) := by
    simp [hinf, Opens.coe_inf]
  have hφUV' : IsCompact ((c.φ (U'o ⊓ V'o) : Opens X) : Set X) := hset ▸ hφUV
  exact c.isCompact_preimage_of_isCompact (U'o ⊓ V'o) hφUV'

/--
**Statement (2).** If `X` is quasi-compact, has a basis of quasi-compact opens, and the
intersection of any two quasi-compact opens of `X` is quasi-compact, then `X'` is a spectral
topological space. This is the second part of Stacks Project Lemma 5.23.15 (tag `0A2T`).
-/
@[stacks 0A2T "part (2): spectral"]
theorem UniversalSoberMap.spectralSpace
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (c : UniversalSoberMap X X')
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] :
    SpectralSpace X' := by
  have : T0Space X' := c.isT0
  have : QuasiSober X' := c.isQuasiSober
  have : CompactSpace X' := c.compactSpace
  have : PrespectralSpace X' := c.prespectralSpace
  have : QuasiSeparatedSpace X' := c.quasiSeparatedSpace
  exact SpectralSpace.mk

/-- Noetherian space structure transfers through φ.
    Since NoetherianSpace α = WellFoundedGT (Opens α), and φ : Opens X' → Opens X
    is a bijective monotone map (hence an order isomorphism), we get
    WellFoundedGT (Opens X') from WellFoundedGT (Opens X).
    More precisely: φ is injective + monotone, and by bijectivity the inverse is
    also monotone, so φ reflects order. This means φ is strictly monotone.
    StrictMono.wellFoundedGT then gives the result. -/
lemma UniversalSoberMap.noetherianSpace
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (c : UniversalSoberMap X X') [NoetherianSpace X] :
    NoetherianSpace X' :=
  (c.φ_monotone.strictMono_of_injective c.φ_injective).wellFoundedGT

/--
**Statement (3).** If `X` is Noetherian, then `X'` is a Noetherian spectral space.
This is the third part of Stacks Project Lemma 5.23.15 (tag `0A2T`).
-/
@[stacks 0A2T "part (3): Noetherian spectral"]
theorem UniversalSoberMap.noetherianSpectralSpace
    {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']
    (c : UniversalSoberMap X X') [NoetherianSpace X] :
    NoetherianSpace X' ∧ SpectralSpace X' := by
  refine ⟨c.noetherianSpace, ?_⟩
  -- NoetherianSpace X implies CompactSpace, PrespectralSpace, QuasiSeparatedSpace
  have : CompactSpace X := NoetherianSpace.compactSpace X
  have : PrespectralSpace X := instPrespectralSpaceOfNoetherianSpace
  have : QuasiSeparatedSpace X := NoetherianSpace.to_quasiSeparatedSpace
  exact c.spectralSpace

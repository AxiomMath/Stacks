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
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibly closed subspaces of a spectral space

A subset `E` of a spectral space `X` that is closed for the constructible topology is itself a
spectral space in the subspace topology inherited from `X`. The four constituents are
established separately: quasi-compactness of `E`, a basis of quasi-compact opens (each of which
is the restriction of a quasi-compact open of `X`), quasi-separatedness, and quasi-soberness.

## Main results

* `compactSpace_E`: a constructibly closed `E` is quasi-compact.
* `prespectralSpace_E`: the quasi-compact opens form a basis of the subspace topology on `E`.
* `quasiSeparatedSpace_E`: `E` is quasi-separated.
* `quasiSober_E`: `E` is quasi-sober; the generic point of an irreducible closed subset of `E`,
  taken in `X`, already lies in `E`.
* `spectralSpace_of_isClosed_constructibleTopology`: a constructibly closed subset of a spectral
  space is a spectral space.
-/

@[expose] public section

open TopologicalSpace Topology Set


/-- Compactness transfers from a finer topology to a coarser one. -/
lemma compactSpace_of_le
    {α : Type*} {t₁ t₂ : TopologicalSpace α} (h : t₁ ≤ t₂)
    [@CompactSpace α t₁] : @CompactSpace α t₂ := by
  refine @CompactSpace.mk α t₂ ?_
  have h1 : @IsCompact α t₂ (id '' (Set.univ : Set α)) :=
    @IsCompact.image α α t₁ t₂ Set.univ id
      (@CompactSpace.isCompact_univ α t₁ ‹_›) (continuous_id_of_le h)
  rwa [Set.image_univ, Function.surjective_id.range_eq] at h1

/-- `E` is compact in the topology induced from `WithConstructibleTopology X`,
since it is closed in the (compact) constructible topology on `X`. -/
@[sga "4 IV 9.1.11" "9.1.11 g)"]
lemma compactSpace_E_constructible
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    @CompactSpace E
      (TopologicalSpace.induced (Subtype.val : E → X) (constructibleTopology X)) :=
  (@isCompact_iff_compactSpace X (constructibleTopology X) E).mp
    hE.isCompact_constructibleTopology

/-- `E` is compact in the subspace topology from `X`. -/
lemma compactSpace_E
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    CompactSpace E :=
  have := compactSpace_E_constructible E hE
  compactSpace_of_le (induced_mono (constructibleTopology_le X))

/-- For a spectral space `X`, if `E ⊆ X` is constructibly closed and `U ⊆ X`
is compact open, then `E ∩ U` is compact in `X`. -/
lemma isCompact_inter_of_isClosed_constructibleTopology
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X) (hE : @IsClosed X (constructibleTopology X) E)
    (U : Set X) (hUo : IsOpen U) (hUc : IsCompact U) :
    IsCompact (E ∩ U) :=
  -- `U` is constructible-clopen, so `E ∩ U` is constructible-closed, hence
  -- constructible-compact; the constructible topology is the finer one.
  (@IsClosed.inter X E U (constructibleTopology X) hE
    (hUc.isClopen_constructibleTopology hUo).1).isCompact_of_constructibleTopology

/-- For a compact open `U ⊆ X`, the preimage `Subtype.val ⁻¹' U` is compact in `E`. -/
lemma isCompact_E_inter_of_isCompact_isOpen
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E)
    (U : Set X) (hUo : IsOpen U) (hUc : IsCompact U) :
    IsCompact (Subtype.val ⁻¹' U : Set E) := by
  rw [Topology.IsEmbedding.isCompact_iff Topology.IsEmbedding.subtypeVal,
      Subtype.image_preimage_coe]
  exact isCompact_inter_of_isClosed_constructibleTopology E hE U hUo hUc

/-- The compact opens form a topological basis of the subspace topology on `E`. -/
lemma isTopologicalBasis_compactOpens_E
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    IsTopologicalBasis ({ V : Set E | IsOpen V ∧ IsCompact V }) := by
  refine isTopologicalBasis_of_isOpen_of_nhds (fun _ hV => hV.1) ?_
  intro a W haW hWo
  obtain ⟨U, hUo, hUE⟩ := isOpen_induced_iff.mp hWo
  have haU : (a : X) ∈ U := by rw [← hUE] at haW; exact haW
  obtain ⟨V', ⟨hV'o, hV'c⟩, haV', hV'U⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := X)).mem_nhds_iff.mp (hUo.mem_nhds haU)
  exact ⟨Subtype.val ⁻¹' V',
    ⟨hV'o.preimage continuous_subtype_val,
      isCompact_E_inter_of_isCompact_isOpen E hE V' hV'o hV'c⟩,
    haV', fun x hx => by rw [← hUE]; exact hV'U hx⟩

/-- `E` is a `PrespectralSpace` in the subspace topology. -/
lemma prespectralSpace_E
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    PrespectralSpace E :=
  ⟨isTopologicalBasis_compactOpens_E E hE⟩

/-- For any open neighbourhood `W` of `x` in `E`, there is a compact open
`U ⊆ X` with `x.val ∈ U` and `Subtype.val ⁻¹' U ⊆ W`. -/
lemma exists_compactOpen_subset_of_mem_isOpen
    {X : Type*} [TopologicalSpace X] [PrespectralSpace X]
    (E : Set X) (W : Set E) (hWo : IsOpen W) (x : E) (hx : x ∈ W) :
    ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ x.val ∈ U ∧ Subtype.val ⁻¹' U ⊆ W := by
  rw [isOpen_induced_iff] at hWo
  obtain ⟨V, hVo, hVE⟩ := hWo
  have hxV : x.val ∈ V := by simpa [← hVE] using hx
  obtain ⟨U, ⟨hUo, hUc⟩, hxU, hUV⟩ :=
    (PrespectralSpace.isTopologicalBasis (X := X)).exists_subset_of_mem_open hxV hVo
  refine ⟨U, hUo, hUc, hxU, ?_⟩
  rw [← hVE]
  exact preimage_mono hUV

/-- Every compact open subset of `E` is `Subtype.val ⁻¹' U` for some
compact open `U ⊆ X`. -/
lemma exists_compactOpen_eq_preimage
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (W : Set E) (hWo : IsOpen W) (hWc : IsCompact W) :
    ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ W = Subtype.val ⁻¹' U := by
  -- For each `x ∈ W`, pick a compact open `f x ⊆ X` with `x.val ∈ f x` and
  -- `Subtype.val ⁻¹' f x ⊆ W`; then extract a finite subcover.
  choose! f hfo hfc hfx hfW using fun (x : E) (hx : x ∈ W) =>
    exists_compactOpen_subset_of_mem_isOpen E W hWo x hx
  have hcov : W ⊆ ⋃ x ∈ W, (Subtype.val ⁻¹' f x : Set E) :=
    fun x hx => mem_biUnion hx (by simpa using hfx x hx)
  have hopen : ∀ x ∈ W, IsOpen (Subtype.val ⁻¹' f x : Set E) :=
    fun x hx => (hfo x hx).preimage continuous_subtype_val
  obtain ⟨s, hsW, hsFin, hsCov⟩ := hWc.elim_finite_subcover_image hopen hcov
  refine ⟨⋃ x ∈ s, f x,
    isOpen_biUnion (fun x hx => hfo x (hsW hx)),
    hsFin.isCompact_biUnion (fun x hx => hfc x (hsW hx)),
    Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    simp only [preimage_iUnion, mem_iUnion]
    have hx' := hsCov hx
    simp only [mem_iUnion, exists_prop] at hx'
    obtain ⟨y, hy, hxy⟩ := hx'
    exact ⟨y, hy, hxy⟩
  · intro x hx
    simp only [preimage_iUnion, mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact hfW y (hsW hy) hxy

/-- `E` is quasi-separated in the subspace topology. -/
lemma quasiSeparatedSpace_E
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    QuasiSeparatedSpace E := by
  refine ⟨fun W₁ W₂ hW₁o hW₁c hW₂o hW₂c => ?_⟩
  obtain ⟨U₁, hU₁o, hU₁c, hW₁eq⟩ := exists_compactOpen_eq_preimage E W₁ hW₁o hW₁c
  obtain ⟨U₂, hU₂o, hU₂c, hW₂eq⟩ := exists_compactOpen_eq_preimage E W₂ hW₂o hW₂c
  have hinter : W₁ ∩ W₂ = (Subtype.val ⁻¹' (U₁ ∩ U₂) : Set E) := by
    rw [hW₁eq, hW₂eq]; ext; simp [Set.mem_inter_iff]
  rw [hinter]
  exact isCompact_E_inter_of_isCompact_isOpen E hE (U₁ ∩ U₂) (hU₁o.inter hU₂o)
    (QuasiSeparatedSpace.inter_isCompact U₁ U₂ hU₁o hU₁c hU₂o hU₂c)

/-- For a constructibly-closed `E ⊆ X` and `ξ ∉ E`, there is a finite
collection of subbasis elements whose intersection contains `ξ` and is
contained in `Eᶜ`. -/
lemma exists_finite_subbasis_subset_compl
    {X : Type*} [TopologicalSpace X]
    (E : Set X) (hE : @IsClosed X (constructibleTopology X) E)
    (ξ : X) (hξE : ξ ∉ E) :
    ∃ T : Set (Set X), T.Finite ∧ T ⊆ constructibleTopologySubbasis X ∧
        ξ ∈ ⋂₀ T ∧ ⋂₀ T ⊆ Eᶜ := by
  have hb : @IsTopologicalBasis X (constructibleTopology X)
      ((fun f => ⋂₀ f) ''
        {f : Set (Set X) | f.Finite ∧ f ⊆ constructibleTopologySubbasis X}) :=
    @TopologicalSpace.isTopologicalBasis_of_subbasis X (constructibleTopology X)
      (constructibleTopologySubbasis X) rfl
  obtain ⟨_, ⟨T, ⟨hTfin, hTsub⟩, rfl⟩, hξb, hbsub⟩ :=
    (@TopologicalSpace.IsTopologicalBasis.isOpen_iff X (constructibleTopology X) Eᶜ _ hb).mp
      ((@isOpen_compl_iff X E (constructibleTopology X)).mpr hE) ξ hξE
  exact ⟨T, hTfin, hTsub, hξb, hbsub⟩

/-- For a constructibly closed `E ⊆ X` and a generic point `ξ` of the closure of a subset
`S' ⊆ E`, the point `ξ` again lies in `E`. -/
lemma mem_E_of_isGenericPoint_closure
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X) (hE : @IsClosed X (constructibleTopology X) E)
    (S' : Set X) (hSE : S' ⊆ E)
    (ξ : X) (hξ : IsGenericPoint ξ (closure S')) :
    ξ ∈ E := by
  by_contra hξE
  obtain ⟨T, hTfin, hTsub, hξT, hTcompl⟩ :=
    exists_finite_subbasis_subset_compl E hE ξ hξE
  have hξcl : ξ ∈ closure S' := by
    have : ξ ∈ closure ({ξ} : Set X) := subset_closure rfl
    rwa [hξ] at this
  -- Split `T` into its open members and its closed (= compact-complement) members.
  have hTCsub : ∀ t ∈ T, ¬ IsOpen t → IsClosed t := fun t htT htNotOpen =>
    (hTsub htT).elim (fun hO => absurd hO.1 htNotOpen) (fun hC => hC.1)
  obtain ⟨s, hsW, hsS⟩ := mem_closure_iff.mp hξcl (⋂₀ {t ∈ T | IsOpen t})
    ((hTfin.subset fun _ h => h.1).isOpen_sInter fun _ ht => ht.2) fun t ht => hξT t ht.1
  have hsT : s ∈ ⋂₀ T := by
    intro t ht
    by_cases hO : IsOpen t
    · exact hsW t ⟨ht, hO⟩
    · have hclT : closure S' ⊆ t := by
        rw [← hξ]
        exact (hTCsub t ht hO).closure_subset_iff.mpr
          (singleton_subset_iff.mpr (hξT t ht))
      exact hclT (subset_closure hsS)
  exact hTcompl hsT (hSE hsS)

/-- `E` is quasi-sober in the subspace topology. -/
@[sga "4 IV 9.1.11" "partial"]
lemma quasiSober_E
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    QuasiSober E := by
  refine ⟨fun {S} hSi hSc => ?_⟩
  set S' : Set X := Subtype.val '' S with hS'def
  have hS'sub : S' ⊆ E := by rintro _ ⟨⟨x, hx⟩, _, rfl⟩; exact hx
  have hS'irr : IsIrreducible S' := hSi.image _ continuous_subtype_val.continuousOn
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hS'irr.closure isClosed_closure
  have hξE : ξ ∈ E := mem_E_of_isGenericPoint_closure E hE S' hS'sub ξ hξ
  refine ⟨⟨ξ, hξE⟩, ?_⟩
  rw [isGenericPoint_def]
  obtain ⟨T, hT, hT_eq⟩ :=
    (isClosed_induced_iff (f := (Subtype.val : E → X))).mp hSc
  have hS'_eq_inter : S' = E ∩ T := by
    rw [hS'def, ← hT_eq, Subtype.image_preimage_coe]
  have hFT : closure S' ⊆ T :=
    hT.closure_subset_iff.mpr (by rw [hS'_eq_inter]; exact inter_subset_right)
  have hclosed_eq : closure (Subtype.val '' {(⟨ξ, hξE⟩ : E)}) = closure ({ξ} : Set X) := by
    congr 1; simp
  ext a
  rw [closure_subtype, hclosed_eq, hξ]
  constructor
  · intro ha
    have hmem : a ∈ Subtype.val ⁻¹' T := hFT ha
    rwa [hT_eq] at hmem
  · intro ha
    exact subset_closure (by rw [hS'def]; exact ⟨a, ha, rfl⟩)

/-- **Stacks 0902**.
For a spectral space `X` and a subset `E ⊆ X` closed in the constructible topology on `X`, the set
`E` with the subspace topology inherited from `X` is a spectral space. -/
@[stacks 0902, sga "4 IV 9.1.11" "partial"]
theorem spectralSpace_of_isClosed_constructibleTopology
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    (E : Set X)
    (hE : @IsClosed X (constructibleTopology X) E) :
    SpectralSpace E :=
  @SpectralSpace.mk _ _ _
    (compactSpace_E E hE)
    (quasiSober_E E hE)
    (quasiSeparatedSpace_E E hE)
    (prespectralSpace_E E hE)



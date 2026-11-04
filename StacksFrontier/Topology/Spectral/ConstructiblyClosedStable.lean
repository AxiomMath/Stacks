module

public import Mathlib.Topology.Spectral.ConstructibleTopology
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibly closed sets stable under specialization

Let `X` be a spectral space. Every point of the closure of a constructibly closed set `E` is a
specialization of a point of `E`: the sets `U ∩ E`, for `U` a quasi-compact open neighbourhood of
the point, are constructibly closed with the finite intersection property, so quasi-compactness
of the constructible topology gives a point in all of them. Consequently a constructibly closed
set stable under specialization is closed, and a constructibly open set stable under
generalization is open.

## Main results

* `mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology`: a point of `closure E`
  is a specialization of a point of `E`.
* `isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization`: a constructibly
  closed set stable under specialization is closed.
* `isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization`: a constructibly open set
  stable under generalization is open.
* `specializes_and_isClosed_and_isOpen_of_constructible`: the three statements combined.
-/

@[expose] public section

open Topology TopologicalSpace Set Filter

variable {X : Type*} [TopologicalSpace X]

/-- In a prespectral space, `y ⤳ x` iff every compact open neighbourhood of
`x` contains `y`. -/
private lemma specializes_iff_forall_isCompact_isOpen [PrespectralSpace X] {x y : X} :
    y ⤳ x ↔ ∀ U : Set X, IsOpen U → IsCompact U → x ∈ U → y ∈ U := by
  rw [(PrespectralSpace.isTopologicalBasis.nhds_hasBasis).specializes_iff]
  exact ⟨fun H U hU hcU hxU => H U ⟨⟨hU, hcU⟩, hxU⟩,
    fun H U ⟨⟨hUo, hUc⟩, hxU⟩ => H U hUo hUc hxU⟩

/-- A compact open `U ⊆ X` is closed in the constructible topology, i.e. its
complement is open in the constructible topology. -/
private lemma isClosed_constructibleTopology_of_isCompact_isOpen
    {U : Set X} (hUo : IsOpen U) (hUc : IsCompact U) :
    IsClosed[constructibleTopology X] U := by
  rw [← @isOpen_compl_iff _ U (constructibleTopology X)]
  refine IsCompact.isOpen_constructibleTopology_of_isClosed ?_ hUo.isClosed_compl
  simpa using hUc

/-- Given `x ∈ closure E` with `E` closed in the constructible topology of a spectral space, there
is a `y ∈ E` with `y ⤳ x`. -/
private lemma exists_specializes_of_mem_closure
    [SpectralSpace X] {E : Set X}
    (hE : IsClosed[constructibleTopology X] E)
    {x : X} (hxE : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := by
  -- The intersections with `E` of the compact open neighbourhoods of `x`.
  let 𝓕 : Set (Set X) := (fun U => U ∩ E) '' { U : Set X | IsOpen U ∧ IsCompact U ∧ x ∈ U }
  -- (a) Each member of `𝓕` is closed in the constructible topology.
  have h_closed_ctop : ∀ S ∈ 𝓕, IsClosed[constructibleTopology X] S := by
    rintro _ ⟨U, ⟨hUo, hUc, -⟩, rfl⟩
    exact @IsClosed.inter X U E (constructibleTopology X)
      (isClosed_constructibleTopology_of_isCompact_isOpen hUo hUc) hE
  -- (b) Finite intersection property of `𝓕`: for each member of a finite subfamily choose a
  -- compact open `φ S` with `φ S ∩ E = S`; their intersection is an open neighbourhood of `x`,
  -- so it meets `E`.
  have h_finite_inter :
      ∀ A ⊆ 𝓕, A.Finite → (⋂₀ A).Nonempty := by
    intro A hAsub hAfin
    classical
    have h : ∀ S ∈ A, ∃ U : Set X, IsOpen U ∧ IsCompact U ∧ x ∈ U ∧ U ∩ E = S :=
      fun S hS => by
        obtain ⟨U, ⟨hUo, hUc, hxU⟩, hUS⟩ := hAsub hS
        exact ⟨U, hUo, hUc, hxU, hUS⟩
    choose! φ hφ_open hφ_compact hφ_mem hφ_eq using h
    obtain ⟨z, hzV, hzE⟩ := mem_closure_iff.mp hxE (⋂ S ∈ A, φ S)
      (hAfin.isOpen_biInter hφ_open) (mem_iInter₂.mpr hφ_mem)
    exact ⟨z, Set.mem_sInter.mpr fun S hS =>
      hφ_eq S hS ▸ ⟨mem_iInter₂.mp hzV S hS, hzE⟩⟩
  -- (c) Quasi-compactness of the constructible topology gives a point `y` in every member of `𝓕`.
  have hcs : @CompactSpace X (constructibleTopology X) :=
    @Function.Surjective.compactSpace (WithConstructibleTopology X) X _
      (constructibleTopology X) _
      (WithTopology.continuous_ofTopology (constructibleTopology X)) _
      (WithTopology.ofTopology_surjective (constructibleTopology X))
  obtain ⟨y, hy⟩ := @CompactSpace.nonempty_sInter X (constructibleTopology X) hcs 𝓕
    h_closed_ctop h_finite_inter
  -- `univ ∩ E ∈ 𝓕` because `univ` is a compact open neighbourhood of `x`; likewise for any
  -- compact open neighbourhood `U`, which gives `y ⤳ x`.
  exact ⟨y, (Set.mem_sInter.mp hy (Set.univ ∩ E)
      ⟨Set.univ, ⟨isOpen_univ, CompactSpace.isCompact_univ, Set.mem_univ x⟩, rfl⟩).2,
    specializes_iff_forall_isCompact_isOpen.mpr fun U hUo hUc hxU =>
      (Set.mem_sInter.mp hy (U ∩ E) ⟨U, ⟨hUo, hUc, hxU⟩, rfl⟩).1⟩

/-- If `X` is a spectral space and `E ⊆ X` is closed in the constructible topology, then every
point of `closure E` is a specialization of some point of `E`. -/
theorem mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology
    [SpectralSpace X] {E : Set X} (hE : IsClosed[constructibleTopology X] E)
    {x : X} (hx : x ∈ closure E) : ∃ y ∈ E, y ⤳ x :=
  exists_specializes_of_mem_closure hE hx

/-- If `X` is a spectral space and `E ⊆ X` is closed in the constructible topology and stable
under specialization, then `E` is closed in `X`. -/
@[sga "3 XV 3.3" "partial"]
theorem isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
    [SpectralSpace X] {E : Set X} (hE : IsClosed[constructibleTopology X] E)
    (hE_spec : StableUnderSpecialization E) : IsClosed E := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨y, hyE, hyx⟩ := exists_specializes_of_mem_closure hE hx
  exact hE_spec hyx hyE

/-- If `X` is a spectral space and `E' ⊆ X` is open in the constructible topology and stable
under generalization, then `E'` is open in `X`. -/
@[sga "1 IV 6.4" "special case", sga "3 XV 3.3" "partial", sga "3 XV 6.6" "more general"]
theorem isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization
    [SpectralSpace X] {E' : Set X} (hE' : IsOpen[constructibleTopology X] E')
    (hE'_gen : StableUnderGeneralization E') : IsOpen E' := by
  rw [← isClosed_compl_iff]
  refine isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization ?_ hE'_gen.compl
  -- `E'ᶜ` is closed in the constructible topology because `E'` is open in it.
  rw [← @isOpen_compl_iff _ E'ᶜ (constructibleTopology X)]
  simpa using hE'

/-- **Stacks 0903**.
For a spectral space `X`: a point of the closure of a constructibly closed set is a specialization
of a point of that set; a constructibly closed set stable under specialization is closed; and a
constructibly open set stable under generalization is open. -/
@[stacks 0903]
theorem specializes_and_isClosed_and_isOpen_of_constructible [SpectralSpace X] :
    (∀ {E : Set X}, IsClosed[constructibleTopology X] E →
        ∀ {x : X}, x ∈ closure E → ∃ y ∈ E, y ⤳ x) ∧
      (∀ {E : Set X}, IsClosed[constructibleTopology X] E →
        StableUnderSpecialization E → IsClosed E) ∧
      (∀ {E' : Set X}, IsOpen[constructibleTopology X] E' →
        StableUnderGeneralization E' → IsOpen E') :=
  ⟨fun hE _ hx => mem_closure_iff_exists_specializes_of_isClosed_constructibleTopology hE hx,
    fun hE hE' => isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization hE hE',
    fun hE hE' => isOpen_of_isOpen_constructibleTopology_of_stableUnderGeneralization hE hE'⟩

end

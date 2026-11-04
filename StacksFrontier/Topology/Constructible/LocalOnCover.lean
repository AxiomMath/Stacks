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
public import StacksFrontier.Topology.Constructible.MeetConstructible
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibility is local on a finite constructible cover

Let `X` be a topological space whose topology has a basis of quasi-compact opens, and let
`E₁, …, Eₘ` be a finite family of constructible subsets covering `X`. A subset `S ⊆ X` is
constructible in `X` if and only if its preimage in each `Eⱼ` is constructible in `Eⱼ`. The
two directions come from pulling a constructible set back along the inclusion of a
constructible subspace and pushing one forward along it.

## Main results

* `exists_open_retrocompact_decomposition`: every constructible set is a finite union of
  differences `U i \ V i` of retrocompact open sets.
* `stacks09YI_preimage`: the preimage of a constructible set in a constructible subspace is
  constructible.
* `inclusion_preimage_isConstructible`: constructibility is preserved by pulling back along
  the inclusion of one constructible subset into another.
* `stacks09YJ_image`: the image of a constructible set of a constructible subspace is
  constructible in `X`.
* `isConstructible_iff_isConstructible_preimage`: constructibility is detected on a finite
  constructible cover.
-/

@[expose] public section

open Set Topology TopologicalSpace


variable {X : Type*} [TopologicalSpace X]

/-! ### Constructible sets: normal form and basic properties -/

/-- Every constructible set is a finite union of differences of open retrocompact sets. -/
@[ega "0 9.1.3" "necessity", sga "3 VIB 3.7" "(ii)"]
lemma exists_open_retrocompact_decomposition
    {E : Set X} (hE : IsConstructible E) :
    ∃ (n : ℕ) (U V : Fin n → Set X),
      (∀ i, IsOpen (U i) ∧ IsRetrocompact (U i)) ∧
      (∀ i, IsOpen (V i) ∧ IsRetrocompact (V i)) ∧
      E = ⋃ i, (U i \ V i) := by
  set S := { U : Set X | IsOpen U ∧ IsRetrocompact U }
  have h_bot : (⊥ : Set X) ∈ S := ⟨isOpen_empty, IsRetrocompact.empty⟩
  have h_top : (⊤ : Set X) ∈ S := ⟨isOpen_univ, IsRetrocompact.univ⟩
  have hsublat : IsSublattice S :=
    ⟨fun _ ⟨haOpen, haRetro⟩ _ ⟨hbOpen, hbRetro⟩ => ⟨haOpen.union hbOpen, haRetro.union hbRetro⟩,
     fun _ ⟨haOpen, haRetro⟩ _ ⟨hbOpen, hbRetro⟩ =>
       ⟨haOpen.inter hbOpen, haRetro.inter_isOpen hbRetro hbOpen⟩⟩
  have hE' : E ∈ BooleanSubalgebra.closure S := hE
  rw [BooleanSubalgebra.mem_closure_iff_sup_sdiff hsublat h_bot h_top] at hE'
  obtain ⟨t, ht⟩ := hE'
  refine ⟨t.card,
      fun i => ((t.equivFin.symm i : ↥S × ↥S).1 : Set X),
      fun i => ((t.equivFin.symm i : ↥S × ↥S).2 : Set X),
      fun i => (t.equivFin.symm i : ↥S × ↥S).1.property,
      fun i => (t.equivFin.symm i : ↥S × ↥S).2.property, ?_⟩
  rw [ht, Finset.sup_eq_iSup,
      show (⨆ a ∈ t, (↑a.1 \ ↑a.2 : Set X))
          = ⨆ a : t, ((a : ↥S × ↥S).1 : Set X) \ ((a : ↥S × ↥S).2 : Set X)
        from by simp [iSup_subtype]]
  exact (Equiv.iSup_congr t.equivFin.symm (fun _ => rfl)).symm

/-! ### Stacks 09YI: pullback to a constructible subset -/

/-- **Stacks 09YI.** The preimage of a constructible set in `X` along the inclusion
of a constructible subset `E` is constructible in `E`. -/
@[ega "0 9.2.1" "partial", sga "3 VIB 4.2" "partial"]
lemma stacks09YI_preimage [PrespectralSpace X] {E : Set X}
    (hE : IsConstructible E) {S : Set X} (hS : IsConstructible S) :
    IsConstructible ((Subtype.val : ↥E → X) ⁻¹' S) :=
  isConstructible_preimage_subtypeVal_of_isConstructible hE hS

/-! ### Pullback along inclusions of constructible subsets -/

omit [TopologicalSpace X] in
/-- A set-theoretic identity: the image of `F ⊆ E` intersected with a subset `E' ⊆ E` is
the image of the inclusion-preimage of `F`. -/
lemma image_inter_eq_image_inclusion_preimage
    {E E' : Set X} (h_sub : E' ⊆ E) (F : Set ↥E) :
    ((Subtype.val : ↥E → X) '' F) ∩ E'
      = (Subtype.val : ↥E' → X) '' (Set.inclusion h_sub ⁻¹' F) := by
  ext x
  constructor
  · rintro ⟨⟨⟨y, _⟩, hyF, rfl⟩, hxE'⟩
    exact ⟨⟨y, hxE'⟩, hyF, rfl⟩
  · rintro ⟨⟨y, hyE'⟩, hyF, rfl⟩
    exact ⟨⟨⟨y, h_sub hyE'⟩, hyF, rfl⟩, hyE'⟩

/-- A constructible subset of a prespectral space is itself prespectral. -/
private lemma prespectralSpace_subtype_of_isConstructible [PrespectralSpace X]
    {E : Set X} (hE : IsConstructible E) : PrespectralSpace ↥E := by
  refine PrespectralSpace.mk ?_
  have hB_base : IsTopologicalBasis
      ((preimage (Subtype.val : ↥E → X)) '' {U : Set X | IsOpen U ∧ IsCompact U}) :=
    isTopologicalBasis_subtype PrespectralSpace.isTopologicalBasis E
  have hE_retro : IsRetrocompact E := IsRetrocompact_of_IsConstructible hE
  refine IsTopologicalBasis.of_isOpen_of_subset
    (s' := {V : Set ↥E | IsOpen V ∧ IsCompact V}) (fun _ ⟨h, _⟩ => h) hB_base ?_
  rintro _ ⟨U, ⟨hUopen, hUcompact⟩, rfl⟩
  refine ⟨continuous_subtype_val.isOpen_preimage U hUopen, ?_⟩
  rw [IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe]
  exact hE_retro hUcompact hUopen

/-- **Pullback constructibility along subspace inclusion.** If `E' ⊆ E` are both
constructible and `F ⊆ E` is constructible in `E`, then `F` pulled back to `E'` along
the inclusion is constructible in `E'`. -/
@[ega "0 9.2.1" "partial", sga "3 VIB 4.2" "partial"]
lemma inclusion_preimage_isConstructible [PrespectralSpace X]
    {E E' : Set X} (hE : IsConstructible E) (hE' : IsConstructible E')
    (h_sub : E' ⊆ E)
    {F : Set ↥E} (hF : IsConstructible F) :
    IsConstructible (Set.inclusion h_sub ⁻¹' F) := by
  have : PrespectralSpace ↥E := prespectralSpace_subtype_of_isConstructible hE
  -- Identify `E'` inside `E` with the subspace `Subtype.val ⁻¹' E'` via a homeomorphism.
  let φ : ↥E' ≃ₜ ↥((Subtype.val : ↥E → X) ⁻¹' E') :=
    { toFun := fun y => ⟨⟨y.1, h_sub y.2⟩, y.2⟩
      invFun := fun y => ⟨y.val.val, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  refine IsConstructible.preimage (continuous_inclusion h_sub) (fun V hVopen hVrc => ?_) hF
  -- Retrocompactness of `V` pulled back through `E` transfers to `E'` via `φ`.
  have hpull := isRetrocompact_preimage_subtypeVal
    (IsRetrocompact_of_IsConstructible (stacks09YI_preimage hE hE')) hVopen hVrc
  intro W hWc hWo
  have hPre : IsCompact (φ ⁻¹' ((Subtype.val ⁻¹' V) ∩ (φ '' W))) :=
    (Homeomorph.isCompact_preimage φ).mpr
      (hpull ((Homeomorph.isCompact_image φ).mpr hWc)
        ((Homeomorph.isOpen_image φ).mpr hWo))
  rwa [Set.preimage_inter, φ.preimage_image] at hPre

/-! ### Stacks 09YJ: pushforward along inclusion of a constructible subset -/

/-- **Base case of Stacks 09YJ.** For open retrocompact `U`, `V`, the image of a
constructible set in `U \ V` is constructible in `X`. -/
lemma base_case_diff_image [PrespectralSpace X]
    {U V : Set X} (hU_open : IsOpen U) (hU_rc : IsRetrocompact U)
    (hV_open : IsOpen V) (hV_rc : IsRetrocompact V)
    {F : Set ↥(U \ V)} (hF : IsConstructible F) :
    IsConstructible ((Subtype.val : ↥(U \ V) → X) '' F) := by
  have h_sub : U \ V ⊆ U := Set.sdiff_subset
  rw [show (Subtype.val : ↥(U \ V) → X) '' F =
      (Subtype.val : ↥U → X) '' (Set.inclusion h_sub '' F) by rw [Set.image_image]]
  refine IsConstructible.image_of_isOpenEmbedding hU_open.isOpenEmbedding_subtypeVal
    (Subtype.range_val ▸ hU_rc) ?_
  have hrange : range (Set.inclusion h_sub) = ((Subtype.val : ↥U → X) ⁻¹' V)ᶜ := by
    ext ⟨x, _⟩
    simp
  refine IsConstructible.image_of_isClosedEmbedding
    ⟨IsEmbedding.inclusion h_sub,
      hrange ▸ (hV_open.preimage continuous_subtype_val).isClosed_compl⟩ ?_ hF
  rw [hrange, compl_compl]
  exact isRetrocompact_preimage_subtypeVal hU_rc hV_open hV_rc

/-- **Stacks 09YJ.** The image of a constructible set in a constructible subspace `E`
along the inclusion is constructible in `X`. -/
@[ega "0 9.1.8" "(ii), sufficiency", ega "0 9.2.1" "partial", sga "3 VIB 3.7" "partial"]
lemma stacks09YJ_image [PrespectralSpace X] {E : Set X}
    (hE : IsConstructible E) {F : Set ↥E} (hF : IsConstructible F) :
    IsConstructible ((Subtype.val : ↥E → X) '' F) := by
  obtain ⟨n, U, V, hU, hV, hE_eq⟩ := exists_open_retrocompact_decomposition hE
  rw [show (Subtype.val : ↥E → X) '' F
        = ⋃ i, ((Subtype.val : ↥E → X) '' F) ∩ (U i \ V i) by
      rw [← Set.inter_iUnion, ← hE_eq,
        Set.inter_eq_left.mpr (Subtype.coe_image_subset E F)]]
  refine IsConstructible.iUnion fun i => ?_
  obtain ⟨hUi_open, hUi_rc⟩ := hU i
  obtain ⟨hVi_open, hVi_rc⟩ := hV i
  have hEi_sub : (U i \ V i) ⊆ E := hE_eq ▸ subset_iUnion (fun j => U j \ V j) i
  have hEi_cons : IsConstructible (U i \ V i) :=
    (hUi_rc.isConstructible hUi_open).sdiff (hVi_rc.isConstructible hVi_open)
  rw [image_inter_eq_image_inclusion_preimage hEi_sub F]
  exact base_case_diff_image hUi_open hUi_rc hVi_open hVi_rc
    (inclusion_preimage_isConstructible hE hEi_cons hEi_sub hF)

/-! ### Main theorem -/

/-- **Stacks 09YK**.
For `X` a topological space whose topology has a basis of quasi-compact opens and
`E₁, …, Eₘ` a finite family of constructible subsets covering `X`, a subset `S ⊆ X` is
constructible in `X` if and only if its preimage in each `Eⱼ` is constructible in `Eⱼ`. -/
@[stacks 09YK, ega "0 9.1.9" "special case", ega "0 9.2.1" "more general"]
theorem isConstructible_iff_isConstructible_preimage
    (h_basis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U })
    {m : ℕ} (E : Fin m → Set X)
    (hE_cons : ∀ j, IsConstructible (E j))
    (hcover : (⋃ j, E j) = Set.univ)
    (S : Set X) :
    IsConstructible S ↔
      ∀ j, IsConstructible ((Subtype.val : ↥(E j) → X) ⁻¹' S) := by
  have : PrespectralSpace X := PrespectralSpace.mk h_basis
  refine ⟨fun hS j => stacks09YI_preimage (hE_cons j) hS, fun h => ?_⟩
  rw [show S = ⋃ j, (Subtype.val : ↥(E j) → X) ''
      ((Subtype.val : ↥(E j) → X) ⁻¹' S) by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
    refine ⟨fun hxS => ?_, fun ⟨_, ⟨_, _⟩, hyS, rfl⟩ => hyS⟩
    obtain ⟨j, hxEj⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact ⟨j, ⟨x, hxEj⟩, hxS, rfl⟩]
  exact IsConstructible.iUnion (fun j => stacks09YJ_image (hE_cons j) (h j))



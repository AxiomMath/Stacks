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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A constructible subset of a constructible set is constructible

Let `X` be a topological space with a basis of quasi-compact opens. Let `E ⊆ X` be
constructible in `X`, and let `F ⊆ E` be constructible in the topological subspace `E`. Then
`F`, viewed as a subset of `X` via the inclusion `E ↪ X`, is constructible in `X`.

## Main definitions

* `IsConstructibleSet`: a finite union `⋃ i, U i ∩ (V i)ᶜ` of differences of retrocompact
  opens.

## Main results

* `isConstructibleSet_iff_isConstructible`: `IsConstructibleSet` agrees with Mathlib's
  `Topology.IsConstructible`.
* `isConstructible_preimage_inclusion`: for `S ⊆ E` with `S` constructible and `E`
  retrocompact in a prespectral space, the restriction to `↥S` of a constructible subset of
  `↥E` is constructible.
* `isConstructibleSet_of_isConstructibleSet_in_constructible`: the image in `X` of a
  constructible subset of a constructible subset `E ⊆ X` is constructible.
-/

@[expose] public section

open Set Topology TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A subset `E ⊆ X` is *constructible* in the Stacks-Project sense if it is a
finite indexed union `⋃ i, U i ∩ (V i)ᶜ`, where each `U i, V i` is open and
retrocompact in `X`. -/
@[ega "IV 10.1.1", ega "IV 8.3.9", sga "3 VIB 3.7"]
def IsConstructibleSet (E : Set X) : Prop :=
  ∃ (n : ℕ) (U V : Fin n → Set X),
    (∀ i, IsOpen (U i)) ∧ (∀ i, IsRetrocompact (U i)) ∧
    (∀ i, IsOpen (V i)) ∧ (∀ i, IsRetrocompact (V i)) ∧
    E = ⋃ i, U i ∩ (V i)ᶜ

/-! ### Equivalence with Mathlib's `Topology.IsConstructible` -/

/-- The difference `U ∩ Vᶜ` of two retrocompact open sets is constructible. -/
lemma isConstructible_inter_compl {U V : Set X} (hUopen : IsOpen U) (hUretro : IsRetrocompact U)
    (hVopen : IsOpen V) (hVretro : IsRetrocompact V) : IsConstructible (U ∩ Vᶜ) := by
  rw [← Set.sdiff_eq]
  exact (hUretro.isConstructible hUopen).sdiff (hVretro.isConstructible hVopen)

/-- A finite union of differences `U i ∩ (V i)ᶜ` of retrocompact open sets is constructible. -/
@[ega "0 9.1.3" "sufficiency", sga "3 VIB 3.7" "(ii)"]
lemma isConstructible_iUnion_inter_compl {n : ℕ} {U V : Fin n → Set X}
    (hUopen : ∀ i, IsOpen (U i)) (hUretro : ∀ i, IsRetrocompact (U i))
    (hVopen : ∀ i, IsOpen (V i)) (hVretro : ∀ i, IsRetrocompact (V i)) :
    IsConstructible (⋃ i, U i ∩ (V i)ᶜ) :=
  IsConstructible.iUnion fun i =>
    isConstructible_inter_compl (hUopen i) (hUretro i) (hVopen i) (hVretro i)

/-- An `IsConstructibleSet` (finite union of open-retrocompact differences) is
a `Topology.IsConstructible` set. -/
@[ega "0 9.1.3" "sufficiency"]
lemma isConstructible_of_isConstructibleSet {E : Set X}
    (hE : IsConstructibleSet E) : IsConstructible E := by
  obtain ⟨n, U, V, hUo, hUr, hVo, hVr, hEeq⟩ := hE
  rw [hEeq]
  exact isConstructible_iUnion_inter_compl hUo hUr hVo hVr

/-- Union of two `IsConstructibleSet`s is `IsConstructibleSet`. -/
lemma IsConstructibleSet.union {A B : Set X}
    (hA : IsConstructibleSet A) (hB : IsConstructibleSet B) :
    IsConstructibleSet (A ∪ B) := by
  obtain ⟨nA, UA, VA, hUAo, hUAr, hVAo, hVAr, hAeq⟩ := hA
  obtain ⟨nB, UB, VB, hUBo, hUBr, hVBo, hVBr, hBeq⟩ := hB
  refine ⟨nA + nB, Fin.append UA UB, Fin.append VA VB, ?_, ?_, ?_, ?_, ?_⟩
  iterate 4 intro k; induction k using Fin.addCases <;> simp [*]
  · rw [hAeq, hBeq]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff]
    refine ⟨fun h => h.elim
      (fun ⟨i, hi⟩ => ⟨Fin.castAdd nB i, by simpa [Fin.append_left] using hi⟩)
      (fun ⟨j, hj⟩ => ⟨Fin.natAdd nA j, by simpa [Fin.append_right] using hj⟩), ?_⟩
    rintro ⟨k, hk⟩
    induction k using Fin.addCases with
    | left i => exact Or.inl ⟨i, by simpa [Fin.append_left] using hk⟩
    | right j => exact Or.inr ⟨j, by simpa [Fin.append_right] using hk⟩

/-- A `Topology.IsConstructible` set is an `IsConstructibleSet` (a finite union
of open-retrocompact differences `U \ V`). -/
@[ega "0 9.1.3" "necessity"]
lemma isConstructibleSet_of_isConstructible {E : Set X}
    (hE : IsConstructible E) : IsConstructibleSet E := by
  induction E, hE using BooleanSubalgebra.closure_sdiff_sup_induction
    (isSublattice := isSublattice_isOpen_and_isRetrocompact)
    (bot_mem := bot_mem_isOpen_and_isRetrocompact)
    (top_mem := top_mem_isOpen_and_isRetrocompact) with
  | sdiff U hU V hV =>
    obtain ⟨hUopen, hUretro⟩ := hU
    obtain ⟨hVopen, hVretro⟩ := hV
    refine ⟨1, (fun _ => U), (fun _ => V),
      fun _ => hUopen, fun _ => hUretro, fun _ => hVopen, fun _ => hVretro, ?_⟩
    ext x
    simp [Set.mem_inter_iff, Set.mem_compl_iff]
  | sup s _ t _ hs ht => exact hs.union ht

/-- The two notions of constructibility agree. -/
@[ega "0 9.1.3"]
lemma isConstructibleSet_iff_isConstructible {E : Set X} :
    IsConstructibleSet E ↔ IsConstructible E :=
  ⟨isConstructible_of_isConstructibleSet, isConstructibleSet_of_isConstructible⟩

/-! ### Constructible subsets of subspaces -/

omit [TopologicalSpace X] in
/-- If `A` and `B` are subsets of `E` covering it, the image in `X` of `F : Set ↥E` is the
union of the images of the restrictions of `F` to `↥A` and to `↥B`. -/
lemma image_val_eq_union_image_val_inclusion {A B E : Set X} (hA : A ⊆ E) (hB : B ⊆ E)
    (hcover : E ⊆ A ∪ B) (F : Set ↥E) :
    (Subtype.val : ↥E → X) '' F =
      (Subtype.val : ↥A → X) '' (Set.inclusion hA ⁻¹' F) ∪
        (Subtype.val : ↥B → X) '' (Set.inclusion hB ⁻¹' F) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨y, hyF, rfl⟩
    rcases hcover y.2 with hy | hy
    · exact Or.inl ⟨⟨(y : X), hy⟩, hyF, rfl⟩
    · exact Or.inr ⟨⟨(y : X), hy⟩, hyF, rfl⟩
  · rintro _ (⟨z, hzF, rfl⟩ | ⟨z, hzF, rfl⟩)
    · exact ⟨Set.inclusion hA z, hzF, rfl⟩
    · exact ⟨Set.inclusion hB z, hzF, rfl⟩

/-- If `U` and `V` are retrocompact open sets and
`E = U ∩ Vᶜ`, then the image in `X` of a constructible subset of `↥E` is constructible. -/
lemma isConstructible_image_val_of_eq_inter_compl {U V E : Set X}
    (hUopen : IsOpen U) (hUretro : IsRetrocompact U)
    (hVopen : IsOpen V) (hVretro : IsRetrocompact V) (hE : E = U ∩ Vᶜ)
    {F : Set ↥E} (hF : IsConstructible F) :
    IsConstructible ((Subtype.val : ↥E → X) '' F) := by
  subst hE
  have hsub : U ∩ Vᶜ ⊆ U := fun _ hx => hx.1
  have hpre : (Subtype.val : ↥U → X) ⁻¹' (U ∩ Vᶜ) = (Subtype.val : ↥U → X) ⁻¹' Vᶜ :=
    Set.ext fun u => by simp
  have hUemb : IsOpenEmbedding (Subtype.val : ↥U → X) := hUopen.isOpenEmbedding_subtypeVal
  have hrange : (range (Set.inclusion hsub))ᶜ = (Subtype.val : ↥U → X) ⁻¹' V := by
    rw [Set.range_inclusion, show {x : ↥U | (x : X) ∈ U ∩ Vᶜ} = _ from hpre]
    simp
  have himg : IsConstructible (Set.inclusion hsub '' F) :=
    hF.image_of_isClosedEmbedding (.inclusion hsub (hpre ▸ hVopen.isClosed_compl.preimage
      continuous_subtype_val)) (by rw [hrange]; exact hVretro.preimage_of_isOpenEmbedding hUemb)
  rw [show (Subtype.val : ↥(U ∩ Vᶜ) → X) '' F
      = (Subtype.val : ↥U → X) '' (Set.inclusion hsub '' F) from by rw [← Set.image_comp]; rfl]
  exact himg.image_of_isOpenEmbedding hUemb (by simpa [Subtype.range_coe] using hUretro)

/-- In a prespectral space, the preimage of a
constructible set under `Subtype.val : E → X` (with `E` retrocompact) is
constructible in `↥E`. -/
private lemma isConstructible_preimage_subtypeVal
    [PrespectralSpace X] {E : Set X} (hE_retro : IsRetrocompact E)
    {E' : Set X} (hE' : IsConstructible E') :
    IsConstructible ((Subtype.val : E → X) ⁻¹' E') :=
  hE'.preimage continuous_subtype_val
    (fun _V hVopen hVcomp ↦ isRetrocompact_preimage_subtypeVal hE_retro hVopen hVcomp)

/-- The subspace of a prespectral space `X` along a retrocompact `E` is also
prespectral. -/
private lemma prespectralSpace_subtype_of_isRetrocompact
    [PrespectralSpace X] {E : Set X} (hE_retro : IsRetrocompact E) :
    PrespectralSpace ↥E := by
  have hB_basis : IsTopologicalBasis ({V : Set X | IsOpen V ∧ IsCompact V}) :=
    PrespectralSpace.isTopologicalBasis
  refine PrespectralSpace.of_isTopologicalBasis
    (B := (fun V : Set X => (Subtype.val : ↥E → X) ⁻¹' V) ''
      {V : Set X | IsOpen V ∧ IsCompact V}) ?_ ?_
  · exact IsInducing.isTopologicalBasis IsInducing.subtypeVal hB_basis
  · rintro W ⟨V, ⟨hVopen, hVretro⟩, rfl⟩
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
    exact hE_retro hVretro hVopen

/-- For `S ⊆ T ⊆ X`, the homeomorphism `↥S ≃ₜ ↥((Subtype.val : ↥T → X)⁻¹' S)`. -/
private def subspaceHomeo {T : Set X} {S : Set X} (hST : S ⊆ T) :
    ↥S ≃ₜ ↥((Subtype.val : ↥T → X) ⁻¹' S) where
  toFun x := ⟨⟨(x : X), hST x.2⟩, x.2⟩
  invFun y := ⟨(y.1 : X), y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.mpr (continuous_induced_rng.mpr continuous_subtype_val)
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- Let `S ⊆ E` be subsets of a prespectral
space with `S` constructible in `X` and `E` retrocompact. Then the restriction to `↥S` of a
constructible subset of `↥E` is constructible. -/
lemma isConstructible_preimage_inclusion [PrespectralSpace X] {E S : Set X}
    (hEretro : IsRetrocompact E) (hScons : IsConstructible S) (hSE : S ⊆ E)
    {F : Set ↥E} (hF : IsConstructible F) :
    IsConstructible (Set.inclusion hSE ⁻¹' F) := by
  have : PrespectralSpace ↥E := prespectralSpace_subtype_of_isRetrocompact hEretro
  have hpre : IsConstructible
      ((Subtype.val : ↥((Subtype.val : ↥E → X) ⁻¹' S) → ↥E) ⁻¹' F) :=
    isConstructible_preimage_subtypeVal (X := ↥E)
      (IsRetrocompact_of_IsConstructible
        (isConstructible_preimage_subtypeVal hEretro hScons)) hF
  rw [show Set.inclusion hSE ⁻¹' F = subspaceHomeo hSE ⁻¹'
        ((Subtype.val : ↥((Subtype.val : ↥E → X) ⁻¹' S) → ↥E) ⁻¹' F) from
      Set.ext fun _ => Iff.rfl]
  exact hpre.preimage_of_isOpenEmbedding (subspaceHomeo hSE).isOpenEmbedding

/-! ### Images of constructible subsets -/

/-- Let `E = E₁ ∪ E₂` with `E₁ = U ∩ Vᶜ` for retrocompact opens `U` and `V`, and `E₂`
constructible such that the image in `X` of every constructible subset of `↥E₂` is
constructible. Then the image in `X` of a constructible subset of `↥E` is constructible. -/
lemma isConstructible_image_val_union [PrespectralSpace X] {U V E₁ E₂ E : Set X}
    (hUopen : IsOpen U) (hUretro : IsRetrocompact U)
    (hVopen : IsOpen V) (hVretro : IsRetrocompact V) (hE₁ : E₁ = U ∩ Vᶜ)
    (hE₂ : IsConstructible E₂)
    (himg₂ : ∀ G : Set ↥E₂, IsConstructible G → IsConstructible ((Subtype.val : ↥E₂ → X) '' G))
    (hE : E = E₁ ∪ E₂) (F : Set ↥E) (hF : IsConstructible F) :
    IsConstructible ((Subtype.val : ↥E → X) '' F) := by
  have hsub₁ : E₁ ⊆ E := by rw [hE]; exact Set.subset_union_left
  have hsub₂ : E₂ ⊆ E := by rw [hE]; exact Set.subset_union_right
  have hE₁cons : IsConstructible E₁ := by
    rw [hE₁]; exact isConstructible_inter_compl hUopen hUretro hVopen hVretro
  have hEretro : IsRetrocompact E :=
    IsRetrocompact_of_IsConstructible (by rw [hE]; exact hE₁cons.union hE₂)
  rw [image_val_eq_union_image_val_inclusion hsub₁ hsub₂ hE.subset F]
  exact .union
    (isConstructible_image_val_of_eq_inter_compl hUopen hUretro hVopen hVretro hE₁
      (isConstructible_preimage_inclusion hEretro hE₁cons hsub₁ hF))
    (himg₂ _ (isConstructible_preimage_inclusion hEretro hE₂ hsub₂ hF))

/-- If `E = ⋃ i, U i ∩ (V i)ᶜ` is a finite union of differences of retrocompact opens, then the
image in `X` of a constructible subset of `↥E` is constructible. -/
private lemma isConstructible_image_aux [PrespectralSpace X] :
    ∀ (n : ℕ) (U V : Fin n → Set X),
      (∀ i, IsOpen (U i)) → (∀ i, IsRetrocompact (U i)) →
      (∀ i, IsOpen (V i)) → (∀ i, IsRetrocompact (V i)) →
      ∀ (E : Set X), E = (⋃ i, U i ∩ (V i)ᶜ) →
      ∀ (F : Set ↥E), IsConstructible F →
      IsConstructible (Subtype.val '' F : Set X) := by
  intro n
  induction n with
  | zero =>
    intro U V _ _ _ _ E hEeq F _
    have himg : (Subtype.val '' F : Set X) = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨y, _, _⟩ => by simpa [hEeq] using y.2
    rw [himg]
    exact IsConstructible.empty
  | succ k ih =>
    intro U V hUo hUr hVo hVr E hEeq F hF
    exact isConstructible_image_val_union (E₁ := U 0 ∩ (V 0)ᶜ)
      (E₂ := ⋃ i : Fin k, U i.succ ∩ (V i.succ)ᶜ)
      (hUo 0) (hUr 0) (hVo 0) (hVr 0) rfl
      (isConstructible_iUnion_inter_compl (U := fun i => U i.succ) (V := fun i => V i.succ)
        (fun i => hUo i.succ) (fun i => hUr i.succ) (fun i => hVo i.succ) (fun i => hVr i.succ))
      (ih (fun i => U i.succ) (fun i => V i.succ)
        (fun i => hUo i.succ) (fun i => hUr i.succ)
        (fun i => hVo i.succ) (fun i => hVr i.succ) _ rfl)
      (by rw [hEeq]; exact Set.iUnion_fin_add_one_eq_iUnion_succ _) F hF

/-! ### Main theorem -/

/-- Let `X` be a topological space with a basis
of quasi-compact opens. Let `E ⊆ X` be constructible in `X`, and let
`F ⊆ E` be constructible in the topological subspace `E`. Then `F`, viewed
as a subset of `X` via the inclusion `Subtype.val : E → X`, is
constructible in `X`. -/
@[stacks 09YJ,
  ega "0 9.1.8" "(ii), sufficiency",
  ega "0 9.2.1" "partial",
  sga "3 VIB 3.7" "partial"]
theorem isConstructibleSet_of_isConstructibleSet_in_constructible
    (hX : PrespectralSpace X)
    {E : Set X} (hE : IsConstructibleSet E)
    {F : Set ↥E} (hF : IsConstructibleSet F) :
    IsConstructibleSet (Subtype.val '' F : Set X) := by
  have : PrespectralSpace X := hX
  obtain ⟨n, U, V, hUo, hUr, hVo, hVr, hEeq⟩ := hE
  exact isConstructibleSet_of_isConstructible (isConstructible_image_aux n U V hUo hUr hVo hVr E
    hEeq F (isConstructible_of_isConstructibleSet hF))


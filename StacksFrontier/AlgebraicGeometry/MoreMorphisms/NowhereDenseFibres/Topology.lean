module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.NoetherianSpace
public import StacksCore.Topology.NowhereDense.Defs
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Topological input for nowhere dense generic fibres

This module collects the purely topological statements used in the proofs of Stacks Tags
054X and 0554: how a closed subset fails to be nowhere dense, how generic points interact
with dense open subsets, the comparison of `topologicalKrullDim` with `Order.height` on
irreducible closed subsets, and a lower bound for the number of irreducible components of a
space covered by finitely many closed subsets.

## Main results

* `exists_mem_genericPoints_of_not_isNowhereDense`: a closed subset of a sober space that is
  not nowhere dense contains the generic point of an irreducible component.
* `IsGenericPoint.mem_of_isOpen_of_dense`: the generic point of the whole space lies in
  every dense open subset.
* `topologicalKrullDim_coe_eq_height`: the dimension of an irreducible closed subset is its
  height in the lattice of irreducible closed subsets.
* `topologicalKrullDim_coe_lt_coe_of_lt`: dimension is strictly monotone on irreducible
  closed subsets of finite dimension.
* `Homeomorph.isNowhereDense_preimage_iff`: nowhere density transports along a
  homeomorphism.
* `isNowhereDense_of_isClosed_ne_univ_subtype`: a proper closed subset of an irreducible
  space is nowhere dense.
* `le_ncard_irreducibleComponents_of_isClosed_cover`: a Noetherian space covered by `n`
  closed subsets, each containing a point outside all the others, has at least `n`
  irreducible components.
-/

@[expose] public section

open TopologicalSpace

section GenericPoints

variable {T : Type*} [TopologicalSpace T]

/-- A closed subset of a sober space which is not nowhere dense contains the generic point of
an irreducible component of the whole space.

Sobriety alone suffices; no Noetherian hypothesis is needed, because the component used is the
one through a chosen interior point rather than one supplied by a finiteness argument. -/
theorem exists_mem_genericPoints_of_not_isNowhereDense [QuasiSober T]
    {A : Set T} (hA : IsClosed A) (hnd : ¬ IsNowhereDense A) :
    ∃ x : T, x ∈ A ∧ x ∈ genericPoints T := by
  have hne : interior A ≠ ∅ := fun he => hnd (by rw [IsNowhereDense, hA.closure_eq]; exact he)
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  let C : irreducibleComponents T :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let g : genericPoints T := genericPoints.ofComponent C
  have hcl : x ∈ closure ({g.1} : Set T) := by
    rw [genericPoints.isGenericPoint_ofComponent C]
    exact mem_irreducibleComponent
  exact ⟨g.1, interior_subset
    ((specializes_iff_mem_closure.mpr hcl).mem_open isOpen_interior hx), g.2⟩

/-- The generic point of a whole topological space lies in every dense open subset. -/
theorem IsGenericPoint.mem_of_isOpen_of_dense {η : T} (hη : IsGenericPoint η Set.univ)
    {U : Set T} (hU : IsOpen U) (hd : Dense U) : η ∈ U := by
  refine (hη.mem_open_set_iff hU).2 ?_
  obtain ⟨y, hy⟩ : U.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hUempty
    have hηcl : η ∈ closure U := hd.closure_eq ▸ Set.mem_univ η
    rw [hUempty, closure_empty] at hηcl
    exact hηcl
  exact ⟨y, Set.mem_univ y, hy⟩

end GenericPoints

section Dimension

variable {T : Type*} [TopologicalSpace T]

/-- The preimage of an irreducible subset under the inclusion of a larger subset is
irreducible. -/
private lemma isIrreducible_preimage_val {s t : Set T} (hs : IsIrreducible s) (h : s ⊆ t) :
    IsIrreducible ((Subtype.val : t → T) ⁻¹' s) := by
  have := Subtype.irreducibleSpace hs
  have he : Set.inclusion h '' (Set.univ : Set s) = (Subtype.val : t → T) ⁻¹' s := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_preimage]
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩⟩
  rw [← he]
  exact (IrreducibleSpace.isIrreducible_univ s).image _ (by fun_prop)

/-- The dimension of an irreducible closed subset is its height in the lattice of
irreducible closed subsets of the ambient space. -/
theorem topologicalKrullDim_coe_eq_height (Z : IrreducibleCloseds T) :
    topologicalKrullDim (Z : Set T) = (Order.height Z : WithBot ℕ∞) := by
  let e₁ : Set.Iic Z ↪o IrreducibleCloseds (Z : Set T) :=
    OrderEmbedding.ofMapLEIff
      (fun W ↦ ⟨Subtype.val ⁻¹' (W.1 : Set T),
        isIrreducible_preimage_val W.1.isIrreducible W.2,
        W.1.isClosed.preimage continuous_subtype_val⟩)
      (fun A B ↦ ⟨fun h x hx ↦ h (show (⟨x, A.2 hx⟩ : (Z : Set T)) ∈ _ from hx),
        fun h _ hx ↦ h hx⟩)
  let e₂ : IrreducibleCloseds (Z : Set T) ↪o Set.Iic Z :=
    OrderEmbedding.ofMapLEIff
      (fun W : IrreducibleCloseds (Z : Set T) ↦
        ⟨⟨Subtype.val '' (W : Set (Z : Set T)),
          W.isIrreducible'.image _ continuous_subtype_val.continuousOn,
          Z.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _ W.isClosed'⟩,
          Set.image_subset_iff.mpr fun x _ ↦ x.2⟩)
      (by
        intro A B
        change (Subtype.val '' (A : Set (Z : Set T)) ⊆
          Subtype.val '' (B : Set (Z : Set T))) ↔ (A : Set (Z : Set T)) ⊆ B
        refine ⟨fun h x hx ↦ ?_, fun h a ha ↦ ?_⟩
        · obtain ⟨y, hy, hxy⟩ := h ⟨x, hx, rfl⟩
          exact Subtype.ext hxy ▸ hy
        · obtain ⟨b, hb, hba⟩ := (Set.mem_image _ _ _).mp ha
          exact ⟨b, h hb, hba⟩)
  rw [topologicalKrullDim]
  refine le_antisymm ?_ ?_
  · calc
      Order.krullDim (IrreducibleCloseds (Z : Set T)) ≤ Order.krullDim (Set.Iic Z) :=
        Order.krullDim_le_of_strictMono e₂ e₂.strictMono
      _ = (Order.height Z : WithBot ℕ∞) := (Order.height_eq_krullDim_Iic Z).symm
  · calc
      (Order.height Z : WithBot ℕ∞) = Order.krullDim (Set.Iic Z) :=
        Order.height_eq_krullDim_Iic Z
      _ ≤ Order.krullDim (IrreducibleCloseds (Z : Set T)) :=
        Order.krullDim_le_of_strictMono e₁ e₁.strictMono

/-- Dimension is strictly monotone on irreducible closed subsets of finite dimension. -/
theorem topologicalKrullDim_coe_lt_coe_of_lt (W C : IrreducibleCloseds T) (hWC : W < C)
    (hWdim : topologicalKrullDim (W : Set T) ≠ ⊤) :
    topologicalKrullDim (W : Set T) < topologicalKrullDim (C : Set T) := by
  rw [topologicalKrullDim_coe_eq_height W, topologicalKrullDim_coe_eq_height C]
  have hWheight : Order.height W < ⊤ := by
    by_contra h
    refine hWdim ?_
    rw [topologicalKrullDim_coe_eq_height W, show (Order.height W : WithBot ℕ∞) = ⊤ from ?_]
    rw [← WithBot.coe_top, WithBot.coe_inj]
    exact le_antisymm le_top (not_lt.mp h)
  exact_mod_cast Order.height_strictMono hWC hWheight

end Dimension

section NowhereDense

/-- Nowhere density transports along a homeomorphism. -/
theorem Homeomorph.isNowhereDense_preimage_iff {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (T : Set B) :
    IsNowhereDense (e ⁻¹' T) ↔ IsNowhereDense T := by
  rw [IsNowhereDense, IsNowhereDense, ← e.preimage_closure, ← e.preimage_interior,
    Set.preimage_eq_empty_iff, e.surjective.range_eq, Set.disjoint_univ]

/-- A closed subset of the subtype of an irreducible set which is not everything is nowhere
dense. -/
theorem isNowhereDense_of_isClosed_ne_univ_subtype {T : Type*} [TopologicalSpace T]
    (S : Set T) (hS : IsIrreducible S) (A : Set S) (hAclosed : IsClosed A)
    (hAproper : A ≠ Set.univ) : IsNowhereDense A := by
  have := Subtype.irreducibleSpace hS
  rw [IsNowhereDense, hAclosed.closure_eq]
  refine Set.eq_empty_of_subset_empty fun x hx => ?_
  obtain ⟨y, hy, hyc⟩ := nonempty_preirreducible_inter isOpen_interior hAclosed.isOpen_compl
    ⟨x, hx⟩ (Set.nonempty_compl.mpr hAproper)
  exact hyc (interior_subset hy)

/-- If a Noetherian space is covered by `n` closed subsets and each of them contains a point
lying in none of the others, then it has at least `n` irreducible components. -/
theorem le_ncard_irreducibleComponents_of_isClosed_cover {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] (n : ℕ) (S : Fin n → Set T) (hclosed : ∀ i, IsClosed (S i))
    (hcover : ∀ x, ∃ i, x ∈ S i)
    (hexclusive : ∀ i, ∃ x, x ∈ S i ∧ ∀ j, j ≠ i → x ∉ S j) :
    n ≤ (irreducibleComponents T).ncard := by
  classical
  choose p hp using hexclusive
  have hpc : ∀ i, ∃ C ∈ irreducibleComponents T, p i ∈ C := by
    intro i
    have hmem : p i ∈ ⋃₀ irreducibleComponents T := by
      rw [sUnion_irreducibleComponents]
      trivial
    simpa only [Set.mem_sUnion] using hmem
  choose C hC hCp using hpc
  have hCsub : ∀ i, C i ⊆ S i := by
    intro i
    obtain ⟨t, ht, hsub⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp (hC i).1 (Finset.univ.image S)
        (by
          intro z hz
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
          obtain ⟨j, rfl⟩ := hz
          exact hclosed j)
        (fun x _ => by
          obtain ⟨j, hxj⟩ := hcover x
          exact Set.mem_sUnion.mpr
            ⟨S j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hxj⟩)
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
    obtain ⟨j, rfl⟩ := ht
    have hji : j = i := by
      by_contra hji
      exact (hp i).2 j hji (hsub (hCp i))
    exact hji ▸ hsub
  have hinj : Function.Injective C := by
    intro i j hij
    by_contra hne
    exact (hp i).2 j (Ne.symm hne) (hCsub j (hij ▸ hCp i))
  have : Fintype (↥(irreducibleComponents T)) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  have hcard := Fintype.card_le_of_injective (fun i => (⟨C i, hC i⟩ : irreducibleComponents T))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  simpa using hcard

end NowhereDense

end

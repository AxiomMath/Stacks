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
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The space of connected components of a spectral space

The space of connected components of a spectral space is profinite. The key point is that in a
spectral space the connected component of a point `x` is the intersection of all clopen sets
containing `x`: quasi-separatedness lets one refine a separating pair of opens to quasi-compact
opens and then cut their overlap away with finitely many clopens through `x`, which shows the
intersection is preconnected. Clopen sets are saturated for the quotient map, so their images
separate distinct points of the quotient.

## Main results

* `spectral_iInter_isClopen_isPreconnected`: the intersection of all clopens through a point of a
  spectral space is preconnected.
* `spectral_connectedComponent_eq_iInter_isClopen`: the connected component of `x` is the
  intersection of all clopens containing `x`.
* `isOpen_image_mk_of_isClopen`: the image of a clopen set in `ConnectedComponents X` is open.
* `connectedComponents_isProfinite`: `ConnectedComponents X` is Hausdorff, quasi-compact
  and totally disconnected.
-/

@[expose] public section

open Topology Set

/-! ### Generalities about the intersection of clopens through a point -/

/-- The connected component of `x` is contained in every clopen set containing `x`,
hence in the intersection of all such clopens. -/
lemma connectedComponent_subset_iInter_isClopen_set
    (X : Type*) [TopologicalSpace X] (x : X) :
    connectedComponent x ⊆ ⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z :=
  subset_iInter₂ fun _ ⟨hZ, hxZ⟩ =>
    isPreconnected_connectedComponent.subset_isClopen hZ ⟨x, mem_connectedComponent, hxZ⟩

/-- `x` lies in the intersection of all clopens containing it. -/
lemma mem_iInter_isClopen_self {X : Type*} [TopologicalSpace X] (x : X) :
    x ∈ ⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z := by
  simp

/-- The intersection of all clopens through `x` is closed. -/
lemma isClosed_iInter_isClopen {X : Type*} [TopologicalSpace X] (x : X) :
    IsClosed (⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z) :=
  isClosed_iInter fun _ => isClosed_iInter fun hZ => hZ.1.isClosed

/-- The intersection of all clopens through `x` is contained in every clopen containing `x`. -/
lemma iInter_isClopen_subset
    {X : Type*} [TopologicalSpace X] (x : X)
    {Z : Set X} (hZ : IsClopen Z) (hxZ : x ∈ Z) :
    (⋂ Z' ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z') ⊆ Z :=
  biInter_subset_of_mem ⟨hZ, hxZ⟩

/-! ### Splitting a set along a cover by two subsets -/

/-- If `C` is covered by `U ∪ V` and misses the overlap `U ∩ V`, then `C ∩ U` is exactly the
part of `C` outside `V`. -/
lemma inter_eq_diff_of_subset_union_of_disjoint_inter {X : Type*} {C U V : Set X}
    (hCUV : C ⊆ U ∪ V) (hdisj : Disjoint C (U ∩ V)) : C ∩ U = C \ V := by
  ext z
  exact ⟨fun ⟨hzC, hzU⟩ => ⟨hzC, fun hzV => disjoint_left.mp hdisj hzC ⟨hzU, hzV⟩⟩,
    fun ⟨hzC, hzV⟩ => ⟨hzC, (hCUV hzC).resolve_right hzV⟩⟩

/-- A clopen set covered by two open sets whose overlap it misses stays clopen after
intersecting with either of them. -/
lemma IsClopen.inter_of_subset_union {X : Type*} [TopologicalSpace X] {C U V : Set X}
    (hC : IsClopen C) (hU : IsOpen U) (hV : IsOpen V) (hCUV : C ⊆ U ∪ V)
    (hdisj : Disjoint C (U ∩ V)) : IsClopen (C ∩ U) :=
  ⟨inter_eq_diff_of_subset_union_of_disjoint_inter hCUV hdisj ▸ hC.isClosed.sdiff hV,
    hC.isOpen.inter hU⟩

/-! ### Quasi-compact refinements in prespectral spaces -/

/-- In a prespectral space, an open set containing a compact set can be shrunk to a
quasi-compact open neighbourhood. -/
lemma exists_qcOpen_of_isCompact_subset_isOpen
    {X : Type*} [TopologicalSpace X] [PrespectralSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ U' : Set X, IsCompact U' ∧ IsOpen U' ∧ K ⊆ U' ∧ U' ⊆ U := by
  classical
  have basis := PrespectralSpace.isTopologicalBasis (X := X)
  choose V hVbasis hxV hVU using fun (p : K) =>
    basis.exists_subset_of_mem_open (hKU p.2) hU
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V (fun p => (hVbasis p).1)
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  exact ⟨⋃ p ∈ t, V p,
    t.isCompact_biUnion (fun p _ => (hVbasis p).2),
    isOpen_biUnion (fun p _ => (hVbasis p).1),
    ht,
    iUnion₂_subset (fun p _ => hVU p)⟩

/-! ### Separating a compact set from the intersection of clopens -/

/-- A point outside the intersection of all clopens through `x` is separated from `x` by a
clopen set. -/
private lemma exists_isClopen_of_notMem_iInter {X : Type*} [TopologicalSpace X] {x z : X}
    (hz : z ∉ ⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z) :
    ∃ Z : Set X, IsClopen Z ∧ x ∈ Z ∧ z ∉ Z := by
  simp only [mem_iInter, mem_ofPred_eq, not_forall] at hz
  obtain ⟨Z, ⟨hZ, hxZ⟩, hzZ⟩ := hz
  exact ⟨Z, hZ, hxZ, hzZ⟩

/-- Finite-intersection property: if a compact set is disjoint from the intersection of
all clopens through `x`, then it is already disjoint from a finite intersection of
clopens through `x`. -/
lemma exists_finite_clopen_inter_disjoint_isCompact
    {X : Type*} [TopologicalSpace X] (x : X)
    {K : Set X} (hK : IsCompact K)
    (h : Disjoint (⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z) K) :
    ∃ T : Finset (Set X),
      (∀ Z ∈ T, IsClopen Z ∧ x ∈ Z) ∧ Disjoint (⋂ Z ∈ T, (Z : Set X)) K := by
  classical
  have hsep : ∀ z : K, ∃ Z : Set X, IsClopen Z ∧ x ∈ Z ∧ z.1 ∉ Z := fun z =>
    exists_isClopen_of_notMem_iInter (disjoint_right.mp h z.2)
  choose Z hZcl hZx hZnz using hsep
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun z : K => (Z z)ᶜ)
    (fun z => (hZcl z).compl.isOpen) (fun y hy => mem_iUnion.mpr ⟨⟨y, hy⟩, hZnz ⟨y, hy⟩⟩)
  refine ⟨s.image Z, ?_, ?_⟩
  · rintro W hW
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨hZcl z, hZx z⟩
  · rw [disjoint_left]
    intro p hp_in_inter hpK
    obtain ⟨z, hzs, hpz⟩ := mem_iUnion₂.mp (hs hpK)
    exact hpz <| by
      simpa using mem_iInter₂.mp hp_in_inter (Z z) (Finset.mem_image.mpr ⟨z, hzs, rfl⟩)

/-- Quasi-separated cutting: if two quasi-compact open sets `U`, `V` cover the intersection of
all clopens through `x`, which misses their overlap, then a single clopen set containing `x` is
already covered by `U ∪ V` and already misses `U ∩ V`. -/
lemma exists_isClopen_subset_union_disjoint_inter
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [QuasiSeparatedSpace X] (x : X)
    {U V : Set X} (hU : IsOpen U) (hUc : IsCompact U) (hV : IsOpen V) (hVc : IsCompact V)
    (hsub : (⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z) ⊆ U ∪ V)
    (hdisj : Disjoint (⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z) (U ∩ V)) :
    ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ C ⊆ U ∪ V ∧ Disjoint C (U ∩ V) := by
  obtain ⟨T₁, hT₁cl, hT₁disj⟩ := exists_finite_clopen_inter_disjoint_isCompact x
    (hU.union hV).isClosed_compl.isCompact (disjoint_left.mpr fun _ hz hzn => hzn (hsub hz))
  have hC₁ : IsClopen (⋂ Z ∈ T₁, (Z : Set X)) :=
    isClopen_biInter_finset fun Z hZ => (hT₁cl Z hZ).1
  have hC₁UV : (⋂ Z ∈ T₁, (Z : Set X)) ⊆ U ∪ V := fun _ hz => by
    by_contra hzn
    exact disjoint_left.mp hT₁disj hz hzn
  obtain ⟨T₂, hT₂cl, hT₂disj⟩ := exists_finite_clopen_inter_disjoint_isCompact x
    ((QuasiSeparatedSpace.inter_isCompact U V hU hUc hV hVc).inter_left hC₁.isClosed)
    (disjoint_left.mpr fun _ hz ⟨_, hzU, hzV⟩ => disjoint_left.mp hdisj hz ⟨hzU, hzV⟩)
  exact ⟨(⋂ Z ∈ T₁, (Z : Set X)) ∩ ⋂ Z ∈ T₂, (Z : Set X),
    hC₁.inter (isClopen_biInter_finset fun Z hZ => (hT₂cl Z hZ).1),
    ⟨mem_iInter₂.mpr fun Z hZ => (hT₁cl Z hZ).2, mem_iInter₂.mpr fun Z hZ => (hT₂cl Z hZ).2⟩,
    fun _ hz => hC₁UV hz.1,
    disjoint_left.mpr fun _ ⟨hz₁, hz₂⟩ ⟨hzU, hzV⟩ =>
      disjoint_left.mp hT₂disj hz₂ ⟨hz₁, hzU, hzV⟩⟩

/-! ### Main topological lemma: the intersection of clopens through `x` is preconnected -/

/-- In a spectral space, the intersection of all clopens containing a point `x` is
preconnected. -/
lemma spectral_iInter_isClopen_isPreconnected
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] (x : X) :
    IsPreconnected (⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z) := by
  set Q : Set X := ⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z
  have hxQ : x ∈ Q := mem_iInter_isClopen_self x
  have hQclosed : IsClosed Q := isClosed_iInter_isClopen x
  intro A B hA hB hQAB hQA hQB
  by_contra hcontra
  have hABdisj : Disjoint Q (A ∩ B) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hcontra)
  have hcompact : ∀ {A B : Set X}, IsOpen B → Q ⊆ A ∪ B → Disjoint Q (A ∩ B) →
      IsCompact (Q ∩ A) := fun hB hQAB hdisj =>
    (inter_eq_diff_of_subset_union_of_disjoint_inter hQAB hdisj ▸ hQclosed.sdiff hB).isCompact
  obtain ⟨U, hUc, hUo, hQA_sub, hU_sub⟩ :=
    exists_qcOpen_of_isCompact_subset_isOpen (hcompact hB hQAB hABdisj) hA inter_subset_right
  obtain ⟨V, hVc, hVo, hQB_sub, hV_sub⟩ :=
    exists_qcOpen_of_isCompact_subset_isOpen
      (hcompact hA (by rwa [union_comm]) (by rwa [inter_comm])) hB inter_subset_right
  have hQUV : Q ⊆ U ∪ V := fun z hzQ =>
    (hQAB hzQ).imp (fun h => hQA_sub ⟨hzQ, h⟩) (fun h => hQB_sub ⟨hzQ, h⟩)
  have hQUVdisj : Disjoint Q (U ∩ V) := disjoint_left.mpr fun _ hzQ ⟨hzU, hzV⟩ =>
    disjoint_left.mp hABdisj hzQ ⟨hU_sub hzU, hV_sub hzV⟩
  obtain ⟨C, hC, hxC, hCUV, hCdisj⟩ :=
    exists_isClopen_subset_union_disjoint_inter x hUo hUc hVo hVc hQUV hQUVdisj
  have hcut : ∀ {A B U V : Set X}, IsOpen U → IsOpen V → C ⊆ U ∪ V → Disjoint C (U ∩ V) →
      Q ∩ A ⊆ U → Q ∩ B ⊆ V → x ∈ A → (Q ∩ B).Nonempty → False :=
    fun hU hV hCUV hCdisj hAU hBV hxA ⟨y, hyQ, hyB⟩ => by
    obtain ⟨hyC, hyU⟩ := iInter_isClopen_subset x (hC.inter_of_subset_union hU hV hCUV hCdisj)
      ⟨hxC, hAU ⟨hxQ, hxA⟩⟩ hyQ
    exact disjoint_left.mp hCdisj hyC ⟨hyU, hBV ⟨hyQ, hyB⟩⟩
  rcases hQAB hxQ with hxA | hxB
  · exact hcut hUo hVo hCUV hCdisj hQA_sub hQB_sub hxA hQB
  · exact hcut hVo hUo (by rwa [union_comm]) (by rwa [inter_comm]) hQB_sub hQA_sub hxB hQA

/-! ### Identifying connected components in a spectral space -/

/-- In a spectral space, the connected component of `x` equals the intersection of all
clopen subsets containing `x` (Stacks 005F). -/
lemma spectral_connectedComponent_eq_iInter_isClopen
    (X : Type*) [TopologicalSpace X] [SpectralSpace X] (x : X) :
    connectedComponent x = ⋂ Z ∈ {s : Set X | IsClopen s ∧ x ∈ s}, Z :=
  Subset.antisymm (connectedComponent_subset_iInter_isClopen_set X x)
    ((spectral_iInter_isClopen_isPreconnected X x).subset_connectedComponent
      (mem_iInter_isClopen_self x))

/-! ### Pushing clopens to the quotient `ConnectedComponents X` -/

/-- A clopen set is saturated with respect to the connected-components quotient. -/
lemma preimage_image_mk_of_isClopen
    {X : Type*} [TopologicalSpace X] (W : Set X) (hW : IsClopen W) :
    (ConnectedComponents.mk : X → ConnectedComponents X) ⁻¹'
      ((ConnectedComponents.mk : X → ConnectedComponents X) '' W) = W :=
  (connectedComponents_preimage_image W).trans hW.biUnion_connectedComponent_eq

/-- The image of a clopen subset of `X` in `ConnectedComponents X` is open. -/
lemma isOpen_image_mk_of_isClopen
    {X : Type*} [TopologicalSpace X] (W : Set X) (hW : IsClopen W) :
    IsOpen ((ConnectedComponents.mk : X → ConnectedComponents X) '' W) := by
  rw [ConnectedComponents.isQuotientMap_coe.isOpen_preimage.symm,
    preimage_image_mk_of_isClopen W hW]
  exact hW.isOpen

/-! ### Hausdorff separation in `ConnectedComponents X` -/

/-- Distinct points in `ConnectedComponents X` are separated by disjoint open sets,
provided clopens through every point determine the connected components. -/
lemma exists_disjoint_open_of_ne
    {X : Type*} [TopologicalSpace X]
    (h : ∀ z : X, connectedComponent z = ⋂ Z ∈ {s : Set X | IsClopen s ∧ z ∈ s}, Z)
    (a b : ConnectedComponents X) (hab : a ≠ b) :
    ∃ A B : Set (ConnectedComponents X),
      IsOpen A ∧ IsOpen B ∧ a ∈ A ∧ b ∈ B ∧ Disjoint A B := by
  obtain ⟨x, rfl⟩ := a.exists_rep
  obtain ⟨y, rfl⟩ := b.exists_rep
  have hy : y ∉ connectedComponent x := fun hy =>
    hab (ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hy))
  obtain ⟨U, hU, hxU, hyU⟩ := exists_isClopen_of_notMem_iInter (h x ▸ hy)
  refine ⟨(ConnectedComponents.mk : X → _) '' U,
      (ConnectedComponents.mk : X → _) '' Uᶜ,
      isOpen_image_mk_of_isClopen U hU,
      isOpen_image_mk_of_isClopen Uᶜ hU.compl,
      ⟨x, hxU, rfl⟩, ⟨y, by simpa using hyU, rfl⟩, ?_⟩
  rw [Set.disjoint_iff]
  rintro c ⟨hcA, hcB⟩
  obtain ⟨z, rfl⟩ := c.exists_rep
  exact (preimage_image_mk_of_isClopen Uᶜ hU.compl).subset hcB
    ((preimage_image_mk_of_isClopen U hU).subset hcA)

/-- **Stacks 0906**.
For a spectral space `X` the space of connected components `π₀(X) = ConnectedComponents X` is
profinite: Hausdorff, quasi-compact and totally disconnected. -/
@[stacks 0906]
theorem connectedComponents_isProfinite
    (X : Type*) [TopologicalSpace X] [SpectralSpace X] :
    T2Space (ConnectedComponents X) ∧
    CompactSpace (ConnectedComponents X) ∧
    TotallyDisconnectedSpace (ConnectedComponents X) :=
  ⟨⟨fun a b hab => exists_disjoint_open_of_ne
      (spectral_connectedComponent_eq_iInter_isClopen X) a b hab⟩,
    inferInstance, inferInstance⟩

module

public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.BaseCase
public import StacksFrontier.Topology.Dimension.UnionDimension

/-!
# Tag 0B1V: the subvarieties to move off

A rationally trivial `r`-cycle `α` is a finite combination `∑ cᵢ ([Wᵢ,₀]_r - [Wᵢ,∞]_r)` of basic
rational equivalences. The proof of Tag 0B1V moves the second cycle off the irreducible components
of the fibres `Wᵢ,₀` and `Wᵢ,∞`. This file collects them into a finite family of closed
subvarieties of dimension `r` of `X`, and shows that a closed subvariety `Z` of dimension `s`
meeting every member of the family properly has `α · [Z]` rationally equivalent to zero.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

/-- The irreducible components of a subset, read as subsets of the ambient space. -/
def componentSets {T : Type*} [TopologicalSpace T] (F : Set T) : Set (Set T) :=
  Set.image Subtype.val '' irreducibleComponents ↥F

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- A subset of a Noetherian space has finitely many irreducible components. -/
theorem finite_componentSets [NoetherianSpace T] (F : Set T) : (componentSets F).Finite :=
  NoetherianSpace.finite_irreducibleComponents.image _

/-- An irreducible component of a closed subset is closed in the ambient space. -/
theorem isClosed_of_mem_componentSets {F A : Set T} (hF : IsClosed F) (hA : A ∈ componentSets F) :
    IsClosed A := by
  obtain ⟨c, hc, rfl⟩ := hA
  exact hF.isClosedMap_subtype_val c (isClosed_of_mem_irreducibleComponents c hc)

/-- An irreducible component of a subset is irreducible in the ambient space. -/
theorem isIrreducible_of_mem_componentSets {F A : Set T} (hA : A ∈ componentSets F) :
    IsIrreducible A := by
  obtain ⟨c, hc, rfl⟩ := hA
  exact hc.1.image _ continuous_subtype_val.continuousOn

/-- An irreducible component of a subset `F` is contained in `F`. -/
theorem subset_of_mem_componentSets {F A : Set T} (hA : A ∈ componentSets F) : A ⊆ F := by
  obtain ⟨c, -, rfl⟩ := hA
  exact Subtype.coe_image_subset F c

/-- A subset is contained in the union of its irreducible components. -/
theorem subset_sUnion_componentSets (F : Set T) : F ⊆ ⋃₀ componentSets F := by
  intro x hx
  have : (⟨x, hx⟩ : ↥F) ∈ ⋃₀ irreducibleComponents ↥F := by
    rw [sUnion_irreducibleComponents]; trivial
  obtain ⟨c, hc, hxc⟩ := this
  exact ⟨_, ⟨c, hc, rfl⟩, ⟨⟨x, hx⟩, hxc, rfl⟩⟩

/-- **The dimension bound of a union read off the pieces.** If a closed set `S` lies in the union
of a finite family of closed sets, each of which cuts out of `S` a subset of dimension at most
`m - n`, then so has `S`. -/
theorem topologicalKrullDim_add_le_of_subset_sUnion [QuasiSober T] {S : Set T} (hS : IsClosed S)
    {𝒜 : Set (Set T)} (h𝒜 : 𝒜.Finite) (hA : ∀ A ∈ 𝒜, IsClosed A) (hSA : S ⊆ ⋃₀ 𝒜) (n m : ℕ)
    (hc : ∀ A ∈ 𝒜, topologicalKrullDim ↥(S ∩ A) + (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞)) :
    topologicalKrullDim ↥S + (n : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) := by
  classical
  have : Fintype ↥𝒜 := h𝒜.fintype
  rcases isEmpty_or_nonempty ↥𝒜 with he | hne
  · have hSe : S = ∅ := by
      refine Set.eq_empty_of_subset_empty fun x hx => ?_
      obtain ⟨A, hA𝒜, -⟩ := hSA hx
      exact (he.false ⟨A, hA𝒜⟩).elim
    subst hSe
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).mpr inferInstance]
    simp
  · obtain ⟨A₀, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset ↥𝒜)
      Finset.univ_nonempty (fun A => topologicalKrullDim ↥(S ∩ (A : Set T)))
    have hle : topologicalKrullDim ↥S ≤
        (Finset.univ : Finset ↥𝒜).sup (fun A => topologicalKrullDim ↥(S ∩ (A : Set T))) := by
      refine topologicalKrullDim_le_of_subset_biUnion (Finset.univ : Finset ↥𝒜) hS
        (fun A => hA A.1 A.2) ?_ fun A hAt =>
          Finset.le_sup (f := fun A : ↥𝒜 => topologicalKrullDim ↥(S ∩ (A : Set T))) hAt
      intro x hx
      obtain ⟨A, hA𝒜, hxA⟩ := hSA hx
      exact Set.mem_biUnion (Finset.mem_univ (⟨A, hA𝒜⟩ : ↥𝒜)) hxA
    rw [hsup] at hle
    exact (add_le_add_left hle _).trans (hc A₀.1 A₀.2)

end Topology

section Fibres

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [IsVariety k p]

/-- **The subvarieties to move off**: the irreducible components of the fibres over `0` and over
`∞` of the members `Wᵢ` of a family in `X × ℙ¹`. -/
def fibreComponentSets {ι : Type*} (W : ι → (projectiveLineProduct p).IdealSheafData) :
    Set (Set X) :=
  ⋃ i, componentSets ((zeroFiber p (W i)).support : Set X) ∪
    componentSets ((infinityFiber p (W i)).support : Set X)

variable {k p}

/-- For a finite family `W`, the set `fibreComponentSets k p W` is finite. -/
theorem finite_fibreComponentSets {ι : Type*} [Finite ι]
    (W : ι → (projectiveLineProduct p).IdealSheafData) : (fibreComponentSets k p W).Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := ⟨⟩
  exact Set.finite_iUnion fun i => (finite_componentSets _).union (finite_componentSets _)

/-- Every member of `fibreComponentSets k p W` is closed in `X`. -/
theorem isClosed_of_mem_fibreComponentSets {ι : Type*}
    {W : ι → (projectiveLineProduct p).IdealSheafData} {A : Set X}
    (hA : A ∈ fibreComponentSets k p W) : IsClosed A := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  rcases hi with hi | hi
  · exact isClosed_of_mem_componentSets (zeroFiber p (W i)).support.isClosed hi
  · exact isClosed_of_mem_componentSets (infinityFiber p (W i)).support.isClosed hi

/-- Every member of `fibreComponentSets k p W` is irreducible. -/
theorem isIrreducible_of_mem_fibreComponentSets {ι : Type*}
    {W : ι → (projectiveLineProduct p).IdealSheafData} {A : Set X}
    (hA : A ∈ fibreComponentSets k p W) : IsIrreducible A := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  rcases hi with hi | hi
  · exact isIrreducible_of_mem_componentSets hi
  · exact isIrreducible_of_mem_componentSets hi

/-- **Every member of the family has dimension `r`.** -/
theorem topologicalKrullDim_of_mem_fibreComponentSets {ι : Type*}
    {W : ι → (projectiveLineProduct p).IdealSheafData} [∀ i, IsIntegral (W i).subscheme] {r : ℕ}
    (hDim : ∀ i, ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 = r + 1)
    (h₀ : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (infinitySection p))
    {A : Set X} (hA : A ∈ fibreComponentSets k p W) :
    topologicalKrullDim ↥A = (r : WithBot ℕ∞) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  have hDim' : ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 =
        (r : ℤ) + 1 := hDim i
  rcases hi with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · simpa using topologicalKrullDim_component_zeroFiber k p (W i) hDim' (h₀ i) hc
  · simpa using topologicalKrullDim_component_infinityFiber k p (W i) hDim' (hInf i) hc

variable [DecidableEq X] (hX : IsRegular X)

/-- **The base case of Tag 0B1V.** Let `α = ∑ cᵢ ([Wᵢ,₀]_r - [Wᵢ,∞]_r)` and let `Z = closure {z}`,
of dimension `s`, meet every irreducible component of every fibre `Wᵢ,₀`, `Wᵢ,∞` properly. Then
`α · [Z]` is rationally equivalent to zero. -/
theorem torFormulaCycleIntersectionProduct_sum_mem_ratCycles (n r s : ℕ)
    (hn : topologicalKrullDim X = (n : WithBot ℕ∞)) {ι : Type*} [Fintype ι]
    (W : ι → (projectiveLineProduct p).IdealSheafData) [∀ i, IsIntegral (W i).subscheme]
    (hDim : ∀ i, ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 = r + 1)
    (h₀ : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (zeroSection p))
    (hInf : ∀ i, ¬ Set.range (W i).subschemeι ⊆ Set.range (infinitySection p))
    (c : ι → ℤ) (z : X) (hz : topologicalKrullDim (closure ({z} : Set X)) = (s : WithBot ℕ∞))
    (hT : ∀ A ∈ fibreComponentSets k p W,
      topologicalKrullDim ↥(closure ({z} : Set X) ∩ A) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞)) :
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) p hX ((r : ℤ) + s - n)
        (∑ i, c i • ((cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (zeroFiber p (W i)).subschemeι r).1 -
          (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p
            (infinityFiber p (W i)).subschemeι r).1))
        (Function.locallyFinsuppWithin.single z 1) ∈
      ratCycles (fieldChowSituation k) p ((r : ℤ) + s - n) := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := ⟨⟩
  show cycleIntersectionProductLeftHom (torFormulaSubvarietyProductTotal (fieldChowSituation k)
    p hX ((r : ℤ) + s - n)) (Function.locallyFinsuppWithin.single z 1) _ ∈ _
  rw [map_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [map_zsmul]
  refine AddSubgroup.zsmul_mem _ ?_ _
  have hbound : ∀ F : Set X, IsClosed F →
      componentSets F ⊆ fibreComponentSets k p W →
      topologicalKrullDim ↥(closure ({z} : Set X) ∩ F) + (n : WithBot ℕ∞) ≤
        ((s + r : ℕ) : WithBot ℕ∞) := by
    intro F hF hsub
    refine topologicalKrullDim_add_le_of_subset_sUnion (isClosed_closure.inter hF)
      (finite_componentSets F) (fun A hA => isClosed_of_mem_componentSets hF hA)
      (fun x hx => subset_sUnion_componentSets F hx.2) n (s + r) fun A hA => ?_
    refine le_trans (add_le_add_left (topologicalKrullDim_le_of_subset ?_) _) (hT A (hsub hA))
    exact Set.inter_subset_inter_left _ Set.inter_subset_left
  have hDim' : ∀ ξ : genericPoints (W i).subscheme,
      relativeDimension (fieldChowSituation k).dimensionFunction (familyBase p (W i)) ξ.1 =
        r + 1 := hDim i
  exact torFormulaCycleIntersectionProduct_fibreDifference_mem_ratCycles k p hX n r s hn (W i)
    hDim' (h₀ i) (hInf i) z hz
    (hbound _ (zeroFiber p (W i)).support.isClosed
      (fun A hA => Set.mem_iUnion.mpr ⟨i, Or.inl hA⟩))
    (hbound _ (infinityFiber p (W i)).support.isClosed
      (fun A hA => Set.mem_iUnion.mpr ⟨i, Or.inr hA⟩))

end Fibres

end Stacks.Intersection.RationalEquivalenceProduct

end

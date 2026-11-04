module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentDimension
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Either `f` is an isomorphism or every component of the special fibre is a curve

In Situation [Stacks, Tag 0AX8] the observation following the situation says that, once the
uninteresting case of a finite (hence invertible) `f` is discarded, every irreducible component
`C_i` of the special fibre `X_s` is a curve. This file proves that observation as the dichotomy
"`f` is an isomorphism, or every component is a curve", which needs no hypothesis beyond the
Situation, and records that when `f` is an isomorphism every point of `X` over the closed point
has a local ring of dimension two.

The argument is the one behind the observation. Each component has dimension at most one
(`AlgebraicGeometry.VanishingSituation.topologicalKrullDim_component_le_one`). If `C_i` had
dimension zero it would be the single point `ξ_i`, which lies on no other component, so `ξ_i`
would be an isolated point of `X_s`, and a modification of the spectrum of a normal local domain
with an isolated point in its closed fibre is an isomorphism
(`AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`, through
[Stacks, Tag 0BFP]).

## Main results

The elided prefix is `AlgebraicGeometry.VanishingSituation`.

* `isIso_f_of_topologicalKrullDim_component_le_zero`: a component of dimension at most zero forces
  `f` to be an isomorphism.
* `isIso_f_or_forall_topologicalKrullDim_component_eq_one`: the observation following
  Situation 0AX8.
* `coheight_eq_two_of_isIso`: if `f` is an isomorphism, every point over the closed point has
  coheight two.

## References

* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Topology

universe u

namespace AlgebraicGeometry

namespace VanishingSituation

variable (V : VanishingSituation.{u})

/-- The local ring of the base at its closed point has dimension two. -/
theorem ringKrullDim_stalk_closedPoint :
    ringKrullDim (V.base.presheaf.stalk V.closedPoint) = 2 := by
  rw [ringKrullDim_stalk_eq_coheight, ← idealHeight_eq_coheight,
    show (V.closedPoint : V.base).asIdeal = IsLocalRing.maximalIdeal V.A from rfl,
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, V.dimension_two]

/-- A component of the special fibre of dimension at most zero is the single point
`componentFiberGenericPoint V i`. -/
theorem component_eq_singleton_of_le_zero (i : Fin V.numberOfComponents)
    (h : topologicalKrullDim (V.component i) ≤ 0) :
    V.component i = {componentFiberGenericPoint V i} := by
  have hz := componentFiberGenericPoint_spec V i
  refine Set.Subset.antisymm (fun w hw => ?_) (Set.singleton_subset_iff.mpr hz.mem)
  have hzw : (⟨componentFiberGenericPoint V i, hz.mem⟩ : V.component i) ⤳ ⟨w, hw⟩ :=
    Topology.IsInducing.subtypeVal.specializes_iff.mp (hz.specializes hw)
  exact (congrArg Subtype.val
    (Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero h hzw)).symm

/-- The generic point of a component of the special fibre lies on no other component. -/
theorem componentFiberGenericPoint_notMem_component {i j : Fin V.numberOfComponents}
    (hij : j ≠ i) : componentFiberGenericPoint V i ∉ V.component j := by
  intro hmem
  have hsub : V.component i ⊆ V.component j := by
    rw [← (componentFiberGenericPoint_spec V i).def]
    exact (isClosed_of_mem_irreducibleComponents _
      (V.component_mem_irreducibleComponents j)).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hmem)
  exact hij (V.component_injective (Set.Subset.antisymm
    ((V.component_mem_irreducibleComponents i).2 (V.component_mem_irreducibleComponents j).1 hsub)
    hsub))

/-- A component of the special fibre of dimension at most zero is an open point of it. -/
theorem isOpen_singleton_componentFiberGenericPoint_of_le_zero (i : Fin V.numberOfComponents)
    (h : topologicalKrullDim (V.component i) ≤ 0) :
    IsOpen ({componentFiberGenericPoint V i} : Set V.specialFiber) := by
  have hcompl : ({componentFiberGenericPoint V i} : Set V.specialFiber)ᶜ =
      ⋃ j : Fin V.numberOfComponents, ⋃ (_ : j ≠ i), V.component j := by
    ext w
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, exists_prop]
    constructor
    · intro hw
      obtain ⟨Z, hZ, hwZ⟩ := Set.mem_sUnion.mp
        (sUnion_irreducibleComponents (X := V.specialFiber) ▸ Set.mem_univ w)
      obtain ⟨j, rfl⟩ := V.exists_component_eq Z hZ
      refine ⟨j, fun hji => hw ?_, hwZ⟩
      subst hji
      rwa [component_eq_singleton_of_le_zero V j h, Set.mem_singleton_iff] at hwZ
    · rintro ⟨j, hji, hwj⟩ rfl
      exact componentFiberGenericPoint_notMem_component V hji hwj
  rw [← isClosed_compl_iff, hcompl]
  exact isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ =>
    isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents j)

/-- **A component of the special fibre of dimension at most zero forces `f` to be an
isomorphism.** Its generic point is isolated in the special fibre
(`isOpen_singleton_componentFiberGenericPoint_of_le_zero`), and a modification of `Spec(A)` with
an isolated point in its closed fibre is an isomorphism
(`AlgebraicGeometry.IsModification.isIso_of_isOpen_singleton_fiber`). -/
theorem isIso_f_of_topologicalKrullDim_component_le_zero (i : Fin V.numberOfComponents)
    (h : topologicalKrullDim (V.component i) ≤ 0) : IsIso V.f :=
  V.modification.isIso_of_isOpen_singleton_fiber (componentFiberGenericPoint V i)
    (isOpen_singleton_componentFiberGenericPoint_of_le_zero V i h)

/-- If `f` is an isomorphism, every point of `X` over the closed point has coheight two. -/
theorem coheight_eq_two_of_isIso [IsIso V.f] {x : V.X} (hx : V.f x = V.closedPoint) :
    Order.coheight x = 2 := by
  have hdim := ringKrullDim_eq_of_ringEquiv (asIso (V.f.stalkMap x)).commRingCatIsoToRingEquiv
  rw [hx, ringKrullDim_stalk_closedPoint, ringKrullDim_stalk_eq_coheight] at hdim
  have h2 : ((Order.coheight x : ℕ∞) : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := hdim.symm
  exact WithBot.coe_injective h2

/-- A component of the special fibre of dimension different from one has dimension at most
zero. -/
private theorem topologicalKrullDim_component_le_zero_of_ne_one
    (i : Fin V.numberOfComponents) (h : topologicalKrullDim (V.component i) ≠ 1) :
    topologicalKrullDim (V.component i) ≤ 0 := by
  have hlt := lt_of_le_of_ne (V.topologicalKrullDim_component_le_one i) h
  generalize topologicalKrullDim (V.component i) = d at hlt ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    have hn : n < 1 := by exact_mod_cast hlt
    exact_mod_cast (Order.lt_one_iff.mp hn).le

/-- **The observation following [Stacks, Tag 0AX8].** Either `f` is an isomorphism (the case of
a finite `f`, discarded in the source), or every irreducible component of the special fibre is a
curve. -/
theorem isIso_f_or_forall_topologicalKrullDim_component_eq_one :
    IsIso V.f ∨ ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1 := by
  by_contra! h
  obtain ⟨hiso, i, hi⟩ := h
  exact hiso (V.isIso_f_of_topologicalKrullDim_component_le_zero i
    (topologicalKrullDim_component_le_zero_of_ne_one V i hi))

end VanishingSituation

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspace
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpenLocallyFinite

/-!
# No component of the cycle of `Z` lies in an effective Cartier divisor cut out on `Z`

In the situation of Stacks 0EDT let `X/B` be good, let `(ℒ, s, i : E → X)` be a triple as in
Definition 0ER1 and let `Z ⊆ X` be a closed subspace whose intersection `E ∩ Z` is an effective
Cartier divisor on `Z`.  Then no integral closed subspace occurring in the cycle `[Z]_{k + 1}` of
Stacks 0EE9 is contained in `E`.  The source of Stacks 0ER7 deduces this from the regularity of
`s|_Z`.

## Main results

* `AlgebraicGeometry.Space.not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero`: an
  integral closed subspace with a nonzero coefficient in `[Z]_k` is not contained in the
  vanishing locus of `s`, when `E ∩ Z` is an effective Cartier divisor on `Z`.
* `AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_eq`: **Stacks 0ER7**, given
  Stacks 0EQL for the restricted triple `(Z, ℒ|_Z, s|_Z)`.

## Implementation notes

### The four steps of the non-containment

Write `|Y|` for the point set of a subspace `Y`.  The argument runs in `|X|`, where the three
subspaces in play all have point sets: `T = |Z|` and `|E|` are closed, and `|W|` is the closure
of the generic point of `W`.

1. Stacks 083S: the open complement of `E ∩ Z` in `Z` is scheme-theoretically dense, by
   `isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor`.
2. Scheme-theoretic density gives density of point sets, by
   `AlgebraicGeometry.Space.dense_subspacePointSet_of_isSchemeTheoreticallyDense`.  The inclusion
   of `Z` is a closed embedding on points, so the dense open subset of `|Z|` it produces is
   `|Z| ∖ |E|`, dense in `T`.
3. Stacks 0EE6: a subspace with a nonzero coefficient in `[Z]_k` has for its point set an
   irreducible component of `T`, by
   `AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero`.
4. A dense open subset contains the generic point of every irreducible component.  Stacks 0EE5
   gives the components of `T` only *locally* finitely
   (`AlgebraicGeometry.Space.locallyFinite_irreducibleComponents_of_isClosed`), which is what
   `TopologicalSpace.mem_of_mem_genericPoints_of_dense_of_locallyFinite` asks for: local
   finiteness is exactly what makes the union of the other components closed, and that is the
   only use the argument for finitely many components makes of finiteness.

So the generic point of `W` lies in `|Z| ∖ |E|`.  Were `W` contained in `E`, that point would lie
in `|E|`.

### Why the lemma is stated in the subtype `|Z|`

Step 4 is applied in the topological space `↥T`, not in `|Z|` itself.  Both would do — the
inclusion of `Z` is a closed embedding onto `T` — but local finiteness of the components is
available for a closed subset of the point space of a *good* algebraic space, by Stacks 0EE5, and
`Z` is not assumed good: only `dim_δ(Z) ≤ k`, which is what Stacks 0EE6 needs, is assumed of it.
So the components are those of `↥T`, and the density of step 2 is transported into `↥T` along the
closed embedding.

### The hypotheses of the statement of Stacks 0ER7

In `AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_eq` the cycle `[Z]_{k+1}` is
`AlgebraicGeometry.Space.closedSubspaceCycle`, which needs no hypothesis beyond the δ-dimension
bound.  Stacks 0EQL for `(Z, ℒ|_Z, s|_Z)` is a hypothesis: the family `ic` of cycles
`[E ∩ W]_k`, its agreement `hic` with clause 0ER1(1)(a), and the identity
`hsum : [E ∩ Z]_k = ∑ n_W [E ∩ W]_k`.  The right-hand cycle `β` is supplied with its pinning
equation `hβ`, because forming it directly would need `dim_δ(E ∩ Z) ≤ k`, the statement that an
effective Cartier divisor drops the δ-dimension by one.

## References

* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### The components of the cycle of `Z` avoid the vanishing locus -/

section NonContainment

/-- The topology of the non-containment argument, isolated.  Let `g : α → β` be a closed
embedding whose image has locally finite irreducible components, let `N ⊆ β` be closed and let
`g ⁻¹' Nᶜ` be dense in `α`.  Then a point of `β` whose closure is an irreducible component of
the image of `g` is not in `N`.

The closure of `g ⁻¹' Nᶜ` is everything, so the closure of its image is the image of `g`, which
makes the trace of `Nᶜ` on the subtype `Set.range g` a dense open subset; the closure of the
point in that subtype is the given component, by the closure formula for an inducing map; and
`TopologicalSpace.mem_of_mem_genericPoints_of_dense_of_locallyFinite` applies. -/
private theorem notMem_of_dense_preimage_compl {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : Topology.IsClosedEmbedding g)
    (hlf : LocallyFinite fun C : irreducibleComponents ↥(Set.range g) ↦
      Subtype.val '' (C : Set ↥(Set.range g)))
    {N : Set β} (hN : IsClosed N) (hd : Dense (g ⁻¹' Nᶜ)) {x : β}
    {C : irreducibleComponents ↥(Set.range g)}
    (hxC : closure {x} = Subtype.val '' (C : Set ↥(Set.range g))) : x ∉ N := by
  have hval : Topology.IsClosedEmbedding ((↑) : ↥(Set.range g) → β) :=
    hg.isClosed_range.isClosedEmbedding_subtypeVal
  have hrange : Set.range ((↑) : ↥(Set.range g) → β) = Set.range g := Subtype.range_coe
  have hxR : x ∈ Set.range g := by
    have hx : x ∈ closure ({x} : Set β) := subset_closure rfl
    obtain ⟨c, -, hcx⟩ := hxC ▸ hx
    exact hcx ▸ c.2
  have hUopen : IsOpen (((↑) : ↥(Set.range g) → β) ⁻¹' Nᶜ) :=
    hN.isOpen_compl.preimage continuous_subtype_val
  have hUdense : Dense (((↑) : ↥(Set.range g) → β) ⁻¹' Nᶜ) := by
    have himg : ((↑) : ↥(Set.range g) → β) '' (((↑) : ↥(Set.range g) → β) ⁻¹' Nᶜ) =
        Nᶜ ∩ Set.range g := by
      rw [Set.image_preimage_eq_inter_range, hrange]
    have hcl : closure (Nᶜ ∩ Set.range g) = Set.range g := by
      rw [← Set.image_preimage_eq_inter_range, hg.closure_image_eq, hd.closure_eq,
        Set.image_univ]
    rw [dense_iff_closure_eq]
    refine Set.image_injective.mpr Subtype.val_injective ?_
    rw [← hval.closure_image_eq, himg, hcl, Set.image_univ, hrange]
  have hlf' : LocallyFinite fun C : irreducibleComponents ↥(Set.range g) ↦
      (C : Set ↥(Set.range g)) := by
    simpa [Set.preimage_image_eq _ Subtype.val_injective] using
      hlf.preimage_continuous (continuous_subtype_val (p := fun y ↦ y ∈ Set.range g))
  have hCeq : (C : Set ↥(Set.range g)) = closure {(⟨x, hxR⟩ : ↥(Set.range g))} := by
    rw [hval.isInducing.closure_eq_preimage_closure_image, Set.image_singleton, hxC,
      Set.preimage_image_eq _ Subtype.val_injective]
  have hgp : closure ({(⟨x, hxR⟩ : ↥(Set.range g))} : Set ↥(Set.range g)) ∈
      irreducibleComponents ↥(Set.range g) := hCeq ▸ C.2
  exact mem_of_mem_genericPoints_of_dense_of_locallyFinite hlf' hUopen hUdense hgp

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

/-- **The non-containment step of Stacks 0ER7.**  Let `X/B` be good, let `ℒ` be a sheaf of
modules on `X` with a global section `s` and vanishing locus `E = Z(s)`, and let `Z ⊆ X` be a
closed subspace with `dim_δ(Z) ≤ k` whose intersection `E ∩ Z` is an effective Cartier divisor
on `Z`.  Then an integral closed subspace `W ⊆ X` with a nonzero coefficient in the `k`-cycle
`[Z]_k` of Stacks 0EE9 is not contained in `E`.

The complement of `E ∩ Z` in `Z` is dense on points by Stacks 083S, so its
image `|Z| ∖ |E|` is a dense open subset of `|Z|`; the point set of `W` is an irreducible
component of `|Z|` by Stacks 0EE6; the components of `|Z|` are locally finite by Stacks 0EE5, so
that dense open subset contains the generic point of `W`; and a `W` inside `E` would have that
point in `|E|`. -/
theorem not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero
    (hZdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ (k : EInt))
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩
      (interOnClosedSubspace D p hp L s Z))
    (γZ : points D.site D.base D.base_mem Z.1.toFunctor →
      GeometricPoint D.site D.base D.base_mem Z.1.toFunctor)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : cycleCoeffOfClosedSubspace D p hp Z.1 Z.2 k γZ W ≠ 0) :
    ¬ W.subspace ≤ (vanishingLocus D p hp L s).1 := by
  intro hle
  obtain ⟨C, hC⟩ := exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero D p hp
    Z.1 Z.2 k γZ hZdim W hW
  have hgen : closure {W.ambientGenericPoint D.site D.base D.base_mem} =
      subspacePointSet D.site D.base D.base_mem X W.subspace :=
    W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hp.1
  have hTcl : IsClosed (subspacePointSet D.site D.base D.base_mem X Z.1) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hp.1 Z.1 Z.2
  have hEcl : IsClosed (subspacePointSet D.site D.base D.base_mem X
      (vanishingLocus D p hp L s).1) :=
    isClosed_subspacePointSet_of_isClosedSubspace D hp.1 _ (vanishingLocus D p hp L s).2
  have hg : Topology.IsClosedEmbedding
      (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι) :=
    isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hp.1 Z.2.2
  have hcompl : subspacePointSet D.site D.base D.base_mem Z.1.toFunctor
      (openComplement D.site D.base D.base_mem (interOnClosedSubspace D p hp L s Z).1) =
      (subspacePointSet D.site D.base D.base_mem Z.1.toFunctor
        (interOnClosedSubspace D p hp L s Z).1)ᶜ :=
    range_pointsMap_ι_openComplement D.site D.base D.base_mem _
  have hinter : subspacePointSet D.site D.base D.base_mem Z.1.toFunctor
      (interOnClosedSubspace D p hp L s Z).1 =
      pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι ⁻¹'
        subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L s).1 :=
    subspacePointSet_preimage D.site D.base D.base_mem Z.1.ι (vanishingLocus D p hp L s).1
  have hdense : Dense (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι ⁻¹'
      (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L s).1)ᶜ) := by
    have h : Dense (subspacePointSet D.site D.base D.base_mem Z.1.toFunctor
        (openComplement D.site D.base D.base_mem (interOnClosedSubspace D p hp L s Z).1)) :=
      dense_subspacePointSet_of_isSchemeTheoreticallyDense D.site D.base D.base_mem
        (X := ⟨Z.1.toFunctor, Z.2.1⟩)
        (openComplement D.site D.base D.base_mem (interOnClosedSubspace D p hp L s Z).1)
        (isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor D.site D.base
          D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩ (interOnClosedSubspace D p hp L s Z) hCartier)
    rwa [hcompl, hinter, ← Set.preimage_compl] at h
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hp.1
    D.isAlgebraicSpace p hp.2.2 D.locallyNoetherian
  refine notMem_of_dense_preimage_compl hg (locallyFinite_irreducibleComponents_of_isClosed
    D.site D.base D.base_mem X hp.1 hN _ hTcl) hEcl hdense (hgen.trans hC) ?_
  have hsub : subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X (vanishingLocus D p hp L s).1 := by
    rintro - ⟨y, rfl⟩
    rw [← Subfunctor.homOfLe_ι hle, pointsMap_comp]
    exact ⟨_, rfl⟩
  exact hsub (hgen.le (subset_closure rfl))

end NonContainment

/-! ### Stacks 0ER7 with the non-containment discharged -/

section Main

variable (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p))
    (rule : GysinComponentRule D p (vanishingLocus D p hp L s) k)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

/-- **Stacks 0ER7, given Stacks 0EQL.** In Situation 0EDT let `X/B` be good and let
`(ℒ, s, i : E → X)` be a triple as in Definition 0ER1.  Let `Z ⊆ X` be a closed subspace with
`dim_δ(Z) ≤ k + 1` such that `E ∩ Z` is an effective Cartier divisor on `Z`.  Then
`i^*([Z]_{k + 1}) = [E ∩ Z]_k`.

The cycle `[Z]_{k+1}` is `AlgebraicGeometry.Space.closedSubspaceCycle`, which is Stacks 0EE9 as
an element of `Z_{k+1}(X)`, and `[E ∩ Z]_k` is the element `β` of `Z_k(E)` whose coefficient
family is the one of Stacks 0EE9 for the intersection read on `E`, pinned to it by `hβ`.

The hypotheses `ic`, `hic` and `hsum` are Stacks 0EQL for `(Z, ℒ|_Z, s|_Z)`, the identity
`[E ∩ Z]_k = ∑ n_W [E ∩ W]_k` over the components `W` of `Z` of δ-dimension `k + 1`.  That no
integral closed subspace occurring in `[Z]_{k+1}` is contained in `E` is
`AlgebraicGeometry.Space.not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero`. -/
theorem gysinCycleMap_closedSubspaceCycle_eq
    (_hL : IsInvertibleSheaf D p hp L)
    (hZdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ ((k + 1 : ℤ) : EInt))
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩
      (interOnClosedSubspace D p hp L s Z))
    (γEZ : points D.site D.base D.base_mem
        (interOnVanishingLocus D p hp L s Z).1.toFunctor →
      GeometricPoint D.site D.base D.base_mem
        (interOnVanishingLocus D p hp L s Z).1.toFunctor)
    (β : CycleGroup D ((vanishingLocus D p hp L s).1.ι ≫ p) k)
    (hβ : β.1 = cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p) hE
      (interOnVanishingLocus D p hp L s Z).1 (interOnVanishingLocus D p hp L s Z).2 k γEZ)
    (ic : IntegralClosedSubspace D.site D.base D.base_mem X →
      CycleGroup D ((vanishingLocus D p hp L s).1.ι ≫ p) k)
    (hic : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X)
      (hW : deltaDimension D p W = k + 1)
      (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1),
      ic W = rule.intersectionCycle W hW hWE)
    (hsum : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem
        (vanishingLocus D p hp L s).1.toFunctor,
      cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p) hE
          (interOnVanishingLocus D p hp L s Z).1 (interOnVanishingLocus D p hp L s Z).2 k γEZ T =
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W * (ic W).1 T) :
    gysinCycleMap D p (vanishingLocus D p hp L s) hE k rule
        (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim) = β := by
  refine Subtype.ext (funext fun T => ?_)
  rw [gysinCycleMap_apply, hβ, hsum T]
  refine finsum_congr fun W => ?_
  by_cases hW0 : (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W = 0
  · rw [hW0, zero_mul, zero_mul]
  rw [closedSubspaceCycle_coe] at hW0
  have hWdim : deltaDimension D p W = k + 1 := not_not.1 fun hne =>
    hW0 (cycleCoeffOfClosedSubspace_eq_zero_of_deltaDimension_ne D p hp Z.1 Z.2 (k + 1) _ W hne)
  have hWE := not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero D p hp L s (k + 1) Z
    hZdim hCartier _ W hW0
  rw [gysinComponentCycle_of_not_le D p (vanishingLocus D p hp L s) hE k rule hWdim hWE,
    hic W hWdim hWE]

end Main

end AlgebraicGeometry.Space

end

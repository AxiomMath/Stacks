module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.OffDiagonalIncidenceVariety
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.NowhereDense

/-!
# The incidence variety of lines is taken over the distinct pairs, not over all of `Y × Z`

Stacks tag 0B1R bounds the dimension of the incidence variety
`T = {(y, z, p) : y ∈ Y ∖ Z, z ∈ Z, p ∈ yz}` by `dim Y + dim Z + 1`, the bound coming from the
projection `T ⟶ Y ∖ Z × Z` having the line `yz` as every fibre. The base of that projection is
**not** the whole of `Y ×_k Z`: three points of which two coincide are collinear whatever the
third is, so over a pair `(y, y)` with `y ∈ Y ∩ Z` the fibre of the collinearity subscheme is the
whole of `𝐏(V)`, and no bound of the form `dim Y + dim Z + 1` can hold for the incidence variety
over all of `Y ×_k Z` once `Y ∩ Z` is nonempty.

This file builds the base the source uses: the open subscheme of `Y ×_k Z` on which the first
point avoids `Z`. Over it the two points of a pair are *different points of `𝐏(V)`*, which is the
hypothesis under which the fibre is a line, and its dimension is at most `dim Y + dim Z`. The
incidence variety over it is `AlgebraicGeometry.ProjectiveSpaceOfModule.incidenceVariety` of the
resulting morphism to `𝐏(V) ×_k 𝐏(V)`; no second incidence variety is introduced, since that
construction is already general in its base.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosedOffSnd`: the open subscheme of `Y ×_k Z`
  where the first point avoids `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodOfClosedOffSndToProdTwo`: its morphism to
  `𝐏(V) ×_k 𝐏(V)`, the base of the incidence variety of Tag 0B1R.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.fst_prodOfClosedToProdTwo` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.snd_prodOfClosedToProdTwo`: the two projections of a
  point of `Y ×_k Z`, read in `𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.fst_mem_and_snd_mem_prodOfClosedToProdTwo`: they lie
  in `Y` and in `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.fst_ne_snd_prodOfClosedOffSndToProdTwo`: **over the
  open subscheme the two points of a pair are distinct.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodOfClosedOffSnd_le`: its
  dimension is at most `dim Y + dim Z`.

## Implementation notes

The distinctness delivered here is the inequality of the two *points* of `𝐏(V)`, not the
statement that the pair avoids the diagonal of `𝐏(V) ×_k 𝐏(V)`. The former is strictly stronger
and is what a product of disjoint subsets gives: the first point lies in `Y ∖ Z` and the second in
`Z`, and those are disjoint subsets of `𝐏(V)`. It is also what the fibre argument needs, because
two morphisms `Spec κ(w) ⟶ 𝐏(V)` with different image points are different, so the two
`κ(w)`-points of the fibre are distinct and the degree-one forms vanishing at both have corank
two. Avoiding the diagonal would be the weaker hypothesis — the generic point of
`𝐏(V) ×_k 𝐏(V)` has equal image points under the two projections and is not on the diagonal — and
it is not needed.

The open subscheme is cut out of `Y ×_k Z` rather than built as a product `(Y ∖ Z) ×_k Z`: `Y ∖ Z`
is not closed, so it is not a `closedSubschemeOf`, and the two descriptions have the same
underlying scheme because the first projection of a product restricted to the preimage of an open
is the product of the open with the second factor.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) (hZ : IsClosed Z)

/-- **A closed point of a closed subset of `𝐏(V)` is a closed point of the reduced closed
subscheme on it.** The inclusion of the subscheme is a closed immersion, hence injective, so the
preimage of the singleton is the singleton of the unique preimage; and that preimage is closed
because the inclusion is continuous. -/
public theorem exists_isClosed_closedSubschemeOf {x : projectiveSpaceOfModule k V}
    (hxc : IsClosed ({x} : Set (projectiveSpaceOfModule k V))) (hxY : x ∈ Y) :
    ∃ x₁ : closedSubschemeOf k V Y hY, (closedSubschemeOfι k V Y hY).base x₁ = x ∧
      IsClosed ({x₁} : Set (closedSubschemeOf k V Y hY)) := by
  obtain ⟨x₁, hx₁⟩ : x ∈ Set.range (closedSubschemeOfι k V Y hY).base :=
    (range_closedSubschemeOfι k V Y hY).symm ▸ hxY
  refine ⟨x₁, hx₁, (IsClosedImmersion.isClosedEmbedding
    (closedSubschemeOfι k V Y hY)).isClosed_iff_image_isClosed.2 ?_⟩
  rwa [Set.image_singleton, hx₁]

/-- The first projection of a point of `Y ×_k Z`, read in `𝐏(V)`. -/
public theorem fst_prodOfClosedToProdTwo (s : prodOfClosed k V Y Z hY hZ) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base
        ((prodOfClosedToProdTwo k V Y Z hY hZ).base s) =
      (closedSubschemeOfι k V Y hY).base
        ((pullback.fst (closedSubschemeOfToSpec k V Y hY)
          (closedSubschemeOfToSpec k V Z hZ)).base s) := by
  have h : prodOfClosedToProdTwo k V Y Z hY hZ ≫
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfι k V Y hY :=
    pullback.lift_fst _ _ _
  exact congrArg (fun m : prodOfClosed k V Y Z hY hZ ⟶ projectiveSpaceOfModule k V =>
    m.base s) h

/-- The second projection of a point of `Y ×_k Z`, read in `𝐏(V)`. -/
public theorem snd_prodOfClosedToProdTwo (s : prodOfClosed k V Y Z hY hZ) :
    (pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base
        ((prodOfClosedToProdTwo k V Y Z hY hZ).base s) =
      (closedSubschemeOfι k V Z hZ).base
        ((pullback.snd (closedSubschemeOfToSpec k V Y hY)
          (closedSubschemeOfToSpec k V Z hZ)).base s) := by
  have h : prodOfClosedToProdTwo k V Y Z hY hZ ≫
      pullback.snd (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      pullback.snd (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfι k V Z hZ :=
    pullback.lift_snd _ _ _
  exact congrArg (fun m : prodOfClosed k V Y Z hY hZ ⟶ projectiveSpaceOfModule k V =>
    m.base s) h

/-- **The two points of a pair in `Y ×_k Z` lie in `Y` and in `Z`.** -/
public theorem fst_mem_and_snd_mem_prodOfClosedToProdTwo (s : prodOfClosed k V Y Z hY hZ) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base
          ((prodOfClosedToProdTwo k V Y Z hY hZ).base s) ∈ Y ∧
      (pullback.snd (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base
          ((prodOfClosedToProdTwo k V Y Z hY hZ).base s) ∈ Z := by
  refine ⟨?_, ?_⟩
  · rw [fst_prodOfClosedToProdTwo]
    exact (range_closedSubschemeOfι k V Y hY).subset (Set.mem_range_self _)
  · rw [snd_prodOfClosedToProdTwo]
    exact (range_closedSubschemeOfι k V Z hZ).subset (Set.mem_range_self _)

/-- **The open subscheme of `Y ×_k Z` on which the first point avoids `Z`.** This is the base of
the incidence variety of Tag 0B1R; over the whole of `Y ×_k Z` the fibre of the collinearity
subscheme is not a line along the diagonal. -/
public def prodOfClosedOffSnd : (prodOfClosed k V Y Z hY hZ).Opens :=
  (pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
      closedSubschemeOfι k V Y hY) ⁻¹ᵁ ⟨Zᶜ, hZ.isOpen_compl⟩

/-- A point of the open subscheme has its first point outside `Z`. -/
public theorem fst_notMem_of_mem_prodOfClosedOffSnd {s : prodOfClosed k V Y Z hY hZ}
    (hs : s ∈ prodOfClosedOffSnd k V Y Z hY hZ) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (projectiveSpaceOfModuleToSpec k V)).base
          ((prodOfClosedToProdTwo k V Y Z hY hZ).base s) ∉ Z := by
  rw [fst_prodOfClosedToProdTwo]
  exact hs

/-- **The base of the incidence variety of Tag 0B1R**: the open subscheme of `Y ×_k Z` where the
first point avoids `Z`, mapped to `𝐏(V) ×_k 𝐏(V)`. -/
public def prodOfClosedOffSndToProdTwo :
    (prodOfClosedOffSnd k V Y Z hY hZ).toScheme ⟶ prodTwo k V :=
  (prodOfClosedOffSnd k V Y Z hY hZ).ι ≫ prodOfClosedToProdTwo k V Y Z hY hZ

/-- **Over the open subscheme the two points of a pair are distinct points of `𝐏(V)`.** The first
lies in `Y ∖ Z` and the second in `Z`. This is the hypothesis under which the fibre of the
collinearity subscheme over a pair is a line, and it is exactly what fails over the diagonal
part of `Y ×_k Z`. -/
public theorem fst_ne_snd_prodOfClosedOffSndToProdTwo
    (s : (prodOfClosedOffSnd k V Y Z hY hZ).toScheme) :
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base
        ((prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base s) ≠
      (pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base
        ((prodOfClosedOffSndToProdTwo k V Y Z hY hZ).base s) := by
  have hmem : ((prodOfClosedOffSnd k V Y Z hY hZ).ι).base s ∈
      prodOfClosedOffSnd k V Y Z hY hZ := s.2
  have hout := fst_notMem_of_mem_prodOfClosedOffSnd k V Y Z hY hZ hmem
  have hin := (fst_mem_and_snd_mem_prodOfClosedToProdTwo k V Y Z hY hZ
    (((prodOfClosedOffSnd k V Y Z hY hZ).ι).base s)).2
  intro heq
  rw [prodOfClosedOffSndToProdTwo] at heq
  exact hout (heq ▸ hin)

/-- **The dimension of the base is at most `dim Y + dim Z`.** It is an open subscheme of
`Y ×_k Z`, whose dimension is the sum by Tag 0B2M. -/
public theorem topologicalKrullDim_prodOfClosedOffSnd_le [FiniteDimensional k V] [Nontrivial V] :
    topologicalKrullDim (prodOfClosedOffSnd k V Y Z hY hZ).toScheme ≤
      topologicalKrullDim (closedSubschemeOf k V Y hY) +
        topologicalKrullDim (closedSubschemeOf k V Z hZ) := by
  have hopen : topologicalKrullDim (prodOfClosedOffSnd k V Y Z hY hZ).toScheme =
      topologicalKrullDim ((prodOfClosedOffSnd k V Y Z hY hZ) :
        Set (prodOfClosed k V Y Z hY hZ)) :=
    Eq.trans (IsHomeomorph.topologicalKrullDim_eq _
      (prodOfClosedOffSnd k V Y Z hY hZ).ι.isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph) <|
      IsHomeomorph.topologicalKrullDim_eq _
        (Homeomorph.setCongr (Scheme.Opens.range_ι (prodOfClosedOffSnd k V Y Z hY hZ))).isHomeomorph
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  have hfin : ∀ (W : Set (projectiveSpaceOfModule k V)) (hW : IsClosed W),
      LocallyOfFiniteType (closedSubschemeOfToSpec k V W hW) := fun W hW =>
    inferInstanceAs (LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨W, hW⟩ : Closeds (projectiveSpaceOfModule k V))).subschemeι ≫
        projectiveSpaceOfModuleToSpec k V))
  have := hfin Y hY
  have := hfin Z hZ
  rw [hopen, ← topologicalKrullDim_pullback k (closedSubschemeOfToSpec k V Y hY)
    (closedSubschemeOfToSpec k V Z hZ)]
  exact (topologicalKrullDim_le_of_subset (Set.subset_univ _)).trans topologicalKrullDim_univ.le

end AlgebraicGeometry.ProjectiveSpaceOfModule

end

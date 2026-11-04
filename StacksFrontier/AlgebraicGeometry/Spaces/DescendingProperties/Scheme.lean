module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceCoveringLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusPreimage

/-!
# Descending the property of being a scheme along a limit of algebraic spaces

Let `X = limit D` be the limit of a cofiltered inverse system of quasi-compact algebraic
spaces over `S` with affine transition morphisms. This file reduces "some stage is a scheme"
to a statement about points: if every point of `X` lies in the inverse image of the schematic
locus of some stage, then some stage is a scheme outright.

## Main results

* `AlgebraicGeometry.Space.exists_isRepresentable_obj_of_forall_mem_schematicLocus`: the
  reduction above.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isAffineSpace_limit_restrictDiagram`: an
  affine open subspace of the limit is the inverse image of a quasi-compact open subspace of
  some stage, and the system restricted to that open subspace has affine limit.

## Implementation notes

The schematic locus of Stacks 03JH is the largest open subspace which is a scheme, so a stage
is a scheme exactly when its schematic locus is the whole of it. Two facts turn the pointwise
hypothesis into that conclusion. First, the schematic loci of the stages grow along the
transition morphisms: the preimage of the schematic locus of a stage along an affine morphism
lies in the schematic locus of the source, which is
`AlgebraicGeometry.Space.preimage_schematicLocus_le`, and the transition morphisms of the
system are affine. Second, a monotone family of open subspaces whose inverse images see every
point of the limit is already everything at one stage, which is
`AlgebraicGeometry.Space.exists_eq_top_of_covering_limit`. Applying the second to the family
of schematic loci, whose monotonicity is the first, gives a stage whose schematic locus is
`⊤`; its inclusion is then an isomorphism and the stage is representable.

Quasi-separatedness of the stages is not needed, neither result above using it. The two size
hypotheses are those of Stacks 07SF, inherited unchanged from
`AlgebraicGeometry.Space.exists_eq_top_of_covering_limit`: they are what makes the limit an
algebraic space at all in this presheaf model.

These are the two halves of Stacks 07SR that are independent of Stacks 07SQ. The source's proof
of that tag covers a scheme-like limit by affine opens, descends them to quasi-compact open
subspaces of the stages by Stacks 0827, and appeals to Stacks 07SQ to make each of them affine,
hence a scheme, at a later stage; the schematic loci of the stages then see every point of the
limit and the first result above applies. The second result above is the descent step, and it
delivers the restricted system together with the affineness of its limit, which is exactly the
hypothesis Stacks 07SQ consumes. Its index category is the slice `Over i`, which is cofiltered
by `CategoryTheory.IsCofiltered.over`, with the size bounds supplied by
`AlgebraicGeometry.mk_over_lt` and `AlgebraicGeometry.Space.cardinal_mk_hom_over_lt`.

## References

* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **A stage of a limit is a scheme as soon as the stages' schematic loci see every point of
the limit.** For a cofiltered inverse system of quasi-compact algebraic spaces over `S` with
affine transition morphisms, if every point of `limit D` lies in the inverse image of the
schematic locus of some stage, then some stage is representable by a scheme. -/
theorem exists_isRepresentable_obj_of_forall_mem_schematicLocus
    (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hCompact : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hpoint : ∀ x : points B S hS (limit D), ∃ i,
      pointsMap B S hS (limit D) (limit.π D i) x ∈
        Set.range (pointsMap B S hS (schematicLocus B S hS (D.obj i)).toFunctor
          (schematicLocus B S hS (D.obj i)).ι)) :
    ∃ i, (D.obj i).IsRepresentable := by
  obtain ⟨i, hi⟩ := exists_eq_top_of_covering_limit B S hS D hSize hHomSize hD hAffine hCompact
    (fun i => schematicLocus B S hS (D.obj i))
    (fun i =>
      (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS (hD i)).1)
    (fun {i j} f => preimage_schematicLocus_le B S hS (D.map f) (hD j) (hD i) (hAffine f))
    hpoint
  have _ : (schematicLocus B S hS (D.obj i)).toFunctor.IsRepresentable :=
    (isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS (hD i)).2
  have _ : IsIso (schematicLocus B S hS (D.obj i)).ι :=
    (Subfunctor.eq_top_iff_isIso _).mp hi
  exact ⟨i, isRepresentable_of_natIso (schematicLocus B S hS (D.obj i)).toFunctor
    (asIso (schematicLocus B S hS (D.obj i)).ι)⟩

/-! ### Descending an affine open subspace of the limit -/

/-- **An affine open subspace of the limit comes from a stage, with affine restricted system.**
An affine open subspace `W` of `limit D` is the inverse image of a quasi-compact open subspace
`V` of some stage, by Stacks 0827, and the limit of the system obtained by restricting `D` to
`V` is then affine, being `W`. -/
theorem exists_isOpenSubspace_isAffineSpace_limit_restrictDiagram
    (hSize : #I < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof)
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (W : Subfunctor (limit D)) (hW : IsOpenSubspace B S hS W)
    (hWaff : IsAffineSpace B S hS W.toFunctor) :
    ∃ (i : I) (V : Subfunctor (D.obj i)), IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
      V.preimage (limit.π D i) = W ∧
      IsAffineSpace B S hS (limit (restrictDiagram B S hS D i V.ι)) := by
  obtain ⟨i, V, hV, hVqc, hpre⟩ := exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq
    B S hS D hSize hHomSize hD hAffine W hW hWaff.isQuasiCompactSpace
  refine ⟨i, V, hV, hVqc, hpre, ?_⟩
  have hpreaff : IsAffineSpace B S hS (V.preimage (limit.π D i)).toFunctor := by
    rw [hpre]; exact hWaff
  exact hpreaff.of_iso ((restrictConePtIsoPreimage B S hS D i V).symm.trans
    ((isLimitRestrictCone B S hS D i V.ι).conePointUniqueUpToIso (limit.isLimit _)))

end AlgebraicGeometry.Space

end

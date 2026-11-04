module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBaseInverse

/-!
# Subspaces cut out by points under the change of base of Stacks 04SG

Let `g : V ⟶ S` be a morphism of a big fppf site, let `X` be a presheaf on the big fppf site of `S`
over the representable presheaf of `g`, let `X_V` be the presheaf on the big fppf site of `V` that
Stacks 04SG attaches to it, and let `T ⊆ |X|`. A section of `X_V` over `W ⟶ V` is a section `s` of
`X` over `W ⟶ V ⟶ S` lying over `W ⟶ V`. This file shows that the point-set image of such a
section lies in the inverse image `T_V ⊆ |X_V|` of `T` under the homeomorphism
`AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph` exactly when the point-set image of
`s` lies in `T`, so that the subfunctor `AlgebraicGeometry.Space.openSubspaceOfPoints` of `X_V`
cut out by `T_V` is the one Stacks 04SG attaches to the subfunctor of `X` cut out by `T`.

## Main results

* `AlgebraicGeometry.Space.class_map_relocalizeRep_eq`: the points cut out by a section of `X_V`
  correspond, under the homeomorphism of point spaces, to those cut out by the underlying section
  of `X`.
* `AlgebraicGeometry.Space.hasImageIn_smallerBaseInverse_iff` and
  `AlgebraicGeometry.Space.mem_openSubspaceOfPoints_smallerBaseInverse_iff`: the comparison of the
  two point-set conditions.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)
  (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))

/-- The section of `X` over `W ⟶ V ⟶ S` underlying a section of `X_V` over `W ⟶ V`. -/
abbrev smallerBaseInverseSection {W : BigFppfOver B V hV}
    (x : ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X).obj (op W)) :
    X.left.obj (op ((Over.map g).obj W)) :=
  x.1

/-- **The points cut out by a section over a smaller base.** The field-valued point over `S` cut
out of the section of `X` underlying a section `x` of `X_V` by the extension of a field-valued
point `p` of `W` is the image, under the homeomorphism
`AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph`, of the field-valued point over `V`
cut out of `x` by `p`. -/
theorem class_map_relocalizeRep_eq {W : BigFppfOver B V hV}
    (x : ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X).obj (op W))
    (p : FieldValuedPoint B V hV (yoneda.obj W)) :
    (FieldValuedPoint.map B S hS _ (yonedaEquiv.symm (smallerBaseInverseSection B V S hV hS g X x))
        (FieldValuedPoint.relocalizeRep B V S hV hS g W p)).class B S hS X.left =
      pointsSmallerBaseInverseHomeomorph B V S hV hS g X
        ((FieldValuedPoint.map B V hV _ (yonedaEquiv.symm x) p).class B V hV _) := by
  rw [pointsSmallerBaseInverseHomeomorph_apply, pointsRelocalize_class, pointsMap_class]
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨_, FieldValuedPoint.dominates_refl B S hS _ _, 𝟙 _, ?_⟩
  show X.left.map _ (X.left.map _ (X.left.map _ x.1)) = X.left.map _ x.1
  refine (congrArg (X.left.map _) (FunctorToTypes.map_comp_apply X.left _ _ x.1).symm).trans
    ((FunctorToTypes.map_comp_apply X.left _ _ x.1).symm.trans
    (congrArg (fun k => X.left.map k x.1) (Quiver.Hom.unop_inj (Over.OverMorphism.ext ?_))))
  show 𝟙 _ ≫ 𝟙 _ ≫ p.value.left = p.value.left
  rw [Category.id_comp, Category.id_comp]

/-- A field-valued point of the representable presheaf of `W` viewed over `S`, read back over `V`
and then over `S` again, has the class it started with. -/
theorem class_relocalizeRep_derelocalizeRep {W : BigFppfOver B V hV}
    (q : FieldValuedPoint B S hS (yoneda.obj ((Over.map g).obj W))) :
    (FieldValuedPoint.relocalizeRep B V S hV hS g W
        (FieldValuedPoint.derelocalizeRep B V S hV hS g W q)).class B S hS _ =
      q.class B S hS _ := by
  have hw : q.value.left ≫ (W.hom ≫ g) = (⟨q.toBase⟩ : B.obj q.contained ⟶ B.obj hS) :=
    Over.w q.value
  have hw' : q.value.left.hom ≫ W.hom.hom ≫ g.hom = q.toBase := congrArg (fun k => k.hom) hw
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨q, ?_, FieldValuedPoint.dominates_refl B S hS _ _⟩
  refine ⟨Over.homMk (𝟙 _) (by
    ext
    have hbase : 𝟙 _ ≫ (q.value.left ≫ W.hom).hom ≫ g.hom = q.toBase :=
      (Category.id_comp _).trans ((Category.assoc _ _ _).trans hw')
    exact hbase), ?_⟩
  exact Over.OverMorphism.ext (Category.id_comp _)

/-- **Point-set images over a smaller base.** A section `x` of `X_V` over `W ⟶ V` has point-set
image in the inverse image of `T ⊆ |X|` under
`AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph` exactly when the section of `X`
underlying it has point-set image in `T`. -/
theorem hasImageIn_smallerBaseInverse_iff (T : Set (points B S hS X.left))
    {W : BigFppfOver B V hV}
    (x : ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X).obj (op W)) :
    HasImageIn B V hV _ (pointsSmallerBaseInverseHomeomorph B V S hV hS g X ⁻¹' T) W x ↔
      HasImageIn B S hS X.left T ((Over.map g).obj W)
        (smallerBaseInverseSection B V S hV hS g X x) := by
  rw [hasImageIn_iff_range_subset, hasImageIn_iff_range_subset]
  constructor
  · rintro h _ ⟨y, rfl⟩
    induction y using Quot.ind with | _ q =>
    have hq := h ⟨(FieldValuedPoint.derelocalizeRep B V S hV hS g W q).class B V hV _, rfl⟩
    rw [Set.mem_preimage, pointsMap_class, ← class_map_relocalizeRep_eq] at hq
    show pointsMap B S hS _ _ (q.class B S hS _) ∈ T
    rwa [← class_relocalizeRep_derelocalizeRep B V S hV hS g q, pointsMap_class]
  · rintro h _ ⟨y, rfl⟩
    induction y using Quot.ind with | _ p =>
    show pointsSmallerBaseInverseHomeomorph B V S hV hS g X
      (pointsMap B V hV _ _ (p.class B V hV _)) ∈ T
    rw [pointsMap_class, ← class_map_relocalizeRep_eq]
    exact h ⟨(FieldValuedPoint.relocalizeRep B V S hV hS g W p).class B S hS _, rfl⟩

/-- The same comparison for the subfunctors cut out by the two sets of points, Stacks 03BZ: a
section of `X_V` lies in the subfunctor cut out by the inverse image of `T` exactly when the
section of `X` underlying it lies in the subfunctor cut out by `T`. -/
theorem mem_openSubspaceOfPoints_smallerBaseInverse_iff (T : Set (points B S hS X.left))
    {W : BigFppfOver B V hV}
    (x : ((smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X).obj (op W)) :
    x ∈ (openSubspaceOfPoints B V hV _
        (pointsSmallerBaseInverseHomeomorph B V S hV hS g X ⁻¹' T)).obj (op W) ↔
      smallerBaseInverseSection B V S hV hS g X x ∈
        (openSubspaceOfPoints B S hS X.left T).obj (op ((Over.map g).obj W)) := by
  show Set.range _ ⊆ _ ↔ Set.range _ ⊆ _
  rw [← hasImageIn_iff_range_subset, ← hasImageIn_iff_range_subset]
  exact hasImageIn_smallerBaseInverse_iff B V S hV hS g X T x

end AlgebraicGeometry.Space

end

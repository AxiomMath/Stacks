module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The open complement of a closed subspace

Let `X` be an algebraic space over a scheme `S` and let `Z ⊆ X` be a closed subspace. The
*open complement* `X \ Z` is the subfunctor `AlgebraicGeometry.Space.openComplement` of
`StacksFrontier/AlgebraicGeometry/Spaces/Modifications.lean`: a section of `X` lies in it when
every restriction of that section which factors through `Z` is over an empty scheme. This file
proves that this subfunctor is an open subspace of `X` in the sense of Stacks 02YU, and that
its point set is the set-theoretic complement of the point set of `Z`.

Both facts come from one identification, valid for an arbitrary subfunctor of an arbitrary
presheaf: the complement subfunctor is the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by the complement of the point set.
That identification is purely a statement about field-valued points and needs no hypothesis;
the closedness of the subspace and the algebraicity of the ambient space enter only at the
last step, through Tag 04CD and part (1) of Tag 03BZ.

## Main definitions

No new definitions are introduced. The complement is
`AlgebraicGeometry.Space.openComplement`, already defined in
`StacksFrontier/AlgebraicGeometry/Spaces/Modifications.lean`.

## Main results

* `AlgebraicGeometry.Space.openComplement_eq_openSubspaceOfPoints_compl`: the complement
  subfunctor is cut out by the complement of the point set.
* `AlgebraicGeometry.Space.range_pointsMap_ι_openComplement`: the point set of the complement
  is the complement of the point set.
* `AlgebraicGeometry.Space.isOpenSubspace_openComplement`: the complement of a closed subspace
  of an algebraic space over `S` is an open subspace.
* `AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_compl_range_pointsMap`: the
  same statement for the complement of the point set of an arbitrary closed immersion into an
  algebraic space, which is the shape in which the open complement of a closed immersion is
  usually needed.

## Implementation notes

The identification is proved by comparing membership on both sides at a section `x` of the
ambient presheaf over an object `C` of the site.

That a section of the complement subfunctor has no point in the point set of the subfunctor is
where Tag 03BU is used: if a field-valued point of `h_C` has the same image in the ambient
presheaf as a field-valued point of the subfunctor, the two have a common field-valued
extension, and restricting `x` to the site object of that extension produces a section lying in
the subfunctor over a *field spectrum*, which is never empty. Taking the closed point of that
field spectrum contradicts the defining condition of the complement.

Conversely, if `x` restricts into the subfunctor along `a : C ⟶ D` and the scheme `D` is
nonempty, then a point of `D` gives a point of `h_D` by the Tag 03BX comparison bijection
`AlgebraicGeometry.Space.pointsToScheme`, and its image in the ambient presheaf lies in the
point set of the subfunctor because the restricted section factors through the subfunctor by
`CategoryTheory.Subfunctor.lift`. So the section has a point in the point set, and is not in
the subfunctor cut out by the complement.

Nothing here carries `@[stacks 04E5]`. Tag 04E5 is the full-faithfulness of direct image
along a closed immersion together with the description of its essential image; the open
complement is only the object in terms of which that description is phrased. Stacks has no
separate tag for the open complement itself. Four of 04E5's five assertions are proved and
tagged in `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean` --
full faithfulness on sheaves of sets and on abelian sheaves, and the left-inverse clause for
each -- resting on the cover density and local fullness proved in that module. The one
outstanding assertion is the ESSENTIAL IMAGE, which is phrased in terms of the open complement
defined here, and which needs the restriction functor along that open immersion together with
Étale Cohomology 04CA and 03LR; neither is in this repository.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Membership in the open complement of a subfunctor, unfolded: a section lies in the
complement when every restriction of it which factors through the subfunctor is over an empty
scheme. -/
theorem mem_openComplement_iff (T : Subfunctor F) {C : (BigFppfOver B S hS)ᵒᵖ} (x : F.obj C) :
    x ∈ (openComplement B S hS T).obj C ↔
      ∀ (D : (BigFppfOver B S hS)ᵒᵖ) (a : C ⟶ D), F.map a x ∈ T.obj D →
        IsEmpty ((BigFppfOver.toScheme B S hS).obj D.unop) :=
  Iff.rfl

/-- The open complement of a subfunctor is the subfunctor cut out by the complement of its
point set.

Neither the subfunctor nor the ambient presheaf is assumed to be anything: this is an identity
between two subfunctors of an arbitrary presheaf on the big fppf site of `S`. -/
theorem openComplement_eq_openSubspaceOfPoints_compl (T : Subfunctor F) :
    openComplement B S hS T =
      openSubspaceOfPoints B S hS F (Set.range (pointsMap B S hS T.toFunctor T.ι))ᶜ := by
  ext C x
  constructor
  · intro hx
    rw [mem_openSubspaceOfPoints_iff]
    rintro y ⟨p, rfl⟩
    rw [Set.mem_compl_iff]
    rintro ⟨t, ht⟩
    obtain ⟨P, rfl⟩ := Quot.exists_rep p
    obtain ⟨Q, rfl⟩ := Quot.exists_rep t
    rw [pointsMap_class, pointsMap_class, FieldValuedPoint.class_eq_class_iff] at ht
    -- Repackage the two dominations so that the sources and targets of the two morphisms are
    -- named site objects rather than `siteObject` of a record.
    obtain ⟨r, αT, hT, αP, hP⟩ : ∃ (r : FieldValuedPoint B S hS F)
        (αT : r.siteObject ⟶ Q.siteObject), F.map αT.op Q.value.val = r.value ∧
        ∃ αP : r.siteObject ⟶ P.siteObject, F.map αP.op (F.map P.value.op x) = r.value := by
      obtain ⟨r, ⟨αT, hT⟩, ⟨αP, hP⟩⟩ := ht
      exact ⟨r, αT, hT, αP, hP⟩
    refine (hx (Opposite.op r.siteObject) (αP ≫ P.value).op ?_).elim
      (IsLocalRing.closedPoint r.carrier)
    have h1 : F.map (αP ≫ P.value).op x = r.value := by
      rwa [op_comp, F.map_comp, types_comp_apply]
    rw [h1, ← hT]
    exact T.map αT.op Q.value.property
  · intro hx D a ha
    rw [mem_openSubspaceOfPoints_iff] at hx
    rw [← not_nonempty_iff]
    rintro ⟨pt⟩
    obtain ⟨p, -⟩ := surjective_pointsToScheme B S hS D.unop pt
    have hrange : Subfunctor.range (yoneda.map a.unop ≫ yonedaEquiv.symm x) ≤ T := by
      rintro E y ⟨f, rfl⟩
      have hfa : (yoneda.map a.unop ≫ yonedaEquiv.symm x).app E f =
          F.map f.op (F.map a x) := by
        show F.map (f ≫ a.unop).op x = _
        rw [op_comp, F.map_comp, types_comp_apply, Quiver.Hom.op_unop]
      rw [hfa]
      exact T.map f.op ha
    refine (hx ⟨pointsMap B S hS _ (yoneda.map a.unop) p, rfl⟩)
      ⟨pointsMap B S hS _ (Subfunctor.lift _ hrange) p, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.lift_ι]

/-- The point set of the open complement of a subfunctor is the complement of its point set.

Like `AlgebraicGeometry.Space.openComplement_eq_openSubspaceOfPoints_compl`, this needs no
hypothesis; it is part (1) of Tag 03BZ transported along that identification. -/
theorem range_pointsMap_ι_openComplement (T : Subfunctor F) :
    Set.range (pointsMap B S hS (openComplement B S hS T).toFunctor
        (openComplement B S hS T).ι) =
      (Set.range (pointsMap B S hS T.toFunctor T.ι))ᶜ := by
  rw [openComplement_eq_openSubspaceOfPoints_compl, range_pointsMap_ι_openSubspaceOfPoints]

/-- The open complement of a closed subspace of an algebraic space over `S` is an open
subspace.

The point set of the closed subspace is closed by Tag 04CD, so its complement is open, and
part (1) of Tag 03BZ turns an open set of points into an open subspace. -/
theorem isOpenSubspace_openComplement (hF : IsAlgebraicSpace B S hS F) (T : Subfunctor F)
    (hT : IsClosedSubspace B S hS T) :
    IsOpenSubspace B S hS (openComplement B S hS T) := by
  rw [openComplement_eq_openSubspaceOfPoints_compl]
  exact isOpenSubspace_openSubspaceOfPoints B S hS hF _
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS hF T.ι hT.2).isOpen_compl

/-- The complement of the point set of a closed immersion into an algebraic space over `S`
cuts out an open subspace.

This is the form the open complement of a closed immersion `i : Z ⟶ X` takes when the closed
subspace is presented by the immersion rather than by a subfunctor of `X`; its point set is the
complement of the point set of `i`, by part (1) of Tag 03BZ. -/
theorem isOpenSubspace_openSubspaceOfPoints_compl_range_pointsMap
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) (i : Z ⟶ F)
    (hi : IsClosedImmersion B S hS i) :
    IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS F (Set.range (pointsMap B S hS Z i))ᶜ) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hF _
    (isClosed_range_pointsMap_of_isClosedImmersion B S hS hF i hi).isOpen_compl

end AlgebraicGeometry.Space

end

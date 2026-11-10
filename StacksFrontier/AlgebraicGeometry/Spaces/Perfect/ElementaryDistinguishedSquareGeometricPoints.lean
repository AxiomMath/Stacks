module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyConnectedFiniteSeparable
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints

/-!
# Geometric points of an elementary distinguished square

Let `(U ⊆ W, f : V ⟶ W)` be an elementary distinguished square of algebraic spaces over `S`,
so `U` is an open subspace of `W` and `f` is étale and restricts to an isomorphism over the
reduced closed complement `T = W \ U`. This file counts the lifts of a geometric point
`x̄ : Spec k ⟶ W` through the two legs of the square:

* `x̄` has at most one lift to `U`;
* `x̄` has exactly one lift to `U` precisely when its image point lies in `|U|`;
* `x̄` has exactly one lift to `V` when its image point does not lie in `|U|`.

A lift of `x̄` along `g : Y ⟶ W` is a section of `Y` over the field spectrum of `x̄` which `g`
sends to the section of `x̄`; no extension of the field is allowed.

## Main definitions

* `AlgebraicGeometry.Space.GeometricPointLift` is the type of lifts of a geometric point of
  `W` along a morphism `g : Y ⟶ W`, namely the sections of `Y` over the field spectrum of the
  point which `g` carries to the point's own section.

## Main results

* `AlgebraicGeometry.Space.FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem`: a
  field-valued point is a section of the reduced closed subspace on a closed set of points
  exactly when the point it represents lies in that set.
* `AlgebraicGeometry.Space.subsingleton_geometricPointLift_of_mono`: a geometric point has at
  most one lift along a monomorphism, hence at most one lift to an open subspace.
* `AlgebraicGeometry.Space.nonempty_geometricPointLift_ι_iff_mem_range_pointsMap` and
  `AlgebraicGeometry.Space.existsUnique_geometricPointLift_ι_iff_mem_range_pointsMap`: a
  geometric point of an algebraic space lifts to an open subspace exactly when its image point
  lies in that subspace, and then uniquely.
* `AlgebraicGeometry.Space.existsUnique_geometricPointLift_of_notMem_range_pointsMap`, with its
  two corollaries
  `AlgebraicGeometry.Space.nonempty_geometricPointLift_of_notMem_range_pointsMap` and
  `AlgebraicGeometry.Space.subsingleton_geometricPointLift_of_notMem_range_pointsMap`: a
  geometric point of `W` whose image point misses `|U|` has exactly one lift along the étale
  leg of the square.
* `AlgebraicGeometry.Space.geometricPointLift_dichotomy` collects the three counts into the
  dichotomy itself.

## References

* [Stacks Project, Tag 08GM](https://stacks.math.columbia.edu/tag/08GM)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03JJ](https://stacks.math.columbia.edu/tag/03JJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe w v' u' u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Lifting a section through a morphism which is an isomorphism over a subfunctor -/

/-- A morphism of type-valued functors which restricts to an isomorphism over a subfunctor of
its target has exactly one preimage for every section of the target lying in that subfunctor. -/
private theorem existsUnique_app_eq_of_isIso_fromPreimage {C : Type u'} [Category.{v'} C]
    {X Y : C ⥤ Type w} (f : X ⟶ Y) (T : Subfunctor Y)
    (hiso : IsIso (T.fromPreimage f)) (c : C) (b : Y.obj c) (hb : b ∈ T.obj c) :
    ∃! a : X.obj c, f.app c a = b := by
  have hbij : Function.Bijective ((T.fromPreimage f).app c) :=
    (isIso_iff_bijective _).1 inferInstance
  obtain ⟨p, hp⟩ := hbij.2 ⟨b, hb⟩
  refine ⟨p.1, congrArg Subtype.val hp, fun a ha => ?_⟩
  have hmem : a ∈ (T.preimage f).obj c := show f.app c a ∈ T.obj c from ha ▸ hb
  exact congrArg Subtype.val (hbij.1 ((Subtype.ext ha :
    (T.fromPreimage f).app c ⟨a, hmem⟩ = ⟨b, hb⟩).trans hp.symm))

/-! ### Field-valued points of a reduced closed subspace -/

section ReducedClosed

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A field-valued point is a section of the reduced closed subspace on a closed set of points
exactly when the point it represents lies in that set. -/
theorem FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (Z : Set (points B S hS W)) (hZ : IsClosed Z) (p : FieldValuedPoint B S hS W) :
    p.value ∈ (reducedClosedSubspace B S hS W hW Z hZ).obj (op (p.siteObject B S hS W)) ↔
      p.class B S hS W ∈ Z := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← range_pointsMap_ι_reducedClosedSubspace B S hS W hW Z hZ]
    exact ⟨(⟨p.carrier, p.contained, p.toBase, ⟨p.value, h⟩⟩ :
      FieldValuedPoint B S hS (reducedClosedSubspace B S hS W hW Z hZ).toFunctor).class
        B S hS _, rfl⟩
  · have hred : HasEtaleLocalProperty B S hS (yoneda.obj (p.siteObject B S hS W))
        (fun Y : Scheme.{u} => IsReduced Y) := by
      refine hasEtaleLocalProperty_of_representable B S hS _ _ (p.siteObject B S hS W)
        (Iso.refl _) ?_
      change IsReduced (Spec (.of p.carrier))
      infer_instance
    obtain ⟨g, hg⟩ := (exists_lift_reducedClosedSubspace_iff_pointsMap_range_subset B S hS W hW
      Z hZ (isAlgebraicSpace_yoneda B S hS _) hred (yonedaEquiv.symm p.value)).2 (by
        rintro _ ⟨z, rfl⟩
        rwa [FieldValuedPoint.pointsMap_eq_class])
    have hval := congrArg yonedaEquiv hg
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply] at hval
    exact hval ▸ (yonedaEquiv g).property

end ReducedClosed

/-! ### Lifts of a geometric point -/

/-- A unique solution of a predicate is the same as a nonempty, subsingleton type of solutions. -/
private theorem existsUnique_iff_nonempty_and_subsingleton {α : Type*} (p : α → Prop) :
    (∃! a, p a) ↔ Nonempty {a // p a} ∧ Subsingleton {a // p a} := by
  rw [← unique_subtype_iff_existsUnique, unique_iff_subsingleton_and_nonempty, and_comm]

section Lifts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The lifts of a geometric point `x` of `W` along a morphism `g : Y ⟶ W`: the sections of `Y`
over the field spectrum carried by `x` which `g` sends to the section carried by `x`. -/
abbrev GeometricPointLift {Y W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ W)
    (x : GeometricPoint B S hS W) : Type u :=
  {y : Y.obj (op (x.val.siteObject B S hS W)) //
    g.app (op (x.val.siteObject B S hS W)) y = x.val.value}

/-- A geometric point has at most one lift along a monomorphism. -/
theorem subsingleton_geometricPointLift_of_mono
    {Y W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ W) (hg : Mono g)
    (x : GeometricPoint B S hS W) :
    Subsingleton (GeometricPointLift B S hS g x) := by
  have hinj : Function.Injective (g.app (op (x.val.siteObject B S hS W))) := by
    rw [← mono_iff_injective]
    exact (NatTrans.mono_iff_mono_app g).1 inferInstance _
  exact ⟨fun y z => Subtype.ext (hinj (y.2.trans z.2.symm))⟩

/-- A geometric point of an algebraic space lifts to an open subspace exactly when its image
point lies in that subspace. -/
theorem nonempty_geometricPointLift_ι_iff_mem_range_pointsMap
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (hU : IsOpenSubspace B S hS U) (x : GeometricPoint B S hS W) :
    Nonempty (GeometricPointLift B S hS U.ι x) ↔
      x.image ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  refine Iff.trans ⟨fun ⟨y, hy⟩ => ?_, fun h => ⟨⟨⟨x.val.value, h⟩, rfl⟩⟩⟩
    (FieldValuedPoint.mem_obj_iff_class_mem_range B S hS hW U hU x.val)
  exact (hy : y.val = x.val.value) ▸ y.property

/-- A geometric point of an algebraic space has exactly one lift to an open subspace exactly
when its image point lies in that subspace. -/
theorem existsUnique_geometricPointLift_ι_iff_mem_range_pointsMap
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (U : Subfunctor W) (hU : IsOpenSubspace B S hS U) (x : GeometricPoint B S hS W) :
    (∃! y : U.toFunctor.obj (op (x.val.siteObject B S hS W)),
        U.ι.app (op (x.val.siteObject B S hS W)) y = x.val.value) ↔
      x.image ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) := by
  rw [← nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS hW U hU x,
    existsUnique_iff_nonempty_and_subsingleton]
  exact ⟨And.left, fun h => ⟨h, subsingleton_geometricPointLift_of_mono B S hS U.ι inferInstance x⟩⟩

end Lifts

/-! ### The dichotomy at an elementary distinguished square -/

section Square

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
  (U : Subfunctor W) (f : V ⟶ W)

/-- A geometric point of the target of an elementary distinguished square whose image point
misses the open subspace has exactly one lift along the étale morphism. -/
theorem existsUnique_geometricPointLift_of_notMem_range_pointsMap
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (x : GeometricPoint B S hS W)
    (hx : x.image ∉ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    ∃! y : V.obj (op (x.val.siteObject B S hS W)),
      f.app (op (x.val.siteObject B S hS W)) y = x.val.value :=
  existsUnique_app_eq_of_isIso_fromPreimage f _ hsq.isIsoOverComplement _ _
    ((FieldValuedPoint.mem_obj_reducedClosedSubspace_iff_class_mem B S hS hW
      (Set.range (pointsMap B S hS U.toFunctor U.ι))ᶜ hsq.isClosedComplement x.val).2 hx)

/-- The existence half of
`AlgebraicGeometry.Space.existsUnique_geometricPointLift_of_notMem_range_pointsMap`. -/
theorem nonempty_geometricPointLift_of_notMem_range_pointsMap
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (x : GeometricPoint B S hS W)
    (hx : x.image ∉ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    Nonempty (GeometricPointLift B S hS f x) := by
  exact ((existsUnique_iff_nonempty_and_subsingleton _).1
    (existsUnique_geometricPointLift_of_notMem_range_pointsMap B S hS hW U f hsq x hx)).1

/-- The uniqueness half of
`AlgebraicGeometry.Space.existsUnique_geometricPointLift_of_notMem_range_pointsMap`. -/
theorem subsingleton_geometricPointLift_of_notMem_range_pointsMap
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (x : GeometricPoint B S hS W)
    (hx : x.image ∉ Set.range (pointsMap B S hS U.toFunctor U.ι)) :
    Subsingleton (GeometricPointLift B S hS f x) := by
  exact ((existsUnique_iff_nonempty_and_subsingleton _).1
    (existsUnique_geometricPointLift_of_notMem_range_pointsMap B S hS hW U f hsq x hx)).2

/-- The geometric-point dichotomy for an elementary distinguished square: a geometric point of
the target either lies in the open subspace, and then lifts to it, or it does not, and then it
does not lift to it and does lift along the étale morphism. -/
theorem geometricPointLift_dichotomy
    (hsq : IsElementaryDistinguishedSquare B S hS hW U f) (x : GeometricPoint B S hS W) :
    (x.image ∈ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
        Nonempty (GeometricPointLift B S hS U.ι x)) ∨
      (x.image ∉ Set.range (pointsMap B S hS U.toFunctor U.ι) ∧
        IsEmpty (GeometricPointLift B S hS U.ι x) ∧
        Nonempty (GeometricPointLift B S hS f x)) := by
  have hU := nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS hW U
    hsq.isOpenSubspace x
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS U.toFunctor U.ι)
  · exact Or.inl ⟨hx, hU.2 hx⟩
  · exact Or.inr ⟨hx, not_nonempty_iff.1 (mt hU.1 hx),
      nonempty_geometricPointLift_of_notMem_range_pointsMap B S hS hW U f hsq x hx⟩

end Square

end AlgebraicGeometry.Space

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Prestack
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-!
# The stack of finite-type algebraic spaces (Stacks 04UD)

Let `S` be a scheme contained in a big fppf site `B`. Stacks 04UD asserts the three conditions
of Stacks 026F for the projection from algebraic spaces *of finite type* over varying base
schemes — the full subcategory of the comma category of Stacks 04U8 cut out by finite typeness
of the structure morphism — to the big fppf site of `S`.

Conditions (1) and (2) are proved here; condition (3) and the assembled tag,
`AlgebraicGeometry.finiteTypeSpacesProjection_isStack_of_bootstrap`, are in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/VaryingBase/FiniteTypeEffective.lean`, which carries
the tag. Conditions (1) and (2) are each the restriction of the corresponding condition
for all algebraic spaces, Stacks 04UA, to a full subcategory closed under strongly cartesian
pullback: that closure is condition (1) of Stacks 04TU, so
`CategoryTheory.Functor.isFibered_restrict_of_closed` gives condition (1), and the morphism
presheaf of the restriction is isomorphic to the morphism presheaf of the ambient category
(`CategoryTheory.Functor.morPresheafιIso`), which gives condition (2).

The closure itself is the mathematical content and is the source's appeal to Stacks 03XH. A
morphism of the comma category is strongly cartesian exactly when the square it forms is
cartesian (Stacks 04U9), so the structure morphism of the source is a base change of the
structure morphism of the target, and being of finite type — locally of finite type together
with quasi-compactness — is stable under base change. The locally-of-finite-type half is
`AlgebraicGeometry.Space.isLocallyOfFiniteType_isStableUnderBaseChange`; the
quasi-compactness half is Stacks 03HF,
`AlgebraicGeometry.Space.isQuasiCompact_of_isPullback` of
`StacksFrontier/AlgebraicGeometry/Spaces/MapDescent.lean`. That closes the gap recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/FiniteTypeProperties.lean`,
which states the locally-of-finite-type halves of Stacks 03XG and 03XH only because
quasi-compactness was missing.

## Main definitions

* `AlgebraicGeometry.isFiniteTypeSpace`, the finite-type property on algebraic spaces over
  varying base schemes;
* `AlgebraicGeometry.FiniteTypeSpaces`, the full subcategory it cuts out;
* `AlgebraicGeometry.finiteTypeSpacesProjection`, its projection to the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.finiteTypeSpacesProjection_isFibered`: condition (1) of Stacks 04UD.
* `AlgebraicGeometry.finiteTypeSpacesProjection_isMorSheaf`: condition (2) of Stacks 04UD.
* `AlgebraicGeometry.Space.isQuasiCompact_baseChange`: the base change statement for
  quasi-compactness that condition (1) rests on, read at the chosen fibre product. The tag it
  specialises, **Stacks 03HF**, sits on the cartesian-square form
  `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback` of
  `StacksFrontier/AlgebraicGeometry/Spaces/MapDescent.lean`.
* `AlgebraicGeometry.Space.isEtale_comp_iso`: postcomposing an étale morphism with an
  isomorphism leaves it étale.

## Implementation notes

Condition (3), effective descent, lives in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/VaryingBase/FiniteTypeEffective.lean`. The source
obtains it from Bootstrap, Lemma 0ADV part (2), whose proof goes through Bootstrap, Theorem 04S6,
and this file is upstream of the proof of that theorem in the import graph.

Conditions (1) and (2) are stated in the shape the fields of `CategoryTheory.Functor.IsStack`
take them, exactly as Stacks 04UA is stated in
`StacksFrontier/AlgebraicGeometry/Spaces/Prestack.lean`, so that the three can be assembled into
that structure without restating the instance.

## References

* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Postcomposing an étale morphism with an isomorphism leaves it étale. -/
theorem isEtale_comp_iso {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ F) (e : F ≅ F')
    (hf : IsEtale B S hS f) : IsEtale B S hS (f ≫ e.hom) := by
  intro V φ hφ
  rw [← Category.assoc]
  exact MorphismProperty.RespectsIso.postcomp _ e.hom _ (hf V φ hφ)

/-- The base change of a quasi-compact morphism of algebraic spaces over `S` along an
arbitrary morphism is quasi-compact.

This is the shape in which the source states Stacks 03HF. The tag sits on the
cartesian-square form `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`, which this
specialises at `CategoryTheory.IsPullback.of_hasPullback`. -/
theorem isQuasiCompact_baseChange {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (g : H ⟶ G) (hf : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (pullback.fst g f) :=
  isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback g f).flip hf

end Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over a scheme in the big fppf site of `S` whose structure morphism is of
finite type. -/
abbrev isFiniteTypeSpace : ObjectProperty
    (Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  fun X ↦ Space.IsFiniteType B S hS X.hom

/-- Algebraic spaces of finite type over varying schemes in the big fppf site of `S`. -/
abbrev FiniteTypeSpaces := (isFiniteTypeSpace B S hS).FullSubcategory

/-- The projection from finite-type algebraic spaces over varying schemes to their bases. -/
abbrev finiteTypeSpacesProjection :
    FiniteTypeSpaces B S hS ⥤ BigFppfOver B S hS :=
  (isFiniteTypeSpace B S hS).ι ⋙ spacesProjection B S hS

/-- A strongly cartesian morphism of the comma category of Stacks 04U8 exhibits the structure
morphism of its source as a base change of the structure morphism of its target. -/
theorem isPullback_hom_of_isStronglyCartesian
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (hm : (spacesProjection B S hS).IsStronglyCartesian m.right m) :
    IsPullback A.hom m.left.hom (yoneda.map m.right) C.hom := by
  rw [spacesProjection_isStronglyCartesian_iff] at hm
  have hiso : IsIso (pullback.lift A.hom m.left.hom m.w.symm) := by
    have hc : IsIso (ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap m.right)
          (ObjectProperty.homMk C.hom)) := hm
    exact inferInstanceAs (IsIso ((ObjectProperty.ι _).map
      (ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap m.right)
          (ObjectProperty.homMk C.hom))))
  exact IsPullback.of_iso_pullback ⟨m.w.symm⟩ (asIso (pullback.lift A.hom m.left.hom m.w.symm))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The same square as `AlgebraicGeometry.isPullback_hom_of_isStronglyCartesian`, read in the
category of algebraic spaces over `S`, where the structure morphisms are the morphisms of
algebraic spaces of Stacks 04U8. -/
theorem isPullback_commaHomAsSpaceMap_of_isStronglyCartesian
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (hm : (spacesProjection B S hS).IsStronglyCartesian m.right m) :
    IsPullback m.left (commaHomAsSpaceMap A) (commaHomAsSpaceMap C) (schemeSpaceMap m.right) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    (isPullback_hom_of_isStronglyCartesian B S hS m hm).flip

/-- Condition (1) of Stacks 04TU for finite typeness: a strongly cartesian morphism whose target
is of finite type over its base has source of finite type over its base.

This is the source's appeal to Stacks 03XH inside the proof of Stacks 04UD. -/
theorem closedUnderStronglyCartesian_isFiniteTypeSpace :
    Functor.ClosedUnderStronglyCartesian (spacesProjection B S hS) (isFiniteTypeSpace B S hS) := by
  intro V U A C g m hm hC
  have hV : A.right = V := IsHomLift.domain_eq (spacesProjection B S hS) g m
  have hU : C.right = U := IsHomLift.codomain_eq (spacesProjection B S hS) g m
  subst hV
  subst hU
  have hg : m.right = g := by
    simpa using IsHomLift.fac' (spacesProjection B S hS) g m
  have hm' : (spacesProjection B S hS).IsStronglyCartesian m.right m := by rw [hg]; exact hm
  refine Functor.isoOverId_of_prop (P := isFiniteTypeSpace B S hS) ?_
  exact ⟨(Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS m hm') hC.1,
    Space.isQuasiCompact_of_isPullback B S hS
      (isPullback_hom_of_isStronglyCartesian B S hS m hm').flip hC.2⟩

/-- **Condition (1) of Stacks 04UD.** The projection from finite-type algebraic spaces over
varying schemes to the big fppf site of `S` is a fibred category. -/
@[stacks 04UD "condition (1)"]
theorem finiteTypeSpacesProjection_isFibered :
    (finiteTypeSpacesProjection B S hS).IsFibered :=
  have := spacesProjection_isFibered B S hS
  Functor.isFibered_restrict_of_closed (spacesProjection B S hS) (isFiniteTypeSpace B S hS)
    (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS)

/-- **Condition (2) of Stacks 04UD.** Morphisms of finite-type algebraic spaces over a fixed
scheme satisfy fppf descent. -/
@[stacks 04UD "condition (2)"]
theorem finiteTypeSpacesProjection_isMorSheaf :
    haveI : (finiteTypeSpacesProjection B S hS).IsFibered :=
      finiteTypeSpacesProjection_isFibered B S hS
    ∀ (U : BigFppfOver B S hS)
      (X Y : (finiteTypeSpacesProjection B S hS).Fiber U),
      (finiteTypeSpacesProjection B S hS).IsMorSheaf
        (BigFppfOver.topology B S hS) U X Y := by
  have := spacesProjection_isFibered B S hS
  have := finiteTypeSpacesProjection_isFibered B S hS
  intro U X Y
  exact (Presheaf.isSheaf_of_iso_iff
      (Functor.morPresheafιIso (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS) X Y)).2
    (spacesProjection_isMorSheaf B S hS U
      (Functor.fiberι _ _ X) (Functor.fiberι _ _ Y))

end AlgebraicGeometry

end

module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianUnderlyingSets
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.MorphismOfTopoiSectionRelocalization
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of an abelian sheaf along a morphism of topoi

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi between the topoi of sheaves of sets on two
small sites — an adjoint pair with left exact inverse image, and no functor between the sites.
Such an `f` carries sheaves of abelian groups along `f⁻¹` as well, by
`CategoryTheory.Sites.abelianInverseImage`: the group operations are read as operations on
internal commutative group objects, the left exact `f⁻¹` carries those to group operations
again, and the result is read back sectionwise. Tag 093R asserts that `f⁻¹` preserves local
constancy not only for sheaves of sets but also for sheaves of groups, abelian groups, rings and
modules; this file proves the *finite* abelian case of that assertion.

The argument is the one that the condition allows: finite local constancy of an abelian sheaf is
a property of its underlying sheaf of sets
(`Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_forget`), the underlying sheaf of sets of
`abelianInverseImage f` is `f⁻¹` of the underlying sheaf of sets on the nose
(`CategoryTheory.Sites.abelianInverseImage_forgetIso` is `Iso.refl`), and `f⁻¹` preserves finite
local constancy of sheaves of sets by
`MorphismOfTopoi.isFiniteLocallyConstant_inverseImage_of_smallSites`.

## Main results

* `MorphismOfTopoi.isFiniteLocallyConstant_abelianInverseImage_of_smallSites` — **Tag 093R** for
  finite locally constant sheaves of abelian groups: the inverse image of a finite locally
  constant abelian sheaf along an arbitrary morphism of topoi between the topoi of sheaves of
  sets on two small sites is finite locally constant.

## What of Tag 093R is *not* proved here

The tag also asserts the statement for a locally constant sheaf of abelian groups which is not
finite, and for sheaves of groups, of rings and of modules over a fixed ring. None of those is
below, and the route taken here does not reach them:
`Stacks.ConstantSheaf.isFiniteLocallyConstant_of_forget` is a theorem about *finite* values, and
its unrestricted analogue is false — an abelian sheaf whose underlying sheaf of sets is locally
constant need not be locally constant as an abelian sheaf, since a bijection between the
trivializing values carries no group structure.

The non-finite abelian case is reached by a different route, in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianLocallyConstantInverseImage`: carrying a
trivialization of an abelian sheaf across the relocalization of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.MorphismOfTopoiSectionRelocalization` requires
that relocalization to be read on internal commutative group objects, and
`MorphismOfTopoi.abelianSectionRelocalization` does read it there.

For sheaves of groups, of rings and of modules the library still has only
`Stacks.ConstantSheaf.isLocallyConstant_sheafPullback`, which holds for an arbitrary coefficient
category but only for the inverse image along a *morphism of sites*, i.e. along a continuous
left exact cover-preserving functor between the two sites; a morphism of topoi need not be
induced by such a functor.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf

universe w

namespace MorphismOfTopoi

variable {C : Type w} [SmallCategory C] {D : Type w} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w)))

/-- **Tag 093R, the finite abelian case.** The inverse image of a finite locally constant sheaf
of abelian groups along an arbitrary morphism of topoi between the topoi of sheaves of sets on
two small sites is finite locally constant.

No functor between the two sites is assumed. Finite local constancy of an abelian sheaf is a
property of its underlying sheaf of sets by
`Stacks.ConstantSheaf.isFiniteLocallyConstant_iff_forget`, the underlying sheaf of sets of the
abelian inverse image is the geometric inverse image of the underlying sheaf of sets, and the
latter preserves finite local constancy by
`MorphismOfTopoi.isFiniteLocallyConstant_inverseImage_of_smallSites`. -/
@[stacks 093R "finite locally constant sheaves of abelian groups, for an arbitrary morphism of \
  topoi between the topoi of sheaves of sets on two small sites"]
public lemma isFiniteLocallyConstant_abelianInverseImage_of_smallSites
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ V : D, HasWeakSheafify (K.over V) AddCommGrpCat.{w}]
    (G : Sheaf K AddCommGrpCat.{w}) [hG : IsFiniteLocallyConstant K G] :
    IsFiniteLocallyConstant J ((CategoryTheory.Sites.abelianInverseImage f).obj G) :=
  isFiniteLocallyConstant_of_forget J _
    (isFiniteLocallyConstant_inverseImage_of_smallSites J K f _
      (hG := isFiniteLocallyConstant_forget K G hG))

end MorphismOfTopoi

end

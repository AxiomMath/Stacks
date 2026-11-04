module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackAtAPointPair
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberGerm
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The fibre of the structure map on sheaves of sets, as a transpose

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a geometric
point of `X`.  The fibre comparison of Stacks 04K2, part (4) for sheaves of sets,
`AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso`, followed by the fibre at `x` of the
inverse-image form `f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of Stacks 03G8, is a homomorphism
`(𝒪_Y)_{f ∘ x} ⟶ (𝒪_X)_x` of the structure-sheaf fibres, read on sheaves of sets.

This file identifies that composite as a *transpose*: it is the adjunct, across the skyscraper
adjunction at the image point, of the structure map followed by the direct image of germ
formation at `x` and the skyscraper comparison of Stacks 03G8.  That is the form in which the
composite can be computed on germs, since the skyscraper adjunction reads germs off the
components of a map into a skyscraper:
`CategoryTheory.GrothendieckTopology.Point`'s
`toPresheafFiber_comp_skyscraperSheafAdjunction_homEquiv_symm`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleStructureSetSheaf`: the sheaf of sets underlying the
  structure sheaf of the small étale ringed topos.
* `AlgebraicGeometry.Space.smallEtaleStructureSetUnit`: germ formation at `x`, read as a map
  into the skyscraper with value the fibre.
* `AlgebraicGeometry.Space.smallEtaleStructureSetSkyscraperHom`: the map out of the structure
  sheaf of `Y` whose transpose the composite is.

## Main results

* `AlgebraicGeometry.Space.fiberIso_comp_setFSharpInverseImage`: the composite is that
  transpose.
* `AlgebraicGeometry.Space.setFSharp_eq_forgetRing_fSharp`: the direct-image form of the
  structure map does not depend on whether the ring operations are forgotten in one step or in
  two.

## Implementation notes

The transpose identity is `CategoryTheory.Adjunction.conjugate_comp` for the composite
adjunction `f⁻¹ ⊣ f_*` followed by the skyscraper adjunction at `x`, which is what makes the
fibre comparison the *conjugate* of the skyscraper comparison rather than an arbitrary
isomorphism of the two functors.  Its three object arguments are supplied explicitly: left to
unification, solving `f_*(?B) =?= (sheafCompose (forget RingCat)).obj (pushforwardRingSheaf …)`
is a higher-order problem that exhausts the heartbeat budget, whereas with `A`, `B` and `M`
given the proof elaborates in a few seconds.

The passage between the two forgetful readings of the structure map is proved by exhibiting
both as the adjunct of one and the same map of sheaves of sets: the ring-level one by
`AlgebraicGeometry.RingedToposHom.ringSheafMap_ringFsharp` and the commutative-ring-level one by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`; the two inverse-image
forms agree on the nose, since `forget₂ CommRingCat RingCat` followed by `forget RingCat` is
`forget CommRingCat`.

## References

* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the small étale ringed topos of an algebraic space, as a sheaf of
(not necessarily commutative) rings. -/
abbrev smallEtaleStructureRingSheaf (Z : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS Z.1) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Z).O

/-- The sheaf of sets underlying the structure sheaf of the small étale ringed topos of an
algebraic space. -/
abbrev smallEtaleStructureSetSheaf (Z : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  (sheafCompose (SmallEtale.topology B S hS Z.1) (forget RingCat.{u})).obj
    (smallEtaleStructureRingSheaf B S hS Z)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The fibre at `x` of the sheaf of sets underlying the structure sheaf of `X`. -/
abbrev smallEtaleStructureSetFiber :=
  ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)).obj
    (smallEtaleStructureSetSheaf B S hS X)

/-- The unit of the skyscraper adjunction at `x` at the sheaf of sets underlying the structure
sheaf: germ formation at `x`, read as a map into the skyscraper with value the fibre. -/
abbrev smallEtaleStructureSetUnit :
    smallEtaleStructureSetSheaf B S hS X ⟶
      (etaleSitePoint B S hS X.1 x X.2).skyscraperSheafFunctor.obj
        (smallEtaleStructureSetFiber B S hS x) :=
  ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction (A := Type u)).homEquiv
    (smallEtaleStructureSetSheaf B S hS X) (smallEtaleStructureSetFiber B S hS x) (𝟙 _)

/-- The map out of the structure sheaf of `Y` whose transpose across the skyscraper adjunction
at the image point is the fibre comparison followed by the fibre of the structure map: the
structure map of Stacks 03G8 on sheaves of sets, the direct image of germ formation at `x`, and
the skyscraper comparison of Stacks 03G8. -/
abbrev smallEtaleStructureSetSkyscraperHom :
    smallEtaleStructureSetSheaf B S hS Y ⟶
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafFunctor.obj
        (smallEtaleStructureSetFiber B S hS x) :=
  (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
      (smallEtaleRingedToposModulesHom B S hS f).fSharp ≫
    (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward.map
      (smallEtaleStructureSetUnit B S hS x) ≫
    (smallEtaleSkyscraperIso B S hS f x).hom.app (smallEtaleStructureSetFiber B S hS x)

/-- The fibre comparison of Stacks 04K2, part (4) for sheaves of sets, followed by the fibre at
`x` of the inverse-image form of the structure map of Stacks 03G8, is the transpose across the
skyscraper adjunction at the image point of
`AlgebraicGeometry.Space.smallEtaleStructureSetSkyscraperHom`.

This is the whole use made of the fact that the fibre comparison is the *conjugate* of the
skyscraper comparison rather than an arbitrary isomorphism of the two functors. -/
theorem fiberIso_comp_setFSharpInverseImage :
    (smallEtaleInverseImageFiberIso B S hS f x).hom.app
          (smallEtaleStructureSetSheaf B S hS Y) ≫
        ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)).map
          ((sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
            (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage) =
      (((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction
          (A := Type u)).homEquiv (smallEtaleStructureSetSheaf B S hS Y)
          (smallEtaleStructureSetFiber B S hS x)).symm
        (smallEtaleStructureSetSkyscraperHom B S hS f x) := by
  have hadj : ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv
        (smallEtaleStructureSetSheaf B S hS Y) (smallEtaleStructureSetSheaf B S hS X)).symm
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp) =
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage :=
    (Equiv.symm_apply_eq _).2 (smallEtaleRingedToposModulesHom B S hS f).fSharp_adjunct
  have hcc := Adjunction.conjugate_comp
    (A := smallEtaleStructureSetSheaf B S hS Y) (B := smallEtaleStructureSetSheaf B S hS X)
    (M := smallEtaleStructureSetFiber B S hS x)
    (smallEtaleRingedToposHom B S hS f).toToposHom.adj
    ((etaleSitePoint B S hS X.1 x X.2).skyscraperSheafAdjunction (A := Type u))
    ((etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2).skyscraperSheafAdjunction
      (A := Type u))
    (smallEtaleSkyscraperIso B S hS f x)
    ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
      (smallEtaleRingedToposModulesHom B S hS f).fSharp) (𝟙 _) _
    (Equiv.apply_symm_apply _ _).symm
  rw [hadj, Category.comp_id] at hcc
  exact hcc

/-- The structure map of Stacks 03G8 read on sheaves of sets does not depend on whether the ring
operations are forgotten in one step or in two: the direct-image form of the structure map of the
four-field morphism of ringed topoi, with the ring operations forgotten, is the direct-image form
of the structure map with the commutative-ring operations forgotten.

Both are the adjunct of one and the same map of sheaves of sets, by
`AlgebraicGeometry.RingedToposHom.ringSheafMap_ringFsharp` on one side and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` on the other. -/
theorem setFSharp_eq_forgetRing_fSharp :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget RingCat.{u})).map
        (smallEtaleRingedToposModulesHom B S hS f).fSharp =
      (smallEtaleRingedTopos B S hS Y).forgetRing.map
        (smallEtaleRingedToposHom B S hS f).fSharp := by
  refine Eq.trans (AlgebraicGeometry.RingedToposHom.ringSheafMap_ringFsharp
    (smallEtaleRingedToposHom B S hS f)) ?_
  refine Eq.trans (congrArg
    ((smallEtaleRingedToposHom B S hS f).toToposHom.adj.homEquiv
      ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
      ((smallEtaleRingedTopos B S hS X).forgetRing.obj (smallEtaleRingedTopos B S hS X).O))
    (AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
      (smallEtaleRingedToposHom B S hS f))) ?_
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Space

end

end

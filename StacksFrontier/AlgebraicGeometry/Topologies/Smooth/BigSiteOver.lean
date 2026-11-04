module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.StandardCovering

/-!
# The big and big affine smooth sites of a scheme

Let `B` be a big smooth site containing a scheme `S`. This file defines the slice of `B` over `S`
and its full subcategory on affine objects, together with their covering families and Grothendieck
topologies.

## Main definitions

* `AlgebraicGeometry.BigSmoothOver`: the big smooth category over `S`, the slice of `B` over `S`.
* `AlgebraicGeometry.BigSmoothOver.IsCovering`: its covering families, those whose underlying
  family is a covering of `B`.
* `AlgebraicGeometry.BigSmoothOver.topology`: the localized Grothendieck topology of `B` over `S`.
* `AlgebraicGeometry.BigAffineSmooth`: the full subcategory of `BigSmoothOver` consisting of
  affine schemes.
* `AlgebraicGeometry.BigAffineSmooth.IsCovering`: its covering families, those which are coverings
  in `BigSmoothOver` and whose underlying family is a standard smooth covering.
* `AlgebraicGeometry.BigAffineSmooth.topology`: the Grothendieck topology these families generate.

## References

* [Stacks Project, Tag 03X0](https://stacks.math.columbia.edu/tag/03X0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)

/-- The object of the chosen big smooth category represented by `S`. -/
public abbrev BigSmoothSite.base : B.category := ⟨S, hS⟩

/-- The big smooth category over `S`: the slice of the chosen big smooth category over `S`. -/
@[stacks 03X0 "part (1), category"]
public abbrev BigSmoothOver := Over (B.base S hS)

namespace BigSmoothOver

/-- The forgetful functor from the big smooth category over `S` to the chosen big smooth
category. -/
public abbrev forget : BigSmoothOver B S hS ⥤ B.category := Over.forget (B.base S hS)

/-- The canonical functor from the big smooth category over `S` to schemes. -/
public abbrev toScheme : BigSmoothOver B S hS ⥤ Scheme.{u} :=
  forget B S hS ⋙ ObjectProperty.ι _

/-- A family in the big smooth category over `S` is covering precisely when its underlying family
is a covering in the chosen big smooth site. -/
@[stacks 03X0 "part (1), coverings"]
public abbrev IsCovering (E : Covering (BigSmoothOver B S hS)) : Prop :=
  B.IsCovering ⟨(Over.forget (B.base S hS)).obj E.1,
    E.2.map (Over.forget (B.base S hS))⟩

/-- The Grothendieck topology of the localized big smooth site over `S`. -/
public abbrev topology : GrothendieckTopology (BigSmoothOver B S hS) :=
  B.grothendieckTopology.over (B.base S hS)

end BigSmoothOver

/-- The property of an object of the big smooth category over `S` that its underlying scheme is
affine. -/
public abbrev BigSmoothOver.IsAffineOver : ObjectProperty (BigSmoothOver B S hS) :=
  fun X ↦ IsAffine ((BigSmoothOver.toScheme B S hS).obj X)

/-- The big affine smooth category over `S`: the full subcategory of the big smooth category over
`S` consisting of the objects whose underlying scheme is affine. -/
@[stacks 03X0 "part (2), category"]
public abbrev BigAffineSmooth := (BigSmoothOver.IsAffineOver B S hS).FullSubcategory

namespace BigAffineSmooth

/-- The canonical full embedding of the big affine smooth category into the big smooth category
over `S`. -/
public abbrev inclusion : BigAffineSmooth B S hS ⥤ BigSmoothOver B S hS :=
  (BigSmoothOver.IsAffineOver B S hS).ι

/-- The canonical functor from the big affine smooth category over `S` to schemes. -/
public abbrev toScheme : BigAffineSmooth B S hS ⥤ Scheme.{u} :=
  inclusion B S hS ⋙ BigSmoothOver.toScheme B S hS

/-- The underlying scheme of an object of the big affine smooth category is affine. -/
public instance isAffine_toScheme_obj (X : BigAffineSmooth B S hS) :
    IsAffine ((toScheme B S hS).obj X) := X.property

/-- A family in the big affine smooth category is standard smooth when its underlying finite family
of scheme morphisms is a standard smooth covering. -/
public abbrev IsStandardSmoothCovering (E : Covering (BigAffineSmooth B S hS)) : Prop :=
  ∃ hI : Finite E.2.I₀,
    @AlgebraicGeometry.IsStandardSmoothCovering ((toScheme B S hS).obj E.1) E.1.2
      E.2.I₀ hI (fun i ↦ (toScheme B S hS).obj (E.2.X i)) (fun i ↦ (E.2.X i).2)
      (fun i ↦ (toScheme B S hS).map (E.2.f i))

/-- A family in the big affine smooth category over `S` is covering precisely when its image in the
big smooth category over `S` is covering and its underlying family is a standard smooth
covering. -/
@[stacks 03X0 "part (2), coverings"]
public abbrev IsCovering (E : Covering (BigAffineSmooth B S hS)) : Prop :=
  BigSmoothOver.IsCovering B S hS
      ⟨(inclusion B S hS).obj E.1, E.2.map (inclusion B S hS)⟩ ∧
    IsStandardSmoothCovering B S hS E

/-- The precoverage of the big affine smooth category over `S` whose covering presieves are those
of the covering families `IsCovering`. -/
public def precoverage : Precoverage (BigAffineSmooth B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩}

/-- The Grothendieck topology on the big affine smooth category over `S` generated by its covering
families. -/
public abbrev topology : GrothendieckTopology (BigAffineSmooth B S hS) :=
  (precoverage B S hS).toGrothendieck

end BigAffineSmooth

end AlgebraicGeometry

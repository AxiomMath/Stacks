module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelowPlus
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.StandardUpperShriekPlus
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts

/-!
# Transporting a functor between `D_QCoh` and `D⁺_QCoh`

The duality statements of [Stacks, Section 0AU3] are about functors of the bounded-below
quasi-coherent derived categories `D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`, while the functors this
repository constructs — `Stacks.Duality.upperShriek` of [Stacks, Tag 0A9Y], the twisted inverse
image of [Stacks, Tag 0A9E] — are functors of the unbounded `D_QCoh`. `D⁺_QCoh` is a full
subcategory of `D_QCoh` cut out by a property of objects, so a functor of the latter that carries
bounded-below objects to bounded-below objects restricts to one of the former, and the restriction
has the *same* value on objects. This file is that transport and its one-line consequences.

The boundedness hypothesis is the only input: it is [Stacks, Tag 0A9I] for the twisted inverse
image, and `Stacks.Duality.isBoundedBelow_upperShriek_obj` for `f^!`.

Since the transport changes nothing on objects, a statement about the underlying complex of a
value of the restricted functor *is* the statement about the underlying complex of the value of
the original. That is what makes a `D⁺_QCoh`-typed statement — such as the conclusion of
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts` — reachable from a `D_QCoh`-typed one.

## Main definitions

All in the namespace `Stacks.Duality`.

* `quasiCoherentPlusLift` — the restriction of `F : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` to the
  bounded-below parts, with the model of the derived categories a free binder, so that it applies
  in particular at `CategoryTheory.HasDerivedCategory.standard`, where it lands in
  `Stacks.Duality.quasiCoherentDerivedCategoryPlus` — the category in which
  `Stacks.Duality.isDualizingComplex_upperShriek_of_fts` reads its `f^!` parameter.

## Main results

* `quasiCoherentDerivedCategoryPlus_eq_ofModel_standard` —
  `Stacks.Duality.quasiCoherentDerivedCategoryPlus`, whose model is pinned in its own body, is
  `Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel` at the standard model. This is the
  identification that lets the model-free transport be used where the pinned category is wanted.
* `quasiCoherentPlusLift_obj_obj`, `quasiCoherentPlusLift_obj_obj_obj` and
  `quasiCoherentPlusLift_comp_ι` — the transport is the identity on objects, and composing it
  with the inclusion of the bounded-below part gives back the original functor after that
  inclusion.
* `upperShriekPlus_eq_quasiCoherentPlusLift` and
  `standardUpperShriekPlus_eq_quasiCoherentPlusLift` — the two bounded-below functors the
  repository already has are this transport applied to `f^!` and to the right adjoint of `Rf_*`.
  Nothing below duplicates them.
* `isDualizingComplex_upperShriekPlus_obj` — the transport at work: `f^!` of a dualizing complex
  is dualizing, stated for `Stacks.Duality.upperShriekPlus` on `D⁺_QCoh`, from the statement for
  `Stacks.Duality.upperShriek` on `D_QCoh`.

## Implementation notes

*No `@[stacks]` attribute is placed on anything in this file, and no tag's coverage changes.*
`quasiCoherentPlusLift` is a restriction of a functor to a full subcategory, which is
`CategoryTheory.ObjectProperty.lift` and no mathematics. The boundedness inputs it consumes are
registered where they are proved. `isDualizingComplex_upperShriekPlus_obj` is
`Stacks.Duality.isDualizingComplex_upperShriek_obj` read through the transport at one functor;
restricting the domain of a statement makes it weaker, not stronger, so it states no tag that its
input does not already state.

The model-free `quasiCoherentPlusLift` carries two independent
`CategoryTheory.HasDerivedCategory` universes, one for each scheme, because the two schemes'
derived categories are chosen separately everywhere else in the development; at the standard
model both are forced.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe w w' u

namespace Stacks.Duality

/-- **The pinned and the model-free bounded-below quasi-coherent derived categories agree at the
standard model.** `Stacks.Duality.quasiCoherentDerivedCategoryPlus` is defined in a file that
pins `CategoryTheory.HasDerivedCategory.standard`, so it is
`Stacks.Duality.quasiCoherentDerivedCategoryPlusOfModel` at that instance. -/
theorem quasiCoherentDerivedCategoryPlus_eq_ofModel_standard (Z : Scheme.{u}) :
    quasiCoherentDerivedCategoryPlus Z =
      @quasiCoherentDerivedCategoryPlusOfModel Z (HasDerivedCategory.standard _) :=
  rfl

section Lift

variable {X Y : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} Y.Modules]

/-- **A functor of the quasi-coherent derived categories preserving bounded-below cohomology
restricts to the bounded-below parts.** `D⁺_QCoh` is the full subcategory of `D_QCoh` on the
objects with bounded-below cohomology, so this is the restriction of `F` to it; its value on an
object is the value of `F`, by `Stacks.Duality.quasiCoherentPlusLift_obj_obj`. -/
def quasiCoherentPlusLift (F : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X)
    (hF : ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
      DerivedCategoryB.IsBoundedBelow (F.obj K).obj) :
    quasiCoherentDerivedCategoryPlusOfModel Y ⥤ quasiCoherentDerivedCategoryPlusOfModel X :=
  ObjectProperty.lift (fun K : quasiCoherentDerivedCategory X => DerivedCategoryB.IsBoundedBelow
      K.obj)
    (ObjectProperty.ι _ ⋙ F) fun K => hF K.obj K.property

variable (F : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X)
  (hF : ∀ K : quasiCoherentDerivedCategory Y, DerivedCategoryB.IsBoundedBelow K.obj →
    DerivedCategoryB.IsBoundedBelow (F.obj K).obj)

/-- The restriction to the bounded-below parts has the same value as the functor it restricts. -/
theorem quasiCoherentPlusLift_obj_obj (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    ((quasiCoherentPlusLift F hF).obj K).obj = F.obj K.obj :=
  rfl

/-- The underlying complex of a value of the restriction is the underlying complex of the value
of the functor it restricts. This is the form a statement about `D_QCoh` is read in when it is
needed about `D⁺_QCoh`: the two sides are the same term, so no transport of the statement along
an isomorphism is involved. -/
theorem quasiCoherentPlusLift_obj_obj_obj (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    ((quasiCoherentPlusLift F hF).obj K).obj.obj = (F.obj K.obj).obj :=
  rfl

/-- The restriction to the bounded-below parts, followed by the inclusion of the bounded-below
part of the target, is the inclusion of the bounded-below part of the source followed by the
original functor. -/
theorem quasiCoherentPlusLift_comp_ι :
    quasiCoherentPlusLift F hF ⋙ ObjectProperty.ι _ = ObjectProperty.ι _ ⋙ F :=
  rfl

end Lift

section UpperShriek

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- `Stacks.Duality.upperShriekPlus` is this transport applied to `f^!` of [Stacks, Tag 0A9Y] and
to the boundedness of `Stacks.Duality.isBoundedBelow_upperShriek_obj`. -/
theorem upperShriekPlus_eq_quasiCoherentPlusLift :
    upperShriekPlus f j =
      quasiCoherentPlusLift (upperShriek f j) (isBoundedBelow_upperShriek_obj f j) :=
  rfl

end UpperShriek

section StandardTwistedInverseImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- `Stacks.Duality.standardUpperShriekPlus` is this transport applied to the right adjoint of
`Rf_*` at the standard model and to [Stacks, Tag 0A9I] for it.

That it typechecks is the point: the right-hand side is a
`Stacks.Duality.quasiCoherentPlusLift`, and the type of the left-hand side is
`Stacks.Duality.quasiCoherentDerivedCategoryPlus Y ⥤
Stacks.Duality.quasiCoherentDerivedCategoryPlus X`, which is the type of the `f^!` parameter of
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`. So the transport, fed a functor of the
unbounded `D_QCoh` at the standard model that preserves bounded-below cohomology, produces a term
of exactly that type; the identification of the two bounded-below categories it relies on is
`Stacks.Duality.quasiCoherentDerivedCategoryPlus_eq_ofModel_standard`. -/
theorem standardUpperShriekPlus_eq_quasiCoherentPlusLift :
    standardUpperShriekPlus f =
      @quasiCoherentPlusLift X Y (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (AnyModel.standardTwistedInverseImage f)
        (isBoundedBelow_standardTwistedInverseImage_obj f) :=
  rfl

end StandardTwistedInverseImage

section Dualizing

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  (j : CompactificationOf (Over.mk f.left))

/-- **`f^!` of a dualizing complex is dualizing, on `D⁺_QCoh`.** Let `S` be a Noetherian scheme,
`f : X ⟶ Y` a morphism of `AlgebraicGeometry.FTS S` and `j` a compactification of `X` over `Y`.
If `K ∈ D⁺_QCoh(𝒪_Y)` is a dualizing complex then so is `f^!K ∈ D⁺_QCoh(𝒪_X)`. -/
theorem isDualizingComplex_upperShriekPlus_obj
    (K : quasiCoherentDerivedCategoryPlusOfModel Y.left)
    (hK : IsDualizingComplex K.obj.obj) :
    IsDualizingComplex ((upperShriekPlus f j).obj K).obj.obj :=
  isDualizingComplex_upperShriek_obj f j K.obj hK

end Dualizing

end Stacks.Duality

end

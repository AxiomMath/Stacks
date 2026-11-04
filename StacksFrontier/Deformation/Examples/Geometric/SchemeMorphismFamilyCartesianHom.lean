module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSource
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessinger
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional

/-!
# An arrow of flat families of morphisms of schemes from a commuting square

An arrow of `Deformation.Examples.SchemeMorphismFamily` records a morphism `β` of the bases, a
morphism `es` of the sources and a morphism `et` of the targets, and asks for **two** cartesian
squares: `source_pullback`, saying that the source of the second family is the fibre product of
the source of the first with the target of the second, and `target_pullback`, saying that the
target of the second family is the base change of the target of the first.

The `source_pullback` field is awkward to produce directly, and this file shows that it never has
to be. In any arrow of families the two endpoint components are *separately* base changes over
`baseSpecMap β`, and conversely those two squares plus the bare commuting square

`Q.morphism ≫ et = es ≫ P.morphism`

reconstruct `source_pullback`. The reason is the `over_base` field: pasting the square of
morphisms onto the cartesian square of the target turns the top and bottom rows into the two
structure morphisms, so the pasted rectangle *is* the cartesian square of the source, and the
pasting lemmas of `CategoryTheory.IsPullback` run in both directions.

So an arrow of families over an arbitrary — in particular non-invertible — morphism of bases is
exactly: a morphism of bases, a base change of each endpoint along it, and a commuting square.
No cartesianness of the square of morphisms has to be checked, and none is lost.

## Main definitions

* `Deformation.Examples.SchemeMorphismFamily.Hom.ofEndpointPullbacks`: **the arrow constructor.**
  From a morphism `β` of the bases, two endpoint morphisms exhibiting each endpoint of the second
  family as the base change of the corresponding endpoint of the first along `baseSpecMap β`, and
  a commuting square relating them to the two morphisms being deformed.
* `Deformation.Examples.SchemeMorphismFamily.Hom.ofIsIso`: the same when the morphism of bases
  and the two endpoint morphisms are invertible, where the two cartesian squares reduce to one
  commuting square.
* `Deformation.Examples.morphismDeformationHom`: the arrow read in the deformation category of a
  fixed morphism of schemes over the residue field.

## Main results

* `Deformation.Examples.SchemeMorphismFamily.isPullback_sourceToBase_of_isPullback_morphism`: the
  converse pasting — the source endpoint square of an arrow of families is cartesian. Together
  with the constructor this says the two descriptions of an arrow carry the same information.
* `Deformation.Examples.SchemeMorphismFamily.Hom.isPullback_sourceToBase`: the previous theorem
  read on an arbitrary arrow.
* `Deformation.Examples.SchemeMorphismFamily.sourceToBase_comm_of_morphism_comm`: the
  *commutativity* of the source endpoint square is itself free, so it is not an input to
  `Deformation.Examples.SchemeMorphismFamily.Hom.ofIsIso`.
* `Deformation.Examples.isPullback_toBase_comp_baseSpecMap_of_cartesian`: **the two endpoint
  squares the constructor asks for are the `cartesian` fields of a pair of arrows of the endpoint
  deformation categories**, read over the two bases through invertible morphisms of `𝒞_Λ` as
  `Deformation.Examples.deformationAmbientToBase` does. So the constructor's inputs are exactly
  what the deformation theory of the two endpoint schemes already produces.
* `Deformation.Examples.morphismDeformationHom_isHomLift`: an arrow of the deformation category
  lies over a prescribed morphism of `𝒞_Λ` once its component on bases factors through it.

## Implementation notes

The base change arrow of `StacksFrontier.Deformation.Examples.Geometric.SchemeMorphisms` goes
over an arbitrary morphism of bases, but only to the family built from
`CategoryTheory.Limits.pullback`, the chosen pullback. The constructor here takes the second
family as given, so it applies to a second family that is a base change without being the
chosen pullback.

## References

* [Stacks Project, Tag 0E3T](https://stacks.math.columbia.edu/tag/0E3T)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Deformation.Examples

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

namespace SchemeMorphismFamily

variable {P Q : SchemeMorphismFamily.{u, v} Λ k}

/-- **The source endpoint square of an arrow of families is cartesian.** Given the cartesian
square of the morphisms and the cartesian square of the targets, pasting them horizontally gives
a rectangle whose two horizontal edges are `Q.morphism ≫ Q.targetToBase` and
`P.morphism ≫ P.targetToBase`; the `over_base` field of each family rewrites these as the two
structure morphisms of the sources, so the rectangle is the cartesian square of the sources. -/
theorem isPullback_sourceToBase_of_isPullback_morphism {β : P.base ⟶ Q.base}
    {es : Q.source ⟶ P.source} {et : Q.target ⟶ P.target}
    (hmor : IsPullback Q.morphism es et P.morphism)
    (htgt : IsPullback et Q.targetToBase P.targetToBase (baseSpecMap β)) :
    IsPullback es Q.sourceToBase P.sourceToBase (baseSpecMap β) := by
  have h := hmor.paste_horiz htgt.flip
  rw [Q.over_base, P.over_base] at h
  exact h.flip

/-- The source endpoint square of an arbitrary arrow of families is cartesian. -/
theorem Hom.isPullback_sourceToBase (φ : P ⟶ Q) :
    IsPullback φ.source Q.sourceToBase P.sourceToBase (baseSpecMap φ.base) :=
  isPullback_sourceToBase_of_isPullback_morphism φ.source_pullback φ.target_pullback

/-- **An arrow of flat families of morphisms of schemes from two base changes and a commuting
square.** Let `P` and `Q` be flat families of morphisms of schemes, let `β : P.base ⟶ Q.base`,
and let

* `es : Q.source ⟶ P.source` exhibit `Q.source` as the base change of `P.source` along
  `baseSpecMap β`;
* `et : Q.target ⟶ P.target` exhibit `Q.target` as the base change of `P.target` along
  `baseSpecMap β`;
* the square of the two morphisms being deformed commute, `Q.morphism ≫ et = es ≫ P.morphism`.

Then there is an arrow `P ⟶ Q` with these three components. The cartesian square
`source_pullback` is *not* an input: cancelling the cartesian square of the targets off the
rectangle `es`, `et` fit into after `over_base` produces it, by
`CategoryTheory.IsPullback.of_right`.

This is the converse direction of
`Deformation.Examples.SchemeMorphismFamily.isPullback_sourceToBase_of_isPullback_morphism`. -/
def Hom.ofEndpointPullbacks (β : P.base ⟶ Q.base)
    (es : Q.source ⟶ P.source) (et : Q.target ⟶ P.target)
    (hsrc : IsPullback es Q.sourceToBase P.sourceToBase (baseSpecMap β))
    (htgt : IsPullback et Q.targetToBase P.targetToBase (baseSpecMap β))
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) : P ⟶ Q where
  base := β
  source := es
  target := et
  source_pullback := by
    refine IsPullback.of_right ?_ hcomm htgt.flip
    rw [Q.over_base, P.over_base]
    exact hsrc.flip
  target_pullback := htgt

/-- The component on bases of `Hom.ofEndpointPullbacks β es et hsrc htgt hcomm` is `β`. -/
@[simp]
theorem Hom.ofEndpointPullbacks_base (β : P.base ⟶ Q.base)
    (es : Q.source ⟶ P.source) (et : Q.target ⟶ P.target)
    (hsrc : IsPullback es Q.sourceToBase P.sourceToBase (baseSpecMap β))
    (htgt : IsPullback et Q.targetToBase P.targetToBase (baseSpecMap β))
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) :
    (Hom.ofEndpointPullbacks β es et hsrc htgt hcomm).base = β := rfl

/-- The component on sources of `Hom.ofEndpointPullbacks β es et hsrc htgt hcomm` is `es`. -/
@[simp]
theorem Hom.ofEndpointPullbacks_source (β : P.base ⟶ Q.base)
    (es : Q.source ⟶ P.source) (et : Q.target ⟶ P.target)
    (hsrc : IsPullback es Q.sourceToBase P.sourceToBase (baseSpecMap β))
    (htgt : IsPullback et Q.targetToBase P.targetToBase (baseSpecMap β))
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) :
    (Hom.ofEndpointPullbacks β es et hsrc htgt hcomm).source = es := rfl

/-- The component on targets of `Hom.ofEndpointPullbacks β es et hsrc htgt hcomm` is `et`. -/
@[simp]
theorem Hom.ofEndpointPullbacks_target (β : P.base ⟶ Q.base)
    (es : Q.source ⟶ P.source) (et : Q.target ⟶ P.target)
    (hsrc : IsPullback es Q.sourceToBase P.sourceToBase (baseSpecMap β))
    (htgt : IsPullback et Q.targetToBase P.targetToBase (baseSpecMap β))
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) :
    (Hom.ofEndpointPullbacks β es et hsrc htgt hcomm).target = et := rfl

/-- **The square of the source structure morphisms commutes as soon as the square of the
morphisms and the square of the target structure morphisms do.** Only the *commutativity* of the
source endpoint square is at stake here, and it is a consequence of `over_base` on both families:
both routes around it factor through the morphism being deformed. -/
theorem sourceToBase_comm_of_morphism_comm {β : P.base ⟶ Q.base}
    {es : Q.source ⟶ P.source} {et : Q.target ⟶ P.target}
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism)
    (htgt : et ≫ P.targetToBase = Q.targetToBase ≫ baseSpecMap β) :
    es ≫ P.sourceToBase = Q.sourceToBase ≫ baseSpecMap β := by
  rw [← P.over_base, ← Q.over_base, ← Category.assoc, ← hcomm, Category.assoc, htgt,
    Category.assoc]

/-- **An arrow of flat families of morphisms of schemes over an invertible morphism of bases.**
When the morphism of bases and the two endpoint components are invertible, the only input beyond
them is the commuting square of the two morphisms being deformed together with the commuting
square of the targets: a commuting square two of whose parallel edges are invertible is
cartesian, and the commuting square of the sources comes from
`Deformation.Examples.SchemeMorphismFamily.sourceToBase_comm_of_morphism_comm`. -/
def Hom.ofIsIso (β : P.base ⟶ Q.base) [IsIso β]
    (es : Q.source ⟶ P.source) [IsIso es] (et : Q.target ⟶ P.target) [IsIso et]
    (htgt : et ≫ P.targetToBase = Q.targetToBase ≫ baseSpecMap β)
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) : P ⟶ Q :=
  Hom.ofEndpointPullbacks β es et
    (IsPullback.of_horiz_isIso ⟨sourceToBase_comm_of_morphism_comm hcomm htgt⟩)
    (IsPullback.of_horiz_isIso ⟨htgt⟩) hcomm

/-- The component on bases of `Hom.ofIsIso β es et htgt hcomm` is `β`. -/
@[simp]
theorem Hom.ofIsIso_base (β : P.base ⟶ Q.base) [IsIso β]
    (es : Q.source ⟶ P.source) [IsIso es] (et : Q.target ⟶ P.target) [IsIso et]
    (htgt : et ≫ P.targetToBase = Q.targetToBase ≫ baseSpecMap β)
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) :
    (Hom.ofIsIso β es et htgt hcomm).base = β := rfl

/-- The component on sources of `Hom.ofIsIso β es et htgt hcomm` is `es`. -/
@[simp]
theorem Hom.ofIsIso_source (β : P.base ⟶ Q.base) [IsIso β]
    (es : Q.source ⟶ P.source) [IsIso es] (et : Q.target ⟶ P.target) [IsIso et]
    (htgt : et ≫ P.targetToBase = Q.targetToBase ≫ baseSpecMap β)
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) :
    (Hom.ofIsIso β es et htgt hcomm).source = es := rfl

/-- The component on targets of `Hom.ofIsIso β es et htgt hcomm` is `et`. -/
@[simp]
theorem Hom.ofIsIso_target (β : P.base ⟶ Q.base) [IsIso β]
    (es : Q.source ⟶ P.source) [IsIso es] (et : Q.target ⟶ P.target) [IsIso et]
    (htgt : et ≫ P.targetToBase = Q.targetToBase ≫ baseSpecMap β)
    (hcomm : Q.morphism ≫ et = es ≫ P.morphism) :
    (Hom.ofIsIso β es et htgt hcomm).target = et := rfl

/-- Every arrow of families is the one the constructor produces from its own components: the
constructor is a reparametrisation of `Deformation.Examples.SchemeMorphismFamily.Hom`, not a
further source of arrows. -/
theorem Hom.ofEndpointPullbacks_self (φ : P ⟶ Q) :
    Hom.ofEndpointPullbacks φ.base φ.source φ.target φ.isPullback_sourceToBase
      φ.target_pullback φ.source_pullback.w = φ :=
  Hom.ext rfl rfl rfl

end SchemeMorphismFamily

/-! ### The arrow read in the deformation category of a morphism of schemes -/

section DeformationCategory

variable {X Y : Scheme.{v}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **An arrow of deformations of a morphism of schemes from two base changes and a commuting
square.** The arrow
`Deformation.Examples.SchemeMorphismFamily.Hom.ofEndpointPullbacks` read in the slice
`Deformation.Examples.schemeMorphismDeformationCategory`: the two extra inputs are the
compatibilities of the endpoint morphisms with the two special-fibre arrows, and the
compatibility on bases is automatic because `Deformation.Examples.residueFieldBase` is
terminal. -/
def morphismDeformationHom {P Q : schemeMorphismDeformationCategory f pX pY hf}
    (β : P.left.base ⟶ Q.left.base)
    (es : Q.left.source ⟶ P.left.source) (et : Q.left.target ⟶ P.left.target)
    (hsrc : IsPullback es Q.left.sourceToBase P.left.sourceToBase (baseSpecMap β))
    (htgt : IsPullback et Q.left.targetToBase P.left.targetToBase (baseSpecMap β))
    (hcomm : Q.left.morphism ≫ et = es ≫ P.left.morphism)
    (hs : Q.hom.source ≫ es = P.hom.source)
    (ht : Q.hom.target ≫ et = P.hom.target) : P ⟶ Q :=
  Over.homMk (SchemeMorphismFamily.Hom.ofEndpointPullbacks β es et hsrc htgt hcomm)
    (SchemeMorphismFamily.Hom.ext
      ((isTerminal_residueFieldBase (Λ := Λ) (k := k)).hom_ext _ _) hs ht)

/-- The component on bases of the underlying arrow of families of `morphismDeformationHom` is
`β`. -/
@[simp]
theorem morphismDeformationHom_left_base
    {P Q : schemeMorphismDeformationCategory f pX pY hf}
    (β : P.left.base ⟶ Q.left.base)
    (es : Q.left.source ⟶ P.left.source) (et : Q.left.target ⟶ P.left.target)
    (hsrc : IsPullback es Q.left.sourceToBase P.left.sourceToBase (baseSpecMap β))
    (htgt : IsPullback et Q.left.targetToBase P.left.targetToBase (baseSpecMap β))
    (hcomm : Q.left.morphism ≫ et = es ≫ P.left.morphism)
    (hs : Q.hom.source ≫ es = P.hom.source)
    (ht : Q.hom.target ≫ et = P.hom.target) :
    (morphismDeformationHom f pX pY hf β es et hsrc htgt hcomm hs ht).left.base = β := rfl

/-- **An arrow of deformations of `f` lies over a prescribed morphism of `𝒞_Λ` as soon as its
component on bases factors through it.** The two objects of the deformation category have bases
only *equal* to the two objects of `𝒞_Λ` the morphism connects, so the factorisation is through
the two `eqToHom`s; this is `CategoryTheory.IsHomLift.of_fac'` for the structure functor
`Deformation.Examples.schemeMorphismDeformationCategoryProjection`, whose action on arrows is
the component on bases. -/
theorem morphismDeformationHom_isHomLift
    {P Q : schemeMorphismDeformationCategory f pX pY hf} (φ : P ⟶ Q)
    {A B : ArtinianLocalAlgCat.{u, v, v} Λ k}
    (hA : P.left.base = A) (hB : Q.left.base = B) (g : A ⟶ B)
    (hg : φ.left.base = eqToHom hA ≫ g ≫ eqToHom hB.symm) :
    (schemeMorphismDeformationCategoryProjection f pX pY hf).IsHomLift g φ :=
  IsHomLift.of_fac' (schemeMorphismDeformationCategoryProjection f pX pY hf) g φ hA hB hg

end DeformationCategory

/-! ### The endpoint squares are the cartesian fields of the endpoint arrows -/

section Endpoints

variable {Λ' κ : Type u} [CommRing Λ'] [Field κ] [Algebra Λ' κ]

/-- **The structure morphism of a deformation, read over another base, is still a base change.**
Let `φ : P ⟶ Q` be an arrow of deformations of a scheme over `κ`, and let `eP : A ⟶ P.base` and
`eQ : B ⟶ Q.base` be *invertible* morphisms of `𝒞_Λ` through which the two structure morphisms
are to be read — `Deformation.Examples.deformationAmbientToBase`, the morphism `g'` of
[Stacks Project, Tag 0CK2]. If `β : A ⟶ B` is compatible with them, `eP ≫ φ.base = β ≫ eQ`,
then the component of `φ` on total spaces exhibits `Q` as the base change of `P` along
`baseSpecMap β`.

This is the `cartesian` field of `φ` pasted below the square of the four base morphisms, which
is cartesian because its two vertical edges `baseSpecMap eP` and `baseSpecMap eQ` are invertible
by `Deformation.Examples.isIso_baseSpecMap`.

Together with
`Deformation.Examples.SchemeMorphismFamily.Hom.ofEndpointPullbacks` this says that **a pair of
arrows of the two endpoint deformation categories over one morphism of bases, plus a commuting
square of the two morphisms being deformed, is an arrow of
`Deformation.Examples.SchemeMorphismFamily`** — no cartesian square of the morphisms has to be
produced. The two `cartesian` fields are the only cartesianness needed, and an arrow of
`Deformation.Examples.SchemeDeformationCategory` carries one by construction. -/
theorem isPullback_toBase_comp_baseSpecMap_of_cartesian
    {Z : Over (Spec (CommRingCat.of κ))}
    {P Q : SchemeDeformationCategory (Λ := Λ') (k := κ) Z} (φ : P ⟶ Q)
    {A B : ArtinianLocalAlgCat.{u, u, u} Λ' κ}
    (eP : A ⟶ P.base) [IsIso eP] (eQ : B ⟶ Q.base) [IsIso eQ]
    (β : A ⟶ B) (hβ : eP ≫ φ.base = β ≫ eQ) :
    IsPullback φ.map (Q.toBase ≫ baseSpecMap eQ) (P.toBase ≫ baseSpecMap eP)
      (baseSpecMap β) := by
  refine φ.cartesian.paste_vert (IsPullback.of_vert_isIso ⟨?_⟩)
  rw [← baseSpecMap_comp, ← baseSpecMap_comp, hβ]

end Endpoints

end Deformation.Examples

end

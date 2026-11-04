module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DirectSums
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness

/-!
# Derived direct image is an exact functor, and the twisted inverse image

Let `f : X ⟶ Y` be a morphism of schemes. Derived direct image
`Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` is the total right derived functor of a functor out of the homotopy
category of cochain complexes of `𝒪_X`-modules, so it commutes with the shift and is an exact
functor of triangulated categories for formal reasons: a right derived functor along the
quasi-isomorphisms commutes with the shift
(`CategoryTheory.Functor.IsRightDerivedFunctor.commShift`), and it is triangulated as soon as
every complex admits a K-injective resolution
(`Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`), which holds in the
Grothendieck abelian category `𝒪_X`-Mod. Exactness descends to the restriction
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` because `D_QCoh` is a triangulated subcategory and the restriction
is compatible with the inclusions up to the canonical isomorphism.

This file records those four facts as instances, and uses them to remove the exactness
hypotheses from the Brown-representability statement of [Stacks, Tag 0A9E]. Of the five inputs
that `Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward` asks for, three were
discharged for an arbitrary scheme in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/DirectSums.lean` (that `D_QCoh` is a
triangulated subcategory on either side, and that `D_QCoh(𝒪_X)` has direct sums). Exactness of
the restricted functor is discharged here. What is left are exactly the three statements
[Stacks, Tag 0A9E] derives from quasi-compactness and quasi-separatedness, and nothing else:

* **Tag 08D5** — `Rf_*` preserves quasi-coherence of cohomology, the argument `hpush` without
  which the restricted functor cannot even be written down;
* **Tag 08DZ** — `Rf_*` commutes with direct sums;
* **Tag 09IS** — `D_QCoh(𝒪_X)` is compactly generated.

## Main results

All of these live in the namespace `Stacks.Duality.DerivedPushforward`.

* `commShift_derivedPushforward` and `isTriangulated_derivedPushforward` — `Rf_*` on the unbounded
  derived categories commutes with the shift and is exact, for an arbitrary morphism of schemes
  and an arbitrary choice of derived category.
* `commShift_quasiCoherentDerivedPushforward` and
  `isTriangulated_quasiCoherentDerivedPushforward` — the same for the restriction of `Rf_*` to the
  quasi-coherent derived categories.
* `isClosedUnderIsomorphisms_derivedQuasicoherent` — `D_QCoh(𝒪_X)` is closed under isomorphisms
  of `D(𝒪_X)`.
* `isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator` — the Stacks proof of
  [Stacks, Tag 0A9E] with Tags 08D5, 08DZ and 09IS as its only hypotheses, 09IS in the
  single-compact-generator shape that [Stacks, Tag 09IS] produces.
* `isLeftAdjoint_quasiCoherentDerivedPushforward_of_generatorFamily` — the same with 09IS in the
  generating-family shape, recording that the exactness hypotheses of
  `isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator` are now discharged by instance
  search.

## Implementation notes

The two statements about `Rf_*` itself are at a free morphism universe `w` for the derived
categories. The four statements about the restriction to `D_QCoh` are at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` instead, because that is the model at which
`D_QCoh(𝒪_X)` is known to be a triangulated subcategory with direct sums, and — as the module
docstring of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` explains — the only model
at which the Brown-representability hypothesis `HasCoproducts` is true rather than false.

`commShift_derivedPushforward` is the canonical structure
`CategoryTheory.Functor.IsRightDerivedFunctor.commShift` for the unit of the total right derived
functor, and not some other shift compatibility; this is what makes
`Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`, whose statement fixes that
structure, applicable to it.

`isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator` goes through
`CategoryTheory.Pretriangulated.isLeftAdjoint_lift_of_compact_generator` rather than through
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward`: the ambient derived categories
are not locally small at the morphism universe, only the subcategories are, and that lemma is
stated for exactly that situation. It takes the exactness of the *ambient* functor and derives
the exactness of the lift itself, which is why the hypotheses disappear rather than being
discharged one at a time.

No `@[stacks]` attribute is attached. Tag 0A9E is the assertion that the right adjoint exists for
a morphism of quasi-compact, quasi-separated schemes with no further hypotheses; the three tags
above are still hypotheses here, so an attribute on any declaration in this file would report an
open tag as formalized.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  Opposite

universe w u

namespace Stacks.Duality.DerivedPushforward

open Stacks.AlgebraicGeometry.QuasicoherentWeakSerre

/-! ### Exactness of `Rf_*` on the unbounded derived categories -/

section Ambient

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **Derived direct image commutes with the shift.** `Rf_*` is the total right derived functor
of direct image along the quasi-isomorphisms, and a right derived functor along a class of
morphisms compatible with the shift commutes with the shift. -/
instance commShift_derivedPushforward : (Stacks.Duality.derivedPushforward f).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift _
    ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) ℤ

/-- **Derived direct image is an exact functor of triangulated categories.** `𝒪_X`-modules form a
Grothendieck abelian category, so every cochain complex of them admits a K-injective resolution
([Stacks, Tag 079P]), and a right derived functor along the quasi-isomorphisms out of such a
category is triangulated. -/
instance isTriangulated_derivedPushforward :
    (Stacks.Duality.derivedPushforward f).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (fun K => ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion X.Modules).app K,
      inferInstance, inferInstance⟩)
    (Stacks.Duality.homotopyPushforward f) _
    ((Stacks.Duality.homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))

end Ambient

/-! ### Exactness of the restriction to the quasi-coherent derived categories -/

/-- `D_QCoh(𝒪_X)` is closed under isomorphisms of `D(𝒪_X)`: cohomology sends an isomorphism of
the derived category to an isomorphism of `𝒪_X`-modules, and quasi-coherence is closed under
isomorphisms. -/
instance isClosedUnderIsomorphisms_derivedQuasicoherent (X : Scheme.{u}) :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _ (isQuasicoherent_isWeakSerre X)

section Restricted

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- The restriction of `Rf_*` to the quasi-coherent derived categories is compatible with the
inclusions: `(restricted Rf_*) ⋙ ι ≅ ι ⋙ Rf_*`, by definition of the restriction. -/
abbrev quasiCoherentDerivedPushforwardCompιIso :
    Stacks.Duality.quasiCoherentDerivedPushforward f hpush ⋙
        (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ≅
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⋙
        Stacks.Duality.derivedPushforward f :=
  (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).liftCompιIso _ hpush

/-- The restriction of `Rf_*` to the quasi-coherent derived categories commutes with the shift:
`D_QCoh` is stable under the shift, so the inclusions commute with it, and the restriction does
because its composite with the inclusion does. -/
instance commShift_quasiCoherentDerivedPushforward :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).CommShift ℤ :=
  Functor.CommShift.ofComp (quasiCoherentDerivedPushforwardCompιIso f hpush) ℤ

/-- **The restriction of `Rf_*` to the quasi-coherent derived categories is exact.** `D_QCoh` is a
triangulated subcategory of `D` on either side, so a distinguished triangle of `D_QCoh(𝒪_X)` is
one of `D(𝒪_X)`, and exactness of the restriction is exactness of its composite with the fully
faithful inclusion, which is `Rf_*` on the inclusion of the source. -/
instance isTriangulated_quasiCoherentDerivedPushforward :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsTriangulated :=
  letI : NatTrans.CommShift (quasiCoherentDerivedPushforwardCompιIso f hpush).hom ℤ :=
    Functor.CommShift.ofComp_compatibility (quasiCoherentDerivedPushforwardCompιIso f hpush) ℤ
  (Functor.isTriangulated_iff_comp_right
    (quasiCoherentDerivedPushforwardCompιIso f hpush)).2 inferInstance

end Restricted

/-! ### The twisted inverse image, with exactness discharged -/

section TwistedInverseImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The Stacks proof of [Stacks, Tag 0A9E], with exactly the three geometric inputs of the
source as hypotheses.** Let `f : X ⟶ Y` be a morphism of schemes. Suppose

* derived direct image preserves quasi-coherence of cohomology ([Stacks, Tag 08D5], the argument
  `hpush`);
* the restricted derived direct image commutes with direct sums ([Stacks, Tag 08DZ]);
* `D_QCoh(𝒪_X)` has a compact weak generator ([Stacks, Tag 09IS]).

Then the restricted derived direct image has a right adjoint — the twisted inverse image `f^×`.

Nothing else is assumed. That `D_QCoh` is a triangulated subcategory on either side and has direct
sums is `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated`
and `hasCoproducts_quasiCoherentDerivedCategory`; that the restricted functor is exact is
`commShift_quasiCoherentDerivedPushforward` and
`isTriangulated_quasiCoherentDerivedPushforward`. The proof is one application of
[Stacks, Tag 0A8G] in the form
`CategoryTheory.Pretriangulated.isLeftAdjoint_lift_of_compact_generator`. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_compactGenerator
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)]
    (E : Stacks.Duality.quasiCoherentDerivedCategory X) [IsCompactObject.{u} E]
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint := by
  have hsum := hasCoproducts_quasiCoherentDerivedCategory X
  exact Pretriangulated.isLeftAdjoint_lift_of_compact_generator.{u + 1, u + 1, u, u, u} _ _
    (Stacks.Duality.derivedPushforward f) inferInstance inferInstance hpush E hE

/-- [Stacks, Tag 0A9E] with [Stacks, Tag 09IS] in the generating-family shape, in which
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward` phrases it: a family `E` whose
members are compact in the sense that `preadditiveCoyoneda.obj (op (E i))` preserves direct sums,
and such that the only objects right orthogonal to all shifts of all `E i` are the zero objects.

The content of this restatement is that it carries three hypotheses rather than five:
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator`
asks in addition that the restricted functor commute with the shift and be triangulated, and
those are now supplied by instance search. -/
theorem isLeftAdjoint_quasiCoherentDerivedPushforward_of_generatorFamily
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)]
    {ι : Type u} (E : ι → Stacks.Duality.quasiCoherentDerivedCategory X)
    [∀ (i : ι) (α : Type u),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ K : Stacks.Duality.quasiCoherentDerivedCategory X,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K) :
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint :=
  isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator f hpush E hE

end TwistedInverseImage

end Stacks.Duality.DerivedPushforward

end

module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.Abstract
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedRestrictAdjunction
import all StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# The unit criterion of [Stacks, Tag 09IR] along an open immersion of schemes

`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/Abstract.lean` reduces the equivalence

> `E ⟶ R (L E)` is invertible ⟺ `E` is right orthogonal to every shift of `K`

to a detection hypothesis, for an adjunction `L ⊣ R` of pretriangulated categories with `L`
triangulated and `L K = 0`. This file instantiates it at the derived adjunction `j^* ⊣ Rj_*` of
`StacksFrontier/AlgebraicGeometry/Duality/OpenImmersion/DerivedRestrictAdjunction.lean`, and then
carries the conclusion across to the **lifted** adjunction between full subcategories, which is
the form the generation step consumes.

That last move is the point of the file. The hypothesis `hunit` of
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion` is about the
unit of `liftDerivedRestrictPushforwardAdjunction`, a restriction of the ambient adjunction along
the two fully faithful inclusions. Proving anything about that unit directly would require
knowing that the lifted restriction functor is triangulated, which the repository does not have.
It is not needed: Mathlib's `Adjunction.map_restrictFullyFaithful_unit_app` expresses the
inclusion of the restricted unit as the ambient unit composed with two isomorphisms, so the two
units are invertible together, and the ambient one is reached by the abstract theorem. Likewise
the two orthogonality conditions — in the subcategory and in the ambient category — are
equivalent, because the inclusion is fully faithful and commutes with the shift.

## Main results

* `CategoryTheory.Adjunction.isIso_restrictFullyFaithful_unit_app_iff` — the unit of a restricted
  adjunction is invertible at an object exactly when the ambient unit is.
* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_ι` — right orthogonality
  to the shifts of an object of a shift-stable full subcategory passes to the ambient category.
* `Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_unit_iff` — the
  equivalence of [Stacks, Tag 09IR] for `j^* ⊣ Rj_*` on the full derived categories, modulo the
  detection hypothesis.
* `Stacks.Duality.OpenImmersion.isIso_liftUnit_of_rightOrthogonal_shiftClosure_singleton` — the
  hypothesis `hunit` of the generation step, derived from the three geometric inputs.
* `Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection` — the inductive
  step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] with `hunit` eliminated in favour of those
  three inputs. **Vacuous as stated, and not to be consumed**: see its docstring and the
  implementation notes below.

## Implementation notes

No `@[stacks]` attribute is attached: Tag 09IR is the detection hypothesis together with the
vanishing `j^* K = 0`, neither of which is proved here.

The three remaining geometric inputs, named exactly as they appear below:

* `hKzero : IsZero ((derivedRestrict j).obj K)` — the Koszul complex on generators of the ideal
  cutting out `Y \ X` restricts to zero on `X`. For `X = ⋃ᵢ D(f_i)` inside `Y = Spec A` and `K`
  the sheafified Koszul complex `Stacks.Koszul.Truncation.koszulObject` of
  `StacksFrontier/RingTheory/Koszul/Truncation/DerivedKoszulObject.lean`, the algebraic half is
  `Koszul.acyclic_seqComplex_of_isUnit`
  (`StacksFrontier/RingTheory/Koszul/PowerLift/UnitEntry.lean`), whose own docstring records that
  the passage to the sheafified complex is not carried out there either.
* `hcounit : IsIso ((derivedRestrictPushforwardAdjunction j).counit.app Z)` — `Rj_*` is fully
  faithful, that is `j^* Rj_* = id`. This is the derived form of the corresponding statement for
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`.
* `hdet` — [Stacks, Tag 09IR] proper: an object of `D(𝒪_Y)` restricting to zero on `X` and right
  orthogonal to all shifts of `K` is zero. In the affine case this is the commutative algebra of
  the source — the Koszul power triangles of [Stacks, Tag 08E3] and the comparison
  `D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0].

Every statement below carries free `[HasDerivedCategory.{w} _]` binders for both schemes and
mentions `CategoryTheory.HasDerivedCategory.standard` nowhere, so the results are available at
the locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the
only model at which [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe w u

/-! ### The unit of a restricted adjunction -/

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {D : Type*} [Category D]
  {C' : Type*} [Category C'] {D' : Type*} [Category D']
  {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'} (adj : L' ⊣ R')
  (hiC : iC.FullyFaithful) (hiD : iD.FullyFaithful)
  {L : C ⥤ D} {R : D ⥤ C} (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)

/-- **The unit of a restricted adjunction is invertible exactly where the ambient unit is.**
Mathlib's `CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app` writes the image of the
restricted unit under the fully faithful inclusion `iC` as the ambient unit followed by two
isomorphisms; a fully faithful functor reflects invertibility, so the two units are invertible
together.

This is what makes a statement about the unit of `j^* ⊣ Rj_*` on the whole derived categories
usable as the hypothesis `hunit` of the generation step, which is phrased for the adjunction
restricted to a pair of full subcategories. -/
theorem isIso_restrictFullyFaithful_unit_app_iff (X : C) :
    IsIso ((adj.restrictFullyFaithful hiC hiD comm1 comm2).unit.app X) ↔
      IsIso (adj.unit.app (iC.obj X)) := by
  have key : IsIso (iC.map ((adj.restrictFullyFaithful hiC hiD comm1 comm2).unit.app X)) ↔
      IsIso (adj.unit.app (iC.obj X)) := by
    simp
  exact ⟨fun _ => key.1 (iC.map_isIso _), fun h => have := key.2 h; hiC.isIso_of_isIso_map _⟩

end CategoryTheory.Adjunction

/-! ### Orthogonality in a full subcategory and in the ambient category -/

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

/-- **Right orthogonality to the shifts of an object of a full subcategory is the same condition
in the subcategory and in the ambient category.** The inclusion of a shift-stable full
subcategory is fully faithful and commutes with the shift, so a morphism
`(A.ι.obj K)⟦a⟧ ⟶ A.ι.obj E` is, up to the shift-commutation isomorphism, the image of a unique
morphism `K⟦a⟧ ⟶ E`, and the two vanish together. -/
theorem rightOrthogonal_shiftClosure_singleton_ι (A : ObjectProperty C) [A.IsStableUnderShift ℤ]
    {K E : A.FullSubcategory}
    (hK : ((singleton K).shiftClosure ℤ).rightOrthogonal E) :
    ((singleton (A.ι.obj K)).shiftClosure ℤ).rightOrthogonal (A.ι.obj E) := by
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hK ⊢
  intro _ a g
  have hpre : A.fullyFaithfulι.preimage
      ((A.ι.commShiftIso (A := ℤ) a).hom.app K ≫ g) = 0 := hK () a _
  have hmap := A.fullyFaithfulι.map_preimage ((A.ι.commShiftIso (A := ℤ) a).hom.app K ≫ g)
  rw [hpre, A.ι.map_zero] at hmap
  rw [← cancel_epi ((A.ι.commShiftIso (A := ℤ) a).hom.app K), comp_zero, ← hmap]

end CategoryTheory.ObjectProperty

/-! ### [Stacks, Tag 09IR] for `j^* ⊣ Rj_*`, modulo the detection hypothesis -/

namespace Stacks.Duality.OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- **[Stacks, Tag 09IR] for the derived adjunction along an open immersion of schemes**, with
its commutative algebra isolated as the hypothesis `hdet`. Let `j : X ⟶ Y` be an open immersion
and let `K` be an object of `D(𝒪_Y)` restricting to zero on `X`. Granted

* `hcounit`, that `j^* Rj_* = id` at `j^* E`, and
* `hdet`, that an object of `D(𝒪_Y)` restricting to zero on `X` and right orthogonal to all
  shifts of `K` is zero,

an object `E` of `D(𝒪_Y)` satisfies `E = Rj_*(E|_X)` — the unit of the adjunction is invertible
at `E` — if and only if `E` is right orthogonal to every shift of `K`. -/
theorem isIso_derivedRestrictPushforwardAdjunction_unit_iff
    {K E : DerivedCategory Y.Modules} (hKzero : IsZero ((derivedRestrict j).obj K))
    (hcounit : IsIso ((derivedRestrictPushforwardAdjunction j).counit.app
      ((derivedRestrict j).obj E)))
    (hdet : ∀ M : DerivedCategory Y.Modules, IsZero ((derivedRestrict j).obj M) →
      ((singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M) :
    IsIso ((derivedRestrictPushforwardAdjunction j).unit.app E) ↔
      ((singleton K).shiftClosure ℤ).rightOrthogonal E :=
  CategoryTheory.ObjectProperty.isIso_unit_iff_rightOrthogonal_shiftClosure_singleton
    (derivedRestrictPushforwardAdjunction j) hKzero hcounit hdet

section Subcategories

variable (A : ObjectProperty (DerivedCategory Y.Modules))
  (B : ObjectProperty (DerivedCategory X.Modules))
  [A.IsTriangulated] [B.IsTriangulated]
  (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict j).obj K.obj))
  (hpush : ∀ L : B.FullSubcategory, A ((Stacks.Duality.derivedPushforward j).obj L.obj))

omit [B.IsTriangulated] in
/-- **The hypothesis `hunit` of the generation step, derived from the three geometric inputs.**
For `K` an object of `A ⊆ D(𝒪_Y)` restricting to zero on `X`, an object `E` of `A` right
orthogonal to all shifts of `K` has invertible unit for the **lifted** adjunction
`Stacks.Duality.OpenImmersion.liftDerivedRestrictPushforwardAdjunction`.

The orthogonality hypothesis is transported to the ambient derived category by
`CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_ι`, the conclusion is
obtained there by
`Stacks.Duality.OpenImmersion.isIso_derivedRestrictPushforwardAdjunction_unit_iff`, and it is
carried back to the subcategory by
`CategoryTheory.Adjunction.isIso_restrictFullyFaithful_unit_app_iff`. In particular nothing has
to be known about the lifted restriction functor beyond its being a restriction. -/
theorem isIso_liftUnit_of_rightOrthogonal_shiftClosure_singleton {K : A.FullSubcategory}
    (hKzero : IsZero ((derivedRestrict j).obj K.obj))
    (hcounit : ∀ Z : DerivedCategory X.Modules,
      IsIso ((derivedRestrictPushforwardAdjunction j).counit.app Z))
    (hdet : ∀ M : DerivedCategory Y.Modules, IsZero ((derivedRestrict j).obj M) →
      ((singleton K.obj).shiftClosure ℤ).rightOrthogonal M → IsZero M)
    (E : A.FullSubcategory)
    (hE : ((singleton K).shiftClosure ℤ).rightOrthogonal E) :
    IsIso ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app E) :=
  (Adjunction.isIso_restrictFullyFaithful_unit_app_iff _ _ _ _ _ E).2
    ((isIso_derivedRestrictPushforwardAdjunction_unit_iff j hKzero (hcounit _) hdet).2
      (rightOrthogonal_shiftClosure_singleton_ι A hE))

include hpush in
/-- **The inductive step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] with `hunit` eliminated.**
This is `Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_openImmersion` with
its single geometric hypothesis replaced by the three inputs of [Stacks, Tag 09IR]: the Koszul
object restricts to zero on the open, `Rj_*` is fully faithful, and an object restricting to zero
on the open and orthogonal to the shifts of the Koszul object vanishes.

**This statement is vacuous, and should not be used towards [Stacks, Tag 09IS].** The
third input, `hdet`, is quantified over *all* of `D(𝒪_Y)`, and in that generality it is false: the
docstring of `Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/AffineSituation.lean` says so in its
own words — "`hdet` as stated here is false, and this statement is therefore vacuous" — with a
discrete-valuation-ring counterexample. What the source assumes is that the object lie in
`D_QCoh`, and the quasi-coherent form is proved and tagged as
`Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`
(registered for 09IR, implication (2) to (1)) in that same file. The inductive step to
use is therefore
`isWeakTriangulatedGenerator_biprod_of_openImmersion` fed from that lemma, not this. This
declaration is kept only because its signature is part of an existing interface. -/
theorem isWeakTriangulatedGenerator_biprod_of_detection {Q K : A.FullSubcategory}
    {P : B.FullSubcategory} (hret : Retract P ((liftDerivedRestrict j A B hres).obj Q))
    (hP : (ObjectProperty.singleton P).IsWeakTriangulatedGenerator)
    (hKzero : IsZero ((derivedRestrict j).obj K.obj))
    (hcounit : ∀ Z : DerivedCategory X.Modules,
      IsIso ((derivedRestrictPushforwardAdjunction j).counit.app Z))
    (hdet : ∀ M : DerivedCategory Y.Modules, IsZero ((derivedRestrict j).obj M) →
      ((singleton K.obj).shiftClosure ℤ).rightOrthogonal M → IsZero M) :
    (ObjectProperty.singleton (Q ⊞ K)).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_biprod_of_openImmersion j A B hres hpush hret hP
    (isIso_liftUnit_of_rightOrthogonal_shiftClosure_singleton j A B hres hpush hKzero hcounit hdet)

end Subcategories

end Stacks.Duality.OpenImmersion

end

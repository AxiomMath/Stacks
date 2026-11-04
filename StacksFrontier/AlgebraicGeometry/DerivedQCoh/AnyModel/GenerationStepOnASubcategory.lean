module

public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.OpenImmersion

/-!
# The generation step of Tag 09IS with its detection hypothesis confined to a subcategory

`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/Abstract.lean` reduces the implication
"(2) implies (1)" of [Stacks, Tag 09IR] — an object right orthogonal to every shift of `K` has
invertible unit `E ⟶ R (L E)` — to the detection hypothesis

> `hdet` : every object `M` with `L M = 0` and `Hom(K⟦n⟧, M) = 0` for all `n` is zero,

quantified over **every** object of the source category. For the derived adjunction
`j^* ⊣ Rj_*` along an open immersion that hypothesis is false: its own counterexample is
recorded in the docstring of
`Stacks.Koszul.Truncation.isIso_unit_iff_hom_koszulObject_eq_zero`, where taking the empty
sequence of equations makes it read "an object of `D(𝒪_X)` with vanishing derived global sections
is zero", which fails on the spectrum of a discrete valuation ring. Consequently
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection`, which is the
inductive step of [Stacks, Tag 09IS] with `hunit` eliminated in favour of that hypothesis, is
vacuous, and the registered half `Stacks.Koszul.Truncation.isIso_unit_of_hom_koszulObject_eq_zero`
of [Stacks, Tag 09IR] carries the quasi-coherence hypothesis the source states instead.

What the source assumes is that `E` lie in `D_QCoh(𝒪_X)`, and that is enough: the cone of the
unit is again quasi-coherent, because `E` is, because `Rj_*` preserves quasi-coherent cohomology
along a quasi-compact open immersion ([Stacks, Tag 08D5]), and because the quasi-coherent objects
are closed under cones. This file replays the abstract argument with `hdet` **confined to a class
of objects closed under cones** and containing `E` and `R (L E)`, and then instantiates it at the
derived adjunction along an open immersion, giving the inductive step of [Stacks, Tag 09IS] in a
form that is not vacuous.

## Main results

* `CategoryTheory.ObjectProperty.isIso_unit_of_rightOrthogonal_shiftClosure_singleton_of_prop` —
  the abstract implication "(2) implies (1)" with `hdet` confined to a class of objects.
* `Stacks.Duality.OpenImmersion.isIso_liftUnit_of_rightOrthogonal_of_prop` — the hypothesis
  `hunit` of the generation step, from a detection hypothesis confined to the ambient
  subcategory `A`.
* `Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection_of_prop` — the
  inductive step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] with `hunit` eliminated in favour
  of a detection hypothesis quantified over the objects of `A` only.

## Implementation notes

No `@[stacks]` attribute is attached. [Stacks, Tag 09IR] is the detection hypothesis together
with the vanishing `j^* K = 0`, neither of which is proved here, and [Stacks, Tag 09IS] needs in
addition the perfect generator of the affine case, the extension of a perfect object along
[Stacks, Tag 09IQ] and the induction principle [Stacks, Tag 08DR].

**The abstract statement would be better as a generalisation in place.**
`CategoryTheory.ObjectProperty.isIso_unit_of_rightOrthogonal_shiftClosure_singleton` of
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/Abstract.lean` is the case
`A = ⊤` of the statement below, so the dedup-correct move is to add the three arguments `hA`,
`hAE`, `hAR` to it and keep one declaration. That file is not this one's to change; the
one-line form of the change is recorded in the report of the work that produced this file.

**Why the detection hypothesis is not confined by working inside `A.FullSubcategory`.** The
abstract theorem applied to the lifted adjunction
`Stacks.Duality.OpenImmersion.liftDerivedRestrictPushforwardAdjunction` would quantify `hdet`
over the objects of `A` automatically, with no new abstract statement at all; but it asks for
`CategoryTheory.Functor.IsTriangulated` of the lifted restriction functor, which the repository
does not have — the same obstruction that
`StacksFrontier/AlgebraicGeometry/Duality/KoszulOrthogonality/OpenImmersion.lean` records. The route
below stays in the ambient derived category, where restriction is triangulated, and carries the
class `A` through the triangle by hand.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂ w u

namespace CategoryTheory.ObjectProperty

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ] [L.IsTriangulated]

/-- **An object right orthogonal to the shifts of `K` has invertible unit**, granted a detection
hypothesis quantified over a class `A` of objects only. This is
`CategoryTheory.ObjectProperty.isIso_unit_of_rightOrthogonal_shiftClosure_singleton` with `hdet`
confined to `A`; the case `A = ⊤` is that statement.

The cone `N` of the unit `E ⟶ R (L E)` is killed by `L`, because `L` of the unit is invertible
wherever the counit is; it is right orthogonal to the shifts of `K`, because that condition is a
triangulated subcategory containing `E` and everything in the image of `R`; and it lies in `A`,
because `A` is closed under the cone of a morphism between its objects and both `E` and `R (L E)`
lie in it. So `hdet` applies to it, and a distinguished triangle with vanishing third vertex has
invertible first morphism. -/
theorem isIso_unit_of_rightOrthogonal_shiftClosure_singleton_of_prop (A : ObjectProperty C)
    (hA : ∀ T : Triangle C, T ∈ distTriang C → A T.obj₁ → A T.obj₂ → A T.obj₃)
    {K E : C} (hK : IsZero (L.obj K)) (hE : IsIso (adj.counit.app (L.obj E)))
    (hAE : A E) (hAR : A (R.obj (L.obj E)))
    (hdet : ∀ M : C, A M → IsZero (L.obj M) →
      ((singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M)
    (hortho : ((singleton K).shiftClosure ℤ).rightOrthogonal E) :
    IsIso (adj.unit.app E) := by
  obtain ⟨N, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app E)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hdet N (hA _ hT hAE hAR) ?_ ?_)
  · exact Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hT)
      (isIso_map_unit_of_isIso_counit adj E hE)
  · exact ext_of_isTriangulatedClosed₃ _ _ hT hortho
      (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj adj hK (L.obj E))

end Abstract

end CategoryTheory.ObjectProperty

namespace Stacks.Duality.OpenImmersion

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  (A : ObjectProperty (DerivedCategory Y.Modules))
  (B : ObjectProperty (DerivedCategory X.Modules))
  [A.IsTriangulated] [B.IsTriangulated]
  (hres : ∀ K : A.FullSubcategory, B ((derivedRestrict j).obj K.obj))
  (hpush : ∀ L : B.FullSubcategory, A ((Stacks.Duality.derivedPushforward j).obj L.obj))

omit [B.IsTriangulated] in
/-- **The hypothesis `hunit` of the generation step, from a detection hypothesis confined to
`A`.** For `K` an object of `A ⊆ D(𝒪_Y)` restricting to zero on `X`, an object `E` of `A` right
orthogonal to all shifts of `K` has invertible unit for the **lifted** adjunction
`Stacks.Duality.OpenImmersion.liftDerivedRestrictPushforwardAdjunction`, granted that `A` is
closed under cones and that objects *of `A`* restricting to zero on `X` and right orthogonal to
the shifts of `K` vanish.

This is
`Stacks.Duality.OpenImmersion.isIso_liftUnit_of_rightOrthogonal_shiftClosure_singleton` with its
detection hypothesis confined to `A`, which for `A = D_QCoh(𝒪_Y)` is where
[Stacks, Tag 09IR] is true. The two objects `hdet` has to be applied to beyond `E` itself are
`E` and `Rj_*(E|_X)`; the first is `E`'s own membership and the second is the hypothesis
`hpush`. -/
theorem isIso_liftUnit_of_rightOrthogonal_of_prop
    (hA : ∀ T : Triangle (DerivedCategory Y.Modules), T ∈ distTriang (DerivedCategory Y.Modules) →
      A T.obj₁ → A T.obj₂ → A T.obj₃)
    {K : A.FullSubcategory} (hKzero : IsZero ((derivedRestrict j).obj K.obj))
    (hcounit : ∀ Z : DerivedCategory X.Modules,
      IsIso ((derivedRestrictPushforwardAdjunction j).counit.app Z))
    (hdet : ∀ M : DerivedCategory Y.Modules, A M → IsZero ((derivedRestrict j).obj M) →
      ((singleton K.obj).shiftClosure ℤ).rightOrthogonal M → IsZero M)
    (E : A.FullSubcategory)
    (hE : ((singleton K).shiftClosure ℤ).rightOrthogonal E) :
    IsIso ((liftDerivedRestrictPushforwardAdjunction j A B hres hpush).unit.app E) :=
  (Adjunction.isIso_restrictFullyFaithful_unit_app_iff _ _ _ _ _ E).2
    (isIso_unit_of_rightOrthogonal_shiftClosure_singleton_of_prop
      (derivedRestrictPushforwardAdjunction j) A hA hKzero (hcounit _) E.2
      (hpush ⟨_, hres E⟩) hdet (rightOrthogonal_shiftClosure_singleton_ι A hE))

include hpush in
/-- **The inductive step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A], with a detection
hypothesis that is not vacuous.** This is
`Stacks.Duality.OpenImmersion.isWeakTriangulatedGenerator_biprod_of_detection` with `hdet`
quantified over the objects of `A` rather than over all of `D(𝒪_Y)`, and with the extra
hypothesis that `A` is closed under cones.

Confining `hdet` is what makes the statement usable: over all of `D(𝒪_Y)` the hypothesis is
false, so that version says nothing, whereas over `A = D_QCoh(𝒪_Y)` it is the content of
[Stacks, Tag 09IR] and the closure under cones is
`AlgebraicGeometry.derivedCategoryB_obj₃_of_distTriang`. -/
theorem isWeakTriangulatedGenerator_biprod_of_detection_of_prop
    (hA : ∀ T : Triangle (DerivedCategory Y.Modules), T ∈ distTriang (DerivedCategory Y.Modules) →
      A T.obj₁ → A T.obj₂ → A T.obj₃)
    {Q K : A.FullSubcategory} {P : B.FullSubcategory}
    (hret : Retract P ((liftDerivedRestrict j A B hres).obj Q))
    (hP : (ObjectProperty.singleton P).IsWeakTriangulatedGenerator)
    (hKzero : IsZero ((derivedRestrict j).obj K.obj))
    (hcounit : ∀ Z : DerivedCategory X.Modules,
      IsIso ((derivedRestrictPushforwardAdjunction j).counit.app Z))
    (hdet : ∀ M : DerivedCategory Y.Modules, A M → IsZero ((derivedRestrict j).obj M) →
      ((singleton K.obj).shiftClosure ℤ).rightOrthogonal M → IsZero M) :
    (ObjectProperty.singleton (Q ⊞ K)).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_biprod_of_openImmersion j A B hres hpush hret hP
    (isIso_liftUnit_of_rightOrthogonal_of_prop j A B hres hpush hA hKzero hcounit hdet)

end Stacks.Duality.OpenImmersion

end

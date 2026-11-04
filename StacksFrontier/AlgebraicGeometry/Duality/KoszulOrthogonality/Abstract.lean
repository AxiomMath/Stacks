module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulGeneration.TruncationCriterion
public import StacksFrontier.CategoryTheory.Triangulated.GeneratorAdjunction
import all StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability

/-!
# Orthogonality to an object killed by the left adjoint, and invertibility of the unit

Let `L ⊣ R` be an adjunction between pretriangulated categories with `L` triangulated, and let
`K` be an object of the source with `L K = 0`. Think of `L` as restriction `j^*` to an open
subscheme, of `R` as derived direct image `Rj_*`, and of `K` as the Koszul complex on generators
of the ideal cutting out the closed complement, which restricts to zero on the open. This file
proves the equivalence that [Stacks, Tag 09IR] asserts in that geometric situation:

> an object `E` of the source has invertible unit `E ⟶ R (L E)` if and only if it is right
> orthogonal to every shift of `K`.

One implication is formal: `R Y` receives no nonzero map from a shift of `K`, because such a map
is adjoint to a map out of `L (K⟦a⟧) ≅ (L K)⟦a⟧ = 0`, so an object isomorphic to `R (L E)`
through its unit is right orthogonal to the shifts of `K`.

The other implication is the content of the source's proof, and it is **not** formal: it is
reduced here to the single hypothesis

> `hdet` : an object `N` with `L N = 0` which is right orthogonal to all shifts of `K` is zero,

which is where all the commutative algebra of [Stacks, Tag 09IR] lives — the Koszul power
triangles of [Stacks, Tag 0663]/[Stacks, Tag 08E3] together with the affine comparison
`D(A) ≌ D_QCoh(𝒪_{Spec A})` of [Stacks, Tag 06Z0]. Given `hdet` the implication is three steps.
Choose a distinguished triangle `E ⟶ R (L E) ⟶ N ⟶ E⟦1⟧`. Right orthogonality to the shifts of
`K` is a triangulated subcategory, so `N` inherits it from `E` and `R (L E)`. And `L N = 0`,
because `L` of the unit at `E` is a section of the counit at `L E` and so is invertible as soon
as the counit is, which for an open immersion it is. Then `N = 0` by `hdet`, and a distinguished
triangle whose third vertex vanishes has invertible first map.

## Main results

* `CategoryTheory.ObjectProperty.isZero_map_shift_of_isZero_map` — `L` kills the shifts of
  anything it kills.
* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj` —
  nothing in the image of `R` receives a nonzero map from a shift of `K`.
* `CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_singleton_of_isIso_unit` — the
  formal implication, "invertible unit implies orthogonal".
* `CategoryTheory.ObjectProperty.isIso_map_unit_of_isIso_counit` — `L` of the unit is invertible
  wherever the counit is.
* `CategoryTheory.ObjectProperty.isZero_of_rightOrthogonal_shiftClosure_singleton_of_isZero_map`
  — the cone of the unit is zero, assuming the detection hypothesis.
* `CategoryTheory.ObjectProperty.isIso_unit_of_rightOrthogonal_shiftClosure_singleton` — the
  substantial implication, reduced to the detection hypothesis.
* `CategoryTheory.ObjectProperty.isIso_unit_iff_rightOrthogonal_shiftClosure_singleton` — the
  equivalence of [Stacks, Tag 09IR], abstractly.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_biprod_of_detection` — the
  generation step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A] with its hypothesis on the unit
  replaced by the detection hypothesis, which is the form the sources actually verify.

## Implementation notes

No `@[stacks]` attribute is attached. Tag 09IR is a statement about the Koszul complex on an
affine scheme; what is proved here is the part of its proof that is independent of the geometry,
with the geometric input isolated as `hdet`. Attaching the tag to any declaration below would
make the dashboard report the whole tag formalized, which it is not.

There is no `HasDerivedCategory` instance anywhere in this file, so no model of the derived
category is chosen; the results apply to the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, which is the only one at which
[Stacks, Tag 09IS] and [Stacks, Tag 0A9A] have content (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration.lean`).

The hypothesis on the counit is taken at the single object `L E` rather than as invertibility of
the whole counit, because that is all the argument uses and the geometric input available for it
is pointwise. For an open immersion `j` it says `j^* Rj_*(E|_U) = E|_U`, that is, that `Rj_*` is
fully faithful.

`hdet` is phrased with `IsZero (L.obj N)` rather than with a support condition on `N`, because
that is what the triangle supplies and because it is the model-free form: the geometric statement
"the cohomology sheaves of `N` are supported on the closed complement" is a consequence, not an
input.

## References

* [Stacks Project, Tag 09IR](https://stacks.math.columbia.edu/tag/09IR)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

/-! ### Orthogonality to the shifts of an object killed by the left adjoint -/

section Shift

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasShift C ℤ]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ]

omit [Preadditive C] in
/-- **A functor commuting with the shift kills the shifts of anything it kills.** If `L K = 0`
then `L (K⟦a⟧) ≅ (L K)⟦a⟧ = 0` for every `a : ℤ`. -/
theorem isZero_map_shift_of_isZero_map {K : C} (hK : IsZero (L.obj K)) (a : ℤ) :
    IsZero (L.obj (K⟦a⟧)) :=
  ((shiftFunctor D a).map_isZero hK).of_iso ((L.commShiftIso (A := ℤ) a).app K)

include adj in
/-- **Nothing in the image of the right adjoint receives a nonzero map from a shift of an object
killed by the left adjoint.** A morphism `K⟦a⟧ ⟶ R Y` corresponds under the adjunction to a
morphism `L (K⟦a⟧) ⟶ Y` out of a zero object, so there is at most one of them. -/
theorem rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj {K : C}
    (hK : IsZero (L.obj K)) (Y : D) :
    ((singleton K).shiftClosure ℤ).rightOrthogonal (R.obj Y) := by
  rw [rightOrthogonal_shiftClosure_ofObj_iff]
  intro _ a f
  exact (Stacks.DerivedTruncation.subsingleton_hom_rightAdjoint_obj_of_isZero adj
    (isZero_map_shift_of_isZero_map hK a) Y).allEq f 0

/-- **An object with invertible unit is right orthogonal to the shifts of anything killed by the
left adjoint.** This is the implication "(1) implies (2)" of [Stacks, Tag 09IR]: if
`E ⟶ R (L E)` is invertible then `E` lies in the image of `R` up to isomorphism, and right
orthogonality is closed under isomorphism. -/
theorem rightOrthogonal_shiftClosure_singleton_of_isIso_unit {K E : C}
    (hK : IsZero (L.obj K)) (hE : IsIso (adj.unit.app E)) :
    ((singleton K).shiftClosure ℤ).rightOrthogonal E :=
  prop_of_iso _ (asIso (adj.unit.app E)).symm
    (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj adj hK (L.obj E))

end Shift

/-! ### The left adjoint applied to the unit -/

section Counit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

/-- **`L` of the unit is invertible wherever the counit is.** The two are mutually inverse at
`L E` by the triangle identity `L(η_E) ≫ ε_{L E} = 𝟙`. -/
theorem isIso_map_unit_of_isIso_counit (E : C) (hE : IsIso (adj.counit.app (L.obj E))) :
    IsIso (L.map (adj.unit.app E)) := by
  have h : L.map (adj.unit.app E) ≫ adj.counit.app (L.obj E) = 𝟙 _ :=
    adj.left_triangle_components E
  rw [← IsIso.eq_comp_inv] at h
  rw [h]
  infer_instance

end Counit

/-! ### The equivalence of [Stacks, Tag 09IR], reduced to the detection hypothesis -/

section Triangulated

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.CommShift ℤ] [L.IsTriangulated]

/-- **The cone of the unit is zero**, for an object right orthogonal to the shifts of `K`,
granted the detection hypothesis. Right orthogonality to the shifts of `K` is a triangulated
subcategory of the source, so the third vertex of a distinguished triangle
`E ⟶ R (L E) ⟶ N ⟶ E⟦1⟧` inherits it; and `L N = 0` because `L` of the unit is invertible. -/
theorem isZero_of_rightOrthogonal_shiftClosure_singleton_of_isZero_map
    {K E N : C} (hK : IsZero (L.obj K)) (hE : IsIso (adj.counit.app (L.obj E)))
    (hdet : ∀ M : C, IsZero (L.obj M) →
      ((singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M)
    (hortho : ((singleton K).shiftClosure ℤ).rightOrthogonal E)
    {g : R.obj (L.obj E) ⟶ N} {h : N ⟶ E⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (adj.unit.app E) g h ∈ distTriang C) :
    IsZero N := by
  refine hdet N (Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hT) ?_)
    (ext_of_isTriangulatedClosed₃ _ _ hT hortho
      (rightOrthogonal_shiftClosure_singleton_rightAdjoint_obj adj hK (L.obj E)))
  exact isIso_map_unit_of_isIso_counit adj E hE

/-- **An object right orthogonal to the shifts of `K` has invertible unit**, granted the
detection hypothesis. This is the implication "(2) implies (1)" of [Stacks, Tag 09IR] with its
geometric content isolated: the cone of the unit is right orthogonal to the shifts of `K` and is
killed by `L`, hence zero, and a distinguished triangle with vanishing third vertex has
invertible first morphism. -/
theorem isIso_unit_of_rightOrthogonal_shiftClosure_singleton {K E : C}
    (hK : IsZero (L.obj K)) (hE : IsIso (adj.counit.app (L.obj E)))
    (hdet : ∀ M : C, IsZero (L.obj M) →
      ((singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M)
    (hortho : ((singleton K).shiftClosure ℤ).rightOrthogonal E) :
    IsIso (adj.unit.app E) := by
  obtain ⟨N, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app E)
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1
    (isZero_of_rightOrthogonal_shiftClosure_singleton_of_isZero_map adj hK hE hdet hortho hT)

/-- **[Stacks, Tag 09IR], abstractly.** For an adjunction `L ⊣ R` between pretriangulated
categories with `L` triangulated, an object `K` killed by `L`, and an object `E` at which the
counit is invertible, the unit `E ⟶ R (L E)` is invertible if and only if `E` is right orthogonal
to every shift of `K` — granted the detection hypothesis `hdet`, which is where the Koszul
mathematics of the source sits. -/
theorem isIso_unit_iff_rightOrthogonal_shiftClosure_singleton {K E : C}
    (hK : IsZero (L.obj K)) (hE : IsIso (adj.counit.app (L.obj E)))
    (hdet : ∀ M : C, IsZero (L.obj M) →
      ((singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M) :
    IsIso (adj.unit.app E) ↔ ((singleton K).shiftClosure ℤ).rightOrthogonal E :=
  ⟨rightOrthogonal_shiftClosure_singleton_of_isIso_unit adj hK,
    isIso_unit_of_rightOrthogonal_shiftClosure_singleton adj hK hE hdet⟩

/-- **The generation step of [Stacks, Tag 09IS] and [Stacks, Tag 0A9A], with the hypothesis on
the unit replaced by the detection hypothesis.** This is
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_biprod_of_adjunction` with
its `hunit` supplied by the equivalence above, so the remaining geometric inputs are exactly the
three the sources use: `L K = 0` (the Koszul complex restricts to zero on the open), invertibility
of the counit (`Rj_*` is fully faithful), and `hdet` ([Stacks, Tag 09IR] proper). -/
theorem isWeakTriangulatedGenerator_singleton_biprod_of_detection
    {Q K : C} [HasBinaryBiproduct Q K] {P : D} (hret : Retract P (L.obj Q))
    (hP : (singleton P).IsWeakTriangulatedGenerator)
    (hK : IsZero (L.obj K)) (hcounit : ∀ Y : D, IsIso (adj.counit.app Y))
    (hdet : ∀ M : C, IsZero (L.obj M) →
      ((singleton K).shiftClosure ℤ).rightOrthogonal M → IsZero M) :
    (singleton (Q ⊞ K)).IsWeakTriangulatedGenerator :=
  isWeakTriangulatedGenerator_singleton_biprod_of_adjunction adj hret hP fun _ hortho =>
    isIso_unit_of_rightOrthogonal_shiftClosure_singleton adj hK (hcounit _) hdet hortho

end Triangulated

end CategoryTheory.ObjectProperty

end

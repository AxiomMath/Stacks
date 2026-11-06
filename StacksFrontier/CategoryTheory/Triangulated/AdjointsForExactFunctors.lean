module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute

/-!
# Adjoints of exact functors between triangulated categories

Let `F : C ⥤ D` be an exact functor between pre-triangulated categories. If `F` admits a right
adjoint `G : D ⥤ C`, then `G` is exact as well; this is Mathlib's, and is recorded here by the
`add_to_stacks` lines below.

This file proves that such an `F` is an equivalence as soon as it is fully faithful and `G` has
zero kernel.

## Implementation notes

An *exact* functor between pre-triangulated categories is `[·.CommShift ℤ]` together with
`[·.IsTriangulated]` — the commutation with the shift is data. For a right adjoint that
commutation is not given in advance: `Adjunction.rightAdjointCommShift` is the `CommShift`
structure on `G` that the adjunction induces from the one on `F`, and it is the unique one
compatible with the unit (`Adjunction.CommShift.compatibilityUnit_unique_right`).

## References

* [Stacks project, Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D)
* [Stacks project, Tag 001P](https://stacks.math.columbia.edu/tag/001P) (Yoneda)
-/

@[expose] public section

-- Mathlib produces the commutation of the right adjoint with the shift, its additivity, and
-- its preservation of distinguished triangles.
add_to_stacks 0A8D "the commutation of the right adjoint with the shift"
  CategoryTheory.Adjunction.rightAdjointCommShift
add_to_stacks 0A8D "additivity of the right adjoint"
  CategoryTheory.Adjunction.right_adjoint_additive
add_to_sga "4 XVII 2.2.13.1" "special case" CategoryTheory.Adjunction.right_adjoint_additive
add_to_stacks 0A8D "the right adjoint preserves distinguished triangles"
  CategoryTheory.Adjunction.isTriangulated_rightAdjoint
add_to_sga "4½ Etat_0 2.6.7" "more general" CategoryTheory.Adjunction.isTriangulated_rightAdjoint

end

section

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

(Stacks Tag 09J1, Lemma 13.7.2.)

Let `D` and `D'` be triangulated categories, and let `F : D ⥤ D'` and
`G : D' ⥤ D` be functors. Assume that:

1. `F` and `G` are exact (triangulated) functors;
2. `F` is fully faithful;
3. `G` is a right adjoint to `F` (equivalently, `F` is a left adjoint to `G`); and
4. the kernel of `G` is zero (i.e. for every object `X` of `D'`, `G(X) ≅ 0`
   implies `X ≅ 0`).

Then `F` is an equivalence of categories.
-/

/-
## Background and context (following Stacks, Chapter 13, Derived Categories)

- **Exact functor of triangulated categories.** A functor `F : D ⥤ D'` is
  *exact* if it is additive, comes equipped with a natural isomorphism
  `F ∘ [1] ≅ [1] ∘ F` commuting with the shift functors, and transforms
  distinguished triangles into distinguished triangles. In Mathlib this is
  packaged as `F.CommShift ℤ` (the compatibility with the shift functors)
  together with `F.IsTriangulated` (the functor sends distinguished triangles
  to distinguished triangles). In particular an exact functor sends zero objects
  to zero objects.

- **Adjunction.** `G` is a *right adjoint* to `F` (equivalently, `F` is a *left
  adjoint* to `G`) if there is a natural bijection
  `Hom_{D'}(F X, Y) ≅ Hom_{D}(X, G Y)`, natural in `X` and `Y`. This is the
  Mathlib relation `F ⊣ G`, which carries a *unit* `η : 𝟭 D ⟶ F ⋙ G` and a
  *counit* `ε : G ⋙ F ⟶ 𝟭 D'` satisfying the triangle identities.

- **Fully faithful functor.** `F` is *fully faithful* if for every pair of
  objects `X, X'` the induced map `Hom_{D}(X, X') → Hom_{D'}(F X, F X')` is a
  bijection. In Mathlib this is `F.Full` together with `F.Faithful`.

- **Kernel of an exact functor (Stacks Definition 13.6.5, via Lemma 13.6.2).**
  For an exact functor `G : D' ⥤ D`, the *kernel* of `G` is the strictly full
  subcategory of `D'` whose objects are those `X` with `G X` a zero object.
  We say *the kernel of `G` is zero* if for every object `X` of `D'`,
  `G X ≅ 0` implies `X ≅ 0`. In a (pre)additive setting "is a zero object" is
  the predicate `CategoryTheory.Limits.IsZero`, and we use the formulation
  `IsZero (G.obj X) → IsZero X`.

- **Equivalence of categories.** `F` is an *equivalence of categories* if there
  is a quasi-inverse functor with the appropriate natural isomorphisms;
  equivalently, `F` is fully faithful and essentially surjective. In Mathlib
  this is the predicate `F.IsEquivalence`.
-/

open CategoryTheory CategoryTheory.Triangulated CategoryTheory.Limits

universe v v' u u'

variable {D : Type u} {D' : Type u'} [Category.{v} D] [Category.{v'} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  [IsTriangulated D] [IsTriangulated D']

variable (F : D ⥤ D') (G : D' ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]

omit [IsTriangulated D] [IsTriangulated D'] in
/-- Let `F : D ⥤ D'` and `G : D' ⥤ D` be exact functors of pretriangulated categories with
`F ⊣ G`. If `F` is fully faithful and every `X : D'` with `G X` a zero object is itself a zero
object, then `F` is an equivalence of categories. -/
@[stacks 09J1]
theorem isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero
    [F.IsTriangulated] [G.IsTriangulated] [F.Full] [F.Faithful]
    (adj : F ⊣ G)
    (hker : ∀ X : D', IsZero (G.obj X) → IsZero X) :
    F.IsEquivalence := by
  have hunit : IsIso adj.unit := Adjunction.unit_isIso_of_L_fully_faithful adj
  have hess : F.EssSurj := ⟨fun X => by
    obtain ⟨Z, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle (adj.counit.app X)
    have hGiso : IsIso (G.map (adj.counit.app X)) :=
      IsIso.of_isIso_comp_left (adj.unit.app (G.obj X)) (G.map (adj.counit.app X))
    have : IsIso (adj.counit.app X) :=
      (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).mp <| hker Z <|
        Pretriangulated.Triangle.isZero₃_of_isIso₁
          (G.mapTriangle.obj (Pretriangulated.Triangle.mk (adj.counit.app X) g h))
          (G.map_distinguished _ hT) hGiso
    exact ⟨G.obj X, ⟨asIso (adj.counit.app X)⟩⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := hess }

end

end

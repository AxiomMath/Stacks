module

public import StacksFrontier.Homology.Injectives.BrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilitySmallHom
import all StacksFrontier.Homology.Injectives.BrownRepresentability
import StacksCore.Tactic.StacksAttribute

/-!
# Exact right adjoints out of the derived category of a Grothendieck abelian category

Let `A` be a Grothendieck abelian category and let `F : D(A) ⥤ D` be an exact functor into a
triangulated category which transforms direct sums into direct sums. Then `F` has an exact right
adjoint, [Stacks, Tag 0F5Y].

## Main results

* `Stacks.Injectives.isLeftAdjoint_of_isGrothendieckAbelian`: `F` is a left adjoint.
* `Stacks.Injectives.exists_exact_rightAdjoint_of_isGrothendieckAbelian`: **[Stacks, Tag 0F5Y]**,
  the right adjoint exists and is exact.

## Implementation notes

*Universes.* Here `A : Type u` has morphisms in `Type v` and is Grothendieck abelian relative to
`v`. Every Grothendieck abelian category met in practice is of this kind, for instance sheaves of
modules on a site with sections in `Type v`. The direct sums `F` must preserve are indexed by
`Type v`, and the morphism groups out of the image of `F` must be `Type v`-small. The derived
category of `A` may be any model `HasDerivedCategory.{z} A`, and the morphisms of the target `D`
may live in any universe.

These are the universes of the source's statement. The untagged declaration
`Stacks.Injectives.exists_exact_rightAdjoint` and
`Stacks.Injectives.isRepresentable_of_isGrothendieckAbelian` ask instead for
`IsGrothendieckAbelian.{max w u v} A`. No category with a nonzero object `G` and objects in a
universe above `v` satisfies that. A direct sum `⨁_κ G` indexed by a type `κ` in a universe above
`v` would have `Hom(⨁_κ G, G) = ∏_κ End(G)`, which has at least `2^κ` elements, yet it is a type in
`Type v`. A Grothendieck abelian category does have objects in a universe above `v`, so the two
base declarations apply to no nonzero category.

*Proof.* Brown representability for `D(A)` is the core
`Stacks.Injectives.isRepresentable_of_equivalence_isGrothendieckAbelian` of
`StacksFrontier.Homology.Injectives.BrownRepresentability`. It represents a homological functor
`D(A)ᵒᵖ ⥤ AddCommGrpCat.{v}` that transforms `Type v`-indexed direct sums into products. We apply
it to the `Type v`-shrink `CategoryTheory.ObjectProperty.shrinkAb` of `W ↦ Hom_D(F W, Y)`, which
is again homological and again transforms direct sums into products. Composing the representing
bijection with `Shrink.addEquiv` represents `W ↦ Hom_D(F W, Y)` itself, so the partial right
adjoint of `F` is defined at every object. The core is private to that module, hence the
`import all`. The new declarations live in this separate module, and not beside the base ones,
so that the base module and its compiled declarations are unchanged.

## References

* [Stacks Project, Tag 0F5Y](https://stacks.math.columbia.edu/tag/0F5Y)
* [Stacks Project, Tag 0F5X](https://stacks.math.columbia.edu/tag/0F5X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite Opposite

universe z v u v' u'

namespace Stacks.Injectives

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{z} A]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : DerivedCategory A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
  [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F]

/-- The partial right adjoint of an exact, direct-sum-preserving functor out of the derived
category of a Grothendieck abelian category is defined at every object `Y`, as soon as the
morphism groups `Hom(F W, Y)` are `Type v`-small. -/
theorem rightAdjointObjIsDefined_of_isGrothendieckAbelian
    (hsmall : ∀ (W : DerivedCategory A) (Y : D), Small.{v} (F.obj W ⟶ Y)) (Y : D) :
    F.rightAdjointObjIsDefined Y := by
  let P := F.op ⋙ preadditiveYoneda.obj Y
  have : ∀ U : (DerivedCategory A)ᵒᵖ, Small.{v} (P.obj U) := fun U ↦ hsmall U.unop Y
  have : ∀ α : Type v, PreservesLimitsOfShape (Discrete α) P := fun α ↦
    have := preservesLimitsOfShape_op (Discrete α) F
    have := preservesLimitsOfShape_preadditiveYoneda_obj (J := Discrete α) Y
    inferInstance
  have : P.IsHomological :=
    main_statement_comp_triangulated_homological F.op (preadditiveYoneda.obj Y)
  have : (CategoryTheory.Equivalence.refl : A ≌ A).functor.Additive :=
    inferInstanceAs (𝟭 A).Additive
  have : (CategoryTheory.Equivalence.refl : A ≌ A).inverse.Additive :=
    inferInstanceAs (𝟭 A).Additive
  obtain ⟨X, ⟨r⟩⟩ := (isRepresentable_of_equivalence_isGrothendieckAbelian
    (CategoryTheory.Equivalence.refl : A ≌ A) (ObjectProperty.shrinkAb.{v} P)).has_representation
  refine (F.rightAdjointObjIsDefined_iff Y).2 (Functor.RepresentableBy.isRepresentable
    (Y := X) { homEquiv := fun {W} ↦ r.homEquiv.trans Shrink.addEquiv.toEquiv,
               homEquiv_comp := ?_ })
  intro W W' f g
  change Shrink.addEquiv (r.homEquiv (f ≫ g)) = F.map f ≫ Shrink.addEquiv (r.homEquiv g)
  rw [r.homEquiv_comp]
  exact ObjectProperty.shrinkAb_map_addEquiv P f.op _

/-- The adjoint-existence part of [Stacks, Tag 0F5Y]. Let `A` be a Grothendieck abelian category
and `D` a pretriangulated category. An exact functor `F : D(A) ⥤ D` which transforms direct sums
into direct sums, and whose morphism groups `Hom(F W, Y)` are small, is a left adjoint. -/
theorem isLeftAdjoint_of_isGrothendieckAbelian
    (hsmall : ∀ (W : DerivedCategory A) (Y : D), Small.{v} (F.obj W ⟶ Y)) :
    F.IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top (eq_top_iff.2 fun Y _ ↦
    rightAdjointObjIsDefined_of_isGrothendieckAbelian A F hsmall Y)

/-- **[Stacks, Tag 0F5Y].** Let `A` be a Grothendieck abelian category and `D` a pretriangulated
category. An exact functor `F : D(A) ⥤ D` which transforms direct sums into direct sums, and whose
morphism groups `Hom(F W, Y)` are small, has an exact right adjoint: a functor `G`, an adjunction
`F ⊣ G`, and a commutation of `G` with the shift making `G` triangulated.

Here `A` is Grothendieck abelian relative to its morphism universe `v` and the direct sums are
indexed by `Type v`. The smallness of `Hom(F W, Y)` is the source's standing convention that
morphisms form sets, read at that universe. It is also necessary: if `F ⊣ G`, then
`Hom(F W, Y) ≃ Hom(W, G Y)`, and the derived category of `A` is locally `Type v`-small. -/
@[stacks 0F5Y "A Grothendieck abelian relative to its morphism universe v, direct sums indexed \
by Type v, Hom(F W, Y) Type v-small (the source's convention that morphisms form sets); D may be \
any pretriangulated category"]
theorem exists_exact_rightAdjoint_of_isGrothendieckAbelian
    (hsmall : ∀ (W : DerivedCategory A) (Y : D), Small.{v} (F.obj W ⟶ Y)) :
    ∃ (G : D ⥤ DerivedCategory A) (_ : F ⊣ G) (commShift : G.CommShift ℤ),
      letI := commShift
      G.IsTriangulated := by
  have := isLeftAdjoint_of_isGrothendieckAbelian A F hsmall
  let adj : F ⊣ F.rightAdjoint := Adjunction.ofIsLeftAdjoint F
  let : F.rightAdjoint.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨F.rightAdjoint, adj, inferInstance, adj.isTriangulated_rightAdjoint⟩

end Stacks.Injectives

end

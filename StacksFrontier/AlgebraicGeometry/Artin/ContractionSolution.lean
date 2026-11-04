module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFunctor

/-!
# Solutions of Artin's contraction problem

In the situation of Stacks 0GH8, recorded by
`AlgebraicGeometry.Artin.ContractionSituation`, a *solution* of the contraction problem with
target `X` is a proper morphism `f : X' ⟶ X` of algebraic spaces over `S`, a closed subset
`T ⊆ |X|` and an isomorphism `a : X_{/T} ⟶ W` of formal algebraic spaces over `S` such that

1. `T'` is the inverse image of `T` under `|f| : |X'| ⟶ |X|`,
2. `f` maps `U'` isomorphically onto an open subspace `U ⊆ X`, and
3. `g = a ∘ f_{/T}`, where `f_{/T} : X'_{/T'} ⟶ X_{/T}` is the morphism of completions
   induced by `f`.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.Solution`: a solution of the contraction
  problem with target `X`.
* `AlgebraicGeometry.Artin.ContractionSituation.IsSolution`: `X` is a solution, that is, a
  solution with target `X` exists.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.preimage_compl_T`: condition (1) read
  on complements, `|f|⁻¹(|X| ∖ T) = |X'| ∖ T' = |U'|`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.range_pointsMap_U'_comp_f`: condition
  (2) read on points, `f` maps the point set of `U'` onto the point set of `U`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.completionSheafRestrict_eq`: condition
  (3) solved for `f_{/T}`, which is `g` followed by the inverse of `a`.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A *solution* of the contraction problem of Stacks 0GH8 with target `X`: a proper morphism
`f : X' ⟶ X` of algebraic spaces over `S`, a closed subset `T ⊆ |X|` and an isomorphism
`a : X_{/T} ⟶ W` such that `T'` is the inverse image of `T` under `|f|`, such that `f` maps
`U'` isomorphically onto an open subspace `U ⊆ X`, and such that `g = a ∘ f_{/T}`. -/
structure Solution (c : ContractionSituation B S hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- `X` is an algebraic space over `S`, in the sense of Stacks 025Y. -/
  isAlgebraicSpace_X : IsAlgebraicSpace B S hS X
  /-- The contraction `f : X' ⟶ X`. -/
  f : c.X' ⟶ X
  /-- `f` is a proper morphism of algebraic spaces over `S`, in the sense of Stacks 03ZM. -/
  isProper_f : Space.IsProper B S hS f
  /-- The closed subset `T ⊆ |X|` that `T'` is contracted to. -/
  T : Set (Space.points B S hS X)
  /-- `T` is closed in the point space `|X|` of Stacks 03BY. -/
  isClosed_T : IsClosed T
  /-- Condition (1): `T'` is the inverse image of `T` under `|f| : |X'| ⟶ |X|`. -/
  preimage_T : Space.pointsMap B S hS c.X' f ⁻¹' T = c.T'
  /-- Condition (2): the subspace `U ⊆ X` that `f` maps `U'` isomorphically onto. -/
  U : Subfunctor X
  /-- Condition (2): `U` is an open subspace of `X`, in the sense of Stacks 02YU. -/
  isOpenSubspace_U : Space.IsOpenSubspace B S hS U
  /-- Condition (2): the isomorphism `U' ⟶ U` that `f` restricts to. -/
  isoU : c.U'.toFunctor ≅ U.toFunctor
  /-- Condition (2): the isomorphism `U' ⟶ U` is the restriction of `f`: it is compatible
  with the inclusions of `U'` into `X'` and of `U` into `X`. -/
  isoU_comp_ι : isoU.hom ≫ U.ι = c.U'.ι ≫ f
  /-- Condition (3): the isomorphism `a : X_{/T} ⟶ W` from the completion of `X` along `T`
  of Stacks 0AMC to the formal algebraic space `W`. -/
  a : Space.completionSheaf B S hS X T ≅ c.W
  /-- Condition (3): `g = a ∘ f_{/T}`, where `f_{/T} : X'_{/T'} ⟶ X_{/T}` is the morphism
  of completions induced by `f`. -/
  completion_comp_a :
    Space.completionSheafRestrict B S hS f c.T' T preimage_T.symm.subset ≫ a.hom = c.g

/-- `X` *is a solution* of the contraction problem of Stacks 0GH8 when some solution with
target `X` exists, that is, when the data `(f, T, a)` of
`AlgebraicGeometry.Artin.ContractionSituation.Solution` can be found for it. -/
def IsSolution (c : ContractionSituation B S hS)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  Nonempty (Solution c X)

namespace Solution

variable {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Solution c X)

/-- Condition (1) read on complements: the inverse image of `|X| ∖ T` under `|f|` is
`|X'| ∖ T'`, the point set of `U'`. -/
theorem preimage_compl_T : Space.pointsMap B S hS c.X' s.f ⁻¹' s.Tᶜ = c.T'ᶜ := by
  rw [Set.preimage_compl, s.preimage_T]

/-- Condition (2) read on points: `f` maps the point set of `U'` onto the point set of `U`. -/
theorem range_pointsMap_U'_comp_f :
    Set.range (Space.pointsMap B S hS c.U'.toFunctor (c.U'.ι ≫ s.f)) =
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) := by
  have hsurj : Function.Surjective (Space.pointsMap B S hS c.U'.toFunctor s.isoU.hom) := by
    intro y
    have h : Space.pointsMap B S hS s.U.toFunctor (s.isoU.inv ≫ s.isoU.hom) = id := by
      rw [Iso.inv_hom_id, Space.pointsMap_id]
    rw [Space.pointsMap_comp] at h
    exact ⟨Space.pointsMap B S hS s.U.toFunctor s.isoU.inv y, congrFun h y⟩
  rw [← s.isoU_comp_ι, Space.pointsMap_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]

/-- Condition (3) solved for the induced morphism of completions: `f_{/T}` is `g` followed by
the inverse of `a`. -/
theorem completionSheafRestrict_eq :
    Space.completionSheafRestrict B S hS s.f c.T' s.T s.preimage_T.symm.subset =
      c.g ≫ s.a.inv := by
  rw [← s.completion_comp_a, Category.assoc, s.a.hom_inv_id, Category.comp_id]

end Solution

end AlgebraicGeometry.Artin.ContractionSituation

end

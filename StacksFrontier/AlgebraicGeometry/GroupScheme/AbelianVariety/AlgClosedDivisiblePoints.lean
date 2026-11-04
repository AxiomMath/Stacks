module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.SeparablyClosedDivisiblePoints

/-!
# Rational points of a group scheme over an algebraically closed field, under a surjective `[n]`

Let `A` be a group scheme locally of finite type over an algebraically closed field `k`. If
multiplication by `n` on `A` is surjective, then every `k`-rational point of `A` is `[n]` of a
`k`-rational point. The fibre of `[n]` over the point is nonempty and locally of finite type over
`k`, so it has a closed point, and a closed point of such a scheme is `k`-rational
(`AlgebraicGeometry.pointOfClosedPoint`).

Over a separably closed field the same conclusion needs `[n]` étale
(`Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_isSepClosed`). Over an algebraically closed field
surjectivity is enough, and surjectivity follows from étaleness
(`Stacks.Groupoids.surjective_zpow_id_left_of_etale`) or from finiteness and flatness alike.

## Main results

* `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed`
* `Stacks.Groupoids.exists_comp_zpow_id_left_eq_of_etale_of_isAlgClosed`

## References

* [Stacks Project, Tag 03RP](https://stacks.math.columbia.edu/tag/03RP)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.Groupoids

variable {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]

/-- **Over an algebraically closed field, a surjective multiplication by `n` makes every rational
point divisible by `n`.** Let `A` be a group scheme locally of finite type over an algebraically
closed field `k` on which multiplication by `n` is surjective, and let `g` be a `k`-rational point
of `A`. Then `g = [n] ∘ g'` for some `k`-rational point `g'`. -/
theorem exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed [IsAlgClosed k]
    [LocallyOfFiniteType A.hom] (n : ℤ) (hS : Surjective ((𝟙 A : A ⟶ A) ^ n).left)
    (g : Spec (.of k) ⟶ A.left) (hg : g ≫ A.hom = 𝟙 (Spec (.of k))) :
    ∃ g' : Spec (.of k) ⟶ A.left, g' ≫ A.hom = 𝟙 (Spec (.of k)) ∧
      g' ≫ ((𝟙 A : A ⟶ A) ^ n).left = g := by
  set m := ((𝟙 A : A ⟶ A) ^ n).left
  have hm : m ≫ A.hom = A.hom := zpow_id_left_comp_hom A n
  have : LocallyOfFiniteType (m ≫ A.hom) := by rw [hm]; infer_instance
  have : LocallyOfFiniteType m := locallyOfFiniteType_of_comp m A.hom
  have : JacobsonSpace (pullback m g : Scheme.{u}) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd m g)
  obtain ⟨p, -⟩ := (pullback.snd m g).surjective
    (Nonempty.some (inferInstanceAs (Nonempty ↥(Spec (CommRingCat.of k)))))
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (X := (pullback m g : Scheme.{u}))
    (Z := Set.univ) ⟨p, trivial⟩ isClosed_univ.isLocallyClosed
  have hz' : IsClosed ({z} : Set (pullback m g : Scheme.{u})) := hz
  let s := pointOfClosedPoint (pullback.snd m g) z hz'
  have hs : s ≫ pullback.snd m g = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have key : (s ≫ pullback.fst m g) ≫ m = g := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  refine ⟨s ≫ pullback.fst m g, ?_, key⟩
  rw [← hm, ← Category.assoc, key, hg]

/-- **Over an algebraically closed field, an étale multiplication by `n` on an abelian variety
makes every rational point divisible by `n`.** -/
theorem exists_comp_zpow_id_left_eq_of_etale_of_isAlgClosed [IsAlgClosed k]
    [AlgebraicGeometry.IsAbelianVariety k A] (n : ℤ) (hE : Etale ((𝟙 A : A ⟶ A) ^ n).left)
    (g : Spec (.of k) ⟶ A.left) (hg : g ≫ A.hom = 𝟙 (Spec (.of k))) :
    ∃ g' : Spec (.of k) ⟶ A.left, g' ≫ A.hom = 𝟙 (Spec (.of k)) ∧
      g' ≫ ((𝟙 A : A ⟶ A) ^ n).left = g :=
  exists_comp_zpow_id_left_eq_of_surjective_of_isAlgClosed A n
    (surjective_zpow_id_left_of_etale A n hE) g hg

end Stacks.Groupoids

end

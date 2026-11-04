module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GeneratorAgreement
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicStalkPullback
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MultiplierFromSections
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.StalkUnitDescent

/-!
# The ratio of two multipliers of Tag 0BD7 is a unit of the local ring of the base

The uniqueness sentence of the penultimate paragraph of [Stacks, Tag 0BD7] is that a multiplier
`g` is well defined "up to multiplication by an element of `𝒪_{Y, y}^*`". Neither multiplier is
a regular function, so the sentence is a statement about germs of `𝒦_Y`; this file proves it.

The chain is: two members `t_i`, `t_j` of the family generate `ℒ` on the intersection of their
generating loci, so they differ there by a unit section `c` of `𝒪_X`
(`Stacks.SheafOfModules.exists_isUnit_smul_restrictₛₗ_of_subset_generatingLocus`); that relation
rises to the multipliers
(`Stacks.InvertiblePullback.restrict_pullback_eq_mul_of_isPullMeromorphicFamily`); at a point of
that intersection the two germs of `𝒦_Y` are written over a common denominator
(`AlgebraicGeometry.exists_mul_toTotalQuotientStalk_eq₂`), and the square of [Stacks, Tag 02OT]
on the local rings (`AlgebraicGeometry.totalQuotientStalkMap_toTotalQuotientStalk`) turns the
relation into one between the *numerators* and their images under `φ^♯`, which is the shape
`AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_stalkMap` descends.

## Main results

* `Stacks.InvertiblePullback.exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamily`: the germs of
  two multipliers at a point over which their sections both generate differ by a unit of
  `𝒪_{Y, φ(x)}`.

## Implementation notes

The hypothesis is the relation `t_i = c t_j` with `c` a unit, not the generating loci: the
caller supplies the open and the unit, which is what lets the same statement serve both the
intersection of two generating loci and any smaller open.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Meromorphic

universe u

namespace Stacks.InvertiblePullback

/-- **The uniqueness clause of [Stacks, Tag 0BD7] on the local ring of the base.** If the two
sections `t_i`, `t_j` of the family differ on `W` by a unit of `𝒪_X(W)`, then at a point of `W`
the germs of the two multipliers differ by a unit of `𝒪_{Y, φ(x)}`. -/
theorem exists_isUnit_mul_germ_eq_of_isPullMeromorphicFamily
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsIntegral X] [IsIntegral Y]
    (L : _root_.SheafOfModules.{u} (_root_.structureSheafRing X.toRingedSpace))
    (s : MeromorphicSection X.sheaf L) {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    (ht : IsPullMeromorphicFamily f L s g t)
    (i j : ι) {W : Opens X.toRingedSpace.carrier} {x : X} (hxW : x ∈ W)
    (hWi : W ≤ (f ⁻¹ᵁ A i : X.Opens)) (hWj : W ≤ (f ⁻¹ᵁ A j : X.Opens))
    (c : X.presheaf.obj (op W)) (hcu : IsUnit c)
    (hc : L.val.restrictₛₗ (homOfLE hWi).op (t i)
      = c • L.val.restrictₛₗ (homOfLE hWj).op (t j))
    (hxi : f.base x ∈ A i) (hxj : f.base x ∈ A j) :
    ∃ v : ↑(Y.presheaf.stalk (f.base x)), IsUnit v ∧
      Y.totalQuotientSheaf.presheaf.germ (A i) (f.base x) hxi (g i)
        = toTotalQuotientStalk Y (f.base x) v *
          Y.totalQuotientSheaf.presheaf.germ (A j) (f.base x) hxj (g j) := by
  have hpull : ∀ (k : ι) (hWk : W ≤ (f ⁻¹ᵁ A k : X.Opens)) (hxk : f.base x ∈ A k),
      X.totalQuotientSheaf.presheaf.germ W x hxW
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.map (homOfLE hWk).op).hom
              (((Scheme.ringSheafPullbackOfFlat f).hom.app (op (A k))).hom (g k)))
        = totalQuotientStalkMap f x
            (Y.totalQuotientSheaf.presheaf.germ (A k) (f.base x) hxk (g k)) := by
    intro k hWk hxk
    rw [totalQuotientStalkMap_germ f x (A k) hxk (g k)]
    exact TopCat.Presheaf.germ_res_apply X.totalQuotientSheaf.presheaf (homOfLE hWk) x hxW _
  have hkappa : X.totalQuotientSheaf.presheaf.germ W x hxW
        (((toTotalQuotientRingSheaf X).hom.app (op W)).hom c)
      = toTotalQuotientStalk X x (X.presheaf.germ W x hxW c) :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW X.toTotalQuotientSheaf.hom c).symm
  have hgerm : totalQuotientStalkMap f x
        (Y.totalQuotientSheaf.presheaf.germ (A i) (f.base x) hxi (g i))
      = toTotalQuotientStalk X x (X.presheaf.germ W x hxW c) *
        totalQuotientStalkMap f x
          (Y.totalQuotientSheaf.presheaf.germ (A j) (f.base x) hxj (g j)) := by
    rw [← hpull i hWi hxi, ← hpull j hWj hxj, ← hkappa]
    exact (congrArg (ConcreteCategory.hom (X.totalQuotientSheaf.presheaf.germ W x hxW))
        (restrict_pullback_eq_mul_of_isPullMeromorphicFamily f L s g t hs ht
          i j hWi hWj c hc)).trans
      (map_mul (ConcreteCategory.hom (X.totalQuotientSheaf.presheaf.germ W x hxW)) _ _)
  obtain ⟨p, q, d, hd, hpd, hqd⟩ := exists_mul_toTotalQuotientStalk_eq₂ Y (f.base x)
    (Y.totalQuotientSheaf.presheaf.germ (A i) (f.base x) hxi (g i))
    (Y.totalQuotientSheaf.presheaf.germ (A j) (f.base x) hxj (g j))
  have hK : ∀ (a : ↑(Y.totalQuotientSheaf.presheaf.stalk (f.base x)))
      (e r : ↑(Y.presheaf.stalk (f.base x))),
      a * toTotalQuotientStalk Y (f.base x) e = toTotalQuotientStalk Y (f.base x) r →
      totalQuotientStalkMap f x a * toTotalQuotientStalk X x ((f.stalkMap x).hom e)
        = toTotalQuotientStalk X x ((f.stalkMap x).hom r) := by
    intro a e r h
    rw [← totalQuotientStalkMap_toTotalQuotientStalk f x e,
      ← totalQuotientStalkMap_toTotalQuotientStalk f x r,
      ← map_mul (totalQuotientStalkMap f x), h]
  have hPi := hK _ d p hpd
  have hPj := hK _ d q hqd
  have hnum : toTotalQuotientStalk X x ((f.stalkMap x).hom p)
      = toTotalQuotientStalk X x
          (ConcreteCategory.hom (X.presheaf.germ W x hxW) c * (f.stalkMap x).hom q) := by
    rw [map_mul (toTotalQuotientStalk X x), ← hPj, ← hPi, hgerm, mul_assoc]
  obtain ⟨v, hv, hvpq⟩ := exists_isUnit_mul_eq_of_isUnit_stalkMap f x p q
    (hcu.map (ConcreteCategory.hom (X.presheaf.germ W x hxW)))
    (toTotalQuotientStalk_injective X x hnum)
  exact ⟨v, hv, eq_mul_of_numerator_eq_mul Y (f.base x) hd hpd hqd hvpq⟩


end Stacks.InvertiblePullback

end

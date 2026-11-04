module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictPseudoCoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A direct summand of an `m`-pseudo-coherent object is `m`-pseudo-coherent

Let `X` be a ringed space. If a binary biproduct `A ⊞ B` in `D(𝒪_X)` is `m`-pseudo-coherent, then
each of `A` and `B` is. This is Stacks 064X, which the Stacks project states for modules over a
ring; the argument here is the same one, run on an open subspace of `X`.

The argument is a descending induction. Above the top degree in which `A ⊞ B` has cohomology both
summands are pseudo-coherent for trivial reasons, because cohomology that vanishes on a biproduct
vanishes on each summand — the identity of `H^j(A)` factors through `H^j(A ⊞ B)`. Each step down
applies Stacks 08CD part (1) to the split triangle `A ⟶ A ⊞ B ⟶ B ⟶ A⟦1⟧` and to its braided
counterpart.

The step the module case does not need is the localization. On a ringed space,
`m`-pseudo-coherence of `A ⊞ B` does *not* bound its cohomology globally — only on a
neighbourhood of each point. So the induction runs on such a neighbourhood, with the hypothesis
carried there by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` and the conclusion
brought back by `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`.

Stacks 09VA needs this: pushing a strictly perfect complex forward along a closed immersion gives
a complex whose terms are direct summands of `(i_*𝒪_Z)^{⊕n}`, while the hypothesis of 09VA is
about `i_*𝒪_Z` itself.

## Main results

* `AlgebraicGeometry.RingedSpace.isZero_homology_of_isZero_homology_biprod`: cohomology that
  vanishes on a biproduct vanishes on each summand.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod_of_isZero_homology_gt`: the
  descending induction, on a space where the cohomology of the biproduct is bounded above.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod`: both summands of an
  `m`-pseudo-coherent binary biproduct are `m`-pseudo-coherent. This is **Stacks 08CE** at a
  fixed degree; the two degree-free conclusions of that tag are in
  `StacksFrontier/Topology/Sheaves/Cohomology/PseudoCoherence/Summands.lean`.

## Implementation notes

The descending induction is separated out as a statement about one ringed space with a global
degree bound, which is what makes it free of any restriction functor; the localizing theorem then
only has to produce the bound and transport the hypothesis.

`AlgebraicGeometry.RingedSpace.derivedRestrictModules` is additive, hence preserves finite
biproducts, hence binary ones — the last step is Mathlib's
`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts`, a lemma rather than an
instance, so it is declared a local instance here. The resulting
`CategoryTheory.Functor.mapBiprod` is what lets the split triangle be formed on the restricted
objects while the hypothesis is about the restriction of the biproduct.

The two halves of the conclusion are the same statement with the summands exchanged, so each
proof establishes the left-hand one for an arbitrary pair and applies it twice, the second time
through `CategoryTheory.Limits.biprod.braiding`.

## References

* [Stacks Project, Tag 08CE](https://stacks.math.columbia.edu/tag/08CE)
* [Stacks Project, Tag 064X](https://stacks.math.columbia.edu/tag/064X)
* [Stacks Project, Lemma 20.46.10 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

universe d d' u

attribute [local instance] CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

namespace AlgebraicGeometry.RingedSpace

/-! ### Vanishing cohomology passes to the summands -/

/-- Cohomology that vanishes on a biproduct vanishes on each summand: the identity of `H^j(A)` is
`H^j` of the inclusion followed by `H^j` of the projection, and the object in the middle is
zero. -/
public theorem isZero_homology_of_isZero_homology_biprod {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)] {A B : DerivedCategory (OXMod.{u, u} Y)} {j : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj (A ⊞ B))) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj A) := by
  rw [IsZero.iff_id_eq_zero, ← (DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).map_id,
    show 𝟙 A = biprod.inl ≫ biprod.fst from by simp, CategoryTheory.Functor.map_comp,
    h.eq_of_src ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).map biprod.fst) 0,
    comp_zero]

/-! ### The descending induction, with a global degree bound -/

/-- Vanishing of cohomology in degree `j` transfers along an isomorphism. -/
private theorem isZero_homology_of_iso {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)] {A B : DerivedCategory (OXMod.{u, u} Y)} {j : ℤ}
    (e : A ≅ B) (h : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj B)) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj A) :=
  h.of_iso ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).mapIso e)

/-- **Both summands of an `m`-pseudo-coherent biproduct whose cohomology vanishes above some
degree `b` are `m`-pseudo-coherent.**

Above `max m b` each summand has no cohomology at all
(`AlgebraicGeometry.RingedSpace.isZero_homology_of_isZero_homology_biprod`), hence is
pseudo-coherent from that degree on
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isZero_homology_ge`). The split triangle
`A ⟶ A ⊞ B ⟶ B ⟶ A⟦1⟧` and Stacks 08CD part (1) then carry that down one degree at a time: the
triangle gives `B` in degree `i - 1` from `A` in degree `i` and `A ⊞ B` in degree `i - 1`, and the
braided triangle gives `A`. -/
public theorem isPseudoCoherentFrom_of_biprod_of_isZero_homology_gt {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)] (m b : ℤ)
    {A B : DerivedCategory (OXMod.{u, u} Y)} (hsum : IsPseudoCoherentFrom (A ⊞ B) m)
    (hb : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj (A ⊞ B))) :
    IsPseudoCoherentFrom A m ∧ IsPseudoCoherentFrom B m := by
  have hAN : IsPseudoCoherentFrom A (max m b + 1) :=
    isPseudoCoherentFrom_of_isZero_homology_ge _ _ fun j hj =>
      isZero_homology_of_isZero_homology_biprod (hb j (by omega))
  have hBN : IsPseudoCoherentFrom B (max m b + 1) :=
    isPseudoCoherentFrom_of_isZero_homology_ge _ _ fun j hj =>
      isZero_homology_of_isZero_homology_biprod
        (isZero_homology_of_iso (biprod.braiding B A) (hb j (by omega)))
  have descend : ∀ (i : ℤ) (_ : i ≤ max m b + 1), m ≤ i →
      IsPseudoCoherentFrom A i ∧ IsPseudoCoherentFrom B i :=
    Int.leInductionDown (m := max m b + 1) (fun _ => ⟨hAN, hBN⟩) fun i _ ih hmi => by
      have hs : IsPseudoCoherentFrom (A ⊞ B) (i - 1) := hsum.mono hmi
      have hAi : IsPseudoCoherentFrom A (i - 1 + 1) := by
        simpa only [sub_add_cancel] using (ih (by omega)).1
      have hBi : IsPseudoCoherentFrom B (i - 1 + 1) := by
        simpa only [sub_add_cancel] using (ih (by omega)).2
      exact ⟨isPseudoCoherentFrom_obj₃_of_distinguished (i - 1) (binaryBiproductTriangle B A)
          (binaryBiproductTriangle_distinguished B A) hBi (hs.ofIso (biprod.braiding A B)),
        isPseudoCoherentFrom_obj₃_of_distinguished (i - 1) (binaryBiproductTriangle A B)
          (binaryBiproductTriangle_distinguished A B) hAi hs⟩
  exact descend m (by omega) le_rfl

/-! ### The localized statement -/

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ V : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]

/-- **Stacks 064X on a ringed space: both summands of an `m`-pseudo-coherent binary biproduct in
`D(𝒪_X)` are `m`-pseudo-coherent.**

`m`-pseudo-coherence is local
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`), so it is enough to find,
around every point, an open `U` on which the restriction of the summand is `m`-pseudo-coherent.
Choose `U` so that `A ⊞ B` has no cohomology above some degree there
(`AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict`); restriction is
additive, so `(A ⊞ B)|_U ≅ A|_U ⊞ B|_U`, and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod_of_isZero_homology_gt` applies on
`X|U`.

This is also **Stacks 08CE** for a fixed degree: the ringed-space statement of 08CE at a fixed
degree is literally this one, and both of its conclusions are proved here at once. -/
@[stacks 08CE "m-pseudo-coherent, both summands", sga "6 I 2.12" "n-pc: sum ⇒ F',F''"]
public theorem isPseudoCoherentFrom_of_biprod (m : ℤ)
    {A B : DerivedCategory (OXMod.{u, u} X)} (h : IsPseudoCoherentFrom (A ⊞ B) m) :
    IsPseudoCoherentFrom A m ∧ IsPseudoCoherentFrom B m := by
  have main : ∀ A B : DerivedCategory (OXMod.{u, u} X),
      IsPseudoCoherentFrom (A ⊞ B) m → IsPseudoCoherentFrom A m := by
    intro A B h
    refine isPseudoCoherentFrom_of_local_restrict A m fun x => ?_
    obtain ⟨U, hxU, b, hb⟩ := exists_isZero_homology_gt_derivedRestrict (A ⊞ B) m h x
    refine ⟨U, hxU, (isPseudoCoherentFrom_of_biprod_of_isZero_homology_gt m b
      ((isPseudoCoherentFrom_derivedRestrictModules (A ⊞ B) m h U).ofIso
        ((derivedRestrictModules X U).mapBiprod A B)) fun j hj => ?_).1⟩
    exact isZero_homology_of_iso ((derivedRestrictModules X U).mapBiprod A B).symm (hb j hj)
  exact ⟨main A B h, main B A (h.ofIso (biprod.braiding A B))⟩

end AlgebraicGeometry.RingedSpace

end

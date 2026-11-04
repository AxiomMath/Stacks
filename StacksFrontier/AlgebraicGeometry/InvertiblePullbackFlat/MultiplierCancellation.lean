module

public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorSupport
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.PullbackMeromorphicFamily

/-!
# The common factor `s` cancels from the multipliers of Tag 0BD7

The multipliers `g` of [Stacks, Tag 0BD7] are compared through the products `φ^*(g) s`, so every
relation between two of them has to be read off a relation between the products. This file
records that `g ↦ φ^*(g) s` is multiplication by `s` on the pullback of `g`, and that for a
*regular* meromorphic section `s` it is therefore injective: two multipliers with the same
product have the same pullback.

## Main results

* `Stacks.Meromorphic.pullbackMeromorphicMul_val_app_eq`: `φ^*(g) s` is the section `φ^*(g)` of
  `𝒦_X` multiplied by `s`.
* `Stacks.Meromorphic.pullback_eq_of_pullbackMeromorphicMul_eq`: for a regular `s`, two
  multipliers whose products with `s` agree have equal pullbacks to `𝒦_X`.
* `Stacks.Meromorphic.restrict_pullbackMeromorphicMul_val_app` and
  `Stacks.Meromorphic.restrict_pullback_eq_of_restrict_pullbackMeromorphicMul_eq`: the same on an
  arbitrary open `W ≤ φ^{-1}(V)`, which is where the comparison of two multipliers happens — the
  section of `𝒪_X` relating two generating sections of `ℒ` lives only on the intersection of
  their generating loci, never on a whole preimage.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Meromorphic

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (L : X.Modules)
  (s : MeromorphicSection X.sheaf L)

/-- **The multiplier map of [Stacks, Tag 0BD7] is multiplication by `s`.** The section `φ^*(g) s`
over `φ^{-1}(V)` is the image of the pullback `φ^*(g)` under multiplication by `s`. -/
theorem pullbackMeromorphicMul_val_app_eq (V : Y.Opens)
    (a : (totalQuotientSheafAsModule Y).val.obj (op V)) :
    (pullbackMeromorphicMul f L s).val.app (op V) a
      = (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app
          (op (f ⁻¹ᵁ V : X.Opens))).hom
          (((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom a) := rfl

/-- **The common factor `s` cancels.** For a regular meromorphic section `s`, two meromorphic
multipliers on an open of the base whose products with `s` agree have the same pullback to
`𝒦_X` — the step that lets a relation between the multipliers be read off a relation between the
sections of `ℒ` they produce. -/
theorem pullback_eq_of_pullbackMeromorphicMul_eq
    (hs : IsRegularMeromorphicSection X.sheaf L s) (V : Y.Opens)
    {a b : (totalQuotientSheafAsModule Y).val.obj (op V)}
    (hab : (pullbackMeromorphicMul f L s).val.app (op V) a
      = (pullbackMeromorphicMul f L s).val.app (op V) b) :
    ((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom a
      = ((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom b :=
  SheafOfModules.app_injective_of_mono hs (op (f ⁻¹ᵁ V : X.Opens))
    ((pullbackMeromorphicMul_val_app_eq f L s V a).symm.trans
      (hab.trans (pullbackMeromorphicMul_val_app_eq f L s V b)))

/-- Multiplication by `s` commutes with restriction to an open `W` of the preimage: the
restriction of `φ^*(g) s` is the restriction of `φ^*(g)` multiplied by `s`. -/
theorem restrict_pullbackMeromorphicMul_val_app (V : Y.Opens) {W : X.Opens}
    (hW : W ≤ (f ⁻¹ᵁ V : X.Opens)) (a : (totalQuotientSheafAsModule Y).val.obj (op V)) :
    (meromorphicSectionSheaf X.sheaf L).val.restrictₛₗ (homOfLE hW).op
        ((pullbackMeromorphicMul f L s).val.app (op V) a)
      = (((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val.app (op W)).hom
          (((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
            X.totalQuotientSheaf).obj.map (homOfLE hW).op).hom
              (((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom a)) := by
  rw [pullbackMeromorphicMul_val_app_eq]
  exact (PresheafOfModules.naturality_apply
    ((meromorphicSectionSheaf X.sheaf L).unitHomEquiv.symm s).val (homOfLE hW).op
      (((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom a)).symm

/-- **The common factor `s` cancels on an arbitrary open of the preimage.** If the products
`φ^*(g) s` of two meromorphic multipliers with a regular `s` agree merely on an open `W` of
`φ^{-1}(V)`, then the pullbacks of the two multipliers to `𝒦_X` already agree on `W`. -/
theorem restrict_pullback_eq_of_restrict_pullbackMeromorphicMul_eq
    (hs : IsRegularMeromorphicSection X.sheaf L s) (V : Y.Opens) {W : X.Opens}
    (hW : W ≤ (f ⁻¹ᵁ V : X.Opens))
    {a b : (totalQuotientSheafAsModule Y).val.obj (op V)}
    (hab : (meromorphicSectionSheaf X.sheaf L).val.restrictₛₗ (homOfLE hW).op
        ((pullbackMeromorphicMul f L s).val.app (op V) a)
      = (meromorphicSectionSheaf X.sheaf L).val.restrictₛₗ (homOfLE hW).op
        ((pullbackMeromorphicMul f L s).val.app (op V) b)) :
    ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).obj.map (homOfLE hW).op).hom
          (((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom a)
      = ((Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
          X.totalQuotientSheaf).obj.map (homOfLE hW).op).hom
            (((Scheme.ringSheafPullbackOfFlat f).hom.app (op V)).hom b) :=
  SheafOfModules.app_injective_of_mono hs (op W)
    ((restrict_pullbackMeromorphicMul_val_app f L s V hW a).symm.trans
      (hab.trans (restrict_pullbackMeromorphicMul_val_app f L s V hW b)))

end Stacks.Meromorphic

end

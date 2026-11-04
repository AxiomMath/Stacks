module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.LocalizedFlat
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GN2 for the localization of a flat morphism at an object carrying a presentation

Let `f : (C, O_C) ⟶ (D, O_D)` be a flat morphism of ringed sites and let `V` be an object of `D`
over which the sheaf of `O_D`-modules `F` admits a finite global presentation. The morphism of
ringed sites `f_V : (C/u(V), O_{u(V)}) ⟶ (D/V, O_V)` that Stacks 04J0 localizes `f` to at `V` is
again flat, and `F|_V` is globally presented by assumption, so Stacks 0GN2 for a globally
presented source applies to it: the canonical map

`f_V^* Hom_{O_V}(F|_V, G|_V) ⟶ Hom_{O_{u(V)}}(f_V^*(F|_V), f_V^*(G|_V))`

of Stacks 0GMX is an isomorphism.

This is the invertibility input of the localization square — the hypothesis `h` of
`Stacks.SheafOfModules.InternalHom.isIso_over_of_square` — and it is the half of the reduction of
Stacks 0GN2 to the globally presented case that needs nothing about the canonical map's behaviour
under localization. The other half, that the restriction of the canonical map of `f` *is* the
canonical map of `f_V` read through the two localization comparisons, is a separate statement.

The two inputs are `Stacks.SheafOfModules.InternalHom`
`.isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation`, which is Stacks 0GN2 for a
globally presented source with the presentation assumed as the property Tag 03DL is phrased with,
and `AlgebraicGeometry.RingedSite.Hom.isFlatMapULift_localized_ringedToposHom_fSharpInverseImage`,
which is Stacks 04JB inherited by the localization of Stacks 04J0 at the spelling of flatness
that the former consumes — `O_C` flat as an `f⁻¹O_D`-module, with `f⁻¹` the inverse image of the
morphism of ringed topoi.

## Main results

* `Stacks.SheafOfModules.InternalHom.isIso_pullbackInternalHomMap_localized`: **Stacks 0GN2 for
  the localized morphism at an object over which the source is globally presented.**

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SheafOfModules.InternalHom

universe u

section Localized

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

/-- **Stacks 0GN2 for the localized morphism, at an object over which the source is globally
presented.** Let `f` be a flat morphism of ringed sites and `V` an object of the target site over
which `F` admits a finite global presentation. Then the canonical map of Stacks 0GMX for the
localized morphism `f_V` of Stacks 04J0 at `F|_V` and `G|_V` is an isomorphism.

Flatness of `f_V` is Stacks 04JB inherited by the localization,
`AlgebraicGeometry.RingedSite.Hom.isFlatMapULift_localized_ringedToposHom_fSharpInverseImage`;
with it the statement is `isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation` at `f_V`,
whose presentation hypothesis is exactly `hV`. -/
@[ega "0 6.7.6" "special case"]
theorem isIso_pullbackInternalHomMap_localized
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift
      f.ringedToposHom.fSharpInverseImage)
    (V : Y.C) (hV : _root_.SheafOfModules.HasFiniteGlobalPresentation (F.over V)) :
    IsIso (pullbackInternalHomMap (f.localized V) (F.over V) (G.over V)) :=
  isIso_pullbackInternalHomMap_of_hasFiniteGlobalPresentation (f.localized V) (F.over V)
    (G.over V) (f.isFlatMapULift_localized_ringedToposHom_fSharpInverseImage V hf) hV

end Localized

end Stacks.SheafOfModules.InternalHom

end

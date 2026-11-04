module

public import StacksFrontier.Homology.DerivedCategory.ModelComparison
public import StacksFrontier.Homology.Perfect.LargeUniverse
import all StacksFrontier.Homology.Perfect.Characterizing

@[expose] public noncomputable section

/-!
# Perfectness is compactness, at an arbitrary chosen derived category

`StacksDraft.Perfect.isPerfect_iff_isCompactObject_max` is [stacks 07LT] for modules in a universe
above the universe of the ring, but it sits inside a section of
`StacksFrontier/Homology/Perfect/LargeUniverse.lean` carrying
`attribute [local instance] HasDerivedCategory.standard`, as does
`StacksDraft.Perfect.isPerfect_iff_isCompactObject` in `Characterizing.lean`. Neither takes a
`[HasDerivedCategory]` binder, so both speak only about the standard model.

That specialisation is not harmless here, and the reason is a universe count. For `R : Type u` and
modules in `Type (max u v)`, write `m := max u v`. The standard model is
`HasDerivedCategory.{m + 1}`, so the morphisms of `D(R)` live in `Type (m + 1)`. But
`CategoryTheory.IsCompactObject.{w}` quantifies the index types of the direct sums it tests over
`Type w`, so it is *monotone increasing* in `w`, and
`CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` asks for
compactness at the category's **own** hom universe. At the standard model that is `m + 1`, while
`isPerfect_iff_isCompactObject_max` delivers compactness at `m` — one level below, hence strictly
weaker, hence unusable. A dévissage that wants to feed perfect objects to a homotopy-colimit
presentation therefore cannot even state its hypotheses against the specialised version.

This file removes the specialisation, additively and without touching either file, by transport.
Both halves of the equivalence transport along the comparison equivalence of two chosen models:
perfectness because the comparison identifies the two localization functors
(`StacksDraft.DerivedModel.modelCompQIso`) and is fully faithful, and compactness because
`CategoryTheory.isCompactObject_iff_isCompactObject_obj` is invariant under an additive equivalence
**at a fixed level `w`**, with the two categories allowed different hom universes. So the
conclusion is again compactness at `m`, now for an arbitrary chosen model — and at a model with
hom universe `m` (a locally small one, e.g. from
`StacksDraft.Perfect.nonempty_smallDerivedCategory`) the two levels coincide and the hypothesis of
the homotopy-colimit presentation is met.

## Main results

* `StacksDraft.Perfect.AnyModel.isPerfect_iff_isPerfect_modelEquiv` — perfectness is carried both
  ways by the comparison equivalence of two chosen models.
* `StacksDraft.Perfect.AnyModel.isPerfect_iff_isCompactObject_max` — [stacks 07LT] in a module
  universe above the ring, for an arbitrary chosen derived category.
* `StacksDraft.Perfect.AnyModel.nonempty_locallySmallDerivedCategory` — a chosen derived category
  of `R`-modules whose morphisms live in the module universe itself, which is the model at which
  the previous result's conclusion is at the category's own hom universe.

## References

* [The Stacks Project, Tag 07LT](https://stacks.math.columbia.edu/tag/07LT)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.DerivedModel

universe u v w z

namespace StacksDraft.Perfect.AnyModel

/-- Perfectness does not depend on the chosen derived category: the comparison equivalence carries
a bounded finite-projective representative both ways, since it identifies the two localization
functors and is fully faithful. -/
theorem isPerfect_iff_isPerfect_modelEquiv {R : Type u} [Ring R]
    (h₁ : HasDerivedCategory.{w} (ModuleCat.{v} R))
    (h₂ : HasDerivedCategory.{z} (ModuleCat.{v} R))
    (K : @DerivedCategory (ModuleCat.{v} R) _ _ h₁) :
    @IsPerfect R _ h₁ K ↔ @IsPerfect R _ h₂ ((modelEquiv h₁ h₂).functor.obj K) :=
  ⟨fun ⟨P, a, b, ha, hb, hf, hp, ⟨ei⟩⟩ => ⟨P, a, b, ha, hb, hf, hp,
      ⟨(modelEquiv h₁ h₂).functor.mapIso ei ≪≫ (modelCompQIso h₁ h₂).app P⟩⟩,
    fun ⟨P, a, b, ha, hb, hf, hp, ⟨ei⟩⟩ => ⟨P, a, b, ha, hb, hf, hp,
      ⟨(modelEquiv h₁ h₂).functor.preimageIso (ei ≪≫ ((modelCompQIso h₁ h₂).app P).symm)⟩⟩⟩

/-- **Stacks 07LT in a module universe above the ring, at an arbitrary chosen derived category.**
An object of `D(R)` is perfect if and only if it is compact, with the direct sums tested over index
types in the module universe. -/
theorem isPerfect_iff_isCompactObject_max {R : Type u} [CommRing R]
    [h : HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) :
    IsPerfect K ↔ IsCompactObject.{max u v} K := by
  let hstd := HasDerivedCategory.standard (ModuleCat.{max u v} R)
  let := modelEquiv_functor_additive h hstd
  rw [isPerfect_iff_isPerfect_modelEquiv h hstd K,
    isCompactObject_iff_isCompactObject_obj (modelEquiv h hstd).functor K]
  exact StacksDraft.Perfect.isPerfect_iff_isCompactObject_max.{u, v} _

/-- A chosen derived category of `R`-modules whose morphisms live in the module universe itself.

This is the model at which `isPerfect_iff_isCompactObject_max` becomes usable: its conclusion is
compactness at the module universe `max u v`, and here that *is* the hom universe of the category,
which is what
`CategoryTheory.Pretriangulated.exists_isHomotopyColimit_of_compactlyGenerated` asks for. At
`HasDerivedCategory.standard` the hom universe is `max u v + 1` instead and the hypothesis cannot
be met.

The underlying local smallness is `StacksDraft.Perfect`'s, reached here through `import all`
because it is `private` there; the exactness of countable products in `Mod_{max u v}(R)` that it
needs is `StacksDraft.Perfect.moduleCat_hasExactLimitsOfShape_discrete_nat`, whose statement
mentions no derived category and so is unaffected by the `HasDerivedCategory.standard` pin on the
section it sits in. -/
theorem nonempty_locallySmallDerivedCategory {R : Type u} [CommRing R] :
    Nonempty (HasDerivedCategory.{max u v} (ModuleCat.{max u v} R)) := by
  let _ : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max u v} R) :=
    StacksDraft.Perfect.moduleCat_hasExactLimitsOfShape_discrete_nat
  exact StacksDraft.Perfect.nonempty_smallDerivedCategory

end StacksDraft.Perfect.AnyModel

end

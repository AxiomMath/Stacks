module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechConeExact

/-!
# A surjection of modules induces a degreewise surjection of Čech cones

`Stacks.LocalCohomology.shortExact_map_cechConeFunctor` says that
`Stacks.LocalCohomology.cechConeFunctor` carries a short exact sequence of modules to a short
exact sequence of cochain complexes. What a tower of Čech cones needs instead is the statement for
a *bare* epimorphism: that `(cechConeFunctor f).map g` is surjective in every degree as soon as
`g` is surjective.

This file supplies it, by completing `g` to a short exact sequence with its categorical kernel and
reading off the surjectivity of the third map degreewise. The epimorphism form is what the
transition maps of a tower come as — there is no short exact sequence of towers in sight — and it
is the hypothesis shape that
`DerivedCategory.isDerivedLimitWithProjections_Q_limit_of_epi` consumes.

## Main results

* `Stacks.LocalCohomology.surjective_cechConeFunctor_map` — degreewise surjectivity of
  `(cechConeFunctor f).map g` for a surjective `g`.
* `Stacks.LocalCohomology.epi_cechConeFunctor_map` — the same as an epimorphism of complexes.

## References

* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- **A surjection of modules induces a surjection in each degree of the cone of the Čech
augmentation.** Completing `g` to the short exact sequence `0 ⟶ ker g ⟶ M ⟶ N ⟶ 0` and applying
`Stacks.LocalCohomology.shortExact_map_cechConeFunctor` gives a short exact sequence of complexes,
whose third map is degreewise surjective. -/
public theorem surjective_cechConeFunctor_map {M N : ModuleCat.{max u v} R} (g : M ⟶ N)
    (hg : Function.Surjective g.hom) (p : ℤ) :
    Function.Surjective (((cechConeFunctor.{v} f).map g).f p) := by
  have : Epi g := (ModuleCat.epi_iff_surjective g).2 hg
  have hS : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel g) }
  exact ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
    (shortExact_map_cechConeFunctor.{v} f _ hS) p).moduleCat_surjective_g

/-- **A surjection of modules induces an epimorphism of cones of the Čech augmentation.** -/
public theorem epi_cechConeFunctor_map {M N : ModuleCat.{max u v} R} (g : M ⟶ N)
    (hg : Function.Surjective g.hom) : Epi ((cechConeFunctor.{v} f).map g) :=
  HomologicalComplex.epi_of_epi_f _ fun p ↦
    (ModuleCat.epi_iff_surjective _).2 (surjective_cechConeFunctor_map f g hg p)

end Stacks.LocalCohomology

end

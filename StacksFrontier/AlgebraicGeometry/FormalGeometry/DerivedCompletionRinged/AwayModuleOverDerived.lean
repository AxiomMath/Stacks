module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechGlobalSliceAway
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction

/-!
# The base change `(𝒪_f)|_U ≅ (𝒪_U)_{f|_U}` in the derived categories

Let `(𝒞, 𝒪)` be a ringed site, `U` an object of `𝒞` and `f` a global section of `𝒪`. The
restriction to `𝒞/U` of `𝒪_f` placed in degree zero is `(𝒪_U)_{f|_U}` placed in degree zero.
Consequently `f|_U` lies in the vanishing locus of [Stacks, Tag 0998] of `K|_U` if and only if
the derived internal Hom over `𝒪_U` out of the restriction of `𝒪_f` into `K|_U` vanishes.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedAwayModuleOverIso`: the isomorphism
  `(𝒪_f[0])|_U ≅ (𝒪_U)_{f|_U}[0]` in the derived category of `𝒪_U`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor`:
  `f|_U` lies in the vanishing locus of `K|_U` if and only if
  `R𝑆heafHom_{𝒪_U}((𝒪_f)|_U, K|_U) = 0`.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The restriction to `𝒞/U` of `𝒪_f` placed in degree zero is isomorphic to `(𝒪_U)_{f|_U}`
placed in degree zero. -/
def derivedAwayModuleOverIso :
    (SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        U).mapDerivedCategory.obj (derivedAwayModule X h) ≅
      derivedAwayModule (X.over U) (globalSectionOver X U h) :=
  ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      U).mapDerivedCategorySingleFunctor 0).app (awayModule X h) ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))) 0).mapIso
        (awayModuleOverIso X U h)

/-- The restricted section `f|_U` lies in the vanishing locus of `K|_U` over `𝒞/U` if and only
if the derived internal Hom over `𝒪_U` out of the restriction of `𝒪_f` into `K|_U` vanishes. -/
theorem memVanishingIdeal_over_iff_isZero_derivedSheafHom_overFunctor
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    MemVanishingIdeal (X.over U)
        ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          U).mapDerivedCategory.obj K)
        (globalSectionOver X U h) ↔
      IsZero (((derivedSheafHomBifunctor (X.over U)).obj
        (op ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          U).mapDerivedCategory.obj (derivedAwayModule X h)))).obj
            ((SheafOfModules.overFunctor.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
              U).mapDerivedCategory.obj K)) :=
  (isZero_derivedSheafHom_iff_of_iso (X.over U) _ (derivedAwayModuleOverIso X U h)).symm

end AlgebraicGeometry.RingedSite

end

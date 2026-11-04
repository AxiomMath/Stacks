module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CechSliceRestriction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.CompletionIdempotent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ReflectorCompletion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech completion functor commutes with restriction to a localized ringed site

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let `U` be an
object of `𝒞`. The completion functor of [Stacks, Tag 099B] attached to that family is
`K ↦ K^∧ = R𝑆heafHom_𝒪(Č(f), K)`, and this file proves

`K^∧|_U ≅ (K|_U)^∧` naturally in `K`,

the completion on the right being the one of the restricted family `f|_U` on the localized
ringed site. This is the mathematical content of the invertibility assertion of
[Stacks, Tag 0A0F].

## Main definitions

* `AlgebraicGeometry.RingedSite.extendedAlternatingCechDerivedRestrictIso`: `Č(f)|_U ≅ Č(f|_U)`
  in `D(𝒪_U)`.
* `AlgebraicGeometry.RingedSite.completionFunctorRestrictIso`: **the natural isomorphism
  `K^∧|_U ≅ (K|_U)^∧`.**

## Implementation notes

Two inputs:

* restriction to a slice commutes with the derived internal Hom bifunctor of [Stacks, Tag 0996].
  This is [Stacks, Tag 08JB], `AlgebraicGeometry.RingedSite.derivedHomRestriction` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedHomRestriction.lean`, an
  isomorphism natural in both variables; naturality in the covariant variable is what makes the
  comparison here natural in `K`, and functoriality in the contravariant variable is what lets
  the first argument be replaced.
* `Č(f)|_U ≅ Č(f|_U)`. At the level of complexes this is
  `AlgebraicGeometry.RingedSite.extendedAlternatingCechOverIso` of `CechSliceRestriction.lean`;
  restriction of modules to a slice is exact, so
  `CategoryTheory.Functor.mapDerivedCategoryFactors` carries the class of a complex to the class
  of its degreewise restriction and the identification descends to `D(𝒪_U)`.

The map `a` of [Stacks, Tag 0A0F] is built from the *reflector* of [Stacks, Tag 099F],
`AlgebraicGeometry.RingedSite.derivedCompletion`, which is `Functor.leftAdjoint` of the inclusion
of the derived-complete objects — an arbitrary choice of left adjoint, not the Čech functor used
here. The two are joined by an isomorphism
`derivedCompletion X (idealOfGlobalSections X f) ≅ completionFunctor X f` carrying one unit to
the other — the uniqueness of a left adjoint up to a unit-compatible isomorphism, applied to the
universal property which
`AlgebraicGeometry.RingedSite.bijective_precomp_completionUnit_idealOfGlobalSections` gives;
that is `exists_iso_derivedCompletion_completionFunctor` below. Together with
`AlgebraicGeometry.RingedSite.completionUnit_comp_completionFunctorRestrictIso_inv` of
`CompletionUnitRestriction.lean`, it feeds the criterion
`AlgebraicGeometry.RingedSite.isIso_derivedCompletionRestrictComparison_of_unit_comp` of
`LocalizationCompletion.lean`, which gives the invertibility of `a`.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0A0F](https://stacks.math.columbia.edu/tag/0A0F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] (U : X.C)
  [HasWeakSheafify (X.over U).J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **`Č(f)|_U ≅ Č(f|_U)` in the derived category of the localized ringed site.** Restriction of
sheaves of modules to a slice is exact, so the functor it induces on derived categories carries
the class of a complex to the class of its degreewise restriction
(`CategoryTheory.Functor.mapDerivedCategoryFactors`); the degreewise restriction of the extended
alternating Čech complex of `f` is the extended alternating Čech complex of `f|_U` by
`AlgebraicGeometry.RingedSite.extendedAlternatingCechOverIso`. -/
def extendedAlternatingCechDerivedRestrictIso :
    (SheafOfModules.overFunctor.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (extendedAlternatingCech X f)) ≅
      DerivedCategory.Q.obj (extendedAlternatingCech (X.over U)
        (fun i ↦ globalSectionOver X U (f i))) :=
  (SheafOfModules.overFunctor.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategoryFactors.app
      (extendedAlternatingCech X f) ≪≫
    DerivedCategory.Q.mapIso (extendedAlternatingCechOverIso X U f)

/-- Restriction of the completion `K^∧ = R𝑆heafHom(Č(f), K)` to the slice, identified by
[Stacks, Tag 08JB] with the derived internal Hom on the slice out of the *restriction* of `Č(f)`:
the first argument has not yet been identified with `Č(f|_U)`. Natural in `K` by the naturality
of [Stacks, Tag 08JB] in its covariant variable. -/
def completionFunctorRestrictAux :
    completionFunctor X f ⋙
        (SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ⋙
        (derivedSheafHomBifunctor (X.over U)).obj
          (op ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj
            (DerivedCategory.Q.obj (extendedAlternatingCech X f)))) :=
  NatIso.ofComponents
    (fun K ↦ (derivedHomRestriction X U).iso
      (DerivedCategory.Q.obj (extendedAlternatingCech X f)) K)
    fun {_K _L} g ↦ (derivedHomRestriction X U).natural_right g

/-- **The completion functor of [Stacks, Tag 099B] commutes with restriction to a localized
ringed site:** `K^∧|_U ≅ (K|_U)^∧`, naturally in `K`, where the completion on the right is the
one of the restricted family `f|_U` on `(𝒞/U, 𝒪_U)`.

Both completions are derived internal Hom out of an extended alternating Čech complex, so the
statement is [Stacks, Tag 08JB] — restriction commutes with derived internal Hom — followed by
the replacement of the restricted Čech complex by the Čech complex of the restricted family,
which is `extendedAlternatingCechDerivedRestrictIso`. -/
def completionFunctorRestrictIso :
    completionFunctor X f ⋙
        (SheafOfModules.overFunctor.{u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory ⋙
        completionFunctor (X.over U) (fun i ↦ globalSectionOver X U (f i)) :=
  completionFunctorRestrictAux X U f ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.overFunctor.{u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory
      ((derivedSheafHomBifunctor (X.over U)).mapIso
        (extendedAlternatingCechDerivedRestrictIso X U f).symm.op)

/-- **The reflector of [Stacks, Tag 099F] at `ℐ = (f_1, …, f_r)` is the Čech completion
functor**, by an isomorphism carrying one completion map to the other: for every `K` there is
`K^∧ ≅ R𝑆heafHom_𝒪(Č(f), K)` under which the unit of the reflector adjunction is the completion
map of `Completion.lean`.

The reflector itself is `CategoryTheory.Functor.leftAdjoint` of the inclusion of the
derived-complete objects, an arbitrary choice of left adjoint carrying no formula; what pins it
down is the universal property, and the Čech functor has that universal property by
`AlgebraicGeometry.RingedSite.bijective_precomp_completionUnit_idealOfGlobalSections`, which is
the formula [Stacks, Tag 099B] gives alongside its existence statement. So this is
`AlgebraicGeometry.RingedSite.exists_iso_derivedCompletion_of_bijective_precomp` applied to the
completion map, with its target derived complete by clause 1 of that tag,
`AlgebraicGeometry.RingedSite.isDerivedComplete_completionFunctor`. -/
theorem exists_iso_derivedCompletion_completionFunctor
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    letI := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
    ∃ θ : (derivedCompletion X (idealOfGlobalSections X f)).obj K ≅
        (completionFunctor X f).obj K,
      (derivedCompletionUnit X (idealOfGlobalSections X f)).app K ≫ θ.hom =
        (completionUnit X f).app K :=
  let := isRightAdjoint_ι_isDerivedComplete_idealOfGlobalSections X f
  exists_iso_derivedCompletion_of_bijective_precomp X (idealOfGlobalSections X f)
    (isDerivedComplete_completionFunctor X f K) ((completionUnit X f).app K)
    fun _M hM ↦ bijective_precomp_completionUnit_idealOfGlobalSections X f K hM

/-- The component at `K` of `completionFunctorRestrictIso` is the restriction isomorphism of
`derivedHomRestriction` for `R𝑆heafHom_𝒪(Č(f), K)`, followed by the map induced on the first
argument of `derivedSheafHomBifunctor` by the inverse of
`extendedAlternatingCechDerivedRestrictIso`. -/
theorem completionFunctorRestrictIso_hom_app
    (K : DerivedCategory (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    (completionFunctorRestrictIso X U f).hom.app K =
      ((derivedHomRestriction X U).iso
          (DerivedCategory.Q.obj (extendedAlternatingCech X f)) K).hom ≫
        ((derivedSheafHomBifunctor (X.over U)).map
            (extendedAlternatingCechDerivedRestrictIso X U f).symm.op.hom).app
          ((SheafOfModules.overFunctor.{u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U).mapDerivedCategory.obj K) :=
  rfl

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationAtGlobalSection
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.KFlatIntoKInjectiveIsKInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksCore.Tactic.StacksAttribute

/-!
# `𝒪_f` is K-flat

Let `(𝒞, 𝒪)` be a ringed site and let `f` be a global section of `𝒪`. The sheaf `𝒪_f`,
placed in degree zero, is a K-flat complex of `𝒪`-modules. With [Stacks, Tag 0A96] this makes
the internal Hom complex `SheafHom•_𝒪(𝒪_f, I)` K-injective whenever `I` is.

This is the step the source's proof of [Stacks, Tag 0996(3)] cites: it reads
`R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_g, K))` as an *iterated* derived internal Hom, which needs
`SheafHom•_𝒪(𝒪_g, 𝓘•)` to be K-injective as a complex of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.isKFlat_awayComplex`: `𝒪_f` in degree zero is K-flat.
* `AlgebraicGeometry.RingedSite.isFlat_awayModule`: `𝒪_f` is a flat sheaf of `𝒪`-modules.
* `AlgebraicGeometry.RingedSite.isKFlat_awayModule`: the same K-flatness, over a site on which
  only weak sheafification of rings is assumed.
* `AlgebraicGeometry.RingedSite.derivedTensorSingleAwayModuleIso`: derived tensoring with
  `𝒪_f[0]` is the termwise ordinary tensor product.

## Implementation notes

Nothing is assumed of `f`.

K-flatness is `Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat`, the base case of
[Stacks, Tag 06YQ] for a flat module in a single degree; its flatness hypothesis is
`AlgebraicGeometry.RingedSite.isFlatMap_toAwaySheaf`, since flatness of the map `𝒪 ⟶ 𝒪_f` is by
definition flatness of `𝒪_f` as an `𝒪`-module, which is `awayModule`.

K-flatness is what [Stacks, Tag 0A96] consumes: internal Hom out of a K-flat complex into a
K-injective complex is K-injective. That consequence is drawn in
`AwayInternalHomMulDerived.lean`, where it is stated at the `awayComplex` spelling the clause
uses, as `AlgebraicGeometry.RingedSite.isKInjective_sheafHomComplex_awayComplex`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSite

section AwayComplex

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]
  (f : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

omit [HasSheafify X.J AddCommGrpCat.{u}] in
/-- **`𝒪_f`, placed in degree zero, is a K-flat complex of `𝒪`-modules.** Flatness of the
localization map is flatness of `𝒪_f` as an `𝒪`-module, and a flat module in a single degree is
K-flat. -/
theorem isKFlat_awayComplex :
    Stacks.SheafOfModules.IsKFlat X.O
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (awayModule X f)) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.O (awayModule X f)
    (isFlatMap_toAwaySheaf f) 0

end AwayComplex

section AwayModule

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **`𝒪_f` is a flat sheaf of `𝒪`-modules.** This is flatness of the map `𝒪 ⟶ 𝒪_f`
(`AlgebraicGeometry.RingedSite.isFlatMap_toAwaySheaf`), which is by definition flatness of the
target as a module over the source. -/
theorem isFlat_awayModule :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (awayModule X h) :=
  isFlatMap_toAwaySheaf h

/-- **`𝒪_f` placed in degree zero is a K-flat complex of `𝒪`-modules.** By the base case of
[Stacks, Tag 06YQ] it suffices that `𝒪_f` be flat, which is `isFlat_awayModule`. -/
theorem isKFlat_awayModule :
    Stacks.SheafOfModules.IsKFlat X.O
      ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          (awayModule X h)) :=
  Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.O (awayModule X h)
    (isFlat_awayModule X h) 0

section DerivedTensor

attribute [local instance] HasDerivedCategory.standard

/-- **Derived tensoring with `𝒪_f[0]` is the termwise ordinary tensor product.** For every
cochain complex `K` of `𝒪`-modules,

`K ⊗^𝐋_𝒪 𝒪_f[0] ≅ (p ↦ K^p ⊗_𝒪 𝒪_f)`

in `D(𝒪)`. This is the bridge between the *ordinary* base-change identifications
`AlgebraicGeometry.RingedSite.awayTensorIsoBaseChangeAwayModule` and
`Stacks.Sheaves.CechFlatNeighbourhood.awayLocalizationBaseChangeIso` and the *derived* tensor
product that the currying isomorphism of [Stacks, Tag 08J9] produces.

It is the one-sided K-flat comparison of [Stacks, Tag 06YU] —
`Stacks.SheafOfModules.DerivedTensorProduct.comparisonRight`, which asks K-flatness of its
right factor only — read at the right factor `𝒪_f[0]`, where `isKFlat_awayModule` discharges
that hypothesis; followed by
`CochainComplex.KFlatBifunctor.totalSingleIso`, which collapses the total complex of a second
factor concentrated in one degree to the termwise complex. -/
def derivedTensorSingleAwayModuleIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
              (awayModule X h))) ≅
      DerivedCategory.Q.obj
        (CochainComplex.KFlatBifunctor.rowComplex
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) K (awayModule X h)) :=
  (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight K _
      (isKFlat_awayModule X h) ≪≫
    DerivedCategory.Q.mapIso (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) K (awayModule X h))

end DerivedTensor

end AwayModule

end AlgebraicGeometry.RingedSite

end

module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomSchemeIsoModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkFormula

/-!
# The Ext sheaves on an affine open are the affine Ext sheaves of the affine models

Let `X` be a scheme, `F` a sheaf of `𝒪_X`-modules, `K` an object of `D(𝒪_X)` and `U ⊆ X` an
affine open. Suppose given a module `M` over `A = Γ(X, U)` and an object `ω` of `D(A)` whose
images under `~` model `F|_U` and `K|_U` across the isomorphism `hU.isoSpec : U ≅ Spec A`. Then
the Ext sheaf `𝓔xt^{-i}_{𝒪_X}(F, K)` restricted to `U` is the `U`-pullback of
`AlgebraicGeometry.AffineExt.cohomologySheaf A M̃ ω̃ (-i)`, the affine Ext cohomology sheaf of the
models on `Spec A`.

This is **pure transport**: nothing is assumed about `X`, `F` or `K` beyond the two modelling
hypotheses. No Noetherian, coherence or dualizing hypothesis enters, and none is needed — the
statement only moves one and the same derived internal Hom across two restrictions.

The transport is assembled from four ingredients, with no new mathematics:

* restriction along a morphism of schemes is exact, so it commutes with the cohomology functors
  of the derived category (`DerivedCategoryB.mapDerivedCategoryHomologyIso`);
* the derived internal Hom commutes with restriction to an open subscheme,
  [Stacks, Tag 08DL] in the form
  `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`;
* the derived internal Hom commutes with restriction along an isomorphism of schemes,
  `Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso`, used here at `hU.isoSpec.hom`;
* an exact functor commutes with placing a module in degree zero,
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.

## Main results

* `Stacks.Duality.nonempty_restrict_extSheafOf_iso`: **the restriction of the Ext sheaf to an
  affine open is the pullback of the affine Ext cohomology sheaf of the affine models.**

## Implementation notes

The whole chain is run on the open subscheme `U.toScheme`, never on `Spec Γ(X, U)`: the affine
side is brought *up* to `U` by `derivedSheafHomSchemeIsoIso` at `hU.isoSpec.hom`, rather than the
`U` side being pushed *down* along `hU.isoSpec.inv`. This is what makes the conclusion land on the
nose in the `Scheme.Modules.restrictFunctor hU.isoSpec.hom` form, and it is why no cancellation of
a double restriction (`Scheme.Modules.restrictFunctorCompInvIso`) and no occurrence of
`CategoryTheory.inv hU.isoSpec.hom` appear anywhere below.

No `@[stacks]` attribute is attached: this is infrastructure for reading the Ext sheaves on an
affine chart, not a delivery of a tag. [Stacks, Tag 08DL] is registered on
`AlgebraicGeometry.RingedSite.derivedHom_restriction_exists`, and the Ext sheaves themselves on
`Stacks.SheafOfModules.derivedSheafExt` under [Stacks, Tag 0BQP].

The exactness of restriction to a slice site is named rather than synthesized: the two
`PreservesFiniteLimits`/`PreservesFiniteColimits` instance arguments of
`derivedSheafHomSchemeRestrictionIso` come from
`Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits` and its colimit
companion, theorems rather than instances in this development. The same holds of the exactness of
`~`, supplied by the local attributes below as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedTilde/AffineExt/Basic.lean`.

The derived model is pinned with priority `10000`, as the import closure reaches
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory` instances
are global; see the note in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPseudoCoherentHomQuasicoherent`.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Duality

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHom`,
--   `Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso`.
attribute [local instance 10000] HasDerivedCategory.standard
  AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

/-- **The Ext sheaves on an affine open are the affine Ext sheaves of the affine models.** Let
`F` be a sheaf of `𝒪_X`-modules and `K` an object of `D(𝒪_X)`, let `U ⊆ X` be an affine open, and
let `M` and `ω` be a module and an object of the derived category over `A = Γ(X, U)` such that
`M̃` models `F|_U` and `ω̃` models `K|_U` across `hU.isoSpec : U ≅ Spec A`. Then the restriction of
`𝓔xt^{-i}_{𝒪_X}(F, K)` to `U` is the pullback along `hU.isoSpec.hom` of the affine Ext cohomology
sheaf `AlgebraicGeometry.AffineExt.cohomologySheaf A M̃ ω̃ (-i)`.

Both sides are a cohomology sheaf of a derived internal Hom, so the proof is a chain of
transports. Restriction along `U.ι` is exact, so it passes the cohomology functor; the derived
internal Hom it meets is carried into `U` by [Stacks, Tag 08DL]; the two arguments are rewritten
by the modelling hypotheses, which is where `mapDerivedCategorySingleFunctor` turns the restricted
single complex on `F` into the single complex on the restriction of `F`; and the resulting derived
internal Hom on `U` is identified with the restriction along `hU.isoSpec.hom` of the derived
internal Hom on `Spec A`, past which the cohomology functor travels again. -/
theorem nonempty_restrict_extSheafOf_iso {X : Scheme.{u}} (F : X.Modules)
    (K : DerivedCategory X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (M : ModuleCat.{u} Γ(X, U)) (ω : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (hM : Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj F ≅
       (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj M))
    (hω : Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
       (tilde.functor Γ(X, U) ⋙
         Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω))
    (i : ℤ) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj (Stacks.Duality.extSheafOf F K i) ≅
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom).obj
        (AlgebraicGeometry.AffineExt.cohomologySheaf Γ(X, U)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M) ω (-i))) := by
  obtain ⟨eM⟩ := hM
  obtain ⟨eω⟩ := hω
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := X.ringCatSheaf) U
  let _ := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := X.ringCatSheaf) U
  -- The object of `D(𝒪_U)` modelling `K|_U` after the affine model is inserted.
  have bω : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj ω) :=
    eω ≪≫ (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (tilde.functor Γ(X, U)) (Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app ω
  -- The same for the single complex on `F`, where the affine model is a module.
  have aF : (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M)) :=
    ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategorySingleFunctor 0).app F ≪≫
      (DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso eM ≪≫
      (((Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategorySingleFunctor
        0).app ((tilde.functor Γ(X, U)).obj M)).symm ≪≫
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.mapIso
        (((tilde.functor Γ(X, U)).mapDerivedCategorySingleFunctor 0).app M).symm
  refine ⟨?_⟩
  refine ((DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor U.ι) (-i)).app _).symm ≪≫ ?_
  refine (DerivedCategory.homologyFunctor
    (Stacks.SheafOfModules.StructureSheafModules U.toScheme.sheaf) (-i)).mapIso ?_ ≪≫
    (DerivedCategoryB.mapDerivedCategoryHomologyIso
      (Scheme.Modules.restrictFunctor hU.isoSpec.hom) (-i)).app _
  refine Stacks.SheafOfModules.derivedSheafHomSchemeRestrictionIso U
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) K ≪≫ ?_ ≪≫
    (Stacks.SheafOfModules.derivedSheafHomSchemeIsoIso hU.isoSpec.hom
      ((tilde.functor Γ(X, U)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj M))
      ((tilde.functor Γ(X, U)).mapDerivedCategory.obj ω)).symm
  exact ((Stacks.SheafOfModules.derivedSheafHom U.toScheme.sheaf).mapIso aF.symm.op).app _ ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom U.toScheme.sheaf).obj (op _)).mapIso bω

end Stacks.Duality

end

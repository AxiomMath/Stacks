module

public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseBigCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusSemilinearAction
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The canonical map of [Stacks, Tag 07N5]

In Situation [Stacks, Tag 07N2] let `(E, F_E)` be an `F`-crystal on `X/S` relative to `σ`,
[Stacks, Tag 07N3].  [Stacks, Tag 07N5] asserts that the canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

of `D(A)`, `A = Γ(S, 𝒪_S)`, becomes an isomorphism after inverting `p`.  **This file constructs
that map**, as `frobeniusMap07N5Canonical`, the first term of
`Crystalline.GlobalCrystallineSituation.SmallSite.FrobeniusMap07N5` the library has; and it proves
that the map factors through the third arrow of the source's proof,
`frobeniusFactorsThroughCohomologyMap07N5_canonical`, which was the one hypothesis of
`...SmallSite.statement07N5_of_baseChangeArrows07N5Isogeny` that could not be discharged while the
map was an arbitrary parameter.

So [Stacks, Tag 07N5] is no longer a statement about a carried map: at the canonical map it is
*equivalent* to the isogeny of the first two arrows of its own proof
(`statement07N5_canonical_iff_baseChangeArrows07N5Isogeny`), which is the source's (07QC) and
(07N6) and rests on [Stacks, Tag 07MU] and [Stacks, Tag 07MY].

## How the map is built, and what it does not need

The underived input is the comparison on global sections along change of divided power base, on
the **big** crystalline site, where change of base is an endofunctor and preserves the structure
sheaf on the nose (`...changeBase_op_comp_crisRing`), so that no open immersion is involved and
the absolute Frobenius of `X` is admissible:

`Γ_{S'} ⟶ u^* ⋙ Γ_S ⋙ res`, that is `changeBaseBigBaseGlobalSectionsTrans`,

at the module universe of the cohomology.  Four steps turn it into a transformation of functors on
bounded below derived categories and a fifth into the shape of the tag, exactly as
`SmallSite/BaseChangeMapConstruction.lean` does for the base change map (07MT) of
[Stacks, Tag 07MS] on the small sites:

1. `Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans` derives it, giving
   `RΓ_{S'} ⟶ R(u^* ⋙ (Γ_S ⋙ res))`.
2. `Stacks.DerivedIndexing.rightDerivedPlusCompTrans`, the canonical map of [Stacks, Tag 05T2],
   splits the right hand side as `R u^* ⋙ R(Γ_S ⋙ res)`.
3. `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic` splits `R(Γ_S ⋙ res)` as
   `RΓ_S ⋙ R(res)`; its acyclicity hypothesis is free, `res` being exact.
4. `CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus` replaces `R(res)` by
   `res` itself, so that the target is a restriction of scalars of an object of `D⁺(A)`.
5. `...SmallSite.frobeniusDerivedBaseChangeAdjunction` ([Stacks, Tag 0GMT]) transposes the
   resulting `σ`-semilinear map `RΓ ⟶ σ_* RΓ` into a map out of `RΓ ⊗^L_{A, σ} A`.

Step 2 is **only a map, and that is the whole point.**  Its being an isomorphism is the instance
of [Stacks, Tag 015M] for the pair `((F_X)^*_cris, Γ(CRIS(X/S), -))`, equivalently
`Γ(CRIS(X/S), -)`-acyclicity of `(F_X)^*_cris I` for `I` an injective sheaf of
`𝒪_{X/S}`-modules on `CRIS(X/S)`.  That acyclicity is **not proved here and not needed here**: the
canonical comparison of [Stacks, Tag 05T2] runs from `R(G ∘ F)` to `RG ∘ RF`, which is the
direction in which the construction travels.  The record in
`SmallSite/FrobeniusSemilinearAction.lean` and `Crystalline/FrobeniusBigGlobalSections.lean` that
arrow 1 is "a Grothendieck-spectral-sequence question about whether `(F_X)_cris^*` carries
injectives to `Γ(CRIS(X/S), -)`-acyclics" named a sufficient condition for the comparison to be
invertible, not for the arrow to exist.  At abelian coefficients that condition does hold, and
unconditionally: `Crystalline/ChangeBaseAbelianInjectives.lean`.

What the passage from the derived transformation to a map of single objects *does* need is
exactness of `u^*`, through `CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso` computing
`R u^*(M[0])` as `(u^* M)[0]`; that is
`...changeBaseBigModulePullback_preservesFiniteLimits` and
`...changeBaseBigModulePullback_preservesFiniteColimits`, [Stacks, Tag 04BD](2), with no
hypothesis on `g`.

## From the big site to the small one

The tag's objects are the cohomology of `Cris(X/S)`, while an `F`-crystal carries its module on
`CRIS(X/S)` and the construction above runs there.  The passage is
`...SmallSite.derivedRestrictModuleGlobalSectionsULiftIso`,
`RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i^{-1}N)`, proved in
`SmallSite/ModuleRestrictionCohomologyULift.lean` on top of
`...SmallSite.rightAcyclic_moduleRestrictι_obj`; it is applied at `N = E` and at
`N = (F_X)^*_cris E`, and nothing else about the inclusion is used.

## Faithfulness

The map is canonical: no parameter is carried and no choice is made.  Its underived input is
pinned pointwise by `sectionsMap_frobeniusBigSections_val`, which says that composing the
comparison with a Frobenius structure map `φ` sends a global section `x` to the family
`A ↦ φ_A(x(u(A)))` — verbatim `Crystalline.FCrystal.sectionsFrobenius_val`, the underived
`F_E ∘ (F_X)^*_cris` of `Crystalline/FrobeniusBigGlobalSections.lean`.  The `σ`-semilinearity is
the semilinearity of that comparison over `...SmallSite.baseChangeRingHom Spec(σ)`, which **is**
`σ` by `...SmallSite.baseChangeRingHom_specSigma`, and `frobeniusSigmaSemilinearAction` is the map
read as a term of `...SmallSite.SigmaSemilinearAction07N5`, the type that file proves is exactly
arrow 1.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedChangeBaseBigGlobalSectionsTrans` — steps 1-4 for a general change of divided power
  base: `RΓ_{S'} ⟶ R u^* ⋙ RΓ_S ⋙ res`.
* `derivedChangeBaseBigGlobalSectionsMap` — the same at a single sheaf of modules,
  `RΓ(CRIS(Y/S'), N) ⟶ res_* RΓ(CRIS(X/S), u^* N)`.
* `frobeniusBigModulePullback` — `(F_X)^*_cris` at the module universe of the cohomology.
* `derivedFrobeniusRestrictGlobalSectionsMap` — the comparison for the Frobenius, read on the
  small site: `RΓ(Cris(X/S), i^{-1}N) ⟶ σ_* RΓ(Cris(X/S), i^{-1}(F_X)^*_cris N)`.
* `frobeniusSemilinearBaseChangeArrow` — **arrow 1 of [Stacks, Tag 07N5]**, that map at the
  module of an `F`-crystal and in the unbounded derived category.
* `frobeniusBaseChangeArrows07N5` — **a term of `...SmallSite.BaseChangeArrows07N5`**, the
  composite of the first two arrows: arrow 1 transposed across [Stacks, Tag 0GMT].
* `frobeniusSigmaSemilinearAction` — **a term of `...SmallSite.SigmaSemilinearAction07N5`**, the
  `σ`-semilinear Frobenius action on `RΓ(Cris(X/S), E)`.
* `frobeniusMap07N5Canonical` — **the canonical map of [Stacks, Tag 07N5]**, a term of
  `...SmallSite.FrobeniusMap07N5`: `frobeniusBaseChangeArrows07N5` followed by the third arrow
  `...SmallSite.frobeniusCohomologyMap`.

## Main results

* `sectionsMap_frobeniusBigSections_val` — the underived input of arrow 1, pointwise.
* `frobeniusMap07N5Canonical_eq_ofSemilinearAction` — the canonical map is the one induced by
  `frobeniusSigmaSemilinearAction`, so the two readings of arrow 1 agree.
* `frobeniusFactorsThroughCohomologyMap07N5_canonical` — **the canonical map factors through the
  third arrow of the source's proof**, by construction.
* `statement07N5_canonical_iff_baseChangeArrows07N5Isogeny` — **[Stacks, Tag 07N5] at the
  canonical map is equivalent to the isogeny of the first two arrows of its proof**, given the
  rank delimiter `...SmallSite.BoundedCommonLocalRanks07N5` inherited from [Stacks, Tag 07N4].

## What is and is not proved

Everything here is unconditional in the situation: no affineness, no properness, no smoothness,
no hypothesis on `p` beyond those in a `GlobalCrystallineSituation`, and no hypothesis on the
`F`-crystal — not even nondegeneracy, which enters only through the third arrow's isogeny.

**No `@[stacks 07N5]` attribute is placed in this file.**  What is constructed here is the tag's
map; its conclusion — that the map becomes an isomorphism after inverting `p` — is
`...SmallSite.Statement07N5` at this map, and by the equivalence above it is exactly
`...SmallSite.BaseChangeArrows07N5Isogeny`, the source's (07QC) and (07N6).  That conclusion is
reached in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Frobenius07N5Theorem.lean`, where the tag is
registered on `...SmallSite.statement07N5`, by splitting the two arrows over `X^{(1)}` and
reading each against the source's own citation for it: arrow 1 is an isomorphism by
`...SmallSite.isIso_baseChangeArrow07QC` and arrow 2 an isogeny by
`...SmallSite.becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6`.  This file contributes the
map and its factorization, not those two arrow statements.  The rank delimiter is inherited from
`...SmallSite.becomesIsoAfterInvertingPrime_frobeniusCohomologyMap` and is introduced nowhere in
this file.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA wP

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section ChangeBase

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **Steps 1-4 of the construction**, for a general change of divided power base and at the
module universe of the cohomology: the natural transformation

`RΓ(CRIS(Y/S'), -) ⟶ R u^* ⋙ RΓ(CRIS(X/S), -) ⋙ res_*`

of functors `D⁺(Mod_{𝒪_{Y/S'}}) ⥤ D⁺(Mod_{A'})`, where `u^*` is
`...changeBaseBigModulePullback` and `res_*` is restriction of scalars along
`...SmallSite.baseChangeRingHom f`.

It is a *map* and not an isomorphism: step 2, the canonical transformation of
[Stacks, Tag 05T2], is a map, and assuming it invertible would be assuming the instance of
[Stacks, Tag 015M] that the module documentation explains is neither available nor needed.  The
two isomorphisms used, steps 3 and 4, carry no hypothesis beyond exactness of restriction of
scalars.

Carrying no hypothesis on `g`, this is the big-site twin of
`...SmallSite.derivedBaseChangeGlobalSectionsTrans`, which exists only for `g` an open
immersion. -/
def derivedChangeBaseBigGlobalSectionsTrans (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber) :
    derivedBigModuleGlobalSectionsFunctor S' ⟶
      (changeBaseBigModulePullback S S' f g h).rightDerivedFunctorPlus ⋙
        derivedBigModuleGlobalSectionsFunctor S ⋙
          (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus :=
  Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
      (changeBaseBigBaseGlobalSectionsTrans f g h) ≫
    Stacks.DerivedIndexing.rightDerivedPlusCompTrans (changeBaseBigModulePullback S S' f g h)
      (bigBaseModuleGlobalSections S ⋙ ModuleCat.restrictScalars (baseChangeRingHom f)) ≫
    Functor.whiskerLeft (changeBaseBigModulePullback S S' f g h).rightDerivedFunctorPlus
      ((Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic (bigBaseModuleGlobalSections S)
            (ModuleCat.restrictScalars (baseChangeRingHom f))
            (fun _ _ => Functor.rightAcyclic_of_exact _ _)).hom ≫
        Functor.whiskerLeft (bigBaseModuleGlobalSections S).rightDerivedFunctorPlus
          (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
            (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f))).hom)

/-- **The comparison on derived global sections at a single sheaf of modules**,

`RΓ(CRIS(Y/S'), N) ⟶ res_* RΓ(CRIS(X/S), u^* N)`   in `D⁺(Mod_{A'})`.

A morphism into a restriction of scalars along `...SmallSite.baseChangeRingHom f` is exactly a map
semilinear over that ring map, so this is the derived form of
`...changeBaseBigBaseGlobalSectionsTrans`.

It is `derivedChangeBaseBigGlobalSectionsTrans` at `N[0]` followed by the computation
`R u^*(N[0]) ≅ (u^* N)[0]` of
`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso`, which is where exactness of the
pullback is used. -/
def derivedChangeBaseBigGlobalSectionsMap (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (N : BigModuleSheaf S') :
    (derivedBigModuleGlobalSections S').obj N ⟶
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus.obj
        ((derivedBigModuleGlobalSections S).obj
          ((changeBaseBigModulePullback S S' f g h).obj N)) :=
  (derivedChangeBaseBigGlobalSectionsTrans f g h).app
      ((DerivedCategory.Plus.singleFunctor (BigModuleSheaf S') 0).obj N) ≫
    (derivedBigModuleGlobalSectionsFunctor S ⋙
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus).map
      (Functor.rightDerivedFunctorPlusObjSingleIso (changeBaseBigModulePullback S S' f g h)
        N).hom

end ChangeBase

section Frobenius

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- **`σ_*` on bounded below derived categories of `A`-modules**, restriction of scalars along the
Frobenius lift `σ` of a Frobenius crystal situation [Stacks, Tag 07N2].

Restriction of scalars is exact, so no derived functor is involved.  It is the bounded below twin
of `...SmallSite.frobeniusSigmaRestrictScalars`, and the ring map is spelled
`...SmallSite.baseChangeRingHom Spec(σ)` for the same reason: that is the spelling the chapter's
`- ⊗^L_{A, σ} A` is built at, and `...SmallSite.baseChangeRingHom_specSigma` proves it is `σ`. -/
abbrev frobeniusSigmaRestrictScalarsPlus :
    DerivedCategory.Plus (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) :=
  (ModuleCat.restrictScalars.{u + 1}
    (baseChangeRingHom (S := T.global) (S' := T.global) T.specSigma)).mapDerivedCategoryPlus

/-- **`(F_X)^*_cris` at the module universe of the cohomology**: change of divided power base
along `Spec(σ)` and the absolute Frobenius of `X`, read on `...SmallSite.BigModuleSheaf`.

`Crystalline.FCrystalSituation.frobeniusModulePullback` is the same functor at the module universe
`u` of the chapter's crystals, and `bigModuleULift_comp_frobeniusBigModulePullback` says the two
agree through the universe lift. -/
def frobeniusBigModulePullback : BigModuleSheaf T.global ⥤ BigModuleSheaf T.global :=
  changeBaseBigModulePullback T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma

omit [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))] in
/-- **Raising the module universe commutes with the Frobenius pullback**, on the nose.  This is
what lets the Frobenius structure map `F_E` of an `F`-crystal, which lives at the module universe
`u`, be composed with the derived comparison, which lives at `u + 1`. -/
theorem bigModuleULift_comp_frobeniusBigModulePullback :
    T.frobeniusModulePullback ⋙ bigModuleULift T.global =
      bigModuleULift T.global ⋙ frobeniusBigModulePullback T := rfl

/-- **The derived comparison for the Frobenius on the big crystalline site**,

`RΓ(CRIS(X/S), N) ⟶ σ_* RΓ(CRIS(X/S), (F_X)^*_cris N)`   in `D⁺(Mod_A)`,

for `N` a sheaf of `𝒪_{X/S}`-modules at the module universe of the chapter's crystals.  It is
`derivedChangeBaseBigGlobalSectionsMap` along `Spec(σ)` and the absolute Frobenius of `X`, at the
universe lift of `N`; the target is read at the lift of `(F_X)^*_cris N` by
`bigModuleULift_comp_frobeniusBigModulePullback`. -/
def derivedFrobeniusBigGlobalSectionsMap
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    (derivedBigModuleGlobalSections T.global).obj ((bigModuleULift T.global).obj N) ⟶
      (frobeniusSigmaRestrictScalarsPlus T).obj
        ((derivedBigModuleGlobalSections T.global).obj
          ((bigModuleULift T.global).obj (T.frobeniusModulePullback.obj N))) :=
  derivedChangeBaseBigGlobalSectionsMap T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma ((bigModuleULift T.global).obj N)

/-- **The derived comparison for the Frobenius, read on the small crystalline site**,

`RΓ(Cris(X/S), i^{-1}N) ⟶ σ_* RΓ(Cris(X/S), i^{-1}(F_X)^*_cris N)`   in `D⁺(Mod_A)`.

It is `derivedFrobeniusBigGlobalSectionsMap` conjugated by
`...SmallSite.derivedRestrictModuleGlobalSectionsULiftIso`, the comparison
`RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i^{-1}N)` of [Stacks, Tag 07IM] at module coefficients, taken
once at `N` and once at `(F_X)^*_cris N`. -/
def derivedFrobeniusRestrictGlobalSectionsMap
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    moduleULiftDerivedGlobalSections T.global (restrictSheafOfModules N) ⟶
      (frobeniusSigmaRestrictScalarsPlus T).obj
        (moduleULiftDerivedGlobalSections T.global
          (restrictSheafOfModules (T.frobeniusModulePullback.obj N))) :=
  (derivedRestrictModuleGlobalSectionsULiftIso T.global N).inv ≫
    derivedFrobeniusBigGlobalSectionsMap T N ≫
      (frobeniusSigmaRestrictScalarsPlus T).map
        (derivedRestrictModuleGlobalSectionsULiftIso T.global
          (T.frobeniusModulePullback.obj N)).hom

/-- **The underived comparison at the Frobenius**, at the module universe of the cohomology: a
global section of `M` read at the images of the objects of `CRIS(X/S)` under the Frobenius
endofunctor, which makes it a global section of `(F_X)^*_cris M`. -/
abbrev frobeniusBigSections (M : BigModuleSheaf T.global) (x : M.sections) :
    ((frobeniusBigModulePullback T).obj M).sections :=
  changeBaseBigSections T.global T.global T.specSigma T.frobenius
    T.toClosedFiber_comp_closedFiberMap_specSigma M x

omit [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))] in
/-- **The underived input of arrow 1, pointwise.**  Composing the comparison with a Frobenius
structure map `φ : (F_X)^*_cris M ⟶ M` sends a global section `x` to the family whose value at an
object `A` of `CRIS(X/S)` is `φ_A` applied to the value of `x` at the image of `A` under the
Frobenius endofunctor.

This is verbatim `Crystalline.FCrystal.sectionsFrobenius_val`, which pins the underived
`F_E ∘ (F_X)^*_cris` of `Crystalline/FrobeniusBigGlobalSections.lean`; so the map constructed
below is the derived form of that action and not some other morphism of the same type. -/
theorem sectionsMap_frobeniusBigSections_val (M : BigModuleSheaf T.global)
    (φ : (frobeniusBigModulePullback T).obj M ⟶ M) (x : M.sections)
    (A : (Thickening T.global)ᵒᵖ) :
    (SheafOfModules.sectionsMap φ (frobeniusBigSections T M x)).val A =
      φ.val.app A (x.val (op (T.frobeniusChangeBase.obj A.unop))) := rfl

/-- **Arrow 1 of [Stacks, Tag 07N5]**: the `σ`-semilinear comparison

`RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X/S), (F_X)^*_cris E)`

in `D(Mod_A)`, at the module of an `F`-crystal.  It is
`derivedFrobeniusRestrictGlobalSectionsMap` at `E`, carried from `D⁺` into the unbounded derived
category along `CategoryTheory.DerivedCategory.Plus.ι`, which is where the tag's objects live:
the derived tensor product `- ⊗^L_{A, σ} A` is only right t-exact. -/
def frobeniusSemilinearBaseChangeArrow (E : Crystalline.FCrystal T) :
    DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global (toSmallFCrystal E)) ⟶
      (frobeniusSigmaRestrictScalars T).obj (frobeniusPullbackDerivedGlobalSections T E) :=
  DerivedCategory.Plus.ι.map (derivedFrobeniusRestrictGlobalSectionsMap T E.crystal)

/-- **A term of `...SmallSite.BaseChangeArrows07N5`**, the composite of the first two arrows of
the proof of [Stacks, Tag 07N5]:

`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`.

It is arrow 1 transposed across `...SmallSite.frobeniusDerivedBaseChangeAdjunction`, the chapter's
instance of [Stacks, Tag 0GMT].  No term of this type existed in the library, which is what made
`...SmallSite.BaseChangeArrows07N5Isogeny` a proposition about nothing. -/
def frobeniusBaseChangeArrows07N5 (E : Crystalline.FCrystal T) : BaseChangeArrows07N5 T E :=
  ((frobeniusDerivedBaseChangeAdjunction T).homEquiv _ _).symm
    (frobeniusSemilinearBaseChangeArrow T E)

/-- **A term of `...SmallSite.SigmaSemilinearAction07N5`**: the canonical `σ`-semilinear Frobenius
action

`RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X/S), E)`

on the module-valued crystalline cohomology of an `F`-crystal, arrow 1 followed by `σ_*` of the
third arrow `...SmallSite.frobeniusCohomologyMap`.

`...SmallSite.frobeniusMap07N5Equiv` proves that such an action is exactly the map of
[Stacks, Tag 07N5]; `frobeniusMap07N5Canonical_eq_ofSemilinearAction` says this one induces the
map below. -/
def frobeniusSigmaSemilinearAction (E : Crystalline.FCrystal T) :
    SigmaSemilinearAction07N5 T (toSmallFCrystal E) :=
  frobeniusSemilinearBaseChangeArrow T E ≫
    (frobeniusSigmaRestrictScalars T).map (frobeniusCohomologyMap T E)

/-- **The canonical map of [Stacks, Tag 07N5]**,

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

of `D(A)`: the composite of the first two arrows, `frobeniusBaseChangeArrows07N5`, followed by the
third arrow `...SmallSite.frobeniusCohomologyMap`, which is `RΓ(Cris(X/S), i^{-1}-)` applied to
the `F`-crystal's structure map `F_E`.

This is the first term of `...SmallSite.FrobeniusMap07N5` the library has, and it is the one
parameter `...SmallSite.Statement07N5` carries.  It is canonical: nothing is chosen, and
`sectionsMap_frobeniusBigSections_val` pins its underived input to the underived action
`Crystalline.FCrystal.sectionsFrobenius`.  **The tag is not proved by its existence**: it is
proved at this map, as `...SmallSite.statement07N5` of `SmallSite/Frobenius07N5Theorem.lean`; see
the module documentation. -/
def frobeniusMap07N5Canonical (E : Crystalline.FCrystal T) :
    FrobeniusMap07N5 T (toSmallFCrystal E) :=
  frobeniusBaseChangeArrows07N5 T E ≫ frobeniusCohomologyMap T E

/-- **The canonical map is the one induced by the canonical `σ`-semilinear action**, so arrow 1
read as a map out of the derived tensor product and arrow 1 read as a semilinear endomorphism of
`RΓ` are the same datum.  This is naturality of the adjunction
`...SmallSite.frobeniusDerivedBaseChangeAdjunction` in its right variable. -/
theorem frobeniusMap07N5Canonical_eq_ofSemilinearAction (E : Crystalline.FCrystal T) :
    frobeniusMap07N5Canonical T E =
      frobeniusMap07N5OfSemilinearAction T (frobeniusSigmaSemilinearAction T E) :=
  ((frobeniusDerivedBaseChangeAdjunction T).homEquiv_naturality_right_symm
    (frobeniusSemilinearBaseChangeArrow T E) (frobeniusCohomologyMap T E)).symm

/-- **The canonical map factors through the third arrow of the source's proof**, by construction
and for every `F`-crystal, nondegenerate or not.

`...SmallSite.FrobeniusFactorsThroughCohomologyMap07N5` was a proposition carried as a hypothesis
because `...SmallSite.Statement07N5` quantified over an arbitrary choice of its map, for which
there is nothing to factor.  At the canonical map the factorization is the definition. -/
theorem frobeniusFactorsThroughCohomologyMap07N5_canonical :
    FrobeniusFactorsThroughCohomologyMap07N5 T (frobeniusMap07N5Canonical T) :=
  fun E _ => ⟨frobeniusBaseChangeArrows07N5 T E, rfl⟩

variable [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))]

/-- **[Stacks, Tag 07N5] at the canonical map is exactly the isogeny of the first two arrows of
its own proof.**

`...SmallSite.statement07N5_iff_baseChangeArrows07N5Isogeny` with its factorization hypothesis
discharged by `frobeniusFactorsThroughCohomologyMap07N5_canonical`.  What remains on the right is
the source's (07QC) and (07N6), which rest on [Stacks, Tag 07MU] and [Stacks, Tag 07MY].

`...SmallSite.BoundedCommonLocalRanks07N5` is the delimiter inherited from [Stacks, Tag 07N4]
through the third arrow's isogeny; it is not a hypothesis of the tag and is introduced nowhere
here.  It is discharged for crystals of constant rank by
`Crystalline.FCrystal.hasBoundedCommonLocalRank_of_rank`. -/
theorem statement07N5_canonical_iff_baseChangeArrows07N5Isogeny
    (hrank : BoundedCommonLocalRanks07N5 T) :
    Statement07N5 T (frobeniusMap07N5Canonical T) ↔
      BaseChangeArrows07N5Isogeny T (frobeniusMap07N5Canonical T) :=
  statement07N5_iff_baseChangeArrows07N5Isogeny T _ hrank
    (frobeniusFactorsThroughCohomologyMap07N5_canonical T)

end Frobenius

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

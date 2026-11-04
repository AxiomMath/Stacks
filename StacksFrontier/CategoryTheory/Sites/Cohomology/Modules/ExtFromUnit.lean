module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.FirstCohomologyAndExtensions

/-!
# Morphisms out of the structure sheaf compute cohomology on a ringed site

Let `(C, O)` be a ringed site on a small site and let `M` be a sheaf of `O`-modules. The
extension groups out of the structure sheaf are the cohomology of the site:
`Ext^n_{Mod(O)}(O, M) = H^n(C, M)` for every `n`, where the right-hand side is the `n`-th right
derived functor of global sections of `Stacks.Cohomology.SiteModules.cohomologyFunctor`.

This is the all-degree form of the degree-one statement
`Stacks.Cohomology.SiteModules.extOneEquivFirstCohomology` ([Stacks, Tag 03F1]), and it needs
no new mathematics: the comparison of `δ`-functors
`Stacks.Cohomology.SiteModules.extCohomologyDeltaIso` — produced there from the universality of
both sides — already carries every degree, and the degree-one statement merely evaluates it at
`n = 1`.

Since `Ext^n(X, Y)` is by definition the group of morphisms `X[0] ⟶ Y[0]⟦n⟧` in the derived
category, this says that morphisms out of the structure sheaf in the derived category compute
sheaf cohomology; `derivedHomEquivCohomology` records that reading.

## Main definitions

* `Stacks.Cohomology.SiteModules.deltaFunctorEval`: evaluation of a cohomological `δ`-functor
  in a fixed degree at a fixed object, as a functor on `δ`-functors.

## Main results

* `Stacks.Cohomology.SiteModules.extEquivCohomology`: the additive equivalence
  `Ext^n(O, M) ≃+ H^n(C, M)`, in every degree.
* `Stacks.Cohomology.SiteModules.extEquivCohomology_one`: in degree one it is
  `Stacks.Cohomology.SiteModules.extOneEquivFirstCohomology`, so the characterisations proved
  for that map apply to this one.
* `Stacks.Cohomology.SiteModules.derivedHomEquivCohomology`: the same equivalence written
  with the morphism group `Hom_{D(Mod(O))}(O[0], M[0]⟦n⟧)` of the derived category in place of
  `Ext^n(O, M)`.

## Implementation notes

No `@[stacks]` attribute is placed. [Stacks, Tag 03F1] is the degree-one statement together
with the identification of the class of an extension, and that is where it is registered; the
source uses the all-degree identification throughout as the definition of cohomology of a
complex (for instance in the displayed formula of [Stacks, Tag 08DC]) rather than stating it as
a numbered result, so there is no tag whose content this is.

The `Ext` groups of sheaves of modules in universe `u` live in universe `u + 1` while
cohomology is valued in `u`-modules, so the comparison runs through
`Stacks.Cohomology.SiteModules.moduleToLiftedAddCommGrp` exactly as in the degree-one case; the
`ULift` is undone by `AddEquiv.ulift`.

## References

* [Stacks Project, Tag 03F1](https://stacks.math.columbia.edu/tag/03F1)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe u

namespace Stacks.Cohomology.SiteModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasExt.standard

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Evaluating a cohomological `δ`-functor in degree `n` at a fixed object. This is
`Stacks.Cohomology.SiteModules.deltaFunctorEvalOne` with the degree a parameter. -/
def deltaFunctorEval (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) (n : ℕ) :
    DeltaFunctor (SheafOfModules.{u} R) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} where
  obj F := (F.functor n).obj M
  map η := (η.app n).app M
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Extensions of the structure sheaf are cohomology, in every degree.** For a ringed site
`(C, O)` and a sheaf of `O`-modules `M`, the extension group `Ext^n(O, M)` is canonically the
`n`-th cohomology `H^n(C, M)` of `M` on the site.

Both sides are the degree-`n` part of a universal cohomological `δ`-functor whose degree-zero
part is global sections, so they are identified by
`Stacks.Cohomology.SiteModules.extCohomologyDeltaIso`. -/
def extEquivCohomology (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) (n : ℕ) :
    Ext (SheafOfModules.unit R) M n ≃+ (cohomologyFunctor R n).obj M := by
  let h₁ := (deltaFunctorEval R M n).mapIso (extCohomologyDeltaIso R)
  let e₁ : Ext (SheafOfModules.unit R) M n ≃+
      ((universalCohomologyDeltaFunctor R).functor n).obj M :=
    (Iso.addCommGroupIsoToAddEquiv h₁).trans (AddEquiv.ulift.{u, u + 1})
  let hcast : ((universalCohomologyDeltaFunctor R).functor n).obj M ≅
      (cohomologyFunctor R n).obj M :=
    (eqToIso (universalCohomologyDeltaFunctor_functor R n)).app M
  let F := forget₂ (ModuleCat.{u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{u}
  exact e₁.trans <| Iso.addCommGroupIsoToAddEquiv (F.mapIso hcast)

/-- In degree one the all-degree comparison is the map of [Stacks, Tag 03F1], so the
characterisation of that map by the class of an extension applies to this one. -/
theorem extEquivCohomology_one (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) :
    extEquivCohomology R M 1 = extOneEquivFirstCohomology R M := rfl

/-- **Morphisms out of the structure sheaf in the derived category compute cohomology.** The
group of morphisms `O[0] ⟶ M[0]⟦n⟧` in the derived category of `O`-modules is canonically the
`n`-th cohomology `H^n(C, M)`.

This is `Stacks.Cohomology.SiteModules.extEquivCohomology` composed with the identification of
`Ext^n` with a morphism group of the derived category. -/
def derivedHomEquivCohomology (R : Sheaf J RingCat.{u}) (M : SheafOfModules.{u} R) (n : ℕ) :
    Abelian.zExt (SheafOfModules.unit R) M (n : ℤ) ≃+ (cohomologyFunctor R n).obj M :=
  Ext.homAddEquiv.symm.trans (extEquivCohomology R M n)

end Stacks.Cohomology.SiteModules

end

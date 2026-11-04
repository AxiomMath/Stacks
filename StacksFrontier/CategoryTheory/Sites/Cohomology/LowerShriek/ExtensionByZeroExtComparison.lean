module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.DerivedSectionsAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Ext` out of `j_{U!}O_U` is the sheaf cohomology of the underlying abelian sheaf

Let `(C, J)` be a small site, `R` a sheaf of rings on it, `U` an object of `C` and `F` a sheaf of
`R`-modules. Sections over `U` are corepresented in two different abelian categories: in
`Mod(R)` by the extension by zero `j_{U!}O_U` of the structure sheaf of the localization at `U`
(Stacks 0G1V), and in `Ab(C, J)` by the free abelian sheaf on the presheaf represented by `U`,
which is the object Mathlib's `CategoryTheory.Sheaf.H'` takes `Ext` out of. Deriving sections in
either place therefore computes the same groups, and this file says so:

`Ext_{Mod(R)}(j_{U!}O_U, F, n) ≅ H^n(U, F)`,

where the right-hand side is the cohomology of the *underlying abelian sheaf* of `F`.

The abelian-versus-module distinction is the whole content. The two `Ext`-groups are taken in
different abelian categories, and the underlying abelian sheaf of an injective sheaf of modules
is not injective, so the comparison is not a formality: it is the `δ`-functor argument of Stacks
03FD, whose acyclicity input is that the underlying abelian sheaf of an injective module sheaf
has vanishing positive-degree `Ext` against the sheafification of a sectionwise torsion-free
presheaf.

## Main definitions

* `Stacks.Cohomology.DerivedLowerShriek.sheafCohomologyGenerator`: the abelian sheaf out of which
  Mathlib's `CategoryTheory.Sheaf.H'` takes `Ext`, namely the sheafification of the free abelian
  presheaf on `yoneda.obj U`.
* `Stacks.Cohomology.DerivedLowerShriek.sectionsCorepresentationComparison`: the two
  corepresentations of sections over `U` matched up, that is
  `Hom_{Mod(R)}(j_{U!}O_U, -) ≅ Hom_{Ab}(ℤ_U, (-)^{ab})`.
* `Stacks.Cohomology.DerivedLowerShriek.extensionByZeroUnitExtIso`: the comparison itself, as an
  isomorphism of functors on `Mod(R)` in each degree.

## Main results

* `Stacks.Cohomology.DerivedLowerShriek.extAddEquivSheafCohomology`: the comparison evaluated at
  a sheaf of modules, as an additive equivalence onto `CategoryTheory.Sheaf.H'`.
* `Stacks.Cohomology.DerivedLowerShriek.isZero_ext_iff_isZero_sheafCohomology` and
  `Stacks.Cohomology.DerivedLowerShriek.ext_eq_zero_of_isZero_sheafCohomology`: the transfer of a
  vanishing statement from the abelian side to the module side, which is what a consumer whose
  hypothesis is phrased with `Ext` out of `j_{U!}O_U` needs from the Čech vanishing theorems,
  which are phrased with `CategoryTheory.Sheaf.H'`.

## Implementation notes

No hypothesis beyond those of Stacks 0G1V and Stacks 03FD is imposed: the sheaf of rings is an
arbitrary sheaf of rings on an arbitrary small site, not the structure sheaf of a ringed site,
and it is not assumed commutative.

The site is small — `C : Type u` with `Category.{u} C` — because `CategoryTheory.Sheaf.H'`
aligns the universe of the coefficient sheaf with the morphism universe of the site, and because
the corepresentation of abelian sections over `U` used here,
`ModuleSheafCohomology.evaluationRepresentation`, is stated for a small site. Nothing in the
argument needs smallness beyond that.

The comparison is `ModuleSheafCohomology.extComparisonIso`, the acyclicity form of Stacks 03FD,
applied to the exact functor `SheafOfModules.toSheaf R`. Its two inputs are supplied by existing
results: the acyclicity is `ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf`, and the
degree-zero identification is `sectionsCorepresentationComparison`, which is Stacks 0G1V
(`moduleSectionsCorepresentation`) followed by the corepresentation of abelian sections
(`ModuleSheafCohomology.evaluationRepresentation`). Only the identification in degree zero is
normalized by construction; nothing is claimed here about the degree-zero component of the
resulting isomorphism, which is what `ModuleCohomologyComparisonDef` is the place to record.

No Stacks tag is registered: this is a comparison between two results that are already
registered, Stacks 0G1V on the module side and Stacks 03FD for the `δ`-functor argument.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe u

namespace Stacks.Cohomology.DerivedLowerShriek

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) (R : Sheaf J RingCat.{u})
  (U : C)

/-- The abelian sheaf out of which Mathlib's `CategoryTheory.Sheaf.H'` takes `Ext`: the
sheafification of the free abelian presheaf on the presheaf of sets represented by `U`. It
corepresents sections over `U` on abelian sheaves. -/
@[sga "4 XVIII 1.4.24", sga "7 VII 1.4" "special case"]
abbrev sheafCohomologyGenerator : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- Sheaf cohomology over `U` is `Ext` out of `sheafCohomologyGenerator`. This holds by
definition of `CategoryTheory.Sheaf.cohomologyPresheafFunctor`; it is recorded so that the
comparison below can be read as a statement about `CategoryTheory.Sheaf.H'`. -/
lemma extFunctorObj_sheafCohomologyGenerator_obj (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    (extFunctorObj (sheafCohomologyGenerator J U) n).obj F = Sheaf.H'.{u, u, u} F n U :=
  rfl

attribute [local instance] ModuleSheafCohomology.toSheaf_preservesFiniteColimits

/-- **The two corepresentations of sections over `U`, matched up.** Morphisms out of the
extension by zero `j_{U!}O_U` in sheaves of `R`-modules are the sections over `U` (Stacks 0G1V),
and the sections over `U` of the underlying abelian sheaf are the morphisms out of the free
abelian sheaf on the representable at `U`. The two sections functors are the same functor, so
the corepresentations compose. -/
@[sga "4 V 3.5" "partial"]
def sectionsCorepresentationComparison :
    preadditiveCoyoneda.obj (op (extensionByZeroUnit R U)) ≅
      SheafOfModules.toSheaf R ⋙
        preadditiveCoyoneda.obj (op (sheafCohomologyGenerator J U)) :=
  moduleSectionsCorepresentation J R U ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
      (ModuleSheafCohomology.evaluationRepresentation J U)

/-- **`Ext` out of `j_{U!}O_U` is the sheaf cohomology of the underlying abelian sheaf over
`U`.** In every degree, the `Ext`-functor out of the extension by zero of the structure sheaf of
the localization at `U`, taken in sheaves of `R`-modules, agrees with the `Ext`-functor out of
the free abelian sheaf on the representable at `U` — that is, with `CategoryTheory.Sheaf.H'` —
taken after forgetting to abelian sheaves. The isomorphism is natural in the sheaf of modules.

This is the acyclicity form of Stacks 03FD applied to the exact functor
`SheafOfModules.toSheaf R`: both sides are universal `δ`-functors in the module sheaf agreeing in
degree zero, the right-hand one because the underlying abelian sheaf of an injective sheaf of
modules, while not injective, is `Ext`-acyclic against the corepresenting abelian sheaf
(`ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf`). -/
@[sga "4 V 3.5" "special case"]
def extensionByZeroUnitExtIso (n : ℕ) :
    extFunctorObj (extensionByZeroUnit R U) n ≅
      SheafOfModules.toSheaf R ⋙ extFunctorObj (sheafCohomologyGenerator J U) n :=
  ModuleSheafCohomology.extComparisonIso (SheafOfModules.toSheaf R)
    (sheafCohomologyGenerator J U) (extensionByZeroUnit R U)
    (fun I _ m e => ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf J R I U m e)
    (sectionsCorepresentationComparison J R U) n

/-- **Stacks 03FD over an object, in the `Ext`-out-of-`j_{U!}O_U` form.** The degree-`n`
`Ext`-group from `j_{U!}O_U` to a sheaf of `R`-modules `F`, taken in the category of sheaves of
`R`-modules, is the degree-`n` sheaf cohomology of `U` with values in the underlying abelian
sheaf of `F`. -/
def extAddEquivSheafCohomology (F : SheafOfModules.{u} R) (n : ℕ) :
    Ext.{u} (extensionByZeroUnit R U) F n ≃+
      Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf R).obj F) n U :=
  Iso.addCommGroupIsoToAddEquiv ((extensionByZeroUnitExtIso J R U n).app F)

/-- The `Ext`-group out of `j_{U!}O_U` vanishes exactly when the sheaf cohomology of the
underlying abelian sheaf over `U` does. -/
lemma isZero_ext_iff_isZero_sheafCohomology (F : SheafOfModules.{u} R) (n : ℕ) :
    IsZero ((extFunctorObj (extensionByZeroUnit R U) n).obj F) ↔
      IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf R).obj F) n U) :=
  ⟨fun h => h.of_iso ((extensionByZeroUnitExtIso J R U n).app F).symm,
    fun h => h.of_iso ((extensionByZeroUnitExtIso J R U n).app F)⟩

/-- **The vanishing transfer.** If the sheaf cohomology of the underlying abelian sheaf of `F`
over `U` vanishes in degree `n`, then every degree-`n` `Ext`-class from `j_{U!}O_U` to `F` in
sheaves of `R`-modules is zero. This is the form in which the Čech vanishing theorems, which are
stated with `CategoryTheory.Sheaf.H'`, feed a consumer whose hypothesis is stated with `Ext` out
of `j_{U!}O_U`. -/
theorem ext_eq_zero_of_isZero_sheafCohomology (F : SheafOfModules.{u} R) (n : ℕ)
    (h : IsZero (Sheaf.H'.{u, u, u} ((SheafOfModules.toSheaf R).obj F) n U))
    (e : Ext.{u} (extensionByZeroUnit R U) F n) : e = 0 :=
  have : Subsingleton (Ext.{u} (extensionByZeroUnit R U) F n) :=
    AddCommGrpCat.isZero_iff_subsingleton.mp
      ((isZero_ext_iff_isZero_sheafCohomology J R U F n).2 h)
  Subsingleton.elim _ _

end Stacks.Cohomology.DerivedLowerShriek

end

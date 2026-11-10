module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOpens

/-!
# The projection formula for the Gysin map on cohomology

Let `π : X ⟶ S` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = n + 1`, and let
`i : Z ⟶ X` be the closed subscheme they cut out.  For a class `α ∈ H^q(X, Ω^p_{X/S})` the
**projection formula** of [Stacks, Tag 0G8C] computes the Gysin image of the restriction `α|_Z`:

`γ^{p, q}(α|_Z) = α ∪ γ^{0, 0}(1)` in `H^{q + c}(X, Ω^{p + c}_{X/S})`.

The source proves it from [Stacks, Tag 0G88] — the projection formula for the Gysin map at the
level of local cohomology — and Cohomology, [Stacks, Tag 0G77], the compatibility of the cup
product with forgetting support.

What is proved here is the first half, in the following form.  Write
`γ^p_{f₁, …, f_c} : i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` for the Gysin map of
[Stacks, Tag 0G83] and `γ^{p, q}` for the map on cohomology it induces, [Stacks, Tag 0G8A].
Restriction of forms `α ↦ α|_Z` is a morphism `Ω^p_{X/S} ⟶ i_*Ω^p_{Z/S}` of sheaves, and the
**Gysin formula map** `Ω^p_{X/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` carries a local `p`-form `ω̃` to the
class of `ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c` divided by `f₁ ⋯ f_c`; the two are related by
`AlgebraicGeometry.Scheme.Hom.formRestriction_comp_gysinMapOfFormKernel`, which is the formula
clause of Tag 0G83.  Then

`γ^{p, q}(α|_Z)` is the class with support `[α ∧ d f₁ ∧ ⋯ ∧ d f_c / f₁ ⋯ f_c]` in
`H^{q + c}_Z(X, Ω^{p + c}_{X/S})`, with its support forgotten,

which is `equationGysinCohomologyMap_comp_eq` below and is the cohomological content of
Tag 0G88 for the Gysin map of a family of equations.  It is the items (1), (2) and (4) of the
source's own list.  The remaining item (3) — that forgetting the support of that class gives the
cup product with `γ^{0, 0}(1)` — is Cohomology, Tag 0G77 together with the matching of the two
constructions of Cohomology, Tag 0G76.  The full statement of Tag 0G8C is
`Stacks.DeRham.GysinCupHodge.gysinHodgeFormsMapOfConormalRank_hodgeRestriction`.

## Main definitions

* `cohomologyMapOfModuleHom`: the map `H^q(X, 𝒜) ⟶ H^q(X, 𝒜')` induced by a morphism of sheaves
  of modules, read through the comparison `Stacks.DeRham.CohomologicalGysin`.`
  cohomologyDerivedSingleIso` between the cohomology groups and the cohomology of derived global
  sections of a module placed in degree `c`.
* `forgetSupportCohomology`: **forgetting the support**, the map
  `H^q(X, i_*ℋ^c_Z(ℱ)) ⟶ H^{q + c}(X, ℱ)` induced by the Gysin edge morphism
  `Stacks.DeRham.CohomologicalGysin.supportedGysinEdge`.  Under the identification
  `H^q(X, i_*ℋ^c_Z(ℱ)) = H^{q + c}_Z(X, ℱ)` of Cohomology, Tag 0G70 and the degeneration of
  Remark 0G8A this is the canonical map of the source.
* `ComparisonIsNatural`: the naturality in the sheaf of the comparison
  `cohomologyDerivedSingleIso`; see the implementation notes.

## Main results

* `cohomologyMapOfModuleHom_comp` and `cohomologyMapOfSingleHom_single_comp`: the comparison-read
  map on cohomology is functorial, and splitting off a morphism of sheaves from a morphism
  `𝒜[-c] ⟶ ℱ` of the derived category splits the induced map on cohomology.
* `gysinCohomologyMap_eq`: **the Gysin map on cohomology factors through the group with
  support**, `γ^q = (forget the support) ∘ H^q(γ)`.  This is the definition of Tag 0G8A read as
  a factorisation.
* `equationGysinCohomologyMap_comp_eq`: **the cohomological projection formula**, the half of
  Tag 0G8C that is proved here and the cohomological form of Tag 0G88 for a family of equations.

## Implementation notes

**One naturality.**

* `ComparisonIsNatural` is the naturality in the sheaf of the comparison
  `Stacks.DeRham.CohomologicalGysin.cohomologyDerivedSingleIso`.  That comparison is
  `Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, which is built object by
  object out of a chosen injective resolution and carries no naturality.  The library does have
  the natural version, `Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived`
  of `StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived`, but no
  lemma identifying the two, and the non-natural one is the one Tag 0G8A is built from.  The
  hypothesis is used only to pass between `cohomologyMapOfModuleHom`, which the factorisations
  below produce, and `Hfunctor`.`map`, which is the canonical map on cohomology and the one the
  statement of Tag 0G8C is phrased with.  Everything proved without it is stated without it:
  `equationGysinCohomologyMap_comp_eq` carries no hypothesis of this kind.

**The degree-zero class of `1`.**  `γ^{0, 0}(1)` is formed as `γ^{0, 0}` applied to the class of
the unit global section of `Ω^0_{X/S}` restricted to `Z`.  That is the source's `1`: restriction
of forms is unital, `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_one`, so
`1|_Z = 1`.  The passage from a global section to a degree-zero cohomology class is Mathlib's
`CategoryTheory.Functor.toRightDerivedZero`.

**What Tag 0G8A's own hypotheses are.**  `hker`, the description of the kernel of restriction of
`p`-forms that Tag 0G83 assumes, and `hvan`, the vanishing of `ℋ^j_Z(Ω^{p+c}_{X/S})` for
`j < c`, are hypotheses of Tag 0G8A and are passed along unchanged; the smoothness of
`X → S` and the Koszul regularity of `Z → X` of the source enter only through `hvan`, whose
sufficient condition is Tag 0G7P.  `EquationSupportVanishes`, the shape `hvan` is asked for in, is
concluded by
`isZero_homology_derivedSupportedSections_of_locallyKoszulRegular_of_lt` (namespace
`Stacks.Perfect.LocalCohomologyDegrees`)
in `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.KoszulFlatVanishingLocal` as soon
as `Ω^{p+c}_{X/S}` is flat and quasi-coherent and the equations are Koszul-regular on the affine
opens, which is what smoothness and Koszul regularity give; its companion `..._of_ne` carries Tag
0G7P whole.

## References

* [Stacks Project, Tag 0G8C](https://stacks.math.columbia.edu/tag/0G8C)
* [Stacks Project, Tag 0G88](https://stacks.math.columbia.edu/tag/0G88)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G77](https://stacks.math.columbia.edu/tag/0G77)
* [Stacks Project, Tag 0G76](https://stacks.math.columbia.edu/tag/0G76)
* [Stacks Project, Tag 0G70](https://stacks.math.columbia.edu/tag/0G70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinProjection

universe u

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

-- Sheaves of modules on a ringed space have a derived category.  The choice
-- `HasDerivedCategory.standard _` pins the universes, so it is made once, in
-- `CohomologicalGysinMap`, and only the instance attribute is re-attached here.
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-! ### The map on cohomology induced by a morphism of sheaves, read through the comparison -/

/-- **The map `H^q(X, 𝒜) ⟶ H^q(X, 𝒜')` induced by a morphism `ψ : 𝒜 ⟶ 𝒜'` of sheaves of
modules, read through the comparison `cohomologyDerivedSingleIso` at the placement in degree
`c`.**  It is the canonical map on cohomology — `Hfunctor`.`map ψ` — as soon as that comparison
is natural, which is `ComparisonIsNatural`; the factorisations below produce this form, and the
statements of the source are phrased with the canonical one. -/
def cohomologyMapOfModuleHom (X : RingedSpace.{u, u})
    (A A' : _root_.SheafOfModules.{u} (structureSheafRing X)) (c q : ℕ)
    (ψ : A ⟶ A') :
    Hgroup (structureSheafRing X) ⊤ q A ⟶
      Hgroup (structureSheafRing X) ⊤ q A' :=
  (cohomologyDerivedSingleIso X A (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega)).inv ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} ((q : ℤ) + (c : ℤ))).map
      ((derivedGlobalSections X).map ((singleFunctor _ (c : ℤ)).map ψ)) ≫
    (cohomologyDerivedSingleIso X A' (c : ℤ) ((q : ℤ) + (c : ℤ)) q (by omega)).hom

/-- **The comparison-read map on cohomology is functorial.**  The comparison isomorphism at the
intermediate sheaf cancels. -/
theorem cohomologyMapOfModuleHom_comp (X : RingedSpace.{u, u})
    (A A' A'' : _root_.SheafOfModules.{u} (structureSheafRing X)) (c q : ℕ)
    (ψ : A ⟶ A') (ψ' : A' ⟶ A'') :
    cohomologyMapOfModuleHom X A A'' c q (ψ ≫ ψ') =
      cohomologyMapOfModuleHom X A A' c q ψ ≫ cohomologyMapOfModuleHom X A' A'' c q ψ' := by
  simp [cohomologyMapOfModuleHom, Functor.map_comp]

/-- **Splitting a morphism of sheaves off a morphism `𝒜[-c] ⟶ ℱ` of the derived category splits
the map it induces on cohomology.**  The comparison isomorphism at the intermediate sheaf
cancels, so no naturality of the comparison is needed. -/
theorem cohomologyMapOfSingleHom_single_comp (X : RingedSpace.{u, u})
    (A A' F : _root_.SheafOfModules.{u} (structureSheafRing X)) (c q : ℕ)
    (ψ : A ⟶ A')
    (φ : (singleFunctor _ (c : ℤ)).obj A' ⟶ (singleFunctor _ (0 : ℤ)).obj F) :
    cohomologyMapOfSingleHom X A F c q ((singleFunctor _ (c : ℤ)).map ψ ≫ φ) =
      cohomologyMapOfModuleHom X A A' c q ψ ≫ cohomologyMapOfSingleHom X A' F c q φ := by
  simp [cohomologyMapOfSingleHom, cohomologyMapOfModuleHom, Functor.map_comp]

/-- **The naturality in the sheaf of the comparison `cohomologyDerivedSingleIso`**, in the shape
in which it is used below: the comparison-read map on cohomology induced by a morphism of sheaves
is the canonical one.  See the implementation notes of the module: the comparison is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, which carries no naturality,
and the natural version
`Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived` is not known to agree
with it. -/
abbrev ComparisonIsNatural (X : RingedSpace.{u, u}) (c : ℕ) : Prop :=
  ∀ (q : ℕ) (A A' : _root_.SheafOfModules.{u} (structureSheafRing X))
    (ψ : A ⟶ A'), cohomologyMapOfModuleHom X A A' c q ψ =
      (Hfunctor (structureSheafRing X) ⊤ q).map ψ

/-! ### Forgetting the support -/

section ForgetSupport

variable {X : RingedSpace.{u, u}} (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **Forgetting the support**, `H^q(X, i_*ℋ^c_Z(ℱ)) ⟶ H^{q + c}(X, ℱ)`: the map on cohomology
induced by the Gysin edge morphism `supportedGysinEdge` of [Stacks, Tag 0G8A].

Under the identification `H^q(X, i_*ℋ^c_Z(ℱ)) = H^q(Z, ℋ^c_Z(ℱ)) = H^{q + c}_Z(X, ℱ)` — the
first because `i_*` along the inclusion of a closed subset preserves cohomology, the second
Cohomology, [Stacks, Tag 0G70] together with the degeneration `Rℋ_Z(ℱ) = ℋ^c_Z(ℱ)[-c]` that the
vanishing hypothesis provides, as in Remark [Stacks, Tag 0G8A] — this is the canonical map
`H^{q + c}_Z(X, ℱ) ⟶ H^{q + c}(X, ℱ)` of the source. -/
def forgetSupportCohomology (c : ℕ)
    (F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hvan : ∀ j : ℤ, j < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ j
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (q : ℕ) :
    Hgroup (structureSheafRing X) ⊤ q
        ((modulePushforward (closedSubsetInclusion X Z)).obj
          (localCohomologySheafOfComplex X Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F))) ⟶
      Hgroup (structureSheafRing X) ⊤ (q + c) F :=
  cohomologyMapOfSingleHom X _ F c q
    (supportedGysinEdge Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F) hvan)

/-- **The Gysin map on cohomology factors through the group with support.**  The map `γ^q` of
[Stacks, Tag 0G8A] is the map induced by the sheaf-level Gysin map `γ`, followed by forgetting
the support.  This is its definition read as a factorisation, by
`cohomologyMapOfSingleHom_single_comp`. -/
theorem gysinCohomologyMap_eq (c : ℕ)
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hvan : ∀ j : ℤ, j < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ j
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (γ : A ⟶ (modulePushforward (closedSubsetInclusion X Z)).obj
      (localCohomologySheafOfComplex X Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F)))
    (q : ℕ) :
    gysinCohomologyMap Z hZ c A F hvan γ q =
      cohomologyMapOfModuleHom X A _ c q γ ≫ forgetSupportCohomology Z hZ c F hvan q :=
  cohomologyMapOfSingleHom_single_comp X A _ F c q γ _

end ForgetSupport

/-! ### The projection formula -/

section Projection

open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

variable {Z X S : Scheme.{u}}

/-- The vanishing hypothesis of [Stacks, Tag 0G8A] for the sheaf `Ω^{p+c}_{X/S}` and the closed
set cut out by a family of equations, in the shape `equationGysinCohomologyMap` asks for it. -/
abbrev EquationSupportVanishes (π : X ⟶ S) {n : ℕ} (f : Fin (n + 1) → Γ(X, ⊤)) (p : ℕ) : Prop :=
  ∀ j : ℤ, j < ((n + 1 : ℕ) : ℤ) →
    IsZero (localCohomologySheafOfComplex X.toRingedSpace (equationsClosedSet f)
      (isClosed_equationsClosedSet f) j ((singleFunctor _ (0 : ℤ)).obj
        (relativeDifferentialForms π ((p : ℤ) + ((n + 1 : ℕ) : ℤ)))))

/-- **The cohomological projection formula for the Gysin map of a family of equations.**  Let
`π : X ⟶ S`, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` with `c = n + 1` and let `i : Z ⟶ X` be the closed
subscheme they cut out.  Then the composite

`H^q(X, Ω^p_{X/S}) --(restriction to Z)--> H^q(X, i_*Ω^p_{Z/S}) --γ^{p,q}--> H^{q+c}(X, Ω^{p+c})`

is the composite

`H^q(X, Ω^p_{X/S}) --(Gysin formula)--> H^{q+c}_Z(X, Ω^{p+c}) --(forget support)--> H^{q+c}(X, …)`,

the first arrow of the second composite being induced by the morphism of sheaves carrying a local
`p`-form `ω̃` to the class of `ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c` divided by `f₁ ⋯ f_c`.

**This is the cohomological content of [Stacks, Tag 0G88]** for the Gysin map of a family of
equations, which is items (1), (2) and (4) of the source's proof of [Stacks, Tag 0G8C]: the
sheaf-level projection formula is the formula clause of [Stacks, Tag 0G83],
`formRestriction_comp_gysinMapOfFormKernel`, and the two factorisations are
`cohomologyMapOfModuleHom_comp` and `gysinCohomologyMap_eq`.  Nothing is assumed beyond the
hypotheses `hker` and `hvan` that [Stacks, Tag 0G8A] already carries. -/
@[stacks 0G8C "the cohomological content of the proof, items (1), (2) and (4) of the source's \
list, for the Gysin map of a family of equations: gamma^{p,q} of the restriction of alpha to Z \
is the class with support of alpha wedge df_1 wedge ... wedge df_c over f_1 ... f_c with its \
support forgotten, proved with no hypothesis beyond the hker and hvan that Tag 0G8A \
already carries; the remaining identification of that class with alpha cup gamma^{0,0}(1) is \
Cohomology Tags 0G77 and 0G76 in the Hgroup presentation of the groups, which is absent here"]
theorem equationGysinCohomologyMap_comp_eq (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {n : ℕ}
    (f : Fin (n + 1) → Γ(X, ⊤)) (p : ℕ)
    [(relativeDifferentialForms π ((p : ℤ) + ((n + 1 : ℕ) : ℤ))).IsQuasicoherent]
    (hker : FormKernelGeneratedByEquations i π f (p : ℤ))
    (hvan : EquationSupportVanishes π f p) (q : ℕ) :
    cohomologyMapOfModuleHom X.toRingedSpace _ _ (n + 1) q (formRestriction i π (p : ℤ)) ≫
        equationGysinCohomologyMap i π f p hker hvan q =
      cohomologyMapOfModuleHom X.toRingedSpace _ _ (n + 1) q (gysinFormulaHom π f (p : ℤ)) ≫
        forgetSupportCohomology (equationsClosedSet f) (isClosed_equationsClosedSet f) (n + 1)
          (relativeDifferentialForms π ((p : ℤ) + ((n + 1 : ℕ) : ℤ))) hvan q := by
  have hfac : equationGysinCohomologyMap i π f p hker hvan q =
      cohomologyMapOfModuleHom X.toRingedSpace _ _ (n + 1) q (gysinMapOfFormKernel i π f p hker) ≫
        forgetSupportCohomology (equationsClosedSet f) (isClosed_equationsClosedSet f) (n + 1)
          (relativeDifferentialForms π ((p : ℤ) + ((n + 1 : ℕ) : ℤ))) hvan q :=
    gysinCohomologyMap_eq (equationsClosedSet f) (isClosed_equationsClosedSet f) (n + 1) _ _ hvan
      (gysinMapOfFormKernel i π f p hker) q
  have hsplit : cohomologyMapOfModuleHom X.toRingedSpace _ _ (n + 1) q
        (gysinFormulaHom π f (p : ℤ)) =
      cohomologyMapOfModuleHom X.toRingedSpace _ _ (n + 1) q (formRestriction i π (p : ℤ)) ≫
        cohomologyMapOfModuleHom X.toRingedSpace _ _ (n + 1) q
          (gysinMapOfFormKernel i π f p hker) :=
    (congrArg
        (cohomologyMapOfModuleHom X.toRingedSpace (relativeDifferentialForms π (p : ℤ))
          (pushforwardLocalCohomology f
            (relativeDifferentialForms π ((p : ℤ) + ((n + 1 : ℕ) : ℤ)))) (n + 1) q)
        (formRestriction_comp_gysinMapOfFormKernel i π f p hker).symm).trans
      (cohomologyMapOfModuleHom_comp X.toRingedSpace _ _ _ (n + 1) q _ _)
  rw [hfac, hsplit]
  exact (Category.assoc _ _ _).symm

/-- The class in `H^0(X, Ω^0_{X/S})` of the unit global section, the source's `1`.  The passage
from a global section to a degree-zero cohomology class is Mathlib's
`CategoryTheory.Functor.toRightDerivedZero`.

The corresponding class for the structure sheaf itself is
`Stacks.Cohomology.SpaceModules.oneCohomologyClass`; the two are carried to each other by the
comparison `Ω^0_{X/S} ≅ 𝒪_X` of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`, an identification not used
below. -/
def oneFormCohomologyClass (π : X ⟶ S) :
    Hgroup X.ringCatSheaf ⊤ 0 (relativeDifferentialForms π ((0 : ℕ) : ℤ)) :=
  ((secF X.ringCatSheaf (⊤ : X.Opens)).toRightDerivedZero.app
      (relativeDifferentialForms π ((0 : ℕ) : ℤ))).hom
    ((relativeDifferentialFormsAlgebra π).one.eval (Opposite.op (⊤ : X.Opens)))

/-- **The Gysin class of `1`**, `γ^{0, 0}(1) ∈ H^c(X, Ω^c_{X/S})`.  It is `γ^{0, 0}` applied to
the restriction to `Z` of the unit class of `oneFormCohomologyClass`; that is the source's `1` in
`H^0(Z, 𝒪_Z)`, because restriction of relative differential forms is unital,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback_one`. -/
def gysinOneClass (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) {n : ℕ}
    (f : Fin (n + 1) → Γ(X, ⊤))
    [(relativeDifferentialForms π ((0 : ℤ) + ((n + 1 : ℕ) : ℤ))).IsQuasicoherent]
    (hker₀ : FormKernelGeneratedByEquations i π f ((0 : ℕ) : ℤ))
    (hvan₀ : EquationSupportVanishes π f 0) :
    Hgroup X.ringCatSheaf ⊤ (0 + (n + 1))
      (relativeDifferentialForms π ((0 : ℤ) + ((n + 1 : ℕ) : ℤ))) :=
  (equationGysinCohomologyMap i π f 0 hker₀ hvan₀ 0).hom
    (((Hfunctor (structureSheafRing X.toRingedSpace) ⊤ 0).map
        (formRestriction i π ((0 : ℕ) : ℤ))).hom (oneFormCohomologyClass π))

end Projection

end Stacks.DeRham.GysinProjection

end

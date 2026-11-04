module

public import StacksFrontier.AlgebraicGeometry.AffineMorphismCohomology.Collapse
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.Existence
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.DirectImage.RationalTailAcyclic
public import StacksFrontier.AlgebraicGeometry.Curves.DirectImage.RationalTailContraction

/-!
# Contracting a rational tail changes neither the cohomology of the structure sheaf nor the genus

Let `k` be a field, let `X` be a scheme proper over `k` of dimension one with at worst nodal
singularities and only constant global functions, let `C ⊆ X` be a rational tail
([Stacks, Tag 0E3H]) and let `c : X ⟶ X'` be a contraction of `C` onto the scheme-theoretic
closure `X'` of its complement. Then for every `n`

`H ⁿ(X, 𝒪_X) ≅ H ⁿ(X', 𝒪_{X'})`,

the two sides being modules over the different rings `Γ(X, ⊤)` and `Γ(X', ⊤)`, so that the
comparison is stated after restriction of scalars along `c.appTop : Γ(X', ⊤) ⟶ Γ(X, ⊤)`, exactly
as the closed-immersion comparison
`Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso` is.

In degree one this is **the genus clause of [Stacks, Tag 0E3H]**, the assertion that `X'` has the
same genus as `X`: the genus is `AlgebraicGeometry.genus`, a `Module.finrank` over `k` of
`AlgebraicGeometry.structureSheafCohomology`, so reading the isomorphism as an equality of genera
needs the two `k`-module structures to be matched, which is
`Stacks.Curves.structureMap_appTop_comp_appTop` — the contraction is a morphism over `Spec k` on
global functions. The conclusion is `Stacks.Curves.genus_complementaryCurve`, with no hypothesis
beyond the tag's own.

## The argument

The two inputs of the source are both used, and nothing else is:

* `c_*𝒪_X = 𝒪_{X'}`, which is `Stacks.Curves.isIso_structureSheaf_to_pushforward` at the level of
  sheaves of rings, carried to sheaves of modules by
  `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom`;
* the vanishing of the higher direct images, which is
  `Stacks.Curves.isZero_rightDerived_pushforward_ambientStructureSheaf`.

The passage from the vanishing to the isomorphism on cohomology is the collapse of the right
derived functors of the composite `Γ(X', -) ∘ c_*`, which is `Γ(X, -)` up to the restriction of
scalars `Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop`. The collapse used is
`Stacks.AcyclicCollapse.objIso`, whose hypotheses are that `c_*` carry injective objects to
objects with acyclic global sections — true for an arbitrary morphism of schemes, by
`Stacks.Cohomology.ClosedImmersion.rightAcyclic_moduleGlobalSections_pushforward_injective`, which
is [Stacks, Tag 01EX] part (2) — and that the object be acyclic for `c_*` in *every* positive
degree. That last hypothesis is why
`Stacks.Curves.isZero_rightDerived_pushforward_ambientStructureSheaf` is needed and the
degree-one statement of the tag is not enough.

## Main definitions

* `Stacks.Curves.contractionCohomologyObjIso`: **`H ⁿ(X, 𝒪_X) ≅ H ⁿ(X', 𝒪_{X'})`** for a
  contraction of a rational tail, after restriction of scalars along `c.appTop`.

## Main results

* `Stacks.Curves.appTop_complementaryCurveι_comp_appTop` and
  `Stacks.Curves.structureMap_appTop_comp_appTop`: a contraction is, on global functions, a
  morphism over the ground field — the `k`-algebra structure of `Γ(X, ⊤)` is the one of
  `Γ(X', ⊤)` pushed along `c.appTop`.
* `Stacks.Curves.genus_complementaryCurve`: **the genus clause of [Stacks, Tag 0E3H]**, that the
  scheme-theoretic closure of the complement of a rational tail has the genus of the curve.

## Implementation notes

**Why the contraction is a morphism over the ground field, on global functions.** Only the
`appTop` consequence of that is needed, and it does not have to be proved from the pushout
presentation of `X`: the retraction clause of
`AlgebraicGeometry.IsContractionOfRationalTail` gives `c.appTop ≫ (complementaryCurveι C).appTop
= 𝟙`, and `c.appTop` is invertible by
`Stacks.Curves.isIso_appTop_of_isContractionOfRationalTail`, so the other composite
`(complementaryCurveι C).appTop ≫ c.appTop` is the identity as well — an inverse on one side of
an isomorphism is an inverse. That is
`Stacks.Curves.appTop_complementaryCurveι_comp_appTop`, and it is all the compatibility the
`Module.finrank` comparison needs; the full statement `c ≫ complementaryCurveι C ≫ (X ↘ Spec k)
= X ↘ Spec k` is not proved and not used.

**The attribute.** `Stacks.Curves.genus_complementaryCurve` is registered under Tag 0E3H with
the sub-label `"complementary_curve"` and not under the bare tag, following the convention of
this development: [Stacks, Tag 0E3H] is an example with a dozen separate assertions in it, and
this declaration proves one of them.
So no single declaration states the whole example and an unscoped registration would claim more
than is proved.

**Restriction of scalars.** Its additivity, exactness and preservation of homology are supplied
positionally rather than by instance search, as in
`Stacks.Cohomology.ClosedImmersion.closedImmersionCohomologyIso`, whose construction this one
follows factor for factor; the only change is that the second factor there is
`Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`, which needs `c_*` to be exact,
and here it is `Stacks.AcyclicCollapse.objIso`, which needs the object to be `c_*`-acyclic
instead. Exactness of `c_*` is what a closed immersion buys and a contraction does not have.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.Curves

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Alias of `Stacks.PointImageHigherDirectImage.abelian_modules`. -/
alias abelian_modules := Stacks.PointImageHigherDirectImage.abelian_modules

attribute [local instance] Stacks.PointImageHigherDirectImage.abelian_modules

/-- Alias of `Stacks.PointImageHigherDirectImage.enoughInjectives_modules`. -/
alias enoughInjectives_modules := Stacks.PointImageHigherDirectImage.enoughInjectives_modules

attribute [local instance] Stacks.PointImageHigherDirectImage.enoughInjectives_modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] {C : X.IdealSheafData}

/-- **The direct image of the structure sheaf along a contraction of a rational tail is the
structure sheaf of the target**, as sheaves of modules. This is
`Stacks.Curves.isIso_structureSheaf_to_pushforward`, which is a statement about sheaves of rings,
read through `AlgebraicGeometry.isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom`. -/
def pushforwardStructureSheafIso
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) :
    SheafOfModules.unit (complementaryCurve C).ringCatSheaf ≅
      (Scheme.Modules.pushforward c).obj (SheafOfModules.unit X.ringCatSheaf) :=
  @asIso _ _ _ _ (structureSheafToPushforward c)
    (isIso_unitToPushforwardObjUnit_of_isIso_ringCatSheafHom c
      (isIso_structureSheaf_to_pushforward k X hdim hnodal C hC hc))

/-- **Contracting a rational tail does not change the cohomology of the structure sheaf**: for a
contraction `c : X ⟶ X'` of a rational tail of a proper one-dimensional nodal curve over `k` with
only constant global functions, and every `n`,

`H ⁿ(X, 𝒪_X) ≅ H ⁿ(X', 𝒪_{X'})`,

the left side regarded as a `Γ(X', ⊤)`-module along `c.appTop`.

This is the cohomological content of the genus clause of [Stacks, Tag 0E3H]; what separates it
from that clause is recorded in the implementation notes of this file. -/
def contractionCohomologyObjIso
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {hC : IsRationalTail k X C} {c : X ⟶ complementaryCurve C}
    (hc : IsContractionOfRationalTail hC c) (n : ℕ) :
    (ModuleCat.restrictScalars c.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      ((moduleGlobalSections (complementaryCurve C)).rightDerived n).obj
        (SheafOfModules.unit (complementaryCurve C).ringCatSheaf) :=
  letI : HasDerivedCategory.{u + 1} (complementaryCurve C).Modules :=
    HasDerivedCategory.standard _
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} Γ(complementaryCurve C, ⊤)) :=
    HasDerivedCategory.standard _
  let R := ModuleCat.restrictScalars.{u} c.appTop.hom
  have _ : R.Additive := ⟨by intros; rfl⟩
  have _ : PreservesFiniteLimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : PreservesFiniteColimits R := ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have _ : R.PreservesHomology := Functor.preservesHomologyOfExact R
  (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X) R
        (Scheme.Modules.pushforward c ⋙ moduleGlobalSections (complementaryCurve C))
        (sectionsRestrictionIsoTop c) n).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Stacks.AcyclicCollapse.objIso (Scheme.Modules.pushforward c)
      (moduleGlobalSections (complementaryCurve C))
      (Stacks.Cohomology.ClosedImmersion.rightAcyclic_moduleGlobalSections_pushforward_injective c)
      (fun m hm => isZero_rightDerived_pushforward_ambientStructureSheaf hdim hnodal hc m hm) n ≪≫
    (((moduleGlobalSections (complementaryCurve C)).rightDerived n).mapIso
      (pushforwardStructureSheafIso hdim hnodal hc)).symm

/-! ### The genus clause -/

/-- The two spellings of the ring map making the global functions on `Y` an algebra over the
ground field, through `Scheme.Hom.appTop` and through `Scheme.Hom.appLE` at the top opens,
agree. -/
theorem comp_appTop_hom_eq_comp_appLE_hom (k : Type u) [Field k] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of k)) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appLE ⊤ ⊤ (by simp)).hom := by
  have happ : h.appTop = h.appLE ⊤ ⊤ (by simp) := by
    simpa [Scheme.Hom.appTop] using
      (Scheme.Hom.app_eq_appLE (f := h) (U := (⊤ : (Spec (.of k)).Opens)))
  exact congrArg CommRingCat.Hom.hom
    (congrArg (fun u => (Scheme.ΓSpecIso (.of k)).inv ≫ u) happ)

/-- The cohomology of the structure sheaf that the genus is defined from, written as the global
sections cohomology with scalars restricted along `Scheme.Hom.appTop`. This is
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField` with the `appLE` spelling of
the structure map traded for the `appTop` one. -/
def structureSheafCohomologyIsoRestrict (k : Type u) [Field k] {Y : Scheme.{u}}
    (h : Y ⟶ Spec (.of k)) (n : ℕ) :
    structureSheafCohomology h n ≅
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appTop).hom).obj
        (((moduleGlobalSections Y).rightDerived n).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  structureSheafCohomologyIsoCohomologyOverField k h n ≪≫
    (ModuleCat.restrictScalarsCongr (comp_appTop_hom_eq_comp_appLE_hom k h)).symm.app _

variable {c : X ⟶ complementaryCurve C}

omit [IsProper (X ↘ Spec (.of k))] in
/-- **A contraction of a rational tail is an isomorphism on global functions, with the inclusion
of the complementary curve as its inverse.** The retraction clause of
`AlgebraicGeometry.IsContractionOfRationalTail` gives one composite, and the other follows
because `c.appTop` is invertible
(`Stacks.Curves.isIso_appTop_of_isContractionOfRationalTail`). -/
theorem appTop_complementaryCurveι_comp_appTop [IsReduced X] (hC : IsRationalTail k X C)
    (hc : IsContractionOfRationalTail hC c) :
    (complementaryCurveι C).appTop ≫ c.appTop = 𝟙 Γ(X, ⊤) := by
  have := isIso_appTop_of_isContractionOfRationalTail hC hc
  have h : c.appTop ≫ (complementaryCurveι C).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hc.1]
    simp
  rw [← IsIso.inv_eq_of_hom_inv_id h, IsIso.inv_hom_id]

omit [IsProper (X ↘ Spec (.of k))] in
/-- **A contraction of a rational tail is a morphism over the ground field, on global
functions.** This is what makes the cohomology comparison
`Stacks.Curves.contractionCohomologyObjIso` an identification of `k`-modules: the `k`-algebra
structure of `Γ(X, ⊤)` is the one of `Γ(X', ⊤)` pushed along `c.appTop`. -/
theorem structureMap_appTop_comp_appTop [IsReduced X] (hC : IsRationalTail k X C)
    (hc : IsContractionOfRationalTail hC c) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop) ≫ c.appTop =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop := by
  rw [Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    appTop_complementaryCurveι_comp_appTop hC hc, Category.comp_id]

/-- **Contracting a rational tail does not change the genus**: for `X` proper over `k` of
dimension one with at worst nodal singularities and only constant global functions, and `C ⊆ X`
a rational tail, the scheme-theoretic closure `X'` of the complement of `C` has the genus of `X`.

This is the genus clause of [Stacks, Tag 0E3H], with no hypothesis beyond that tag's own. It is
`Stacks.Curves.contractionCohomologyObjIso` at the canonical contraction, restricted further
along the structure map of `X'` — which identifies the two `k`-module structures by
`Stacks.Curves.structureMap_appTop_comp_appTop` — and then read as an equality of dimensions.

The attribute registers Tag 0E3H with the sub-label `"complementary_curve"`, and not the bare
tag: [Stacks, Tag 0E3H] makes several separate assertions about `X'` and this declaration
proves only the one about the genus, so no single declaration states the whole example. -/
@[stacks 0E3H "complementary_curve"]
theorem genus_complementaryCurve
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    genus (complementaryCurveι C ≫ (X ↘ Spec (.of k))) = genus (X ↘ Spec (.of k)) := by
  have : IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  set c := canonicalContraction k X hdim hnodal C hC with hcdef
  have hc : IsContractionOfRationalTail hC c :=
    isContractionOfRationalTail_canonicalContraction k X hdim hnodal C hC
  have hgf := congrArg CommRingCat.Hom.hom (structureMap_appTop_comp_appTop hC hc).symm
  rw [CommRingCat.hom_comp] at hgf
  have e : structureSheafCohomology (X ↘ Spec (.of k)) 1 ≅
      structureSheafCohomology (complementaryCurveι C ≫ (X ↘ Spec (.of k))) 1 :=
    structureSheafCohomologyIsoRestrict k (X ↘ Spec (.of k)) 1 ≪≫
      ModuleCat.restrictScalarsComp'App _ _ _ hgf _ ≪≫
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
          (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop).hom).mapIso
        (contractionCohomologyObjIso hdim hnodal hc 1) ≪≫
      (structureSheafCohomologyIsoRestrict k
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))) 1).symm
  rw [genus_eq_finrank_structureSheafCohomology, genus_eq_finrank_structureSheafCohomology]
  exact (e.toLinearEquiv.finrank_eq).symm

end Stacks.Curves

end

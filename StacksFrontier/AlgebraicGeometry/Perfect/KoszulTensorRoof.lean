module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeSheafPerfectHomQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystemPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulSliceRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.TensorRoofFromSystem

/-!
# Lifting a map over a union of basic opens along a Koszul tensor factor

Let `A` be a commutative ring, `X = Spec A`, `f = (f₁, …, f_r)` a finite sequence in `A` and
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`. Let `E` be a perfect object of `D(𝒪_X)` and `E'` an object with
quasi-coherent cohomology sheaves. Every map `α : E|_U ⟶ E'|_U` fits into a roof

`E ←β— Iₑ ⊗^𝐋_{𝒪_X} E —γ→ E'`

in which `Iₑ` is a stage of the derived Koszul system on the powers of `f`, `β|_U` is invertible
and `γ|_U = β|_U ≫ α`. The middle object is a derived tensor product of `E` with the *perfect*
complex `Iₑ`, which is what carries cohomological support from `E` to it.

## Main results

* `Koszul.DerivedSystem.exists_roof_tensorKoszul`: the roof, with perfectness of `Iₑ`.
* `Koszul.DerivedSystem.affineTensorUnitIso` and `Koszul.DerivedSystem.structureSheafHomUnit`:
  the unit `𝒪_X ⊗^𝐋 E ≅ E` of [Stacks, Tag 0FPT] on `Spec A`, and the morphism
  `𝒪_X ⟶ R𝓗om(E, E)` it transposes to.

## How the roof is built

`Stacks.Cohomology.SliceDerivedSheafHom.exists_roof_of_exists_factorisation` is the argument,
stated over a variable ringed site; this file supplies its four hypotheses at `Spec A`:

* the augmentations `aₑ : Iₑ ⟶ 𝒪_X` become invertible after restriction to `U` —
  `Koszul.DerivedSystem.isIso_sliceRestrict_map_canonical`;
* `𝒪_X` is a unit for `⊗^𝐋` against `E` — [Stacks, Tag 0FPT], through
  `Koszul.DerivedSystem.structureSheafHomUnit`, whose transpose is the unit isomorphism;
* every `φ : 𝒪_X|_U ⟶ R𝓗om(E, E')|_U` comes from a Koszul stage — [Stacks, Tag 08DD], as
  `Koszul.DerivedSystem.exists_koszulStage_factorisation_slice`;
* `R𝓗om(E, E')` has quasi-coherent cohomology, which is what 08DD needs — part (2) of
  [Stacks, Tag 0A6H], `AlgebraicGeometry.derivedCategoryB_derivedSheafHom_of_isPerfect`.

## Implementation notes

The registrations of [Stacks, Tag 08EH] and [Stacks, Tag 08DD] are on other declarations, so no
`@[stacks]` attribute is placed and the declarations carry descriptive names.

Everything is in the **slice-site** model of `𝒪_U`-modules, the model the derived internal hom,
the tensor–internal-hom bijection and the mate of [Stacks, Tag 08I3] are stated in;
`Koszul.DerivedSystem.exists_koszulStage_factorisation_slice` is what carries 08DD into it from
the open-subspace model it is proved in.

**What is not asserted, against the statement of [Stacks, Tag 08EH].** Two clauses of the source
are not here, and both are spelling crossings rather than mathematics:

* the source takes `U` to be an arbitrary quasi-compact open of the affine scheme `X`, whereas
  `U = D(f₁) ∪ ⋯ ∪ D(f_r)` here. Every quasi-compact open of `Spec A` is such a union — the basic
  opens are a basis and `U` is compact — but that identification is not available in the form
  `∃ r f, Koszul.DerivedSystem.unionOfBasicOpens f = U`, and the carriers `PrimeSpectrum A` and
  the topological space of the scheme `Spec A` are not interchangeable by elaboration;
* the source asserts that the middle object `E₁` is perfect. What is asserted here is that the
  tensor *factor* `Iₑ` is perfect. The two are joined by [Stacks, Tag 09J5], proved as
  `AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct`, which is stated at the
  `StrictlyPerfect.OXMod` spelling of the modules on a ringed space rather than at the ringed-site
  spelling used here.

A general affine scheme, rather than a spectrum, is likewise reached only through `X ≅ Spec Γ(X)`,
which is a third crossing of the same kind.

The unit of the derived tensor product is taken from the structure-sheaf-indexed packaging of
[Stacks, Tag 06YU] read at the site-indexed one by
`AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite`, which keeps the same bifunctor;
so no comparison of two derived tensor products enters, and the unit isomorphism is literally an
isomorphism of the bifunctor the bijection of [Stacks, Tag 08J8] is stated at.

## References

* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules (StructureSheafModules ringedSite)
open Stacks.Cohomology.SliceDerivedSheafHom

universe u

namespace Koszul.DerivedSystem

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {A : CommRingCat.{u}} {r : ℕ}

/-- The ringed site of `X = Spec A`: the site of opens of `Spec A` with its structure sheaf. -/
abbrev affineSite (A : CommRingCat.{u}) : RingedSite.{u, u, u} := ringedSite (Spec A).sheaf

/-- **`D(𝒪_X)` for `X = Spec A`, in the ringed-site spelling of the module category.** The
objects are those of `Koszul.DerivedSystem.derivedCat` — the two categories are the same by
`rfl` — but the structure sheaf is named as the one of the ringed site `affineSite A`, which is
the spelling the derived internal hom, the tensor–internal-hom bijection of [Stacks, Tag 08J8]
and the roof of [Stacks, Tag 08EH] are all stated at.

**Everything in this file is stated at this spelling, deliberately.** The two spellings of the
category are definitionally equal, so an object of either is accepted for the other in term
mode, and `Koszul.DerivedSystem.affineStructureSheafObject` is where that crossing happens,
once. What is *not* interchangeable is their `Preadditive` structure: with `E` named at the
`derivedCat` spelling, the hom group `𝒪_X ⟶ R𝓗om(E, E)` has no `Add` — instance search finds
`Preadditive` for each spelling separately and for neither of the mixed homs that
`derivedSheafHomBifunctor (affineSite A)` then produces — and the transpose below, which is an
element of that group, cannot be written down. Do not restate anything
below at `derivedCat`. -/
abbrev affineDerivedCat (A : CommRingCat.{u}) :=
  DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (affineSite A).O))

/-- The structure sheaf `𝒪_X` in degree zero, as an object of `affineDerivedCat`. This is
`Koszul.DerivedSystem.structureSheafObject` read at the ringed-site spelling of the module
category, the two being definitionally equal. -/
def affineStructureSheafObject (A : CommRingCat.{u}) : affineDerivedCat A :=
  structureSheafObject A

/-- The tensor–internal-hom bijection of [Stacks, Tag 08J8] on `X = Spec A`. Naming the instance
at the objects it is used at is not cosmetic; see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SliceDerivedSheafHomTranspose.lean`. -/
abbrev affineCurryEquiv (K E Z : affineDerivedCat A) :=
  RingedSite.derivedCurryHomEquiv (affineSite A) K E Z

/-- **[Stacks, Tag 0FPT] on `Spec A`**: the structure sheaf in degree zero is a unit for the
derived tensor product, `𝒪_X ⊗^𝐋_{𝒪_X} E ≅ E`. It is the unit constraint of the
structure-sheaf-indexed packaging of [Stacks, Tag 06YU], read at the site-indexed derived tensor
product through `AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite`, which has the
same bifunctor. -/
def affineTensorUnitIso (A : CommRingCat.{u}) (E : affineDerivedCat A) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        (affineStructureSheafObject A)).obj E ≅ E :=
  Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso (affineSite A)
    (AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite (affineSite A)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct (affineSite A))) E

/-- The morphism `𝒪_X ⟶ R𝓗om(E, E)` that the unit isomorphism of
`Koszul.DerivedSystem.affineTensorUnitIso` transposes to under the tensor–internal-hom bijection
of [Stacks, Tag 08J8]. It plays the role of the identity of `E`, read as a global section of the
derived internal hom. -/
def structureSheafHomUnit (A : CommRingCat.{u}) (E : affineDerivedCat A) :
    affineStructureSheafObject A ⟶
      ((RingedSite.derivedSheafHomBifunctor (affineSite A)).obj (op E)).obj E :=
  (affineCurryEquiv (affineStructureSheafObject A) E E).symm (affineTensorUnitIso A E).hom

/-- The transpose of `Koszul.DerivedSystem.structureSheafHomUnit` is invertible, being the unit
isomorphism of [Stacks, Tag 0FPT]. This is the hypothesis `hv` of
`Stacks.Cohomology.SliceDerivedSheafHom.exists_roof_of_exists_factorisation`.

**The bijection is written out here rather than through `affineCurryEquiv`, deliberately.** The
two are the same term — the abbreviation is reducible with exactly this body — but
`Koszul.DerivedSystem.exists_roof_tensorKoszul` below needs this statement at the spelling the
roof's hypothesis `hv` has, namely `RingedSite.derivedCurryHomEquiv (affineSite A) …`. Written
through the abbreviation, matching the two costs a crossing that unfolds `affineSite` and
`ringedSite` into `Spec A` — 482 unfoldings of each, 509 of `Scheme.toLocallyRingedSpace` — and
exceeds the default recursion limit all by itself, in a one-line `example` at command level.
Elaborating the type as written costs nothing. Do not tidy it back to `affineCurryEquiv`.

**And `exists_roof_tensorKoszul` below does not cite this theorem for its `hv`, deliberately.**
It re-runs these two lines in place. Citing it instead makes the elaborator compare two whole,
independently elaborated mentions of the bijection — the one in this statement against the one
in the roof's hypothesis, after the roof's eight instance arguments have been resynthesized at
`affineSite A` — and that comparison exceeds the default heartbeat budget on its own, with
`v` given or left to be determined by `hv`. This is the rule that
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/TensorRoofFromSystem.lean` records for this bijection, that such an equation is to be consumed
by `rw` and not by `exact` against another declaration's hypothesis. This statement is kept
because it is the content of [Stacks, Tag 0FPT] here: the transpose of the unit is invertible. -/
theorem isIso_affineCurryEquiv_structureSheafHomUnit (A : CommRingCat.{u})
    (E : affineDerivedCat A) :
    IsIso (RingedSite.derivedCurryHomEquiv (affineSite A) (affineStructureSheafObject A) E E
      (structureSheafHomUnit A E)) := by
  rw [structureSheafHomUnit, AddEquiv.apply_symm_apply]
  exact (affineTensorUnitIso A E).isIso_hom

/-- **The roof of [Stacks, Tag 08EH] at `X = Spec A` and `U = D(f₁) ∪ ⋯ ∪ D(f_r)`, without the
perfectness of the tensor factor.** The four hypotheses of
`Stacks.Cohomology.SliceDerivedSheafHom.exists_roof_of_exists_factorisation` supplied at
`affineSite A`, with the quasi-coherence of the derived internal hom taken as a hypothesis
rather than derived.

**Separated from `exists_roof_tensorKoszul` for the elaborator's budget.** Heartbeats accumulate
per declaration, and the two steps of this argument each cost most of one default budget: this
one matches the conclusion of `exists_roof_of_exists_factorisation` against the statement
written here, and the one below matches that statement against the conclusion wanted, which
adds the perfectness clause. Performed in one declaration the two together exceed the default
limit. -/
private theorem exists_roof_tensorKoszul_aux (f : Fin r → A) (E E' : affineDerivedCat A)
    (hH : HasQuasicoherentCohomology A
      (((RingedSite.derivedSheafHomBifunctor (affineSite A)).obj (op E)).obj E'))
    (α : (restrictD (affineSite A) (unionOfBasicOpens f)).obj E ⟶
      (restrictD (affineSite A) (unionOfBasicOpens f)).obj E') :
    ∃ (e : ℕ)
      (β : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E)
      (γ : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E'),
      IsIso ((restrictD (affineSite A) (unionOfBasicOpens f)).map β) ∧
        (restrictD (affineSite A) (unionOfBasicOpens f)).map γ =
          (restrictD (affineSite A) (unionOfBasicOpens f)).map β ≫ α :=
  exists_roof_of_exists_factorisation (affineSite A) (unionOfBasicOpens f)
    (ι := ℕ) (fun e : ℕ => (koszulDerivedSystem f).obj (op e)) (affineStructureSheafObject A) E E'
    (fun e => canonicalKoszulToStructureSheaf f e)
    (fun e => isIso_sliceRestrict_map_canonical f e) (structureSheafHomUnit A E)
    (by rw [structureSheafHomUnit, AddEquiv.apply_symm_apply]
        exact (affineTensorUnitIso A E).isIso_hom)
    (fun φ => exists_koszulStage_factorisation_slice f
      (((RingedSite.derivedSheafHomBifunctor (affineSite A)).obj (op E)).obj E') hH φ) α

/-- **[Stacks, Tag 08EH] for `X = Spec A` and `U = D(f₁) ∪ ⋯ ∪ D(f_r)`, with the tensor
presentation of the middle object.** Let `E` be a perfect object of `D(𝒪_X)` and `E'` an object
with quasi-coherent cohomology sheaves. Every map `α : E|_U ⟶ E'|_U` fits into a roof

`E ←β— Iₑ ⊗^𝐋_{𝒪_X} E —γ→ E'`

with `Iₑ` a stage of the derived Koszul system on the powers of `f` — a perfect object of
`D(𝒪_X)` — such that `β|_U` is invertible and `γ|_U = β|_U ≫ α`; that is,
`α = γ|_U ∘ (β|_U)⁻¹`.

The registration of [Stacks, Tag 08EH] is on another declaration, so no tag
attribute is placed here. -/
theorem exists_roof_tensorKoszul (f : Fin r → A) (E E' : affineDerivedCat A)
    (hE : RingedSpace.IsPerfect (X := (Spec A).toRingedSpace) E)
    (hE' : HasQuasicoherentCohomology A E')
    (α : (restrictD (affineSite A) (unionOfBasicOpens f)).obj E ⟶
      (restrictD (affineSite A) (unionOfBasicOpens f)).obj E') :
    ∃ (e : ℕ)
      (β : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E)
      (γ : ((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj
        ((koszulDerivedSystem f).obj (op e))).obj E ⟶ E'),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace)
          ((koszulDerivedSystem f).obj (op e)) ∧
        IsIso ((restrictD (affineSite A) (unionOfBasicOpens f)).map β) ∧
          (restrictD (affineSite A) (unionOfBasicOpens f)).map γ =
            (restrictD (affineSite A) (unionOfBasicOpens f)).map β ≫ α := by
  obtain ⟨e, β, γ, hβ, hγ⟩ := exists_roof_tensorKoszul_aux f E E'
    (derivedCategoryB_derivedSheafHom_of_isPerfect (Spec A) E E' hE hE') α
  exact ⟨e, β, γ, isPerfect_koszulDerivedSystem_obj f e, hβ, hγ⟩

end Koszul.DerivedSystem

end

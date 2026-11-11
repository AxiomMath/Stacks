module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.CartanEilenbergTotalFiltrationQuasiIso
public import StacksFrontier.Algebra.Homology.MapTotalFiltration
public import StacksFrontier.Algebra.Homology.SpectralSequence.Transport
public import StacksFrontier.Homology.Injectives.Ext.FilteredPageOne
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexSpectralSequences
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.StupidTruncationSpectralSequence

/-!
# The brutal truncation spectral sequence is the first Cartan-Eilenberg spectral sequence

Let `(X, O_X)` be a ringed space and let `F^•` be a bounded below complex of `O_X`-modules. There
are two constructions of a spectral sequence with `E_1^{p, q} = H^q(X, F^p)` converging to
`H^{p + q}(X, F^•)`:

* filtering `F^•` by its brutal truncations `σ_{≥ p}F^•` and taking the spectral sequence of the
  resulting filtered complex of global sections, which is
  `Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence.spectralSequence`
  ([Stacks, Tag 0FLK]);
* taking a Cartan-Eilenberg resolution `I^{•,•}` of `F^•` and the spectral sequence of
  `Tot(Γ(I))` filtered by the first coordinate, which is the *first* spectral sequence of
  [Stacks, Tag 015J].

This file proves they agree: `nonempty_spectralSequence_iso_cartanEilenbergFirst`, which is the
third bullet of the bounded below case of [Stacks, Tag 0FLK], and
`exists_stupidTruncationSpectralSequence_iso_cartanEilenbergFirst`, which packages it with the
boundedness and convergence of clause (2) for one and the same spectral sequence.

## The shape of the comparison

Both sides are objects of `CohomologicalSpectralSequence _ 1`, so "equal" is read as "isomorphic
in that category" (`CategoryTheory.SpectralSequence.Hom` and its `Category` instance). The
comparison is produced by the functoriality of the spectral sequence of a filtered complex
([Stacks, Tag 012O]) applied to a single morphism of filtered complexes, and shown to be an
isomorphism by `CategoryTheory.SpectralSequence.isIso_of_isIso_hom`: it suffices to be an
isomorphism on the first page.

That morphism is obtained in four moves.

1. The first total filtration `F^pTot(I)` of the Cartan-Eilenberg resolution is a bounded below
   complex of filtered injective objects
   (`StacksDraft.CartanEilenbergResolutions.isFilteredInjective_evalFil_totalFiltration₁`), and
   the brutal truncation filtration of `F^•` is finite in every degree
   (`CochainComplex.stupidTruncationFiltration_isDegreewiseFinite`), so [Stacks, Tag 05TY] in the
   form `CochainComplex.filteredHomotopic_lift` lifts the filtered augmentation
   `σ_{≥ •}F^• ⟶ F^•Tot(I)` along the filtered quasi-isomorphism `σ_{≥ •}F^• ⟶ S.replacement`,
   giving `β : S.replacement ⟶ F^•Tot(I)` with `S.replacementMap ≫ β` filtered homotopic to the
   augmentation.
2. `β` is a quasi-isomorphism on every filtration step: the augmentation is
   (`StacksDraft.CartanEilenbergResolutions.quasiIso_filteredTotalAugmentation_natTrans_app`), so
   is `S.replacementMap`, and a filtered homotopy restricts to a homotopy on each step
   (`CochainComplex.quasiIso_natTrans_app_of_filteredHomotopic`).
3. Global sections preserve that: both `S.replacement` and `F^•Tot(I)` have bounded below
   filtration steps with injective terms, hence K-injective filtration steps, and an additive
   functor carries a quasi-isomorphism between K-injective complexes to a quasi-isomorphism.
   Two consecutive steps then give the graded pieces
   (`FilteredComplexSpectralSequence.quasiIso_gr_map`) and hence the first page
   (`FilteredComplexSpectralSequence.isIso_filteredSpectralSequenceMap_hom_one`).
4. Finally `Γ(Tot(I))` and `Tot(Γ(I))` agree *as filtered complexes*, because the total complex of
   the Cartan-Eilenberg bicomplex has finite support in each total degree and an additive functor
   commutes with such a total complex compatibly with the filtration by the first coordinate
   (`HomologicalComplex₂.TotalMap.totalFiltration₁IsoOfFinite`). Composing with that isomorphism
   lands in the filtered complex whose spectral sequence is the 015J one.

## Main results

All in the namespace `Stacks.Cohomology.FilteredComplex`.

* `cartanEilenbergFirstSpectralSequence`: the first spectral sequence of [Stacks, Tag 015J] for
  global sections and a Cartan-Eilenberg resolution.
* `nonempty_spectralSequence_iso_cartanEilenbergFirst`: clause (3) of the bounded below case of
  [Stacks, Tag 0FLK].
* `exists_stupidTruncationSpectralSequence_iso_cartanEilenbergFirst`: the same, in the existential
  shape of clauses (1) and (2).
* `exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst`: the bounded
  below clauses of [Stacks, Tag 0FLK] for the spectral sequence of [Stacks, Tag 0BKK]: it can be
  computed by a filtered K-injective resolution as in Remark [Stacks, Tag 0BKL], and that
  resolution's spectral sequence is bounded, converges to `H^{i + j}(X, F^•)` and is the first
  spectral sequence of every Cartan-Eilenberg resolution.

## Implementation notes

The hypotheses `hge` and `hinj` on the brutal-truncation package are exactly two of the
conclusions of
`Stacks.Cohomology.FilteredComplex.exists_boundedBelowStupidTruncationSpectralSequence`, so this
clause composes with that one; they are not extra assumptions on the source, but the record of
which replacement the bounded below construction produces. They are genuinely needed: without
filtered injectivity the spectral sequence of `Γ(S.replacement)` is not determined by `F^•`.

The spelling of `CategoryTheory.FilteredObject.Filtration.ι`, whose codomain goes through the
constant functor, is crossed once by `CochainComplex.filtrationStepι`; every statement here is
written at that spelling rather than mixing the two, which is what keeps the proofs free of
`erw`.

## References

* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 05TY](https://stacks.math.columbia.edu/tag/05TY)
* [Stacks Project, Tag 012O](https://stacks.math.columbia.edu/tag/012O)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.CartanEilenbergResolutions

universe u

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u})

/-- **The first spectral sequence of [Stacks, Tag 015J]** for global sections on a ringed space
and a Cartan-Eilenberg resolution `I^{•,•}` of `F^•`: the spectral sequence of `Tot(Γ(I))`
filtered by the first coordinate, read from page one, where the source's description of its first
page `'E_1^{p, q} = H^q(X, F^p)` starts. -/
@[ega "0 12.1.7" "partial"]
abbrev cartanEilenbergFirstSpectralSequence
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (I : F.CartanEilenbergResolution) :
    CohomologicalSpectralSequence (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 1 :=
  ((Stacks.Cohomology.CechSpectral.totalSpectralSequence₁Functor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))).obj
    (HomologicalComplex₂.TotalMap.mapBicomplex
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) I.bicomplex)).shiftStart (by omega)

section GlobalSections

variable {J J' : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}

/-- Global sections of the `p`-th step of a morphism of filtered complexes, at the spelling
`globalSectionsFilteredComplex` presents. -/
abbrev globalSectionsFilteredComplexMapf (φ : J ⟶ J') (p : ℤᵒᵖ) :
    (globalSectionsFilteredComplex X J).filtration.obj p ⟶
      (globalSectionsFilteredComplex X J').filtration.obj p :=
  (globalSectionsComplexFunctor X).map (φ.natTrans.app p)

/-- **Global sections of a morphism of filtered complexes of module sheaves.** This is the
functoriality of `Stacks.Cohomology.FilteredComplex.globalSectionsFilteredComplex`. -/
def globalSectionsFilteredComplexMap (φ : J ⟶ J') :
    globalSectionsFilteredComplex X J ⟶ globalSectionsFilteredComplex X J' :=
  FilteredObject.homMk ((globalSectionsComplexFunctor X).map φ.hom)
    (globalSectionsFilteredComplexMapf X φ)
    (fun p => (Functor.map_comp _ _ _).symm.trans
      ((congrArg (globalSectionsComplexFunctor X).map (φ.comm p)).trans
        (Functor.map_comp _ _ _)))

/-- A bounded below complex of filtered injective objects has K-injective filtration steps: each
step has injective terms and is bounded below by the bound of the ambient complex, so
`CochainComplex.isKInjective_of_injective` applies. -/
lemma isKInjective_filtration_obj
    (M : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (c : ℤ)
    (hMge : M.X.IsStrictlyGE c)
    (hM : ∀ n, (CochainComplex.evalFil M n).IsFilteredInjective) (p : ℤᵒᵖ) :
    (M.filtration.obj p).IsKInjective := by
  have : ∀ n, Injective ((M.filtration.obj p).X n) := fun n =>
    CochainComplex.injective_filtration_obj_X_of_isFilteredInjective M hM p n
  have := hMge
  have : (M.filtration.obj p).IsStrictlyGE c :=
    (CochainComplex.isStrictlyGE_iff _ _).mpr (fun n hn =>
      (CochainComplex.isZero_of_isStrictlyGE M.X c n hn).of_mono
        ((CochainComplex.filtrationStepι M p).f n))
  exact CochainComplex.isKInjective_of_injective _ c

/-- **Global sections preserve a stepwise quasi-isomorphism between bounded below complexes of
filtered injective objects.** Each filtration step is K-injective by
`isKInjective_filtration_obj`, and an additive functor carries a quasi-isomorphism between
K-injective complexes to a quasi-isomorphism. -/
lemma quasiIso_globalSectionsFilteredComplexMap_natTrans_app
    (a b : ℤ) (hJge : J.X.IsStrictlyGE a) (hJ'ge : J'.X.IsStrictlyGE b)
    (hJ : ∀ n, (CochainComplex.evalFil J n).IsFilteredInjective)
    (hJ' : ∀ n, (CochainComplex.evalFil J' n).IsFilteredInjective)
    (φ : J ⟶ J') (hφ : ∀ p : ℤ, QuasiIso (φ.natTrans.app (op p))) (p : ℤ) :
    QuasiIso ((globalSectionsFilteredComplexMap X φ).natTrans.app (op p)) := by
  change QuasiIso (globalSectionsFilteredComplexMapf X φ (op p))
  exact Stacks.Injectives.KInjectiveResolution.quasiIso_mapHomologicalComplex_map_of_isKInjective
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) (φ.natTrans.app (op p))
    (isKInjective_filtration_obj X J a hJge hJ (op p))
    (isKInjective_filtration_obj X J' b hJ'ge hJ' (op p)) (hφ p)

end GlobalSections

/-- **The comparison of [Stacks, Tag 0FLK] with [Stacks, Tag 015J], from the stepwise
quasi-isomorphy of the filtered Cartan-Eilenberg augmentation.** If the filtered augmentation
`σ_{≥ p}F^• ⟶ F^pTot(I)` is a quasi-isomorphism on every filtration step (`hCE`), the brutal
truncation spectral sequence of `S` is isomorphic to the first spectral sequence of the
Cartan-Eilenberg resolution `I`.

`hCE` is a statement about the Cartan-Eilenberg resolution alone: `F^pTot(I)` is the total
complex of the brutal truncation `σ_{≥ p}I^{•,•}` of the bicomplex in its first coordinate, whose
columns still resolve the terms of `σ_{≥ p}F^•`. It holds for every bounded below `F^•`, by
`StacksDraft.CartanEilenbergResolutions.quasiIso_filteredTotalAugmentation_natTrans_app`, which
is how `nonempty_spectralSequence_iso_cartanEilenbergFirst` below applies this lemma.

The proof constructs the filtered lift, shows it is a quasi-isomorphism on every step, passes
through global sections, identifies the first page, and compares `Γ(Tot(I))` with `Tot(Γ(I))`
as filtered complexes. -/
theorem nonempty_spectralSequence_iso_cartanEilenbergFirst_of_quasiIso_augmentation
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (a : ℤ)
    (S : StupidTruncationSpectralSequence X F)
    (hge : S.replacement.X.IsStrictlyGE a)
    (hinj : ∀ n, (CochainComplex.evalFil S.replacement n).IsFilteredInjective)
    (I : F.CartanEilenbergResolution)
    [I.bicomplex.HasTotal (ComplexShape.up ℤ)]
    (hCE : ∀ p : ℤ, QuasiIso ((filteredTotalAugmentation I).natTrans.app (op p))) :
    Nonempty (S.spectralSequence ≅ cartanEilenbergFirstSpectralSequence X I) := by
  obtain ⟨b, hb⟩ := exists_isStrictlyGE_totalFiltration₁ I
  have := hb
  -- 1. lift the filtered Cartan-Eilenberg augmentation along the replacement
  obtain ⟨β, hβ⟩ := (CochainComplex.filteredHomotopic_lift
    (CochainComplex.stupidTruncationFiltration_isDegreewiseFinite F)
    (fun n => ((CochainComplex.isFilteredInjective_evalFil_iff S.replacement n).1 (hinj n)).1)
    b (isFilteredInjective_evalFil_totalFiltration₁ I) S.replacementMap
    (filteredQuasiIso_of_natTrans S.replacementMap
      S.replacementMap_step_quasiIso)).1 (filteredTotalAugmentation I)
  -- 2. the lift is a quasi-isomorphism on every filtration step
  have hβstep (p : ℤ) : QuasiIso (β.natTrans.app (op p)) :=
    CochainComplex.quasiIso_natTrans_app_of_filteredHomotopic hβ p
      (S.replacementMap_step_quasiIso p)
      (hCE p)
  -- 3. global sections preserve that, so the first page is identified
  have hstep := quasiIso_globalSectionsFilteredComplexMap_natTrans_app X a b hge hb hinj
    (isFilteredInjective_evalFil_totalFiltration₁ I) β hβstep
  -- 4. compose with `Γ(Tot(I)) = Tot(Γ(I))` as filtered complexes
  let G := SheafOfModules.evaluation (structureSheafRing X) (op ⊤)
  have : (HomologicalComplex₂.TotalMap.mapBicomplex G I.bicomplex).HasTotal
    (ComplexShape.up ℤ) := inferInstance
  let e : globalSectionsFilteredComplex X I.bicomplex.totalFiltration₁ ≅
      (HomologicalComplex₂.TotalMap.mapBicomplex G I.bicomplex).totalFiltration₁ :=
    (HomologicalComplex₂.TotalMap.totalFiltration₁IsoOfFinite G I.bicomplex
      (fun n => finite_not_isZero_bicomplex I n)
      (HomologicalComplex₂.TotalMap.mono_map_totalFiltration₁_ι G I.bicomplex)).symm
  have hgr (p : ℤ) :
      QuasiIso ((FilteredObject.gr p).map (globalSectionsFilteredComplexMap X β ≫ e.hom)) := by
    rw [Functor.map_comp]
    have := FilteredComplexSpectralSequence.quasiIso_gr_map
      (globalSectionsFilteredComplexMap X β) p (hstep p) (hstep (p + 1))
    have : IsIso ((FilteredObject.gr p).map e.hom) :=
      (CategoryTheory.FilteredObject.gr p).map_isIso e.hom
    infer_instance
  have := FilteredComplexSpectralSequence.isIso_filteredSpectralSequenceMap_hom_one
    (globalSectionsFilteredComplexMap X β ≫ e.hom) hgr
  have hiso : IsIso (CategoryTheory.SpectralSequence.shiftStartMap
      (CochainComplex.filteredSpectralSequenceMap
        (globalSectionsFilteredComplexMap X β ≫ e.hom)) (show (0 : ℤ) ≤ 1 by omega)) :=
    CategoryTheory.SpectralSequence.isIso_of_isIso_hom _ (by assumption)
  exact ⟨@asIso _ _ _ _ _ hiso⟩

/-- **The brutal truncation spectral sequence of a bounded below filtered injective package is
the first spectral sequence of a Cartan-Eilenberg resolution.**

For a bounded below complex `F^•` of `O_X`-modules, a brutal-truncation package `S` whose
replacement is bounded below in degree `a` (`hge`) and filtered injective in every degree
(`hinj`), and any Cartan-Eilenberg resolution `I^{•,•}` of `F^•`, the spectral sequence of `S` is
isomorphic to the first spectral sequence of the Cartan-Eilenberg resolution of
[Stacks, Tag 015J].  The proof applies
`nonempty_spectralSequence_iso_cartanEilenbergFirst_of_quasiIso_augmentation` with
`StacksDraft.CartanEilenbergResolutions.quasiIso_filteredTotalAugmentation_natTrans_app`. -/
@[ega "0 11.4.3" "'E = CE first sequence"]
theorem nonempty_spectralSequence_iso_cartanEilenbergFirst
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} (a : ℤ)
    (hF : F.IsStrictlyGE a)
    (S : StupidTruncationSpectralSequence X F)
    (hge : S.replacement.X.IsStrictlyGE a)
    (hinj : ∀ n, (CochainComplex.evalFil S.replacement n).IsFilteredInjective)
    (I : F.CartanEilenbergResolution) :
    Nonempty (S.spectralSequence ≅ cartanEilenbergFirstSpectralSequence X I) := by
  have := hasTotal_bicomplex I
  exact nonempty_spectralSequence_iso_cartanEilenbergFirst_of_quasiIso_augmentation X a S hge hinj
    I (fun p => quasiIso_filteredTotalAugmentation_natTrans_app I ⟨a, hF⟩ p)

/-- For a bounded below complex of module sheaves there is a brutal-truncation package whose
spectral sequence is bounded, converges to `H^{i + j}(X, F^•)`, *and* is isomorphic to the first
spectral sequence of every Cartan-Eilenberg resolution of `F^•`.

This is `exists_boundedBelowStupidTruncationSpectralSequence` with the comparison
`nonempty_spectralSequence_iso_cartanEilenbergFirst` added for the package it produces. It is a
statement about a package (`StupidTruncationSpectralSequence`), whose replacement need not be a
filtered K-injective resolution; the bounded below clauses of [Stacks, Tag 0FLK] for the spectral
sequence of [Stacks, Tag 0BKK] are
`exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst` and
`stupidTruncation_filteredKInjectiveResolution_spectralSequence`. -/
@[ega "0 11.4.3" "'E, T = RΓ, bdd below",
  ega "0 12.4.1" "'E abutment, absolute",
  ega "0 12.1.7" "boundedness"]
theorem exists_stupidTruncationSpectralSequence_iso_cartanEilenbergFirst
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (a : ℤ)
    (hF : F.IsStrictlyGE a) :
    ∃ S : StupidTruncationSpectralSequence X F,
      IsBounded S.spectralSequence ∧
      SpectralSequence.AbutsTo S.spectralSequence (fun n => hypercohomology X S.RΓ F n) ∧
      ∀ I : F.CartanEilenbergResolution,
        Nonempty (S.spectralSequence ≅ cartanEilenbergFirstSpectralSequence X I) := by
  obtain ⟨S, hge, -, hinj, hbdd, habuts⟩ :=
    exists_boundedBelowStupidTruncationSpectralSequence X F a hF
  exact ⟨S, hbdd, habuts, fun I =>
    nonempty_spectralSequence_iso_cartanEilenbergFirst X a hF S hge hinj I⟩

/-- **Stacks 0FLK, the bounded below case.** Let `F^•` be a bounded below complex of
`O_X`-modules. Then

1. the spectral sequence of [Stacks, Tag 0BKK] for the brutal truncation filtration
   `σ_{≥ p}F^•` can be constructed through Remark [Stacks, Tag 0BKL]: there is a filtered
   K-injective resolution `R` of `σ_{≥ •}F^•` which is bounded below, has a filtration finite in
   every degree and is filtered injective in every degree;
2. its spectral sequence `R.spectralSequence` (the 0BKK spectral sequence) has
   `E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p)`, is bounded and converges to
   `H^{i + j}(X, F^•)`;
3. it is isomorphic to the first spectral sequence of [Stacks, Tag 015J] of every
   Cartan-Eilenberg resolution of `F^•`.

Clause 2 holds for every filtered K-injective resolution of `σ_{≥ •}F^•`, by
`stupidTruncation_filteredKInjectiveResolution_spectralSequence`, and is restated here for the
resolution of clause 1. -/
@[stacks 0FLK "bounded below: the 0BKK spectral sequence of a filtered K-injective resolution of \
(F, σ_{≥p}F) built via Remark 0BKL has E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p), is \
bounded, converges to H^{p + q}(X, F), and is isomorphic to the first spectral sequence (Tag \
015J) of every Cartan-Eilenberg resolution of F"]
theorem exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (a : ℤ)
    (hF : F.IsStrictlyGE a)
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homotopySections
      (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    (hRΓ : RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))) :
    ∃ R : FilteredKInjectiveResolution X (CochainComplex.stupidTruncationFiltration F),
      R.obj.X.IsStrictlyGE a ∧ R.obj.filtration.IsDegreewiseFinite ∧
      (∀ n : ℤ, (CochainComplex.evalFil R.obj n).IsFilteredInjective) ∧
      (∀ p q : ℤ, Nonempty ((R.spectralSequence.page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).obj
          (RΓ.obj (((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj (F.X p))⟦(-p : ℤ)⟧)))) ∧
      (∀ p q : ℤ, Nonempty ((R.spectralSequence.page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) q).obj
          (RΓ.obj ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj (F.X p))))) ∧
      IsBounded R.spectralSequence ∧
      SpectralSequence.AbutsTo R.spectralSequence (fun n => hypercohomology X RΓ F n) ∧
      ∀ I : F.CartanEilenbergResolution,
        Nonempty (R.spectralSequence ≅ cartanEilenbergFirstSpectralSequence X I) := by
  have := hRΓ
  obtain ⟨R, hge, hfin, hinj⟩ := exists_boundedBelow_filteredKInjectiveResolution X
    (CochainComplex.stupidTruncationFiltration F) a hF
    (CochainComplex.stupidTruncationFiltration_isDegreewiseFinite F)
  obtain ⟨-, hR⟩ := stupidTruncation_filteredKInjectiveResolution_spectralSequence X F RΓ α hRΓ
  obtain ⟨hshift, he₁, hconv⟩ := hR R
  obtain ⟨hbdd, habuts⟩ := hconv a hF
  let S : StupidTruncationSpectralSequence X F :=
    .ofFirstPageIso hRΓ R.map R.quasiIso R.quasiIso_step R.quasiIso_gr
      (R.nonempty_firstPageIso RΓ α)
  exact ⟨R, hge, hfin, hinj, hshift, he₁, hbdd, habuts, fun I =>
    nonempty_spectralSequence_iso_cartanEilenbergFirst X a hF S hge hinj I⟩

end Stacks.Cohomology.FilteredComplex

end

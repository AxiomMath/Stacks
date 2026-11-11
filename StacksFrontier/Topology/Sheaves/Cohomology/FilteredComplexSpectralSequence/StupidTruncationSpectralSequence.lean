module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.StupidTruncation
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.HypercohomologySpectralSequence

/-!
# The spectral sequence of the brutal truncation filtration of a complex of sheaves

Let `(X, O_X)` be a ringed space and let `F^•` be a complex of `O_X`-modules. Filtering `F^•` by
its brutal (stupid) truncations, `F^pF^• = σ_{≥ p}F^•`, and feeding that filtered complex to the
spectral sequence of a filtered complex gives a cohomological spectral sequence `(E_r)_{r ≥ 1}`
with `d_r` of bidegree `(r, -r + 1)` and
```
E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p).
```
The brutal filtration is finite in every degree -- in degree `n` it is all of `F^n` for `p ≤ n`
and zero for `p > n` -- so for a bounded below `F^•` the spectral sequence can be built from a
bounded below filtered injective replacement, with no filtered K-injective resolution, and it is
bounded and converges to `H^{i + j}(X, F^•)`.

## Main definitions

* `Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence`: the brutal truncation
  filtration of a complex of module sheaves together with a filtered replacement computing its
  spectral sequence and the two descriptions of the first page.
* `Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence.spectralSequence`: the
  resulting spectral sequence, read from page one.
* `Stacks.Cohomology.FilteredComplex.FilteredKInjectiveResolution.spectralSequence`: the spectral
  sequence of [Stacks, Tag 0BKK] computed by a filtered K-injective resolution, read from page one.

## Main results

* `CochainComplex.stupidTruncationFiltration_isDegreewiseFinite`: the brutal truncation
  filtration is finite in every degree.
* `stupidTruncation_filteredKInjectiveResolution_spectralSequence` (namespace
  `Stacks.Cohomology.FilteredComplex`):
  [Stacks, Tag 0FLK] for the spectral sequence of [Stacks, Tag 0BKK] itself: the brutal truncation
  filtration has a filtered K-injective resolution, and for every such resolution the spectral
  sequence it computes has `E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p)` and, for `F^•`
  bounded below, is bounded and converges to `H^{i + j}(X, F^•)`.
* `Stacks.Cohomology.FilteredComplex.exists_stupidTruncationSpectralSequence`: a brutal
  truncation package exists for every complex of module sheaves.
* `Stacks.Cohomology.FilteredComplex.exists_boundedBelowStupidTruncationSpectralSequence`: for a
  bounded below complex it can be built from a bounded below filtered injective replacement
  whose filtration is finite in every degree and whose graded terms are injective, and it is
  **bounded** and **converges to `H^{i + j}(X, F^•)`**.

## Implementation notes

The two descriptions of the first page are the two sides of the source's equality
`H^{p + q}(X, F^p[-p]) = H^q(X, F^p)`, recorded as isomorphisms of modules. The passage between
them is the commutation of the derived global-sections functor with the shift, available because
a right-derived functor between triangulated categories commutes with the shift, together with
the shift sequence of the homology functor; this is the same route as the `e₁Iso` field of
`Stacks.Cohomology.FilteredComplex.CanonicalTruncationSpectralSequence`.

The spectral sequence of a `StupidTruncationSpectralSequence` is the filtered-complex spectral
sequence of the global sections of its filtered replacement, i.e. literally the one of
[Stacks, Tag 0BKK] for the brutal truncation filtration, read from page one because that is the
page at which the source's description starts.

**Clause (3) of [Stacks, Tag 0FLK] is formalized elsewhere.** The source also asserts, for a
bounded below `F^•`, that this spectral sequence *is equal to* the first spectral sequence of
Derived Categories, [Stacks, Tag 015J] — the Cartan–Eilenberg spectral sequence of the complex,
for the functor `RΓ(X, -)`. The declarations below construct the brutal-truncation spectral
sequence from a filtered K-injective (or, in the bounded below case, filtered injective)
replacement, whereas the 015J sequence is built from a Cartan–Eilenberg resolution; the
identification of the two is
`Stacks.Cohomology.FilteredComplex.nonempty_spectralSequence_iso_cartanEilenbergFirst` in the
module `CartanEilenbergComparison` of this directory
(`StacksDraft.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence`)
and cannot be stated here because the 015J side needs the total complex of a
Cartan–Eilenberg bicomplex, one import layer further on.

**Which declarations carry the tag.** A `StupidTruncationSpectralSequence` does not require its
replacement to be a filtered K-injective resolution, so its spectral sequence is not, as a
statement, the one of [Stacks, Tag 0BKK]. The Stacks tag 0FLK is therefore registered on
`stupidTruncation_filteredKInjectiveResolution_spectralSequence`, about the spectral sequence of
an arbitrary `FilteredKInjectiveResolution` of the brutal truncation filtration, and, for the
bounded below clauses (the construction through Remark 0BKL and the comparison with 015J), on
`exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst` in that file.

The degreewise finiteness of the brutal truncation filtration is stated here rather than in
`StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.StupidTruncation`, which does not
have the filtration-finiteness vocabulary of
`StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs` in scope.

## References

* [Stacks Project, Tag 0FLK](https://stacks.math.columbia.edu/tag/0FLK)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0BKL](https://stacks.math.columbia.edu/tag/0BKL)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open StacksDraft.StupidTruncation
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u

/-- **The brutal truncation filtration is finite in every degree**: in degree `n` the step
`σ_{≥ n}K^•` already exhausts `K^n`, and the step `σ_{≥ n + 1}K^•` vanishes there. -/
lemma CochainComplex.stupidTruncationFiltration_isDegreewiseFinite {C : Type*} [Category* C]
    [Abelian C] (K : CochainComplex C ℤ) :
    (CochainComplex.stupidTruncationFiltration K).filtration.IsDegreewiseFinite := by
  intro n
  refine ⟨n, n + 1, ?_, ?_⟩
  · rw [show ((CochainComplex.stupidTruncationFiltration K).filtration.ι.app (op n)).f n =
        (stupidTruncGEXIso K n n le_rfl).hom from ιStupidTruncGE_f K n n le_rfl]
    exact (stupidTruncGEXIso K n n le_rfl).isIso_hom
  · exact CochainComplex.isZero_of_isStrictlyGE
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE (n + 1))) (n + 1) n (by omega)

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

section Pages

variable (X : RingedSpace.{u, u})
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))

/-- `H^{p + q}(X, gr^pσ_{≥ •}F^•) = H^{p + q}(X, F^p[-p])`: the `p`-th graded piece of the brutal
truncation filtration represents `F^p[-p]`. -/
def stupidGradedPieceHypercohomologyIso
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (p q : ℤ) :
    hypercohomology X RΓ
        ((FilteredObject.gr p).obj (CochainComplex.stupidTruncationFiltration F)) (p + q) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).obj
        (RΓ.obj (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj (F.X p))⟦(-p : ℤ)⟧)) :=
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).mapIso
      (RΓ.mapIso (CochainComplex.stupidGradedPieceDerivedIso F p))

variable
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)

/-- `H^{p + q}(X, M[-p]) = H^q(X, M)`: the derived global-sections functor commutes with the
shift, and the homology functor absorbs it by renumbering. -/
def shiftHypercohomologyIso
    (hRΓ : RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (M : SheafOfModules.{u} (structureSheafRing X)) (p q : ℤ) :
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).obj
      (RΓ.obj (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)⟦(-p : ℤ)⟧)) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) q).obj
        (RΓ.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj M)) := by
  have : RΓ.CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift RΓ α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
  exact (DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).mapIso
        ((RΓ.commShiftIso (-p)).app _) ≪≫
    ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 0).shiftIso
        (-p) (p + q) q (by omega)).app _

end Pages

/-- **The spectral sequence of the brutal truncation filtration** `F^pF^• = σ_{≥ p}F^•` of a
complex of module sheaves: a derived global-sections functor, a filtered replacement of the
brutal truncation filtration computing the spectral sequence of [Stacks, Tag 0BKK], and the two
standard descriptions `E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p)` of its first page. -/
structure StupidTruncationSpectralSequence (X : RingedSpace.{u, u})
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) where
  /-- A derived global-sections functor used to compute hypercohomology. -/
  RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
  /-- The comparison from underived to derived global sections. -/
  α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ
  /-- The chosen functor really is the right-derived global-sections functor. -/
  isRightDerived : RΓ.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
  /-- A filtered replacement of the brutal truncation filtration, as in [Stacks, Tag 0BKK]. -/
  replacement : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))
  /-- The filtered quasi-isomorphism to the replacement. -/
  replacementMap : CochainComplex.stupidTruncationFiltration F ⟶ replacement
  /-- The underlying replacement map is a quasi-isomorphism. -/
  replacementMap_quasiIso : QuasiIso replacementMap.hom
  /-- Every filtration step is replaced quasi-isomorphically. -/
  replacementMap_step_quasiIso (p : ℤ) : QuasiIso (replacementMap.natTrans.app (op p))
  /-- Every associated graded piece is replaced quasi-isomorphically. -/
  replacementMap_gr_quasiIso (p : ℤ) : QuasiIso ((FilteredObject.gr p).map replacementMap)
  /-- `E_1^{p, q} = H^{p + q}(X, F^p[-p])`. -/
  e₁IsoShift (p q : ℤ) : Nonempty
    (((globalSectionsSpectralSequence X replacement).page 1 (by omega)).X (p, q) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).obj
        (RΓ.obj (((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj (F.X p))⟦(-p : ℤ)⟧)))
  /-- Equivalently, `E_1^{p, q} = H^q(X, F^p)`. -/
  e₁Iso (p q : ℤ) : Nonempty
    (((globalSectionsSpectralSequence X replacement).page 1 (by omega)).X (p, q) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) q).obj
        (RΓ.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X)) 0).obj (F.X p))))

/-- The spectral sequence of a brutal-truncation package, read from page one: the
filtered-complex spectral sequence of the global sections of its filtered replacement. -/
abbrev StupidTruncationSpectralSequence.spectralSequence {X : RingedSpace.{u, u}}
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (S : StupidTruncationSpectralSequence X F) :
    CohomologicalSpectralSequence (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 1 :=
  (globalSectionsSpectralSequence X S.replacement).shiftStart (by omega)

/-- Global sections on a ringed space has an everywhere-defined unbounded right-derived functor,
with its comparison from underived global sections. -/
private lemma exists_isRightDerivedFunctor_globalSections (X : RingedSpace.{u, u}) :
    ∃ (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
        DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
      (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶
        DerivedCategory.Qh ⋙ RΓ),
      RΓ.IsRightDerivedFunctor α
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  exact ⟨derivedSections (structureSheafRing X) (⊤ : Opens X.carrier),
    (homotopySections (structureSheafRing X) (⊤ : Opens X.carrier)).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)),
    inferInstance⟩

/-- Package a filtered replacement of the brutal truncation filtration, with the identification of
its first page with the hypercohomology of the graded pieces, as a
`StupidTruncationSpectralSequence`. -/
def StupidTruncationSpectralSequence.ofFirstPageIso {X : RingedSpace.{u, u}}
    {F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    {RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))}
    {α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶
      DerivedCategory.Qh ⋙ RΓ}
    (hRΓ : RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    {I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (i : CochainComplex.stupidTruncationFiltration F ⟶ I) (hi : QuasiIso i.hom)
    (hstep : ∀ p : ℤ, QuasiIso (i.natTrans.app (op p)))
    (hgr : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map i))
    (hfirst : ∀ p q : ℤ, Nonempty
      (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, q) ≅
        hypercohomology X RΓ
          ((FilteredObject.gr p).obj (CochainComplex.stupidTruncationFiltration F)) (p + q))) :
    StupidTruncationSpectralSequence X F where
  RΓ := RΓ
  α := α
  isRightDerived := hRΓ
  replacement := I
  replacementMap := i
  replacementMap_quasiIso := hi
  replacementMap_step_quasiIso := hstep
  replacementMap_gr_quasiIso := hgr
  e₁IsoShift p q := by
    obtain ⟨e⟩ := hfirst p q
    exact ⟨e ≪≫ stupidGradedPieceHypercohomologyIso X RΓ F p q⟩
  e₁Iso p q := by
    obtain ⟨e⟩ := hfirst p q
    exact ⟨e ≪≫ stupidGradedPieceHypercohomologyIso X RΓ F p q ≪≫
      shiftHypercohomologyIso X RΓ α hRΓ (F.X p) p q⟩

/-- For every complex of module sheaves on a ringed space there is a brutal-truncation package
`StupidTruncationSpectralSequence X F`, with `E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p)`.

The package does not require its replacement to be a filtered K-injective resolution, so this is
weaker than [Stacks, Tag 0FLK], which is about the spectral sequence of [Stacks, Tag 0BKK] built
from a filtered K-injective resolution; that statement is
`Stacks.Cohomology.FilteredComplex.stupidTruncation_filteredKInjectiveResolution_spectralSequence`.
The package produced here is built from such a resolution. -/
theorem exists_stupidTruncationSpectralSequence (X : RingedSpace.{u, u})
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    Nonempty (StupidTruncationSpectralSequence X F) := by
  obtain ⟨RΓ, α, hRΓ⟩ := exists_isRightDerivedFunctor_globalSections X
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  obtain ⟨J, j, -, hIStep, -, -, hKI, hKIStep, -, hKISubquot, hj, hjStep, -, hjSubquot⟩ :=
    Stacks.Injectives.exists_filtered_quasiIso_isKInjective
      (CochainComplex.stupidTruncationFiltration F)
  let R : FilteredKInjectiveResolution X (CochainComplex.stupidTruncationFiltration F) :=
    { obj := J, map := j, quasiIso := hj, quasiIso_step := hjStep
      quasiIso_gr := fun p => hjSubquot p (p + 1) (by omega)
      injective_step := hIStep, isKInjective := hKI, isKInjective_step := hKIStep
      isKInjective_gr := fun p => hKISubquot p (p + 1) (by omega) }
  exact ⟨.ofFirstPageIso hRΓ j hj hjStep (fun p => hjSubquot p (p + 1) (by omega))
    (R.nonempty_firstPageIso RΓ α)⟩

/-- If `F^•` is bounded below, there is a brutal-truncation package built through Remark
[Stacks, Tag 0BKL], from a bounded below filtered injective replacement whose filtration is finite
in every degree, whose spectral sequence is **bounded** and **converges to `H^{i + j}(X, F^•)`**.

This is a statement about a package (`StupidTruncationSpectralSequence`); the bounded below
clauses of [Stacks, Tag 0FLK] for the spectral sequence of [Stacks, Tag 0BKK] itself are
`Stacks.Cohomology.FilteredComplex.stupidTruncation_filteredKInjectiveResolution_spectralSequence`
and
`exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst`. -/
@[ega "0 11.4.3" "'E, T = RΓ, bdd below", ega "0 12.4.1" "'E abutment, absolute"]
theorem exists_boundedBelowStupidTruncationSpectralSequence (X : RingedSpace.{u, u})
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (a : ℤ)
    (hF : F.IsStrictlyGE a) :
    ∃ S : StupidTruncationSpectralSequence X F,
      S.replacement.X.IsStrictlyGE a ∧
      S.replacement.filtration.IsDegreewiseFinite ∧
      (∀ n : ℤ, (CochainComplex.evalFil S.replacement n).IsFilteredInjective) ∧
      IsBounded S.spectralSequence ∧
      SpectralSequence.AbutsTo S.spectralSequence
        (fun n => hypercohomology X S.RΓ F n) := by
  obtain ⟨RΓ, α, hRΓ⟩ := exists_isRightDerivedFunctor_globalSections X
  obtain ⟨I, i, hIge, hIfin, hIfilInj, hgr, hstep, hhom, -, hfirst, hbdd,
      Fil, hFil, -, hFilFinite, hinf, hinfIso⟩ :=
    exists_spectralSequence_of_boundedBelowFilteredComplex X RΓ α hRΓ
      (CochainComplex.stupidTruncationFiltration F) a hF
      (CochainComplex.stupidTruncationFiltration_isDegreewiseFinite F)
  refine ⟨.ofFirstPageIso hRΓ i hhom hstep hgr hfirst,
    hIge, hIfin, hIfilInj, hbdd, ?_⟩
  exact SpectralSequence.AbutsTo.shiftStart
    (E := globalSectionsSpectralSequence X I) ⟨hinf, Fil, hFil, hFilFinite, hinfIso⟩ (by omega)

/-- The spectral sequence of [Stacks, Tag 0BKK] computed by a filtered K-injective resolution `R`
of a filtered complex of module sheaves: the filtered-complex spectral sequence of the global
sections of `R`, read from page one. -/
abbrev FilteredKInjectiveResolution.spectralSequence {X : RingedSpace.{u, u}}
    {K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))}
    (R : FilteredKInjectiveResolution X K) :
    CohomologicalSpectralSequence (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 1 :=
  (globalSectionsSpectralSequence X R.obj).shiftStart (by omega)

/-- **Stacks 0FLK.** Let `F^•` be a complex of `O_X`-modules on a ringed space `X`, filtered by
its brutal truncations `F^pF^• = σ_{≥ p}F^•`. This filtered complex has a filtered K-injective
resolution, and for *every* filtered K-injective resolution `R` of it the spectral sequence of
[Stacks, Tag 0BKK] it computes (`R.spectralSequence`) has
`E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p)`, the cohomology being taken with respect to any
right-derived global-sections functor `RΓ`. If `F^•` is bounded below, this spectral sequence is
bounded and converges to `H^{i + j}(X, F^•)`.

The remaining bounded below assertions of the tag, that the sequence can be built through Remark
[Stacks, Tag 0BKL] and that it is the first spectral sequence of [Stacks, Tag 015J], are
`exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst`. -/
@[stacks 0FLK "for the spectral sequence of 0BKK computed by any filtered K-injective resolution \
of (F, σ_{≥p}F): existence of the resolution, E_1^{p, q} = H^{p + q}(X, F^p[-p]) = H^q(X, F^p), \
and, for F bounded below, boundedness and convergence to H^{p + q}(X, F). The construction via \
Remark 0BKL and the comparison with Tag 015J are \
exists_filteredKInjectiveResolution_stupidTruncation_iso_cartanEilenbergFirst"]
theorem stupidTruncation_filteredKInjectiveResolution_spectralSequence (X : RingedSpace.{u, u})
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    (hRΓ : RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))) :
    Nonempty (FilteredKInjectiveResolution X (CochainComplex.stupidTruncationFiltration F)) ∧
    ∀ R : FilteredKInjectiveResolution X (CochainComplex.stupidTruncationFiltration F),
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
      ∀ a : ℤ, F.IsStrictlyGE a →
        IsBounded R.spectralSequence ∧
        SpectralSequence.AbutsTo R.spectralSequence (fun n => hypercohomology X RΓ F n) := by
  have := hRΓ
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  refine ⟨?_, fun R => ⟨fun p q => ?_, fun p q => ?_, fun a hF => ?_⟩⟩
  · obtain ⟨J, j, -, hIStep, -, -, hKI, hKIStep, -, hKISubquot, hj, hjStep, -, hjSubquot⟩ :=
      Stacks.Injectives.exists_filtered_quasiIso_isKInjective
        (CochainComplex.stupidTruncationFiltration F)
    exact ⟨⟨J, j, hj, hjStep, fun p => hjSubquot p (p + 1) (by omega), hIStep, hKI, hKIStep,
      fun p => hKISubquot p (p + 1) (by omega)⟩⟩
  · obtain ⟨e⟩ := R.nonempty_firstPageIso RΓ α p q
    exact ⟨e ≪≫ stupidGradedPieceHypercohomologyIso X RΓ F p q⟩
  · obtain ⟨e⟩ := R.nonempty_firstPageIso RΓ α p q
    exact ⟨e ≪≫ stupidGradedPieceHypercohomologyIso X RΓ F p q ≪≫
      shiftHypercohomologyIso X RΓ α hRΓ (F.X p) p q⟩
  · obtain ⟨R₀, -, hfin, -⟩ := exists_boundedBelow_filteredKInjectiveResolution X
      (CochainComplex.stupidTruncationFiltration F) a hF
      (CochainComplex.stupidTruncationFiltration_isDegreewiseFinite F)
    obtain ⟨hzero, hiso⟩ := R₀.hypercohomology_bounds_of_isDegreewiseFinite RΓ α hfin
    obtain ⟨hbdd, Fil, hFil, -, hFilFinite, hinf, hinfIso⟩ := R.converges RΓ α hzero hiso
    exact ⟨hbdd, SpectralSequence.AbutsTo.shiftStart (E := globalSectionsSpectralSequence X R.obj)
      ⟨hinf, Fil, hFil, hFilFinite, hinfIso⟩ (by omega)⟩

end Stacks.Cohomology.FilteredComplex

end

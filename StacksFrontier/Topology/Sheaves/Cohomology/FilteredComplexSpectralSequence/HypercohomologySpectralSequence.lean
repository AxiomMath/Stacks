module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.CanonicalTruncation
public import StacksFrontier.Algebra.Homology.SpectralSequence.Renumbering
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredComplexSpectralSequence.FilteredKInjectiveResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hypercohomology spectral sequence of a complex of module sheaves

Let `(X, O_X)` be a ringed space. Filtering a complex `K^•` of `O_X`-modules by its canonical
truncations, `F^pK^• = τ_{≤ -p}K^•`, and feeding that filtered complex to the spectral sequence of
a filtered complex gives a cohomological spectral sequence with
```
E_1^{p, q} = H^{p + q}(X, H^{-p}(K^•)[p]) = H^{2p + q}(X, H^{-p}(K^•)).
```
Renumbering by `p = -j`, `q = i + 2j` turns it into a spectral sequence starting at page two whose
differentials have bidegree `(r, -r + 1)` and whose second page is
```
E_2^{i, j} = H^i(X, H^j(K)).
```

## Main definitions

* `Stacks.Cohomology.FilteredComplex.globalSectionsSpectralSequence`: the filtered-complex
  spectral sequence of the complex of global sections of a filtered complex of module sheaves.
* `Stacks.Cohomology.FilteredComplex.CanonicalTruncationSpectralSequence`: the canonical
  truncation filtration of a complex of module sheaves together with its filtered K-injective
  replacement, the two descriptions of the first page of the resulting spectral sequence, and the
  convergence statement inherited from [Stacks, Tag 0BKK].
* `Stacks.Cohomology.FilteredComplex.HypercohomologySpectralSequence`: a representative of an
  object of the derived category together with its canonical truncation spectral sequence,
  renumbered to start at page two.
* `Stacks.Cohomology.FilteredComplex.hypercohomologySpectralSequence`: the canonical such datum.

## Main results

* `Stacks.Cohomology.FilteredComplex.exists_canonicalTruncationSpectralSequence`: the canonical
  truncation spectral sequence exists for every complex of module sheaves.
* `Stacks.Cohomology.FilteredComplex.exists_boundedBelowTruncationSpectralSequence`: for a
  bounded-below complex it can be built from a bounded-below filtered replacement whose
  filtration is finite in every degree and whose graded terms are injective.
* `Stacks.Cohomology.FilteredComplex.exists_spectralSequence_of_boundedBelowFilteredComplex`: for
  a bounded-below filtered complex with a degreewise finite filtration, the spectral sequence of
  [Stacks, Tag 0BKK] is computed by a bounded-below filtered injective resolution, with no
  filtered K-injective resolution.
* `Stacks.Cohomology.FilteredComplex.hypercohomologySpectralSequence_e₂`: the second page of the
  renumbered spectral sequence is the hypercohomology of the cohomology objects of `K`.
* `Stacks.Cohomology.FilteredComplex.exists_boundedBelowHypercohomologySpectralSequence`: **for a
  bounded-below complex the renumbered spectral sequence is bounded and converges to
  `H^{i + j}(X, K)`.**

## Implementation notes

The equalities of the source are recorded as isomorphisms of modules, and the spectral sequence is
not an arbitrary one with the given first page: it is identified, on every page, with the
filtered-complex spectral sequence of the global sections of the filtered K-injective replacement
occurring in [Stacks, Tag 0BKK].

The first-page identification is recorded twice, once against the hypercohomology of the graded
piece and once, after the truncation triangle and the shift convention, against the degree
`2p + q` cohomology of the degree `-p` cohomology object; both are needed by consumers.

The boundedness and convergence conclusion of [Stacks, Tag 0BKK] is about the *un-renumbered*
sequence: it is the `convergence` field of `CanonicalTruncationSpectralSequence`, and the
filtration it produces is indexed by the first coordinate `p` of the old bidegree. The closing
clause of [Stacks, Tag 0BKM] asserts it of the renumbered `E₂` sequence instead, where the
filtration of `H^n` is indexed by `i = p + n`. The two are related by
`CategoryTheory.SpectralSequence.AbutsTo.truncationRenumberRestrictPages` and
`CategoryTheory.SpectralSequence.truncationRenumber_finite_not_isZero_page_two`
(`StacksFrontier/Algebra/Homology/SpectralSequence/`), which transport abutment and degreewise
boundedness along the bidegree bijection; total degree is preserved, so the abutment family is
unchanged and only the filtration index is translated.

## References

* [Stacks Project, Tag 0BKM](https://stacks.math.columbia.edu/tag/0BKM)
* [Stacks Project, Tag 0BKK](https://stacks.math.columbia.edu/tag/0BKK)
* [Stacks Project, Tag 0BKL](https://stacks.math.columbia.edu/tag/0BKL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Pretriangulated
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe u

namespace Stacks.Cohomology.FilteredComplex

attribute [local instance] HasDerivedCategory.standard

/-- The filtered-complex spectral sequence of the complex of global sections of a filtered
complex of module sheaves on a ringed space. -/
abbrev globalSectionsSpectralSequence (X : RingedSpace.{u, u})
    (J : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) :
    CohomologicalSpectralSequence (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 0 :=
  CochainComplex.Filtered.spectralSequenceFunctor.obj (globalSectionsFilteredComplex X J)

/-- **The spectral sequence of the canonical truncation filtration** `F^pK^• = τ_{≤ -p}K^•` of a
complex of module sheaves, together with the filtered K-injective replacement computing it, the
two standard descriptions of its first page, and the convergence statement of
[Stacks, Tag 0BKK]. -/
structure CanonicalTruncationSpectralSequence (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) where
  /-- A derived global-sections functor used to compute hypercohomology. -/
  RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
  /-- The comparison from underived to derived global sections. -/
  α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ
  /-- The chosen functor really is the right-derived global-sections functor. -/
  isRightDerived : RΓ.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
  /-- The complex equipped with its canonical truncation filtration. -/
  filtered : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))
  /-- The underlying complex of the filtration is the given complex. -/
  underlyingIso : filtered.X ≅ K
  /-- The `p`-th filtration step is `τ_{≤ -p}K^•`. -/
  stepIso (p : ℤ) : filtered.filtration.obj (op p) ≅ K.truncLE (-p)
  /-- The step identifications commute with the inclusions into `K^•`. -/
  stepIso_hom_comp (p : ℤ) :
    (stepIso p).hom ≫ K.ιTruncLE (-p) =
      filtered.filtration.ι.app (op p) ≫ underlyingIso.hom
  /-- The `p`-th graded piece represents `H^{-p}(K^•)[p]`. -/
  gradedPieceIso (p : ℤ) :
    DerivedCategory.Q.obj ((FilteredObject.gr p).obj filtered) ≅
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
        ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) (-p)).obj
          (DerivedCategory.Q.obj K)))⟦p⟧
  /-- A filtered injective replacement, as in [Stacks, Tag 0BKK]. -/
  injectiveReplacement : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))
  /-- The filtered quasi-isomorphism to the injective replacement. -/
  replacementMap : filtered ⟶ injectiveReplacement
  /-- The underlying replacement map is a quasi-isomorphism. -/
  replacementMap_quasiIso : QuasiIso replacementMap.hom
  /-- Every filtration step is replaced quasi-isomorphically. -/
  replacementMap_step_quasiIso (p : ℤ) : QuasiIso (replacementMap.natTrans.app (op p))
  /-- Every associated graded piece is replaced quasi-isomorphically. -/
  replacementMap_gr_quasiIso (p : ℤ) : QuasiIso ((FilteredObject.gr p).map replacementMap)
  /-- The replacement is termwise injective. -/
  injective_terms (n : ℤ) : Injective (injectiveReplacement.X.X n)
  /-- Every filtration step of the replacement is termwise injective. -/
  injective_step_terms (p n : ℤ) : Injective ((injectiveReplacement.filtration.obj (op p)).X n)
  /-- Every graded piece of the replacement is termwise injective. -/
  injective_gr_terms (p n : ℤ) :
    Injective (((FilteredObject.gr p).obj injectiveReplacement).X n)
  /-- The first page is the hypercohomology of the graded pieces. -/
  e₁IsoGraded (p q : ℤ) : Nonempty
    (((globalSectionsSpectralSequence X injectiveReplacement).page 1 (by omega)).X (p, q) ≅
      hypercohomology X RΓ ((FilteredObject.gr p).obj filtered) (p + q))
  /-- Equivalently, `E_1^{p, q}` is the degree `2p + q` cohomology of the degree `-p` cohomology
  object of `K^•`. -/
  e₁Iso (p q : ℤ) : Nonempty
    (((globalSectionsSpectralSequence X injectiveReplacement).page 1 (by omega)).X (p, q) ≅
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (2 * p + q)).obj
          (RΓ.obj ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            ((DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) (-p)).obj
              (DerivedCategory.Q.obj K)))))
  /-- The boundedness and convergence conclusion of [Stacks, Tag 0BKK], available whenever its
  two filtration hypotheses hold. -/
  convergence :
    (∀ n : ℤ, ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (hypercohomology X RΓ (filtered.filtration.obj (op p)) n)) →
    (∀ n : ℤ, ∃ p₁ : ℤ, ∀ p : ℤ, p ≤ p₁ →
      IsIso (hypercohomologyMap X RΓ (filtered.filtration.ι.app (op p)) n)) →
    (∀ n : ℤ, {p : ℤ | ¬ IsZero
      (((globalSectionsSpectralSequence X injectiveReplacement).page 1
        (by omega)).X (p, n - p))}.Finite) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ filtered.X n))
        (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n p : ℤ, F n p = imageSubobject
          (hypercohomologyMap X RΓ (filtered.filtration.ι.app (op p)) n)) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
        (∀ p q : ℤ,
          (globalSectionsSpectralSequence X injectiveReplacement).HasPageInfinityAt (p, q)) ∧
        ∀ p q : ℤ, Nonempty
          ((globalSectionsSpectralSequence X injectiveReplacement).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega))))

/-- The spectral sequence of a canonical-truncation package: the filtered-complex spectral
sequence of the global sections of its filtered K-injective replacement. -/
abbrev CanonicalTruncationSpectralSequence.spectralSequence
    {X : RingedSpace.{u, u}} {K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (S : CanonicalTruncationSpectralSequence X K) :
    CohomologicalSpectralSequence (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 0 :=
  globalSectionsSpectralSequence X S.injectiveReplacement

/-- The first page of the spectral sequence of a filtered complex is the cohomology of its
graded pieces. -/
@[ega "0 11.2.2" "partial", sga "4 Vbis 2.5.2" "(X)"]
private lemma nonempty_firstPage_iso_gradedPiece_homology
    {A : Type*} [Category* A] [Abelian A] (M : CochainComplex.Filtered A) (p q : ℤ) :
    Nonempty (((CochainComplex.Filtered.spectralSequenceFunctor.obj M).page 1
        (by omega)).X (p, q) ≅ ((FilteredObject.gr p).obj M).homology (p + q)) := by
  obtain ⟨_, _, _, h⟩ := FilteredComplexSpectralSequence.exists_iso_gradedPiece_zeroPage
    M (CochainComplex.filtrationSubobject M) (fun _ _ => rfl)
    (CochainComplex.filtrationSubobject_antitone M)
  exact h p q (p + q) rfl

/-- **Stacks 0BKM.** For every complex of modules on a ringed space, the canonical truncation
filtration gives a spectral sequence with
`E_1^{p, q} = H^{p + q}(X, H^{-p}(K^•)[p]) = H^{2p + q}(X, H^{-p}(K^•))`. -/
@[stacks 0BKM "truncation_e1_page"]
theorem exists_canonicalTruncationSpectralSequence (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    Nonempty (CanonicalTruncationSpectralSequence X K) := by
  let F := CochainComplex.canonicalTruncationFiltration K
  obtain ⟨RΓ, α, hR, hrest⟩ := exists_spectralSequence_of_filteredComplex X F
  obtain ⟨J, j, hj, hjstep, hjgr, hinj, hinjstep, hinjgr, hrest⟩ := hrest
  obtain ⟨E, F₀, Z, D, hF, hZ, hD, hrest⟩ := hrest
  obtain ⟨he, hfirst, hconv⟩ := hrest
  obtain ⟨e, -⟩ := he
  have hcycles : ∀ r p n : ℤ,
      FilteredComplexSpectralSequence.cycles (globalSectionsFilteredComplex X J).X
        (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J)) r p n =
        Z r p n := by
    intro r p n
    simp only [FilteredComplexSpectralSequence.cycles, CochainComplex.filtrationSubobject]
    rw [← hF p n, ← hF (p + r) (n + 1), ← hZ r p n]
  have hboundaries : ∀ r p n : ℤ,
      FilteredComplexSpectralSequence.boundaries (globalSectionsFilteredComplex X J).X
        (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J)) r p n =
        D r p n := by
    intro r p n
    rw [FilteredComplexSpectralSequence.boundaries, hD r p n,
      hcycles (r - 1) (p + 1) n, hcycles (r - 1) (p - r + 1) (n - 1)]
  have hpage (r p q : ℤ) (hr : 0 ≤ r) :
      ((globalSectionsSpectralSequence X J).page r hr).X (p, q) ≅ (E.page r hr).X (p, q) := by
    have eJ' : FilteredComplexSpectralSequence.pageObj (globalSectionsFilteredComplex X J).X
        (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J)) r p (p + q) ≅
        cokernel (Subobject.ofLE (D r p (p + q) ⊓ Z r p (p + q)) (Z r p (p + q))
          inf_le_right) := by
      change cokernel (Subobject.ofLE
        (FilteredComplexSpectralSequence.boundaries (globalSectionsFilteredComplex X J).X
            (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J))
            r p (p + q) ⊓
          FilteredComplexSpectralSequence.cycles (globalSectionsFilteredComplex X J).X
            (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J))
            r p (p + q))
        (FilteredComplexSpectralSequence.cycles (globalSectionsFilteredComplex X J).X
          (CochainComplex.filtrationSubobject (globalSectionsFilteredComplex X J))
          r p (p + q)) inf_le_right) ≅ _
      rw [hboundaries r p (p + q), hcycles r p (p + q)]
    exact CochainComplex.Filtered.pageIso (globalSectionsFilteredComplex X J) r p q hr ≪≫
      eJ' ≪≫ (e r p q (p + q) hr rfl).symm
  have hFirst (p q : ℤ) : Nonempty
      (((globalSectionsSpectralSequence X J).page 1 (by omega)).X (p, q) ≅
        hypercohomology X RΓ ((FilteredObject.gr p).obj F) (p + q)) := by
    obtain ⟨eH⟩ := hfirst p q
    exact ⟨hpage 1 p q (by omega) ≪≫ eH⟩
  refine ⟨{
    RΓ := RΓ
    α := α
    isRightDerived := hR
    filtered := F
    underlyingIso := Iso.refl _
    stepIso := fun _ => Iso.refl _
    stepIso_hom_comp := fun p => by
      change 𝟙 (K.truncLE (-p)) ≫ K.ιTruncLE (-p) = K.ιTruncLE (-p) ≫ 𝟙 K
      simp
    gradedPieceIso := fun p => CochainComplex.canonicalGradedPieceIso K p (-p) rfl
    injectiveReplacement := J
    replacementMap := j
    replacementMap_quasiIso := hj
    replacementMap_step_quasiIso := hjstep
    replacementMap_gr_quasiIso := hjgr
    injective_terms := hinj
    injective_step_terms := hinjstep
    injective_gr_terms := hinjgr
    e₁IsoGraded := hFirst
    e₁Iso := fun p q => by
      obtain ⟨eGraded⟩ := hFirst p q
      have : RΓ.CommShift ℤ :=
        Functor.IsRightDerivedFunctor.commShift RΓ α
          (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)) ℤ
      exact ⟨eGraded ≪≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).mapIso
          (RΓ.mapIso (CochainComplex.canonicalGradedPieceIso K p (-p) rfl)) ≪≫
        (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).mapIso
          ((RΓ.commShiftIso p).app _) ≪≫
        ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 0).shiftIso p (p + q)
          (2 * p + q) (by omega)).app _⟩
    convergence := by
      intro hzero hiso
      obtain ⟨hfin, F', hanti, hF', hfinite, hstable, hEinf⟩ := hconv hzero hiso
      have hfin' : ∀ n : ℤ, {p : ℤ | ¬ IsZero
          (((globalSectionsSpectralSequence X J).page 1 (by omega)).X (p, n - p))}.Finite := by
        intro n
        refine (hfin n).subset fun p hp hz => ?_
        exact hp (IsZero.of_iso hz (hpage 1 p (n - p) (by omega)))
      refine ⟨hfin', F', hanti, hF', hfinite,
        fun p q => SpectralSequence.hasPageInfinityAt_of_finite_page _ 1 (by omega) hfin'
          (p, q), ?_⟩
      intro p q
      obtain ⟨einf⟩ := hEinf p q
      have : E.HasPageInfinityAt (p, q) := hstable p q
      have : (globalSectionsSpectralSequence X J).HasPageInfinityAt (p, q) :=
        SpectralSequence.hasPageInfinityAt_of_finite_page _ 1 (by omega) hfin' (p, q)
      set r := max (E.rMin (p, q)) ((globalSectionsSpectralSequence X J).rMin (p, q)) with hrdef
      have hrE : E.rMin (p, q) ≤ r := le_max_left _ _
      have hrE' : (globalSectionsSpectralSequence X J).rMin (p, q) ≤ r := le_max_right _ _
      have : E.HasEdgeMonoAtFrom (p, q) r := ⟨(E.rToMin_LE_rMin (p, q)).trans hrE⟩
      have : E.HasEdgeEpiAtFrom (p, q) r := ⟨(E.rFromMin_LE_rMin (p, q)).trans hrE⟩
      have : (globalSectionsSpectralSequence X J).HasEdgeMonoAtFrom (p, q) r :=
        ⟨((globalSectionsSpectralSequence X J).rToMin_LE_rMin (p, q)).trans hrE'⟩
      have : (globalSectionsSpectralSequence X J).HasEdgeEpiAtFrom (p, q) r :=
        ⟨((globalSectionsSpectralSequence X J).rFromMin_LE_rMin (p, q)).trans hrE'⟩
      exact ⟨(globalSectionsSpectralSequence X J).pageInfinityIso (p, q) r ≪≫
        hpage r p q ((globalSectionsSpectralSequence X J).le₀_of_hasEdgeEpiAtFrom (p, q) r) ≪≫
        (E.pageInfinityIso (p, q) r).symm ≪≫ einf⟩ }⟩

/-- A filtration step with zero degree-`n` term is `⊥` in degree `n`, as a subobject. -/
private lemma filtrationSubobject_eq_bot_of_isZero {A : Type*} [Category* A] [Abelian A]
    (M : CochainComplex.Filtered A) (p n : ℤ) (h : IsZero ((M.filtration.obj (op p)).X n)) :
    CochainComplex.filtrationSubobject M p n = ⊥ := by
  change Subobject.mk ((M.filtration.ι.app (op p)).f n) = ⊥
  rw [Subobject.mk_eq_bot_iff_zero]
  exact h.eq_of_src _ _

/-- A degreewise finite filtration of a complex is degreewise everything for `p ≪ 0` and zero
for `p ≫ 0`. -/
private lemma finiteFilteredComplex_bounds {A : Type*} [Category* A] [Abelian A]
    (M : CochainComplex.Filtered A) (hM : M.filtration.IsDegreewiseFinite) :
    (∀ n : ℤ, ∃ a : ℤ, ∀ p : ℤ, p ≤ a → IsIso ((M.filtration.ι.app (op p)).f n)) ∧
    ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → IsZero ((M.filtration.obj (op p)).X n) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · obtain ⟨a, _, ha, _⟩ := hM n
    refine ⟨a, fun p hp => ?_⟩
    have hFa : CochainComplex.filtrationSubobject M a n = ⊤ :=
      (Subobject.isIso_iff_mk_eq_top _).1 ha
    exact (Subobject.isIso_iff_mk_eq_top _).2
      (top_le_iff.mp (hFa ▸ CochainComplex.filtrationSubobject_antitone M p a n hp))
  · obtain ⟨_, b, _, hb⟩ := hM n
    refine ⟨b, fun p hp => ?_⟩
    have hFb := filtrationSubobject_eq_bot_of_isZero M b n hb
    exact IsZero.of_mono_eq_zero ((M.filtration.ι.app (op p)).f n) (Subobject.mk_eq_bot_iff_zero.1
      (le_bot_iff.mp ((CochainComplex.filtrationSubobject_antitone M b p n hp).trans hFb.le)))

/-- A degreewise finite filtration satisfies the two cohomological hypotheses of
[Stacks, Tag 0BK5]. -/
private lemma finiteFilteredComplex_homology_bounds {A : Type*} [Category* A] [Abelian A]
    (M : CochainComplex.Filtered A) (hM : M.filtration.IsDegreewiseFinite) :
    (∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → IsZero ((M.filtration.obj (op p)).homology n)) ∧
    ∀ n : ℤ, ∃ a : ℤ, ∀ p : ℤ, p ≤ a →
      IsIso (HomologicalComplex.homologyMap (M.filtration.ι.app (op p)) n) := by
  obtain ⟨htop, hbot⟩ := finiteFilteredComplex_bounds M hM
  refine ⟨fun n => ?_, fun n => ?_⟩
  · obtain ⟨b, hb⟩ := hbot n
    exact ⟨b, fun p hp => ShortComplex.isZero_homology_of_isZero_X₂ _ (hb p hp)⟩
  · obtain ⟨a₁, ha₁⟩ := htop (n - 1)
    obtain ⟨a₂, ha₂⟩ := htop n
    obtain ⟨a₃, ha₃⟩ := htop (n + 1)
    exact ⟨min a₁ (min a₂ a₃), fun p hp =>
      CochainComplex.isIso_homologyMap_of_isIso_f (M.filtration.ι.app (op p)) n
        (ha₁ p (by omega)) (ha₂ p (by omega)) (ha₃ p (by omega))⟩

/-- A degreewise finite filtration is degreewise eventually `⊤` on the left and `⊥` on the right
as a filtration by subobjects. -/
private lemma finiteFilteredComplex_subobject_bounds {A : Type*} [Category* A] [Abelian A]
    (M : CochainComplex.Filtered A) (hM : M.filtration.IsDegreewiseFinite) :
    (∀ n : ℤ, ∃ a : ℤ, ∀ p : ℤ, p ≤ a → CochainComplex.filtrationSubobject M p n = ⊤) ∧
    ∀ n : ℤ, ∃ b : ℤ, ∀ p : ℤ, b ≤ p → CochainComplex.filtrationSubobject M p n = ⊥ := by
  obtain ⟨htop, hbot⟩ := finiteFilteredComplex_bounds M hM
  refine ⟨fun n => ?_, fun n => ?_⟩
  · obtain ⟨a, ha⟩ := htop n
    exact ⟨a, fun p hp => (Subobject.isIso_iff_mk_eq_top _).1 (ha p hp)⟩
  · obtain ⟨b, hb⟩ := hbot n
    exact ⟨b, fun p hp => filtrationSubobject_eq_bot_of_isZero M p n (hb p hp)⟩

/-- Once the filtration is `⊥` in degree `n + 1` and `⊤` in degree `n - 1` at the relevant
indices, the cycles and boundaries of the filtered-complex spectral sequence have reached their
stable values. -/
private lemma filteredComplex_cycles_boundaries_stabilize
    {A : Type*} [Category* A] [Abelian A] (M : CochainComplex.Filtered A) (r p n : ℤ)
    (hhi : CochainComplex.filtrationSubobject M (p + r) (n + 1) = ⊥)
    (hlo : CochainComplex.filtrationSubobject M (p - r + 1) (n - 1) = ⊤) :
    FilteredComplexSpectralSequence.cycles M.X (CochainComplex.filtrationSubobject M) r p n =
      kernelSubobject (M.X.d n (n + 1)) ⊓ CochainComplex.filtrationSubobject M p n ∧
    FilteredComplexSpectralSequence.boundaries M.X
        (CochainComplex.filtrationSubobject M) r p n =
      kernelSubobject (M.X.d n (n + 1)) ⊓ CochainComplex.filtrationSubobject M (p + 1) n ⊔
        imageSubobject (M.X.d (n - 1) n) ⊓ CochainComplex.filtrationSubobject M p n := by
  constructor
  · rw [FilteredComplexSpectralSequence.cycles, hhi, Subobject.pullback_bot, inf_comm]
  · rw [FilteredComplexSpectralSequence.boundaries,
      FilteredComplexSpectralSequence.cycles, FilteredComplexSpectralSequence.cycles,
      show p + 1 + (r - 1) = p + r by ring, show n - 1 + 1 = n by ring,
      show p - r + 1 + (r - 1) = p by ring, hhi, hlo, Subobject.pullback_bot, top_inf_eq,
      Abelian.Subobject.exists_pullback_eq_inf,
      inf_comm (CochainComplex.filtrationSubobject M (p + 1) n),
      inf_comm (CochainComplex.filtrationSubobject M p n)]

/-- The canonical truncation filtration is finite in every degree: in degree `n` it is all of
`K^n` from `p = -(n + 1)` down and zero from `p = -(n - 1)` up. -/
lemma CanonicalTruncationSpectralSequence.isDegreewiseFinite {X : RingedSpace.{u, u}}
    {K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (S : CanonicalTruncationSpectralSequence X K) :
    S.filtered.filtration.IsDegreewiseFinite := by
  intro n
  refine ⟨-(n + 1), -(n - 1), ?_, ?_⟩
  · have heq := HomologicalComplex.congr_hom (S.stepIso_hom_comp (-(n + 1))) n
    simp only [HomologicalComplex.comp_f] at heq
    have : IsIso ((K.ιTruncLE (-(-(n + 1)))).f n) := by
      rw [show -(-(n + 1)) = n + 1 by omega]
      exact CochainComplex.isIso_ιTruncLE_f_of_lt K (n + 1) n (by omega)
    have hcomp : IsIso ((S.filtered.filtration.ι.app (op (-(n + 1)))).f n ≫
        S.underlyingIso.hom.f n) := by
      rw [← heq]
      infer_instance
    exact (isIso_comp_right_iff _ _).1 hcomp
  · have hzero : IsZero ((K.truncLE (-(-(n - 1)))).X n) := by
      simpa using (K.truncLE (n - 1)).isZero_of_isStrictlyLE (n - 1) n (by omega)
    exact IsZero.of_iso hzero
      ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso (S.stepIso (-(n - 1))))

/-- Global sections of a filtered complex with filtered-injective evaluations is the filtered
complex produced by the functorial construction of [Stacks, Tag 015W]. -/
private lemma globalSectionsFilteredComplex_eq_mapFilteredInjective (X : RingedSpace.{u, u})
    (I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))
    (hI : ∀ n, (CochainComplex.evalFil I n).IsFilteredInjective) :
    globalSectionsFilteredComplex X I =
      CochainComplex.mapFilteredInjective (SheafOfModules.evaluation (structureSheafRing X) (op ⊤))
        I hI :=
  rfl

/-- Equal morphisms have equal image subobjects. Stated separately because `rw` cannot rewrite
under `CategoryTheory.Limits.imageSubobject`: its `CategoryTheory.Limits.HasImage` instance
argument mentions the morphism, so the rewrite motive is not type correct. -/
private lemma imageSubobject_congr {C : Type*} [Category* C] [Abelian C] {A B : C} {f g : A ⟶ B}
    (h : f = g) : imageSubobject f = imageSubobject g := by
  subst h
  rfl

/-- The identification of hypercohomology with the cohomology of the complex of global sections,
read from global sections to hypercohomology, is compatible with maps of K-injective
complexes. -/
private lemma globalSectionsHomologyIsoHypercohomology_naturality (X : RingedSpace.{u, u})
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    {I J : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J) (n : ℤ) :
    HomologicalComplex.homologyMap ((globalSectionsComplexFunctor X).map f) n ≫
        (hypercohomologyIsoGlobalSectionsHomology X RΓ α J n).inv =
      (hypercohomologyIsoGlobalSectionsHomology X RΓ α I n).inv ≫
        hypercohomologyMap X RΓ f n :=
  (CommSq.mk (hypercohomologyIsoGlobalSectionsHomology_naturality X RΓ α f n)).vert_inv.w

/-- For a filtered replacement with filtered-injective evaluations and K-injective graded pieces,
the first page of the global-sections spectral sequence is the hypercohomology of the graded
pieces of the original filtered complex. -/
lemma boundedFilteredReplacement_firstPageIso (X : RingedSpace.{u, u})
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (K I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))
    (i : K ⟶ I)
    (hIfil : ∀ n, (CochainComplex.evalFil I n).IsFilteredInjective)
    (hKinj : ∀ p : ℤ, ((FilteredObject.gr p).obj I).IsKInjective)
    (hgr : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map i)) (p q : ℤ) :
    Nonempty (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, q) ≅
      hypercohomology X RΓ ((FilteredObject.gr p).obj K) (p + q)) := by
  have := hKinj p
  obtain ⟨e₁⟩ := nonempty_firstPage_iso_gradedPiece_homology
    (globalSectionsFilteredComplex X I) p q
  have eGr : (FilteredObject.gr p).obj (globalSectionsFilteredComplex X I) ≅
      (globalSectionsComplexFunctor X).obj ((FilteredObject.gr p).obj I) := by
    rw [globalSectionsFilteredComplex_eq_mapFilteredInjective X I hIfil]
    exact CochainComplex.gradedPieceMapFilteredInjectiveIso
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) I hIfil p
  have : IsIso (DerivedCategory.Q.map ((FilteredObject.gr p).map i)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hgr p)
  exact ⟨e₁ ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      (ComplexShape.up ℤ) (p + q)).mapIso eGr ≪≫
    (hypercohomologyIsoGlobalSectionsHomology X RΓ α
      ((FilteredObject.gr p).obj I) (p + q)).symm ≪≫
    (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (p + q)).mapIso
      (RΓ.mapIso (asIso (DerivedCategory.Q.map ((FilteredObject.gr p).map i))).symm)⟩

/-- For a filtered replacement with filtered-injective evaluations and K-injective graded pieces,
the first page of the global-sections spectral sequence is again the hypercohomology of the graded
pieces of the canonical truncation filtration. -/
private lemma boundedReplacement_e₁IsoGraded (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (S : CanonicalTruncationSpectralSequence X K)
    (I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))
    (i : S.filtered ⟶ I)
    (hIfil : ∀ n, (CochainComplex.evalFil I n).IsFilteredInjective)
    (hKinj : ∀ p : ℤ, ((FilteredObject.gr p).obj I).IsKInjective)
    (hgr : ∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map i)) (p q : ℤ) :
    Nonempty (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, q) ≅
      hypercohomology X S.RΓ ((FilteredObject.gr p).obj S.filtered) (p + q)) := by
  have := S.isRightDerived
  exact boundedFilteredReplacement_firstPageIso X S.RΓ S.α S.filtered I i hIfil hKinj hgr p q

/-- **Convergence for a bounded-below filtered replacement.** When the replacement has a
degreewise finite filtration and K-injective total complex and filtration steps, the
global-sections spectral sequence is bounded, the filtration induced on the hypercohomology of
the resolved complex is finite, and the infinity page is its associated graded. -/
lemma boundedFilteredReplacement_converges (X : RingedSpace.{u, u})
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))]
    (K I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))
    (i : K ⟶ I) (hIfin : I.filtration.IsDegreewiseFinite)
    (hIK : I.X.IsKInjective) (hIstepK : ∀ p : ℤ, (I.filtration.obj (op p)).IsKInjective)
    (hstep : ∀ p : ℤ, QuasiIso (i.natTrans.app (op p))) (hhom : QuasiIso i.hom) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero
      (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, n - p))}.Finite) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ K.X n))
        (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n p : ℤ, F n p = imageSubobject
          (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
        (∀ p q : ℤ, (globalSectionsSpectralSequence X I).HasPageInfinityAt (p, q)) ∧
        ∀ p q : ℤ, Nonempty
          ((globalSectionsSpectralSequence X I).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega)))) := by
  classical
  have hMfin : (globalSectionsFilteredComplex X I).filtration.IsDegreewiseFinite := by
    intro n
    obtain ⟨b, c, hb, hc⟩ := hIfin n
    refine ⟨b, c, ?_, ?_⟩
    · have : IsIso ((I.filtration.ι.app (op b)).f n) := hb
      exact inferInstanceAs (IsIso ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).map
        ((I.filtration.ι.app (op b)).f n)))
    · exact Functor.map_isZero (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)) hc
  obtain ⟨hzeroM, hisoM⟩ := finiteFilteredComplex_homology_bounds _ hMfin
  have : IsIso (DerivedCategory.Q.map i.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hhom
  have hQstep (p : ℤ) : IsIso (DerivedCategory.Q.map (i.natTrans.app (op p))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hstep p)
  have hHyperHom (n : ℤ) : IsIso (hypercohomologyMap X RΓ i.hom n) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).map
        (RΓ.map (DerivedCategory.Q.map i.hom))))
  have hHyperStep (p n : ℤ) :
      IsIso (hypercohomologyMap X RΓ (i.natTrans.app (op p)) n) :=
    inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).map
        (RΓ.map (DerivedCategory.Q.map (i.natTrans.app (op p))))))
  let φ (n : ℤ) : (globalSectionsFilteredComplex X I).X.homology n ≅
      hypercohomology X RΓ K.X n :=
    (hypercohomologyIsoGlobalSectionsHomology X RΓ α I.X n).symm ≪≫
      (asIso (hypercohomologyMap X RΓ i.hom n)).symm
  let ε (p n : ℤ) :
      ((globalSectionsFilteredComplex X I).filtration.obj (op p)).homology n ≅
        hypercohomology X RΓ (K.filtration.obj (op p)) n :=
    (hypercohomologyIsoGlobalSectionsHomology X RΓ α
        (I.filtration.obj (op p)) n).symm ≪≫
      (asIso (hypercohomologyMap X RΓ (i.natTrans.app (op p)) n)).symm
  have hNat (p n : ℤ) :
      HomologicalComplex.homologyMap
          ((globalSectionsFilteredComplex X I).filtration.ι.app (op p)) n ≫
        (hypercohomologyIsoGlobalSectionsHomology X RΓ α I.X n).inv =
      (hypercohomologyIsoGlobalSectionsHomology X RΓ α
          (I.filtration.obj (op p)) n).inv ≫
        hypercohomologyMap X RΓ (I.filtration.ι.app (op p)) n :=
    globalSectionsHomologyIsoHypercohomology_naturality X RΓ α
      (I := I.filtration.obj (op p)) (J := I.X) (I.filtration.ι.app (op p)) n
  have hHyperComm (p n : ℤ) :
      hypercohomologyMap X RΓ (i.natTrans.app (op p)) n ≫
          hypercohomologyMap X RΓ (I.filtration.ι.app (op p)) n =
        hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n ≫
          hypercohomologyMap X RΓ i.hom n := by
    simp only [hypercohomologyMap, ← Functor.map_comp]
    rw [i.comm (op p)]
  have hCancel (p n : ℤ) :
      hypercohomologyMap X RΓ (I.filtration.ι.app (op p)) n ≫
          inv (hypercohomologyMap X RΓ i.hom n) =
        inv (hypercohomologyMap X RΓ (i.natTrans.app (op p)) n) ≫
          hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n := by
    rw [IsIso.comp_inv_eq, Category.assoc, ← hHyperComm p n, IsIso.inv_hom_id_assoc]
  have hComm (p n : ℤ) :
      HomologicalComplex.homologyMap
          ((globalSectionsFilteredComplex X I).filtration.ι.app (op p)) n ≫ (φ n).hom =
        (ε p n).hom ≫
          hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n :=
    (Category.assoc _ _ _).symm.trans <|
      (eq_whisker (hNat p n) _).trans <|
        (Category.assoc _ _ _).trans <|
          (whisker_eq _ (hCancel p n)).trans (Category.assoc _ _ _).symm
  let F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ K.X n) := fun n p =>
    imageSubobject (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)
  have hImage (n p : ℤ) : F n p = (Subobject.map (φ n).hom).obj
      ((globalSectionsFilteredComplex X I).inducedFiltrationStep n p) := by
    calc F n p
        = imageSubobject ((ε p n).hom ≫
            hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n) :=
          (imageSubobject_iso_comp (ε p n).hom _).symm
      _ = imageSubobject (HomologicalComplex.homologyMap
            ((globalSectionsFilteredComplex X I).filtration.ι.app (op p)) n ≫ (φ n).hom) :=
          imageSubobject_congr (hComm p n).symm
      _ = _ := (Subobject.map_imageSubobject _ (φ n)).symm
  have hAnti : ∀ n : ℤ, Antitone (F n) := by
    intro n p p' hpp'
    rw [hImage, hImage]
    exact (Subobject.map (φ n).hom).monotone
      ((globalSectionsFilteredComplex X I).inducedFiltrationStep_antitone n hpp')
  have hFinite : ∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥ := by
    intro n
    obtain ⟨b, hb⟩ := hzeroM n
    obtain ⟨c, hc⟩ := hisoM n
    refine ⟨min b c, max b c, min_le_max, ?_, ?_⟩
    · have htop : (globalSectionsFilteredComplex X I).inducedFiltrationStep n (min b c) = ⊤ := by
        have := hc (min b c) (min_le_right _ _)
        exact Subobject.imageSubobject_eq_top_of_epi _
      rw [hImage, htop]
      exact (Subobject.mapIsoToOrderIso (φ n)).map_top
    · have hz := hb (max b c) (le_max_left _ _)
      have hbot : (globalSectionsFilteredComplex X I).inducedFiltrationStep n (max b c) = ⊥ := by
        rw [show (globalSectionsFilteredComplex X I).inducedFiltrationStep n (max b c) =
            imageSubobject (HomologicalComplex.homologyMap
              ((globalSectionsFilteredComplex X I).filtration.ι.app (op (max b c))) n) from rfl,
          show HomologicalComplex.homologyMap
              ((globalSectionsFilteredComplex X I).filtration.ι.app (op (max b c))) n = 0 from
            hz.eq_of_src _ _, imageSubobject_zero]
      rw [hImage, hbot]
      exact (Subobject.mapIsoToOrderIso (φ n)).map_bot
  refine ⟨CochainComplex.Filtered.finite_not_isZero_page_one _ hzeroM hisoM, F, hAnti,
    fun _ _ => rfl, hFinite,
    fun p q => CochainComplex.Filtered.hasPageInfinityAt_of_eventually _ hzeroM hisoM (p, q), ?_⟩
  intro p q
  obtain ⟨egr⟩ := CochainComplex.Filtered.nonempty_pageInfinityIso_inducedFiltrationStep
    (globalSectionsFilteredComplex X I) hzeroM hisoM p q
  have hle : (globalSectionsFilteredComplex X I).inducedFiltrationStep (p + q) (p + 1) ≤
      (globalSectionsFilteredComplex X I).inducedFiltrationStep (p + q) p :=
    (globalSectionsFilteredComplex X I).inducedFiltrationStep_antitone (p + q) (by omega)
  have hIm (s : ℤ) : (Subobject.mapIsoToOrderIso (φ (p + q)))
      ((globalSectionsFilteredComplex X I).inducedFiltrationStep (p + q) s) = F (p + q) s :=
    (hImage (p + q) s).symm
  exact ⟨egr ≪≫ Subobject.cokernelMapIso (φ (p + q)) _ _ hle ≪≫
    Subobject.cokernelOfLEIsoOfEq
      ((Subobject.mapIsoToOrderIso (φ (p + q))).map_rel_iff'.2 hle)
      (hAnti (p + q) (by omega)) (hIm (p + 1)) (hIm p)⟩

/-- **Convergence for a bounded-below filtered replacement.** When the replacement has a
degreewise finite filtration and K-injective total complex and filtration steps, the
global-sections spectral sequence is bounded, the filtration induced on the hypercohomology of
the resolved complex is finite, and the infinity page is its associated graded. -/
private lemma boundedReplacement_convergence (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (S₀ : CanonicalTruncationSpectralSequence X K)
    (I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X)))
    (i : S₀.filtered ⟶ I) (hIfin : I.filtration.IsDegreewiseFinite)
    (hIK : I.X.IsKInjective) (hIstepK : ∀ p : ℤ, (I.filtration.obj (op p)).IsKInjective)
    (hstep : ∀ p : ℤ, QuasiIso (i.natTrans.app (op p))) (hhom : QuasiIso i.hom) :
    (∀ n : ℤ, {p : ℤ | ¬ IsZero
      (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, n - p))}.Finite) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X S₀.RΓ S₀.filtered.X n))
        (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n p : ℤ, F n p = imageSubobject
          (hypercohomologyMap X S₀.RΓ (S₀.filtered.filtration.ι.app (op p)) n)) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
        (∀ p q : ℤ, (globalSectionsSpectralSequence X I).HasPageInfinityAt (p, q)) ∧
        ∀ p q : ℤ, Nonempty
          ((globalSectionsSpectralSequence X I).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega)))) := by
  have := S₀.isRightDerived
  exact boundedFilteredReplacement_converges X S₀.RΓ S₀.α S₀.filtered I i hIfin hIK hIstepK
    hstep hhom

/-- If every degree of a filtered complex is eventually one of its filtration steps, injectivity of
the terms of the steps gives injectivity of the terms of the complex. -/
private lemma injective_X_of_isDegreewiseFinite {A : Type*} [Category* A] [Abelian A]
    (I : CochainComplex.Filtered A) (hIfin : I.filtration.IsDegreewiseFinite)
    (hIstepInj : ∀ p n : ℤ, Injective ((I.filtration.obj (op p)).X n)) (n : ℤ) :
    Injective (I.X.X n) := by
  obtain ⟨p, -, hp, -⟩ := hIfin n
  exact Injective.of_iso (asIso ((I.filtration.ι.app (op p)).f n)) (hIstepInj p n)

/-- The filtration steps of a bounded-below filtered complex with termwise injective steps are
K-injective. -/
private lemma isKInjective_filtration_obj_of_injective {A : Type*} [Category* A] [Abelian A]
    (I : CochainComplex.Filtered A) (a : ℤ) [I.X.IsStrictlyGE a]
    (hIstepInj : ∀ p n : ℤ, Injective ((I.filtration.obj (op p)).X n)) (p : ℤ) :
    (I.filtration.obj (op p)).IsKInjective := by
  have : (I.filtration.obj (op p)).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro m hm
    exact (I.X.isZero_of_isStrictlyGE a m hm).of_mono ((I.filtration.ι.app (op p)).f m)
  have (m : ℤ) := hIstepInj p m
  exact CochainComplex.isKInjective_of_injective _ a

/-- **Stacks 0BKL.** Let `(X, O_X)` be a ringed space and let `K^•` be a filtered complex of
`O_X`-modules which is bounded below and whose filtration is finite in each degree. Then the
spectral sequence of [Stacks, Tag 0BKK] can be built without a filtered K-injective resolution:
a filtered quasi-isomorphism `i : K^• ⟶ I^•` as in [Stacks, Tag 05TW], with `I^•` bounded below,
the filtration on each `I^n` finite and each `gr^pI^n` injective, gives the filtered complex
`Γ(X, I^•)` with `F^pΓ(X, I^•) = Γ(X, F^pI^•)`, whose spectral sequence has first page
`E_1^{p, q} = H^{p + q}(X, gr^pK^•)` and is bounded and converges to `H^*(X, K^•)` with a finite
induced filtration. -/
@[stacks 0BKL, ega "0 13.7.3" "ringed space, bdd below"]
theorem exists_spectralSequence_of_boundedBelowFilteredComplex (X : RingedSpace.{u, u})
    (RΓ : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))))
    (α : homotopySections (structureSheafRing X) (⊤ : Opens X.carrier) ⟶ DerivedCategory.Qh ⋙ RΓ)
    (hRΓ : RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)))
    (K : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (a : ℤ)
    (hK : K.X.IsStrictlyGE a) (hKfin : K.filtration.IsDegreewiseFinite) :
    ∃ (I : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (i : K ⟶ I),
      I.X.IsStrictlyGE a ∧
      I.filtration.IsDegreewiseFinite ∧
      (∀ n : ℤ, (CochainComplex.evalFil I n).IsFilteredInjective) ∧
      (∀ p : ℤ, QuasiIso ((FilteredObject.gr p).map i)) ∧
      (∀ p : ℤ, QuasiIso (i.natTrans.app (op p))) ∧
      QuasiIso i.hom ∧
      (∀ p : ℤᵒᵖ, (globalSectionsFilteredComplex X I).filtration.obj p =
        (globalSectionsComplexFunctor X).obj (I.filtration.obj p)) ∧
      (∀ p q : ℤ, Nonempty
        (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, q) ≅
          hypercohomology X RΓ ((FilteredObject.gr p).obj K) (p + q))) ∧
      (∀ n : ℤ, {p : ℤ | ¬ IsZero
        (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, n - p))}.Finite) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (hypercohomology X RΓ K.X n))
        (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n p : ℤ, F n p = imageSubobject
          (hypercohomologyMap X RΓ (K.filtration.ι.app (op p)) n)) ∧
        (∀ n : ℤ, ∃ b c : ℤ, b ≤ c ∧ F n b = ⊤ ∧ F n c = ⊥) ∧
        (∀ p q : ℤ, (globalSectionsSpectralSequence X I).HasPageInfinityAt (p, q)) ∧
        ∀ p q : ℤ, Nonempty
          ((globalSectionsSpectralSequence X I).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by omega)))) := by
  have := hRΓ
  have := hK
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  have : EnoughInjectives (SheafOfModules.{u} (structureSheafRing X)) := inferInstance
  obtain ⟨I, i, hqi, -, -, hIge, hIfilInj⟩ :=
    CochainComplex.exists_mono_isStrictHom_filteredQuasiIso_isStrictlyGE_injective_gradedPiece
      K a hKfin
  have hIfin : I.filtration.IsDegreewiseFinite := fun n =>
    ((CochainComplex.isFilteredInjective_evalFil_iff I n).1 (hIfilInj n)).1
  have hIgrInj : ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj I).X n) :=
    fun p n => ((CochainComplex.isFilteredInjective_evalFil_iff I n).1 (hIfilInj n)).2 p
  have hIgrKinj (p : ℤ) : ((FilteredObject.gr p).obj I).IsKInjective := by
    have := hIge
    have := CochainComplex.isStrictlyGE_gr I a p
    have (n : ℤ) := hIgrInj p n
    exact CochainComplex.isKInjective_of_injective _ a
  have hIstepInj (p n : ℤ) : Injective ((I.filtration.obj (op p)).X n) :=
    CochainComplex.injective_filtration_obj_X_of_isFilteredInjective I hIfilInj (op p) n
  have hIinj := injective_X_of_isDegreewiseFinite I hIfin hIstepInj
  have hgr (p : ℤ) : QuasiIso ((FilteredObject.gr p).map i) := hqi p
  have hstep (p : ℤ) : QuasiIso (i.natTrans.app (op p)) :=
    CochainComplex.quasiIso_natTrans_app_of_filteredQuasiIso i hqi hKfin hIfin (op p)
  have hhom : QuasiIso i.hom :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
      ((CochainComplex.isIso_Q_map_gradedPiece_and_forget_of_filteredQuasiIso i hqi).2
        hKfin hIfin)
  have hIK : I.X.IsKInjective := by
    have := hIge
    have (m : ℤ) := hIinj m
    exact CochainComplex.isKInjective_of_injective I.X a
  have hIstepK := isKInjective_filtration_obj_of_injective I a hIstepInj
  obtain ⟨hbdd, F, hF, hFeq, hFfin, hinf, hinfIso⟩ :=
    boundedFilteredReplacement_converges X RΓ α K I i hIfin hIK hIstepK hstep hhom
  exact ⟨I, i, hIge, hIfin, hIfilInj, hgr, hstep, hhom,
    globalSectionsFilteredComplex_filtration_obj X I,
    boundedFilteredReplacement_firstPageIso X RΓ α K I i hIfilInj hIgrKinj hgr,
    hbdd, F, hF, hFeq, hFfin, hinf, hinfIso⟩

/-- **Stacks 0BKM, through Remark 0BKL.** For a bounded-below complex the canonical truncation
spectral sequence can also be built from a bounded-below filtered replacement whose filtration is
finite in every degree and whose graded terms are injective; the first-page formula is the
same. -/
@[stacks 0BKM "truncation_e1_page",
  ega "0 11.4.3" "''E₂, T = RΓ",
  ega "0 12.4.1" "''E2, absolute case"]
theorem exists_boundedBelowTruncationSpectralSequence (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    ∃ (S : CanonicalTruncationSpectralSequence X K) (a : ℤ),
      S.injectiveReplacement.X.IsStrictlyGE a ∧
      S.injectiveReplacement.filtration.IsDegreewiseFinite ∧
      ∀ p q : ℤ, Nonempty
        (((globalSectionsSpectralSequence X S.injectiveReplacement).page 1
            (by omega)).X (p, q) ≅
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (2 * p + q)).obj
              (S.RΓ.obj ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X)) 0).obj
                  ((DerivedCategory.homologyFunctor
                    (SheafOfModules.{u} (structureSheafRing X)) (-p)).obj
                      (DerivedCategory.Q.obj K))))) := by
  obtain ⟨a, hKa⟩ := hK
  obtain ⟨S₀⟩ := exists_canonicalTruncationSpectralSequence X K
  have hSGE : S₀.filtered.X.IsStrictlyGE a := by
    have := hKa
    exact CochainComplex.isStrictlyGE_of_iso S₀.underlyingIso.symm a
  obtain ⟨I, i, hIge, hIfin, hIfilInj, hgr, hstep, hhom, -, h₁, hconv⟩ :=
    exists_spectralSequence_of_boundedBelowFilteredComplex X S₀.RΓ S₀.α S₀.isRightDerived
      S₀.filtered a hSGE S₀.isDegreewiseFinite
  have hIgrInj : ∀ p n : ℤ, Injective (((FilteredObject.gr p).obj I).X n) :=
    fun p n => ((CochainComplex.isFilteredInjective_evalFil_iff I n).1 (hIfilInj n)).2 p
  have hIstepInj (p n : ℤ) : Injective ((I.filtration.obj (op p)).X n) :=
    CochainComplex.injective_filtration_obj_X_of_isFilteredInjective I hIfilInj (op p) n
  have hIinj := injective_X_of_isDegreewiseFinite I hIfin hIstepInj
  have h₁' (p q : ℤ) : Nonempty
      (((globalSectionsSpectralSequence X I).page 1 (by omega)).X (p, q) ≅
        (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (2 * p + q)).obj
            (S₀.RΓ.obj ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X)) 0).obj
                ((DerivedCategory.homologyFunctor
                  (SheafOfModules.{u} (structureSheafRing X)) (-p)).obj
                    (DerivedCategory.Q.obj K))))) := by
    obtain ⟨e₁⟩ := h₁ p q
    obtain ⟨e₂⟩ := S₀.e₁IsoGraded p q
    obtain ⟨e₃⟩ := S₀.e₁Iso p q
    exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃⟩
  exact ⟨{ S₀ with
    injectiveReplacement := I
    replacementMap := i
    replacementMap_quasiIso := hhom
    replacementMap_step_quasiIso := hstep
    replacementMap_gr_quasiIso := hgr
    injective_terms := hIinj
    injective_step_terms := hIstepInj
    injective_gr_terms := hIgrInj
    e₁IsoGraded := h₁
    e₁Iso := h₁'
    convergence := fun _ _ => hconv },
    a, hIge, hIfin, h₁'⟩

/-- **The hypercohomology spectral sequence of an object of the derived category**: a
representative of `K`, its identification with `K`, and the canonical truncation spectral
sequence of that representative. -/
structure HypercohomologySpectralSequence (X : RingedSpace.{u, u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) where
  /-- A complex of module sheaves representing `K`. -/
  representative : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ
  /-- Its identification with `K` in the derived category. -/
  representativeIso : DerivedCategory.Q.obj representative ≅ K
  /-- The canonical truncation spectral sequence of the representative. -/
  truncation : CanonicalTruncationSpectralSequence X representative

/-- The underlying spectral sequence: its pages start at two and its differentials have bidegree
`(r, -r + 1)`, the new bidegree `(i, j)` being the old bidegree `(-j, i + 2j)`. -/
abbrev HypercohomologySpectralSequence.spectralSequence {X : RingedSpace.{u, u}}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (S : HypercohomologySpectralSequence X K) :
    CohomologicalSpectralSequence (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) 2 :=
  SpectralSequence.truncationRenumber
    (SpectralSequence.restrictPages S.truncation.spectralSequence 1 (by omega))

/-- **Stacks 0BKM.** The hypercohomology spectral sequence of an object of the derived category
of module sheaves on a ringed space: take a representative, filter it by its canonical
truncations, apply derived global sections, and renumber the resulting spectral sequence. -/
@[stacks 0BKM "hypercohomology_e2_page"]
def hypercohomologySpectralSequence (X : RingedSpace.{u, u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    HypercohomologySpectralSequence X K :=
  ⟨DerivedCategory.Q.objPreimage K, DerivedCategory.Q.objObjPreimageIso K,
    Classical.choice (exists_canonicalTruncationSpectralSequence X
      (DerivedCategory.Q.objPreimage K))⟩

/-- **Stacks 0BKM.** The second page of the hypercohomology spectral sequence is the
hypercohomology of the cohomology objects of `K`: `E_2^{i, j} = H^i(X, H^j(K))`. -/
@[stacks 0BKM "hypercohomology_e2_page"]
theorem hypercohomologySpectralSequence_e₂ (X : RingedSpace.{u, u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ) :
    Nonempty (((hypercohomologySpectralSequence X K).spectralSequence.page 2).X (i, j) ≅
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) i).obj
        ((hypercohomologySpectralSequence X K).truncation.RΓ.obj
          ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).obj
            ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (structureSheafRing X)) j).obj K)))) := by
  let S := hypercohomologySpectralSequence X K
  let eH := (DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) (2 * -j + (i + 2 * j))).mapIso
    (S.truncation.RΓ.mapIso
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0).mapIso
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X)) (- -j)).mapIso S.representativeIso)))
  obtain ⟨e₁⟩ := S.truncation.e₁Iso (-j) (i + 2 * j)
  exact ⟨by simpa [S, HypercohomologySpectralSequence.spectralSequence,
    SpectralSequence.truncationRenumber, SpectralSequence.restrictPages,
    show (SpectralSequence.truncationRenumberingEmbedding 2).f (i, j) = (-j, i + 2 * j) from rfl,
    show 2 * -j + (i + 2 * j) = i by omega, show - -j = j by omega] using e₁ ≪≫ eH⟩

/-- **Stacks 0BKM, the closing clause.**  If `K^•` is bounded below, the renumbered spectral
sequence -- the one whose second page is `H^i(X, H^j(K^•))` -- is **bounded**, and it **converges
to `H^{i + j}(X, K^•)`**: some finite decreasing filtration of `H^n(X, K^•)` has the terms
`E_∞^{i, n - i}` of its infinity page as graded pieces.

The spectral sequence is the one of
`exists_boundedBelowTruncationSpectralSequence`, i.e. the one built through Remark
[Stacks, Tag 0BKL] from a bounded-below filtered replacement; boundedness and convergence of that
sequence *before* the renumbering are `boundedReplacement_convergence`, which needs no hypothesis
beyond degreewise finiteness of the replacement's filtration, and they are carried across the
bidegree change `(i, j) ↦ (-j, i + 2j)` by
`CategoryTheory.SpectralSequence.truncationRenumber_finite_not_isZero_page_two` and
`CategoryTheory.SpectralSequence.AbutsTo.truncationRenumberRestrictPages`.  The abutment is read
on `K^•` itself rather than on the underlying complex of the filtration by
`CategoryTheory.SpectralSequence.AbutsTo.of_iso`. -/
@[stacks 0BKM "bounded below: the renumbered sequence is bounded and converges to H^{i+j}(X, K)",
  ega "0 11.4.3" "T = RΓ, bounded below",
  ega "III 6.2.1" "absolute case, Y=point",
  ega "0 12.4.1" "abutment, absolute case"]
theorem exists_boundedBelowHypercohomologySpectralSequence (X : RingedSpace.{u, u})
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hK : ∃ a : ℤ, K.IsStrictlyGE a) :
    ∃ S : HypercohomologySpectralSequence X (DerivedCategory.Q.obj K),
      IsBounded S.spectralSequence ∧
        SpectralSequence.AbutsTo S.spectralSequence
          (fun n => hypercohomology X S.truncation.RΓ K n) := by
  obtain ⟨S₀, b, hIge, hIfin, -⟩ := exists_boundedBelowTruncationSpectralSequence X K hK
  have hIK : S₀.injectiveReplacement.X.IsKInjective := by
    have := hIge
    have (n : ℤ) := S₀.injective_terms n
    exact CochainComplex.isKInjective_of_injective S₀.injectiveReplacement.X b
  have hIstepK := isKInjective_filtration_obj_of_injective S₀.injectiveReplacement b
    S₀.injective_step_terms
  obtain ⟨hfin, F, hF, -, hbnd, hpi, hgr⟩ :=
    boundedReplacement_convergence X K S₀ S₀.injectiveReplacement S₀.replacementMap hIfin hIK
      hIstepK S₀.replacementMap_step_quasiIso S₀.replacementMap_quasiIso
  refine ⟨⟨K, Iso.refl _, S₀⟩, fun n =>
    SpectralSequence.truncationRenumber_finite_not_isZero_page_two _ hfin n, ?_⟩
  refine SpectralSequence.AbutsTo.of_iso
    (SpectralSequence.AbutsTo.truncationRenumberRestrictPages
      (E := S₀.spectralSequence) ⟨hpi, F, hF, hbnd, hgr⟩ (by omega)) fun n => ?_
  exact (DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) n).mapIso
    (S₀.RΓ.mapIso (DerivedCategory.Q.mapIso S₀.underlyingIso))

end Stacks.Cohomology.FilteredComplex

end

module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.BoundedBelowComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.DoubleComplexSpectralSequences
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.RowHomologyOfACartanEilenbergResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.AcyclicCoveringComputesDerivedSections
public import StacksCore.Algebra.Homology.HomologicalTricomplex.Associator
import StacksCore.Tactic.StacksAttribute

/-!
# The Čech-to-cohomology spectral sequence of a bounded below complex

Let `(X, O_X)` be a ringed space, let `U : I → Opens X` be an open covering of `X` and let
`F^•` be a bounded below complex of `O_X`-modules. There is a cohomological spectral sequence
with

```
E_2^{p,q} = H^p(Tot(Č^•(U, H^q(F^•))))
```

abutting to `H^{p+q}(X, F^•)`, where `H^q(F^•)` is the complex `n ↦ R^q i(F^n)` of cohomology
presheaves, `i` being the forgetful functor from sheaves of modules to abelian presheaves, and
`p`, `q` range over `ℤ`.

The spectral sequence is the second spectral sequence of the double complex

```
B^{m,n} = ⨁_{p + q = n} Č^p(U, i(I^{q,m}))
```

of `Stacks.Cech.cechCartanEilenbergBicomplex`, for `I^{•,•}` a Cartan-Eilenberg resolution of
`F^•`.

## Main definitions

* `Stacks.Cech.cechCartanEilenbergTotalIso`: `Tot(B^{•,•}) ≅ Tot(Č^•(U, Tot(L)))`, for `L` a
  double complex of abelian presheaves.
* `Stacks.Cech.cechDerivedIsoDerivedGlobalSections`: on a bounded below complex of injectives
  the derived total Čech complex is derived global sections.

## Main results

* `Stacks.Cech.exists_cechSpectralSequence`: the Čech-to-cohomology spectral sequence of a
  bounded below complex.
* `Stacks.Cohomology.CechSpectral.abutsTo_totalSpectralSequence₂Functor`: the canonical second
  spectral sequence of a diagonally finite double complex abuts to the cohomology of its total
  complex.
* `Stacks.Cech.finite_diagonal_cechCartanEilenbergBicomplex`: `B^{•,•}` is diagonally finite.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 08BI](https://stacks.math.columbia.edu/tag/08BI)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 015H](https://stacks.math.columbia.edu/tag/015H)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 01ER](https://stacks.math.columbia.edu/tag/01ER)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

namespace Stacks.Cech

universe w v u

/-! ### Vanishing of the double complex outside a quadrant -/

section Vanishing

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : Type w} (U : J → C)
  [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).Additive]
  (L : HomologicalComplex₂ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ) (up ℤ))

/-- A term of the Čech triple complex vanishes as soon as the term of `L` it is the Čech complex
of does. -/
lemma isZero_cechTricomplexFunctor_X_X_X_of_isZero (p q m : ℤ) (h : IsZero ((L.X q).X m)) :
    IsZero (((((cechTricomplexFunctor U).obj L).X p).X q).X m) :=
  Functor.map_isZero
    (cechComplexFunctorInt U ⋙ HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p) h

variable [∀ K : HomologicalComplex₂ AddCommGrpCat.{w} (up ℤ) (up ℤ), K.HasTotal (up ℤ)]

/-- A term `B^{m,n}` of `B^{•,•}` is zero as soon as every summand `Č^p(U, L^{q,m})` with
`p + q = n` is zero. -/
lemma isZero_cechCartanEilenbergBicomplex_X_X (m n : ℤ)
    (h : ∀ p q : ℤ, p + q = n → IsZero (((((cechTricomplexFunctor U).obj L).X p).X q).X m)) :
    IsZero (((cechCartanEilenbergBicomplex U L).X m).X n) :=
  HomologicalComplex₂.isZero_total_X_of_isZero
    (((cechTricomplexFunctor U).obj L).X' m) (up ℤ) n (fun p q hpq => h p q hpq)

/-- `B^{m,n} = 0` for `n < n₀` when `L` is strictly `≥ n₀`. -/
lemma isZero_cechCartanEilenbergBicomplex_X_X_of_lt (n₀ : ℤ) [CochainComplex.IsStrictlyGE L n₀]
    (m n : ℤ) (hn : n < n₀) : IsZero (((cechCartanEilenbergBicomplex U L).X m).X n) := by
  refine isZero_cechCartanEilenbergBicomplex_X_X U L m n fun p q hpq => ?_
  rcases lt_or_ge p 0 with hp | hp
  · exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) m)
      (isZero_cechTricomplexFunctor_X_X_of_neg U L p hp q)
  · exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) m)
      (isZero_cechTricomplexFunctor_X_X_of_lt U L n₀ p q (by omega))

/-- `B^{m,n} = 0` for `m < 0` when `L` vanishes in negative second degrees. -/
lemma isZero_cechCartanEilenbergBicomplex_X_X_of_neg
    (hL : ∀ q m : ℤ, m < 0 → IsZero ((L.X q).X m)) (m n : ℤ) (hm : m < 0) :
    IsZero (((cechCartanEilenbergBicomplex U L).X m).X n) :=
  isZero_cechCartanEilenbergBicomplex_X_X U L m n fun p q _ =>
    isZero_cechTricomplexFunctor_X_X_X_of_isZero U L p q m (hL q m hm)

/-- `B^{•,•}` is diagonally finite: on each antidiagonal `m + n = N` only finitely many terms
are nonzero, when `L` is strictly `≥ n₀` and vanishes in negative second degrees. -/
lemma finite_diagonal_cechCartanEilenbergBicomplex (n₀ : ℤ) [CochainComplex.IsStrictlyGE L n₀]
    (hL : ∀ q m : ℤ, m < 0 → IsZero ((L.X q).X m)) (N : ℤ) :
    {mn : ℤ × ℤ | mn.1 + mn.2 = N ∧
      ¬ IsZero (((cechCartanEilenbergBicomplex U L).X mn.1).X mn.2)}.Finite := by
  refine ((Set.finite_Icc (0 : ℤ) (N - n₀)).prod (Set.finite_Icc n₀ N)).subset
    fun mn ⟨hsum, hne⟩ => ?_
  have hm : 0 ≤ mn.1 :=
    not_lt.1 fun h => hne (isZero_cechCartanEilenbergBicomplex_X_X_of_neg U L hL _ _ h)
  have hn : n₀ ≤ mn.2 :=
    not_lt.1 fun h => hne (isZero_cechCartanEilenbergBicomplex_X_X_of_lt U L n₀ _ _ h)
  exact ⟨⟨hm, by omega⟩, hn, by omega⟩

/-- The total complex of `B^{•,•}` is the total Čech complex of the total complex of `L`,
`Tot(B^{•,•}) ≅ Tot(Č^•(U, Tot(L)))`, for `L` diagonally finite. -/
def cechCartanEilenbergTotalIso
    (hL : ∀ n : ℤ, {qm : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) qm = n ∧
      ¬ IsZero ((L.X qm.1).X qm.2)}.Finite) :
    (cechCartanEilenbergBicomplex U L).total (up ℤ) ≅
      (cechTotalComplexFunctor U).obj (L.total (up ℤ)) :=
  HomologicalComplex₂.totalFlipIso (((cechTricomplexFunctor U).obj L).int₁₂ (up ℤ)) (up ℤ) ≪≫
    HomologicalComplex₃.totalAssociator ((cechTricomplexFunctor U).obj L) (up ℤ) (up ℤ) (up ℤ) ≪≫
      total₂₃IsoCechTotalComplex U L hL

end Vanishing

end Stacks.Cech

/-! ### Convergence of the second spectral sequence of a double complex -/

namespace Stacks.Cohomology.CechSpectral

open HomologicalComplex₂

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
  [∀ (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)),
    K.HasTotal (ComplexShape.up ℤ)]

/-- The canonical second spectral sequence of a diagonally finite double complex abuts to the
cohomology of its total complex. -/
theorem abutsTo_totalSpectralSequence₂Functor
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hK : ∀ n : ℤ, {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero ((K.X pq.1).X pq.2)}.Finite) :
    SpectralSequence.AbutsTo ((totalSpectralSequence₂Functor C).obj K)
      (fun n => (K.total (ComplexShape.up ℤ)).homology n) := by
  obtain ⟨e, -, -, -, -, -⟩ := CochainComplex.exists_iso_spectralSequence_page
    K.totalFiltration₂ _ (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
  exact CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite K.totalFiltration₂ _
    (fun _ _ => rfl) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl)
    ((totalSpectralSequence₂Functor C).obj K) e
    (K.isDegreewiseFinite_totalFiltration₂ hK)

end Stacks.Cohomology.CechSpectral

/-! ### The spectral sequence -/

namespace Stacks.Cech

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- On a bounded below complex of injectives `L^•` the derived total Čech complex is derived
global sections of `K^•`, through any quasi-isomorphism `f : K^• ⟶ L^•`. -/
def cechDerivedIsoDerivedGlobalSections {I : Type u} (U : I → Opens X) (hU : ⊤ = iSup U)
    (K L : CochainComplex.Plus (SheafOfModules.{u} R)) (f : K ⟶ L) [QuasiIso f.hom]
    (hLinj : ∀ n : ℤ, Injective (L.1.X n)) :
    (cechDerivedFunctor X R U).obj L ≅ (derivedGlobalSectionsFunctor X R).obj K :=
  haveI := isIso_globalSectionsToCechDerived_of_injective X R U hU L hLinj
  haveI := isIso_globalSectionsToDerived_of_injective X R L hLinj
  (asIso ((globalSectionsToCechDerived X R U).app L)).symm ≪≫
    asIso ((globalSectionsToDerivedNat X R).app L) ≪≫
      (asIso ((derivedGlobalSectionsFunctor X R).map f)).symm

/-- For a ringed space `(X, O_X)`, an open covering `U : I → Opens X` of `X` and a bounded below
complex `F^•` of `O_X`-modules there is a cohomological spectral sequence, starting on page two,
with

```
E_2^{p,q} = H^p(Tot(Č^•(U, H^q(F^•))))
```

where `H^q(F^•)` is the complex `n ↦ R^q i(F^n)` of cohomology presheaves, abutting to
`H^{p+q}(X, F^•)`. -/
@[stacks 08BN "the tag's spectral sequence: `E_2^{p,q} = H^p(Tot(Č(U, H^q(F))))`, both \
coordinates ranging over `ℤ`, abutting to `H^{p+q}(X, F)`, for a ringed space, an open covering \
of `X` and a bounded below complex of `O_X`-modules. The tag's comparison map \
`Tot(Č(U, F)) ⟶ RΓ(X, F)`, with its Tag 07M9 and Tag 08BM compatibilities, is \
`Stacks.Cech.cechToDerivedGlobalSections`, and the two halves are asserted together at the \
lemma's own three inputs by \
`Stacks.Cech.exists_cechToDerivedComparison_and_cechSpectralSequence`"]
theorem exists_cechSpectralSequence {I : Type u} (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u} 2,
      (∀ p q : ℤ,
        Nonempty ((E.page 2).X (p, q) ≅
          ((cechTotalComplexFunctor U).obj
            ((((underlyingPresheafFunctor X R).rightDerivedPlus q).mapHomologicalComplex
              (up ℤ)).obj K.1)).homology p)) ∧
      SpectralSequence.AbutsTo E (fun n =>
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
          ((derivedGlobalSectionsFunctor X R).obj K)) := by
  classical
  obtain ⟨a, ha⟩ := K.2
  obtain ⟨CE, hCE⟩ := K.1.exists_cartanEilenbergResolution a
  obtain ⟨i₀, hneg, -⟩ := StacksDraft.CartanEilenbergResolutions.exists_bounds_bicomplex CE
  have := StacksDraft.CartanEilenbergResolutions.hasTotal_bicomplex CE
  have hCEfin := StacksDraft.CartanEilenbergResolutions.finite_not_isZero_bicomplex CE
  set Lb := (((underlyingPresheafFunctor X R).mapHomologicalComplex (up ℤ)
    ).mapHomologicalComplex (up ℤ)).obj CE.bicomplex
  have hLneg : ∀ q m : ℤ, m < 0 → IsZero ((Lb.X q).X m) :=
    fun q m hm => Functor.map_isZero (underlyingPresheafFunctor X R) (hneg q m hm)
  have hLge : CochainComplex.IsStrictlyGE Lb a :=
    (CochainComplex.isStrictlyGE_iff _ _).2 fun p hp =>
      Functor.map_isZero ((underlyingPresheafFunctor X R).mapHomologicalComplex (up ℤ))
        (CochainComplex.isZero_of_isStrictlyGE CE.bicomplex a p hp)
  have hLfin : ∀ n : ℤ, {qm : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) qm = n ∧
      ¬ IsZero ((Lb.X qm.1).X qm.2)}.Finite :=
    fun n => (hCEfin n).subset fun qm h =>
      ⟨h.1, fun hz => h.2 (Functor.map_isZero (underlyingPresheafFunctor X R) hz)⟩
  have hTfin := finite_support_cechTricomplexFunctor U Lb a
  have hBfin := finite_diagonal_cechCartanEilenbergBicomplex U Lb a hLneg
  refine ⟨(HomologicalComplex₂.e₂SpectralSequence₂Functor AddCommGrpCat.{u}).obj
    (cechCartanEilenbergBicomplex U Lb), ?_, ?_⟩
  · intro p q
    obtain ⟨e⟩ :=
      CochainComplex.CartanEilenbergResolution.nonempty_rowHomologyIso_rightDerivedPlus
        (underlyingPresheafFunctor X R) K.2 CE q
    exact ⟨cechCartanEilenbergBicomplexPageTwoIso U Lb p q hTfin ≪≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℤ) p).mapIso
        ((cechTotalComplexFunctor U).mapIso e)⟩
  · have hJinj : ∀ n : ℤ, Injective ((CE.bicomplex.total (up ℤ)).X n) :=
      fun n => StacksDraft.CartanEilenbergResolutions.injective_total_X CE n
    set Lp : CochainComplex.Plus (SheafOfModules.{u} R) :=
      ⟨CE.bicomplex.total (up ℤ), StacksDraft.CartanEilenbergResolutions.plus_total CE⟩
    set f : K ⟶ Lp :=
      ObjectProperty.homMk (StacksDraft.CartanEilenbergResolutions.totalAugmentation CE)
    have : QuasiIso f.hom :=
      StacksDraft.CartanEilenbergResolutions.quasiIso_totalAugmentation CE K.2
    have θ : (cechCartanEilenbergBicomplex U Lb).total (up ℤ) ≅
        (cechTotalComplexFunctor U).obj ((underlyingPresheafComplexFunctor X R).obj Lp.1) :=
      cechCartanEilenbergTotalIso U Lb hLfin ≪≫
        (cechTotalComplexFunctor U).mapIso
          (HomologicalComplex₂.TotalMap.totalIsoOfFinite (underlyingPresheafFunctor X R)
            CE.bicomplex hCEfin)
    have hab := Stacks.Cohomology.CechSpectral.abutsTo_totalSpectralSequence₂Functor
      (cechCartanEilenbergBicomplex U Lb) hBfin
    have habs := hab.of_iso fun n =>
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (up ℤ) n).mapIso θ ≪≫
        ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} n).app
          ((cechTotalComplexFunctor U).obj
            ((underlyingPresheafComplexFunctor X R).obj Lp.1))).symm ≪≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
          (cechDerivedIsoDerivedGlobalSections X R U hU K Lp f hJinj)
    have heq : (HomologicalComplex₂.e₂SpectralSequence₂Functor AddCommGrpCat.{u}).obj
          (cechCartanEilenbergBicomplex U Lb) =
        ((Stacks.Cohomology.CechSpectral.totalSpectralSequence₂Functor AddCommGrpCat.{u}).obj
          (cechCartanEilenbergBicomplex U Lb)).shiftStart (by omega : (0 : ℤ) ≤ 2) := by
      change (Stacks.Cohomology.CechSpectral.restrictR₀ (by omega : (0 : ℤ) ≤ 2)).obj
        ((HomologicalComplex₂.spectralSequence₂Functor AddCommGrpCat.{u}).obj
          (cechCartanEilenbergBicomplex U Lb)) = _
      rw [HomologicalComplex₂.spectralSequence₂Functor_obj]
      rfl
    rw [heq]
    exact habs.shiftStart (by omega)

end Stacks.Cech

end

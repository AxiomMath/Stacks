module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceTagTotal
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage

/-!
# The cohomology spectral sequence of a simplicial site (Stacks 09WJ)

Let `S` be a simplicial-site situation (Stacks 09WE), with total site `C_total` and component
sites `C_n`, and let `F` be an abelian sheaf on `C_total`. Choosing the injective resolution
`I^•` of `F` and applying the complex of Stacks 0D77 degreewise gives the double complex

```
A^{q,p} = Γ(C_p, I^q_p)
```

of `StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequence.lean`. This file
assembles the spectral sequence of that double complex into the statement of Stacks 09WJ: it is
functorial in `F`, its first page is

```
E_1^{p,q} = H^q(C_p, F_p),
```

and it abuts to `H^{p+q}(C_total, F)`.

The three ingredients the module documentation of
`StacksFrontier/CategoryTheory/Sites/Simplicial/CohomologySpectralSequence.lean` records as missing
are supplied here and in its two companions:

* `CategoryTheory.SimplicialSiteSituation.rightDerivedComponentSectionsNatIso`
  (`CohomologySpectralSequenceTagComponent.lean`) identifies `H^q(Γ(C_p, I^•_p))` with
  `H^q(C_p, F_p)`, using Stacks 09WG (7) and Stacks 09WH;
* `CategoryTheory.SimplicialSiteSituation.totalCohomologyIsoTotalComplexHomology`
  (`CohomologySpectralSequenceTagTotal.lean`) identifies `H^n(Tot(A^{•,•}))` with
  `H^n(C_total, F)`, using Stacks 0133;
* the functoriality in `F` is below: an injective resolution is functorial only up to homotopy,
  so the functor laws of `cohomologySpectralSequence` hold by
  `HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂`, which is why the
  spectral sequence is presented from its first page.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.cohomologyDoubleComplex`: the double complex
  `A^{q,p} = Γ(C_p, I^q_p)` of the chosen injective resolution of an abelian sheaf.
* `CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence`: **the spectral sequence of
  Stacks 09WJ**, as a functor of the abelian sheaf.
* `CategoryTheory.SimplicialSiteSituation.pageOneFunctor`: its first page at `(p, q)`, as a
  functor of the abelian sheaf.
* `CategoryTheory.SimplicialSiteSituation.totalCohomologyZ`: the integer-graded sheaf cohomology
  `H^n(C_total, F)`, as the cohomology of `Γ(C_total, I^•)`; it vanishes in negative degrees and
  is the right derived functor of `Γ(C_total, -)` in the others.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence_pageOneIso`:
  **`E_1^{p,q} = H^q(C_p, F_p)`**, naturally in the abelian sheaf.
* `CategoryTheory.SimplicialSiteSituation.pageOneIsoColumnHomology_hom_d` of
  `CohomologySpectralSequence.lean` is the differential `d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`.
* `CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence_abutsTo`: **the spectral
  sequence abuts to `H^{p+q}(C_total, F)`.**
* `CategoryTheory.SimplicialSiteSituation.totalCohomologyZ_iso_rightDerived` and
  `isZero_totalCohomologyZ_of_neg`: the abutment family is the sheaf cohomology of the total
  site, extended by zero to the negative degrees.

## What is and is not Stacks 09WJ

Stacks 09WJ is stated for an object `K` of `D^+(C_total)`. Everything below is for an abelian
sheaf `F` on `C_total`, i.e. for `K = F[0]`, and the functoriality obtained is functoriality in
`F` over the category of abelian sheaves, not over `D^+(C_total)`. The tagged declarations
therefore carry labelled attributes saying exactly that, as does the topological analogue
`Stacks.Topology.Simplicial.cohomologySpectralSequence` of Stacks 09W6. Extending the
construction to a general bounded-below object of the derived category is not done here: it needs
the spectral sequence to be a functor out of `DerivedCategory.Plus (Sheaf S.totalTopology Ab)`,
and the double complex above is built from the *chosen* injective resolution of a sheaf.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WH](https://stacks.math.columbia.edu/tag/09WH)
* [Stacks Project, Tag 0D77](https://stacks.math.columbia.edu/tag/0D77)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-! ### The double complex of an abelian sheaf -/

/-- **The double complex `A^{q,p} = Γ(C_p, I^q_p)` of an abelian sheaf** on the total site of a
simplicial-site situation, for the chosen injective resolution `I^•` of the sheaf. -/
abbrev cohomologyDoubleComplex (F : Sheaf S.totalTopology Ab.{u}) :
    HomologicalComplex₂ Ab.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  S.sectionsDoubleComplex (S.injectiveResolutionZ F)

/-- The chosen descent of a morphism of abelian sheaves to the chosen injective resolutions,
extended by zero to integer degrees. -/
abbrev descZ {F F' : Sheaf S.totalTopology Ab.{u}} (f : F ⟶ F') :
    S.injectiveResolutionZ F ⟶ S.injectiveResolutionZ F' :=
  (ComplexShape.embeddingUpNat.extendFunctor (Sheaf S.totalTopology Ab.{u})).map
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))

/-- The morphism of double complexes attached to a morphism of abelian sheaves: the double
complex of the chosen descent of that morphism to the chosen injective resolutions. -/
def cohomologyDoubleComplexMap {F F' : Sheaf S.totalTopology Ab.{u}} (f : F ⟶ F') :
    S.cohomologyDoubleComplex F ⟶ S.cohomologyDoubleComplex F' :=
  (S.sectionsDoubleComplexFunctor).map (S.descZ f)

/-- A homotopy between two descents to the chosen injective resolutions induces a homotopy
between the induced morphisms of double complexes: the complex of Stacks 0D77 is additive, and
extension by zero carries homotopies to homotopies. -/
def cohomologyDoubleComplexHomotopy {F F' : Sheaf S.totalTopology Ab.{u}}
    {φ ψ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution F').cocomplex}
    (H : Homotopy φ ψ) :
    Homotopy ((S.sectionsDoubleComplexFunctor).map
        ((ComplexShape.embeddingUpNat.extendFunctor (Sheaf S.totalTopology Ab.{u})).map φ))
      ((S.sectionsDoubleComplexFunctor).map
        ((ComplexShape.embeddingUpNat.extendFunctor (Sheaf S.totalTopology Ab.{u})).map ψ)) :=
  (S.cechSectionsComplexZ).mapHomotopy (H.extend ComplexShape.embeddingUpNat)

/-- `cohomologyDoubleComplexMap` sends an identity to a filtered homotopy class of the
identity. -/
theorem filteredHomotopy₂_cohomologyDoubleComplexMap_id (F : Sheaf S.totalTopology Ab.{u}) :
    HomologicalComplex₂.FilteredHomotopy₂ (S.cohomologyDoubleComplexMap (𝟙 F)) (𝟙 _) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((S.cohomologyDoubleComplexHomotopy
        (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).trans
      (Homotopy.ofEq (by
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])))

/-- `cohomologyDoubleComplexMap` is multiplicative up to filtered homotopy. -/
theorem filteredHomotopy₂_cohomologyDoubleComplexMap_comp
    {F F' F'' : Sheaf S.totalTopology Ab.{u}} (f : F ⟶ F') (g : F' ⟶ F'') :
    HomologicalComplex₂.FilteredHomotopy₂ (S.cohomologyDoubleComplexMap (f ≫ g))
      (S.cohomologyDoubleComplexMap f ≫ S.cohomologyDoubleComplexMap g) :=
  HomologicalComplex₂.filteredHomotopy₂_of_homotopy
    ((S.cohomologyDoubleComplexHomotopy
        (InjectiveResolution.descCompHomotopy f g (injectiveResolution F)
          (injectiveResolution F') (injectiveResolution F''))).trans
      (Homotopy.ofEq (by rw [Functor.map_comp, Functor.map_comp]; rfl)))

/-! ### The spectral sequence, as a functor of the abelian sheaf -/

/-- **Stacks 09WJ, the spectral sequence.** For an abelian sheaf `F` on the total site of a
simplicial-site situation there is a cohomological spectral sequence, functorial in `F`: the
spectral sequence of the filtration by the simplicial coordinate of the double complex
`A^{q,p} = Γ(C_p, I^q_p)` of the chosen injective resolution of `F`, presented from its first
page.

The functor laws hold because filtered homotopic morphisms of double complexes induce the same
maps on the pages from the first on; an injective resolution is functorial only up to homotopy,
which is why the presentation starts at the first page. -/
@[stacks 09WJ "the spectral sequence, for an abelian sheaf on the total site, functorial in it"]
def cohomologySpectralSequence :
    Sheaf S.totalTopology Ab.{u} ⥤ CohomologicalSpectralSequence Ab.{u} 1 where
  obj F := (S.sectionsSpectralSequence (S.injectiveResolutionZ F)).shiftStart zero_le_one
  map f := CategoryTheory.SpectralSequence.shiftStartMap
    (HomologicalComplex₂.spectralSequenceMap₂ (S.cohomologyDoubleComplexMap f))
    zero_le_one
  map_id F := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (S.filteredHomotopy₂_cohomologyDoubleComplexMap_id F)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [HomologicalComplex₂.spectralSequenceMap₂_id]
    simp
  map_comp f g := by
    refine CategoryTheory.SpectralSequence.hom_ext fun r hr => ?_
    refine Eq.trans (HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (S.filteredHomotopy₂_cohomologyDoubleComplexMap_comp f g)
      (show (1 : ℤ) ≤ r by omega)) ?_
    rw [HomologicalComplex₂.spectralSequenceMap₂_comp]
    rfl

/-- The first page of the spectral sequence at `(p, q)`, as a functor of the abelian sheaf. -/
abbrev pageOneFunctor (n q : ℕ) : Sheaf S.totalTopology Ab.{u} ⥤ Ab.{u} :=
  S.cohomologySpectralSequence ⋙
    CategoryTheory.SpectralSequence.pageFunctor Ab.{u} _ 1 1 le_rfl ⋙
      HomologicalComplex.eval Ab.{u} _ ((n : ℤ), (q : ℤ))

/-! ### The first page is the cohomology of the components -/

/-- **The columns of the double complex compute the complexes of sections over the components.**
Taking the homology of the double complex in the outer degree `q` and then its term in the
simplicial degree `n` is taking the sections over `C_n` degreewise and then the `q`-th
cohomology, naturally in the complex of abelian sheaves.

This is the natural form of `CategoryTheory.SimplicialSiteSituation.columnHomologyIso`: the two
steps are that evaluation in a fixed degree is exact, hence commutes with homology, and the
degreewise identification `cechSectionsComplexZCompEval`. -/
def columnHomologyNatIso (n : ℕ) (q : ℤ) :
    S.sectionsDoubleComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (CochainComplex Ab.{u} ℤ) (ComplexShape.up ℤ) q ⋙
          HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (n : ℤ) ≅
      (S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q :=
  Functor.isoWhiskerLeft (S.sectionsDoubleComplexFunctor)
      (Functor.mapHomologicalComplexHomologyIso
        (HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (n : ℤ))
        (ComplexShape.up ℤ) q).symm ≪≫
    Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (S.cechSectionsComplexZCompEval n)
        (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) q)

variable (n q : ℕ)

/-- **The first page at `(n, q)` is the `q`-th cohomology of the complex of sections over `C_n`
of the chosen injective resolution.** -/
def pageOneIsoResolutionSections (F : Sheaf S.totalTopology Ab.{u}) :
    (S.pageOneFunctor n q).obj F ≅
      (((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (S.injectiveResolutionZ F)).homology (q : ℤ) :=
  HomologicalComplex₂.isoOnePageTotalFiltration₂ (S.cohomologyDoubleComplex F) _
      (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) (n : ℤ) (q : ℤ) ≪≫
    (S.columnHomologyNatIso n (q : ℤ)).app (S.injectiveResolutionZ F)

/-- `pageOneIsoResolutionSections` is natural in the abelian sheaf, for the chosen descent of a
morphism to the chosen injective resolutions. -/
theorem pageOneIsoResolutionSections_hom_naturality {F F' : Sheaf S.totalTopology Ab.{u}}
    (f : F ⟶ F') :
    (S.pageOneFunctor n q).map f ≫
        (S.pageOneIsoResolutionSections n q F').hom =
      (S.pageOneIsoResolutionSections n q F).hom ≫
        HomologicalComplex.homologyMap
          (((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (S.descZ f)) (q : ℤ) :=
  square_comp
    (HomologicalComplex₂.isoOnePageTotalFiltration₂_naturality_functor
      (S.cohomologyDoubleComplexMap f) (n : ℤ) (q : ℤ))
    ((S.columnHomologyNatIso n (q : ℤ)).hom.naturality (S.descZ f))

/-- **The `q`-th cohomology of the complex of sections over `C_n` of the chosen injective
resolution is the `q`-th right derived functor of `Γ(C_n, (-)_n)`**: extension by zero commutes
with the additive functor `Γ(C_n, (-)_n)` and does not change the cohomology in the degrees
coming from `ℕ`. -/
def resolutionSectionsIsoRightDerived (F : Sheaf S.totalTopology Ab.{u}) :
    (((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (S.injectiveResolutionZ F)).homology (q : ℤ) ≅
      ((S.componentSectionsFunctor ⦋n⦌).rightDerived q).obj F :=
  (HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) (q : ℤ)).mapIso
      ((S.componentSectionsFunctor ⦋n⦌).mapExtendIso (injectiveResolution F).cocomplex
        ComplexShape.embeddingUpNat) ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl) ≪≫
    ((injectiveResolution F).isoRightDerivedObj (S.componentSectionsFunctor ⦋n⦌) q).symm

/-- `resolutionSectionsIsoRightDerived` is natural in the abelian sheaf, for the chosen descent
of a morphism to the chosen injective resolutions. -/
theorem resolutionSectionsIsoRightDerived_hom_naturality {F F' : Sheaf S.totalTopology Ab.{u}}
    (f : F ⟶ F') :
    HomologicalComplex.homologyMap
          (((S.componentSectionsFunctor ⦋n⦌).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (S.descZ f)) (q : ℤ) ≫
        (S.resolutionSectionsIsoRightDerived n q F').hom =
      (S.resolutionSectionsIsoRightDerived n q F).hom ≫
        ((S.componentSectionsFunctor ⦋n⦌).rightDerived q).map f :=
  by
  refine square_comp₃ ?_
    (HomologicalComplex.extendHomologyIso_hom_naturality _ ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f q = (q : ℤ) from rfl))
    (InjectiveResolution.isoRightDerivedObj_inv_naturality f
      (injectiveResolution F) (injectiveResolution F')
      (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))
      (InjectiveResolution.desc_commutes_zero f (injectiveResolution F')
        (injectiveResolution F)) (S.componentSectionsFunctor ⦋n⦌) q).symm
  show HomologicalComplex.homologyMap _ (q : ℤ) ≫ HomologicalComplex.homologyMap _ (q : ℤ) =
    HomologicalComplex.homologyMap _ (q : ℤ) ≫ HomologicalComplex.homologyMap _ (q : ℤ)
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (fun u => HomologicalComplex.homologyMap u (q : ℤ))
    ((S.componentSectionsFunctor ⦋n⦌).mapExtendIso_hom_naturality
      (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))
      ComplexShape.embeddingUpNat)

/-- **Stacks 09WJ, the first page.** `E_1^{p,q} = H^q(C_p, F_p)`: the first page of the spectral
sequence of the simplicial-site situation at `(p, q)` is the sheaf cohomology of the restriction
of `F` to the component site `C_p`, naturally in the abelian sheaf `F`.

Together with
`CategoryTheory.SimplicialSiteSituation.pageOneIsoColumnHomology_hom_d`, which identifies
`d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}` with the differential of the complex of Stacks 0D77, this
is the first page and the first differential of Stacks 09WJ. -/
@[stacks 09WJ "the first page E_1^{p,q} = H^q(C_p, F_p) for an abelian sheaf, naturally in it"]
def cohomologySpectralSequence_pageOneIso :
    S.pageOneFunctor n q ≅ S.componentCohomologyFunctor ⦋n⦌ q :=
  NatIso.ofComponents
    (fun F => S.pageOneIsoResolutionSections n q F ≪≫
      S.resolutionSectionsIsoRightDerived n q F ≪≫
      S.rightDerivedComponentSectionsIso ⦋n⦌ q F)
    fun {_ _} f =>
      square_comp₃
        (S.pageOneIsoResolutionSections_hom_naturality n q f)
        (S.resolutionSectionsIsoRightDerived_hom_naturality n q f)
        (S.rightDerivedComponentSectionsIso_hom_naturality ⦋n⦌ q f)

/-! ### The first differential -/

/-- **Stacks 09WJ, the first differential.** `d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`: the
differential of the first page out of the bidegree `(p, q)` lands in the bidegree `(p + 1, q)`,
every other component being zero. Together with the type of
`CategoryTheory.SimplicialSiteSituation.cohomologySpectralSequence`, which provides
`d (p, q) (p + 1, q) : E_1^{p,q} ⟶ E_1^{p+1,q}`, this is the shape of `d_1` that Stacks 09WJ
asserts.

What that differential *is* under the identification of the first page is
`CategoryTheory.SimplicialSiteSituation.pageOneIsoColumnHomology_hom_d`: up to the sign
`(-1)^q`, the map induced on `H^q` by the differential of the complex of Stacks 0D77. -/
@[stacks 09WJ "the first differential d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}"]
theorem isZero_pageOne_d_of_ne (F : Sheaf S.totalTopology Ab.{u}) (p q p' q' : ℤ)
    (h : (p', q') ≠ (p + 1, q)) :
    (((S.cohomologySpectralSequence).obj F).page 1 le_rfl).d (p, q) (p', q') = 0 := by
  refine HomologicalComplex.shape _ _ _ fun hc => h ?_
  have hc : (p, q) + ((1 : ℤ), 1 - (1 : ℤ)) = (p', q') := hc
  rw [← hc]
  simp

/-! ### The abutment is the cohomology of the total site -/

variable (F : Sheaf S.totalTopology Ab.{u})

/-- **The integer-graded sheaf cohomology `H^n(C_total, F)`**: the cohomology of the complex
`Γ(C_total, I^•)` of global sections of the chosen injective resolution, extended by zero to
integer degrees. It vanishes for `n < 0` (`isZero_totalCohomologyZ_of_neg`) and is the `n`-th
right derived functor of `Γ(C_total, -)` for `n ≥ 0` (`totalCohomologyZ_iso_rightDerived`). -/
abbrev totalCohomologyZ (n : ℤ) : Ab.{u} :=
  (S.totalSectionsComplex (S.injectiveResolutionZ F)).homology n

/-- The integer-graded sheaf cohomology of the total site vanishes in negative degrees, the
chosen injective resolution being concentrated in the non-negative ones. -/
theorem isZero_totalCohomologyZ_of_neg (n : ℤ) (hn : n < 0) :
    IsZero (S.totalCohomologyZ F n) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ n).1
    (ShortComplex.exact_of_isZero_X₂ _
      ((Sheaf.Γ S.totalTopology Ab.{u}).map_isZero (S.isZero_injectiveResolutionZ_X F n hn)))

/-- In the degrees coming from `ℕ` the integer-graded sheaf cohomology of the total site is the
right derived functor of `Γ(C_total, -)`, i.e. the sheaf cohomology `H^n(C_total, F)`. -/
def totalCohomologyZ_iso_rightDerived (n : ℕ) :
    S.totalCohomologyZ F (n : ℤ) ≅ ((Sheaf.Γ S.totalTopology Ab.{u}).rightDerived n).obj F :=
  S.totalSectionsResolutionRightDerivedIso F n

/-- **Stacks 09WJ, the convergence.** The spectral sequence of the simplicial-site situation
abuts to `H^{p+q}(C_total, F)`: its infinity page at `(p, q)` is the `p`-th graded piece of a
finite filtration of the sheaf cohomology of the total site in degree `p + q`.

This is `sectionsSpectralSequence_abutsTo_total`, whose abutment is the cohomology of the total
complex of `A^{•,•}`, transported along the comparison of Stacks 0133 and read from the first
page. -/
@[stacks 09WJ "the abutment H^{p+q}(C_total, F) for an abelian sheaf"]
theorem cohomologySpectralSequence_abutsTo :
    CategoryTheory.SpectralSequence.AbutsTo
      ((S.cohomologySpectralSequence).obj F) (S.totalCohomologyZ F) :=
  ((S.sectionsSpectralSequence_abutsTo_total (S.injectiveResolutionZ F)
      (S.isZero_injectiveResolutionZ_X F)).of_iso
    fun n => (S.sectionsComparisonHomologyIso (S.injectiveResolutionZ F)
      (S.isZero_injectiveResolutionZ_X F) (S.injective_injectiveResolutionZ_X F) n).symm).shiftStart
    zero_le_one

end CategoryTheory.SimplicialSiteSituation

end

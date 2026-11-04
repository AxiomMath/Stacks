module

public import StacksFrontier.Algebra.Homology.HomBicomplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.SectionsComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedPlusDoubleComplex
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentTotalAcyclicity
import StacksCore.Tactic.StacksAttribute

/-!
# The cohomology spectral sequence on a ringed simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of rings on its total site.
Stacks 0D7E asserts that for `K` in `D⁺(O)` there is a spectral sequence, functorial in `K`, with

`E_1^{p,q} = H^q(C_p, K_p),  d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`

converging to `H^{p+q}(C_total, K)`. This file constructs it, following the source.

Represent `K` by a bounded below complex `I^•` of injective `O`-modules. Applying `Hom_O(-, -)` to
the resolution `… → g_{1!} O_1 → g_{0!} O_0` of Stacks 0D9B and to `I^•` gives the bicomplex

`A^{p,q} = Hom_O(g_{p!} O_p, I^q) = Γ(C_p, I^q_p)`

whose columns in the simplicial direction are the complexes of Stacks 0D9C with their degree `-1`
term omitted, and whose rows are the complexes of sections `Γ(C_p, I^•_p)`. The spectral sequence
is the one of the filtration of the total complex by the simplicial degree `p`.

* The columns are exact in positive degrees with `Γ(C_total, I^q)` as kernel in degree `0`, so the
  total complex computes `Γ(C_total, I^•)`, that is `RΓ(C_total, K)` (Stacks 0133).
* Restriction `g_p^*` to the component `C_p` is exact, so `I^•_p` represents `K_p`, and its terms
  are totally acyclic on `C_p` (Stacks 0D73), hence acyclic for `Γ(C_p, -)` (Stacks 0731 (3)). So
  the rows compute `RΓ(C_p, K_p)` by Leray's acyclicity lemma (Stacks 015E), and the first page is
  `H^q(C_p, K_p)`.
* Homotopic maps of complexes give the same map of spectral sequences from the first page on, so
  the spectral sequence is a functor of `K` in `D⁺(O)`, and the identification of its first page
  is natural in `K`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution.resolutionCochainComplex`:
  the resolution of Stacks 0D9B as a cochain complex, with `g_{p!} O_p` in degree `-p`.
* `CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution.sectionsBicomplex`: the
  bicomplex `A^{p,q} = Hom_O(g_{p!} O_p, K^q)` of a complex `K^•`, and
  `….sectionsComplexFunctor`: the complex `p ↦ Hom_O(g_{p!} O_p, M)` as a functor of the module
  `M`, which applied degreewise to `K^•` is that bicomplex with its two directions exchanged.
* `CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution.globalSectionsComplex` and
  `….sectionsAugmentation`: the complex `Γ(C_total, K^•) = Hom_O(O, K^•)` and the augmentation
  `Γ(C_total, K^•) → A^{0,•}`.
* `CategoryTheory.SimplicialSiteSituation.moduleCohomologySpectralSequence`: the spectral
  sequence, as a functor of `K` in `D⁺(O)`.

## Main results

* `SimplicialSiteSituation.SimplicialModuleResolution.exists_sectionsSpectralSequence`:
  **Stacks 0D7E**.
* `CategoryTheory.SimplicialSiteSituation.moduleCohomologySpectralSequencePageOneIso`: the first
  page `E_1^{p,q} = H^q(C_p, K_p)`, naturally in `K`.
* `CategoryTheory.SimplicialSiteSituation.abutsTo_moduleCohomologySpectralSequence`: the
  convergence to `H^{p+q}(C_total, K)`.
* `CategoryTheory.SimplicialSiteSituation.sectionsComplexFunctorEvalIso`: the term
  `Hom_O(g_{p!} O_p, M)` is `Γ(C_p, M_p)`, naturally in `M`.
* `SimplicialSiteSituation.SimplicialModuleResolution.sectionsBicomplexTotalHomologyIso`:
  Stacks 0133 for the augmentation of the complex of Stacks 0D9C — for a bounded below `K^•` of
  injective `O`-modules the total complex of `A^{•,•}` computes the cohomology of
  `Γ(C_total, K^•)`.
* `SimplicialSiteSituation.SimplicialModuleResolution.exists_sectionsSpectralSequence_rowHomology`:
  for a bounded below complex `K^•`, the spectral sequence of the bicomplex read on the objects it
  is built from — its first page the cohomology of the rows, its abutment the cohomology of the
  total complex.

## Implementation notes

Global sections `Γ(C, -)` of a sheaf of modules are those of its underlying abelian sheaf,
`CategoryTheory.Sheaf.Γ`, and `H^q(C, -)` is the cohomology of the right derived functor
`RΓ(C, -)` of that functor on the bounded below derived category. `Hom_O(O, -)` and
`Hom_O(g_{p!} O_p, -)` are identified with `Γ(C_total, -)` and `Γ(C_p, g_p^*(-))` by
`coyonedaUnitIsoModuleGlobalSections` and `sectionsComplexFunctorEvalIso`.

The spectral sequence is presented from its first page: its zeroth page is the bicomplex of a
chosen complex of injectives, which is not functorial in `K`. The general construction is
`StacksFrontier/Algebra/Homology/SpectralSequence/DerivedPlusDoubleComplex.lean`, which also serves
the abelian counterpart Stacks 0D7A. The resolution of Stacks 0D9B is a chosen one; the derived
categories are the standard ones, `CategoryTheory.HasDerivedCategory.standard`.

The bicomplex is `CochainComplex.homBicomplex`, which fills its contravariant slot through
`CochainComplex.opEquivalence` and therefore has `Hom_O(K⁻ᵖ, I^q)` in bidegree `(p, q)`; the
resolution is reindexed by negation into `ComplexShape.up ℤ` along
`ComplexShape.embeddingDownNat` so that its degree `-p` term is `g_{p!} O_p`.

Coefficients sit at the site universe, as for the resolution of Stacks 0D9B.

## References

* [Stacks Project, Tag 0D7E](https://stacks.math.columbia.edu/tag/0D7E)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D9C](https://stacks.math.columbia.edu/tag/0D9C)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
* [Stacks Project, Tag 0D73](https://stacks.math.columbia.edu/tag/0D73)
* [Stacks Project, Tag 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}
  (D : SimplicialModuleResolution S O)

/-! ### The resolution as a complex in non-positive degrees -/

/- The reindexing below is along `ComplexShape.embeddingDownNat` and takes a
`SimplicialModuleResolution`.  `CategoryTheory.SimplicialSiteSituation.moduleResolutionComplex`
reindexes along `ComplexShape.embeddingUpIntLE 0` and takes a
`SimplicialModuleResolutionActual`, a different type of resolution datum, so neither definition
can be applied to the other's argument. -/

/-- The resolution `… → g_{1!} O_1 → g_{0!} O_0` of Stacks 0D9B as a cochain complex, with
`g_{p!} O_p` in degree `-p` and zero in positive degrees. -/
public def resolutionCochainComplex : CochainComplex (SheafOfModules.{u} O) ℤ :=
  D.complex.extend ComplexShape.embeddingDownNat

/-- The term of the reindexed resolution in degree `-p` is `g_{p!} O_p`. -/
public def resolutionCochainComplexXIso (p : ℕ) :
    D.resolutionCochainComplex.X (-(p : ℤ)) ≅ D.complex.X p :=
  HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := p) rfl

/-- The reindexed resolution vanishes in positive degrees. -/
public theorem isZero_resolutionCochainComplex_X (n : ℤ) (hn : 0 < n) :
    IsZero (D.resolutionCochainComplex.X n) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingDownNat n
    fun i => by change -(i : ℤ) ≠ n; omega

/-- The reindexed resolution is concentrated in degrees `≤ 0`: it is extended by zero from the
embedding of those degrees. -/
public instance isStrictlyLE_resolutionCochainComplex :
    CochainComplex.IsStrictlyLE D.resolutionCochainComplex 0 := by
  dsimp only [resolutionCochainComplex]
  infer_instance

/-- The reindexed resolution is bounded above. -/
public theorem resolutionCochainComplex_minus :
    CochainComplex.minus (SheafOfModules.{u} O) D.resolutionCochainComplex := by
  rw [CochainComplex.minus_iff]
  refine ⟨0, ⟨fun i hi => D.isZero_resolutionCochainComplex_X i ?_⟩⟩
  exact (ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).1 hi

/-- The differential of the reindexed resolution from degree `-(m + 1)` to degree `-m` is the
differential `g_{(m+1)!} O_{m+1} → g_{m!} O_m` of the resolution. -/
public theorem resolutionCochainComplex_d (m : ℕ) :
    D.resolutionCochainComplex.d (-((m : ℤ) + 1)) (-(m : ℤ)) =
      (D.resolutionCochainComplexXIso (m + 1)).hom ≫ D.complex.d (m + 1) m ≫
        (D.resolutionCochainComplexXIso m).inv :=
  HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl

/-- The differential of the reindexed resolution from degree `-(m + 2)` to degree `-(m + 1)`. -/
public theorem resolutionCochainComplex_d_succ (m : ℕ) :
    D.resolutionCochainComplex.d (-((m : ℤ) + 1 + 1)) (-((m : ℤ) + 1)) =
      (D.resolutionCochainComplexXIso (m + 2)).hom ≫ D.complex.d (m + 2) (m + 1) ≫
        (D.resolutionCochainComplexXIso (m + 1)).inv :=
  HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat rfl rfl

/-- The differential of the reindexed resolution from degree `-1` to degree `0`. -/
public theorem resolutionCochainComplex_d_zero :
    D.resolutionCochainComplex.d (-1) 0 =
      (D.resolutionCochainComplexXIso 1).hom ≫ D.complex.d 1 0 ≫
        (D.resolutionCochainComplexXIso 0).inv :=
  HomologicalComplex.extend_d_eq _ ComplexShape.embeddingDownNat (i := 1) (j := 0) rfl rfl

/-- The augmentation `g_{0!} O_0 → O` of Stacks 0D9B, read on the degree `0` term of the
reindexed resolution. -/
public def resolutionAugmentation :
    D.resolutionCochainComplex.X 0 ⟶ SheafOfModules.unit O :=
  (D.resolutionCochainComplexXIso 0).hom ≫ D.augmentation

/-- The augmentation kills the differential arriving in degree `0`. -/
public theorem resolutionAugmentation_comp :
    D.resolutionCochainComplex.d (-1) 0 ≫ D.resolutionAugmentation = 0 := by
  rw [resolutionAugmentation, D.resolutionCochainComplex_d_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [D.augmentation_comp, Limits.comp_zero]

/-- The augmentation is epi, that of Stacks 0D9B being so. -/
public instance epi_resolutionAugmentation : Epi D.resolutionAugmentation := by
  rw [resolutionAugmentation]
  have := D.augmentation_epi
  infer_instance

/-- A map out of the degree `-i` term of the reindexed resolution killing the differential
arriving there kills the differential of the resolution of Stacks 0D9B, after the identification
of that term. -/
private theorem complex_d_comp_inv_comp_eq_zero (F : SheafOfModules.{u} O) (i : ℕ)
    (ψ : D.resolutionCochainComplex.X (-(i : ℤ)) ⟶ F)
    (hψ : D.resolutionCochainComplex.d (-((i : ℤ) + 1)) (-(i : ℤ)) ≫ ψ = 0) :
    D.complex.d (i + 1) i ≫ (D.resolutionCochainComplexXIso i).inv ≫ ψ = 0 := by
  rw [D.resolutionCochainComplex_d i] at hψ
  simp only [Category.assoc] at hψ
  refine (cancel_epi (D.resolutionCochainComplexXIso (i + 1)).hom).1 ?_
  rw [Limits.comp_zero]
  exact hψ

/-- **Factorisation in positive degree.** A map out of the degree `-(m+1)` term of the reindexed
resolution killing the differential arriving there factors through the differential leaving it,
the resolution being exact in positive degrees and the target injective. -/
public theorem exists_comp_eq_of_comp_eq_zero (F : SheafOfModules.{u} O) [Injective F] (m : ℕ)
    (ψ : D.resolutionCochainComplex.X (-((m : ℤ) + 1)) ⟶ F)
    (hψ : D.resolutionCochainComplex.d (-((m : ℤ) + 1 + 1)) (-((m : ℤ) + 1)) ≫ ψ = 0) :
    ∃ χ : D.resolutionCochainComplex.X (-(m : ℤ)) ⟶ F,
      D.resolutionCochainComplex.d (-((m : ℤ) + 1)) (-(m : ℤ)) ≫ χ = ψ := by
  have hex0 : (D.complex.sc' (m + 2) (m + 1) m).Exact := by
    rw [← HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
    exact D.exact_positive (m + 1) (by omega)
  have hex : (ShortComplex.mk (D.complex.d (m + 2) (m + 1)) (D.complex.d (m + 1) m)
      (D.complex.d_comp_d _ _ _)).Exact := hex0
  have hψ' := D.complex_d_comp_inv_comp_eq_zero F (m + 1) ψ hψ
  have hc : D.complex.d (m + 1) m ≫ hex.descToInjective _ hψ' =
      (D.resolutionCochainComplexXIso (m + 1)).inv ≫ ψ := hex.comp_descToInjective _ hψ'
  refine ⟨(D.resolutionCochainComplexXIso m).hom ≫ hex.descToInjective _ hψ', ?_⟩
  rw [D.resolutionCochainComplex_d m]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, hc, Iso.hom_inv_id_assoc]

/-- **Factorisation in degree zero.** A map out of the degree `0` term of the reindexed
resolution killing the differential arriving there factors through the augmentation, the
resolution of Stacks 0D9B being exact at `g_{0!} O_0`. -/
public theorem exists_augmentation_comp_eq (F : SheafOfModules.{u} O)
    (ψ : D.resolutionCochainComplex.X 0 ⟶ F)
    (hψ : D.resolutionCochainComplex.d (-1) 0 ≫ ψ = 0) :
    ∃ χ : SheafOfModules.unit O ⟶ F, D.resolutionAugmentation ≫ χ = ψ := by
  have hψ' := D.complex_d_comp_inv_comp_eq_zero F 0 ψ hψ
  have : Epi (ShortComplex.mk (D.complex.d 1 0) D.augmentation D.augmentation_comp).g :=
    D.augmentation_epi
  obtain ⟨χ, hχ⟩ := D.exact_zero.desc' _ hψ'
  refine ⟨χ, ?_⟩
  have hχ' : D.augmentation ≫ χ = (D.resolutionCochainComplexXIso 0).inv ≫ ψ := hχ
  rw [resolutionAugmentation, Category.assoc, hχ', Iso.hom_inv_id_assoc]

/-! ### The bicomplex of sections -/

variable (K : CochainComplex (SheafOfModules.{u} O) ℤ)

/-- **The bicomplex `A^{p,q} = Hom_O(g_{p!} O_p, K^q) = Γ(C_p, K^q_p)`** of a cochain complex
`K^•` of sheaves of `O`-modules on the total site: the Hom bicomplex of the resolution of
Stacks 0D9B and `K^•`. Its rows are the complexes of sections of Stacks 0D9C. -/
public def sectionsBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CochainComplex.homBicomplex D.resolutionCochainComplex K

/-- The term of the bicomplex in bidegree `(p, q)`, for a non-negative `p`, is
`Hom_O(g_{p!} O_p, K^q)`. -/
public def sectionsBicomplexXXIso (p : ℕ) (q : ℤ) :
    ((D.sectionsBicomplex K).X (p : ℤ)).X q ≅ AddCommGrpCat.of (D.complex.X p ⟶ K.X q) :=
  (preadditiveCoyoneda.mapIso (D.resolutionCochainComplexXIso p).symm.op).app (K.X q)

/-- **The term of the bicomplex in bidegree `(p, q)` is the group `Γ(C_p, K^q_p)`** of
Stacks 0D9C: the universal property `Hom_O(g_{p!} O_p, F) = Γ(C_p, F_p)` of the resolution,
applied to `K^q`. -/
public def sectionsBicomplexXXIsoSectionsGrp (p : ℕ) (q : ℤ) :
    ((D.sectionsBicomplex K).X (p : ℤ)).X q ≅ D.sectionsGrp (K.X q) p :=
  D.sectionsBicomplexXXIso K p q ≪≫ (D.sectionsIso (K.X q) (p + 1)).symm

/-- The diagonals of the bicomplex have finitely many nonzero terms, for a `K^•` bounded
below: the resolution is concentrated in non-positive degrees. -/
public theorem sectionsBicomplex_finite_diagonals
    (hK : CochainComplex.plus (SheafOfModules.{u} O) K) (n : ℤ) :
    {pq : ℤ × ℤ |
      ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n ∧
      ¬ IsZero (((D.sectionsBicomplex K).X pq.1).X pq.2)}.Finite :=
  CochainComplex.homBicomplex_finite_diagonals _ _ D.resolutionCochainComplex_minus hK n

/-- **The total complex `Tot^n = ⊕_{p + q = n} Γ(C_p, K^q_p)`** of the bicomplex of sections,
for a `K^•` bounded below. -/
public def sectionsBicomplexTotal (hK : CochainComplex.plus (SheafOfModules.{u} O) K) :
    CochainComplex AddCommGrpCat.{u} ℤ :=
  CochainComplex.homBicomplexTotal D.resolutionCochainComplex K
    D.resolutionCochainComplex_minus hK

/-! ### The complex of global sections and the abutment -/

/-- **The complex of global sections `Γ(C_total, K^•) = Hom_O(O, K^•)`**: the universal property
`Hom(O, F) = Γ(C_total, F)` applied degreewise to `K^•`. Its term in degree `q` is the term of
the complex of Stacks 0D9C at `K^q` in the source's degree `-1`. -/
public def globalSectionsComplex : CochainComplex AddCommGrpCat.{u} ℤ :=
  ((preadditiveCoyoneda.obj (op (SheafOfModules.unit O))).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K

/-- The term of the complex of global sections in degree `q` is the term of the complex of
Stacks 0D9C at `K^q` in the source's degree `-1`. -/
public theorem globalSectionsComplex_X (q : ℤ) :
    (globalSectionsComplex K).X q = (D.sectionsComplex (K.X q)).X 0 :=
  rfl

/-- **The augmentation of the bicomplex** in the simplicial direction: precomposition with the
augmentation `g_{0!} O_0 → O` of Stacks 0D9B, which in degree `q` is the differential of the
complex of Stacks 0D9C from the source's degree `-1` to its degree `0`. -/
public def sectionsAugmentation :
    globalSectionsComplex K ⟶ rowZero ((D.sectionsBicomplex K).flip) where
  f q := (preadditiveCoyoneda.map D.resolutionAugmentation.op).app (K.X q)
  comm' q q' _ := ((preadditiveCoyoneda.map D.resolutionAugmentation.op).naturality
    (K.d q q')).symm

/-- The terms of the bicomplex vanish in negative simplicial degree. -/
public theorem isZero_sectionsBicomplex_flip_X_X (p q : ℤ) (hq : q < 0) :
    IsZero (((D.sectionsBicomplex K).flip.X p).X q) :=
  CochainComplex.isZero_homBicomplex_X_X_of_isZero_left _ _ q p
    (D.isZero_resolutionCochainComplex_X (-q) (by omega))

/-- The diagonals of the bicomplex read in the other order are finite, for a `K^•` bounded
below. -/
public theorem diagonalFinite_sectionsBicomplex_flip
    (hK : CochainComplex.plus (SheafOfModules.{u} O) K) :
    DiagonalFinite ((D.sectionsBicomplex K).flip) := by
  obtain ⟨b, hb⟩ := (CochainComplex.plus_iff _ K).1 hK
  have := hb
  intro n
  refine (Set.finite_Icc b n).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  refine Set.mem_Icc.2 ⟨?_, ?_⟩
  · by_contra h
    exact hp (CochainComplex.isZero_homBicomplex_X_X_of_isZero_right
      D.resolutionCochainComplex K (n - p) p
      (CochainComplex.isZero_of_isStrictlyGE K b p (by omega)))
  · by_contra h
    exact hp (CochainComplex.isZero_homBicomplex_X_X_of_isZero_left
      D.resolutionCochainComplex K (n - p) p
      (D.isZero_resolutionCochainComplex_X (-(n - p)) (by omega)))

/-- **The columns of the bicomplex in the simplicial direction are exact in positive degree**,
for a `K^q` injective: they are the complexes of Stacks 0D9C with their degree `-1` term
omitted. -/
public theorem exactAt_sectionsBicomplex_flip_X (p : ℤ) (hinj : Injective (K.X p)) (m : ℕ) :
    ((D.sectionsBicomplex K).flip.X p).ExactAt ((m : ℤ) + 1) := by
  have := hinj
  rw [HomologicalComplex.exactAt_iff' _ ((m : ℤ)) ((m : ℤ) + 1) ((m : ℤ) + 1 + 1)
    (by simp) (by simp), ShortComplex.ab_exact_iff]
  intro ψ hψ
  obtain ⟨χ, hχ⟩ := D.exists_comp_eq_of_comp_eq_zero (K.X p) m ψ hψ
  exact ⟨χ, hχ⟩

/-- **The augmentation is a kernel of the first simplicial differential**, which is exactness of
the complex of Stacks 0D9C in the source's degrees `-1` and `0`. -/
public theorem inducesIsoKernel_sectionsAugmentation (p : ℤ) :
    ∃ hα : (D.sectionsAugmentation K).f p ≫ ((D.sectionsBicomplex K).flip.X p).d 0 1 = 0,
      IsIso (kernel.lift (((D.sectionsBicomplex K).flip.X p).d 0 1)
        ((D.sectionsAugmentation K).f p) hα) := by
  have key : ∀ g : SheafOfModules.unit O ⟶ K.X p,
      D.resolutionCochainComplex.d (-1) 0 ≫ D.resolutionAugmentation ≫ g = 0 := by
    intro g
    rw [← Category.assoc, D.resolutionAugmentation_comp, Limits.zero_comp]
  have hα : (D.sectionsAugmentation K).f p ≫ ((D.sectionsBicomplex K).flip.X p).d 0 1 = 0 :=
    ConcreteCategory.ext_apply (fun g => (key g).trans (by rfl))
  refine ⟨hα, ?_⟩
  have hmono : Mono ((D.sectionsAugmentation K).f p) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    exact (cancel_epi D.resolutionAugmentation).mp
      (show D.resolutionAugmentation ≫ a = D.resolutionAugmentation ≫ b from hab)
  have hex : (ShortComplex.mk ((D.sectionsAugmentation K).f p)
      (((D.sectionsBicomplex K).flip.X p).d 0 1) hα).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro ψ hψ
    obtain ⟨χ, hχ⟩ := D.exists_augmentation_comp_eq (K.X p) ψ hψ
    exact ⟨χ, hχ⟩
  have := hmono
  have : Epi (kernel.lift _ _ hα) := (ShortComplex.mk _ _ hα).exact_iff_epi_kernel_lift.1 hex
  have : Mono (kernel.lift _ _ hα) := mono_of_mono_fac (kernel.lift_ι _ _ hα)
  exact isIso_of_mono_of_epi _

/-- **The hypotheses of Stacks 0133** for the augmentation of the bicomplex in the simplicial
direction, for a bounded below `K^•` of injective `O`-modules. -/
public theorem hypotheses_sectionsAugmentation
    (hK : CochainComplex.plus (SheafOfModules.{u} O) K)
    (hinj : ∀ q : ℤ, Injective (K.X q)) :
    Hypotheses (globalSectionsComplex K) ((D.sectionsBicomplex K).flip)
      (D.sectionsAugmentation K) where
  diagonalFinite := D.diagonalFinite_sectionsBicomplex_flip K hK
  zero_of_neg p q hq := D.isZero_sectionsBicomplex_flip_X_X K p q hq
  exactAt_of_ne_zero p q hq := by
    rcases lt_trichotomy q 0 with h | h | h
    · exact HomologicalComplex.ExactAt.of_isZero (D.isZero_sectionsBicomplex_flip_X_X K p q h)
    · exact absurd h hq
    · have hqq : (((q - 1).toNat : ℤ)) + 1 = q := by omega
      exact hqq ▸ D.exactAt_sectionsBicomplex_flip_X K p (hinj p) (q - 1).toNat
  inducesIsoKernel p := D.inducesIsoKernel_sectionsAugmentation K p

/-- **Stacks 0133 for the augmentation of the complex of Stacks 0D9C.** For a bounded below `K^•`
of injective `O`-modules the total complex of `A^{•,•}` computes the cohomology of
`Γ(C_total, K^•)`: the columns of `A^{•,•}` in the simplicial direction are the complexes of
Stacks 0D9C, exact away from the source's degree `-1` and with the augmentation as a kernel of
the first differential. -/
public def sectionsBicomplexTotalHomologyIso
    (hK : CochainComplex.plus (SheafOfModules.{u} O) K)
    (hinj : ∀ q : ℤ, Injective (K.X q)) (n : ℤ) :
    (D.sectionsBicomplexTotal K hK).homology n ≅ (globalSectionsComplex K).homology n := by
  have hfin := D.sectionsBicomplex_finite_diagonals K hK
  let _ : (D.sectionsBicomplex K).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ (ComplexShape.up ℤ) hfin
  let _ : ((D.sectionsBicomplex K).flip).HasTotal (ComplexShape.up ℤ) :=
    hasTotal_of_diagonalFinite _ (D.diagonalFinite_sectionsBicomplex_flip K hK)
  exact ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
      ((D.sectionsBicomplex K).totalFlipIso (ComplexShape.up ℤ))).symm ≪≫
    (comparisonHomologyIso (globalSectionsComplex K) ((D.sectionsBicomplex K).flip)
      (D.sectionsAugmentation K) (D.hypotheses_sectionsAugmentation K hK hinj) n).symm

/-! ### The spectral sequence -/

/-- The spectral sequence of the bicomplex of sections, read on the objects it is built from:
its first page is the cohomology `H^q(Γ(C_p, K^•_p))` of a row of the bicomplex, its first
differential is induced by the differential of the complex of Stacks 0D9C, and it abuts to the
cohomology of the total complex. -/
public theorem exists_sectionsSpectralSequence_rowHomology
    (hK : CochainComplex.plus (SheafOfModules.{u} O) K) :
    ∃ (E : CohomologicalSpectralSequence AddCommGrpCat.{u} 0)
      (β : ∀ p q : ℤ, (E.page 1 zero_le_one).X (p, q) ≅ ((D.sectionsBicomplex K).X p).homology q),
      (∀ p q : ℤ, (E.page 1 zero_le_one).d (p, q) (p + 1, q) ≫ (β (p + 1) q).hom =
        (β p q).hom ≫
          HomologicalComplex.homologyMap ((D.sectionsBicomplex K).d p (p + 1)) q) ∧
      SpectralSequence.AbutsTo E (fun n => (D.sectionsBicomplexTotal K hK).homology n) := by
  classical
  have hfin := D.sectionsBicomplex_finite_diagonals K hK
  let _ : (D.sectionsBicomplex K).HasTotal (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_finite _ (ComplexShape.up ℤ) hfin
  let T := (D.sectionsBicomplex K).totalFiltration₁
  let Fil : ∀ (_p n : ℤ), Subobject (T.X.X n) := fun p n =>
    Subobject.mk ((T.filtration.ι.app (op p)).f n)
  let Zc : ∀ (_r _p n : ℤ), Subobject (T.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1))
  let Dc : ∀ (_r _p n : ℤ), Subobject (T.X.X n) := fun r p n =>
    Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1))
  have hFil : ∀ p n : ℤ, Fil p n = Subobject.mk ((T.filtration.ι.app (op p)).f n) :=
    fun _ _ => rfl
  have hZc : ∀ r p n : ℤ, Zc r p n =
      Fil p n ⊓ (Subobject.pullback (T.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) :=
    fun _ _ _ => rfl
  have hDc : ∀ r p n : ℤ, Dc r p n = Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (T.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1)) :=
    fun _ _ _ => rfl
  obtain ⟨E, e, -, hδ, -, -, -⟩ :=
    CochainComplex.exists_cohomologicalSpectralSequence T Fil hFil Zc hZc Dc hDc
  obtain ⟨-, ⟨β, hβ⟩, -⟩ := (D.sectionsBicomplex K).exists_iso_pages_totalFiltration₁
    Fil hFil Zc hZc Dc hDc E e hδ
  have hAbuts : SpectralSequence.AbutsTo E (fun n => T.X.homology n) :=
    CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite T Fil hFil Zc hZc Dc hDc E e
      ((D.sectionsBicomplex K).isDegreewiseFinite_totalFiltration₁ hfin)
  exact ⟨E, β, hβ, hAbuts⟩

/-! ### The rows of the bicomplex as a functor of the module -/

/-- **The complex `p ↦ Hom_O(g_{p!} O_p, M)`** of a sheaf of `O`-modules `M`, as a functor of
`M`: `Hom_O(-, M)` applied to the resolution of Stacks 0D9B, reindexed so that the term in
degree `p` is `Hom_O(g_{p!} O_p, M)`. Its terms are the groups `Γ(C_p, M_p)` of Stacks 0D9C, and
applied degreewise to a complex `K^•` it is the bicomplex `A^{•,•}` with its two directions
exchanged (`sectionsComplexFunctor_mapHomologicalComplex_obj`). -/
public def sectionsComplexFunctor :
    SheafOfModules.{u} O ⥤ CochainComplex AddCommGrpCat.{u} ℤ where
  obj M := ((preadditiveYoneda.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CochainComplex.opEquivalence _).functor.obj (op D.resolutionCochainComplex))
  map f := (NatTrans.mapHomologicalComplex (preadditiveYoneda.map f) (ComplexShape.up ℤ)).app _
  map_id M := by
    rw [Functor.map_id, NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [Functor.map_comp, NatTrans.mapHomologicalComplex_comp]
    rfl

/-- The functor of rows is additive. -/
public instance sectionsComplexFunctor_additive : D.sectionsComplexFunctor.Additive where
  map_add {M N f g} := by
    ext p x
    exact Preadditive.comp_add (C := SheafOfModules.{u} O) _ _ _ _ f g

/-- Applied degreewise to a complex `K^•`, the functor of rows is the bicomplex `A^{•,•}` with
its two directions exchanged. -/
public theorem sectionsComplexFunctor_mapHomologicalComplex_obj :
    (D.sectionsComplexFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K =
      (D.sectionsBicomplex K).flip :=
  rfl

/-- The functor of rows vanishes in negative degrees, the resolution of Stacks 0D9B being
concentrated in non-positive degrees. -/
public theorem isZero_sectionsComplexFunctor_obj_X (M : SheafOfModules.{u} O) (p : ℤ)
    (hp : p < 0) : IsZero ((D.sectionsComplexFunctor.obj M).X p) :=
  (preadditiveCoyoneda.map_isZero (D.isZero_resolutionCochainComplex_X (-p) (by omega)).op).obj M

/-- **The augmentation `Γ(C_total, K^•) → A^{0,•}`, naturally in `K^•`**: precomposition with the
augmentation `g_{0!} O_0 → O` of Stacks 0D9B, from the complex `Hom_O(O, K^•)` to the row of
the bicomplex in simplicial degree `0`. -/
public def sectionsAugmentationNat :
    (preadditiveCoyoneda.obj (op (SheafOfModules.unit O))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⟶
      D.sectionsComplexFunctor.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        rowZeroFunctor AddCommGrpCat.{u} where
  app K := D.sectionsAugmentation K
  naturality K L f := by
    ext q x
    exact (Category.assoc (obj := SheafOfModules.{u} O) _ _ _)

/-- **The hypotheses of Stacks 0133** for the augmentation, at a bounded below complex of
injective `O`-modules. -/
public theorem hypotheses_sectionsAugmentationNat (Z : CochainComplex (SheafOfModules.{u} O) ℤ)
    (n : ℤ) (hZ : Z.IsStrictlyGE n) (hinj : ∀ q : ℤ, Injective (Z.X q)) :
    Hypotheses (((preadditiveCoyoneda.obj (op (SheafOfModules.unit O))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z)
      ((D.sectionsComplexFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      (D.sectionsAugmentationNat.app Z) :=
  D.hypotheses_sectionsAugmentation Z ((CochainComplex.plus_iff _ Z).2 ⟨n, hZ⟩) hinj

end CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution

namespace CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}
  (D : SimplicialModuleResolution S O) (K : CochainComplex (SheafOfModules.{u} O) ℤ)

/-- **The bicomplex is nonzero wherever the sections are.** Its term in bidegree `(p, q)` is the
group `Γ(C_p, K^q_p)` of Stacks 0D9C, so the construction is not degenerate. -/
public theorem not_isZero_sectionsBicomplex_X_X (p : ℕ) (q : ℤ)
    (h : ¬ IsZero (D.sectionsGrp (K.X q) p)) :
    ¬ IsZero (((D.sectionsBicomplex K).X (p : ℤ)).X q) :=
  fun hz => h ((Iso.isZero_iff (D.sectionsBicomplexXXIsoSectionsGrp K p q)).1 hz)

end CategoryTheory.SimplicialSiteSituation.SimplicialModuleResolution

/-! ### Global sections and restriction to a component -/

namespace CategoryTheory.SimplicialSiteSituation

/-- **`Hom_O(O, -) = Γ(C, -)`** on sheaves of modules over a small site, with `Γ(C, -)` the global
sections of the underlying abelian sheaf, `CategoryTheory.Sheaf.Γ`. -/
public def coyonedaUnitIsoModuleGlobalSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ≅
      SheafOfModules.toSheaf R ⋙ Sheaf.Γ J AddCommGrpCat.{u} :=
  Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso R ≪≫
    (Stacks.Cohomology.globalSectionsUnderlyingIso R).symm

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})

/-- Restriction of sheaves of modules to a component is additive. -/
local instance componentModuleRestriction_additive (n : SimplexCategory) :
    (componentModuleRestriction S O n).Additive where
  map_add := rfl

/-- Restriction of sheaves of modules to a component is left exact. -/
local instance componentModuleRestriction_preservesFiniteLimits (n : SimplexCategory) :
    PreservesFiniteLimits (componentModuleRestriction S O n) := by
  unfold componentModuleRestriction
  infer_instance

/-- Restriction of sheaves of modules to a component is right exact, the component inclusion
being cocontinuous. -/
local instance componentModuleRestriction_preservesFiniteColimits (n : SimplexCategory) :
    PreservesFiniteColimits (componentModuleRestriction S O n) := by
  unfold componentModuleRestriction
  open Stacks.SheafOfModules.PushforwardRightExact in
  exact preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
    (componentFunctor S n) _ (isAlmostCocontinuous_of_isCocontinuous _ _ _)

/-- Lower shriek of modules from a component is additive, being a left adjoint. -/
local instance componentModuleLowerShriek_additive (n : SimplexCategory) :
    (componentModuleLowerShriek S O n).Additive :=
  (componentModuleLowerShriekAdjunction S O n).left_adjoint_additive

/-- **`Hom_O(g_{p!} O_p, M) = Γ(C_p, M_p)`, naturally in `M`**: the term in degree `p` of the
functor of rows is global sections on the component `C_p` of the restriction `g_p^*`, by the
adjunction `g_{p!} ⊣ g_p^*` of Stacks 0D72 and `Hom_{O_p}(O_p, -) = Γ(C_p, -)`. -/
public def sectionsComplexFunctorEvalIso (Da : SimplicialModuleResolutionActual S O) (p : ℕ) :
    Da.sectionsComplexFunctor ⋙
        HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (p : ℤ) ≅
      componentModuleRestriction S O ⦋p⦌ ⋙
        (SheafOfModules.toSheaf (componentRingSheaf S O ⦋p⦌) ⋙
          Sheaf.Γ (S.componentTopology ⦋p⦌) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun M => (preadditiveCoyoneda.mapIso
      (Da.resolutionCochainComplexXIso p ≪≫ eqToIso (Da.lowerShriekDegreeEq p)).symm.op).app M)
      (fun f => by
        ext x
        exact (Category.assoc (obj := SheafOfModules.{u} O) _ _ _)) ≪≫
    NatIso.ofComponents (fun M => ((componentModuleLowerShriekAdjunction S O ⦋p⦌).homAddEquiv
        (SheafOfModules.unit (componentRingSheaf S O ⦋p⦌)) M).toAddCommGrpIso)
      (fun f => by
        ext x
        exact (componentModuleLowerShriekAdjunction S O ⦋p⦌).homEquiv_naturality_right x f) ≪≫
    Functor.isoWhiskerLeft (componentModuleRestriction S O ⦋p⦌)
      (coyonedaUnitIsoModuleGlobalSections (componentRingSheaf S O ⦋p⦌))

/-! ### The spectral sequence on `D⁺(O)` -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The spectral sequence of Stacks 0D7E, as a functor of `K` in `D⁺(O)`.** An object `K` is
represented by a bounded below complex of injective `O`-modules `I^•`, and sent to the spectral
sequence of the filtration by the simplicial degree of the total complex of the bicomplex
`A^{p,q} = Hom_O(g_{p!} O_p, I^q) = Γ(C_p, I^q_p)`, presented from its first page. Homotopic maps
of complexes induce the same map from the first page on, which makes it a functor of `K`. The
resolution of Stacks 0D9B is a chosen one. -/
public def moduleCohomologySpectralSequence :
    DerivedCategory.Plus (SheafOfModules.{u} O) ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u} 1 :=
  Stacks.DegreewiseSpectralSequence.derivedFunctor
    (nonempty_simplicialModuleResolution S O).some.sectionsComplexFunctor

/-- **`E_1^{p,q} = H^q(C_p, K_p)`, naturally in `K`**: the first page in column `p ≥ 0` is the
`q`-th cohomology of `RΓ(C_p, g_p^* K)`. The terms `g_p^* I^q` of the restriction of a bounded
below complex of injectives are totally acyclic on `C_p` (Stacks 0D73), hence acyclic for
`Γ(C_p, -)` (Stacks 0731 (3)), so the row `Γ(C_p, I^•_p)` computes `RΓ(C_p, K_p)` by Leray's
acyclicity lemma (Stacks 015E). -/
public def moduleCohomologySpectralSequencePageOneIso (p : ℕ) (q : ℤ) :
    moduleCohomologySpectralSequence S O ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u} _ ((p : ℤ), q) ≅
      (componentModuleRestriction S O ⦋p⦌).mapDerivedCategoryPlus ⋙
        (SheafOfModules.toSheaf (componentRingSheaf S O ⦋p⦌) ⋙
          Sheaf.Γ (S.componentTopology ⦋p⦌) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q :=
  Stacks.DegreewiseSpectralSequence.derivedPageOneIsoOfRightAcyclic _ (p : ℤ) q
    (componentModuleRestriction S O ⦋p⦌) _
    (sectionsComplexFunctorEvalIso S O (nonempty_simplicialModuleResolution S O).some p)
    (fun I hI => by
      have := hI
      exact Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_moduleGlobalSections _ _
        (S.isTotallyAcyclic_componentModule_of_injective ⦋p⦌ O I))

/-- The first page vanishes in the negative columns, the resolution of Stacks 0D9B being
concentrated in non-positive degrees. -/
public theorem isZero_moduleCohomologySpectralSequence_page_one
    (K : DerivedCategory.Plus (SheafOfModules.{u} O)) (p q : ℤ) (hp : p < 0) :
    IsZero ((((moduleCohomologySpectralSequence S O).obj K).page 1 le_rfl).X (p, q)) := by
  let D := (nonempty_simplicialModuleResolution S O).some.toSimplicialModuleResolution
  have hz : ∀ M : SheafOfModules.{u} O, IsZero ((D.sectionsComplexFunctor.obj M).X p) :=
    fun M => D.isZero_sectionsComplexFunctor_obj_X M p hp
  have h := Stacks.DegreewiseSpectralSequence.isZero_derivedFunctor_page_one
    D.sectionsComplexFunctor p q hz K
  exact h

/-- **The spectral sequence converges to `H^{p+q}(C_total, K)`**, the cohomology of
`RΓ(C_total, K)`. On a bounded below complex of injectives `I^•` the columns of the bicomplex in
the simplicial direction are the complexes of Stacks 0D9C, exact with `Γ(C_total, I^q)` as kernel
in degree `0`, so the total complex computes `Γ(C_total, I^•)` (Stacks 0133). -/
public theorem abutsTo_moduleCohomologySpectralSequence
    (K : DerivedCategory.Plus (SheafOfModules.{u} O)) :
    CategoryTheory.SpectralSequence.AbutsTo ((moduleCohomologySpectralSequence S O).obj K)
      (fun n => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
        ((SheafOfModules.toSheaf O ⋙
          Sheaf.Γ S.totalTopology AddCommGrpCat.{u}).rightDerivedFunctorPlus.obj K)) := by
  unfold moduleCohomologySpectralSequence
  let D := (nonempty_simplicialModuleResolution S O).some.toSimplicialModuleResolution
  have h := Stacks.DegreewiseSpectralSequence.abutsTo_derivedFunctor D.sectionsComplexFunctor
    (preadditiveCoyoneda.obj (op (SheafOfModules.unit O))) D.sectionsAugmentationNat
    D.hypotheses_sectionsAugmentationNat K
  exact h.of_iso fun n => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).mapIso
    ((Functor.rightDerivedFunctorPlusNatIso (coyonedaUnitIsoModuleGlobalSections O)).app K)

namespace SimplicialModuleResolution

/-- **Stacks 0D7E.** In Situation 09WE let `O` be a sheaf of rings on the total site. For `K` in
`D⁺(O)` there is a spectral sequence `(E_r, d_r)`, functorial in `K` and presented from its first
page, with

`E_1^{p,q} = H^q(C_p, K_p),  d_1^{p,q} : E_1^{p,q} → E_1^{p+1,q}`

converging to `H^{p+q}(C_total, K)`. Here `K_p = g_p^* K` is the restriction of `K` to the
component `C_p` (Stacks 0D72), `H^q(C_p, -)` is the cohomology of `RΓ(C_p, -)` on `D⁺(O_p)` and
`H^n(C_total, -)` that of `RΓ(C_total, -)` on `D⁺(O)`, global sections of a sheaf of modules
being those of its underlying abelian sheaf. The identification of the first page is natural in
`K`, and the first page vanishes in the negative columns. -/
@[stacks 0D7E]
public theorem exists_sectionsSpectralSequence :
    ∃ E : DerivedCategory.Plus (SheafOfModules.{u} O) ⥤
        CohomologicalSpectralSequence AddCommGrpCat.{u} 1,
      (∀ (p : ℕ) (q : ℤ), Nonempty (E ⋙
          CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u} _ 1 1 le_rfl ⋙
            HomologicalComplex.eval AddCommGrpCat.{u} _ ((p : ℤ), q) ≅
        (componentModuleRestriction S O ⦋p⦌).mapDerivedCategoryPlus ⋙
          (SheafOfModules.toSheaf (componentRingSheaf S O ⦋p⦌) ⋙
            Sheaf.Γ (S.componentTopology ⦋p⦌) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
            DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} q)) ∧
      (∀ (K : DerivedCategory.Plus (SheafOfModules.{u} O)) (p q : ℤ), p < 0 →
        IsZero (((E.obj K).page 1 le_rfl).X (p, q))) ∧
      ∀ K : DerivedCategory.Plus (SheafOfModules.{u} O),
        CategoryTheory.SpectralSequence.AbutsTo (E.obj K)
          (fun n => (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
            ((SheafOfModules.toSheaf O ⋙
              Sheaf.Γ S.totalTopology AddCommGrpCat.{u}).rightDerivedFunctorPlus.obj K)) :=
  ⟨moduleCohomologySpectralSequence S O,
    fun p q => ⟨moduleCohomologySpectralSequencePageOneIso S O p q⟩,
    isZero_moduleCohomologySpectralSequence_page_one S O,
    abutsTo_moduleCohomologySpectralSequence S O⟩

end SimplicialModuleResolution

end Derived

end CategoryTheory.SimplicialSiteSituation

end

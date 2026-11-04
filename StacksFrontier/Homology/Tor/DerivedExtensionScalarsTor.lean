module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Derived extension of scalars of a module, and its left derived functors

Let `f : R →+* R'` be a homomorphism of commutative rings and `M` an `R`-module. Reading `M` as
the object `M[0]` of `D(R)` and applying total derived extension of scalars gives `M ⊗ᴸ_R R'`,
whose cohomology in degree `-i` is the `i`-th left derived functor of extension of scalars
evaluated at `M` — that is, `Tor_i^R(R', M)` with its `R'`-module structure.

## Main definitions

* `RingTheory.TorIndependence.derivedExtensionComparisonIso`: at a complex where the comparison
  morphism of the derived functor is invertible, the derived extension is the termwise
  extension.
* `RingTheory.TorIndependence.derivedExtensionSingleIsoLeftDerived`: the natural isomorphism

  `H^{-i}(ext^L_{R → R'}(M[0])) ≅ (L_i ext_{R → R'})(M)`.

## Implementation notes

The model of the derived category is a free binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]`
for each of the two rings; nothing below pins it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

attribute [local implicit_reducible]
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral
  CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplex
  CategoryTheory.ProjectiveResolution.cochainComplex

universe u w

namespace RingTheory.TorIndependence

variable {R R' : Type u} [CommRing R] [CommRing R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-! ### The comparison with the termwise extension -/

/-- The comparison morphism of derived extension of scalars is invertible at the cochain complex
underlying a projective resolution: that complex is strictly bounded above by `0` and projective
in every degree. -/
instance isIso_comparison_app_cochainComplex (f : R →+* R') {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) :
    IsIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app P.cochainComplex) :=
  (totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison_isIso_of_projective
    P.cochainComplex 0

/-- The comparison morphism of derived extension of scalars is invertible at the extension to
`ℤ`-indexed cochain complexes of the chain complex of a projective resolution. -/
instance isIso_comparison_app_extend (f : R →+* R') {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) :
    IsIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app
      (P.complex.extend ComplexShape.embeddingDownNat)) :=
  (totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison_isIso_of_projective
    P.cochainComplex 0

/-- A bounded-above complex of projectives has an invertible comparison morphism. -/
theorem isIso_comparison_app_of_projective (f : R →+* R')
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) [P.IsStrictlyLE m]
    [∀ i, Projective (P.X i)] :
    IsIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app P) :=
  (totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison_isIso_of_projective P m

/-- **The derived extension of a complex of projectives is its termwise extension.** -/
def derivedExtensionComparisonIso (f : R →+* R') (P : CochainComplex (ModuleCat.{u} R) ℤ)
    [IsIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app P)] :
    (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  asIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app P)

/-- `derivedExtensionComparisonIso` is natural in the complex: it intertwines the derived
extension of `ψ : P ⟶ P'` with the termwise extension of `ψ`. -/
theorem derivedExtensionComparisonIso_hom_naturality (f : R →+* R')
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    [IsIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app P)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.app P')] (ψ : P ⟶ P') :
    (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.map (DerivedCategory.Q.map ψ) ≫
        (derivedExtensionComparisonIso f P').hom =
      (derivedExtensionComparisonIso f P).hom ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ) :=
  (totalDerivedExtensionScalars.{u, u, u, w, w} f).comparison.naturality ψ

/-- The homology functor of the derived category, read on a complex. -/
def derivedHomologyIso (n : ℤ) (K : CochainComplex (ModuleCat.{u} R') ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).obj (DerivedCategory.Q.obj K) ≅
      K.homology n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R') n).app K

/-- `derivedHomologyIso` is natural in the complex. -/
theorem derivedHomologyIso_hom_naturality (n : ℤ)
    {K L : CochainComplex (ModuleCat.{u} R') ℤ} (χ : K ⟶ L) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (DerivedCategory.Q.map χ) ≫
        (derivedHomologyIso n L).hom =
      (derivedHomologyIso n K).hom ≫ HomologicalComplex.homologyMap χ n :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R') n).hom.naturality χ

/-! ### A projective resolution read in the derived category -/

/-- The derived category reads the cochain complex of a projective resolution of `M` as
`M[0]`. -/
def projectiveResolutionIsoSingle {M : ModuleCat.{u} R} (P : ProjectiveResolution M) :
    DerivedCategory.Q.obj P.cochainComplex ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M :=
  asIso (DerivedCategory.Q.map P.π')

/-- A morphism of resolutions lifting `g` is carried by the localization functor to `g[0]`. -/
theorem projectiveResolutionIsoSingle_hom_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (P : ProjectiveResolution M) (P' : ProjectiveResolution N)
    (ψ : P.cochainComplex ⟶ P'.cochainComplex)
    (hψ : ψ ≫ P'.π' = P.π' ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g) :
    DerivedCategory.Q.map ψ ≫ (projectiveResolutionIsoSingle P').hom =
      (projectiveResolutionIsoSingle P).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g := by
  dsimp only [projectiveResolutionIsoSingle, asIso_hom]
  show DerivedCategory.Q.map ψ ≫ DerivedCategory.Q.map P'.π' =
    DerivedCategory.Q.map P.π' ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g)
  rw [← Functor.map_comp, ← Functor.map_comp, hψ]

/-- The same square with the two isomorphisms inverted. -/
theorem projectiveResolutionIsoSingle_inv_naturality {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (P : ProjectiveResolution M) (P' : ProjectiveResolution N)
    (ψ : P.cochainComplex ⟶ P'.cochainComplex)
    (hψ : ψ ≫ P'.π' = P.π' ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g) :
    (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g ≫
        (projectiveResolutionIsoSingle P').inv =
      (projectiveResolutionIsoSingle P).inv ≫ DerivedCategory.Q.map ψ := by
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (projectiveResolutionIsoSingle_hom_naturality g P P' ψ hψ).symm

/-! ### From the extension of a cochain complex to the extension of a chain complex -/

/-- The embedding of `ℕ`-indexed chain complexes into `ℤ`-indexed cochain complexes sends `i`
to `-i`. -/
theorem embeddingDownNat_f (i : ℕ) : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl

/-- Termwise extension of scalars commutes with extending a chain complex to a cochain
complex. -/
def extendComplexIso (f : R →+* R') (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℤ) :
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (K.extend ComplexShape.embeddingDownNat)).homology n ≅
      ((((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K).extend ComplexShape.embeddingDownNat).homology n :=
  HomologicalComplex.homologyMapIso
    (HomologicalComplex.mapHomologicalComplexExtendIso (ModuleCat.extendScalars.{u, u, u} f)
      K ComplexShape.embeddingDownNat).symm n

/-- `extendComplexIso` is natural in the chain complex. -/
theorem extendComplexIso_hom_naturality (f : R →+* R')
    {K K' : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ K') (n : ℤ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)) n ≫
        (extendComplexIso f K' n).hom =
      (extendComplexIso f K n).hom ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.down ℕ)).map φ) ComplexShape.embeddingDownNat) n := by
  dsimp only [extendComplexIso, HomologicalComplex.homologyMapIso, Iso.symm_hom]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
  exact congrArg (HomologicalComplex.homologyMap · n)
    (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
      (ModuleCat.extendScalars.{u, u, u} f) K φ ComplexShape.embeddingDownNat)

/-- The `i`-th left derived functor of extension of scalars at `M`, read as the homology of the
termwise extension of a projective resolution. This is
`CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` with its source written as a homology
rather than as the homology functor applied to a complex. -/
def isoLeftDerivedObjHomology (f : R →+* R') {M : ModuleCat.{u} R} (P : ProjectiveResolution M)
    (i : ℕ) :
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology i ≅
      ((ModuleCat.extendScalars.{u, u, u} f).leftDerived i).obj M :=
  (P.isoLeftDerivedObj (ModuleCat.extendScalars.{u, u, u} f) i).symm

/-- `isoLeftDerivedObjHomology` is natural in `M`, along a morphism `φ` of projective resolutions
lifting `g : M ⟶ N`. -/
theorem isoLeftDerivedObjHomology_hom_naturality (f : R →+* R') {M N : ModuleCat.{u} R}
    (g : M ⟶ N) (P : ProjectiveResolution M) (P' : ProjectiveResolution N)
    (φ : P.complex ⟶ P'.complex) (comm : φ.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ g) (i : ℕ) :
    HomologicalComplex.homologyMap
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ) i ≫ (isoLeftDerivedObjHomology f P' i).hom =
      (isoLeftDerivedObjHomology f P i).hom ≫
        ((ModuleCat.extendScalars.{u, u, u} f).leftDerived i).map g :=
  (ProjectiveResolution.isoLeftDerivedObj_inv_naturality g P P' φ comm
    (ModuleCat.extendScalars.{u, u, u} f) i).symm

/-! ### The composite identification -/

/-- **The cohomology in degree `-i` of the derived extension of `M[0]` is the `i`-th left derived
functor of extension of scalars at `M`**, computed on a projective resolution of `M`. -/
def singleDerivedExtensionIsoLeftDerivedOfResolution (f : R →+* R') {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (i : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).obj
        ((totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≅
      ((ModuleCat.extendScalars.{u, u, u} f).leftDerived i).obj M :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).mapIso
      ((totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.mapIso
        (projectiveResolutionIsoSingle P).symm) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).mapIso
      (derivedExtensionComparisonIso f (P.complex.extend ComplexShape.embeddingDownNat)) ≪≫
    derivedHomologyIso (-(i : ℤ))
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P.complex.extend ComplexShape.embeddingDownNat)) ≪≫
    extendComplexIso f P.complex (-(i : ℤ)) ≪≫
    HomologicalComplex.extendHomologyIso
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex) ComplexShape.embeddingDownNat
      (embeddingDownNat_f i) ≪≫
    isoLeftDerivedObjHomology f P i

/-- The composite identification is natural in `M`, along any lift of `g` to the two chosen
resolutions. -/
theorem singleDerivedExtensionIsoLeftDerivedOfResolution_hom_naturality (f : R →+* R')
    {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (P : ProjectiveResolution M) (P' : ProjectiveResolution N)
    (φ : P.complex ⟶ P'.complex)
    (comm : φ.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ g)
    (hφ : HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat ≫ P'.π' =
      P.π' ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g)
    (i : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map
        ((totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.map
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g)) ≫
        (singleDerivedExtensionIsoLeftDerivedOfResolution f P' i).hom =
      (singleDerivedExtensionIsoLeftDerivedOfResolution f P i).hom ≫
        ((ModuleCat.extendScalars.{u, u, u} f).leftDerived i).map g := by
  have key : ∀ {X Y Z W : DerivedCategory (ModuleCat.{u} R')} (a : X ⟶ Y) (b : Y ⟶ W)
      (c : X ⟶ Z) (d : Z ⟶ W), a ≫ b = c ≫ d →
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map a ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map b =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map c ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))).map d :=
    fun a b c d h => by rw [← Functor.map_comp, ← Functor.map_comp, h]
  have k1 := key (a := (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map g))
    (b := (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.map
        (projectiveResolutionIsoSingle P').inv)
    (c := (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.map
        (projectiveResolutionIsoSingle P).inv)
    (d := (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor.map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)))
    (by
      rw [← Functor.map_comp, ← Functor.map_comp,
        projectiveResolutionIsoSingle_inv_naturality g P P'
          (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) hφ])
  have k2 := key _ _ _ _
    (derivedExtensionComparisonIso_hom_naturality f
      (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat))
  have k3 := derivedHomologyIso_hom_naturality (R' := R') (-(i : ℤ))
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat))
  have k4 := extendComplexIso_hom_naturality f φ (-(i : ℤ))
  have k5 := HomologicalComplex.extendHomologyIso_hom_naturality
    (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
      (ComplexShape.down ℕ)).map φ) ComplexShape.embeddingDownNat (embeddingDownNat_f i)
  have k6 := isoLeftDerivedObjHomology_hom_naturality f g P P' φ comm i
  dsimp only [singleDerivedExtensionIsoLeftDerivedOfResolution, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [reassoc_of% k1, reassoc_of% k2, reassoc_of% k3, reassoc_of% k4, reassoc_of% k5, k6]

/-- The canonical lift of `g` to the chosen projective resolutions, extended to cochain
complexes, is compatible with the two quasi-isomorphisms to `M[0]` and `N[0]`. -/
theorem extendMap_lift_comp_π' {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (P : ProjectiveResolution M) (P' : ProjectiveResolution N) :
    HomologicalComplex.extendMap (ProjectiveResolution.lift g P P')
        ComplexShape.embeddingDownNat ≫ P'.π' =
      P.π' ≫ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map g :=
  have comm : (ProjectiveResolution.lift g P P').f 0 ≫ P'.π.f 0 =
      P.π.f 0 ≫ ((ChainComplex.single₀ (ModuleCat.{u} R)).map g).f 0 := by
    simpa using ProjectiveResolution.lift_commutes_zero g P P'
  ProjectiveResolution.Hom.hom'_comp_π'
    (⟨ProjectiveResolution.lift g P P', comm⟩ : ProjectiveResolution.Hom P P' g)

/-- **Derived extension of scalars of a module, read in cohomology, is the left derived functor
of extension of scalars.** For every `i`, the degree `-i` cohomology of `M ⊗ᴸ_R R'` is
`(L_i ext_{R → R'})(M)`, naturally in `M`. -/
def derivedExtensionSingleIsoLeftDerived (f : R →+* R') (i : ℕ) :
    DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
        (totalDerivedExtensionScalars.{u, u, u, w, w} f).functor ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ)) ≅
      (ModuleCat.extendScalars.{u, u, u} f).leftDerived i :=
  NatIso.ofComponents
    (fun M => singleDerivedExtensionIsoLeftDerivedOfResolution f (ProjectiveResolution.of M) i)
    (fun {M N} g => singleDerivedExtensionIsoLeftDerivedOfResolution_hom_naturality f g
      (ProjectiveResolution.of M) (ProjectiveResolution.of N)
      (ProjectiveResolution.lift g _ _) (ProjectiveResolution.lift_commutes_zero g _ _)
      (extendMap_lift_comp_π' g (ProjectiveResolution.of M) (ProjectiveResolution.of N)) i)

end RingTheory.TorIndependence

end

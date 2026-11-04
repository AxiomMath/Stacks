module

public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations.Cocycle

/-!
# The classes of the two families in a common target

The identifications of the degree-`c` cohomology of the extended alternating Čech complex with
`i_*ℋ^c_T(ℱ)` (Stacks 0G7M), and the determinant identity
`supportedFractionClass_eq_det_smul` of Stacks 0G7S as one equation of maps into `i_*ℋ^c_Z(ℱ)`.
Part of `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations`.

* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleLimits (homOfSections homOfSections_app)
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

attribute [local instance] Classical.propDecidable

variable {X : Scheme.{u}}

/-! ### The classes of the two families in a common target -/

section CommonTarget

-- As in `section Derived` above: the standard model of the derived category is given a priority
-- that beats the global locally small model, because every library statement used here is
-- elaborated at the standard model.
attribute [local instance 10000] HasDerivedCategory.standard

open ExtensionByZeroModules
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.CechDerivedSupport
open Stacks.Perfect.ExtendedAlternatingCech.Augmentation
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward
  derivedSupportedPushforwardUnit)

/-- The embedding of `ℕ` into `ℤ` underlying the extension of a complex is the coercion. -/
public theorem embeddingUpNat_f (p : ℕ) : ComplexShape.embeddingUpNat.f p = (p : ℤ) := rfl

/-- The cohomology of a complex read in the derived category is its cohomology, with both ends
spelled in `X.Modules`. -/
public def derivedQHomologyIso (L : CochainComplex X.Modules ℤ) (p : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules p).obj (DerivedCategory.Q.obj L) ≅
      L.homology p :=
  (DerivedCategory.homologyFunctorFactors X.Modules p).app L

/-- The identification of the cohomology of a complex with its cohomology in the derived
category is natural. -/
public theorem derivedQHomologyIso_hom_naturality {L L' : CochainComplex X.Modules ℤ}
    (α : L ⟶ L') (p : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules p).map (DerivedCategory.Q.map α) ≫
        (derivedQHomologyIso L' p).hom =
      (derivedQHomologyIso L p).hom ≫ HomologicalComplex.homologyMap α p :=
  DerivedCategory.homologyFunctorFactors_hom_naturality α p

/-- `i_* R𝓗_T(ℱ)`, as an object of `D(𝒪_X)` spelled in `X.Modules`. -/
public def supportPushSingle {T : Set X} (hT : IsClosed T) (G : X.Modules) :
    DerivedCategory X.Modules :=
  (supportPush hT).obj ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-- `i_*ℋ^p_T(ℱ)`, the degree-`p` cohomology sheaf of `i_* R𝓗_T(ℱ)`. -/
public abbrev supportCohomologySheaf {T : Set X} (hT : IsClosed T) (G : X.Modules) (p : ℤ) :
    X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules p).obj (supportPushSingle hT G)

/-- The comparison `𝓕^• ⟶ i_* R𝓗_T(ℱ)` of Stacks 0G7L, with its target spelled by
`supportPushSingle`. -/
public def cechToSupport {m : ℕ} (e : Fin m → Γ(X, ⊤)) (G : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) :
    DerivedCategory.Q.obj ((cplx e G).extend ComplexShape.embeddingUpNat) ⟶
      supportPushSingle hT G :=
  cechToDerivedSupport e G hT hTe

/-- The subfamily projection is compatible with the comparison of Stacks 0G7L. -/
public theorem Q_map_extendMap_subfamilyCplxMap_comp_cechToSupport {m n : ℕ}
    (e : Fin n → Γ(X, ⊤)) (φ : Fin m ↪o Fin n) (G : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (hTeφ : equationsClosedSet (e ∘ φ) ⊆ T) :
    DerivedCategory.Q.map (HomologicalComplex.extendMap (subfamilyCplxMap e φ G)
          ComplexShape.embeddingUpNat) ≫ cechToSupport (e ∘ φ) G hT hTeφ =
      cechToSupport e G hT hTe :=
  Q_map_extendMap_subfamilyCplxMap_comp_cechToDerivedSupport e φ G hT hTe hTeφ

/-- The degree-`p` cohomology of the extended complex mapped to `i_*ℋ^p_T(ℱ)` by the comparison
of Stacks 0G7L. -/
public def extendHomologyToSupport {m : ℕ} (e : Fin m → Γ(X, ⊤)) (G : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (p : ℕ) :
    ((cplx e G).extend ComplexShape.embeddingUpNat).homology (p : ℤ) ⟶
      supportCohomologySheaf hT G (p : ℤ) :=
  (derivedQHomologyIso ((cplx e G).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫
    (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map (cechToSupport e G hT hTe)

/-- The subfamily projection is compatible with the degree-`p` cohomology of the comparison of
Stacks 0G7L, read on the extended complexes. -/
public theorem homologyMap_extendMap_comp_extendHomologyToSupport {m n : ℕ}
    (e : Fin n → Γ(X, ⊤)) (φ : Fin m ↪o Fin n) (G : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (hTeφ : equationsClosedSet (e ∘ φ) ⊆ T) (p : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex.extendMap (subfamilyCplxMap e φ G)
          ComplexShape.embeddingUpNat) (p : ℤ) ≫
        extendHomologyToSupport (e ∘ φ) G hT hTeφ p =
      extendHomologyToSupport e G hT hTe p := by
  have hnat : HomologicalComplex.homologyMap (HomologicalComplex.extendMap
          (subfamilyCplxMap e φ G) ComplexShape.embeddingUpNat) (p : ℤ) ≫
        (derivedQHomologyIso ((cplx (e ∘ φ) G).extend ComplexShape.embeddingUpNat)
          (p : ℤ)).inv =
      (derivedQHomologyIso ((cplx e G).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map
          (DerivedCategory.Q.map (HomologicalComplex.extendMap (subfamilyCplxMap e φ G)
            ComplexShape.embeddingUpNat)) := by
    rw [Iso.comp_inv_eq, Category.assoc, derivedQHomologyIso_hom_naturality,
      Iso.inv_hom_id_assoc]
  rw [extendHomologyToSupport, extendHomologyToSupport, ← Category.assoc, hnat,
    Category.assoc, ← Functor.map_comp,
    Q_map_extendMap_subfamilyCplxMap_comp_cechToSupport]

/-- **The degree-`p` cohomology of the extended alternating Čech complex mapped to
`i_*ℋ^p_T(ℱ)`**, by the canonical comparison of Stacks 0G7L. -/
public def cechHomologyToSupport {m : ℕ} (e : Fin m → Γ(X, ⊤)) (G : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (p : ℕ) :
    (cplx e G).homology p ⟶ supportCohomologySheaf hT G (p : ℤ) :=
  (HomologicalComplex.extendHomologyIso (cplx e G) ComplexShape.embeddingUpNat
    (embeddingUpNat_f p)).inv ≫ extendHomologyToSupport e G hT hTe p

/-- **The projections out of a family onto a subfamily all induce the same map on
`i_*ℋ^p_T(ℱ)`.** This is the step of the proof of Stacks 0G7S which says that the projections
out of the mixed complex "represent the identity on `i_* R𝓗_Z(ℱ)`", read in degree `p`. -/
public theorem homologyMap_subfamilyCplxMap_comp_cechHomologyToSupport {m n : ℕ}
    (e : Fin n → Γ(X, ⊤)) (φ : Fin m ↪o Fin n) (G : X.Modules)
    {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (hTeφ : equationsClosedSet (e ∘ φ) ⊆ T) (p : ℕ) :
    HomologicalComplex.homologyMap (subfamilyCplxMap e φ G) p ≫
        cechHomologyToSupport (e ∘ φ) G hT hTeφ p =
      cechHomologyToSupport e G hT hTe p := by
  have hnat : HomologicalComplex.homologyMap (subfamilyCplxMap e φ G) p ≫
        (HomologicalComplex.extendHomologyIso (cplx (e ∘ φ) G)
          ComplexShape.embeddingUpNat (embeddingUpNat_f p)).inv =
      (HomologicalComplex.extendHomologyIso (cplx e G) ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv ≫
        HomologicalComplex.homologyMap (HomologicalComplex.extendMap
          (subfamilyCplxMap e φ G) ComplexShape.embeddingUpNat) (p : ℤ) := by
    rw [Iso.comp_inv_eq, Category.assoc,
      HomologicalComplex.extendHomologyIso_hom_naturality, Iso.inv_hom_id_assoc]
  rw [cechHomologyToSupport, cechHomologyToSupport, ← Category.assoc, hnat, Category.assoc,
    homologyMap_extendMap_comp_extendHomologyToSupport]

/-- **The target of the class map of Stacks 0G7Q, read in `i_*ℋ^c_T(ℱ)`.** The composite of the
two identifications: the cokernel of the last differential is the degree-`c` cohomology of the
extended alternating Čech complex (`cokernelLastDifIsoHomology`), and that is `i_*ℋ^c_T(ℱ)` by
the canonical comparison of Stacks 0G7L (`cechHomologyToSupport`).  It is invertible by
`isIso_cokernelLastDifToSupport`.

Neither identification uses the quasi-coherence of `ℱ`, and `General.cokernelLastDifToSupport`
is the same composite without that hypothesis. -/
public def cokernelLastDifToSupport {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)
    [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    cokernel (lastDif f F) ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  (cokernelLastDifIsoHomology f F).hom ≫ cechHomologyToSupport f F hT hTf (d + 1)

/-- The class of a top-degree cochain, carried through the identification of the cokernel of the
last differential with the degree-`c` cohomology and then to `i_*ℋ^c_T(ℱ)`. -/
private theorem comp_cokernelπ_comp_cokernelLastDifIsoHomology_comp_cechHomologyToSupport
    {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) {M : X.Modules}
    (u : M ⟶ prodTerm f F d) :
    u ≫ cokernel.π (lastDif f F) ≫ (cokernelLastDifIsoHomology f F).hom ≫
        cechHomologyToSupport f F hT hTf (d + 1) =
      cechCocycleClass f F d u (comp_difSucc_top f F u) ≫
        cechHomologyToSupport f F hT hTf (d + 1) := by
  rw [← comp_cokernelπ_comp_cokernelLastDifIsoHomology, Category.assoc, Category.assoc]

/-- The class in `i_*ℋ^c_T(ℱ)` of a top-degree cochain is the image of its degree-`c`
cohomology class. -/
public theorem comp_cokernelπ_comp_cokernelLastDifToSupport {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) {M : X.Modules}
    (u : M ⟶ prodTerm f F d) :
    u ≫ cokernel.π (lastDif f F) ≫ cokernelLastDifToSupport f F hT hTf =
      cechCocycleClass f F d u (comp_difSucc_top f F u) ≫
        cechHomologyToSupport f F hT hTf (d + 1) := by
  exact comp_cokernelπ_comp_cokernelLastDifIsoHomology_comp_cechHomologyToSupport f F hT hTf u

/-- **The class in `i_*ℋ^c_T(ℱ)` of a projection of the mixed cocycle is the class of the mixed
cocycle itself.** This is the whole content of the last step of the proof of Stacks 0G7S: the
degree-`c` cohomology class of the mixed cocycle `σ` on the complex of the `2c` equations is
carried to the class of each of its two projections, and the two projections induce the same map
on `i_*ℋ^c_T(ℱ)`. -/
public theorem subfamily_comp_cokernelπ_comp_cokernelLastDifToSupport {d : ℕ}
    (E : Fin ((d + 1) + (d + 1)) → Γ(X, ⊤))
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    {f : Fin (d + 1) → Γ(X, ⊤)} (hEdot : ∀ k, E k = ∑ j, mixedRows a k j * f j)
    (φ : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) {T : Set X} (hT : IsClosed T)
    (hTE : equationsClosedSet E ⊆ T) (hTφ : equationsClosedSet (E ∘ φ) ⊆ T)
    (v : F ⟶ prodTerm (E ∘ φ) F d)
    (hv : mixedFractionHom E a F ≫ subfamilyProd E φ F d = v) :
    v ≫ cokernel.π (lastDif (E ∘ φ) F) ≫ cokernelLastDifToSupport (E ∘ φ) F hT hTφ =
      cechCocycleClass E F d (mixedFractionHom E a F)
          (mixedFractionHom_difSucc E a F hEdot) ≫
        cechHomologyToSupport E F hT hTE (d + 1) := by
  rw [comp_cokernelπ_comp_cokernelLastDifToSupport,
    ← homologyMap_subfamilyCplxMap_comp_cechHomologyToSupport E φ F hT hTE hTφ (d + 1),
    ← Category.assoc, cechCocycleClass_comp_homologyMap]
  exact congrArg (fun ψ => ψ ≫ cechHomologyToSupport (E ∘ φ) F hT hTφ (d + 1))
    (cechCocycleClass_congr (E ∘ φ) F d _ _ hv.symm)

/-! ### The identifications are invertible -/

/-- **Stacks 0G7M, for `i_* R𝓗_T`.** If the closed subset `T` is contained in the common zero
locus of the equations and `ℱ` is quasi-coherent, then `i_* R𝓗_T` inverts the augmentation
`𝓕^• ⟶ ℱ[0]` of Stacks 0G7L: the derived sections with support do, by
`isIso_map_augmentation_of_subset`, and the remaining direct image is a functor. -/
public theorem isIso_supportPush_map_augmentation {m : ℕ} (e : Fin m → Γ(X, ⊤))
    (G : X.Modules) [G.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTsub : T ⊆ equationsClosedSet e) :
    IsIso ((supportPush hT).map (augmentation e G)) := by
  have h0 : IsIso ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).map
      (augmentation e G)) :=
    isIso_map_augmentation_of_subset e G hT hTsub
      (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
      (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
      (inferInstanceAs (Functor.IsRightDerivedFunctor
        (derivedSupportedSectionsOnClosed X.toRingedSpace T hT)
        (derivedSupportedSectionsOnClosedUnit X.toRingedSpace T hT)
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ))))
  let _ := pushforward_preservesFiniteLimits X.toRingedSpace T
  let _ := pushforward_preservesFiniteColimits X.toRingedSpace T hT
  exact Functor.map_isIso
    ((modulePushforward (closedSubsetInclusion X.toRingedSpace T)).mapDerivedCategory)
    ((derivedSupportedSectionsOnClosed X.toRingedSpace T hT).map (augmentation e G))

/-- **The comparison of Stacks 0G7L is invertible** when `ℱ` is quasi-coherent and the closed
subset `T` is exactly the common zero locus of the equations: the counit of Stacks 0G72 is
invertible at the extended alternating Čech complex by Stacks 0G7M
(`isIso_derivedSupportedSectionsToId_cech`), and `i_* R𝓗_T` inverts the augmentation by the
other half of Stacks 0G7M. -/
public theorem isIso_cechToSupport {m : ℕ} (e : Fin m → Γ(X, ⊤)) (G : X.Modules)
    [G.IsQuasicoherent] {T : Set X} (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T)
    (hTsub : T ⊆ equationsClosedSet e) :
    IsIso (cechToSupport e G hT hTe) := by
  have h1 := isIso_supportPush_map_augmentation e G hT hTsub
  have hc := isIso_derivedSupportedSectionsToId_cech e G hT hTe
  have h2 : IsIso ((supportPushCounit hT).app
      (DerivedCategory.Q.obj ((cplx e G).extend ComplexShape.embeddingUpNat)) ≫
      cechToSupport e G hT hTe) := by
    rw [show (supportPushCounit hT).app
          (DerivedCategory.Q.obj ((cplx e G).extend ComplexShape.embeddingUpNat)) ≫
            cechToSupport e G hT hTe = (supportPush hT).map (augmentation e G) from
        derivedSupportedSectionsToId_comp_cechToDerivedSupport e G hT hTe]
    exact h1
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hc h2

/-- **The identification of the target of the class map of Stacks 0G7Q with `i_*ℋ^c_T(ℱ)` is an
isomorphism**, when `ℱ` is quasi-coherent and `T` is the common zero locus of the equations. -/
public theorem isIso_cokernelLastDifToSupport {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) [F.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (hTsub : T ⊆ equationsClosedSet f) :
    IsIso (cokernelLastDifToSupport f F hT hTf) := by
  have h := isIso_cechToSupport f F hT hTf hTsub
  rw [cokernelLastDifToSupport, cechHomologyToSupport, extendHomologyToSupport]
  have h2 := Functor.map_isIso (DerivedCategory.homologyFunctor X.Modules ((d + 1 : ℕ) : ℤ))
    (cechToSupport f F hT hTf)
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' (Iso.isIso_inv _) h2))

/-! ### Stacks 0G7S, the determinant identity -/

/-- The class map of Stacks 0G7Q carries the class of a section to the class of its fraction. -/
public theorem cokernelπ_comp_supportedFractionClass {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) :
    cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F =
      fractionHom f F d ≫ cokernel.π (lastDif f F) := by
  rw [supportedFractionClass, cokernel.π_desc]

/-- The class map of Stacks 0G7Q read in `i_*ℋ^c_T(ℱ)` carries the class of a section to the
class of its fraction. -/
public theorem cokernelπ_comp_supportedFractionClass_comp {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent] {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F ≫
        cokernelLastDifToSupport f F hT hTf =
      fractionHom f F d ≫ cokernel.π (lastDif f F) ≫
        cokernelLastDifToSupport f F hT hTf := by
  rw [← Category.assoc, cokernelπ_comp_supportedFractionClass, Category.assoc]

/-! ### The identification of the target, for an arbitrary coefficient module

Stacks 0G7Q asserts its class map, and its functoriality in `ℱ`, for an arbitrary
`𝒪_X`-module `ℱ`; quasi-coherence enters the remark only where an identification has to be
*invertible*, which is Stacks 0G7M.  The identification `cokernelLastDifToSupport` of the target
and the two formulas above are therefore repeated here without that hypothesis, which is what
lets `Stacks.Perfect.SupportedFraction.fractionClassTrans` be a natural transformation of
functors defined on all of `X.Modules`.  The declarations above keep the hypothesis, as the
consumers of Stacks 0G7S do.
-/

/-- **The target of the class map of Stacks 0G7Q, read in `i_*ℋ^c_T(ℱ)`, for an arbitrary
`𝒪_X`-module.**  The same composite as `cokernelLastDifToSupport`: both factors,
`cokernelLastDifIsoHomology` and the comparison `cechHomologyToSupport` of Stacks 0G7L, are
canonical maps available for every `ℱ`.  Quasi-coherence is needed only to make the second of
them invertible, which is Stacks 0G7M and is `isIso_cokernelLastDifToSupport`. -/
public def General.cokernelLastDifToSupport {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤))
    (F : X.Modules) {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    cokernel (lastDif f F) ⟶ supportCohomologySheaf hT F ((d + 1 : ℕ) : ℤ) :=
  (cokernelLastDifIsoHomology f F).hom ≫ cechHomologyToSupport f F hT hTf (d + 1)

/-- The class in `i_*ℋ^c_T(ℱ)` of a top-degree cochain is the image of its degree-`c`
cohomology class, for an arbitrary `𝒪_X`-module. -/
public theorem General.comp_cokernelπ_comp_cokernelLastDifToSupport {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) {M : X.Modules}
    (u : M ⟶ prodTerm f F d) :
    u ≫ cokernel.π (lastDif f F) ≫ General.cokernelLastDifToSupport f F hT hTf =
      cechCocycleClass f F d u (comp_difSucc_top f F u) ≫
        cechHomologyToSupport f F hT hTf (d + 1) := by
  exact comp_cokernelπ_comp_cokernelLastDifIsoHomology_comp_cechHomologyToSupport f F hT hTf u

/-- The class map of Stacks 0G7Q read in `i_*ℋ^c_T(ℱ)` carries the class of a section to the
class of its fraction, for an arbitrary `𝒪_X`-module. -/
public theorem General.cokernelπ_comp_supportedFractionClass_comp {d : ℕ}
    (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules) {T : Set X}
    (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F ≫
        General.cokernelLastDifToSupport f F hT hTf =
      fractionHom f F d ≫ cokernel.π (lastDif f F) ≫
        General.cokernelLastDifToSupport f F hT hTf := by
  rw [← Category.assoc, cokernelπ_comp_supportedFractionClass, Category.assoc]

/-- **Stacks Project, Tag 0G7S**, the determinant identity as a single equation in a common
target.

With `X`, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `ℱ` as in Stacks 0G7I, let `a_{ji} ∈ Γ(X, 𝒪_X)` and
`g_j = ∑_i a_{ji} f_i`, let `ℱ` be quasi-coherent and let `g₁, …, g_c` cut out the same closed
subset `Z` as `f₁, …, f_c`.  Then

`c_{f₁,…,f_c} = det(a_{ji}) c_{g₁,…,g_c}`

as maps into the single object `i_*ℋ^c_Z(ℱ)`.

The two class maps `supportedFractionClass f F` and `supportedFractionClass g F` of Stacks 0G7Q
land in the cokernels of the last differentials of the `f`- and the `g`-complex.  Each of those
cokernels is identified with `i_*ℋ^c_Z(ℱ)` by `cokernelLastDifToSupport`, the composite of
`cokernelLastDifIsoHomology` (the cokernel of the last differential is the degree-`c` cohomology
of the complex) with the degree-`c` cohomology of the canonical comparison `cechToDerivedSupport`
of Stacks 0G7L; both identifications are isomorphisms, which is the first two conjuncts and is
Stacks 0G7M.  Both class maps are then read on the common source `ℱ` through the canonical
epimorphisms `cokernel.π (equationsMultiplication f F)` and
`cokernel.π (equationsMultiplication g F)` presenting `i_* i^*ℱ` in the two ways the remark does;
since those are epimorphisms, the displayed equation is equivalent to the equality of the class
maps themselves, and no choice of isomorphism between the two presentations of `i_* i^*ℱ` is
needed.

The proof is the source's: both sides are the image of the single degree-`c` cohomology class of
the mixed cocycle `mixedFractionHom` on the complex of the `2c` equations `f₁, …, f_c, g₁, …, g_c`
(`subfamily_comp_cokernelπ_comp_cokernelLastDifToSupport` applied to the two projections
`mixedFractionHom_subfamilyProd_castAdd` and `mixedFractionHom_subfamilyProd_natAdd`).

The hypothesis `hZ` replaces the source's "`g₁, …, g_c` cut out `Z` scheme theoretically" by the
equality of the two common zero loci as closed *subsets*.  That is implied by the
scheme-theoretic condition, so the statement is a generalisation of the source's and not a
weakening of it.  It suffices because `R𝓗_T` depends only on the closed subset `T`: no scheme
structure on `Z` enters the identification of the two targets. -/
@[stacks 0G7S "the determinant identity c_{f₁,…,f_c} = det(a_{ji})·c_{g₁,…,g_c} as ONE equation
of maps into the common target i_*ℋ^c_Z(ℱ), together with the invertibility of the two
identifications it is read through.  The 0G7Q class maps of the f- and the g-complex are composed
with cokernelLastDifToSupport -- cokernel of the last differential ≅ H^c of the complex ≅
i_*ℋ^c_Z(ℱ), the last step by the canonical comparison of Stacks 0G7L and its invertibility,
which is Stacks 0G7M -- and are read on the common source ℱ through the two canonical
epimorphisms ℱ ↠ i_*i^*ℱ; those are epimorphisms, so this is equivalent to the equality of the
class maps and needs no chosen isomorphism between the two presentations of i_*i^*ℱ.  The
hypothesis used in place of the source's 'g₁,…,g_c cut out Z scheme theoretically' is the weaker
set-level equality of the two common zero loci, so this is a GENERALIZATION and not a weakening:
it suffices because RℋT depends only on the closed set T, so no scheme structure on Z enters the
identification of the two targets"]
public theorem supportedFractionClass_eq_det_smul {d : ℕ} (f g : Fin (d + 1) → Γ(X, ⊤))
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (hg : ∀ j, g j = ∑ i, a j i * f i)
    (hZ : equationsClosedSet g = equationsClosedSet f) :
    IsIso (cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl) ∧
      IsIso (cokernelLastDifToSupport g F (isClosed_equationsClosedSet f) hZ.le) ∧
      cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F ≫
          cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl =
        globalSmul a.det F ≫ cokernel.π (equationsMultiplication g F) ≫
          supportedFractionClass g F ≫
            cokernelLastDifToSupport g F (isClosed_equationsClosedSet f) hZ.le := by
  refine ⟨isIso_cokernelLastDifToSupport f F (isClosed_equationsClosedSet f) subset_rfl
      subset_rfl,
    isIso_cokernelLastDifToSupport g F (isClosed_equationsClosedSet f) hZ.le hZ.ge, ?_⟩
  obtain ⟨E, rfl, rfl, hEdot⟩ : ∃ E : Fin ((d + 1) + (d + 1)) → Γ(X, ⊤),
      E ∘ (Fin.castAddOrderEmb (d + 1) : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) = f ∧
      E ∘ (Fin.natAddOrderEmb (d + 1) : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) = g ∧
      (∀ k, E k = ∑ j, mixedRows a k j * f j) :=
    ⟨mixedEquations f g, mixedEquations_comp_castAdd f g, mixedEquations_comp_natAdd f g,
      mixedEquations_eq_dot f g a hg⟩
  have hTE : equationsClosedSet E ⊆ equationsClosedSet
      (E ∘ (Fin.castAddOrderEmb (d + 1) : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) :=
    equationsClosedSet_subset_subfamily E (Fin.castAddOrderEmb (d + 1))
  have hL := subfamily_comp_cokernelπ_comp_cokernelLastDifToSupport E a F hEdot
    (Fin.castAddOrderEmb (d + 1)) (isClosed_equationsClosedSet _) hTE subset_rfl
    (fractionHom (E ∘ (Fin.castAddOrderEmb (d + 1) :
      Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) F d)
    (mixedFractionHom_subfamilyProd_castAdd E a F)
  have hR := subfamily_comp_cokernelπ_comp_cokernelLastDifToSupport E a F hEdot
    (Fin.natAddOrderEmb (d + 1)) (isClosed_equationsClosedSet _) hTE hZ.le
    (globalSmul a.det F ≫ fractionHom (E ∘ (Fin.natAddOrderEmb (d + 1) :
      Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) F d)
    (mixedFractionHom_subfamilyProd_natAdd E a F)
  rw [cokernelπ_comp_supportedFractionClass_comp,
    cokernelπ_comp_supportedFractionClass_comp, hL, ← Category.assoc, hR]

end CommonTarget

end Stacks.Perfect.SupportedFraction

end

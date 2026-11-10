module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableCohomologyDerivedTensorPerfectInputs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableCohomologyDerivedTensorPerfectQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CountableCohomologyDerivedTensorStrictlyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTensorInstances
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedSectionsOnSliceTriangulated

/-!
# The cohomology clause of Stacks 0CRU at a perfect complex

Let `X` be a quasi-compact quasi-separated algebraic space over a scheme `S`, let `K` be an
object of `D_QCoh(𝒪_X)` whose cohomology sheaves have countable sets of sections over the affine
schemes étale over `X`, and let `E` be a perfect object of `D(𝒪_X)` (Stacks 08G5).  Then
`H^i(U, (K ⊗^𝐋_{𝒪_X} E)|_U)` is countable for every quasi-compact quasi-separated `U` étale
over `X`.

Together with the quasi-coherence of the cohomology sheaves of `K ⊗^𝐋_{𝒪_X} E`
(`AlgebraicGeometry.Space.qcohDerived_derivedTensor_of_isPerfect`), the main input is that these
cohomology sheaves have countable sets of sections over every affine étale chart.

## Main results

* `AlgebraicGeometry.Space.countable_sections_homology_derivedTensor_of_isPerfect`: the sections
  of `H^q(K ⊗^𝐋 E)` over the affine étale charts are countable.
* `AlgebraicGeometry.Space.hasCountableCohomology_derivedTensor_restrict_of_isPerfect`: the
  cohomology clause of Stacks 0CRU.

## References

* [Stacks Project, Tag 0218](https://stacks.math.columbia.edu/tag/0218)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AddCommGrpCat (HasCountableCohomology)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  isGrothendieckAbelian_modules enoughInjectives_modules'
  Stacks.Cohomology.HypercohomologyEdge.evaluation_additive
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  smallEtaleRingedSite_essentiallySmall
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective

/-- The universe lift of abelian groups is left exact. -/
local instance : PreservesFiniteLimits AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

/-- The universe lift of abelian groups is right exact. -/
local instance : PreservesFiniteColimits AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Countability across the universe lift -/

/-- **Countable cohomology descends along the universe lift of abelian groups**: if the universe
lift of `N` has countable cohomology, then so does `N`.  This is the converse of
`AlgebraicGeometry.Space.hasCountableCohomology_uliftFunctor_mapDerivedCategory`. -/
theorem hasCountableCohomology_of_uliftFunctor_mapDerivedCategory
    {N : DerivedCategory AddCommGrpCat.{u}}
    (hN : HasCountableCohomology
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj N)) :
    HasCountableCohomology N := fun q => by
  have hq : Countable ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj N) := hN q
  exact Countable.of_equiv _
    (((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      AddCommGrpCat.uliftFunctor.{u + 1, u} q).app N).addCommGroupIsoToAddEquiv.toEquiv.trans
        Equiv.ulift)

/-! ### Stacks 0BKZ read backwards -/

variable {X : AlgebraicSpaces B S hS}

/-- **The cohomology over an affine étale chart of a complex with quasi-coherent cohomology
sheaves is the module of sections of its cohomology sheaves there.**  Over an affine étale chart
`v` of `X` the hypercohomology `H^q(v, L)` is `H^q(L)(v)`, for `L` with quasi-coherent cohomology
sheaves (Stacks 0BKZ). -/
def derivedSectionsAbAtHomologyIso (v : SmallEtale B S hS X.1)
    (hv : IsAffineChart B S hS X.1 v) (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).IsQuasicoherentOnSite) (q : ℤ) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).obj
        ((derivedSectionsAbAt B S hS v).obj L) ≅
      (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op v))) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q ⋙
          SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) (op v)).obj L) :=
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  have hedge :=
    Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover
      O v L (IsAffineChart B S hS X.1) (hasEnoughObjects_isAffineChart B S hS X.1)
      (fun V hV p hp m => isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 _
        (hqc m) V hV p hp) hv q
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).mapIso
      ((Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
        (SheafOfModules.evaluation O (op v)) (forget₂ _ AddCommGrpCat.{u})).app L).symm ≪≫
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      (forget₂ (ModuleCat.{u} (O.obj.obj (op v))) AddCommGrpCat.{u}) q).app
      ((Stacks.Cohomology.HypercohomologyEdge.derivedSections O v).obj L) ≪≫
    (forget₂ (ModuleCat.{u} (O.obj.obj (op v))) AddCommGrpCat.{u}).mapIso
      (@asIso _ _ _ _ _ hedge)

/-- **The sections of the cohomology sheaves over an affine étale chart are countable as soon as
the cohomology over that chart is**, for a complex with quasi-coherent cohomology sheaves. -/
theorem countable_sections_of_hasCountableCohomology_derivedSectionsAbAt
    (v : SmallEtale B S hS X.1) (hv : IsAffineChart B S hS X.1 v)
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).IsQuasicoherentOnSite)
    (h : HasCountableCohomology ((derivedSectionsAbAt B S hS v).obj L)) (q : ℤ) :
    Countable (((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).val.obj (op v)) :=
  have := h q
  Countable.of_equiv _
    (derivedSectionsAbAtHomologyIso B S hS v hv L hqc q).addCommGroupIsoToAddEquiv.toEquiv

/-! ### The dévissage on the slice at an affine chart -/

section Slice

open Stacks.Cohomology.Localization.OfEssentiallySmall (derivedSectionsOnSlice
  derivedSectionsOverObjectIsoSlice derivedRestrictionIsoMapDerivedCategory)
open Stacks.SheafOfModules.DerivedTensorProduct.SliceRestriction (derivedTensorRestrictIso)

variable (w : (smallEtaleRingedSite B S hS X.1 X.2).C)

/-- **Stacks 0D6F at the small étale site of an algebraic space.**  The unbounded derived
sections over an étale chart `w` of `X` are the unbounded derived global sections, on the slice
of the small étale site at `w`, of the restriction to that slice. -/
def derivedSectionsAbAtIsoSlice (M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (derivedSectionsAbAt B S hS w).obj M ≅
      (derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj
        ((AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
          (smallEtaleRingedSite B S hS X.1 X.2) w).obj M) :=
  (derivedSectionsOverObjectIsoSlice (smallEtaleRingedSite B S hS X.1 X.2).J
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O) w).app M ≪≫
    (derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).mapIso
      ((derivedRestrictionIsoMapDerivedCategory (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).app M)

variable (TU : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
  ((smallEtaleRingedSite B S hS X.1 X.2).over w))

/-- **An `𝒪_X|_w`-module placed in a degree is a shift of it placed in degree zero**:
`M[0]⟦-i⟧ ≅ M[i]`.  This is the shift datum of `DerivedCategory.singleFunctors`. -/
def sliceSingleShiftIso (M : AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
    ((smallEtaleRingedSite B S hS X.1 X.2).over w)) (i : ℤ) :
    ((DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
        ((smallEtaleRingedSite B S hS X.1 X.2).over w)) 0).obj M)⟦-i⟧ ≅
      (DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
        ((smallEtaleRingedSite B S hS X.1 X.2).over w)) i).obj M :=
  ((DerivedCategory.singleFunctors (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
    ((smallEtaleRingedSite B S hS X.1 X.2).over w))).shiftIso (-i) i 0 (by lia)).app M

/-- **`K ⊗^𝐋 𝒪_X|_w[i]` is `K⟦-i⟧`** on the slice at `w`. -/
def sliceTensorSingleUnitIso (K' : DerivedCategory
    (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w))) (i : ℤ) :
    (TU.tensor.obj K').obj
        ((DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
          ((smallEtaleRingedSite B S hS X.1 X.2).over w)) i).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            ((smallEtaleRingedSite B S hS X.1 X.2).over w).O))) ≅ K'⟦-i⟧ :=
  (TU.tensor.obj K').mapIso (sliceSingleShiftIso B S hS w _ i).symm ≪≫
    ((TU.tensor.obj K').commShiftIso (-i)).app _ ≪≫
    (shiftFunctor (DerivedCategory (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w))) (-i)).mapIso (TU.unitIso K')

/-- Countable cohomology of the universe lift of the derived sections on the slice at `w` is
invariant under isomorphism of the input complex. -/
private theorem hasCountableCohomology_uliftDerivedSectionsOnSlice_of_iso
    {M N : DerivedCategory (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w))} (e : M ≅ N)
    (h : HasCountableCohomology (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj
      ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj M))) :
    HasCountableCohomology (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj
      ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj N)) :=
  h.of_iso (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.mapIso
    ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O) w).mapIso e))

/-- **Countable cohomology on the slice at `w` passes to tensor products with strictly perfect
complexes.**  If the universe lift of the derived sections on the slice of every shift of `K'`
has countable cohomology, then so does the universe lift of the derived sections on the slice of
`K' ⊗^𝐋 P`, for every strictly perfect complex `P` of `𝒪_X|_w`-modules. -/
theorem hasCountableCohomology_uliftDerivedSectionsOnSlice_derivedTensor_of_isStrictlyPerfect
    (K' : DerivedCategory (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w)))
    (hK' : ∀ n : ℤ, HasCountableCohomology
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj
        ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj (K'⟦n⟧))))
    (P : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS X.1 X.2).over w).O) P) :
    HasCountableCohomology (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj
      ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj
        ((TU.tensor.obj K').obj (DerivedCategory.Q.obj P)))) := by
  classical
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex
    (fun A => HasCountableCohomology (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj
      ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj ((TU.tensor.obj K').obj A))))
    (fun e h => hasCountableCohomology_uliftDerivedSectionsOnSlice_of_iso B S hS w
      ((TU.tensor.obj K').mapIso e) h)
    (fun _ hA => hasCountableCohomology_of_isZero
      (Functor.map_isZero AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory
        (Functor.map_isZero (derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O) w)
          (Functor.map_isZero (TU.tensor.obj K') hA))))
    ?_ P hP.bounded ?_
  · intro Sc hSc h₁ h₃
    exact AddCommGrpCat.HasCountableCohomology.obj₂ _
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.map_distinguished _
        ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O) w).map_distinguished _
          ((TU.tensor.obj K').map_distinguished _
            (DerivedCategory.triangleOfSES_distinguished hSc)))) h₁ h₃
  · intro i
    obtain ⟨m, ⟨r⟩⟩ :=
      (Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct
        ((smallEtaleRingedSite B S hS X.1 X.2).over w).O (P.X i)).mp (hP.termDirectSummand i)
    refine hasCountableCohomology_of_retract
      (((r.map (DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
          ((smallEtaleRingedSite B S hS X.1 X.2).over w)) i ⋙ TU.tensor.obj K')).map
        (derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) w)).map
        AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory) ?_
    let f₁ : Fin m → DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O).over w)) :=
      fun _ => (DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
          ((smallEtaleRingedSite B S hS X.1 X.2).over w)) i ⋙ TU.tensor.obj K').obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          ((smallEtaleRingedSite B S hS X.1 X.2).over w).O))
    let f₂ : Fin m → DerivedCategory AddCommGrpCat.{u} := fun j =>
      (derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj (f₁ j)
    refine HasCountableCohomology.of_iso
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.mapIso
          ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS X.1 X.2).O) w).mapIso
            ((DerivedCategory.singleFunctor (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
                ((smallEtaleRingedSite B S hS X.1 X.2).over w)) i ⋙
              TU.tensor.obj K').mapBiproduct
                (fun _ : Fin m => SheafOfModules.unit
                  (Stacks.SheafOfModules.Tensor.ringSheaf
                    ((smallEtaleRingedSite B S hS X.1 X.2).over w).O))) ≪≫
          (derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O) w).mapBiproduct f₁) ≪≫
        AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.mapBiproduct f₂).symm) ?_
    refine hasCountableCohomology_biproduct
      (fun j => AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj (f₂ j))
      fun _ => ?_
    exact hasCountableCohomology_uliftDerivedSectionsOnSlice_of_iso B S hS w
      (sliceTensorSingleUnitIso B S hS w TU K' i).symm (hK' (-i))

/-- **The cohomology of `K ⊗^𝐋 E` over an affine étale chart carrying a strictly perfect model of
the restriction of `E` is countable.**  Here `w` is an affine étale chart of `X` on whose slice
the restriction of `E` is represented by a strictly perfect complex `P`, and `K` has
quasi-coherent cohomology sheaves with countable sets of sections over the affine étale charts. -/
theorem hasCountableCohomology_derivedSectionsAbAt_derivedTensor_of_sliceModel
    (TU' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w))
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj K).IsQuasicoherentOnSite)
    (hcountK : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj K).val.obj (op v)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hw : IsAffineChart B S hS X.1 w)
    (P : CochainComplex (AlgebraicGeometry.RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over w)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf
      ((smallEtaleRingedSite B S hS X.1 X.2).over w).O) P)
    (e : DerivedCategory.Q.obj P ≅
      (AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
        (smallEtaleRingedSite B S hS X.1 X.2) w).obj E) :
    HasCountableCohomology ((derivedSectionsAbAt B S hS w).obj ((T.tensor.obj K).obj E)) := by
  classical
  have hbase : HasCountableCohomology
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj
        ((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O) w).obj
          ((AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
            (smallEtaleRingedSite B S hS X.1 X.2) w).obj K))) :=
    (hasCountableCohomology_uliftFunctor_mapDerivedCategory
      (hasCountableCohomology_derivedSectionsAbAt B S hS w hw K hqcK
        fun q => hcountK w hw q)).of_iso
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.mapIso
        (derivedSectionsAbAtIsoSlice B S hS w K))
  refine hasCountableCohomology_of_uliftFunctor_mapDerivedCategory
    (HasCountableCohomology.of_iso
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.mapIso
        (derivedSectionsAbAtIsoSlice B S hS w ((T.tensor.obj K).obj E)).symm) ?_)
  refine hasCountableCohomology_uliftDerivedSectionsOnSlice_of_iso B S hS w
    ((TU'.tensor.obj ((AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
        (smallEtaleRingedSite B S hS X.1 X.2) w).obj K)).mapIso e ≪≫
      (derivedTensorRestrictIso (smallEtaleRingedSite B S hS X.1 X.2) w T TU' K E).symm) ?_
  refine hasCountableCohomology_uliftDerivedSectionsOnSlice_derivedTensor_of_isStrictlyPerfect
    B S hS w TU' ((AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2) w).obj K) (fun n => ?_) P hP
  exact HasCountableCohomology.of_iso
    ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.mapIso
      (((derivedSectionsOnSlice (smallEtaleRingedSite B S hS X.1 X.2).J
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O) w).commShiftIso n).app
        ((AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
          (smallEtaleRingedSite B S hS X.1 X.2) w).obj K)) ≪≫
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.commShiftIso n).app _).symm)
    (hasCountableCohomology_shift hbase n)

end Slice

/-! ### The second input of Stacks 0CRU at a perfect complex -/

/-- **The cohomology sheaves of `K ⊗^𝐋 E` have countable sets of sections over the affine étale
charts**, for `K` an object of `D(𝒪_X)` with quasi-coherent cohomology sheaves having countable
sets of sections over the affine étale charts and `E` a perfect object of `D(𝒪_X)`. -/
theorem countable_sections_homology_derivedTensor_of_isPerfect
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj K).IsQuasicoherentOnSite)
    (hcountK : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj K).val.obj (op v)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect.{u + 1, u, u, u, u + 1} E)
    (hqcL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      ((T.tensor.obj K).obj E)).IsQuasicoherentOnSite)
    (v : SmallEtale B S hS X.1) (hv : IsAffineChart B S hS X.1 v) (q : ℤ) :
    Countable (((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      ((T.tensor.obj K).obj E)).val.obj (op v)) := by
  classical
  obtain ⟨E₀, hE₀, ⟨eE⟩⟩ := hE
  obtain ⟨ι, hfin, V, f, haff, hcov, hmodels⟩ :=
    exists_finite_affine_isStrictlyPerfect_refinement B S hS X.1 X.2 v hv E₀ hE₀
  refine Stacks.SheafOfModules.countable_sections_of_ofArrows _ V f hcov fun i => ?_
  obtain ⟨P, hP, qi, hqi⟩ := hmodels i
  refine countable_sections_of_hasCountableCohomology_derivedSectionsAbAt B S hS (V i) (haff i)
    _ hqcL (hasCountableCohomology_derivedSectionsAbAt_derivedTensor_of_sliceModel B S hS (V i)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((smallEtaleRingedSite B S hS X.1 X.2).over (V i))) T K
      hqcK hcountK E (haff i) P hP ?_) q
  exact (@asIso _ _ _ _ _ ((DerivedCategory.isIso_Q_map_iff_quasiIso _ qi).mpr hqi)) ≪≫
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O) (V i)).mapDerivedCategoryFactors.app E₀).symm ≪≫
    (AlgebraicGeometry.RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2) (V i)).mapIso eE

/-! ### The cohomology clause of Stacks 0CRU -/

/-- Let `X` be a quasi-compact quasi-separated algebraic space over `S`, let `K` be an object of
`D_QCoh(𝒪_X)` whose cohomology sheaves have countable sets of sections over the affine schemes
étale over `X`, and let `E` be a perfect object of `D(𝒪_X)`.  Then `H^i(U, (K ⊗^𝐋_{𝒪_X} E)|_U)`
is countable for every quasi-compact quasi-separated `U` étale over `X` and every `i`. -/
@[stacks 0CRU "the sets H^i(U, K ⊗^𝐋 E)"]
theorem hasCountableCohomology_derivedTensor_restrict_of_isPerfect
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqcK : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj K).IsQuasicoherentOnSite)
    (hcountK : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj K).val.obj (op v)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect.{u + 1, u, u, u, u + 1} E)
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS U.1.left).obj
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj
        ((T.tensor.obj K).obj E))) :=
  have hqcL : ∀ q : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) q).obj
      ((T.tensor.obj K).obj E)).IsQuasicoherentOnSite :=
    qcohDerived_derivedTensor_of_isPerfect B S hS X T ⟨K, hqcK⟩ E hE
  hasCountableCohomology_derivedGlobalSectionsAb_restrict B S hS hZ X
    ((T.tensor.obj K).obj E) hqcL
    (fun v hv q => countable_sections_homology_derivedTensor_of_isPerfect B S hS T K hqcK
      hcountK E hE hqcL v hv q) U hUqc hUqs

end AlgebraicGeometry.Space

end

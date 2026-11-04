module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete.AdicWeakSerreClass
public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.DerivedComplete.NoetherianTorPseudoCoherent
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor


/-!
# Cohomology of derived completion over a Noetherian ring

For a complex over a Noetherian ring whose cohomology modules are finite, the cohomology of its
derived completion, taken to be any left adjoint to the inclusion of the full subcategory of
derived-complete objects, is the adic completion of its cohomology.

## Main results

* `AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion` identifies the
  cohomology modules of a derived completion with the corresponding adic completions.

## References

* [The Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AdicCompletionCohomology

section FlatTensor

open CategoryTheory.MonoidalCategory
attribute [local instance] HasDerivedCategory.standard
noncomputable section

private theorem kFlat_single {A : Type u} [CommRing A]
    (M : ModuleCat.{u} A) [Module.Flat A M] :
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M).KFlat := by
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  have (n : ℤ) : Module.Flat A (S.X n) := by
    by_cases hn : n = 0
    · subst n
      exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).toLinearEquiv
    · have : Subsingleton (S.X n) := ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M n hn)
      infer_instance
  exact CochainComplex.KFlat.kFlat_of_flat S 0

private theorem homology_tensor_single_flat {A : Type u} [CommRing A]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (M : ModuleCat.{u} A) [Module.Flat A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((T.tensor.obj K).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K ⊗ M) := by
  obtain ⟨P, f, hPL, _, hf, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution.{u, u} (DerivedCategory.Q.objPreimage K)
  have hP : P.KFlat := hPL
  have := hf
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  have := AdicCompletionTor.tensorSingleInclusion_isIso M P
  exact ⟨H.mapIso ((T.tensor.flip.obj _).mapIso e.symm) ≪≫
    H.mapIso (T.comparison P S hP (kFlat_single M)) ≪≫
    H.mapIso (DerivedCategory.Q.mapIso
      (asIso (AdicCompletionTor.tensorSingleInclusion M P)).symm) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).app _ ≪≫
    (P.sc i).mapHomologyIso (tensorRight M) ≪≫
    (tensorRight M).mapIso ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{u} A) i).app P).symm ≪≫
    (tensorRight M).mapIso (H.mapIso e)⟩

end
end FlatTensor

section Truncation

attribute [local instance] HasDerivedCategory.standard

private theorem isIso_homology_truncLE {A : Type u} [CommRing A]
    (X : CochainComplex (ModuleCat.{u} A) ℤ) (n i : ℤ) (hi : i ≤ n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (DerivedCategory.Q.map (X.ιTruncLE n))) := by
  have := X.quasiIsoAt_ιTruncLE n i hi
  exact (NatIso.isIso_map_iff
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i) (X.ιTruncLE n)).mpr
      (inferInstanceAs (IsIso (HomologicalComplex.homologyMap (X.ιTruncLE n) i)))

/-- The truncation inclusion `τ_{≤ n} X ⟶ X` of a complex of `A`-modules induces an isomorphism
on `H^i` in `D(A)` for every `i ≤ n`. -/
public alias isIso_homologyFunctor_map_ιTruncLE := isIso_homology_truncLE

private theorem truncLE_isPseudoCoherent {A : Type u} [CommRing A] [IsNoetherianRing A]
    (X : CochainComplex (ModuleCat.{u} A) ℤ)
    (hX : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (DerivedCategory.Q.obj X)))
    (n : ℤ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj (X.truncLE n)) := by
  have hz : ∀ i : ℤ, n < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (DerivedCategory.Q.obj (X.truncLE n))) :=
    (DerivedCategory.isLE_iff _ n).mp inferInstance
  apply (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    (DerivedCategory.Q.obj (X.truncLE n)) 0 A).2.1.mpr
  refine ⟨⟨n, hz⟩, fun i ↦ ?_⟩
  by_cases hi : i ≤ n
  · have := hX i
    have := isIso_homology_truncLE X n i hi
    exact Module.Finite.equiv (asIso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (DerivedCategory.Q.map (X.ιTruncLE n)))).toLinearEquiv.symm
  · have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (DerivedCategory.Q.obj (X.truncLE n))) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz i (lt_of_not_ge hi))
    infer_instance

end Truncation

section Completion

open CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard
noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
/-- Countable products are exact in the category of `A`-modules. -/
local instance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
  moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
/-- The derived category of `A`-modules has countable products. -/
local instance : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
open AdicCompletionFlatTensor in
private theorem completion_single_ring
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (C : DerivedCategory (ModuleCat.{u} A) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete I L).FullSubcategory)
    (adj : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun L ↦ IsDerivedComplete I L).ι)
    (hC : ∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) (C.obj K).obj) :
    Nonempty ((C.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A A))).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I A))) := by
  obtain ⟨e⟩ :=
    (derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
      A I T C ⟨adj⟩ hC).1 A A
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun L ↦ IsDerivedComplete I L
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let r := TensorProduct.rid A A
  exact ⟨(C ⋙ P.ι).mapIso (S.mapIso r.toModuleIso).symm ≪≫ e ≪≫
    S.mapIso ((AdicCompletion.congr I r).restrictScalars A).toModuleIso⟩

private theorem completion_pseudoCoherent
    (C : DerivedCategory (ModuleCat.{u} A) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete I L).FullSubcategory)
    (adj : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun L ↦ IsDerivedComplete I L).ι)
    (hC : ∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K) (C.obj K).obj)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    Nonempty ((C.obj K).obj ≅
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (AdicCompletion I A)))) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  let U := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun L ↦ IsDerivedComplete I L
  have hU : DerivedCategory.TStructure.t.minus U := ⟨0, inferInstance⟩
  obtain ⟨e⟩ := (AdicCompletionPseudoCoherentTensor.derivedCompletion_tensor_iso_of_boundedAbove
    A I T C ⟨adj⟩ hC U hU).2 K hK
  obtain ⟨c⟩ := completion_single_ring I T C adj hC
  let un : (T.tensor.obj U).obj K ≅ K :=
    CochainComplex.DerivedTensor.derivedTensorProductCommIso U K ≪≫ T.rightUnitor.app K
  exact ⟨(C ⋙ P.ι).mapIso un.symm ≪≫ e ≪≫
    (T.tensor.flip.obj K).mapIso c ≪≫
      CochainComplex.DerivedTensor.derivedTensorProductCommIso _ K⟩

private theorem derivedComplete_stableUnderShift
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun K ↦ IsDerivedComplete I K).IsStableUnderShift ℤ := by
  let D : ObjectProperty (ModuleCat.{u} A) :=
    fun M ↦ IsDerivedCompleteModule I M
  obtain ⟨hD, hiff⟩ :=
    AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff.{u, u} A I
  have : D.IsWeakSerreClass := hD
  exact ⟨fun n ↦ ⟨fun K hK ↦ (hiff (K⟦n⟧)).mp fun i ↦ D.prop_of_iso
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso n i (n + i) rfl).app K).symm
    ((hiff K).mpr hK (n + i))⟩⟩

private theorem homology_completion_pseudoCoherent
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : DerivedCategory (ModuleCat.{u} A) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete I L).FullSubcategory)
    (adj : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun L ↦ IsDerivedComplete I L).ι)
    (hC : ∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K) (C.obj K).obj)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (C.obj K).obj ≅
      ModuleCat.of A (AdicCompletion I
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))) := by
  have hfin := ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    K 0 A).2.1.mp hK).2 i
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨e⟩ := completion_pseudoCoherent I C adj hC K hK
  obtain ⟨t⟩ := homology_tensor_single_flat T (ModuleCat.of A (AdicCompletion I A)) K i
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e ≪≫ t ≪≫
    ((TensorProduct.comm A M (AdicCompletion I A)).trans
      ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars A)).toModuleIso⟩

private theorem homology_completion_of_le
    {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (f : Fin r → A)
    (C : DerivedCategory (ModuleCat.{u} A) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete (Ideal.span (Set.range f)) L).FullSubcategory)
    (adj : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
      fun L ↦ IsDerivedComplete (Ideal.span (Set.range f)) L).ι)
    (hC : ∀ K, IsDerivedLimit
      (NoetherianAdicCompletion.idealPowerQuotientSystem (Ideal.span (Set.range f)) ⋙
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj K) (C.obj K).obj)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (j : ℤ) (hj : j ≤ -(r : ℤ) - 1) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj (C.obj K).obj ≅
      ModuleCat.of A (AdicCompletion (Ideal.span (Set.range f))
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K))) := by
  let X := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj X ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let K₀ := DerivedCategory.Q.obj (X.truncLE (-1))
  let φ : K₀ ⟶ K := DerivedCategory.Q.map (X.ιTruncLE (-1)) ≫ e.hom
  have hX (i : ℤ) : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (DerivedCategory.Q.obj X)) := by
    have := hK i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e).toLinearEquiv.symm
  have hφ (i : ℤ) (hi : i ≤ -1) :
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map φ) := by
    have := isIso_homology_truncLE X (-1) i hi
    dsimp only [φ]
    rw [Functor.map_comp]
    infer_instance
  have hφ₀ : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map φ) :=
    (DerivedCategory.isZero_of_isLE K₀ (-1) 0 (by omega)).mono _
  have hc := ((CompletionAdjunction.derivedCompletion_finiteCohomologicalDimension A f C adj φ).2
    ⟨hφ, hφ₀⟩).1 j hj
  have hj' : j ≤ -1 := by omega
  have := hφ j hj'
  obtain ⟨b⟩ := homology_completion_pseudoCoherent (Ideal.span (Set.range f)) C adj hC K₀
    (truncLE_isPseudoCoherent X hX (-1)) j
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun L ↦ IsDerivedComplete (Ideal.span (Set.range f)) L
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) j
  exact ⟨(asIso (H.map ((C ⋙ P.ι).map φ))).symm ≪≫ b ≪≫
    ((AdicCompletion.congr (Ideal.span (Set.range f))
      (asIso (H.map φ)).toLinearEquiv).restrictScalars A).toModuleIso⟩

/-- If every cohomology module of a complex over a Noetherian ring is finite,
then the cohomology modules of its derived completion are the adic completions of the original
cohomology modules. -/
@[stacks 0A06]
public theorem derivedCompletion_homology_iso_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : ∀ n : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K)) :
    letI : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
      moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete I L
    ∀ (C : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory),
      (C ⊣ P.ι) → ∀ n : ℤ,
        Nonempty
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
              ((C ⋙ P.ι).obj K)) ≅
            ModuleCat.of A
              (AdicCompletion I
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj K))) := by
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun L ↦ IsDerivedComplete I L
  intro P' C adj n
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  change Ideal.span (Set.range f) = I at hf
  subst I
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨L, ⟨adjL⟩, hL, _, _⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A (Ideal.span (Set.range f)) T
  have : P.IsStableUnderShift ℤ :=
    derivedComplete_stableUnderShift A (Ideal.span (Set.range f))
  let := adjL.leftAdjointCommShift ℤ
  let F := L ⋙ P.ι
  let a : ℤ := (r : ℤ) + 1 + n
  let j : ℤ := -(r : ℤ) - 1
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A)
  let eK : (H j).obj (K⟦a⟧) ≅ (H n).obj K :=
    ((H 0).shiftIso a j n (by dsimp [a, j]; omega)).app K
  let eL : (H j).obj (F.obj (K⟦a⟧)) ≅ (H n).obj (F.obj K) :=
    (H j).mapIso ((F.commShiftIso a).app K) ≪≫
      ((H 0).shiftIso a j n (by dsimp [a, j]; omega)).app (F.obj K)
  have hKsh (i : ℤ) : Module.Finite A ((H i).obj (K⟦a⟧)) := by
    have := hK (a + i)
    let e : (H i).obj (K⟦a⟧) ≅ (H (a + i)).obj K :=
      ((H 0).shiftIso a i (a + i) rfl).app K
    exact Module.Finite.equiv e.toLinearEquiv.symm
  obtain ⟨b⟩ := homology_completion_of_le f L adjL hL (K⟦a⟧) hKsh j le_rfl
  let e : F.obj K ≅ (C ⋙ P.ι).obj K :=
    P.ι.mapIso ((adjL.leftAdjointUniq adj).app K)
  exact ⟨(H n).mapIso e.symm ≪≫ eL.symm ≪≫ b ≪≫
    ((AdicCompletion.congr (Ideal.span (Set.range f))
      eK.toLinearEquiv).restrictScalars A).toModuleIso⟩

end
end Completion
end AdicCompletionCohomology

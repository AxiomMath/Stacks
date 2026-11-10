module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalInvariantsInjectionInputs
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafOpenDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportZeroConstantSmooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H⁰_c(W_k̄, j_* G) = 0` on a smooth affine curve

Let `W` be a smooth affine curve over a finite field `k`, `j : V ⟶ W` an open immersion with
`V` nonempty and `G` a finite type locally constant sheaf of `Λ`-modules on `V`. Then
`H⁰_c(W_k̄, j_* G) = 0` for every algebraically closed extension `k̄` of `k`.

## Main results

* `Stacks.EtaleCohomology.mono_compactSupportSheafCohomology_zero_map`: `H⁰_c(X_k̄, -)` preserves
  monomorphisms.
* `Stacks.EtaleCohomology.affineCurveDirectImageCompactSupportZeroInput`: the vanishing
  `H⁰_c(W_k̄, j_* G) = 0`, as the statement
  `Stacks.EtaleCohomology.AffineCurveDirectImageCompactSupportZeroInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section LeftExact

/-- A right adjoint preserves monomorphisms. -/
lemma mono_map_of_adjunction {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {X Y : D} (m : X ⟶ Y) [Mono m] : Mono (G.map m) :=
  have := adj.isRightAdjoint
  inferInstance

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar]

/-- **`H⁰_c(X_k̄, -)` preserves monomorphisms of sheaves.** -/
theorem mono_compactSupportSheafCohomology_zero_map {A B : EtaleModules.{u, 0} Λ X} (φ : A ⟶ B)
    [Mono φ] : Mono ((compactSupportSheafCohomology Λ f j kbar 0).map φ) := by
  let S := ShortComplex.mk φ (cokernel.π φ) (cokernel.condition φ)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel φ) inferInstance inferInstance
  have hS' := hS.map_of_exact (HomologicalComplex.single (EtaleModules.{u, 0} Λ X)
    (ComplexShape.up ℤ) 0)
  have hneg : IsZero (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      ⟨(CochainComplex.singleFunctor _ 0).obj (cokernel φ), CochainComplex.plus_singleFunctor_obj _⟩
        (-1)) := by
    have : CochainComplex.IsStrictlyGE ((CochainComplex.singleFunctor
        (EtaleModules.{u, 0} Λ X) 0).obj (cokernel φ)) 0 := by
      change CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (cokernel φ)) 0
      infer_instance
    have : (compactSupportFrobeniusCohomology.{u, 0} Λ f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj (cokernel φ),
          CochainComplex.plus_singleFunctor_obj _⟩).IsGE 0 :=
      isGE_compactSupportFrobeniusFunctor_obj.{u, 0} Λ f j kbar
        ⟨(CochainComplex.singleFunctor _ 0).obj (cokernel φ),
          CochainComplex.plus_singleFunctor_obj _⟩ 0
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 (-1) (by omega)
  exact mono_homology_compactSupportFrobeniusFunctor_map_f Λ f j kbar hS'
    (CochainComplex.plus_singleFunctor_obj _) (CochainComplex.plus_singleFunctor_obj _)
    (CochainComplex.plus_singleFunctor_obj _) (-1) 0 (by omega) hneg

end LeftExact

/-! ### The input `Stacks.EtaleCohomology.AffineCurveDirectImageCompactSupportZeroInput` -/

/-- **`H⁰_c(W_k̄, j_* G) = 0`** for a smooth affine curve `W` over a finite field, an open
immersion `j : V ⟶ W` with `V` nonempty and a finite type locally constant sheaf `G` on `V`. -/
@[sga "4½ Sommes_trig 1.18" "1.18 b), special case"]
theorem affineCurveDirectImageCompactSupportZeroInput :
    AffineCurveDirectImageCompactSupportZeroInput.{u} := by
  intro k _ _ W V fW _ _ _ _ _ _ jWb kbar _ _ _ jW _ _ _ Λ _ G hG
  have : IsIntegral W := IsCurve.toIsVariety.toIsIntegral (k := k) (f := fW)
  have : IsIntegral V := isIntegral_of_isOpenImmersion jW
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian fW
  have : SmoothOfRelativeDimension 1 fW := smoothOfRelativeDimension_one_of_isCurve k fW
  have : SmoothOfRelativeDimension 1 (jW ≫ fW) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (jW ≫ fW))
  have : IsCurve k (jW ≫ fW) :=
    { topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field 1 (jW ≫ fW) }
  have : IsNormal (Spec (CommRingCat.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  have : IsNormal V := isNormal_of_smooth (jW ≫ fW)
  have hX : IsGeometricallyUnibranch V := isGeometricallyUnibranch_of_isNormal
  let x : GeometricPoint V := GeometricPoint.ofPoint V (Classical.arbitrary V)
  obtain ⟨A, M, -, ⟨e⟩⟩ := trivializedByPointedGaloisCovers hX x Λ G hG
  let V' : Scheme.{u} := A.obj.left
  let f : V' ⟶ V := A.obj.hom
  have : IsFinite f := A.obj.prop.1
  have : Etale f := A.obj.prop.2
  have : ConnectedSpace V' := inferInstanceAs (ConnectedSpace A.obj.left)
  have : Nonempty V' := ConnectedSpace.toNonempty
  let e' := etaleModuleInverseImageIsoConstantOfOverPullback
    ((PointedGaloisCover.toEtale x).obj A) Λ G M e
  have hjU : (jW ≫ jWb.immersion) ≫ jWb.toBase = jW ≫ fW := by
    rw [Category.assoc, CompactificationOf.immersion_toBase]
  obtain ⟨C⟩ := nonempty_coverCompactification k (jW ≫ fW) jWb.toBase (jW ≫ jWb.immersion) hjU f
  have : IsIntegralHom C.fb := inferInstance
  let W' : Scheme.{u} := pullback C.fb jWb.immersion
  let ι' : W' ⟶ C.Vb := pullback.fst C.fb jWb.immersion
  let g : W' ⟶ W := pullback.snd C.fb jWb.immersion
  let jW' : V' ⟶ W' := pullback.lift C.j (f ≫ jW) (by rw [C.w, Category.assoc])
  have hjι : jW' ≫ ι' = C.j := pullback.lift_fst _ _ _
  have hjg : jW' ≫ g = f ≫ jW := pullback.lift_snd _ _ _
  have : IsOpenImmersion (jW' ≫ ι') := by rw [hjι]; infer_instance
  have : IsOpenImmersion jW' := IsOpenImmersion.of_comp jW' ι'
  have : Nonempty W' := ⟨jW'.base (Classical.arbitrary V')⟩
  have : IsIntegral W' := isIntegral_of_isOpenImmersion ι'
  have : IsNormal W' := isNormal_of_smooth (ι' ≫ C.q)
  have : IsAffine W' := isAffine_of_isAffineHom g
  have hι'q : ι' ≫ C.q = g ≫ fW := by
    rw [← C.hq, ← Category.assoc, pullback.condition, Category.assoc,
      CompactificationOf.immersion_toBase]
  let cW' : CompactificationOf (Over.mk (g ≫ fW)) :=
    ⟨StructuredArrow.mk (Y := Over.mk C.q)
        (Over.homMk (U := Over.mk (g ≫ fW)) (V := Over.mk C.q) ι' hι'q),
      ⟨inferInstanceAs (IsOpenImmersion ι'), C.isProper⟩⟩
  have : SmoothOfRelativeDimension 1 cW'.toBase :=
    inferInstanceAs (SmoothOfRelativeDimension 1 C.q)
  have hW' := isZero_compactSupportFrobeniusCohomologyGroup_zero_constant_of_smooth (g ≫ fW) cW'
    kbar Λ M
  have hW := hW'.of_iso ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso
    ((compactSupportFrobeniusCohomologyIntegralIso Λ fW jWb (g ≫ fW) cW' g C.fb C.hq
      (IsPullback.of_hasPullback C.fb jWb.immersion).flip kbar _) ≪≫
      (compactSupportFrobeniusFunctor.{u, 0} Λ fW jWb kbar).mapIso
        (directImageSingleIso Λ g _))).symm
  have : Surjective f := by
    rw [surjective_iff]
    exact Set.range_eq_univ.1 (IsClopen.eq_univ
      ⟨f.isClosedMap.isClosed_range, f.isOpenMap.isOpen_range⟩ ⟨_, Classical.arbitrary V', rfl⟩)
  have := faithful_etaleModuleInverseImage_of_surjective Λ f
  let η := (etaleModuleInverseImageAdj.{u, 0} Λ f).unit.app G
  let cI := etaleModuleDirectImageComp.{u, 0} Λ f jW (f ≫ jW) rfl ≪≫
    (etaleModuleDirectImageComp.{u, 0} Λ jW' g (f ≫ jW) hjg.symm).symm
  let φ := (etaleModuleDirectImage.{u, 0} Λ jW).map η ≫
    (etaleModuleDirectImage.{u, 0} Λ jW).map ((etaleModuleDirectImage.{u, 0} Λ f).map e'.hom) ≫
    cI.hom.app _ ≫
    (etaleModuleDirectImage.{u, 0} Λ g).map (constantModuleSheafOpenDirectImageIso Λ jW' M).inv
  have : Mono φ := by
    have h₀ : Mono η := (etaleModuleInverseImageAdj.{u, 0} Λ f).unit_mono_of_L_faithful G
    have h₁ : Mono ((etaleModuleDirectImage.{u, 0} Λ jW).map η) :=
      @mono_map_of_adjunction _ _ _ _ _ _ (etaleModuleInverseImageAdj.{u, 0} Λ jW) _ _ η h₀
    have h₂ := (SplitMono.mk _ ((etaleModuleDirectImage.{u, 0} Λ f ⋙
      etaleModuleDirectImage.{u, 0} Λ jW).mapIso e').hom_inv_id).mono
    have h₄ := (SplitMono.mk _ ((etaleModuleDirectImage.{u, 0} Λ g).mapIso
      (constantModuleSheafOpenDirectImageIso Λ jW' M)).inv_hom_id).mono
    exact @mono_comp' _ _ _ _ _ _ _ h₁ (@mono_comp' _ _ _ _ _ _ _ h₂
      (@mono_comp' _ _ _ _ _ _ _ (SplitMono.mk _ (cI.hom_inv_id_app _)).mono h₄))
  exact @IsZero.of_mono _ _ _ _ _ _
    (mono_compactSupportSheafCohomology_zero_map Λ fW jWb kbar φ) hW

end Stacks.EtaleCohomology

module

public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ProperSupportSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactnessGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqsPseudoCoherentFrom

/-!
# Cohomology and base change: the pseudo-coherent case

Let `f : X ⟶ Y` be a morphism of algebraic spaces. This file proves the pseudo-coherence part of
Stacks 0CTL from the perfectness part of Stacks 0A1P by approximation by perfect complexes
(Stacks 08HP) and the cohomological dimension of `Rf_*` on `D_QCoh` (Stacks 08FA).

## Main results

* `Space.isPseudoCoherentFrom_of_approximatesFrom`: a target approximated from `m` by an
  `m`-pseudo-coherent object is `m`-pseudo-coherent.
* `Space.isPseudoCoherentFrom_derivedModulePushforward_derivedTensor_of_isAffineSpace`: the
  approximation argument over an affine base.
* `Space.isPseudoCoherent_derivedModulePushforward_derivedTensor_of_perfectness`: the
  pseudo-coherence part of Stacks 0CTL, given the perfectness part of Stacks 0A1P.
* `Space.isPseudoCoherent_derivedModulePushforward_of_perfectness`: Stacks 0CTN, given the
  perfectness part of Stacks 0A1P.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

/-- Approximations from `m` compose. -/
theorem DerivedCategory.ApproximatesFrom.comp {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {P K L : DerivedCategory C} {φ : P ⟶ K} {ψ : K ⟶ L} {m : ℤ}
    (hφ : DerivedCategory.ApproximatesFrom φ m) (hψ : DerivedCategory.ApproximatesFrom ψ m) :
    DerivedCategory.ApproximatesFrom (φ ≫ ψ) m := by
  refine ⟨fun j hj => ?_, ?_⟩ <;> rw [Functor.map_comp]
  · exact IsIso.comp_isIso' (hφ.1 j hj) (hψ.1 j hj)
  · exact epi_comp' hφ.2 hψ.2

/-- A morphism approximates its target from `m` as soon as a cone of it is in `D^{≤ m - 1}`. -/
theorem DerivedCategory.approximatesFrom_of_isLE {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (m : ℤ)
    (h : T.obj₃.IsLE (m - 1)) : DerivedCategory.ApproximatesFrom T.mor₁ m :=
  (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ T hT m).2 fun i hi =>
    T.obj₃.isZero_of_isLE (m - 1) i (by omega)

/-- A cone of an approximation from `m` is in `D^{≤ m - 1}`. -/
theorem DerivedCategory.ApproximatesFrom.isLE_obj₃ {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) {m : ℤ}
    (h : DerivedCategory.ApproximatesFrom T.mor₁ m) : T.obj₃.IsLE (m - 1) := by
  rw [DerivedCategory.isLE_iff]
  exact fun i hi =>
    (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ T hT m).1 h i (by omega)

/-- A triangulated functor preserving `D^{≤ n}` for every `n` preserves approximations from `m`. -/
theorem DerivedCategory.ApproximatesFrom.map {C D : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] [Category* D] [Abelian D] [HasDerivedCategory D]
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (E : DerivedCategory C) (n : ℤ), E.IsLE n → (F.obj E).IsLE n)
    {P K : DerivedCategory C} {φ : P ⟶ K} {m : ℤ} (hφ : DerivedCategory.ApproximatesFrom φ m) :
    DerivedCategory.ApproximatesFrom (F.map φ) m := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle φ
  exact DerivedCategory.approximatesFrom_of_isLE _ (F.map_distinguished _ hT) m
    (hF _ _ (DerivedCategory.ApproximatesFrom.isLE_obj₃ _ hT hφ))

/-- The inclusion `σ^{≥c}K ⟶ K` of a brutal truncation approximates `K` from `c`. -/
theorem DerivedCategory.approximatesFrom_Q_map_ιStupidTruncGE {C : Type*} [Category* C]
    [Abelian C] [HasDerivedCategory C] (K : CochainComplex C ℤ) (c : ℤ) :
    DerivedCategory.ApproximatesFrom (DerivedCategory.Q.map
      (HomologicalComplex.ιStupidTrunc K (ComplexShape.embeddingUpIntGE c))) c := by
  let ι := HomologicalComplex.ιStupidTrunc K (ComplexShape.embeddingUpIntGE c)
  have key : ∀ i, Arrow.mk ((DerivedCategory.homologyFunctor C i).map (DerivedCategory.Q.map ι)) ≅
      Arrow.mk (HomologicalComplex.homologyMap ι i) := fun i =>
    Arrow.isoMk ((DerivedCategory.homologyFunctorFactors C i).app _)
      ((DerivedCategory.homologyFunctorFactors C i).app _)
      ((DerivedCategory.homologyFunctorFactors C i).hom.naturality ι).symm
  refine ⟨fun i hi => ?_, ?_⟩
  · exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff (key i)).2
      (StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE K c i hi)
  · refine ((MorphismProperty.epimorphisms C).arrow_mk_iso_iff (key c)).2 ?_
    have e₂ :
        IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) c).map ι).τ₂ := by
      show IsIso (ι.f c)
      rw [StacksDraft.StupidTruncation.ιStupidTruncGE_f K c c le_rfl]
      infer_instance
    have e₃ :
        IsIso ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) c).map ι).τ₃ := by
      show IsIso (ι.f ((ComplexShape.up ℤ).next c))
      rw [CochainComplex.next,
        StacksDraft.StupidTruncation.ιStupidTruncGE_f K c (c + 1) (by omega)]
      infer_instance
    exact (MorphismProperty.epimorphisms.iff _).2 (inferInstanceAs
      (Epi (ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) c).map ι))))

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- **A target approximated from `m` by an `m`-pseudo-coherent object is `m`-pseudo-coherent.**
If `φ : P ⟶ K` in `D(𝒪_X)` is an isomorphism on `Hⁱ` for `i > m` and surjective on `Hᵐ`, and
`P` is `m`-pseudo-coherent, then so is `K`. -/
theorem isPseudoCoherentFrom_of_approximatesFrom
    {P K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : P ⟶ K) (m : ℤ) (hφ : DerivedCategory.ApproximatesFrom φ m)
    (hP : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom P m) :
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentFrom K m := by
  refine isPseudoCoherentFrom_of_chart_approximation _ m fun U => ?_
  obtain ⟨R, hR, h⟩ := exists_chart_approximation_of_isPseudoCoherentFrom B S hS P m hP U
  refine ⟨R, hR, fun V g hg => ?_⟩
  obtain ⟨Q, hQ, hb, ψ, hiso, hepi⟩ := h g hg
  have hψφ := DerivedCategory.ApproximatesFrom.comp (m := m) ⟨hiso, hepi⟩
    (DerivedCategory.ApproximatesFrom.map
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X V))
      (fun E n hE => isLE_smallEtaleDerivedModulePullback_obj _ E n hE) hφ)
  exact ⟨Q, hQ, hb, _, hψφ.1, hψφ.2⟩

/-- **The upper bound of `Rf_*` on `D_QCoh`, shifted.** If `Rf_*` carries objects of `D_QCoh`
with cohomology in degrees `≤ 0` to objects with cohomology vanishing in degrees `≥ N` (Stacks
08FA), it carries `D_QCoh ∩ D^{≤ k}` into `D^{≤ k + N - 1}`. -/
theorem isLE_derivedModulePushforward_of_isLE (f : X ⟶ Y) (N : ℤ)
    (hN : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X E →
      (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj E)) →
      ∀ m : ℤ, N ≤ m → IsZero ((DerivedCategory.homologyFunctor _ m).obj
        ((derivedModulePushforward B S hS f).obj E)))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hE : QcohDerived B S hS X E) (k : ℤ)
    (hk : E.IsLE k) : ((derivedModulePushforward B S hS f).obj E).IsLE (k + N - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have h₁ := hN (E⟦k⟧) (qcohDerived_shift E k hE)
    (fun m hm => (E.isZero_of_isLE k (k + m) (by omega)).of_iso
      (((DerivedCategory.homologyFunctor _ 0).shiftIso k m (k + m) rfl).app E)) (i - k) (by omega)
  exact (h₁.of_iso ((DerivedCategory.homologyFunctor _ (i - k)).mapIso
    (((derivedModulePushforward B S hS f).commShiftIso k).app E).symm)).of_iso
    (((DerivedCategory.homologyFunctor _ 0).shiftIso k (i - k) i (by omega)).app
      ((derivedModulePushforward B S hS f).obj E)).symm

/-- If `F` is a triangulated endofunctor of `D(𝒪_X)` and the cone of `α` is sent by `F` into
`D_QCoh ∩ D^{≤ k}` with `k + N < m`, then `Rf_* F α` approximates from `m`. -/
private theorem approximatesFrom_derivedModulePushforward_map_of_isLE
    (f : X ⟶ Y) (N : ℤ)
    (hN : ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2), QcohDerived B S hS X E →
      (∀ m : ℤ, 0 < m → IsZero ((DerivedCategory.homologyFunctor _ m).obj E)) →
      ∀ m : ℤ, N ≤ m → IsZero ((DerivedCategory.homologyFunctor _ m).obj
        ((derivedModulePushforward B S hS f).obj E)))
    (F : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    [F.CommShift ℤ] [F.IsTriangulated]
    {A B' : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} (α : A ⟶ B')
    {C : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)} {g : B' ⟶ C} {h : C ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk α g h ∈ distTriang _) (hq : QcohDerived B S hS X (F.obj C)) {k m : ℤ}
    (hk : (F.obj C).IsLE k) (hkm : k + N < m) :
    DerivedCategory.ApproximatesFrom ((derivedModulePushforward B S hS f).map (F.map α)) m := by
  have hR : ((derivedModulePushforward B S hS f).obj (F.obj C)).IsLE (m - 1 - 1) := by
    have := isLE_derivedModulePushforward_of_isLE f N hN _ hq _ hk
    exact DerivedCategory.TStructure.t.isLE_of_le _ (k + N - 1) _ (by omega)
  have h := DerivedCategory.approximatesFrom_of_isLE _
    ((F ⋙ derivedModulePushforward B S hS f).map_distinguished _ hT) (m - 1) hR
  exact ⟨fun i hi => h.1 i (by omega), @IsIso.epi_of_iso _ _ _ _ _ (h.1 m (by omega))⟩

/-- A complex of quasi-coherent modules has quasi-coherent cohomology sheaves. -/
theorem qcohDerived_Q_obj_of_isQuasicoherentOnSite
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : ∀ n, (G.X n).IsQuasicoherentOnSite) : QcohDerived B S hS X (DerivedCategory.Q.obj G) := by
  rw [qcohDerived_Q_obj_iff]
  intro q
  let P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
  exact P.prop_of_isColimit_cokernelCofork
    (G.homologyIsCokernel ((ComplexShape.up ℤ).prev q) q rfl) (hG _)
    (P.prop_of_isLimit_kernelFork (G.cyclesIsKernel q ((ComplexShape.up ℤ).next q) rfl) (hG q)
      (hG _))

/-- **The pseudo-coherence part of Stacks 0CTL over an affine base, from perfectness of the
truncations.** Let `f : X ⟶ Y` be quasi-compact and quasi-separated with `Y` affine, `E`
pseudo-coherent and `𝒢^•` a complex of quasi-coherent modules vanishing above `b`. If
`Rf_*(P ⊗^L σ^{≥c}𝒢^•)` is perfect for every perfect `P` and every `c`, then
`Rf_*(E ⊗^L 𝒢^•)` is `m`-pseudo-coherent for every `m`. -/
theorem isPseudoCoherentFrom_derivedModulePushforward_derivedTensor_of_isAffineSpace
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (b : ℤ) (hGb : ∀ i, b < i → IsZero (G.X i))
    (hGq : ∀ n, (G.X n).IsQuasicoherentOnSite)
    (hperf : ∀ P, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect P → ∀ c : ℤ,
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj P).obj
          (DerivedCategory.Q.obj (G.stupidTrunc (ComplexShape.embeddingUpIntGE c))))))
    (m : ℤ) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherentFrom
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) m := by
  let R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) := derivedModulePushforward B S hS f
  have hXqc : IsQuasiCompactSpace B S hS X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_hom_of_isAffineSpace B S hS f hfqc hY
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedModulePushforward B S hS f hfqc hfqs
    hY.isQuasiCompactSpace
  obtain ⟨r, hr⟩ := exists_approximatesFrom_of_isPseudoCoherentFrom B S hS X hXqc
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS
      B.contains_terminal f hfqs hY)
  have hEq : QcohDerived B S hS X E :=
    derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE
  have hGQ : QcohDerived B S hS X (DerivedCategory.Q.obj G) :=
    qcohDerived_Q_obj_of_isQuasicoherentOnSite G hGq
  have : CochainComplex.IsStrictlyLE G b := (CochainComplex.isStrictlyLE_iff _ _).2 hGb
  have hGle : (DerivedCategory.Q.obj G).IsLE b := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    infer_instance
  -- the tensor functor `- ⊗^L 𝒢^•`
  let TG : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
    (smallEtaleDerivedTensor B S hS X).flip.obj (DerivedCategory.Q.obj G)
  let : TG.CommShift ℤ := (smallEtaleDerivedTensorProduct B S hS X).commShift_left _
  let : TG.IsTriangulated := (smallEtaleDerivedTensorProduct B S hS X).exact_left _
  -- Step 1: approximate `E` by a perfect `P`
  obtain ⟨K₀, hK₀, ⟨eK₀⟩⟩ := hE
  obtain ⟨P, α, hP, hα₁, hα₂⟩ := hr ⟨E, hEq⟩ (m - N - b) ⟨K₀, hK₀ _, ⟨eK₀⟩⟩
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle α
  have hCle : C.IsLE (m - N - b - 1) :=
    DerivedCategory.ApproximatesFrom.isLE_obj₃ (Triangle.mk α g h) hT ⟨hα₁, hα₂⟩
  have hCq : QcohDerived B S hS X C := (QcohDerived B S hS X).ext_of_isTriangulatedClosed₃ _ hT
    (qcohDerived_of_isPerfect_derivedCategoryB X P hP) hEq
  have hTCle : (TG.obj C).IsLE (m - N - b - 1 + b) :=
    (Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).1
      (Stacks.SheafOfModules.DerivedTensorProduct.isBoundedAboveBy_tensor_general
        (smallEtaleDerivedTensorProduct B S hS X)
        ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).2 hCle)
        ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).2 hGle))
  have happ₁ := approximatesFrom_derivedModulePushforward_map_of_isLE (m := m) f N hN TG α hT
    (qcohDerived_smallEtaleDerivedTensor X _ _ hCq hGQ) hTCle (by omega)
  -- Step 2: truncate `𝒢^•` below
  obtain ⟨a, ha⟩ := exists_isZero_homology_of_isPseudoCoherentFrom B S hS X hXqc P 0
    (isPseudoCoherentFrom_of_isPerfect hP 0)
  have hPa : P.IsLE a := by rwa [DerivedCategory.isLE_iff]
  let c := m - N - a
  let σ := G.stupidTrunc (ComplexShape.embeddingUpIntGE c)
  let ι := HomologicalComplex.ιStupidTrunc G (ComplexShape.embeddingUpIntGE c)
  have hσq : QcohDerived B S hS X (DerivedCategory.Q.obj σ) := by
    refine qcohDerived_Q_obj_of_isQuasicoherentOnSite σ fun n => ?_
    by_cases hn : c ≤ n
    · exact (hGq n).of_iso (StacksDraft.StupidTruncation.stupidTruncGEXIso G c n hn).symm
    · exact SheafOfModules.IsQuasicoherentOnSite.of_isZero
        (CochainComplex.isZero_of_isStrictlyGE σ c n (by omega))
  obtain ⟨D, g', h', hT'⟩ := distinguished_cocone_triangle (DerivedCategory.Q.map ι)
  have hDle : D.IsLE (c - 1) := DerivedCategory.ApproximatesFrom.isLE_obj₃
    (Triangle.mk (DerivedCategory.Q.map ι) g' h') hT'
    (DerivedCategory.approximatesFrom_Q_map_ιStupidTruncGE G c)
  have hDq : QcohDerived B S hS X D := (QcohDerived B S hS X).ext_of_isTriangulatedClosed₃ _ hT'
    hσq hGQ
  let TP : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) := (smallEtaleDerivedTensor B S hS X).obj P
  let : TP.CommShift ℤ := (smallEtaleDerivedTensorProduct B S hS X).commShift_right _
  let : TP.IsTriangulated := (smallEtaleDerivedTensorProduct B S hS X).exact_right _
  have hTDle : (TP.obj D).IsLE (a + (c - 1)) :=
    (Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).1
      (Stacks.SheafOfModules.DerivedTensorProduct.isBoundedAboveBy_tensor_general
        (smallEtaleDerivedTensorProduct B S hS X)
        ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).2 hPa)
        ((Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE _ _).2 hDle))
  have happ₂ := approximatesFrom_derivedModulePushforward_map_of_isLE (m := m) f N hN TP
    (DerivedCategory.Q.map ι) hT'
    (qcohDerived_smallEtaleDerivedTensor X _ _ (qcohDerived_of_isPerfect_derivedCategoryB X P hP)
      hDq) hTDle (by omega)
  -- Step 3: conclude
  exact isPseudoCoherentFrom_of_approximatesFrom _ m
    (DerivedCategory.ApproximatesFrom.comp happ₂ happ₁)
    (isPseudoCoherentFrom_of_isPerfect (hperf P hP c) m)

/-- **The pseudo-coherence part of Stacks 0CTL, from the perfectness part of Stacks 0A1P.** Let
`f : X ⟶ Y` be of finite presentation, `E` pseudo-coherent and `𝒢^•` a bounded above complex of
`𝒪_X`-modules of finite presentation, flat over `Y`, with support proper over `Y`. If the
perfectness statement of Stacks 0A1P holds, then `Rf_*(E ⊗^L 𝒢^•)` is pseudo-coherent. -/
theorem isPseudoCoherent_derivedModulePushforward_derivedTensor_of_perfectness
    (h0A1P : ∀ {X' Y' : AlgebraicSpaces B S hS} (f' : X' ⟶ Y')
      (hf' : IsFinitePresentation B S hS f'.hom)
      (E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))),
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X'.1 X'.2) E' →
      ∀ G' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) ℤ,
      {i : ℤ | ¬ IsZero (G'.X i)}.Finite → (∀ n, (G'.X n).IsFinitePresentation) →
      (∀ n, IsFlatOver B S hS X'.2 f'.hom (G'.X n)) →
      (∀ n, HasProperSupport B S hS X'.2 Y'.2 f'.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf'.1)
        ((SheafOfModules.toSheaf _).obj (G'.X n))) →
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y'.1 Y'.2)
        ((derivedModulePushforward B S hS f').obj
          (((smallEtaleDerivedTensor B S hS X').obj E').obj (DerivedCategory.Q.obj G'))))
    (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hGb : ∃ b : ℤ, ∀ i, b < i → IsZero (G.X i)) (hGfp : ∀ n, (G.X n).IsFinitePresentation)
    (hGflat : ∀ n, IsFlatOver B S hS X.2 f.hom (G.X n))
    (hGsupp : ∀ n, HasProperSupport B S hS X.2 Y.2 f.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1)
      ((SheafOfModules.toSheaf _).obj (G.X n))) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
      ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G))) := by
  obtain ⟨b, hb⟩ := hGb
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m => ?_
  refine isPseudoCoherentFrom_of_forall_isAffineChart _ m fun V hV => ?_
  refine RingedSite.isPseudoCoherentFrom_of_iso _ m ?_
    (chartBaseChangeDerivedTensorPushforwardIso f V E G)
  have hcond := fun n => modulePullback_coefficient_conditions
    (isPullback_chartBaseChangeInclusion B S hS f V)
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1) (G.X n) (hGfp n)
    (hGflat n) (hGsupp n)
  have hfV := isFinitePresentation_chartBaseChangeProjection f V hf
  let GV := ((modulePullback B S hS (chartBaseChangeInclusion B S hS f V)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj G
  refine isPseudoCoherentFrom_derivedModulePushforward_derivedTensor_of_isAffineSpace
    (chartBaseChangeProjection B S hS f V) hfV.2.1 hfV.2.2 (isAffineSpace_chartSpace B S hS Y V hV)
    _ (isPseudoCoherent_smallEtaleDerivedModulePullback _ E hE) GV b
    (fun i hi => (modulePullback B S hS _).map_isZero (hb i hi))
    (fun n => isQuasicoherentOnSite_of_isFinitePresentation _ (hcond n).1) ?_ m
  intro P hP c
  let σ := GV.stupidTrunc (ComplexShape.embeddingUpIntGE c)
  have hσ : ∀ n, n < c → IsZero (σ.X n) := fun n hn =>
    CochainComplex.isZero_of_isStrictlyGE σ c n hn
  have hσb : ∀ n, b < n → IsZero (σ.X n) := fun n hn => by
    by_cases hcn : c ≤ n
    · exact ((modulePullback B S hS _).map_isZero (hb n hn)).of_iso
        (StacksDraft.StupidTruncation.stupidTruncGEXIso GV c n hcn)
    · exact hσ n (by omega)
  refine h0A1P (chartBaseChangeProjection B S hS f V) hfV P hP σ ?_ (fun n => ?_) (fun n => ?_)
    (fun n => ?_)
  · exact (Set.finite_Icc c b).subset fun i hi =>
      ⟨not_lt.1 fun h => hi (hσ i h), not_lt.1 fun h => hi (hσb i h)⟩
  · by_cases hn : c ≤ n
    · exact (SheafOfModules.isFinitePresentation _).prop_of_iso
        (StacksDraft.StupidTruncation.stupidTruncGEXIso GV c n hn).symm (hcond n).1
    · exact isFinitePresentation_of_isZero B S hS (hσ n (by omega))
  · by_cases hn : c ≤ n
    · exact IsFlatOver.of_iso B S hS _
        (StacksDraft.StupidTruncation.stupidTruncGEXIso GV c n hn).symm (hcond n).2.1
    · exact isFlatOver_of_isZero B S hS _ (hσ n (by omega))
  · by_cases hn : c ≤ n
    · exact hasProperSupport_of_iso (chartSpace B S hS Y V).2 _ _
        (StacksDraft.StupidTruncation.stupidTruncGEXIso GV c n hn).symm (hcond n).2.2
    · exact hasProperSupport_of_isZero B S hS _ _ _ _ (hσ n (by omega))

/-- **Stacks 0CTN, from the perfectness part of Stacks 0A1P.** For `f : X ⟶ Y` flat, proper and
of finite presentation and `E` pseudo-coherent, `Rf_*E` is pseudo-coherent, and its formation
commutes with arbitrary base change: the base change map of Stacks 07A7 is invertible for every
cartesian square. Pseudo-coherence is the case `𝒢^• = 𝒪_X[0]` of the pseudo-coherence part of
Stacks 0CTL; base change is Stacks 08IR, `f` being flat. -/
theorem isPseudoCoherent_derivedModulePushforward_of_perfectness
    (h0A1P : ∀ {X' Y' : AlgebraicSpaces B S hS} (f' : X' ⟶ Y')
      (hf' : IsFinitePresentation B S hS f'.hom)
      (E' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X'))),
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS X'.1 X'.2) E' →
      ∀ G' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')) ℤ,
      {i : ℤ | ¬ IsZero (G'.X i)}.Finite → (∀ n, (G'.X n).IsFinitePresentation) →
      (∀ n, IsFlatOver B S hS X'.2 f'.hom (G'.X n)) →
      (∀ n, HasProperSupport B S hS X'.2 Y'.2 f'.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf'.1)
        ((SheafOfModules.toSheaf _).obj (G'.X n))) →
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y'.1 Y'.2)
        ((derivedModulePushforward B S hS f').obj
          (((smallEtaleDerivedTensor B S hS X').obj E').obj (DerivedCategory.Q.obj G'))))
    (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom) (hpr : IsProper B S hS f.hom)
    (hf : IsFinitePresentation B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent
        ((derivedModulePushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
        (sq : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' sq.w E) := by
  refine ⟨?_, fun g g' f' sq => isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS
    f g f' g' sq hf.2.1 hf.2.2 (torIndependent_of_isFlat_left f g hfl) E
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 E hE)⟩
  let C := Modules.{u, u} B S hS X.1 X.2
  let O := structureSheafModule B S hS X
  let G := (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj O
  have hG : ∀ n, n ≠ 0 → IsZero (G.X n) := fun n hn =>
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  have h := isPseudoCoherent_derivedModulePushforward_derivedTensor_of_perfectness h0A1P f hf E hE
    G ⟨0, fun i hi => hG i (by omega)⟩
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact (SheafOfModules.isFinitePresentation _).prop_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 O).symm
          (inferInstance : (structureSheafModule B S hS X).IsFinitePresentation)
      · exact isFinitePresentation_of_isZero B S hS (hG n hn))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact IsFlatOver.of_iso B S hS _
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 O).symm
          (isFlatOver_structureSheafModule B S hS f hfl)
      · exact isFlatOver_of_isZero B S hS _ (hG n hn))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · exact hasProperSupport_of_iso Y.2 _ _
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 O).symm
          (hasProperSupport_structureSheafModule B S hS f hpr
            (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hf.1))
      · exact hasProperSupport_of_isZero B S hS _ _ _ _ (hG n hn))
  let e : ((smallEtaleDerivedTensor B S hS X).obj E).obj (DerivedCategory.Q.obj G) ≅ E :=
    ((smallEtaleDerivedTensor B S hS X).obj E).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ C 0).app O).symm ≪≫
      Stacks.SheafOfModules.DerivedTensorProduct.unitIso (smallEtaleDerivedTensorProduct B S hS X) E
  exact (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m =>
    RingedSite.isPseudoCoherentFrom_of_iso _ m
      ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 h m)
      ((derivedModulePushforward B S hS f).mapIso e).symm

end AlgebraicGeometry.Space

end

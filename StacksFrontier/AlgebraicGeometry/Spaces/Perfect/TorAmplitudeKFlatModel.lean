module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankChartModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.BottomRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove

/-!
# Tor amplitude bounded below on an algebraic space: a K-flat model

Let `X` be an algebraic space and let `E` be an object of `D(𝒪_X)` of Tor amplitude in `[a, ∞]`.
Then `E` is represented by a K-flat complex `K` of flat `𝒪_X`-modules with `K^i = 0` for `i < a`
(Stacks 0F1M on the small étale site of `X`). Such a complex computes every derived pullback:
`Lf^*E = f^*K`, again K-flat with flat terms and zero below `a`; hence `H^j(Lf^*E) = 0` for
`j < a` and `H^a(Lf^*E) = Ker(f^*K^a ⟶ f^*K^{a+1})`.

## Main results

* `AlgebraicGeometry.Space.exists_kFlat_isStrictlyGE_of_hasTorAmplitudeGE`: the K-flat model.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackObjQIsoOfKFlat`: `Lf^*(K) ≅ f^*K` for
  `K` K-flat with flat terms.
* `AlgebraicGeometry.Space.isZero_pullbackHomology_of_hasTorAmplitudeGE`: `H^j(Lf^*E) = 0` for
  `j < a` and every `f`.
* `AlgebraicGeometry.Space.pullbackHomologyIsoKernel`: `H^a(Lf^*E) ≅ Ker(f^*d_K^a)`.

## References

* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.SheafOfModules (DerivedTensorProduct)
open BottomRankLocus (pullbackHomology)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

/-- The truncation `τ_{≥ a}P` of a complex of flat `𝒪_X`-modules whose cokernel of
`d^{a-1}` is flat has flat terms. -/
private theorem isFlat_truncGE_X {X : AlgebraicSpaces B S hS}
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) (a : ℤ)
    [P.IsGE a]
    (hPflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) (P.X i))
    (hCoker : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) (cokernel (P.d (a - 1) a)))
    (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) ((P.truncGE a).X i) := by
  have eOpCoker : P.opcycles a ≅ cokernel (P.d (a - 1) a) :=
    IsColimit.coconePointUniqueUpToIso
      (P.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
  rcases lt_trichotomy i a with hlt | heq | hgt
  · exact isFlat_of_isZero B S hS ((P.truncGE a).isZero_of_isStrictlyGE a i hlt)
  · subst heq
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      (eOpCoker.symm ≪≫ (P.truncGEXIsoOpcycles i).symm) hCoker
  · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      (P.truncGEXIso a i hgt).symm (hPflat i)

/-- The kernel of the projection `P ⟶ τ_{≥ a}P` vanishes above `a`. -/
private theorem isStrictlyLE_kernel_πTruncGE {X : AlgebraicSpaces B S hS}
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) (a : ℤ)
    (hSE : (ShortComplex.kernelSequence (P.πTruncGE a)).ShortExact) :
    (ShortComplex.kernelSequence (P.πTruncGE a)).X₁.IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have hiso : IsIso ((P.πTruncGE a).f i) :=
    P.isIso_πTruncGE_f _
      (show (ComplexShape.embeddingUpIntGE a).f (i - a).natAbs = i by
        rw [ComplexShape.embeddingUpIntGE_f, Int.natAbs_of_nonneg (by omega)]
        omega)
      (by rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]; omega)
  have hSi := hSE.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)
  have _ := hSi.mono_f
  refine IsZero.of_mono_eq_zero _ (hSi.exact.mono_g_iff.1 ?_)
  exact @IsIso.mono_of_iso _ _ _ _ _ hiso

/-- The truncation `τ_{≥ a}P` of a K-flat complex `P` of flat `𝒪_X`-modules is K-flat as soon
as its terms are flat (Stacks 0G7B applied to `0 ⟶ Ker ⟶ P ⟶ τ_{≥ a}P ⟶ 0`). -/
private theorem smallEtaleModuleKFlat_truncGE {X : AlgebraicSpaces B S hS}
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) (a : ℤ)
    (hP : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (hTruncFlat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS X).O) ((P.truncGE a).X i)) :
    smallEtaleModuleKFlat B S hS X
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (P.truncGE a)) := by
  have hπepi : Epi (P.πTruncGE a) :=
    HomologicalComplex.epi_of_epi_f _ fun i => by
      dsimp only [CochainComplex.πTruncGE]
      infer_instance
  have hSE : (ShortComplex.kernelSequence (P.πTruncGE a)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance hπepi
  have hKerFlat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
        (O := (smallEtaleRingedTopos B S hS X).O)
        ((ShortComplex.kernelSequence (P.πTruncGE a)).X₁.X i) := fun i =>
    Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact _
      ((ShortComplex.kernelSequence (P.πTruncGE a)).map
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
      (hSE.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
      (hP.2 i) (hTruncFlat i)
  have _ := isStrictlyLE_kernel_πTruncGE P a hSE
  have hKerKFlat := (smallEtaleModuleKFlat_of_isStrictlyLE B S hS X
    (ShortComplex.kernelSequence (P.πTruncGE a)).X₁ a hKerFlat).1
  exact ⟨Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact
    (smallEtaleRingedTopos B S hS X).O
    (ShortComplex.kernelSequence (P.πTruncGE a)) hSE hTruncFlat hKerKFlat hP.1, hTruncFlat⟩

/-- **Stacks 0F1M (1) `⇒` (2) on the small étale site of an algebraic space.** An object of
`D(𝒪_X)` of Tor amplitude in `[a, ∞]` is represented by a K-flat complex of flat `𝒪_X`-modules
vanishing in every degree below `a`. -/
theorem exists_kFlat_isStrictlyGE_of_hasTorAmplitudeGE {X : AlgebraicSpaces B S hS}
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (hE : DerivedTensorProduct.HasTorAmplitudeGE T E a) :
    ∃ K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ,
      smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ∧
      K.IsStrictlyGE a ∧ Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨P, p, hPkflat, hPflat, hp, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize
      (smallEtaleRingedTopos B S hS X).O (DerivedCategory.Q.objPreimage E)
  have _ : QuasiIso p := hp
  have eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hPamp : DerivedTensorProduct.HasTorAmplitudeGE T (DerivedCategory.Q.obj P) a :=
    hE.of_iso eP
  have _ : P.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff, DerivedCategory.isGE_iff]
    exact fun i hi => (hPamp (SheafOfModules.unit _) i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (T.unitIso _).symm)
  have hCoker := DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitudeGE T P a hPkflat
    hPflat hPamp
  exact ⟨P.truncGE a, smallEtaleModuleKFlat_truncGE P a ⟨hPkflat, hPflat⟩
    (isFlat_truncGE_X P a hPflat hCoker), inferInstance,
    ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ eP⟩⟩

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 06YY, the computation, with `f^* = modulePullback f`.** The derived pullback of a
K-flat complex of flat `𝒪_X`-modules is its degreewise pullback. -/
def smallEtaleDerivedModulePullbackObjQIsoOfKFlat (f : Y ⟶ X)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hK : smallEtaleModuleKFlat B S hS X
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    (smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  have := isIso_smallEtaleDerivedModulePullbackComparison_app B S hS f _ hK
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS Y)
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  haveI : G.Additive := modulePullback_additive f
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app K).symm ≪≫
    asIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.quotient _ _).obj K)) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _ ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (F := F) (G := G)
      (pullbackModulesIsoModulePullback B S hS f) (ComplexShape.up ℤ)).app K)

/-- **Stacks 0G7E with `f^* = modulePullback f`.** The degreewise pullback of a K-flat complex
of flat `𝒪_X`-modules is K-flat with flat terms. -/
theorem smallEtaleModuleKFlat_pb (f : Y ⟶ X)
    (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hK : smallEtaleModuleKFlat B S hS X
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    smallEtaleModuleKFlat B S hS Y ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  let F := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS Y)
    (Y := smallEtaleRingedTopos B S hS X) (smallEtaleRingedToposHom B S hS f).toModulesHom
  let G : type_of% F := modulePullback B S hS f
  have : G.Additive := modulePullback_additive f
  let e := (NatIso.mapHomologicalComplex (F := F) (G := G)
      (pullbackModulesIsoModulePullback B S hS f) (ComplexShape.up ℤ)).app K
  obtain ⟨h₁, h₂⟩ := smallEtaleModuleKFlat_pullbackMapHomotopy B S hS f _ hK
  exact ⟨CochainComplex.KFlatBifunctor.KFlat.of_iso _ h₁ e,
    fun i => Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      ((HomologicalComplex.eval _ _ i).mapIso e) (h₂ i)⟩

section KFlatModel

variable {E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
  {a : ℤ} (K : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (hK : smallEtaleModuleKFlat B S hS X ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
  [K.IsStrictlyGE a] (e : DerivedCategory.Q.obj K ≅ E)

/-- A K-flat model of `E` computes `Lf^*E`: it is the degreewise pullback of the model. -/
def smallEtaleDerivedModulePullbackObjIsoOfKFlat (f : Y ⟶ X) :
    (smallEtaleDerivedModulePullback B S hS f).obj E ≅
      DerivedCategory.Q.obj (((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  (smallEtaleDerivedModulePullback B S hS f).mapIso e.symm ≪≫
    smallEtaleDerivedModulePullbackObjQIsoOfKFlat f K hK

include hK e in
/-- **The derived pullbacks of an object with a K-flat model in degrees `≥ a` vanish below
`a`**: `H^j(Lf^*E) = 0` for `j < a` and every `f`. -/
theorem isZero_pullbackHomology_of_kFlat (f : Y ⟶ X) (j : ℤ) (hj : j < a) :
    IsZero (pullbackHomology E j f) := by
  have : (DerivedCategory.Q.obj
      (((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).IsGE a := by
    rw [DerivedCategory.isGE_Q_obj_iff]
    infer_instance
  exact (DerivedCategory.isZero_of_isGE _ a j hj).of_iso
    ((DerivedCategory.homologyFunctor _ j).mapIso
      (smallEtaleDerivedModulePullbackObjIsoOfKFlat K hK e f))

/-- **The bottom cohomology of a derived pullback is a kernel**: for a K-flat model `K` of `E`
vanishing below `a`, `H^a(Lf^*E) ≅ Ker(f^*K^a ⟶ f^*K^{a+1})`. -/
def pullbackHomologyIsoKernel (f : Y ⟶ X) :
    pullbackHomology E a f ≅ kernel ((pb f).map (K.d a (a + 1))) :=
  let K' := ((pb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  (DerivedCategory.homologyFunctor _ a).mapIso
      (smallEtaleDerivedModulePullbackObjIsoOfKFlat K hK e f) ≪≫
    (DerivedCategory.homologyFunctorFactors _ a).app K' ≪≫
    (K'.isoHomologyπ (a - 1) a (by simp)
      ((CochainComplex.isZero_of_isStrictlyGE K' a (a - 1) (by omega)).eq_of_src _ _)).symm ≪≫
    IsLimit.conePointUniqueUpToIso (K'.cyclesIsKernel a (a + 1) (by simp))
      (limit.isLimit _)

end KFlatModel

/-- **Stacks 0F1M on an algebraic space: vanishing of derived pullbacks below the Tor
amplitude.** If `E` has Tor amplitude in `[a, ∞]`, then `H^j(Lf^*E) = 0` for every morphism
`f` of algebraic spaces and every `j < a`. -/
theorem isZero_pullbackHomology_of_hasTorAmplitudeGE
    (T : DerivedTensorProduct (smallEtaleRingedSite B S hS X.1 X.2))
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) (a : ℤ)
    (hE : DerivedTensorProduct.HasTorAmplitudeGE T E a) (f : Y ⟶ X) (j : ℤ) (hj : j < a) :
    IsZero (pullbackHomology E j f) := by
  obtain ⟨K, hK, _, ⟨e⟩⟩ := exists_kFlat_isStrictlyGE_of_hasTorAmplitudeGE T E a hE
  exact isZero_pullbackHomology_of_kFlat K hK e f j hj

end AlgebraicGeometry.Space

end

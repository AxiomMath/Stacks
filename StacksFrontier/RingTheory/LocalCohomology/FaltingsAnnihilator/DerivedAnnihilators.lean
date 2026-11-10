module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Stabilization
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.AnnihilatorsLocalCohomology.Basic
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Characterization
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDualityExt
public import StacksFrontier.RingTheory.Ext.BaseChange
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.BoundedComparison
public import StacksFrontier.RingTheory.LocalCohomology.DepthExtension.DegreeZero
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterion
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksFrontier.RingTheory.LocalCohomology.SectionsWithSupport
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.Topology.Specialization.Defs
import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessAnnihilatorCriterionPlus

/-!
# Faltings' annihilator theorem

Over a Noetherian ring admitting a dualizing complex, a single ideal supported in a larger
specialization-closed set annihilates the low local cohomology with support in a smaller one
exactly when a depth-plus-dimension inequality holds along every specialization from outside
the larger set into the smaller one.

## Main results

* `Stacks.LocalCohomology.exists_annihilator_localCohomology_iff_depth_add_dim` — the criterion
  for a bounded-below complex with finite cohomology.
* `Stacks.LocalCohomology.annihilatorDepthCriterionPlus` — the same, as the predicate
  `AnnihilatorDepthCriterionPlus` on the base ring.
* `Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff` — the criterion for a
  finite module, which is Faltings' annihilator theorem.
* `Stacks.LocalCohomology.nonempty_adicCompletion_ext_linearEquiv_matlisDual_localCohomology` and
  its bounded-below form `…_localCohomologyPlus` — [Stacks, Tag 0AAK] with local cohomology
  spelled as support in `V(𝔪)`.
* `Stacks.LocalCohomology.nonempty_adicCompletion_localizedDualCohomology_linearEquiv_matlisDual`
  — local duality at an arbitrary prime, objectwise in the complex.

## Implementation notes

Local cohomology with support in a subset is the derived functor of sections with support, and
the comparison with the ideal-supported model is used only to import local duality. The
dualizing complex and the module are taken with modules in the ring's own universe, matching
the local-duality results this rests on.

## References

* [Faltings-annulators]
* [Stacks Project, Tag 0EHZ](https://stacks.math.columbia.edu/tag/0EHZ)
* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.LocalCohomology

open CategoryTheory.Limits CategoryTheory.Pretriangulated

private theorem mem_annihilator_end_iff
    {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear R C] (X : C) (r : R) :
    r ∈ Module.annihilator R (End X) ↔ r • 𝟙 X = 0 := by
  rw [Module.mem_annihilator]
  refine ⟨fun h => by simpa using congrArg End.asHom (h 1), ?_⟩
  intro h f
  ext
  simpa using congrArg (fun g => g ≫ f.asHom) h

private theorem annihilator_end_le_map
    {R : Type u} [CommRing R] {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [Linear R C] [Linear R D]
    (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C) :
    Module.annihilator R (End X) ≤ Module.annihilator R (End (F.obj X)) := by
  intro r hr
  rw [mem_annihilator_end_iff] at hr ⊢
  simpa only [F.map_smul, F.map_id, F.map_zero] using congrArg F.map hr

private theorem mul_le_annihilator_end_of_distinguished
    {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear R C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasZeroObject C] [Pretriangulated C] (T : Triangle C) (hT : T ∈ distinguishedTriangles)
    (I J : Ideal R) (hI : I ≤ Module.annihilator R (End T.obj₁))
    (hJ : J ≤ Module.annihilator R (End T.obj₃)) :
    I * J ≤ Module.annihilator R (End T.obj₂) := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [mem_annihilator_end_iff]
  have hb' := (mem_annihilator_end_iff T.obj₃ b).mp (hJ hb)
  have ha' := (mem_annihilator_end_iff T.obj₁ a).mp (hI ha)
  have hz : (b • 𝟙 T.obj₂) ≫ T.mor₂ = 0 := by
    rw [Linear.smul_comp, Category.id_comp]
    simpa using congrArg (fun f => T.mor₂ ≫ f) hb'
  obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT (b • 𝟙 T.obj₂) hz
  calc
    (a * b) • 𝟙 T.obj₂ = a • (b • 𝟙 T.obj₂) := mul_smul a b _
    _ = a • (f ≫ T.mor₁) := by rw [hf]
    _ = f ≫ (a • 𝟙 T.obj₁) ≫ T.mor₁ := by simp
    _ = 0 := by rw [ha']; simp

private theorem annihilator_end_moduleCat
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    Module.annihilator R (End M) = Module.annihilator R M := by
  ext r
  rw [mem_annihilator_end_iff, Module.mem_annihilator]
  constructor
  · intro h x
    exact ConcreteCategory.congr_hom h x
  · intro h
    ext x
    exact h x

/-- The homology of a truncation `τ≤ b X` is annihilated by `I` when that of `X` is, in degrees
`i ≤ b`. -/
private theorem annihilator_homology_truncLE_of_le
    {A : Type u} [CommRing A] (X : DerivedCategory (ModuleCat.{u} A)) (b i : ℤ) (I : Ideal A)
    (hI : i ≤ b → I ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)) :
    I ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((DerivedCategory.TStructure.t.truncLE b).obj X)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) X
  have : T.obj₁.IsLE b := by
    change ((DerivedCategory.TStructure.t.truncLE b).obj X).IsLE b
    infer_instance
  have : T.obj₃.IsGE (b + 1) := by
    change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsGE (b + 1)
    infer_instance
  change I ≤ Module.annihilator A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj T.obj₁)
  intro r hr
  by_cases hi : i ≤ b
  · have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map T.mor₁) := by
      apply isIso_homology_mor₁ T hT i
      · exact DerivedCategory.isZero_of_isGE T.obj₃ (b + 1) i (by omega)
      · exact DerivedCategory.isZero_of_isGE T.obj₃ (b + 1) (i - 1) (by omega)
    exact (LinearEquiv.annihilator_eq
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        T.mor₁)).toLinearEquiv).symm ▸ hI hi hr
  · have hz := DerivedCategory.isZero_of_isLE T.obj₁ b i (by omega)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Module.mem_annihilator.mpr fun x => Subsingleton.elim _ _

private theorem pow_le_annihilator_end_of_homology
    {A : Type u} [CommRing A] (a : ℤ) (n : ℕ)
    (X : DerivedCategory (ModuleCat.{u} A)) [X.IsGE a] [X.IsLE (a + n)]
    (I : Ideal A)
    (hI : ∀ i : ℤ, I ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)) :
    I ^ (n + 1) ≤ Module.annihilator A (End X) := by
  let (i : ℤ) : Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
    inferInstance
  induction n generalizing X with
  | zero =>
      simp only [zero_add, pow_one]
      have : X.IsLE a := by simpa using (inferInstance : X.IsLE (a + (0 : ℕ)))
      intro r hr
      rw [mem_annihilator_end_iff]
      apply hom_eq_zero_of_isLE_isGE X X a
      rw [Functor.map_smul, CategoryTheory.Functor.map_id]
      exact (mem_annihilator_end_iff _ r).mp
        ((annihilator_end_moduleCat (R := A) _).symm ▸ hI a hr)
  | succ n ih =>
      let b := a + (n : ℤ)
      let T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X
      have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1)
        (by omega) X
      have : X.IsLE (b + 1) := by
        convert (inferInstance : X.IsLE (a + (n + 1 : ℕ))) using 1; dsimp [b]; omega
      have : T.obj₁.IsGE a := by
        change ((DerivedCategory.TStructure.t.truncLE b).obj X).IsGE a
        infer_instance
      have : T.obj₁.IsLE (a + n) := by
        change ((DerivedCategory.TStructure.t.truncLE b).obj X).IsLE b
        infer_instance
      have : T.obj₃.IsGE (b + 1) := by
        change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsGE (b + 1)
        infer_instance
      have : T.obj₃.IsLE (b + 1) := by
        change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsLE (b + 1)
        infer_instance
      have hleft : I ^ (n + 1) ≤ Module.annihilator A (End T.obj₁) :=
        ih T.obj₁ fun i => annihilator_homology_truncLE_of_le X b i I fun _ => hI i
      have hright : I ≤ Module.annihilator A (End T.obj₃) := by
        intro r hr
        rw [mem_annihilator_end_iff]
        apply hom_eq_zero_of_isLE_isGE T.obj₃ T.obj₃ (b + 1)
        rw [Functor.map_smul, CategoryTheory.Functor.map_id]
        rw [← mem_annihilator_end_iff, annihilator_end_moduleCat]
        have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (b + 1)).map T.mor₂) := by
          apply isIso_homology_mor₂ T hT (b + 1)
          · exact DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1) (by omega)
          · exact DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1 + 1) (by omega)
        exact (LinearEquiv.annihilator_eq
          (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (b + 1)).map
            T.mor₂)).toLinearEquiv) ▸
            hI (b + 1) hr
      rw [pow_succ]
      exact mul_le_annihilator_end_of_distinguished T hT _ _ hleft hright

private theorem pow_le_annihilator_truncLE_of_homology
    {A : Type u} [CommRing A] (a : ℤ) (n : ℕ)
    (X : DerivedCategory (ModuleCat.{u} A)) [X.IsGE a] (I : Ideal A)
    (hI : ∀ i : ℤ, i ≤ a + n → I ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)) :
    I ^ (n + 1) ≤ Module.annihilator A
      (End ((DerivedCategory.TStructure.t.truncLE (a + n)).obj X)) := by
  apply pow_le_annihilator_end_of_homology a n _ I
  exact fun i => annihilator_homology_truncLE_of_le X _ i I (hI i)

private theorem mul_le_annihilator_of_exact
    {A : Type u} [CommRing A] (S : ShortComplex (ModuleCat.{u} A)) (hS : S.Exact)
    (I J : Ideal A) (hI : I ≤ Module.annihilator A S.X₁)
    (hJ : J ≤ Module.annihilator A S.X₃) :
    I * J ≤ Module.annihilator A S.X₂ := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  have hz : b • x ∈ LinearMap.ker S.g.hom := by
    simp only [LinearMap.mem_ker, map_smul]
    exact Module.mem_annihilator.mp (hJ hb) _
  rw [← hS.moduleCat_range_eq_ker] at hz
  obtain ⟨y, hy⟩ := hz
  rw [mul_smul, ← hy, ← S.f.hom.map_smul, Module.mem_annihilator.mp (hI ha) y, map_zero]

/-- An element killing `X` kills every homology object of `F.obj X`. -/
private theorem annihilator_end_le_homology_obj
    {A : Type u} [CommRing A]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    [F.Additive] [F.Linear A] (i : ℤ) (X : DerivedCategory (ModuleCat.{u} A)) :
    Module.annihilator A (End X) ≤
      Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (F.obj X)) := by
  have : Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
    inferInstance
  have hmap := (annihilator_end_le_map (R := A) F X).trans
    (annihilator_end_le_map (R := A) (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)
      (F.obj X))
  rwa [annihilator_end_moduleCat] at hmap

theorem pow_le_annihilator_homology_map_of_homology
    {A : Type u} [CommRing A]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    [F.Additive] [F.Linear A] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ (X : DerivedCategory (ModuleCat.{u} A)) (b : ℤ),
      X.IsGE b → (F.obj X).IsGE b)
    (a : ℤ) (n : ℕ) (X : DerivedCategory (ModuleCat.{u} A)) [X.IsGE a]
    (I : Ideal A)
    (hI : ∀ i : ℤ, i ≤ a + n → I ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)) :
    ∀ i : ℤ, i ≤ a + n → I ^ (n + 1) ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (F.obj X)) := by
  let b := a + (n : ℤ)
  let T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1)
    (by omega) X
  have : T.obj₃.IsGE (b + 1) := by
    change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsGE (b + 1)
    infer_instance
  have : (F.obj T.obj₃).IsGE (b + 1) := hF _ _ inferInstance
  have hann := pow_le_annihilator_truncLE_of_homology a n X I hI
  intro i hi
  have hFT := F.map_distinguished T hT
  have hiso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (F.map T.mor₁)) := by
    apply isIso_homology_mor₁ (F.mapTriangle.obj T) hFT i
    · exact DerivedCategory.isZero_of_isGE (F.obj T.obj₃) (b + 1) i (by dsimp [b]; omega)
    · exact DerivedCategory.isZero_of_isGE (F.obj T.obj₃) (b + 1) (i - 1) (by dsimp [b]; omega)
  exact (LinearEquiv.annihilator_eq
    (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (F.map T.mor₁))).toLinearEquiv) ▸
      hann.trans (annihilator_end_le_homology_obj F i T.obj₁)

noncomputable def localCohomologyPlusIso
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory.Plus (ModuleCat.{max u v} A)) (i : ℤ) :
    localCohomologyWithSupportInPlus
      A T K i ≅
    localCohomologyWithSupportIn
      A T K.obj i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
    ((Classical.choice
      (Stacks.LocalCohomology.nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso
        A T)).app K)

noncomputable def plusQhQuotientIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (N : CochainComplex.Plus C) :
    DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient C).obj N) ≅ DerivedCategory.Plus.Q.obj N :=
  DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.QhCompιIsoιCompQh C).app _ ≪≫
      DerivedCategory.Qh.mapIso
        ((HomotopyCategory.Plus.quotientCompιIso C).app N) ≪≫
      (DerivedCategory.quotientCompQhIso C).app N.obj)

noncomputable def rightDerivedPlusObjIsoOfInjectiveComplex
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] (L : CochainComplex.Plus C)
    [∀ i, Injective (L.obj.X i)] (Y : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Q.obj L ≅ Y) :
    F.rightDerivedFunctorPlus.obj Y ≅
      DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj L) := by
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj L)) := by
    have : ∀ i, Injective (((HomotopyCategory.Plus.quotient C).obj L).obj.as.X i) :=
      fun i => inferInstance
    infer_instance
  exact F.rightDerivedFunctorPlus.mapIso
      (e.symm ≪≫ (plusQhQuotientIso L).symm) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient C).obj L))).symm ≪≫
    plusQhQuotientIso (F.mapCochainComplexPlus.obj L)

noncomputable def rightDerivedPlusLowestHomologyIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (Y : DerivedCategory.Plus C) (a : ℤ) [Y.IsGE a] :
    (DerivedCategory.Plus.homologyFunctor D a).obj (F.rightDerivedFunctorPlus.obj Y) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor C a).obj Y) := by
  apply Classical.choice
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Y a
  let N := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let (i : ℤ) : Injective (N.obj.X i) := by
    change Injective ((InjectiveObject.ι C).obj (L.obj.X i))
    infer_instance
  have : N.obj.IsStrictlyGE a := by
    change CochainComplex.IsStrictlyGE
      (((InjectiveObject.ι C).mapHomologicalComplex (.up ℤ)).obj L.obj) a
    infer_instance
  let NF := F.mapCochainComplexPlus.obj N
  let eF := rightDerivedPlusObjIsoOfInjectiveComplex F N Y e
  have hd : N.obj.d (a - 1) a = 0 :=
    (N.obj.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _
  have hdF : NF.obj.d (a - 1) a = 0 := by
    change F.map (N.obj.d (a - 1) a) = 0
    rw [hd, F.map_zero]
  let ec : F.obj (N.obj.cycles a) ≅ NF.obj.cycles a :=
    IsLimit.conePointUniqueUpToIso
      (KernelFork.mapIsLimit _ (N.obj.cyclesIsKernel a (a + 1) (by simp)) F)
      (NF.obj.cyclesIsKernel a (a + 1) (by simp))
  let hN : (DerivedCategory.Plus.homologyFunctor C a).obj (DerivedCategory.Plus.Q.obj N) ≅
      N.obj.homology a := (DerivedCategory.homologyFunctorFactors C a).app N.obj
  let hNF : (DerivedCategory.Plus.homologyFunctor D a).obj (DerivedCategory.Plus.Q.obj NF) ≅
      NF.obj.homology a := (DerivedCategory.homologyFunctorFactors D a).app NF.obj
  exact ⟨(DerivedCategory.Plus.homologyFunctor D a).mapIso eF ≪≫ hNF ≪≫
    (NF.obj.isoHomologyπ (a - 1) a (by simp) hdF).symm ≪≫ ec.symm ≪≫
    F.mapIso (N.obj.isoHomologyπ (a - 1) a (by simp) hd ≪≫ hN.symm ≪≫
      (DerivedCategory.Plus.homologyFunctor C a).mapIso e)⟩

noncomputable def derivedSectionsWithSupportInPlusCompObjIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT' : StableUnderSpecialization T')
    (Y : DerivedCategory.Plus (ModuleCat.{u} A)) :
    (derivedSectionsWithSupportInPlus.{u, u} A T).obj
      ((derivedSectionsWithSupportInPlus.{u, u} A T').obj Y) ≅
      (derivedSectionsWithSupportInPlus.{u, u} A (T ∩ T')).obj Y := by
  apply Classical.choice
  let C := ModuleCat.{u} A
  let : EnoughInjectives C := ModuleCat.enoughInjectives A
  obtain ⟨a, ha⟩ := Y.property
  have : Y.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Y a).mp ha
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Y a
  let N := (InjectiveObject.ι C).mapCochainComplexPlus.obj L
  let F := sectionsWithSupportInFunctor.{u, u} A T'
  let G := sectionsWithSupportInFunctor.{u, u} A T
  let H := sectionsWithSupportInFunctor.{u, u} A (T ∩ T')
  let N' := F.mapCochainComplexPlus.obj N
  let (i : ℤ) : Injective (N.obj.X i) := by
    change Injective ((InjectiveObject.ι C).obj (L.obj.X i))
    infer_instance
  let (i : ℤ) : Injective (N'.obj.X i) :=
    (Module.injective_iff_injective_object A _).mp
      (Stacks.LocalCohomology.injective_sectionsWithSupportIn T' hT' (N.obj.X i))
  let eF := rightDerivedPlusObjIsoOfInjectiveComplex F N Y e
  let eG := rightDerivedPlusObjIsoOfInjectiveComplex G N' (F.rightDerivedFunctorPlus.obj Y) eF.symm
  let eH := rightDerivedPlusObjIsoOfInjectiveComplex H N Y e
  let eN : G.mapCochainComplexPlus.obj N' ≅ H.mapCochainComplexPlus.obj N :=
    (CochainComplex.Plus.ι C).preimageIso
      ((Functor.mapHomologicalComplexCompIso
        (Stacks.LocalCohomology.sectionsWithSupportInCompIso A T T')
        (ComplexShape.up ℤ)).app N.obj)
  exact ⟨eG ≪≫ DerivedCategory.Plus.Q.mapIso eN ≪≫ eH.symm⟩

noncomputable def localCohomologyPlusCompIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T T' : Set (PrimeSpectrum A)) (hT' : StableUnderSpecialization T')
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (i : ℤ) :
    localCohomologyWithSupportInPlus A T
      ((derivedSectionsWithSupportInPlus A T').obj K) i ≅
      localCohomologyWithSupportInPlus A (T ∩ T') K i :=
  (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).mapIso
    (derivedSectionsWithSupportInPlusCompObjIso A T T' hT' K)

lemma isGE_derivedSectionsWithSupportIn
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ) [K.IsGE a] :
    ((derivedSectionsWithSupportIn.{u, u}
      A T).obj K).IsGE a := by
  let X : DerivedCategory.Plus (ModuleCat.{u} A) := ⟨K, a, inferInstance⟩
  have : X.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff X a).mp
    (by change K.IsGE a; infer_instance)
  have : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives A
  have h := Functor.isGE_rightDerivedFunctorPlus_obj
    (sectionsWithSupportInFunctor.{u, u} A T) X a
  exact (DerivedCategory.isGE_iff _ a).mpr fun i hi =>
    (DerivedCategory.Plus.isZero_homology_of_isGE
      ((sectionsWithSupportInFunctor.{u, u} A T).rightDerivedFunctorPlus.obj X) a i hi).of_iso
        (localCohomologyPlusIso A T X i).symm

noncomputable def localCohomologyLowestIso
    (A : Type u) [CommRing A] (Z : Set (PrimeSpectrum A))
    (X : DerivedCategory.Plus (ModuleCat.{u} A))
    (i : ℤ) [X.obj.IsGE i] :
    localCohomologyWithSupportInPlus A Z X i ≅
      (sectionsWithSupportInFunctor.{u, u} A Z).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) i).obj X) := by
  have : X.IsGE i := (DerivedCategory.Plus.isGE_ι_obj_iff X i).mp
    (by change X.obj.IsGE i; infer_instance)
  have : EnoughInjectives (ModuleCat.{u} A) := ModuleCat.enoughInjectives A
  letI : PreservesFiniteLimits (sectionsWithSupportInFunctor.{u, u} A Z) :=
    Stacks.LocalCohomology.sectionsWithSupportInFunctor_preservesFiniteLimits Z
  exact rightDerivedPlusLowestHomologyIso (sectionsWithSupportInFunctor.{u, u} A Z) X i

theorem mul_pow_le_annihilator_sections_homology
    (A : Type u) [CommRing A] (Z : Set (PrimeSpectrum A))
    (X : DerivedCategory.Plus (ModuleCat.{u} A))
    (a : ℤ) (n : ℕ) [X.obj.IsGE a] (I J : Ideal A)
    (hI : ∀ j : ℤ, j ≤ a + n → I ≤ Module.annihilator A
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) j).obj X))
    (hJ : J ≤ Module.annihilator A
      (localCohomologyWithSupportInPlus A Z X (a + n + 1))) :
    J * I ^ (n + 1) ≤ Module.annihilator A
      ((sectionsWithSupportInFunctor.{u, u} A Z).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) (a + n + 1)).obj X)) := by
  let C := ModuleCat.{u} A
  let b := a + (n : ℤ)
  let T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X.obj
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) X.obj
  let F := derivedSectionsWithSupportIn.{u, u} A Z
  let F₀ := sectionsWithSupportInFunctor.{u, u} A Z
  let : F.Linear A := Stacks.LocalCohomology.derivedSectionsWithSupportIn_linear A Z
  let : F.CommShift ℤ := Stacks.LocalCohomology.derivedSectionsWithSupportIn_commShift A Z
  let : F.IsTriangulated := Stacks.LocalCohomology.derivedSectionsWithSupportIn_isTriangulated A Z
  have : T.obj₁.IsLE b := by
    change ((DerivedCategory.TStructure.t.truncLE b).obj X.obj).IsLE b
    infer_instance
  have : T.obj₃.IsGE (b + 1) := by
    change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X.obj).IsGE (b + 1)
    infer_instance
  let R : DerivedCategory.Plus C := ⟨T.obj₃, b + 1, inferInstance⟩
  have hlow : I ^ (n + 1) ≤ Module.annihilator A (End T.obj₁) :=
    pow_le_annihilator_truncLE_of_homology a n X.obj I hI
  have hF := F.map_distinguished T hT
  have he := (DerivedCategory.homologyFunctor C 0).homologySequence_exact₃
    (F.mapTriangle.obj T) hF (b + 1) (b + 1 + 1) rfl
  have hlast : I ^ (n + 1) ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor C (b + 1 + 1)).obj (F.obj T.obj₁)) :=
    hlow.trans (annihilator_end_le_homology_obj F (b + 1 + 1) T.obj₁)
  have hmid : J * I ^ (n + 1) ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor C (b + 1)).obj (F.obj T.obj₃)) :=
    mul_le_annihilator_of_exact _ he J (I ^ (n + 1))
      (hJ.trans_eq (localCohomologyPlusIso A Z X (b + 1)).toLinearEquiv.annihilator_eq) hlast
  have : IsIso ((DerivedCategory.homologyFunctor C (b + 1)).map T.mor₂) :=
    isIso_homology_mor₂ T hT (b + 1)
      (DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1) (by omega))
      (DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1 + 1) (by omega))
  let e := (localCohomologyPlusIso A Z R (b + 1)).symm ≪≫
    localCohomologyLowestIso A Z R (b + 1) ≪≫
      F₀.mapIso (asIso ((DerivedCategory.homologyFunctor C (b + 1)).map T.mor₂)).symm
  exact hmid.trans_eq e.toLinearEquiv.annihilator_eq

theorem depth_gt_of_localCohomology_isZero
    (A : Type u) [CommRing A] (I : Ideal A)
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (s : ℤ)
    (hzero : ∀ i : ℤ, i ≤ s → CategoryTheory.Limits.IsZero
      (localCohomologyWithSupportInPlus
        A (PrimeSpectrum.zeroLocus (I : Set A)) K i)) :
    (DerivedCategory.Plus.depth A I K : EInt) > (s : EInt) := by
  change (WithBot.some (DerivedCategory.Plus.depth A I K) : EInt) >
    (WithBot.some (s : WithTop ℤ) : EInt)
  apply WithBot.coe_lt_coe.mpr
  have hbound : ((s + 1 : ℤ) : WithTop ℤ) ≤ DerivedCategory.Plus.depth A I K := by
    change ((s + 1 : ℤ) : WithTop ℤ) ≤
      sInf ((fun i : ℤ => (i : WithTop ℤ)) ''
        {i : ℤ | ¬ CategoryTheory.Limits.IsZero
          (localCohomologyWithSupportInPlus
            A (PrimeSpectrum.zeroLocus (I : Set A)) K i)})
    by_cases hS : ((fun i : ℤ => (i : WithTop ℤ)) ''
        {i : ℤ | ¬ CategoryTheory.Limits.IsZero
          (localCohomologyWithSupportInPlus
            A (PrimeSpectrum.zeroLocus (I : Set A)) K i)}).Nonempty
    · apply le_csInf hS
      intro x hx
      rcases hx with ⟨i, hiNZ, hi⟩
      rw [← hi]
      change ¬ CategoryTheory.Limits.IsZero
        (localCohomologyWithSupportInPlus
          A (PrimeSpectrum.zeroLocus (I : Set A)) K i) at hiNZ
      have hnot : ¬ i ≤ s := fun h => hiNZ (hzero i h)
      exact WithTop.coe_le_coe.mpr (by omega)
    · rw [Set.not_nonempty_iff_eq_empty.mp hS]
      simp
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by omega)) hbound

theorem localCohomology_isZero_of_lt_depth
    (A : Type u) [CommRing A] (I : Ideal A)
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) (i : ℤ)
    (hi : (i : EInt) < DerivedCategory.Plus.depth A I K) :
    CategoryTheory.Limits.IsZero
      (localCohomologyWithSupportInPlus
        A (PrimeSpectrum.zeroLocus (I : Set A)) K i) := by
  classical
  by_contra hn
  let L := derivedSectionsWithSupportInPlus
    A (PrimeSpectrum.zeroLocus (I : Set A)) |>.obj K
  obtain ⟨b, hb⟩ := L.property
  have hbounded : BddBelow ((fun j : ℤ => (j : WithTop ℤ)) ''
      {j : ℤ | ¬ CategoryTheory.Limits.IsZero
        (localCohomologyWithSupportInPlus
          A (PrimeSpectrum.zeroLocus (I : Set A)) K j)}) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    apply WithTop.coe_le_coe.mpr
    by_contra hbj
    exact hj ((DerivedCategory.isGE_iff L.obj b).mp hb j (lt_of_not_ge hbj))
  have hle : DerivedCategory.Plus.depth A I K ≤ (i : WithTop ℤ) :=
    csInf_le hbounded ⟨i, hn, rfl⟩
  exact (not_lt_of_ge (WithBot.coe_le_coe.mpr hle)) hi

private theorem exists_matlisDual_apply_ne_zero
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M E : ModuleCat.{u} R) [Injective E]
    (e : (ModuleCat.uliftFunctor.{u} R).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R)) ⟶ E) [Mono e]
    (x : M) (hx : x ≠ 0) : ∃ f : M →ₗ[R] E, f x ≠ 0 := by
  let g := LinearMap.toSpanSingleton R M x
  have hg : g.ker ≠ ⊤ := by
    intro h
    have h1 : g 1 = 0 := (LinearMap.mem_ker).mp (h ▸ Submodule.mem_top)
    exact hx (by simpa [g] using h1)
  let j : R →ₗ[R] E := e.hom.comp
    (ULift.moduleEquiv.symm.toLinearMap.comp (Algebra.linearMap R (ResidueField R)))
  have hker : g.ker ≤ j.ker := by
    intro r hr
    have hrm := IsLocalRing.le_maximalIdeal hg hr
    have hz : algebraMap R (ResidueField R) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrm
    change e.hom (ULift.up (algebraMap R (ResidueField R) r)) = 0
    rw [hz]
    exact e.hom.map_zero
  let g' : g.range →ₗ[R] E := (g.ker.liftQ j hker).comp
    g.quotKerEquivRange.symm.toLinearMap
  let : Module.Injective R E := Module.injective_module_of_injective_object R E
  obtain ⟨f, hf⟩ := Module.Injective.out g.range.subtype Subtype.val_injective g'
  refine ⟨f, ?_⟩
  have hfx : f x = e.hom (ULift.up (1 : ResidueField R)) := by
    have h := hf ⟨g 1, LinearMap.mem_range_self g 1⟩
    change f (g 1) = (g.ker.liftQ j hker)
      (g.quotKerEquivRange.symm ⟨g 1, LinearMap.mem_range_self g 1⟩) at h
    rw [LinearMap.quotKerEquivRange_symm_apply_image] at h
    change f (g 1) = j 1 at h
    have h1 : g 1 = x := by simp [g]
    rw [h1] at h
    change f x = e.hom (ULift.up (algebraMap R (ResidueField R) 1)) at h
    simpa only [map_one] using h
  rw [hfx]
  intro h
  have hinj := (ModuleCat.mono_iff_injective e).mp inferInstance
  have : (ULift.up (1 : ResidueField R) : ULift.{u} (ResidueField R)) = 0 :=
    hinj (h.trans e.hom.map_zero.symm)
  exact one_ne_zero (congrArg ULift.down this)

theorem annihilator_matlisDual
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M E : ModuleCat.{u} R) [Injective E]
    (e : (ModuleCat.uliftFunctor.{u} R).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R)) ⟶ E) [Mono e] :
    Module.annihilator R (M →ₗ[R] E) = Module.annihilator R M := by
  ext r
  simp only [Module.mem_annihilator]
  refine ⟨fun hr x => ?_, fun hr f => ?_⟩
  · by_contra hx
    obtain ⟨f, hf⟩ := exists_matlisDual_apply_ne_zero R M E e (r • x) hx
    have h := congrArg (fun g : M →ₗ[R] E => g x) (hr f)
    change r • f x = 0 at h
    exact hf ((f.map_smul r x).trans h)
  · ext x
    change r • f x = 0
    rw [← map_smul, hr x, map_zero]

theorem annihilator_adicCompletion
    {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [IsHausdorff I M] :
    Module.annihilator R (AdicCompletion I M) = Module.annihilator R M := by
  refine le_antisymm
    ((AdicCompletion.of I M).annihilator_le_of_injective
      (AdicCompletion.of_injective I M)) ?_
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro x
  apply AdicCompletion.ext
  intro n
  rw [AdicCompletion.val_smul_apply, AdicCompletion.val_zero_apply]
  obtain ⟨m, hm⟩ := (I ^ n • (⊤ : Submodule R M)).mkQ_surjective (x.val n)
  rw [← hm, ← map_smul, hr, map_zero]

end Stacks.LocalCohomology

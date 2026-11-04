module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionMap
public import StacksFrontier.Homology.Perfect.NilpotentLifting
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory

/-!
# Vanishing of the obstruction to lifting a derived complex

For a square-zero surjection `R' → R` of commutative rings, a bounded-above object `K` of
`D(R)` lifts to `D(R')` precisely when its canonical obstruction morphism vanishes.

The proof is the one in the source. One direction is immediate: a lift supplies a complex of
`R'`-modules whose reduction represents `K`, so the squares of its differentials are zero and
the obstruction class they compute is zero. For the converse, a vanishing obstruction gives a
homotopy killing the square of the lifted differential on a bounded-above free lift; correcting
the lifted differential by that homotopy produces an honest complex of `R'`-modules, and its
derived extension of scalars is isomorphic to `K`.

## Main results

* `Deformation.Obstruction.canonicalObstructionMap_eq_zero_iff_exists_lift`: the vanishing
  criterion for a derived lift.

## Implementation notes

A derived lift is expressed by an isomorphism from its derived extension of scalars to the
given complex; equality of objects in a derived category is not the appropriate notion of
identification.

## References

* [Stacks Project, Tag 0DYR](https://stacks.math.columbia.edu/tag/0DYR)
-/

@[expose] public section

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
  CochainComplex.DerivedExtensionScalars
attribute [local instance] HasDerivedCategory.standard

namespace Deformation.Obstruction

universe u

private lemma exists_free_cover
    {R : Type u} [Ring R] [Small.{u} R] (X : ModuleCat.{u} R) :
    ∃ (Y : ModuleCat.{u} R) (_ : Module.Free R Y) (p : Y ⟶ X), Epi p := by
  let e : Module.Basis X R (X →₀ Shrink.{u} R) :=
    ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv R R)⟩
  refine ⟨ModuleCat.of R (X →₀ Shrink.{u} R), Module.Free.of_basis e,
    ModuleCat.ofHom (e.constr ℕ _root_.id), ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  intro x
  exact ⟨Finsupp.single x 1, by simp [e, Module.Basis.constr_apply]⟩

/-- A complex of free modules has projective terms. -/
private lemma projective_X_of_free {R : Type u} [CommRing R]
    {C : CochainComplex (ModuleCat.{u} R) ℤ} (hfree : ∀ n, Module.Free R (C.X n)) (n : ℤ) :
    Projective (C.X n) := by
  have := hfree n
  infer_instance

private theorem exists_boundedAbove_free_representative
    {R : Type u} [CommRing R] [Small.{u} R]
    (K : DerivedCategory (ModuleCat.{u} R)) (b : ℤ) [K.IsLE b] :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      P.IsStrictlyLE b ∧ (∀ i, Module.Free R (P.X i)) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  classical
  obtain ⟨L, e, hL⟩ := ‹K.IsLE b›
  let : L.IsStrictlyLE b := hL
  let F : ObjectProperty (ModuleCat.{u} R) := fun X => Module.Free R X
  let : F.ContainsZero := ⟨⟨ModuleCat.of R (Fin 0 → Shrink.{u} R),
    ModuleCat.isZero_of_subsingleton _, inferInstance⟩⟩
  obtain ⟨P, p, _, hp, hfree, hbound⟩ :=
    (CochainComplex.exists_quasiIso_prop F exists_free_cover b).1 L
  have : QuasiIso p := hp
  exact ⟨P, hbound, hfree, ⟨asIso (DerivedCategory.Q.map p) ≪≫ e.symm⟩⟩

private noncomputable def canonicalFreeDifferentialLift
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (Q : CochainComplex (ModuleCat.{u} R') ℤ)
    (hfree : ∀ n, Module.Free R' (Q.X n)) :
    Deformation.Obstruction.FreeDifferentialLift f
      (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Q) := by
  letI : Algebra R' R := f.toAlgebra
  let F := ModuleCat.extendScalars.{u, u, u} f
  let E := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let red (n : ℤ) : Q.X n →ₛₗ[f] (E.obj Q).X n := {
    toFun := fun x => (1 : R) ⊗ₜ[R'] x
    map_add' := by intro x y; exact TensorProduct.tmul_add (1 : R) x y
    map_smul' := by
      intro r x
      change (1 : R) ⊗ₜ[R'] (r • x) = f r • ((1 : R) ⊗ₜ[R'] x)
      exact (TensorProduct.smul_tmul r (1 : R) x).symm }
  have hred_surj (n : ℤ) : Function.Surjective (red n) := by
    change Function.Surjective (TensorProduct.mk R' R (Q.X n) (1 : R))
    exact TensorProduct.mk_surjective R' (Q.X n) R hf
  refine {
    X := Q.X
    free := hfree
    d := Q.d
    shape := fun i j hij => Q.shape i j hij
    reduction := red
    reduction_surjective := hred_surj
    reduction_ker := ?_
    reduction_d := ?_ }
  · intro n
    exact MilnorPatching.ker_tensorProductMk_of_surjective f hf
  · intro i j x
    change (1 : R) ⊗ₜ[R'] (Q.d i j).hom x =
      (1 : R) ⊗ₜ[R'] (Q.d i j).hom x
    rfl

private theorem isZero_derivedTensor_single_of_isStrictlyLE
    {R : Type u} [CommRing R]
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ) (hb : E.IsStrictlyLE b)
    (hE : E.KFlat) (M : ModuleCat.{u} R) (i : ℤ) (hi : b < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((T.tensor.obj (DerivedCategory.Q.obj E)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) := by
  obtain ⟨P, hPproj, hPLE, ⟨eP⟩⟩ :=
    StacksDraft.TorAmplitude.exists_projective_representative_of_isLE
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) 0
      ((DerivedCategory.isLE_iff _ 0).1 inferInstance)
  have hPKF : P.KFlat := StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective P 0 hPproj
  have hbdd : (E ⊗ P).IsStrictlyLE (b + 0) :=
    TotalTensorComplex.tensor_isStrictlyLE E P b 0
  have : (E ⊗ P).IsStrictlyLE b := by simpa using hbdd
  refine IsZero.of_iso ?_
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      ((T.tensor.obj (DerivedCategory.Q.obj E)).mapIso eP ≪≫ T.comparison E P hE hPKF) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app (E ⊗ P))
  apply ShortComplex.isZero_homology_of_isZero_X₂
  exact CochainComplex.isZero_of_isStrictlyLE (E ⊗ P) b i hi

private theorem isLE_of_nilpotent_reduction
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (D : CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars f)
    (K : DerivedCategory (ModuleCat.{u} R')) (b : ℤ)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (hb : E.IsStrictlyLE b)
    (hEprojective : ∀ i : ℤ, Module.Projective R (E.X i))
    (hErep : Nonempty (DerivedCategory.Q.obj E ≅ D.functor.obj K)) : K.IsLE b := by
  have hEproj : ∀ i : ℤ, Projective (E.X i) := fun i => by
    have := hEprojective i
    infer_instance
  have hEKF : E.KFlat := StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective
    E b hEproj
  have : D.functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ D.functor ⟶
        (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := ModuleCat.{u} R) from D.comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R') (ComplexShape.up ℤ)) := D.isLeftDerived
  refine StacksDraft.TorAmplitude.isLE_of_hasTorAmplitudeAbove_derivedExtensionScalars f hf
    ⟨2, hzero⟩ D.functor
    (show DerivedCategory.Q (C := ModuleCat.{u} R') ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q (C := ModuleCat.{u} R) from D.comparison)
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R')
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) K b ?_
  intro M i hi
  refine (isZero_derivedTensor_single_of_isStrictlyLE
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R) E b hb hEKF M i hi).of_iso ?_
  exact (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
    (((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor.mapIso
      hErep.some).app _).symm

private theorem curvature_toDerived_eq_zero_of_zero_square
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {K : DerivedCategory (ModuleCat.{u} R)}
    (L : Deformation.Obstruction.FreeDifferentialLift f P)
    (e : DerivedCategory.Q.obj P ≅ K)
    (c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L)
    (hdd : ∀ n x, L.d (n + 1) (n + 2) (L.d n (n + 1) x) = 0) :
    c.toDerived e = 0 := by
  have hhom : c.hom = 0 := by
    ext n x
    obtain ⟨y, rfl⟩ := L.reduction_surjective n x
    apply c.kernelEmbedding_injective (n + 2)
    rw [c.hom_eq_square]
    show _ = c.kernelEmbedding (n + 2) 0
    rw [map_zero]
    exact hdd n y
  simp [Deformation.Obstruction.LiftedDifferentialCurvature.toDerived, hhom]

private theorem toDerived_eq_zero_iff_qMap_hom_eq_zero
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {K : DerivedCategory (ModuleCat.{u} R)}
    (c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L)
    (e : DerivedCategory.Q.obj P ≅ K) :
    c.toDerived e = 0 ↔ DerivedCategory.Q.map c.hom = 0 := by
  let r := ((DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (P ⊗
    Deformation.Obstruction.kernelComplex f hf)) ≫ (shiftFunctor (DerivedCategory (ModuleCat.{u} R))
      (2 : ℤ)).map (c.tensorComparison ≫
        ((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor R).map e.hom).app
          (Deformation.Obstruction.squareZeroKernelObject f hf))
  have : IsIso (DerivedCategory.Q.map (𝟙 P ⊗ₘ c.kernelResolutionMap)) :=
    c.tensorResolution_isIso
  have : IsIso (DerivedCategory.Q.map c.kernelResolutionMap) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 c.kernelResolution_quasiIso
  have : IsIso c.tensorComparison := by
    dsimp [Deformation.Obstruction.LiftedDifferentialCurvature.tensorComparison]
    infer_instance
  have : IsIso r := by
    dsimp [r]
    infer_instance
  refine ⟨fun h => ?_, fun h => by
    simp [Deformation.Obstruction.LiftedDifferentialCurvature.toDerived, h]⟩
  have h' : (e.inv ≫ DerivedCategory.Q.map c.hom) ≫ r = 0 := by
    simpa [r, Deformation.Obstruction.LiftedDifferentialCurvature.toDerived,
      Category.assoc] using h
  rw [← cancel_epi e.inv, ← cancel_mono r, h']
  simp

private lemma nonempty_homotopy_zero_of_Q_map_eq_zero
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {P Q : CochainComplex A ℤ} [P.IsKProjective] (f : P ⟶ Q)
    (hf : DerivedCategory.Q.map f = 0) : Nonempty (Homotopy f 0) := by
  apply (HomotopyCategory.quotient_map_eq_zero_iff f).1
  apply (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj Q)).injective
  rw [Functor.map_zero, ← cancel_mono ((DerivedCategory.quotientCompQhIso A).hom.app Q)]
  simp only [DerivedCategory.quotientCompQhIso_hom_naturality, hf,
    Limits.comp_zero, Limits.zero_comp]

private lemma exists_curvature_homotopy_of_obstruction_eq_zero
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K)
    (hω : (Deformation.Obstruction.canonicalObstructionMap
      f hf hzero K hK).val = 0) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ),
      P.IsStrictlyLE b ∧ (∀ n, Module.Free R (P.X n)) ∧
      ∃ (_e : DerivedCategory.Q.obj P ≅ K)
        (L : Deformation.Obstruction.FreeDifferentialLift f P)
        (c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L),
        Nonempty (Homotopy c.hom 0) := by
  let ω := Deformation.Obstruction.canonicalObstructionMap f hf hzero K hK
  obtain ⟨P, b, hb, hfree, ⟨e⟩⟩ := ω.property.exists_free_representative
  obtain ⟨L⟩ := ω.property.exists_lift P hfree
  obtain ⟨c⟩ := ω.property.exists_curvature P b hb hfree L
  have hto : c.toDerived e = 0 := by
    rw [← ω.property.eq_curvature P b hb hfree e L c]
    exact hω
  have hmap : DerivedCategory.Q.map c.hom = 0 :=
    (toDerived_eq_zero_iff_qMap_hom_eq_zero c e).1 hto
  have : ∀ n, Projective (P.X n) := projective_X_of_free hfree
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  exact ⟨P, b, hb, hfree, e, L, c,
    nonempty_homotopy_zero_of_Q_map_eq_zero c.hom hmap⟩

private noncomputable def curvatureHomotopyComponent
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) :
    P.X n ⟶ (P ⊗ Deformation.Obstruction.kernelComplex f hf).X (n + 1) :=
  h.hom n (n - 1) ≫
    ((P ⊗ Deformation.Obstruction.kernelComplex f hf).shiftFunctorObjXIso
      2 (n - 1) (n + 1) (by omega)).hom

private lemma kernelEmbedding_reduction_zero
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (n : ℤ) (z : (P ⊗ Deformation.Obstruction.kernelComplex f hf).X n) :
    L.reduction n (c.kernelEmbedding n z) = 0 := by
  obtain ⟨w, rfl⟩ := kernelTensorInclusion_surjective (f := f) (hf := hf) P n z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' =>
      rw [(Deformation.Obstruction.kernelTensorInclusion f hf P n).hom.map_add,
        (c.kernelEmbedding n).map_add, (L.reduction n).map_add, hw, hw']
      simp
  | tmul x a =>
      obtain ⟨y, rfl⟩ := L.reduction_surjective n x
      obtain ⟨a', rfl⟩ := (RingHom.ker f).toCotangent_surjective a
      rw [c.kernelEmbedding_tmul n y a']
      simp [RingHom.mem_ker.mp a'.property]

private noncomputable def curvatureCorrection
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) : L.X n ⟶ L.X (n + 1) := by
  letI := L.free n
  let B := Module.Free.chooseBasis R' (L.X n)
  exact ModuleCat.ofHom (B.constr R' fun i =>
    c.kernelEmbedding (n + 1)
      ((curvatureHomotopyComponent h n).hom
          (L.reduction n (B i))))

private lemma curvatureCorrection_apply_basis
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) [Module.Free R' (L.X n)]
    (i : Module.Free.ChooseBasisIndex R' (L.X n)) :
    (curvatureCorrection h n).hom (Module.Free.chooseBasis R' (L.X n) i) =
      c.kernelEmbedding (n + 1)
        (((P ⊗ Deformation.Obstruction.kernelComplex f hf).shiftFunctorObjXIso
          2 (n - 1) (n + 1) (by omega)).hom.hom
            (h.hom n (n - 1)
              (L.reduction n (Module.Free.chooseBasis R' (L.X n) i)))) := by
  let := L.free n
  simp [curvatureCorrection, curvatureHomotopyComponent, Module.Basis.constr_apply,
    Module.Basis.repr_self]

private noncomputable def curvatureCorrectionExpected
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) : L.X n ⟶ L.X (n + 1) := by
  letI : Module.Free R' (L.X n) := L.free n
  let ψ : (L.X n : Type u) →ₗ[R'] (L.X (n + 1) : Type u) := {
    toFun := fun x => c.kernelEmbedding (n + 1)
      ((curvatureHomotopyComponent h n).hom (L.reduction n x))
    map_add' := by
      intro x y
      simp
    map_smul' := by
      intro r x
      rw [LinearMap.map_smulₛₗ (L.reduction n) r x]
      rw [LinearMap.map_smul (curvatureHomotopyComponent h n).hom (f r)]
      simpa using kernelEmbedding_smul c (n + 1) r
        ((curvatureHomotopyComponent h n).hom (L.reduction n x))
  }
  exact ModuleCat.ofHom ψ

private lemma curvatureCorrection_eq_expected
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) [Module.Free R' (L.X n)] :
    curvatureCorrection h n = curvatureCorrectionExpected h n := by
  apply ModuleCat.hom_ext
  apply (Module.Free.chooseBasis R' (L.X n)).ext
  intro i
  rw [curvatureCorrection_apply_basis]
  rfl

private lemma curvatureCorrection_reduction
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) (x : L.X n) :
    L.reduction (n + 1) ((curvatureCorrection h n).hom x) = 0 := by
  let := L.free n
  rw [congrArg ModuleCat.Hom.hom (curvatureCorrection_eq_expected h n)]
  exact kernelEmbedding_reduction_zero (n + 1)
    ((curvatureHomotopyComponent h n).hom (L.reduction n x))

private lemma curvatureCorrection_sq
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) (x : L.X n) :
    (curvatureCorrection h (n + 1)).hom ((curvatureCorrection h n).hom x) = 0 := by
  let : Module.Free R' (L.X n) := L.free n
  let : Module.Free R' (L.X (n + 1)) := L.free (n + 1)
  rw [congrArg ModuleCat.Hom.hom (curvatureCorrection_eq_expected h (n + 1))]
  show c.kernelEmbedding ((n + 1) + 1)
    ((curvatureHomotopyComponent h (n + 1)).hom
      (L.reduction (n + 1) ((curvatureCorrection h n).hom x))) = 0
  rw [curvatureCorrection_reduction h n x]
  simp

private lemma homotopy_shiftComponent_eq
    {R : Type u} [CommRing R]
    {A B : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : A ⟶ B⟦(2 : ℤ)⟧}
    (h : Homotopy f g) (i j k t : ℤ) (hjk : j = k)
    (hjt : t = j + 2) (hkt : t = k + 2) :
    h.hom i j ≫ (B.shiftFunctorObjXIso 2 j t hjt).hom =
      h.hom i k ≫ (B.shiftFunctorObjXIso 2 k t hkt).hom := by
  cases hjk
  rfl

private lemma curvatureHomotopy_comm
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) :
    c.hom.f n ≫ (CochainComplex.shiftFunctorObjXIso
        (P ⊗ Deformation.Obstruction.kernelComplex f hf)
        2 n ((n + 1) + 1) (by omega)).hom =
      P.d n (n + 1) ≫
          (h.hom (n + 1) n ≫
            ((P ⊗ Deformation.Obstruction.kernelComplex f hf).shiftFunctorObjXIso
              2 n ((n + 1) + 1) (by omega)).hom) +
      curvatureHomotopyComponent h n ≫
        (P ⊗ Deformation.Obstruction.kernelComplex f hf).d
          (n + 1) ((n + 1) + 1) := by
  have hh := h.comm n
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel n (n + 1) by simp),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)] at hh
  have hsrc : n - 1 + 2 = n + 1 := by omega
  have hdst : n + 2 = (n + 1) + 1 := by omega
  have hidx : n + 1 - 1 = n := by omega
  have hcoeff : (2 : ℤ).negOnePow = 1 := by norm_num [Int.negOnePow]
  -- The shift is by two, so its differential has no sign. The component isomorphisms
  -- in `curvatureHomotopyComponent` identify the two shifted homotopy components.
  simpa [curvatureHomotopyComponent, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq, HomologicalComplex.XIsoOfEq_rfl,
    CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_d',
    HomologicalComplex.d_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    hsrc, hdst, hidx, hcoeff, add_sub_cancel_right, Category.assoc] using congrArg
      (fun g => g ≫ (CochainComplex.shiftFunctorObjXIso
        (P ⊗ Deformation.Obstruction.kernelComplex f hf)
        2 n ((n + 1) + 1) (by omega)).hom) hh

private lemma curvatureCorrection_homotopy_equation
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) (x : L.X n) :
    L.d (n + 1) ((n + 1) + 1) ((curvatureCorrection h n).hom x) +
      (curvatureCorrection h (n + 1)).hom (L.d n (n + 1) x) =
        L.d (n + 1) ((n + 1) + 1) (L.d n (n + 1) x) := by
  let : Module.Free R' (L.X n) := L.free n
  let : Module.Free R' (L.X (n + 1)) := L.free (n + 1)
  rw [congrArg ModuleCat.Hom.hom (curvatureCorrection_eq_expected h n),
    congrArg ModuleCat.Hom.hom (curvatureCorrection_eq_expected h (n + 1))]
  show L.d (n + 1) ((n + 1) + 1)
      (c.kernelEmbedding (n + 1)
        ((curvatureHomotopyComponent h n).hom (L.reduction n x))) +
      c.kernelEmbedding ((n + 1) + 1)
        ((curvatureHomotopyComponent h (n + 1)).hom
          (L.reduction (n + 1) (L.d n (n + 1) x))) =
    L.d (n + 1) ((n + 1) + 1) (L.d n (n + 1) x)
  rw [← kernelEmbedding_d c (n + 1)
    ((curvatureHomotopyComponent h n).hom (L.reduction n x)), L.reduction_d]
  have hsq := c.hom_eq_square n x
  -- The two index expressions are equal but Lean does not reduce integer addition
  -- notation definitionally at this dependent component.
  let Q := P ⊗ Deformation.Obstruction.kernelComplex f hf
  have castEmbedding {i j : ℤ} (hij : i = j) (z : Q.X i) :
      c.kernelEmbedding j ((Q.XIsoOfEq hij).hom z) =
        (Eq.ndrec (motive := fun k => (L.X k : Type u)) (c.kernelEmbedding i z) hij) := by
    cases hij
    rfl
  have castDifferential {i j : ℤ} (hij : i = j) (y : L.X (n + 1)) :
      Eq.ndrec (motive := fun k => (L.X k : Type u))
          (L.d (n + 1) i y) hij = L.d (n + 1) j y := by
    cases hij
    rfl
  have hij : n + 2 = (n + 1) + 1 := by omega
  have hsq' : c.kernelEmbedding ((n + 1) + 1)
        ((Q.XIsoOfEq hij).hom (c.hom.f n (L.reduction n x))) =
      L.d (n + 1) ((n + 1) + 1) (L.d n (n + 1) x) := by
    have hsqcast := congrArg
      (fun y : L.X (n + 2) =>
        Eq.ndrec (motive := fun k => (L.X k : Type u)) y hij) hsq
    rw [← castEmbedding hij] at hsqcast
    rw [castDifferential hij] at hsqcast
    exact hsqcast
  have hcomm := congrArg (fun g => g.hom (L.reduction n x))
    (curvatureHomotopy_comm h n)
  have hshift :
      (Q.shiftFunctorObjXIso 2 n ((n + 1) + 1) (by omega)).hom =
        (Q.XIsoOfEq hij).hom := by
    ext z
    simp [CochainComplex.shiftFunctorObjXIso]
  have hcomponent : curvatureHomotopyComponent h (n + 1) =
      h.hom (n + 1) n ≫ (Q.shiftFunctorObjXIso 2 n ((n + 1) + 1) (by omega)).hom := by
    simpa [curvatureHomotopyComponent] using
      homotopy_shiftComponent_eq h (n + 1) ((n + 1) - 1) n ((n + 1) + 1)
        (by omega) (by omega) (by omega)
  have hcommEval :
      (Q.shiftFunctorObjXIso 2 n ((n + 1) + 1) (by omega)).hom
          (c.hom.f n (L.reduction n x)) =
        (Q.d (n + 1) ((n + 1) + 1)).hom
            ((curvatureHomotopyComponent h n).hom (L.reduction n x)) +
          ((h.hom (n + 1) n ≫
            (Q.shiftFunctorObjXIso 2 n ((n + 1) + 1) (by omega)).hom).hom)
            (P.d n (n + 1) (L.reduction n x)) := by
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_add, LinearMap.add_apply, add_comm] using hcomm
  rw [← hsq', ← (c.kernelEmbedding ((n + 1) + 1)).map_add, hcomponent]
  have hsum := congrArg (c.kernelEmbedding ((n + 1) + 1)) hcommEval.symm
  rwa [hshift] at hsum

private noncomputable def curvatureCorrectedDifferential
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) : L.X n ⟶ L.X (n + 1) :=
  L.d n (n + 1) - curvatureCorrection h n

private lemma curvatureCorrected_d_comp
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (n : ℤ) :
    curvatureCorrectedDifferential h n ≫ curvatureCorrectedDifferential h (n + 1) = 0 := by
  ext x
  show (L.d (n + 1) ((n + 1) + 1) - curvatureCorrection h (n + 1)).hom
      ((L.d n (n + 1) - curvatureCorrection h n).hom x) = 0
  simp only [ModuleCat.hom_sub, LinearMap.sub_apply, map_sub]
  rw [curvatureCorrection_sq h n x, ← curvatureCorrection_homotopy_equation h n x]
  abel

private noncomputable def curvatureCorrectedComplex
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) : CochainComplex (ModuleCat.{u} R') ℤ :=
  CochainComplex.of L.X (curvatureCorrectedDifferential h)
    (curvatureCorrected_d_comp h)

private noncomputable def reductionRestrictionMap
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Deformation.Obstruction.FreeDifferentialLift f P) (n : ℤ) :
    L.X n ⟶ (ModuleCat.restrictScalars f).obj (P.X n) :=
  (ModuleCat.semilinearMapAddEquiv f (L.X n) (P.X n)) (L.reduction n)

private noncomputable def reductionExtensionMap
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Deformation.Obstruction.FreeDifferentialLift f P) (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} f).obj (L.X n) ⟶ P.X n :=
  ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv _ _).symm
    (reductionRestrictionMap L n)

private lemma reductionExtensionMap_unit
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Deformation.Obstruction.FreeDifferentialLift f P)
    (n : ℤ) (x : L.X n) :
    (reductionExtensionMap L n).hom ((1 : R) ⊗ₜ[R'] x) = L.reduction n x := by
  have h1 := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars_hom_apply f
    (reductionExtensionMap L n) x
  have h2 : ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars f
      (reductionExtensionMap L n) = reductionRestrictionMap L n :=
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv (L.X n) (P.X n)).apply_symm_apply
      (reductionRestrictionMap L n)
  rw [h2] at h1
  exact h1.symm

private noncomputable def reductionExtensionIso
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (L : Deformation.Obstruction.FreeDifferentialLift f P)
    (n : ℤ) : (ModuleCat.extendScalars.{u, u, u} f).obj (L.X n) ≅ P.X n := by
  letI : Algebra R' R := f.toAlgebra
  let ψ := reductionExtensionMap L n
  have hsurj : Function.Surjective ψ.hom := by
    intro y
    obtain ⟨x, hx⟩ := L.reduction_surjective n y
    refine ⟨(1 : R) ⊗ₜ[R'] x, ?_⟩
    rw [reductionExtensionMap_unit]
    exact hx
  have hinj : Function.Injective ψ.hom := by
    change Function.Injective (fun z : TensorProduct R' R (L.X n) => ψ.hom z)
    intro z w hzw
    let : Algebra R' R := f.toAlgebra
    obtain ⟨x, hx⟩ : ∃ x : L.X n,
        (TensorProduct.mk R' R (L.X n) (1 : R)) x = z - w :=
      TensorProduct.mk_surjective R' (L.X n) R hf (z - w)
    have hred : L.reduction n x = 0 := by
      change ψ.hom z = ψ.hom w at hzw
      have h : ψ.hom ((TensorProduct.mk R' R (L.X n) (1 : R)) x) = 0 := by
        calc
          _ = ψ.hom (z - w) := congrArg ψ.hom hx
          _ = ψ.hom z - ψ.hom w := map_sub _ _ _
          _ = 0 := by rw [hzw, sub_self]
      change (reductionExtensionMap L n).hom ((1 : R) ⊗ₜ[R'] x) = 0 at h
      rw [reductionExtensionMap_unit] at h
      exact h
    have hmk : (1 : R) ⊗ₜ[R'] x = 0 := by
      have hxker : x ∈ LinearMap.ker (TensorProduct.mk R' R (L.X n) (1 : R)) := by
        rw [MilnorPatching.ker_tensorProductMk_of_surjective f hf,
          ← L.reduction_ker n]
        exact LinearMap.mem_ker.mpr hred
      exact LinearMap.mem_ker.mp hxker
    have hz : z - w = 0 := by
      change (TensorProduct.mk R' R (L.X n) (1 : R)) x = 0 at hmk
      calc
        z - w = (TensorProduct.mk R' R (L.X n) (1 : R)) x := hx.symm
        _ = 0 := hmk
    exact sub_eq_zero.mp hz
  haveI : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).2 ⟨hinj, hsurj⟩
  exact asIso ψ

private noncomputable def curvatureCorrectedReductionIso
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (curvatureCorrectedComplex h) ≅ P := by
  let E := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)
  let C' := curvatureCorrectedComplex h
  let ε : ∀ n, (E.obj C').X n ≅ P.X n := fun n => reductionExtensionIso hf L n
  refine HomologicalComplex.Hom.isoOfComponents ε ?_
  intro i j hij
  rw [ComplexShape.up_Rel] at hij
  subst j
  have hc :
      (ModuleCat.extendScalars.{u, u, u} f).map (curvatureCorrection h i) ≫
          (reductionExtensionIso hf L (i + 1)).hom = 0 := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (reductionExtensionMap L (i + 1)).hom
        ((1 : R) ⊗ₜ[R'] (curvatureCorrection h i).hom x) = 0
    rw [reductionExtensionMap_unit]
    exact curvatureCorrection_reduction h i x
  have hd :
      (ModuleCat.extendScalars.{u, u, u} f).map (L.d i (i + 1)) ≫
          (reductionExtensionIso hf L (i + 1)).hom =
        (reductionExtensionIso hf L i).hom ≫ P.d i (i + 1) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (reductionExtensionMap L (i + 1)).hom
        ((1 : R) ⊗ₜ[R'] (L.d i (i + 1)).hom x) =
      (P.d i (i + 1)).hom
        ((reductionExtensionMap L i).hom ((1 : R) ⊗ₜ[R'] x))
    rw [reductionExtensionMap_unit, reductionExtensionMap_unit]
    exact L.reduction_d i (i + 1) x
  dsimp [E, C', curvatureCorrectedComplex] at hc hd ⊢
  rw [CochainComplex.of_d]
  change
    (reductionExtensionIso hf L i).hom ≫ P.d i (i + 1) =
    (ModuleCat.extendScalars.{u, u, u} f).map
        (curvatureCorrectedDifferential h i) ≫
          (reductionExtensionIso hf L (i + 1)).hom
  calc
    _ = (ModuleCat.extendScalars.{u, u, u} f).map (L.d i (i + 1)) ≫
          (reductionExtensionIso hf L (i + 1)).hom := hd.symm
    _ = (ModuleCat.extendScalars.{u, u, u} f).map
          (curvatureCorrectedDifferential h i) ≫
          (reductionExtensionIso hf L (i + 1)).hom := by
      rw [curvatureCorrectedDifferential, Functor.map_sub, Preadditive.sub_comp, hc]
      simp

private lemma curvatureCorrectedComplex_isStrictlyLE
    {R' R : Type u} [CommRing R'] [CommRing R]
    {f : R' →+* R} {hf : Function.Surjective f}
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {L : Deformation.Obstruction.FreeDifferentialLift f P}
    {c : Deformation.Obstruction.LiftedDifferentialCurvature f hf P L}
    (h : Homotopy c.hom 0) (b : ℤ) (hb : P.IsStrictlyLE b) :
    (curvatureCorrectedComplex h).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  let : Subsingleton (P.X n) :=
    ModuleCat.isZero_iff_subsingleton.mp (P.isZero_of_isStrictlyLE b n hn)
  have htop : (⊤ : Submodule R' (L.X n)) ≤
      RingHom.ker f • (⊤ : Submodule R' (L.X n)) := by
    intro x _
    rw [← L.reduction_ker n]
    exact LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
  have hnil : IsNilpotent (RingHom.ker f) := ⟨2, by simpa [pow_two] using hzero⟩
  have hz := Submodule.eq_bot_of_le_smul_of_isNilpotent (RingHom.ker f)
    (⊤ : Submodule R' (L.X n)) hnil htop
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun x y => sub_eq_zero.mp ((Submodule.eq_bot_iff _).1 hz _ trivial)⟩

/-- A bounded-above derived complex over `R` lifts across a square-zero surjection
`R' → R` exactly when its canonical obstruction morphism is zero. -/
@[stacks 0DYR "vanishing_criterion"]
theorem canonicalObstructionMap_eq_zero_iff_exists_lift
    {R' R : Type u} [CommRing R'] [CommRing R]
    (f : R' →+* R) (hf : Function.Surjective f)
    (hzero : (RingHom.ker f) ^ 2 = ⊥)
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus K) :
      (Deformation.Obstruction.canonicalObstructionMap f hf hzero K hK).val = 0 ↔
      ∃ K' : DerivedCategory (ModuleCat.{u} R'),
        Nonempty ((derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K' ≅ K) := by
  constructor
  · intro hω
    obtain ⟨P, b, hb, hfree, e, L, c, ⟨h⟩⟩ :=
      exists_curvature_homotopy_of_obstruction_eq_zero f hf hzero K hK hω
    let C' := curvatureCorrectedComplex h
    let D := derivedExtensionScalarsGeneral.{u, u, u} f
    have : C'.IsStrictlyLE b := curvatureCorrectedComplex_isStrictlyLE hzero h b hb
    have : ∀ n, Projective (C'.X n) := projective_X_of_free (C := C') L.free
    have : IsIso (D.comparison.app C') := D.comparison_isIso_of_projective C' b
    exact ⟨DerivedCategory.Q.obj C', ⟨asIso (D.comparison.app C') ≪≫
      DerivedCategory.Q.mapIso (curvatureCorrectedReductionIso h) ≪≫ e⟩⟩
  · rintro ⟨K', ⟨α⟩⟩
    obtain ⟨N, hN⟩ := (DerivedCategory.minus_iff K).1 hK
    let b := N - 1
    have : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun i hi =>
      hN i (by dsimp [b] at hi ⊢; omega)
    obtain ⟨P, hPb, hPfree, ⟨eK⟩⟩ := exists_boundedAbove_free_representative K b
    have hPproj (i : ℤ) : Module.Projective R (P.X i) := by
      have := hPfree i
      exact Module.Projective.of_free
    let D := derivedExtensionScalarsGeneral.{u, u, u} f
    have : K'.IsLE b :=
      isLE_of_nilpotent_reduction f hf hzero D K' b P hPb hPproj ⟨eK ≪≫ α.symm⟩
    obtain ⟨Q, hQb, hQfree, ⟨eQ⟩⟩ := exists_boundedAbove_free_representative K' b
    let F := ModuleCat.extendScalars.{u, u, u} f
    let P' : CochainComplex (ModuleCat.{u} R) ℤ :=
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q
    have hP'b : P'.IsStrictlyLE b := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact F.map_isZero (Q.isZero_of_isStrictlyLE b i hi)
    have hP'free (i : ℤ) : Module.Free R (P'.X i) := by
      let : Algebra R' R := f.toAlgebra
      have := hQfree i
      have bP : Module.Basis (Module.Free.ChooseBasisIndex R' (Q.X i)) R
          ((ModuleCat.extendScalars.{u, u, u} f).obj (Q.X i) : Type u) :=
        (Module.Free.chooseBasis R' (Q.X i)).baseChange R
      exact Module.Free.of_basis bP
    have : ∀ i, Projective (Q.X i) := projective_X_of_free hQfree
    have : IsIso (D.comparison.app Q) := D.comparison_isIso_of_projective Q b
    have e : DerivedCategory.Q.obj P' ≅ K :=
      (asIso (D.comparison.app Q)).symm ≪≫ D.functor.mapIso eQ ≪≫ α
    let L := canonicalFreeDifferentialLift f hf Q hQfree
    let ω := Deformation.Obstruction.canonicalObstructionMap f hf hzero K hK
    obtain ⟨c⟩ := ω.property.exists_curvature P' b hP'b hP'free L
    have hdd : ∀ n x, L.d (n + 1) (n + 2) (L.d n (n + 1) x) = 0 := by
      intro n x
      dsimp [L, canonicalFreeDifferentialLift] at x ⊢
      show (Q.d (n + 1) (n + 2)).hom ((Q.d n (n + 1)).hom x) = 0
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_d]
      rfl
    exact (ω.property.eq_curvature P' b hP'b hP'free e L c).trans
      (curvature_toDerived_eq_zero_of_zero_square L e c hdd)

end Deformation.Obstruction

end

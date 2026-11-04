module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.TwoTermComplex.IdealPower
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Restricted.RigSmooth
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.Homology
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion
public import StacksFrontier.RingTheory.Restricted.RigSmoothCriteria.Conditions

/-!
# Criteria for rig-smoothness: the three equivalences

Rig-smoothness is equivalent to the cohomological condition, to the factorization condition and
to the existence of a Jacobian cover (Stacks 0GAJ); on one Jacobian chart `H⁻¹(NL^∧_{B/A})` is
power torsion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits
open Rig.AdicFiniteTypeAlgebra
open Rig.CompletedPolynomialPresentation
open Rig.CompletedNaiveCotangentComplex

universe u v

namespace Rig
open Stacks.Smooth.JacobianCriterion

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CompletedPolynomialPresentation.extension
  Algebra.Extension.ofSurjective CompletedNaiveCotangentComplex.cochainComplex

private def linearEquivOfModuleCatIso {R : Type u} [CommRing R]
    {M N : ModuleCat.{v} R} (e : M ≅ N) : M ≃ₗ[R] N where
  toFun := ModuleCat.homEquiv e.hom
  invFun := ModuleCat.homEquiv e.inv
  left_inv := by
    intro x
    change (e.hom ≫ e.inv) x = x
    simp
  right_inv := by
    intro x
    change (e.inv ≫ e.hom) x = x
    simp
  map_add' := (ModuleCat.homEquiv e.hom).map_add
  map_smul' := (ModuleCat.homEquiv e.hom).map_smul

private def extOneAnnihilatorIdeal {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{v} R)) : Ideal R where
  carrier := {r | ∀ (N : ModuleCat.{v} R), ∀ x : DerivedCategory.Ext K
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) 1, r • x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy N z
    rw [add_smul, hx N z, hy N z, zero_add]
  smul_mem' := by
    intro x y hy N z
    change (x * y) • z = 0
    rw [mul_smul, hy N z, smul_zero]

/-- An ideal of `B` contains `algebraMap a` for all `a ∈ I ^ c` iff it contains `(I B) ^ c`. -/
private lemma forall_mem_pow_algebraMap_iff
    {A : Type u} [CommRing A] {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (c : ℕ) (S : Ideal B.carrier) :
    (∀ a : A, a ∈ I ^ c → algebraMap A B.carrier a ∈ S) ↔ B.adicIdeal ^ c ≤ S := by
  rw [show B.adicIdeal = I.map (algebraMap A B.carrier) by rfl, ← Ideal.map_pow,
    Ideal.map_le_iff_le_comap]
  rfl

/-- Powers of the ideal of definition of `B` annihilate `Ext¹(K, -)` iff the corresponding powers
of the extended ideal lie in `extOneAnnihilatorIdeal K`. -/
private lemma exists_forall_ext_smul_eq_zero_iff
    {A : Type u} [CommRing A] {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (K : DerivedCategory (ModuleCat.{max u v} B.carrier)) :
    (∃ c : ℕ, ∀ (N : ModuleCat.{max u v} B.carrier)
      (x : DerivedCategory.Ext K ((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      ∀ a : A, a ∈ I ^ c → (algebraMap A B.carrier a) • x = 0) ↔
    ∃ c : ℕ, B.adicIdeal ^ c ≤ extOneAnnihilatorIdeal K :=
  exists_congr fun c => Iff.trans
    ⟨fun h a ha N x => h N x a ha, fun h N x a ha => h a ha N x⟩
    (forall_mem_pow_algebraMap_iff B c (extOneAnnihilatorIdeal K))

private lemma cotangentFactorizationIdeal_lifted
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    cotangentFactorizationIdeal (completedNaiveCotangentComplex B P).differential =
      cotangentFactorizationIdeal (completedNaiveCotangentComplex B P).liftedDifferential := by
  let K := completedNaiveCotangentComplex B P
  let eD := ULift.moduleEquiv (R := B.carrier)
    (M := P.extension.Cotangent)
  let eE := ULift.moduleEquiv (R := B.carrier)
    (M := Fin P.variableCount → B.carrier)
  ext a
  constructor
  · rintro ⟨h, hh⟩
    let hLift := eD.symm.toLinearMap.comp (h.comp eE.toLinearMap)
    refine ⟨hLift, ?_⟩
    ext x
    cases x with
    | up x =>
      show h (K.differential x) = _
      have hp := congrArg (fun f : P.extension.Cotangent →ₗ[B.carrier]
        P.extension.Cotangent => f x) hh
      exact hp
  · rintro ⟨h, hh⟩
    let hBase := eD.toLinearMap.comp (h.comp eE.symm.toLinearMap)
    refine ⟨hBase, ?_⟩
    ext x
    show ULift.down (h (ULift.up (K.differential x))) = a • x
    have hp := congrArg (fun f : LiftedCotangent →ₗ[B.carrier] LiftedCotangent =>
      f (ULift.up x)) hh
    simpa [LinearMap.comp_apply, K.liftedDifferential_up] using congrArg ULift.down hp

private lemma completedNaiveCotangent_factorizationOnComplex_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (J : Ideal B.carrier) :
    (∀ a : B.carrier, a ∈ J →
      ∃ h : (completedNaiveCotangentComplex B P).cochainComplex.X 0 ⟶
        (completedNaiveCotangentComplex B P).cochainComplex.X (-1),
        (completedNaiveCotangentComplex B P).cochainComplex.d (-1) 0 ≫ h =
          a • 𝟙 _) ↔
      J ≤ cotangentFactorizationIdeal
        (completedNaiveCotangentComplex B P).liftedDifferential := by
  let K := completedNaiveCotangentComplex B P
  let L := K.cochainComplex
  constructor
  · intro h a ha
    obtain ⟨g, hg⟩ := h a ha
    let hlin := ModuleCat.homEquiv
      (K.degreeZeroIso.inv ≫ g ≫ K.degreeNegOneIso.hom)
    refine ⟨hlin, ?_⟩
    have hconj : K.degreeNegOneIso.inv ≫ (L.d (-1) 0 ≫ g) ≫
        K.degreeNegOneIso.hom =
        ModuleCat.ofHom (hlin.comp K.liftedDifferential) := by
      rw [K.cochainComplex_d]
      simp [hlin, Category.assoc, ModuleCat.ofHom_comp, ModuleCat.homEquiv]
    have hscalar : K.degreeNegOneIso.inv ≫ (a • 𝟙 (L.X (-1))) ≫
        K.degreeNegOneIso.hom = a • 𝟙 (ModuleCat.of B.carrier LiftedCotangent) := by
      calc
        K.degreeNegOneIso.inv ≫ (a • 𝟙 (L.X (-1))) ≫ K.degreeNegOneIso.hom =
            a • (K.degreeNegOneIso.inv ≫ 𝟙 (L.X (-1)) ≫ K.degreeNegOneIso.hom) := by
          simp [Linear.smul_comp, Linear.comp_smul]
        _ = a • 𝟙 (ModuleCat.of B.carrier LiftedCotangent) := by
          congr 1
          show K.degreeNegOneIso.inv ≫ K.degreeNegOneIso.hom = _
          rw [Iso.inv_hom_id]
    have heq := congrArg (fun f => K.degreeNegOneIso.inv ≫ f ≫ K.degreeNegOneIso.hom) hg
    rw [hconj, hscalar] at heq
    have heqLin := congrArg (fun f : ModuleCat.of B.carrier LiftedCotangent ⟶
      ModuleCat.of B.carrier LiftedCotangent => f.hom) heq
    simpa [ModuleCat.ofHom_comp] using heqLin
  · intro h a ha
    obtain ⟨g, hg⟩ := h ha
    let g' := K.degreeZeroIso.hom ≫ ModuleCat.ofHom g ≫ K.degreeNegOneIso.inv
    refine ⟨g', ?_⟩
    calc
      L.d (-1) 0 ≫ g' = K.degreeNegOneIso.hom ≫
          ModuleCat.ofHom (g.comp K.liftedDifferential) ≫ K.degreeNegOneIso.inv := by
        rw [K.cochainComplex_d]
        simp [g', Category.assoc, ModuleCat.ofHom_comp]
      _ = K.degreeNegOneIso.hom ≫ ModuleCat.ofHom (a • LinearMap.id) ≫
          K.degreeNegOneIso.inv := by rw [hg]
      _ = K.degreeNegOneIso.hom ≫ (a • 𝟙 (ModuleCat.of B.carrier LiftedCotangent)) ≫
          K.degreeNegOneIso.inv := by
        congr 1
      _ = a • 𝟙 (L.X (-1)) := by
        calc
          _ = a • (K.degreeNegOneIso.hom ≫ 𝟙 _ ≫ K.degreeNegOneIso.inv) := by
            simp [Linear.smul_comp, Linear.comp_smul]
          _ = _ := by
            congr 1
            show K.degreeNegOneIso.hom ≫ K.degreeNegOneIso.inv = _
            rw [Iso.hom_inv_id]

private lemma completedNaiveCotangent_degreeZero_free
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    Module.Free B.carrier
      ((completedNaiveCotangentComplex B P).cochainComplex.X 0) :=
  Module.Free.of_equiv
    (linearEquivOfModuleCatIso (completedNaiveCotangentComplex B P).degreeZeroIso).symm

private lemma jacobianChart_factorization
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (b : P.completedPolynomialRing)
    {m : ℕ} (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker)
    (hdet : P.toAlgHom
      (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j : P.completedPolynomialRing)) ∣
        P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    P.toAlgHom b ^ 2 ∈ cotangentFactorizationIdeal
      (completedNaiveCotangentComplex B P).differential := by
  let K := completedNaiveCotangentComplex B P
  let D := P.extension.Cotangent
  let E := Fin P.variableCount → B.carrier
  have hkerEq : P.ker = P.extension.ker := rfl
  let u : Fin m → D := fun j ↦ Algebra.Extension.Cotangent.mk (hkerEq ▸ f j)
  let M : Matrix (Fin m) (Fin m) B.carrier := fun i j ↦ K.differential (u j) (T i)
  have hM : M = fun i j ↦ P.toAlgHom (K.partialDeriv (T i) (f j : P.completedPolynomialRing)) := by
    ext i j
    show K.differential (Algebra.Extension.Cotangent.mk (hkerEq ▸ f j)) (T i) = _
    rw [K.differential_mk]
  have hdetM : M.det = P.toAlgHom (Matrix.det fun i j : Fin m ↦
      K.partialDeriv (T i) (f j : P.completedPolynomialRing)) := by
    rw [hM]
    exact (P.toAlgHom.map_det _).symm
  obtain ⟨q, hq⟩ := hdet
  have hqM : P.toAlgHom b = M.det * q := by
    simpa [hdetM] using hq
  let coord : E →ₗ[B.carrier] (Fin m → B.carrier) :=
    LinearMap.pi fun i ↦ LinearMap.proj (T i)
  let adj : (Fin m → B.carrier) →ₗ[B.carrier] (Fin m → B.carrier) :=
    LinearMap.pi fun j ↦ ∑ i, M.adjugate j i • LinearMap.proj i
  let comb : (Fin m → B.carrier) →ₗ[B.carrier] D :=
    ∑ j, (LinearMap.proj j).smulRight (u j)
  let h : E →ₗ[B.carrier] D := comb.comp (adj.comp coord)
  have hgen : ∀ j : Fin m, h (K.differential (u j)) = M.det • u j := by
    intro j
    have hcoord : coord (K.differential (u j)) = M.mulVec (Pi.single j (1 : B.carrier)) := by
      ext i
      show (K.differential (u j)) (T i) = _
      simp [Matrix.mulVec, M]
    have hadj : adj (M.mulVec (Pi.single j (1 : B.carrier))) = M.det • Pi.single j 1 := by
      have hcol : M.mulVec (Pi.single j (1 : B.carrier)) = M.col j := by
        ext i
        simp [Matrix.mulVec, Matrix.col_apply]
      rw [hcol]
      ext k
      have hentry := congrArg (fun N : Matrix (Fin m) (Fin m) B.carrier => N k j)
        (Matrix.adjugate_mul M)
      have hentry' : ∑ i, M.adjugate k i * M i j =
          M.det * (Pi.single j (1 : B.carrier) : Fin m → B.carrier) k := by
        simpa [Matrix.mul_apply, Matrix.one_apply, smul_eq_mul, Pi.single_apply] using hentry
      simp [adj, LinearMap.pi_apply, LinearMap.sum_apply,
        LinearMap.proj_apply, Matrix.col_apply, hentry']
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hcoord, hadj]
    simp [comb, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Pi.single_apply]
  have hspan : ∀ x : D, x ∈ Submodule.span B.carrier (Set.range u) →
      h (K.differential x) = M.det • x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hgen j
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp [map_add, ihx, ihy]
    | smul a x hx ih =>
      simp [map_smul, smul_smul, ih, mul_comm]
  have hbspan : ∀ x : D,
      P.toAlgHom b • x ∈ Submodule.span B.carrier (Set.range u) := by
    intro x
    obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective (P := P.extension) x
    let b' : P.extension.Ring := b
    have hzker : b' * z.val ∈ P.extension.ker := by
      show algebraMap P.extension.Ring B.carrier (b' * z.val) = 0
      rw [map_mul, z.property, mul_zero]
    have hzP : z.val ∈ P.ker := hkerEq.symm ▸ z.property
    obtain ⟨y, hy, w, hw, hsum⟩ := Submodule.mem_sup.mp (hrelations z.val hzP)
    have hyker : y ∈ P.extension.ker := by
      have hfker : Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) ≤
          P.extension.ker := Ideal.span_le.mpr (by
            rintro a ⟨j, rfl⟩
            exact (f j).property)
      exact hfker hy
    have hyspan := cotangent_mk_mem_span_of_mem_span P.extension f y hyker hy
    have hwzero : Algebra.Extension.Cotangent.mk (P := P.extension) ⟨w, by
        have hwsq : P.extension.ker ^ 2 ≤ P.extension.ker := Ideal.pow_le_self (by norm_num)
        exact hwsq hw⟩ = 0 :=
      (Algebra.Extension.Cotangent.mk_eq_zero_iff _).2 hw
    have hsumVal : b' * z.val = y + w := by
      exact hsum.symm
    have hsum' : (⟨b' * z.val, hzker⟩ : P.extension.ker) =
        ⟨y, hyker⟩ + ⟨w, by
          have hwsq : P.extension.ker ^ 2 ≤ P.extension.ker := Ideal.pow_le_self (by norm_num)
          exact hwsq hw⟩ := Subtype.ext hsumVal
    have hmk := congrArg (Algebra.Extension.Cotangent.mk (P := P.extension)) hsum'
    have hscalar : Algebra.Extension.Cotangent.mk (P := P.extension) ⟨b' * z.val, hzker⟩ =
        P.toAlgHom b • Algebra.Extension.Cotangent.mk (P := P.extension) z := by
      calc
        _ = b' • Algebra.Extension.Cotangent.mk (P := P.extension) z := by
          show Algebra.Extension.Cotangent.mk (P := P.extension) (b' • z) = _
          exact map_smul (Algebra.Extension.Cotangent.mk (P := P.extension)) b' z
        _ = _ := by
          rw [extension_cotangent_ring_smul_eq_algebraMap]
          congr 1
    rw [hscalar, map_add, hwzero] at hmk
    simp only [add_zero] at hmk
    exact hmk.symm ▸ hyspan
  let h' := (P.toAlgHom b * q) • h
  refine ⟨h', ?_⟩
  ext x
  have hb := hspan (P.toAlgHom b • x) (hbspan x)
  have hb' : P.toAlgHom b • h (K.differential x) =
      (M.det * P.toAlgHom b) • x := by
    simpa [map_smul, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hb
  show (P.toAlgHom b * q) • h (K.differential x) = (P.toAlgHom b ^ 2) • x
  calc
    _ = q • (P.toAlgHom b • h (K.differential x)) := by
      rw [smul_smul]
      congr 1
      ring
    _ = q • ((M.det * P.toAlgHom b) • x) := by rw [hb']
    _ = (P.toAlgHom b ^ 2) • x := by
      rw [smul_smul, hqM]
      congr 1
      ring

private lemma exists_finset_subfamily_radical_of_fg
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    {ι : Type*} (f : ι → R)
    (hle : I ≤ (Ideal.span (Set.range f)).radical) :
    ∃ t : Finset ι, I ≤ (Ideal.span (f '' (t : Set ι))).radical := by
  classical
  obtain ⟨n, g, hg⟩ := (Submodule.fg_iff_exists_fin_generating_family).mp hI
  have hgen (i : Fin n) : g i ∈ I := by
    rw [← hg]
    exact Submodule.subset_span ⟨i, rfl⟩
  let exponent : Fin n → ℕ := fun i => Classical.choose
    (Ideal.mem_radical_iff.mp (hle (hgen i)))
  have hpower (i : Fin n) : g i ^ exponent i ∈ Ideal.span (Set.range f) :=
    Classical.choose_spec (Ideal.mem_radical_iff.mp (hle (hgen i)))
  let support (i : Fin n) : Finset R :=
    Classical.choose (Submodule.mem_span_finite_of_mem_span (hpower i))
  have hsupport (i : Fin n) :
      (support i : Set R) ⊆ Set.range f ∧
        g i ^ exponent i ∈ Ideal.span (support i : Set R) :=
    Classical.choose_spec (Submodule.mem_span_finite_of_mem_span (hpower i))
  let label (i : Fin n) (y : support i) : ι :=
    Classical.choose (Set.mem_range.mp ((hsupport i).1 y.2))
  have hlabel (i : Fin n) (y : support i) : f (label i y) = y.1 :=
    Classical.choose_spec (Set.mem_range.mp ((hsupport i).1 y.2))
  let indices (i : Fin n) : Finset ι := (support i).attach.image (label i)
  let allIndices := Finset.univ.biUnion indices
  have hsupportImage (i : Fin n) :
      (support i : Set R) ⊆ f '' (indices i : Set ι) := by
    intro y hy
    let z : support i := ⟨y, hy⟩
    refine ⟨label i z, Finset.mem_image.mpr ⟨z, Finset.mem_attach _ _, rfl⟩, ?_⟩
    exact hlabel i z
  have hindices (i : Fin n) : (indices i : Set ι) ⊆ (allIndices : Set ι) := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩
  have himage (i : Fin n) : f '' (indices i : Set ι) ⊆ f '' (allIndices : Set ι) := by
    rintro y ⟨j, hj, rfl⟩
    exact ⟨j, hindices i hj, rfl⟩
  have hpowerAll (i : Fin n) :
      g i ^ exponent i ∈ Ideal.span (f '' (allIndices : Set ι)) :=
    Submodule.span_mono (hsupportImage i |>.trans (himage i))
      (hsupport i).2
  refine ⟨allIndices, ?_⟩
  rw [← hg]
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact Ideal.mem_radical_iff.mpr ⟨exponent i, hpowerAll i⟩

/-- Rig-smoothness is equivalent to the cohomological criterion for the completed naive
cotangent complex. -/
@[stacks 0GAJ "conditions (1) and (2)"]
public theorem isRigSmooth_iff_cotangentCohomologyCondition
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    Rig.IsRigSmooth B ↔ HasCotangentCohomologyCondition B P := by
  let K := DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex
  let Hneg := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) (-1)).obj K
  let Hzero := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} B.carrier) 0).obj K
  have hcriterion :=
    (TwoTermComplex.exists_power_ext_one_annihilated_iff_cohomology_conditions
      B.adicIdeal K (completedNaiveCotangent_homology_vanishes B P)).1
  let J := extOneAnnihilatorIdeal (R := B.carrier) K
  have hExt : _ ↔ ∃ c : ℕ, ∀ (N : ModuleCat.{max u v} B.carrier)
      (b : B.carrier), b ∈ B.adicIdeal ^ c →
      ∀ (x : DerivedCategory.Ext K ((DerivedCategory.singleFunctor
        (ModuleCat.{max u v} B.carrier) 0).obj N) 1), b • x = 0 :=
    (exists_forall_ext_smul_eq_zero_iff B K).trans
      (exists_congr fun c => ⟨fun h N b hb x => h hb N x, fun h b hb N x => h N b hb x⟩)
  rw [Rig.isRigSmooth_iff B P]
  show _ ↔ ∃ c : ℕ,
    (∀ (a : B.carrier), a ∈ B.adicIdeal ^ c → ∀ x : Hneg, a • x = 0) ∧
      Module.IsIProjective B.carrier (B.adicIdeal ^ c) Hzero
  exact hExt.trans hcriterion

/-- Rig-smoothness is equivalent to uniform factorization of powers of the ideal of
definition through the differential of a chosen completed naive cotangent complex. -/
@[stacks 0GAJ "conditions (1) and (3)"]
public theorem isRigSmooth_iff_cotangentFactorization
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    Rig.IsRigSmooth B ↔ HasCotangentFactorization B P := by
  let K := DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex
  let J := B.adicIdeal
  let E := extOneAnnihilatorIdeal (R := B.carrier) K
  let F := cotangentFactorizationIdeal (completedNaiveCotangentComplex B P).differential
  let Flift := cotangentFactorizationIdeal
    (completedNaiveCotangentComplex B P).liftedDifferential
  have hFLift : F = Flift := cotangentFactorizationIdeal_lifted B P
  have hExtA := exists_forall_ext_smul_eq_zero_iff B K
  have hFactorA : HasCotangentFactorization B P ↔ ∃ c : ℕ, J ^ c ≤ F :=
    exists_congr fun c => forall_mem_pow_algebraMap_iff B c F
  have hK' := completedNaiveCotangent_homology_vanishes B P
  have hbounds := completedNaiveCotangent_strictBounds B P
  have hfreeZero := completedNaiveCotangent_degreeZero_free B P
  have hequiv : Nonempty (DerivedCategory.Q.obj
      (completedNaiveCotangentComplex B P).cochainComplex ≅ K) :=
    ⟨Iso.refl K⟩
  have hPowerCriterion :
      (∃ c : ℕ, J ^ c ≤ E) ↔ (∃ c : ℕ, J ^ c ≤ Flift) := by
    constructor
    · rintro ⟨c, hc⟩
      let Q := J ^ c
      have hcrit :=
        TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization Q K hK'
      have hext : ∀ (N : ModuleCat.{max u v} B.carrier) (a : B.carrier),
          a ∈ Q → ∀ x : DerivedCategory.Ext K
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1,
            a • x = 0 := fun N a ha x => hc ha N x
      have hfactor := hcrit.2.1.mp (hcrit.1.mp hext)
        ((completedNaiveCotangentComplex B P).cochainComplex)
        hbounds.1 hbounds.2 (by
          let := hfreeZero
          infer_instance) hequiv
      exact ⟨c, (completedNaiveCotangent_factorizationOnComplex_iff B P Q).1 hfactor⟩
    · rintro ⟨c, hc⟩
      let Q := J ^ c
      have hcrit :=
        TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization Q K hK'
      have hfree : ∃ L : CochainComplex (ModuleCat.{max u v} B.carrier) ℤ,
          L.IsStrictlyGE (-1) ∧ L.IsStrictlyLE 0 ∧ Module.Free B.carrier (L.X 0) ∧
            Nonempty (DerivedCategory.Q.obj L ≅ K) ∧
            ∀ (a : B.carrier), a ∈ Q → ∃ h : L.X 0 ⟶ L.X (-1),
              L.d (-1) 0 ≫ h = a • 𝟙 (L.X (-1)) :=
        ⟨(completedNaiveCotangentComplex B P).cochainComplex, hbounds.1, hbounds.2,
          hfreeZero, hequiv, (completedNaiveCotangent_factorizationOnComplex_iff B P Q).2 hc⟩
      have hext := hcrit.1.mpr hfree
      exact ⟨c, fun a ha N x => hext N a ha x⟩
  rw [Rig.isRigSmooth_iff B P]
  exact hExtA.trans (hPowerCriterion.trans (hFLift ▸ hFactorA.symm))

/-- Rig-smoothness is equivalent to a finite Jacobian cover away from the ideal of
definition. -/
@[stacks 0GAJ "conditions (1) and (4)"]
public theorem isRigSmooth_iff_hasJacobianCover
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B) :
    Rig.IsRigSmooth B ↔ HasJacobianCover B P := by
  constructor
  · intro hrig
    classical
    have hfactor : HasCotangentFactorization B P :=
      (isRigSmooth_iff_cotangentFactorization B P).mp hrig
    let Q := {q : Ideal B.carrier // q.IsPrime ∧ ¬ B.adicIdeal ≤ q}
    choose localData localData_spec using fun q : Q =>
      have : q.1.IsPrime := q.2.1
      exists_jacobian_chart_away_prime B P hfactor q.1 q.2.2
    let fchart : Q → B.carrier := fun q => P.toAlgHom (localData q)
    have hrad : B.adicIdeal ≤ (Ideal.span (Set.range fchart)).radical := by
      rw [Ideal.radical_eq_sInf]
      apply le_sInf
      intro q hq
      let : q.IsPrime := hq.2
      by_contra hnot
      let q' : Q := ⟨q, ⟨inferInstance, hnot⟩⟩
      have hmem : fchart q' ∈ Ideal.span (Set.range fchart) :=
        Ideal.subset_span ⟨q', rfl⟩
      exact (localData_spec q').1 (hq.1 hmem)
    let : IsNoetherianRing B.carrier := Rig.isNoetherianRing B
    obtain ⟨t, ht⟩ := exists_finset_subfamily_radical_of_fg B.adicIdeal
      (Ideal.fg_of_isNoetherianRing _) fchart hrad
    let idx : Fin t.card → Q := fun i => (t.equivFin.symm i : Q)
    let b : Fin t.card → P.completedPolynomialRing := fun i => localData (idx i)
    have hsets : Set.range (fun i : Fin t.card => fchart (idx i)) =
        fchart '' (t : Set Q) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨idx i, (t.equivFin.symm i).property, rfl⟩
      · rintro ⟨q, hqt, rfl⟩
        refine ⟨t.equivFin ⟨q, hqt⟩, ?_⟩
        simp [idx]
    have hcover : B.adicIdeal ≤
        (Ideal.span (Set.range fun i : Fin t.card => P.toAlgHom (b i))).radical := by
      show B.adicIdeal ≤ (Ideal.span (Set.range fun i : Fin t.card => fchart (idx i))).radical
      rwa [hsets]
    exact ⟨t.card, b, hcover, fun i => (localData_spec (idx i)).2⟩
  · rintro ⟨s, b, hcover, hcharts⟩
    let F := cotangentFactorizationIdeal (completedNaiveCotangentComplex B P).differential
    have hchartFactor : ∀ l : Fin s, (P.toAlgHom (b l)) ^ 2 ∈ F := by
      intro l
      obtain ⟨m, T, f, hdet, hrelations⟩ := hcharts l
      exact jacobianChart_factorization B P (b l) T f hdet hrelations
    have hspan :
        Ideal.span (Set.range fun l : Fin s => P.toAlgHom (b l)) ≤ F.radical := by
      apply Ideal.span_le.mpr
      rintro x ⟨l, rfl⟩
      show P.toAlgHom (b l) ∈ F.radical
      rw [Ideal.mem_radical_iff]
      exact ⟨2, by simpa only [pow_two] using hchartFactor l⟩
    have hrad : B.adicIdeal ≤ F.radical :=
      hcover.trans (by simpa [Ideal.radical_idem] using Ideal.radical_mono hspan)
    obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
      (Ideal.fg_of_isNoetherianRing B.adicIdeal)
    refine (isRigSmooth_iff_cotangentFactorization B P).2 ⟨c, fun a ha => ?_⟩
    exact (forall_mem_pow_algebraMap_iff B c F).2 hc a ha

/-- **Stacks 0GAJ, inside the proof of (4) ⟹ (2).**  Let `b` carry a Jacobian chart: a
subset `T` of `m` of the variables and `m` elements `f₁, …, fₘ` of the presentation ideal `J`
whose Jacobian minor along `T` divides `b`, with `b J ⊆ (f₁, …, fₘ) + J²`.  Then
`H⁻¹(NL^∧_{B/A})` is `b`-power torsion; in fact `b²` already annihilates it. -/
@[stacks 0GAJ "the proof of (4) ⟹ (2): H⁻¹(NL^∧) is b_l-power torsion"]
public theorem isElementPowerTorsion_hneg_of_jacobianChart
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) (b : P.completedPolynomialRing)
    {m : ℕ} (T : Fin m ↪ Fin P.variableCount) (f : Fin m → P.ker)
    (hdet : P.toAlgHom
      (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (T i) (f j : P.completedPolynomialRing)) ∣
        P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    IsElementPowerTorsion B.carrier (completedNaiveCotangentComplex B P).Hneg
      (P.toAlgHom b) := by
  obtain ⟨h, hh⟩ := jacobianChart_factorization B P b T f hdet hrelations
  intro x
  refine ⟨2, Nat.succ_pos 1, ?_⟩
  have hx : (completedNaiveCotangentComplex B P).differential (x : P.extension.Cotangent) = 0 :=
    LinearMap.mem_ker.mp x.property
  have hp := congrArg
    (fun q : P.extension.Cotangent →ₗ[B.carrier] P.extension.Cotangent =>
      q (x : P.extension.Cotangent)) hh
  simp only [LinearMap.coe_comp, Function.comp_apply, hx, map_zero, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq] at hp
  exact Subtype.ext (by simpa using hp.symm)

end Rig

end

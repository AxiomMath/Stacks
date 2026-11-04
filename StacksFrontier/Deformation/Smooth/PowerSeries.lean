module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Completed.PowerSeries
public import StacksFrontier.Deformation.Formal.Groupoid.CofiberedCompletion
public import StacksFrontier.Deformation.RestrictedRepresentable
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace
public import StacksFrontier.RingTheory.Noetherian.Endomorphism

/-!
# Smooth morphisms between restricted representable categories

A map `f : R ⟶ S` of Noetherian complete local `Λ`-algebras with residue field `k` induces,
by precomposition, a morphism `restrictedRepresentableMap f` from the restricted functor
represented by `S` to the restricted functor represented by `R`. This file proves that this
morphism is smooth exactly when `f` exhibits `S` as a formal power series ring in finitely
many variables over `R`, that is, `IsPowerSeriesOver f`: there is an `R`-algebra equivalence
`S ≃ₐ[R] MvPowerSeries (Fin n) R`.

## Main results

* `Deformation.restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver`: the morphism of
  restricted representable categories induced by `R ⟶ S` is smooth if and only if `S` is a
  power series ring over `R`.

## References

* [Stacks Project, Tag 06HL](https://stacks.math.columbia.edu/tag/06HL)
-/

@[expose] public section

open CategoryTheory
open IsLocalRing
open scoped Topology

universe u v w

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

private theorem isSmooth_restrictedRepresentableMap_iff_lifts
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    IsSmooth (restrictedRepresentableMap f) ↔
      ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (q : B ⟶ A),
        Function.Surjective q.hom →
          ∀ (sA : S ⟶ artinianToComplete.obj A)
            (rB : R ⟶ artinianToComplete.obj B),
            (restrictedCoyonedaMap f).app A sA =
                (restrictedCoyoneda R).map q rB →
              ∃ sB : S ⟶ artinianToComplete.obj B,
                (restrictedCoyoneda S).map q sB = sA ∧
                  (restrictedCoyonedaMap f).app B sB = rB := by
  show IsSmooth (elementsBasedFunctor (restrictedCoyonedaMap f)) ↔ _
  exact isSmooth_elementsBasedFunctor_iff (restrictedCoyonedaMap f)

@[ega "0 19.3.4.1" "(ii)"]
private theorem exists_algHom_mvPowerSeries_of_nilpotent
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [TopologicalSpace R] [DiscreteTopology R]
    [TopologicalSpace B] [DiscreteTopology B]
    (n : ℕ) (x : Fin n → B) (hx : ∀ i, IsNilpotent (x i)) :
      ∃ φ : MvPowerSeries (Fin n) R →ₐ[R] B,
      (∀ i, φ (MvPowerSeries.X i) = x i) ∧
        @Continuous (MvPowerSeries (Fin n) R) B
          (MvPowerSeries.WithPiTopology.instTopologicalSpace R) ‹TopologicalSpace B› φ := by
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let _ : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  let _ : TopologicalSpace (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instTopologicalSpace R
  let _ : UniformSpace (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instUniformSpace
  let _ : DiscreteTopology (R × B) := inferInstance
  let _ : ContinuousSMul R B := ⟨continuous_of_discreteTopology⟩
  have : DiscreteUniformity B := by
    rw [discreteUniformity_iff_eq_principal_setRelId, uniformity_eq_comap_nhds_zero' B,
      nhds_discrete, Filter.comap_pure]
    congr 1
    ext x
    show x.2 + -x.1 = 0 ↔ x.1 = x.2
    constructor
    · intro hx
      have hx' : x.2 - x.1 = 0 := by simpa [sub_eq_add_neg] using hx
      exact (sub_eq_zero.mp hx').symm
    · intro hx
      rw [← sub_eq_add_neg]; exact sub_eq_zero.mpr hx.symm
  have : CompleteSpace B := inferInstance
  have heval : MvPowerSeries.HasEval x := by
    constructor
    · exact fun i => (hx i).isTopologicallyNilpotent
    · simp [Filter.cofinite_eq_bot]
  refine ⟨MvPowerSeries.aeval heval, ?_, ?_⟩
  · intro i
    simpa using MvPowerSeries.aeval_coe heval (MvPolynomial.X i)
  · exact MvPowerSeries.continuous_aeval (σ := Fin n) (R := R) heval

/-- Elements of the maximal ideal of an Artinian local ring are nilpotent. -/
private theorem isNilpotent_of_mem_maximalIdeal {B : Type*} [CommRing B] [IsLocalRing B]
    [IsArtinianRing B] {x : B} (hx : x ∈ maximalIdeal B) : IsNilpotent x := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal B).mp inferInstance
  have hm := Ideal.pow_mem_pow hx N
  rw [hN] at hm
  exact ⟨N, Ideal.mem_bot.mp hm⟩

private theorem exists_algHom_mvPowerSeries_of_artinianLocal
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [IsLocalRing B] [IsNoetherianRing B] [IsArtinianRing B]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace B] [DiscreteTopology B]
    (n : ℕ) (x : Fin n → B)
    (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal B) :
    ∃ φ : MvPowerSeries (Fin n) R →ₐ[R] B,
      (∀ i, φ (MvPowerSeries.X i) = x i) ∧
        @Continuous (MvPowerSeries (Fin n) R) B
          (MvPowerSeries.WithPiTopology.instTopologicalSpace R) ‹TopologicalSpace B› φ := by
  have hnil : ∀ i, IsNilpotent (x i) := fun i => isNilpotent_of_mem_maximalIdeal (hx i)
  exact exists_algHom_mvPowerSeries_of_nilpotent n x hnil

/-- The variables of a power series ring over a local ring lie in its maximal ideal. -/
private theorem X_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ} (i : Fin n) :
    (MvPowerSeries.X i : MvPowerSeries (Fin n) R) ∈ maximalIdeal (MvPowerSeries (Fin n) R) := by
  rw [Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem]
  simp

private theorem relativeCotangent_isTorsionByMaximalIdeal
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Module.IsTorsionBySet S (relativeCotangentSpaceOverBase S)
      (maximalIdeal S : Ideal S) := by
  have hset : Module.IsTorsionBySet S (relativeCotangentSpaceOverBase S)
      (maximalIdeal S : Set S) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x a ha
    show (a : S) * (x : S) ∈
      (RingHom.ker (algebraMap Λ k)).map (algebraMap Λ S) + maximalIdeal S ^ 2
    have hprod : (a : S) * (x : S) ∈ maximalIdeal S * maximalIdeal S :=
      Ideal.mul_mem_mul ha x.2
    have hprod' : (a : S) * (x : S) ∈ maximalIdeal S ^ 2 := by
      simpa [pow_two] using hprod
    exact Submodule.mem_sup.mpr ⟨0, Ideal.zero_mem _, a * (x : S),
      hprod', by simp⟩
  simpa using (Module.isTorsionBySet_iff_is_torsion_by_span
    (R := S) (M := relativeCotangentSpaceOverBase S) (s := (maximalIdeal S : Set S))).1 hset

@[instance_reducible]
private noncomputable def relativeCotangentModuleOverResidue
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Module (ResidueField S) (relativeCotangentSpaceOverBase S) := by
  let h := relativeCotangent_isTorsionByMaximalIdeal S
  let e : (S ⧸ maximalIdeal S) ≃+* ResidueField S :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  let : Module (S ⧸ maximalIdeal S) (relativeCotangentSpaceOverBase S) := h.module
  exact Module.compHom (relativeCotangentSpaceOverBase S) e.symm.toRingHom

@[instance_reducible]
private noncomputable def relativeCotangentModuleOverK
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Module k (relativeCotangentSpaceOverBase S) := by
  let : Algebra k (ResidueField S) := S.residueEquiv.symm.toAlgHom.toRingHom.toAlgebra
  let : Module (ResidueField S) (relativeCotangentSpaceOverBase S) :=
    relativeCotangentModuleOverResidue S
  exact Module.compHom (relativeCotangentSpaceOverBase S) (algebraMap k (ResidueField S))

private theorem relativeCotangent_finiteDimensional
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    letI : Module k (relativeCotangentSpaceOverBase S) := relativeCotangentModuleOverK S
    FiniteDimensional k (relativeCotangentSpaceOverBase S) := by
  let _ : Module k (relativeCotangentSpaceOverBase S) := relativeCotangentModuleOverK S
  let _ : Algebra k (ResidueField S) := S.residueEquiv.symm.toAlgHom.toRingHom.toAlgebra
  let _ : Module (ResidueField S) (relativeCotangentSpaceOverBase S) :=
    relativeCotangentModuleOverResidue S
  let _ : Module.Finite S (maximalIdeal S) :=
    Module.Finite.of_fg (maximalIdeal S).fg_of_isNoetherianRing
  have hfinite : Module.Finite S (relativeCotangentSpaceOverBase S) :=
    Module.Finite.of_surjective (Submodule.mkQ (relativeCotangentSubmodule S))
      (Submodule.mkQ_surjective _)
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfinite
  let W : Submodule k (relativeCotangentSpaceOverBase S) :=
    Submodule.span k (s : Set (relativeCotangentSpaceOverBase S))
  show Module.Finite k (relativeCotangentSpaceOverBase S)
  rw [Module.finite_def]
  refine ⟨s, ?_⟩
  apply top_unique
  intro x _
  have hx : x ∈ Submodule.span S (s : Set (relativeCotangentSpaceOverBase S)) := by
    rw [hs]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact W.zero_mem
  | add y z hy hz hy' hz' =>
      exact W.add_mem (hy' Submodule.mem_top) (hz' Submodule.mem_top)
  | smul a y hy hy' =>
      have hy'' := hy' Submodule.mem_top
      have ha : (S.residueEquiv (residue S a)) • y ∈
          W := W.smul_mem _ hy''
      have hsmul : a • y = (S.residueEquiv (residue S a)) • y := by
        let h := relativeCotangent_isTorsionByMaximalIdeal S
        have hscalar :
            algebraMap k (ResidueField S) (S.residueEquiv (residue S a)) = residue S a := by
          show S.residueEquiv.symm (S.residueEquiv (residue S a)) = _
          exact S.residueEquiv.symm_apply_apply _
        show a • y =
          (algebraMap k (ResidueField S) (S.residueEquiv (residue S a))) • y
        rw [hscalar]; exact (h.mk_smul a y).symm
      rw [hsmul]; exact ha

private noncomputable def relativeCotangentBasis
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    letI : Module k (relativeCotangentSpaceOverBase S) := relativeCotangentModuleOverK S
    Module.Basis (Fin (Module.finrank k (relativeCotangentSpaceOverBase S))) k
      (relativeCotangentSpaceOverBase S) := by
  let : Module k (relativeCotangentSpaceOverBase S) := relativeCotangentModuleOverK S
  let : FiniteDimensional k (relativeCotangentSpaceOverBase S) :=
    relativeCotangent_finiteDimensional S
  exact Module.finBasis k (relativeCotangentSpaceOverBase S)

private noncomputable def relativeCotangentRepresentatives
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (S : CompleteLocalAlgCat.{u, v, w} Λ k) :
    letI : Module k (relativeCotangentSpaceOverBase S) := relativeCotangentModuleOverK S
    Fin (Module.finrank k (relativeCotangentSpaceOverBase S)) → maximalIdeal S := by
  let : Module k (relativeCotangentSpaceOverBase S) := relativeCotangentModuleOverK S
  let b := relativeCotangentBasis S
  exact fun i => Classical.choose
    (Submodule.mkQ_surjective (relativeCotangentSubmodule S) (b i))
private noncomputable def rebaseBase
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    CompleteLocalAlgCat.{v, v, w} (↑R) k := by
  let : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  refine { carrier := R, completeLocal := R.completeLocal, residueEquiv := ?_ }
  exact AlgEquiv.ofRingEquiv (f := R.residueEquiv.toRingEquiv) (by intro x; rfl)

private noncomputable def rebaseTarget
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R S : CompleteLocalAlgCat.{u, v, w} Λ k) (f : R ⟶ S) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    letI : Algebra R S := f.hom.toRingHom.toAlgebra
    letI : Algebra S k :=
      (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
    letI : Algebra R (ResidueField S) :=
      (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
    letI : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (f.residue_comm r).symm)
    CompleteLocalAlgCat.{v, v, w} (↑R) k := by
  let : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  let : Algebra R S := f.hom.toRingHom.toAlgebra
  let : Algebra S k :=
    (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
  let : Algebra R (ResidueField S) :=
    (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
  let : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.residue_comm r).symm)
  let e : ResidueField S ≃ₐ[R] k :=
    AlgEquiv.ofRingEquiv (f := S.residueEquiv.toRingEquiv) (by
      intro r
      exact f.residue_comm r)
  exact { carrier := S, completeLocal := S.completeLocal, residueEquiv := e }

private noncomputable def rebasePowerSeriesResidueEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    ResidueField (MvPowerSeries (Fin n) R) ≃ₐ[R] k := by
  let : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  let : Algebra R (ResidueField R) := ResidueField.algebra R
  let eR : ResidueField R ≃ₐ[R] k := {
    toRingEquiv := R.residueEquiv.toRingEquiv
    commutes' := by intro r; rfl }
  let cc : MvPowerSeries (Fin n) R →ₐ[R] R := {
    toRingHom := MvPowerSeries.constantCoeff
    commutes' := by intro r; rfl }
  let : IsLocalHom cc.toRingHom := IsLocalHom.of_surjective cc.toRingHom (by
    intro r
    exact ⟨MvPowerSeries.C r, MvPowerSeries.constantCoeff_C r⟩)
  let : IsLocalHom cc := ⟨fun _ h => IsLocalHom.map_nonunit (f := cc.toRingHom) _ h⟩
  have hbij : Function.Bijective (ResidueField.mapAlgHom cc) := by
    constructor
    · exact RingHom.injective _
    · intro y
      obtain ⟨a, rfl⟩ := residue_surjective y
      refine ⟨residue _ (MvPowerSeries.C a), ?_⟩
      rw [ResidueField.mapAlgHom_residue]
      change residue R (MvPowerSeries.constantCoeff (MvPowerSeries.C a)) = _
      simp
  exact (AlgEquiv.ofBijective (ResidueField.mapAlgHom cc) hbij).trans eR

private theorem rebasePowerSeriesResidueEquiv_apply
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ)
    (x : MvPowerSeries (Fin n) R) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    (rebasePowerSeriesResidueEquiv R n) (residue _ x) =
      R.residueEquiv (residue R (MvPowerSeries.constantCoeff x)) := by
  rfl

private noncomputable def rebasePowerSeries
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    CompleteLocalAlgCat.{v, v, w} R k := by
  let : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  refine { carrier := (MvPowerSeries (Fin n) R), completeLocal := ?_, residueEquiv := ?_ }
  · exact {
      isNoetherian := inferInstance
      isLocal := inferInstance
      isComplete := MvPowerSeries.isAdicComplete_maximalIdeal n R inferInstance }
  · exact rebasePowerSeriesResidueEquiv R n

private noncomputable def rebasePowerSeriesMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) (n : ℕ)
    (g : MvPowerSeries (Fin n) R →+* S)
    (hgR : ∀ r, g (MvPowerSeries.C r) = f.hom r) (hg : IsLocalHom g) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    letI : Algebra R S := f.hom.toRingHom.toAlgebra
    letI : Algebra S k :=
      (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
    letI : Algebra R (ResidueField S) :=
      (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
    letI : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (f.residue_comm r).symm)
    rebasePowerSeries R n ⟶ rebaseTarget R S f := by
  let : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  let : Algebra R S := f.hom.toRingHom.toAlgebra
  let : Algebra S k :=
    (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
  let : Algebra R (ResidueField S) :=
    (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
  let : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.residue_comm r).symm)
  let gAlg : MvPowerSeries (Fin n) R →ₐ[R] S := {
    toRingHom := g
    commutes' := fun r => hgR r }
  refine ⟨gAlg, hg, ?_⟩
  intro x
  let x' : MvPowerSeries (Fin n) R := x
  let c := MvPowerSeries.constantCoeff x'
  have hx : x' - MvPowerSeries.C c ∈
      maximalIdeal (MvPowerSeries (Fin n) R) := by
    rw [Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem]; simp [c]
  have hres : residue S (g x') = residue S (g (MvPowerSeries.C c)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    have hdiff : g x' - g (MvPowerSeries.C c) ∈ maximalIdeal S := by
      rw [← map_sub]
      exact map_nonunit g _ hx
    exact (residue_eq_zero_iff _).2 hdiff
  calc
    S.residueEquiv (residue S (g x')) =
        S.residueEquiv (residue S (g (MvPowerSeries.C c))) := by rw [hres]
    _ = S.residueEquiv (residue S (f.hom c)) := by
      congr 1
      exact congrArg (residue S) (hgR c)
    _ = R.residueEquiv (residue R c) := f.residue_comm c
    _ = (rebasePowerSeries R n).residueEquiv
        (residue (MvPowerSeries (Fin n) R) x) := by
      change R.residueEquiv (residue R c) =
        (rebasePowerSeriesResidueEquiv R n)
          (residue (MvPowerSeries (Fin n) R) x)
      simpa [c, x'] using (rebasePowerSeriesResidueEquiv_apply R n x).symm

private noncomputable def relativeCotangentSpaceMapLinear
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A B : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ B) :
    letI : Module k (relativeCotangentSpaceOverBase A) :=
      relativeCotangentModuleOverK A
    letI : Module k (relativeCotangentSpaceOverBase B) :=
      relativeCotangentModuleOverK B
    relativeCotangentSpaceOverBase A →ₗ[k]
      relativeCotangentSpaceOverBase B := by
  let : Module k (relativeCotangentSpaceOverBase A) :=
    relativeCotangentModuleOverK A
  let : Module k (relativeCotangentSpaceOverBase B) :=
    relativeCotangentModuleOverK B
  let : Algebra k (ResidueField A) :=
    A.residueEquiv.symm.toAlgHom.toRingHom.toAlgebra
  let : Algebra k (ResidueField B) :=
    B.residueEquiv.symm.toAlgHom.toRingHom.toAlgebra
  refine {
    toFun := relativeCotangentSpaceMap f
    map_add' := map_add _
    map_smul' := ?_ }
  intro c x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (relativeCotangentSubmodule A) x
  obtain ⟨a, ha⟩ := residue_surjective (A.residueEquiv.symm c)
  have hcA : algebraMap k (ResidueField A) c = residue A a := by
    change A.residueEquiv.symm c = residue A a
    exact ha.symm
  have hcB : algebraMap k (ResidueField B) c = residue B (f.hom a) := by
    apply B.residueEquiv.injective
    calc
      B.residueEquiv (algebraMap k (ResidueField B) c) = c :=
        AlgEquiv.apply_symm_apply B.residueEquiv c
      _ = A.residueEquiv (residue A a) := by rw [ha]; simp
      _ = B.residueEquiv (residue B (f.hom a)) := (f.residue_comm a).symm
  let hA := relativeCotangent_isTorsionByMaximalIdeal A
  let hB := relativeCotangent_isTorsionByMaximalIdeal B
  let _ : Module (ResidueField A) (relativeCotangentSpaceOverBase A) :=
    relativeCotangentModuleOverResidue A
  let _ : Module (ResidueField B) (relativeCotangentSpaceOverBase B) :=
    relativeCotangentModuleOverResidue B
  have hleft (z : relativeCotangentSpaceOverBase A) : c • z = a • z := by
    change (algebraMap k (ResidueField A) c) • z = _
    rw [hcA]
    exact hA.mk_smul a z
  have hright (z : relativeCotangentSpaceOverBase B) : c • z = f.hom a • z := by
    change (algebraMap k (ResidueField B) c) • z = _
    rw [hcB]
    exact hB.mk_smul (f.hom a) z
  change relativeCotangentSpaceMap f (c • Submodule.Quotient.mk x) =
    c • relativeCotangentSpaceMap f (Submodule.Quotient.mk x)
  rw [hleft, hright]
  change Submodule.Quotient.mk (p := relativeCotangentSubmodule B)
      (maximalIdealMap f (a • x)) =
    Submodule.Quotient.mk (p := relativeCotangentSubmodule B)
      (f.hom a • maximalIdealMap f x)
  apply congrArg (Submodule.Quotient.mk (p := relativeCotangentSubmodule B))
  apply Subtype.ext
  exact map_mul f.hom a (x : A)

private theorem eval₂Hom_isLocalHom
    {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (n : ℕ) (φ : A →+* B) [IsLocalHom φ]
    (a : Fin n → B) (F : MvPowerSeries (Fin n) A →+* B)
    (hC : ∀ x, F (MvPowerSeries.C x) = φ x)
    (hX : ∀ i, F (MvPowerSeries.X i) = a i)
    (ha : ∀ i, a i ∈ maximalIdeal B) : IsLocalHom F := by
  let J : Ideal (MvPowerSeries (Fin n) A) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A))
  have hmap : Ideal.map F J ≤ maximalIdeal B := by
    show Ideal.map F
        (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A))) ≤ _
    rw [Ideal.map_span]
    apply Ideal.span_le.2
    rintro _ ⟨y, ⟨i, rfl⟩, rfl⟩
    rw [hX i]; exact ha i
  refine ⟨fun x hFxUnit => ?_⟩
  by_contra hxUnit
  let c := MvPowerSeries.constantCoeff x
  have hc : c ∈ nonunits A := by
    rw [mem_nonunits_iff]
    intro hcUnit; exact hxUnit ((MvPowerSeries.isUnit_iff_constantCoeff).2 hcUnit)
  have hφc : φ c ∈ maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hφunit; exact hc ((isUnit_map_iff φ c).mp hφunit)
  have hxJ : x - MvPowerSeries.C c ∈ J := by
    show x - MvPowerSeries.C c ∈
      Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A))
    apply (Stacks.MvPowerSeries.RegularParameters.mem_span_X_iff_constantCoeff_eq_zero n _).2
    simp [c]
  have hFJ : F (x - MvPowerSeries.C c) ∈ maximalIdeal B :=
    hmap (Ideal.mem_map_of_mem F hxJ)
  have hsum : φ c + F (x - MvPowerSeries.C c) ∈ maximalIdeal B :=
    (maximalIdeal B).add_mem hφc hFJ
  have hFx : F x ∈ maximalIdeal B := by
    have heq : F x = φ c + F (x - MvPowerSeries.C c) := by
      calc
        F x = F (MvPowerSeries.C c + (x - MvPowerSeries.C c)) :=
          congrArg F (by ring : MvPowerSeries.C c + (x - MvPowerSeries.C c) = x).symm
        _ = F (MvPowerSeries.C c) + F (x - MvPowerSeries.C c) := map_add _ _ _
        _ = φ c + F (x - MvPowerSeries.C c) := by rw [hC]
    rw [heq]
    exact hsum
  exact (IsLocalRing.mem_maximalIdeal _).mp hFx hFxUnit

private theorem smooth_lift_firstOrder
    {R S P : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (hs : IsSmooth (restrictedRepresentableMap f)) (r : R ⟶ P) (φ : P ⟶ S)
    (hφ : Function.Surjective φ.hom) (hfac : r ≫ φ = f) :
    ∃ sB : S ⟶ artinianToComplete.obj (AdicTruncation.obj P 1),
      sB ≫ artinianToComplete.map (AdicTruncation.map φ 1) =
          quotientProjection S 1 ∧
        f ≫ sB = r ≫ quotientProjection P 1 := by
  let B := AdicTruncation.obj P 1
  let A := AdicTruncation.obj S 1
  let q := AdicTruncation.map φ 1
  have hq : Function.Surjective q.hom := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hp⟩ := hφ s
    refine ⟨Ideal.Quotient.mk (AdicTruncation.ideal P 1) p, ?_⟩
    show Ideal.Quotient.mk (AdicTruncation.ideal S 1) (φ.hom p) = _
    rw [hp]
  let rB : R ⟶ artinianToComplete.obj B :=
    r ≫ quotientProjection P 1
  let sA : S ⟶ artinianToComplete.obj A :=
    quotientProjection S 1
  have hcomm : (restrictedCoyonedaMap f).app A sA =
      (restrictedCoyoneda R).map q rB := by
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro x
    have hval : φ.hom (r.hom x) = f.hom x := by
      simpa using congrArg (fun z : R ⟶ S => z.hom x) hfac
    show Ideal.Quotient.mk (AdicTruncation.ideal S 1) (f.hom x) =
      q.hom (Ideal.Quotient.mk (AdicTruncation.ideal P 1) (r.hom x))
    rw [← hval]
    rfl
  exact (isSmooth_restrictedRepresentableMap_iff_lifts f).mp hs q hq sA rB hcomm
private theorem smooth_lift_truncation
    {R S T : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (hs : IsSmooth (restrictedRepresentableMap f)) (r : R ⟶ T) (n : ℕ)
    (sA : S ⟶ artinianToComplete.obj (AdicTruncation.obj T (n + 1)))
    (hbase : f ≫ sA = r ≫
      quotientProjection T (n + 1)) :
    ∃ sB : S ⟶ artinianToComplete.obj (AdicTruncation.obj T (n + 2)),
      sB ≫ artinianToComplete.map (AdicTruncation.transition T (n + 1)) = sA ∧
        f ≫ sB = r ≫ quotientProjection T (n + 2) := by
  let B := AdicTruncation.obj T (n + 2)
  let A := AdicTruncation.obj T (n + 1)
  let q := AdicTruncation.transition T (n + 1)
  have hq : Function.Surjective q.hom := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨Ideal.Quotient.mk (AdicTruncation.ideal T (n + 2)) x, ?_⟩
    rfl
  let rB : R ⟶ artinianToComplete.obj B :=
    r ≫ quotientProjection T (n + 2)
  have hcomm : (restrictedCoyonedaMap f).app A sA =
      (restrictedCoyoneda R).map q rB := by
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro x
    have hfac : f ≫ sA =
        r ≫ quotientProjection T (n + 1) := hbase
    have hstep := congrArg (fun z : R ⟶ artinianToComplete.obj A => z.hom x)
      (by
        calc
          f ≫ sA = r ≫ quotientProjection T (n + 1) := hfac
          _ = r ≫ (quotientProjection T (n + 2) ≫
              artinianToComplete.map q) := by
            rw [← quotientProjection_transition T (n + 1)]
          _ = r ≫ quotientProjection T (n + 2) ≫
              artinianToComplete.map q := by rw [← Category.assoc]
          _ = rB ≫ artinianToComplete.map q := rfl)
    simpa [rB, restrictedCoyonedaMap] using hstep
  exact (isSmooth_restrictedRepresentableMap_iff_lifts f).mp hs q hq sA rB hcomm

private theorem smooth_lift_to_complete
    {R S T : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (hs : IsSmooth (restrictedRepresentableMap f)) (r : R ⟶ T)
    (s₀ : S ⟶ artinianToComplete.obj (AdicTruncation.obj T 1))
    (h₀ : f ≫ s₀ = r ≫ quotientProjection T 1) :
    ∃ s : S ⟶ T, f ≫ s = r ∧ s ≫ quotientProjection T 1 = s₀ := by
  classical
  let F (n : ℕ) := {s : S ⟶ artinianToComplete.obj
    (AdicTruncation.obj T (n + 1)) // f ≫ s = r ≫ quotientProjection T (n + 1)}
  have step (n : ℕ) (s : F n) := smooth_lift_truncation f hs r n s.1 s.2
  let seq : ∀ n, F n := fun n => Nat.rec (motive := F) ⟨s₀, h₀⟩
    (fun n s => ⟨(step n s).choose, (step n s).choose_spec.2⟩) n
  have hseq (n : ℕ) : (seq (n + 1)).1 ≫ artinianToComplete.map
      (AdicTruncation.transition T (n + 1)) = (seq n).1 :=
    (step n (seq n)).choose_spec.1
  let a : ℕ → ℕ := fun n => n + 2
  have ha : StrictMono a := fun i j h => Nat.add_lt_add_right h 2
  let maps (n : ℕ) : S →+* T ⧸ maximalIdeal T ^ a n := (seq n).1.hom.toRingHom
  have hc : ∀ {n}, (Ideal.Quotient.factorPow (maximalIdeal T)
      (ha.monotone (Nat.le_succ n))).comp (maps (n + 1)) = maps n := by
    intro n
    ext x
    exact congrArg (fun z : S ⟶ artinianToComplete.obj
      (AdicTruncation.obj T (n + 1)) => z.hom x) (hseq n)
  let s := IsAdicComplete.StrictMono.liftRingHom (maximalIdeal T) ha maps hc
  have hm (n : ℕ) (x : S) : Ideal.Quotient.mk (maximalIdeal T ^ a n) (s x) =
      (seq n).1.hom x := IsAdicComplete.StrictMono.mk_liftRingHom _ _ _ _ x
  have hbase : s.comp f.hom.toRingHom = r.hom.toRingHom := by
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext' (maximalIdeal T) ha
    intro n x
    rw [RingHom.coe_comp, Function.comp_apply, hm]
    exact congrArg (fun z : R ⟶ artinianToComplete.obj
      (AdicTruncation.obj T (n + 1)) => z.hom x) (seq n).2
  let sl : S →ₐ[Λ] T :=
    { toRingHom := s
      commutes' := fun c => by
        simpa using congrArg (fun z : R →+* T => z (algebraMap Λ R c)) hbase }
  have hsl : IsLocalHom sl.toRingHom := by
    refine ⟨fun x hx => ?_⟩
    apply s₀.isLocal.map_nonunit x
    have hunit := hx.map (quotientProjection T 1).hom.toRingHom
    change IsUnit (Ideal.Quotient.mk (maximalIdeal T ^ a 0) (s x)) at hunit
    rw [hm] at hunit
    exact hunit
  let sm : S ⟶ T :=
    { hom := sl
      isLocal := hsl
      residue_comm := fun x => by
        have hh := (quotientProjection T 1).residue_comm (s x)
        change (artinianToComplete.obj (AdicTruncation.obj T 1)).residueEquiv
          (residue _ (Ideal.Quotient.mk (maximalIdeal T ^ a 0) (s x))) = _ at hh
        rw [hm] at hh
        exact hh.symm.trans (s₀.residue_comm x) }
  exact ⟨sm, CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun x => congrArg (fun z : R →+* T => z x)
    hbase), CompleteLocalAlgCat.Hom.ext (AlgHom.ext (hm 0))⟩

private theorem exists_algHom_mvPowerSeries_of_mem_maximalIdeal
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [TopologicalSpace R] [DiscreteTopology R]
    [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B]
    (n : ℕ) (x : Fin n → B) (hx : ∀ i, x i ∈ maximalIdeal B) :
    ∃ φ : MvPowerSeries (Fin n) R →ₐ[R] B,
      (∀ i, φ (MvPowerSeries.X i) = x i) ∧
        @Continuous (MvPowerSeries (Fin n) R) B
          (MvPowerSeries.WithPiTopology.instTopologicalSpace R)
          ((maximalIdeal B).adicTopology) φ := by
  let _ : TopologicalSpace B := (maximalIdeal B).adicTopology
  let _ : IsTopologicalRing B := (maximalIdeal B).ringFilterBasis.isTopologicalRing
  let _ : IsAdic (maximalIdeal B) := rfl
  let _ : WithIdeal B := ⟨maximalIdeal B⟩
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  let _ : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  let _ : TopologicalSpace (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instTopologicalSpace R
  let _ : UniformSpace (MvPowerSeries (Fin n) R) :=
    MvPowerSeries.WithPiTopology.instUniformSpace
  let _ : ContinuousSMul R B := DiscreteTopology.instContinuousSMul R B
  have hcomplete := (IsAdic.isAdicComplete_iff (I := maximalIdeal B) rfl).mp inferInstance
  have : CompleteSpace B := hcomplete.1
  have : T2Space B := hcomplete.2
  have heval : MvPowerSeries.HasEval x := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (hx i)
    · simp [Filter.cofinite_eq_bot]
  refine ⟨MvPowerSeries.aeval heval, ?_, ?_⟩
  · intro i
    simpa using MvPowerSeries.aeval_coe heval (MvPolynomial.X i)
  · exact MvPowerSeries.continuous_aeval (σ := Fin n) (R := R) heval

private theorem exists_rebasePowerSeriesMap_of_cotangentBasis
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    letI : Algebra R S := f.hom.toRingHom.toAlgebra
    letI : Algebra S k :=
      (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
    letI : Algebra R (ResidueField S) :=
      (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
    letI : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (f.residue_comm r).symm)
    let B := rebaseTarget R S f
    letI : Module k (relativeCotangentSpaceOverBase B) :=
      relativeCotangentModuleOverK B
    letI : FiniteDimensional k (relativeCotangentSpaceOverBase B) :=
      relativeCotangent_finiteDimensional B
    ∃ g : rebasePowerSeries R
        (Module.finrank k (relativeCotangentSpaceOverBase B)) ⟶ B,
      (∀ i, g.hom (MvPowerSeries.X i) =
        ((relativeCotangentRepresentatives B i : B) : S)) ∧
      (∀ i, Submodule.Quotient.mk (relativeCotangentRepresentatives B i) =
        relativeCotangentBasis B i) := by
  let _ : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  let _ : Algebra R S := f.hom.toRingHom.toAlgebra
  let _ : Algebra S k :=
    (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
  let _ : Algebra R (ResidueField S) :=
    (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
  let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (f.residue_comm r).symm)
  let B := rebaseTarget R S f
  let _ : Algebra k (ResidueField B) :=
    B.residueEquiv.symm.toAlgHom.toRingHom.toAlgebra
  let _ : Module k (relativeCotangentSpaceOverBase B) :=
    relativeCotangentModuleOverK B
  let _ : FiniteDimensional k (relativeCotangentSpaceOverBase B) :=
    relativeCotangent_finiteDimensional B
  let n := Module.finrank k (relativeCotangentSpaceOverBase B)
  let b := relativeCotangentBasis B
  let x := relativeCotangentRepresentatives B
  have hxclass (i : Fin n) : Submodule.Quotient.mk (x i) = b i :=
    Classical.choose_spec (Submodule.mkQ_surjective
      (relativeCotangentSubmodule B) (b i))
  let _ : TopologicalSpace R := ⊥
  let _ : DiscreteTopology R := ⟨rfl⟩
  let xs : Fin n → S := fun i => (x i).val
  let _ : Algebra R S := f.hom.toRingHom.toAlgebra
  obtain ⟨g, hgX, _⟩ := @exists_algHom_mvPowerSeries_of_mem_maximalIdeal
    R S _ _ (f.hom.toRingHom.toAlgebra) _ _ _ _ n xs (fun i => (x i).2)
  have hC (r : R) : g (MvPowerSeries.C r) = f.hom r := g.commutes r
  let _ : IsLocalHom f.hom.toRingHom := f.isLocal
  have hlocal : IsLocalHom g.toRingHom :=
    eval₂Hom_isLocalHom n f.hom.toRingHom xs g.toRingHom hC hgX
      (fun i => (x i).2)
  exact ⟨rebasePowerSeriesMap f n g.toRingHom hC hlocal, hgX, hxclass⟩

private noncomputable def rebasePowerSeriesStructureMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    rebaseBase R ⟶ rebasePowerSeries R n := by
  let : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  let : Algebra R (MvPowerSeries (Fin n) R) := (algebraMap R _).toAlgebra
  let : Algebra (↑R) (↑(rebaseBase R)) :=
    (rebaseBase R).algebra
  let : Algebra (↑R) (↑(rebasePowerSeries R n)) :=
    (rebasePowerSeries R n).algebra
  let g :
      (↑(rebaseBase R)) →ₐ[↑R]
        (↑(rebasePowerSeries R n)) := {
    toRingHom := MvPowerSeries.C
    commutes' := fun r => rfl }
  refine ⟨g, ?_, ?_⟩
  · exact ⟨fun r hr => (MvPowerSeries.isUnit_iff_constantCoeff).mp hr⟩
  · intro r
    exact rebasePowerSeriesResidueEquiv_apply R n (algebraMap R _ r)

private theorem rebasePowerSeries_relativeCotangent_span_X
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    letI : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    letI : Module k (relativeCotangentSpaceOverBase (rebasePowerSeries R n)) :=
      relativeCotangentModuleOverK (rebasePowerSeries R n)
    Submodule.span k (Set.range fun i : Fin n =>
        (Submodule.Quotient.mk
        (⟨MvPowerSeries.X i, X_mem_maximalIdeal i⟩ : maximalIdeal (MvPowerSeries (Fin n) R)) :
        relativeCotangentSpaceOverBase (rebasePowerSeries R n))) = ⊤ := by
  let _ : Algebra R k :=
    (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
  let f := rebasePowerSeriesStructureMap R n
  let _ : Module k (relativeCotangentSpaceOverBase (rebasePowerSeries R n)) :=
    relativeCotangentModuleOverK (rebasePowerSeries R n)
  let Q : Type (max v 0) := MvPowerSeries (Fin n) R
  have hComm : (rebasePowerSeries R n).commRing =
      (inferInstance : CommRing (MvPowerSeries (Fin n) R)) := by rfl
  cases hComm
  let _ : Algebra k (ResidueField ↑(rebasePowerSeries R n)) :=
    (rebasePowerSeriesResidueEquiv R n).symm.toAlgHom.toRingHom.toAlgebra
  have hk : RingHom.ker (algebraMap R k) = maximalIdeal R := by
    ext x
    show R.residueEquiv (residue R x) = 0 ↔ x ∈ maximalIdeal R
    rw [map_eq_zero_iff _ R.residueEquiv.injective, residue_eq_zero_iff]
  let J := relativeCotangentSubmodule (rebasePowerSeries R n)
  let xclass : Fin n → relativeCotangentSpaceOverBase (rebasePowerSeries R n) := fun i =>
    Submodule.Quotient.mk (p := J) (⟨(MvPowerSeries.X i : ↑(rebasePowerSeries R n)),
      X_mem_maximalIdeal i⟩ : maximalIdeal ↑(rebasePowerSeries R n))
  show Submodule.span k (Set.range xclass) = ⊤
  apply top_unique
  intro z _
  change maximalIdeal ↑(rebasePowerSeries R n) ⧸ J at z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J z
  let xx : Q := (x : ↑(rebasePowerSeries R n))
  have hx0mem : MvPowerSeries.constantCoeff xx ∈ maximalIdeal R :=
    (Stacks.MvPowerSeries.RegularParameters.mem_maximalIdeal_iff_constantCoeff_mem
      (x : ↑(rebasePowerSeries R n))).mp x.2
  let c0 := MvPowerSeries.constantCoeff xx
  have hbase : MvPowerSeries.C c0 ∈ (maximalIdeal R).map (algebraMap R Q) :=
    Ideal.mem_map_of_mem (algebraMap R Q) hx0mem
  have hw0 : MvPowerSeries.constantCoeff (∑ i : Fin n, MvPowerSeries.C
      (MvPowerSeries.coeff (Finsupp.single i 1) xx) * MvPowerSeries.X i : Q) = (0 : R) := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by
      rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  have hw1 : ∀ j : Fin n, MvPowerSeries.coeff (Finsupp.single j 1)
      (∑ i : Fin n, MvPowerSeries.C
        (MvPowerSeries.coeff (Finsupp.single i 1) xx) * MvPowerSeries.X i : Q) =
      MvPowerSeries.coeff (Finsupp.single j 1) xx := by
    intro j
    rw [map_sum, Finset.sum_eq_single j]
    · rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X, ite_eq_left rfl, mul_one]
    · intro i _ hij
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X,
        ite_eq_right (fun hcontra =>
          hij ((Finsupp.single_left_inj (by norm_num)).mp hcontra.symm)),
        mul_zero]
    · exact fun hj => absurd (Finset.mem_univ j) hj
  have hsq : (xx - MvPowerSeries.C c0 -
      ∑ i : Fin n, MvPowerSeries.C
        (MvPowerSeries.coeff (Finsupp.single i 1) xx) * MvPowerSeries.X i) ∈
        maximalIdeal Q ^ 2 := by
    refine Stacks.MvPowerSeries.RegularParameters.mem_sq_maximalIdeal_of_linear_coeff_zero
      _ ?_ ?_
    · rw [map_sub, map_sub, MvPowerSeries.constantCoeff_C, hw0]
      simp [c0]
    · intro j
      have hC0 : MvPowerSeries.coeff (Finsupp.single j 1) (MvPowerSeries.C c0 : Q) = 0 := by
        rw [MvPowerSeries.coeff_C]; simp
      rw [map_sub, map_sub, hC0, hw1 j, sub_zero, sub_self]
  have hrel : (xx - ∑ i : Fin n, MvPowerSeries.C
      (MvPowerSeries.coeff (Finsupp.single i 1) xx) * MvPowerSeries.X i) ∈
      (maximalIdeal R).map (algebraMap R Q) + maximalIdeal Q ^ 2 :=
    Submodule.mem_sup.mpr ⟨MvPowerSeries.C c0, hbase, _, hsq, by abel⟩
  have hquot : Submodule.Quotient.mk (x : maximalIdeal ↑(rebasePowerSeries R n)) =
      ∑ i : Fin n, (R.residueEquiv (residue R
        (MvPowerSeries.coeff (Finsupp.single i 1) xx))) • xclass i := by
    let a : Fin n → R := fun i => MvPowerSeries.coeff (Finsupp.single i 1) xx
    let y : Fin n → maximalIdeal ↑(rebasePowerSeries R n) := fun i => ⟨(MvPowerSeries.C (a i) *
      MvPowerSeries.X i : ↑(rebasePowerSeries R n)),
        Ideal.mul_mem_left _ _ (X_mem_maximalIdeal i)⟩
    have hq : Submodule.Quotient.mk (p := J) (x : maximalIdeal ↑(rebasePowerSeries R n)) =
      Submodule.Quotient.mk (p := J) (∑ i : Fin n, y i) := by
      have hrelJ : (x - ∑ i : Fin n, y i) ∈ J := by
        dsimp only [J, relativeCotangentSubmodule]
        rw [hk]
        show (x - ∑ i : Fin n, y i) ∈
          Submodule.comap (maximalIdeal ↑(rebasePowerSeries R n)).subtype
            ((maximalIdeal R).map (algebraMap R ↑(rebasePowerSeries R n)) +
              maximalIdeal ↑(rebasePowerSeries R n) ^ 2)
        rw [Submodule.mem_comap]
        show ((x - ∑ i : Fin n, y i : maximalIdeal ↑(rebasePowerSeries R n)) :
          ↑(rebasePowerSeries R n)) ∈ _
        rw [Submodule.coe_sub, Submodule.coe_sum]
        show ((x : ↑(rebasePowerSeries R n)) -
          ∑ i : Fin n, (y i : ↑(rebasePowerSeries R n))) ∈
          ((maximalIdeal R).map
            (algebraMap R ↑(rebasePowerSeries R n)) :
              Ideal ↑(rebasePowerSeries R n)) ⊔
            (maximalIdeal ↑(rebasePowerSeries R n) ^ 2 :
              Ideal ↑(rebasePowerSeries R n))
        exact hrel
      exact (Submodule.Quotient.eq J).2 hrelJ
    have hsmul (i : Fin n) :
        (R.residueEquiv (residue R (a i))) • xclass i =
          Submodule.Quotient.mk (y i) := by
      let c : ↑(rebasePowerSeries R n) := MvPowerSeries.C (a i)
      let xP : maximalIdeal ↑(rebasePowerSeries R n) :=
        ⟨MvPowerSeries.X i, X_mem_maximalIdeal i⟩
      have hxclass : xclass i = Submodule.Quotient.mk xP := rfl
      let htor := relativeCotangent_isTorsionByMaximalIdeal (rebasePowerSeries R n)
      let _ : Module (ResidueField ↑(rebasePowerSeries R n))
          (relativeCotangentSpaceOverBase (rebasePowerSeries R n)) := htor.module
      let _ : SMul (↑(rebasePowerSeries R n) ⧸
          maximalIdeal ↑(rebasePowerSeries R n))
          (relativeCotangentSpaceOverBase (rebasePowerSeries R n)) := htor.hasSMul
      have hscalar : algebraMap k (ResidueField ↑(rebasePowerSeries R n))
          (R.residueEquiv (residue R (a i))) = residue ↑(rebasePowerSeries R n) c := by
        apply (rebasePowerSeriesResidueEquiv R n).injective
        show (rebasePowerSeriesResidueEquiv R n)
            ((rebasePowerSeriesResidueEquiv R n).symm
              (R.residueEquiv (residue R (a i)))) =
          (rebasePowerSeriesResidueEquiv R n) (residue Q (MvPowerSeries.C (a i) : Q))
        rw [AlgEquiv.apply_symm_apply, rebasePowerSeriesResidueEquiv_apply]
        simp [MvPowerSeries.constantCoeff_C]
      show algebraMap k (ResidueField ↑(rebasePowerSeries R n))
          (R.residueEquiv (residue R (a i))) • xclass i = _
      rw [hscalar]
      calc
        _ = residue ↑(rebasePowerSeries R n) c • xclass i := rfl
        _ = Ideal.Quotient.mk
              (maximalIdeal ↑(rebasePowerSeries R n))
              c • xclass i := rfl
        _ = c • xclass i := htor.mk_smul c _
        _ = Submodule.Quotient.mk (y i) := by
          rw [hxclass]
          show Submodule.Quotient.mk (c • xP) = Submodule.Quotient.mk (y i)
          apply congrArg (Submodule.Quotient.mk (p := J))
          apply Subtype.ext
          show (MvPowerSeries.C (a i) • (MvPowerSeries.X i : Q)) =
            (MvPowerSeries.C (a i) * MvPowerSeries.X i : Q)
          rfl
    change (Submodule.Quotient.mk (p := J) (x : maximalIdeal ↑(rebasePowerSeries R n)) :
        relativeCotangentSpaceOverBase (rebasePowerSeries R n)) =
      (Submodule.Quotient.mk (p := J) (∑ i : Fin n, y i) :
        relativeCotangentSpaceOverBase (rebasePowerSeries R n)) at hq
    have hmap : (Submodule.Quotient.mk (p := J) (∑ i : Fin n, y i) :
          relativeCotangentSpaceOverBase (rebasePowerSeries R n)) =
        ∑ i : Fin n, (Submodule.Quotient.mk (p := J) (y i) :
          relativeCotangentSpaceOverBase (rebasePowerSeries R n)) := by
      simpa only [Submodule.mkQ_apply] using map_sum (Submodule.mkQ J) y Finset.univ
    have hsums : (∑ i : Fin n, (Submodule.Quotient.mk (p := J) (y i) :
          relativeCotangentSpaceOverBase (rebasePowerSeries R n))) =
        ∑ i : Fin n, (R.residueEquiv (residue R (a i))) • xclass i := by
      exact Finset.sum_congr rfl fun i _ => (hsmul i).symm
    exact hq.trans (hmap.trans hsums)
  show (Submodule.Quotient.mk (x : maximalIdeal ↑(rebasePowerSeries R n)) :
      relativeCotangentSpaceOverBase (rebasePowerSeries R n)) ∈
    Submodule.span k (Set.range xclass)
  rw [hquot]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
private theorem isSmooth_restrictedRepresentableMap_of_isPowerSeriesOver
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (hps : IsPowerSeriesOver f) : IsSmooth (restrictedRepresentableMap f) := by
  let _ : Algebra R S := f.hom.toRingHom.toAlgebra
  obtain ⟨n, ⟨e⟩⟩ := hps
  rw [isSmooth_restrictedRepresentableMap_iff_lifts]
  intro B A q hq sA rB hcomm
  let _ : Algebra R B := rB.hom.toRingHom.toAlgebra
  let _ : Algebra R A := (q.hom.toRingHom.comp rB.hom.toRingHom).toAlgebra
  let _ : TopologicalSpace R := ⊥
  let _ : DiscreteTopology R := ⟨rfl⟩
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := ⟨rfl⟩
  have hcomm' : sA.hom.toRingHom.comp f.hom.toRingHom =
      (rB ≫ artinianToComplete.map q).hom.toRingHom := by
    have hh := congrArg (fun z : CompleteLocalAlgCat.Hom R
        (artinianToComplete.obj A) => z.hom.toRingHom) hcomm
    convert hh using 1 <;> rfl
  let _ : IsLocalHom sA.hom.toRingHom := sA.isLocal
  let a : Fin n → A := fun i => sA.hom (e.symm (MvPowerSeries.X i))
  have ha : ∀ i, a i ∈ maximalIdeal A := by
    intro i
    have hx : e.symm (MvPowerSeries.X i) ∈ maximalIdeal S := by
      rw [mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' := hu.map e
      simp only [MvPowerSeries.isUnit_iff_constantCoeff, AlgEquiv.apply_symm_apply,
        MvPowerSeries.constantCoeff_X] at hu'
      exact not_isUnit_zero hu'
    exact map_nonunit sA.hom.toRingHom _ hx
  choose b hb using fun i => hq (a i)
  have hbmax : ∀ i, b i ∈ maximalIdeal B := by
    intro i
    have hnot : ¬ IsUnit (a i) := by
      simpa [mem_maximalIdeal, mem_nonunits_iff] using ha i
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit (q.hom (b i)) := hu.map q.hom.toRingHom
    rw [hb i] at hu'
    exact hnot hu'
  obtain ⟨g, hg, hgcont⟩ := exists_algHom_mvPowerSeries_of_artinianLocal
    (R := R) (B := B) n b hbmax
  let t : S →ₐ[R] B := g.comp e.toAlgHom
  let qR : B →ₐ[R] A :=
    { toRingHom := q.hom.toRingHom
      commutes' := fun r => rfl }
  let sAR : MvPowerSeries (Fin n) R →ₐ[R] A :=
    { toRingHom := sA.hom.toRingHom.comp (e.symm.toAlgHom.toRingHom)
      commutes' := fun r => by
        calc
          sA.hom (e.symm (algebraMap R (MvPowerSeries (Fin n) R) r)) =
              sA.hom (f.hom r) := by
            rw [e.symm.commutes]
            rfl
          _ = (rB ≫ artinianToComplete.map q).hom r :=
            congrArg (fun z : R →+* A => z r) hcomm'
          _ = algebraMap R A r := rfl }
  have hvars : ∀ i, (qR.comp g) (MvPowerSeries.X i) =
      sAR (MvPowerSeries.X i) := by
    intro i
    simp [qR, sAR, hg, hb, a]
  have hmap : qR.comp g = sAR := by
    refine AlgHom.coe_ringHom_injective ?_
    refine MvPowerSeries.hom_ext_of_isNilpotent n _ _ (fun r => ?_) (fun i => ?_)
      (fun i => ?_)
    · rw [MvPowerSeries.c_eq_algebraMap]
      exact ((qR.comp g).commutes r).trans (sAR.commutes r).symm
    · exact hvars i
    · exact (hvars i).symm ▸ isNilpotent_of_mem_maximalIdeal (ha i)
  have hcomp : q.hom.toRingHom.comp t.toRingHom = sA.hom.toRingHom := by
    ext x
    have hx := congrArg (fun z : MvPowerSeries (Fin n) R →ₐ[R] A => z (e x)) hmap
    simpa [qR, t, sAR] using hx
  have hxEq (x : S) : q.hom (t x) = sA.hom x := congrArg (fun z : S →+* A => z x) hcomp
  have htlocal : IsLocalHom t.toRingHom :=
    ⟨fun x hx => sA.isLocal.map_nonunit x (hxEq x ▸ hx.map q.hom.toRingHom)⟩
  have htres : ∀ x : S, B.residueEquiv (residue B (t x)) =
      S.residueEquiv (residue S x) := fun x => by
    rw [← sA.residue_comm x, ← hxEq x]
    exact (q.residue_comm (t x)).symm
  let sB : CompleteLocalAlgCat.Hom S (artinianToComplete.obj B) :=
    { hom := t.restrictScalars Λ
      isLocal := htlocal
      residue_comm := htres }
  exact ⟨sB, CompleteLocalAlgCat.Hom.ext (AlgHom.ext hxEq),
    CompleteLocalAlgCat.Hom.ext (AlgHom.ext fun r => t.commutes r)⟩

/-- The morphism between restricted representable categories induced by `f : R ⟶ S` is smooth
if and only if `f` exhibits `S` as a formal power series ring in finitely many variables over
`R`. -/
@[stacks 06HL "smooth if and only if a power series ring",
  sga "7 VI 2.2(c)",
  sga "1 III 1.5" "complete local case"]
public theorem restrictedRepresentableMap_isSmooth_iff_isPowerSeriesOver
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    IsSmooth (restrictedRepresentableMap f) ↔ IsPowerSeriesOver f := by
  constructor
  · intro hs
    let _ : Algebra R k :=
      (R.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue R)).toAlgebra
    let _ : Algebra R S := f.hom.toRingHom.toAlgebra
    let _ : Algebra S k :=
      (S.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue S)).toAlgebra
    let _ : Algebra R (ResidueField S) :=
      (IsLocalRing.residue S).comp f.hom.toRingHom |>.toAlgebra
    let _ : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (f.residue_comm r).symm)
    let B := rebaseTarget R S f
    let _ : Algebra k (ResidueField B) :=
      B.residueEquiv.symm.toAlgHom.toRingHom.toAlgebra
    let _ : Module k (relativeCotangentSpaceOverBase B) :=
      relativeCotangentModuleOverK B
    let _ : FiniteDimensional k (relativeCotangentSpaceOverBase B) :=
      relativeCotangent_finiteDimensional B
    let n := Module.finrank k (relativeCotangentSpaceOverBase B)
    obtain ⟨g, hgX, hclass⟩ := exists_rebasePowerSeriesMap_of_cotangentBasis f
    let T := rebasePowerSeries R n
    let _ : Module k (relativeCotangentSpaceOverBase T) :=
      relativeCotangentModuleOverK T
    let L := relativeCotangentSpaceMapLinear g
    let b := relativeCotangentBasis B
    let v : Fin n → relativeCotangentSpaceOverBase T := fun i =>
      Submodule.Quotient.mk
        (⟨MvPowerSeries.X i, X_mem_maximalIdeal i⟩ : maximalIdeal (MvPowerSeries (Fin n) R))
    have himage (i : Fin n) : L (v i) = b i := by
      show Submodule.Quotient.mk
        (⟨g.hom (MvPowerSeries.X i), _⟩ : maximalIdeal B) = b i
      convert hclass i using 1
      congr 1
      exact Subtype.ext (hgX i)
    have hspan : Submodule.span k (Set.range v) = ⊤ :=
      rebasePowerSeries_relativeCotangent_span_X R n
    have hLi : Function.Injective L := by
      apply LinearMap.injective_of_linearIndependent hspan
      rw [show L ∘ v = b from funext himage]
      exact b.linearIndependent
    have hL : Function.Surjective L := by
      apply LinearMap.range_eq_top.mp
      apply top_unique
      rw [← b.span_eq]
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      exact ⟨v i, himage i⟩
    have hg : Function.Surjective g.hom :=
      (surjective_iff_surjective_relativeCotangentSpaceMap g).2 hL
    let P := mvPowerSeriesObject R n
    have hres (x : P) : P.residueEquiv (residue P x) = T.residueEquiv (residue T x) := rfl
    let φ : P ⟶ S :=
      { hom :=
          { toRingHom := g.hom.toRingHom
            commutes' := fun c => by
              have hh := g.hom.commutes (algebraMap Λ R c)
              change g.hom (MvPowerSeries.C (algebraMap Λ R c)) = _ at hh
              show g.hom (algebraMap Λ (MvPowerSeries (Fin n) R) c) = _
              rw [MvPowerSeries.algebraMap_apply]
              exact hh.trans (f.hom.commutes c) }
        isLocal := g.isLocal
        residue_comm := fun x => (g.residue_comm x).trans (hres x).symm }
    let r : R ⟶ P :=
      { hom :=
          { toRingHom := MvPowerSeries.C
            commutes' := fun c => by
              show MvPowerSeries.C (algebraMap Λ R c) =
                algebraMap Λ (MvPowerSeries (Fin n) R) c
              exact MvPowerSeries.algebraMap_apply.symm }
        isLocal := (rebasePowerSeriesStructureMap R n).isLocal
        residue_comm := fun x => (hres _).trans
          ((rebasePowerSeriesStructureMap R n).residue_comm x) }
    have hfac : r ≫ φ = f := by
      apply CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      exact g.hom.commutes
    obtain ⟨s₀, hs₀, hb₀⟩ := smooth_lift_firstOrder f hs r φ hg hfac
    obtain ⟨s, hbase, hfirst⟩ := smooth_lift_to_complete f hs r s₀ hb₀
    let sR : B ⟶ T :=
      { hom :=
          { toRingHom := s.hom.toRingHom
            commutes' := fun x =>
              congrArg (fun z : R ⟶ P => z.hom x) hbase }
        isLocal := s.isLocal
        residue_comm := fun x => (hres _).symm.trans (s.residue_comm x) }
    have hmod (x : S) : Ideal.Quotient.mk (maximalIdeal S ^ 2)
        (g.hom (s.hom x)) = Ideal.Quotient.mk (maximalIdeal S ^ 2) x := by
      have hh := congrArg (fun z : S ⟶ artinianToComplete.obj
          (AdicTruncation.obj S 1) => z.hom x) hs₀
      have hx := congrArg (fun z : S ⟶ artinianToComplete.obj
          (AdicTruncation.obj P 1) => z.hom x) hfirst
      change Ideal.Quotient.mk (maximalIdeal P ^ 2) (s.hom x) = s₀.hom x at hx
      change (AdicTruncation.map φ 1).hom (s₀.hom x) = _ at hh
      rw [← hx] at hh
      exact hh
    let M := relativeCotangentSpaceMapLinear sR
    have hLM (x : relativeCotangentSpaceOverBase B) : L (M x) = x := by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
        (relativeCotangentSubmodule B) x
      show Submodule.Quotient.mk
        (⟨g.hom (s.hom x.val), _⟩ : maximalIdeal B) = Submodule.Quotient.mk x
      apply (Submodule.Quotient.eq _).2
      show g.hom (s.hom x.val) - x.val ∈
        (RingHom.ker (algebraMap R k)).map (algebraMap R S) + maximalIdeal S ^ 2
      exact (show maximalIdeal S ^ 2 ≤
        (RingHom.ker (algebraMap R k)).map (algebraMap R S) + maximalIdeal S ^ 2 from
          le_sup_right) (Ideal.Quotient.eq.mp (hmod x.val))
    have hMs : Function.Surjective M := fun x => ⟨L x, hLi (hLM (L x))⟩
    have hsR : Function.Surjective sR.hom :=
      (surjective_iff_surjective_relativeCotangentSpaceMap sR).2 hMs
    have hgs : Function.Injective (sR.hom.toRingHom.comp g.hom.toRingHom) :=
      surjective_endomorphism_noetherian_injective T _ (hsR.comp hg)
    have hgi : Function.Injective g.hom := fun x y h => hgs (congrArg sR.hom h)
    exact ⟨n, ⟨(AlgEquiv.ofBijective g.hom ⟨hgi, hg⟩).symm⟩⟩
  · exact isSmooth_restrictedRepresentableMap_of_isPowerSeriesOver f
end Deformation

end

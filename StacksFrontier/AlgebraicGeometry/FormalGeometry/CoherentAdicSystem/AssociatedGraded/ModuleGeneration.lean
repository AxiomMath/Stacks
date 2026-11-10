module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedDegreeColimits
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Transition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel

/-!
# Generation of associated graded modules

Commutative algebra for the associated graded module of a coherent adic system: the graded
pieces `I ⁿ M / I ⁿ⁺¹ M` of an `I`-adically complete module, their identification with the
transition kernels of the quotient tower, and the transport of finite homogeneous generation along
a semilinear equivalence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

local instance ringHomInvPairOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] (σ : R ≃+* S) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ

local instance ringHomInvPairOfRingEquivSymm {R S : Type*} [CommRing R] [CommRing S]
    (σ : R ≃+* S) : RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

/-! ### Generation of associated graded modules -/

/-- An element of a module, read in the degree-zero step of the ideal-power filtration. -/
private def associatedGradedDegreeZero {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (m : M) :
    AssociatedGraded.power (M := M) I 0 :=
  ⟨m, by simp [AssociatedGraded.power]⟩

private theorem associatedGraded_mem_degreeZero {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (m : M) :
    m ∈ AssociatedGraded.power (M := M) I 0 := by
  simp [AssociatedGraded.power]

private theorem associatedGraded_mk_congr {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (n : ℕ)
    (x y : AssociatedGraded.power (M := M) I n) (h : (x : M) = y) :
    AssociatedGraded.mk I n x = AssociatedGraded.mk I n y := by
  obtain rfl := Subtype.ext h
  rfl

/-- An element of `I ^ n` scales any module element into the `n`-th step of the filtration. -/
private theorem associatedGraded_smul_mem_power_self {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (n : ℕ) {a : A} (m : M)
    (ha : a ∈ AssociatedGraded.power (M := A) I n) :
    a • m ∈ AssociatedGraded.power (M := M) I n := by
  rw [AssociatedGraded.ring_power_eq] at ha
  rw [AssociatedGraded.power]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- The class in degree `n` of a module element scaled by an element of `I ^ n`. -/
private def gradedScale {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) (a : AssociatedGraded.power (M := A) I n) (s : M) :
    AssociatedGraded.piece (M := M) I n :=
  AssociatedGraded.mk I n ⟨(a : A) • s,
    associatedGraded_smul_mem_power_self I n s a.property⟩

private lemma gradedScale_mk {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (n : ℕ) (a : AssociatedGraded.power (M := A) I n) (s : M)
    (x : AssociatedGraded.power (M := M) I n) (hx : (x : M) = (a : A) • s) :
    AssociatedGraded.mk I n x = gradedScale I n a s :=
  associatedGraded_mk_congr I n x _ hx

/-- Multiplying an element of a module by an element of `I ^ n` lands in the `n`-th step of the
ideal-power filtration. -/
private def associatedGradedPowerSaturation {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A) (n : ℕ)
    (a : AssociatedGraded.power (M := A) I n) (m : M) :
    AssociatedGraded.power (M := M) I n :=
  ⟨(a : A) • m, associatedGraded_smul_mem_power_self I n m a.property⟩

/-- Scalars from an ideal power of the base ring, pushed into an algebra, still carry a module
into the corresponding step of the base ring's ideal-power filtration. -/
private theorem associatedGraded_mapIdeal_smul_mem_power
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) (n : ℕ) {c : S} (hc : c ∈ (I ^ n).map (algebraMap R S))
    (m : M) :
    c • m ∈ AssociatedGraded.power (M := M) I n := by
  revert m
  change c ∈ Submodule.span S
    ((algebraMap R S) '' ((I ^ n : Ideal R) : Set R)) at hc
  induction hc using Submodule.span_induction with
  | mem x hx =>
      intro m
      obtain ⟨r, hr, rfl⟩ := hx
      change (algebraMap R S r) • m ∈ I ^ n • (⊤ : Submodule R M)
      rw [IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
  | zero =>
      intro m
      change (0 : S) • m ∈ I ^ n • (⊤ : Submodule R M)
      simp
  | add x y hx hy ihx ihy =>
      intro m
      change (x + y) • m ∈ I ^ n • (⊤ : Submodule R M)
      rw [add_smul]
      exact Submodule.add_mem _ (ihx m) (ihy m)
  | smul a x hx ih =>
      intro m
      change (a * x) • m ∈ I ^ n • (⊤ : Submodule R M)
      rw [show a * x = x * a by rw [mul_comm], mul_smul]
      exact ih (a • m)

/-- Generators over an algebra whose residue ring modulo the extended ideal is a quotient of the
base ring already generate every associated graded piece over the base ring. -/
private theorem associatedGraded_piece_closure_smul_generators_of_residue_surjective
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) (G : Finset M)
    (hG : Submodule.span S (G : Set M) = ⊤)
    (hres : ∀ c : S, ∃ r : R, c - algebraMap R S r ∈ I.map (algebraMap R S))
    (n : ℕ) :
    AddSubgroup.closure
      {x : AssociatedGraded.piece (M := M) I n |
        ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := R) I n,
          x = gradedScale I n a s} = ⊤ := by
  apply top_unique
  intro x _
  induction x using Quotient.inductionOn with
  | _ y =>
    let H : AddSubgroup (AssociatedGraded.piece (M := M) I n) :=
      AddSubgroup.closure
        {x : AssociatedGraded.piece (M := M) I n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := R) I n,
            x = gradedScale I n a s}
    have gen (m : M) (hm : m ∈ Submodule.span S (G : Set M)) :
        ∀ a : AssociatedGraded.power (M := R) I n,
          AssociatedGraded.mk I n
            (associatedGradedPowerSaturation I n a m) ∈ H := by
      induction hm using Submodule.span_induction with
      | mem s hs =>
          intro a
          apply AddSubgroup.subset_closure
          exact ⟨s, hs, a, rfl⟩
      | zero =>
          intro a
          have hzero : associatedGradedPowerSaturation I n a (0 : M) = 0 := by
            apply Subtype.ext
            simp [associatedGradedPowerSaturation]
          rw [hzero]
          exact H.zero_mem
      | add m₁ m₂ hm₁ hm₂ ih₁ ih₂ =>
          intro a
          have hsum : associatedGradedPowerSaturation I n a (m₁ + m₂) =
              associatedGradedPowerSaturation I n a m₁ +
              associatedGradedPowerSaturation I n a m₂ := by
            apply Subtype.ext
            simp [associatedGradedPowerSaturation, smul_add]
          rw [hsum]
          change Submodule.Quotient.mk
            (associatedGradedPowerSaturation I n a m₁ +
             associatedGradedPowerSaturation I n a m₂) ∈ H
          rw [Submodule.Quotient.mk_add]
          exact AddSubgroup.add_mem H (ih₁ a) (ih₂ a)
      | smul c m hm ih =>
          intro a
          obtain ⟨r, hr⟩ := hres c
          have ha : (a : R) ∈ I ^ n := by
            simpa [AssociatedGraded.power] using a.property
          let a' : AssociatedGraded.power (M := R) I n :=
            ⟨(a : R) * r, by
              simpa [AssociatedGraded.power] using
                (Ideal.mul_mem_right r (I ^ n) ha)⟩
          have hdiff : (algebraMap R S (a : R)) * (c - algebraMap R S r) ∈
              (I ^ (n + 1)).map (algebraMap R S) := by
            have hprod : (algebraMap R S (a : R)) * (c - algebraMap R S r) ∈
                (I ^ n).map (algebraMap R S) * I.map (algebraMap R S) :=
              Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) hr
            simpa [Ideal.map_mul, pow_succ] using hprod
          have herr :
              (algebraMap R S (a : R) * (c - algebraMap R S r)) • m ∈
                AssociatedGraded.power (M := M) I (n + 1) :=
            associatedGraded_mapIdeal_smul_mem_power I (n + 1) hdiff m
          have heq : AssociatedGraded.mk I n
              (associatedGradedPowerSaturation I n a (c • m)) =
            AssociatedGraded.mk I n
              (associatedGradedPowerSaturation I n a' m) := by
            apply (Submodule.Quotient.eq _).2
            have hval : (a : R) • (c • m) - ((a' : R) • m) =
                (algebraMap R S (a : R) * (c - algebraMap R S r)) • m := by
              have h₁ : (a : R) • (c • m) =
                  (algebraMap R S (a : R) * c) • m := by
                rw [← IsScalarTower.algebraMap_smul (A := S), smul_smul]
              have h₂ : ((a' : R) • m) =
                  (algebraMap R S ((a : R) * r)) • m := by
                rw [← IsScalarTower.algebraMap_smul (A := S)]
              rw [h₁, h₂, map_mul, ← sub_smul, mul_sub]
            change (a : R) • (c • m) - ((a' : R) • m) ∈
              AssociatedGraded.power (M := M) I (n + 1)
            rw [hval]
            exact herr
          rw [heq]
          exact ih a'
    have hy : (y : M) ∈ I ^ n • (⊤ : Submodule R M) := by
      simpa [AssociatedGraded.power] using y.property
    have hPy : ∀ hz : (y : M) ∈ AssociatedGraded.power (M := M) I n,
        AssociatedGraded.mk I n ⟨(y : M), hz⟩ ∈ H := by
      refine Submodule.smul_induction_on' hy ?_ ?_
      · intro a ha m _ hmem
        have hmG : m ∈ Submodule.span S (G : Set M) := by
          rw [hG]
          exact Submodule.mem_top
        have ha' : a ∈ AssociatedGraded.power (M := R) I n := by simpa using ha
        have hgen := gen m hmG ⟨a, ha'⟩
        have heq : associatedGradedPowerSaturation I n ⟨a, ha'⟩ m =
            ⟨a • m, hmem⟩ := by
          apply Subtype.ext
          rfl
        rw [← heq]
        exact hgen
      · intro z hz w hw ihz ihw _
        change Submodule.Quotient.mk
          ((⟨z, hz⟩ : AssociatedGraded.power (M := M) I n) + ⟨w, hw⟩) ∈ H
        rw [Submodule.Quotient.mk_add]
        exact AddSubgroup.add_mem H (ihz hz) (ihw hw)
    exact hPy y.property

/-- Every element of the adic completion of a ring agrees with an element of the ring modulo the
extended ideal. -/
private theorem adicCompletion_residue_surjective
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) :
    ∀ c : AdicCompletion I R,
      ∃ r : R,
        c - algebraMap R (AdicCompletion I R) r ∈
          I.map (algebraMap R (AdicCompletion I R)) := by
  intro c
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I c)
  refine ⟨r, ?_⟩
  have hEval : (AdicCompletion.evalOneₐ I).toRingHom
      (algebraMap R (AdicCompletion I R) r) = Ideal.Quotient.mk I r :=
    congrArg (fun f : R →+* R ⧸ I => f r)
      (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk (I := I))
  have hr' : (AdicCompletion.evalOneₐ I).toRingHom c = Ideal.Quotient.mk I r := by
    simpa using hr.symm
  have hz : c - algebraMap R (AdicCompletion I R) r ∈
      RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
    apply RingHom.mem_ker.mpr
    rw [map_sub]
    change (AdicCompletion.evalOneₐ I).toRingHom c -
      (AdicCompletion.evalOneₐ I).toRingHom
        (algebraMap R (AdicCompletion I R) r) = 0
    rw [hEval, hr', sub_self]
  exact (AdicCompletion.ker_evalOneₐ_eq_map I hI) ▸ hz

/-- A finite module over the adic completion of a Noetherian ring has a single finite subset
generating every associated graded piece of its ideal-power filtration. -/
private theorem adicCompletion_associatedGraded_piece_closure_smul_fg
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    {I : Ideal R} [AddCommGroup M] [Module R M]
    [Module (AdicCompletion I R) M] [IsScalarTower R (AdicCompletion I R) M]
    [Module.Finite (AdicCompletion I R) M] :
    ∃ G : Finset M, ∀ n : ℕ,
      AddSubgroup.closure
        {x : AssociatedGraded.piece (M := M) I n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := R) I n,
            x = gradedScale I n a s} = ⊤ := by
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  obtain ⟨G, hG⟩ := Module.Finite.fg_top
    (R := AdicCompletion I R) (M := M)
  refine ⟨G, fun n => ?_⟩
  exact associatedGraded_piece_closure_smul_generators_of_residue_surjective
    I G hG (adicCompletion_residue_surjective I hI) n

/-- A surjection from a submodule whose kernel is the restriction of `T` identifies the quotient
with the target. -/
private def quotEquivOfKerComap {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {S T : Submodule R M} (g : S →ₗ[R] N)
    (hker : LinearMap.ker g = T.comap S.subtype) (hsurj : Function.Surjective g) :
    (S ⧸ T.comap S.subtype) ≃+ N :=
  ((Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)).toAddEquiv

/-- If two compatible projections from an inverse limit are surjective and their kernels are
consecutive ideal powers, the associated graded piece identifies with the transition kernel. -/
private def associatedGradedPieceEquivKernel
    {R M N N' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (I : Ideal R) (n : ℕ) (p : M →ₗ[R] N) (q : M →ₗ[R] N')
    (f : N →ₗ[R] N') (hp : Function.Surjective p)
    (hpker : LinearMap.ker p = AssociatedGraded.power (M := M) I (n + 1))
    (hqker : LinearMap.ker q = AssociatedGraded.power (M := M) I n)
    (hcomp : f.comp p = q) :
    AssociatedGraded.piece (M := M) I n ≃+ LinearMap.ker f := by
  let S : Submodule R M := AssociatedGraded.power (M := M) I n
  let T : Submodule R M := AssociatedGraded.power (M := M) I (n + 1)
  let g : S →ₗ[R] LinearMap.ker f :=
    { toFun := fun x =>
        ⟨p x, by
          change (f.comp p) x = 0
          rw [hcomp]
          have hx : (x : M) ∈ LinearMap.ker q := by
            rw [hqker]
            exact x.property
          exact LinearMap.mem_ker.mpr hx⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro r x; ext; simp }
  have hker : LinearMap.ker g = T.comap S.subtype := by
    ext x
    change g x = 0 ↔ (x : M) ∈ AssociatedGraded.power (M := M) I (n + 1)
    rw [← hpker]
    exact Subtype.ext_iff
  have hsurj : Function.Surjective g := by
    intro z
    obtain ⟨x, hx⟩ := hp z.1
    have hxS : x ∈ S := by
      change x ∈ AssociatedGraded.power (M := M) I n
      rw [← hqker, LinearMap.mem_ker, ← hcomp, LinearMap.comp_apply, hx]
      exact z.2
    exact ⟨⟨x, hxS⟩, Subtype.ext hx⟩
  exact quotEquivOfKerComap g hker hsurj

private theorem associatedGradedPieceEquivKernel_mk_val
    {R M N N' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (I : Ideal R) (n : ℕ) (p : M →ₗ[R] N) (q : M →ₗ[R] N')
    (f : N →ₗ[R] N') (hp : Function.Surjective p)
    (hpker : LinearMap.ker p = AssociatedGraded.power (M := M) I (n + 1))
    (hqker : LinearMap.ker q = AssociatedGraded.power (M := M) I n)
    (hcomp : f.comp p = q)
    (x : AssociatedGraded.power (M := M) I n) :
    ((associatedGradedPieceEquivKernel I n p q f hp hpker hqker hcomp
      (AssociatedGraded.mk I n x)) : N) = p x := by
  dsimp [associatedGradedPieceEquivKernel]
  rfl

/-- The degree-zero associated graded piece is the first quotient projection. -/
private def associatedGradedZeroPieceEquivOfSurjective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (p : M →ₗ[R] N)
    (hp : Function.Surjective p)
    (hpker : LinearMap.ker p = AssociatedGraded.power (M := M) I 1) :
    AssociatedGraded.piece (M := M) I 0 ≃+ N := by
  let S : Submodule R M := AssociatedGraded.power (M := M) I 0
  let T : Submodule R M := AssociatedGraded.power (M := M) I 1
  let g : S →ₗ[R] N := p.domRestrict S
  have hker : LinearMap.ker g = T.comap S.subtype := by
    ext x
    change p x = 0 ↔ (x : M) ∈ AssociatedGraded.power (M := M) I 1
    rw [← hpker, LinearMap.mem_ker]
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hp y
    exact ⟨⟨x, by simp [S]⟩, hx⟩
  exact quotEquivOfKerComap g hker hsurj

private theorem associatedGradedZeroPieceEquivOfSurjective_mk
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (p : M →ₗ[R] N)
    (hp : Function.Surjective p)
    (hpker : LinearMap.ker p = AssociatedGraded.power (M := M) I 1)
    (x : AssociatedGraded.power (M := M) I 0) :
    associatedGradedZeroPieceEquivOfSurjective I p hp hpker
      (AssociatedGraded.mk I 0 x) = p x := by
  dsimp [associatedGradedZeroPieceEquivOfSurjective]
  rfl

/-! ### Transport of generation along a semilinear equivalence -/

section FiniteGenerationTransport

variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

private lemma semilinear_mem_power (σ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ ≤ J) (f : M →ₛₗ[σ] N) (n : ℕ) {x : M}
    (hx : x ∈ AssociatedGraded.power I n) : f x ∈ AssociatedGraded.power J n := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha m _
    rw [show f (a • m) = σ a • f m from f.map_smulₛₗ a m]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    have hh := Ideal.mem_map_of_mem σ ha
    rw [Ideal.map_pow] at hh
    exact (pow_le_pow_left' hIJ n) hh
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

private lemma semilinear_mem_power_iff (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ.toRingHom = J) (e : M ≃ₛₗ[σ.toRingHom] N) (n : ℕ) (x : M) :
    e x ∈ AssociatedGraded.power J n ↔ x ∈ AssociatedGraded.power I n := by
  have hJI : J.map σ.symm.toRingHom = I := by
    rw [← hIJ, Ideal.map_map]
    simp
  constructor
  · intro hx
    have hh := semilinear_mem_power σ.symm.toRingHom J I hJI.le e.symm.toLinearMap n hx
    change e.symm (e x) ∈ _ at hh
    rw [e.symm_apply_apply] at hh
    exact hh
  · exact semilinear_mem_power σ.toRingHom I J hIJ.le e.toLinearMap n

private lemma semilinear_symm_mem_power_iff (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ.toRingHom = J) (e : M ≃ₛₗ[σ.toRingHom] N) (n : ℕ) (y : N) :
    e.symm y ∈ AssociatedGraded.power I n ↔ y ∈ AssociatedGraded.power J n :=
  (semilinear_mem_power_iff σ I J hIJ e n (e.symm y)).symm.trans (by rw [e.apply_symm_apply])

private def gradedPowerEquiv (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ.toRingHom = J) (e : M ≃ₛₗ[σ.toRingHom] N) (n : ℕ) :
    AssociatedGraded.power (M := M) I n ≃ₛₗ[σ.toRingHom]
      AssociatedGraded.power (M := N) J n :=
  e.ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv]
    exact semilinear_symm_mem_power_iff σ I J hIJ e n y)

private def gradedPieceEquiv (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ.toRingHom = J) (e : M ≃ₛₗ[σ.toRingHom] N) (n : ℕ) :
    AssociatedGraded.piece (M := M) I n ≃ₛₗ[σ.toRingHom]
      AssociatedGraded.piece (M := N) J n :=
  Submodule.Quotient.equiv _ _ (gradedPowerEquiv σ I J hIJ e n) (by
    ext y
    rw [Submodule.mem_map_equiv]
    exact semilinear_symm_mem_power_iff σ I J hIJ e (n + 1) y.val)

private lemma gradedPieceEquiv_mk (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ.toRingHom = J) (e : M ≃ₛₗ[σ.toRingHom] N) (n : ℕ)
    (x : AssociatedGraded.power (M := M) I n) :
    gradedPieceEquiv σ I J hIJ e n (AssociatedGraded.mk I n x) =
      AssociatedGraded.mk J n (gradedPowerEquiv σ I J hIJ e n x) := rfl

private lemma closure_eq_top_of_addEquiv {A B : Type*}
    [AddGroup A] [AddGroup B] (e : A ≃+ B) (s : Set A) (t : Set B)
    (hs : AddSubgroup.closure s = ⊤) (hst : ∀ x ∈ s, e x ∈ t) :
    AddSubgroup.closure t = ⊤ := by
  have hle : AddSubgroup.closure s ≤ (AddSubgroup.closure t).comap e.toAddMonoidHom :=
    (AddSubgroup.closure_le _).mpr fun x hx => AddSubgroup.subset_closure (hst x hx)
  rw [hs] at hle
  apply top_unique
  intro y _
  have hh := hle (show e.symm y ∈ (⊤ : AddSubgroup A) from trivial)
  change e (e.symm y) ∈ AddSubgroup.closure t at hh
  simpa only [e.apply_symm_apply] using hh

private lemma finite_generators_transport (σ : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ.toRingHom = J) (e : M ≃ₛₗ[σ.toRingHom] N)
    (h : ∃ G : Finset M, ∀ n : ℕ,
      AddSubgroup.closure
        {x : AssociatedGraded.piece (M := M) I n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := R) I n,
            x = gradedScale I n a s} = ⊤) :
    ∃ G : Finset N, ∀ n : ℕ,
      AddSubgroup.closure
        {x : AssociatedGraded.piece (M := N) J n |
          ∃ s ∈ G, ∃ a : AssociatedGraded.power (M := S) J n,
            x = gradedScale J n a s} = ⊤ := by
  classical
  obtain ⟨G, hG⟩ := h
  refine ⟨G.image e, fun n => ?_⟩
  apply closure_eq_top_of_addEquiv (gradedPieceEquiv σ I J hIJ e n).toAddEquiv _ _ (hG n)
  rintro _ ⟨s, hs, a, rfl⟩
  have ha : σ a.val ∈ AssociatedGraded.power (M := S) J n := by
    simp only [AssociatedGraded.ring_power_eq]
    rw [← hIJ, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (by simpa [AssociatedGraded.ring_power_eq] using a.property)
  refine ⟨e s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ⟨σ a.val, ha⟩, ?_⟩
  exact (gradedPieceEquiv_mk σ I J hIJ e n (associatedGradedPowerSaturation I n a s)).trans
    (gradedScale_mk J n ⟨σ (a : R), ha⟩ (e s) _ (e.map_smulₛₗ a.val s))

end FiniteGenerationTransport

end Stacks.Coherent

end

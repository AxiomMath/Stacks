module

public import Mathlib.Algebra.Polynomial.Module.TensorProduct
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Kaehler.Polynomial
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexedUniversalProperty
public import StacksFrontier.RingTheory.DividedPowers.Ring
import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.FirstOrderExtension
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PolynomialRing

/-!
# Divided power differentials of a divided power polynomial algebra

For a divided power ring `(B, I, δ)` over `A` and the divided power polynomial algebra
`P = B⟨x_w : w ∈ W⟩` on an arbitrary family of variables, with divided power ideal `IP + P₊`,

`Ω¹_{P/A,δ'} = (P ⊗_B Ω¹_{B/A,δ}) ⊕ ⨁_w P · d x_w`,

as a canonical equivalence characterized by its values on the differentials of coefficients and
of variables.  Divided power derivations of `P` into a module `N` are identified with sections of
the square-zero divided power thickening `P ⊕ N`, to which the universal property of `P` applies,
so a divided power derivation of `P` is free data on the coefficients and on the variables.

## Main results

* `Crystalline.dividedPowerDifferentialsDividedPowerPolynomialEquiv` — the divided power
  polynomial formula.

## References

* [Stacks Project, Tag 07HS](https://stacks.math.columbia.edu/tag/07HS)
-/

@[expose] public section

namespace Crystalline

section DividedPowerPolynomial

open DividedPowers
open scoped TensorProduct

universe uA uB uW uN

/-- A module over a commutative ring is a central-scalar module over the opposite ring. -/
private theorem exists_isCentralScalar_mulOpposite (R M : Type*) [CommRing R] [AddCommGroup M]
    [Module R M] : ∃ i : Module Rᵐᵒᵖ M, @IsCentralScalar R M _ i.toSMul :=
  by
  let i : Module Rᵐᵒᵖ M := Module.compHom M (RingEquiv.toOpposite R).symm.toRingHom
  refine ⟨i, ⟨fun r z => ?_⟩⟩
  change (RingEquiv.toOpposite R).symm (MulOpposite.op r) • z = r • z
  simp [RingEquiv.toOpposite_symm_apply]

/-- The inclusion `R → R ⊕ M` of the square-zero extension, read on pairs. -/
private theorem trivSqZeroExt_algebraMap_pair {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (a : R) :
    (AddEquiv.refl (TrivSqZeroExt R M) : TrivSqZeroExt R M ≃+ R × M)
      (algebraMap R (TrivSqZeroExt R M) a) = (a, 0) := by
  rw [TrivSqZeroExt.algebraMap_eq_inl]
  rfl

/-- The product of two pairs in the square-zero extension. -/
private theorem trivSqZeroExt_pair_mul {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x y : R) (m n : M) :
    (show TrivSqZeroExt R M from (x, m)) * (show TrivSqZeroExt R M from (y, n)) =
      show TrivSqZeroExt R M from (x * y, x • n + y • m) :=
  TrivSqZeroExt.ext rfl (by rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul]; rfl)

/-- The product of the square-zero extension, read on pairs. -/
private theorem trivSqZeroExt_mul_pair {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (b b' : TrivSqZeroExt R M) :
    (AddEquiv.refl (TrivSqZeroExt R M) : TrivSqZeroExt R M ≃+ R × M) (b * b') =
      (b.fst * b'.fst, b.fst • b'.snd + b'.fst • b.snd) :=
  Prod.ext (TrivSqZeroExt.fst_mul _ _) (by
    change (b * b').snd = b.fst • b'.snd + b'.fst • b.snd
    rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul])

section UniversalDerivations

variable (B : DividedPowerRing.{uB}) (W : Type uW) (N : Type uN) [AddCommGroup N]
  [Module (setIndexedDividedPowerPolynomialAlgebra B W) N]

/-- A divided power derivation of `B⟨x_w⟩` into a module exists for every prescribed
derivation on the coefficients obeying the divided power chain rule and every prescribed
family of values on the variables. -/
private theorem exists_dividedPowerPolynomialDerivation
    (dB : (B : Type uB) →+ N)
    (hleib : ∀ b b' : B, dB (b * b') =
      algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b • dB b' +
        algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b' • dB b)
    (hdp : ∀ (k : ℕ), ∀ x ∈ B.ideal, dB (B.dividedPowers.dpow (k + 1) x) =
      algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)
        (B.dividedPowers.dpow k x) • dB x)
    (v : W → N) :
    ∃ D : setIndexedDividedPowerPolynomialAlgebra B W →+ N,
      (∀ x y, D (x * y) = x • D y + y • D x) ∧
      (∀ (k : ℕ), ∀ x ∈ dividedPowerPolynomialIdeal B.ideal W,
        D ((setIndexedDividedPowerPolynomialDividedPowers B W).dpow (k + 1) x) =
          (setIndexedDividedPowerPolynomialDividedPowers B W).dpow k x • D x) ∧
      (∀ b : B, D (algebraMap (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) b) = dB b) ∧
      (∀ w : W, D (dividedPowerPolynomialVariable (B : Type uB) w) = v w) := by
  classical
  set P := setIndexedDividedPowerPolynomialAlgebra B W with hPdef
  set JP := dividedPowerPolynomialIdeal B.ideal W with hJPdef
  set dP := setIndexedDividedPowerPolynomialDividedPowers B W with hdPdef
  obtain ⟨_, _⟩ := exists_isCentralScalar_mulOpposite P N
  let T := TrivSqZeroExt P N
  let JT : Ideal T := Ideal.comap (TrivSqZeroExt.fstHom P P N).toRingHom JP
  let e : T ≃+ P × N := AddEquiv.refl _
  have hmem : ∀ b : T, b ∈ JT ↔ (e b).1 ∈ JP := fun _ => Iff.rfl
  have hiota : ∀ a : P, e (algebraMap P T a) = (a, 0) := trivSqZeroExt_algebraMap_pair
  have hmulT : ∀ b b' : T, e (b * b') =
      ((e b).1 * (e b').1, (e b).1 • (e b').2 + (e b').1 • (e b).2) := trivSqZeroExt_mul_pair
  let gT := squareZeroDividedPowers dP e JT (algebraMap P T) hiota hmulT hmem
  let C : DividedPowerRing := ⟨T, JT, gT⟩
  have hdB_one : dB 1 = 0 := by simpa using hleib 1 1
  let fRing : (B : Type uB) →+* T :=
    { toFun := fun b => (algebraMap (B : Type uB) P b, dB b)
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · change algebraMap (B : Type uB) P 1 = 1
          rw [map_one]
        · change dB 1 = 0
          exact hdB_one
      map_mul' := fun b b' => by rw [trivSqZeroExt_pair_mul, map_mul, hleib]
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_
        · change algebraMap (B : Type uB) P 0 = 0
          rw [map_zero]
        · change dB 0 = 0
          exact dB.map_zero
      map_add' := by
        intro b b'
        refine TrivSqZeroExt.ext ?_ ?_
        · change algebraMap (B : Type uB) P (b + b') =
            algebraMap (B : Type uB) P b + algebraMap (B : Type uB) P b'
          rw [map_add]
        · change dB (b + b') = dB b + dB b'
          exact dB.map_add b b' }
  have hcoeffDP := setIndexedDividedPowerPolynomialCoefficient_isDPMorphism B W
  have hfmemJT : ∀ x ∈ B.ideal, fRing x ∈ JT := by
    intro x hx
    exact hcoeffDP.ideal_comp (Ideal.mem_map_of_mem _ hx)
  have hfDP : DividedPowers.IsDPMorphism B.dividedPowers gT fRing := by
    refine ⟨Ideal.map_le_iff_le_comap.mpr fun x hx => hfmemJT x hx, ?_⟩
    intro n x hx
    have hxJ : fRing x ∈ JT := hfmemJT x hx
    match n with
    | 0 =>
        rw [show gT.dpow 0 (fRing x) = 1 from squareZeroDpow_zero dP e JT hxJ,
          B.dividedPowers.dpow_zero hx, map_one]
    | k + 1 =>
        rw [show gT.dpow (k + 1) (fRing x) =
            e.symm (dP.dpow (k + 1) (e (fRing x)).1,
              dP.dpow k (e (fRing x)).1 • (e (fRing x)).2) from
          squareZeroDpow_succ dP e JT k hxJ]
        refine TrivSqZeroExt.ext ?_ ?_
        · change dP.dpow (k + 1) (algebraMap (B : Type uB) P x) =
            algebraMap (B : Type uB) P (B.dividedPowers.dpow (k + 1) x)
          exact hcoeffDP.dpow_comp x hx
        · change dP.dpow k (algebraMap (B : Type uB) P x) • dB x =
            dB (B.dividedPowers.dpow (k + 1) x)
          rw [hdp k x hx, hcoeffDP.dpow_comp x hx]
  let fDP : DividedPowers.DPMorphism B.dividedPowers C.dividedPowers :=
    DividedPowers.DPMorphism.mk' hfDP
  let kVar : W → C.ideal := fun w =>
    ⟨(dividedPowerPolynomialVariable (B : Type uB) w, v w),
      (hmem _).2 (variable_mem_polynomialIdeal B w)⟩
  obtain ⟨phi, ⟨hphiC, hphiV⟩, -⟩ :=
    existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B W C fDP kVar
  -- the first component of `phi` is the identity
  let piRing : T →+* P := (TrivSqZeroExt.fstHom P P N).toRingHom
  have hpiDP : DividedPowers.IsDPMorphism gT dP piRing :=
    isDPMorphism_squareZero_fst dP e JT (algebraMap P T) hiota hmulT hmem piRing
      (fun _ => rfl)
  let PRing : DividedPowerRing := ⟨P, JP, dP⟩
  let psi : DividedPowers.DPMorphism dP PRing.dividedPowers :=
    (DividedPowers.DPMorphism.mk' hpiDP).comp phi
  have hphiCval : ∀ b : B, phi (algebraMap (B : Type uB) P b) = fRing b := fun b =>
    congrArg (fun q : DividedPowers.DPMorphism B.dividedPowers C.dividedPowers =>
      q.toRingHom b) hphiC
  have hfst : ∀ x : P, (phi x).fst = x := by
    have hpsi : psi = DividedPowers.DPMorphism.id dP := by
      refine (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B W PRing
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism B W)
        (fun w => ⟨dividedPowerPolynomialVariable (B : Type uB) w,
          variable_mem_polynomialIdeal B w⟩)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · refine DFunLike.ext _ _ fun b => ?_
        change piRing (phi (algebraMap (B : Type uB) P b)) = algebraMap (B : Type uB) P b
        rw [hphiCval b]
        rfl
      · intro w
        change piRing (phi (dividedPowerPolynomialVariable (B : Type uB) w)) = _
        rw [hphiV w]
        rfl
      · refine DFunLike.ext _ _ fun b => ?_
        rfl
      · intro w
        rfl
    intro x
    have h := congrArg (fun q : DividedPowers.DPMorphism dP PRing.dividedPowers =>
      q.toRingHom x) hpsi
    exact h
  refine ⟨{ toFun := fun x => (phi x).snd
            map_zero' := by
              change (phi.toRingHom 0).snd = 0
              rw [map_zero]; rfl
            map_add' := by
              intro x y
              change (phi.toRingHom (x + y)).snd = (phi.toRingHom x).snd + (phi.toRingHom y).snd
              rw [map_add]; rfl }, ?_, ?_, ?_, ?_⟩
  · intro x y
    change (phi.toRingHom (x * y)).snd = x • (phi.toRingHom y).snd + y • (phi.toRingHom x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, op_smul_eq_smul]
    change (phi x).fst • (phi y).snd + (phi y).fst • (phi x).snd = _
    rw [hfst x, hfst y]
    rfl
  · intro k x hx
    change (phi.toRingHom (dP.dpow (k + 1) x)).snd = dP.dpow k x • (phi.toRingHom x).snd
    rw [← phi.dpow_comp x hx,
      show gT.dpow (k + 1) (phi.toRingHom x) =
          e.symm (dP.dpow (k + 1) (e (phi.toRingHom x)).1,
            dP.dpow k (e (phi.toRingHom x)).1 • (e (phi.toRingHom x)).2) from
        squareZeroDpow_succ dP e JT k
          ((hmem _).2 (by rw [show (e (phi.toRingHom x)).1 = x from hfst x]; exact hx))]
    change dP.dpow k (phi x).fst • (phi x).snd = _
    rw [hfst x]
    rfl
  · intro b
    change (phi.toRingHom (algebraMap (B : Type uB) P b)).snd = dB b
    rw [show phi.toRingHom (algebraMap (B : Type uB) P b) = fRing b from hphiCval b]
    rfl
  · intro w
    change (phi.toRingHom (dividedPowerPolynomialVariable (B : Type uB) w)).snd = v w
    rw [show phi.toRingHom (dividedPowerPolynomialVariable (B : Type uB) w) = (kVar w : T) from
      hphiV w]
    rfl

/-- A divided power derivation of `B⟨x_w⟩` is determined by its restriction to the
coefficients together with its values on the variables. -/
private theorem dividedPowerPolynomialDerivation_ext
    (D E : setIndexedDividedPowerPolynomialAlgebra B W →+ N)
    (hD : ∀ x y, D (x * y) = x • D y + y • D x)
    (hE : ∀ x y, E (x * y) = x • E y + y • E x)
    (hDdp : ∀ (k : ℕ), ∀ x ∈ dividedPowerPolynomialIdeal B.ideal W,
      D ((setIndexedDividedPowerPolynomialDividedPowers B W).dpow (k + 1) x) =
        (setIndexedDividedPowerPolynomialDividedPowers B W).dpow k x • D x)
    (hEdp : ∀ (k : ℕ), ∀ x ∈ dividedPowerPolynomialIdeal B.ideal W,
      E ((setIndexedDividedPowerPolynomialDividedPowers B W).dpow (k + 1) x) =
        (setIndexedDividedPowerPolynomialDividedPowers B W).dpow k x • E x)
    (hcoeff : ∀ b : B, D (algebraMap (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) b) =
      E (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b))
    (hvar : ∀ w : W, D (dividedPowerPolynomialVariable (B : Type uB) w) =
      E (dividedPowerPolynomialVariable (B : Type uB) w)) :
    ∀ x, D x = E x := by
  classical
  set P := setIndexedDividedPowerPolynomialAlgebra B W with hPdef
  set JP := dividedPowerPolynomialIdeal B.ideal W with hJPdef
  set dP := setIndexedDividedPowerPolynomialDividedPowers B W with hdPdef
  obtain ⟨_, _⟩ := exists_isCentralScalar_mulOpposite P N
  let T := TrivSqZeroExt P N
  let JT : Ideal T := Ideal.comap (TrivSqZeroExt.fstHom P P N).toRingHom JP
  let e : T ≃+ P × N := AddEquiv.refl _
  have hmem : ∀ b : T, b ∈ JT ↔ (e b).1 ∈ JP := fun _ => Iff.rfl
  have hiota : ∀ a : P, e (algebraMap P T a) = (a, 0) := trivSqZeroExt_algebraMap_pair
  have hmulT : ∀ b b' : T, e (b * b') =
      ((e b).1 * (e b').1, (e b).1 • (e b').2 + (e b').1 • (e b).2) := trivSqZeroExt_mul_pair
  let gT := squareZeroDividedPowers dP e JT (algebraMap P T) hiota hmulT hmem
  let C : DividedPowerRing := ⟨T, JT, gT⟩
  have hgraph : ∀ F : P →+ N, (∀ x y, F (x * y) = x • F y + y • F x) →
      (∀ (k : ℕ), ∀ x ∈ JP, F (dP.dpow (k + 1) x) = dP.dpow k x • F x) →
      ∃ m : DividedPowers.DPMorphism dP C.dividedPowers, ∀ x, m.toRingHom x = (x, F x) := by
    intro F hF hFdp
    have hF1 : F 1 = 0 := by simpa using hF 1 1
    let g : P →+* T :=
      { toFun := fun x => (x, F x)
        map_one' := TrivSqZeroExt.ext rfl hF1
        map_mul' := fun x y => by rw [trivSqZeroExt_pair_mul, hF]
        map_zero' := TrivSqZeroExt.ext rfl F.map_zero
        map_add' := fun x y => TrivSqZeroExt.ext rfl (F.map_add x y) }
    exact ⟨DividedPowers.DPMorphism.mk' (isDPMorphism_squareZero_of_graph dP e JT
      (algebraMap P T) hiota hmulT hmem g F (fun _ => rfl) hFdp), fun _ => rfl⟩
  obtain ⟨mD, hmD⟩ := hgraph D hD hDdp
  obtain ⟨mE, hmE⟩ := hgraph E hE hEdp
  let kVar : W → C.ideal := fun w =>
    ⟨mD.toRingHom (dividedPowerPolynomialVariable (B : Type uB) w),
      (hmem _).2 (by rw [hmD]; exact variable_mem_polynomialIdeal B w)⟩
  have hext : ∀ x, D x = E x → mE.toRingHom x = mD.toRingHom x := fun x h => by
    rw [hmD, hmE]
    exact TrivSqZeroExt.ext rfl h.symm
  have hme : mD = mE :=
    (existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial B W C
      (mD.comp (setIndexedDividedPowerPolynomialCoefficientDPMorphism B W)) kVar).unique
      ⟨rfl, fun w => rfl⟩
      ⟨DFunLike.ext _ _ fun b => hext _ (hcoeff b), fun w => hext _ (hvar w)⟩
  intro x
  have h' : mD.toRingHom x = mE.toRingHom x := congrArg (fun q => q.toRingHom x) hme
  rw [hmD, hmE] at h'
  exact (TrivSqZeroExt.ext_iff.mp h').2

end UniversalDerivations

/-- The divided power polynomial algebra `B⟨x_w : w ∈ W⟩` over a divided power ring
`(B, I, δ)`, bundled with its divided power ideal `I·B⟨x_w⟩ + B⟨x_w⟩₊` as a divided power ring. -/
private noncomputable abbrev dividedPowerPolynomialDPRing
    (B : DividedPowerRing.{uB}) (W : Type uW) : DividedPowerRing.{max uB uW} :=
  DividedPowerRing.of (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerPolynomialIdeal B.ideal W)
    (setIndexedDividedPowerPolynomialDividedPowers B W)

/-- The universal divided power differential is additive. -/
private lemma dividedPowerDifferential_map_add {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] {J : Ideal C} (hJ : DividedPowers J) (x y : C) :
    dividedPowerDifferential (A := A) hJ (x + y) =
      dividedPowerDifferential (A := A) hJ x + dividedPowerDifferential (A := A) hJ y := by
  simp only [dividedPowerDifferential, map_add]

/-- The Leibniz rule for the universal divided power differential. -/
private lemma dividedPowerDifferential_map_mul {A C : Type*} [CommRing A] [CommRing C]
    [Algebra A C] {J : Ideal C} (hJ : DividedPowers J) (x y : C) :
    dividedPowerDifferential (A := A) hJ (x * y) =
      x • dividedPowerDifferential (A := A) hJ y + y • dividedPowerDifferential (A := A) hJ x := by
  simp only [dividedPowerDifferential, Derivation.leibniz, map_add, map_smul]


/-- The divided power derivation of the coefficients `B` into the divided power
differentials of `B⟨x_w⟩`, sending `b` to the universal differential of its image. -/
private noncomputable def dividedPowerPolynomialCoefficientDerivation
    {A : Type uA} [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW) :
    DividedPowerDerivation A B (algebraMap A B)
      (dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W)) := by
  let P := setIndexedDividedPowerPolynomialAlgebra B W
  let dP := setIndexedDividedPowerPolynomialDividedPowers B W
  let M := dividedPowerDifferentials (A := A) dP
  letI : LinearMap.CompatibleSMul Ω[P⁄A] M B P := ⟨fun F b x ↦ by
    rw [← IsScalarTower.algebraMap_smul P b x, map_smul,
      IsScalarTower.algebraMap_smul P b (F x)]⟩
  let q : Ω[P⁄A] →ₗ[B] M :=
    ((dividedPowerDifferentialRelations (A := A) dP).mkQ).restrictScalars B
  let D : Derivation A B M :=
    q.compDer ((KaehlerDifferential.map A A B P).compDer (KaehlerDifferential.D A B))
  have hc := setIndexedDividedPowerPolynomialCoefficient_isDPMorphism B W
  have hgen (x : B) (hx : x ∈ B.ideal) (n : ℕ) :
      D (B.dividedPowers.dpow (n + 1) x) = B.dividedPowers.dpow n x • D x := by
    dsimp [D]
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D]
    rw [← hc.dpow_comp (n := n + 1) x hx]
    have hp := dividedPowerDifferential_dpow (A := A) dP
      ⟨algebraMap (B : Type uB) P x, hc.ideal_comp (Ideal.mem_map_of_mem _ hx)⟩ n
    change q (KaehlerDifferential.D A P
        (dP.dpow (n + 1) (algebraMap (B : Type uB) P x))) =
      dP.dpow n (algebraMap (B : Type uB) P x) •
        q (KaehlerDifferential.D A P (algebraMap (B : Type uB) P x)) at hp
    rw [hp, hc.dpow_comp (n := n) x hx]
    exact IsScalarTower.algebraMap_smul P (B.dividedPowers.dpow n x)
      (q (KaehlerDifferential.D A P (algebraMap (B : Type uB) P x)))
  refine { toDerivation := D.restrictScalars ℤ, map_ringHom' := ?_, map_dpow' := ?_ }
  · intro a
    exact D.map_algebraMap a
  · intro n hn x hx
    cases n with
    | zero => omega
    | succ n => simpa using hgen x hx n


section ComparisonMaps
variable {A : Type uA} [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- The `B`-linear comparison `Ω¹_{B/A,δ} → Ω¹_{B⟨x_w⟩/A,δ'}` induced by the inclusion
of the coefficients. -/
private noncomputable def dividedPowerPolynomialCoefficientLift :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[B]
      dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W) :=
  Classical.choose (dividedPowerDifferentials_lift B
    (dividedPowerPolynomialCoefficientDerivation (A := A) B W))

/-- The coefficient comparison carries the universal differential of `b` to the universal
differential of the image of `b`. -/
private lemma dividedPowerPolynomialCoefficientLift_apply (b : B) :
    dividedPowerPolynomialCoefficientLift (A := A) B W
        (dividedPowerDifferential (A := A) B.dividedPowers b) =
      dividedPowerDifferential (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W)
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b) := by
  have h := (Classical.choose_spec (dividedPowerDifferentials_lift B
    (dividedPowerPolynomialCoefficientDerivation (A := A) B W))).1 b
  refine h.trans ?_
  simp [dividedPowerPolynomialCoefficientDerivation, dividedPowerDifferential,
    KaehlerDifferential.map_D]

/-- The scalar extension `B⟨x_w⟩ ⊗_B Ω¹_{B/A,δ} → Ω¹_{B⟨x_w⟩/A,δ'}` of the coefficient
comparison. -/
private noncomputable def dividedPowerPolynomialTensorLift :
    (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
        dividedPowerDifferentials (A := A) B.dividedPowers) →ₗ[
      setIndexedDividedPowerPolynomialAlgebra B W]
      dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W) := by
  let P := setIndexedDividedPowerPolynomialAlgebra B W
  let M := dividedPowerDifferentials (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W)
  let c := dividedPowerPolynomialCoefficientLift (A := A) B W
  let f : P →ₗ[P] (dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[B] M) :=
    { toFun := fun p =>
        { toFun := fun om => p • c om
          map_add' := by intro x y; simp [smul_add, map_add]
          map_smul' := by
            intro b om
            change p • c (b • om) = b • (p • c om)
            rw [c.map_smul]
            exact smul_comm p b (c om) }
      map_add' := by intro p q; ext om; simp [add_smul]
      map_smul' := by intro p q; ext om; simp [mul_smul] }
  exact TensorProduct.AlgebraTensorModule.lift f

/-- The scalar extension sends a pure tensor to the comparison of its one-form, scaled by
the polynomial factor. -/
private lemma dividedPowerPolynomialTensorLift_tmul
    (p : setIndexedDividedPowerPolynomialAlgebra B W)
    (om : dividedPowerDifferentials (A := A) B.dividedPowers) :
    dividedPowerPolynomialTensorLift (A := A) B W (p ⊗ₜ[B] om) =
      p • dividedPowerPolynomialCoefficientLift (A := A) B W om :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ _ _

/-- The map `(B⟨x_w⟩ ⊗_B Ω¹_{B/A,δ}) × (W →₀ B⟨x_w⟩) → Ω¹_{B⟨x_w⟩/A,δ'}` which extends the
coefficient comparison and sends the `w`-th basis vector of the second summand to `d x_w`. -/
private noncomputable def dividedPowerPolynomialInverseMap :
    ((setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
          dividedPowerDifferentials (A := A) B.dividedPowers) ×
        (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)) →ₗ[
      setIndexedDividedPowerPolynomialAlgebra B W]
      dividedPowerDifferentials (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W) := by
  let c := dividedPowerPolynomialTensorLift (A := A) B W
  let dx := Finsupp.linearCombination (setIndexedDividedPowerPolynomialAlgebra B W)
    (fun w : W => dividedPowerDifferential (A := A)
      (setIndexedDividedPowerPolynomialDividedPowers B W)
      (dividedPowerPolynomialVariable (B : Type uB) w))
  exact
    { toFun := fun x => c x.1 + dx x.2
      map_add' := by
        intro x y
        change c (x.1 + y.1) + dx (x.2 + y.2) = (c x.1 + dx x.2) + (c y.1 + dx y.2)
        rw [map_add, map_add]
        exact add_add_add_comm _ _ _ _
      map_smul' := by
        intro p x
        change c (p • x.1) + dx (p • x.2) = p • (c x.1 + dx x.2)
        rw [map_smul, map_smul, smul_add] }

end ComparisonMaps

section ForwardMap
variable {A : Type uA} [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- There is a `B⟨x_w⟩`-linear map out of `Ω¹_{B⟨x_w⟩/A,δ'}` carrying the differential of a
coefficient `b` to `1 ⊗ d b` and the differential of a variable `x_w` to the `w`-th basis
vector. -/
private theorem exists_dividedPowerPolynomialForwardMap :
    ∃ F : dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) →ₗ[
        setIndexedDividedPowerPolynomialAlgebra B W]
        ((setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers) ×
          (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)),
      (∀ b : B, F (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)) =
        (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b, 0)) ∧
      (∀ w : W, F (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariable (B : Type uB) w)) = (0, Finsupp.single w 1)) := by
  classical
  set P := setIndexedDividedPowerPolynomialAlgebra B W with hPdef
  set dP := setIndexedDividedPowerPolynomialDividedPowers B W with hdPdef
  set OmB := dividedPowerDifferentials (A := A) B.dividedPowers with hOmB
  set M := ((P ⊗[B] OmB) × (W →₀ P)) with hM
  have htmul : ∀ (x : B) (om : OmB),
      (algebraMap (B : Type uB) P x) • (1 ⊗ₜ[B] om : P ⊗[B] OmB) = 1 ⊗ₜ[B] (x • om) := by
    intro x om
    rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  let dB : (B : Type uB) →+ M := AddMonoidHom.mk'
    (fun b => (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b, 0))
    (fun b b' => by
      refine Prod.ext ?_ (add_zero _).symm
      change (1 : P) ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers (b + b') = _
      rw [dividedPowerDifferential_map_add, TensorProduct.tmul_add]
      rfl)
  have hleib : ∀ b b' : B, dB (b * b') =
      algebraMap (B : Type uB) P b • dB b' + algebraMap (B : Type uB) P b' • dB b := by
    intro b b'
    refine Prod.ext ?_ (by
      change (0 : W →₀ P) = algebraMap (B : Type uB) P b • (0 : W →₀ P) +
        algebraMap (B : Type uB) P b' • (0 : W →₀ P)
      rw [smul_zero, smul_zero, add_zero])
    change (1 : P) ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers (b * b') =
      algebraMap (B : Type uB) P b • ((1 : P) ⊗ₜ[B]
          dividedPowerDifferential (A := A) B.dividedPowers b') +
        algebraMap (B : Type uB) P b' • ((1 : P) ⊗ₜ[B]
          dividedPowerDifferential (A := A) B.dividedPowers b)
    rw [htmul, htmul, dividedPowerDifferential_map_mul, TensorProduct.tmul_add]
  have hdp : ∀ (k : ℕ), ∀ x ∈ B.ideal, dB (B.dividedPowers.dpow (k + 1) x) =
      algebraMap (B : Type uB) P (B.dividedPowers.dpow k x) • dB x := by
    intro k x hx
    refine Prod.ext ?_ (by
      change (0 : W →₀ P) =
        algebraMap (B : Type uB) P (B.dividedPowers.dpow k x) • (0 : W →₀ P)
      rw [smul_zero])
    change (1 : P) ⊗ₜ[B]
        dividedPowerDifferential (A := A) B.dividedPowers (B.dividedPowers.dpow (k + 1) x) =
      algebraMap (B : Type uB) P (B.dividedPowers.dpow k x) • ((1 : P) ⊗ₜ[B]
        dividedPowerDifferential (A := A) B.dividedPowers x)
    rw [htmul, dividedPowerDifferential_dpow (A := A) B.dividedPowers ⟨x, hx⟩ k]
  obtain ⟨D, hDleib, hDdp, hDcoeff, hDvar⟩ :=
    exists_dividedPowerPolynomialDerivation B W M dB hleib hdp
      (fun w => ((0 : P ⊗[B] OmB), Finsupp.single w 1))
  have hDA : ∀ a : A, D (algebraMap A P a) = 0 := by
    intro a
    have h : algebraMap A P a = algebraMap (B : Type uB) P (algebraMap A (B : Type uB) a) :=
      (IsScalarTower.algebraMap_apply A (B : Type uB) P a)
    rw [h, hDcoeff]
    refine Prod.ext ?_ rfl
    change (1 : P) ⊗ₜ[B]
      dividedPowerDifferential (A := A) B.dividedPowers (algebraMap A (B : Type uB) a) = 0
    rw [show dividedPowerDifferential (A := A) B.dividedPowers
        (algebraMap A (B : Type uB) a) = 0 by
      simp only [dividedPowerDifferential, Derivation.map_algebraMap, map_zero],
      TensorProduct.tmul_zero]
  let DD : DividedPowerDerivation A (dividedPowerPolynomialDPRing B W) (algebraMap A P) M :=
    { toDerivation :=
        { toFun := fun x => D x
          map_add' := D.map_add
          map_smul' := fun z x => map_zsmul D z x
          map_one_eq_zero' := by
            have h := hDcoeff 1
            rw [map_one] at h
            refine h.trans ?_
            refine Prod.ext ?_ rfl
            change (1 : P) ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers 1 = 0
            rw [show dividedPowerDifferential (A := A) B.dividedPowers 1 = 0 by
              simp only [dividedPowerDifferential, Derivation.map_one_eq_zero, map_zero],
              TensorProduct.tmul_zero]
          leibniz' := fun x y => hDleib x y }
      map_ringHom' := hDA
      map_dpow' := by
        intro n hn x hx
        cases n with
        | zero => omega
        | succ n => simpa using hDdp n x hx }
  obtain ⟨F, hF, -⟩ := dividedPowerDifferentials_lift (dividedPowerPolynomialDPRing B W) DD
  exact ⟨F, fun b => (hF _).trans (hDcoeff b), fun w => (hF _).trans (hDvar w)⟩

end ForwardMap

section Decomposition
variable {A : Type uA} [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- The coefficient-and-variables description of the divided power differentials of
`B⟨x_w⟩` is realized by an isomorphism, pinned down by its values on the universal
differentials of coefficients and of variables. -/
public theorem exists_dividedPowerPolynomialDifferentialsEquiv :
    Nonempty { e : dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) ≃ₗ[
        setIndexedDividedPowerPolynomialAlgebra B W]
        ((setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers) ×
          (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)) //
      (∀ b : B, e (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)) =
        (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b, 0)) ∧
      (∀ w : W, e (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariable (B : Type uB) w)) = (0, Finsupp.single w 1)) } := by
  classical
  set P := setIndexedDividedPowerPolynomialAlgebra B W with hPdef
  set dP := setIndexedDividedPowerPolynomialDividedPowers B W with hdPdef
  set OmB := dividedPowerDifferentials (A := A) B.dividedPowers with hOmB
  set OmP := dividedPowerDifferentials (A := A) dP with hOmP
  let F := Classical.choose (exists_dividedPowerPolynomialForwardMap (A := A) B W)
  have hFc := (Classical.choose_spec (exists_dividedPowerPolynomialForwardMap (A := A) B W)).1
  have hFv := (Classical.choose_spec (exists_dividedPowerPolynomialForwardMap (A := A) B W)).2
  let G := dividedPowerPolynomialInverseMap (A := A) B W
  have hGc : ∀ b : B, G (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b, 0) =
      dividedPowerDifferential (A := A) dP (algebraMap (B : Type uB) P b) := by
    intro b
    change dividedPowerPolynomialTensorLift (A := A) B W
        (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b) +
      Finsupp.linearCombination P (fun w : W => dividedPowerDifferential (A := A) dP
        (dividedPowerPolynomialVariable (B : Type uB) w)) 0 = _
    rw [map_zero, add_zero, dividedPowerPolynomialTensorLift_tmul,
      dividedPowerPolynomialCoefficientLift_apply, one_smul]
  have hGv : ∀ w : W, G ((0 : P ⊗[B] OmB), Finsupp.single w (1 : P)) =
      dividedPowerDifferential (A := A) dP (dividedPowerPolynomialVariable (B : Type uB) w) := by
    intro w
    change dividedPowerPolynomialTensorLift (A := A) B W 0 +
      Finsupp.linearCombination P (fun w : W => dividedPowerDifferential (A := A) dP
        (dividedPowerPolynomialVariable (B : Type uB) w)) (Finsupp.single w 1) = _
    rw [map_zero, zero_add, Finsupp.linearCombination_single, one_smul]
  -- `G ∘ F` is the identity
  have hdPdpow : ∀ (k : ℕ), ∀ x ∈ dividedPowerPolynomialIdeal B.ideal W,
      dividedPowerDifferential (A := A) dP (dP.dpow (k + 1) x) =
        dP.dpow k x • dividedPowerDifferential (A := A) dP x := by
    intro k x hx
    exact dividedPowerDifferential_dpow (A := A) dP ⟨x, hx⟩ k
  let dPadd : P →+ OmP :=
    AddMonoidHom.mk' (dividedPowerDifferential (A := A) dP) (dividedPowerDifferential_map_add dP)
  let L : OmP →ₗ[P] OmP := G ∘ₗ F
  let E : P →+ OmP := L.toAddMonoidHom.comp dPadd
  have hGF : ∀ q : P, G (F (dividedPowerDifferential (A := A) dP q)) =
      dividedPowerDifferential (A := A) dP q := by
    have hE := dividedPowerPolynomialDerivation_ext B W OmP E dPadd
      (fun x y => by
        change L (dividedPowerDifferential (A := A) dP (x * y)) = _
        rw [dividedPowerDifferential_map_mul, map_add, map_smul, map_smul]
        rfl)
      (dividedPowerDifferential_map_mul dP)
      (fun k x hx => by
        change L (dividedPowerDifferential (A := A) dP (dP.dpow (k + 1) x)) = _
        rw [hdPdpow k x hx, map_smul]
        rfl)
      hdPdpow
      (fun b => by
        change L (dividedPowerDifferential (A := A) dP
          (algebraMap (B : Type uB) P b)) = _
        change G (F (dividedPowerDifferential (A := A) dP
          (algebraMap (B : Type uB) P b))) = _
        rw [hFc b, hGc b]
        rfl)
      (fun w => by
        change L (dividedPowerDifferential (A := A) dP
          (dividedPowerPolynomialVariable (B : Type uB) w)) = _
        change G (F (dividedPowerDifferential (A := A) dP
          (dividedPowerPolynomialVariable (B : Type uB) w))) = _
        rw [hFv w, hGv w]
        rfl)
    exact fun q => hE q
  have hGFid : G ∘ₗ F = LinearMap.id :=
    LinearMap.ext_on_range (dividedPowerDifferentials_span (A := A) dP) hGF
  -- `F ∘ G` is the identity
  have hFcoeffLift : ∀ om : OmB, F (dividedPowerPolynomialCoefficientLift (A := A) B W om) =
      ((1 : P) ⊗ₜ[B] om, 0) := by
    have h : (F.restrictScalars B).comp
        ((dividedPowerPolynomialCoefficientLift (A := A) B W).restrictScalars B) =
        ({ toFun := fun om : OmB => ((1 : P) ⊗ₜ[B] om, (0 : W →₀ P))
           map_add' := fun x y => by
             refine Prod.ext ?_ (add_zero _).symm
             change (1 : P) ⊗ₜ[B] (x + y) = (1 : P) ⊗ₜ[B] x + (1 : P) ⊗ₜ[B] y
             rw [TensorProduct.tmul_add]
           map_smul' := fun b x => by
             refine Prod.ext ?_ (smul_zero b).symm
             change (1 : P) ⊗ₜ[B] (b • x) = b • ((1 : P) ⊗ₜ[B] x)
             rw [TensorProduct.tmul_smul] } :
          OmB →ₗ[B] ((P ⊗[B] OmB) × (W →₀ P))) := by
      apply LinearMap.ext_on (dividedPowerDifferentials_span (A := A) B.dividedPowers)
      rintro _ ⟨b, rfl⟩
      change F (dividedPowerPolynomialCoefficientLift (A := A) B W
        (dividedPowerDifferential (A := A) B.dividedPowers b)) = _
      rw [dividedPowerPolynomialCoefficientLift_apply, hFc b]
      rfl
    intro om
    exact LinearMap.congr_fun h om
  have hFtensor : ∀ x : P ⊗[B] OmB,
      F (dividedPowerPolynomialTensorLift (A := A) B W x) = (x, 0) := by
    intro x
    induction x with
    | tmul p om =>
        rw [dividedPowerPolynomialTensorLift_tmul, map_smul, hFcoeffLift]
        refine Prod.ext ?_ (smul_zero p)
        change p • ((1 : P) ⊗ₜ[B] om) = p ⊗ₜ[B] om
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
        exact Prod.ext rfl (add_zero _)
  have hFfinsupp : ∀ y : W →₀ P, F (Finsupp.linearCombination P
      (fun w : W => dividedPowerDifferential (A := A) dP
        (dividedPowerPolynomialVariable (B : Type uB) w)) y) = (0, y) := by
    intro y
    have h : F.comp (Finsupp.linearCombination P
        (fun w : W => dividedPowerDifferential (A := A) dP
          (dividedPowerPolynomialVariable (B : Type uB) w))) =
        { toFun := fun y : W →₀ P => ((0 : P ⊗[B] OmB), y)
          map_add' := fun x y => Prod.ext (add_zero _).symm rfl
          map_smul' := fun p x => Prod.ext (smul_zero p).symm rfl } := by
      refine Finsupp.lhom_ext' fun w => LinearMap.ext fun p => ?_
      change F (Finsupp.linearCombination P
        (fun w : W => dividedPowerDifferential (A := A) dP
          (dividedPowerPolynomialVariable (B : Type uB) w)) (Finsupp.single w p)) = _
      rw [Finsupp.linearCombination_single, map_smul, hFv w]
      refine Prod.ext ?_ ?_
      · exact smul_zero p
      · change p • Finsupp.single w (1 : P) = Finsupp.single w p
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact LinearMap.congr_fun h y
  have hFGid : F ∘ₗ G = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    change F (dividedPowerPolynomialTensorLift (A := A) B W x.1 +
      Finsupp.linearCombination P (fun w : W => dividedPowerDifferential (A := A) dP
        (dividedPowerPolynomialVariable (B : Type uB) w)) x.2) = x
    rw [map_add, hFtensor, hFfinsupp]
    refine Prod.ext ?_ ?_
    · change x.1 + 0 = x.1
      rw [add_zero]
    · change (0 : W →₀ P) + x.2 = x.2
      rw [zero_add]
  exact ⟨⟨LinearEquiv.ofLinearMap F G hFGid hGFid, hFc, hFv⟩⟩

/-- **The divided power polynomial decomposition of divided power differentials.**  For a divided
power ring `(B, I, δ)` over `A` and the divided power polynomial algebra `P = B⟨x_w : w ∈ W⟩`
with divided power ideal `IP + P₊`, one has
`Ω¹_{P/A,δ'} = (P ⊗_B Ω¹_{B/A,δ}) ⊕ ⨁_w P · d x_w`, the isomorphism being characterized by its
values on the differentials of coefficients and of variables. -/
@[stacks 07HS "divided_power_polynomial"]
public noncomputable def dividedPowerDifferentialsDividedPowerPolynomialEquiv
    {A : Type uA} [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW) :
    { e : dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) ≃ₗ[
        setIndexedDividedPowerPolynomialAlgebra B W]
        ((setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers) ×
          (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)) //
      (∀ b : B, e (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)) =
        (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b, 0)) ∧
      (∀ w : W, e (dividedPowerDifferential (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W)
          (dividedPowerPolynomialVariable (B : Type uB) w)) = (0, Finsupp.single w 1)) } :=
  Classical.choice (exists_dividedPowerPolynomialDifferentialsEquiv B W)

end Decomposition

end DividedPowerPolynomial

end Crystalline

end

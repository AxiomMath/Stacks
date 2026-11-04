module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.RingTheory.Rig.Category.CompletedBaseChange

/-!
# Completed polynomial presentations

Every object of `Rig.AdicFiniteTypeAlgebra` is a quotient of a completed polynomial algebra
in finitely many variables; over a Noetherian base the objects are Noetherian, quotients of
objects are objects, and the completed polynomial algebras are objects.
-/

@[expose] public section

open CategoryTheory

universe u v u₁ u₂

namespace Rig

section

/-- The image of an extended ideal under an algebra map is the ideal extended to the target. -/
private theorem map_map_algebraMap_algHom {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S) (I : Ideal A) :
    (I.map (algebraMap A R)).map f = I.map (algebraMap A S) := by
  rw [← Ideal.map_coe f (Ideal.map _ I), Ideal.map_map, f.comp_algebraMap]

/-- A presentation of `B` as a quotient of the adic completion of a polynomial algebra in
finitely many variables. -/
public structure CompletedPolynomialPresentation
    {A : Type u} [CommRing A] (I : Ideal A)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) where
  /-- The number of polynomial variables. -/
  variableCount : ℕ
  /-- The ideal by which the completed polynomial algebra is quotiented. -/
  ideal : Ideal (AdicCompletion
    (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin variableCount) A))
    (MvPolynomial (Fin variableCount) A))
  /-- The resulting quotient is the given algebra, as an `A`-algebra. -/
  quotientEquiv :
    let P := AdicCompletion
      (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin variableCount) A))
      (MvPolynomial (Fin variableCount) A)
    (P ⧸ ideal) ≃ₐ[A] B.carrier

/-- **Stacks Project, Tag 0AJP.** An adically complete algebra of finite type modulo a
finitely generated ideal is a quotient of a completed polynomial algebra in finitely many
variables. -/
@[stacks 0AJP "completed_polynomial_presentation"]
public theorem exists_adicCompletion_mvPolynomial_quotient_equiv
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    ∃ r : ℕ,
      let P := AdicCompletion
        (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A)
    ∃ J : Ideal P, Nonempty ((P ⧸ J) ≃ₐ[A] B.carrier) := by
  let L : Ideal B.carrier := I.map (algebraMap A B.carrier)
  let _ : IsAdicComplete L B.carrier := B.isAdicallyComplete
  obtain ⟨r, ⟨P⟩⟩ :=
    (Algebra.FiniteType.iff_exists_generators (R := A ⧸ I) (S := B.reduction)).mp
      B.finiteTypeReduction
  let g : Fin r → B.carrier := fun i =>
    Classical.choose (Ideal.Quotient.mk_surjective (I := L) (P.val i))
  have hg (i : Fin r) : Ideal.Quotient.mk L (g i) = P.val i :=
    Classical.choose_spec (Ideal.Quotient.mk_surjective (I := L) (P.val i))
  let q : MvPolynomial (Fin r) A →ₐ[A] B.carrier := MvPolynomial.aeval g
  have hqL : (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)).map q ≤ L := by
    exact (map_map_algebraMap_algHom q I).le
  let K : Ideal (MvPolynomial (Fin r) A) :=
    I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)
  have hpow (n : ℕ) : K ^ n ≤ (L ^ n).comap q := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hqL n
  let fn (n : ℕ) :
      AdicCompletion K (MvPolynomial (Fin r) A) →ₐ[A] B.carrier ⧸ L ^ n :=
    (Ideal.quotientMapₐ (R₁ := A) (L ^ n) q (hpow n)).comp
      ((AdicCompletion.evalₐ K n).restrictScalars A)
  have hfn : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right hmn)).comp (fn n) = fn m := by
    intro m n hmn
    ext x
    have heval : Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (AdicCompletion.evalₐ K n x) = AdicCompletion.evalₐ K m x := by
      have hh := congrArg (Ideal.Quotient.factor
        (show K ^ m • ⊤ ≤ K ^ m by simp)) (x.property hmn)
      show Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
          (Ideal.Quotient.factor (show K ^ n • ⊤ ≤ K ^ n by simp) (x.val n)) =
        Ideal.Quotient.factor (show K ^ m • ⊤ ≤ K ^ m by simp) (x.val m)
      simpa [Ideal.Quotient.factor_comp_apply, AdicCompletion.transitionMap] using hh
    simp only [fn, AlgHom.comp_apply]
    show Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      ((Ideal.quotientMapₐ (L ^ n) q (hpow n)) (AdicCompletion.evalₐ K n x)) =
      (Ideal.quotientMapₐ (L ^ m) q (hpow m)) (AdicCompletion.evalₐ K m x)
    rw [← heval]
    induction AdicCompletion.evalₐ K n x using Quotient.inductionOn' with
    | _ z => rfl
  let F := IsAdicComplete.liftAlgHom L fn hfn
  have hqred (z : MvPolynomial (Fin r) A) :
      Ideal.Quotient.mk L (q z) =
        MvPolynomial.aeval P.val (MvPolynomial.map (Ideal.Quotient.mk I) z) := by
    calc
      _ = MvPolynomial.aeval (R := A) (fun i => Ideal.Quotient.mk L (g i)) z := by
        simpa [q] using
          (MvPolynomial.comp_aeval_apply (φ := Ideal.Quotient.mkₐ A L) g z)
      _ = MvPolynomial.aeval (R := A) P.val z := by simp only [hg]
      _ = _ := (MvPolynomial.aeval_map_algebraMap (A := A ⧸ I) P.val z).symm
  have hred : Function.Surjective ((Ideal.Quotient.mk L).comp F.toRingHom) := by
    intro b
    obtain ⟨x, hx⟩ := P.aeval_val_surjective b
    obtain ⟨z, hz⟩ := MvPolynomial.map_surjective
      (σ := Fin r) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective x
    refine ⟨AdicCompletion.of K _ z, ?_⟩
    have hFz : Ideal.Quotient.mk L (F (AdicCompletion.of K _ z)) =
        Ideal.Quotient.mk L (q z) := by
      have h := IsAdicComplete.mk_liftAlgHom L fn hfn 1 (AdicCompletion.of K _ z)
      have h' : Ideal.Quotient.mk L (F (AdicCompletion.of K _ z)) =
          Ideal.Quotient.factor (show L ^ 1 ≤ L by simp)
            (fn 1 (AdicCompletion.of K _ z)) :=
        congrArg (Ideal.Quotient.factor (show L ^ 1 ≤ L by simp)) h
      rw [h']
      simp [fn]
    simpa [hFz, hqred, hz] using hx
  have hF : Function.Surjective F.toRingHom := by
    let T := AdicCompletion K (MvPolynomial (Fin r) A)
    let M : Ideal T := K.map (algebraMap (MvPolynomial (Fin r) A) T)
    have hKfg : K.FG := hI.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)
    have : IsAdicComplete K T := AdicCompletion.isAdicComplete hKfg
    have : IsPrecomplete M T :=
      (IsPrecomplete.map_algebraMap_iff).mpr inferInstance
    have hML : M.map F.toRingHom = L := by
      rw [show M = I.map (algebraMap A T) from
        map_map_algebraMap_algHom (IsScalarTower.toAlgHom A (MvPolynomial (Fin r) A) T) I]
      exact map_map_algebraMap_algHom F I
    have : IsHausdorff (M.map F.toRingHom) B.carrier := hML.symm ▸ inferInstance
    apply surjective_of_mk_map_comp_surjective (I := M) (f := F.toRingHom)
    show Function.Surjective ((Ideal.Quotient.mk (M.map F.toRingHom)).comp F.toRingHom)
    rw [hML]
    exact hred
  exact ⟨r, RingHom.ker F.toRingHom, ⟨Ideal.quotientKerAlgEquivOfSurjective hF⟩⟩

/-- A chosen completed polynomial presentation of `B`.  Its `variableCount`, `ideal`, and
`quotientEquiv` fields give the data asserted by
`exists_adicCompletion_mvPolynomial_quotient_equiv`. -/
public noncomputable def completedPolynomialPresentation
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    CompletedPolynomialPresentation I B := by
  let h := exists_adicCompletion_mvPolynomial_quotient_equiv I hI B
  let r := Classical.choose h
  let hJ := Classical.choose_spec h
  let J := Classical.choose hJ
  let e := Classical.choose_spec hJ
  exact ⟨r, J, Classical.choice e⟩

end

section

/-- Every adically complete algebra of finite type modulo an ideal over a Noetherian
commutative ring has a Noetherian underlying ring. -/
@[stacks 0AJQ "noetherian_objects"]
public instance isNoetherianRing {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I) :
    IsNoetherianRing B.carrier := by
  obtain ⟨r, J, ⟨e⟩⟩ :=
    exists_adicCompletion_mvPolynomial_quotient_equiv I (Ideal.fg_of_isNoetherianRing I) B
  let _ : IsNoetherianRing
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
        (MvPolynomial (Fin r) A)) :=
    AdicCompletion.isNoetherianRing (I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A))
  exact isNoetherianRing_of_ringEquiv _ e.toRingEquiv

end

section
variable {A₁ A₂ : Type*} [CommRing A₁] [CommRing A₂]

/-- The map on quotients by powers induced by a ring homomorphism which sends
`I₁ ^ c` into `I₂`. -/
public def quotientPowMap (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    (c n : ℕ) (hφ : Ideal.map φ (I₁ ^ c) ≤ I₂) :
    A₁ ⧸ I₁ ^ (c * n) →+* A₂ ⧸ I₂ ^ n :=
  Ideal.quotientMap (I₂ ^ n) φ (by
    rw [← Ideal.map_le_iff_le_comap, pow_mul, Ideal.map_pow]
    exact pow_le_pow_left' hφ n)

/-- The map induced on quotients sends the class of an element to the class of
its image. -/
public theorem quotientPowMap_mk (φ : A₁ →+* A₂) (I₁ : Ideal A₁) (I₂ : Ideal A₂)
    (c n : ℕ) (hφ : Ideal.map φ (I₁ ^ c) ≤ I₂) (x : A₁) :
    quotientPowMap φ I₁ I₂ c n hφ (Ideal.Quotient.mk (I₁ ^ (c * n)) x) =
      Ideal.Quotient.mk (I₂ ^ n) (φ x) := by simp [quotientPowMap]

end

section

/-- Every quotient of an adically complete algebra of finite type modulo an ideal over a
Noetherian ring is again an adically complete algebra of finite type modulo that ideal. -/
@[stacks 0AJQ "quotients_remain_objects"]
public theorem quotient_isAdicFiniteType {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (J : Ideal B.carrier) :
    IsAdicComplete (I.map (algebraMap A (B.carrier ⧸ J))) (B.carrier ⧸ J) ∧
      Algebra.FiniteType (A ⧸ I)
        ((B.carrier ⧸ J) ⧸ I.map (algebraMap A (B.carrier ⧸ J))) := by
  let K : Ideal B.carrier := I.map (algebraMap A B.carrier)
  let Q := B.carrier ⧸ J
  let L : Ideal Q := I.map (algebraMap A Q)
  let _ : IsAdicComplete K B.carrier := B.isAdicallyComplete
  have hQcomplete : IsAdicComplete K Q :=
    isAdicComplete_of_iInf_smul_eq_bot (R := B.carrier) K (M := Q)
      (IsHausdorff.of_le_jacobson K Q (IsAdicComplete.le_jacobson_bot K)).iInf_pow_smul
  have hmap : L = K.map (algebraMap B.carrier Q) := by
    exact (map_map_algebraMap_algHom (IsScalarTower.toAlgHom A B.carrier Q) I).symm
  have hQcompleteRing : IsAdicComplete L Q := by
    rw [hmap]
    exact (IsAdicComplete.map_algebraMap_iff (R := B.carrier) (S := Q) (M := Q) K).mpr
      hQcomplete
  have hKpre : K ≤ Ideal.comap (algebraMap B.carrier Q) L :=
    Ideal.map_le_iff_le_comap.mp (hmap.symm ▸ le_refl L)
  let gAlg : B.reduction →ₐ[A ⧸ I] Q ⧸ L :=
    { toRingHom := Ideal.quotientMap L (algebraMap B.carrier Q) hKpre
      commutes' := by
        intro a
        obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) a
        calc
          Ideal.quotientMap L (algebraMap B.carrier Q) hKpre
              (algebraMap (A ⧸ I) B.reduction (Ideal.Quotient.mk I a₀)) =
              Ideal.quotientMap L (algebraMap B.carrier Q) hKpre
                (algebraMap B.carrier B.reduction (algebraMap A B.carrier a₀)) := by
            congr 1
          _ = algebraMap A (Q ⧸ L) a₀ := by
            rw [IsScalarTower.algebraMap_apply A B.carrier (Q ⧸ L) a₀]
            rfl }
  exact ⟨hQcompleteRing, Algebra.FiniteType.of_surjective gAlg
    (Ideal.quotientMap_surjective (H := hKpre) Ideal.Quotient.mk_surjective)⟩

end

section
variable (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ)

/-- The completion of a polynomial algebra is complete for the ideal extended
from the coefficient ring. -/
@[stacks 0AJP "polynomial_completions"]
public theorem iAdicallyCompleteRing_adicCompletion_mvPolynomial (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap A
        (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
          (MvPolynomial (Fin r) A))))
      (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
        (MvPolynomial (Fin r) A)) := by
  let R := MvPolynomial (Fin r) A
  let J := I.map (algebraMap A R)
  let S := AdicCompletion J R
  have hJ : IsAdicComplete J S := AdicCompletion.isAdicComplete (hI.map _)
  have hA : IsAdicComplete I S :=
    (IsAdicComplete.map_algebraMap_iff (S := R) I S).mp hJ
  exact (IsAdicComplete.map_algebraMap_iff I S).mpr hA

/-- The reduction modulo `I` of a completed polynomial algebra is of finite
type over `A ⧸ I`. -/
@[stacks 0AJP "polynomial_completions"]
public theorem finiteType_quotient_adicCompletion_mvPolynomial (hI : I.FG) :
    Algebra.FiniteType (A ⧸ I)
      ((AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
          (MvPolynomial (Fin r) A)) ⧸
        I.map (algebraMap A
          (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
            (MvPolynomial (Fin r) A)))) := by
  let R := MvPolynomial (Fin r) A
  let J := I.map (algebraMap A R)
  let S := AdicCompletion J R
  let K := I.map (algebraMap A S)
  have hJ : J.FG := hI.map _
  have hK : K = J.map (algebraMap R S) := by
    exact (map_map_algebraMap_algHom (IsScalarTower.toAlgHom A R S) I).symm
  have e : (S ⧸ K) ≃ₐ[R] R ⧸ J :=
    (Ideal.quotientEquivAlgOfEq R
      (hK.trans (AdicCompletion.ker_evalOneₐ_eq_map J hJ).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.evalOneₐ_surjective J))
  have hAS : Algebra.FiniteType A (S ⧸ K) :=
    (inferInstance : Algebra.FiniteType A R).trans ((Algebra.FiniteType.quotient R J).equiv e.symm)
  exact Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ I) (S ⧸ K)

end

section
variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (r : ℕ)

/-- The completion of the polynomial ring in `r` variables over a Noetherian ring is
complete for the ideal extended from the coefficient ring. -/
@[stacks 0AJQ "polynomial_completions"]
public theorem iAdicallyCompleteRing_adicCompletion_mvPolynomial_of_isNoetherianRing :
    IsAdicComplete
      (I.map (algebraMap A
        (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
          (MvPolynomial (Fin r) A))))
      (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
        (MvPolynomial (Fin r) A)) :=
  iAdicallyCompleteRing_adicCompletion_mvPolynomial A I r (Ideal.fg_of_isNoetherianRing I)

/-- The reduction modulo `I` of the completed polynomial ring in `r` variables is of
finite type over `A ⧸ I`. -/
@[stacks 0AJQ "polynomial_completions"]
public theorem finiteType_quotient_adicCompletion_mvPolynomial_of_isNoetherianRing :
    Algebra.FiniteType (A ⧸ I)
      ((AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
          (MvPolynomial (Fin r) A)) ⧸
        I.map (algebraMap A
          (AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A)))
            (MvPolynomial (Fin r) A)))) :=
  finiteType_quotient_adicCompletion_mvPolynomial A I r (Ideal.fg_of_isNoetherianRing I)

end

end Rig

end

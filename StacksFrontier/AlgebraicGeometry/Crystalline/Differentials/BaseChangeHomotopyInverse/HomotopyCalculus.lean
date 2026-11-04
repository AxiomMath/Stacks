module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChange
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse.DzDecomposition

/-!
# The differential calculus of the integrating homotopy

The rules for the de Rham differentials of the two complexes needed in the proof of Stacks,
Tag 07Q7: wedging with forms of the base, the Leibniz rule for the extended connection, the base
terms `f ⊗ x` of the target complex and the action of the integrating homotopy on them, its
anticommutation with wedging by forms of the base, and the fact that the Cartan remainder of the
base change map factors through it (using assumptions (5)-(7) of Tag 07Q1).
-/

@[expose] public section

open scoped TensorProduct DirectSum


universe u u' w

namespace Crystalline

open Stacks.DeRham.DifferentialDescent


variable {A B Omega : Type u} {A' B' Omega' : Type u'} {M : Type w}
variable
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B' Omega']
  [AddCommGroup M] [Module B M]


section DifferentialRules


noncomputable def formWedge (p : ℕ) (w : Omega) :
    M ⊗[B] (⋀[B]^p Omega) →ₗ[B] M ⊗[B] (⋀[B]^(p + 1) Omega) :=
  TensorProduct.map LinearMap.id (leftWedge p w)

theorem formWedge_tmul (p : ℕ) (w : Omega) (m : M) (v : ⋀[B]^p Omega) :
    formWedge p w (m ⊗ₜ[B] v) = m ⊗ₜ[B] leftWedge p w v := by
  simp [formWedge]

private theorem leftWedge_anticomm (p : ℕ) (v w : Omega) (x : ⋀[B]^p Omega) :
    leftWedge (p + 1) v (leftWedge p w x) =
      -leftWedge (p + 1) w (leftWedge p v x) := by
  apply Subtype.ext
  simp only [Submodule.coe_neg, leftWedge_coe]
  rw [← mul_assoc, ← mul_assoc,
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v w), neg_mul]

private theorem formWedge_add (p : ℕ) (v w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge p (v + w) x = formWedge p v x + formWedge p w x := by
  simp only [formWedge, map_add, TensorProduct.map_add_right, LinearMap.add_apply]

private theorem formWedge_smul (p : ℕ) (b : B) (w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge p (b • w) x = formWedge p w (b • x) := by
  simp only [formWedge, map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]

private theorem formWedge_sub (p : ℕ) (v w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge p (v - w) x = formWedge p v x - formWedge p w x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul m x => simp [formWedge_tmul, TensorProduct.tmul_sub]

theorem formWedge_zero (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge p (0 : Omega) x = 0 := by
  simp [formWedge]

private theorem formWedge_square (p : ℕ) (w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge (p + 1) w (formWedge p w x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul m x =>
    rw [formWedge_tmul, formWedge_tmul]
    have hw : leftWedge (p + 1) w (leftWedge p w x) = 0 := by
      apply Subtype.ext
      simp only [leftWedge_coe, Submodule.coe_zero, ← mul_assoc,
        ExteriorAlgebra.ι_sq_zero, zero_mul]
    rw [hw, TensorProduct.tmul_zero]

private theorem formWedge_anticomm (p : ℕ) (v w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge (p + 1) v (formWedge p w x) = -formWedge (p + 1) w (formWedge p v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]; abel
  | tmul m u =>
    rw [formWedge_tmul, formWedge_tmul, formWedge_tmul, formWedge_tmul, leftWedge_anticomm,
      TensorProduct.tmul_neg]

noncomputable def connectionDifferentialAddHom
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) (p : ℕ) :
    (M ⊗[B] (⋀[B]^p Omega)) →+ (M ⊗[B] (⋀[B]^(p + 1) Omega)) :=
  (RestrictScalars.addEquiv A B _).toAddMonoidHom.comp
    ((extendedConnection S pi hpi hgen nabla).toLinearMap p |>.toAddMonoidHom |>.comp
      (RestrictScalars.addEquiv A B _).symm.toAddMonoidHom)

private theorem connectionDifferentialAddHom_tmul
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) (p : ℕ) (m : M) (w : ⋀[B]^p Omega) :
    connectionDifferentialAddHom S pi hpi hgen nabla p (m ⊗ₜ[B] w) =
      TensorProduct.map LinearMap.id ((leftWedge p).flip w) (nabla m) +
        m ⊗ₜ[B] RestrictScalars.addEquiv A B _
          ((extendedConnection S pi hpi hgen nabla).deRhamDifferential p w) :=
  (extendedConnection S pi hpi hgen nabla).map_tmul p m w

theorem extendedConnection_leibniz
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) (p : ℕ) (b : B)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    connectionDifferentialAddHom S pi hpi hgen nabla p (b • x) =
      b • connectionDifferentialAddHom S pi hpi hgen nabla p x +
      formWedge p (SourceDeRham.targetD pi b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]; abel
  | tmul m w =>
    rw [TensorProduct.smul_tmul', connectionDifferentialAddHom_tmul,
      connectionDifferentialAddHom_tmul, nabla.leibniz]
    simp only [map_add, map_smul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearMap.flip_apply, ← TensorProduct.smul_tmul', formWedge_tmul, smul_add,
      SourceDeRham.targetD]
    abel

private theorem descendedDifferential_rule
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) :
    SourceDeRham.SatisfiesRule pi
      (extendedConnection S pi hpi hgen nabla).deRhamDifferential := by
  have h := Classical.choose_spec
    (exists_unique_quotient_deRhamDifferential S pi hpi hgen)
  rw [h.2.2.1 _ (extendedConnection S pi hpi hgen nabla).commutes]
  exact h.2.1

private theorem descendedDifferential_exact_wedge
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) (p : ℕ) (v : Fin p → B) :
    (extendedConnection S pi hpi hgen nabla).deRhamDifferential p
      (exteriorPower.ιMulti B p (SourceDeRham.targetD pi ∘ v)) = 0 := by
  have h := descendedDifferential_rule S pi hpi hgen nabla p (Fin.cons 1 v)
  have hzero : SourceDeRham.targetD pi (1 : B) = 0 := by
    simp [SourceDeRham.targetD]
  have heq : (fun i : Fin (p + 1) =>
        SourceDeRham.targetD pi ((Fin.cons (1 : B) v : Fin (p + 1) → B) i)) =
      Fin.cons (0 : Omega) (SourceDeRham.targetD pi ∘ v) := by
    funext i
    refine Fin.cases hzero (fun j => rfl) i
  simp only [SourceDeRham.tgtGen, SourceDeRham.tgtGenRes, Fin.cons_zero, Fin.cons_succ,
    one_smul, heq, ← leftWedge_ιMulti, map_zero, LinearMap.zero_apply, Function.comp_def] at h
  exact h

private theorem extendedConnection_exact_wedge
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) (p : ℕ) (m : M) (v : Fin p → B) :
    connectionDifferentialAddHom S pi hpi hgen nabla p
      (m ⊗ₜ[B] exteriorPower.ιMulti B p (SourceDeRham.targetD pi ∘ v)) =
      TensorProduct.map LinearMap.id
        ((leftWedge p).flip (exteriorPower.ιMulti B p (SourceDeRham.targetD pi ∘ v)))
        (nabla m) := by
  have h := (extendedConnection S pi hpi hgen nabla).map_tmul p m
    (exteriorPower.ιMulti B p (SourceDeRham.targetD pi ∘ v))
  rw [descendedDifferential_exact_wedge, map_zero, TensorProduct.tmul_zero, add_zero] at h
  exact h

private theorem tensorWedge_cons (p : ℕ) (w : Omega) (v : ⋀[B]^p Omega)
    (t : M ⊗[B] Omega) :
    TensorProduct.map LinearMap.id ((leftWedge (p + 1)).flip (leftWedge p w v)) t =
      -formWedge (p + 1) w (TensorProduct.map LinearMap.id ((leftWedge p).flip v) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | tmul m x =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.flip_apply,
      formWedge_tmul]
    rw [leftWedge_anticomm, TensorProduct.tmul_neg]

private theorem extendedConnection_wedge_exact
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M) (p : ℕ) (b : B)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    connectionDifferentialAddHom S pi hpi hgen nabla (p + 1)
      (formWedge p (SourceDeRham.targetD pi b) x) =
      -formWedge (p + 1) (SourceDeRham.targetD pi b)
        (connectionDifferentialAddHom S pi hpi hgen nabla p x) := by
  induction x using tensorExterior_induction_of_span (SourceDeRham.targetD pi)
      (targetD_span pi hpi) p with
  | hzero => simp
  | hadd x y hx hy => simp only [map_add, hx, hy, neg_add]
  | hwedge m v =>
    rw [formWedge_tmul, leftWedge_ιMulti]
    have hvec : Fin.cons (SourceDeRham.targetD pi b) (SourceDeRham.targetD pi ∘ v) =
        SourceDeRham.targetD pi ∘ Fin.cons b v := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    rw [hvec, extendedConnection_exact_wedge, extendedConnection_exact_wedge,
      ← hvec, ← leftWedge_ιMulti, tensorWedge_cons]

end DifferentialRules

section BaseTerms


variable (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
  (psi : Omega →ₛₗ[algebraMap B B'] Omega') (z : B')
  (dec : DzDecomposition pi' psi z)

noncomputable def baseTerm (p : ℕ) (f : B')
    (x : M ⊗[B] (⋀[B]^p Omega)) : (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega') :=
  coefficientInclusion pi' psi z dec p (f ⊗ₜ[B] x)

omit [SMulCommClass A' B B'] in
theorem baseTerm_tmul (p : ℕ) (f : B') (m : M) (v : Fin p → Omega) :
    baseTerm pi' psi z dec p f (m ⊗ₜ[B] exteriorPower.ιMulti B p v) =
      (f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ v) :=
  coefficientInclusion_tmul_ιMulti pi' psi z dec p f m v

omit [SMulCommClass A' B B'] in
private theorem baseTerm_zero (p : ℕ) (f : B') :
    baseTerm pi' psi z dec (M := M) p f 0 = 0 := by
  simp [baseTerm]

omit [SMulCommClass A' B B'] in
private theorem baseTerm_add (p : ℕ) (f : B') (x y : M ⊗[B] (⋀[B]^p Omega)) :
    baseTerm pi' psi z dec p f (x + y) =
      baseTerm pi' psi z dec p f x + baseTerm pi' psi z dec p f y := by
  simp [baseTerm, TensorProduct.tmul_add]

omit [SMulCommClass A' B B'] in
theorem baseTerm_smul_one (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
    baseTerm pi' psi z dec p f x = f • baseTerm pi' psi z dec p 1 x := by
  unfold baseTerm
  rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

omit [SMulCommClass A' B B'] in
private theorem baseTerm_wedge (p : ℕ) (f : B') (w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge p (psi w) (baseTerm pi' psi z dec p f x) =
      baseTerm pi' psi z dec (p + 1) f (formWedge p w x) := by
  induction x using tensorExterior_induction p with
  | hzero => simp [baseTerm_zero]
  | hadd x y hx hy => simp only [map_add, baseTerm_add, hx, hy]
  | hwedge m v =>
    rw [baseTerm_tmul, formWedge_tmul, formWedge_tmul,
      leftWedge_ιMulti, leftWedge_ιMulti, baseTerm_tmul]
    rw [Function.comp_def, Fin.comp_cons]
    rfl

noncomputable def integratingHomotopyAddHom (theta : B' →ₗ[B] B') (p : ℕ) :
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) →+
      ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) :=
  (coefficientInclusion pi' psi z dec p).toAddMonoidHom.comp
    ((TensorProduct.map theta LinearMap.id).toAddMonoidHom.comp
      (coefficientRankOneProjection pi' psi z dec p).toAddMonoidHom)

omit [SMulCommClass A' B B'] in
theorem integratingHomotopyAddHom_base (theta : B' →ₗ[B] B') (p : ℕ)
    (f : B') (x : M ⊗[B] (⋀[B]^(p + 1) Omega)) :
    integratingHomotopyAddHom pi' psi z dec theta p (baseTerm pi' psi z dec (p + 1) f x) = 0 := by
  induction x using tensorExterior_induction (p + 1) with
  | hzero => simp [baseTerm_zero]
  | hadd x y hx hy => simp only [baseTerm_add, map_add, hx, hy, add_zero]
  | hwedge m v =>
    rw [baseTerm_tmul]
    simp [integratingHomotopyAddHom, coefficientRankOneProjection_base]

omit [SMulCommClass A' B B'] in
theorem integratingHomotopyAddHom_dz (theta : B' →ₗ[B] B') (p : ℕ)
    (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
    integratingHomotopyAddHom pi' psi z dec theta p
      (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x)) =
      baseTerm pi' psi z dec p (theta f) x := by
  induction x using tensorExterior_induction p with
  | hzero => simp [baseTerm_zero]
  | hadd x y hx hy => simp only [baseTerm_add, map_add, hx, hy]
  | hwedge m v =>
    rw [baseTerm_tmul, formWedge_tmul, leftWedge_ιMulti, baseTerm_tmul]
    simp [integratingHomotopyAddHom, coefficientRankOneProjection_dz,
      coefficientInclusion_tmul_ιMulti]

omit [SMulCommClass A' B B'] in
/-- Wedging a base term with a pure tensor of base forms is a base term. -/
private theorem formWedge_baseFormInclusion_tmul (p : ℕ) (f : B') (w : Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    formWedge p (baseFormInclusion pi' psi z dec (f ⊗ₜ[B] w)) (baseTerm pi' psi z dec p 1 x) =
      baseTerm pi' psi z dec (p + 1) f (formWedge p w x) := by
  change formWedge p (dec.equiv (f ⊗ₜ[B] w, 0)) _ = _
  rw [dec.equiv_tmul, formWedge_smul, ← baseTerm_smul_one, baseTerm_wedge]

omit [SMulCommClass A' B B'] in
private theorem integratingHomotopyAddHom_differentialForm
    (theta : B' →ₗ[B] B') (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
    integratingHomotopyAddHom pi' psi z dec theta p
      (formWedge p (SourceDeRham.targetD pi' f) (baseTerm pi' psi z dec p 1 x)) =
      baseTerm pi' psi z dec p (theta (dec.partialZ f)) x := by
  have horizontal (w : B' ⊗[B] Omega) :
      integratingHomotopyAddHom pi' psi z dec theta p
        (formWedge p (baseFormInclusion pi' psi z dec w) (baseTerm pi' psi z dec p 1 x)) = 0 := by
    induction w using TensorProduct.induction_on with
    | zero => simp [formWedge]
    | add w w' hw hw' => rw [map_add, formWedge_add, map_add, hw, hw', add_zero]
    | tmul f w => rw [formWedge_baseFormInclusion_tmul, integratingHomotopyAddHom_base]
  rw [← dec.dOne_add_partialZ_smul f, formWedge_add, map_add]
  show integratingHomotopyAddHom pi' psi z dec theta p
      (formWedge p (baseFormInclusion pi' psi z dec (dec.dOne f))
        (baseTerm pi' psi z dec p 1 x)) + _ = _
  rw [horizontal, zero_add, formWedge_smul, ← baseTerm_smul_one, integratingHomotopyAddHom_dz]

omit [SMulCommClass A' B B'] in
private theorem integratingHomotopyAddHom_dz_horizontal
    (theta : B' →ₗ[B] B') (p : ℕ) (w : B' ⊗[B] Omega)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    integratingHomotopyAddHom pi' psi z dec theta (p + 1)
      (formWedge (p + 1) (SourceDeRham.targetD pi' z)
        (formWedge p (baseFormInclusion pi' psi z dec w) (baseTerm pi' psi z dec p 1 x))) =
      formWedge p (baseFormInclusion pi' psi z dec
        (TensorProduct.map theta LinearMap.id w)) (baseTerm pi' psi z dec p 1 x) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [formWedge_zero]
  | add w w' hw hw' =>
    simp only [map_add, formWedge_add, hw, hw']
  | tmul f w =>
    rw [formWedge_baseFormInclusion_tmul, integratingHomotopyAddHom_dz,
      TensorProduct.map_tmul, LinearMap.id_apply, formWedge_baseFormInclusion_tmul]

omit [SMulCommClass A' B B'] in
private theorem integratingHomotopyAddHom_dz_differentialForm
    (theta : B' →ₗ[B] B') (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
    integratingHomotopyAddHom pi' psi z dec theta (p + 1)
      (formWedge (p + 1) (SourceDeRham.targetD pi' z)
        (formWedge p (SourceDeRham.targetD pi' f) (baseTerm pi' psi z dec p 1 x))) =
      formWedge p (baseFormInclusion pi' psi z dec
        (TensorProduct.map theta LinearMap.id (dec.dOne f))) (baseTerm pi' psi z dec p 1 x) := by
  rw [← dec.dOne_add_partialZ_smul f, formWedge_add, map_add, map_add]
  show integratingHomotopyAddHom pi' psi z dec theta (p + 1)
      (formWedge (p + 1) (SourceDeRham.targetD pi' z)
        (formWedge p (baseFormInclusion pi' psi z dec (dec.dOne f))
          (baseTerm pi' psi z dec p 1 x))) + _ = _
  rw [integratingHomotopyAddHom_dz_horizontal, formWedge_smul, formWedge_square,
    map_zero, add_zero]

omit [SMulCommClass A' B B'] in
/-- **`θ ⊗ 1` commutes with the action of the base ring**, `θ` being `B`-linear. -/
private theorem map_theta_smul (theta : B' →ₗ[B] B') (p : ℕ) (b : B)
    (u : B' ⊗[B] (M ⊗[B] (⋀[B]^p Omega))) :
    TensorProduct.map theta (LinearMap.id (R := B) (M := M ⊗[B] (⋀[B]^p Omega)))
        (algebraMap B B' b • u) =
      algebraMap B B' b •
        TensorProduct.map theta (LinearMap.id (R := B) (M := M ⊗[B] (⋀[B]^p Omega))) u := by
  have h1 : ∀ f : B', theta (algebraMap B B' b • f) = algebraMap B B' b • theta f := fun f ↦ by
    rw [IsScalarTower.algebraMap_smul, map_smul, ← IsScalarTower.algebraMap_smul B' b (theta f)]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [smul_add, map_add, hu, hv]
  | tmul f x =>
    conv_lhs => rw [TensorProduct.smul_tmul']
    rw [TensorProduct.map_tmul, LinearMap.id_apply, h1, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.smul_tmul']

omit [SMulCommClass A' B B'] in
/-- **The integrating homotopy `h` commutes with the action of the base ring `B`.**  It is the
composite of two `B'`-linear maps with `θ ⊗ 1`, and `θ` is `B`-linear.  This is what makes the
`p`-adically completed homotopy linear over the completed base rather than merely additive. -/
theorem integratingHomotopyAddHom_smul (theta : B' →ₗ[B] B') (p : ℕ) (b : B)
    (y : (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega')) :
    integratingHomotopyAddHom pi' psi z dec theta p (algebraMap B B' b • y) =
      algebraMap B B' b • integratingHomotopyAddHom pi' psi z dec theta p y := by
  show coefficientInclusion pi' psi z dec p
      (TensorProduct.map theta LinearMap.id
        (coefficientRankOneProjection pi' psi z dec p (algebraMap B B' b • y))) = _
  rw [map_smul, map_theta_smul, map_smul]
  rfl

/-- The endomorphism `h ∘ (ψω ∧ ·) + (ψω ∧ ·) ∘ h` of the degree-`n` term, the second summand
read as zero in degree `0`.  It is zero, which is the anticommutation of the integrating
homotopy with wedging by a form pulled back from the base. -/
noncomputable def anticommAddHom (theta : B' →ₗ[B] B') (w : Omega) : ∀ n : ℕ,
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^n Omega')) →+ ((B' ⊗[B] M) ⊗[B'] (⋀[B']^n Omega'))
  | 0 => (integratingHomotopyAddHom pi' psi z dec theta 0).comp
      (formWedge 0 (psi w)).toAddMonoidHom
  | n + 1 => (integratingHomotopyAddHom pi' psi z dec theta (n + 1)).comp
        (formWedge (n + 1) (psi w)).toAddMonoidHom +
      (formWedge n (psi w)).toAddMonoidHom.comp
        (integratingHomotopyAddHom pi' psi z dec theta n)

omit [SMulCommClass A' B B'] in
theorem anticommAddHom_zero_apply (theta : B' →ₗ[B] B') (w : Omega)
    (y : (B' ⊗[B] M) ⊗[B'] (⋀[B']^0 Omega')) :
    anticommAddHom pi' psi z dec theta w 0 y =
      integratingHomotopyAddHom pi' psi z dec theta 0 (formWedge 0 (psi w) y) :=
  rfl

omit [SMulCommClass A' B B'] in
theorem anticommAddHom_succ_apply (theta : B' →ₗ[B] B') (w : Omega) (n : ℕ)
    (y : (B' ⊗[B] M) ⊗[B'] (⋀[B']^(n + 1) Omega')) :
    anticommAddHom pi' psi z dec theta w (n + 1) y =
      integratingHomotopyAddHom pi' psi z dec theta (n + 1) (formWedge (n + 1) (psi w) y) +
        formWedge n (psi w) (integratingHomotopyAddHom pi' psi z dec theta n y) :=
  rfl

omit [SMulCommClass A' B B'] in
/-- **The integrating homotopy anticommutes with wedging by a form of the base.**  One induction
over the generators of the decomposition (07Q1) proves it in every degree: on a base term both
summands vanish, because the homotopy kills base terms; on a `dz`-term the two summands are
negatives of one another, by the anticommutativity of the wedge product. -/
theorem anticommAddHom_eq_zero (theta : B' →ₗ[B] B') (w : Omega) (n : ℕ)
    (y : (B' ⊗[B] M) ⊗[B'] (⋀[B']^n Omega')) :
    anticommAddHom pi' psi z dec theta w n y = 0 := by
  have hmem : y ∈ (anticommAddHom pi' psi z dec theta w n).ker := by
    refine tensorExterior_dz_induction (M := M) pi' psi z dec
      (fun n => (anticommAddHom pi' psi z dec theta w n).ker) ?_ ?_ n y
    · intro n f m v
      simp only [AddMonoidHom.mem_ker]
      rw [← baseTerm_tmul pi' psi z dec n f m v]
      cases n with
      | zero =>
        rw [anticommAddHom_zero_apply, baseTerm_wedge, integratingHomotopyAddHom_base]
      | succ n =>
        rw [anticommAddHom_succ_apply, baseTerm_wedge, integratingHomotopyAddHom_base,
          integratingHomotopyAddHom_base, map_zero, add_zero]
    · intro n f m v
      simp only [AddMonoidHom.mem_ker]
      have hgen : ((f ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' (n + 1)
            (Fin.cons (SourceDeRham.targetD pi' z) (psi ∘ v))) =
          formWedge n (SourceDeRham.targetD pi' z)
            (baseTerm pi' psi z dec n f (m ⊗ₜ[B] exteriorPower.ιMulti B n v)) := by
        rw [baseTerm_tmul, formWedge_tmul, leftWedge_ιMulti]
      rw [hgen, anticommAddHom_succ_apply, integratingHomotopyAddHom_dz, formWedge_anticomm,
        map_neg, baseTerm_wedge, integratingHomotopyAddHom_dz, baseTerm_wedge, neg_add_cancel]
  exact AddMonoidHom.mem_ker.mp hmem

omit [SMulCommClass A' B B'] in
private theorem baseTerm_coeff_sub (p : ℕ) (f g : B')
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    baseTerm pi' psi z dec p (f - g) x =
      baseTerm pi' psi z dec p f x - baseTerm pi' psi z dec p g x := by
  simp [baseTerm, TensorProduct.sub_tmul]

omit [SMulCommClass A' B B'] in
theorem baseTerm_algebraMap (p : ℕ) (b : B)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    baseTerm pi' psi z dec p (algebraMap B B' b) x =
      baseTerm pi' psi z dec p 1 (b • x) := by
  unfold baseTerm
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]

omit [SMulCommClass A' B B'] in
/-- The base term is `B`-linear in its argument: scaling the form by `b` scales the term by the
image of `b`. -/
theorem baseTerm_one_smul (q : ℕ) (b : B) (x : M ⊗[B] (⋀[B]^q Omega)) :
    baseTerm pi' psi z dec q 1 (b • x) =
      algebraMap B B' b • baseTerm pi' psi z dec q 1 x := by
  rw [← baseTerm_algebraMap, baseTerm_smul_one]

omit [SMulCommClass A' B B'] in
private theorem baseTerm_remainder_mem_range
    (a : B) (theta : B' →ₗ[B] B')
    (hepsilon : ∀ f : B', a • f - theta (dec.partialZ f) ∈ Set.range (algebraMap B B'))
    (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
    algebraMap B B' a • baseTerm pi' psi z dec p f x -
      baseTerm pi' psi z dec p (theta (dec.partialZ f)) x ∈
      Set.range (baseTerm pi' psi z dec p 1) := by
  obtain ⟨b, hb⟩ := hepsilon f
  refine ⟨b • x, ?_⟩
  rw [← baseTerm_algebraMap, hb, baseTerm_coeff_sub]
  congr 1
  rw [baseTerm_smul_one, baseTerm_smul_one pi' psi z dec p f x,
    smul_smul, Algebra.smul_def]

omit [SMulCommClass A' B B'] in
private theorem dz_remainder_mem_range
    (a : B) (theta : B' →ₗ[B] B')
    (hpartialZ_theta : ∀ f : B', dec.partialZ (theta f) = a • f)
    (hepsilonPrime : ∀ f : B',
      TensorProduct.map theta (LinearMap.id (R := B) (M := Omega)) (dec.dOne f) -
        dec.dOne (theta f) ∈ LinearMap.range (TensorProduct.mk B B' Omega 1))
    (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
    algebraMap B B' a •
        formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x) -
      (formWedge p (SourceDeRham.targetD pi' (theta f)) (baseTerm pi' psi z dec p 1 x) -
        formWedge p (baseFormInclusion pi' psi z dec
          (TensorProduct.map theta LinearMap.id (dec.dOne f))) (baseTerm pi' psi z dec p 1 x)) ∈
      Set.range (baseTerm pi' psi z dec (p + 1) 1) := by
  obtain ⟨w, hw⟩ := hepsilonPrime f
  change 1 ⊗ₜ[B] w = _ at hw
  have hdiff :
      formWedge p (baseFormInclusion pi' psi z dec
          (TensorProduct.map theta LinearMap.id (dec.dOne f))) (baseTerm pi' psi z dec p 1 x) -
        formWedge p (baseFormInclusion pi' psi z dec (dec.dOne (theta f)))
          (baseTerm pi' psi z dec p 1 x) =
      baseTerm pi' psi z dec (p + 1) 1 (formWedge p w x) := by
    rw [← formWedge_sub, ← map_sub, ← hw]
    exact formWedge_baseFormInclusion_tmul pi' psi z dec p 1 w x
  have hscalar : algebraMap B B' a •
        formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x) =
      formWedge p ((a • f) • SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p 1 x) := by
    rw [formWedge_smul, map_smul, baseTerm_smul_one pi' psi z dec p f x,
      map_smul, smul_smul, Algebra.smul_def]
  refine ⟨formWedge p w x, ?_⟩
  rw [hscalar, ← dec.dOne_add_partialZ_smul (theta f), hpartialZ_theta, formWedge_add]
  show baseTerm pi' psi z dec (p + 1) 1 (formWedge p w x) =
    _ - (formWedge p (baseFormInclusion pi' psi z dec (dec.dOne (theta f)))
      (baseTerm pi' psi z dec p 1 x) + _ - _)
  rw [← hdiff]
  abel

end BaseTerms

section DeRhamCalculus


variable
  (S : SourceDeRham A B) (S' : SourceDeRham A' B')
  (pi : Ω[B⁄A] →ₗ[B] Omega) (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
  (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
  (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
  (psi : Omega →ₛₗ[algebraMap B B'] Omega')
  (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
  (nabla : Connection A B pi M)
  (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla)
  (c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
  (hc_wedge : ∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
      c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
      (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega))
  (hc_comm : ∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
      c (p + 1)
        ((extendedConnection S pi hpi hgen nabla).toLinearMap p x) =
      (extendedConnection S' pi' hpi' hgen'
        (Connection.baseChange psi nabla hpsi)).toLinearMap p (c p x))
  (z : B') (dec : DzDecomposition pi' psi z)

include hc_wedge hc_comm in
omit [Algebra A A'] [IsScalarTower A B B'] [IsScalarTower A A' B'] in
omit [SMulCommClass A' B B'] in
private theorem differential_baseTerm (p : ℕ) (f : B')
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    connectionDifferentialAddHom S' pi' hpi' hgen'
      (Connection.baseChange psi nabla hpsi) p
      (baseTerm pi' psi z dec p f x) =
      baseTerm pi' psi z dec (p + 1) f
        (connectionDifferentialAddHom S pi hpi hgen nabla p x) +
      formWedge p (SourceDeRham.targetD pi' f) (baseTerm pi' psi z dec p 1 x) := by
  have hcomm : connectionDifferentialAddHom S' pi' hpi' hgen'
      (Connection.baseChange psi nabla hpsi) p
        (baseTerm pi' psi z dec p 1 x) =
      baseTerm pi' psi z dec (p + 1) 1
        (connectionDifferentialAddHom S pi hpi hgen nabla p x) := by
    have hc0 := baseChangeMap_eq_coefficientInclusion pi' psi z dec p (c p) (hc_wedge p) x
    have hc1 := baseChangeMap_eq_coefficientInclusion pi' psi z dec (p + 1)
      (c (p + 1)) (hc_wedge (p + 1))
      (connectionDifferentialAddHom S pi hpi hgen nabla p x)
    change c p x = baseTerm pi' psi z dec p 1 x at hc0
    change c (p + 1) (connectionDifferentialAddHom S pi hpi hgen nabla p x) = _ at hc1
    rw [← hc0]
    exact (hc_comm p x).symm.trans hc1
  rw [baseTerm_smul_one, extendedConnection_leibniz, hcomm, ← baseTerm_smul_one]

include hc_wedge hc_comm in
omit [Algebra A A'] [IsScalarTower A B B'] [IsScalarTower A A' B'] in
omit [SMulCommClass A' B B'] in
private theorem homotopy_differential_baseTerm (theta : B' →ₗ[B] B') (p : ℕ) (f : B')
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    integratingHomotopyAddHom pi' psi z dec theta p
      (connectionDifferentialAddHom S' pi' hpi' hgen'
        (Connection.baseChange psi nabla hpsi) p
        (baseTerm pi' psi z dec p f x)) =
      baseTerm pi' psi z dec p (theta (dec.partialZ f)) x := by
  rw [differential_baseTerm S S' pi pi' hpi hgen hpi' hgen' psi hpsi nabla c hc_wedge hc_comm,
    map_add, integratingHomotopyAddHom_base, zero_add,
    integratingHomotopyAddHom_differentialForm]

include hc_wedge hc_comm in
omit [Algebra A A'] [IsScalarTower A B B'] [IsScalarTower A A' B'] in
omit [SMulCommClass A' B B'] in
private theorem homotopy_differential_dz_baseTerm (theta : B' →ₗ[B] B') (p : ℕ) (f : B')
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    connectionDifferentialAddHom S' pi' hpi' hgen'
        (Connection.baseChange psi nabla hpsi) p
      (integratingHomotopyAddHom pi' psi z dec theta p
        (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x))) +
      integratingHomotopyAddHom pi' psi z dec theta (p + 1)
        (connectionDifferentialAddHom S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi) (p + 1)
          (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x))) =
      formWedge p (SourceDeRham.targetD pi' (theta f)) (baseTerm pi' psi z dec p 1 x) -
        formWedge p (baseFormInclusion pi' psi z dec
          (TensorProduct.map theta LinearMap.id (dec.dOne f))) (baseTerm pi' psi z dec p 1 x) := by
  rw [integratingHomotopyAddHom_dz]
  have hd := extendedConnection_wedge_exact S' pi' hpi' hgen'
    (Connection.baseChange psi nabla hpsi) p z
    (baseTerm pi' psi z dec p f x)
  change connectionDifferentialAddHom S' pi' hpi' hgen'
      (Connection.baseChange psi nabla hpsi) (p + 1)
      (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x)) =
    -(formWedge (p + 1) (SourceDeRham.targetD pi' z)
      (connectionDifferentialAddHom S' pi' hpi' hgen'
        (Connection.baseChange psi nabla hpsi) p
        (baseTerm pi' psi z dec p f x))) at hd
  have hh :
      integratingHomotopyAddHom pi' psi z dec theta (p + 1)
        (connectionDifferentialAddHom S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi) (p + 1)
          (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x))) =
      -(integratingHomotopyAddHom pi' psi z dec theta (p + 1)
        (formWedge (p + 1) (SourceDeRham.targetD pi' z)
          (connectionDifferentialAddHom S' pi' hpi' hgen'
            (Connection.baseChange psi nabla hpsi) p
            (baseTerm pi' psi z dec p f x)))) :=
    (congrArg (integratingHomotopyAddHom pi' psi z dec theta (p + 1)) hd).trans
      (map_neg (integratingHomotopyAddHom pi' psi z dec theta (p + 1)) _)
  rw [hh]
  simp only [differential_baseTerm S S' pi pi' hpi hgen hpi' hgen' psi hpsi nabla
      c hc_wedge hc_comm z dec, map_add, integratingHomotopyAddHom_dz,
      integratingHomotopyAddHom_dz_differentialForm]
  abel

end DeRhamCalculus

/-- Restrict a linear map on scalar-restriction type synonyms along a tower. -/
def restrictLinearMapTower
    (R R' S : Type*) [CommSemiring R] [CommSemiring R'] [CommSemiring S]
    [Algebra R R'] [Algebra R' S] [Algebra R S] [IsScalarTower R R' S]
    {X Y : Type*} [AddCommMonoid X] [Module S X] [AddCommMonoid Y] [Module S Y]
    (f : RestrictScalars R' S X →ₗ[R'] RestrictScalars R' S Y) :
    RestrictScalars R S X →ₗ[R] RestrictScalars R S Y where
  toFun x := f x
  map_add' x y := f.map_add x y
  map_smul' r x := by
    change X at x
    have h := f.map_smul (algebraMap R R' r) x
    change f (algebraMap R' S (algebraMap R R' r) • x) =
      algebraMap R' S (algebraMap R R' r) • (show Y from f x) at h
    rw [← IsScalarTower.algebraMap_apply R R' S] at h
    exact h

/-- **The Cartan remainder of the base-change map factors through it.**  This is the body of the
proof of Lemma 07Q7 that the homotopy identities are checked on: on a base term the remainder is
`ε(f)ω`, which lies in the image because `ε(f)` lies in `B` by assumption (07Q5); on a `dz`-term
it is `ε'(f) ∧ η`, which lies in the image because `ε'(f)` lies in `Ω` by assumption (07Q6).  The
two cases are the generators of the decomposition (07Q1), so they suffice. -/
theorem cartanRemainder_mem_range
    (S : SourceDeRham A B) (S' : SourceDeRham A' B')
    (pi : Ω[B⁄A] →ₗ[B] Omega) (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
    (psi : Omega →ₛₗ[algebraMap B B'] Omega')
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
    (nabla : Connection A B pi M)
    (c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
    (hc_wedge : ∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
      c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega))
    (hc_comm : ∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
      c (p + 1)
          ((extendedConnection S pi hpi hgen nabla).toLinearMap p x) =
        (extendedConnection S' pi' hpi' hgen'
          (Connection.baseChange psi nabla hpsi)).toLinearMap p (c p x))
    (a : B) (z : B') (theta : B' →ₗ[B] B')
    (dec : DzDecomposition pi' psi z)
    (hpartialZ_theta : ∀ f : B', dec.partialZ (theta f) = a • f)
    (hepsilon : ∀ f : B',
      a • f - theta (dec.partialZ f) ∈ Set.range (algebraMap B B'))
    (hepsilonPrime : ∀ f : B',
      TensorProduct.map theta (LinearMap.id (R := B) (M := Omega)) (dec.dOne f) -
          dec.dOne (theta f) ∈
        LinearMap.range (TensorProduct.mk B B' Omega 1)) :
    ∀ (p : ℕ) (y : RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))),
      @cartanRemainder A _
          (fun p => RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))
          (fun p => inferInstanceAs (AddCommGroup
            (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))))
          (fun p => inferInstanceAs (Module A
            (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')))))
          (fun p => restrictLinearMapTower A A' B'
            (X := (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
            (Y := (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
            ((extendedConnection S' pi' hpi' hgen'
              (Connection.baseChange psi nabla hpsi)).toLinearMap p))
          (integratingHomotopy (A := A) (M := M) pi' psi z dec theta)
          (fun p => RestrictScalars.lsmul A B'
            ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) (algebraMap B B' a)) p y ∈
        LinearMap.range (c p) := by
  classical
  let nabla' := Connection.baseChange psi nabla hpsi
  let Y : ℕ → Type _ := fun p =>
    RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
  let yGroup : ∀ p, AddCommGroup (Y p) := fun p =>
    inferInstanceAs (AddCommGroup
      (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))))
  let yModule : ∀ p, Module A (Y p) := fun p =>
    inferInstanceAs (Module A
      (RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))))
  let dY : ∀ p, Y p →ₗ[A] Y (p + 1) := fun p =>
    restrictLinearMapTower A A' B'
      (X := (B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
      (Y := (B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
      ((extendedConnection S' pi' hpi' hgen' nabla').toLinearMap p)
  let hh := integratingHomotopy (A := A) (M := M) pi' psi z dec theta
  let s : ∀ p, Y p →ₗ[A] Y p := fun p =>
    RestrictScalars.lsmul A B' _ (algebraMap B B' a)
  let g : ∀ p, Y p →ₗ[A] Y p := @cartanRemainder A _ Y yGroup yModule dY hh s
  show ∀ p y, g p y ∈ LinearMap.range (c p)
  have hc_base (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)) :
      c p x = baseTerm pi' psi z dec p 1 x :=
    baseChangeMap_eq_coefficientInclusion pi' psi z dec p (c p) (hc_wedge p) x
  have hbase (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
      g p (baseTerm pi' psi z dec p f x) =
        algebraMap B B' a • baseTerm pi' psi z dec p f x -
          baseTerm pi' psi z dec p (theta (dec.partialZ f)) x := by
    cases p with
    | zero =>
      exact congrArg
        (fun y => algebraMap B B' a • baseTerm pi' psi z dec 0 f x - y)
        (homotopy_differential_baseTerm S S' pi pi' hpi hgen hpi' hgen' psi hpsi
          nabla c hc_wedge hc_comm z dec theta 0 f x)
    | succ p =>
      exact (congrArg₂
        (fun u v => algebraMap B B' a • baseTerm pi' psi z dec (p + 1) f x -
          connectionDifferentialAddHom S' pi' hpi' hgen' nabla' p u - v)
        (integratingHomotopyAddHom_base pi' psi z dec theta p f x)
        (homotopy_differential_baseTerm S S' pi pi' hpi hgen hpi' hgen' psi hpsi
          nabla c hc_wedge hc_comm z dec theta (p + 1) f x)).trans
        (by
          rw [map_zero]
          exact congrArg
            (fun y => y - baseTerm pi' psi z dec (p + 1) (theta (dec.partialZ f)) x)
            (sub_zero (algebraMap B B' a • baseTerm pi' psi z dec (p + 1) f x)))
  have hdz (p : ℕ) (f : B') (x : M ⊗[B] (⋀[B]^p Omega)) :
      g (p + 1) (formWedge p (SourceDeRham.targetD pi' z)
        (baseTerm pi' psi z dec p f x)) ∈ LinearMap.range (c (p + 1)) := by
    have hcalc := homotopy_differential_dz_baseTerm S S' pi pi' hpi hgen hpi' hgen'
      psi hpsi nabla c hc_wedge hc_comm z dec theta p f x
    have hr := dz_remainder_mem_range pi' psi z dec a theta hpartialZ_theta
      hepsilonPrime p f x
    obtain ⟨y, hy⟩ := hr
    refine ⟨y, (hc_base (p + 1) y).trans ?_⟩
    exact hy.trans ((congrArg
      (fun v => algebraMap B B' a •
        formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x) - v)
      hcalc).symm.trans (sub_add_eq_sub_sub
        (algebraMap B B' a •
          formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x))
        (connectionDifferentialAddHom S' pi' hpi' hgen' nabla' p
          (integratingHomotopyAddHom pi' psi z dec theta p
            (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x))))
        (integratingHomotopyAddHom pi' psi z dec theta (p + 1)
          (connectionDifferentialAddHom S' pi' hpi' hgen' nabla' (p + 1)
            (formWedge p (SourceDeRham.targetD pi' z) (baseTerm pi' psi z dec p f x))))))
  let H : ∀ p, AddSubgroup ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) := fun p => {
    carrier := {y | ∃ x : RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)), c p x = g p y}
    zero_mem' := ⟨0, (c p).map_zero.trans (g p).map_zero.symm⟩
    add_mem' := by
      rintro y w ⟨x, hx⟩ ⟨v, hv⟩
      exact ⟨x + v, ((c p).map_add x v).trans
        ((congrArg₂ (· + ·) hx hv).trans ((g p).map_add y w).symm)⟩
    neg_mem' := by
      rintro y ⟨x, hx⟩
      exact ⟨-x, (map_neg (c p) x).trans
        ((congrArg Neg.neg hx).trans (map_neg (g p) y).symm)⟩ }
  apply tensorExterior_dz_induction pi' psi z dec H
  · intro p f m v
    obtain ⟨y, hy⟩ := baseTerm_remainder_mem_range pi' psi z dec a theta hepsilon
      p f (m ⊗ₜ[B] exteriorPower.ιMulti B p v)
    refine ⟨y, (hc_base p y).trans ?_⟩
    exact hy.trans ((hbase p f (m ⊗ₜ[B] exteriorPower.ιMulti B p v)).symm.trans
      (congrArg (g p) (baseTerm_tmul pi' psi z dec p f m v)))
  · intro p f m v
    have hr := hdz p f (m ⊗ₜ[B] exteriorPower.ιMulti B p v)
    simp only [baseTerm_tmul, formWedge_tmul, leftWedge_ιMulti] at hr
    exact hr

end Crystalline

end

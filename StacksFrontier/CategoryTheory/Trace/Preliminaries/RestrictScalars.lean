module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Finiteness.Finsupp
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.ProjectiveTrace
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.GroupTrace
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace of a group-algebra endomorphism over the coefficient ring

Let `R` be a possibly noncommutative ring and `G` a finite group.  A module over the group
algebra `R[G]` is a module over `R` by restriction of scalars along `R → R[G]`, and finiteness
and projectivity are inherited.  For an endomorphism of a finite projective `R[G]`-module, the
trace computed over `R` is `#G` times the group trace.

## Main results

* `Stacks.Trace.finite_restrictScalars_groupAlgebra` and
  `Stacks.Trace.projective_restrictScalars_groupAlgebra`: finiteness and projectivity are
  inherited after restricting scalars to the coefficient ring.
* `Stacks.Trace.projectiveModuleTrace_restrictScalars_groupAlgebra`: the two traces differ by
  the factor `#G`.

## Implementation notes

The coefficient-ring action is the one obtained by restricting scalars along
`MonoidAlgebra.singleOneRingHom`.  The two inheritance lemmas are stated as conclusions under
that `letI`, so that the trace identity itself can be stated with all three instances in scope.

Over a finite group, a finite free `R[G]`-module `Fin n → R[G]` is a finite free `R`-module on
the index type `Fin n × G`; the equivalence `groupAlgebraPiEquiv` realizes this, and the
comparison of diagonal entries across it is what produces the factor `#G`.

## References

* [Stacks Project, Tag 03U7](https://stacks.math.columbia.edu/tag/03U7)
-/

@[expose] public section

open scoped MonoidAlgebra

open CategoryTheory.FilteredDerived

universe u v w

namespace Stacks.Trace

/-- The action of the coefficient ring on the group ring is multiplication by the image of
the coefficient under `R → R[G]`. -/
lemma groupAlgebra_smul_eq_mul (R : Type u) (G : Type v)
    [Ring R] [Monoid G] (r : R) (a : R[G]) :
    r • a = MonoidAlgebra.singleOneRingHom (R := R) (M := G) r * a := by
  ext g
  simp [MonoidAlgebra.singleOneRingHom, MonoidAlgebra.coeff_single_one_mul]

/-- If the `R`-action on a module over `R[G]` is through `R → R[G]`, then `R`, `R[G]` and the
module form a scalar tower. -/
private lemma isScalarTower_of_smul_eq_singleOne
    (R : Type u) (G : Type v) (M : Type w) [Ring R] [Monoid G]
    [AddCommGroup M] [Module R M] [Module R[G] M]
    (h : ∀ (r : R) (m : M), r • m = MonoidAlgebra.singleOneRingHom (R := R) (M := G) r • m) :
    IsScalarTower R R[G] M :=
  ⟨fun r a m => by rw [h r (a • m), groupAlgebra_smul_eq_mul R G r a, mul_smul]⟩

/-- Restricting scalars along `R → R[G]` makes `R`, `R[G]` and the module a scalar tower. -/
private lemma isScalarTower_restrictScalars_groupAlgebra
    (R : Type u) (G : Type v) (P : Type w) [Ring R] [Monoid G]
    [AddCommGroup P] [Module R[G] P] :
    letI : Module R P := Module.compHom P
      (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
    IsScalarTower R R[G] P :=
  let : Module R P := Module.compHom P
    (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
  isScalarTower_of_smul_eq_singleOne R G P fun _ _ => rfl

/-- The coefficient ring, the group algebra and `Fin n → R[G]` form a scalar tower. -/
private lemma isScalarTower_pi_groupAlgebra (R : Type u) (G : Type v) [Ring R] [Monoid G] (n : ℕ) :
    IsScalarTower R R[G] (Fin n → R[G]) :=
  isScalarTower_of_smul_eq_singleOne R G _ fun r x =>
    funext fun i => groupAlgebra_smul_eq_mul R G r (x i)

/-- A module finite over the group algebra of a finite group is finite over the coefficient
ring. -/
lemma finite_restrictScalars_groupAlgebra
    (R : Type u) (G : Type v) (P : Type w) [Ring R] [Group G] [Finite G]
    [AddCommGroup P] [Module R[G] P] [Module.Finite R[G] P] :
    letI : Module R P := Module.compHom P
      (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
    Module.Finite R P := by
  let : Module R P := Module.compHom P
    (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
  have : IsScalarTower R R[G] P := isScalarTower_restrictScalars_groupAlgebra R G P
  have : Module.Finite R R[G] := MonoidAlgebra.moduleFinite
  exact Module.Finite.trans R[G] P

/-- A module projective over a group algebra is projective over the coefficient ring. -/
lemma projective_restrictScalars_groupAlgebra
    (R : Type u) (G : Type v) (P : Type w) [Ring R] [Group G]
    [AddCommGroup P] [Module R[G] P] [Module.Projective R[G] P] :
    letI : Module R P := Module.compHom P
      (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
    Module.Projective R P := by
  let : Module R P := Module.compHom P (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
  have : IsScalarTower R R[G] P := isScalarTower_restrictScalars_groupAlgebra R G P
  obtain ⟨i, hi⟩ := Module.projective_def.mp ‹Module.Projective R[G] P›
  have : IsScalarTower R R[G] (P →₀ R[G]) :=
    isScalarTower_of_smul_eq_singleOne R G _ fun r x =>
      Finsupp.ext fun y => groupAlgebra_smul_eq_mul R G r (x y)
  exact Module.Projective.of_split (i.restrictScalars R)
    ((Finsupp.linearCombination R[G] id).restrictScalars R)
    (LinearMap.ext hi)

/-- Over a finite group, `Fin n → R[G]` is a finite free `R`-module on the index type
`Fin n × G`. -/
private noncomputable def groupAlgebraPiEquiv (R : Type u) (G : Type v)
    [Ring R] [Group G] [Finite G] (n : ℕ) :
    (Fin n → R[G]) ≃ₗ[R] (Fin n × G → R) := by
  let e₁ : (Fin n → R[G]) ≃ₗ[R] (Fin n → G →₀ R) :=
    LinearEquiv.piCongrRight (fun _ =>
      MonoidAlgebra.coeffLinearEquiv R (S := R) (M := G))
  let e₂ : (Fin n → G →₀ R) ≃ₗ[R] (Fin n → G → R) :=
    LinearEquiv.piCongrRight (fun _ => Finsupp.linearEquivFunOnFinite R R G)
  let e₃ : (Fin n × G → R) ≃ₗ[R] (Fin n → G → R) :=
    (LinearEquiv.funCongrLeft R R (Equiv.sigmaEquivProd (Fin n) G)).trans
      (LinearEquiv.piCurry R (fun (_ : Fin n) (_ : G) => R))
  exact e₁.trans (e₂.trans e₃.symm)

/-- `groupAlgebraPiEquiv` carries the standard basis vector at `(i, g)` to the `i`-th standard
basis vector scaled by the group element `g`. -/
private lemma groupAlgebraPiEquiv_symm_basis (R : Type u) (G : Type v)
    [Ring R] [Group G] [Finite G] (n : ℕ) (i : Fin n) (g : G) :
    (groupAlgebraPiEquiv R G n).symm
      (standardBasisVector R (Fin n × G) (i, g)) =
      Pi.single (M := fun _ : Fin n => R[G]) i (MonoidAlgebra.single g (1 : R)) := by
  ext j h
  simp [groupAlgebraPiEquiv, standardBasisVector,
    MonoidAlgebra.coeffLinearEquiv_symm_apply, Equiv.sigmaEquivProd,
    Sigma.curry, LinearMap.funLeft_apply, Pi.single_apply, Prod.mk.injEq]
  by_cases hji : j = i
  · subst j
    by_cases hEq : h = g
    · subst h
      simp
    · simp [hEq]
  · simp [hji, Prod.mk.injEq]

/-- The `(i, g)` coordinate of `groupAlgebraPiEquiv` is the coefficient of `g` in the `i`-th
component. -/
private lemma groupAlgebraPiEquiv_apply (R : Type u) (G : Type v)
    [Ring R] [Group G] [Finite G] (n : ℕ) (x : Fin n → R[G]) (i : Fin n) (g : G) :
    groupAlgebraPiEquiv R G n x (i, g) = (x i).coeff g := by
  simp [groupAlgebraPiEquiv, MonoidAlgebra.coeffLinearEquiv_apply,
    Equiv.sigmaEquivProd, Sigma.uncurry, LinearMap.funLeft_apply]

/-- Transported along `groupAlgebraPiEquiv`, the coefficient-ring trace of an endomorphism of
`Fin n → R[G]` is `#G` times the class of the coefficient of the identity in its
group-algebra trace. -/
@[sga "5 IIIB 5.10.11" "A = K = R",
  sga "5 IIIB 5.11.1" "special case",
  sga "5 IIIB 5.13" "special case",
  sga "5 IIIB 6.7" "special case"]
private lemma freeModuleTrace_groupAlgebra (R : Type u) (G : Type v)
    [Ring R] [Group G] [Fintype G] (n : ℕ)
    (H : Module.End R[G] (Fin n → R[G])) :
    freeModuleTrace R (Fin n × G)
      (((groupAlgebraPiEquiv R G n).toLinearMap).comp
        ((H.restrictScalars R).comp ((groupAlgebraPiEquiv R G n).symm.toLinearMap))) =
      (Nat.card G) • additiveCommutatorQuotientMk R
        (∑ i, (H (standardBasisVector R[G] (Fin n) i) i).coeff 1) := by
  classical
  have := isScalarTower_pi_groupAlgebra R G n
  have hdiag (i : Fin n) (g : G) :
      (((groupAlgebraPiEquiv R G n).toLinearMap).comp
        ((H.restrictScalars R).comp ((groupAlgebraPiEquiv R G n).symm.toLinearMap)))
        (standardBasisVector R (Fin n × G) (i, g)) (i, g) =
        (H (standardBasisVector R[G] (Fin n) i) i).coeff 1 := by
    have hb : (groupAlgebraPiEquiv R G n).symm (standardBasisVector R (Fin n × G) (i, g)) =
        MonoidAlgebra.single g (1 : R) • standardBasisVector R[G] (Fin n) i := by
      rw [groupAlgebraPiEquiv_symm_basis]
      ext j
      simp [standardBasisVector, Pi.single_apply]
    change groupAlgebraPiEquiv R G n
      (H ((groupAlgebraPiEquiv R G n).symm (standardBasisVector R (Fin n × G) (i, g)))) (i, g) = _
    rw [hb, H.map_smul, groupAlgebraPiEquiv_apply]
    simp [standardBasisVector, MonoidAlgebra.coeff_single_mul_apply]
  rw [freeModuleTrace_apply, map_sum, Fintype.sum_prod_type]
  simp_rw [hdiag]
  simp [Finset.sum_const, Nat.card_eq_fintype_card, Finset.sum_nsmul]

/-- **Stacks Project, Tag 03U7.** The coefficient-ring trace of an endomorphism of a finite
projective module over the group algebra of a finite group is the order of the group times its
group trace. -/
@[stacks 03U7,
  sga "4½ Rapport 5.6",
  sga "5 IIIB 5.10.11" "A = K = R",
  sga "5 IIIB 5.13" "(1), special case",
  sga "5 IIIB 6.7" "special case"]
theorem projectiveModuleTrace_restrictScalars_groupAlgebra
    (R : Type u) (G : Type v) (P : Type w) [Ring R] [Group G] [Finite G]
    [AddCommGroup P] [Module R[G] P]
    [Module.Finite R[G] P] [Module.Projective R[G] P]
    (f : Module.End R[G] P) :
    letI : Module R P := Module.compHom P
      (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
    letI : Module.Finite R P := finite_restrictScalars_groupAlgebra R G P
    letI : Module.Projective R P := projective_restrictScalars_groupAlgebra R G P
    let fR : Module.End R P :=
      { f with
        map_smul' := by
          intro r p
          exact f.map_smul (MonoidAlgebra.singleOneRingHom (R := R) (M := G) r) p }
    projectiveModuleTrace R P fR =
      (Nat.card G) • groupTrace R G P f := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Module R P := Module.compHom P (MonoidAlgebra.singleOneRingHom (R := R) (M := G))
  have : IsScalarTower R R[G] P := isScalarTower_restrictScalars_groupAlgebra R G P
  have : Module.Finite R P := finite_restrictScalars_groupAlgebra R G P
  have : Module.Projective R P := projective_restrictScalars_groupAlgebra R G P
  let fR : Module.End R P := f.restrictScalars R
  dsimp only
  change projectiveModuleTrace R P fR =
    (Nat.card G) • epsilon R G (projectiveModuleTrace R[G] P f)
  obtain ⟨n, pS, iS, hpS, hiS, hpiS⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R[G] P
  have := isScalarTower_pi_groupAlgebra R G n
  let e := groupAlgebraPiEquiv R G n
  let pR : (Fin n × G → R) →ₗ[R] P :=
    (pS.restrictScalars R).comp e.symm.toLinearMap
  let iR : P →ₗ[R] (Fin n × G → R) :=
    e.toLinearMap.comp (iS.restrictScalars R)
  have hpiR : pR.comp iR = LinearMap.id := by
    ext x
    simpa [pR, iR] using LinearMap.congr_fun hpiS x
  let H : Module.End R[G] (Fin n → R[G]) := iS.comp (f.comp pS)
  have hmaps : iR.comp (fR.comp pR) =
      e.toLinearMap.comp ((H.restrictScalars R).comp e.symm.toLinearMap) := by
    ext x
    rfl
  rw [projectiveModuleTrace_eq_of_split R P fR pR iR hpiR, hmaps,
    freeModuleTrace_groupAlgebra R G n H, projectiveModuleTrace_eq_of_split R[G] P f pS iS hpiS,
    freeModuleTrace_apply, epsilon_mk]
  simp only [map_sum, MonoidAlgebra.coeff_sum]
  simp [H, LinearMap.comp_apply, Nat.card_eq_fintype_card]

end Stacks.Trace

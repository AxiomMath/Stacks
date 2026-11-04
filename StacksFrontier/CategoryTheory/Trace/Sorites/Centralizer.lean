module

public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.Finiteness.Finsupp
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.RestrictScalars
public import StacksFrontier.CategoryTheory.Trace.Sorites.GroupAlgebraRestriction
public import StacksFrontier.CategoryTheory.Trace.Sorites.TraceCoordinates
public import StacksCore.Tactic.StacksAttribute

/-!
# Trace and the centralizer trace

The trace of an element acting on a module finite projective over a finite
group algebra is the order of its centralizer times its centralizer trace.

## Main definitions

* `centralizer` is the centralizer in the group acting through an inclusion.
* `centralizerTrace` is the associated group trace.

## Main results

* `trace_eq_card_centralizer_nsmul_groupTrace` is the trace identity.

## Implementation notes

Only the map `G →* Γ` is needed from the monoid extension. The module is
given directly over `Λ[Γ]`, and its subgroup actions are restrictions of scalars.

## References

* [Stacks Project, Tag 03UB](https://stacks.math.columbia.edu/tag/03UB)
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra

open CategoryTheory.FilteredDerived

universe u v w x

namespace Stacks.Trace

variable {Λ : Type u} {G : Type v} {Γ : Type w} {P : Type x}
variable [Ring Λ] [Group G] [Finite G] [Monoid Γ]
variable [AddCommGroup P] [Module Λ[Γ] P]

/-- Functoriality of the group ring is compatible with the unit maps of the coefficient
ring. -/
private lemma mapDomain_singleOne (R : Type u) (H : Type v) (Γ : Type w)
    [Ring R] [Monoid H] [Monoid Γ] (j : H →* Γ) (r : R) :
    MonoidAlgebra.mapDomainRingHom R j
      (MonoidAlgebra.singleOneRingHom (R := R) (M := H) r) =
    MonoidAlgebra.singleOneRingHom (R := R) (M := Γ) r := by
  ext g
  simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.singleOneRingHom]

omit [Finite G] in
/-- The image of the group ring of a subgroup centralizing an element of the ambient monoid
commutes with that element. -/
private lemma centralizer_commutes_mapDomain (i : G →* Γ) (γ : Γ)
    (H : Subgroup G) (h : ∀ g : H, i g * γ = γ * i g) (a : Λ[H]) :
    MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a *
        MonoidAlgebra.single γ (1 : Λ) =
      MonoidAlgebra.single γ (1 : Λ) *
        MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a := by
  let z : Λ[Γ] := MonoidAlgebra.single γ (1 : Λ)
  show MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a * z =
    z * MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a
  induction a using MonoidAlgebra.induction_on with
  | of g =>
      simp [MonoidAlgebra.mapDomainRingHom, z, MonoidAlgebra.single_mul_single, h g]
  | add a b ha hb =>
      simp only [map_add, add_mul, mul_add, ha, hb]
  | smul r a ha =>
      have hmap : MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) (r • a) =
          r • MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a := by
        ext t
        simp [MonoidAlgebra.mapDomainRingHom]
      have hscalar : z * MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r =
          MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r * z := by
        simp [z, MonoidAlgebra.single_mul_single, MonoidAlgebra.singleOneRingHom]
      rw [hmap, groupAlgebra_smul_eq_mul Λ Γ r
        (MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a),
        mul_assoc, ha, ← mul_assoc _ z, ← hscalar, mul_assoc]

/-- Restriction of a `Λ[Γ]`-module to a submonoid of `Γ`. -/
def restrictedModule (Λ : Type u) (P : Type x) {H : Type*} [Ring Λ]
    [AddCommGroup P] [Module Λ[Γ] P] [Monoid H] (_j : H →* Γ) := P
  deriving AddCommGroup, Module Λ[Γ]

/-- The `Λ[H]`-module structure on `restrictedModule Λ P j`, obtained by restricting scalars along
the ring homomorphism `Λ[H] → Λ[Γ]` induced by `j`. -/
noncomputable instance restrictedModule.module {H : Type*} [Monoid H]
    (j : H →* Γ) : Module Λ[H] (restrictedModule Λ P j) :=
  Module.compHom (restrictedModule Λ P j) (MonoidAlgebra.mapDomainRingHom Λ j)

/-- Restriction to the coefficient ring. -/
def coefficientModule (Λ : Type u) (Γ : Type w) (P : Type x)
    [Ring Λ] [Monoid Γ] [AddCommGroup P] [Module Λ[Γ] P] := P
  deriving AddCommGroup, Module Λ[Γ]

/-- The `Λ`-module structure on `coefficientModule Λ Γ P`, obtained by restricting scalars along
the inclusion `Λ → Λ[Γ]`, `r ↦ r • 1`. -/
noncomputable instance coefficientModule.module : Module Λ
    (coefficientModule Λ Γ P) :=
  Module.compHom (coefficientModule Λ Γ P)
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ))

/-- The restriction of a `Λ[Γ]`-module to a submonoid and its restriction to the coefficient
ring have the same underlying `Λ`-module. -/
private noncomputable def restrictedCoefficientLinearEquiv {H : Type*} [Monoid H]
    (j : H →* Γ) :
    letI : Module Λ (restrictedModule Λ P j) := Module.compHom
      (restrictedModule Λ P j) (MonoidAlgebra.singleOneRingHom (R := Λ) (M := H))
    restrictedModule Λ P j ≃ₗ[Λ] coefficientModule Λ Γ P := by
  letI : Module Λ (restrictedModule Λ P j) := Module.compHom
    (restrictedModule Λ P j) (MonoidAlgebra.singleOneRingHom (R := Λ) (M := H))
  exact
    { toFun := id
      invFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r p
        change (MonoidAlgebra.mapDomainRingHom Λ j
          (MonoidAlgebra.singleOneRingHom (R := Λ) (M := H) r)) • p =
          (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r) • p
        rw [mapDomain_singleOne]
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Elements of `G` commuting with `γ` under `i`. -/
@[sga "5 IIIB 5.11.3"]
def centralizer (i : G →* Γ) (γ : Γ) : Subgroup G where
  carrier := {g | i g * γ = γ * i g}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change i (a * b) * γ = γ * i (a * b)
    rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  inv_mem' := by
    intro a ha
    change i a⁻¹ * γ = γ * i a⁻¹
    calc
      i a⁻¹ * γ = i a⁻¹ * (γ * i a) * i a⁻¹ := by
        rw [mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = i a⁻¹ * (i a * γ) * i a⁻¹ := by rw [ha]
      _ = γ * i a⁻¹ := by
        rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- The coefficient and group-algebra actions on a restricted module form a scalar tower. -/
private lemma isScalarTower_restrictedModule {H : Type*} [Monoid H] (j : H →* Γ) :
    letI : Module Λ (restrictedModule Λ P j) := Module.compHom _
      (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ))
    IsScalarTower Λ Λ[H] (restrictedModule Λ P j) := by
  let : Module Λ (restrictedModule Λ P j) := Module.compHom _
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ))
  refine ⟨fun r a p => ?_⟩
  rw [groupAlgebra_smul_eq_mul Λ H r a]
  change (MonoidAlgebra.mapDomainRingHom Λ j
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := H) r * a)) • p =
    MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r •
      (MonoidAlgebra.mapDomainRingHom Λ j a • p)
  rw [map_mul, mapDomain_singleOne]
  exact mul_smul _ _ _

/-- Finite generation restricts from a finite group to a subgroup. -/
lemma restricted_module_finite (i : G →* Γ)
    [Module.Finite Λ[G] (restrictedModule Λ P i)]
    (H : Subgroup G) :
    Module.Finite Λ[H] (restrictedModule Λ P (i.comp H.subtype)) := by
  let Q := restrictedModule Λ P (i.comp H.subtype)
  let : Module Λ Q := Module.compHom Q
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ))
  have : IsScalarTower Λ Λ[H] Q := isScalarTower_restrictedModule (P := P) _
  have : Module.Finite Λ Q := by
    let QG := restrictedModule Λ P i
    let : Module Λ QG := Module.compHom QG
      (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ))
    have : IsScalarTower Λ Λ[G] QG := isScalarTower_restrictedModule (P := P) _
    let : Module.Finite Λ Λ[G] := MonoidAlgebra.moduleFinite
    have hQG : Module.Finite Λ QG := Module.Finite.trans Λ[G] QG
    let e : QG ≃ₗ[Λ] Q :=
      { toFun := id
        invFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Module.Finite.equiv e
  exact Module.Finite.of_restrictScalars_finite Λ Λ[H] Q (hM := this)

/-- Projectivity restricts from a finite group to a subgroup. -/
@[sga "4½ Rapport 5.9" "(g)"]
lemma restricted_module_projective (i : G →* Γ)
    [Module.Projective Λ[G] (restrictedModule Λ P i)]
    (H : Subgroup G) :
    Module.Projective Λ[H] (restrictedModule Λ P (i.comp H.subtype)) := by
  let Q := restrictedModule Λ P (i.comp H.subtype)
  let : Module Λ[G] Q := Module.compHom Q (MonoidAlgebra.mapDomainRingHom Λ i)
  let : Module Λ[H] Λ[G] :=
    Module.compHom _ (MonoidAlgebra.mapDomainRingHom Λ H.subtype)
  have hcomp : ∀ b : Λ[H], MonoidAlgebra.mapDomainRingHom Λ i
      (MonoidAlgebra.mapDomainRingHom Λ H.subtype b) =
      MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) b := by
    intro b
    rw [MonoidAlgebra.mapDomainRingHom_comp]
    rfl
  have : IsScalarTower Λ[H] Λ[G] Λ[G] := ⟨fun b x y => mul_assoc _ x y⟩
  have : IsScalarTower Λ[H] Λ[G] Q := by
    refine ⟨fun b x p => ?_⟩
    show (MonoidAlgebra.mapDomainRingHom Λ i
        (MonoidAlgebra.mapDomainRingHom Λ H.subtype b * x)) • p =
      MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) b •
        (MonoidAlgebra.mapDomainRingHom Λ i x • p)
    rw [map_mul, ← hcomp]
    exact mul_smul _ _ _
  have : Module.Projective Λ[G] Q :=
    Module.Projective.of_equiv' (M := restrictedModule Λ P i)
      { toFun := id
        invFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have : Module.Projective Λ[H] Λ[G] :=
    MonoidAlgebra.projective_restrictScalars_subgroup Λ H
  exact Module.Projective.trans_of_isScalarTower Λ[H] Λ[G] Q

/-- The action of a commuting element as a centralizer-linear endomorphism. -/
noncomputable def centralizerEndomorphism (i : G →* Γ) (γ : Γ) :
    { f : Module.End Λ[centralizer i γ]
        (restrictedModule Λ P (i.comp (centralizer i γ).subtype)) //
      ∀ p : P, f p = (MonoidAlgebra.single γ (1 : Λ)) • p } := by
  classical
  let H := centralizer i γ
  let f : Module.End Λ[H] (restrictedModule Λ P (i.comp H.subtype)) :=
      { toFun := fun p => MonoidAlgebra.single γ (1 : Λ) • p
        map_add' := fun p q => smul_add _ _ _
        map_smul' := by
          intro a p
          change MonoidAlgebra.single γ (1 : Λ) •
              (MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a • p) =
            MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a •
              (MonoidAlgebra.single γ (1 : Λ) • p)
          calc
            _ = (MonoidAlgebra.single γ (1 : Λ) *
                MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a) • p :=
                  (mul_smul _ _ _).symm
            _ = (MonoidAlgebra.mapDomainRingHom Λ (i.comp H.subtype) a *
                MonoidAlgebra.single γ (1 : Λ)) • p := by
                  rw [centralizer_commutes_mapDomain i γ H
                    (fun g => g.property) a]
            _ = _ := mul_smul _ _ _ }
  exact ⟨f, fun p => rfl⟩

/-- The trace of `γ` relative to its centralizer. -/
noncomputable def centralizerTrace (i : G →* Γ)
    [Module.Finite Λ[G] (restrictedModule Λ P i)]
    [Module.Projective Λ[G] (restrictedModule Λ P i)]
    (γ : Γ) : AdditiveCommutatorQuotient Λ := by
  let H := centralizer i γ
  letI : Module.Finite Λ[H] (restrictedModule Λ P (i.comp H.subtype)) :=
    restricted_module_finite i H
  letI : Module.Projective Λ[H] (restrictedModule Λ P (i.comp H.subtype)) :=
    restricted_module_projective i H
  exact groupTrace Λ H (restrictedModule Λ P (i.comp H.subtype))
    (centralizerEndomorphism i γ).val

/-- Finite generation over the coefficients of a finite group algebra. -/
lemma finite_over_coefficients (i : G →* Γ)
    [Module.Finite Λ[G] (restrictedModule Λ P i)] :
    Module.Finite Λ (coefficientModule Λ Γ P) := by
  let Q := restrictedModule Λ P i
  let : Module Λ Q := Module.compHom Q
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := G))
  have : IsScalarTower Λ Λ[G] Q := by
    refine ⟨fun r a p => ?_⟩
    rw [groupAlgebra_smul_eq_mul Λ G r a]
    show (MonoidAlgebra.mapDomainRingHom Λ i
      (MonoidAlgebra.singleOneRingHom (R := Λ) (M := G) r * a)) • p =
      MonoidAlgebra.singleOneRingHom (R := Λ) (M := G) r •
        (MonoidAlgebra.mapDomainRingHom Λ i a • p)
    rw [map_mul]
    exact mul_smul _ _ _
  let : Module.Finite Λ Λ[G] := MonoidAlgebra.moduleFinite
  have hQ : Module.Finite Λ Q := Module.Finite.trans Λ[G] Q
  let e : Q ≃ₗ[Λ] coefficientModule Λ Γ P := restrictedCoefficientLinearEquiv i
  exact Module.Finite.equiv e

omit [Finite G] in
/-- Projectivity over the coefficients of a finite group algebra. -/
lemma projective_over_coefficients (i : G →* Γ)
    [Module.Projective Λ[G] (restrictedModule Λ P i)] :
    Module.Projective Λ (coefficientModule Λ Γ P) := by
  let Q := restrictedModule Λ P i
  let : Module Λ Q := Module.compHom Q
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := G))
  let : Module Λ (coefficientModule Λ Γ P) := Module.compHom
    (coefficientModule Λ Γ P)
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ))
  let e : Q ≃ₗ[Λ] coefficientModule Λ Γ P := restrictedCoefficientLinearEquiv i
  let : Module.Projective Λ Q := by
    simpa only [Module.compHom] using
      (projective_restrictScalars_groupAlgebra Λ G Q)
  exact Module.Projective.of_equiv' e

/-- The coefficient-linear action of `γ`. -/
noncomputable def coefficientEndomorphism (γ : Γ) :
    { f : Module.End Λ (coefficientModule Λ Γ P) //
      ∀ p : P, f p = (MonoidAlgebra.single γ (1 : Λ)) • p } := by
  classical
  let z : Λ[Γ] := MonoidAlgebra.single γ (1 : Λ)
  let f : Module.End Λ (coefficientModule Λ Γ P) :=
      { toFun := fun p => z • p
        map_add' := fun p q => smul_add _ _ _
        map_smul' := by
          intro r p
          change z • (MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r • p) =
            MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r • (z • p)
          have hcomm : z * MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r =
              MonoidAlgebra.singleOneRingHom (R := Λ) (M := Γ) r * z := by
            simp [z, MonoidAlgebra.single_mul_single,
              MonoidAlgebra.singleOneRingHom]
          rw [← mul_smul z, hcomm, mul_smul] }
  exact ⟨f, fun p => rfl⟩

/-- The ordinary trace is the centralizer order times the centralizer trace. -/
@[stacks 03UB, sga "4½ Rapport 5.9" "(5.9.1)"]
lemma trace_eq_card_centralizer_nsmul_groupTrace (i : G →* Γ)
    [Module.Finite Λ[G] (restrictedModule Λ P i)]
    [Module.Projective Λ[G] (restrictedModule Λ P i)]
    (γ : Γ) :
    letI : Module.Finite Λ (coefficientModule Λ Γ P) :=
      finite_over_coefficients (P := P) i
    letI : Module.Projective Λ (coefficientModule Λ Γ P) :=
      projective_over_coefficients (P := P) i
    projectiveModuleTrace Λ (coefficientModule Λ Γ P)
      (coefficientEndomorphism (P := P) γ).val =
      Nat.card (centralizer i γ) • centralizerTrace (P := P) i γ := by
  let H := centralizer i γ
  let Q := restrictedModule Λ P (i.comp H.subtype)
  let : Module Λ Q := Module.compHom Q
    (MonoidAlgebra.singleOneRingHom (R := Λ) (M := H))
  let : Module.Finite Λ[H] Q := restricted_module_finite i H
  let : Module.Projective Λ[H] Q := restricted_module_projective i H
  let : Module.Finite Λ Q := finite_restrictScalars_groupAlgebra Λ H Q
  let : Module.Projective Λ Q := projective_restrictScalars_groupAlgebra Λ H Q
  let fH : Module.End Λ[H] Q := (centralizerEndomorphism (P := P) i γ).val
  let fΛ : Module.End Λ Q :=
    { fH with
      map_smul' := by
        intro r p
        show fH (r • p) = r • fH p
        exact fH.map_smul (MonoidAlgebra.singleOneRingHom (R := Λ) (M := H) r) p }
  let : Module.Finite Λ (coefficientModule Λ Γ P) :=
    finite_over_coefficients (P := P) i
  let : Module.Projective Λ (coefficientModule Λ Γ P) :=
    projective_over_coefficients (P := P) i
  let e : Q ≃ₗ[Λ] coefficientModule Λ Γ P :=
    restrictedCoefficientLinearEquiv (i.comp H.subtype)
  have hf : e.toLinearMap.comp (fΛ.comp e.symm.toLinearMap) =
      (coefficientEndomorphism (P := P) γ).val := by
    ext p
    show MonoidAlgebra.single γ (1 : Λ) • p =
      MonoidAlgebra.single γ (1 : Λ) • p
    rfl
  have hleft :
      projectiveModuleTrace Λ (coefficientModule Λ Γ P)
        (coefficientEndomorphism (P := P) γ).val =
      projectiveModuleTrace Λ Q fΛ := by
    rw [← hf]
    exact projectiveModuleTrace_conj Λ e fΛ
  change
    projectiveModuleTrace Λ (coefficientModule Λ Γ P)
        (coefficientEndomorphism (P := P) γ).val =
      Nat.card H • centralizerTrace (P := P) i γ
  rw [hleft]
  show projectiveModuleTrace Λ Q fΛ = Nat.card H • groupTrace Λ H Q fH
  simpa [fΛ, fH, centralizerTrace, H, Q] using
    projectiveModuleTrace_restrictScalars_groupAlgebra Λ H Q fH

end Stacks.Trace

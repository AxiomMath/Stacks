module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Branches.Completion

/-!
# Pushouts of Noetherian complete local algebras

Pushouts of Noetherian complete local algebras along a morphism of the
completed base category.

## Main results

* `CompleteLocalAlgCat.hasPushouts` supplies pushouts in the category of
  Noetherian complete local algebras with fixed residue field.

## Implementation notes

The assertion is expressed as a named instance of `CategoryTheory.Limits.HasPushouts`, so
subsequent constructions can obtain the relevant pushouts by typeclass inference.

## References

* [Stacks Project, Tag 06SB](https://stacks.math.columbia.edu/tag/06SB)
-/

public section

namespace Deformation

/-! ### Pushouts of Noetherian complete local algebras -/

section
open CategoryTheory Limits
universe u v w

namespace CompleteLocalAlgCat

variable (Λ : Type u) (k : Type w) [CommRing Λ] [Field k] [Algebra Λ k]

attribute [local instance] CompleteLocalAlgCat.commRing
  CompleteLocalAlgCat.algebra

open CompleteLocalAlgCat
open IsLocalRing




section Span

variable {Λ k}
variable {R A B : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ A) (g : R ⟶ B)

@[instance_reducible]
private noncomputable def algebraRk : Algebra R k :=
  (residueAlgHom (Λ := Λ) (k := k) R).toRingHom.toAlgebra

@[instance_reducible]
private noncomputable def algebraRA : Algebra R A := f.hom.toRingHom.toAlgebra
@[instance_reducible]
private noncomputable def algebraRB : Algebra R B := g.hom.toRingHom.toAlgebra

private lemma residueAlgHom_commutes_R_A (r : R) :
    residueAlgHom (Λ := Λ) (k := k) A (f.hom r) =
      residueAlgHom (Λ := Λ) (k := k) R r := f.residue_comm r

private noncomputable def residueAlgHomR_A :
    letI := algebraRk (R := R)
    letI := algebraRA f
    A →ₐ[R] k := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  exact
    { (residueAlgHom (Λ := Λ) (k := k) A).toRingHom with
      commutes' := residueAlgHom_commutes_R_A f }

private noncomputable def residueAlgHomR_B :
    letI := algebraRk (R := R)
    letI := algebraRB g
    B →ₐ[R] k := by
  letI := algebraRk (R := R)
  letI := algebraRB g
  exact
    { (residueAlgHom (Λ := Λ) (k := k) B).toRingHom with
      commutes' := residueAlgHom_commutes_R_A g }

private noncomputable abbrev tensor :=
  letI := algebraRA f
  letI := algebraRB g
  TensorProduct R A B

private noncomputable def tensorResidue :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    tensor f g →ₐ[R] k := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  exact Algebra.TensorProduct.productMap (residueAlgHomR_A f) (residueAlgHomR_B g)

private noncomputable abbrev tensorIdeal : Ideal (tensor f g) := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  exact RingHom.ker (tensorResidue f g).toRingHom

private lemma tensorResidue_surjective : Function.Surjective (tensorResidue f g) := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  intro x
  obtain ⟨a, rfl⟩ := residueAlgHom_surjective (Λ := _) (k := _) A x
  refine ⟨(Algebra.TensorProduct.includeLeft : A →ₐ[R] tensor f g) a, ?_⟩
  change Algebra.TensorProduct.productMap (residueAlgHomR_A f) (residueAlgHomR_B g)
      (a ⊗ₜ[R] 1) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  rfl

private instance tensorIdeal_isMaximal : (tensorIdeal f g).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (tensorResidue_surjective f g)

private noncomputable def tensorMapToResidues :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    tensor f g →ₐ[R] TensorProduct R k k := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  exact Algebra.TensorProduct.map (residueAlgHomR_A f) (residueAlgHomR_B g)

private lemma tensorResidue_eq_lmul_comp :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    tensorResidue f g =
      (Algebra.TensorProduct.lmul' R (S := k)).comp (tensorMapToResidues f g) := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [tensorResidue, tensorMapToResidues, residueAlgHomR_A, residueAlgHomR_B,
    Algebra.TensorProduct.lmul'_apply_tmul]

private lemma lmul_injective :
    letI := algebraRk (R := R)
    Function.Injective (Algebra.TensorProduct.lmul' R (S := k)) := by
  let := algebraRk (R := R)
  change Function.Injective (LinearMap.mul' R k)
  exact (LinearMap.mul'_bijective_of_surjective (R := R) (A := k)
    (residueAlgHom_surjective (Λ := _) (k := _) R)).injective

private lemma tensorIdeal_eq_map_ker :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    tensorIdeal f g =
      Ideal.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] tensor f g)
          (RingHom.ker (residueAlgHomR_A f).toRingHom) ⊔
        Ideal.map (Algebra.TensorProduct.includeRight : B →ₐ[R] tensor f g)
          (RingHom.ker (residueAlgHomR_B g).toRingHom) := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  rw [tensorIdeal, tensorResidue_eq_lmul_comp f g]
  have hker : RingHom.ker
      ((Algebra.TensorProduct.lmul' R (S := k)).comp (tensorMapToResidues f g)).toRingHom =
      RingHom.ker (tensorMapToResidues f g).toRingHom := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply]
    exact map_eq_zero_iff _ (lmul_injective (R := R))
  rw [hker]
  exact Algebra.TensorProduct.map_ker _ _
    (residueAlgHom_surjective (Λ := _) (k := _) A)
    (residueAlgHom_surjective (Λ := _) (k := _) B)

private lemma tensorIdeal_fg : (tensorIdeal f g).FG := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  rw [tensorIdeal_eq_map_ker f g]
  apply Submodule.FG.sup <;> exact (Ideal.fg_of_isNoetherianRing _).map _

private noncomputable abbrev completedTensor :=
  AdicCompletion (tensorIdeal f g) (tensor f g)

private lemma scalarTowerRA (f : R ⟶ A) :
    letI := algebraRA f
    IsScalarTower Λ R A := by
  let := algebraRA f
  exact IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap Λ A x = f.hom (algebraMap Λ R x)
    exact (f.hom.commutes x).symm

private lemma scalarTowerRB (g : R ⟶ B) :
    letI := algebraRB g
    IsScalarTower Λ R B :=
  scalarTowerRA g

private lemma scalarTowerTensor (f : R ⟶ A) (g : R ⟶ B) :
    letI := algebraRA f
    letI := algebraRB g
    IsScalarTower Λ R (tensor f g) := by
  let := algebraRA f
  let := algebraRB g
  let := scalarTowerRA f
  exact IsScalarTower.of_algebraMap_eq fun x => by
    rw [Algebra.TensorProduct.algebraMap_apply (S := Λ) (R := R)
      (A := A) (B := B),
      IsScalarTower.algebraMap_apply Λ R A]
    rw [← Algebra.TensorProduct.includeLeft_apply (R := R) (S := Λ) (A := A) (B := B)]
    exact Algebra.TensorProduct.includeLeft.commutes (algebraMap Λ R x)

private lemma scalarTowerResidue :
    letI := algebraRk (R := R)
    IsScalarTower Λ R k := by
  let := algebraRk (R := R)
  exact IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap Λ k x = residueAlgHom (Λ := Λ) (k := k) R (algebraMap Λ R x)
    exact ((residueAlgHom (Λ := Λ) (k := k) R).commutes x).symm

private noncomputable def tensorQuotientEquiv :
    (tensor f g ⧸ tensorIdeal f g) ≃+* k :=
  RingHom.quotientKerEquivOfSurjective (tensorResidue_surjective f g)

private noncomputable def completedResidue : completedTensor f g →ₐ[Λ] k := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerTensor f g
  letI := scalarTowerResidue (Λ := Λ) (k := k) (R := R)
  let q : completedTensor f g →+* tensor f g ⧸ tensorIdeal f g :=
    (AdicCompletion.evalOneₐ (tensorIdeal f g)).toRingHom
  let h : completedTensor f g →+* k :=
    (tensorQuotientEquiv f g).toRingHom.comp q
  exact
    { h with
      commutes' := fun x => by
        change tensorQuotientEquiv f g
            (AdicCompletion.evalOneₐ (tensorIdeal f g)
              (algebraMap Λ (completedTensor f g) x)) = algebraMap Λ k x
        rw [show algebraMap Λ (completedTensor f g) x =
          AdicCompletion.of (tensorIdeal f g) (tensor f g)
            (algebraMap Λ (tensor f g) x) from rfl]
        rw [AdicCompletion.evalOneₐ_of]
        rw [IsScalarTower.algebraMap_apply Λ R (tensor f g)]
        change RingHom.quotientKerEquivOfSurjective (tensorResidue_surjective f g)
          (Ideal.Quotient.mk (RingHom.ker (tensorResidue f g).toRingHom)
            (algebraMap R (tensor f g) (algebraMap Λ R x))) = _
        rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
        have hc := (tensorResidue f g).commutes (algebraMap Λ R x)
        rw [IsScalarTower.algebraMap_apply Λ R k]
        exact hc }

private lemma completedResidue_surjective : Function.Surjective (completedResidue f g) := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  exact (tensorQuotientEquiv f g).surjective.comp
    (AdicCompletion.evalOneₐ_surjective (tensorIdeal f g))

private lemma tensorQuotient_noetherian :
    IsNoetherianRing (tensor f g ⧸ tensorIdeal f g) :=
  isNoetherianRing_of_ringEquiv k (tensorQuotientEquiv f g).symm

private theorem completedTensorCompleteLocal :
    IsNoetherianCompleteLocalRing (completedTensor f g) := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  let h := completion_noetherian (tensor f g) (tensorIdeal f g)
    (tensorQuotient_noetherian f g) (tensorIdeal_fg f g)
  have hmax : (Ideal.map (algebraMap (tensor f g) (completedTensor f g))
      (tensorIdeal f g)).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le (tensorIdeal f g) (tensorIdeal f g)
      le_rfl (tensorIdeal_fg f g)
  let : IsAdicComplete
      (Ideal.map (algebraMap (tensor f g) (completedTensor f g)) (tensorIdeal f g))
      (completedTensor f g) := h.2
  let hlocal : IsLocalRing (completedTensor f g) :=
    isLocalRing_of_isAdicComplete_maximal
      (Ideal.map (algebraMap (tensor f g) (completedTensor f g)) (tensorIdeal f g))
  refine ⟨h.1, hlocal, ?_⟩
  rw [show @maximalIdeal (completedTensor f g) _ hlocal =
    Ideal.map (algebraMap (tensor f g) (completedTensor f g)) (tensorIdeal f g) from
      (IsLocalRing.eq_maximalIdeal hmax).symm]
  exact h.2

private lemma ker_completedResidue :
    letI := (completedTensorCompleteLocal f g).isLocal
    RingHom.ker (completedResidue f g).toRingHom = maximalIdeal (completedTensor f g) := by
  let := (completedTensorCompleteLocal f g).isLocal
  exact IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (completedResidue_surjective f g))

private noncomputable def completedResidueEquiv :
    letI := (completedTensorCompleteLocal f g).isLocal
    ResidueField (completedTensor f g) ≃ₐ[Λ] k := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  letI := (completedTensorCompleteLocal f g).isLocal
  have hker := ker_completedResidue f g
  let e₀ : ResidueField (completedTensor f g) ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective (completedResidue_surjective f g))
  exact
    { e₀ with
      commutes' := fun x => by
        change ((Ideal.quotEquivOfEq hker.symm).trans
          (RingHom.quotientKerEquivOfSurjective (completedResidue_surjective f g)))
          (Ideal.Quotient.mk _ (algebraMap Λ (completedTensor f g) x)) = algebraMap Λ k x
        rw [RingEquiv.trans_apply]
        rw [Ideal.quotEquivOfEq_mk]
        rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
        change completedResidue f g (algebraMap Λ (completedTensor f g) x) = _
        exact (completedResidue f g).commutes x }

private noncomputable def pushoutObj : CompleteLocalAlgCat.{u, v, w} Λ k where
  carrier := completedTensor f g
  commRing := inferInstance
  algebra := inferInstance
  completeLocal := completedTensorCompleteLocal f g
  residueEquiv := completedResidueEquiv f g

private lemma residueAlgHom_pushoutObj :
    residueAlgHom (Λ := Λ) (k := k) (pushoutObj f g) = completedResidue f g := by
  let := (completedTensorCompleteLocal f g).isLocal
  have hker := ker_completedResidue f g
  ext x
  change ((Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective (completedResidue_surjective f g)))
      (Ideal.Quotient.mk (maximalIdeal (completedTensor f g))
        (x : completedTensor f g)) = _
  rw [RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk hker.symm (x : completedTensor f g)]
  change RingHom.quotientKerEquivOfSurjective (completedResidue_surjective f g)
      (Ideal.Quotient.mk (RingHom.ker (completedResidue f g).toRingHom)
        (x : completedTensor f g)) = completedResidue f g (x : completedTensor f g)
  exact RingHom.quotientKerEquivOfSurjective_apply_mk
    (completedResidue_surjective f g) (x : completedTensor f g)

private noncomputable abbrev algebraRPt (s : PushoutCocone f g) : Algebra R s.pt :=
  (s.inl.hom.toRingHom.comp f.hom.toRingHom).toAlgebra

private lemma scalarTowerPt (s : PushoutCocone f g) :
    letI := algebraRPt f g s
    IsScalarTower Λ R s.pt := by
  let := algebraRPt f g s
  exact IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap Λ s.pt x = s.inl.hom (f.hom (algebraMap Λ R x))
    rw [f.hom.commutes, s.inl.hom.commutes]

private noncomputable def tensorToTarget
    (s : PushoutCocone f g) : tensor f g →ₐ[Λ] s.pt := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  letI := algebraRPt f g s
  have hspanAlg : s.inl.hom.comp f.hom = s.inr.hom.comp g.hom := by
    simpa only [CompleteLocalAlgCat.comp_hom] using
      congrArg (fun h : R ⟶ s.pt => h.hom) s.condition
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  let left : A →ₐ[R] s.pt :=
    { s.inl.hom.toRingHom with commutes' := fun _ => rfl }
  let right : B →ₐ[R] s.pt :=
    { toRingHom := s.inr.hom.toRingHom
      commutes' := fun r => by
        change s.inr.hom (g.hom r) = s.inl.hom (f.hom r)
        exact (DFunLike.congr_fun hspanAlg r).symm }
  let m : tensor f g →ₐ[R] s.pt := Algebra.TensorProduct.productMap left right
  letI := scalarTowerPt f g s
  letI := scalarTowerTensor f g
  exact m.restrictScalars Λ

private lemma tensorToTarget_includeLeft (s : PushoutCocone f g) (a : A) :
    letI := algebraRPt f g s
    letI := scalarTowerPt f g s
    letI := algebraRA f
    letI := algebraRB g
    letI := scalarTowerRA f
    letI := scalarTowerRB g
    letI := scalarTowerTensor f g
    tensorToTarget f g s
      (Algebra.TensorProduct.includeLeft (R := R) (S := Λ) (A := A) (B := B) a) =
      s.inl.hom a := by
  let := algebraRA f
  let := algebraRB g
  let := scalarTowerRA f
  let := scalarTowerRB g
  let := scalarTowerTensor f g
  let := algebraRPt f g s
  let := scalarTowerPt f g s
  change Algebra.TensorProduct.productMap _ _ (a ⊗ₜ[R] 1) = _
  rw [Algebra.TensorProduct.productMap_left_apply]
  rfl

private lemma tensorToTarget_includeRight (s : PushoutCocone f g) (b : B) :
    letI := algebraRPt f g s
    letI := scalarTowerPt f g s
    letI := algebraRA f
    letI := algebraRB g
    letI := scalarTowerRA f
    letI := scalarTowerRB g
    letI := scalarTowerTensor f g
    tensorToTarget f g s
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).restrictScalars Λ b) =
      s.inr.hom b := by
  let := algebraRA f
  let := algebraRB g
  let := scalarTowerRA f
  let := scalarTowerRB g
  let := scalarTowerTensor f g
  let := algebraRPt f g s
  let := scalarTowerPt f g s
  change Algebra.TensorProduct.productMap _ _ (1 ⊗ₜ[R] b) = _
  rw [Algebra.TensorProduct.productMap_right_apply]
  rfl

private lemma tensorToTarget_residue
    (s : PushoutCocone f g) :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    (residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp
        (tensorToTarget f g s).toRingHom = (tensorResidue f g).toRingHom := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  let := algebraRPt f g s
  let := scalarTowerRA f
  let := scalarTowerRB g
  let := scalarTowerTensor f g
  let := scalarTowerResidue (Λ := Λ) (k := k) (R := R)
  have hspanAlg : s.inl.hom.comp f.hom = s.inr.hom.comp g.hom := by
    simpa only [CompleteLocalAlgCat.comp_hom] using
      congrArg (fun h : R ⟶ s.pt => h.hom) s.condition
  let left : A →ₐ[R] s.pt :=
    { s.inl.hom.toRingHom with commutes' := fun _ => rfl }
  let right : B →ₐ[R] s.pt :=
    { toRingHom := s.inr.hom.toRingHom
      commutes' := fun r => by
        change s.inr.hom (g.hom r) = s.inl.hom (f.hom r)
        exact (DFunLike.congr_fun hspanAlg r).symm }
  let resToK : s.pt →ₐ[R] k :=
    { toRingHom := (residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom
      commutes' := fun r => by
        change residueAlgHom (Λ := Λ) (k := k) s.pt (s.inl.hom (f.hom r)) =
          residueAlgHom (Λ := Λ) (k := k) R r
        rw [residueAlgHom_apply, residueAlgHom_apply]
        rw [s.inl.residue_comm, f.residue_comm] }
  have hA : resToK.comp left = residueAlgHomR_A f := by
    ext a
    change residueAlgHom (Λ := Λ) (k := k) s.pt (s.inl.hom a) =
      residueAlgHom (Λ := Λ) (k := k) A a
    rw [residueAlgHom_apply, residueAlgHom_apply]
    exact s.inl.residue_comm a
  have hB : resToK.comp right = residueAlgHomR_B g := by
    ext b
    change residueAlgHom (Λ := Λ) (k := k) s.pt (s.inr.hom b) =
      residueAlgHom (Λ := Λ) (k := k) B b
    rw [residueAlgHom_apply, residueAlgHom_apply]
    exact s.inr.residue_comm b
  have hres : resToK.comp (Algebra.TensorProduct.productMap left right) =
      tensorResidue f g := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.productMap_apply_tmul]
    rw [map_mul]
    change resToK (left a) * resToK (right b) =
      residueAlgHomR_A f a * residueAlgHomR_B g b
    rw [← DFunLike.congr_fun hA a, ← DFunLike.congr_fun hB b]
    rfl
  exact congrArg (fun h : (tensor f g) →ₐ[R] k => h.toRingHom) hres

private lemma residueAlgHom_ker_maximal (X : CompleteLocalAlgCat.{u, v, w} Λ k) :
    RingHom.ker (residueAlgHom (Λ := Λ) (k := k) X).toRingHom = maximalIdeal X :=
  IsLocalRing.eq_maximalIdeal
    (RingHom.ker_isMaximal_of_surjective _ (residueAlgHom_surjective (Λ := Λ) (k := k) X))

private lemma map_le_maximalIdeal_of_le_ker {T : Type*} [CommRing T]
    (X : CompleteLocalAlgCat.{u, v, w} Λ k) (ψ : T →+* X) (J : Ideal T)
    (h : J ≤ RingHom.ker ((residueAlgHom (Λ := Λ) (k := k) X).toRingHom.comp ψ)) :
    J.map ψ ≤ maximalIdeal X := by
  rw [← residueAlgHom_ker_maximal X, Ideal.map_le_iff_le_comap]
  exact h

private lemma tensorToTarget_ideal_le
    (s : PushoutCocone f g) :
    (tensorIdeal f g).map (tensorToTarget f g s).toRingHom ≤ maximalIdeal s.pt := by
  let := algebraRPt f g s
  refine map_le_maximalIdeal_of_le_ker s.pt _ _ ?_
  rw [tensorIdeal, tensorToTarget_residue f g s]

private lemma completedTensorMap_ideal_le
    (s : PushoutCocone f g) (φ : completedTensor f g →ₐ[Λ] s.pt)
    (hφ : ∀ c, φ (algebraMap (tensor f g) (completedTensor f g) c) =
      tensorToTarget f g s c) :
    (tensorIdeal f g).map (algebraMap (tensor f g) (completedTensor f g)) ≤
      RingHom.ker ((residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp φ.toRingHom) := by
  let E : tensor f g →+* completedTensor f g := algebraMap (tensor f g) (completedTensor f g)
  rw [Ideal.map_le_iff_le_comap]
  change tensorIdeal f g ≤ RingHom.ker
    ((residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp (φ.toRingHom.comp E))
  have hcomp : φ.toRingHom.comp E = (tensorToTarget f g s).toRingHom := RingHom.ext hφ
  rw [hcomp, tensorToTarget_residue f g s]


private noncomputable def completedTensorMap
    (s : PushoutCocone f g) : completedTensor f g →ₐ[Λ] s.pt := by
  letI := algebraRPt f g s
  letI : IsAdicComplete (maximalIdeal s.pt) s.pt := s.pt.completeLocal.isComplete
  exact Classical.choose (exists_algHom_adicCompletion_of_map_le
    (I := tensorIdeal f g) (K := maximalIdeal s.pt)
    (tensorToTarget f g s) (tensorToTarget_ideal_le f g s))

private lemma completedTensorMap_algebraMap
    (s : PushoutCocone f g) (c : tensor f g) :
    completedTensorMap f g s (algebraMap (tensor f g) (completedTensor f g) c) =
      tensorToTarget f g s c := by
  let := algebraRPt f g s
  let : IsAdicComplete (maximalIdeal s.pt) s.pt := s.pt.completeLocal.isComplete
  exact Classical.choose_spec (exists_algHom_adicCompletion_of_map_le
    (I := tensorIdeal f g) (K := maximalIdeal s.pt)
    (tensorToTarget f g s) (tensorToTarget_ideal_le f g s)) c

private noncomputable def tensorToCompleted :
    tensor f g →ₐ[Λ] completedTensor f g := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  letI := scalarTowerTensor f g
  letI : Algebra (tensor f g) (completedTensor f g) := inferInstance
  letI : IsScalarTower Λ (tensor f g) (completedTensor f g) := inferInstance
  exact
    { (algebraMap (tensor f g) (completedTensor f g)) with
      commutes' := fun x => IsScalarTower.algebraMap_apply Λ (tensor f g)
        (completedTensor f g) x }

private noncomputable def pushoutLeftAlgHom : A →ₐ[Λ] completedTensor f g := by
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  letI := scalarTowerTensor f g
  exact (tensorToCompleted f g).comp
    (Algebra.TensorProduct.includeLeft (R := R) (S := Λ) (A := A) (B := B))

private noncomputable def pushoutRightAlgHom : B →ₐ[Λ] completedTensor f g := by
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  letI := scalarTowerTensor f g
  exact (tensorToCompleted f g).comp
    ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).restrictScalars Λ)

private lemma local_of_residue_commute
    {X Y : CompleteLocalAlgCat.{u, v, w} Λ k} (φ : X →ₐ[Λ] Y)
    (hres : (residueAlgHom (Λ := Λ) (k := k) Y).comp φ =
      residueAlgHom (Λ := Λ) (k := k) X) : IsLocalHom φ.toRingHom := by
  apply ((IsLocalRing.local_hom_TFAE φ.toRingHom).out 2 1).mp
  rintro _ ⟨x, hx, rfl⟩
  rw [← residueAlgHom_ker_maximal Y, SetLike.mem_coe, RingHom.mem_ker]
  rw [← residueAlgHom_ker_maximal X, SetLike.mem_coe, RingHom.mem_ker] at hx
  exact (DFunLike.congr_fun hres x).trans hx

private lemma completedResidue_algebraMap (c : tensor f g) :
    completedResidue f g (algebraMap (tensor f g) (completedTensor f g) c) =
      tensorResidue f g c := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  let := scalarTowerRA f
  let := scalarTowerTensor f g
  let := scalarTowerResidue (Λ := Λ) (k := k) (R := R)
  simp only [completedResidue, AlgHom.coe_mk]
  change RingHom.quotientKerEquivOfSurjective (tensorResidue_surjective f g)
    (Ideal.Quotient.mk (RingHom.ker (tensorResidue f g).toRingHom) c) = _
  rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

private lemma ringHom_eq_of_evalOne
    {A : Type*} [CommRing A] (I : Ideal A)
    (hI : I.FG) (φ ψ : AdicCompletion I A →+* k)
    (hφ : (I.map (algebraMap A (AdicCompletion I A))) ≤ RingHom.ker φ)
    (hψ : (I.map (algebraMap A (AdicCompletion I A))) ≤ RingHom.ker ψ)
    (hbase : ∀ a, φ (algebraMap A (AdicCompletion I A) a) =
      ψ (algebraMap A (AdicCompletion I A) a)) : φ = ψ := by
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I x)
  have hEval : AdicCompletion.evalOneₐ I x = Ideal.Quotient.mk I a := ha.symm
  have hmem : x - algebraMap A (AdicCompletion I A) a ∈
      I.map (algebraMap A (AdicCompletion I A)) := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I hI]
    change AdicCompletion.evalOneₐ I
      (x - algebraMap A (AdicCompletion I A) a) = 0
    rw [map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.evalOneₐ_of, hEval]
    exact sub_self _
  have hφx := hφ hmem
  have hψx := hψ hmem
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hφx hψx
  exact hφx.trans ((hbase a).trans hψx.symm)

private lemma completedMaps_ext
    {A S : Type*} [CommRing A] [CommRing S] [Algebra Λ A] [Algebra Λ S]
    (I : Ideal A) (K : Ideal S) [IsAdicComplete K S] (hI : I.FG)
    (φ ψ : AdicCompletion I A →ₐ[Λ] S)
    (hφ : I.map (φ.toRingHom.comp (algebraMap A (AdicCompletion I A))) ≤ K)
    (hψ : I.map (ψ.toRingHom.comp (algebraMap A (AdicCompletion I A))) ≤ K)
    (hbase : ∀ a, φ (algebraMap A (AdicCompletion I A) a) =
      ψ (algebraMap A (AdicCompletion I A) a)) : φ = ψ := by
  apply IsAdicComplete.algHom_ext K
  intro n
  apply AlgHom.ext
  intro x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  have hEval : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) a := ha.symm
  have hle : I ^ n ≤ I ^ n • (⊤ : Ideal A) := by
    simp
  have hEval' : AdicCompletion.eval I A n x =
      Ideal.Quotient.mk (I ^ n • (⊤ : Ideal A)) a := by
    rw [← AdicCompletion.factor_evalₐ_eq_eval I x hle, hEval]
    simp
  have hmemSub : x - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n) • (⊤ : Submodule A (AdicCompletion I A)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    change AdicCompletion.eval I A n
      (x - AdicCompletion.of I A a) = 0
    rw [map_sub, AdicCompletion.eval_of, hEval']
    exact sub_self _
  have hmem : x - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
    rw [Ideal.smul_top_eq_map (I ^ n)] at hmemSub
    exact (Submodule.restrictScalars_mem A _ _).mp hmemSub
  have hd (χ : AdicCompletion I A →ₐ[Λ] S)
      (hχ : I.map (χ.toRingHom.comp (algebraMap A (AdicCompletion I A))) ≤ K) :
      χ (x - algebraMap A (AdicCompletion I A) a) ∈ K ^ n := by
    have hpow : (I ^ n).map
        (χ.toRingHom.comp (algebraMap A (AdicCompletion I A))) ≤ K ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' hχ n
    exact hpow (by rw [← Ideal.map_map]; exact Ideal.mem_map_of_mem χ.toRingHom hmem)
  have hφd := hd φ hφ
  have hψd := hd ψ hψ
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2
  have hφ' : φ x - φ (algebraMap A (AdicCompletion I A) a) ∈ K ^ n := by
    simpa only [map_sub] using hφd
  have hψ' : ψ (algebraMap A (AdicCompletion I A) a) - ψ x ∈ K ^ n := by
    have hn := (K ^ n).neg_mem hψd
    simpa only [map_sub, neg_sub] using hn
  change φ x - ψ x ∈ K ^ n
  rw [show φ x - ψ x =
      (φ x - φ (algebraMap A (AdicCompletion I A) a)) +
        (ψ (algebraMap A (AdicCompletion I A) a) - ψ x) by rw [hbase a]; ring]
  exact add_mem hφ' hψ'

private lemma completedTensorMap_residue
    (s : PushoutCocone f g) (φ : completedTensor f g →ₐ[Λ] s.pt)
    (hφ : ∀ c, φ (algebraMap (tensor f g) (completedTensor f g) c) =
      tensorToTarget f g s c)
    (hideal : (tensorIdeal f g).map (algebraMap (tensor f g) (completedTensor f g)) ≤
      RingHom.ker ((residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp φ.toRingHom)) :
    (residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp φ.toRingHom =
      (completedResidue f g).toRingHom := by
  let I := tensorIdeal f g
  let E : tensor f g →+* completedTensor f g := algebraMap (tensor f g) (completedTensor f g)
  let ψ : completedTensor f g →+* k := (completedResidue f g).toRingHom
  have hψ : I.map E ≤ RingHom.ker ψ := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I (tensorIdeal_fg f g)]
    intro x hx
    change AdicCompletion.evalOneₐ I x = 0 at hx
    change tensorQuotientEquiv f g (AdicCompletion.evalOneₐ I x) = 0
    rw [hx]
    simp
  apply ringHom_eq_of_evalOne I (tensorIdeal_fg f g)
    ((residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp φ.toRingHom)
    ψ hideal hψ
  intro c
  change residueAlgHom (Λ := Λ) (k := k) s.pt (φ (E c)) =
    completedResidue f g (E c)
  rw [hφ c, completedResidue_algebraMap]
  exact DFunLike.congr_fun (tensorToTarget_residue f g s) c

private lemma tensorResidue_includeLeft (a : A) :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    tensorResidue f g (Algebra.TensorProduct.includeLeft
      (R := R) (S := R) (A := A) (B := B) a) =
      residueAlgHomR_A f a := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  change Algebra.TensorProduct.productMap (residueAlgHomR_A f) (residueAlgHomR_B g)
    (a ⊗ₜ[R] 1) = _
  rw [Algebra.TensorProduct.productMap_left_apply]

private lemma tensorResidue_includeRight (b : B) :
    letI := algebraRk (R := R)
    letI := algebraRA f
    letI := algebraRB g
    tensorResidue f g (Algebra.TensorProduct.includeRight
      (R := R) (A := A) (B := B) b) =
      residueAlgHomR_B g b := by
  let := algebraRk (R := R)
  let := algebraRA f
  let := algebraRB g
  change Algebra.TensorProduct.productMap (residueAlgHomR_A f) (residueAlgHomR_B g)
    (1 ⊗ₜ[R] b) = _
  rw [Algebra.TensorProduct.productMap_right_apply]

-- The generated category morphism obligations unfold the completed residue-field equivalence.
private noncomputable def pushoutLeft : A ⟶ pushoutObj f g := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  letI := scalarTowerTensor f g
  let φ : A →ₐ[Λ] pushoutObj f g := pushoutLeftAlgHom f g
  letI := (completedTensorCompleteLocal f g).isLocal
  have hres : (residueAlgHom (Λ := Λ) (k := k) (pushoutObj f g)).comp φ =
      residueAlgHom (Λ := Λ) (k := k) A := by
    ext a
    change completedResidue f g
        (algebraMap (tensor f g) (completedTensor f g)
          (Algebra.TensorProduct.includeLeft (R := R) (S := Λ) (A := A) (B := B) a)) = _
    rw [completedResidue_algebraMap]
    change tensorResidue f g (a ⊗ₜ[R] 1) = _
    exact tensorResidue_includeLeft f g a
  exact
    { hom := φ
      isLocal := local_of_residue_commute φ hres
      residue_comm := fun a => DFunLike.congr_fun hres a }

-- The generated category morphism obligations unfold the completed residue-field equivalence.
private noncomputable def pushoutRight : B ⟶ pushoutObj f g := by
  letI := algebraRk (R := R)
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  letI := scalarTowerTensor f g
  let φ : B →ₐ[Λ] pushoutObj f g := pushoutRightAlgHom f g
  letI := (completedTensorCompleteLocal f g).isLocal
  have hres : (residueAlgHom (Λ := Λ) (k := k) (pushoutObj f g)).comp φ =
      residueAlgHom (Λ := Λ) (k := k) B := by
    ext b
    change completedResidue f g
        (algebraMap (tensor f g) (completedTensor f g)
          (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b)) = _
    rw [completedResidue_algebraMap]
    change tensorResidue f g (1 ⊗ₜ[R] b) = _
    exact tensorResidue_includeRight f g b
  exact
    { hom := φ
      isLocal := local_of_residue_commute φ hres
      residue_comm := fun b => DFunLike.congr_fun hres b }

private noncomputable def pushoutDesc
    (s : PushoutCocone f g) : pushoutObj f g ⟶ s.pt := by
  let φ : completedTensor f g →ₐ[Λ] s.pt := completedTensorMap f g s
  have hφ (c : tensor f g) :
      φ (algebraMap (tensor f g) (completedTensor f g) c) = tensorToTarget f g s c :=
    completedTensorMap_algebraMap f g s c
  have hres₁ : (residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp φ.toRingHom =
      (completedResidue f g).toRingHom :=
    completedTensorMap_residue f g s φ hφ (completedTensorMap_ideal_le f g s φ hφ)
  have hres : (residueAlgHom (Λ := Λ) (k := k) s.pt).comp φ =
      residueAlgHom (Λ := Λ) (k := k) (pushoutObj f g) := by
    ext x
    exact (DFunLike.congr_fun hres₁ x).trans
      (DFunLike.congr_fun (congrArg AlgHom.toRingHom (residueAlgHom_pushoutObj f g)).symm x)
  letI := (completedTensorCompleteLocal f g).isLocal
  exact
    { hom := φ
      isLocal := local_of_residue_commute (X := pushoutObj f g) (Y := s.pt) φ hres
      residue_comm := fun x => DFunLike.congr_fun hres x }

private noncomputable def pushoutCocone : PushoutCocone f g := by
  letI := algebraRA f
  letI := algebraRB g
  letI := scalarTowerRA f
  letI := scalarTowerRB g
  letI := scalarTowerTensor f g
  refine PushoutCocone.mk (pushoutLeft f g) (pushoutRight f g) ?_
  apply CompleteLocalAlgCat.Hom.ext
  ext r
  change tensorToCompleted f g
      (Algebra.TensorProduct.includeLeft (R := R) (S := Λ) (A := A) (B := B)
        (f.hom r)) =
    tensorToCompleted f g
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).restrictScalars Λ
        (g.hom r))
  apply congrArg (tensorToCompleted f g)
  calc
    Algebra.TensorProduct.includeLeft (R := R) (S := Λ) (A := A) (B := B) (f.hom r) =
        Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B)
          (algebraMap R A r) := rfl
    _ = algebraMap R (tensor f g) r :=
      Algebra.TensorProduct.includeLeft.commutes r
    _ = Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)
          (algebraMap R B r) := (Algebra.TensorProduct.includeRight.commutes r).symm
    _ = (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).restrictScalars Λ
          (g.hom r) := rfl

private lemma pushoutDesc_fac_left (s : PushoutCocone f g) :
    pushoutLeft f g ≫ pushoutDesc f g s = s.inl := by
  let := algebraRA f
  let := algebraRB g
  let := scalarTowerRA f
  let := scalarTowerRB g
  let := scalarTowerTensor f g
  let := algebraRPt f g s
  let := scalarTowerPt f g s
  apply CompleteLocalAlgCat.Hom.ext
  ext a
  change completedTensorMap f g s (pushoutLeftAlgHom f g a) = s.inl.hom a
  rw [pushoutLeftAlgHom]
  change completedTensorMap f g s
    (algebraMap (tensor f g) (completedTensor f g)
      (Algebra.TensorProduct.includeLeft (R := R) (S := Λ) (A := A) (B := B) a)) = _
  rw [completedTensorMap_algebraMap]
  exact tensorToTarget_includeLeft f g s a

private lemma pushoutDesc_fac_right (s : PushoutCocone f g) :
    pushoutRight f g ≫ pushoutDesc f g s = s.inr := by
  let := algebraRA f
  let := algebraRB g
  let := scalarTowerRA f
  let := scalarTowerRB g
  let := scalarTowerTensor f g
  let := algebraRPt f g s
  let := scalarTowerPt f g s
  apply CompleteLocalAlgCat.Hom.ext
  ext b
  change completedTensorMap f g s (pushoutRightAlgHom f g b) = s.inr.hom b
  rw [pushoutRightAlgHom]
  change completedTensorMap f g s
    (algebraMap (tensor f g) (completedTensor f g)
      ((Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).restrictScalars Λ b)) = _
  rw [completedTensorMap_algebraMap]
  exact tensorToTarget_includeRight f g s b

private noncomputable def pushoutCoconeIsColimit :
    IsColimit (pushoutCocone f g) := by
  refine PushoutCocone.IsColimit.mk (pushoutCocone f g).condition
    (fun s => pushoutDesc f g s) ?_ ?_ ?_
  · exact pushoutDesc_fac_left f g
  · exact pushoutDesc_fac_right f g
  · intro s m hleft hright
    let := algebraRA f
    let := algebraRB g
    let := scalarTowerRA f
    let := scalarTowerRB g
    let := scalarTowerTensor f g
    let : IsAdicComplete (maximalIdeal s.pt) s.pt := s.pt.completeLocal.isComplete
    let F : completedTensor f g →ₐ[Λ] s.pt := m.hom
    let G : completedTensor f g →ₐ[Λ] s.pt := (pushoutDesc f g s).hom
    let E : tensor f g →+* completedTensor f g :=
      algebraMap (tensor f g) (completedTensor f g)
    have hmleft : m.hom.comp (pushoutLeftAlgHom f g) = s.inl.hom :=
      congrArg (fun q : A ⟶ s.pt => q.hom) hleft
    have hmright : m.hom.comp (pushoutRightAlgHom f g) = s.inr.hom :=
      congrArg (fun q : B ⟶ s.pt => q.hom) hright
    have hFG : F.comp (tensorToCompleted f g) = G.comp (tensorToCompleted f g) := by
      apply AlgHom.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        have hla : F (tensorToCompleted f g
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B) a)) =
            s.inl.hom a := by
          change m.hom (pushoutLeftAlgHom f g a) = s.inl.hom a
          exact DFunLike.congr_fun hmleft a
        have hld : G (tensorToCompleted f g
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B) a)) =
            s.inl.hom a :=
          DFunLike.congr_fun (congrArg (fun q : A ⟶ s.pt => q.hom)
            (pushoutDesc_fac_left f g s)) a
        have hra : F (tensorToCompleted f g
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b)) =
            s.inr.hom b := by
          change m.hom (pushoutRightAlgHom f g b) = s.inr.hom b
          exact DFunLike.congr_fun hmright b
        have hrd : G (tensorToCompleted f g
            (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b)) =
            s.inr.hom b :=
          DFunLike.congr_fun (congrArg (fun q : B ⟶ s.pt => q.hom)
            (pushoutDesc_fac_right f g s)) b
        have hprod :
            Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B) a *
              Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b =
                a ⊗ₜ[R] b := by
          rw [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        calc
          F (tensorToCompleted f g (a ⊗ₜ[R] b)) =
              F (tensorToCompleted f g
                (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B) a *
                  Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b)) := by
            rw [hprod]
          _ = F (tensorToCompleted f g
                (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B) a)) *
              F (tensorToCompleted f g
                (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b)) := by
            simp only [map_mul]
          _ = G (tensorToCompleted f g
                (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B) a)) *
              G (tensorToCompleted f g
                (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B) b)) := by
            rw [hla, hld, hra, hrd]
          _ = G (tensorToCompleted f g (a ⊗ₜ[R] b)) := by
            rw [← map_mul G, ← map_mul (tensorToCompleted f g), hprod]
      | add x y hx hy =>
        simp only [AlgHom.comp_apply, map_add, hx, hy]
    have hbase : ∀ c, F (E c) = G (E c) := by
      intro c
      change (F.comp (tensorToCompleted f g)) c =
        (G.comp (tensorToCompleted f g)) c
      exact DFunLike.congr_fun hFG c
    have hres : (residueAlgHom (Λ := Λ) (k := k) s.pt).comp F =
        residueAlgHom (Λ := Λ) (k := k) (pushoutObj f g) := by
      ext x
      exact m.residue_comm x
    let := algebraRk (R := R)
    let := scalarTowerResidue (Λ := Λ) (k := k) (R := R)
    have hresE : (residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp
        (F.toRingHom.comp E) = (tensorResidue f g).toRingHom := by
      apply RingHom.ext
      intro c
      change residueAlgHom (Λ := Λ) (k := k) s.pt (F (E c)) = tensorResidue f g c
      have hx := DFunLike.congr_fun hres (E c)
      rw [residueAlgHom_pushoutObj, completedResidue_algebraMap] at hx
      exact hx
    have hFI : (tensorIdeal f g).map (F.toRingHom.comp E) ≤
        maximalIdeal s.pt := by
      refine map_le_maximalIdeal_of_le_ker s.pt _ _ ?_
      rw [hresE]
    have hGI : (tensorIdeal f g).map (G.toRingHom.comp E) ≤
        maximalIdeal s.pt := by
      have hφ : ∀ c, (completedTensorMap f g s)
          (algebraMap (tensor f g) (completedTensor f g) c) = tensorToTarget f g s c :=
        completedTensorMap_algebraMap f g s
      have hker : (tensorIdeal f g).map E ≤ RingHom.ker
          ((residueAlgHom (Λ := Λ) (k := k) s.pt).toRingHom.comp G.toRingHom) :=
        completedTensorMap_ideal_le f g s (completedTensorMap f g s) hφ
      have h := Ideal.map_le_iff_le_comap.1 hker
      exact map_le_maximalIdeal_of_le_ker s.pt _ _ h
    exact CompleteLocalAlgCat.Hom.ext (completedMaps_ext (I := tensorIdeal f g)
      (K := maximalIdeal s.pt) (tensorIdeal_fg f g) F G hFI hGI hbase)

end Span

/-- The category of Noetherian complete local `Λ`-algebras with residue field identified
with `k` admits pushouts. -/
@[stacks 06SB]
public instance hasPushouts :
    HasPushouts (CompleteLocalAlgCat.{u, v, w} Λ k) := by
  let : ∀ {X Y Z : CompleteLocalAlgCat.{u, v, w} Λ k}
      {f : X ⟶ Y} {g : X ⟶ Z}, HasColimit (span f g) :=
    fun {_ _ _ f g} ↦ ⟨⟨pushoutCocone f g, pushoutCoconeIsColimit f g⟩⟩
  exact hasPushouts_of_hasColimit_span (C := CompleteLocalAlgCat.{u, v, w} Λ k)

end CompleteLocalAlgCat

end

end Deformation

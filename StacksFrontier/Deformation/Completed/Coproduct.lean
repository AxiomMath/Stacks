module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.Deformation.Completed.Basic

/-!
# Binary coproducts of complete local algebras

Binary coproducts in the completed base category, computed as a completed
tensor product.

## Main results

* `instHasBinaryCoproducts` gives binary coproducts in the category of
  Noetherian complete local algebras with fixed residue field.

## Implementation notes

The Stacks context assumes that the base is Noetherian and its map to the residue
field is finite. Only finite generation of the kernel of
`k ⊗[Λ] k → k` is used here, so finite type of `k` over `Λ` suffices.

## References

* [Stacks Project, Tag 06H1](https://stacks.math.columbia.edu/tag/06H1)
-/

public section

namespace Deformation

/-! ### Binary coproducts of complete local algebras -/

section
open CategoryTheory Limits
open scoped TensorProduct
universe u v w

private noncomputable def extendAlgHom
    {Λ A D : Type*} [CommRing Λ] [CommRing A] [CommRing D]
    [Algebra Λ A] [Algebra Λ D]
    (I : Ideal A) (J : Ideal D) (f : A →ₐ[Λ] D)
    (hIJ : I.map f.toRingHom ≤ J) [IsAdicComplete J D] :
    AdicCompletion I A →ₐ[Λ] D := by
  have hpow (n : ℕ) : (I ^ n).map f.toRingHom ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hIJ n
  let fbar : (n : ℕ) → AdicCompletion I A →ₐ[Λ] D ⧸ J ^ n := fun n =>
    (Ideal.quotientMapₐ (J ^ n) f (Ideal.map_le_iff_le_comap.mp (hpow n))).comp
      ((AdicCompletion.evalₐ I n).restrictScalars Λ)
  have hfbar : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right hle)).comp (fbar n) = fbar m := by
    intro m n hle
    apply AlgHom.ext
    intro x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simp only [fbar, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        AdicCompletion.evalₐ_mk, Ideal.quotient_map_mkₐ,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.factorₐ_apply,
        Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      rw [← map_sub]
      apply Ideal.map_le_iff_le_comap.mp (hpow m)
      simpa only [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (x.property hle).symm
  have : IsScalarTower Λ A (AdicCompletion I A) := IsScalarTower.of_algebraMap_eq' rfl
  exact IsAdicComplete.liftAlgHom J fbar hfbar

private theorem extendAlgHom_comp_algebraMap
    {Λ T D : Type*} [CommRing Λ] [CommRing T] [CommRing D]
    [Algebra Λ T] [Algebra Λ D]
    (I : Ideal T) (J : Ideal D) [IsAdicComplete J D]
    (f : T →ₐ[Λ] D) (hIJ : I.map f.toRingHom ≤ J) :
    (extendAlgHom I J f hIJ).comp
      (IsScalarTower.toAlgHom Λ T (AdicCompletion I T)) = f := by
  let : IsScalarTower Λ T (AdicCompletion I T) := IsScalarTower.of_algebraMap_eq' rfl
  unfold extendAlgHom
  apply IsAdicComplete.algHom_ext (I := J)
  intro n
  rw [← AlgHom.comp_assoc, IsAdicComplete.mkₐ_comp_liftAlgHom]
  exact AlgHom.ext fun x => by simp

private theorem algHom_ext_adicCompletion
    {Λ T D : Type*} [CommRing Λ] [CommRing T] [CommRing D]
    [Algebra Λ T] [Algebra Λ D]
    (I : Ideal T) (J : Ideal D) (hI : I.FG) [IsAdicComplete J D]
    (f g : AdicCompletion I T →ₐ[Λ] D)
    (hf : I.map (f.toRingHom.comp (algebraMap T (AdicCompletion I T))) ≤ J)
    (hg : I.map (g.toRingHom.comp (algebraMap T (AdicCompletion I T))) ≤ J)
    (hfg : f.comp (IsScalarTower.toAlgHom Λ T (AdicCompletion I T)) =
      g.comp (IsScalarTower.toAlgHom Λ T (AdicCompletion I T))) : f = g := by
  apply AlgHom.ext
  intro x
  rw [IsHausdorff.eq_iff_smodEq (I := J)]
  intro n
  rw [SModEq.sub_mem]
  obtain ⟨r, hr⟩ := Submodule.mkQ_surjective
    ((I ^ n) • (⊤ : Submodule T T)) (x.val n)
  have hx : x - algebraMap T (AdicCompletion I T) r ∈
      (I ^ n) • (⊤ : Submodule T (AdicCompletion I T)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub]
    exact sub_eq_zero.mpr hr.symm
  have hmap (F : AdicCompletion I T →ₐ[Λ] D)
      (hF : I.map (F.toRingHom.comp (algebraMap T (AdicCompletion I T))) ≤ J) :
      F (x - algebraMap T (AdicCompletion I T) r) ∈ J ^ n • (⊤ : Submodule D D) := by
    have hx' : x - algebraMap T (AdicCompletion I T) r ∈
        (I ^ n).map (algebraMap T (AdicCompletion I T)) := by
      simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hx
    have hpow : (I ^ n).map (F.toRingHom.comp (algebraMap T (AdicCompletion I T))) ≤ J ^ n := by
      rw [Ideal.map_pow]
      exact pow_le_pow_left' hF n
    have := Ideal.mem_map_of_mem (f := F.toRingHom) hx'
    rw [Ideal.map_map] at this
    simpa [Ideal.mul_top] using hpow this
  have hbase : f (algebraMap T (AdicCompletion I T) r) =
      g (algebraMap T (AdicCompletion I T) r) := by
    simpa only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply] using
      congrArg (fun F : T →ₐ[Λ] D => F r) hfg
  rw [show f x - g x = f (x - algebraMap T (AdicCompletion I T) r) -
      g (x - algebraMap T (AdicCompletion I T) r) by
    rw [map_sub, map_sub, hbase]
    ring]
  exact Submodule.sub_mem (J ^ n • (⊤ : Submodule D D)) (hmap f hf) (hmap g hg)

private noncomputable def completionObject
    {Λ k T : Type*} [CommRing Λ] [Field k] [CommRing T]
    [Algebra Λ k] [Algebra Λ T]
    (q : T →ₐ[Λ] k) (hq : Function.Surjective q)
    (hfg : (RingHom.ker q.toRingHom).FG) :
    CompleteLocalAlgCat Λ k := by
  let I : Ideal T := RingHom.ker q.toRingHom
  have hmax : I.IsMaximal := RingHom.ker_isMaximal_of_surjective q.toRingHom hq
  have hmapmax : (I.map (algebraMap T (AdicCompletion I T))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  let Ic : Ideal (AdicCompletion I T) := I.map (algebraMap T (AdicCompletion I T))
  letI : Ic.IsMaximal := hmapmax
  letI : IsAdicComplete Ic (AdicCompletion I T) := by
    change IsAdicComplete (I.map (algebraMap T (AdicCompletion I T))) _
    exact AdicCompletion.isAdicComplete_self I hfg
  letI : IsLocalRing (AdicCompletion I T) :=
    isLocalRing_of_isAdicComplete_maximal Ic
  letI : Algebra Λ (AdicCompletion I T) := inferInstance
  letI : IsScalarTower Λ T (AdicCompletion I T) := IsScalarTower.of_algebraMap_eq' rfl
  have hmaxeq : IsLocalRing.maximalIdeal (AdicCompletion I T) =
      I.map (algebraMap T (AdicCompletion I T)) :=
    (IsLocalRing.eq_maximalIdeal hmapmax).symm
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (AdicCompletion I T)) (AdicCompletion I T) := by
    rw [hmaxeq]
    exact AdicCompletion.isAdicComplete_self I hfg
  have hmaxfg : (IsLocalRing.maximalIdeal (AdicCompletion I T)).FG := by
    rw [hmaxeq]
    exact hfg.map (algebraMap T (AdicCompletion I T))
  have hnoeth : IsNoetherianRing (AdicCompletion I T) :=
    complete_local_ring_noetherian _ hcomplete hmaxfg
  have hlocal : IsLocalRing (AdicCompletion I T) := inferInstance
  have hlocalq : IsLocalRing (AdicCompletion (RingHom.ker q.toRingHom) T) := by
    change IsLocalRing (AdicCompletion I T)
    exact hlocal
  letI := hlocalq
  let qhat : AdicCompletion I T →ₐ[Λ] k := AdicCompletion.kerProj hq
  have hqhat : Function.Surjective qhat :=
    AdicCompletion.kerProj_surjective hq
  have hker : RingHom.ker qhat.toRingHom =
      IsLocalRing.maximalIdeal (AdicCompletion I T) := by
    change RingHom.ker qhat.toRingHom =
      IsLocalRing.maximalIdeal (AdicCompletion (RingHom.ker q.toRingHom) T)
    exact IsLocalRing.ker_eq_maximalIdeal qhat.toRingHom hqhat
  have hres :
      (AdicCompletion I T ⧸ IsLocalRing.maximalIdeal (AdicCompletion I T)) ≃ₐ[Λ] k :=
    (Ideal.quotientEquivAlgOfEq Λ hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hqhat)
  exact
    { carrier := AdicCompletion I T
      commRing := inferInstance
      algebra := inferInstance
      completeLocal := ⟨hnoeth, inferInstance, hcomplete⟩
      residueEquiv := hres }

private noncomputable def residueTensorMap {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (A B : CompleteLocalAlgCat Λ k) : A ⊗[Λ] B →ₐ[Λ] k ⊗[Λ] k :=
  Algebra.TensorProduct.map (residueAlgHom A) (residueAlgHom B)

private noncomputable def tensorResidueMap {Λ k : Type*} [CommRing Λ] [Field k] [Algebra Λ k]
    (A B : CompleteLocalAlgCat Λ k) : A ⊗[Λ] B →ₐ[Λ] k :=
  (Algebra.TensorProduct.lmul' Λ).comp (residueTensorMap A B)

private theorem tensorResidueMap_includeLeft {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] (A B : CompleteLocalAlgCat Λ k) (a : A) :
    tensorResidueMap A B (Algebra.TensorProduct.includeLeft (R := Λ) (S := Λ) (A := A) (B := B) a) =
      residueAlgHom A a := by
  simp [tensorResidueMap, residueTensorMap]

private theorem tensorResidueMap_includeRight {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] (A B : CompleteLocalAlgCat Λ k) (b : B) :
    tensorResidueMap A B (Algebra.TensorProduct.includeRight (R := Λ) (A := A) (B := B) b) =
      residueAlgHom B b := by
  simp [tensorResidueMap, residueTensorMap]

private theorem tensorResidueMap_surjective {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] (A B : CompleteLocalAlgCat Λ k) :
    Function.Surjective (tensorResidueMap A B) := by
  intro x
  obtain ⟨a, rfl⟩ :=
    (A.residueEquiv.surjective.comp Ideal.Quotient.mk_surjective) x
  exact ⟨_, tensorResidueMap_includeLeft A B a⟩

private theorem tensorResidueMap_kernel_fg {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat Λ k) :
    (RingHom.ker (tensorResidueMap A B).toRingHom).FG := by
  let fA := residueAlgHom A
  let fB := residueAlgHom B
  have hfA : Function.Surjective fA :=
    A.residueEquiv.surjective.comp Ideal.Quotient.mk_surjective
  have hfB : Function.Surjective fB :=
    B.residueEquiv.surjective.comp Ideal.Quotient.mk_surjective
  have hfgA : (RingHom.ker fA.toRingHom).FG := by
    rw [residueAlgHom_ker A]
    exact Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A)
  have hfgB : (RingHom.ker fB.toRingHom).FG := by
    rw [residueAlgHom_ker B]
    exact Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal B)
  have hkerMap : (RingHom.ker (residueTensorMap A B).toRingHom).FG := by
    change (RingHom.ker (Algebra.TensorProduct.map fA fB)).FG
    rw [Algebra.TensorProduct.map_ker fA fB hfA hfB]
    exact Submodule.FG.sup (hfgA.map _) (hfgB.map _)
  have hkerMul :
      (RingHom.ker (Algebra.TensorProduct.lmul' Λ : k ⊗[Λ] k →ₐ[Λ] k).toRingHom).FG := by
    change (KaehlerDifferential.ideal Λ k).FG
    exact KaehlerDifferential.ideal_fg (R := Λ) (S := k)
  exact Ideal.fg_ker_comp (residueTensorMap A B).toRingHom
    (Algebra.TensorProduct.lmul' Λ).toRingHom hkerMap hkerMul
    (Algebra.TensorProduct.map_surjective fA fB hfA hfB)

private noncomputable def binaryCoproductObject {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat Λ k) :
    CompleteLocalAlgCat Λ k :=
  completionObject (tensorResidueMap A B) (tensorResidueMap_surjective A B)
    (tensorResidueMap_kernel_fg A B)

private noncomputable def binaryCoproductObjectι {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat Λ k) :
    (A ⊗[Λ] B) →ₐ[Λ] binaryCoproductObject A B := by
  let q := tensorResidueMap A B
  let I : Ideal (A ⊗[Λ] B) := RingHom.ker q.toRingHom
  letI : IsScalarTower Λ (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact IsScalarTower.toAlgHom Λ (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B))

private theorem binaryCoproductObject_maximalIdeal {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat Λ k) :
    IsLocalRing.maximalIdeal (binaryCoproductObject A B) =
      (RingHom.ker (tensorResidueMap A B).toRingHom).map
        (binaryCoproductObjectι A B).toRingHom := by
  let q := tensorResidueMap A B
  let I : Ideal (A ⊗[Λ] B) := RingHom.ker q.toRingHom
  have hfg : I.FG := tensorResidueMap_kernel_fg A B
  have hmax : I.IsMaximal := RingHom.ker_isMaximal_of_surjective q.toRingHom
    (tensorResidueMap_surjective A B)
  have hmapi : (I.map (algebraMap (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B)))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  let : I.IsMaximal := hmax
  let : IsAdicComplete
      (I.map (algebraMap (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B))))
      (AdicCompletion I (A ⊗[Λ] B)) := AdicCompletion.isAdicComplete_self I hfg
  let : (I.map (algebraMap (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B)))).IsMaximal := hmapi
  let : IsLocalRing (AdicCompletion I (A ⊗[Λ] B)) :=
    isLocalRing_of_isAdicComplete_maximal
      (I.map (algebraMap (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B))))
  have h : IsLocalRing.maximalIdeal
      (AdicCompletion I (A ⊗[Λ] B)) =
      I.map (algebraMap (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B))) :=
    (IsLocalRing.eq_maximalIdeal hmapi).symm
  change IsLocalRing.maximalIdeal (AdicCompletion I (A ⊗[Λ] B)) =
    (RingHom.ker (tensorResidueMap A B).toRingHom).map
      (algebraMap (A ⊗[Λ] B) (AdicCompletion I (A ⊗[Λ] B)))
  simpa [q, I] using h

private theorem binaryCoproductObject_residue_map {Λ k : Type*} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat Λ k) (x : A ⊗[Λ] B) :
    (binaryCoproductObject A B).residueEquiv
        (IsLocalRing.residue (binaryCoproductObject A B)
          (binaryCoproductObjectι A B x)) =
      tensorResidueMap A B x := by
  let q := tensorResidueMap A B
  let I : Ideal (A ⊗[Λ] B) := RingHom.ker q.toRingHom
  let hq := tensorResidueMap_surjective A B
  let O := binaryCoproductObject A B
  let : CommRing (AdicCompletion I (A ⊗[Λ] B)) := O.commRing
  let : Algebra Λ (AdicCompletion I (A ⊗[Λ] B)) := O.algebra
  let : IsLocalRing (AdicCompletion I (A ⊗[Λ] B)) := O.completeLocal.isLocal
  let qhat : AdicCompletion I (A ⊗[Λ] B) →ₐ[Λ] k := AdicCompletion.kerProj hq
  have hqhat : Function.Surjective qhat := by
    change Function.Surjective (AdicCompletion.kerProj hq)
    exact AdicCompletion.kerProj_surjective hq
  have hker : RingHom.ker qhat =
      IsLocalRing.maximalIdeal (AdicCompletion I (A ⊗[Λ] B)) := by
    change RingHom.ker qhat.toRingHom = _
    exact IsLocalRing.ker_eq_maximalIdeal qhat.toRingHom hqhat
  change ((Ideal.quotientEquivAlgOfEq Λ hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hqhat))
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (AdicCompletion I (A ⊗[Λ] B)))
      (binaryCoproductObjectι A B x)) = q x
  simp only [AlgEquiv.trans_apply]
  change AdicCompletion.kerProj hq (binaryCoproductObjectι A B x) = q x
  rw [binaryCoproductObjectι]
  exact AdicCompletion.kerProj_of hq x

/-- A morphism `C ⟶ binaryCoproductObject A B` from a `Λ`-algebra map `C → A ⊗[Λ] B`
compatible with the residue maps. -/
private noncomputable def binaryCoproductInclude {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B C : CompleteLocalAlgCat.{u, v, w} Λ k) (i : C →ₐ[Λ] A ⊗[Λ] B)
    (hi : ∀ c, tensorResidueMap A B (i c) = residueAlgHom C c) :
    C ⟶ binaryCoproductObject A B := by
  let f := (binaryCoproductObjectι A B).comp i
  refine ⟨f, ?_, ?_⟩
  · apply ((IsLocalRing.local_hom_TFAE f.toRingHom).out 3 1).mp
    rw [binaryCoproductObject_maximalIdeal]
    calc
      (IsLocalRing.maximalIdeal C).map f.toRingHom =
          ((IsLocalRing.maximalIdeal C).map i.toRingHom).map
            (binaryCoproductObjectι A B).toRingHom := by
        rw [Ideal.map_map]
        rfl
      _ ≤ (RingHom.ker (tensorResidueMap A B).toRingHom).map
          (binaryCoproductObjectι A B).toRingHom :=
        Ideal.map_mono <| by
          rw [Ideal.map_le_iff_le_comap]
          intro c hc
          change i c ∈ RingHom.ker (tensorResidueMap A B).toRingHom
          rw [RingHom.mem_ker]
          change tensorResidueMap A B (i c) = 0
          rw [hi]
          rw [← residueAlgHom_ker C] at hc
          exact RingHom.mem_ker.mp hc
  · intro c
    change (binaryCoproductObject A B).residueEquiv
        (IsLocalRing.residue (binaryCoproductObject A B)
          (binaryCoproductObjectι A B (i c))) = _
    rw [binaryCoproductObject_residue_map A B (i c), hi]
    rfl

private noncomputable def binaryCoproductInl {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat.{u, v, w} Λ k) :
    A ⟶ binaryCoproductObject A B :=
  binaryCoproductInclude A B A
    (Algebra.TensorProduct.includeLeft (R := Λ) (S := Λ) (A := A) (B := B))
    (tensorResidueMap_includeLeft A B)

private noncomputable def binaryCoproductInr {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat.{u, v, w} Λ k) :
    B ⟶ binaryCoproductObject A B :=
  binaryCoproductInclude A B B
    (Algebra.TensorProduct.includeRight (R := Λ) (A := A) (B := B))
    (tensorResidueMap_includeRight A B)

private noncomputable def binaryTensorMap {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] {D : CompleteLocalAlgCat.{u, v, w} Λ k}
    (A B : CompleteLocalAlgCat.{u, v, w} Λ k) (f : A ⟶ D) (g : B ⟶ D) :
    (A ⊗[Λ] B) →ₐ[Λ] D :=
  (Algebra.TensorProduct.lmul' Λ).comp
    (Algebra.TensorProduct.map f.hom g.hom)

private theorem binaryTensorMap_residue {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] {D : CompleteLocalAlgCat.{u, v, w} Λ k}
    (A B : CompleteLocalAlgCat.{u, v, w} Λ k) (f : A ⟶ D) (g : B ⟶ D) :
    (residueAlgHom D).comp (binaryTensorMap A B f g) = tensorResidueMap A B := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
    simp [binaryTensorMap, tensorResidueMap, residueTensorMap, f.residue_comm a,
      g.residue_comm b]

private theorem residueAlgHom_comp_of_comp_ι {Λ : Type u} {k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k] [Algebra.FiniteType Λ k]
    {A B D : CompleteLocalAlgCat.{u, v, w} Λ k} (H : binaryCoproductObject A B →ₐ[Λ] D)
    [IsLocalHom H.toRingHom]
    (h : (residueAlgHom D).comp (H.comp (binaryCoproductObjectι A B)) = tensorResidueMap A B) :
    (residueAlgHom D).comp H = residueAlgHom (binaryCoproductObject A B) := by
  have hbridge (t : A ⊗[Λ] B) : residueAlgHom (binaryCoproductObject A B)
      (binaryCoproductObjectι A B t) = tensorResidueMap A B t := by
    simpa [residueAlgHom_apply] using binaryCoproductObject_residue_map A B t
  apply AlgHom.ext
  intro z
  obtain ⟨t, ht⟩ := tensorResidueMap_surjective A B
    (residueAlgHom (binaryCoproductObject A B) z)
  have hz : z - binaryCoproductObjectι A B t ∈
      IsLocalRing.maximalIdeal (binaryCoproductObject A B) := by
    rw [← residueAlgHom_ker (binaryCoproductObject A B)]
    change residueAlgHom (binaryCoproductObject A B)
      (z - binaryCoproductObjectι A B t) = 0
    rw [map_sub, hbridge, ht]
    simp
  have hD : residueAlgHom D (H (z - binaryCoproductObjectι A B t)) = 0 := by
    have hm := map_nonunit H.toRingHom _ hz
    rw [← residueAlgHom_ker D] at hm
    exact RingHom.mem_ker.mp hm
  have hleft : residueAlgHom D (H z) =
      residueAlgHom D (H (binaryCoproductObjectι A B t)) :=
    sub_eq_zero.mp (by simpa only [map_sub] using hD)
  exact hleft.trans ((DFunLike.congr_fun h t).trans ht)

private noncomputable def binaryCoproductDesc {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    {A B D : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ D) (g : B ⟶ D) :
    binaryCoproductObject A B ⟶ D := by
  let q := tensorResidueMap A B
  let T := A ⊗[Λ] B
  let I : Ideal T := RingHom.ker q.toRingHom
  let F : T →ₐ[Λ] D := binaryTensorMap A B f g
  have hresF : (residueAlgHom D).comp F = q := binaryTensorMap_residue A B f g
  have hIJ : I.map F.toRingHom ≤ IsLocalRing.maximalIdeal D := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [← residueAlgHom_ker D]
    change residueAlgHom D (F x) = 0
    exact (DFunLike.congr_fun hresF x).trans (RingHom.mem_ker.mp hx)
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal D) D := D.completeLocal.isComplete
  let G := extendAlgHom I (IsLocalRing.maximalIdeal D) F hIJ
  let H : binaryCoproductObject A B →ₐ[Λ] D := G
  have hrestrict : H.comp (binaryCoproductObjectι A B) = F := by
    change (extendAlgHom I (IsLocalRing.maximalIdeal D) F hIJ).comp
      (IsScalarTower.toAlgHom Λ T (AdicCompletion I T)) = F
    exact extendAlgHom_comp_algebraMap I (IsLocalRing.maximalIdeal D) F hIJ
  have hlocal : IsLocalHom H.toRingHom := by
    apply ((IsLocalRing.local_hom_TFAE H.toRingHom).out 3 1).mp
    calc
      (IsLocalRing.maximalIdeal (binaryCoproductObject A B)).map H.toRingHom =
          I.map (H.toRingHom.comp (binaryCoproductObjectι A B).toRingHom) := by
        rw [binaryCoproductObject_maximalIdeal, Ideal.map_map]
      _ = I.map F.toRingHom := by
        change I.map (H.comp (binaryCoproductObjectι A B)).toRingHom = I.map F.toRingHom
        rw [hrestrict]
      _ ≤ IsLocalRing.maximalIdeal D := hIJ
  letI : IsLocalHom H.toRingHom := hlocal
  have hres := residueAlgHom_comp_of_comp_ι H (by rw [hrestrict]; exact hresF)
  exact ⟨H, hlocal, fun z => DFunLike.congr_fun hres z⟩

private theorem binaryCoproductDesc_comp_tensor {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    {A B D : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ D) (g : B ⟶ D) :
    (binaryCoproductDesc f g).hom.comp (binaryCoproductObjectι A B) =
      binaryTensorMap A B f g := by
  unfold binaryCoproductDesc
  dsimp only
  exact extendAlgHom_comp_algebraMap _ _ _ _

private theorem binaryCoproductDesc_inl {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    {A B D : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ D) (g : B ⟶ D) :
    binaryCoproductInl A B ≫ binaryCoproductDesc f g = f := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro a
  simpa [binaryCoproductInl, binaryCoproductInclude, AlgHom.comp_assoc, binaryTensorMap,
    Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.lmul'_comp_includeLeft] using
    congrArg (fun p : (A ⊗[Λ] B) →ₐ[Λ] D => p
      (Algebra.TensorProduct.includeLeft (R := Λ) (S := Λ) (A := A) (B := B) a))
      (binaryCoproductDesc_comp_tensor f g)

private theorem binaryCoproductDesc_inr {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    {A B D : CompleteLocalAlgCat.{u, v, w} Λ k} (f : A ⟶ D) (g : B ⟶ D) :
    binaryCoproductInr A B ≫ binaryCoproductDesc f g = g := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro b
  simpa [binaryCoproductInr, binaryCoproductInclude, AlgHom.comp_assoc, binaryTensorMap,
    Algebra.TensorProduct.map_comp_includeRight,
    Algebra.TensorProduct.lmul'_comp_includeRight] using
    congrArg (fun p : (A ⊗[Λ] B) →ₐ[Λ] D => p
      (Algebra.TensorProduct.includeRight (R := Λ) (A := A) (B := B) b))
      (binaryCoproductDesc_comp_tensor f g)

private theorem tensor_algHom_ext {Λ A B C : Type*} [CommRing Λ] [CommRing A] [CommRing B]
    [Semiring C] [Algebra Λ A] [Algebra Λ B] [Algebra Λ C] {f g : A ⊗[Λ] B →ₐ[Λ] C}
    (hL : f.comp (Algebra.TensorProduct.includeLeft (R := Λ) (S := Λ) (A := A) (B := B)) =
      g.comp (Algebra.TensorProduct.includeLeft (R := Λ) (S := Λ) (A := A) (B := B)))
    (hR : f.comp (Algebra.TensorProduct.includeRight (R := Λ) (A := A) (B := B)) =
      g.comp (Algebra.TensorProduct.includeRight (R := Λ) (A := A) (B := B))) : f = g := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
      have hmul : a ⊗ₜ[Λ] b =
          Algebra.TensorProduct.includeLeft (R := Λ) (S := Λ) (A := A) (B := B) a *
            Algebra.TensorProduct.includeRight (R := Λ) (A := A) (B := B) b := by
        rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hmul, map_mul, map_mul]
      exact congr_arg₂ (· * ·) (DFunLike.congr_fun hL a) (DFunLike.congr_fun hR b)

private theorem binaryCoproduct_hom_ext {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    {A B D : CompleteLocalAlgCat.{u, v, w} Λ k}
    (F G : binaryCoproductObject A B ⟶ D)
    (hL : binaryCoproductInl A B ≫ F = binaryCoproductInl A B ≫ G)
    (hR : binaryCoproductInr A B ≫ F = binaryCoproductInr A B ≫ G) : F = G := by
  let q := tensorResidueMap A B
  let T := A ⊗[Λ] B
  let I : Ideal T := RingHom.ker q.toRingHom
  have hcomp : F.hom.comp (binaryCoproductObjectι A B) =
      G.hom.comp (binaryCoproductObjectι A B) :=
    tensor_algHom_ext
      (by simpa [binaryCoproductInl, binaryCoproductInclude, AlgHom.comp_assoc] using
        congrArg (fun f : A ⟶ D => f.hom) hL)
      (by simpa [binaryCoproductInr, binaryCoproductInclude, AlgHom.comp_assoc] using
        congrArg (fun f : B ⟶ D => f.hom) hR)
  have hIota (x : T) (hx : x ∈ I) :
      binaryCoproductObjectι A B x ∈ IsLocalRing.maximalIdeal (binaryCoproductObject A B) := by
    rw [binaryCoproductObject_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  have hmap (H : binaryCoproductObject A B ⟶ D) :
      I.map (H.hom.toRingHom.comp (binaryCoproductObjectι A B).toRingHom) ≤
        IsLocalRing.maximalIdeal D := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    let : IsLocalHom H.hom.toRingHom := H.isLocal
    exact map_nonunit H.hom.toRingHom _ (hIota x hx)
  exact CompleteLocalAlgCat.Hom.ext <| algHom_ext_adicCompletion I (IsLocalRing.maximalIdeal D)
    (tensorResidueMap_kernel_fg A B) F.hom G.hom (hmap F) (hmap G) hcomp

private noncomputable def binaryCoproductIsColimit {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k] [Algebra.FiniteType Λ k]
    (A B : CompleteLocalAlgCat.{u, v, w} Λ k) :
    IsColimit (BinaryCofan.mk (binaryCoproductInl A B) (binaryCoproductInr A B)) :=
  BinaryCofan.isColimitMk (fun s => binaryCoproductDesc s.inl s.inr)
    (fun s => binaryCoproductDesc_inl s.inl s.inr)
    (fun s => binaryCoproductDesc_inr s.inl s.inr) fun s m hL hR =>
      binaryCoproduct_hom_ext m (binaryCoproductDesc s.inl s.inr)
        (hL.trans (binaryCoproductDesc_inl s.inl s.inr).symm)
        (hR.trans (binaryCoproductDesc_inr s.inl s.inr).symm)

/-- The category of Noetherian complete local `Λ`-algebras with residue field `k`
admits coproducts of pairs of objects. -/
@[stacks 06H1]
instance instHasBinaryCoproducts {Λ : Type u} {k : Type w}
    [CommRing Λ] [Field k] [Algebra Λ k] [Algebra.FiniteType Λ k] :
    HasBinaryCoproducts (CompleteLocalAlgCat.{u, v, w} Λ k) := by
  let : ∀ {A B : CompleteLocalAlgCat.{u, v, w} Λ k},
      HasColimit (pair A B) := fun {A B} =>
    ⟨⟨BinaryCofan.mk (binaryCoproductInl A B) (binaryCoproductInr A B),
      binaryCoproductIsColimit A B⟩⟩
  exact hasBinaryCoproducts_of_hasColimit_pair
    (C := CompleteLocalAlgCat.{u, v, w} Λ k)

end

end Deformation

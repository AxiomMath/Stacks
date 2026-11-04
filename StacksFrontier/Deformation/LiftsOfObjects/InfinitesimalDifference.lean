module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.Torsion.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.SmallExtensionLift
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# The infinitesimal difference map of a small extension

Let `f : A' → A` be a surjection of Artinian local algebras whose kernel `I` is annihilated by
the maximal ideal of `A'`. Then `I` is a finite-dimensional `k`-vector space, and the
self-fibre product `A' ×_A A'` maps onto the square-zero extension `k[I]` by

`(a₁, a₂) ↦ (ā₁, a₂ - a₁)`.

This is the map the source calls `g`, and it is what converts a pair of lifts of an object into
a tangent vector.

## Main results

* `Deformation.kernelModule_finite`: the kernel is finite-dimensional over `k`.
* `Deformation.infinitesimalDifferenceMap`: the map above, packaged as a
  `Deformation.InfinitesimalMap` for the identity of `A'` and the two projections of the
  self-fibre product.

## Implementation notes

The `k`-structure on the kernel is `Deformation.kernelModule`, i.e. the one induced by the
residue map of `A'` and the structural identification of its residue field with `k`.
Finite-dimensionality is proved by transporting the `A'`-submodule lattice: the annihilation
hypothesis makes `k`-submodules and `A'`-submodules of the kernel the same thing, and the
kernel is Artinian over `A'`.

The target of the map is the Artinian square-zero extension `k[I]` of
`Deformation.squareZeroExtensionArtinian`, and the additive coordinate is the identity of
`k × I`, so the two coordinate equations of `Deformation.InfinitesimalMap` hold by `rfl`.

## References

* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
-/

@[expose] public section

namespace Deformation

/-! ### Finite-dimensionality of the kernel -/

section
open CategoryTheory IsLocalRing

universe u v w

/-- A morphism of Artinian local algebras whose kernel is annihilated by the maximal ideal of
the source has finite-dimensional kernel over the residue field. -/
public theorem kernelModule_finite
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0) :
    letI : Module k (RingHom.ker f.hom.toRingHom) := kernelModule f hann
    Module.Finite k (RingHom.ker f.hom.toRingHom) := by
  let I := RingHom.ker f.hom.toRingHom
  let hTors : Module.IsTorsionBySet A' I (maximalIdeal A') := fun i a =>
    Subtype.ext (hann a.1 a.2 i)
  let : Module (ResidueField A') I := hTors.module
  let : Module k I := kernelModule f hann
  let : Module A' I := inferInstance
  have hsmul (a : A') (x : I) :
      a • x = (A'.residueEquiv (residue A' a)) • x := by
    apply Subtype.ext
    change a * (x : A') =
      ((A'.residueEquiv.symm (A'.residueEquiv (residue A' a)) • x : I) : A')
    rw [A'.residueEquiv.symm_apply_apply]
    exact congrArg Subtype.val (Module.IsTorsionBySet.mk_smul hTors a x).symm
  let e : Submodule k I ↪o Submodule A' I :=
    { toFun := fun U =>
        { carrier := U.carrier
          zero_mem' := U.zero_mem
          add_mem' := U.add_mem
          smul_mem' := by
            intro a x hx
            rw [hsmul]
            exact U.smul_mem (A'.residueEquiv (residue A' a)) hx }
      inj' := fun U V h => Submodule.ext fun x =>
        Iff.of_eq (congrArg (fun W : Submodule A' I => x ∈ W) h)
      map_rel_iff' := Iff.rfl }
  have hArtK : IsArtinian k I := e.wellFoundedLT
  exact IsSemiprimaryRing.finite_of_isArtinian k k I

end

/-! ### The infinitesimal difference map -/

section
open CategoryTheory IsLocalRing

universe u v w

/-- The infinitesimal-coordinate map from the self-pullback of a small
extension, specified by `(a₁,a₂) ↦ (ā₁,a₂-a₁)`. -/
public noncomputable def infinitesimalDifferenceMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f : A' ⟶ A) (hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0) :
    let _P := ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf)
    let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)
    let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)
    InfinitesimalMap f (𝟙 A') p₁ p₂ := by
  classical
  let I := RingHom.ker f.hom.toRingHom
  letI : Module k I := kernelModule f hann
  letI : Module.Finite k I := kernelModule_finite f hann
  let hTors : Module.IsTorsionBySet A' I (maximalIdeal A') := fun i a =>
    Subtype.ext (hann a.1 a.2 i)
  letI : Module (ResidueField A') I := hTors.module
  letI : Module kᵐᵒᵖ I := Module.compHom I {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  letI : IsCentralScalar k I := ⟨fun _ _ => rfl⟩
  letI : Module A' I := inferInstance
  letI : IsScalarTower Λ A' I := inferInstance
  have hsmul (a : A') (i : I) :
      a • i = (A'.residueEquiv (residue A' a)) • i := by
    apply Subtype.ext
    change a * (i : A') =
      ((A'.residueEquiv.symm (A'.residueEquiv (residue A' a)) • i : I) : A')
    rw [A'.residueEquiv.symm_apply_apply]
    exact congrArg Subtype.val (Module.IsTorsionBySet.mk_smul hTors a i).symm
  have hresidueAlgMap (a : Λ) :
      residue A' (algebraMap Λ A' a) = algebraMap Λ (ResidueField A') a := by
    symm
    rw [IsScalarTower.algebraMap_apply Λ A' (ResidueField A') a]
    simp [IsLocalRing.ResidueField.algebraMap_eq]
  let V : FGModuleCat.{w} k := FGModuleCat.of k I
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun a i =>
    calc
      (algebraMap Λ k a) • i =
          (A'.residueEquiv (residue A' (algebraMap Λ A' a))) • i := by
            rw [← A'.residueEquiv.commutes a, hresidueAlgMap]
      _ = (algebraMap Λ A' a) • i := (hsmul _ i).symm
      _ = a • i := IsScalarTower.algebraMap_smul (R := Λ) (A := A') (M := V) a i
  letI : IsScalarTower Λ kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun a i =>
    calc
      (algebraMap Λ kᵐᵒᵖ a) • i = (algebraMap Λ k a) • i := rfl
      _ = (A'.residueEquiv (residue A' (algebraMap Λ A' a))) • i := by
        rw [← A'.residueEquiv.commutes a, hresidueAlgMap]
      _ = (algebraMap Λ A' a) • i := (hsmul _ i).symm
      _ = a • i := IsScalarTower.algebraMap_smul (R := Λ) (A := A') (M := V) a i
  let P := ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf)
  let p₁ := ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)
  let p₂ := ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)
  let T := (squareZeroExtensionArtinian Λ k).obj V
  letI : CommRing (TrivSqZeroExt k V) := T.commRing
  letI : Algebra Λ (TrivSqZeroExt k V) := T.algebra
  let coordinate : T ≃+ (k × I) :=
    { toFun := fun x => (x.fst, x.snd)
      invFun := fun x => (x.1, x.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hcomm (z : P.carrier) : f.hom (p₁.hom z) = f.hom (p₂.hom z) := by
    have hw := congrArg (fun g : P ⟶ A => g.hom z)
      (ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)).w
    simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply] using hw
  have hdiff (z : P.carrier) : f.hom (p₂.hom z - p₁.hom z) = 0 := by
    rw [map_sub, hcomm z, sub_self]
  have hres (x : P.carrier) : residue A' (p₂.hom x) = residue A' (p₁.hom x) := by
    apply A'.residueEquiv.injective
    rw [← f.residue_comm (p₂.hom x), ← f.residue_comm (p₁.hom x), hcomm x]
  let qval (z : P.carrier) : TrivSqZeroExt k V :=
    (A'.residueEquiv (residue A' (p₁.hom z)),
      ⟨p₂.hom z - p₁.hom z, hdiff z⟩)
  let q : P.carrier →+* TrivSqZeroExt k V :=
    { toFun := qval
      map_one' := by
        apply TrivSqZeroExt.ext
        · simp [qval]
        · apply Subtype.ext
          simp [qval]
      map_mul' := by
        intro x y
        apply TrivSqZeroExt.ext
        · change _ = TrivSqZeroExt.fst (qval x * qval y)
          rw [TrivSqZeroExt.fst_mul]
          simp [qval]
        · change (qval (x * y)).snd = (qval x * qval y).snd
          apply Subtype.ext
          have hraw : p₂.hom x * p₂.hom y - p₁.hom x * p₁.hom y =
              p₂.hom x * (p₂.hom y - p₁.hom y) +
                (p₂.hom x - p₁.hom x) * p₁.hom y := by ring
          change p₂.hom (x * y) - p₁.hom (x * y) = _
          rw [map_mul, map_mul, TrivSqZeroExt.snd_mul]
          simpa [V, qval, ← hres x, hres y, ← hsmul, sub_eq_add_neg, mul_comm,
            mul_left_comm, mul_assoc, Submodule.coe_smul, Submodule.coe_add] using hraw
      map_zero' := by
        apply TrivSqZeroExt.ext
        · simp [qval]
        · apply Subtype.ext
          simp [qval]
      map_add' := by
        intro x y
        apply TrivSqZeroExt.ext
        · change _ = TrivSqZeroExt.fst (qval x + qval y)
          rw [TrivSqZeroExt.fst_add]
          simp [qval]
        · change (qval (x + y)).snd = (qval x + qval y).snd
          apply Subtype.ext
          rw [TrivSqZeroExt.snd_add]
          simp [V, qval, map_add]
          ring }
  let gAlg : P.carrier →ₐ[Λ] TrivSqZeroExt k V :=
    { toRingHom := q
      commutes' := by
        intro r
        apply TrivSqZeroExt.ext
        · change A'.residueEquiv (residue A' (p₁.hom (algebraMap Λ P r))) =
            TrivSqZeroExt.fst (algebraMap Λ (TrivSqZeroExt k V) r)
          rw [p₁.hom.commutes]
          have hmap : algebraMap Λ (TrivSqZeroExt k V) r =
              TrivSqZeroExt.inl (algebraMap Λ k r) :=
            TrivSqZeroExt.algebraMap_eq_inl' Λ k V r
          rw [hmap, TrivSqZeroExt.fst_inl]
          exact A'.residueEquiv.commutes r
        · apply Subtype.ext
          change p₂.hom (algebraMap Λ P r) - p₁.hom (algebraMap Λ P r) =
            ↑(TrivSqZeroExt.snd (algebraMap Λ (TrivSqZeroExt k V) r) : V)
          rw [p₂.hom.commutes, p₁.hom.commutes]
          have hmap : algebraMap Λ (TrivSqZeroExt k V) r =
              TrivSqZeroExt.inl (algebraMap Λ k r) :=
            TrivSqZeroExt.algebraMap_eq_inl' Λ k V r
          rw [hmap, TrivSqZeroExt.snd_inl]
          simp }
  refine
    { target := T
      coordinate := coordinate
      g :=
        { hom := gAlg
          isLocal := by
            refine ⟨fun z hg => ?_⟩
            have hfst : IsUnit (A'.residueEquiv (residue A' (p₁.hom z))) := by
              have hfst' : IsUnit (TrivSqZeroExt.fst (gAlg z)) :=
                TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hg
              exact hfst'
            have hresne : residue A' (p₁.hom z) ≠ 0 := by
              intro hzero
              exact hfst.ne_zero (by simp [hzero])
            have hu₁ : IsUnit (p₁.hom z) :=
              (residue_ne_zero_iff_isUnit (p₁.hom z)).mp hresne
            exact p₁.isLocal.map_nonunit z hu₁
          residue_comm := by
            intro z
            change T.residueEquiv (residue T (gAlg z)) = P.residueEquiv (residue P z)
            rw [squareZeroExtensionArtinian_residue]
            change A'.residueEquiv (residue A' (p₁.hom z)) = P.residueEquiv (residue P z)
            exact p₁.residue_comm z }
      g_surjective := by
        intro y
        let yc := coordinate y
        obtain ⟨a, ha⟩ := residue_surjective (A'.residueEquiv.symm yc.1)
        let b : A' := a + yc.2.1
        have hb : f.hom a = f.hom b := by
          have hi : f.hom yc.2.1 = 0 := yc.2.2
          dsimp [b]
          rw [map_add, hi, add_zero]
        refine ⟨⟨(a, b), hb⟩, ?_⟩
        let z : P.carrier := ⟨(a, b), hb⟩
        have hp₁ : p₁.hom z = a := by
          rw [ArtinianLocalAlgCat.pullbackFst_of_surjective_hom]
          rfl
        have hp₂ : p₂.hom z = b := by
          rw [ArtinianLocalAlgCat.pullbackSnd_of_surjective_hom]
          rfl
        apply coordinate.injective
        apply TrivSqZeroExt.ext
        · change A'.residueEquiv (residue A' (p₁.hom z)) = yc.1
          rw [hp₁, ha, A'.residueEquiv.apply_symm_apply]
        · apply Subtype.ext
          change p₂.hom z - p₁.hom z = (yc.2 : I)
          rw [hp₂, hp₁]
          simp [b]
      first := fun _ => rfl
      difference_mem := fun z => RingHom.mem_ker.mpr (hdiff z)
      second := fun _ => rfl }

end

end Deformation

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EtaSheaf

/-!
# A generator of the stalk ideal, and multiplication by it on a free stalk

Let `(X, O_X)` be a ringed space carrying an invertible sheaf of ideals `ι : I ⟶ O_X` and let
`x` be a point at which the stalk `I_x` is free of rank one over `O_{X,x}`.  This file extracts
from that freeness the two pointwise facts that clause (5) of Tag 0GT5 asks for, and which the
pointwise form of Tag 0F8N needs as input:

* a generator `f` of the stalk ideal `I_x ⊆ O_{X,x}`, which is automatically a nonzerodivisor
  of `O_{X,x}`;
* injectivity, at `x`, of the ideal-power inclusion
  `I^{⊗ (n+1)} ⊗ M ⟶ I^{⊗ n} ⊗ M` — that is, of multiplication by the ideal on the twisted
  stalk — whenever the stalk `M_x` is a finite free `O_{X,x}`-module.

The second fact is the reason for the first.  Through the comparison of Tag 01CB the stalk of
the ideal-power inclusion in degree `n` is multiplication by `f` composed with an isomorphism,
so its injectivity is the regularity of `f` on `(I^{⊗ n} ⊗ M)_x`; and if `M_x` is finite free
then so is `(I^{⊗ n} ⊗ M)_x`, on which a nonzerodivisor of `O_{X,x}` acts injectively.  No
torsion-freeness of `M` as a sheaf is used, which is what makes the statement applicable to a
cohomology sheaf.

## Main results

* `Stacks.IdealTorsion.Eta.exists_generatesStalkIdeal_mem_nonZeroDivisors`: a trivialized stalk
  of an ideal sheaf has a generator, and it is a nonzerodivisor.
* `Stacks.IdealTorsion.Eta.isSMulRegular_of_stalk_linearEquiv`: a nonzerodivisor of `O_{X,x}`
  acts injectively on a finite free stalk.
* `Stacks.IdealTorsion.Eta.injective_stalkMapL_idealPowerIncl`: **multiplication by the ideal
  is injective on the twisted stalk** of a module whose stalk at `x` is finite free.

## Implementation notes

The stalk vocabulary of Tag 01CB — `ringStalk`, `grpStalk`, `stalkMapL` — with its germ and
functoriality lemmas, the stalk `idealStalkMap` of the ideal inclusion and the value of the
zeroth ideal-power inclusion on a pure tensor of stalks are all developed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EtaSheaf.lean` and imported from there.  The
proofs below are written in the style of those lemmas, for the same reason: the structure sheaf
has three spellings which agree only at `default` transparency, so a step that `rw` or `simp`
cannot take is written out as a chain of ground equations closed by `Eq.trans` and `congrArg`.

## References

* [Stacks Project, Tag 0GT4](https://stacks.math.columbia.edu/tag/0GT4)
* [Stacks Project, Tag 0GT5](https://stacks.math.columbia.edu/tag/0GT5)
* [Stacks Project, Tag 0F8N](https://stacks.math.columbia.edu/tag/0F8N)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

open Stacks.SheafOfModules.Invertible (tensorPowerEquivalence
  tensorRightFunctor_isEquivalence powSuccIso
  tensorProductRightUnitor)

open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk grpStalk grpGerm stalkMapL
  tensorStalkIso)

universe u

namespace Stacks.IdealTorsion.Eta

variable (X : RingedSpace.{u})

local notation "Oₓ" => (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)
local notation "𝒪" => SheafOfModules.unit Oₓ

/-! ## A free stalk of rank one of the ideal gives a regular generator -/

/-- A trivialization of the stalk of the ideal writes every element of `I_x` as a multiple of
the trivializing one, hence every element of the stalk ideal as a multiple of its image. -/
private lemma idealStalkMap_eq_mul
    {I : SheafOfModules.{u} Oₓ} (ι : I ⟶ 𝒪) (x : X)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x)
    (a : grpStalk X I.val x) :
    idealStalkMap X ι x a = eI a * idealStalkMap X ι x (eI.symm 1) := by
  have hgen : eI a • eI.symm 1 = a := by
    rw [← map_smul, smul_eq_mul, mul_one, eI.symm_apply_apply]
  conv_lhs => rw [← hgen]
  rw [map_smul, smul_eq_mul]

/-- The image of a trivializing element of `I_x` under the stalk of the ideal inclusion is a
nonzerodivisor of `O_{X,x}`: the composite `O_{X,x} ⟶ I_x ⟶ O_{X,x}` of the trivialization with
that stalk map is multiplication by it, and is injective because both factors are. -/
private lemma mem_nonZeroDivisors_idealStalkMap
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι] (x : X)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x) :
    idealStalkMap X ι x (eI.symm 1) ∈ nonZeroDivisors (ringStalk X x) := by
  have key : ∀ a : ringStalk X x, a * idealStalkMap X ι x (eI.symm 1) = 0 → a = 0 := by
    intro a ha
    have h : idealStalkMap X ι x (a • eI.symm 1) = idealStalkMap X ι x 0 := by
      rwa [map_smul, map_zero, smul_eq_mul]
    have h0 : a • eI.symm 1 = 0 := idealStalkMap_injective X ι x h
    have h1 : a • (1 : ringStalk X x) = 0 := by
      rw [← eI.apply_symm_apply (1 : ringStalk X x), ← map_smul, h0, map_zero]
    simpa only [smul_eq_mul, mul_one] using h1
  exact mem_nonZeroDivisors_iff.2 ⟨fun a h => key a (by rwa [mul_comm]), key⟩

/-- **A trivializing element of the stalk of the ideal generates the stalk ideal, and its image
is a nonzerodivisor.**  Given a trivialization `eI` of `I_x`, the image `f` of `eI⁻¹ 1` under the
stalk of the ideal inclusion generates the stalk ideal `I_x ⊆ O_{X,x}`, and `f` is a
nonzerodivisor of `O_{X,x}`.

This is clause (5) of Tag 0GT5 read at `x`, with the ideal being invertible and a subsheaf —
condition (2) of Tag 0GT3 — in place of Situation 0GT4's local generation by a
nonzerodivisor. -/
public theorem exists_generatesStalkIdeal_mem_nonZeroDivisors (I : SheafOfModules.{u} Oₓ)
    (ι : I ⟶ 𝒪) [Mono ι] (x : X)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x) :
    ∃ f : ringStalk X x,
      GeneratesStalkIdeal X ι x f ∧ f ∈ nonZeroDivisors (ringStalk X x) := by
  refine ⟨idealStalkMap X ι x (eI.symm 1), ⟨idealStalkMap_mem_stalkIdeal X ι x _, ?_⟩,
    mem_nonZeroDivisors_idealStalkMap X I ι x eI⟩
  rintro _ ⟨U, hxU, s, rfl⟩
  refine ⟨eI (grpGerm X I.val x U hxU s), ?_⟩
  rw [← idealStalkMap_germ X ι x U hxU s]
  exact idealStalkMap_eq_mul X ι x eI _

/-- **A nonzerodivisor acts injectively on a finite free stalk.**  If the stalk `M_x` is a
finite free `O_{X,x}`-module and `f` is a nonzerodivisor of `O_{X,x}`, then multiplication by
`f` on `M_x` is injective: in coordinates it is multiplication by `f` on each one. -/
public theorem isSMulRegular_of_stalk_linearEquiv {M : SheafOfModules.{u} Oₓ} {x : X}
    {r : ℕ} (f : ringStalk X x) (hf : f ∈ nonZeroDivisors (ringStalk X x))
    (eM : grpStalk X M.val x ≃ₗ[ringStalk X x] (Fin r → ringStalk X x)) :
    IsSMulRegular (grpStalk X M.val x) f := by
  intro a b hab
  refine eM.injective (funext fun i => ?_)
  have h : f * eM a i = f * eM b i := by
    simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using congrArg (fun z => eM z i) hab
  have h0 : (eM a i - eM b i) * f = 0 := by
    rw [sub_mul, mul_comm (eM a i) f, mul_comm (eM b i) f, h, sub_self]
  exact sub_eq_zero.1 (hf.2 _ h0)

/-! ## Multiplication by the ideal on a twisted stalk -/

section

open TensorProduct in
/-- **The zeroth ideal-power inclusion at a stalk is multiplication by the trivializing
element.**  Through the stalk comparison of Tag 01CB for a tensor product and a trivialization
`eI` of `I_x`, the stalk of `I^{⊗ 1} ⊗ M ⟶ I^{⊗ 0} ⊗ M` is the action of
`f = ι_x (eI⁻¹ 1)` composed with an `O_{X,x}`-linear isomorphism. -/
private lemma injective_stalkMapL_idealPowerIncl_zero
    (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪) [Mono ι]
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (x : X)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x)
    (hM : IsSMulRegular (grpStalk X M.val x) (idealStalkMap X ι x (eI.symm 1))) :
    Function.Injective (stalkMapL X (idealPowerTerm X I (0 + 1) M).val
      (idealPowerTerm X I 0 M).val (idealPowerIncl X I ι 0 M).val x) := by
  set f := idealStalkMap X ι x (eI.symm 1) with hfdef
  set E : grpStalk X M.val x ⊗[ringStalk X x] grpStalk X I.val x ≃ₗ[ringStalk X x]
      grpStalk X M.val x :=
    (TensorProduct.congr (LinearEquiv.refl (ringStalk X x) (grpStalk X M.val x)) eI).trans
      (TensorProduct.rid (ringStalk X x) (grpStalk X M.val x)) with hEdef
  have key : ∀ t : grpStalk X M.val x ⊗[ringStalk X x] grpStalk X I.val x,
      stalkMapL X (idealPowerTerm X I (0 + 1) M).val (idealPowerTerm X I 0 M).val
          (idealPowerIncl X I ι 0 M).val x ((tensorStalkIso X x M I).symm t) = f • E t := by
    intro t
    -- Both sides are linear in `t`, so `eq_of_forall_tmul` reduces the claim to pure tensors.
    refine eq_of_forall_tmul
      ((stalkMapL X (idealPowerTerm X I (0 + 1) M).val (idealPowerTerm X I 0 M).val
          (idealPowerIncl X I ι 0 M).val x) ∘ₗ (tensorStalkIso X x M I).symm.toLinearMap)
      (f • E.toLinearMap) ?_ t
    intro m a
    show stalkMapL X (idealPowerTerm X I (0 + 1) M).val (idealPowerTerm X I 0 M).val
        (idealPowerIncl X I ι 0 M).val x
        ((tensorStalkIso X x M I).symm (m ⊗ₜ[ringStalk X x] a)) = f • E (m ⊗ₜ[ringStalk X x] a)
    refine Eq.trans (idealPowerIncl_zero_stalk_tmul X I ι M x m a) ?_
    have hE : E (m ⊗ₜ[ringStalk X x] a) = eI a • m := by
      simp only [hEdef, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        LinearEquiv.refl_apply, TensorProduct.rid_tmul]
    rw [hE, idealStalkMap_eq_mul X ι x eI a, ← hfdef, mul_smul, smul_comm]
  intro z w hzw
  obtain ⟨t, rfl⟩ := (tensorStalkIso X x M I).symm.surjective z
  obtain ⟨s, rfl⟩ := (tensorStalkIso X x M I).symm.surjective w
  exact congrArg (tensorStalkIso X x M I).symm
    (E.injective (hM ((key t).symm.trans (hzw.trans (key s)))))

end

/-! ## Untwisting an ideal power at a stalk -/

/-- **Untwisting one ideal power at a stalk.**  If the stalk `I_x` of the invertible ideal is
free of rank one over `O_{X,x}`, then tensoring by one more copy of `I` does not change the
stalk: `(I^{⊗ (n+1)} ⊗ M)_x ≅ (I^{⊗ n} ⊗ M)_x`.

The isomorphism is the successor comparison `powSuccIso` of the integer iterates of the
autoequivalence "tensor by `I`", followed by the stalk comparison of Tag 01CB for the tensor
product and by the trivialization of `I_x`. -/
public theorem nonempty_idealPowerTerm_succ_stalkEquiv (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I] (x : X)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x)
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    Nonempty (grpStalk X (idealPowerTerm X I (n + 1) M).val x ≃ₗ[ringStalk X x]
      grpStalk X (idealPowerTerm X I n M).val x) := by
  have : Functor.IsEquivalence
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I) :=
    tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I
  refine ⟨(moduleStalkIso X
      (powSuccIso (Functor.asEquivalence
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I)) n M)
      x).symm.trans
    (((tensorStalkIso X x (idealPowerTerm X I n M) I).trans
      (TensorProduct.congr (LinearEquiv.refl _ _) eI)).trans (TensorProduct.rid _ _))⟩

/-- **Untwisting an ideal power at a stalk.**  If the stalk `I_x` of the invertible ideal is
free of rank one over `O_{X,x}` then `(I^{⊗ n} ⊗ M)_x ≅ M_x` for every `n : ℤ` and every sheaf
of modules `M`.  Both signs of `n` are covered: the induction steps up with the successor
comparison and down with its inverse, so there is no constraint on `n`.

The isomorphism is not canonical — it depends on the chosen trivialization `eI` of `I_x` — but
`IsFiniteFreeStalkOfRank` only sees the isomorphism class, which is all that is used. -/
public theorem nonempty_idealPowerTerm_stalkEquiv (I : SheafOfModules.{u} Oₓ)
    [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I] (x : X)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x)
    (n : ℤ) (M : SheafOfModules.{u} Oₓ) :
    Nonempty (grpStalk X (idealPowerTerm X I n M).val x ≃ₗ[ringStalk X x]
      grpStalk X M.val x) := by
  induction n using Int.induction_on generalizing M with
  | zero => exact ⟨LinearEquiv.refl _ _⟩
  | succ k ih =>
      exact ⟨(nonempty_idealPowerTerm_succ_stalkEquiv X I x eI k M).some.trans (ih M).some⟩
  | pred k ih =>
      have e₁ := (nonempty_idealPowerTerm_succ_stalkEquiv X I x eI (-(k : ℤ) - 1) M).some.symm
      have e₂ := moduleStalkIso X
        (eqToIso (congrArg (fun j : ℤ => idealPowerTerm X I j M)
          (show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring))) x
      exact ⟨(e₁.trans e₂).trans (ih M).some⟩

/-- **Multiplication by the ideal is injective on a twisted stalk with finite free fibre.**  Let
`x` be a point at which the stalk `I_x` of the invertible ideal is trivialized by `eI` and at
which the stalk `M_x` is finite free of rank `r`.  Then the stalk at `x` of the ideal-power
inclusion `I^{⊗ (n+1)} ⊗ M ⟶ I^{⊗ n} ⊗ M` is injective, for every `n : ℤ`.

This is the hypothesis that the pointwise form of Tag 0F8N needs, proved from freeness alone:
by `exists_generatesStalkIdeal_mem_nonZeroDivisors` the element `f = ι_x (eI⁻¹ 1)` is a
nonzerodivisor of `O_{X,x}`; the twisted stalk `(I^{⊗ n} ⊗ M)_x` is again finite free of
rank `r`, so `f` acts injectively on it; and the inclusion in degree `n` is, after the successor
comparison of the ideal powers, the zeroth one on `I^{⊗ n} ⊗ M`, which is the action of `f` up
to an isomorphism.  `M` is *not* assumed `I`-torsion-free as a sheaf, which is what makes this
applicable to a cohomology sheaf. -/
public theorem injective_stalkMapL_idealPowerIncl (I : SheafOfModules.{u} Oₓ) (ι : I ⟶ 𝒪)
    [Mono ι] [Stacks.SheafOfModules.IsInvertible X.sheaf.obj (Oₓ).property I]
    (M : SheafOfModules.{u} Oₓ) (x : X) (n : ℤ) (r : ℕ)
    (eI : grpStalk X I.val x ≃ₗ[ringStalk X x] ringStalk X x)
    (eM : grpStalk X M.val x ≃ₗ[ringStalk X x] (Fin r → ringStalk X x)) :
    Function.Injective (stalkMapL X (idealPowerTerm X I (n + 1) M).val
      (idealPowerTerm X I n M).val (idealPowerIncl X I ι n M).val x) := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u} X.sheaf).flip.obj I
  have : T.IsEquivalence :=
    tensorRightFunctor_isEquivalence X.sheaf.obj (Oₓ).property I
  have hreg : IsSMulRegular (grpStalk X (idealPowerTerm X I n M).val x)
      (idealStalkMap X ι x (eI.symm 1)) :=
    isSMulRegular_of_stalk_linearEquiv X _
      (mem_nonZeroDivisors_idealStalkMap X I ι x eI)
      ((nonempty_idealPowerTerm_stalkEquiv X I x eI n M).some.trans eM)
  have hcomp : stalkMapL X (idealPowerTerm X I (n + 1) M).val
        (idealPowerTerm X I n M).val (idealPowerIncl X I ι n M).val x =
      (stalkMapL X (idealPowerTerm X I (0 + 1) (idealPowerTerm X I n M)).val
          (idealPowerTerm X I 0 (idealPowerTerm X I n M)).val
          (idealPowerIncl X I ι 0 (idealPowerTerm X I n M)).val x).comp
        (stalkMapL X (idealPowerTerm X I (n + 1) M).val
          (T.asEquivalence.functor.obj (idealPowerTerm X I n M)).val
          (powSuccIso T.asEquivalence n M).inv.val
          x) :=
    stalkMapL_comp X (idealPowerTerm X I (n + 1) M)
      (T.asEquivalence.functor.obj (idealPowerTerm X I n M))
      (idealPowerTerm X I n M)
      (powSuccIso T.asEquivalence n M).inv
      (idealPowerIncl X I ι 0 (idealPowerTerm X I n M)) x
  rw [hcomp]
  exact (injective_stalkMapL_idealPowerIncl_zero X I ι (idealPowerTerm X I n M) x eI
    hreg).comp (stalkMapL_injective_of_mono X
      (powSuccIso T.asEquivalence n M).inv x)

end Stacks.IdealTorsion.Eta

end

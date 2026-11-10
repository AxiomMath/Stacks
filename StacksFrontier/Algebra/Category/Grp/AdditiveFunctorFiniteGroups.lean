module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additive functors on finitely generated abelian groups annihilated by an integer

Let `T` be an additive functor from abelian groups to a preadditive category. If `T` kills the
cyclic groups `ℤ/dℤ` for every divisor `d` of an integer `n` (with `ℤ/0ℤ = ℤ`), then it kills
every finitely generated abelian group annihilated by `n`. Such a group `M` is a finite direct
sum of copies of `ℤ` and of cyclic groups `ℤ/p^eℤ`; each summand embeds in `M`, so its order
divides `n` (a copy of `ℤ` forces `n = 0`). The identity of `M` is the sum of the composites
`M ⟶ ℤ/dℤ ⟶ M` of the projections and inclusions of the summands, and `T` carries each
composite to a morphism through a zero object.

This is the step of [Stacks, Tag 0F08] which replaces a coefficient group annihilated by `n` by a
cyclic one.

## Main results

* `AddCommGrpCat.isZero_obj_of_fg_of_zsmul_eq_zero` — an additive functor killing `ℤ/dℤ` for every
  `d ∣ n` kills every finitely generated abelian group annihilated by `n`.

## References

* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace AddCommGrpCat

/-- **An additive functor killing every `ℤ/dℤ` with `d ∣ n` kills every finitely generated
abelian group annihilated by `n`.** Write the group as `ℤ^m ⊕ ⨁ ℤ/p^eℤ`; a generator of each
summand is annihilated by `n`, so `p^e ∣ n`, and `n = 0` if `m > 0`; the identity of the group
is the sum over the summands of projection followed by inclusion, and the functor carries each of
those composites through a zero object. -/
theorem isZero_obj_of_fg_of_zsmul_eq_zero {C : Type*} [Category.{w} C] [Preadditive C]
    (T : AddCommGrpCat.{v} ⥤ C) [T.Additive] (n : ℤ)
    (hT : ∀ d : ℕ, (d : ℤ) ∣ n → IsZero (T.obj (AddCommGrpCat.of (ULift.{v} (ZMod d)))))
    (M : AddCommGrpCat.{v}) [AddGroup.FG M] (hM : ∀ x : M, n • x = 0) : IsZero (T.obj M) := by
  classical
  obtain ⟨m, ι, _, p, _, e, ⟨φ⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod M
  -- The order of each summand.
  let d : Fin m ⊕ ι → ℕ := Sum.elim (fun _ ↦ 0) (fun i ↦ p i ^ e i)
  have hdvd : ∀ k, (d k : ℤ) ∣ n := by
    rintro (j | i)
    · have h := congrArg (fun y ↦ (φ y).1 j) (hM (φ.symm (Finsupp.single j 1, 0)))
      simp only [map_zsmul, AddEquiv.apply_symm_apply, map_zero, Prod.smul_mk,
        Prod.fst_zero, Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.single_eq_same] at h
      simp [d, h]
    · have h := congrArg (fun y ↦ (φ y).2 i) (hM (φ.symm (0, DirectSum.of _ i 1)))
      simp only [map_zsmul, AddEquiv.apply_symm_apply, map_zero, Prod.smul_mk, smul_zero,
        Prod.snd_zero, DirectSum.zero_apply] at h
      rw [DirectSum.smul_apply, DirectSum.of_eq_same, zsmul_one] at h
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd n (p i ^ e i)).1 h
  -- The projections onto and inclusions of the summands.
  let π : ∀ k, M ⟶ AddCommGrpCat.of (ULift.{v} (ZMod (d k))) := fun k ↦ match k with
    | Sum.inl j => AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((Finsupp.applyAddHom j).comp ((AddMonoidHom.fst _ _).comp φ.toAddMonoidHom)))
    | Sum.inr i => AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
        ((DirectSum.component ℤ ι _ i).toAddMonoidHom.comp
          ((AddMonoidHom.snd _ _).comp φ.toAddMonoidHom)))
  let ι' : ∀ k, AddCommGrpCat.of (ULift.{v} (ZMod (d k))) ⟶ M := fun k ↦ match k with
    | Sum.inl j => AddCommGrpCat.ofHom (φ.symm.toAddMonoidHom.comp
        ((AddMonoidHom.inl _ _).comp ((Finsupp.singleAddHom j).comp
          AddEquiv.ulift.toAddMonoidHom)))
    | Sum.inr i => AddCommGrpCat.ofHom (φ.symm.toAddMonoidHom.comp
        ((AddMonoidHom.inr _ _).comp ((DirectSum.of _ i).comp AddEquiv.ulift.toAddMonoidHom)))
  have hsum : ∑ k, π k ≫ ι' k = 𝟙 M := by
    ext x
    have hhom : (∑ k, π k ≫ ι' k).hom = ∑ k, (π k ≫ ι' k).hom :=
      map_sum AddCommGrpCat.homAddEquiv _ _
    rw [hhom, AddMonoidHom.finsetSum_apply, Fintype.sum_sum_type]
    apply φ.injective
    rw [map_add, map_sum, map_sum, AddCommGrpCat.hom_id, AddMonoidHom.id_apply]
    refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sum, Prod.snd_sum,
      AddEquiv.toAddMonoidHom_eq_coe, hom_comp, ConcreteCategory.hom_ofHom,
      AddMonoidHom.coe_comp, AddMonoidHom.coe_ofClass, AddMonoidHom.coe_fst, Function.comp_apply,
      Finsupp.applyAddHom_apply, Finsupp.singleAddHom_apply, AddMonoidHom.inl_apply,
      AddEquiv.apply_symm_apply, LinearMap.toAddMonoidHom_coe, AddMonoidHom.coe_snd,
      AddMonoidHom.inr_apply, Finset.sum_const_zero, add_zero, zero_add, π, ι']
    · exact Finsupp.univ_sum_single _
    · conv_rhs => rw [← DirectSum.sum_univ_of (φ x).2]
      rfl
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← T.map_id, ← hsum, T.map_sum]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [T.map_comp, (hT _ (hdvd k)).eq_zero_of_tgt (T.map (π k)), zero_comp]

end AddCommGrpCat

module

public import StacksFrontier.AlgebraicGeometry.FreeStalkBasis.BiprodPowStalk
public import StacksFrontier.AlgebraicGeometry.FreeStalkBasis.LocalRank
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (5) of Tag 0AYT at arbitrary rank

[Stacks, Tag 0AYT] (5) says that for `X` proper over a field `k`, `ℱ` coherent with
`dim Supp ℱ ≤ 0` and `ℰ` locally free of rank `n`,

  `χ(X, ℱ ⊗ ℰ) = n · χ(X, ℱ)`.

This file proves it, at every rank. Its whole content is the sheaf isomorphism

  `ℰ ⊗ ℱ ≅ ℱ^{⊞ n}`,

after which the Euler-characteristic formula is
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_iso_biprodPow`, which needs
no finiteness input. The predecessors of these statements settled the clause only at `n = 1`
(`StacksFrontier/AlgebraicGeometry/TensorEulerZeroDim/Basic.lean`).

## The construction

The isomorphism is the rank-`n` form of the rank-one isomorphism
`AlgebraicGeometry.nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/ZeroDimensionalTensor.lean`), and the covering
is literally the same one: the complement of `Supp ℱ` together with, for each `x` in the
support, an open `N x ⊓ T x` where `N x` meets the support in `x` alone and `T x` carries `n`
sections of `ℰ` whose germs at `x` are a basis of `ℰ_x`. Two distinct members of that covering
meet only outside the support, which is what makes the glueing compatibility vacuous.

What differs from rank one is that there are now `n` comparison morphisms rather than one. The
`j`-th is `s ↦ s ⊗ aⱼ`, glued by `AlgebraicGeometry.exists_hom_app_eq_tmulSection` applied
unchanged — that lemma already takes one section of the second factor per chart, so one
application per basis index is all it needs. The `n` morphisms are assembled into a single
`ℱ^{⊞ n} ⟶ ℱ ⊗ ℰ` by `AlgebraicGeometry.Scheme.Modules.biprodPowDesc`, and that morphism is
shown invertible stalkwise by
`AlgebraicGeometry.isIso_biprodPowDesc_of_bijective_sum_stalkMap`.

The stalkwise hypothesis splits into the same two cases as at rank one.

* **At a point of the support** the chart contains it, and the stalk of the assembled morphism
  is, read through `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, the map `(gⱼ) ↦
    ∑ⱼ gⱼ ⊗ aⱼ(x)` with
  `aⱼ(x)` a basis of `ℰ_x`. That this is bijective is `TensorProduct.bijective_sum_tmul_right`
  below, which is Mathlib's `TensorProduct.equivFinsuppOfBasisRight` restated for a basis
  presented as a bijection rather than as a `Module.Basis`.
* **Off the support** both stalks vanish and every map between them is bijective.

## Main results

* `TensorProduct.bijective_sum_tmul_right`: if `c ↦ ∑ⱼ cⱼ • bⱼ` is a bijection `(Fin n → R) → B`
  then `g ↦ ∑ⱼ gⱼ ⊗ bⱼ` is a bijection `(Fin n → A) → A ⊗[R] B`.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_sum_stalkMapL_of_germ_basis`: at a point
  where the `n` fixed sections
  have germs forming a basis of the stalk of the second factor, the assembled comparison is
  bijective on that stalk.
* `Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_sum_stalkMapL_of_subsingleton`: where the
  stalk of the first factor
  vanishes, every such map is bijective.
* `AlgebraicGeometry.nonempty_tensorSheafIso_biprodPow_of_topologicalKrullDim_supp_le_zero`:
  **the isomorphism `ℰ ⊗ ℱ ≅ ℱ^{⊞ n}`**, the whole remaining content of clause (5).
* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank`:
  clause (5) with the locally free factor written first — the order of the hypothesis `h0AYT` of
  `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`,
  which this discharges.
* `AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_rank_mul`: **clause (5) in the
  source's own argument order**, and the declaration that carries the tag.

## Implementation notes

**The tag is placed, on one declaration, in the source's argument order.**
[Stacks, Tag 0AYT] (5) writes `χ(X, ℱ ⊗ ℰ) = n χ(X, ℱ)` with the coherent
factor first. The chain above it — in particular
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add` —
writes the locally free factor first. Both orders are therefore stated here, the second being
one application of `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap` away from the
first, and `@[stacks 0AYT "tensor_rank"]` sits on the one in the source's order. The other
clauses of Tag 0AYT are not settled here, which is why the attribute carries the clause string.

**Why the rank hypothesis is an instance binder here and an explicit argument in `LocalRank`.**
`AlgebraicGeometry.exists_germ_basis_of_isFiniteLocallyFreeOfRank` declares its module at the
`structureSheafRing` spelling, where the class is not
  found by instance search and
has to be passed positionally. The statements below declare their modules at
`AlgebraicGeometry.Scheme.Modules`, where it is found, so the binder is an instance binder — the
same shape the rank-one statements and the consuming chain use. The crossing happens at the one
application inside the proof.

**The scalar action on a stalk is only available at one of the two spellings.** With `ℰ` at
`X.Modules` the term `c • Stacks.SheafOfModules.TensorStalkRingedSpace.grpGerm …` is
  `synthInstanceFailed`, so the rank-`n`
basis equation is never written out in the assembly: the germ-restriction identity is rewritten
into the goal with `simp only`, whose left-hand side is a germ and carries no scalar action.
This is the spelling wall of `LocalRank`'s implementation note, met from the other side.

## References

* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace TensorProduct

/-- **Tensoring with a basis of a free module of rank `n` is bijective.** If
`c ↦ ∑ⱼ cⱼ • bⱼ` is a bijection `(Fin n → R) → B` then `g ↦ ∑ⱼ gⱼ ⊗ bⱼ` is a bijection
`(Fin n → A) → A ⊗[R] B`.

This is Mathlib's `TensorProduct.equivFinsuppOfBasisRight`, whose inverse is exactly
`(mⱼ) ↦ ∑ⱼ mⱼ ⊗ bⱼ`, restated for a basis presented as a bijection: the hypothesis is turned
into a `Module.Basis` by `Module.Basis.ofEquivFun` of
`Fintype.linearCombination`, and `Finsupp.linearEquivFunOnFinite` turns the finitely supported
family of the Mathlib statement into a function. It is the rank-`n` form of
`TensorProduct.bijective_tmul_right`
(`StacksFrontier/AlgebraicGeometry/TwistedSheaf/ZeroDimensionalTensor.lean`), which is the same
statement at `n = 1` with the sum and the index suppressed. -/
theorem bijective_sum_tmul_right {R A B : Type u} [CommRing R] [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] {n : ℕ} (b : Fin n → B)
    (hb : Function.Bijective fun c : Fin n → R => ∑ j, c j • b j) :
    Function.Bijective fun g : Fin n → A => ∑ j, g j ⊗ₜ[R] b j := by
  classical
  have hlc : (Fintype.linearCombination R b : (Fin n → R) → B) = fun c => ∑ j, c j • b j :=
    funext (Fintype.linearCombination_apply R b)
  let e : (Fin n → R) ≃ₗ[R] B :=
    LinearEquiv.ofBijective (Fintype.linearCombination R b) (by rwa [hlc])
  let bas : Module.Basis (Fin n) R B := Module.Basis.ofEquivFun e.symm
  have hbas : ∀ j, bas j = b j := fun j => by simp [bas, e]
  let Ψ : (Fin n → A) ≃ₗ[R] TensorProduct R A B :=
    (Finsupp.linearEquivFunOnFinite R A (Fin n)).symm.trans
      (TensorProduct.equivFinsuppOfBasisRight bas).symm
  have hΨ : ∀ g : Fin n → A, Ψ g = ∑ j, g j ⊗ₜ[R] b j := by
    intro g
    show (TensorProduct.equivFinsuppOfBasisRight bas).symm
        ((Finsupp.linearEquivFunOnFinite R A (Fin n)).symm g) = _
    rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply,
      Finsupp.sum_fintype _ _ (fun i => TensorProduct.zero_tmul A (bas i))]
    exact Finset.sum_congr rfl fun j _ => by rw [hbas j]; rfl
  rw [← funext hΨ]
  exact Ψ.bijective

end TensorProduct

namespace Stacks.SheafOfModules.TensorStalkRingedSpace

variable {X : RingedSpace.{u, u}}

/-- **At a point where the `n` fixed sections have germs forming a basis of the stalk of the
second factor, the assembled comparison is bijective on that stalk.** The `j`-th morphism acts
on sections over every open inside `W` by tensoring with the fixed section `a j`; the map
in question is `(gⱼ) ↦ ∑ⱼ (ψⱼ)_y (gⱼ)`.

Read through `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso` each summand is `gⱼ ⊗
  germ_y (a j)`, by
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso_stalkMapL_eq` applied once per index,
  so the whole map is
`(gⱼ) ↦ ∑ⱼ gⱼ ⊗ germ_y (a j)` and `TensorProduct.bijective_sum_tmul_right` finishes. This is
the rank-`n` form of
  `Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_stalkMapL_of_germ_basis`. -/
theorem bijective_sum_stalkMapL_of_germ_basis (G M : SheafOfModules.{u} (structureSheafRing X))
    {n : ℕ} (ψ : Fin n → (G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (G)).obj (M)))) (W : Opens X.carrier)
    (a : Fin n → M.val.obj (op W))
    (hψ : ∀ (j : Fin n) (V : Opens X.carrier) (h : V ≤ W) (s : G.val.obj (op V)),
      ((ψ j).val.app (op V)).hom s = toTensorSheafSection X G M (op V)
        (s ⊗ₜ[X.presheaf.obj (op V)] ((M.val).restrictₛₗ ((homOfLE h).op)) (a j)))
    (y : X.carrier) (hy : y ∈ W)
    (hbasis : Function.Bijective fun c : Fin n → ringStalk X y =>
      ∑ j, c j • grpGerm X M.val y W hy (a j)) :
    Function.Bijective (fun g : Fin n → grpStalk X G.val y =>
      ∑ j, stalkMapL X G.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
            ((X)).IsSheaf⟩).obj (G)).obj (M))).val (ψ j).val y (g j)) := by
  have hcomp : ((tensorStalkIso X y G M) ∘
        (fun g : Fin n → grpStalk X G.val y =>
          ∑ j, stalkMapL X G.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
                ((X)).IsSheaf⟩).obj (G)).obj (M))).val (ψ j).val y (g j)))
      = fun g : Fin n → grpStalk X G.val y =>
        ∑ j, g j ⊗ₜ[ringStalk X y] grpGerm X M.val y W hy (a j) := by
    funext g
    show (tensorStalkIso X y G M) (∑ j, _) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ =>
      tensorStalkIso_stalkMapL_eq G M (ψ j) W (a j) (hψ j) y hy (g j)
  refine (Function.Bijective.of_comp_iff' (tensorStalkIso X y G M).bijective _).mp ?_
  rw [hcomp]
  exact TensorProduct.bijective_sum_tmul_right _ hbasis

/-- **Where the stalk of the first factor vanishes, every such sum of stalk maps is
bijective**: the target is a subsingleton by
`Stacks.SheafOfModules.TensorStalkRingedSpace.subsingleton_grpStalk_tensorSheaf`, and the source is
  a finite power of the
hypothesis, so `Pi.instSubsingleton` needs no help. This is the rank-`n` form of
`Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_stalkMapL_of_subsingleton`. -/
theorem bijective_sum_stalkMapL_of_subsingleton
    (G M : SheafOfModules.{u} (structureSheafRing X)) {n : ℕ}
    (ψ : Fin n → (G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (G)).obj (M)))) (y : X.carrier)
    (h : Subsingleton (grpStalk X G.val y)) :
    Function.Bijective (fun g : Fin n → grpStalk X G.val y =>
      ∑ j, stalkMapL X G.val ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
            ((X)).IsSheaf⟩).obj (G)).obj (M))).val (ψ j).val y (g j)) :=
  have _htgt := subsingleton_grpStalk_tensorSheaf G M y h
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **A finite locally free sheaf of rank `n` turns a coherent sheaf with zero-dimensional
support into its `n`-fold biproduct**: `ℰ ⊗ ℱ ≅ ℱ^{⊞ n}`. This is the whole remaining content
of clause (5) of [Stacks, Tag 0AYT], and the rank-`n` form of
`AlgebraicGeometry.nonempty_tensorModulesIso_of_topologicalKrullDim_supp_le_zero`.

See the module docstring for the construction: the covering is the rank-one proof's, the `n`
comparison morphisms are `n` applications of
`AlgebraicGeometry.exists_hom_app_eq_tmulSection`, they are assembled by
`AlgebraicGeometry.Scheme.Modules.biprodPowDesc`, and the assembled morphism is inverted
stalkwise. -/
theorem nonempty_tensorSheafIso_biprodPow_of_topologicalKrullDim_supp_le_zero
    [IsLocallyNoetherian X] (G : X.Modules) [G.IsCoherent]
    (hG : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    Nonempty (((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G)) :
      X.Modules) ≅
      Scheme.Modules.biprodPow G n) := by
  classical
  choose N hxN hN using fun x : ↥(_root_.SheafOfModules.supp G) =>
    exists_open_neighborhood_meets_support_singleton G hG x
  choose T hxT a hbasis using fun x : ↥(_root_.SheafOfModules.supp G) =>
    exists_germ_basis_of_isFiniteLocallyFreeOfRank E n ‹_› (x : X)
  have : G.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  let C : X.Opens :=
    ⟨(_root_.SheafOfModules.supp G)ᶜ, (SheafOfModules.isClosed_supp G).isOpen_compl⟩
  let W : Option ↥(_root_.SheafOfModules.supp G) → X.Opens :=
    fun i => i.elim C fun x => N x ⊓ T x
  let A : (i : Option ↥(_root_.SheafOfModules.supp G)) → Fin n → Γ(E, W i) := fun i =>
    match i with
    | none => fun _ => 0
    | some x => fun j =>
        E.presheaf.map (homOfLE (inf_le_right : N x ⊓ T x ≤ T x)).op (a x j)
  have hW : ∀ y : X, ∃ i, y ∈ W i := fun y =>
    if hy : y ∈ _root_.SheafOfModules.supp G then ⟨some ⟨y, hy⟩, hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩
    else ⟨none, hy⟩
  have hdisj : ∀ i j, i ≠ j → ∀ y : X, y ∈ W i → y ∈ W j →
      y ∉ _root_.SheafOfModules.supp G := fun i j hij y hi hj hys => by
    match i, j with
    | none, _ => exact hi hys
    | _, none => exact hj hys
    | some x, some x' =>
      exact hij (congrArg some (Subtype.ext ((hN x y hi.1 hys).symm.trans (hN x' y hj.1 hys))))
  choose ψ hψ using fun j : Fin n =>
    exists_hom_app_eq_tmulSection G E W hW (fun i => A i j) hdisj
  let ψ' : Fin n → (G ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj G).obj E) := ψ
  have hiso : IsIso (Scheme.Modules.biprodPowDesc G (tensorModules G E) n ψ) := by
    refine isIso_biprodPowDesc_of_bijective_sum_stalkMap G _ n ψ fun y => ?_
    by_cases hy : y ∈ _root_.SheafOfModules.supp G
    · refine Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_sum_stalkMapL_of_germ_basis
        G E ψ' (W (some ⟨y, hy⟩)) (A (some ⟨y, hy⟩))
        (fun j V h s => hψ j (some ⟨y, hy⟩) V h s) y
        ⟨hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩ ?_
      have hres : ∀ j : Fin n,
          grpGerm X.toRingedSpace E.val y (W (some ⟨y, hy⟩)) ⟨hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩
              (A (some ⟨y, hy⟩) j)
            = grpGerm X.toRingedSpace E.val y (T ⟨y, hy⟩) (hxT ⟨y, hy⟩) (a ⟨y, hy⟩ j) := fun j =>
        TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) E.val.presheaf
          (homOfLE (inf_le_right : N ⟨y, hy⟩ ⊓ T ⟨y, hy⟩ ≤ T ⟨y, hy⟩)) y
          ⟨hxN ⟨y, hy⟩, hxT ⟨y, hy⟩⟩ (a ⟨y, hy⟩ j)
      simpa only [hres] using hbasis ⟨y, hy⟩
    · exact Stacks.SheafOfModules.TensorStalkRingedSpace.bijective_sum_stalkMapL_of_subsingleton
        G E ψ' y
        (SheafOfModules.subsingleton_stalk_of_notMem_supp G hy)
  exact ⟨(Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace E G).trans
    (asIso (Scheme.Modules.biprodPowDesc G (tensorModules G E) n ψ)).symm⟩

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- **Clause (5) of [Stacks, Tag 0AYT] at arbitrary rank, with the locally free factor written
first.** For `X` proper over a field, `𝒢` coherent with support of dimension at most zero and
`ℰ` finite locally free of rank `n`, `χ(X, ℰ ⊗ 𝒢) = n · χ(X, 𝒢)`.

This is the argument order and the exact shape of the hypothesis `h0AYT` of
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add`, so
it discharges that input of [Stacks, Tag 0AYV]. The tag is carried instead by
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_rank_mul`, which is this statement
in the source's own argument order.

The isomorphism is
`AlgebraicGeometry.nonempty_tensorSheafIso_biprodPow_of_topologicalKrullDim_supp_le_zero` and
the passage to Euler characteristics is
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_iso_biprodPow`; the local
Noetherianity the isomorphism asks for comes from properness over a field. -/
theorem exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank [IsProper f]
    (E G : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n]
    [SheafOfModules.IsCoherent G]
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0) :
    ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (G))) hT =
        (n : ℤ) * eulerCharacteristic k f G :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  (nonempty_tensorSheafIso_biprodPow_of_topologicalKrullDim_supp_le_zero G hdim E n).elim
    fun e => exists_eulerCharacteristic_tensorSheaf_eq_mul_of_iso_biprodPow k f E G n e

/-- **Clause (5) of [Stacks, Tag 0AYT].** Let `k` be a field, `X` a proper scheme over `k` and
`ℱ` a coherent sheaf with `dim Supp ℱ ≤ 0`. Then

  `χ(X, ℱ ⊗ ℰ) = n · χ(X, ℱ)`

for every locally free module `ℰ` of rank `n`.

This is the clause in the argument order the source writes it in, with the coherent factor
first; the Euler
characteristic requires its argument to be coherent, so the conclusion also supplies that. The
other order, which the chain above this clause consumes, is
`AlgebraicGeometry.exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank`,
and the two differ by `Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap`.

The clause string is on the attribute because the other four clauses of Tag 0AYT are not proved
here: clause (1) is registered on
`AlgebraicGeometry.nonempty_generatingSections_of_support_dim_le_zero`, and clauses (2), (3) and
(4) in `StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing`, on
`AlgebraicGeometry.suppStalkDirectSumAddEquiv` together with
`AlgebraicGeometry.cohomologyOverFieldZeroEquivDirectSumSuppStalk`, on
`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero` and on
`AlgebraicGeometry.eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero`. -/
@[stacks 0AYT "tensor_rank"]
theorem exists_eulerCharacteristic_tensorSheaf_eq_rank_mul [IsProper f] (F : X.Modules)
    [SheafOfModules.IsCoherent F]
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp F) ≤ 0) (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (E))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (E))) h =
        (n : ℤ) * eulerCharacteristic k f F := by
  obtain ⟨hT, hχ⟩ :=
    exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank k f E F n hdim
  have e : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (E)) :
    X.Modules) ≅
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
          ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj (F)) : X.Modules) :=
    Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace F E
  have hF : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
      ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (E))).IsCoherent := by
    let P : ObjectProperty X.Modules := fun M => M.IsCoherent
    have : P.IsWeakSerreClass := _root_.SheafOfModules.coherentModules_isWeakSerreClass
    exact P.prop_of_iso e.symm hT
  exact ⟨hF, (@eulerCharacteristic_eq_of_iso k _ X f _ _ _ hF hT e).trans hχ⟩

/-- **NON-VACUITY: the structure sheaf satisfies the hypothesis on `ℰ`.** Tensoring by `𝒪_X`
multiplies the Euler characteristic by one, which is the clause at the rank-one module the
library can always exhibit. -/
theorem exists_eulerCharacteristic_tensorSheaf_unit_eq_mul [IsProper f] (G : X.Modules)
    [SheafOfModules.IsCoherent G]
    (hdim : topologicalKrullDim (_root_.SheafOfModules.supp G) ≤ 0) :
    ∃ hT : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
        ((X.toRingedSpace)).IsSheaf⟩).obj ((_root_.SheafOfModules.unit X.ringCatSheaf))).obj
        (G))).IsCoherent,
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((_root_.SheafOfModules.unit X.ringCatSheaf))).obj (G))) hT =
        ((1 : ℕ) : ℤ) * eulerCharacteristic k f G :=
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (_root_.SheafOfModules.unit X.ringCatSheaf) 1 :=
    (Stacks.SheafOfModules.Invertible.isFiniteLocallyFreeOfRank_one_unit
      (R := X.ringCatSheaf)).exists_isFiniteLocallyFreeOfRankData.elim
      fun q hq => { exists_isFiniteLocallyFreeOfRankData := ⟨q, hq⟩ }
  exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank k f _ G 1 hdim

end AlgebraicGeometry

end

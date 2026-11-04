module

public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposLowerShriekUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
public import StacksFrontier.Deformation.ToposThickening.FlatLiftLocalLifting
public import StacksFrontier.Deformation.ToposThickening.IdealActionMono
public import StacksFrontier.Deformation.ToposThickening.TrivialExtension

/-!
# Finite presentation of a flat module across a first order thickening

Let `(f, f')` be a morphism of first order thickenings of ringed topoi as in Situation 08M7

```
  (Sh(C), O)   --i-->  (Sh(D), O')
      |                    |
      f                    f'
      v                    v
  (Sh(B), O_ℬ) --t-->  (Sh(B'), O_{ℬ'})
```

with square-zero ideal `I = Ker(i^♯) ⊂ O'`, let `ℱ'` be an `O'`-module and set `ℱ = i^*ℱ'`.
**Stacks 08VU** says that if `ℱ'` is flat over `O_{ℬ'}` and `(f, f')` is strict, then `ℱ'` is of
finite presentation if and only if `ℱ` is.

## Main results

* `Deformation.ToposThickening.isFinitePresentation_iff_pullbackModules_of_isFlat`:
  **Stacks 08VU**.
* `Deformation.ToposThickening.locallySpansKernel_of_isLiftedData`: the step of the proof that
  uses the hypotheses — every relation among lifted generators is locally a combination of the
  lifted relations, as soon as the action `I ⊗_{O'} ℱ' ⟶ ℱ'` is injective.
* `Deformation.ToposThickening.inhabitedSieve_mem_of_isPresentationData_reduction`: a section-level
  presentation of `i^*ℱ'` over an object of the thickened site lifts, on a covering, to one of
  `ℱ'`.
* `Deformation.ToposThickening.isFinitePresentation_reduction_of_isFinitePresentation`: `ℱ` of
  finite presentation makes its direct image `i_*ℱ`, an `i_*O`-module on the thickened site, of
  finite presentation.

## How the proof goes

The direction (1) ⇒ (2) is Stacks 03DO,
`Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules`.

For (2) ⇒ (1) the source assumes, as it may, that the two sites agree. Here the agreement is
made by Stacks 03DM: the morphism `(Sh(C), O) ⟶ (Sh(D), i_*O)` with the same underlying
morphism of topoi as `i` is an equivalence of ringed topoi, so `i_*ℱ` is an `i_*O`-module of
finite presentation on the site of `D` (`isFinitePresentation_reduction_of_isFinitePresentation`).
Everything else happens on that one site, with section-level presentation data
(`Stacks.Sheaves.LocalGeneration.IsPresentationData`): `n` sections, `m` relation tuples, and the
conditions (A) each tuple is a relation, (B) the sections generate locally, (C) every relation is
locally a combination of the tuples.

Over an object `V` carrying such data `(s̄, t̄)` for `i_*ℱ`, the generators and the relations are
lifted and the relations corrected
(`StacksFrontier/Deformation/ToposThickening/FlatLiftLocalLifting.lean`), which gives (A) and (B)
for the lift `(s, t)`. Condition (C) is the source's "right exactness of `⊗` once more": a
relation `∑ a_j s_j = 0` reduces to a relation among the `s̄`, hence is locally
`∑ b_k t_k` up to a tuple `e = incl ε` of sections of `I` with `∑ ε_j s_j = 0`. Because the action
of `I` on `ℱ'` is injective (`Deformation.ToposThickening.isIdealActionMono`, the final assertion
of Stacks 08MQ, which is where flatness and strictness enter), the section `∑ ε_j ⊗ s̄_j` of
`I ⊗_O i_*ℱ` vanishes, hence vanishes locally in the presheaf tensor product
(`idealTensor_sum_tmul_locally_eq_zero`). The equational criterion for vanishing of tensors
(`exists_relations_of_sum_tmul_eq_zero`) then writes `ε` as `∑_κ ρ_κ y_κ` with `ρ_κ` relations
among the `s̄`, after completing the `s̄` locally to generators, and condition (C) for `(s̄, t̄)`
turns this into an `I`-combination of the rows of `t̄`, which is an `O'`-combination of the rows
of `t` (`relationSpanSieve_incl_mem_of_sum_tmul_eq_zero`).

## References

* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.LocalGeneration

universe v u v' u' w vS uS wS vS' uS' wS'

namespace Deformation.ToposThickening

section Algebra

open TensorProduct

/-- **A vanishing tensor, written out on finitely many elements.** If `∑ⱼ eⱼ ⊗ yⱼ = 0` in
`P ⊗_R Q`, then there are finitely many further elements `z` of `Q`, elements `f` of `P` and
coefficients `a`, `a'` such that every `eⱼ` is the combination `∑_κ a_{jκ} f_κ`, the
combinations `∑_κ a'_{lκ} f_κ` vanish, and every column of `(a, a')` is a relation among the
`y` and the `z`.

This is the equational criterion for vanishing
(`TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero`) applied in a finitely generated submodule
of `Q` containing the `y` in which the tensor already vanishes; the `z` complete the `y` to a
generating family of that submodule. -/
theorem exists_relations_of_sum_tmul_eq_zero {R Q P : Type*} [CommRing R] [AddCommGroup Q]
    [Module R Q] [AddCommGroup P] [Module R P] {n : ℕ} (e : Fin n → P) (y : Fin n → Q)
    (h : ∑ j, e j ⊗ₜ[R] y j = 0) :
    ∃ (r : ℕ) (z : Fin r → Q) (k : ℕ) (a : Fin n → Fin k → R) (a' : Fin r → Fin k → R)
      (f : Fin k → P),
      (∀ j, e j = ∑ κ, a j κ • f κ) ∧ (∀ l, ∑ κ, a' l κ • f κ = 0) ∧
        ∀ κ, ∑ j, a j κ • y j + ∑ l, a' l κ • z l = 0 := by
  classical
  let P₀ : Submodule R Q := Submodule.span R (Set.range y)
  have hP₀ : P₀.FG := Submodule.fg_span (Set.finite_range y)
  have hy : ∀ j, y j ∈ P₀ := fun j => Submodule.subset_span ⟨j, rfl⟩
  let t : P₀ ⊗[R] P := ∑ j, (⟨y j, hy j⟩ : P₀) ⊗ₜ[R] e j
  have h' : ∑ j, y j ⊗ₜ[R] e j = 0 := by
    simpa [map_sum] using congrArg (TensorProduct.comm R P Q) h
  have ht : LinearMap.rTensor P P₀.subtype t = 0 := by
    simpa [t, map_sum, LinearMap.rTensor_tmul] using h'
  obtain ⟨Q₁, hle, hfg, ht₁⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hP₀ ht
  obtain ⟨r, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  have hzmem : ∀ l, z l ∈ Q₁ := fun l => hz ▸ Submodule.subset_span ⟨l, rfl⟩
  let m : Fin n ⊕ Fin r → Q₁ :=
    Sum.elim (fun j => ⟨y j, hle (hy j)⟩) (fun l => ⟨z l, hzmem l⟩)
  let nn : Fin n ⊕ Fin r → P := Sum.elim e 0
  have hm : Submodule.span R (Set.range m) = ⊤ := by
    apply Submodule.map_injective_of_injective (Submodule.injective_subtype Q₁)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    refine le_antisymm (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      rcases i with j | l
      · exact hle (hy j)
      · exact hzmem l
    · intro x hx
      rw [← hz] at hx
      exact Submodule.span_mono (show Set.range z ⊆ Set.range (Q₁.subtype ∘ m) from
        fun _ ⟨l, hl⟩ => ⟨Sum.inr l, hl⟩) hx
  have hsum : ∑ i, m i ⊗ₜ[R] nn i = (0 : Q₁ ⊗[R] P) := by
    rw [Fintype.sum_sum_type]
    simp only [m, nn, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, TensorProduct.tmul_zero,
      Finset.sum_const_zero, add_zero]
    refine Eq.trans ?_ ht₁
    simp only [t, map_sum, LinearMap.rTensor_tmul]
    rfl
  obtain ⟨k, a, f, hnn, hrel⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero R hm hsum
  refine ⟨r, z, k, fun j => a (Sum.inl j), fun l => a (Sum.inr l), f, fun j => ?_, fun l => ?_,
    fun κ => ?_⟩
  · simpa [nn] using hnn (Sum.inl j)
  · simpa [nn] using (hnn (Sum.inr l)).symm
  · have h1 := congrArg Q₁.subtype (hrel κ)
    rw [Fintype.sum_sum_type] at h1
    simpa [m, map_add, map_sum] using h1

end Algebra

section IdealCombination

open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap multiplicationMap_tmul
  reductionTensorMap reductionTensorMap_tmul)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inclusion of the square-zero ideal is additive. -/
lemma idealSection_sum (hi : FirstOrderThickening i) {U : Y.Cᵒᵖ} {ι : Type*} (s : Finset ι)
    (b : ι → hi.I.val.obj U) :
    idealSection hi _ (∑ k ∈ s, b k) = ∑ k ∈ s, idealSection hi _ (b k) :=
  map_sum (hi.incl.val.app U).hom b s

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The inclusion of the square-zero ideal commutes with restriction. -/
lemma idealSection_map (hi : FirstOrderThickening i) {U V : Y.Cᵒᵖ} (g : U ⟶ V)
    (b : hi.I.val.obj U) :
    (ringSheaf Y.O).obj.map g (idealSection hi _ b) = idealSection hi _ (restr hi.I g b) :=
  (PresheafOfModules.naturality_apply hi.incl.val g b).symm

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **A tensor of the ideal with the reduction that dies in `ℱ'` dies locally on sections.** Let
`q : ℱ' ⟶ M` be a map to an `O`-module and suppose the action `I ⊗_{O'} ℱ' ⟶ ℱ'` of the
square-zero ideal is injective. If `∑ ε_j s_j = 0` in `ℱ'` with `ε_j` sections of `I`, then the
section `∑ ε_j ⊗ q(s_j)` of the presheaf tensor product `I ⊗_O M` vanishes on a covering. -/
theorem idealTensor_sum_tmul_locally_eq_zero (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (ringSheaf Y.O)} {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M)
    (hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl)) {W : Y.C} {n : ℕ}
    (s : Fin n → F'.val.obj (op W)) (ε : Fin n → hi.I.val.obj (op W))
    (hε : ∑ j, idealSection hi _ (ε j) • s j = 0) :
    ∃ S : Sieve W, S ∈ Y.J W ∧ ∀ (W' : Y.C) (g : W' ⟶ W), S g →
      (PresheafOfModules.tensorObj hi.I.val M.val).map g.op
        (∑ j, ε j ⊗ₜ[(baseRing i).obj.obj (op W)] (q.val.app _ (s j) : M.val.obj (op W))) = 0 := by
  classical
  let ηP := (PresheafOfModules.sheafificationAdjunction (R := ringSheaf (baseRing i))
    (𝟙 (ringSheaf (baseRing i)).obj)).unit.app (PresheafOfModules.tensorObj hi.I.val M.val)
  let η'P := (PresheafOfModules.sheafificationAdjunction (R := ringSheaf Y.O)
    (𝟙 (ringSheaf Y.O).obj)).unit.app (PresheafOfModules.tensorObj
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val F'.val)
  let x' : (PresheafOfModules.tensorObj
      ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val F'.val).obj (op W) :=
    ∑ j, (ε j : ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val.obj (op W))
      ⊗ₜ[Y.O.obj.obj (op W)] s j
  let x : (PresheafOfModules.tensorObj hi.I.val M.val).obj (op W) :=
    ∑ j, ε j ⊗ₜ[(baseRing i).obj.obj (op W)] (q.val.app _ (s j) : M.val.obj (op W))
  have hx' : η'P.app (op W) x' = ∑ j, η'P.app (op W)
      ((ε j : ((SheafOfModules.restrictScalars (ringMap i.fSharp)).obj hi.I).val.obj (op W))
        ⊗ₜ[Y.O.obj.obj (op W)] s j) :=
    map_sum (η'P.app (op W)).hom _ _
  have h1 : (multiplicationMap i.fSharp hi.I F' hi.incl).val.app (op W) (η'P.app (op W) x') =
      0 := by
    rw [hx']
    refine (map_sum ((multiplicationMap i.fSharp hi.I F' hi.incl).val.app (op W)).hom _ _).trans
      (Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hε)
    exact multiplicationMap_tmul i.fSharp hi.I F' hi.incl (op W) (ε j) (s j)
  have : Mono ((SheafOfModules.forget (ringSheaf Y.O)).map
      (multiplicationMap i.fSharp hi.I F' hi.incl)) := inferInstance
  have h2 : η'P.app (op W) x' = 0 :=
    PresheafOfModules.injective_of_mono ((SheafOfModules.forget (ringSheaf Y.O)).map
      (multiplicationMap i.fSharp hi.I F' hi.incl)) (op W) (h1.trans (map_zero _).symm)
  have h3 : ηP.app (op W) x = 0 := by
    have h := (congrArg ((reductionTensorMap i.fSharp hi.I F' M q).val.app (op W)) h2).trans
      (map_zero _)
    rw [hx'] at h
    refine Eq.trans ?_ ((map_sum ((reductionTensorMap i.fSharp hi.I F' M q).val.app
      (op W)).hom _ _).symm.trans h)
    refine (map_sum (ηP.app (op W)).hom _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    exact (reductionTensorMap_tmul i.fSharp hi.I F' M q (op W) (ε j) (s j)).symm
  have hmem := Presheaf.equalizerSieve_mem Y.J
    (CategoryTheory.toSheafify Y.J (PresheafOfModules.tensorObj hi.I.val M.val).presheaf) x 0
    (h3.trans (map_zero (ηP.app (op W)).hom).symm)
  refine ⟨_, hmem, fun W' g hg => ?_⟩
  have h : (PresheafOfModules.tensorObj hi.I.val M.val).presheaf.map g.op x =
      (PresheafOfModules.tensorObj hi.I.val M.val).presheaf.map g.op 0 := hg
  exact h.trans (map_zero _)

omit [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Sections of the structure sheaf of the thickening commute. -/
private lemma mul_comm_ringSheaf {U : Y.Cᵒᵖ} (a b : (ringSheaf Y.O).obj.obj U) : a * b = b * a :=
  mul_comm (show Y.O.obj.obj U from a) (show Y.O.obj.obj U from b)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Sections of the structure sheaf of the base, on the site of the thickening, commute. -/
private lemma mul_comm_baseRing {U : Y.Cᵒᵖ} (a b : (ringSheaf (baseRing i)).obj.obj U) :
    a * b = b * a :=
  mul_comm (show (baseRing i).obj.obj U from a) (show (baseRing i).obj.obj U from b)

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **An ideal combination of relations of the reduction is a combination of the lifted
relations.** Let `t` lift the relations `tb` of a presentation of the reduction along
`O' ⟶ i_*O`. If a tuple `e` of sections of the square-zero ideal is `∑_κ ρ_κ y_κ` for relations
`ρ_κ` among the generators of the reduction and sections `y_κ` of the ideal, then the tuple of
sections of `O'` it defines is locally an `O'`-combination of the rows of `t`. -/
theorem relationSpanSieve_incl_mem (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (ringSheaf (baseRing i))) {W : Y.C} {n m k : ℕ}
    (t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W))
    (tb : Fin m → Fin n → (ringSheaf (baseRing i)).obj.obj (op W))
    (ht : ∀ a j, (structureRingMap i).hom.app _ (t a j) = tb a j)
    (sb : Fin n → M.val.obj (op W)) (hC : LocallySpansKernel M sb tb)
    (ρ : Fin k → Fin n → (ringSheaf (baseRing i)).obj.obj (op W))
    (hρ : ∀ κ, combinationValue M (ρ κ) sb = 0) (y : Fin k → hi.I.val.obj (op W))
    (e : Fin n → hi.I.val.obj (op W)) (he : ∀ j, e j = ∑ κ, ρ κ j • y κ) :
    relationSpanSieve (ringSheaf Y.O) t (fun j => idealSection hi _ (e j)) ∈ Y.J W := by
  classical
  have hκ : ∀ κ, relationSpanSieve (ringSheaf (baseRing i)) tb (ρ κ) ∈ Y.J W :=
    fun κ => relationSpanSieve_mem_of_locallySpansKernel hC (hρ κ)
  refine Y.J.superset_covering ?_ (Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem Y.J _ hκ)
  intro W' g hg
  choose μ hμ using (Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ g).mp hg
  refine ⟨fun a => idealSection hi _ (∑ κ, μ κ a • restr hi.I g.op (y κ)), fun j => ?_⟩
  have htg : ∀ a, (structureRingMap i).hom.app (op W') ((ringSheaf Y.O).obj.map g.op (t a j)) =
      (ringSheaf (baseRing i)).obj.map g.op (tb a j) := fun a => by
    rw [← ht a j]
    exact NatTrans.naturality_apply (structureRingMap i).hom g.op (t a j)
  have hI : restr hi.I g.op (e j) = ∑ a, (ringSheaf (baseRing i)).obj.map g.op (tb a j) •
      ∑ κ, μ κ a • restr hi.I g.op (y κ) := by
    unfold restr
    rw [he j, map_sum]
    simp only [hi.I.val.map_smul, ← hμ, Finset.sum_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun κ _ => ?_
    exact (congrArg (fun c => c • restr hi.I g.op (y κ)) (mul_comm_baseRing (μ κ a) _)).trans
      (mul_smul ((ringSheaf (baseRing i)).obj.map g.op (tb a j)) (μ κ a) (restr hi.I g.op (y κ)))
  rw [idealSection_map hi g.op (e j), hI, idealSection_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← htg a]
  exact ((idealSection_smul hi _ _ _).trans (mul_comm_ringSheaf _ _)).symm

/-- **Being locally a combination of finitely many tuples is local on the object.** -/
theorem relationSpanSieve_mem_of_cover {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {n m : ℕ} {U : C} (t : Fin m → Fin n → R.obj.obj (op U))
    (a : Fin n → R.obj.obj (op U)) (S : Sieve U) (hS : S ∈ J U)
    (h : ∀ (V : C) (f : V ⟶ U), S f → relationSpanSieve R (fun j k => R.obj.map f.op (t j k))
      (fun k => R.obj.map f.op (a k)) ∈ J V) :
    relationSpanSieve R t a ∈ J U := by
  refine J.transitive hS _ fun V f hf => J.superset_covering ?_ (h V f hf)
  rintro W g ⟨c, hc⟩
  refine ⟨c, fun k => ?_⟩
  simpa only [op_comp, ringMap_comp_apply] using hc k

/-- A vanishing combination stays vanishing after restricting the sections and coefficients. -/
private lemma combinationValue_restr_eq_zero {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}} (M : SheafOfModules.{w} R) {U V : Cᵒᵖ}
    (g : U ⟶ V) {r : ℕ} {a : Fin r → R.obj.obj U} {s : Fin r → M.val.obj U}
    (h : combinationValue M a s = 0) :
    combinationValue M (fun i => R.obj.map g (a i)) (fun i => restr M g (s i)) = 0 := by
  rw [← restr_combinationValue, h, restr_zero]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A tensor relation among the generators of the reduction with ideal coefficients is locally
a combination of the lifted relations.** If `∑ e_j ⊗ s̄_j = 0` in the presheaf tensor product
`I ⊗_O M` and `(s̄, t̄)` satisfies conditions (B) and (C) for `M`, then the tuple `incl e` of
sections of `O'` is locally an `O'`-combination of the rows of any lift `t` of `t̄`.

The equational criterion `exists_relations_of_sum_tmul_eq_zero` writes `e` through relations among
`s̄` and finitely many further sections `z` of `M`; condition (B) makes each `z` locally a
combination of the `s̄`, which turns those relations into relations among the `s̄` alone, and
`relationSpanSieve_incl_mem` concludes. -/
theorem relationSpanSieve_incl_mem_of_sum_tmul_eq_zero (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (ringSheaf (baseRing i))) {W : Y.C} {n m : ℕ}
    (t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W))
    (tb : Fin m → Fin n → (ringSheaf (baseRing i)).obj.obj (op W))
    (ht : ∀ a j, (structureRingMap i).hom.app _ (t a j) = tb a j)
    (sb : Fin n → M.val.obj (op W)) (hB : LocallySpans M sb) (hC : LocallySpansKernel M sb tb)
    (e : Fin n → hi.I.val.obj (op W))
    (hz : ∑ j, e j ⊗ₜ[(baseRing i).obj.obj (op W)] sb j = 0) :
    relationSpanSieve (ringSheaf Y.O) t (fun j => idealSection hi _ (e j)) ∈ Y.J W := by
  classical
  obtain ⟨r, z, k, α₀, α₀', y, he₀, hα₀', hrel₀⟩ := exists_relations_of_sum_tmul_eq_zero e sb hz
  let α : Fin n → Fin k → (ringSheaf (baseRing i)).obj.obj (op W) := α₀
  let α' : Fin r → Fin k → (ringSheaf (baseRing i)).obj.obj (op W) := α₀'
  have he : ∀ j, e j = ∑ κ, α j κ • y κ := he₀
  have hα' : ∀ l, ∑ κ, α' l κ • y κ = 0 := hα₀'
  have hrel : ∀ κ, ∑ j, α j κ • sb j + ∑ l, α' l κ • z l = 0 := hrel₀
  have hz' : ∀ l, spanSieve M sb (z l) ∈ Y.J W := fun l => by
    simpa only [op_id, restr_id] using hB W (𝟙 W) (z l)
  refine relationSpanSieve_mem_of_cover _ _ _
    (Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem Y.J _ hz') fun W' g hg => ?_
  choose d hd using (Stacks.SheafOfModules.FiniteTypeKernel.iInf_apply _ g).mp hg
  let R' := ringSheaf (baseRing i)
  let b : Fin k → Fin n → R'.obj.obj (op W') := fun κ j =>
    R'.obj.map g.op (α j κ) + ∑ l, R'.obj.map g.op (α' l κ) * d l j
  have hb : ∀ κ, combinationValue M (b κ) (fun j => restr M g.op (sb j)) = 0 := fun κ => by
    have h0 := congrArg (restr M g.op) (hrel κ)
    rw [restr_zero] at h0
    refine Eq.trans ?_ h0
    simp only [b, combinationValue, add_smul, Finset.sum_add_distrib, Finset.sum_smul,
      mul_smul]
    rw [restr, map_add, map_sum, map_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => (M.val.map_smul g.op _ _).symm
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← Finset.smul_sum, M.val.map_smul]
      congr 1
      have := hd l
      simp only [combinationValue] at this
      exact this
  have he' : ∀ j, restr hi.I g.op (e j) = ∑ κ, b κ j • restr hi.I g.op (y κ) := fun j => by
    simp only [b, add_smul, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm (f := fun κ l => _), he j, restr, map_sum]
    have h0 : ∀ l, ∑ κ, R'.obj.map g.op (α' l κ) • d l j • restr hi.I g.op (y κ) = 0 :=
      fun l => by
        have h1 : ∑ κ, R'.obj.map g.op (α' l κ) • d l j • restr hi.I g.op (y κ) =
            d l j • ∑ κ, R'.obj.map g.op (α' l κ) • restr hi.I g.op (y κ) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun κ _ => smul_comm _ _ _
        rw [h1]
        rw [← smul_zero (d l j), ← combinationValue_restr_eq_zero hi.I g.op (hα' l)]
        rfl
    simp only [h0, Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl fun κ _ => hi.I.val.map_smul g.op _ _
  have hmem := relationSpanSieve_incl_mem hi M (fun a j => (ringSheaf Y.O).obj.map g.op (t a j))
    (fun a j => R'.obj.map g.op (tb a j)) (fun a j => by
      rw [← ht a j]
      exact NatTrans.naturality_apply (structureRingMap i).hom g.op (t a j))
    (fun j => restr M g.op (sb j)) (locallySpansKernel_map hC g) b hb
    (fun κ => restr hi.I g.op (y κ)) (fun j => restr hi.I g.op (e j)) he'
  simpa only [idealSection_map] using hmem

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A tuple of sections of `O'` which is a combination of the rows of `t` up to an ideal tuple
whose tensor with the generators of the reduction vanishes is locally a combination of the rows
of `t`. -/
theorem relationSpanSieve_mem_of_eq_add_incl (hi : FirstOrderThickening i)
    (M : SheafOfModules.{w} (ringSheaf (baseRing i))) {W : Y.C} {n m : ℕ}
    (t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W))
    (tb : Fin m → Fin n → (ringSheaf (baseRing i)).obj.obj (op W))
    (ht : ∀ a j, (structureRingMap i).hom.app _ (t a j) = tb a j)
    (sb : Fin n → M.val.obj (op W)) (hB : LocallySpans M sb) (hC : LocallySpansKernel M sb tb)
    (a : Fin n → (ringSheaf Y.O).obj.obj (op W)) (b : Fin m → (ringSheaf Y.O).obj.obj (op W))
    (ε : Fin n → hi.I.val.obj (op W)) (ha : ∀ j, a j = ∑ k, b k * t k j + idealSection hi _ (ε j))
    (hz : ∑ j, ε j ⊗ₜ[(baseRing i).obj.obj (op W)] sb j = 0) :
    relationSpanSieve (ringSheaf Y.O) t a ∈ Y.J W := by
  refine Y.J.superset_covering ?_
    (relationSpanSieve_incl_mem_of_sum_tmul_eq_zero hi M t tb ht sb hB hC ε hz)
  rintro W' g ⟨c, hc⟩
  refine ⟨fun k => (ringSheaf Y.O).obj.map g.op (b k) + c k, fun j => ?_⟩
  rw [ha j, map_add, map_sum, ← hc j, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, add_mul]

section KernelCondition

open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap)

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The lifted data.** `n` sections `s` of `ℱ'` and `m` tuples `t` of sections of `O'` over
`W` such that each `t k` is a relation among the `s`, and such that the images of `s` and `t` in
the reduction satisfy conditions (B) and (C) of
`Stacks.Sheaves.LocalGeneration.IsPresentationData` there. -/
def IsLiftedData {F' : SheafOfModules.{w} (ringSheaf Y.O)}
    {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M) {W : Y.C} {n m : ℕ}
    (s : Fin n → F'.val.obj (op W)) (t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W)) :
    Prop :=
  (∀ k, combinationValue F' (t k) s = 0) ∧
    LocallySpans M (fun j => (q.val.app _ (s j) : M.val.obj (op W))) ∧
    LocallySpansKernel M (fun j => (q.val.app _ (s j) : M.val.obj (op W)))
      (fun k j => (structureRingMap i).hom.app _ (t k j))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The map to the reduction carries a combination of sections to the combination of their
images with the coefficients reduced. -/
lemma app_combinationValue {F' : SheafOfModules.{w} (ringSheaf Y.O)}
    {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M) {W : Y.Cᵒᵖ} {n : ℕ}
    (c : Fin n → (ringSheaf Y.O).obj.obj W) (s : Fin n → F'.val.obj W) :
    (q.val.app W (combinationValue F' c s) : M.val.obj W) =
      combinationValue M (fun j => (structureRingMap i).hom.app W (c j))
        (fun j => (q.val.app W (s j) : M.val.obj W)) := by
  rw [combinationValue, map_sum]
  exact Finset.sum_congr rfl fun j _ => map_smul (q.val.app W).hom (c j) (s j)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The map to the reduction commutes with restriction. -/
lemma app_restr {F' : SheafOfModules.{w} (ringSheaf Y.O)}
    {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M) {U V : Y.Cᵒᵖ}
    (g : U ⟶ V) (x : F'.val.obj U) :
    (q.val.app V (restr F' g x) : M.val.obj V) = restr M g (q.val.app U x) :=
  PresheafOfModules.naturality_apply q.val g x

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Lifted data restricts to lifted data. -/
lemma IsLiftedData.map {F' : SheafOfModules.{w} (ringSheaf Y.O)}
    {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    {q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M} {W W' : Y.C} {n m : ℕ}
    {s : Fin n → F'.val.obj (op W)} {t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W)}
    (h : IsLiftedData q s t) (g : W' ⟶ W) :
    IsLiftedData q (fun j => restr F' g.op (s j))
      (fun k j => (ringSheaf Y.O).obj.map g.op (t k j)) := by
  obtain ⟨hA, hB, hC⟩ := h
  refine ⟨fun k => ?_, ?_, ?_⟩
  · exact combinationValue_restr_eq_zero F' g.op (hA k)
  · simpa only [app_restr] using locallySpans_map hB g
  · have hrw : ∀ k j, (structureRingMap i).hom.app (op W') ((ringSheaf Y.O).obj.map g.op (t k j)) =
        (ringSheaf (baseRing i)).obj.map g.op ((structureRingMap i).hom.app (op W) (t k j)) :=
      fun k j => NatTrans.naturality_apply (structureRingMap i).hom g.op (t k j)
    simpa only [app_restr, hrw] using locallySpansKernel_map hC g

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **Condition (C) for the lifted data, after lifting the coefficients.** If a relation `c`
among the lifted generators differs from `∑ a_k t_k` by a tuple killed by `O' ⟶ i_*O`, that
tuple is `incl ε` with `∑ ε_j s_j = 0`; `idealTensor_sum_tmul_locally_eq_zero` makes
`∑ ε_j ⊗ s̄_j` vanish locally, and `relationSpanSieve_mem_of_eq_add_incl` concludes. -/
theorem relationSpanSieve_mem_of_lift (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (ringSheaf Y.O)} {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M)
    (hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl)) {W : Y.C} {n m : ℕ}
    {s : Fin n → F'.val.obj (op W)} {t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W)}
    (hd : IsLiftedData q s t) (c : Fin n → (ringSheaf Y.O).obj.obj (op W))
    (hc : combinationValue F' c s = 0) (a : Fin m → (ringSheaf Y.O).obj.obj (op W))
    (ha : ∀ j, (structureRingMap i).hom.app _ (c j - ∑ k, a k * t k j) = 0) :
    relationSpanSieve (ringSheaf Y.O) t c ∈ Y.J W := by
  classical
  choose ε hε using fun j => hi.exists_ideal_section (op W) _ (ha j)
  have hε' : ∀ j, c j = ∑ k, a k * t k j + idealSection hi _ (ε j) := fun j => by
    rw [show idealSection hi _ (ε j) = _ from hε j]
    abel
  have hsum : ∑ j, idealSection hi _ (ε j) • s j = 0 := by
    have h1 : ∀ j, idealSection hi _ (ε j) = c j - ∑ k, a k * t k j := fun j => hε j
    simp only [h1, sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum]
    have h2 : ∀ k, ∑ j, t k j • s j = 0 := hd.1
    have h3 : ∑ j, c j • s j = 0 := hc
    simp only [h2, smul_zero, Finset.sum_const_zero, h3, sub_zero]
  obtain ⟨S, hS, hvan⟩ := idealTensor_sum_tmul_locally_eq_zero hi q hmono s ε hsum
  refine relationSpanSieve_mem_of_cover _ _ S hS fun W' g hg => ?_
  obtain ⟨-, hB, hC⟩ := hd.map g
  refine relationSpanSieve_mem_of_eq_add_incl hi M _ _ (fun _ _ => rfl) _ hB hC _
    (fun k => (ringSheaf Y.O).obj.map g.op (a k)) (fun j => restr hi.I g.op (ε j))
    (fun j => ?_) ?_
  · rw [hε' j, map_add, map_sum, idealSection_map]
    simp only [map_mul]
  · have h := (map_sum ((PresheafOfModules.tensorObj hi.I.val M.val).map g.op).hom _ _).symm.trans
      (hvan W' g hg)
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
    rw [app_restr]
    exact (PresheafOfModules.tensorObj_restrictₛₗ_tmul g.op (ε j) _).symm

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The structure map commutes with restriction. -/
lemma structureRingMap_map {U V : Y.Cᵒᵖ} (g : U ⟶ V) (x : (ringSheaf Y.O).obj.obj U) :
    (structureRingMap i).hom.app V ((ringSheaf Y.O).obj.map g x) =
      (ringSheaf (baseRing i)).obj.map g ((structureRingMap i).hom.app U x) :=
  NatTrans.naturality_apply (structureRingMap i).hom g x

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Condition (C) for the lifted data, after expressing the reduced relation.** If the
reduction of a relation `c` is `∑ b̄_k t̄_k`, then lifting the `b̄_k` locally along the locally
surjective `O' ⟶ i_*O` puts `c` in the situation of `relationSpanSieve_mem_of_lift`. -/
theorem relationSpanSieve_mem_of_reduced_combination (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (ringSheaf Y.O)} {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M)
    (hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl)) {W : Y.C} {n m : ℕ}
    {s : Fin n → F'.val.obj (op W)} {t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W)}
    (hd : IsLiftedData q s t) (c : Fin n → (ringSheaf Y.O).obj.obj (op W))
    (hc : combinationValue F' c s = 0)
    (ab : Fin m → (ringSheaf (baseRing i)).obj.obj (op W))
    (hab : ∀ j, ∑ k, ab k * (structureRingMap i).hom.app _ (t k j) =
      (structureRingMap i).hom.app _ (c j)) :
    relationSpanSieve (ringSheaf Y.O) t c ∈ Y.J W := by
  obtain ⟨S, hS, hlift⟩ := exists_cover_lift_structure_sections hi ab
  refine relationSpanSieve_mem_of_cover _ _ S hS fun W' g hg => ?_
  obtain ⟨a, ha⟩ := hlift W' g hg
  refine relationSpanSieve_mem_of_lift hi q hmono (hd.map g) _ ?_ a fun j => ?_
  · exact combinationValue_restr_eq_zero F' g.op hc
  · rw [map_sub, map_sum, structureRingMap_map, ← hab j, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, ha k, structureRingMap_map]

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Condition (C) for the lifted data at its own object.** The reduction of a relation among
the lifted generators is a relation among the generators of the reduction, hence by condition
(C) there locally a combination of the reduced relations. -/
theorem relationSpanSieve_mem_of_isLiftedData (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (ringSheaf Y.O)} {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M)
    (hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl)) {W : Y.C} {n m : ℕ}
    {s : Fin n → F'.val.obj (op W)} {t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W)}
    (hd : IsLiftedData q s t) (c : Fin n → (ringSheaf Y.O).obj.obj (op W))
    (hc : combinationValue F' c s = 0) :
    relationSpanSieve (ringSheaf Y.O) t c ∈ Y.J W := by
  have hcb := (app_combinationValue q c s).symm.trans
    ((congrArg (q.val.app (op W)) hc).trans (map_zero (q.val.app (op W)).hom))
  refine relationSpanSieve_mem_of_cover _ _ _
    (relationSpanSieve_mem_of_locallySpansKernel hd.2.2 hcb) fun W' g hg => ?_
  obtain ⟨ab, hab⟩ := hg
  refine relationSpanSieve_mem_of_reduced_combination hi q hmono (hd.map g) _ ?_ ab fun j => ?_
  · exact combinationValue_restr_eq_zero F' g.op hc
  · simpa only [structureRingMap_map] using hab j

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Condition (C) for the lifted data.** If the action of the square-zero ideal on `ℱ'` is
injective, every relation among lifted generators is locally a combination of the lifted
relations. -/
theorem locallySpansKernel_of_isLiftedData (hi : FirstOrderThickening i)
    {F' : SheafOfModules.{w} (ringSheaf Y.O)} {M : SheafOfModules.{w} (ringSheaf (baseRing i))}
    (q : F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj M)
    (hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl)) {W : Y.C} {n m : ℕ}
    {s : Fin n → F'.val.obj (op W)} {t : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W)}
    (hd : IsLiftedData q s t) : LocallySpansKernel F' s t := fun _ g c hc =>
  relationSpanSieve_mem_of_isLiftedData hi q hmono (hd.map g) c hc

end KernelCondition

section Lifting

open Stacks.SheafOfModules.FlatSquareZero (ringMap multiplicationMap)

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- `i^*ℱ'` read on the site of the thickening, as a module over `i_*O`: the target of the unit
`ℱ' ⟶ i_*i^*ℱ'` before its scalars are restricted along `i^♯`. -/
noncomputable abbrev reductionModule (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) :
    SheafOfModules.{w} (ringSheaf (baseRing i)) :=
  (pushforwardModuleFunctor i.toToposHom (ringSheaf X.O)).obj
    (i.toRingedToposModulesHom.pullbackModules.obj F')

/-- The unit `ℱ' ⟶ i_*i^*ℱ'`, with target read as `reductionModule`. -/
noncomputable abbrev reductionUnit (i : RingedToposHom X Y)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) :
    F' ⟶ (SheafOfModules.restrictScalars (ringMap i.fSharp)).obj (reductionModule i F') :=
  i.pullbackAdjPushforwardModulesViaComparison.unit.app F'

/-- **Generators of the reduction lift to generators modulo the ideal product.** If the images
of `s` generate `i_*i^*ℱ'` locally, then `s` generates `ℱ'` locally modulo `I·ℱ'`: the
coefficients of a local combination in the reduction lift locally along `O' ⟶ i_*O`, and the
difference dies in the reduction, hence lies in `I·ℱ'`. -/
theorem locallySpansModIdealProduct_of_locallySpans (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O)) {V : Y.C} {n : ℕ} (s : Fin n → F'.val.obj (op V))
    (hB : LocallySpans (reductionModule i F')
      (fun j => ((reductionUnit i F').val.app _ (s j) : (reductionModule i F').val.obj (op V)))) :
    LocallySpansModIdealProduct hi F' s := by
  intro W h y
  refine Y.J.transitive (hB W h ((reductionUnit i F').val.app _ y)) _ fun W₁ k₁ hk₁ => ?_
  obtain ⟨ab, hab⟩ := hk₁
  obtain ⟨S₂, hS₂, hl⟩ := exists_cover_lift_structure_sections hi ab
  refine Y.J.superset_covering ?_ hS₂
  intro W₂ k₂ hk₂
  obtain ⟨a, ha⟩ := hl W₂ k₂ hk₂
  refine ⟨a, mem_idealProductSubmodule_of_unit_eq_zero hi F' _ _ ?_⟩
  have e1 := congrArg (restr (reductionModule i F') k₂.op) hab
  rw [restr_combinationValue] at e1
  change ((reductionUnit i F').val.app _ (restr F' (k₂ ≫ k₁).op y -
    combinationValue F' a (fun j => restr F' ((k₂ ≫ k₁) ≫ h).op (s j))) :
      (reductionModule i F').val.obj (op W₂)) = 0
  rw [show restr F' (k₂ ≫ k₁).op y = restr F' k₂.op (restr F' k₁.op y) by
    rw [restr_restr, op_comp]]
  have key : ((reductionUnit i F').val.app _ (restr F' k₂.op (restr F' k₁.op y)) :
      (reductionModule i F').val.obj (op W₂)) = (reductionUnit i F').val.app _
        (combinationValue F' a (fun j => restr F' ((k₂ ≫ k₁) ≫ h).op (s j))) := by
    rw [app_combinationValue, app_restr, app_restr, ← e1]
    congr 1
    · funext j
      exact (ha j).symm
    · funext j
      have hr : ∀ x : (reductionModule i F').val.obj (op V),
          restr _ (k₁.op ≫ k₂.op) (restr _ h.op x) = restr _ ((k₂ ≫ k₁) ≫ h).op x := fun x => by
        rw [restr_restr, op_comp, op_comp]
      rw [app_restr, restr_restr]
      exact hr _
  rw [map_sub, key, sub_self]

/-- **A presentation of the reduction lifts, locally, to a presentation of `ℱ'`.** If the action
of the square-zero ideal on `ℱ'` is injective, then over every object carrying presentation data
for `i^*ℱ'` there is a covering on whose members `ℱ'` carries presentation data. -/
theorem inhabitedSieve_mem_of_isPresentationData_reduction (hi : FirstOrderThickening i)
    (F' : SheafOfModules.{w} (ringSheaf Y.O))
    (hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl)) {V : Y.C} {n m : ℕ}
    (sb : Fin n → (reductionModule i F').val.obj (op V))
    (tb : Fin m → Fin n → (ringSheaf (baseRing i)).obj.obj (op V))
    (hd : IsPresentationData (reductionModule i F') sb tb) :
    Stacks.Topos.inhabitedSieve Y.J (fun q : ℕ × ℕ => presDataSheaf F' q.1 q.2) V ∈ Y.J V := by
  classical
  let M := reductionModule i F'
  let q := reductionUnit i F'
  obtain ⟨S₁, hS₁, h₁⟩ := exists_cover_lift_unit_sections hi F' sb
  refine Y.J.transitive hS₁ _ fun W₁ g₁ hg₁ => ?_
  obtain ⟨s, hs⟩ := h₁ W₁ g₁ hg₁
  obtain ⟨S₂, hS₂, h₂⟩ := exists_cover_lift_structure_sections hi
    (fun kj : Fin m × Fin n => (ringSheaf (baseRing i)).obj.map g₁.op (tb kj.1 kj.2))
  refine Y.J.transitive hS₂ _ fun W₂ g₂ hg₂ => ?_
  obtain ⟨t₀, ht₀⟩ := h₂ W₂ g₂ hg₂
  let s₂ : Fin n → F'.val.obj (op W₂) := fun j => restr F' g₂.op (s j)
  have hs₂ : ∀ j, (q.val.app _ (s₂ j) : M.val.obj (op W₂)) = restr M (g₂ ≫ g₁).op (sb j) :=
    fun j => (app_restr q g₂.op (s j)).trans ((congrArg (restr M g₂.op) (hs j)).trans
      ((restr_restr M _ _ _).trans (by rw [op_comp])))
  let t₀' : Fin m → Fin n → (ringSheaf Y.O).obj.obj (op W₂) := fun k j => t₀ (k, j)
  have ht₀' : ∀ k j, (structureRingMap i).hom.app _ (t₀' k j) =
      (ringSheaf (baseRing i)).obj.map (g₂ ≫ g₁).op (tb k j) := fun k j => by
    rw [op_comp, ringMap_comp_apply]
    exact ht₀ (k, j)
  have hB₂ : LocallySpans M (fun j => (q.val.app _ (s₂ j) : M.val.obj (op W₂))) := by
    simpa only [hs₂] using locallySpans_map hd.2.1 _
  have hrel : ∀ k, (i.pullbackAdjPushforwardModulesViaComparison.unit.app F').val.app (op W₂)
      (combinationValue F' (t₀' k) s₂) = 0 := fun k => by
    change (q.val.app _ (combinationValue F' (t₀' k) s₂) : M.val.obj (op W₂)) = 0
    rw [app_combinationValue]
    simp only [ht₀', hs₂]
    rw [← restr_combinationValue, hd.1 k, restr_zero]
    rfl
  obtain ⟨S₃, hS₃, h₃⟩ := exists_cover_corrected_relations_and_locallySpans hi F' s₂ t₀'
    (locallySpansModIdealProduct_of_locallySpans hi F' s₂ hB₂) hrel
  refine Y.J.superset_covering ?_ hS₃
  intro W₃ g₃ hg₃
  obtain ⟨t', ht'0, ht', hB'⟩ := h₃ W₃ g₃ hg₃
  have hs₃ : ∀ j, (q.val.app _ (restr F' g₃.op (s₂ j)) : M.val.obj (op W₃)) =
      restr M (g₃ ≫ g₂ ≫ g₁).op (sb j) := fun j => by
    rw [app_restr, hs₂, restr_restr, ← op_comp]
  have htt : ∀ k j, (structureRingMap i).hom.app _ (t' k j) =
      (ringSheaf (baseRing i)).obj.map (g₃ ≫ g₂ ≫ g₁).op (tb k j) := fun k j => by
    rw [ht'0, structureRingMap_map, ht₀', ← ringMap_comp_apply, ← op_comp]
  have hdm := isPresentationData_map hd (g₃ ≫ g₂ ≫ g₁)
  have hlift : IsLiftedData q (fun j => restr F' g₃.op (s₂ j)) t' := by
    refine ⟨ht', ?_⟩
    simpa only [hs₃, htt] using hdm.2
  exact ⟨(n, m), ⟨presDataMk F' ⟨hlift.1, hB', locallySpansKernel_of_isLiftedData hi q hmono
    hlift⟩⟩⟩

end Lifting

end IdealCombination

section Transport

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- **Stacks 03DM along the thickening.** The morphism of ringed topoi
`(Sh(C), O) ⟶ (Sh(D), i_*O)` with the underlying morphism of topoi of a first order thickening
`i` and the identity structure map is an equivalence of ringed topoi, so the direct image of an
`O`-module of finite presentation is an `i_*O`-module of finite presentation. -/
theorem isFinitePresentation_pushforwardModules_of_isFinitePresentation
    (hi : FirstOrderThickening i) (F : SheafOfModules.{w} (ringSheaf X.O))
    (hF : F.IsFinitePresentation) :
    ((AlgebraicGeometry.RingedToposHom.pushforwardModules
      (reshapeHom i (baseRing i) (𝟙 _))).obj F).IsFinitePresentation := by
  let g : RingedToposHom X (reshape Y (baseRing i)) := reshapeHom i (baseRing i) (𝟙 _)
  have : g.toToposHom.pushforward.IsEquivalence := hi.equiv
  have : IsIso g.fSharp := (inferInstance : IsIso (𝟙 (baseRing i)))
  have := g.isIso_pullbackAdjPushforwardModules_counit
  refine (AlgebraicGeometry.RingedToposHom.isFinitePresentation_iff_pullbackModules g _).mpr ?_
  exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
    (asIso (g.pullbackAdjPushforwardModules.counit.app F)).symm hF

/-- `isFinitePresentation_pushforwardModules_of_isFinitePresentation`, with the direct image
read through the Stacks 03D1 direct image of sheaves of modules. -/
theorem isFinitePresentation_reduction_of_isFinitePresentation
    (hi : FirstOrderThickening i) (F : SheafOfModules.{w} (ringSheaf X.O))
    (hF : F.IsFinitePresentation) :
    ((pushforwardModuleFunctor i.toToposHom (ringSheaf X.O)).obj F :
      SheafOfModules.{w} (ringSheaf (baseRing i))).IsFinitePresentation :=
  Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso (Iso.refl _)
    (isFinitePresentation_pushforwardModules_of_isFinitePresentation hi F hF)

end Transport

section Main

open Stacks.SheafOfModules.FlatSquareZero (multiplicationMap)

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X'.C, HasWeakSheafify (X'.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X'.C, (X'.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}] in
/-- **Stacks 08VU.** Let `(f, f')` be a morphism of first order thickenings of ringed topoi as
in Situation 08M7, let `ℱ'` be an `O'`-module and set `ℱ = i^*ℱ'`. Assume that `ℱ'` is flat
over `O_{ℬ'}` and that `(f, f')` is a strict morphism of thickenings. Then `ℱ'` is an
`O'`-module of finite presentation if and only if `ℱ` is an `O`-module of finite
presentation.

Flatness of `ℱ'` over `O_{ℬ'}` is flatness of `ℱ'` read as an `(f')^{-1}O_{ℬ'}`-module, as in
`Deformation.ToposThickening.HasFlatLift`, and `ℱ = i^*ℱ'` is the pullback of Stacks 03D6.

The direction (1) ⇒ (2) is Stacks 03DO and uses none of the hypotheses. For (2) ⇒ (1), Stacks
03DM moves `ℱ` to the site of the thickening, where each local presentation of it lifts to one of
`ℱ'`; flatness and strictness enter only through the injectivity of the action of `I` on `ℱ'`
(`Deformation.ToposThickening.isIdealActionMono`). See the module docstring. -/
@[stacks 08VU]
theorem isFinitePresentation_iff_pullbackModules_of_isFlat
    (i : RingedToposHom X X') (t : RingedToposHom S S') (f : RingedToposHom X S)
    (f' : RingedToposHom X' S') (hi : FirstOrderThickening i) (ht : FirstOrderThickening t)
    (comm : f'.comp i = t.comp f) (F' : SheafOfModules.{w} (ringSheaf X'.O))
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose X'.J (forget₂ CommRingCat.{w} RingCat.{w})).map
          f'.fSharpInverseImage)).obj F'))
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings i t f f' hi ht comm).IsStrict) :
    F'.IsFinitePresentation ↔
      (i.toRingedToposModulesHom.pullbackModules.obj F').IsFinitePresentation := by
  refine ⟨fun hF' => ?_, fun hF => ?_⟩
  · have := hF'
    exact Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso
      ((AlgebraicGeometry.RingedToposHom.pullbackModulesViaComparisonIso i).app F')
      (Stacks.Sheaves.FinitePresentation.isFinitePresentation_pullbackModules i.toModulesHom F')
  · let : HasSheafify X.J AddCommGrpCat.{w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    let : HasSheafify X'.J AddCommGrpCat.{w} :=
      AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
    have hmono : Mono (multiplicationMap i.fSharp hi.I F' hi.incl) :=
      isIdealActionMono i t f f' hi ht comm F' hstrict hflat
    have hM := isFinitePresentation_reduction_of_isFinitePresentation hi _ hF
    obtain ⟨σ, hσ⟩ := hM.exists_quasicoherentData
    refine Stacks.SheafOfModules.isFinitePresentation_of_locally_isPresentationData F'
      fun U => ?_
    have hU : Stacks.Topos.inhabitedSieve X'.J (fun q : ℕ × ℕ => presDataSheaf F' q.1 q.2) U ∈
        X'.J U := by
      refine X'.J.transitive (σ.coversTop U) _ fun V g hg => ?_
      obtain ⟨k, ⟨h⟩⟩ := hg
      have := hσ.isFinite_presentation k
      obtain ⟨n, m, sb, tb, hd⟩ :=
        exists_isPresentationData_of_presentation _ (σ.X k) (σ.presentation k)
      refine X'.J.superset_covering (fun W g' hg' => hg') ?_
      exact inhabitedSieve_mem_of_isPresentationData_reduction hi F' hmono _ _
        (isPresentationData_map hd h)
    refine ⟨_, hU, fun V g hg => ?_⟩
    obtain ⟨q, ⟨p⟩⟩ := hg
    exact ⟨q.1, q.2, _, _, p.property⟩

end Main

end Deformation.ToposThickening

end

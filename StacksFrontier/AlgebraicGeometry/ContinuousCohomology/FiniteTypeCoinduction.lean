module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoinducedEffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange

/-!
# Coinduction of finite `Λ`-modules with a continuous action, and Frobenius reciprocity

Let `G` be a compact topological group, `H` an open subgroup and `Λ` a ring. For a finite
`Λ`-module `M` with a continuous `G`-action the coinduced module `Coind_H M` is the module of all
functions `G ⧸ H → M`, with `(g • f)(x) = g • f(g⁻¹ • x)`
(`Stacks.ContinuousCohomology.coind`); it is again finite because `G ⧸ H` is finite. For trivial
`M = N` it is the module `N[G/H]`.

Frobenius reciprocity: let `φ : G' → G` be a continuous homomorphism with image `H`. Maps of
`G`-modules `Q ⟶ Coind_H M` are the same as maps of `G'`-modules `res Q ⟶ res M`, by composing
with evaluation at the trivial coset.

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoind` — `M ↦ Coind_H M` on finite modules.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoindUnit` — `M ⟶ Coind_H M`, constants.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoindEval` — evaluation at the trivial coset,
  `res (Coind_H M) ⟶ res M`, for `φ` with image in `H`.

## Main results

* `Stacks.GroupCohomology.bijective_finiteTypeContinuousModuleCoindEval_comp` — Frobenius
  reciprocity, for `φ` with image `H`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (H : OpenSubgroup G)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The action of a product on an element of a finite module with a continuous action. -/
lemma finiteTypeContinuousModule_ρ_mul_apply (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (g h : G) (m : M.obj.obj.obj.V) :
    (M.obj.obj.obj.ρ (g * h)).asHom.hom m =
      (M.obj.obj.obj.ρ g).asHom.hom ((M.obj.obj.obj.ρ h).asHom.hom m) := by
  rw [map_mul]
  rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The unit acts trivially on a finite module with a continuous action. -/
lemma finiteTypeContinuousModule_ρ_one_apply (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (m : M.obj.obj.obj.V) : (M.obj.obj.obj.ρ 1).asHom.hom m = m := by
  rw [map_one]
  rfl

/-- **Coinduction `M ↦ Coind_H M` of finite `R`-modules with a continuous `G`-action**, for an
open subgroup `H` of a compact group `G`: the module of functions `G ⧸ H → M` with
`(g • f)(x) = g • f(g⁻¹ • x)`. -/
def finiteTypeContinuousModuleCoind :
    FiniteTypeContinuousModule.{u, v, max u v} R G ⥤
      FiniteTypeContinuousModule.{u, v, max u v} R G :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ coind.{u, v, 0} R H) fun M ↦ by
    have : Module.Finite R M.obj.obj.obj.V := M.property
    change Module.Finite R (G ⧸ (H : Subgroup G) → M.obj.obj.obj.V)
    infer_instance

/-- The underlying module of `Coind_H M` is the module of functions `G ⧸ H → M`. -/
lemma finiteTypeContinuousModuleCoind_obj_V (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    ((finiteTypeContinuousModuleCoind R H).obj M).obj.obj.obj.V =
      ModuleCat.of R (G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :=
  rfl

/-- The action on `Coind_H M`: `(g • f)(x) = g • f(g⁻¹ • x)`. -/
lemma finiteTypeContinuousModuleCoind_ρ_apply
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) (g : G)
    (f : G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) (x : G ⧸ (H : Subgroup G)) :
    (((finiteTypeContinuousModuleCoind R H).obj M).obj.obj.obj.ρ g).asHom.hom f x =
      (M.obj.obj.obj.ρ g).asHom.hom (f (g⁻¹ • x)) :=
  rfl

/-- Coinduction on a map composes with it. -/
lemma finiteTypeContinuousModuleCoind_map_apply
    {M N : FiniteTypeContinuousModule.{u, v, max u v} R G} (a : M ⟶ N)
    (f : G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) (x : G ⧸ (H : Subgroup G)) :
    ((finiteTypeContinuousModuleCoind R H).map a).hom.hom.hom.hom f x =
      a.hom.hom.hom.hom (f x) :=
  rfl

/-- **The embedding `M ⟶ Coind_H M` as the constant functions.** -/
def finiteTypeContinuousModuleCoindUnit (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    M ⟶ (finiteTypeContinuousModuleCoind R H).obj M :=
  ObjectProperty.homMk (coindUnit.{u, v, 0} R H M.obj)

/-- The embedding `M ⟶ Coind_H M` sends `m` to the constant function with value `m`. -/
lemma finiteTypeContinuousModuleCoindUnit_apply
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) (m : M.obj.obj.obj.V)
    (x : G ⧸ (H : Subgroup G)) :
    (finiteTypeContinuousModuleCoindUnit R H M).hom.hom.hom.hom m x = m :=
  rfl

/-- The embedding `M ⟶ Coind_H M` is natural in `M`. -/
lemma finiteTypeContinuousModuleCoindUnit_naturality
    {M N : FiniteTypeContinuousModule.{u, v, max u v} R G} (a : M ⟶ N) :
    finiteTypeContinuousModuleCoindUnit R H M ≫
        (finiteTypeContinuousModuleCoind R H).map a =
      a ≫ finiteTypeContinuousModuleCoindUnit R H N := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

section Eval

variable {R H} {G' : Type v} [Group G'] [TopologicalSpace G'] (φ : G' →ₜ* G)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- An element of `H` fixes the trivial coset. -/
lemma smul_mk_one_eq_of_mem {h : G} (hh : h ∈ H) :
    h • ((1 : G) : G ⧸ (H : Subgroup G)) = ((1 : G) : G ⧸ (H : Subgroup G)) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
  exact H.inv_mem hh

variable (R H)

/-- **Evaluation at the trivial coset**, `res_φ (Coind_H M) ⟶ res_φ M`, `f ↦ f(H)`, for a
continuous homomorphism `φ : G' → G` with image in `H`. -/
def finiteTypeContinuousModuleCoindEval (hφ : ∀ g, φ g ∈ H)
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    (finiteTypeContinuousModuleRes R φ).obj ((finiteTypeContinuousModuleCoind R H).obj M) ⟶
      (finiteTypeContinuousModuleRes R φ).obj M :=
  ObjectProperty.homMk ((homEquiv R G' _ _).symm
    ⟨LinearMap.proj ((1 : G) : G ⧸ (H : Subgroup G)), fun g f ↦ by
      change (M.obj.obj.obj.ρ (φ g)).asHom.hom (f ((φ g)⁻¹ • ((1 : G) : G ⧸ (H : Subgroup G)))) =
        (M.obj.obj.obj.ρ (φ g)).asHom.hom (f ((1 : G) : G ⧸ (H : Subgroup G)))
      rw [smul_mk_one_eq_of_mem (H.inv_mem (hφ g))]⟩)

/-- Evaluation at the trivial coset sends `f` to `f(H)`. -/
lemma finiteTypeContinuousModuleCoindEval_apply (hφ : ∀ g, φ g ∈ H)
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G)
    (f : G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :
    (finiteTypeContinuousModuleCoindEval R H φ hφ M).hom.hom.hom.hom f =
      f ((1 : G) : G ⧸ (H : Subgroup G)) :=
  rfl

/-- Evaluation at the trivial coset is natural in `M`. -/
lemma finiteTypeContinuousModuleCoindEval_naturality (hφ : ∀ g, φ g ∈ H)
    {M N : FiniteTypeContinuousModule.{u, v, max u v} R G} (a : M ⟶ N) :
    (finiteTypeContinuousModuleRes R φ).map ((finiteTypeContinuousModuleCoind R H).map a) ≫
        finiteTypeContinuousModuleCoindEval R H φ hφ N =
      finiteTypeContinuousModuleCoindEval R H φ hφ M ≫
        (finiteTypeContinuousModuleRes R φ).map a := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- Evaluating a constant function gives back its value. -/
lemma finiteTypeContinuousModuleCoindUnit_comp_eval (hφ : ∀ g, φ g ∈ H)
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    (finiteTypeContinuousModuleRes R φ).map (finiteTypeContinuousModuleCoindUnit R H M) ≫
        finiteTypeContinuousModuleCoindEval R H φ hφ M = 𝟙 _ := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- The values of an equivariant map into `Coind_H M` are determined by evaluation at the
trivial coset: `a(q)(gH) = g • a(g⁻¹ • q)(H)`. -/
lemma finiteTypeContinuousModuleCoind_hom_apply_mk
    {Q M : FiniteTypeContinuousModule.{u, v, max u v} R G}
    (a : Q ⟶ (finiteTypeContinuousModuleCoind R H).obj M) (q : Q.obj.obj.obj.V) (g : G) :
    a.hom.hom.hom.hom q (g : G ⧸ (H : Subgroup G)) =
      (M.obj.obj.obj.ρ g).asHom.hom
        (a.hom.hom.hom.hom ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q)
          ((1 : G) : G ⧸ (H : Subgroup G))) := by
  have h := congrFun (ConcreteCategory.congr_hom (a.hom.hom.hom.comm g⁻¹) q)
    ((1 : G) : G ⧸ (H : Subgroup G))
  change a.hom.hom.hom.hom ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q) ((1 : G) : G ⧸ (H : Subgroup G)) =
    (M.obj.obj.obj.ρ g⁻¹).asHom.hom
      (a.hom.hom.hom.hom q (g⁻¹⁻¹ • ((1 : G) : G ⧸ (H : Subgroup G)))) at h
  rw [h, inv_inv, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one,
    ← finiteTypeContinuousModule_ρ_mul_apply, mul_inv_cancel,
    finiteTypeContinuousModule_ρ_one_apply]

/-- **Frobenius reciprocity.** For a continuous homomorphism `φ : G' → G` whose image is the
open subgroup `H`, composing with evaluation at the trivial coset is a bijection from the maps of
`G`-modules `Q ⟶ Coind_H M` onto the maps of `G'`-modules `res Q ⟶ res M`. -/
theorem bijective_finiteTypeContinuousModuleCoindEval_comp (hφ : ∀ g, φ g ∈ H)
    (hH : ∀ h ∈ H, ∃ g, φ g = h) (Q M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    Function.Bijective (fun a : Q ⟶ (finiteTypeContinuousModuleCoind R H).obj M ↦
      (finiteTypeContinuousModuleRes R φ).map a ≫
        finiteTypeContinuousModuleCoindEval R H φ hφ M) := by
  constructor
  · intro a b hab
    have h : ∀ q, a.hom.hom.hom.hom q ((1 : G) : G ⧸ (H : Subgroup G)) =
        b.hom.hom.hom.hom q ((1 : G) : G ⧸ (H : Subgroup G)) := fun q ↦
      ConcreteCategory.congr_hom (congrArg (fun c ↦ c.hom.hom.hom.hom) hab) q
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro q
    funext x
    induction x using QuotientGroup.induction_on with
    | H g => rw [finiteTypeContinuousModuleCoind_hom_apply_mk R H a,
        finiteTypeContinuousModuleCoind_hom_apply_mk R H b, h]
  · intro c
    obtain ⟨cL, hcL⟩ : ∃ cL : Q.obj.obj.obj.V →ₗ[R] M.obj.obj.obj.V,
        ∀ q, c.hom.hom.hom.hom q = cL q := ⟨c.hom.hom.hom.hom.hom, fun _ ↦ rfl⟩
    have hc : ∀ h ∈ H, ∀ q,
        cL ((Q.obj.obj.obj.ρ h).asHom.hom q) = (M.obj.obj.obj.ρ h).asHom.hom (cL q) := by
      intro h hh q
      obtain ⟨g, rfl⟩ := hH h hh
      exact (hcL _).symm.trans ((ConcreteCategory.congr_hom (c.hom.hom.hom.comm g) q).trans
        (congrArg (M.obj.obj.obj.ρ (φ g)).asHom.hom (hcL q)))
    have hwd : ∀ q (g g' : G), g⁻¹ * g' ∈ H →
        (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q)) =
          (M.obj.obj.obj.ρ g').asHom.hom (cL ((Q.obj.obj.obj.ρ g'⁻¹).asHom.hom q)) := by
      intro q g g' hm
      obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, g' = g * h := ⟨g⁻¹ * g', hm, by group⟩
      rw [mul_inv_rev, finiteTypeContinuousModule_ρ_mul_apply R Q, hc h⁻¹ (H.inv_mem hh),
        finiteTypeContinuousModule_ρ_mul_apply R M, ← finiteTypeContinuousModule_ρ_mul_apply R M h,
        mul_inv_cancel, finiteTypeContinuousModule_ρ_one_apply]
    let F : Q.obj.obj.obj.V → G ⧸ (H : Subgroup G) → M.obj.obj.obj.V := fun q ↦
      Quotient.lift (s := QuotientGroup.leftRel (H : Subgroup G))
        (fun g ↦ (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q)))
        (fun g g' hgg' ↦ hwd q g g' (QuotientGroup.leftRel_apply.mp hgg'))
    let L : Q.obj.obj.obj.V →ₗ[R] (G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :=
      { toFun := F
        map_add' := fun q q' ↦ by
          funext x; induction x using QuotientGroup.induction_on with
          | H g =>
            show (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom (q + q'))) =
              (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q)) +
                (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q'))
            rw [map_add, map_add, map_add]
        map_smul' := fun r q ↦ by
          funext x; induction x using QuotientGroup.induction_on with
          | H g =>
            show (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom (r • q))) =
              r • (M.obj.obj.obj.ρ g).asHom.hom (cL ((Q.obj.obj.obj.ρ g⁻¹).asHom.hom q))
            rw [map_smul, map_smul, map_smul] }
    let a : Q ⟶ (finiteTypeContinuousModuleCoind R H).obj M :=
      ObjectProperty.homMk ((homEquiv R G _ _).symm ⟨L, fun g q ↦ by
        funext x
        induction x using QuotientGroup.induction_on with
        | H g' =>
          show (M.obj.obj.obj.ρ g').asHom.hom
              (cL ((Q.obj.obj.obj.ρ g'⁻¹).asHom.hom ((Q.obj.obj.obj.ρ g).asHom.hom q))) =
            (M.obj.obj.obj.ρ g).asHom.hom ((M.obj.obj.obj.ρ (g⁻¹ * g')).asHom.hom
              (cL ((Q.obj.obj.obj.ρ (g⁻¹ * g')⁻¹).asHom.hom q)))
          rw [mul_inv_rev, inv_inv, finiteTypeContinuousModule_ρ_mul_apply R Q,
            ← finiteTypeContinuousModule_ρ_mul_apply R M, mul_inv_cancel_left]⟩)
    refine ⟨a, ?_⟩
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro q
    refine Eq.trans ?_ (hcL q).symm
    show (M.obj.obj.obj.ρ 1).asHom.hom (cL ((Q.obj.obj.obj.ρ 1⁻¹).asHom.hom q)) = cL q
    exact (congrArg
      (fun t : G ↦ (M.obj.obj.obj.ρ 1).asHom.hom (cL ((Q.obj.obj.obj.ρ t).asHom.hom q)))
      inv_one).trans ((finiteTypeContinuousModule_ρ_one_apply R M _).trans
        (congrArg cL (finiteTypeContinuousModule_ρ_one_apply R Q q)))

end Eval

end Stacks.GroupCohomology

end

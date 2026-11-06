module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoinvariantsCountOfCyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteTypeContinuousModuleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import Mathlib.Topology.Algebra.OpenSubgroup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ContinuousModuleScalarAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ContinuousModuleQuotientDescent

/-!
# Permutation modules of finite continuous `G`-sets

For a topological group `G`, a finite set `Y` with a continuous action of `G` and a finite set `A`,
the functions `Y → A → ℤ/m` with `G` acting through `Y` form a finite `ℤ/m`-module with a
continuous `G`-action (`Stacks.EtaleCohomology.permModule`). For the geometric fibre `Y` of a
connected Galois cover of a curve this is the module whose lisse sheaf is the direct image of the
constant sheaf on the cover, which is what the counting argument of [Stacks, Tag 03VK] is run on.

This file builds the morphisms of the counting argument: the augmentation to `ℤ/m`, the map `ψ_a`
sending the basis function of a base point to an element `a` fixed by its stabilizer, and the deck
transformations `R_n` of a Galois `G`-set; and it proves the count: for an additive functor `T`
which preserves surjections and has at most as many elements on the permutation module of `Y` as
on `ℤ/m`, the latter value being `ℤ/m`, `#T(M) ≤ #M_G` for every `M` on which the stabilizers of
`Y` act trivially.

## Main definitions

* `Stacks.EtaleCohomology.permModule`, and `Stacks.EtaleCohomology.trivialContinuousModule`
  (`ℤ/m` with the trivial action, the target of the augmentation).
* `Stacks.EtaleCohomology.permPullback` and `Stacks.EtaleCohomology.permEval`.

## Main results

* `Stacks.EtaleCohomology.finite_and_natCard_obj_le_natCard_coinvariants_of_perm`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

open scoped Stacks.DiscreteModuleTopology

section Perm

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ)

/-- A morphism of finite `ℤ/m`-modules with continuous `G`-action from an equivariant linear
map. -/
def finiteTypeContinuousModuleHomMk
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G}
    (f : P.obj.obj.obj.V →ₗ[ZMod m] Q.obj.obj.obj.V)
    (hf : ∀ (g : G) (x : P.obj.obj.obj.V),
      f ((P.obj.obj.obj.ρ g).asHom.hom x) = (Q.obj.obj.obj.ρ g).asHom.hom (f x)) : P ⟶ Q :=
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom f
      comm := fun g => by
        ext x
        exact hf g x }))

omit [IsTopologicalGroup G] in
/-- The underlying map of `finiteTypeContinuousModuleHomMk m f hf` is `f`. -/
theorem finiteTypeContinuousModuleHomMk_apply
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G}
    (f : P.obj.obj.obj.V →ₗ[ZMod m] Q.obj.obj.obj.V) (hf) (x : P.obj.obj.obj.V) :
    (finiteTypeContinuousModuleHomMk m f hf).hom.hom.hom.hom.hom x = f x :=
  rfl

omit [IsTopologicalGroup G] in
/-- Morphisms of finite continuous modules agree when their underlying maps do. -/
theorem finiteTypeContinuousModule_hom_ext
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G} {f g : P ⟶ Q}
    (h : ∀ x, f.hom.hom.hom.hom.hom x = g.hom.hom.hom.hom.hom x) : f = g := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.Hom.ext
  apply ModuleCat.hom_ext
  exact LinearMap.ext h

variable (Y : Type u) [Fintype Y] [MulAction G Y] (A : Type (u + 1)) [Fintype A]

/-- `G` acting on the functions `Y → A → ℤ/m` through `Y`: `(g φ)(y) = φ(g⁻¹ y)`. -/
def permRepresentation : Representation (ZMod m) G (ULift.{u + 1} (Y → A → ZMod m)) where
  toFun g :=
    { toFun := fun φ => ⟨fun y a => φ.down (g⁻¹ • y) a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext φ : 1
    apply ULift.ext
    funext y a
    simp
  map_mul' g h := by
    ext φ : 1
    apply ULift.ext
    funext y a
    simp [Module.End.mul_apply, mul_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype Y] [Fintype A] in
/-- The action on the permutation module: `(g φ)(y)(a) = φ(g⁻¹ y)(a)`. -/
theorem permRepresentation_apply (g : G) (φ : ULift.{u + 1} (Y → A → ZMod m)) (y : Y) (a : A) :
    (permRepresentation m Y A g φ).down y a = φ.down (g⁻¹ • y) a :=
  rfl

omit [Fintype A] [Fintype Y] in
variable {Y} in
/-- The action on the permutation module is continuous when the stabilizers of `Y` are open. -/
theorem isContinuous_permRepresentation [Finite Y]
    (hY : ∀ y : Y, IsOpen (MulAction.stabilizer G y : Set G)) :
    (actionOfRepresentation (ZMod m) G _ (permRepresentation m Y A)).IsContinuous := by
  refine (isContinuous_actionOfRepresentation_iff _).2 fun φ => ?_
  let S : Subgroup G :=
    { carrier := {g | permRepresentation m Y A g φ = φ}
      mul_mem' := fun {a b} ha hb => by
        show permRepresentation m Y A (a * b) φ = φ
        rw [map_mul, Module.End.mul_apply, show permRepresentation m Y A b φ = φ from hb]
        exact ha
      one_mem' := by
        show permRepresentation m Y A 1 φ = φ
        rw [map_one]
        rfl
      inv_mem' := fun {a} ha => by
        show permRepresentation m Y A a⁻¹ φ = φ
        conv_lhs => rw [← show permRepresentation m Y A a φ = φ from ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl }
  let K : Subgroup G := ⨅ y : Y, MulAction.stabilizer G y
  have hK : IsOpen (K : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun y => hY y
  have hKS : K ≤ S := by
    intro g hg
    show permRepresentation m Y A g φ = φ
    apply ULift.ext
    funext y a
    rw [permRepresentation_apply]
    have hg' : g⁻¹ ∈ MulAction.stabilizer G y :=
      (Subgroup.mem_iInf.1 (K.inv_mem hg)) y
    rw [MulAction.mem_stabilizer_iff.1 hg']
  exact Subgroup.isOpen_mono hKS hK

variable {Y} in
/-- **The permutation module** `ℤ/m[Y] ⊗ ℤ/m^A`, as the functions `Y → A → ℤ/m`, a finite
`ℤ/m`-module with continuous `G`-action. -/
def permModule [NeZero m] (hY : ∀ y : Y, IsOpen (MulAction.stabilizer G y : Set G)) :
    FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G :=
  ⟨ofRepresentation (permRepresentation m Y A) (isContinuous_permRepresentation m A hY),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv (ULift.moduleEquiv (R := ZMod m)).symm)⟩

end Perm

/-! ### The morphisms of the counting argument -/

section Maps

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ)
  [NeZero m]

variable {Y : Type u} [Fintype Y] [MulAction G Y] (A : Type (u + 1)) [Fintype A]
  (hY : ∀ y : Y, IsOpen (MulAction.stabilizer G y : Set G))

/-- **The pull-back along an equivariant map** `τ : Y → Y`: `τ^* φ = φ ∘ τ`. For an automorphism
of a Galois `G`-set it is a deck transformation. -/
def permPullback (τ : Y → Y) (hτ : ∀ (g : G) (y : Y), τ (g • y) = g • τ y) :
    permModule m A hY ⟶ permModule m A hY :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => ⟨fun y a => φ.down (τ y) a⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (fun g φ => by
      apply ULift.ext
      funext y a
      change φ.down (g⁻¹ • τ y) a = φ.down (τ (g⁻¹ • y)) a
      rw [hτ])

/-- The pull-back along `τ` is `(τ^* φ)(y)(a) = φ(τ y)(a)`. -/
theorem permPullback_apply (τ : Y → Y) (hτ : ∀ (g : G) (y : Y), τ (g • y) = g • τ y)
    (φ : ULift.{u + 1} (Y → A → ZMod m)) (y : Y) (a : A) :
    ((permPullback m A hY τ hτ).hom.hom.hom.hom.hom φ).down y a = φ.down (τ y) a :=
  rfl

/-- If `a` and `b` carry `y₀` to the same point, then `a⁻¹ b` lies in the stabilizer of `y₀`. -/
private theorem inv_mul_mem_stabilizer_of_smul_eq {H X : Type*} [Group H] [MulAction H X]
    {y₀ : X} {a b : H} (h : a • y₀ = b • y₀) : a⁻¹ * b ∈ MulAction.stabilizer H y₀ := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, ← h, inv_smul_smul]

/-- The action of a product is the composite of the actions. -/
private theorem rho_mul_apply {H : Type (u + 1)} [Group H] [TopologicalSpace H] {n : ℕ}
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) H) (b c : H)
    (x : M.obj.obj.obj.V) :
    (M.obj.obj.obj.ρ (b * c)).asHom.hom x = (M.obj.obj.obj.ρ b).asHom.hom ((M.obj.obj.obj.ρ c).asHom.hom x) :=
  congrArg (fun f => f.asHom.hom x) (map_mul M.obj.obj.obj.ρ b c)

/-- Right multiplication by an element fixing `x` does not change `ρ a x`. -/
private theorem rho_mul_apply_of_fixed {H : Type (u + 1)} [Group H] [TopologicalSpace H] {n : ℕ}
    (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod n) H) {a s : H}
    {x : M.obj.obj.obj.V} (hx : (M.obj.obj.obj.ρ s).asHom.hom x = x) :
    (M.obj.obj.obj.ρ (a * s)).asHom.hom x = (M.obj.obj.obj.ρ a).asHom.hom x := by
  rw [rho_mul_apply, hx]

variable {A} (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G) {y₀ : Y}
  {rep : Y → G} (hrep : ∀ y, rep y • y₀ = y) {v : A → M.obj.obj.obj.V}
  (hv : ∀ s ∈ MulAction.stabilizer G y₀, ∀ a, (M.obj.obj.obj.ρ s).asHom.hom (v a) = v a)

omit [IsTopologicalGroup G] [NeZero m] in
include hrep hv in
/-- The evaluation map is equivariant. -/
theorem permEval_equivariant (g : G) (φ : ULift.{u + 1} (Y → A → ZMod m)) :
    ∑ y : Y, ∑ a : A, φ.down (g⁻¹ • y) a • (M.obj.obj.obj.ρ (rep y)).asHom.hom (v a) =
      (M.obj.obj.obj.ρ g).asHom.hom
        (∑ y : Y, ∑ a : A, φ.down y a • (M.obj.obj.obj.ρ (rep y)).asHom.hom (v a)) := by
  simp only [map_sum, map_smul]
  refine Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun y => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  show _ = φ.down (g⁻¹ • y) a • (M.obj.obj.obj.ρ g).asHom.hom
    ((M.obj.obj.obj.ρ (rep (g⁻¹ • y))).asHom.hom (v a))
  congr 1
  have hs := inv_mul_mem_stabilizer_of_smul_eq (a := g * rep (g⁻¹ • y)) (b := rep y) (y₀ := y₀)
    (by rw [mul_smul, hrep, hrep, smul_inv_smul])
  rw [← rho_mul_apply, ← mul_inv_cancel_left (g * rep (g⁻¹ • y)) (rep y),
    rho_mul_apply_of_fixed M (hv _ hs a)]

/-- **Evaluation**: `φ ↦ ∑_y ∑_a φ(y)(a) · rep(y) (v a)` for a family `v : A → M` of elements
fixed by the stabilizer of `y₀`, where `rep y` carries `y₀` to `y`. On the basis function of
`(y₀, a)` it is `v a`. -/
def permEval : permModule m A hY ⟶ M :=
  finiteTypeContinuousModuleHomMk m
    { toFun := fun φ => ∑ y : Y, ∑ a : A, φ.down y a • (M.obj.obj.obj.ρ (rep y)).asHom.hom (v a)
      map_add' := fun φ ψ => by
        change ∑ y : Y, ∑ a : A, (φ.down y a + ψ.down y a) • _ = _
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c φ => by
        change ∑ y : Y, ∑ a : A, (c * φ.down y a) • _ = c • _
        simp only [mul_smul, Finset.smul_sum] }
    (fun g φ => permEval_equivariant m M hrep hv g φ)

/-- The evaluation map sends `φ` to `∑_y ∑_a φ(y)(a) · rep(y) (v a)`. -/
theorem permEval_apply (φ : ULift.{u + 1} (Y → A → ZMod m)) :
    (permEval m hY M hrep hv).hom.hom.hom.hom.hom φ =
      ∑ y : Y, ∑ a : A, φ.down y a • (M.obj.obj.obj.ρ (rep y)).asHom.hom (v a) :=
  rfl

end Maps


/-! ### Deck transformations of a Galois `G`-set -/

section Deck

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ)
  [NeZero m] {Y : Type u} [Fintype Y] [MulAction G Y] {y₀ : Y} {rep : Y → G}
  (hrep : ∀ y, rep y • y₀ = y) (hN : (MulAction.stabilizer G y₀).Normal)

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype Y] in
include hrep hN in
/-- The stabilizer of `y₀` is normal, so for every `n` the map `rep(y) y₀ ↦ rep(y) n y₀` is an
equivariant self-map of `Y`. -/
theorem deck_equivariant (n g : G) (y : Y) :
    rep (g • y) • n • y₀ = g • rep y • n • y₀ := by
  set s := (g * rep y)⁻¹ * rep (g • y) with hs_def
  have hs : s ∈ MulAction.stabilizer G y₀ :=
    inv_mul_mem_stabilizer_of_smul_eq (by rw [mul_smul, hrep, hrep])
  have hs' : n⁻¹ * s * n ∈ MulAction.stabilizer G y₀ := by
    have := hN.conj_mem s hs n⁻¹
    rwa [inv_inv] at this
  calc rep (g • y) • n • y₀ = ((g * rep y) * s) • n • y₀ := by rw [hs_def, mul_inv_cancel_left]
    _ = (g * rep y * n) • (n⁻¹ * s * n) • y₀ := by rw [← mul_smul, ← mul_smul]; group
    _ = g • rep y • n • y₀ := by rw [MulAction.mem_stabilizer_iff.1 hs', mul_smul, mul_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype Y] in
include hrep hN in
/-- The deck map is injective. -/
theorem deck_injective (n : G) : Function.Injective fun y : Y => rep y • n • y₀ := by
  intro y y' h
  have hmem : n⁻¹ * (rep y')⁻¹ * rep y * n ∈ MulAction.stabilizer G y₀ := by
    simpa [mul_assoc] using inv_mul_mem_stabilizer_of_smul_eq (y₀ := y₀)
      (a := rep y' * n) (b := rep y * n) (by simpa only [mul_smul] using h.symm)
  have hmem' : (rep y')⁻¹ * rep y ∈ MulAction.stabilizer G y₀ := by
    simpa [mul_assoc] using hN.conj_mem _ hmem n
  rw [← hrep y, ← hrep y']
  calc rep y • y₀ = rep y' • ((rep y')⁻¹ * rep y) • y₀ := by
        rw [← mul_smul, mul_inv_cancel_left]
    _ = rep y' • y₀ := by rw [MulAction.mem_stabilizer_iff.1 hmem']

end Deck


section Trivial

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ)
  [NeZero m]

open scoped Stacks.DiscreteModuleTopology in
/-- **`ℤ/m` with the trivial action**, as a finite `ℤ/m`-module with continuous `G`-action. -/
def trivialContinuousModule : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G :=
  ⟨ofRepresentation (Representation.trivial (ZMod m) G (ULift.{u + 1} (ZMod m)))
      ((isContinuous_actionOfRepresentation_iff _).2 fun _ => by simp),
    (ModuleCat.isFG_iff _).2 (Module.Finite.equiv (ULift.moduleEquiv (R := ZMod m)).symm)⟩

omit [IsTopologicalGroup G] in
/-- An isomorphism of finite continuous modules from an equivariant linear equivalence. -/
def finiteTypeContinuousModuleIsoMk
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G}
    (f : P.obj.obj.obj.V ≃ₗ[ZMod m] Q.obj.obj.obj.V)
    (hf : ∀ (g : G) (x : P.obj.obj.obj.V),
      f ((P.obj.obj.obj.ρ g).asHom.hom x) = (Q.obj.obj.obj.ρ g).asHom.hom (f x)) : P ≅ Q where
  hom := finiteTypeContinuousModuleHomMk m f.toLinearMap hf
  inv := finiteTypeContinuousModuleHomMk m f.symm.toLinearMap fun g y =>
    f.injective ((f.apply_symm_apply _).trans
      ((congrArg (Q.obj.obj.obj.ρ g).asHom.hom (f.apply_symm_apply y)).symm.trans
        (hf g (f.symm y)).symm))
  hom_inv_id := finiteTypeContinuousModule_hom_ext m fun x => f.symm_apply_apply x
  inv_hom_id := finiteTypeContinuousModule_hom_ext m fun x => f.apply_symm_apply x

end Trivial

/-! ### The count -/

section Count

variable {G : Type (u + 1)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (m : ℕ) [NeZero m]

omit [IsTopologicalGroup G] [NeZero m] [CompactSpace G] in
/-- The underlying map of a finite sum of morphisms of finite continuous modules is the sum of
the underlying maps. -/
theorem finiteTypeContinuousModule_sum_apply
    {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G} {ι : Type*} (s : Finset ι)
    (f : ι → (P ⟶ Q)) (x : P.obj.obj.obj.V) :
    (∑ i ∈ s, f i).hom.hom.hom.hom.hom x = ∑ i ∈ s, (f i).hom.hom.hom.hom.hom x := by
  have := additive_continuousModuleToModuleCat.{0, u + 1, u + 1} (ZMod m) G
  let F := finiteTypeContinuousModuleι.{0, u + 1, u + 1} (ZMod m) G ⋙
    Stacks.Injectives.continuousModuleUnderlying.{0, u + 1, u + 1} (ZMod m) G
  have h := congrArg (fun φ => φ.hom x) (F.map_sum f s)
  simp only [ModuleCat.hom_sum] at h
  exact h.trans (LinearMap.sum_apply _ _ _)

omit [IsTopologicalGroup G] [NeZero m] [CompactSpace G] in
/-- A finite sum of functions `Y → A → ℤ/m`, wrapped in `ULift`, is evaluated pointwise. -/
theorem ulift_down_sum_apply {Y : Type u} {A : Type (u + 1)} {ι : Type*} (s : Finset ι)
    (f : ι → ULift.{u + 1} (Y → A → ZMod m)) (y : Y) (a : A) :
    (∑ i ∈ s, f i).down y a = ∑ i ∈ s, (f i).down y a := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]; rfl

variable (T : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G ⥤ ModuleCat.{u + 1} (ZMod m))
  [T.Additive]
  (hT : ∀ {P Q : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G} (b : P ⟶ Q),
    Function.Surjective b.hom.hom.hom.hom.hom → Function.Surjective (T.map b).hom)
  {Y : Type u} [Fintype Y] [MulAction G Y]
  (hY : ∀ y : Y, IsOpen (MulAction.stabilizer G y : Set G)) {y₀ : Y}
  (htrans : ∀ y, ∃ g : G, g • y₀ = y) (hN : (MulAction.stabilizer G y₀).Normal)
  (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} (ZMod m) G)
  (hM : ∀ s ∈ MulAction.stabilizer G y₀, ∀ x, (M.obj.obj.obj.ρ s).asHom.hom x = x)

omit [CompactSpace G] in
include hT htrans hN hM in
/-- **The count of [Stacks, Tag 03VK]**: let `T` be an additive functor on finite continuous
`ℤ/m`-modules preserving surjections, `Y` a finite transitive `G`-set whose stabilizers are normal
(a Galois `G`-set), and suppose that `T` of the permutation module of `Y` has at most as many
elements as `T` of the permutation module of a point, the latter being `ℤ/m`. Then
`T(M)` is finite and `#T(M) ≤ #M_G` for every `M` on which the stabilizers of `Y` act trivially. -/
theorem finite_and_natCard_obj_le_natCard_coinvariants_of_perm
    [Finite (T.obj (permModule m PUnit.{u + 2} hY))]
    (hcard : Nat.card (T.obj (permModule m PUnit.{u + 2} hY)) ≤
      Nat.card (T.obj (trivialContinuousModule m)))
    (e : T.obj (trivialContinuousModule m) ≃ₗ[ZMod m] ZMod m) :
    Finite (T.obj M) ∧ Nat.card (T.obj M) ≤
      Nat.card
        (Representation.Coinvariants (finiteTypeContinuousModuleRepresentation (ZMod m) _ M)) := by
  classical
  choose rep hrep using htrans
  have : Finite M.obj.obj.obj.V := (moduleCat_isFG_iff_finite (ZMod m) _).1 M.property
  let : Fintype M.obj.obj.obj.V := Fintype.ofFinite _
  let P := permModule m PUnit.{u + 2} hY
  let σ := finiteTypeContinuousModuleRepresentation (ZMod m) _ M
  let ψf : M.obj.obj.obj.V → (P ⟶ M) := fun b =>
    permEval m hY M hrep (v := fun _ => b) (fun s hs _ => hM s hs b)
  have hψf : ∀ b φ, (ψf b).hom.hom.hom.hom.hom φ =
      ∑ y : Y, ∑ a : PUnit.{u + 2}, φ.down y a • (M.obj.obj.obj.ρ (rep y)).asHom.hom b := fun _ _ => rfl
  let ψ : M.obj.obj.obj.V →+ (P ⟶ M) :=
    { toFun := ψf
      map_zero' := finiteTypeContinuousModule_hom_ext m fun φ => by
        rw [hψf]
        simp only [map_zero, smul_zero, Finset.sum_const_zero]
        rfl
      map_add' := fun b b' => finiteTypeContinuousModule_hom_ext m fun φ => by
        rw [hψf]
        show _ = (ψf b).hom.hom.hom.hom.hom φ + (ψf b').hom.hom.hom.hom.hom φ
        rw [hψf, hψf, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_add, smul_add] }
  let τ : G → Y → Y := fun n y => rep y • n • y₀
  have hτ : ∀ n, Function.Bijective (τ n) := fun n =>
    (Finite.injective_iff_bijective).1 (deck_injective hrep hN n)
  let R : G → (P ⟶ P) := fun n =>
    permPullback m PUnit.{u + 2} hY (τ n) (deck_equivariant hrep hN n)
  have hR : ∀ (g : G) (b : M.obj.obj.obj.V), R g ≫ ψ b = ψ (σ g⁻¹ b) := by
    intro g b
    apply finiteTypeContinuousModule_hom_ext m
    intro φ
    show (ψf b).hom.hom.hom.hom.hom ((R g).hom.hom.hom.hom.hom φ) =
      (ψf (σ g⁻¹ b)).hom.hom.hom.hom.hom φ
    rw [hψf, hψf, ← (hτ g).sum_comp (fun y => ∑ a : PUnit.{u + 2},
      φ.down y a • (M.obj.obj.obj.ρ (rep y)).asHom.hom (σ g⁻¹ b))]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun a _ => ?_
    show φ.down (τ g y) a • _ = φ.down (τ g y) a • _
    congr 1
    set t := (rep y * g)⁻¹ * rep (τ g y) with ht_def
    have ht : t ∈ MulAction.stabilizer G y₀ :=
      inv_mul_mem_stabilizer_of_smul_eq (by rw [mul_smul, hrep])
    have ht' : g * t * g⁻¹ ∈ MulAction.stabilizer G y₀ := hN.conj_mem t ht g
    show _ = (M.obj.obj.obj.ρ (rep (τ g y))).asHom.hom ((M.obj.obj.obj.ρ g⁻¹).asHom.hom b)
    rw [← rho_mul_apply, show rep (τ g y) * g⁻¹ = rep y * (g * t * g⁻¹) by rw [ht_def]; group,
      rho_mul_apply_of_fixed M (hM _ ht' b)]
  let ε : P ⟶ trivialContinuousModule m :=
    finiteTypeContinuousModuleHomMk m
      { toFun := fun φ => ⟨∑ y : Y, φ.down y PUnit.unit⟩
        map_add' := fun (φ φ' : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)) => by
          apply ULift.ext
          exact Finset.sum_add_distrib
        map_smul' := fun c (φ : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)) => by
          apply ULift.ext
          exact (Finset.mul_sum _ _ _).symm }
      (fun g (φ : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)) => by
        apply ULift.ext
        exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun y => rfl)
  have hεR : ∀ n, R n ≫ ε = ε := fun n => finiteTypeContinuousModule_hom_ext m fun φ => by
    apply ULift.ext
    exact (hτ n).sum_comp (fun y => (φ : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)).down y
      PUnit.unit)
  have hεsurj : Function.Surjective ε.hom.hom.hom.hom.hom := by
    intro (c : ULift.{u + 1} (ZMod m))
    refine
      ⟨(⟨fun y _ => if y = y₀ then c.down else 0⟩ : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)), ?_⟩
    apply ULift.ext
    show (∑ y : Y, if y = y₀ then c.down else 0) = c.down
    rw [Finset.sum_ite_eq' Finset.univ y₀, if_pos (Finset.mem_univ _)]
  have hTε : Function.Bijective (T.map ε).hom :=
    (hT ε hεsurj).bijective_of_nat_card_le hcard
  have hRT : ∀ g : G, T.map (R g) = 𝟙 _ := fun g =>
    ModuleCat.hom_ext <| LinearMap.ext fun s => hTε.1 <| by
      have h := congrArg (fun φ => (T.map φ).hom s) (hεR g)
      simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
      exact h
  let Eε := Equiv.ofBijective _ hTε
  let u₀ : T.obj P := Eε.symm (e.symm 1)
  have hu : ∀ s : T.obj P, ∃ c : ZMod m, s = c • u₀ := by
    intro s
    refine ⟨e ((T.map ε).hom s), hTε.1 ?_⟩
    rw [map_smul]
    show _ = e ((T.map ε).hom s) • Eε (Eε.symm (e.symm 1))
    rw [Equiv.apply_symm_apply, ← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  let Q := permModule m M.obj.obj.obj.V hY
  let Ψ : Q ⟶ M := permEval m hY M hrep (v := id) (fun s hs a => hM s hs a)
  have hΨ : Function.Surjective Ψ.hom.hom.hom.hom.hom := by
    intro b
    refine ⟨⟨fun y a => if y = y₀ ∧ a = b then 1 else 0⟩, ?_⟩
    show ∑ y : Y, ∑ a : M.obj.obj.obj.V, (if y = y₀ ∧ a = b then (1 : ZMod m) else 0) •
      (M.obj.obj.obj.ρ (rep y)).asHom.hom a = b
    rw [Finset.sum_eq_single y₀ (fun y _ hy => Finset.sum_eq_zero fun a _ => by
        rw [if_neg (fun h => hy h.1), zero_smul]) (fun h => absurd (Finset.mem_univ _) h),
      Finset.sum_eq_single b (fun a _ ha => by rw [if_neg (fun h => ha h.2), zero_smul])
        (fun h => absurd (Finset.mem_univ _) h), if_pos ⟨rfl, rfl⟩, one_smul, hM _ (hrep y₀) b]
  let ι : M.obj.obj.obj.V → (P ⟶ Q) := fun b =>
    finiteTypeContinuousModuleHomMk m
      { toFun := fun φ => ⟨fun y a => if a = b then φ.down y PUnit.unit else 0⟩
        map_add' := fun (φ φ' : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)) => by
          apply ULift.ext
          funext y a
          show (if a = b then φ.down y PUnit.unit + φ'.down y PUnit.unit else 0) =
            (if a = b then φ.down y PUnit.unit else 0) + (if a = b then φ'.down y PUnit.unit else 0)
          split_ifs <;> simp
        map_smul' := fun c (φ : ULift.{u + 1} (Y → PUnit.{u + 2} → ZMod m)) => by
          apply ULift.ext
          funext y a
          show (if a = b then c * φ.down y PUnit.unit else 0) =
            c * (if a = b then φ.down y PUnit.unit else 0)
          split_ifs <;> simp }
      (fun g φ => rfl)
  let π : M.obj.obj.obj.V → (Q ⟶ P) := fun b =>
    finiteTypeContinuousModuleHomMk m
      { toFun := fun φ => ⟨fun y _ => φ.down y b⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
      (fun g φ => rfl)
  have hπι : ∑ b, π b ≫ ι b = 𝟙 Q := by
    apply finiteTypeContinuousModule_hom_ext m
    intro φ
    rw [finiteTypeContinuousModule_sum_apply]
    apply ULift.ext
    funext y a
    refine (ulift_down_sum_apply m Finset.univ (fun b => ((ι b).hom.hom.hom.hom.hom
      ((π b).hom.hom.hom.hom.hom φ) : ULift.{u + 1} (Y → M.obj.obj.obj.V → ZMod m))) y a).trans ?_
    show (∑ b, if a = b then φ.down y b else 0) = φ.down y a
    rw [Finset.sum_ite_eq Finset.univ a, if_pos (Finset.mem_univ _)]
  have hιΨ : ∀ b, ι b ≫ Ψ = ψ b := fun b => finiteTypeContinuousModule_hom_ext m fun φ => by
    show ∑ y : Y, ∑ a : M.obj.obj.obj.V, (if a = b then φ.down y PUnit.unit else 0) •
      (M.obj.obj.obj.ρ (rep y)).asHom.hom a = (ψf b).hom.hom.hom.hom.hom φ
    rw [hψf]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fintype.sum_unique]
  have hspan : ∀ t : T.obj M, ∃ (n : ℕ) (a : Fin n → M.obj.obj.obj.V) (s : Fin n → T.obj P),
      t = ∑ i, (T.map (ψ (a i))).hom (s i) := by
    intro t
    obtain ⟨q, rfl⟩ := hT Ψ hΨ t
    let eq := Fintype.equivFin M.obj.obj.obj.V
    refine ⟨Fintype.card M.obj.obj.obj.V, fun i => eq.symm i,
      fun i => (T.map (π (eq.symm i))).hom q, ?_⟩
    have h1 : q = ∑ b, (T.map (ι b)).hom ((T.map (π b)).hom q) := by
      have := congrArg (fun φ => (T.map φ).hom q) hπι
      simp only [T.map_sum, T.map_id, Functor.map_comp, ModuleCat.hom_sum, ModuleCat.hom_comp,
        LinearMap.sum_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at this
      exact this.symm
    conv_lhs => rw [h1]
    rw [map_sum]
    refine (Fintype.sum_equiv eq _ _ fun b => ?_)
    simp only [Equiv.symm_apply_apply]
    rw [← hιΨ]
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact finite_and_natCard_obj_le_natCard_coinvariants T σ ψ R hR hRT u₀ hu hspan

end Count

end Stacks.EtaleCohomology

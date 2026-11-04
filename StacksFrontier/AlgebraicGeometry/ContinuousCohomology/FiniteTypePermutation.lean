module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeDual
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeCoinduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange

/-!
# Permutation modules `N[G/H]`

Let `G` be a compact group, `H` an open subgroup and `N` a finite `R`-module with the trivial
action. The coinduced module `Coind_H N` is the permutation module `N[G/H]` of functions
`G ⧸ H → N`, with `G` translating the argument.

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleIsoMk`: an equivariant linear equivalence
  as an isomorphism.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleUntwistSum`: for `H` acting trivially on `M`
  and `N` the underlying module of `M`, the *untwisted sum* `N[G/H] ⟶ M`,
  `f ↦ Σ_{x ∈ G/H} x • f(x)`.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleUntwistUnit`: the *untwisted unit*
  `M ⟶ N[G/H]`, `m ↦ (gH ↦ g⁻¹ • m)`.
* `Stacks.GroupCohomology.mackeyCosetEquiv`: the bijection `G/φ⁻¹H × Γ/φ(G)H ≃ Γ/H`.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleDualCoindTrivialIso`: the dual of `N[G/H]`
  is `N^∨[G/H]`, as modules over the opposite ring.
* `Stacks.GroupCohomology.finiteTypeContinuousModuleResCoindTrivialIso`: the Mackey
  decomposition: for `φ : G' → G` with normal image and `H` normal, the restriction of `N[G/H]`
  to `G'` is the permutation module `(N^I)[G'/φ⁻¹H]` with `I = G/(φ(G')H)`.

## Main results

* `Stacks.GroupCohomology.epi_finiteTypeContinuousModuleUntwistSum`: the untwisted sum is an
  epimorphism.
* `Stacks.GroupCohomology.mono_finiteTypeContinuousModuleUntwistUnit`: the untwisted unit is a
  monomorphism.
* `Stacks.GroupCohomology.bijective_mackeyCosetMap`: the coset map
  `G/φ⁻¹H × Γ/φ(G)H → Γ/H` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped CharacterModule.MulOppositeAction

universe u v w

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology

section IsoMk

variable {R : Type u} [Ring R] {G : Type v} [Group G] [TopologicalSpace G]

/-- **An equivariant linear equivalence is an isomorphism** of finite `R`-modules with a
continuous `G`-action. -/
def finiteTypeContinuousModuleIsoMk {M N : FiniteTypeContinuousModule.{u, v, w} R G}
    (e : M.obj.obj.obj.V ≃ₗ[R] N.obj.obj.obj.V)
    (he : ∀ g x, e ((M.obj.obj.obj.ρ g).hom x) = (N.obj.obj.obj.ρ g).hom (e x)) : M ≅ N where
  hom := ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv R G _ _).symm ⟨e.toLinearMap, he⟩)
  inv := ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv R G _ _).symm
    ⟨e.symm.toLinearMap, fun g y ↦ e.injective (by
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he])⟩)
  hom_inv_id := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
    apply Action.hom_ext; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
    exact e.apply_symm_apply x

/-- The underlying linear map of `Stacks.GroupCohomology.finiteTypeContinuousModuleIsoMk e he`
is `e`. -/
lemma finiteTypeContinuousModuleIsoMk_hom {M N : FiniteTypeContinuousModule.{u, v, w} R G}
    (e : M.obj.obj.obj.V ≃ₗ[R] N.obj.obj.obj.V)
    (he : ∀ g x, e ((M.obj.obj.obj.ρ g).hom x) = (N.obj.obj.obj.ρ g).hom (e x)) :
    (finiteTypeContinuousModuleIsoMk e he).hom.hom.hom.hom.hom.hom = e.toLinearMap :=
  rfl

end IsoMk

section UntwistSum

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (H : OpenSubgroup G)

variable {R H} in
omit [IsTopologicalGroup G] [CompactSpace G] in
/-- If `H` acts trivially on `M`, then `finiteTypeContinuousModuleRepresentation R G M h = 1` for
every `h ∈ H`. -/
lemma representation_eq_one_of_ρ_eq_one (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) (h : G) (hh : h ∈ H) :
    finiteTypeContinuousModuleRepresentation R G M h = 1 :=
  LinearMap.ext fun m ↦ by
    rw [finiteTypeContinuousModuleRepresentation_apply, Module.End.one_apply]
    exact (congrArg (fun φ ↦ ModuleCat.Hom.hom φ m) (hH h hh)).trans rfl

variable {R H} in
/-- The action of a coset `x = gH` on a module on which `H` acts trivially: `ρ(g)`. -/
def cosetAction (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (x : G ⧸ (H : Subgroup G)) : M.obj.obj.obj.V →ₗ[R] M.obj.obj.obj.V :=
  finiteTypeContinuousModuleRepresentation R G M x.out

variable {R H} in
omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The action of the coset `gH` is `ρ(g)`. -/
lemma cosetAction_mk (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) (g : G) :
    cosetAction M (g : G ⧸ (H : Subgroup G)) =
      finiteTypeContinuousModuleRepresentation R G M g := by
  obtain ⟨h, hg⟩ := QuotientGroup.mk_out_eq_mul (H : Subgroup G) g
  rw [cosetAction, hg, map_mul, representation_eq_one_of_ρ_eq_one M hH h h.2, mul_one]

variable {R H} in
omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The action of `g • x` is `ρ(g)` composed with the action of `x`. -/
lemma cosetAction_smul (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) (g : G) (x : G ⧸ (H : Subgroup G)) :
    cosetAction M (g • x) = finiteTypeContinuousModuleRepresentation R G M g * cosetAction M x := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, cosetAction_mk M hH, cosetAction_mk M hH, map_mul]

/-- The linear map `f ↦ Σ_{x ∈ G/H} x • f(x)`. -/
def untwistSumLinearMap (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    (G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) →ₗ[R] M.obj.obj.obj.V :=
  letI : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  ∑ x : G ⧸ (H : Subgroup G), cosetAction M x ∘ₗ LinearMap.proj x

/-- `Stacks.GroupCohomology.untwistSumLinearMap` sends `f` to the sum over `x ∈ G/H` of
`Stacks.GroupCohomology.cosetAction M x (f x)`. -/
lemma untwistSumLinearMap_apply (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (f : G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :
    letI : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
    untwistSumLinearMap R H M f = ∑ x : G ⧸ (H : Subgroup G), cosetAction M x (f x) := by
  simp [untwistSumLinearMap]

variable {R H} in
/-- The untwisted sum is equivariant. -/
lemma untwistSumLinearMap_translate (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) (g : G) (f : G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :
    untwistSumLinearMap R H M (fun x ↦ f (g⁻¹ • x)) =
      finiteTypeContinuousModuleRepresentation R G M g (untwistSumLinearMap R H M f) := by
  let : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  rw [untwistSumLinearMap_apply, untwistSumLinearMap_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun x ↦ ?_
  change cosetAction M x (f (g⁻¹ • x)) =
    finiteTypeContinuousModuleRepresentation R G M g (cosetAction M (g⁻¹ • x) (f (g⁻¹ • x)))
  rw [cosetAction_smul M hH, Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

variable {R H} in
/-- The untwisted sum of the function supported on the trivial coset with value `m` is `m`. -/
lemma untwistSumLinearMap_single [DecidableEq (G ⧸ (H : Subgroup G))]
    (M : FiniteTypeContinuousModule.{u, v, w} R G) (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1)
    (m : M.obj.obj.obj.V) :
    untwistSumLinearMap R H M (Pi.single ((1 : G) : G ⧸ (H : Subgroup G)) m) = m := by
  let : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  rw [untwistSumLinearMap_apply, Finset.sum_eq_single ((1 : G) : G ⧸ (H : Subgroup G))]
  · rw [Pi.single_eq_same, cosetAction_mk M hH, map_one, Module.End.one_apply]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, map_zero]
  · simp

/-- The underlying finite module of a finite module with a continuous action, with the trivial
action. -/
abbrev finiteTypeContinuousModuleTrivialUnderlying (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    FiniteTypeContinuousModule.{u, v, w} R G :=
  (finiteTypeContinuousModuleTrivial R G).obj ⟨M.obj.obj.obj.V, M.property⟩

/-- **The untwisted sum `N[G/H] ⟶ M`**, `f ↦ Σ_{x ∈ G/H} x • f(x)`, for `H` acting trivially on
`M` and `N` the underlying module of `M`. -/
def finiteTypeContinuousModuleUntwistSum (M : FiniteTypeContinuousModule.{u, v, max u v} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) :
    (finiteTypeContinuousModuleCoind R H).obj (finiteTypeContinuousModuleTrivialUnderlying R M) ⟶
      M :=
  ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv R G _ _).symm
    ⟨untwistSumLinearMap R H M, fun g f ↦ untwistSumLinearMap_translate M hH g f⟩)

/-- **The untwisted sum is an epimorphism.** -/
instance epi_finiteTypeContinuousModuleUntwistSum
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) :
    Epi (finiteTypeContinuousModuleUntwistSum R H M hH) := by
  classical
  exact (finiteTypeContinuousModuleι.{u, v, max u v} R G).epi_of_epi_map
    ((epi_iff_surjective R _).2 fun m ↦
      ⟨Pi.single ((1 : G) : G ⧸ (H : Subgroup G)) m, untwistSumLinearMap_single M hH m⟩)

variable {R H} in
/-- The inverse action of a coset `x = gH` on a module on which `H` acts trivially: `ρ(g⁻¹)`. -/
def cosetInvAction (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (x : G ⧸ (H : Subgroup G)) : M.obj.obj.obj.V →ₗ[R] M.obj.obj.obj.V :=
  finiteTypeContinuousModuleRepresentation R G M x.out⁻¹

variable {R H} in
omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The inverse action of the coset `gH` is `ρ(g⁻¹)`. -/
lemma cosetInvAction_mk (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) (g : G) :
    cosetInvAction M (g : G ⧸ (H : Subgroup G)) =
      finiteTypeContinuousModuleRepresentation R G M g⁻¹ := by
  obtain ⟨h, hg⟩ := QuotientGroup.mk_out_eq_mul (H : Subgroup G) g
  rw [cosetInvAction, hg, mul_inv_rev, map_mul,
    representation_eq_one_of_ρ_eq_one M hH _ (H.inv_mem h.2), one_mul]

/-- The linear map `m ↦ (gH ↦ g⁻¹ • m)`. -/
def untwistUnitLinearMap (M : FiniteTypeContinuousModule.{u, v, w} R G) :
    M.obj.obj.obj.V →ₗ[R] (G ⧸ (H : Subgroup G) → M.obj.obj.obj.V) :=
  LinearMap.pi fun x ↦ cosetInvAction M x

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- `Stacks.GroupCohomology.untwistUnitLinearMap` sends `m` to the function
`x ↦ Stacks.GroupCohomology.cosetInvAction M x m`. -/
lemma untwistUnitLinearMap_apply (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (m : M.obj.obj.obj.V) (x : G ⧸ (H : Subgroup G)) :
    untwistUnitLinearMap R H M m x = cosetInvAction M x m :=
  rfl

variable {R H} in
omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The untwisted unit is equivariant. -/
lemma untwistUnitLinearMap_translate (M : FiniteTypeContinuousModule.{u, v, w} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) (g : G) (m : M.obj.obj.obj.V) :
    untwistUnitLinearMap R H M (finiteTypeContinuousModuleRepresentation R G M g m) =
      fun x ↦ untwistUnitLinearMap R H M m (g⁻¹ • x) := by
  funext x
  induction x using QuotientGroup.induction_on with
  | H a =>
    rw [untwistUnitLinearMap_apply, untwistUnitLinearMap_apply, MulAction.Quotient.smul_mk,
      smul_eq_mul, cosetInvAction_mk M hH, cosetInvAction_mk M hH, ← Module.End.mul_apply,
      ← map_mul, mul_inv_rev, inv_inv]

/-- **The untwisted unit `M ⟶ N[G/H]`**, `m ↦ (gH ↦ g⁻¹ • m)`, for `H` acting trivially on `M`
and `N` the underlying module of `M`. -/
def finiteTypeContinuousModuleUntwistUnit (M : FiniteTypeContinuousModule.{u, v, max u v} R G)
    (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) :
    M ⟶ (finiteTypeContinuousModuleCoind R H).obj
      (finiteTypeContinuousModuleTrivialUnderlying R M) :=
  ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv R G _ _).symm
    ⟨untwistUnitLinearMap R H M, fun g m ↦ untwistUnitLinearMap_translate M hH g m⟩)

/-- **The untwisted unit is a monomorphism.** -/
instance mono_finiteTypeContinuousModuleUntwistUnit
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) (hH : ∀ h ∈ H, M.obj.obj.obj.ρ h = 1) :
    Mono (finiteTypeContinuousModuleUntwistUnit R H M hH) := by
  refine (finiteTypeContinuousModuleι.{u, v, max u v} R G).mono_of_mono_map
    ((mono_iff_injective R _).2 fun m m' e ↦ ?_)
  have h := congrFun e ((1 : G) : G ⧸ (H : Subgroup G))
  change untwistUnitLinearMap R H M m _ = untwistUnitLinearMap R H M m' _ at h
  rwa [untwistUnitLinearMap_apply, untwistUnitLinearMap_apply, cosetInvAction_mk M hH, inv_one,
    map_one, Module.End.one_apply, Module.End.one_apply] at h

end UntwistSum

section Dual

variable (R : Type u) [Ring R] [Finite R] {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (H : OpenSubgroup G)

/-- The dual coefficients `Q^∨` of a finite `R`-module `Q`, a finite `Rᵐᵒᵖ`-module. -/
def dualCoefficient (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{w} R)) :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{w} Rᵐᵒᵖ) :=
  ⟨ModuleCat.of Rᵐᵒᵖ (CharacterModule Q.obj), by
    have : Module.Finite R Q.obj := Q.property
    have : Finite Q.obj := Module.finite_of_finite R
    change Module.Finite Rᵐᵒᵖ (CharacterModule Q.obj)
    exact Module.Finite.of_finite⟩

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- A translate of a function supported at one point is supported at the translated point. -/
lemma pi_single_smul_apply [DecidableEq (G ⧸ (H : Subgroup G))] {A : Type*} [Zero A]
    (x z : G ⧸ (H : Subgroup G)) (a : A) (g : G) :
    (Pi.single x a : G ⧸ (H : Subgroup G) → A) (g • z) =
      (Pi.single (g⁻¹ • x) a : G ⧸ (H : Subgroup G) → A) z := by
  simp only [Pi.single_apply, smul_eq_iff_eq_inv_smul]

omit [Finite R] in
/-- Characters of `A[G/H]` read pointwise commute with translation. -/
lemma piEquiv_dual_funLeft [DecidableEq (G ⧸ (H : Subgroup G))] {A : Type*} [AddCommGroup A]
    [Module R A] (c : CharacterModule (G ⧸ (H : Subgroup G) → A)) (g : G)
    (x : G ⧸ (H : Subgroup G)) :
    CharacterModule.piEquiv R (G ⧸ (H : Subgroup G)) (fun _ ↦ A)
        (CharacterModule.dualMulOpposite (LinearMap.funLeft R A (fun z ↦ g⁻¹⁻¹ • z)) c) x =
      CharacterModule.piEquiv R (G ⧸ (H : Subgroup G)) (fun _ ↦ A) c (g⁻¹ • x) :=
  DFunLike.ext _ _ fun a ↦ by
    change c (fun z ↦ (Pi.single x a : G ⧸ (H : Subgroup G) → A) (g⁻¹⁻¹ • z)) =
      c (Pi.single (g⁻¹ • x) a)
    congr 1
    funext z
    rw [inv_inv, pi_single_smul_apply]

/-- **The dual of a permutation module is the permutation module of the dual coefficients**:
`(Q[G/H])^∨ ≅ Q^∨[G/H]`, as finite `Rᵐᵒᵖ`-modules with continuous `G`-action. -/
def finiteTypeContinuousModuleDualCoindTrivialIso
    (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{max u v} R)) :
    (finiteTypeContinuousModuleDual R G).obj (Opposite.op ((finiteTypeContinuousModuleCoind R H).obj
      ((finiteTypeContinuousModuleTrivial R G).obj Q))) ≅
    (finiteTypeContinuousModuleCoind Rᵐᵒᵖ H).obj
      ((finiteTypeContinuousModuleTrivial Rᵐᵒᵖ G).obj (dualCoefficient R Q)) :=
  letI : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
  finiteTypeContinuousModuleIsoMk
    (CharacterModule.piEquiv R (G ⧸ (H : Subgroup G)) (fun _ ↦ Q.obj))
    (fun g c ↦ funext fun x ↦ piEquiv_dual_funLeft R H c g x)

end Dual

section Mackey

open scoped Pointwise

variable {G Γ : Type v} [Group G] [Group Γ] (φ : G →* Γ) (H : Subgroup Γ) [H.Normal]
  [φ.range.Normal]

/-- The subgroup `φ(G) H` of `Γ`. -/
abbrev mackeySubgroup : Subgroup Γ := φ.range ⊔ H

/-- **The coset map `G/φ⁻¹H × Γ/φ(G)H → Γ/H`**, `(gφ⁻¹H, i) ↦ φ(g) s(i) H` with `s(i)` a
representative of `i`. -/
def mackeyCosetMap : (G ⧸ H.comap φ) × (Γ ⧸ mackeySubgroup φ H) → Γ ⧸ H := fun p ↦
  Quotient.liftOn' p.1 (fun g ↦ ((φ g * p.2.out : Γ) : Γ ⧸ H)) fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab
    rw [QuotientGroup.eq, show (φ a * p.2.out)⁻¹ * (φ b * p.2.out) =
        p.2.out⁻¹ * φ (a⁻¹ * b) * p.2.out by rw [map_mul, map_inv]; group]
    exact (inferInstance : H.Normal).conj_mem' _ hab _

omit [φ.range.Normal] in
/-- `Stacks.GroupCohomology.mackeyCosetMap` on a coset `gφ⁻¹H`. -/
lemma mackeyCosetMap_mk (g : G) (i : Γ ⧸ mackeySubgroup φ H) :
    mackeyCosetMap φ H ((g : G ⧸ H.comap φ), i) = ((φ g * i.out : Γ) : Γ ⧸ H) :=
  rfl

omit [φ.range.Normal] in
/-- `Stacks.GroupCohomology.mackeyCosetMap` is `G`-equivariant, `G` acting on `Γ/H` through
`φ`. -/
lemma mackeyCosetMap_smul (g : G) (a : G ⧸ H.comap φ) (i : Γ ⧸ mackeySubgroup φ H) :
    mackeyCosetMap φ H (g • a, i) = φ g • mackeyCosetMap φ H (a, i) := by
  induction a using QuotientGroup.induction_on with
  | H b =>
    rw [MulAction.Quotient.smul_mk, mackeyCosetMap_mk, mackeyCosetMap_mk, smul_eq_mul,
      MulAction.Quotient.smul_mk, smul_eq_mul, map_mul, mul_assoc]

/-- An element and its `φ(G)`-translates lie in the same `φ(G)H`-coset. -/
lemma mk_mackeySubgroup_mul (g : G) (γ : Γ) :
    ((φ g * γ : Γ) : Γ ⧸ mackeySubgroup φ H) = (γ : Γ ⧸ mackeySubgroup φ H) := by
  have hN : (mackeySubgroup φ H).Normal := Subgroup.sup_normal _ _
  rw [QuotientGroup.eq, show (φ g * γ)⁻¹ * γ = γ⁻¹ * (φ g)⁻¹ * γ by group]
  exact hN.conj_mem' _ (Subgroup.mem_sup_left ((φ.range).inv_mem ⟨g, rfl⟩)) γ

/-- The coset map `G/φ⁻¹H × Γ/φ(G)H → Γ/H` is bijective. -/
theorem bijective_mackeyCosetMap : Function.Bijective (mackeyCosetMap φ H) := by
  have hN : (mackeySubgroup φ H).Normal := Subgroup.sup_normal _ _
  constructor
  · rintro ⟨a, i⟩ ⟨a', i'⟩ h
    induction a using QuotientGroup.induction_on with
    | H g =>
    induction a' using QuotientGroup.induction_on with
    | H g' =>
    rw [mackeyCosetMap_mk, mackeyCosetMap_mk] at h
    have hi : i = i' := by
      have h1 : ((φ g * i.out : Γ) : Γ ⧸ mackeySubgroup φ H) =
          ((φ g' * i'.out : Γ) : Γ ⧸ mackeySubgroup φ H) :=
        QuotientGroup.eq.mpr (Subgroup.mem_sup_right (QuotientGroup.eq.mp h))
      rwa [mk_mackeySubgroup_mul, mk_mackeySubgroup_mul, QuotientGroup.out_eq',
        QuotientGroup.out_eq'] at h1
    subst hi
    refine Prod.ext ?_ rfl
    change (g : G ⧸ H.comap φ) = g'
    rw [QuotientGroup.eq] at h ⊢
    rw [Subgroup.mem_comap, show φ (g⁻¹ * g') =
        i.out * ((φ g * i.out)⁻¹ * (φ g' * i.out)) * i.out⁻¹ by rw [map_mul, map_inv]; group]
    exact (inferInstance : H.Normal).conj_mem _ h _
  · intro x
    induction x using QuotientGroup.induction_on with
    | H γ =>
    let i : Γ ⧸ mackeySubgroup φ H := (γ : Γ ⧸ mackeySubgroup φ H)
    have hs : i.out⁻¹ * γ ∈ mackeySubgroup φ H := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    obtain ⟨_, ⟨g₀, rfl⟩, h, hh, hgh⟩ : i.out⁻¹ * γ ∈ ((φ.range : Set Γ) * (H : Set Γ)) := by
      rwa [← Subgroup.mul_normal]
    obtain ⟨g, hg⟩ : ∃ g, φ g = i.out * φ g₀ * i.out⁻¹ :=
      (inferInstance : φ.range.Normal).conj_mem _ ⟨g₀, rfl⟩ _
    refine ⟨((g : G ⧸ H.comap φ), i), ?_⟩
    rw [mackeyCosetMap_mk, QuotientGroup.eq]
    change φ g₀ * h = i.out⁻¹ * γ at hgh
    have hγ : γ = i.out * (φ g₀ * h) := by rw [hgh]; group
    rwa [show (φ g * i.out)⁻¹ * γ = h by rw [hγ, hg]; group]

/-- The coset map as an equivalence. -/
noncomputable def mackeyCosetEquiv : (G ⧸ H.comap φ) × (Γ ⧸ mackeySubgroup φ H) ≃ Γ ⧸ H :=
  Equiv.ofBijective _ (bijective_mackeyCosetMap φ H)

end Mackey

section MackeyModules

variable (R : Type u) [Ring R] {G Γ : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (φ : G →ₜ* Γ) (H : OpenSubgroup Γ) [(H : Subgroup Γ).Normal]
  [φ.toMonoidHom.range.Normal]

/-- The open subgroup `φ⁻¹H` of `G`. -/
abbrev mackeyOpenSubgroup : OpenSubgroup G := H.comap φ.toMonoidHom φ.continuous

/-- The index set `I = Γ/φ(G)H` of the Mackey decomposition, a finite set. -/
abbrev mackeyIndex : Type v := Γ ⧸ mackeySubgroup φ.toMonoidHom (H : Subgroup Γ)

/-- The index set `Γ/φ(G)H` is finite. -/
instance : Finite (mackeyIndex φ H) :=
  Subgroup.quotient_finite_of_isOpen _
    (Subgroup.isOpen_mono (le_sup_right : (H : Subgroup Γ) ≤ _) H.isOpen)

/-- The coefficients `N^I` of the Mackey decomposition. -/
def mackeyCoefficient (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{max u v} R)) :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{max u v} R) :=
  ⟨ModuleCat.of R (mackeyIndex φ H → Q.obj), by
    have : Module.Finite R Q.obj := Q.property
    change Module.Finite R (mackeyIndex φ H → Q.obj)
    infer_instance⟩

/-- **Mackey decomposition of a permutation module**: for `H` normal and `φ(G)` normal in `Γ`, the
restriction of `N[Γ/H]` to `G` is `(N^I)[G/φ⁻¹H]` with `I = Γ/φ(G)H`. -/
def finiteTypeContinuousModuleResCoindTrivialIso
    (Q : ObjectProperty.FullSubcategory (ModuleCat.isFG.{max u v} R)) :
    (finiteTypeContinuousModuleRes R φ).obj ((finiteTypeContinuousModuleCoind R H).obj
      ((finiteTypeContinuousModuleTrivial R Γ).obj Q)) ≅
    (finiteTypeContinuousModuleCoind R (mackeyOpenSubgroup φ H)).obj
      ((finiteTypeContinuousModuleTrivial R G).obj (mackeyCoefficient R φ H Q)) :=
  finiteTypeContinuousModuleIsoMk
    ((LinearEquiv.funCongrLeft R Q.obj (mackeyCosetEquiv φ.toMonoidHom (H : Subgroup Γ))).trans
      (LinearEquiv.curry R Q.obj _ _))
    (fun g F ↦ funext fun a ↦ funext fun i ↦ by
      change F ((φ g)⁻¹ • mackeyCosetMap φ.toMonoidHom (H : Subgroup Γ) (a, i)) =
        F (mackeyCosetMap φ.toMonoidHom (H : Subgroup Γ) (g⁻¹ • a, i))
      have h := mackeyCosetMap_smul φ.toMonoidHom (H : Subgroup Γ) g⁻¹ a i
      rw [map_inv] at h
      exact congrArg F h.symm)

end MackeyModules

end Stacks.GroupCohomology

end

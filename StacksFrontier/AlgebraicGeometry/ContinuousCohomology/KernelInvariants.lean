module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RingInvariants
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Invariants under the kernel of a quotient map, as a discrete module over the quotient

Let `R` be a ring, not necessarily commutative, and `π : Γ → Q` a continuous surjective
homomorphism from a compact group to a Hausdorff topological group, with kernel `G`. For a
continuous discrete `R`-`Γ`-module `M`, the `G`-invariants `M^G` are a continuous discrete
`R`-`Q`-module: `Γ` preserves them because `G` is normal, `G` acts trivially on them, and the
stabilizer in `Q` of an invariant is the image of its stabilizer in `Γ`, which is open (a closed
subgroup of finite index). Right deriving gives the functor

`RH⁰(G, -) : D⁺(discrete R-Γ-modules) ⥤ D⁺(discrete R-Q-modules)`

of [Stacks, Section 03VI] (`trace.tex`, the notes on homology, item (2)), with `Q` in place of
`Γ / G`.

This is the version over a ring `R` of `Stacks.GroupCohomology.normalInvariantsFunctor` (which is
over `ℤ` and lands in modules over the quotient group `Γ ⧸ N` itself); here the target group is
any `Q` with `Γ / G ≅ Q` through `π`, so that, for instance, `Q` can be the Galois group
`Aut(k̄/k)` with its Krull topology.

## Main definitions

* `Stacks.GroupCohomology.kernelInvariants`: the submodule `M^G`.
* `Stacks.GroupCohomology.kernelInvariantsFunctor`: `M ↦ M^G` as a functor
  `Mod_{R,Γ} ⥤ Mod_{R,Q}`.
* `Stacks.GroupCohomology.derivedKernelInvariants`: its right derived functor on bounded below
  derived categories.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v v' w

namespace Stacks.GroupCohomology

open scoped Stacks.DiscreteModuleTopology

section Invariants

variable (R : Type u) [Ring R] {Γ : Type v} {Q : Type v'} [Group Γ] [TopologicalSpace Γ]
  [Group Q] [TopologicalSpace Q] (π : Γ →ₜ* Q)

private lemma rho_mul' (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (g h : Γ)
    (x : M.obj.obj.V) :
    (M.obj.obj.ρ (g * h)).asHom.hom x = (M.obj.obj.ρ g).asHom.hom ((M.obj.obj.ρ h).asHom.hom x) := by
  rw [map_mul]
  rfl

/-- A morphism of `R`-`Γ`-modules commutes with the action of `Γ`. -/
private lemma hom_rho_apply {M M' : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ}
    (f : M ⟶ M') (g : Γ) (x : M.obj.obj.V) :
    f.hom.hom.hom.hom ((M.obj.obj.ρ g).asHom.hom x) = (M'.obj.obj.ρ g).asHom.hom (f.hom.hom.hom.hom x) :=
  ConcreteCategory.congr_hom (f.hom.hom.comm g) x

/-- **The invariants `M^G` under the kernel `G` of `π`.** -/
def kernelInvariants (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    Submodule R M.obj.obj.V where
  carrier := {x | ∀ g : Γ, π g = 1 → (M.obj.obj.ρ g).asHom.hom x = x}
  zero_mem' := fun _ _ ↦ map_zero _
  add_mem' := fun ha hb g hg ↦ by rw [map_add, ha g hg, hb g hg]
  smul_mem' := fun a _ hx g hg ↦ by rw [map_smul, hx g hg]

/-- `x` lies in `M^G` iff every `g` with `π g = 1` fixes it. -/
lemma mem_kernelInvariants {M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ}
    {x : M.obj.obj.V} :
    x ∈ kernelInvariants R π M ↔ ∀ g : Γ, π g = 1 → (M.obj.obj.ρ g).asHom.hom x = x :=
  Iff.rfl

/-- The invariants under the kernel of `π` are preserved by the action of `Γ`. -/
lemma rho_mem_kernelInvariants (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (γ : Γ)
    {x : M.obj.obj.V} (hx : x ∈ kernelInvariants R π M) :
    (M.obj.obj.ρ γ).asHom.hom x ∈ kernelInvariants R π M := by
  intro g hg
  have hconj : π (γ⁻¹ * g * γ) = 1 := by simp [hg]
  have hsplit : g * γ = γ * (γ⁻¹ * g * γ) := by group
  rw [← rho_mul', hsplit, rho_mul', hx _ hconj]

/-- The action of `Γ` on the invariants under the kernel of `π`. -/
def kernelInvariantsRepresentation (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    Representation R Γ (kernelInvariants R π M) where
  toFun γ := LinearMap.restrict (M.obj.obj.ρ γ).asHom.hom
    fun _ hx ↦ rho_mem_kernelInvariants R π M γ hx
  map_one' := by
    ext x
    exact congrFun (congrArg (fun f ↦ (ModuleCat.Hom.hom f.asHom).toFun) (map_one M.obj.obj.ρ)) x
  map_mul' g h := by
    ext x
    exact rho_mul' R M g h x

variable (hπ : Function.Surjective π)

/-- **The action of `Q` on the invariants under the kernel of `π`**: the kernel acts trivially, so
the action of `Γ` factors through `Γ ⧸ ker π ≃ Q`. -/
def kernelInvariantsQuotientRepresentation
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    Representation R Q (kernelInvariants R π M) :=
  (QuotientGroup.lift (π : Γ →* Q).ker (kernelInvariantsRepresentation R π M) fun g hg ↦ by
      ext x
      exact x.2 g hg).comp
    (QuotientGroup.quotientKerEquivOfSurjective (π : Γ →* Q) hπ).symm.toMonoidHom

/-- The image `π(γ)` acts on the invariants as `γ` does. -/
lemma kernelInvariantsQuotientRepresentation_apply
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (γ : Γ)
    (x : kernelInvariants R π M) :
    (kernelInvariantsQuotientRepresentation R π hπ M (π γ) x : M.obj.obj.V) =
      (M.obj.obj.ρ γ).asHom.hom x := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective (π : Γ →* Q) hπ).symm (π γ) =
      (QuotientGroup.mk γ : Γ ⧸ (π : Γ →* Q).ker) :=
    (QuotientGroup.quotientKerEquivOfSurjective (π : Γ →* Q) hπ).symm_apply_apply
      (QuotientGroup.mk γ)
  simp only [kernelInvariantsQuotientRepresentation, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, h, QuotientGroup.lift_mk]
  rfl

variable [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup Q] [T2Space Q]

/-- **The action of `Q` on `M^G` is continuous**: the stabilizer of an invariant is the image of
its stabilizer in `Γ`, a closed subgroup of finite index of `Q`, hence open. -/
lemma isContinuous_kernelInvariantsQuotientRepresentation
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    (actionOfRepresentation R Q (kernelInvariants R π M)
      (kernelInvariantsQuotientRepresentation R π hπ M)).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro x
  let S : Subgroup Γ :=
    { carrier := {g | (M.obj.obj.ρ g).asHom.hom x = x}
      mul_mem' := fun {a b} ha hb ↦ by
        change (M.obj.obj.ρ (a * b)).asHom.hom x = x
        rw [rho_mul', hb, ha]
      one_mem' := by
        change (M.obj.obj.ρ 1).asHom.hom x = x
        rw [map_one]; rfl
      inv_mem' := fun {a} ha ↦ by
        change (M.obj.obj.ρ a⁻¹).asHom.hom x = x
        conv_lhs => rw [← (show (M.obj.obj.ρ a).asHom.hom x = x from ha)]
        rw [← rho_mul', inv_mul_cancel, map_one]; rfl }
  have hSopen : IsOpen (S : Set Γ) := isOpen_stabilizer R Γ M x
  have hset : {q : Q | kernelInvariantsQuotientRepresentation R π hπ M q x = x} =
      (S.map (π : Γ →* Q) : Set Q) := by
    ext q
    obtain ⟨γ, rfl⟩ := hπ q
    refine ⟨fun h ↦ ⟨γ, ?_, rfl⟩, fun ⟨γ', hγ', hγγ'⟩ ↦ Subtype.ext ?_⟩
    · exact (kernelInvariantsQuotientRepresentation_apply R π hπ M γ x).symm.trans
        (congrArg Subtype.val h)
    · rwa [← show π γ' = π γ from hγγ', kernelInvariantsQuotientRepresentation_apply]
  rw [hset]
  have : (S.map (π : Γ →* Q)).FiniteIndex := by
    have : Finite (Γ ⧸ S) := Subgroup.quotient_finite_of_isOpen S hSopen
    have : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    rw [Subgroup.finiteIndex_iff]
    exact fun h0 ↦ (Subgroup.finiteIndex_iff.mp inferInstance)
      (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_map_dvd S hπ))
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
    ((OpenSubgroup.isClosed ⟨S, hSopen⟩).isCompact.image π.continuous).isClosed

/-- **`M^G` as a continuous discrete `R`-`Q`-module.** -/
def kernelInvariantsObj (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    Stacks.Injectives.ContinuousModule.{u, v', w} R Q :=
  ofRepresentation (kernelInvariantsQuotientRepresentation R π hπ M)
    (isContinuous_kernelInvariantsQuotientRepresentation R π hπ M)

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup Q] [T2Space Q] in
/-- A morphism of `R`-`Γ`-modules carries invariants to invariants. -/
lemma map_mem_kernelInvariants {M M' : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ}
    (f : M ⟶ M') {x : M.obj.obj.V} (hx : x ∈ kernelInvariants R π M) :
    f.hom.hom.hom.hom x ∈ kernelInvariants R π M' := by
  intro g hg
  rw [← hom_rho_apply, hx g hg]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup Q] [T2Space Q] in
/-- The restriction of a morphism of `R`-`Γ`-modules to the invariants commutes with the action
of `Q`. -/
lemma kernelInvariants_restrict_comm {M M' : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ}
    (f : M ⟶ M') (q : Q) (x : kernelInvariants R π M) :
    (LinearMap.restrict f.hom.hom.hom.hom fun _ hx ↦ map_mem_kernelInvariants R π f hx)
        (kernelInvariantsQuotientRepresentation R π hπ M q x) =
      kernelInvariantsQuotientRepresentation R π hπ M' q
        ((LinearMap.restrict f.hom.hom.hom.hom fun _ hx ↦ map_mem_kernelInvariants R π f hx)
          x) := by
  obtain ⟨γ, rfl⟩ := hπ q
  refine Subtype.ext ?_
  simp only [LinearMap.coe_restrict_apply, kernelInvariantsQuotientRepresentation_apply]
  exact hom_rho_apply R f γ x

/-- **`M ↦ M^G`, from discrete `R`-`Γ`-modules to discrete `R`-`Q`-modules**, `G = ker π`. -/
def kernelInvariantsFunctor :
    Stacks.Injectives.ContinuousModule.{u, v, w} R Γ ⥤
      Stacks.Injectives.ContinuousModule.{u, v', w} R Q where
  obj M := kernelInvariantsObj R π hπ M
  map {M M'} f := (homEquiv R Q (kernelInvariantsObj R π hπ M) (kernelInvariantsObj R π hπ M')).symm
    ⟨LinearMap.restrict f.hom.hom.hom.hom fun _ hx ↦ map_mem_kernelInvariants R π f hx,
      kernelInvariants_restrict_comm R π hπ f⟩
  map_id _ := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <|
    ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ Subtype.ext rfl
  map_comp _ _ := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <|
    ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- The functor `M ↦ M^G` acts on morphisms by restriction. -/
@[simp] lemma kernelInvariantsFunctor_map_apply
    {M M' : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ} (f : M ⟶ M')
    (x : kernelInvariants R π M) :
    (show kernelInvariants R π M' from
        ((kernelInvariantsFunctor R π hπ).map f).hom.hom.hom.hom x).1 =
      f.hom.hom.hom.hom x.1 := rfl

/-- The functor `M ↦ M^G` is additive. -/
instance kernelInvariantsFunctor_additive : (kernelInvariantsFunctor R π hπ).Additive where
  map_add := ObjectProperty.hom_ext _ <| ObjectProperty.hom_ext _ <| Action.hom_ext _ _ <|
    ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ Subtype.ext rfl

/-- **The forgetful image of `M^G` is the `G`-invariants of the restriction** to `G = ker π`:
the underlying module of `kernelInvariantsFunctor` is the module of invariants. -/
@[simp] lemma kernelInvariantsObj_V (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    (kernelInvariantsObj R π hπ M).obj.obj.V = ModuleCat.of R (kernelInvariants R π M) := rfl

end Invariants

section Derived

variable (R : Type u) [Ring R] {Γ : Type v} {Q : Type v'} [Group Γ] [TopologicalSpace Γ]
  [IsTopologicalGroup Γ] [CompactSpace Γ] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] (π : Γ →ₜ* Q) (hπ : Function.Surjective π)

attribute [local instance] HasDerivedCategory.standard

/-- **`RH⁰(G, -) : D⁺(Mod_{R,Γ}) ⥤ D⁺(Mod_{R,Q})`**, the right derived functor of the invariants
under the kernel `G` of `π`, valued in discrete `R`-`Q`-modules. The module universe contains the
group universes, so that there are enough injectives. -/
abbrev derivedKernelInvariants :
    DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ) ⥤
      DerivedCategory.Plus (Stacks.Injectives.ContinuousModule.{u, v', max u v w} R Q) :=
  haveI := Stacks.ContinuousCohomology.enoughInjectives.{u, v, w} R Γ
  (kernelInvariantsFunctor.{u, v, v', max u v w} R π hπ).rightDerivedFunctorPlus

end Derived

end Stacks.GroupCohomology

end

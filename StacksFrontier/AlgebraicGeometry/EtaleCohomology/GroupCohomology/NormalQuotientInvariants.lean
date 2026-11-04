module

public import Mathlib.Topology.Algebra.Group.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Continuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules

/-!
# Invariants under a normal subgroup as a module over the quotient group

Let `Γ` be a topological group and `N` a normal subgroup. The `N`-invariants of a discrete
`Γ`-module are a discrete `Γ ⧸ N`-module: `Γ` preserves the invariants because `N` is normal,
`N` acts trivially on them, and the stabilizer of an invariant element is open in `Γ ⧸ N`
because its preimage in `Γ` is open. Right deriving the resulting functor `H⁰(N, -)` gives
`RH⁰(N, -) : D⁺(Mod_Γ) ⥤ D⁺(Mod_{Γ⧸N})`.

Tag 03VI is the whole of Section 64.28, "Profinite groups, cohomology and homology", rather than
a single statement. The attributes in this file carry its two assertions about a normal subgroup:
that `H⁰(N, -)` takes discrete `Γ`-modules to discrete `Γ ⧸ N`-modules, and that it has a right
derived functor between bounded below derived categories.

## Main definitions

* `Stacks.GroupCohomology.normalInvariants` — the submodule of `N`-invariant elements.
* `Stacks.GroupCohomology.normalInvariantsFunctor` — the functor `H⁰(N, -)` from discrete
  `Γ`-modules to discrete `Γ ⧸ N`-modules.
* `Stacks.GroupCohomology.derivedNormalInvariantsFunctor` — the right derived functor
  `RH⁰(N, -)` on bounded below derived categories.
* `Stacks.GroupCohomology.normalInvariantsRightDerived` — the higher right derived functors of
  `H⁰(N, -)`, valued in discrete `Γ ⧸ N`-modules.

## Implementation notes

Discrete `Γ`-modules are `ContinuousGModule Γ`, continuous actions on objects of
`ModuleCat ℤ`, and an object of that category is built from a representation together with the
continuity of its action by `Stacks.GroupCohomology.ofRepresentation`. The residual action of
the quotient is obtained from the action of `Γ` on the invariants by `QuotientGroup.lift`,
whose target may be any monoid, here the endomorphism monoid of the invariants.

The invariants are the intersection of the equalizers of the action of an element of `N` with
the identity, which supplies the submodule structure; `mem_normalInvariants` is the
elementwise description used throughout.

Continuity is checked through openness of stabilizers, which for the quotient topology is
openness in `Γ` of the preimage of a stabilizer; that preimage is the stabilizer in `Γ` of the
same element, open by `Stacks.GroupCohomology.isOpen_stabilizer`.

The derived functors need enough injectives in the source, which holds when the module universe
contains the group universe, so they are stated at module universe `max u v`.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u v

namespace Stacks.GroupCohomology

/- The forgetful functor to topological spaces, giving each underlying group the discrete
topology. -/
local instance hasForget₂ModuleCatIntTopCatNormalQuotient :
    HasForget₂ (ModuleCat.{v} ℤ) TopCat.{v} :=
  { forget₂ := forget (ModuleCat.{v} ℤ) ⋙ TopCat.discrete
    forget_comp := rfl }

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] (N : Subgroup Γ)

section Invariants

variable (M : ContinuousGModule.{u, v} Γ)

/-- The action of a product of group elements on a discrete module is the composite of the two
actions. -/
private lemma rho_mul (g h : Γ) (x : M.obj.obj.V) :
    (M.obj.obj.ρ (g * h)).hom x = (M.obj.obj.ρ g).hom ((M.obj.obj.ρ h).hom x) := by
  rw [map_mul]
  rfl

/-- The submodule of elements of a discrete `Γ`-module fixed by a subgroup `N`, that is
`H⁰(N, M)`. -/
def normalInvariants : Submodule ℤ M.obj.obj.V :=
  ⨅ g : N, LinearMap.eqLocus (M.obj.obj.ρ (g : Γ)).hom LinearMap.id

/-- An element of a discrete `Γ`-module is `N`-invariant exactly when every element of `N`
fixes it. -/
lemma mem_normalInvariants {x : M.obj.obj.V} :
    x ∈ normalInvariants N M ↔ ∀ g ∈ N, (M.obj.obj.ρ g).hom x = x := by
  rw [normalInvariants, Submodule.mem_iInf]
  exact ⟨fun h g hg ↦ h ⟨g, hg⟩, fun h g ↦ h g.1 g.2⟩

/-- A morphism of discrete `Γ`-modules carries `N`-invariants to `N`-invariants. -/
lemma map_mem_normalInvariants {M M' : ContinuousGModule.{u, v} Γ} (f : M ⟶ M')
    {x : M.obj.obj.V} (hx : x ∈ normalInvariants N M) :
    f.hom.hom.hom.hom x ∈ normalInvariants N M' := by
  rw [mem_normalInvariants] at hx ⊢
  intro g hg
  have h : f.hom.hom.hom.hom ((M.obj.obj.ρ g).hom x) =
      (M'.obj.obj.ρ g).hom (f.hom.hom.hom.hom x) :=
    ConcreteCategory.congr_hom (f.hom.hom.comm g) x
  rw [← h, hx g hg]

variable [N.Normal]

/-- The invariants under a normal subgroup are preserved by the action of the whole group. -/
lemma rho_mem_normalInvariants (γ : Γ) {x : M.obj.obj.V}
    (hx : x ∈ normalInvariants N M) :
    (M.obj.obj.ρ γ).hom x ∈ normalInvariants N M := by
  rw [mem_normalInvariants] at hx ⊢
  intro g hg
  have hconj : γ⁻¹ * g * γ ∈ N := by
    simpa using ‹N.Normal›.conj_mem g hg γ⁻¹
  have hsplit : g * γ = γ * (γ⁻¹ * g * γ) := by group
  rw [← rho_mul, hsplit, rho_mul, hx _ hconj]

/-- The action of `Γ` on the `N`-invariants of a discrete `Γ`-module. -/
def normalInvariantsRepresentation : Representation ℤ Γ (normalInvariants N M) where
  toFun γ := LinearMap.restrict (M.obj.obj.ρ γ).hom
    fun _ hx ↦ rho_mem_normalInvariants N M γ hx
  map_one' := by
    ext x
    exact congrFun (congrArg (fun f ↦ (ModuleCat.Hom.hom f).toFun) (map_one M.obj.obj.ρ)) x
  map_mul' g h := by
    ext x
    exact rho_mul M g h x

/-- The action of `Γ` on the `N`-invariants is the restriction of its action on the module. -/
@[simp] lemma normalInvariantsRepresentation_apply (γ : Γ) (x : normalInvariants N M) :
    (normalInvariantsRepresentation N M γ x : M.obj.obj.V) = (M.obj.obj.ρ γ).hom x := rfl

/-- The action of `Γ ⧸ N` on the `N`-invariants of a discrete `Γ`-module: the subgroup `N` acts
trivially on them, so its action factors through the quotient. -/
def normalInvariantsQuotientRepresentation :
    Representation ℤ (Γ ⧸ N) (normalInvariants N M) :=
  QuotientGroup.lift N (normalInvariantsRepresentation N M) fun g hg ↦ by
    ext x
    exact (mem_normalInvariants N M).mp x.2 g hg

/-- The class of `γ` acts on the `N`-invariants the way `γ` acts on the module. -/
@[simp] lemma normalInvariantsQuotientRepresentation_mk (γ : Γ)
    (x : normalInvariants N M) :
    (normalInvariantsQuotientRepresentation N M (QuotientGroup.mk γ) x : M.obj.obj.V) =
      (M.obj.obj.ρ γ).hom x := rfl

variable [IsTopologicalGroup Γ]

/-- The action of `Γ ⧸ N` on the `N`-invariants of a discrete `Γ`-module is continuous for the
discrete topology: the stabilizer of an element has open preimage in `Γ`. -/
lemma isContinuous_normalInvariantsQuotientRepresentation :
    (actionOfRepresentation ℤ (Γ ⧸ N) (normalInvariants N M)
      (normalInvariantsQuotientRepresentation N M)).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro x
  refine isOpen_coinduced.mpr ?_
  show IsOpen {γ : Γ |
    normalInvariantsQuotientRepresentation N M (QuotientGroup.mk γ) x = x}
  have hpre : {γ : Γ |
        normalInvariantsQuotientRepresentation N M (QuotientGroup.mk γ) x = x} =
      {γ : Γ | (M.obj.obj.ρ γ).hom (x : M.obj.obj.V) = (x : M.obj.obj.V)} :=
    Set.ext fun _ ↦ Subtype.ext_iff
  rw [hpre]
  exact isOpen_stabilizer ℤ Γ M _

/-- The `N`-invariants of a discrete `Γ`-module, as a discrete `Γ ⧸ N`-module. -/
def normalInvariantsObj : ContinuousGModule.{u, v} (Γ ⧸ N) :=
  ofRepresentation (normalInvariantsQuotientRepresentation N M)
    (isContinuous_normalInvariantsQuotientRepresentation N M)

/-- The module underlying `H⁰(N, M)` is the submodule of `N`-invariant elements. -/
@[simp] lemma normalInvariantsObj_V :
    (normalInvariantsObj N M).obj.obj.V = ModuleCat.of ℤ (normalInvariants N M) := rfl

end Invariants

section Functor

variable [N.Normal] [IsTopologicalGroup Γ]

/-- Taking invariants under a normal subgroup `N` of a topological group `Γ` is a functor
`H⁰(N, -)` from discrete `Γ`-modules to discrete `Γ ⧸ N`-modules. -/
@[stacks 03VI "H⁰(N, -) takes discrete Γ-modules to discrete Γ/N-modules"]
def normalInvariantsFunctor :
    ContinuousGModule.{u, v} Γ ⥤ ContinuousGModule.{u, v} (Γ ⧸ N) where
  obj M := normalInvariantsObj N M
  map {M M'} f := ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom (LinearMap.restrict f.hom.hom.hom.hom
        fun _ hx ↦ map_mem_normalInvariants N f hx)
      comm := fun q ↦ by
        induction q using QuotientGroup.induction_on with
        | H γ =>
          refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
          exact ConcreteCategory.congr_hom (f.hom.hom.comm γ) x.1 })
  map_id M := by
    ext
    rfl
  map_comp f g := by
    ext
    rfl

/-- The functor `H⁰(N, -)` acts on morphisms by restriction. -/
@[simp] lemma normalInvariantsFunctor_map_apply {M M' : ContinuousGModule.{u, v} Γ}
    (f : M ⟶ M') (x : normalInvariants N M) :
    (((normalInvariantsFunctor N).map f).hom.hom.hom.hom x).1 =
      f.hom.hom.hom.hom x.1 := rfl

/-- The functor `H⁰(N, -)` is additive. -/
instance normalInvariantsFunctor_additive :
    (normalInvariantsFunctor.{u, v} N).Additive where
  map_add := by
    intros
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext rfl)

end Functor

section Derived

variable [N.Normal] [IsTopologicalGroup Γ]

attribute [local instance] HasDerivedCategory.standard

/-- The right derived functor `RH⁰(N, -) : D⁺(Mod_Γ) ⥤ D⁺(Mod_{Γ⧸N})` of taking invariants
under a normal subgroup. -/
@[stacks 03VI "the derived functor RH⁰(N, -) of the invariants functor"]
abbrev derivedNormalInvariantsFunctor :
    DerivedCategory.Plus (ContinuousGModule.{u, max u v} Γ) ⥤
      DerivedCategory.Plus (ContinuousGModule.{u, max u v} (Γ ⧸ N)) :=
  (normalInvariantsFunctor.{u, max u v} N).rightDerivedFunctorPlus

/-- The `i`-th right derived functor of taking invariants under a normal subgroup `N`, valued in
discrete `Γ ⧸ N`-modules. -/
abbrev normalInvariantsRightDerived (i : ℤ) :
    ContinuousGModule.{u, max u v} Γ ⥤ ContinuousGModule.{u, max u v} (Γ ⧸ N) :=
  (normalInvariantsFunctor.{u, max u v} N).rightDerivedPlus i

end Derived

-- The cohomological half of Section 64.28 is the construction of Tag 04JR: the right derived
-- functors of taking invariants on discrete modules over a profinite group.
add_to_stacks 03VI "the cohomology functors Hⁱ(G, -) of a profinite group on discrete modules"
  _root_.continuousGroupCohomologyFunctor
add_to_stacks 03VI "the cohomology groups Hⁱ(G, M) of a profinite group on a discrete module"
  _root_.continuousGroupCohomology

end Stacks.GroupCohomology

end

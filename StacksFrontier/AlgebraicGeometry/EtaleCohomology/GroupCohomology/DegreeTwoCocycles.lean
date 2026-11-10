module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksCore.CategoryTheory.Abelian.DeltaFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeOneCocycles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.ModuleUniverseLift
import StacksCore.Tactic.StacksAttribute

/-!
# Degree two continuous group cohomology and continuous `2`-cocycles

Let `G` be a topological group and `M` a discrete `G`-module. The group `H ²(G, M)` of
`continuousGroupCohomology` is the second right derived functor of invariants, so it carries no
description by cocycles by construction. This file supplies the comparison in degree two, in the
one direction that needs no acyclicity theorem: if every locally constant `2`-cocycle
`G × G → M` is the coboundary of a **locally constant** `1`-cochain, then `H ²(G, M) = 0`.

## Main results

* `Stacks.GroupCohomology.isZero_rightDerivedPlus_succ_of_injective`: the dimension shift
  `R ⁿ F(X₃) = 0 ⟹ R ⁿ⁺¹ F(X₁) = 0` along a short exact sequence with injective middle term.
* `Stacks.GroupCohomology.exists_sub_eq_of_isCocycle_of_injective`: **every locally constant
  `1`-cocycle with values in an injective `R`-`G`-module is a coboundary.** This is the
  degree-one acyclicity of injective objects in cocycle form, proved from injectivity alone by
  splitting the extension of the trivial module `R` that the cocycle defines.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_forall_isCoboundary`:
  `H ²(G, M) = 0` when every locally constant `2`-cocycle with values in `M` is the coboundary
  of a locally constant `1`-cochain.

## Implementation notes

**The shape of the degree-two comparison.** Choose an injective embedding `0 → M → J → Q → 0`.
Dimension shifting (`isZero_rightDerivedPlus_succ_of_injective` at `n = 1`) reduces
`H ²(G, M) = 0` to `H ¹(G, Q) = 0`, and the degree-one criterion
`isZero_continuousGroupCohomology_one_of_forall_isCoboundary` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeOneCocycles` reduces that
in turn to: every locally constant `1`-cocycle with values in `Q` is a coboundary. Given such a
cocycle `c`, lift it pointwise along the surjection `J → Q` to `b : G → J`; the lift is locally
constant because it is a set-theoretic section composed with `c`, and a locally constant map
stays locally constant after composing with an arbitrary map. The coboundary defect
`(g, h) ↦ g • b h - b (gh) + b g` of `b` takes values in `M` and is a locally constant
`2`-cocycle there, so the hypothesis trivializes it by a locally constant `x : G → M`, and
`b - x` is then an *exact* locally constant `1`-cocycle with values in `J` lifting `c`. Since
`J` is injective it is a coboundary, `b - x = g • z - z`, and the image of `z` in `Q`
trivializes `c`.

**Why a locally constant trivializing cochain is needed, and why nothing more is.** The two
ingredients of that argument beyond the degree-one criterion are exactly: local constancy of the
degree-two trivialization, which is the hypothesis; and the degree-one acyclicity of `J` *in
cocycle form*. The latter is the usual hard half of the comparison between continuous cochains
and derived functors, but in degree one it follows from injectivity alone. Given a locally
constant `1`-cocycle `β : G → J`, the module `J ⊕ R` with the twisted action
`g • (j, n) = (g • j + n β g, n)` is again a discrete `G`-module — the cocycle identity is
exactly multiplicativity of the twisted action, and local constancy of `β` makes the stabilizers
open — and `J → J ⊕ R` is a monomorphism. Injectivity of `J` splits it by a `G`-equivariant
retraction `r`, and `z := r (0, 1)` satisfies `g • z - z = β g` because `g` carries `(0, 1)` to
`(β g, 1)`. This is `exists_sub_eq_of_isCocycle_of_injective`, and it needs no coinduced module
and no acyclic-resolution theorem.

**What this does not give.** Degrees `q ≥ 3` are *not* reachable by iterating this file. The
same argument would reduce `H ³(G, M) = 0` to the statement that every locally constant
`2`-cocycle with values in an injective `J` is the coboundary of a locally constant
`1`-cochain, and the extension trick above is specific to degree one: a `2`-cocycle does not
define an extension of the trivial module by `J`. So the file stops at degree two by design,
and a client wanting degree `q` must supply the degree-`q` cocycle statement *together with* the
degree-`(q-1)` acyclicity of injective objects in cocycle form, which is not proved here for
any `q - 1 ≥ 2`.

**Why the twist is built over an arbitrary ring.** The twisted module and everything proved
about it are stated for `R`-`G`-modules rather than only for `G`-modules, i.e. `R = ℤ`. This is
not generality for its own sake: on the carrier of an object of `ModuleCat ℤ` the scalar action
`n • x` picks up `AddCommGroup.toIntModule` rather than the module structure of the object, so
at `R = ℤ` written literally the elementary scalar lemmas (`add_smul`, `smul_zero`, `one_smul`)
do not even typecheck against the goals they are meant to close. With `R` a variable there is no
such diamond, and the `R = ℤ` case is an instance of the general statement.

**Universes.** The degree-`i` group `continuousGroupCohomology.{u, v} G i` takes coefficients in
`ContinuousGModule.{u, max u v} G` for `G : Type u`, and every statement below is polymorphic in
both `u` and `v`, exactly as the degree-one criterion is.

## References

* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the derived-functor
  groups the criterion is about.
* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the `R`-`G`-modules the
  twisted extension is built in.
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T): the long exact sequence
  of a `δ`-functor, of which the dimension shift here is the standard consequence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ContinuousCohomology

open scoped Stacks.DiscreteModuleTopology

universe t u v w

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.GroupCohomology

/-! ### Local constancy detected after an injection -/

/-- A function is locally constant as soon as it becomes so after composing with an injection:
each fibre of `f` is the preimage under `u ∘ f` of the image under `u` of that fibre. -/
theorem isLocallyConstant_of_comp_injective {X A B : Type*} [TopologicalSpace X] {u : A → B}
    (hu : Function.Injective u) {f : X → A} (h : IsLocallyConstant fun x ↦ u (f x)) :
    IsLocallyConstant f :=
  IsLocallyConstant.desc f u h hu

/-! ### Dimension shifting -/

section Derived

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- **Dimension shifting for a right derived functor.** If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is short
exact with `X₂` injective and `R ⁿ F(X₃) = 0`, then `R ⁿ⁺¹ F(X₁) = 0`: the connecting morphism
`R ⁿ F(X₃) ⟶ R ⁿ⁺¹ F(X₁)` is an epimorphism because `R ⁿ⁺¹ F(X₂) = 0`, and it is zero because
its source is. -/
theorem isZero_rightDerivedPlus_succ_of_injective (F : C ⥤ D) [F.Additive]
    {S : ShortComplex C} (hS : S.ShortExact) (hinj : Injective S.X₂) (n : ℕ)
    (h : IsZero ((F.rightDerivedPlus ((n : ℕ) : ℤ)).obj S.X₃)) :
    IsZero ((F.rightDerivedPlus ((n + 1 : ℕ) : ℤ)).obj S.X₁) := by
  let Δ := Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor F
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure F)
    (Stacks.DerivedIndexing.canonicalδ F) (fun _ _ ↦ rfl)
  have hJ : IsZero ((F.rightDerivedPlus ((n + 1 : ℕ) : ℤ)).obj S.X₂) :=
    Functor.isZero_rightDerivedPlus_obj_injective F ((n + 1 : ℕ) : ℤ)
      (by exact_mod_cast Nat.succ_ne_zero n) S.X₂
  have h1 : (Δ.functor (n + 1)).map S.f = 0 := hJ.eq_of_tgt _ _
  have hepi : Epi (Δ.δ hS n) := Δ.epi_δ_of_map_f_eq_zero hS n h1
  exact (IsZero.of_epi_eq_zero (Δ.δ hS n) (h.eq_of_src _ _) :)

end Derived

/-! ### The extension of the trivial module defined by a `1`-cocycle -/

section Twist

variable {R : Type t} [Ring R] {G : Type u} [Group G]
  {V : Type w} [AddCommGroup V] [Module R V]

/-- The identity of `G` acts as the identity. -/
private theorem rep_one_apply (ρ : Representation R G V) (x : V) : ρ 1 x = x := by
  rw [map_one]; rfl

/-- A product of group elements acts as the composite. -/
private theorem rep_mul_apply (ρ : Representation R G V) (g h : G) (x : V) :
    ρ (g * h) x = ρ g (ρ h x) := by rw [map_mul]; rfl

/-- A `1`-cocycle vanishes at the identity. -/
private theorem isCocycle_apply_one (ρ : Representation R G V) (β : G → V)
    (hβ : ∀ g h : G, β (g * h) = ρ g (β h) + β g) : β 1 = 0 := by
  have h := hβ 1 1
  rw [mul_one, rep_one_apply] at h
  simpa using h

/-- The `R`-linear endomorphism of `V ⊕ R` by which `g` acts in the extension of the trivial
module `R` by `V` determined by a `1`-cocycle `β`. -/
private def twistLinear (ρ : Representation R G V) (β : G → V) (g : G) :
    (V × R) →ₗ[R] (V × R) where
  toFun p := (ρ g p.1 + p.2 • β g, p.2)
  map_add' p q := by
    refine Prod.ext ?_ rfl
    change ρ g (p.1 + q.1) + (p.2 + q.2) • β g =
      (ρ g p.1 + p.2 • β g) + (ρ g q.1 + q.2 • β g)
    rw [map_add, add_smul]
    abel
  map_smul' c p := by
    refine Prod.ext ?_ rfl
    change ρ g (c • p.1) + (c • p.2) • β g = c • (ρ g p.1 + p.2 • β g)
    rw [map_smul, smul_add, smul_smul, smul_eq_mul]

/-- The twisted action of `G` on `V ⊕ R` attached to a `1`-cocycle `β`: the cocycle identity for
`β` is exactly multiplicativity of `g ↦ twistLinear ρ β g`. -/
private def twistRepresentation (ρ : Representation R G V) (β : G → V)
    (hβ : ∀ g h : G, β (g * h) = ρ g (β h) + β g) : Representation R G (V × R) where
  toFun g := twistLinear ρ β g
  map_one' := by
    refine LinearMap.ext fun p ↦ Prod.ext ?_ rfl
    change ρ 1 p.1 + p.2 • β 1 = p.1
    rw [isCocycle_apply_one ρ β hβ, smul_zero, add_zero, rep_one_apply]
  map_mul' g h := by
    refine LinearMap.ext fun p ↦ Prod.ext ?_ rfl
    change ρ (g * h) p.1 + p.2 • β (g * h) = ρ g (ρ h p.1 + p.2 • β h) + p.2 • β g
    rw [rep_mul_apply, hβ g h, smul_add, map_add, map_smul]
    abel

@[simp] private theorem twistRepresentation_apply (ρ : Representation R G V) (β : G → V)
    (hβ : ∀ g h : G, β (g * h) = ρ g (β h) + β g) (g : G) (p : V × R) :
    twistRepresentation ρ β hβ g p = (ρ g p.1 + p.2 • β g, p.2) := rfl

/-- On the submodule `V` the twisted action is the original action. -/
private theorem twistRepresentation_apply_inl (ρ : Representation R G V) (β : G → V)
    (hβ : ∀ g h : G, β (g * h) = ρ g (β h) + β g) (g : G) (x : V) :
    twistRepresentation ρ β hβ g (x, 0) = (ρ g x, 0) := by
  refine Prod.ext ?_ rfl
  change ρ g x + (0 : R) • β g = ρ g x
  rw [zero_smul, add_zero]

/-- The twisted action moves `(0, 1)` by the cocycle: this one computation is what makes the
extension nontrivial, and is where the coboundary comes from. -/
private theorem twistRepresentation_apply_inr (ρ : Representation R G V) (β : G → V)
    (hβ : ∀ g h : G, β (g * h) = ρ g (β h) + β g) (g : G) :
    twistRepresentation ρ β hβ g ((0 : V), (1 : R)) = (β g, (1 : R)) := by
  refine Prod.ext ?_ rfl
  change ρ g 0 + (1 : R) • β g = β g
  rw [map_zero, one_smul, zero_add]

omit [Module R V] in
private theorem inr_split (v : V) : ((v, (1 : R)) : V × R) = (v, 0) + (0, 1) := by
  refine Prod.ext ?_ ?_
  · change v = v + 0
    rw [add_zero]
  · change (1 : R) = 0 + 1
    rw [zero_add]

variable [TopologicalSpace G]

/-- **The twisted action is continuous** when `β` is locally constant and the orbit maps of the
original action are: the stabilizer of `(v, n)` is a fibre of the locally constant function
`g ↦ ρ g v + n β g`. -/
private theorem isOpen_twist_stabilizer (ρ : Representation R G V) (β : G → V)
    (hβ : ∀ g h : G, β (g * h) = ρ g (β h) + β g) (hloc : IsLocallyConstant β)
    (horb : ∀ z : V, IsLocallyConstant fun g : G ↦ ρ g z) (p : V × R) :
    IsOpen {g : G | twistRepresentation ρ β hβ g p = p} := by
  have hφ : IsLocallyConstant fun g : G ↦ ρ g p.1 + p.2 • β g :=
    (horb p.1).comp₂ (hloc.comp fun z ↦ p.2 • z) (· + ·)
  have hset : {g : G | twistRepresentation ρ β hβ g p = p} =
      (fun g : G ↦ ρ g p.1 + p.2 • β g) ⁻¹' {p.1} := by
    ext g
    exact ⟨fun h ↦ congrArg Prod.fst h, fun h ↦ Prod.ext h rfl⟩
  rw [hset]
  exact hφ _

end Twist

/-! ### Degree one acyclicity of an injective discrete module, in cocycle form -/

section Injective

variable {R : Type t} [Ring R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The extension of the trivial `R`-`G`-module `R` by `N` defined by a locally constant
`1`-cocycle `β`: the module `N ⊕ R` with `g • (n, c) = (g • n + c β g, c)`. -/
private def twistModule (N : Stacks.Injectives.ContinuousModule.{t, u, max w t} R G)
    (β : G → N.obj.obj.V) (hloc : IsLocallyConstant β)
    (hβ : ∀ g h : G, β (g * h) = (N.obj.obj.ρ g).asHom.hom (β h) + β g) :
    Stacks.Injectives.ContinuousModule.{t, u, max w t} R G :=
  ofRepresentation (twistRepresentation (representationOfModule N) β hβ)
    (by
      rw [isContinuous_actionOfRepresentation_iff]
      exact fun p ↦ isOpen_twist_stabilizer (representationOfModule N) β hβ hloc
        (fun z ↦ isLocallyConstant_ρ_apply N z) p)

/-- The inclusion of `N` into the extension defined by `β`. -/
private def twistIncl (N : Stacks.Injectives.ContinuousModule.{t, u, max w t} R G)
    (β : G → N.obj.obj.V) (hloc : IsLocallyConstant β)
    (hβ : ∀ g h : G, β (g * h) = (N.obj.obj.ρ g).asHom.hom (β h) + β g) :
    N ⟶ twistModule N β hloc hβ :=
  (homEquiv R G N (twistModule N β hloc hβ)).symm
    ⟨LinearMap.inl R N.obj.obj.V R,
      fun g x ↦ (twistRepresentation_apply_inl (representationOfModule N) β hβ g x).symm⟩

/-- **Every locally constant `1`-cocycle with values in an injective `R`-`G`-module is a
coboundary.** This is the degree-one acyclicity of injective objects in cocycle form, and it
needs nothing but injectivity: the cocycle `β` makes `N ⊕ R` an `R`-`G`-module containing `N`,
injectivity of `N` splits that inclusion by a `G`-equivariant retraction `r`, and
`z := r (0, 1)` satisfies `g • z - z = β g` because `g` carries `(0, 1)` to `(β g, 1)`. -/
theorem exists_sub_eq_of_isCocycle_of_injective
    (N : Stacks.Injectives.ContinuousModule.{t, u, max w t} R G) [Injective N]
    {β : G → N.obj.obj.V} (hloc : IsLocallyConstant β)
    (hβ : ∀ g h : G, β (g * h) = (N.obj.obj.ρ g).asHom.hom (β h) + β g) :
    ∃ z : N.obj.obj.V, ∀ g : G, (N.obj.obj.ρ g).asHom.hom z - z = β g := by
  have hmono : Mono (twistIncl N β hloc hβ) := by
    refine (continuousModuleToAction.{t, u, max w t} R G ⋙
      Action.forget (ModuleCat.{max w t} R) G).mono_of_mono_map ?_
    rw [ModuleCat.mono_iff_injective]
    intro x y hxy
    have hpair : ((x, 0) : N.obj.obj.V × R) = ((y, 0) : N.obj.obj.V × R) := hxy
    exact (Prod.ext_iff.mp hpair).1
  let r : twistModule N β hloc hβ ⟶ N := Injective.factorThru (𝟙 N) (twistIncl N β hloc hβ)
  have hr : twistIncl N β hloc hβ ≫ r = 𝟙 N :=
    Injective.comp_factorThru (𝟙 N) (twistIncl N β hloc hβ)
  have hsection : ∀ x : N.obj.obj.V, r.hom.hom.hom.hom ((x, 0) : N.obj.obj.V × R) = x :=
    fun x ↦ congrArg (fun φ : N ⟶ N ↦ φ.hom.hom.hom.hom x) hr
  refine ⟨r.hom.hom.hom.hom ((0, 1) : N.obj.obj.V × R), fun g ↦ ?_⟩
  have hequiv : r.hom.hom.hom.hom (((twistModule N β hloc hβ).obj.obj.ρ g).asHom.hom
        ((0, 1) : N.obj.obj.V × R)) =
      (N.obj.obj.ρ g).asHom.hom (r.hom.hom.hom.hom ((0, 1) : N.obj.obj.V × R)) :=
    ConcreteCategory.congr_hom (r.hom.hom.comm g) _
  have hmove : ((twistModule N β hloc hβ).obj.obj.ρ g).asHom.hom ((0, 1) : N.obj.obj.V × R) =
      ((β g, 1) : N.obj.obj.V × R) :=
    twistRepresentation_apply_inr (representationOfModule N) β hβ g
  have hsplit : r.hom.hom.hom.hom ((β g, 1) : N.obj.obj.V × R) =
      β g + r.hom.hom.hom.hom ((0, 1) : N.obj.obj.V × R) :=
    (congrArg r.hom.hom.hom.hom (inr_split (β g))).trans
      ((map_add r.hom.hom.hom.hom ((β g, 0) : N.obj.obj.V × R)
          ((0, 1) : N.obj.obj.V × R)).trans
        (congrArg (· + r.hom.hom.hom.hom ((0, 1) : N.obj.obj.V × R)) (hsection (β g))))
  have key : (N.obj.obj.ρ g).asHom.hom (r.hom.hom.hom.hom ((0, 1) : N.obj.obj.V × R)) =
      β g + r.hom.hom.hom.hom ((0, 1) : N.obj.obj.V × R) :=
    hequiv.symm.trans ((congrArg r.hom.hom.hom.hom hmove).trans hsplit)
  rw [key]
  abel

end Injective

/-! ### Degree two continuous group cohomology -/

section Two

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Acting by a continuously varying group element on a locally constant family is locally
constant.** The preimage of a set is the union, over the values `z` of the family, of the
intersection of the fibre of the family at `z` with the preimage of the orbit map of `z`. -/
theorem isLocallyConstant_ρ_apply₂ {X : Type*} [TopologicalSpace X]
    (N : ContinuousGModule.{u, w} G) {γ : X → G} (hγ : Continuous γ)
    {ζ : X → N.obj.obj.V} (hζ : IsLocallyConstant ζ) :
    IsLocallyConstant fun x ↦ (N.obj.obj.ρ (γ x)).asHom.hom (ζ x) := by
  intro s
  have hset : (fun x ↦ (N.obj.obj.ρ (γ x)).asHom.hom (ζ x)) ⁻¹' s =
      ⋃ z : N.obj.obj.V,
        γ ⁻¹' ((fun g : G ↦ (N.obj.obj.ρ g).asHom.hom z) ⁻¹' s) ∩ ζ ⁻¹' {z} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun hx ↦ ⟨ζ x, hx, rfl⟩, fun ⟨_, hz, hzx⟩ ↦ hzx ▸ hz⟩
  rw [hset]
  exact isOpen_iUnion fun z ↦
    (hγ.isOpen_preimage _ (isLocallyConstant_ρ_apply N z s)).inter (hζ _)

/-- **Degree two continuous group cohomology vanishes when every continuous `2`-cocycle is the
coboundary of a continuous `1`-cochain.** The cocycle condition is
`d(g₁g₂, g₃) + d(g₁, g₂) = g₁ • d(g₂, g₃) + d(g₁, g₂g₃)` and the coboundary condition is
`d(g₁, g₂) = g₁ • x(g₂) - x(g₁g₂) + x(g₁)` with `x` locally constant; `H ²(G, M)` is the
derived functor group of Stacks 04JR.

Local constancy of the trivializing cochain `x` is essential and is *not* implied by the bare
existence of a trivialization: it is what makes `b - x` in the proof a continuous cochain, and
the continuous cochains are what the derived-functor group sees. -/
theorem isZero_continuousGroupCohomology_two_of_forall_isCoboundary
    (M : ContinuousGModule.{u, max u v} G)
    (hM : ∀ d : G × G → M.obj.obj.V, IsLocallyConstant d →
        (∀ g₁ g₂ g₃ : G, d (g₁ * g₂, g₃) + d (g₁, g₂) =
          (M.obj.obj.ρ g₁).asHom.hom (d (g₂, g₃)) + d (g₁, g₂ * g₃)) →
        ∃ x : G → M.obj.obj.V, IsLocallyConstant x ∧
          ∀ g₁ g₂ : G, (M.obj.obj.ρ g₁).asHom.hom (x g₂) - x (g₁ * g₂) + x g₁ = d (g₁, g₂)) :
    IsZero (continuousGroupCohomology.{u, v} G 2 M) := by
  let U := continuousGModuleUnderlying.{u, max u v} G
  let P : InjectivePresentation M := Classical.choice (EnoughInjectives.presentation M)
  have : Injective P.J := P.injective
  have : Mono P.f := P.mono
  let S : ShortComplex (ContinuousGModule.{u, max u v} G) :=
    ShortComplex.mk P.f (cokernel.π P.f) (cokernel.condition P.f)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel P.f)) inferInstance inferInstance
  have hSu : (S.map U).ShortExact := hS.map_of_exact U
  let fl : M.obj.obj.V →ₗ[ℤ] P.J.obj.obj.V := P.f.hom.hom.hom.hom
  let gl : P.J.obj.obj.V →ₗ[ℤ] (cokernel P.f).obj.obj.V :=
    (cokernel.π P.f).hom.hom.hom.hom
  have hgsurj : Function.Surjective gl := hSu.moduleCat_surjective_g
  have hfinj : Function.Injective fl := hSu.moduleCat_injective_f
  have hexact : ∀ z : P.J.obj.obj.V, gl z = 0 → ∃ m : M.obj.obj.V, fl m = z :=
    (ShortComplex.moduleCat_exact_iff _).mp hSu.exact
  have hgfl : ∀ m : M.obj.obj.V, gl (fl m) = 0 :=
    fun m ↦ ShortComplex.moduleCat_zero_apply (S.map U) m
  have hfeq : ∀ (g : G) (m : M.obj.obj.V),
      fl ((M.obj.obj.ρ g).asHom.hom m) = (P.J.obj.obj.ρ g).asHom.hom (fl m) :=
    fun g m ↦ ConcreteCategory.congr_hom (P.f.hom.hom.comm g) m
  have hgeq : ∀ (g : G) (z : P.J.obj.obj.V),
      gl ((P.J.obj.obj.ρ g).asHom.hom z) = ((cokernel P.f).obj.obj.ρ g).asHom.hom (gl z) :=
    fun g z ↦ ConcreteCategory.congr_hom ((cokernel.π P.f).hom.hom.comm g) z
  have hmulJ : ∀ (g₁ g₂ : G) (z : P.J.obj.obj.V), (P.J.obj.obj.ρ (g₁ * g₂)).asHom.hom z =
      (P.J.obj.obj.ρ g₁).asHom.hom ((P.J.obj.obj.ρ g₂).asHom.hom z) := by
    intro g₁ g₂ z
    rw [map_mul]; rfl
  refine isZero_rightDerivedPlus_succ_of_injective
    (continuousGModuleInvariants.{u, max u v} G) hS P.injective 1 ?_
  refine isZero_continuousGroupCohomology_one_of_forall_isCoboundary (cokernel P.f) ?_
  intro c hcloc hccoc
  obtain ⟨sec, hsec⟩ := hgsurj.hasRightInverse
  have hbloc : IsLocallyConstant fun g : G ↦ sec (c g) := hcloc.comp sec
  have hb : ∀ g : G, gl (sec (c g)) = c g := fun g ↦ hsec (c g)
  have hker : ∀ p : G × G, ∃ m : M.obj.obj.V, fl m =
      (P.J.obj.obj.ρ p.1).asHom.hom (sec (c p.2)) - sec (c (p.1 * p.2)) + sec (c p.1) := by
    intro p
    refine hexact _ ?_
    rw [map_add, map_sub, hgeq, hb, hb, hb, hccoc p.1 p.2]
    abel
  choose d hd using hker
  have hDloc : IsLocallyConstant fun p : G × G ↦
      (P.J.obj.obj.ρ p.1).asHom.hom (sec (c p.2)) - sec (c (p.1 * p.2)) + sec (c p.1) :=
    ((isLocallyConstant_ρ_apply₂ P.J continuous_fst
          (hbloc.comp_continuous continuous_snd)).comp₂
        (hbloc.comp_continuous (continuous_fst.mul continuous_snd)) (· - ·)).comp₂
      (hbloc.comp_continuous continuous_fst) (· + ·)
  have hdloc : IsLocallyConstant d :=
    isLocallyConstant_of_comp_injective hfinj (by simp only [hd]; exact hDloc)
  have hdcoc : ∀ g₁ g₂ g₃ : G, d (g₁ * g₂, g₃) + d (g₁, g₂) =
      (M.obj.obj.ρ g₁).asHom.hom (d (g₂, g₃)) + d (g₁, g₂ * g₃) := by
    intro g₁ g₂ g₃
    refine hfinj ?_
    simp only [map_add, hfeq, hd, map_sub, mul_assoc, hmulJ]
    abel
  obtain ⟨x, hxloc, hx⟩ := hM d hdloc hdcoc
  have hβloc : IsLocallyConstant fun g : G ↦ sec (c g) - fl (x g) :=
    hbloc.comp₂ (hxloc.comp fun m ↦ fl m) (· - ·)
  have hβcoc : ∀ g₁ g₂ : G, sec (c (g₁ * g₂)) - fl (x (g₁ * g₂)) =
      (P.J.obj.obj.ρ g₁).asHom.hom (sec (c g₂) - fl (x g₂)) + (sec (c g₁) - fl (x g₁)) := by
    intro g₁ g₂
    have hbfac : sec (c (g₁ * g₂)) =
        (P.J.obj.obj.ρ g₁).asHom.hom (sec (c g₂)) + sec (c g₁) - fl (d (g₁, g₂)) := by
      rw [hd (g₁, g₂)]; abel
    have hxfac : fl (x (g₁ * g₂)) =
        (P.J.obj.obj.ρ g₁).asHom.hom (fl (x g₂)) + fl (x g₁) - fl (d (g₁, g₂)) := by
      rw [← hx g₁ g₂, map_add, map_sub, hfeq]; abel
    rw [map_sub, hbfac, hxfac]
    abel
  obtain ⟨z, hz⟩ := exists_sub_eq_of_isCocycle_of_injective P.J hβloc hβcoc
  refine ⟨gl z, fun g ↦ ?_⟩
  rw [← hgeq g z, ← map_sub, hz g, map_sub, hgfl, hb g, sub_zero]

end Two

end Stacks.GroupCohomology

end

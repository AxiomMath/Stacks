module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.LocallyConstant.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Limit topologies of inverse systems of discrete spaces

Let `(G_i)` be an inverse system of discrete spaces with limit `G = lim G_i`. The *limit
topology* on `G` ([Stacks, Section 07E7]) is the coarsest topology making every projection
`G → G_i` continuous. For a type `X` with maps `p i : X → A i` this file works with the topology

`⨅ i, TopologicalSpace.induced (p i) ⊥`,

which is the limit topology when `X` is the limit and the `p i` are its projections. This is the
spelling the library already uses for limit topologies (for instance
`Stacks.AdicLimit.limitTopology_eq_iInf_induced_proj`), so the results below apply to them
directly.

The point of the file is a factorisation criterion for continuity: a map `f : X → Y` between two
such spaces is continuous as soon as each `q j ∘ f` is determined by finitely many of the `p i`.
Every comparison map between limits that arises in practice is of this kind: an isomorphism of
inverse systems, a morphism of pro-systems (whose components `X_{m(n)} → Y_n` shift the index),
or the passage from `Hom_k(colim V_n, k)` to `lim Hom_k(V_n, k)`
(`StacksFrontier.Topology.Algebra.Module.DualLimitTopology`).

## Main results

* `continuous_iInf_induced_bot_of_finite`: the factorisation criterion for continuity.
* `continuous_iInf_induced_bot_of_forall_exists`: the case of one index at a time.
* `isTopologicalAddGroup_iInf_induced_bot`: a limit of discrete groups is a topological group.
* `iInf_induced_bot_eq_bot_of_finite`: the limit topology is discrete when finitely many of the
  maps are jointly injective.
* `isHomeomorph_iInf_induced_bot_of_finite`, `isHomeomorph_iInf_induced_bot_of_forall_exists`:
  a bijection satisfying the criterion in both directions is a homeomorphism.
* `ModuleCat.isHomeomorph_conePointsIsoOfNatIso`: the isomorphism between the limits of two
  isomorphic diagrams of modules is a homeomorphism for the limit topologies.
* `LinearEquiv.toContinuousLinearEquivOfIsHomeomorph`: a linear equivalence that is a
  homeomorphism, as a continuous linear equivalence.

## References

* [Stacks Project, Section 07E7](https://stacks.math.columbia.edu/tag/07E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology

universe w w' u v

section Factor

variable {X Y : Type*} {ι κ : Type*} {A : ι → Type*} {B : κ → Type*}

/-- Fibres of `p i` are open for the topology induced by the maps `p i` into discrete spaces. -/
private theorem isOpen_preimage_singleton_iInf_induced_bot (p : ∀ i, X → A i) (i : ι)
    (a : A i) : IsOpen[⨅ i, TopologicalSpace.induced (p i) ⊥] (p i ⁻¹' {a}) :=
  let : TopologicalSpace (A i) := ⊥
  have : DiscreteTopology (A i) := ⟨rfl⟩
  let : TopologicalSpace X := ⨅ i, TopologicalSpace.induced (p i) ⊥
  have hpi : Continuous (p i) := continuous_iInf_dom continuous_induced_dom
  (isOpen_discrete {a}).preimage hpi

/-- **Continuity for limit topologies.** Let `X` and `Y` carry the topologies induced by maps
`p i : X → A i` and `q j : Y → B j` into discrete spaces. A map `f : X → Y` is continuous as soon
as, for every `j`, the value `q j (f x)` depends only on finitely many of the `p i x`. -/
theorem continuous_iInf_induced_bot_of_finite (p : ∀ i, X → A i) (q : ∀ j, Y → B j)
    (f : X → Y)
    (h : ∀ j, ∃ s : Set ι, s.Finite ∧
      ∀ x y, (∀ i ∈ s, p i x = p i y) → q j (f x) = q j (f y)) :
    Continuous[⨅ i, TopologicalSpace.induced (p i) ⊥,
      ⨅ j, TopologicalSpace.induced (q j) ⊥] f := by
  let tX : TopologicalSpace X := ⨅ i, TopologicalSpace.induced (p i) ⊥
  refine continuous_iInf_rng.2 fun j => continuous_induced_rng.2 ?_
  let : TopologicalSpace (B j) := ⊥
  obtain ⟨s, hs, hsq⟩ := h j
  refine (IsLocallyConstant.iff_eventually_eq _ |>.2 fun x => ?_).continuous
  have hopen : IsOpen {y | ∀ i ∈ s, p i y = p i x} := by
    simp only [Set.ofPred_forall]
    exact hs.isOpen_biInter fun i _ => isOpen_preimage_singleton_iInf_induced_bot p i (p i x)
  filter_upwards [hopen.mem_nhds fun _ _ => rfl] with y hy using hsq y x hy

/-- **Continuity for limit topologies, one index at a time.** With `X` and `Y` as in
`continuous_iInf_induced_bot_of_finite`, a map `f : X → Y` is continuous as soon as each
`q j ∘ f` factors through some `p i`. -/
theorem continuous_iInf_induced_bot_of_forall_exists (p : ∀ i, X → A i) (q : ∀ j, Y → B j)
    (f : X → Y) (h : ∀ j, ∃ i, ∃ g : A i → B j, ∀ x, q j (f x) = g (p i x)) :
    Continuous[⨅ i, TopologicalSpace.induced (p i) ⊥,
      ⨅ j, TopologicalSpace.induced (q j) ⊥] f := by
  refine continuous_iInf_induced_bot_of_finite p q f fun j => ?_
  obtain ⟨i, g, hg⟩ := h j
  exact ⟨{i}, Set.finite_singleton i, fun x y hxy => by
    rw [hg, hg, hxy i rfl]⟩

/-- **Discreteness of a limit topology.** The topology induced by maps `p i : X → A i` into
discrete spaces is discrete as soon as finitely many of the `p i` are jointly injective; for
instance, the limit of an inverse system that is essentially constant at a finite stage. -/
@[ega "0 3.8.1" "more general"]
theorem iInf_induced_bot_eq_bot_of_finite (p : ∀ i, X → A i) {s : Set ι} (hs : s.Finite)
    (h : ∀ x y, (∀ i ∈ s, p i x = p i y) → x = y) :
    (⨅ i, TopologicalSpace.induced (p i) ⊥) = ⊥ := by
  let tX : TopologicalSpace X := ⨅ i, TopologicalSpace.induced (p i) ⊥
  refine (discreteTopology_iff_isOpen_singleton.2 fun x => ?_).eq_bot
  have : {x} = ⋂ i ∈ s, p i ⁻¹' {p i x} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun hy _ _ => hy ▸ rfl, fun hy => h y x hy⟩
  rw [this]
  exact hs.isOpen_biInter fun i _ => isOpen_preimage_singleton_iInf_induced_bot p i (p i x)

/-- **Homeomorphisms between limit topologies.** A bijection `e : X ≃ Y` satisfying the criterion
of `continuous_iInf_induced_bot_of_finite` in both directions is a homeomorphism for the
topologies induced by the `p i` and the `q j`. -/
theorem isHomeomorph_iInf_induced_bot_of_finite (p : ∀ i, X → A i) (q : ∀ j, Y → B j)
    (e : X ≃ Y)
    (h : ∀ j, ∃ s : Set ι, s.Finite ∧
      ∀ x y, (∀ i ∈ s, p i x = p i y) → q j (e x) = q j (e y))
    (h' : ∀ i, ∃ s : Set κ, s.Finite ∧
      ∀ x y, (∀ j ∈ s, q j x = q j y) → p i (e.symm x) = p i (e.symm y)) :
    letI := ⨅ i, TopologicalSpace.induced (p i) ⊥
    letI := ⨅ j, TopologicalSpace.induced (q j) ⊥
    IsHomeomorph e :=
  let := ⨅ i, TopologicalSpace.induced (p i) ⊥
  let := ⨅ j, TopologicalSpace.induced (q j) ⊥
  (Homeomorph.mk e (continuous_iInf_induced_bot_of_finite p q e h)
    (continuous_iInf_induced_bot_of_finite q p e.symm h')).isHomeomorph

/-- **Homeomorphisms between limit topologies, one index at a time.** A bijection `e : X ≃ Y`
such that each `q j ∘ e` factors through some `p i` and each `p i ∘ e.symm` through some `q j`
is a homeomorphism. This covers the isomorphism of limits induced by an isomorphism, or a
pro-isomorphism, of inverse systems. -/
theorem isHomeomorph_iInf_induced_bot_of_forall_exists (p : ∀ i, X → A i)
    (q : ∀ j, Y → B j) (e : X ≃ Y)
    (h : ∀ j, ∃ i, ∃ g : A i → B j, ∀ x, q j (e x) = g (p i x))
    (h' : ∀ i, ∃ j, ∃ g : B j → A i, ∀ y, p i (e.symm y) = g (q j y)) :
    letI := ⨅ i, TopologicalSpace.induced (p i) ⊥
    letI := ⨅ j, TopologicalSpace.induced (q j) ⊥
    IsHomeomorph e :=
  let := ⨅ i, TopologicalSpace.induced (p i) ⊥
  let := ⨅ j, TopologicalSpace.induced (q j) ⊥
  (Homeomorph.mk e (continuous_iInf_induced_bot_of_forall_exists p q e h)
    (continuous_iInf_induced_bot_of_forall_exists q p e.symm h')).isHomeomorph

/-- **A limit of discrete groups is a topological group** ([Stacks, Section 07E7]): the
topology induced by additive maps `p i : M → N i` into discrete groups is a group topology. -/
theorem isTopologicalAddGroup_iInf_induced_bot {M : Type*} [AddGroup M] {N : ι → Type*}
    [∀ i, AddGroup (N i)] (p : ∀ i, M →+ N i) :
    @IsTopologicalAddGroup M (⨅ i, TopologicalSpace.induced (p i) ⊥) _ :=
  isTopologicalAddGroup_iInf fun i =>
    let : TopologicalSpace (N i) := ⊥
    have : DiscreteTopology (N i) := ⟨rfl⟩
    isTopologicalAddGroup_induced (p i)

end Factor

/-- A linear equivalence whose underlying map is a homeomorphism, as a continuous linear
equivalence. -/
def LinearEquiv.toContinuousLinearEquivOfIsHomeomorph {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [AddCommMonoid N] [Module R N]
    [TopologicalSpace N] (e : M ≃ₗ[R] N) (he : IsHomeomorph e) : M ≃L[R] N where
  toLinearEquiv := e
  continuous_toFun := he.continuous
  continuous_invFun := by
    have h : (e.symm : N → M) = (he.homeomorph e).symm := funext fun y =>
      e.injective ((e.apply_symm_apply y).trans ((he.homeomorph e).apply_symm_apply y).symm)
    change Continuous e.symm
    rw [h]
    exact (he.homeomorph e).symm.continuous

/-- The underlying function of `e.toContinuousLinearEquivOfIsHomeomorph he` is `e`. -/
@[simp]
theorem LinearEquiv.coe_toContinuousLinearEquivOfIsHomeomorph {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M] [AddCommMonoid N] [Module R N]
    [TopologicalSpace N] (e : M ≃ₗ[R] N) (he : IsHomeomorph e) :
    ⇑(e.toContinuousLinearEquivOfIsHomeomorph he) = e :=
  rfl

namespace ModuleCat

variable {R : Type u} [Ring R] {J : Type w} [Category.{w'} J]

/-- **Isomorphic inverse systems have homeomorphic limits.** For an isomorphism `α : F ≅ G` of
diagrams of `R`-modules and limit cones `c` of `F` and `d` of `G`, the induced isomorphism
`c.pt ≅ d.pt` is a homeomorphism for the limit topologies, every term carrying the discrete
topology. -/
theorem isHomeomorph_conePointsIsoOfNatIso {F G : J ⥤ ModuleCat.{v} R} {c : Cone F}
    {d : Cone G} (hc : IsLimit c) (hd : IsLimit d) (α : F ≅ G) :
    letI := ⨅ j, TopologicalSpace.induced (fun x : c.pt => (c.π.app j).hom x) ⊥
    letI := ⨅ j, TopologicalSpace.induced (fun x : d.pt => (d.π.app j).hom x) ⊥
    IsHomeomorph (hc.conePointsIsoOfNatIso hd α).hom.hom := by
  let e := hc.conePointsIsoOfNatIso hd α
  refine isHomeomorph_iInf_induced_bot_of_forall_exists _ _ e.toLinearEquiv.toEquiv
    (fun j => ⟨j, (α.hom.app j).hom, fun x => ?_⟩)
    (fun j => ⟨j, (α.inv.app j).hom, fun x => ?_⟩)
  · exact LinearMap.congr_fun
      (congrArg Hom.hom (IsLimit.conePointsIsoOfNatIso_hom_comp hc hd α j)) x
  · exact LinearMap.congr_fun
      (congrArg Hom.hom (IsLimit.conePointsIsoOfNatIso_inv_comp hc hd α j)) x

/-- **Limit cones of one diagram have homeomorphic points.** For two limit cones `c` and `d` of
a diagram of `R`-modules, the comparison isomorphism `c.pt ≅ d.pt` is a homeomorphism for the
limit topologies. -/
theorem isHomeomorph_conePointUniqueUpToIso {F : J ⥤ ModuleCat.{v} R} {c d : Cone F}
    (hc : IsLimit c) (hd : IsLimit d) :
    letI := ⨅ j, TopologicalSpace.induced (fun x : c.pt => (c.π.app j).hom x) ⊥
    letI := ⨅ j, TopologicalSpace.induced (fun x : d.pt => (d.π.app j).hom x) ⊥
    IsHomeomorph (hc.conePointUniqueUpToIso hd).hom.hom := by
  let e := hc.conePointUniqueUpToIso hd
  refine isHomeomorph_iInf_induced_bot_of_forall_exists _ _ e.toLinearEquiv.toEquiv
    (fun j => ⟨j, id, fun x => ?_⟩) (fun j => ⟨j, id, fun x => ?_⟩)
  · exact LinearMap.congr_fun
      (congrArg Hom.hom (IsLimit.conePointUniqueUpToIso_hom_comp hc hd j)) x
  · exact LinearMap.congr_fun
      (congrArg Hom.hom (IsLimit.conePointUniqueUpToIso_inv_comp hc hd j)) x

end ModuleCat

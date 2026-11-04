module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.HeightOnePoints
public import StacksFrontier.RingTheory.Branches.CompositionLawMinimalPrimes
public import StacksFrontier.RingTheory.Branches.FlatComapMinimalPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The branches at a point of an algebraic space, grouped over the components through it

Let `X` be a decent algebraic space over `S`, let `W` be an étale scheme chart of `X` and let
`u` be a point of the scheme of `W` lying over `ξ ∈ |X|`. The branches of `X` at `ξ` visible on
`W` are the minimal primes of the local ring `𝒪_{W, u}`, equivalently the irreducible components
of the scheme of `W` through `u`. This file constructs the map which sends such a branch to the
irreducible component of `|X|` it lies on, shows that it is **surjective** onto the components of
`|X|` through `ξ`, and records the regrouping of a sum over the branches as a sum over those
components of the sum over the branches lying on each.

This is the bookkeeping step which the proofs of Stacks 0EQ2, 0EQL and 0EPI take for granted when
they decompose a length over the minimal primes of a local ring at `ξ` by Stacks 02QG and then
collect the terms according to the component of `X` on which each prime lives. It has no tag of
its own in the source, so none is claimed here.

## Main definitions

* `AlgebraicGeometry.Space.componentOfChartComponent`: the irreducible component of `|X|` on
  which a branch lies, the branch being given as an irreducible component of the chart scheme
  through `u`.
* `AlgebraicGeometry.Space.componentOfBranch`: the same map with the branches indexed by the
  minimal primes of `𝒪_{W, u}`, which is the indexing the sum of Stacks 02QG uses.
* `AlgebraicGeometry.Space.componentOfFlatBranch`: the same map for the minimal primes of an
  arbitrary flat algebra over `𝒪_{W, u}`, which is the shape the henselian local ring
  `𝒪^h_{X, ξ}` of Stacks 0ENK and the étale local ring at a geometric point above `ξ` have.

## Main results

* `GeneralizingMap.mem_irreducibleComponents_closure_singleton` and
  `GeneralizingMap.exists_mem_irreducibleComponents_closure_singleton_eq`: the topological core.
  A continuous generalizing map into a quasi-sober space carries a generic point of an
  irreducible component to a generic point of an irreducible component, and every irreducible
  component of the target through the image of a point is reached from a component of the source
  through that point.
* `AlgebraicGeometry.Space.isGenericPoint_componentOfChartComponent` and
  `AlgebraicGeometry.Space.isGenericPoint_componentOfBranch`: the component attached to a branch
  is the closure of the image of the generic point of the branch.
* `AlgebraicGeometry.Space.surjective_componentOfChartComponent` and
  `AlgebraicGeometry.Space.surjective_componentOfBranch`: every irreducible component of `|X|`
  through `ξ` carries at least one branch.
* `AlgebraicGeometry.Space.surjective_componentOfFlatBranch`: the same for the branches of a
  flat algebra over `𝒪_{W, u}` whose structure map is injective.
* `AlgebraicGeometry.Space.finsum_branch_eq_finsum_component_finsum_branch` and
  `AlgebraicGeometry.Space.finsum_flatBranch_eq_finsum_component_finsum_flatBranch`: the
  partition statement, a sum over the branches at `ξ` regrouped as a sum over the components of
  `|X|` through `ξ` of the sum over the branches lying on each.

## Implementation notes

**The map is not injective, so it is not stated as a bijection.** A single irreducible component
of `|X|` can carry several branches: the number of irreducible components of a chart through a
point above `ξ` is the branch count of Stacks 0DQ3
(`AlgebraicGeometry.Space.HasComponentCount`, `AlgebraicGeometry.Space.HasBranchCount`), and
that count exceeds the number of components of `|X|` through `ξ` exactly where `X` fails to be
unibranch — a node on an irreducible curve has one component and two branches, and an étale
chart separating the two analytic branches at the node has two irreducible components through the
point above it, both mapping onto the one component of `|X|`. Injectivity therefore cannot be
asserted; what the consumers need, and what is proved here, is that the map is well defined and
surjective, so that the fibres partition the branches.

**Hypotheses.** Only `IsAlgebraicSpace` and `IsDecentSpace` are needed, through the two
properties of the map from a chart to `|X|` that the argument uses: it is continuous
(`AlgebraicGeometry.Space.continuous_chartSchemeToPoints`, which needs nothing) and generizations
lift along it (`AlgebraicGeometry.Space.generalizingMap_chartSchemeToPoints`, Stacks 03K2), and
through the existence of generic points for irreducible closed subsets of `|X|`
(`AlgebraicGeometry.Space.quasiSober_points_of_isDecentSpace`, the existence half of Stacks
03K6). In particular neither local Noetherianness nor quasi-separatedness nor integrality is
needed, and the Kolmogorov property of Stacks 03K3 is not used: the map is built from closures of
points, not from a choice of generic point in `|X|`. Openness of an étale morphism on points
(Stacks 03IR) is not needed either, which is why no `IsOpenMap` hypothesis appears; lifting
generizations is the weaker input that suffices.

**Reaching the henselian local ring.** The branches at `ξ` in the sense of Stacks 0DQ3 are the
minimal primes of `𝒪^h_{X, ξ}`, not of the Zariski local ring of a chart, and there are in
general more of them. They are matched with the branches on the chart by going down along the
flat local homomorphism `𝒪_{W, u} → 𝒪^h_{X, ξ}`, which is
`StacksDraft.comap_mem_minimalPrimes_of_ringHom_flat`; the `componentOfFlatBranch` layer is that
composite, stated for an arbitrary flat algebra so that it applies to `𝒪^h_{X, ξ}` and to the
étale local ring at a geometric point above `ξ` — both of which live one universe above the chart
local ring. Assembling the flat local algebra structure for a particular one of those rings is
left to the consumer, through `AlgebraicGeometry.Space.exists_isHenselization_etaleLocalRing` and
`Module.Flat.of_isHenselization`.

The partition statement carries the finiteness of the set of branches as a hypothesis rather than
deriving it: the finiteness of the set of components of `|X|` through `ξ` is then a consequence of
surjectivity, and no Noetherian hypothesis on the chart is required. A consumer with a Noetherian
chart local ring gets the hypothesis from
`Ideal.finite_minimalPrimes_of_isNoetherianRing`.

## References

* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 00HS](https://stacks.math.columbia.edu/tag/00HS)
* [Stacks Project, Tag 0DQ3](https://stacks.math.columbia.edu/tag/0DQ3)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

/-! ### Irreducible components under a continuous generalizing map -/

/-- **A continuous generalizing map carries a generic point of an irreducible component to a
generic point of an irreducible component.** If `φ : α → β` is continuous and generizations lift
along it, `β` is quasi-sober and `η` is a generic point of an irreducible component of `α`, then
the closure of `φ η` is an irreducible component of `β`.

The closure of `φ η` is contained in no strictly larger irreducible subset: such a subset has a
generic point `ζ`, which generizes `φ η`, so it lifts to a generization `w` of `η`; but `η` is
generic for a maximal irreducible subset, so `w` and `η` have the same closure, and therefore
`ζ` and `φ η` do too. -/
@[ega "0 2.1.6" "closure direction"]
theorem GeneralizingMap.mem_irreducibleComponents_closure_singleton {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [QuasiSober β] {φ : α → β}
    (hgen : GeneralizingMap φ) (hcont : Continuous φ) {C : Set α}
    (hC : C ∈ irreducibleComponents α) {η : α} (hη : IsGenericPoint η C) :
    closure ({φ η} : Set β) ∈ irreducibleComponents β := by
  refine ⟨isIrreducible_singleton.closure, fun T hT hsub => ?_⟩
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hT.closure isClosed_closure
  obtain ⟨w, hwη, hw⟩ :=
    hgen (hζ.specializes (subset_closure (hsub (subset_closure rfl))))
  have hCw : C ⊆ closure ({w} : Set α) := by
    rw [← hη.def]
    exact hwη.closure_subset
  have hwC : w ∈ C := hC.2 isIrreducible_singleton.closure hCw (subset_closure rfl)
  have h1 : φ η ⤳ ζ := hw ▸ (hη.specializes hwC).map hcont
  calc T ⊆ closure T := subset_closure
    _ = closure ({ζ} : Set β) := hζ.def.symm
    _ ⊆ closure ({φ η} : Set β) := h1.closure_subset

/-- **Every irreducible component of the target through the image of a point is reached.** If
`φ : α → β` is continuous and generizations lift along it, `β` is quasi-sober and `V` is an
irreducible component of `β` containing `φ u`, then some irreducible component `C` of `α`
contains `u` and the closure of the image of any generic point of `C` is `V`.

The generic point `ζ` of `V` generizes `φ u`, so it lifts to a generization `w` of `u`; any
irreducible component `C` containing the closure of `w` contains `u`, and a generic point of `C`
generizes `w`, so its image generizes `ζ`. The closure of that image is then an irreducible
subset containing the maximal irreducible subset `V`, hence is `V`. -/
@[ega "0 2.1.6" "partial"]
theorem GeneralizingMap.exists_mem_irreducibleComponents_closure_singleton_eq {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [QuasiSober β] {φ : α → β}
    (hgen : GeneralizingMap φ) (hcont : Continuous φ) {V : Set β}
    (hV : V ∈ irreducibleComponents β) {u : α} (hu : φ u ∈ V) :
    ∃ C ∈ irreducibleComponents α, u ∈ C ∧
      ∀ η : α, IsGenericPoint η C → closure ({φ η} : Set β) = V := by
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hV.1 (isClosed_of_mem_irreducibleComponents V hV)
  obtain ⟨w, hwu, hw⟩ := hgen (hζ.specializes hu)
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({w} : Set α)) isIrreducible_singleton.closure
  refine ⟨C, hC, hsub hwu.mem_closure, fun η hη => ?_⟩
  have h1 : φ η ⤳ ζ := hw ▸ (hη.specializes (hsub (subset_closure rfl))).map hcont
  have hVsub : V ⊆ closure ({φ η} : Set β) := by
    rw [← hζ.def]
    exact h1.closure_subset
  exact subset_antisymm (hV.2 isIrreducible_singleton.closure hVsub) hVsub

/-- **A finite sum is the sum over the fibres of a surjection out of its index type.** -/
theorem finsum_eq_finsum_finsum_fiber_of_surjective {α β M : Type*} [AddCommMonoid M]
    [Finite α] {g : α → β} (hg : Function.Surjective g) (f : α → M) :
    ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // g a = b}, f a.1 := by
  classical
  have := Finite.of_surjective g hg
  let _ : Fintype α := Fintype.ofFinite _
  let _ : Fintype β := Fintype.ofFinite _
  calc ∑ᶠ a, f a = ∑ a, f a := finsum_eq_sum_of_fintype f
    _ = ∑ b, ∑ a : {a // g a = b}, f a.1 := (Fintype.sum_fiberwise g f).symm
    _ = _ := by
        rw [finsum_eq_sum_of_fintype]
        exact Finset.sum_congr rfl fun b _ => (finsum_eq_sum_of_fintype _).symm

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

/-! ### The component of `|X|` carrying a branch -/

include hX hdec in
/-- The closure in `|X|` of the image of the generic point of an irreducible component of an
étale chart is an irreducible component of `|X|`. -/
theorem mem_irreducibleComponents_closure_singleton_chartSchemeToPoints
    (W : SmallEtale B S hS X) (C : irreducibleComponents (chartScheme W)) :
    closure ({chartSchemeToPoints B S hS X W (genericPoints.ofComponent C).1} :
        Set (points B S hS X)) ∈ irreducibleComponents (points B S hS X) := by
  have : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  exact GeneralizingMap.mem_irreducibleComponents_closure_singleton
    (generalizingMap_chartSchemeToPoints B S hS hX hdec W)
    (continuous_chartSchemeToPoints B S hS W) C.2
    (genericPoints.isGenericPoint_ofComponent C)

/-- **The irreducible component of `|X|` on which a branch at `ξ` lies.** A branch at `ξ` visible
on the étale chart `W` at the point `u` above `ξ` is an irreducible component `C` of the scheme of
`W` through `u`; the component of `|X|` it lies on is the closure of the image of the generic
point of `C`. -/
def componentOfChartComponent (W : SmallEtale B S hS X) (u : chartScheme W)
    (C : {C : irreducibleComponents (chartScheme W) // u ∈ (C : Set (chartScheme W))}) :
    {V : irreducibleComponents (points B S hS X) //
      chartSchemeToPoints B S hS X W u ∈ (V : Set (points B S hS X))} :=
  ⟨⟨closure ({chartSchemeToPoints B S hS X W (genericPoints.ofComponent C.1).1} :
        Set (points B S hS X)),
      mem_irreducibleComponents_closure_singleton_chartSchemeToPoints B S hS hX hdec W C.1⟩,
    Specializes.mem_closure
      (((genericPoints.isGenericPoint_ofComponent C.1).specializes C.2).map
        (continuous_chartSchemeToPoints B S hS W))⟩

/-- The component of `|X|` attached to a branch is the closure of the image of the generic point
of the branch. -/
theorem coe_componentOfChartComponent (W : SmallEtale B S hS X) (u : chartScheme W)
    (C : {C : irreducibleComponents (chartScheme W) // u ∈ (C : Set (chartScheme W))}) :
    ((componentOfChartComponent B S hS hX hdec W u C : irreducibleComponents
        (points B S hS X)) : Set (points B S hS X)) =
      closure ({chartSchemeToPoints B S hS X W (genericPoints.ofComponent C.1).1} :
        Set (points B S hS X)) :=
  rfl

/-- The image of the generic point of a branch is a generic point of the component of `|X|`
attached to it. -/
theorem isGenericPoint_componentOfChartComponent (W : SmallEtale B S hS X) (u : chartScheme W)
    (C : {C : irreducibleComponents (chartScheme W) // u ∈ (C : Set (chartScheme W))}) :
    IsGenericPoint (chartSchemeToPoints B S hS X W (genericPoints.ofComponent C.1).1)
      ((componentOfChartComponent B S hS hX hdec W u C : irreducibleComponents
        (points B S hS X)) : Set (points B S hS X)) :=
  rfl

include hX hdec in
/-- **Every irreducible component of `|X|` through `ξ` carries a branch.** The map from the
irreducible components of the chart through `u` to the irreducible components of `|X|` through
`ξ` is surjective. It is *not* injective: several branches may lie on one component. -/
theorem surjective_componentOfChartComponent (W : SmallEtale B S hS X) (u : chartScheme W) :
    Function.Surjective (componentOfChartComponent B S hS hX hdec W u) := by
  have : QuasiSober (points B S hS X) := quasiSober_points_of_isDecentSpace B S hS hX hdec
  intro V
  obtain ⟨C, hC, huC, hgen⟩ :=
    GeneralizingMap.exists_mem_irreducibleComponents_closure_singleton_eq
      (generalizingMap_chartSchemeToPoints B S hS hX hdec W)
      (continuous_chartSchemeToPoints B S hS W) V.1.2 V.2
  exact ⟨⟨⟨C, hC⟩, huC⟩,
    Subtype.ext (Subtype.ext (hgen _ (genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩)))⟩

/-! ### The branches as minimal primes of the chart local ring -/

/-- **The irreducible component of `|X|` on which a branch at `ξ` lies**, with the branches
indexed by the minimal primes of the local ring `𝒪_{W, u}` of the chart at the point above `ξ`.
The minimal primes correspond to the irreducible components of the chart through `u` by Stacks
00ET, `AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes`. -/
def componentOfBranch (W : SmallEtale B S hS X) (u : chartScheme W)
    (p : {p : PrimeSpectrum ((chartScheme W).presheaf.stalk u) //
      p.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk u)}) :
    {V : irreducibleComponents (points B S hS X) //
      chartSchemeToPoints B S hS X W u ∈ (V : Set (points B S hS X))} :=
  componentOfChartComponent B S hS hX hdec W u ((irreducibleComponentsEquivMinimalPrimes u).symm p)

/-- The image of the point of the chart cut out by a minimal prime of `𝒪_{W, u}` is a generic
point of the component of `|X|` attached to that branch. -/
theorem isGenericPoint_componentOfBranch (W : SmallEtale B S hS X) (u : chartScheme W)
    (p : {p : PrimeSpectrum ((chartScheme W).presheaf.stalk u) //
      p.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk u)}) :
    IsGenericPoint
      (chartSchemeToPoints B S hS X W ((chartScheme W).fromSpecStalk u p.1))
      ((componentOfBranch B S hS hX hdec W u p : irreducibleComponents
        (points B S hS X)) : Set (points B S hS X)) := by
  have h := fromSpecStalk_irreducibleComponentsEquivMinimalPrimes u
    ((irreducibleComponentsEquivMinimalPrimes u).symm p)
  rw [Equiv.apply_symm_apply] at h
  rw [componentOfBranch, h]
  exact isGenericPoint_componentOfChartComponent B S hS hX hdec W u _

include hX hdec in
/-- **Every irreducible component of `|X|` through `ξ` carries a branch**, in the indexing of the
branches by the minimal primes of `𝒪_{W, u}`. The map is *not* injective. -/
theorem surjective_componentOfBranch (W : SmallEtale B S hS X) (u : chartScheme W) :
    Function.Surjective (componentOfBranch B S hS hX hdec W u) :=
  (surjective_componentOfChartComponent B S hS hX hdec W u).comp
    (irreducibleComponentsEquivMinimalPrimes u).symm.surjective

/-! ### Regrouping a sum over the branches as a sum over the components -/

include hX hdec in
/-- **The partition of the branches at `ξ` over the irreducible components of `|X|` through
`ξ`.** A sum over the minimal primes of the local ring of an étale chart at a point above `ξ` —
the shape of the sum of Stacks 02QG,
`AlgebraicGeometry.natCast_length_quotient_span_eq_sum_minimalPrimes` — is the sum over the
irreducible components of `|X|` through `ξ` of the sum over the branches lying on each.

Finiteness of the set of branches is a hypothesis; the set of components of `|X|` through `ξ` is
then finite because the map onto it is surjective. -/
theorem finsum_branch_eq_finsum_component_finsum_branch {M : Type v} [AddCommMonoid M]
    (W : SmallEtale B S hS X) (u : chartScheme W)
    (hfin : Finite {p : PrimeSpectrum ((chartScheme W).presheaf.stalk u) //
      p.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk u)})
    (f : {p : PrimeSpectrum ((chartScheme W).presheaf.stalk u) //
      p.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk u)} → M) :
    ∑ᶠ p, f p =
      ∑ᶠ V : {V : irreducibleComponents (points B S hS X) //
          chartSchemeToPoints B S hS X W u ∈ (V : Set (points B S hS X))},
        ∑ᶠ p : {p // componentOfBranch B S hS hX hdec W u p = V}, f p.1 := by
  have := hfin
  exact finsum_eq_finsum_finsum_fiber_of_surjective
    (surjective_componentOfBranch B S hS hX hdec W u) f

/-! ### The branches in a flat local algebra over the chart local ring -/

section FlatAlgebra

variable (W : SmallEtale B S hS X) (u : chartScheme W) (A : Type v) [CommRing A]
    [Algebra ((chartScheme W).presheaf.stalk u) A]
    [Module.Flat ((chartScheme W).presheaf.stalk u) A]

/-- **The irreducible component of `|X|` on which a branch at `ξ` in a flat algebra over the
chart local ring lies.** A minimal prime of a flat `𝒪_{W, u}`-algebra `A` contracts to a minimal
prime of `𝒪_{W, u}` by going down, `StacksDraft.comap_mem_minimalPrimes_of_ringHom_flat`, so it
determines an irreducible component of `|X|` through `ξ`.

This is the form the branches at `ξ` in the sense of Stacks 0DQ3 take: the henselian local ring
`𝒪^h_{X, ξ}` of Stacks 0ENK and the étale local ring of `X` at a geometric point above `ξ` are
flat — indeed faithfully flat — local `𝒪_{W, u}`-algebras, by `Module.Flat.of_isHenselization`,
and they live one universe above the chart local ring, which is why `A` is allowed its own
universe. -/
def componentOfFlatBranch (q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A}) :
    {V : irreducibleComponents (points B S hS X) //
      chartSchemeToPoints B S hS X W u ∈ (V : Set (points B S hS X))} :=
  componentOfBranch B S hS hX hdec W u
    ⟨PrimeSpectrum.comap (algebraMap ((chartScheme W).presheaf.stalk u) A) q.1,
      StacksDraft.comap_mem_minimalPrimes_of_ringHom_flat _
        (RingHom.flat_algebraMap_iff.2 inferInstance) q.2⟩

/-- The component of `|X|` attached to a branch of `A` is the one attached to the minimal prime
of `𝒪_{W, u}` under it. -/
theorem componentOfFlatBranch_eq_componentOfBranch
    (q : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A})
    (p : {p : PrimeSpectrum ((chartScheme W).presheaf.stalk u) //
      p.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk u)})
    (hp : p.1 = PrimeSpectrum.comap (algebraMap ((chartScheme W).presheaf.stalk u) A) q.1) :
    componentOfFlatBranch B S hS hX hdec W u A q = componentOfBranch B S hS hX hdec W u p := by
  rw [componentOfFlatBranch]
  exact congrArg _ (Subtype.ext hp.symm)

include hX hdec in
/-- **Every irreducible component of `|X|` through `ξ` carries a branch of `A`**, as soon as
`𝒪_{W, u} → A` is injective — which it is for a faithfully flat algebra, in particular for the
henselian local ring at `ξ` and for the étale local ring at a geometric point above `ξ`. The map
is *not* injective. -/
theorem surjective_componentOfFlatBranch
    (hinj : Function.Injective (algebraMap ((chartScheme W).presheaf.stalk u) A)) :
    Function.Surjective (componentOfFlatBranch B S hS hX hdec W u A) := by
  intro V
  obtain ⟨p, hp⟩ := surjective_componentOfBranch B S hS hX hdec W u V
  obtain ⟨P, hPprime, hPcomap⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj p.1.asIdeal p.2
  obtain ⟨q, hq, hqP⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := P) bot_le
  have hcomap : q.comap (algebraMap ((chartScheme W).presheaf.stalk u) A) ∈
      minimalPrimes ((chartScheme W).presheaf.stalk u) :=
    StacksDraft.comap_mem_minimalPrimes_of_ringHom_flat _
      (RingHom.flat_algebraMap_iff.2 inferInstance) hq
  refine ⟨⟨⟨q, hq.1.1⟩, hq⟩, ?_⟩
  have heq : p.1.asIdeal = Ideal.comap (algebraMap ((chartScheme W).presheaf.stalk u) A) q :=
    (StacksDraft.eq_of_mem_minimalPrimes_of_le hcomap p.2
      ((Ideal.comap_mono hqP).trans (le_of_eq hPcomap))).symm
  rw [componentOfFlatBranch_eq_componentOfBranch B S hS hX hdec W u A ⟨⟨q, hq.1.1⟩, hq⟩ p
    (PrimeSpectrum.ext heq), hp]

include hX hdec in
/-- **The partition of the branches at `ξ` in a flat algebra over the chart local ring, over the
irreducible components of `|X|` through `ξ`.** This is the form Stacks 0EQ2 needs, its sum of
Stacks 02QG running over the minimal primes of the henselian local ring `𝒪^h_{X, ξ}`.

Finiteness of the set of branches is a hypothesis; the set of components of `|X|` through `ξ` is
then finite because the map onto it is surjective, which is what the injectivity of
`𝒪_{W, u} → A` is for. -/
theorem finsum_flatBranch_eq_finsum_component_finsum_flatBranch {M : Type*} [AddCommMonoid M]
    (hinj : Function.Injective (algebraMap ((chartScheme W).presheaf.stalk u) A))
    (hfin : Finite {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A})
    (f : {q : PrimeSpectrum A // q.asIdeal ∈ minimalPrimes A} → M) :
    ∑ᶠ q, f q =
      ∑ᶠ V : {V : irreducibleComponents (points B S hS X) //
          chartSchemeToPoints B S hS X W u ∈ (V : Set (points B S hS X))},
        ∑ᶠ q : {q // componentOfFlatBranch B S hS hX hdec W u A q = V}, f q.1 := by
  have := hfin
  exact finsum_eq_finsum_finsum_fiber_of_surjective
    (surjective_componentOfFlatBranch B S hS hX hdec W u A hinj) f

end FlatAlgebra

end AlgebraicGeometry.Space

end

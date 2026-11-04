module

public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FormalBranches
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlatAssembly
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal branches and irreducible components (Stacks 0DRB)

In the situation of **Stacks 0DRA** — an algebraic stack `𝒳` locally of finite type over a
locally Noetherian scheme `S`, a point `x₀ : Spec k ⟶ 𝒳` with `k` a field of finite type over
`S`, and a versal ring `A` to `𝒳` at `x₀` — **Stacks 0DRB** gives a canonical surjection from the
formal branches of `𝒳` through `x₀` (the irreducible components of `Spec A`, recorded by their
generic points, the minimal primes of `A`) to the irreducible components of `|𝒳|` containing
`x₀`. A branch goes to the closure of the image of its generic point under the morphism
`j : Spec A ⟶ 𝒳` of **Stacks 0DR1**.

The source's proof chooses a smooth surjective chart `U ⟶ 𝒳`, uses that `j` is flat
(**Stacks 0DR2**) to see that generic points of `Spec A` lift to codimension `0` points of
`Spec A ×_𝒳 U` mapping to generic points of `U`, and concludes with **Stacks 0DR5**; for
surjectivity it shrinks `U` around a point over `x₀` and uses going down. Here the two claims
are properties of objects of `𝒳` over schemes —
`AlgebraicGeometry.Stack.AlgebraicStacks.SendsGenericPointsToComponents` and
`AlgebraicGeometry.Stack.AlgebraicStacks.ReachesComponents` — which hold at smooth objects
(Stacks 0DR5, resp. openness of a smooth chart over a locally Noetherian scheme), ascend along
morphisms lying over flat morphisms and descend along morphisms lying over flat surjective ones
(going down). The argument of the proof of Stacks 0DR2 — Step III reaches the restriction of a
smooth chart to a completed local ring, Steps I and II move along the faithfully flat
comparisons of parts (1) and (2) of Stacks 0DR1 — therefore carries both to every realization
`Spec A ⟶ 𝒳` (`AlgebraicGeometry.Stack.satisfies_of_realization`), which replaces the algebraic
space `Spec A ×_𝒳 U` of the source.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.objectPointMap`: the map `|T| ⟶ |𝒳|` of an object over
  a scheme `T`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.basePointMap`: the same over `Spec A`, read on primes.
* `AlgebraicGeometry.Stack.VersalSituation.fieldPoint`: the point `x₀ ∈ |𝒳|`.
* `AlgebraicGeometry.Stack.formalBranchComponent`: **Stacks 0DRB**, the map.

## Main results

* `AlgebraicGeometry.Stack.VersalSituation.hasLocallyNoetherianAtlas`: `𝒳` is locally
  Noetherian (Stacks 06R6).
* `AlgebraicGeometry.Stack.satisfies_of_realization`: the argument of Stacks 0DR2 for a property.
* `AlgebraicGeometry.Stack.closure_basePointMap_mem_irreducibleComponents`: the claim of the
  proof — the image of a branch is a component through `x₀`.
* `AlgebraicGeometry.Stack.formalBranchComponent_surjective`: surjectivity.
* `AlgebraicGeometry.Stack.formalBranchComponent_comparison` and
  `AlgebraicGeometry.Stack.formalBranchComponent_independent`: canonicity — compatibility with
  the comparison morphisms of Stacks 0DR1, hence independence of the versal ring.
* `AlgebraicGeometry.Stack.formalBranchComponent_surjective_and_canonical`: **Stacks 0DRB**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.closure_basePointMap_eq_of_hom`: the image of a branch
  through a chart `y ⟶ x` is the closure of the image of the component of the chart it maps to.

## Implementation notes

The map depends on the versal formal object and its realization, not only on the ring `A`: two
versal formal objects over the same `A` can differ by an automorphism of `A` permuting its minimal
primes. This is why the source identifies the branches read off different versal rings along the
comparison maps of Stacks 0DR1 rather than through `A` alone, and canonicity is stated as
compatibility with those comparisons.

## References

* [Stacks Project, Tag 0DRA](https://stacks.math.columbia.edu/tag/0DRA)
* [Stacks Project, Tag 0DRB](https://stacks.math.columbia.edu/tag/0DRB)
* [Stacks Project, Tag 0DR1](https://stacks.math.columbia.edu/tag/0DR1)
* [Stacks Project, Tag 0DR2](https://stacks.math.columbia.edu/tag/0DR2)
* [Stacks Project, Tag 0DR5](https://stacks.math.columbia.edu/tag/0DR5)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Stack

universe u w

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map on points `|T| ⟶ |𝒳|` of an object `y` of an algebraic stack lying over a scheme
`T` of the site: the map on points of the 1-morphism `T ⟶ 𝒳` that `y` names under the 2-Yoneda
lemma, read on the topological space of `T`. -/
def objectPointMap (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : 𝒳.val.val.obj) :
    (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y) → points B S hS 𝒳 :=
  chartPointMap B S hS _ 𝒳
    (Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)))

/-- The map on points of an object is continuous. -/
theorem continuous_objectPointMap (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : 𝒳.val.val.obj) :
    letI := Stack.pointTopology B S hS 𝒳.val
    Continuous (objectPointMap B S hS 𝒳 y) :=
  continuous_chartPointMap B S hS _ 𝒳 _

/-- **The map on points of an object is natural.** For a morphism `m : y' ⟶ y` of `𝒳` lying over
`g : T' ⟶ T`, the 1-morphism `T' ⟶ 𝒳` named by `y'` is 2-isomorphic to `T' ⟶ T ⟶ 𝒳`, so the
point of `y'` at `t` is the point of `y` at `g t`. -/
theorem objectPointMap_map (𝒳 : AlgebraicStacks.{u, w} B S hS) {y' y : 𝒳.val.val.obj}
    (m : y' ⟶ y) (t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y')) :
    objectPointMap B S hS 𝒳 y' t =
      objectPointMap B S hS 𝒳 y ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m) t) := by
  let e : (Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y') rfl)) :
        schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y') ⟶ 𝒳) ≅
      schemeStackMap.{u, w} B S hS (𝒳.val.val.p.map m) ≫
        Bicategory.InducedBicategory.mkHom
          (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl)) :=
    Bicategory.InducedBicategory.isoMk (objectMorphismFactorIso B S hS 𝒳.val m)
  simp only [objectPointMap, chartPointMap, Function.comp_apply]
  rw [pointsMap_eq_of_hom₂ B S hS e.hom, pointsMap_comp, Function.comp_apply]
  congr 1
  let := Stack.pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj y))
  let := Stack.pointTopology B S hS (schemeFibredCategory B S hS (𝒳.val.val.p.obj y'))
  apply (pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj y)).injective
  rw [Homeomorph.apply_symm_apply]
  have h := pointsHomeomorphScheme_pointsMap B S hS
    (schemeStackMap.{u, w} B S hS (𝒳.val.val.p.map m))
    ((pointsHomeomorphScheme B S hS (𝒳.val.val.p.obj y')).symm t)
  rw [siteMap_schemeStackMap, Homeomorph.apply_symm_apply] at h
  exact h

end AlgebraicStacks


/-! ### Generic points and irreducible components -/

/-- In a `T₀` space, a point whose closure is an irreducible component has no proper
generalization: a generalization has a larger irreducible closure, which maximality makes equal. -/
private theorem eq_of_specializes_of_closure_mem_irreducibleComponents {X : Type*}
    [TopologicalSpace X] [T0Space X] {t z : X}
    (ht : closure {t} ∈ irreducibleComponents X) (hzt : z ⤳ t) : z = t := by
  have hsub : closure {t} ⊆ closure {z} := hzt.closure_subset
  have hle := ht.2 isIrreducible_singleton.closure hsub
  have htz : t ⤳ z := specializes_iff_mem_closure.mpr (hle (subset_closure rfl))
  exact (hzt.antisymm htz).eq

/-- In a quasi-sober space every point specializes from a point whose closure is an irreducible
component: the generic point of the irreducible component through it. -/
private theorem exists_specializes_closure_mem_irreducibleComponents {X : Type*}
    [TopologicalSpace X] [QuasiSober X] (t : X) :
    ∃ z, z ⤳ t ∧ closure {z} ∈ irreducibleComponents X := by
  have hZ := irreducibleComponent_mem_irreducibleComponents t
  have hirr : IsIrreducible (irreducibleComponent t) := isIrreducible_irreducibleComponent
  have hgen := hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent
  refine ⟨hirr.genericPoint, ?_, ?_⟩
  · exact hgen.specializes mem_irreducibleComponent
  · rw [hgen.def]; exact hZ

/-- A prime is minimal exactly when the closure of its point is an irreducible component of the
spectrum. -/
private theorem closure_singleton_mem_irreducibleComponents_iff_mem_minimalPrimes {R : Type*}
    [CommRing R] (Q : PrimeSpectrum R) :
    closure {Q} ∈ irreducibleComponents (PrimeSpectrum R) ↔ Q.asIdeal ∈ minimalPrimes R := by
  rw [PrimeSpectrum.closure_singleton, PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents,
    Q.isPrime.radical]

/-- **A generalizing map carries generic points of irreducible components to generic points of
irreducible components**, into a quasi-sober `T₀` space. -/
theorem closure_singleton_mem_irreducibleComponents_of_generalizingMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober Y] [T0Space X]
    {g : X → Y} (hg : GeneralizingMap g) {t : X}
    (ht : closure {t} ∈ irreducibleComponents X) :
    closure {g t} ∈ irreducibleComponents Y := by
  obtain ⟨z, hz, hZ⟩ := exists_specializes_closure_mem_irreducibleComponents (g t)
  obtain ⟨t', ht', rfl⟩ := hg hz
  rwa [eq_of_specializes_of_closure_mem_irreducibleComponents ht ht'] at hZ

/-- **A continuous surjection out of a quasi-sober space reaches every generic point of an
irreducible component of a `T₀` target from a generic point of an irreducible component.** -/
theorem exists_closure_singleton_mem_irreducibleComponents_of_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [QuasiSober X] [T0Space Y]
    {g : X → Y} (hg : Continuous g) (hs : Function.Surjective g) {t : Y}
    (ht : closure {t} ∈ irreducibleComponents Y) :
    ∃ z, closure {z} ∈ irreducibleComponents X ∧ g z = t := by
  obtain ⟨t', rfl⟩ := hs t
  obtain ⟨z, hz, hZ⟩ := exists_specializes_closure_mem_irreducibleComponents t'
  exact ⟨z, hZ, eq_of_specializes_of_closure_mem_irreducibleComponents ht (hz.map hg)⟩

/-- A point whose closure is the closure of an irreducible component of an open subspace has
closure an irreducible component of the whole space. -/
theorem closure_singleton_mem_irreducibleComponents_of_isOpen {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] {W : Set X} (hW : IsOpen W) {T : Set W}
    (hT : T ∈ irreducibleComponents W) {z : X} (hz : closure {z} = closure (Subtype.val '' T)) :
    closure {z} ∈ irreducibleComponents X := by
  obtain ⟨w, hw⟩ := hT.1.nonempty
  have hzw : z ⤳ w.1 := specializes_iff_mem_closure.mpr (hz ▸ subset_closure ⟨w, hw, rfl⟩)
  obtain ⟨z', hz'z, hz'⟩ := exists_specializes_closure_mem_irreducibleComponents z
  have hz'W : z' ∈ W := (hz'z.trans hzw).mem_open hW w.2
  have hpre : IsIrreducible ((Subtype.val : W → X) ⁻¹' closure {z'}) :=
    ⟨⟨⟨z', hz'W⟩, subset_closure rfl⟩, hz'.1.2.preimage hW.isOpenEmbedding_subtypeVal⟩
  have hTsub : T ⊆ (Subtype.val : W → X) ⁻¹' closure {z'} := fun v hv =>
    hz'z.closure_subset (hz ▸ subset_closure ⟨v, hv, rfl⟩)
  have hmem : (⟨z', hz'W⟩ : W) ∈ T := hT.2 hpre hTsub (subset_closure rfl)
  have hzz' : z ⤳ z' := specializes_iff_mem_closure.mpr (hz ▸ subset_closure ⟨_, hmem, rfl⟩)
  rwa [(hz'z.antisymm hzz').eq] at hz'

/-- Under a continuous map, a point whose closure is that of a set `A` has image whose closure is
that of the image of `A`. -/
theorem closure_singleton_image_eq_of_closure_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {z : X} {A : Set X}
    (hz : closure {z} = closure A) : closure {f z} = closure (f '' A) := by
  rw [← Set.image_singleton, ← closure_image_closure hf, hz, closure_image_closure hf]


/-- **Every irreducible component through the image of a point, under a continuous open map out
of a locally Noetherian space, is the closure of the image of a generic point specializing to
it.** This is the topological core of the surjectivity in Stacks 0DRB. A Noetherian open
neighbourhood `W` of `u` has finitely many irreducible components; removing those not through `u`
leaves an open neighbourhood whose image is open, so the component `Z` is covered by the
complement of that image together with the closures of the images of the components of `W`
through `u`, and irreducibility puts `Z` inside one of the latter, hence equal to it. The generic
point of the closure of that component of `W` is the required point. -/
theorem exists_specializes_closure_image_eq_of_isOpenMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [T0Space X]
    (hX : TopologicalSpace.IsLocallyNoetherianSpace X) {f : X → Y} (hf : Continuous f)
    (ho : IsOpenMap f) (u : X) {Z : Set Y} (hZ : Z ∈ irreducibleComponents Y) (hu : f u ∈ Z) :
    ∃ z, z ⤳ u ∧ closure {z} ∈ irreducibleComponents X ∧ closure {f z} = Z := by
  classical
  obtain ⟨W, hW, huW, hWN⟩ := hX u
  have hι : Topology.IsOpenEmbedding (Subtype.val : W → X) := hW.isOpenEmbedding_subtypeVal
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := W)
  let u' : W := ⟨u, huW⟩
  let N : Set (Set W) := {T | T ∈ irreducibleComponents W ∧ u' ∉ T}
  let C : Set (Set W) := {T | T ∈ irreducibleComponents W ∧ u' ∈ T}
  have hNfin : N.Finite := hfin.subset fun _ hT => hT.1
  have hCfin : C.Finite := hfin.subset fun _ hT => hT.1
  let V : Set W := (⋃₀ N)ᶜ
  have hV : IsOpen V := (hNfin.isClosed_sUnion fun T hT =>
    isClosed_of_mem_irreducibleComponents T hT.1).isOpen_compl
  have hu'V : u' ∈ V := fun ⟨_, hT, hu'T⟩ => hT.2 hu'T
  let O : Set Y := f '' (Subtype.val '' V)
  have hO : IsOpen O := ho _ (hι.isOpenMap _ hV)
  have huO : f u ∈ O := ⟨u, ⟨u', hu'V, rfl⟩, rfl⟩
  let g : Set W → Set Y := fun T => closure (f '' (Subtype.val '' T))
  let t : Finset (Set Y) := insert Oᶜ (hCfin.image g).toFinset
  have hcover : Z ⊆ ⋃₀ (t : Set (Set Y)) := by
    intro y hy
    by_cases hyO : y ∈ O
    · obtain ⟨_, ⟨v, hvV, rfl⟩, rfl⟩ := hyO
      obtain ⟨T, hT, hvT⟩ : v ∈ ⋃₀ irreducibleComponents W := by
        rw [sUnion_irreducibleComponents]
        trivial
      have hTC : T ∈ C := ⟨hT, by_contra fun hu'T => hvV ⟨T, ⟨hT, hu'T⟩, hvT⟩⟩
      refine ⟨g T, ?_, subset_closure ⟨v.1, ⟨v, hvT, rfl⟩, rfl⟩⟩
      simp only [t, Finset.coe_insert, Set.Finite.coe_toFinset]
      exact Or.inr ⟨T, hTC, rfl⟩
    · exact ⟨Oᶜ, by simp [t], hyO⟩
  obtain ⟨K, hKt, hZK⟩ := (isIrreducible_iff_sUnion_isClosed.mp hZ.1) t (by
    intro K hK
    simp only [t, Finset.mem_insert, Set.Finite.mem_toFinset] at hK
    rcases hK with rfl | ⟨T, -, rfl⟩
    · exact hO.isClosed_compl
    · exact isClosed_closure) hcover
  simp only [t, Finset.mem_insert, Set.Finite.mem_toFinset] at hKt
  rcases hKt with rfl | ⟨T, hTC, rfl⟩
  · exact absurd huO (hZK hu)
  have hTx : IsIrreducible (Subtype.val '' T) := hTC.1.1.image _ continuous_subtype_val.continuousOn
  have hK : IsIrreducible (g T) := (hTx.image f hf.continuousOn).closure
  have hZeq : Z = g T := subset_antisymm hZK (hZ.2 hK hZK)
  let z := hTx.genericPoint
  have hz : closure {z} = closure (Subtype.val '' T) := hTx.genericPoint_closure_eq
  exact ⟨z, specializes_iff_mem_closure.mpr (hz ▸ subset_closure ⟨u', hTC.2, rfl⟩),
    closure_singleton_mem_irreducibleComponents_of_isOpen hW hTC.1 hz,
    hZeq ▸ closure_singleton_image_eq_of_closure_eq hf hz⟩

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An object `y` of an algebraic stack over a scheme `T` *sends generic points to components*
when the point of `y` at the generic point of every irreducible component of `T` is the generic
point of an irreducible component of `|𝒳|`. -/
def SendsGenericPointsToComponents (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : 𝒳.val.val.obj) :
    Prop :=
  letI := Stack.pointTopology B S hS 𝒳.val
  ∀ t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y),
    closure {t} ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) →
      closure {objectPointMap B S hS 𝒳 y t} ∈ irreducibleComponents (points B S hS 𝒳)

/-- **The closure of the point of a chart at `u` is the closure of the image of the closure of
`u`.** -/
theorem closure_singleton_chartPointMap_eq (U : BigFppfOver B S hS)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (t : (BigFppfOver.toScheme B S hS).obj U) :
    letI := Stack.pointTopology B S hS 𝒳.val
    closure {chartPointMap B S hS U 𝒳 f t} =
      closure (chartPointMap B S hS U 𝒳 f '' closure {t}) := by
  let := Stack.pointTopology B S hS 𝒳.val
  apply subset_antisymm
  · exact closure_mono (Set.singleton_subset_iff.mpr ⟨t, subset_closure rfl, rfl⟩)
  · refine closure_minimal ?_ isClosed_closure
    refine ((image_closure_subset_closure_image
      (continuous_chartPointMap B S hS U 𝒳 f)).trans ?_)
    rw [Set.image_singleton]

/-- **Stacks 0DR5 at a point.** For a smooth object `x` of a locally Noetherian algebraic stack
over `S`, the point of `x` at the generic point of an irreducible component of the scheme it lies
over is the generic point of an irreducible component of `|𝒳|`. -/
theorem sendsGenericPointsToComponents_of_smoothObject (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    {x : 𝒳.val.val.obj} (hx : smoothObject.{u, w} B S hS 𝒳 x) :
    SendsGenericPointsToComponents B S hS 𝒳 x := by
  let := Stack.pointTopology B S hS 𝒳.val
  intro t ht
  have h := closure_image_chartPointMap_mem_irreducibleComponents B S hS _ 𝒳 hN _ hx _ ht
  rwa [← closure_singleton_chartPointMap_eq] at h

/-- **Sending generic points to components ascends along flat morphisms.** If `m : y' ⟶ y` lies
over a flat morphism of schemes, generic points of components of the source map to generic points
of components of the target, and the point of `y'` there is the point of `y`. -/
theorem SendsGenericPointsToComponents.of_flat (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {y' y : 𝒳.val.val.obj} (m : y' ⟶ y)
    (hm : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)))
    (hy : SendsGenericPointsToComponents B S hS 𝒳 y) :
    SendsGenericPointsToComponents B S hS 𝒳 y' := by
  intro t ht
  rw [objectPointMap_map B S hS 𝒳 m t]
  exact hy _ (closure_singleton_mem_irreducibleComponents_of_generalizingMap
    (Flat.generalizingMap _) ht)

/-- **Sending generic points to components descends along surjective morphisms.** -/
theorem SendsGenericPointsToComponents.of_surjective (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {y' y : 𝒳.val.val.obj} (m : y' ⟶ y)
    (hm : Surjective ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)))
    (hy' : SendsGenericPointsToComponents B S hS 𝒳 y') :
    SendsGenericPointsToComponents B S hS 𝒳 y := by
  intro t ht
  obtain ⟨z, hz, rfl⟩ := exists_closure_singleton_mem_irreducibleComponents_of_surjective
    ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)).continuous hm.surj ht
  rw [← objectPointMap_map B S hS 𝒳 m z]
  exact hy' z hz

/-- An object `y` of an algebraic stack over a scheme `T` *reaches all components* when every
irreducible component of `|𝒳|` through the point of `y` at a point `t ∈ T` is the closure of the
point of `y` at a generic point of an irreducible component of `T` specializing to `t`. -/
def ReachesComponents (𝒳 : AlgebraicStacks.{u, w} B S hS) (y : 𝒳.val.val.obj) : Prop :=
  letI := Stack.pointTopology B S hS 𝒳.val
  ∀ (t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)),
    ∀ Z ∈ irreducibleComponents (points B S hS 𝒳), objectPointMap B S hS 𝒳 y t ∈ Z →
      ∃ z, z ⤳ t ∧
        closure {z} ∈ irreducibleComponents ((BigFppfOver.toScheme B S hS).obj
          (𝒳.val.val.p.obj y)) ∧
        closure {objectPointMap B S hS 𝒳 y z} = Z

/-- **A smooth object of a locally Noetherian algebraic stack reaches all components**: its point
map is continuous and open (Stacks 06R7) out of a locally Noetherian scheme. -/
theorem reachesComponents_of_smoothObject (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    {x : 𝒳.val.val.obj} (hx : smoothObject.{u, w} B S hS 𝒳 x) :
    ReachesComponents B S hS 𝒳 x := by
  let := Stack.pointTopology B S hS 𝒳.val
  intro t Z hZ ht
  exact exists_specializes_closure_image_eq_of_isOpenMap
    (isLocallyNoetherianSpace_of_isSmooth B S hS _ 𝒳 hN _ hx)
    (continuous_objectPointMap B S hS 𝒳 x) (isOpenMap_chartPointMap B S hS _ 𝒳 _ hx) t hZ ht

/-- **Reaching all components ascends along flat morphisms.** A generic point below the image of
`t` lifts, by going down, to a generalization of `t`, below which lies a generic point of the
source, and that point maps to the given generic point. -/
theorem ReachesComponents.of_flat (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {y' y : 𝒳.val.val.obj} (m : y' ⟶ y)
    (hm : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)))
    (hy : ReachesComponents B S hS 𝒳 y) :
    ReachesComponents B S hS 𝒳 y' := by
  let := Stack.pointTopology B S hS 𝒳.val
  intro t Z hZ ht
  rw [objectPointMap_map B S hS 𝒳 m t] at ht
  obtain ⟨s, hst, hs, hsZ⟩ := hy _ Z hZ ht
  obtain ⟨s', hs't, rfl⟩ := Flat.generalizingMap _ hst
  obtain ⟨z, hzs', hz⟩ := exists_specializes_closure_mem_irreducibleComponents s'
  have hzeq := eq_of_specializes_of_closure_mem_irreducibleComponents hs
    (hzs'.map ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)).continuous)
  refine ⟨z, hzs'.trans hs't, hz, ?_⟩
  rw [objectPointMap_map B S hS 𝒳 m z, hzeq, hsZ]

/-- **Reaching all components descends along flat surjective morphisms.** A preimage of `t`
carries the component; the generic point it provides maps, the morphism being generalizing, to a
generic point below `t`. -/
theorem ReachesComponents.of_flat_of_surjective (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {y' y : 𝒳.val.val.obj} (m : y' ⟶ y)
    (hm : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)))
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)))
    (hy' : ReachesComponents B S hS 𝒳 y') :
    ReachesComponents B S hS 𝒳 y := by
  let := Stack.pointTopology B S hS 𝒳.val
  intro t Z hZ ht
  obtain ⟨t', rfl⟩ := hs.surj t
  rw [← objectPointMap_map B S hS 𝒳 m t'] at ht
  obtain ⟨z, hzt, hz, hzZ⟩ := hy' t' Z hZ ht
  refine ⟨_, hzt.map ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)).continuous,
    closure_singleton_mem_irreducibleComponents_of_generalizingMap (Flat.generalizingMap _) hz,
    ?_⟩
  rw [← objectPointMap_map B S hS 𝒳 m z, hzZ]

end AlgebraicStacks


namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A prime of a complete local base `A`, as a point of the object `Spec A` of the site. -/
def baseOverPoint (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (P : PrimeSpectrum A.R) :
    (BigFppfOver.toScheme B S hS).obj (Deformation.Artin.baseOver B S hS A hA) :=
  P

/-- The map on points `|Spec A| ⟶ |𝒳|` of an object `y` of an algebraic stack lying over the
spectrum of a complete local base `A`, read on the primes of `A`. -/
def basePointMap (𝒳 : AlgebraicStacks.{u, w} B S hS) (A : Deformation.Artin.FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) (y : 𝒳.val.val.obj)
    (hy : 𝒳.val.val.p.obj y = Deformation.Artin.baseOver B S hS A hA) :
    PrimeSpectrum A.R → points B S hS 𝒳 := fun P =>
  objectPointMap B S hS 𝒳 y ((BigFppfOver.toScheme B S hS).map (eqToHom hy.symm)
    (baseOverPoint B S hS A hA P))

/-- The map on points of an object over `Spec A`, read on primes, is continuous. -/
theorem continuous_basePointMap (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R))) (y : 𝒳.val.val.obj)
    (hy : 𝒳.val.val.p.obj y = Deformation.Artin.baseOver B S hS A hA) :
    letI := Stack.pointTopology B S hS 𝒳.val
    Continuous (basePointMap B S hS 𝒳 A hA y hy) :=
  let := Stack.pointTopology B S hS 𝒳.val
  (continuous_objectPointMap B S hS 𝒳 y).comp
    ((BigFppfOver.toScheme B S hS).map (eqToHom hy.symm)).continuous

/-- Reading the point map of an object over `Spec A` back on the scheme it lies over. -/
theorem objectPointMap_eq_basePointMap (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R))) (y : 𝒳.val.val.obj)
    (hy : 𝒳.val.val.p.obj y = Deformation.Artin.baseOver B S hS A hA)
    (t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y)) :
    objectPointMap B S hS 𝒳 y t =
      basePointMap B S hS 𝒳 A hA y hy ((BigFppfOver.toScheme B S hS).map (eqToHom hy) t) := by
  simp only [basePointMap]
  congr 1
  show t = ((BigFppfOver.toScheme B S hS).map (eqToHom hy) ≫
    (BigFppfOver.toScheme B S hS).map (eqToHom hy.symm)) t
  rw [← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
    CategoryTheory.Functor.map_id]
  rfl


/-- **A minimal prime of `A` is the generic point of an irreducible component of `Spec A`.** -/
theorem closure_baseOverPoint_mem_irreducibleComponents (A : Deformation.Artin.FormalBase S)
    (hA : B.Contains (Spec (.of A.R))) {P : Ideal A.R} (hP : P ∈ minimalPrimes A.R) :
    closure {baseOverPoint B S hS A hA ⟨P, hP.1.1⟩} ∈
      irreducibleComponents ((BigFppfOver.toScheme B S hS).obj
        (Deformation.Artin.baseOver B S hS A hA)) := by
  exact (closure_singleton_mem_irreducibleComponents_iff_mem_minimalPrimes _).2 hP

/-- **The closure of the point of an object over `Spec A` at a prime, through a chart.** For a
morphism `m : y ⟶ x` of `𝒳` from an object over `Spec A` to an object over a scheme `U`, lying
over `g : Spec A ⟶ U`, the closure of the point of `y` at a prime `P` is the closure of the image,
under the chart map of `x`, of the closure of `g P` in `U`. -/
theorem closure_basePointMap_eq_of_hom (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R))) {y x : 𝒳.val.val.obj}
    (hy : 𝒳.val.val.p.obj y = Deformation.Artin.baseOver B S hS A hA) (m : y ⟶ x)
    (P : PrimeSpectrum A.R) :
    letI := Stack.pointTopology B S hS 𝒳.val
    closure {basePointMap B S hS 𝒳 A hA y hy P} =
      closure (chartPointMap B S hS (𝒳.val.val.p.obj x) 𝒳
          (Bicategory.InducedBicategory.mkHom
            (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))) ''
        closure {(BigFppfOver.toScheme B S hS).map (eqToHom hy.symm ≫ 𝒳.val.val.p.map m)
          (baseOverPoint B S hS A hA P)}) := by
  let := Stack.pointTopology B S hS 𝒳.val
  simp only [basePointMap]
  rw [objectPointMap_map B S hS 𝒳 m, ← Scheme.Hom.comp_apply,
    ← CategoryTheory.Functor.map_comp]
  exact closure_singleton_chartPointMap_eq B S hS _ 𝒳 _ _

/-- **Through a flat morphism to a chart, a minimal prime of `A` goes to the generic point of an
irreducible component.** -/
theorem closure_map_baseOverPoint_mem_irreducibleComponents (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (A : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R))) {y x : 𝒳.val.val.obj}
    (hy : 𝒳.val.val.p.obj y = Deformation.Artin.baseOver B S hS A hA) (m : y ⟶ x)
    (hm : Flat ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map m)))
    {P : Ideal A.R} (hP : P ∈ minimalPrimes A.R) :
    closure {(BigFppfOver.toScheme B S hS).map (eqToHom hy.symm ≫ 𝒳.val.val.p.map m)
        (baseOverPoint B S hS A hA ⟨P, hP.1.1⟩)} ∈
      irreducibleComponents ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) := by
  have : Flat ((BigFppfOver.toScheme B S hS).map (eqToHom hy.symm ≫ 𝒳.val.val.p.map m)) := by
    rw [CategoryTheory.Functor.map_comp, eqToHom_map]
    infer_instance
  exact closure_singleton_mem_irreducibleComponents_of_generalizingMap (Flat.generalizingMap _)
    (closure_baseOverPoint_mem_irreducibleComponents B S hS A hA hP)


/-- **The point map of an object over `Spec A` is natural in comparison morphisms.** If
`m : y' ⟶ y` lies, through the identifications of the two bases with spectra, over
`Spec φ : Spec A' ⟶ Spec A`, then the point of `y'` at a prime `P'` of `A'` is the point of `y`
at `φ⁻¹ P'`. -/
theorem basePointMap_comap (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (A A' : Deformation.Artin.FormalBase S) (hA : B.Contains (Spec (.of A.R)))
    (hA' : B.Contains (Spec (.of A'.R))) {y' y : 𝒳.val.val.obj}
    (hy' : 𝒳.val.val.p.obj y' = Deformation.Artin.baseOver B S hS A' hA')
    (hy : 𝒳.val.val.p.obj y = Deformation.Artin.baseOver B S hS A hA) (m : y' ⟶ y)
    (φ : A.R →+* A'.R)
    (hφ : (BigFppfOver.toScheme B S hS).map (eqToHom hy'.symm ≫ 𝒳.val.val.p.map m ≫ eqToHom hy) =
      Spec.map (CommRingCat.ofHom φ))
    (P' : PrimeSpectrum A'.R) :
    basePointMap B S hS 𝒳 A' hA' y' hy' P' =
      basePointMap B S hS 𝒳 A hA y hy (PrimeSpectrum.comap φ P') := by
  simp only [basePointMap]
  rw [objectPointMap_map B S hS 𝒳 m, objectPointMap_eq_basePointMap B S hS 𝒳 A hA y hy]
  simp only [basePointMap]
  congr 2
  have h := congrArg (fun g => g (baseOverPoint B S hS A' hA' P')) hφ
  simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply] at h
  exact h

variable {B S hS} in
/-- **A realization meets its level `0` at the closed point.** For a realization `y` of a formal
object `ξ` and any arrow `b : z ⟶ ξ_0`, every point of the scheme `z` lies over maps, along
`b` followed by the arrow `ξ_0 ⟶ y`, to the closed point of `Spec A`: that arrow lies over
`Spec(A/𝔪) ⟶ Spec A`. -/
theorem _root_.Deformation.Artin.FormalObject.Realization.toScheme_map_eq_closedPoint
    {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}
    {ξ : Deformation.Artin.FormalObject B S hS p} {hA : B.Contains (Spec (.of ξ.base.R))}
    {y : F} {hy : p.obj y = Deformation.Artin.baseOver B S hS ξ.base hA}
    (R : ξ.Realization hA y hy) {z : F} (b : z ⟶ ξ.level 0)
    (s : (BigFppfOver.toScheme B S hS).obj (p.obj z)) :
    (BigFppfOver.toScheme B S hS).map (eqToHom hy)
        ((BigFppfOver.toScheme B S hS).map (p.map (b ≫ R.r 0)) s) =
      baseOverPoint B S hS ξ.base hA (closedPoint ξ.base.R) := by
  rw [CategoryTheory.Functor.map_comp p b (R.r 0), R.map_eq 0, ← Scheme.Hom.comp_apply,
    ← CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  simp only [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply]
  generalize (BigFppfOver.toScheme B S hS).map (eqToHom _) _ = q
  show (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal ξ.base.R ^ (0 + 1))))) q =
    (closedPoint ξ.base.R : PrimeSpectrum ξ.base.R)
  apply PrimeSpectrum.ext
  refine ((maximalIdeal.isMaximal ξ.base.R).eq_of_le
    (PrimeSpectrum.isPrime _).ne_top ?_).symm
  intro w hw
  show Ideal.Quotient.mk _ w ∈ q.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hw)]
  exact q.asIdeal.zero_mem

end AlgebraicStacks

section Versal

variable (D : VersalSituation.{u, w})
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
  (x₀ : D.𝒳.val.val.obj)
  (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

/-- The point `x₀ ∈ |𝒳|` of an object `x₀` of `𝒳` lying over the spectrum of a field `k`. -/
def VersalSituation.fieldPoint : AlgebraicStacks.points D.B D.S D.hS D.𝒳 :=
  AlgebraicStacks.objectPointMap D.B D.S D.hS D.𝒳 x₀
    ((eqToHom (congrArg Over.left hx₀).symm :
      Spec (.of k) ⟶ (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj x₀))
      (closedPoint k))

/-- **The closed point of `Spec A` maps to `x₀`.** The level `0` of a versal formal object
receives `x₀`, and its realization `y` restricts to it over `Spec(A/𝔪) ⟶ Spec A`, whose image is
the closed point. -/
theorem basePointMap_closedPoint
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy
        (closedPoint (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base).R) =
      VersalSituation.fieldPoint D iΛ x₀ hx₀ := by
  unfold VersalSituation.fieldPoint
  rw [AlgebraicStacks.objectPointMap_map D.B D.S D.hS D.𝒳
    (((Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).objects (ξ.level 0)).arrow ≫ Ry.r 0),
    AlgebraicStacks.objectPointMap_eq_basePointMap D.B D.S D.hS D.𝒳
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy]
  congr 1
  have h := Ry.toScheme_map_eq_closedPoint
    ((Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).objects (ξ.level 0)).arrow
    ((eqToHom (congrArg Over.left hx₀).symm :
      Spec (.of k) ⟶ (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj x₀))
      (closedPoint k))
  exact h.symm

end Versal


/-! ### Properties of the realizations of versal formal objects

The proof of Stacks 0DR2 (`AlgebraicGeometry.Stack.flatObject_of_realization_of_isVersal`) shows
that a property of objects of `𝒳` holds at every realization `Spec A ⟶ 𝒳` of every versal formal
object as soon as it ascends along morphisms lying over flat morphisms of schemes, descends along
morphisms lying over flat surjective ones, and holds at smooth objects: Step III reaches the
restriction of a smooth chart to a completed local ring, which maps to the chart over a flat
morphism, and Steps I and II move along faithfully flat comparisons. This section runs that
argument for an arbitrary such property. -/

section Realizations

variable (D : VersalSituation.{u, w}) (Pr : D.𝒳.val.val.obj → Prop)

/-- Every realization `Spec A ⟶ 𝒳` of every versal formal object at the point `x₀ : Spec k ⟶ 𝒳`,
for every presentation of `x₀` over an affine open `Spec Λ` of `S`, has the property `Pr`. -/
def RealizationsSatisfy (x₀ : D.𝒳.val.val.obj) (k : Type u) [Field k] : Prop :=
  ∀ (Λ : Type u) [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (_hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection),
    Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ →
    ∀ (hA : D.B.Contains (Spec (.of ξ.base))) (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA),
      (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ).Realization hA y hy →
      Pr y

/-- A morphism of the site whose conjugate by the transports of its endpoints is flat and
surjective on schemes is itself flat and surjective on schemes: the transports can be
eliminated. -/
private alias flat_and_surjective_inclusionMap_of_conj :=
  AlgebraicGeometry.Stack.flat_and_surjective_of_toScheme_map_eq

/-- `Pr` ascends along morphisms of `𝒳` lying over flat morphisms of schemes. -/
def AscendsAlongFlat : Prop :=
  ∀ ⦃y' y : D.𝒳.val.val.obj⦄ (m : y' ⟶ y),
    Flat (D.B.inclusion.map (D.𝒳.val.val.p.map m).left) → Pr y → Pr y'

/-- `Pr` descends along morphisms of `𝒳` lying over flat surjective morphisms of schemes. -/
def DescendsAlongFlatSurjective : Prop :=
  ∀ ⦃y' y : D.𝒳.val.val.obj⦄ (m : y' ⟶ y),
    Flat (D.B.inclusion.map (D.𝒳.val.val.p.map m).left) →
      Surjective (D.B.inclusion.map (D.𝒳.val.val.p.map m).left) → Pr y' → Pr y

variable {D Pr}

/-- **Step I, for a property.** If one realization of one versal formal object at `x₀` has a
property which ascends along flat and descends along flat surjective morphisms, then every
realization of every versal formal object at `x₀` has it: by part (1) of Stacks 0DR1 two
realizations are comparable over the faithfully flat `Spec A' ⟶ Spec A'[[t₁, …, t_r]]`. -/
theorem realizationsSatisfy_of (hasc : AscendsAlongFlat D Pr)
    (hdesc : DescendsAlongFlatSurjective D Pr) {k : Type u} [Field k] (x₀ : D.𝒳.val.val.obj)
    {Λ : Type u} [CommRing Λ] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ D.S)
    (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (hPy : Pr y) :
    RealizationsSatisfy D Pr x₀ k := by
  intro Λ' _ _ iΛ' hiΛ' hx₀' hfinite' ξ' hξ' hA' y' hy' Ry'
  rcases exists_powerSeries_comparison_realization D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite
      hfinite' ξ hξ ξ' hξ' Ry Ry' with ⟨r, e, -, m, hm⟩ | ⟨r, e, -, m, hm⟩
  · obtain ⟨hfl, hsu⟩ := flat_and_surjective_inclusionMap_of_conj D hy hy'
      (D.𝒳.val.val.p.map m) hm (flat_and_surjective_specMap_symm_comp_C r e)
    exact hdesc m hfl hsu hPy
  · obtain ⟨hfl, -⟩ := flat_and_surjective_inclusionMap_of_conj D hy' hy
      (D.𝒳.val.val.p.map m) hm (flat_and_surjective_specMap_symm_comp_C r e)
    exact hasc m hfl hPy

/-- **Step II, for a property, from the extension to the point.** If every realization at a point
`xₗ` over a finite extension `l/k` has the property, so does every realization at `x₀`: by part
(2) of Stacks 0DR1 each of the latter receives a morphism over a flat surjective morphism from
one of the former. -/
theorem realizationsSatisfy_of_extension (hdesc : DescendsAlongFlatSurjective D Pr)
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l] [Algebra Λ l]
    [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hη : eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l)))
    (hl : RealizationsSatisfy D Pr xₗ l) :
    ∀ (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection),
    Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ →
    ∀ (hA : D.B.Contains (Spec (.of ξ.base))) (y : D.𝒳.val.val.obj)
      (hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA),
      (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
        hfinite ξ).Realization hA y hy →
      Pr y := by
  intro ξ hξ hA y hy Ry
  obtain ⟨ξ', hξ', hA', y', hy', Ry', m, hmflat, hmsurj⟩ :=
    extensionRealizationComparison D Λ k l iΛ hiΛ x₀ hx₀ hfinite ξ hξ hA y hy Ry xₗ hxₗ η hη
  exact hdesc m hmflat hmsurj (hl Λ iΛ hiΛ hxₗ _ ξ' hξ' hA' y' hy' Ry')

/-- **Step II, for a property, from the point to the extension.** If one realization of one
versal formal object at `x₀` has the property, every realization at a point `xₗ` over a finite
extension `l/k` has it. -/
theorem realizationsSatisfy_extension_of (hasc : AscendsAlongFlat D Pr)
    (hdesc : DescendsAlongFlatSurjective D Pr)
    {Λ k l : Type u} [CommRing Λ] [Field k] [Field l] [Algebra Λ k] [Algebra k l] [Algebra Λ l]
    [IsScalarTower Λ k l] [Module.Finite k l]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (hPy : Pr y)
    (xₗ : D.𝒳.val.val.obj)
    (hxₗ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj xₗ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ l)) ≫ iΛ))
    (η : xₗ ⟶ x₀)
    (hη : eqToHom (congrArg Over.left hxₗ).symm ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).map η).left ≫
      eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap k l))) :
    RealizationsSatisfy D Pr xₗ l := by
  obtain ⟨ξ', hξ', hA', y', hy', Ry', m, hmflat, -⟩ :=
    extensionRealizationComparison D Λ k l iΛ hiΛ x₀ hx₀ hfinite ξ hξ hA y hy Ry xₗ hxₗ η hη
  exact realizationsSatisfy_of hasc hdesc xₗ iΛ hiΛ hxₗ _ ξ' hξ' Ry' (hasc m hmflat hPy)

/-- **Every realization of a versal formal object has a property which holds at smooth objects,
ascends along flat and descends along flat surjective morphisms.** This is the argument of the
proof of Stacks 0DR2 for an arbitrary such property: Step III reaches the restriction of a smooth
chart to the completion of a local ring, which maps to the chart over a flat morphism, and the two
directions of Step II carry the property to `x₀`. -/
theorem satisfies_of_realization (hasc : AscendsAlongFlat D Pr)
    (hdesc : DescendsAlongFlatSurjective D Pr)
    (hsm : ∀ x, smoothObject.{u, w} D.B D.S D.hS D.𝒳 x → Pr x)
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy) :
    Pr y := by
  obtain ⟨l, _, _, _, _, hkl, xₗ, hxₗ, η, hη, xR, ζ, hζ, alg, hΛ, -, ⟨x, hxsm, r, hr⟩,
    hζversal, _, _, hfin, η', hη'⟩ := exists_chartPoint_closedFibre_and_restriction D iΛ hiΛ x₀
      hx₀ hfinite
  obtain ⟨hAc, yc, hyc, ⟨Ryc⟩, mc, hmc⟩ :=
    exists_realization_closedFibre_hom D xR ζ hζ Λ iΛ hΛ hζversal
  have hl : RealizationsSatisfy D Pr xₗ l :=
    realizationsSatisfy_extension_of hasc hdesc iΛ hiΛ (ζ.level 0) (ζ.basePoint Λ iΛ hΛ)
      (locallyOfFiniteType_and_quasiCompact_residueField_formalBase D ζ Λ iΛ hΛ) _ hζversal
      Ryc (hasc mc hmc (hasc r hr (hsm x hxsm))) xₗ hxₗ η' hη'
  exact realizationsSatisfy_of_extension hdesc iΛ hiΛ x₀ hx₀ hfinite xₗ hxₗ η hη hl ξ hξ hA y hy
    Ry

end Realizations

/-- **The stack of the versal situation is locally Noetherian.** It is locally of finite type
over the locally Noetherian scheme `S`, whose algebraic stack is locally Noetherian by
Stacks 04YF, so Stacks 06R6 applies to the structure morphism. -/
theorem VersalSituation.hasLocallyNoetherianAtlas (D : VersalSituation.{u, w}) :
    HasPropertyOnSomeSchemeAtlas D.B D.S D.hS (fun X : Scheme.{u} => IsLocallyNoetherian X)
      D.𝒳 := by
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have hS : HasPropertyOnSomeSchemeAtlas D.B D.S D.hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (schemeStack.{u, w} D.B D.S D.hS (Over.mk (𝟙 (D.B.obj D.hS)))) :=
    (exists_scheme_atlas_iff_scheme.{u, w} D.B D.S D.hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) _).2 D.locallyNoetherian
  exact AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType D.B D.S D.hS
    (structureMorphism D.B D.S D.hS D.𝒳) D.locallyFiniteType hS


/-- **The preimage of a minimal prime under a ring map with flat spectrum map is minimal.**
Going down: the spectrum map is generalizing, so it carries generic points of irreducible
components to generic points of irreducible components. -/
@[ega "IV 2.3.4" "(iii), special case"]
theorem comap_mem_minimalPrimes_of_flat {R R' : Type u} [CommRing R] [CommRing R']
    (φ : R →+* R') (hφ : Flat (Spec.map (CommRingCat.ofHom φ))) {P' : Ideal R'}
    (hP' : P' ∈ minimalPrimes R') : P'.comap φ ∈ minimalPrimes R := by
  have h₁ := (closure_singleton_mem_irreducibleComponents_iff_mem_minimalPrimes
    (⟨P', hP'.1.1⟩ : PrimeSpectrum R')).2 hP'
  exact (closure_singleton_mem_irreducibleComponents_iff_mem_minimalPrimes
    (PrimeSpectrum.comap φ ⟨P', hP'.1.1⟩)).1
    (closure_singleton_mem_irreducibleComponents_of_generalizingMap
      (X := Spec (.of R')) (Y := Spec (.of R))
      (Flat.generalizingMap (Spec.map (CommRingCat.ofHom φ))) h₁)

/-! ### Stacks 0DRB -/

section Branches

variable (D : VersalSituation.{u, w})
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
  (x₀ : D.𝒳.val.val.obj)
  (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hfinite : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
    QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
  (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
    D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
  {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
  {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
    (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
  (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
    hfinite ξ).Realization hA y hy)

include hiΛ hξ Ry in
/-- **The claim of the proof of Stacks 0DRB.** The morphism `j : Spec A ⟶ 𝒳` of Stacks 0DR1
sends the generic point of every irreducible component of `Spec A` to the generic point of an
irreducible component of `|𝒳|`. By Stacks 0DR2 `j` is flat; the property ascends along flat and
descends along flat surjective morphisms, and at a smooth chart it is Stacks 0DR5, so the
argument of Stacks 0DR2 carries it to every realization. -/
theorem sendsGenericPointsToComponents_of_realization :
    AlgebraicStacks.SendsGenericPointsToComponents D.B D.S D.hS D.𝒳 y :=
  satisfies_of_realization (Pr := AlgebraicStacks.SendsGenericPointsToComponents D.B D.S D.hS D.𝒳)
    (fun _ _ m hm h => h.of_flat D.B D.S D.hS D.𝒳 m hm)
    (fun _ _ m _ hs h => h.of_surjective D.B D.S D.hS D.𝒳 m hs)
    (fun _ hx => AlgebraicStacks.sendsGenericPointsToComponents_of_smoothObject D.B D.S D.hS D.𝒳
      D.hasLocallyNoetherianAtlas hx)
    iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry

include hiΛ hξ Ry in
/-- **The surjectivity mechanism of the proof of Stacks 0DRB.** Every irreducible component of
`|𝒳|` through the image of a point of `Spec A` is the closure of the image of a generic point of
`Spec A` specializing to it: at a smooth chart this is openness of the chart (Stacks 06R7) over a
locally Noetherian scheme, and the property ascends along flat and descends along flat
surjective morphisms by going down. -/
theorem reachesComponents_of_realization :
    AlgebraicStacks.ReachesComponents D.B D.S D.hS D.𝒳 y :=
  satisfies_of_realization (Pr := AlgebraicStacks.ReachesComponents D.B D.S D.hS D.𝒳)
    (fun _ _ m hm h => h.of_flat D.B D.S D.hS D.𝒳 m hm)
    (fun _ _ m hm hs h => h.of_flat_of_surjective D.B D.S D.hS D.𝒳 m hm hs)
    (fun _ hx => AlgebraicStacks.reachesComponents_of_smoothObject D.B D.S D.hS D.𝒳
      D.hasLocallyNoetherianAtlas hx)
    iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry

include hiΛ hξ Ry in
/-- **The image of a formal branch.** For a minimal prime `P` of the versal ring `A`, the closure
of the image of `P` under `Spec A ⟶ 𝒳` is an irreducible component of `|𝒳|` containing `x₀`. -/
theorem closure_basePointMap_mem_irreducibleComponents {P : Ideal ξ.base}
    (hP : P ∈ minimalPrimes ξ.base) :
    letI := Stack.pointTopology D.B D.S D.hS D.𝒳.val
    closure {AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy ⟨P, hP.1.1⟩} ∈
      irreducibleComponents (AlgebraicStacks.points D.B D.S D.hS D.𝒳) ∧
    VersalSituation.fieldPoint D iΛ x₀ hx₀ ∈
      closure {AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy ⟨P, hP.1.1⟩} := by
  let := Stack.pointTopology D.B D.S D.hS D.𝒳.val
  constructor
  · have hc := AlgebraicStacks.closure_baseOverPoint_mem_irreducibleComponents D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA (P := P) hP
    have : Flat ((BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy.symm)) := by
      rw [eqToHom_map]
      infer_instance
    exact sendsGenericPointsToComponents_of_realization D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry
      ((BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy.symm)
        (AlgebraicStacks.baseOverPoint D.B D.S D.hS
          (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA ⟨P, hP.1.1⟩))
      (closure_singleton_mem_irreducibleComponents_of_generalizingMap
        (Flat.generalizingMap _) hc)
  · rw [← basePointMap_closedPoint D iΛ x₀ hx₀ hfinite ξ Ry, ← specializes_iff_mem_closure]
    refine Specializes.map ?_ (AlgebraicStacks.continuous_basePointMap D.B D.S D.hS D.𝒳
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy)
    rw [← PrimeSpectrum.le_iff_specializes]
    exact IsLocalRing.le_maximalIdeal (hP.1.1 : P.IsPrime).ne_top

include Ry in
/-- **Stacks 0DRB, the map.** The canonical map from the formal branches of `𝒳` through `x₀`,
read off the versal ring `A = ξ.base` of a versal formal object `ξ` with realization
`y : Spec A ⟶ 𝒳` (Stacks 0DR1), to the irreducible components of `|𝒳|` containing `x₀`: a
branch, recorded by its generic point `P`, goes to the closure of the image of `P` under
`Spec A ⟶ 𝒳`. -/
def formalBranchComponent
    (P : formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩) :
    letI := Stack.pointTopology D.B D.S D.hS D.𝒳.val
    {Z : Set (AlgebraicStacks.points D.B D.S D.hS D.𝒳) //
      Z ∈ irreducibleComponents (AlgebraicStacks.points D.B D.S D.hS D.𝒳) ∧
        VersalSituation.fieldPoint D iΛ x₀ hx₀ ∈ Z} :=
  letI := Stack.pointTopology D.B D.S D.hS D.𝒳.val
  ⟨closure {AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy ⟨P.1, P.2.1.1⟩},
    closure_basePointMap_mem_irreducibleComponents D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry P.2⟩

/-- The value of the map of Stacks 0DRB at a branch is the closure of the image of its generic
point. -/
theorem coe_formalBranchComponent
    (P : formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩) :
    letI := Stack.pointTopology D.B D.S D.hS D.𝒳.val
    (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry P).1 =
      closure {AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy
          ⟨P.1, P.2.1.1⟩} :=
  rfl

/-- **Stacks 0DRB, surjectivity.** Every irreducible component of `|𝒳|` through `x₀` is the image
of a formal branch: the closed point of `Spec A` maps to `x₀`, and every component through the
image of a point of `Spec A` is the closure of the image of a generic point of `Spec A`. -/
theorem formalBranchComponent_surjective :
    Function.Surjective (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry) := by
  let := Stack.pointTopology D.B D.S D.hS D.𝒳.val
  rintro ⟨Z, hZ, hx₀Z⟩
  set F := Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base
  let t : (BigFppfOver.toScheme D.B D.S D.hS).obj (D.𝒳.val.val.p.obj y) :=
    (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy.symm)
      (AlgebraicStacks.baseOverPoint D.B D.S D.hS F hA (closedPoint F.R))
  have ht : AlgebraicStacks.objectPointMap D.B D.S D.hS D.𝒳 y t ∈ Z := by
    rwa [← basePointMap_closedPoint D iΛ x₀ hx₀ hfinite ξ Ry] at hx₀Z
  obtain ⟨z, -, hz, hzZ⟩ := reachesComponents_of_realization D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry
    t Z hZ ht
  have : Flat ((BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy)) := by
    rw [eqToHom_map]
    infer_instance
  let Q : PrimeSpectrum F.R := (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy) z
  have hQ : closure {Q} ∈ irreducibleComponents (PrimeSpectrum F.R) :=
    closure_singleton_mem_irreducibleComponents_of_generalizingMap (Flat.generalizingMap _) hz
  refine ⟨⟨Q.asIdeal,
    (closure_singleton_mem_irreducibleComponents_iff_mem_minimalPrimes Q).1 hQ⟩, Subtype.ext ?_⟩
  show closure {AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳 F hA y hy Q} = Z
  rw [← hzZ, AlgebraicStacks.objectPointMap_eq_basePointMap D.B D.S D.hS D.𝒳 F hA y hy z]

include Ry in
/-- **Stacks 0DRB, canonicity.** The map of Stacks 0DRB is compatible with the identification of
formal branches along comparison morphisms. Let `y' : Spec A' ⟶ 𝒳` realize a versal formal object
at a point `x₁` (for instance `x₀` itself, or a point over a finite extension of `k`), and let
`m : y' ⟶ y` lie over `Spec φ` for a ring map `φ : A ⟶ A'` with flat spectrum map, as do the
comparisons of parts (1) and (2) of Stacks 0DR1. Then `φ⁻¹` carries the branches of `A'` to
branches of `A`, and a branch and its image have the same image component. -/
theorem formalBranchComponent_comparison
    {Λ' l : Type u} [CommRing Λ'] [Field l] [Algebra Λ' l]
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : _root_.AlgebraicGeometry.IsOpenImmersion iΛ')
    (x₁ : D.𝒳.val.val.obj)
    (hx₁ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₁ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' l)) ≫ iΛ'))
    (hfinite' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' l)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' l)) ≫ iΛ'))
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₁ hx₁).projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ' D.𝒳.val.val.p x₁ hx₁ D.𝒳.val.property).cofibered ξ')
    {hA' : D.B.Contains (Spec (.of ξ'.base))} {y' : D.𝒳.val.val.obj}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₁ hx₁
      hfinite' ξ').Realization hA' y' hy')
    (m : y' ⟶ y) (φ : (ξ.base : Type u) →+* ξ'.base)
    (hφ : (BigFppfOver.toScheme D.B D.S D.hS).map
        (eqToHom hy'.symm ≫ D.𝒳.val.val.p.map m ≫ eqToHom hy) =
      Spec.map (CommRingCat.ofHom φ))
    (hflat : Flat (Spec.map (CommRingCat.ofHom φ)))
    (P' : formalBranches D iΛ' hiΛ' x₁ hx₁ hfinite' ξ'.base ⟨ξ', rfl, hξ'⟩) :
    ∃ hP : P'.1.comap φ ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩,
      (formalBranchComponent D iΛ' hiΛ' x₁ hx₁ hfinite' ξ' hξ' Ry' P').1 =
        (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry ⟨_, hP⟩).1 := by
  refine ⟨comap_mem_minimalPrimes_of_flat φ hflat P'.2, ?_⟩
  rw [coe_formalBranchComponent, coe_formalBranchComponent]
  congr 2
  exact AlgebraicStacks.basePointMap_comap D.B D.S D.hS D.𝒳
    (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base)
    (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA hA' hy' hy m φ hφ _

include Ry in
/-- **Stacks 0DRB, independence of the versal ring.** For two versal formal objects at `x₀`, over
versal rings `A` and `A'` and for any two presentations of `x₀`, with realizations
`y : Spec A ⟶ 𝒳` and `y' : Spec A' ⟶ 𝒳`, after possibly swapping them there is a ring map
`φ : A' ⟶ A` with faithfully flat spectrum map — the comparison `A ≅ A'[[t₁, …, t_r]]` of part
(1) of Stacks 0DR1 — along which the maps of Stacks 0DRB agree: this is the identification of
the formal branches read off different versal rings, and the map does not depend on the choice. -/
theorem formalBranchComponent_independent
    {Λ' : Type u} [CommRing Λ'] [Algebra Λ' k]
    (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : _root_.AlgebraicGeometry.IsOpenImmersion iΛ')
    (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (hfinite' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
    (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
    (hξ' : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered ξ')
    {hA' : D.B.Contains (Spec (.of ξ'.base))} {y' : D.𝒳.val.val.obj}
    {hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA'}
    (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p x₀ hx₀'
      hfinite' ξ').Realization hA' y' hy') :
    (∃ φ : (ξ'.base : Type u) →+* ξ.base, Flat (Spec.map (CommRingCat.ofHom φ)) ∧
      Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∀ P, ∃ hP : P.1.comap φ ∈ formalBranches D iΛ' hiΛ' x₀ hx₀' hfinite' ξ'.base ⟨ξ', rfl, hξ'⟩,
        (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry P).1 =
          (formalBranchComponent D iΛ' hiΛ' x₀ hx₀' hfinite' ξ' hξ' Ry' ⟨_, hP⟩).1) ∨
    (∃ φ : (ξ.base : Type u) →+* ξ'.base, Flat (Spec.map (CommRingCat.ofHom φ)) ∧
      Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
      ∀ P', ∃ hP : P'.1.comap φ ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩,
        (formalBranchComponent D iΛ' hiΛ' x₀ hx₀' hfinite' ξ' hξ' Ry' P').1 =
          (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry ⟨_, hP⟩).1) := by
  rcases exists_powerSeries_comparison_realization D iΛ hiΛ iΛ' hiΛ' x₀ hx₀ hx₀' hfinite
      hfinite' ξ hξ ξ' hξ' Ry Ry' with ⟨r, e, -, m, hm⟩ | ⟨r, e, -, m, hm⟩
  · obtain ⟨hfl, hsu⟩ := flat_and_surjective_specMap_symm_comp_C r e
    exact Or.inl ⟨_, hfl, hsu, fun P => formalBranchComponent_comparison D iΛ' hiΛ' x₀ hx₀'
      hfinite' ξ' hξ' Ry' iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry m _ hm hfl P⟩
  · obtain ⟨hfl, hsu⟩ := flat_and_surjective_specMap_symm_comp_C r e
    exact Or.inr ⟨_, hfl, hsu, fun P' => formalBranchComponent_comparison D iΛ hiΛ x₀ hx₀
      hfinite ξ hξ Ry iΛ' hiΛ' x₀ hx₀' hfinite' ξ' hξ' Ry' m _ hm hfl P'⟩


include Ry in
/-- **Stacks 0DRB.** In the situation of Definition 0DRA — an algebraic stack `𝒳` locally of
finite type over a locally Noetherian scheme `S`, a point `x₀ : Spec k ⟶ 𝒳` with `k` of finite
type over `S`, and a versal ring `A` to `𝒳` at `x₀`, the base of a versal formal object `ξ` with
its morphism `y : Spec A ⟶ 𝒳` of Stacks 0DR1 — there is a canonical surjection from the formal
branches of `𝒳` through `x₀` to the irreducible components of `|𝒳|` containing `x₀`.

The map is `AlgebraicGeometry.Stack.formalBranchComponent`: a branch, recorded by its generic
point `P`, goes to the closure of the image of `P` under `Spec A ⟶ 𝒳`
(`AlgebraicGeometry.Stack.coe_formalBranchComponent`). The first conjunct is surjectivity. The
second is canonicity: for any other versal formal object at `x₀`, for any presentation of `x₀`,
with versal ring `A'` and realization `y'`, the two maps agree along the identification of the
branches of `A` and `A'` by the faithfully flat comparison of part (1) of Stacks 0DR1, in
whichever direction it goes. -/
@[stacks 0DRB]
theorem formalBranchComponent_surjective_and_canonical :
    Function.Surjective (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry) ∧
    ∀ (Λ' : Type u) [CommRing Λ'] [Algebra Λ' k]
      (iΛ' : Spec (.of Λ') ⟶ D.S) (hiΛ' : _root_.AlgebraicGeometry.IsOpenImmersion iΛ')
      (hx₀' : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
      (hfinite' : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ') ∧
        QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ' k)) ≫ iΛ'))
      (ξ' : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ'
        (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀').projection)
      (hξ' : Deformation.IsVersal
        (Deformation.Artin.predeformationCategory_isPredeformationCategory
          D.B D.hS iΛ' D.𝒳.val.val.p x₀ hx₀' D.𝒳.val.property).cofibered ξ')
      (hA' : D.B.Contains (Spec (.of ξ'.base))) (y' : D.𝒳.val.val.obj)
      (hy' : D.𝒳.val.val.p.obj y' = Deformation.Artin.baseOver D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ' hfinite' ξ'.base) hA')
      (Ry' : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ' D.𝒳.val.val.p
        x₀ hx₀' hfinite' ξ').Realization hA' y' hy'),
      (∃ φ : (ξ'.base : Type u) →+* ξ.base, Flat (Spec.map (CommRingCat.ofHom φ)) ∧
        Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∀ P, ∃ hP : P.1.comap φ ∈ formalBranches D iΛ' hiΛ' x₀ hx₀' hfinite' ξ'.base
            ⟨ξ', rfl, hξ'⟩,
          (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry P).1 =
            (formalBranchComponent D iΛ' hiΛ' x₀ hx₀' hfinite' ξ' hξ' Ry' ⟨_, hP⟩).1) ∨
      (∃ φ : (ξ.base : Type u) →+* ξ'.base, Flat (Spec.map (CommRingCat.ofHom φ)) ∧
        Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
        ∀ P', ∃ hP : P'.1.comap φ ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩,
          (formalBranchComponent D iΛ' hiΛ' x₀ hx₀' hfinite' ξ' hξ' Ry' P').1 =
            (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry ⟨_, hP⟩).1) :=
  ⟨formalBranchComponent_surjective D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry,
    fun _ _ _ iΛ' hiΛ' hx₀' hfinite' ξ' hξ' _ _ _ Ry' =>
      formalBranchComponent_independent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry iΛ' hiΛ' hx₀' hfinite'
        ξ' hξ' Ry'⟩

end Branches

end AlgebraicGeometry.Stack

end

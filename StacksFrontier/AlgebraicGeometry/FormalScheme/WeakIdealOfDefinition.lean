module

public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.LocallyTopologicallyRingedSpace
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.Topology.Algebra.RingLimits

/-!
# Weak ideals of definition on a formal scheme

An *ideal sheaf* on a locally topologically ringed space is a sheaf of ideals of the structure
sheaf, and it is a *weak ideal of definition* when its ideal of sections over every affine
formal open subscheme is a weak ideal of definition of the topological ring of sections there
(Stacks 0AMV); a family of ideal sheaves is a *fundamental system of weak ideals of definition*
when each member is one and their ideals of sections form a neighbourhood basis of zero on
every affine formal open. The condition is local: it holds as soon as it holds on the affine
formal opens refining the members of an affine open covering.

## Main definitions

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`: an ideal of the ring of
  sections over every open, stable under restriction, and local.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.IsWeakIdealOfDefinitionOn`: the
  sectionwise weak ideal-of-definition condition over a class of opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IsFundamentalSystemOfWeakIdealsOfDefinitionOn`:
  a family of ideal sheaves whose ideals of sections are a neighbourhood basis of zero.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isWeakIdealOfDefinition_iSup`:
  the condition passes to a finite union of opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isWeakIdealOfDefinition_of_isCompact`: on a quasi-compact open the condition is local.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isWeakIdealOfDefinitionOn_of_cover`
  and `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover`: the two conditions may be checked on
  the opens of the class refining the members of a covering (used for the locality sentence of
  Stacks 0AIV in `WeakIdealOfDefinitionLocalityMcQuillan`).

## Implementation notes

An ideal sheaf is recorded as a sheaf of ideals of the sections of `𝒪_X`, which is what a
subsheaf `ℐ ⊆ 𝒪_X` of ideals amounts to: `IdealSheaf.map_mem` is the subpresheaf condition and
`IdealSheaf.mem_of_locally_mem` the sheaf condition, that a section belonging to the ideal near
every point of its domain belongs to it. The sections of `𝒪_X` carry a topology, so the
predicate of Stacks 0AMV applies to the ideal of sections with that topology, and no
admissibility hypothesis is needed to state it.

The class of opens playing the role of the affine formal open subschemes is the parameter `𝒜`.
Nothing below depends on which opens those are, so the statements apply to any designated class,
in particular to the weak affine formal opens of a formal scheme in the sense of McQuillan
(Stacks 0AI3) and to the affine formal opens of one à la EGA
(`AlgebraicGeometry.IsFormalScheme`). Correspondingly, the two geometric facts about that class
which the locality criterion consumes — that its members are quasi-compact, and that its members
contained in a given open cover that open — are hypotheses of
`IdealSheaf.isWeakIdealOfDefinitionOn_of_cover` rather than consequences of `𝒜`.

Topological nilpotence of a section over a union is read off from the sheaf condition: the
structure sheaf takes values in topological rings, so the limit presenting the sections over a
union carries the topology induced from the sections over the members of the covering and over
their pairwise intersections (`TopCat.induced_of_isLimit`, the limit being preserved by the
forgetful functor of Stacks 0B23).

## References

* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0AI3](https://stacks.math.columbia.edu/tag/0AI3)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

/-- An *ideal sheaf* `ℐ ⊆ 𝒪_X` on a locally topologically ringed space: an ideal of the ring of
sections over every open, carried into one another by restriction, and local, in that a section
belonging to the ideal in a neighbourhood of every point of its domain belongs to it. -/
structure IdealSheaf (X : LTRS.{u}) where
  /-- The ideal of sections over an open. -/
  ideal : (U : Opens X) → Ideal (X.presheaf.obj (op U)).α
  /-- Restriction carries the ideal of an open into the ideal of a smaller one. -/
  map_mem : ∀ {U V : Opens X} (h : V ≤ U) {s : (X.presheaf.obj (op U)).α},
    s ∈ ideal U → (X.presheaf.map (homOfLE h).op).1 s ∈ ideal V
  /-- A section belonging to the ideal near every point of its domain belongs to it. -/
  mem_of_locally_mem : ∀ {U : Opens X} {s : (X.presheaf.obj (op U)).α},
    (∀ x ∈ U, ∃ (V : Opens X) (h : V ≤ U),
        x ∈ V ∧ (X.presheaf.map (homOfLE h).op).1 s ∈ ideal V) → s ∈ ideal U

namespace IdealSheaf

variable {X : LTRS.{u}}

/-- The structure sheaf itself, the unit ideal sheaf. -/
instance : Inhabited (IdealSheaf X) :=
  ⟨{ ideal := fun _ => ⊤
     map_mem := by intros; exact Submodule.mem_top
     mem_of_locally_mem := by intros; exact Submodule.mem_top }⟩

/-- An ideal sheaf on `X` is a *weak ideal of definition* over a class `𝒜` of opens — the
affine formal open subschemes — when its ideal of sections over every open of `𝒜` is a weak
ideal of definition of the topological ring of sections there. -/
@[stacks 0AIV "the definition, over a class `𝒜` of affine formal opens"]
def IsWeakIdealOfDefinitionOn (I : IdealSheaf X) (𝒜 : Opens X → Prop) : Prop :=
  ∀ U : Opens X, 𝒜 U → TopologicalRing.IsWeakIdealOfDefinition (I.ideal U)

end IdealSheaf

/-- A family of ideal sheaves on `X` is a *fundamental system of weak ideals of definition* over
a class `𝒜` of opens — the affine formal open subschemes — when each member is a weak ideal of
definition and, over every open of `𝒜`, their ideals of sections form a neighbourhood basis of
zero in the topological ring of sections. -/
@[stacks 0AIV "the definition, over a class `𝒜` of affine formal opens"]
def IsFundamentalSystemOfWeakIdealsOfDefinitionOn {X : LTRS.{u}} (𝒮 : Set (IdealSheaf X))
    (𝒜 : Opens X → Prop) : Prop :=
  (∀ I ∈ 𝒮, I.IsWeakIdealOfDefinitionOn 𝒜) ∧
    ∀ U : Opens X, 𝒜 U → (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)

namespace IdealSheaf

variable {X : LTRS.{u}}

/-- An element of the vertex of a limit cone of topological rings all of whose components are
topologically nilpotent is topologically nilpotent: the vertex carries the topology induced by
the projections. -/
private theorem isTopologicallyNilpotent_of_isLimit {J : Type u} [Category.{u} J]
    {F : J ⥤ TopCommRingCat.{u}} {c : Cone F} (hc : IsLimit c) (x : c.pt.α)
    (hx : ∀ j, IsTopologicallyNilpotent ((c.π.app j).1 x)) :
    IsTopologicallyNilpotent x := by
  have ht : (inferInstance : TopologicalSpace c.pt.α) =
      ⨅ j, TopologicalSpace.induced ((c.π.app j).1 : c.pt.α → (F.obj j).α) inferInstance :=
    TopCat.induced_of_isLimit ((forget₂ TopCommRingCat TopCat).mapCone c)
      (isLimitOfPreserves (forget₂ TopCommRingCat TopCat) hc)
  change Filter.Tendsto (x ^ ·) Filter.atTop (nhds (0 : c.pt.α))
  rw [congrArg (fun t : TopologicalSpace c.pt.α => @nhds _ t (0 : c.pt.α)) ht, nhds_iInf,
    Filter.tendsto_iInf]
  intro j
  rw [nhds_induced, Filter.tendsto_comap_iff]
  simpa only [Function.comp_def, map_pow, map_zero, IsTopologicallyNilpotent] using hx j

/-- A section over a union of opens whose restriction to each member is topologically nilpotent
is itself topologically nilpotent. -/
private theorem isTopologicallyNilpotent_of_iSup {ι : Type u} (U : ι → Opens X)
    (x : (X.presheaf.obj (op (iSup U))).α)
    (hx : ∀ i, IsTopologicallyNilpotent ((X.presheaf.map (homOfLE (le_iSup U i)).op).1 x)) :
    IsTopologicallyNilpotent x := by
  obtain ⟨hc⟩ := X.IsSheaf.isSheafPairwiseIntersections U
  refine isTopologicallyNilpotent_of_isLimit hc x fun j => ?_
  induction j using Opposite.rec with
  | op j =>
    cases j with
    | single i => exact hx i
    | pair i j =>
      have heq : (X.presheaf.map (homOfLE ((inf_le_left : U i ⊓ U j ≤ U i).trans
            (le_iSup U i))).op).1 x =
          (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).1
            ((X.presheaf.map (homOfLE (le_iSup U i)).op).1 x) := by
        change (X.presheaf.map _).1 x = ((X.presheaf.map _ ≫ X.presheaf.map _).1 x)
        rw [← X.presheaf.map_comp]
        rfl
      change IsTopologicallyNilpotent ((X.presheaf.map (homOfLE ((inf_le_left :
        U i ⊓ U j ≤ U i).trans (le_iSup U i))).op).1 x)
      rw [heq]
      exact IsTopologicallyNilpotent.map (X.presheaf.map _).2 (hx i)

/-- The ideal of sections over a finite union of opens is a weak ideal of definition as soon as
the ideals of sections over the members are: it is cut out by finitely many open conditions, and
topological nilpotence is read off from the covering. -/
theorem isWeakIdealOfDefinition_iSup (I : IdealSheaf X) {ι : Type u} [Finite ι]
    (U : ι → Opens X)
    (hI : ∀ i, TopologicalRing.IsWeakIdealOfDefinition (I.ideal (U i))) :
    TopologicalRing.IsWeakIdealOfDefinition (I.ideal (iSup U)) := by
  have hmem (x : (X.presheaf.obj (op (iSup U))).α) :
      x ∈ I.ideal (iSup U) ↔
        ∀ i, (X.presheaf.map (homOfLE (le_iSup U i)).op).1 x ∈ I.ideal (U i) := by
    refine ⟨fun hx i => I.map_mem (le_iSup U i) hx, fun hx => I.mem_of_locally_mem fun y hy => ?_⟩
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ⟨U i, le_iSup U i, hi, hx i⟩
  refine ⟨?_, fun x hx => isTopologicallyNilpotent_of_iSup U x fun i =>
    (hI i).2 _ (I.map_mem (le_iSup U i) hx)⟩
  have heq : (I.ideal (iSup U) : Set _) =
      ⋂ i, ((X.presheaf.map (homOfLE (le_iSup U i)).op).1) ⁻¹' (I.ideal (U i) : Set _) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, hmem]
  rw [heq]
  exact isOpen_iInter_of_finite fun i => (hI i).1.preimage (X.presheaf.map _).2

/-- On a quasi-compact open the weak ideal-of-definition condition is local: if every point of
`V` has a neighbourhood inside `V` over which the ideal of sections is a weak ideal of
definition, then so is the ideal of sections over `V`. -/
theorem isWeakIdealOfDefinition_of_isCompact (I : IdealSheaf X) (V : Opens X)
    (hV : IsCompact (V : Set X))
    (hlocal : ∀ x ∈ V, ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal W)) :
    TopologicalRing.IsWeakIdealOfDefinition (I.ideal V) := by
  classical
  choose W hWV hxW hW using fun x : V => hlocal x x.property
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V => (W x : Set X))
    (fun x => (W x).isOpen) fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hsup : ⨆ x : s, W x = V := by
    refine le_antisymm (iSup_le fun x => hWV x) fun x hx => ?_
    obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (le_iSup (fun y : s => W y) ⟨y, hys⟩) hxy
  rw [← hsup]
  exact I.isWeakIdealOfDefinition_iSup (fun x : s => W x) fun x => hW x

/-- The locality of the weak ideal-of-definition condition over an arbitrary class of opens. Let
`𝒰` be a covering of `X` and let `𝒜` be a class of quasi-compact opens whose members contained in
an open cover that open. Then an ideal sheaf is a weak ideal of definition over `𝒜` as soon as its
ideals of sections over the members of `𝒜` contained in a member of `𝒰` are weak ideals of
definition.

For the weak affine formal opens of a formal scheme in the sense of McQuillan both geometric
hypotheses hold, and this gives the locality sentence of Stacks 0AIV in its corrected form,
`IdealSheaf.isWeakIdealOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`. Checking the members
of `𝒰` alone would not do: an ideal sheaf can have the zero ideal of global sections and the unit
ideal on an open avoiding one point. -/
theorem isWeakIdealOfDefinitionOn_of_cover (I : IdealSheaf X) (𝒜 : Opens X → Prop)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hcompact : ∀ U : Opens X, 𝒜 U → IsCompact (U : Set X))
    (hrefine : ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ 𝒜 U)
    (hI : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U)) :
    I.IsWeakIdealOfDefinitionOn 𝒜 := by
  intro T hT
  refine I.isWeakIdealOfDefinition_of_isCompact T (hcompact T hT) fun x hx => ?_
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp (show x ∈ sSup 𝒰 by rw [hcover]; trivial)
  obtain ⟨U, hUW, hxU, hU⟩ := hrefine V hV (V ⊓ T) inf_le_left x ⟨hxV, hx⟩
  exact ⟨U, hUW.trans inf_le_right, hxU, hI V hV U (hUW.trans inf_le_left) hU⟩

/-- The two geometric hypotheses of `isWeakIdealOfDefinitionOn_of_cover` are satisfied outright,
and the criterion then has content: on a space with finitely many points every open is
quasi-compact and refines itself, so a covering by two opens already gives the condition over
every open — including the total space, which neither member of the covering contains. -/
example (X : LTRS.{u}) [Finite ↥X] (I : IdealSheaf X) (V₁ V₂ : Opens X) (hV : V₁ ⊔ V₂ = ⊤)
    (hI : ∀ U : Opens X, U ≤ V₁ ∨ U ≤ V₂ →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U)) :
    I.IsWeakIdealOfDefinitionOn fun _ => True :=
  I.isWeakIdealOfDefinitionOn_of_cover _ {V₁, V₂} (by rw [sSup_pair]; exact hV)
    (fun U _ => (Set.toFinite (U : Set X)).isCompact)
    (fun _ _ W _ _ hx => ⟨W, le_rfl, hx, trivial⟩)
    fun V hV' U hU _ => hI U (by
      rcases (Set.mem_insert_iff.mp hV') with rfl | hV'
      · exact Or.inl hU
      · exact Or.inr (hU.trans_eq (Set.mem_singleton_iff.mp hV')))

end IdealSheaf

/-- The weak ideal-of-definition half of a fundamental system transported along a covering, over
an arbitrary class of opens, with the neighbourhood-basis half given on every open of `𝒜`, by
`IdealSheaf.isWeakIdealOfDefinitionOn_of_cover`. The locality sentence of Stacks 0AIV for
fundamental systems, where the neighbourhood-basis half is also checked on the opens inside the
covering members, is
`isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`. -/
theorem isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover {X : LTRS.{u}}
    (𝒮 : Set (IdealSheaf X)) (𝒜 : Opens X → Prop)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hcompact : ∀ U : Opens X, 𝒜 U → IsCompact (U : Set X))
    (hrefine : ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ 𝒜 U)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U))
    (hbasis : ∀ U : Opens X, 𝒜 U →
      (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 𝒜 :=
  ⟨fun I hI => I.isWeakIdealOfDefinitionOn_of_cover 𝒜 𝒰 hcover hcompact hrefine (h𝒮 I hI), hbasis⟩

/-- The two geometric hypotheses of
`isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover` are satisfied outright, and the criterion
then has content: on a space with finitely many points every open is quasi-compact and refines
itself, so a covering by two opens already gives the fundamental-system condition over every
open — including the total space, which neither member of the covering contains. -/
example (X : LTRS.{u}) [Finite ↥X] (𝒮 : Set (IdealSheaf X)) (V₁ V₂ : Opens X)
    (hV : V₁ ⊔ V₂ = ⊤)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ U : Opens X, U ≤ V₁ ∨ U ≤ V₂ →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U))
    (hbasis : ∀ U : Opens X, (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 fun _ => True :=
  isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover 𝒮 _ {V₁, V₂}
    (by rw [sSup_pair]; exact hV)
    (fun U _ => (Set.toFinite (U : Set X)).isCompact)
    (fun _ _ W _ _ hx => ⟨W, le_rfl, hx, trivial⟩)
    (fun I hI V hV' U hU _ => h𝒮 I hI U (by
      rcases (Set.mem_insert_iff.mp hV') with rfl | hV'
      · exact Or.inl hU
      · exact Or.inr (hU.trans_eq (Set.mem_singleton_iff.mp hV'))))
    fun U _ => hbasis U

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end

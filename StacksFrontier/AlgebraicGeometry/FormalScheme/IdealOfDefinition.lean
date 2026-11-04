module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumGlobalSectionsIso
public import StacksFrontier.AlgebraicGeometry.FormalScheme.SchemeToFormalScheme
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinition
public import StacksFrontier.Topology.Algebra.AdicTopology.IdealOfDefinition

/-!
# Ideals of definition on a formal scheme à la EGA

An ideal sheaf `ℐ ⊆ 𝒪_𝔛` on a formal scheme à la EGA is an *ideal of definition* when its ideal
of sections over every affine formal open subscheme `𝔘` is an ideal of definition of the
admissible topological ring `𝒪_𝔛(𝔘)` (Stacks 07E8), and a family of ideal sheaves is a
*fundamental system of ideals of definition* when each member is one and their ideals of sections
form a neighbourhood basis of zero over every affine formal open. This is **Stacks 0AIW**, the
counterpart for formal schemes à la EGA of the weak notions of Stacks 0AIV recorded in
`StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinition`.

Both conditions are local: they hold as soon as they hold on the affine formal opens refining the
members of an affine open covering. On a quasi-compact formal scheme a fundamental system of
*weak* ideals of definition eventually consists of ideals of definition, because an open ideal
contained in an ideal of definition is an ideal of definition and only finitely many members of
an affine open covering have to be checked.

## Main definitions

* `AlgebraicGeometry.IsAffineFormalOpen`: an open whose induced locally topologically ringed
  space is the formal spectrum of an admissible topological ring.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.IsIdealOfDefinitionOn`: the
  sectionwise ideal-of-definition condition over a class of opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IsFundamentalSystemOfIdealsOfDefinitionOn`:
  a family of ideal sheaves of definition whose ideals of sections are a neighbourhood basis
  of zero.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isWeakIdealOfDefinitionOn_of_isIdealOfDefinitionOn` and
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_isFundamentalSystemOfIdealsOfDefinitionOn`:
  the conditions of Stacks 0AIW are stronger than those of Stacks 0AIV.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isIdealOfDefinition_iSup`: the
  condition passes to a finite union of opens.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isIdealOfDefinition_of_isCompact`: on a quasi-compact open the condition is local.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.isIdealOfDefinitionOn_of_cover`
  and `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.isFundamentalSystemOfIdealsOfDefinitionOn_of_cover`: the two conditions may be checked on the
  opens of the class refining the members of a covering.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn`: on a
  quasi-compact space a fundamental system of weak ideals of definition is eventually a family of
  ideals of definition on a finite affine open covering.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.exists_isIdealOfDefinition_of_isFormalScheme`:
  the same on a quasi-compact formal scheme à la EGA, where the class of opens is the class of
  affine formal open subschemes and the two geometric inputs are discharged.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf`
  `.isIdealOfDefinitionOn_of_isWeakIdealOfDefinitionOn_of_fg`: the two notions agree on a
  finitely generated ideal sheaf.
* `AlgebraicGeometry.isPreAdmissible_of_isAffineFormalOpen`: the ring of sections over an affine
  formal open subscheme has an ideal of definition.

## Implementation notes

The ideal sheaves are those of `WeakIdealOfDefinition.lean`, and the class of opens playing the
role of the affine formal open subschemes is again a parameter `𝒜`, so that the statements apply
to the affine formal opens of a formal scheme à la EGA (`AlgebraicGeometry.IsFormalScheme`) as
well as to any other designated class. Correspondingly the geometric facts about that class which
the criteria consume are hypotheses rather than consequences of `𝒜`: that its members are
quasi-compact, that its members contained in a given open cover that open, and — for the eventual
statement, where the source uses that `𝒪_𝔛(𝔘)` is admissible — that the ring of sections over a
member has an ideal of definition at all. For the class of genuine affine formal open subschemes
`AlgebraicGeometry.IsAffineFormalOpen` the last two are theorems rather than hypotheses —
`AlgebraicGeometry.isFormalScheme_iff_forall_isAffineFormalOpen` and
`AlgebraicGeometry.isPreAdmissible_of_isAffineFormalOpen` — and
`exists_isIdealOfDefinition_of_isFormalScheme` is the resulting statement about a formal scheme
à la EGA.

Cofinality of the powers of the ideal of sections over a finite union is read off from the sheaf
condition exactly as topological nilpotence is in the weak case: the structure sheaf takes values
in topological rings, so the sections over a union carry the topology induced from the sections
over the members of the covering and over their pairwise intersections, and the neighbourhoods of
zero are therefore the finite intersections of the preimages of neighbourhoods of zero over the
members (`nhds_zero_eq_iInf_comap_of_isLimit`).

The source states the eventual conclusion for the affine formal opens of the whole formal scheme.
As with the locality criterion of Stacks 0AIV, that step needs the transfer of the
ideal-of-definition condition from an affine formal open to the smaller affine formal opens inside
it, which this library does not carry; the conclusion is therefore stated for the members of the
finite affine open covering produced by quasi-compactness, which is what the source's own argument
("we only need to check on the finitely many members of an affine open covering") establishes.
Combining it with `IdealSheaf.isIdealOfDefinitionOn_of_cover` is what a consumer does next.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 07E8](https://stacks.math.columbia.edu/tag/07E8)
* [Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped Topology

namespace AlgebraicGeometry

universe u

/-! ### Affine formal open subschemes -/

/-- An open `U` of an object `X` of `LTRS` is an *affine formal open subscheme* when the locally
topologically ringed space induced on `U` is isomorphic to the formal spectrum of an admissible
topological ring. This is exactly the condition that `AlgebraicGeometry.IsFormalScheme` asks of a
neighbourhood of every point, and it is the class of opens on which Stacks 0AIW imposes its
conditions. -/
def IsAffineFormalOpen (X : LTRS.{u}) (U : Opens X) : Prop :=
  ∃ A : TopCommRingCat.{u}, ∃ hlinear : IsLinearTopology A.α A.α,
    letI := hlinear
    TopologicalRing.IsAdmissible A.α ∧
      Nonempty (X.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A.α)

/-- An object of `LTRS` is a formal scheme à la EGA exactly when each of its points has an affine
formal open neighbourhood. -/
theorem isFormalScheme_iff_forall_isAffineFormalOpen (X : LTRS.{u}) :
    IsFormalScheme X ↔ ∀ x : X, ∃ U : Opens X, x ∈ U ∧ IsAffineFormalOpen X U where
  mp hX x := by
    obtain ⟨U, hxU, A, hlinear, hA⟩ := hX x
    exact ⟨U, hxU, A, hlinear, hA⟩
  mpr hX x := by
    obtain ⟨U, hxU, A, hlinear, hA⟩ := hX x
    exact ⟨U, hxU, A, hlinear, hA⟩

/-- The image of an ideal of definition under an isomorphism of topological rings is an ideal of
definition: the isomorphism is a surjective homeomorphism, so it carries the ideal onto an open
set and its powers onto the powers. -/
private theorem isIdealOfDefinition_map_of_iso {R S : TopCommRingCat.{u}} (e : R ≅ S)
    {I : Ideal R.α} (hI : TopologicalRing.IsIdealOfDefinition I) :
    TopologicalRing.IsIdealOfDefinition (I.map e.hom.1) := by
  let homeo := TopCat.homeoOfIso ((forget₂ TopCommRingCat TopCat).mapIso e)
  have hsurj : Function.Surjective (e.hom.1 : R.α → S.α) := homeo.surjective
  refine ⟨?_, fun V hV => ?_⟩
  · rw [Ideal.map_eq_image_of_surjective _ hsurj]
    exact homeo.isOpenMap _ hI.1
  · obtain ⟨n, hn⟩ := hI.2 _ (e.hom.2.tendsto' _ _ (map_zero e.hom.1) hV)
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, Ideal.map_eq_image_of_surjective _ hsurj]
    exact Set.image_subset_iff.mpr hn

/-- The ring of sections over an affine formal open subscheme is pre-admissible: it is isomorphic
as a topological ring to the admissible ring whose formal spectrum the open is, by **Stacks
0AHY**, and an isomorphism of topological rings carries an ideal of definition to one. -/
theorem isPreAdmissible_of_isAffineFormalOpen {X : LTRS.{u}} {U : Opens X}
    (hU : IsAffineFormalOpen X U) :
    TopologicalRing.IsPreAdmissible (X.presheaf.obj (op U)).α := by
  obtain ⟨A, hlinear, hA, ⟨chart⟩⟩ := hU
  let _ := hlinear
  let sectionIso : A ≅ X.presheaf.obj (op U) :=
    spfGammaIso A.α hA ≪≫ PresheafedSpace.Γ.mapIso chart.op ≪≫
      X.presheaf.mapIso (eqToIso (congrArg op U.isOpenEmbedding_obj_top))
  obtain ⟨I, hI⟩ := hA.1
  exact ⟨I.map sectionIso.hom.1, isIdealOfDefinition_map_of_iso sectionIso hI⟩

end AlgebraicGeometry

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

namespace IdealSheaf

variable {X : LTRS.{u}}

/-- An ideal sheaf on `X` is an *ideal of definition* over a class `𝒜` of opens — the affine
formal open subschemes — when its ideal of sections over every open of `𝒜` is an ideal of
definition of the topological ring of sections there. -/
@[stacks 0AIW "the definition, over a class `𝒜` of affine formal opens"]
def IsIdealOfDefinitionOn (I : IdealSheaf X) (𝒜 : Opens X → Prop) : Prop :=
  ∀ U : Opens X, 𝒜 U → TopologicalRing.IsIdealOfDefinition (I.ideal U)

/-- An ideal of definition is a weak ideal of definition: the comparison of Stacks 0AIW with
Stacks 0AIV, over the same class of opens. -/
theorem isWeakIdealOfDefinitionOn_of_isIdealOfDefinitionOn {I : IdealSheaf X}
    {𝒜 : Opens X → Prop} (hI : I.IsIdealOfDefinitionOn 𝒜) :
    I.IsWeakIdealOfDefinitionOn 𝒜 :=
  fun U hU => TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition (hI U hU)

/-- Over a class of opens on which the sections carry a linear topology and the ideal sheaf is
finitely generated, the condition of Stacks 0AIW is no stronger than the condition of Stacks
0AIV: a finitely generated weak ideal of definition is an ideal of definition. -/
theorem isIdealOfDefinitionOn_of_isWeakIdealOfDefinitionOn_of_fg {I : IdealSheaf X}
    {𝒜 : Opens X → Prop}
    (hlin : ∀ U : Opens X, 𝒜 U →
      IsLinearTopology (X.presheaf.obj (op U)).α (X.presheaf.obj (op U)).α)
    (hfg : ∀ U : Opens X, 𝒜 U → (I.ideal U).FG)
    (hI : I.IsWeakIdealOfDefinitionOn 𝒜) :
    I.IsIdealOfDefinitionOn 𝒜 := by
  intro U hU
  let _ := hlin U hU
  exact TopologicalRing.isIdealOfDefinition_of_isWeakIdealOfDefinition (hI U hU) (hfg U hU)

end IdealSheaf

/-- A family of ideal sheaves on `X` is a *fundamental system of ideals of definition* over a
class `𝒜` of opens — the affine formal open subschemes — when each member is an ideal of
definition and, over every open of `𝒜`, their ideals of sections form a neighbourhood basis of
zero in the topological ring of sections. -/
@[stacks 0AIW "the definition, over a class `𝒜` of affine formal opens"]
def IsFundamentalSystemOfIdealsOfDefinitionOn {X : LTRS.{u}} (𝒮 : Set (IdealSheaf X))
    (𝒜 : Opens X → Prop) : Prop :=
  (∀ I ∈ 𝒮, I.IsIdealOfDefinitionOn 𝒜) ∧
    ∀ U : Opens X, 𝒜 U → (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)

/-- A fundamental system of ideals of definition is a fundamental system of weak ideals of
definition: the comparison of Stacks 0AIW with Stacks 0AIV, over the same class of opens. -/
theorem isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_isFundamentalSystemOfIdealsOfDefinitionOn
    {X : LTRS.{u}} {𝒮 : Set (IdealSheaf X)} {𝒜 : Opens X → Prop}
    (h𝒮 : IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 𝒜) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 𝒜 :=
  ⟨fun I hI => IdealSheaf.isWeakIdealOfDefinitionOn_of_isIdealOfDefinitionOn (h𝒮.1 I hI), h𝒮.2⟩

namespace IdealSheaf

variable {X : LTRS.{u}}

/-- The neighbourhoods of zero in the vertex of a limit cone of topological rings are the
infimum of the preimages of the neighbourhoods of zero in the components: the vertex carries the
topology induced by the projections. -/
private theorem nhds_zero_eq_iInf_comap_of_isLimit {J : Type u} [Category.{u} J]
    {F : J ⥤ TopCommRingCat.{u}} {c : Cone F} (hc : IsLimit c) :
    nhds (0 : c.pt.α) =
      ⨅ j, Filter.comap ((c.π.app j).1 : c.pt.α → (F.obj j).α) (nhds 0) := by
  have ht : (inferInstance : TopologicalSpace c.pt.α) =
      ⨅ j, TopologicalSpace.induced ((c.π.app j).1 : c.pt.α → (F.obj j).α) inferInstance :=
    TopCat.induced_of_isLimit ((forget₂ TopCommRingCat TopCat).mapCone c)
      (isLimitOfPreserves (forget₂ TopCommRingCat TopCat) hc)
  rw [congrArg (fun t : TopologicalSpace c.pt.α => @nhds _ t (0 : c.pt.α)) ht, nhds_iInf]
  exact iInf_congr fun j => by rw [nhds_induced, map_zero]

/-- The neighbourhoods of zero in the sections over a union of opens contain the finite
intersections of the preimages of the neighbourhoods of zero in the sections over the members:
the topology of the sections over the union is induced by the restrictions. -/
private theorem nhds_zero_iSup_le {ι : Type u} (U : ι → Opens X) :
    (⨅ i, Filter.comap ((X.presheaf.map (homOfLE (le_iSup U i)).op).1 :
        (X.presheaf.obj (op (iSup U))).α → (X.presheaf.obj (op (U i))).α) (nhds 0)) ≤
      nhds (0 : (X.presheaf.obj (op (iSup U))).α) := by
  obtain ⟨hc⟩ := X.IsSheaf.isSheafPairwiseIntersections U
  refine le_trans ?_ (nhds_zero_eq_iInf_comap_of_isLimit hc).ge
  refine le_iInf fun j => ?_
  induction j using Opposite.rec with
  | op j =>
    cases j with
    | single i => exact iInf_le _ i
    | pair i i' =>
      have hfun : (fun x : (X.presheaf.obj (op (iSup U))).α =>
            (X.presheaf.map (homOfLE ((inf_le_left : U i ⊓ U i' ≤ U i).trans
              (le_iSup U i))).op).1 x) =
          (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U i' ≤ U i)).op).1 ∘
            (X.presheaf.map (homOfLE (le_iSup U i)).op).1 := by
        funext x
        show (X.presheaf.map _).1 x = ((X.presheaf.map _ ≫ X.presheaf.map _).1 x)
        rw [← X.presheaf.map_comp]
        rfl
      show (⨅ i, Filter.comap _ (nhds 0)) ≤
        Filter.comap (fun x => (X.presheaf.map (homOfLE ((inf_le_left : U i ⊓ U i' ≤ U i).trans
          (le_iSup U i))).op).1 x) (nhds 0)
      rw [hfun, ← Filter.comap_comap]
      refine (iInf_le _ i).trans (Filter.comap_mono (Filter.tendsto_iff_comap.mp ?_))
      exact (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U i' ≤ U i)).op).2.tendsto'
        0 0 (map_zero _)

/-- The ideal of sections over a finite union of opens is an ideal of definition as soon as the
ideals of sections over the members are: it is open by the weak criterion, and a neighbourhood of
zero over the union contains a finite intersection of preimages of neighbourhoods of zero over
the members, each of which contains a power of the ideal there. -/
theorem isIdealOfDefinition_iSup (I : IdealSheaf X) {ι : Type u} [Finite ι]
    (U : ι → Opens X)
    (hI : ∀ i, TopologicalRing.IsIdealOfDefinition (I.ideal (U i))) :
    TopologicalRing.IsIdealOfDefinition (I.ideal (iSup U)) := by
  classical
  refine ⟨(I.isWeakIdealOfDefinition_iSup U fun i =>
    TopologicalRing.isWeakIdealOfDefinition_of_isIdealOfDefinition (hI i)).1, fun V hV => ?_⟩
  obtain ⟨t, ht, rfl⟩ := (Filter.mem_iInf_of_finite V).mp (nhds_zero_iSup_le U hV)
  choose W hW hWt using fun i => Filter.mem_comap.mp (ht i)
  choose n hn using fun i => (hI i).2 (W i) (hW i)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ i, n i ≤ m := by
    obtain ⟨m, hm⟩ := (Set.finite_range n).bddAbove
    exact ⟨m, fun i => hm (Set.mem_range_self i)⟩
  refine ⟨m, fun x hx => Set.mem_iInter.mpr fun i => hWt i ?_⟩
  have hmaple : Ideal.map ((X.presheaf.map (homOfLE (le_iSup U i)).op).1)
      (I.ideal (iSup U)) ≤ I.ideal (U i) :=
    Ideal.map_le_iff_le_comap.mpr fun s hs => I.map_mem (le_iSup U i) hs
  have hpow : (X.presheaf.map (homOfLE (le_iSup U i)).op).1 x ∈ (I.ideal (U i)) ^ m :=
    pow_le_pow_left' hmaple m
      (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)
  exact hn i (Ideal.pow_le_pow_right (hm i) hpow)

/-- On a quasi-compact open the ideal-of-definition condition is local: if every point of `V` has
a neighbourhood inside `V` over which the ideal of sections is an ideal of definition, then so is
the ideal of sections over `V`. -/
theorem isIdealOfDefinition_of_isCompact (I : IdealSheaf X) (V : Opens X)
    (hV : IsCompact (V : Set X))
    (hlocal : ∀ x ∈ V, ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
      TopologicalRing.IsIdealOfDefinition (I.ideal W)) :
    TopologicalRing.IsIdealOfDefinition (I.ideal V) := by
  classical
  choose W hWV hxW hW using fun x : V => hlocal x x.property
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V => (W x : Set X))
    (fun x => (W x).isOpen) fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hsup : ⨆ x : s, W x = V := by
    refine le_antisymm (iSup_le fun x => hWV x) fun x hx => ?_
    obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (le_iSup (fun y : s => W y) ⟨y, hys⟩) hxy
  rw [← hsup]
  exact I.isIdealOfDefinition_iSup (fun x : s => W x) fun x => hW x

/-- **Stacks 0AIW**, the locality of the ideal-of-definition condition. Let `𝒰` be a covering of
`X` and let `𝒜` be a class of quasi-compact opens — the affine formal open subschemes — whose
members contained in an open cover that open. Then an ideal sheaf is an ideal of definition over
`𝒜` as soon as its ideals of sections over the members of `𝒜` contained in a member of `𝒰` are
ideals of definition.

Checking the members of `𝒰` alone would not do, for the same reason as in the weak case
(`IdealSheaf.isWeakIdealOfDefinitionOn_of_cover`). -/
@[stacks 0AIW "it suffices to check the ideal-of-definition condition on an affine open \
covering, CORRECTED: the condition is checked on the members of the class contained in a \
covering member, not on the covering members themselves, which is false as the source states \
it; the quasi-compactness `hcompact` and the refinement `hrefine` of the class of affine \
formal opens are part of the statement"]
theorem isIdealOfDefinitionOn_of_cover (I : IdealSheaf X) (𝒜 : Opens X → Prop)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hcompact : ∀ U : Opens X, 𝒜 U → IsCompact (U : Set X))
    (hrefine : ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ 𝒜 U)
    (hI : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      TopologicalRing.IsIdealOfDefinition (I.ideal U)) :
    I.IsIdealOfDefinitionOn 𝒜 := by
  intro T hT
  refine I.isIdealOfDefinition_of_isCompact T (hcompact T hT) fun x hx => ?_
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp (show x ∈ sSup 𝒰 by rw [hcover]; trivial)
  obtain ⟨U, hUW, hxU, hU⟩ := hrefine V hV (V ⊓ T) inf_le_left x ⟨hxV, hx⟩
  exact ⟨U, hUW.trans inf_le_right, hxU, hI V hV U (hUW.trans inf_le_left) hU⟩

end IdealSheaf

/-- **Stacks 0AIW**, the locality of the fundamental-system condition: the neighbourhood-basis
half is a condition on the individual opens of `𝒜`, so only the ideal-of-definition half has to
be transported along the covering, by `IdealSheaf.isIdealOfDefinitionOn_of_cover`. -/
@[stacks 0AIW "it suffices to check the fundamental-system condition on an affine open covering, \
CORRECTED in the same way as the ideal-of-definition condition, and granting `hbasis`: the \
neighbourhood-basis half is a condition on each individual affine formal open and there is \
nothing about it to transport along a covering"]
theorem isFundamentalSystemOfIdealsOfDefinitionOn_of_cover {X : LTRS.{u}}
    (𝒮 : Set (IdealSheaf X)) (𝒜 : Opens X → Prop)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hcompact : ∀ U : Opens X, 𝒜 U → IsCompact (U : Set X))
    (hrefine : ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ 𝒜 U)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      TopologicalRing.IsIdealOfDefinition (I.ideal U))
    (hbasis : ∀ U : Opens X, 𝒜 U →
      (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 𝒜 :=
  ⟨fun I hI => I.isIdealOfDefinitionOn_of_cover 𝒜 𝒰 hcover hcompact hrefine (h𝒮 I hI), hbasis⟩

namespace IdealSheaf

variable {X : LTRS.{u}}

/-- A finite subfamily of a family of ideal sheaves that is downward directed sectionwise and
nonempty has a sectionwise lower bound inside the family. -/
private theorem exists_le_of_finset {𝒮 : Set (IdealSheaf X)} (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    {ι : Type*} (s : Finset ι) (f : ι → IdealSheaf X) (hf : ∀ i ∈ s, f i ∈ 𝒮) :
    ∃ K ∈ 𝒮, ∀ i ∈ s, ∀ W : Opens X, K.ideal W ≤ (f i).ideal W := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨K, hK⟩ := hne
    exact ⟨K, hK, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨K, hK, hKle⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    obtain ⟨L, hL, hLle⟩ := hdir K hK (f i) (hf i (Finset.mem_insert_self _ _))
    refine ⟨L, hL, fun j hj W => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hLle W).2
    · exact (hLle W).1.trans (hKle j hj W)

end IdealSheaf

/-- **Stacks 0AIW**, the eventual ideals of definition. Let `X` be quasi-compact and covered by
the members of a class `𝒜` of opens — the affine formal open subschemes — over each of which the
ring of sections has an ideal of definition, which on a formal scheme à la EGA is the
admissibility of `𝒪_𝔛(𝔘)`. Let `𝒮` be a nonempty, sectionwise downward directed fundamental
system of *weak* ideals of definition over `𝒜`. Then there is a finite covering of `X` by members
of `𝒜` and a member `I₀` of `𝒮` such that every member of `𝒮` below `I₀` has ideals of definition
for its ideals of sections over the covering: an open ideal contained in an ideal of definition is
an ideal of definition, and only the finitely many members of the covering have to be checked. -/
@[stacks 0AIW "`ℐ_λ` is an ideal of definition for `λ` large, RESTRICTED to the finite affine \
open covering that quasi-compactness produces, as in the source's own argument; the \
sectionwise directedness `hdir` and nonemptiness `hne` of the system are the source's \
directedness of the index set `Λ`, and `hadm` is the admissibility of the rings of sections \
over the members of the class of affine formal opens"]
theorem exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn
    {X : LTRS.{u}} [CompactSpace ↥X] (𝒮 : Set (IdealSheaf X)) (𝒜 : Opens X → Prop)
    (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (hfund : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 𝒜)
    (hbase : ∀ x : X, ∃ U : Opens X, x ∈ U ∧ 𝒜 U)
    (hadm : ∀ U : Opens X, 𝒜 U →
      TopologicalRing.IsPreAdmissible (X.presheaf.obj (op U)).α) :
    ∃ 𝒰 : Set (Opens X), 𝒰.Finite ∧ (∀ V ∈ 𝒰, 𝒜 V) ∧ sSup 𝒰 = ⊤ ∧
      ∃ I₀ ∈ 𝒮, ∀ I ∈ 𝒮, (∀ W : Opens X, I.ideal W ≤ I₀.ideal W) →
        ∀ V ∈ 𝒰, TopologicalRing.IsIdealOfDefinition (I.ideal V) := by
  classical
  choose U hxU hAU using hbase
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (U x : Set X))
    (fun x => (U x).isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩
  -- a member of the system small enough at a given point's affine formal open
  have hsmall : ∀ x : X, ∃ I ∈ 𝒮, TopologicalRing.IsIdealOfDefinition (I.ideal (U x)) := by
    intro x
    obtain ⟨J, hJ⟩ := hadm (U x) (hAU x)
    obtain ⟨I, hI, hIJ⟩ := (hfund.2 (U x) (hAU x)).mem_iff.mp
      (hJ.1.mem_nhds J.zero_mem)
    exact ⟨I, hI, TopologicalRing.isIdealOfDefinition_of_le_of_isOpen hJ
      (hfund.1 I hI (U x) (hAU x)).1 (SetLike.coe_subset_coe.mp hIJ)⟩
  choose K hK hKdef using hsmall
  obtain ⟨I₀, hI₀, hI₀le⟩ := IdealSheaf.exists_le_of_finset hne hdir s K fun x _ => hK x
  refine ⟨U '' (s : Set X), s.finite_toSet.image U, ?_, ?_, I₀, hI₀, ?_⟩
  · rintro V ⟨x, -, rfl⟩
    exact hAU x
  · refine le_antisymm le_top fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact Opens.mem_sSup.mpr ⟨U y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro I hI hIle V ⟨x, hx, rfl⟩
    exact TopologicalRing.isIdealOfDefinition_of_le_of_isOpen (hKdef x)
      (hfund.1 I hI (U x) (hAU x)).1 ((hIle (U x)).trans (hI₀le x hx (U x)))

/-- **Stacks 0AIW**, the eventual ideals of definition on a quasi-compact formal scheme à la EGA.
Here the class of opens is the class of affine formal open subschemes, so the two geometric
inputs of
`exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn` are discharged: the
affine formal opens cover `X` because `X` is a formal scheme, and the ring of sections over one of
them is pre-admissible by Stacks 0AHY. -/
@[stacks 0AIW "`ℐ_λ` is an ideal of definition for `λ` large, on a quasi-compact formal scheme \
à la EGA and RESTRICTED to the finite affine open covering that quasi-compactness produces, as \
in the source's own argument; only the sectionwise directedness `hdir` and nonemptiness `hne` \
of the system are carried, and they are the source's directedness of the index set `Λ`"]
theorem exists_isIdealOfDefinition_of_isFormalScheme {X : LTRS.{u}} [CompactSpace ↥X]
    (hX : IsFormalScheme X) (𝒮 : Set (IdealSheaf X)) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (hfund : IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen X)) :
    ∃ 𝒰 : Set (Opens X), 𝒰.Finite ∧ (∀ V ∈ 𝒰, IsAffineFormalOpen X V) ∧ sSup 𝒰 = ⊤ ∧
      ∃ I₀ ∈ 𝒮, ∀ I ∈ 𝒮, (∀ W : Opens X, I.ideal W ≤ I₀.ideal W) →
        ∀ V ∈ 𝒰, TopologicalRing.IsIdealOfDefinition (I.ideal V) :=
  exists_isIdealOfDefinition_of_isFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 _ hne hdir hfund
    ((isFormalScheme_iff_forall_isAffineFormalOpen X).mp hX)
    fun _ hU => isPreAdmissible_of_isAffineFormalOpen hU

namespace IdealSheaf

variable {X : LTRS.{u}}

/-! ### The ideal-of-definition condition is strictly stronger -/

/-- The pseudo-discretisation of a scheme has the same points as the scheme. -/
instance subsingleton_schemeToLTRSObj (Z : Scheme.{u}) [Subsingleton ↥Z] :
    Subsingleton ↥(schemeToLTRSObj Z) :=
  ⟨fun a b => @Subsingleton.elim ↥Z _ a b⟩

/-- On a scheme with at most one point, the nilradical of the ring of sections over each open is
an ideal sheaf of the pseudo-discretisation of the scheme (**Stacks 0AI0**). That the space has at
most one point is what makes the sheaf condition hold: a section nilpotent near every point of
its domain is nilpotent, because the only open with a point is the domain itself. On a general
space the order of nilpotence over a covering is unbounded and this fails. -/
noncomputable def nilradicalIdealSheaf (Z : Scheme.{u}) [Subsingleton ↥Z] :
    IdealSheaf (schemeToLTRSObj Z) where
  ideal U := nilradical ((schemeToLTRSObj Z).presheaf.obj (op U)).α
  map_mem := by
    intro U V hVU element hmem
    exact mem_nilradical.mpr
      ((mem_nilradical.mp hmem).map ((schemeToLTRSObj Z).presheaf.map (homOfLE hVU).op).1)
  mem_of_locally_mem := by
    intro U element hlocal
    by_cases hne : ∃ x, x ∈ U
    · obtain ⟨x, hx⟩ := hne
      obtain ⟨V, hVU, hxV, hmem⟩ := hlocal x hx
      obtain rfl : V = U := le_antisymm hVU fun y _ => by
        rw [Subsingleton.elim y x]; exact hxV
      have hhom : (homOfLE hVU).op = 𝟙 (op V) := rfl
      rw [hhom, (schemeToLTRSObj Z).presheaf.map_id] at hmem
      exact hmem
    · obtain rfl : U = ⊥ := le_antisymm (fun y hy => absurd ⟨y, hy⟩ hne) bot_le
      exact mem_nilradical.mpr ⟨1,
        @Subsingleton.elim (Z.presheaf.obj (op (⊥ : Opens ↥Z)))
          (CommRingCat.subsingleton_of_isTerminal Z.sheaf.isTerminalOfEmpty) _ _⟩

@[simp]
theorem nilradicalIdealSheaf_ideal (Z : Scheme.{u}) [Subsingleton ↥Z]
    (U : Opens ↥(schemeToLTRSObj Z)) :
    (nilradicalIdealSheaf Z).ideal U = nilradical ((schemeToLTRSObj Z).presheaf.obj (op U)).α :=
  rfl

/-- The sections over an open of the pseudo-discretisation of a one-point scheme are discrete. -/
private theorem discreteTopology_sections_of_subsingleton (Z : Scheme.{u}) [Subsingleton ↥Z]
    (U : Opens ↥(schemeToLTRSObj Z)) :
    DiscreteTopology ((schemeToLTRSObj Z).presheaf.obj (op U)).α :=
  ⟨pseudoDiscreteTopology_eq_bot Z.presheaf
    (Set.Subsingleton.isCompact fun _ _ _ _ => Subsingleton.elim _ _)⟩

/-- The nilradical ideal sheaf of a one-point scheme is a weak ideal of definition over every
class of opens: the sections over an open of a one-point space are discrete, so every ideal of
them is open, and a nilpotent element of a ring is topologically nilpotent. -/
theorem nilradicalIdealSheaf_isWeakIdealOfDefinitionOn (Z : Scheme.{u}) [Subsingleton ↥Z]
    (𝒜 : Opens ↥(schemeToLTRSObj Z) → Prop) :
    (nilradicalIdealSheaf Z).IsWeakIdealOfDefinitionOn 𝒜 := by
  intro U _
  let _ := discreteTopology_sections_of_subsingleton Z U
  exact ⟨isOpen_discrete _, fun _ hmem => (mem_nilradical.mp hmem).isTopologicallyNilpotent⟩

/-- If the nilradical ideal sheaf of a one-point scheme is an ideal of definition over a class of
opens containing `U`, then some power of the nilradical of the sections over `U` vanishes: those
sections are discrete, so `{0}` is a neighbourhood of zero. -/
theorem exists_pow_eq_bot_of_isIdealOfDefinitionOn_nilradicalIdealSheaf (Z : Scheme.{u})
    [Subsingleton ↥Z] {𝒜 : Opens ↥(schemeToLTRSObj Z) → Prop}
    {U : Opens ↥(schemeToLTRSObj Z)} (hU : 𝒜 U)
    (h : (nilradicalIdealSheaf Z).IsIdealOfDefinitionOn 𝒜) :
    ∃ n : ℕ, (nilradical ((schemeToLTRSObj Z).presheaf.obj (op U)).α) ^ n = ⊥ := by
  let _ := discreteTopology_sections_of_subsingleton Z U
  obtain ⟨n, hn⟩ := (h U hU).2 {0}
    ((isOpen_discrete _).mem_nhds (Set.mem_singleton
      (0 : ((schemeToLTRSObj Z).presheaf.obj (op U)).α)))
  exact ⟨n, le_antisymm (fun _ hmem => Ideal.mem_bot.mpr (hn hmem)) bot_le⟩

/-- The two geometric hypotheses of `isIdealOfDefinitionOn_of_cover` are satisfied outright, and
the criterion then has content: on a space with finitely many points every open is quasi-compact
and refines itself, so a covering by two opens already gives the condition over every open —
including the total space, which neither member of the covering contains. -/
example (X : LTRS.{u}) [Finite ↥X] (I : IdealSheaf X) (V₁ V₂ : Opens X) (hV : V₁ ⊔ V₂ = ⊤)
    (hI : ∀ U : Opens X, U ≤ V₁ ∨ U ≤ V₂ →
      TopologicalRing.IsIdealOfDefinition (I.ideal U)) :
    I.IsIdealOfDefinitionOn fun _ => True :=
  I.isIdealOfDefinitionOn_of_cover _ {V₁, V₂} (by rw [sSup_pair]; exact hV)
    (fun U _ => (Set.toFinite (U : Set X)).isCompact)
    (fun _ _ W _ _ hx => ⟨W, le_rfl, hx, trivial⟩)
    fun V hV' U hU _ => hI U (by
      rcases (Set.mem_insert_iff.mp hV') with rfl | hV'
      · exact Or.inl hU
      · exact Or.inr (hU.trans_eq (Set.mem_singleton_iff.mp hV')))

end IdealSheaf

/-- **Stacks 0AIW**, the separation of the ideal-of-definition condition from the weak one of
Stacks 0AIV, at the level of ideal sheaves on a formal scheme à la EGA. Let `R` be a nontrivial
commutative ring with exactly one prime ideal whose nilradical is not nilpotent. Then the
pseudo-discretisation of `Spec R` is a formal scheme à la EGA carrying an ideal sheaf — the
nilradical — which is a weak ideal of definition over its affine formal open subschemes and is
*not* an ideal of definition over them. This is why the correspondence of Stacks 0AIV between
weak ideals of definition and thickenings cannot restrict to a correspondence between ideals of
definition and thickenings. -/
@[stacks 0AIW "we do NOT get the same correspondence as in Stacks 0AIV: already on a formal \
scheme à la EGA the ideal-of-definition condition is strictly stronger than the weak one, \
witnessed by the nilradical of the pseudo-discretisation of a one-prime scheme whose nilradical \
is not nilpotent"]
theorem exists_isWeakIdealOfDefinitionOn_not_isIdealOfDefinitionOn_of_nilradical
    (R : Type u) [CommRing R] [Nontrivial R] [Subsingleton (PrimeSpectrum R)]
    (hnil : ∀ n : ℕ, (nilradical R) ^ n ≠ ⊥) :
    ∃ (X : LTRS.{u}) (_ : IsFormalScheme X) (I : IdealSheaf X),
      I.IsWeakIdealOfDefinitionOn (IsAffineFormalOpen X) ∧
        ¬ I.IsIdealOfDefinitionOn (IsAffineFormalOpen X) := by
  classical
  let Z : Scheme.{u} := Spec (CommRingCat.of R)
  let _ : Subsingleton ↥Z := inferInstanceAs (Subsingleton (PrimeSpectrum R))
  refine ⟨schemeToLTRSObj Z, isFormalScheme_schemeToLTRSObj Z, IdealSheaf.nilradicalIdealSheaf Z,
    IdealSheaf.nilradicalIdealSheaf_isWeakIdealOfDefinitionOn Z _, fun hdef => ?_⟩
  -- the unique point lies in an affine formal open, which is therefore the whole space
  obtain ⟨point⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
  obtain ⟨U, hpoint, A, hlinear, hadmissible, hchart⟩ := isFormalScheme_schemeToLTRSObj Z point
  obtain ⟨n, hn⟩ :=
    IdealSheaf.exists_pow_eq_bot_of_isIdealOfDefinitionOn_nilradicalIdealSheaf Z
      (𝒜 := IsAffineFormalOpen (schemeToLTRSObj Z)) (U := U)
      ⟨A, hlinear, hadmissible, hchart⟩ hdef
  have hUtop : U = ⊤ :=
    le_antisymm le_top fun y _ => by rw [Subsingleton.elim y point]; exact hpoint
  rw [hUtop] at hn
  have hn' : (nilradical ↑(Z.presheaf.obj (op (⊤ : Opens ↥Z)))) ^ n = ⊥ := hn
  -- transport the vanishing power of the nilradical along `Γ(Spec R) = R`
  let equiv := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have hmap : Ideal.map equiv.toRingHom
      (nilradical ↑(Z.presheaf.obj (op (⊤ : Opens ↥Z)))) = nilradical R := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun element hmem =>
      mem_nilradical.mpr ((mem_nilradical.mp hmem).map equiv.toRingHom)) fun element hmem => ?_
    have hpre : equiv.symm element ∈ nilradical ↑(Z.presheaf.obj (op (⊤ : Opens ↥Z))) :=
      mem_nilradical.mpr ((mem_nilradical.mp hmem).map equiv.symm.toRingHom)
    simpa using Ideal.mem_map_of_mem equiv.toRingHom hpre
  exact hnil n (by rw [← hmap, ← Ideal.map_pow, hn', Ideal.map_bot])

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinition

/-!
# Locality of a fundamental system of weak ideals of definition

A family `𝒮` of ideal sheaves on a locally topologically ringed space is a fundamental system of
weak ideals of definition over a class `𝒜` of opens — the affine formal open subschemes — when
every member is a weak ideal of definition over `𝒜` and, over every open of `𝒜`, the ideals of
sections of the members form a neighbourhood basis of zero (Stacks 0AIV). This file proves that
both halves of that condition may be checked on the opens of `𝒜` refining the members of a
covering, for a nonempty family directed by inclusion: the neighbourhood-basis half is
transported along the covering, not assumed.

## Main results

* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.exists_forall_restrict_mem_subset`:
  a neighbourhood of zero in the sections over a finite union of opens contains the set of sections
  whose restrictions lie in given neighbourhoods of zero over the members.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.hasBasis_ideal_iSup` and
  `AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.hasBasis_ideal_of_isCompact`: for
  a nonempty directed family of ideal sheaves with open ideals of sections, the
  neighbourhood-basis condition passes to finite unions, and on a quasi-compact open it is local.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_directed`: **Stacks 0AIV**, the
  fundamental-system condition may be checked on the opens of the class refining the members of
  a covering.

## Implementation notes

The source says that the condition may be checked on the members of an affine open covering.
Two corrections are needed, and both are hypotheses of the statement rather than conclusions it
skips.

* The conditions are checked on the opens of `𝒜` *contained in* a member of the covering, as in
  the single-ideal statement `IdealSheaf.isWeakIdealOfDefinitionOn_of_cover`: an ideal sheaf on an
  affine scheme can have the zero ideal of global sections and be the unit ideal on an affine open
  avoiding a closed point, so the covering members alone do not control the smaller opens.
* The family is nonempty and downward directed by inclusion. Without directedness the
  neighbourhood-basis half does not pass to a union: on a disjoint union `U₁ ⊔ U₂` of two affine
  schemes `Spec A` with a nonzero nilpotent ideal `N ⊆ A`, the two ideal sheaves `0 ⊔ N` and
  `N ⊔ 0` form a fundamental system on every affine open of `U₁` and of `U₂` (each family
  contains the zero ideal there), but neither has zero ideal of sections over the affine scheme
  `U₁ ⊔ U₂`, on which `{0}` is open. Directedness is how the source's indexing set `Λ` is used
  everywhere else in Section 87.13, and it is what Stacks 0AIW assumes of its systems.

The neighbourhoods of zero over a union are read off from the sheaf condition: the structure sheaf
takes values in topological rings, so the sections over a union carry the topology induced from
the sections over the members and their pairwise intersections (`TopCat.induced_of_isLimit`).

The helpers `IdealSheaf.exists_forall_restrict_mem_subset`, `IdealSheaf.hasBasis_ideal_iSup` and
`IdealSheaf.hasBasis_ideal_of_isCompact` say nothing about weak ideals of definition: they apply
verbatim to the fundamental systems of ideals of definition of Stacks 0AIW.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

universe u

namespace IdealSheaf

variable {X : LTRS.{u}}

/-- A neighbourhood of zero in the sections over a finite union of opens contains the set of
sections whose restrictions to the members lie in suitable neighbourhoods of zero there: the
sections over the union carry the topology induced by the restrictions to the members and to
their pairwise intersections, and a restriction to a pairwise intersection factors through a
restriction to a member. -/
theorem exists_forall_restrict_mem_subset {ι : Type u} [Finite ι] (U : ι → Opens X)
    {V : Set (X.presheaf.obj (op (iSup U))).α} (hV : V ∈ nhds 0) :
    ∃ W : (i : ι) → Set (X.presheaf.obj (op (U i))).α, (∀ i, W i ∈ nhds 0) ∧
      ∀ x, (∀ i, (X.presheaf.map (homOfLE (le_iSup U i)).op).1 x ∈ W i) → x ∈ V := by
  obtain ⟨hc⟩ := X.IsSheaf.isSheafPairwiseIntersections U
  have hnhds : ∀ {J : Type u} [Category.{u} J] {F : J ⥤ TopCommRingCat.{u}} {c : Cone F},
      IsLimit c → nhds (0 : c.pt.α) =
        ⨅ j, Filter.comap ((c.π.app j).1 : c.pt.α → (F.obj j).α) (nhds 0) := by
    intro J _ F c hc
    have ht : (inferInstance : TopologicalSpace c.pt.α) =
        ⨅ j, TopologicalSpace.induced ((c.π.app j).1 : c.pt.α → (F.obj j).α) inferInstance :=
      TopCat.induced_of_isLimit ((forget₂ TopCommRingCat TopCat).mapCone c)
        (isLimitOfPreserves (forget₂ TopCommRingCat TopCat) hc)
    rw [congrArg (fun t : TopologicalSpace c.pt.α => @nhds _ t (0 : c.pt.α)) ht, nhds_iInf]
    exact iInf_congr fun j => by rw [nhds_induced, map_zero]
  have hle : (⨅ i, Filter.comap ((X.presheaf.map (homOfLE (le_iSup U i)).op).1 :
        (X.presheaf.obj (op (iSup U))).α → (X.presheaf.obj (op (U i))).α) (nhds 0)) ≤
      nhds (0 : (X.presheaf.obj (op (iSup U))).α) := by
    refine le_trans ?_ (hnhds hc).ge
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
          change (X.presheaf.map _).1 x = ((X.presheaf.map _ ≫ X.presheaf.map _).1 x)
          rw [← X.presheaf.map_comp]
          rfl
        change (⨅ i, Filter.comap _ (nhds 0)) ≤
          Filter.comap (fun x => (X.presheaf.map (homOfLE ((inf_le_left :
            U i ⊓ U i' ≤ U i).trans (le_iSup U i))).op).1 x) (nhds 0)
        rw [hfun, ← Filter.comap_comap]
        refine (iInf_le _ i).trans (Filter.comap_mono (Filter.tendsto_iff_comap.mp ?_))
        exact (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U i' ≤ U i)).op).2.tendsto'
          0 0 (map_zero _)
  obtain ⟨t, ht, rfl⟩ := (Filter.mem_iInf_of_finite V).mp (hle hV)
  choose W hW hWt using fun i => Filter.mem_comap.mp (ht i)
  exact ⟨W, hW, fun x hx => Set.mem_iInter.mpr fun i => hWt i (hx i)⟩

/-- A nonempty family of ideal sheaves, downward directed by inclusion, has a lower bound inside
the family for every finite subfamily. -/
theorem exists_mem_forall_ideal_le {𝒮 : Set (IdealSheaf X)} (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    {ι : Type*} [Finite ι] (f : ι → IdealSheaf X) (hf : ∀ i, f i ∈ 𝒮) :
    ∃ K ∈ 𝒮, ∀ i, ∀ W : Opens X, K.ideal W ≤ (f i).ideal W := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∃ K ∈ 𝒮, ∀ i ∈ s, ∀ W : Opens X, K.ideal W ≤ (f i).ideal W by
    obtain ⟨K, hK, hle⟩ := h Finset.univ
    exact ⟨K, hK, fun i => hle i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨K, hK⟩ := hne
    exact ⟨K, hK, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨K, hK, hKle⟩ := ih
    obtain ⟨L, hL, hLle⟩ := hdir K hK (f i) (hf i)
    refine ⟨L, hL, fun j hj W => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hLle W).2
    · exact (hLle W).1.trans (hKle j hj W)

/-- For a nonempty family `𝒮` of ideal sheaves, downward directed by inclusion, whose ideals of
sections over a finite union of opens are open, the ideals of sections over the union form a
neighbourhood basis of zero as soon as they do over each member. -/
theorem hasBasis_ideal_iSup {𝒮 : Set (IdealSheaf X)} (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    {ι : Type u} [Finite ι] (U : ι → Opens X)
    (hopen : ∀ I ∈ 𝒮, IsOpen (I.ideal (iSup U) : Set (X.presheaf.obj (op (iSup U))).α))
    (hU : ∀ i, (nhds (0 : (X.presheaf.obj (op (U i))).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal (U i) : Set (X.presheaf.obj (op (U i))).α)) :
    (nhds (0 : (X.presheaf.obj (op (iSup U))).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal (iSup U) : Set (X.presheaf.obj (op (iSup U))).α) := by
  refine ⟨fun V => ⟨fun hV => ?_, fun ⟨I, hI, hIV⟩ =>
    Filter.mem_of_superset ((hopen I hI).mem_nhds (Ideal.zero_mem _)) hIV⟩⟩
  obtain ⟨W, hW, hWV⟩ := exists_forall_restrict_mem_subset U hV
  choose f hf hfW using fun i => (hU i).mem_iff.mp (hW i)
  obtain ⟨K, hK, hKle⟩ := exists_mem_forall_ideal_le hne hdir f hf
  exact ⟨K, hK, fun x hx => hWV x fun i =>
    hfW i (hKle i (U i) (K.map_mem (le_iSup U i) hx))⟩

/-- On a quasi-compact open the neighbourhood-basis condition is local, for a nonempty family of
ideal sheaves, downward directed by inclusion, whose ideals of sections over that open are open:
if every point has a neighbourhood inside the open over which the ideals of sections form a
neighbourhood basis of zero, then they form one over the open itself. -/
theorem hasBasis_ideal_of_isCompact {𝒮 : Set (IdealSheaf X)} (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (V : Opens X) (hV : IsCompact (V : Set X))
    (hopen : ∀ I ∈ 𝒮, IsOpen (I.ideal V : Set (X.presheaf.obj (op V)).α))
    (hlocal : ∀ x ∈ V, ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
      (nhds (0 : (X.presheaf.obj (op W)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal W : Set (X.presheaf.obj (op W)).α)) :
    (nhds (0 : (X.presheaf.obj (op V)).α)).HasBasis (· ∈ 𝒮)
      fun I : IdealSheaf X => (I.ideal V : Set (X.presheaf.obj (op V)).α) := by
  classical
  choose W hWV hxW hW using fun x : V => hlocal x x.property
  obtain ⟨s, hs⟩ := hV.elim_finite_subcover (fun x : V => (W x : Set X))
    (fun x => (W x).isOpen) fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩
  have hsup : ⨆ x : s, W x = V := by
    refine le_antisymm (iSup_le fun x => hWV x) fun x hx => ?_
    obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact (le_iSup (fun y : s => W y) ⟨y, hys⟩) hxy
  have key := hasBasis_ideal_iSup hne hdir (fun x : s => W x) (by rw [hsup]; exact hopen)
    fun x => hW x
  rw [hsup] at key
  exact key

end IdealSheaf

/-- The locality of the fundamental-system condition, for an abstract class of opens (the form of
Stacks 0AIV for McQuillan formal schemes is
`isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_isMcQuillanFormalScheme`).
Let `𝒰` be a covering of `X` and let `𝒜` be a class of quasi-compact opens — the affine formal
open subschemes — whose members contained in an open cover that open. Let `𝒮` be a nonempty
family of ideal sheaves, downward directed by inclusion, such that over every open of `𝒜`
contained in a member of `𝒰`
each member of `𝒮` has a weak ideal of definition for its ideal of sections and these ideals of
sections form a neighbourhood basis of zero. Then `𝒮` is a fundamental system of weak ideals of
definition over `𝒜`.

Both halves of the condition are transported along the covering: the weak ideal-of-definition
half by `IdealSheaf.isWeakIdealOfDefinitionOn_of_cover`, the neighbourhood-basis half by
`IdealSheaf.hasBasis_ideal_of_isCompact`. -/
theorem isFundamentalSystemOfWeakIdealsOfDefinitionOn_of_cover_of_directed {X : LTRS.{u}}
    (𝒮 : Set (IdealSheaf X)) (𝒜 : Opens X → Prop) (hne : 𝒮.Nonempty)
    (hdir : ∀ I ∈ 𝒮, ∀ J ∈ 𝒮, ∃ K ∈ 𝒮, ∀ W : Opens X,
      K.ideal W ≤ I.ideal W ∧ K.ideal W ≤ J.ideal W)
    (𝒰 : Set (Opens X)) (hcover : sSup 𝒰 = ⊤)
    (hcompact : ∀ U : Opens X, 𝒜 U → IsCompact (U : Set X))
    (hrefine : ∀ V ∈ 𝒰, ∀ W : Opens X, W ≤ V → ∀ x ∈ W,
      ∃ U : Opens X, U ≤ W ∧ x ∈ U ∧ 𝒜 U)
    (h𝒮 : ∀ I ∈ 𝒮, ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      TopologicalRing.IsWeakIdealOfDefinition (I.ideal U))
    (hbasis : ∀ V ∈ 𝒰, ∀ U : Opens X, U ≤ V → 𝒜 U →
      (nhds (0 : (X.presheaf.obj (op U)).α)).HasBasis (· ∈ 𝒮)
        fun I : IdealSheaf X => (I.ideal U : Set (X.presheaf.obj (op U)).α)) :
    IsFundamentalSystemOfWeakIdealsOfDefinitionOn 𝒮 𝒜 := by
  have hweak : ∀ I ∈ 𝒮, I.IsWeakIdealOfDefinitionOn 𝒜 := fun I hI =>
    I.isWeakIdealOfDefinitionOn_of_cover 𝒜 𝒰 hcover hcompact hrefine (h𝒮 I hI)
  refine ⟨hweak, fun T hT => ?_⟩
  refine IdealSheaf.hasBasis_ideal_of_isCompact hne hdir T (hcompact T hT)
    (fun I hI => (hweak I hI T hT).1) fun x hx => ?_
  obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp (show x ∈ sSup 𝒰 by rw [hcover]; trivial)
  obtain ⟨U, hUW, hxU, hU⟩ := hrefine V hV (V ⊓ T) inf_le_left x ⟨hxV, hx⟩
  exact ⟨U, hUW.trans inf_le_right, hxU, hbasis V hV U (hUW.trans inf_le_left) hU⟩

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

end

module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.ComponentCount
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.Topology.Noetherian.LocallyConnected
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected components in fibres near the generic point

Let `f : X ⟶ Y` be a finite type morphism and let `η` be a generic point of `Y`. If the generic
fibre has `n` connected components, then every fibre over some nonempty open subset of `Y` has
at least `n` connected components. This is Stacks Tag 055D.

## Main results

* `AlgebraicGeometry.exists_open_natCard_connectedComponents_fiber_ge` is Stacks Tag 055D.

## Implementation notes

Being of finite type is expressed by `LocallyOfFiniteType` together with `QuasiCompact`, and a
chosen dense generic point by `IsGenericPoint η Set.univ`, which already forces the target to be
irreducible. The fibres are of finite type over fields, hence Noetherian, so they have finitely
many connected components and `Nat.card` is their actual cardinality.

The connected components of the generic fibre form a finite partition into closed subsets. For
each of them the proof takes the reduced closed subscheme of `X` cut out by its closure,
`AlgebraicGeometry.componentClosureSubscheme`. Over a suitable open subset of the base these
subschemes cover every fibre (Tag 054Y), each of them meets every fibre
(`AlgebraicGeometry.componentClosure_exists_open_image`, which rests on generic flatness), and
their pairwise intersections miss every fibre, because a quasi-compact morphism whose image
avoids a generic point avoids a whole neighbourhood of it (Tag 02NE). A finite partition of a
space into nonempty disjoint closed subsets consists of clopen sets, so it has at most as many
parts as the space has connected components.

## References

* [Stacks Project, Tag 055D](https://stacks.math.columbia.edu/tag/055D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- A space partitioned into finitely many nonempty pairwise disjoint closed subsets has at
least that many connected components: each part is clopen, hence contains the connected
component of any of its points. -/
private lemma natCard_le_natCard_connectedComponents_of_isClosed_partition
    {α : Type*} {ι : Type*} [TopologicalSpace α] [Finite (ConnectedComponents α)] [Finite ι]
    (S : ι → Set α) (hclosed : ∀ i, IsClosed (S i)) (hcover : ∀ x, ∃ i, x ∈ S i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hnonempty : ∀ i, (S i).Nonempty) :
    Nat.card ι ≤ Nat.card (ConnectedComponents α) := by
  classical
  choose x hx using hnonempty
  have hclopen : ∀ i, IsClopen (S i) := by
    intro i
    refine ⟨hclosed i, ?_⟩
    rw [← isClosed_compl_iff]
    have hcompl : (S i)ᶜ = ⋃ j ∈ ({j : ι | j ≠ i} : Set ι), S j := by
      ext z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨j, hj⟩ := hcover z
        have hji : j ≠ i := fun h => hz (h ▸ hj)
        exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hj⟩⟩
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hji, hzj⟩ := Set.mem_iUnion.mp hj
        exact fun hzi => (Set.disjoint_left.mp (hdisjoint i j (Ne.symm hji))) hzi hzj
    rw [hcompl]
    exact Set.toFinite {j : ι | j ≠ i} |>.isClosed_biUnion fun j _ => hclosed j
  refine Nat.card_le_card_of_injective (fun i => ConnectedComponents.mk (x i)) ?_
  intro i j hij
  by_contra hne
  have hsub : connectedComponent (x j) ⊆ S j :=
    isPreconnected_connectedComponent.subset_isClopen (hclopen j)
      ⟨x j, mem_connectedComponent, hx j⟩
  exact (Set.disjoint_left.mp (hdisjoint i j hne)) (hx i)
    (hsub (ConnectedComponents.coe_eq_coe'.mp hij))

/-- Every fibre of a finite type morphism has finitely many connected components. -/
private lemma finite_connectedComponents_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) : Finite (ConnectedComponents (f.fiber y)) :=
  have := fiber_isNoetherian f y
  TopologicalSpace.NoetherianSpace.finite_connectedComponents (f.fiber y)

/-- Two closed subsets of the source whose traces on the fibre over a dense generic point are
disjoint have disjoint traces on every fibre over some open neighbourhood of that point: the
closed subscheme cut out by their intersection is quasi-compact over the base and misses the
generic point, hence misses a neighbourhood of it by Stacks Tag 02NE. -/
private theorem exists_open_fibers_disjoint_of_generic_disjoint {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (η : Y) (hη : IsGenericPoint η Set.univ) (A B : Set X) (hA : IsClosed A)
    (hB : IsClosed B) (hηdisj : Disjoint (f.fiberι η ⁻¹' A) (f.fiberι η ⁻¹' B)) :
    ∃ V : Y.Opens, η ∈ V ∧
      ∀ y ∈ V, Disjoint (f.fiberι y ⁻¹' A) (f.fiberι y ⁻¹' B) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨A ∩ B, hA.inter hB⟩
  let g : I.subscheme ⟶ Y := I.subschemeι ≫ f
  have hsupport : (I.support : Set X) = A ∩ B :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨A ∩ B, hA.inter hB⟩
  have hmem : ∀ x : X, x ∈ Set.range I.subschemeι ↔ x ∈ A ∩ B := fun x => by
    rw [I.range_subschemeι, hsupport]
  have : QuasiCompact g := quasiCompact_comp I.subschemeι f
  have : PreirreducibleSpace Y := ⟨by simpa using hη.isIrreducible.isPreirreducible⟩
  have : IrreducibleSpace Y := ⟨⟨η⟩⟩
  have hηgp : η ∈ genericPoints Y := by
    show closure ({η} : Set Y) ∈ irreducibleComponents Y
    rw [show closure ({η} : Set Y) = Set.univ from hη.def, irreducibleComponents_eq_singleton]
    simp
  have hηg : η ∉ Set.range g := by
    rintro ⟨t, ht⟩
    have hxt : f (I.subschemeι t) = η := by simpa [g] using ht
    let z : f.fiber η := (f.fiberHomeo η).symm ⟨I.subschemeι t, hxt⟩
    have hz : f.fiberι η z = I.subschemeι t := f.fiberι_fiberHomeo_symm η ⟨I.subschemeι t, hxt⟩
    have hzAB : f.fiberι η z ∈ A ∩ B := hz ▸ (hmem _).1 ⟨t, rfl⟩
    exact (Set.disjoint_left.mp hηdisj) hzAB.1 hzAB.2
  obtain ⟨V, hηV, hpre⟩ := exists_open_nhds_disjoint_range_of_quasiCompact g η hηgp hηg
  refine ⟨V, hηV, fun y hy => Set.disjoint_left.mpr fun z hzA hzB => ?_⟩
  obtain ⟨t, ht⟩ := (hmem (f.fiberι y z)).2 ⟨hzA, hzB⟩
  have htg : g t = y := by simpa [g] using (congrArg f ht).trans (f.apply_fiberι y z)
  have htV : t ∈ g ⁻¹ᵁ V := by
    show g t ∈ V
    rwa [htg]
  rw [hpre] at htV
  exact (Opens.mem_bot.mp htV).elim

/-- The closed subscheme cut out by the closure of a nonempty closed subset of the generic fibre
meets every fibre over some open neighbourhood of the generic point. -/
private lemma exists_open_fiber_preimage_componentClosure_nonempty {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η Set.univ) (C : Set (f.fiber η)) (hC : IsClosed C)
    (hne : C.Nonempty) :
    ∃ V : Set Y, IsOpen V ∧ η ∈ V ∧ ∀ y ∈ V,
      (f.fiberι y ⁻¹' ((componentClosureSubscheme f η C).support : Set X)).Nonempty := by
  obtain ⟨c, hc⟩ := hne
  rw [← componentClosureSubscheme_preimage_support f η C hC] at hc
  set I := componentClosureSubscheme f η C
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
      (⟨closure (f.fiberι η '' C), isClosed_closure⟩ : Closeds X)
  obtain ⟨x, hx⟩ : f.fiberι η c ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hc
  obtain ⟨V, hVopen, hηV, hV⟩ := componentClosure_exists_open_image f I η hη
    ⟨x, by rw [Scheme.Hom.comp_apply, hx, f.apply_fiberι]⟩
  refine ⟨V, hVopen, hηV, fun y hy => ?_⟩
  obtain ⟨x', hx'⟩ := hV y hy
  refine ⟨(f.fiberHomeo y).symm ⟨I.subschemeι x', by simpa using hx'⟩, ?_⟩
  rw [Set.mem_preimage, f.fiberι_fiberHomeo_symm, ← I.range_subschemeι]
  exact ⟨x', rfl⟩

/-- Given a finite partition of the fibre over a dense generic point into nonempty closed
subsets, every fibre over some nonempty open subset of the base has at least that many
connected components. -/
@[ega "IV 9.7.1" "more general"]
private theorem exists_open_natCard_fiber_components_ge_of_partition {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (η : Y)
    (hη : IsGenericPoint η Set.univ) {ι : Type v} [Finite ι] (C : ι → Set (f.fiber η))
    (hCclosed : ∀ i, IsClosed (C i)) (hCcover : ∀ x : f.fiber η, ∃ i, x ∈ C i)
    (hCdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j)) (hCnonempty : ∀ i, (C i).Nonempty) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, Nat.card ι ≤ Nat.card (ConnectedComponents (f.fiber y)) := by
  classical
  let I : ι → X.IdealSheafData := fun i => componentClosureSubscheme f η (C i)
  let Z : ι → Set X := fun i => ((I i).support : Set X)
  have hZeq : ∀ i, Z i = closure (f.fiberι η '' C i) := fun i => by
    show ((componentClosureSubscheme f η (C i)).support : Set X) = _
    rw [componentClosureSubscheme_support]
  have hZclosed : ∀ i, IsClosed (Z i) := fun i => (I i).support.2
  have hZgeneric : ∀ i, f.fiberι η ⁻¹' Z i = C i := fun i =>
    componentClosureSubscheme_preimage_support f η (C i) (hCclosed i)
  obtain ⟨Vcover, hVcoverOpen, hVcoverNonempty, hVcover⟩ :=
    exists_open_fiber_covered_by_closures f η hη C hCcover
  have hηVcover : η ∈ Vcover :=
    (hη.mem_open_set_iff hVcoverOpen).2 (by simpa using hVcoverNonempty)
  have hmeet : ∀ i, ∃ V : Set Y, IsOpen V ∧ η ∈ V ∧
      ∀ y ∈ V, (f.fiberι y ⁻¹' Z i).Nonempty := fun i =>
    exists_open_fiber_preimage_componentClosure_nonempty f η hη (C i) (hCclosed i) (hCnonempty i)
  choose Vi hViOpen hηVi hViNonempty using hmeet
  have hpair : ∀ p : ι × ι, ∃ W : Set Y, IsOpen W ∧ η ∈ W ∧
      (p.1 ≠ p.2 → ∀ y ∈ W, Disjoint (f.fiberι y ⁻¹' Z p.1) (f.fiberι y ⁻¹' Z p.2)) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨Set.univ, isOpen_univ, Set.mem_univ η, fun h => (h hp).elim⟩
    obtain ⟨W, hηW, hW⟩ := exists_open_fibers_disjoint_of_generic_disjoint f η hη
      (Z p.1) (Z p.2) (hZclosed p.1) (hZclosed p.2)
      (by simpa only [hZgeneric] using hCdisjoint p.1 p.2 hp)
    exact ⟨(W : Set Y), W.2, hηW, fun _ y hy => hW y hy⟩
  choose W hWOpen hηW hWDisjoint using hpair
  refine ⟨(Vcover ∩ ⋂ i, Vi i) ∩ ⋂ p : ι × ι, W p, ?_, ⟨η, ?_⟩, ?_⟩
  · exact (hVcoverOpen.inter (isOpen_iInter_of_finite hViOpen)).inter
      (isOpen_iInter_of_finite hWOpen)
  · exact ⟨⟨hηVcover, Set.mem_iInter.mpr hηVi⟩, Set.mem_iInter.mpr hηW⟩
  intro y hy
  have := finite_connectedComponents_fiber f y
  refine natCard_le_natCard_connectedComponents_of_isClosed_partition
    (fun i => f.fiberι y ⁻¹' Z i) (fun i => (hZclosed i).preimage (f.fiberι y).continuous)
    (fun x => ?_) (fun i j hij => hWDisjoint (i, j) hij y (Set.mem_iInter.mp hy.2 (i, j)))
    (fun i => hViNonempty i y (Set.mem_iInter.mp hy.1.2 i))
  obtain ⟨i, hi⟩ := hVcover y hy.1.1 x
  exact ⟨i, by rwa [Set.mem_preimage, hZeq i]⟩

/-- **Stacks Project, Tag 055D.** For a finite type morphism to a scheme with a chosen dense
generic point, the number of connected components of the fibres is at least the number for the
generic fibre on a nonempty open subset of the base. -/
@[stacks 055D, ega "IV 9.7.1" "connected components"]
theorem exists_open_natCard_connectedComponents_fiber_ge {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (η : Y) (hη : IsGenericPoint η Set.univ) (n : ℕ)
    (hcomp : Nat.card (ConnectedComponents (f.fiber η)) = n) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, n ≤ Nat.card (ConnectedComponents (f.fiber y)) := by
  classical
  have := finite_connectedComponents_fiber f η
  choose rep hrep using ConnectedComponents.surjective_coe (α := f.fiber η)
  let C : ConnectedComponents (f.fiber η) → Set (f.fiber η) := fun c => connectedComponent (rep c)
  have hCcover : ∀ x : f.fiber η, ∃ c, x ∈ C c := by
    intro x
    refine ⟨ConnectedComponents.mk x, ?_⟩
    show x ∈ connectedComponent (rep (ConnectedComponents.mk x))
    rw [ConnectedComponents.coe_eq_coe.mp (hrep (ConnectedComponents.mk x))]
    exact mem_connectedComponent
  have hCdisjoint : ∀ c d, c ≠ d → Disjoint (C c) (C d) := by
    intro c d hcd
    refine Set.disjoint_left.mpr fun x hxc hxd => hcd ?_
    rw [← hrep c, ← hrep d]
    exact ConnectedComponents.coe_eq_coe.mpr
      ((connectedComponent_eq hxc).trans (connectedComponent_eq hxd).symm)
  obtain ⟨V, hVopen, hVne, hVbound⟩ := exists_open_natCard_fiber_components_ge_of_partition
    f η hη C (fun _ => isClosed_connectedComponent) hCcover hCdisjoint
    (fun c => ⟨rep c, mem_connectedComponent⟩)
  exact ⟨V, hVopen, hVne, fun y hy => hcomp.ge.trans (hVbound y hy)⟩

end AlgebraicGeometry

end

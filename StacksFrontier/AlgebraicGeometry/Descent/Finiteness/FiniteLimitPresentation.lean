module

public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionIntoFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.ClosedImmersionLimit

/-!
# A morphism locally of finite type as an inverse limit of morphisms of finite presentation

Let `S` be a quasi-separated scheme and let `f : X ⟶ S` be locally of finite type with `X`
quasi-compact and quasi-separated.  Then `X` is the directed inverse limit of a system of
schemes of finite presentation over `S` whose transition morphisms, and whose limit
projections, are closed immersions.

The argument composes the two factorizations already available.  By [Stacks, Tag 01ZG] the
morphism `f` factors as a closed immersion `X ⟶ Y` followed by a morphism `Y ⟶ S` of finite
presentation.  The image of the quasi-compact `X` meets only finitely many members of an
affine open cover of `Y`, so `X` is a closed subscheme of a quasi-compact open `V ⊆ Y`, whose
inclusion is of finite presentation by [Stacks, Tag 01TU]; replacing `Y` by `V` therefore
costs nothing and makes the ambient scheme quasi-compact.  [Stacks, Tag 09ZP] then presents
that closed immersion `X ⟶ V` as the inverse limit of the closed subschemes of `V` cut out by
the finitely presented ideal sheaves below its kernel, and composing each of those with
`V ⟶ S` gives the system over `S`.

Alongside this, a quasi-compact open of the source of a closed immersion is recorded as the
preimage of a quasi-compact open of the target: the source is a closed subspace, so its opens
are cut out by opens of the target, and such an open may be shrunk to a finite union of affine
opens still containing the compact image.

## Main results

* `AlgebraicGeometry.exists_isLimit_finitePresentation_closedImmersion`: the inverse system of
  schemes of finite presentation over `S` with closed-immersion transition maps and
  closed-immersion limit projections.
* `AlgebraicGeometry.exists_isCompact_preimage_eq_of_isClosedImmersion`: a quasi-compact open
  of the source of a closed immersion descends to a quasi-compact open of the target.

## Implementation notes

The index preorder is produced in `Type u`, the universe of the schemes, rather than in
`Type (u + 1)`: that is the universe [Stacks, Tag 09ZP] already supplies it in, and an
existential over the smaller universe is the sharper statement.

Compactness and quasi-separatedness of each stage are recorded alongside finite presentation,
since both follow from the corresponding property of `V` through the quasi-compact and
quasi-separated structure morphism, and a consumer of the system has no other route to them.

## References

* [Stacks Project, Tag 09ZQ](https://stacks.math.columbia.edu/tag/09ZQ)
* [Stacks Project, Tag 09ZP](https://stacks.math.columbia.edu/tag/09ZP)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 01TU](https://stacks.math.columbia.edu/tag/01TU)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

/-- A quasi-compact open of the source of a closed immersion is the preimage of a quasi-compact
open of the target.  The source is a closed subspace, so the open is cut out by some open of the
target, and that open may be replaced by the union of finitely many affine opens covering the
compact image. -/
theorem exists_isCompact_preimage_eq_of_isClosedImmersion {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsClosedImmersion g] (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ V : Y.Opens, IsCompact (V : Set Y) ∧ g ⁻¹ᵁ V = U := by
  have hEmbed : Topology.IsClosedEmbedding g.base := IsClosedImmersion.isClosedEmbedding g
  obtain ⟨W, hWopen, hW⟩ := hEmbed.isEmbedding.isOpen_iff.mp U.2
  have hKW : g.base '' (U : Set X) ⊆ (⟨W, hWopen⟩ : Y.Opens) := by
    rintro y ⟨x, hxU, rfl⟩
    change x ∈ g.base ⁻¹' W
    rw [hW]
    exact hxU
  obtain ⟨n, A, hAW, hKA⟩ := exists_finite_affineOpens_cover_of_isCompact
    (g.base '' (U : Set X)) (hU.image g.continuous) ⟨W, hWopen⟩ hKW
  refine ⟨⨆ j : Fin n, (A j).1, ?_, ?_⟩
  · rw [isCompact_iff_finite_and_eq_biUnion_affineOpens]
    exact ⟨Set.range A, Set.finite_range A, by simp⟩
  · ext x
    change g.base x ∈ ((⨆ j : Fin n, (A j).1 : Y.Opens) : Set Y) ↔ x ∈ (U : Set X)
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hxj⟩
      have hx : x ∈ g.base ⁻¹' W := hAW j hxj
      rwa [hW] at hx
    · intro hxU
      exact Set.mem_iUnion.mp (hKA ⟨x, hxU, rfl⟩)

/-- If `a ≫ b = c` with `b` and `c` closed immersions, then `a` is a closed immersion. -/
private theorem isClosedImmersion_of_comp_eq {X Y Z : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z}
    {c : X ⟶ Z} (hb : IsClosedImmersion b) (hc : IsClosedImmersion c) (h : a ≫ b = c) :
    IsClosedImmersion a := by
  subst h
  exact IsClosedImmersion.of_comp a b

/-- A quasi-compact and quasi-separated scheme locally of finite type over a quasi-separated
base is a directed inverse limit of quasi-compact and quasi-separated schemes of finite
presentation over that base, with closed immersions as the transition maps and as the limit
projections. -/
@[stacks 09ZQ]
theorem exists_isLimit_finitePresentation_closedImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Functor Iᵒᵖ Scheme.{u}) (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (_ : IsLimit (Cone.mk X p)),
      p ≫ t = (Functor.const Iᵒᵖ).map f ∧
        (∀ i, FinitePresentation (t.app i) ∧
          CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)) ∧
        (∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsClosedImmersion (D.map g)) ∧
        ∀ i, IsClosedImmersion (p.app i) := by
  obtain ⟨Y, q, c, hq, hc, hcomp⟩ := exists_finitePresentation_closedImmersion f
  have : QuasiSeparated q := hq.quasiSeparated
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated q
  obtain ⟨s, hscover⟩ := (isCompact_range c.continuous).elim_finite_subcover
    (fun U : Y.affineOpens => (U : Set Y)) (fun U => U.1.2) (by
      rintro y ⟨x, rfl⟩
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (c.base x)) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  let V : Y.Opens := ⨆ U ∈ s, (U : Y.Opens)
  have hVcompact : IsCompact (V : Set Y) :=
    isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, s.finite_toSet, rfl⟩
  have hrange : Set.range c.base ⊆ (V : Set Y) := by
    intro y hy
    simpa [V, TopologicalSpace.Opens.coe_iSup] using hscover hy
  let cV : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι c (by simpa using hrange)
  have hcV : cV ≫ V.ι = c := IsOpenImmersion.lift_fac _ _ _
  have : IsClosedImmersion (cV ≫ V.ι) := by simpa [hcV] using hc
  have : IsClosedImmersion cV := IsClosedImmersion.of_comp cV V.ι
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hVcompact
  have : QuasiSeparatedSpace V.toScheme := .of_isOpenEmbedding V.ι.isOpenEmbedding
  have : FinitePresentation V.ι :=
    (finitePresentation_iff_quasiCompact_of_isOpenImmersion V.ι).2 inferInstance
  have : LocallyOfFinitePresentation q := hq.locallyOfFinitePresentation
  have : QuasiCompact q := hq.quasiCompact
  have : LocallyOfFinitePresentation (V.ι ≫ q) := locallyOfFinitePresentation_comp _ _
  have : QuasiCompact (V.ι ≫ q) := quasiCompact_comp _ _
  have : QuasiSeparated (V.ι ≫ q) := quasiSeparated_comp _ _
  obtain ⟨I, hpre, hnon, hdir, D, tV, p, hlim, hcompat, hstage⟩ :=
    exists_isLimit_closedImmersion_finitePresentation cV
  let t : D ⟶ (Functor.const Iᵒᵖ).obj S := tV ≫ (Functor.const Iᵒᵖ).map (V.ι ≫ q)
  have hproj (j : Iᵒᵖ) : p.app j ≫ tV.app j = cV := by
    simpa using congrArg (fun η => η.app j) hcompat
  refine ⟨I, inferInstance, inferInstance, inferInstance, D, t, p, hlim, ?_, ?_, ?_, ?_⟩
  · ext j
    change p.app j ≫ (tV.app j ≫ (V.ι ≫ q)) = f
    simp only [← Category.assoc, hproj j, hcV, hcomp]
  · intro j
    have : LocallyOfFinitePresentation (tV.app j) := (hstage j).2.1
    have : QuasiCompact (tV.app j) := (hstage j).2.2.1
    have : QuasiSeparated (tV.app j) := (hstage j).2.2.2
    refine ⟨?_, ?_, ?_⟩
    · change FinitePresentation (tV.app j ≫ (V.ι ≫ q))
      exact ⟨locallyOfFinitePresentation_comp _ _, quasiCompact_comp _ _, quasiSeparated_comp _ _⟩
    · exact @QuasiCompact.compactSpace_of_compactSpace _ _ (tV.app j)
        inferInstance (by change CompactSpace V.toScheme; infer_instance)
    · exact @quasiSeparatedSpace_of_quasiSeparated _ _ (tV.app j)
        (by change QuasiSeparatedSpace V.toScheme; infer_instance) inferInstance
  · intro j k g
    exact isClosedImmersion_of_comp_eq (hstage k).1 (hstage j).1 (by simp)
  · intro j
    exact isClosedImmersion_of_comp_eq (hstage j).1 (inferInstance : IsClosedImmersion cV)
      (hproj j)

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageOffSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageFiberType
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# The essential image of the small étale direct image of sheaves of sets

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S` contained in a big
fppf site `B`. [Stacks, Tag 04E5], part (1), says that the direct image of sheaves of sets along
the morphism of small étale topoi of Stacks 03G2, part (3), is fully faithful and that its
essential image consists of the sheaves whose restriction to `X ∖ Z` is a singleton. Full
faithfulness is
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`; this file proves
the **essential-image clause**, unconditionally, at the universe `Type u` of the structure rings
— the universe at which `AlgebraicGeometry.Space.smallToposMorphismTypeU` lives and the one the
modules development consumes.

## Main results

* `AlgebraicGeometry.Space.exists_hom_chartPreimage_eq_empty`: a small étale neighbourhood of a
  geometric point of `X` whose image misses the point set of `Z` is refined by one whose chart
  misses that point set altogether.
* `AlgebraicGeometry.Space.nonempty_isTerminal_presheafFiber_of_chartPreimage_eq_empty`: a
  presheaf of sets which is a singleton on every chart missing the point set of `Z` has singleton
  fibre at every geometric point outside that point set.
* Étale Cohomology 04FX away from `Z`, for sheaves of sets: a direct image along `i` has exactly
  one section over a chart of `X` whose points miss the point set of `Z`, which is
  `AlgebraicGeometry.Space.nonempty_isTerminal_smallEtaleDirectImage_obj_of_chartPreimage_eq_empty`
* `AlgebraicGeometry.Space.smallEtalePushforward_essImage_iff_of_isClosedImmersion` is
  **Stacks 04E5, part (1), the essential image**: a sheaf of sets on `X_étale` is a direct image
  along `i` exactly when it is a singleton on every étale chart of `X` whose points avoid the
  point set of `Z`.

## How the restriction to `X ∖ Z` is written

The source phrases the criterion as "the restriction of `F` to `X ∖ Z` is isomorphic to `*`".
Here it is written as "`F` has exactly one section over every étale chart of `X` whose points
avoid the point set of `Z`", which says the same thing: an étale chart of `X` missing that point
set is an étale chart of the open complement, every étale chart of the complement is one of
these, and a sheaf of sets is terminal exactly when all of its sections are singletons. Phrasing
the criterion through the charts keeps the statement inside the small étale site of `X`, so that
neither the inverse image along the open immersion of the complement nor its sheafification
enters, and it is the form in which the modules development consumes the clause: a sheaf of
modules over `i_*𝒪_Z` has exactly one section over such a chart by
`AlgebraicGeometry.Space.subsingleton_sections_of_chartPreimage_eq_empty`.

## The proof

The forward inclusion is Étale Cohomology 04FX away from `Z`: a chart of `X` whose points avoid
the point set of `Z` has empty base change along `i`
(`AlgebraicGeometry.Space.isEmpty_smallBaseChange_of_disjoint_range`), the empty sieve covers
that base change, and a sheaf has exactly one section over an object covered by the empty sieve.

The converse is Étale Cohomology 04CA. Membership of the essential image of a fully faithful
right adjoint is invertibility of the unit `F ⟶ i_*i^{-1}F`, and invertibility is tested on the
fibres at the geometric points of `X`, which are a conservative family
(`AlgebraicGeometry.Space.isConservativeFamily_etaleSitePoint`). At a geometric point lying on
`Z` the point comes from a geometric point of `Z`
(`AlgebraicGeometry.Space.exists_geometricPoint_map_eq_of_mem_range`), where the inverse image
carries the unit to an isomorphism because the direct image is fully faithful, and the fibre of
an inverse image is the fibre at the image point, which is Stacks 04K2, part (4) at `Type u`
(`AlgebraicGeometry.Space.smallEtaleInverseImageFiberIso`). At a geometric point missing the
point set of `Z` both fibres are singletons — the source by hypothesis, the target by the
forward inclusion — and any map between singletons is invertible.

## Implementation notes

**Why `Type u` is reachable here.** The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionDirectImageOffSubspace` record that the
argument needs Stacks 04K2, part (4) at `Type u` and that the `stalkSet` formulation of it is
blocked, because the comparison `AlgebraicGeometry.Space.etaleSitePointStalkIso` between the
fibre of the point of the site and the colimit quotient `AlgebraicGeometry.Space.stalkSet` does
not typecheck at `Type u`. That comparison is not needed: `smallEtaleInverseImageFiberIso` states
04K2, part (4) for the fibre of the point of the site itself, and
`isConservativeFamily_etaleSitePoint` states conservativity for the same fibres. Both sides of
the argument therefore speak of `CategoryTheory.GrothendieckTopology.Point.sheafFiber` and the
colimit quotient never appears.

**Passing from sections to fibres.** The fibre of a presheaf at the point of the site is a
filtered colimit over the elements of the geometric fibre functor, and two of its elements can
be represented over a *common* chart
(`CategoryTheory.GrothendieckTopology.Point.toPresheafFiber_jointly_surjective₂`). Refining that
chart to one missing the point set of `Z` is
`AlgebraicGeometry.Space.exists_neighborhood_imageInOpen` applied to the open complement of
`AlgebraicGeometry.Space.chartPreimage`, which is closed by
`AlgebraicGeometry.Space.isClosed_chartPreimage`; every further refinement again misses the point
set, by `AlgebraicGeometry.Space.chartPreimage_subset_preimage`, so the hypothesis applies to the
whole cofinal system and the colimit collapses.

## References

* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04FX](https://stacks.math.columbia.edu/tag/04FX)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isContinuous_smallBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS}

/-! ### Refining a neighbourhood away from the closed subspace -/

/-- A small étale neighbourhood of a geometric point of `X` whose image misses the point set of
a closed immersion `i : Z ⟶ X` is refined by a neighbourhood whose chart misses that point set
altogether.

The preimage of the point set of `i` in the chart is closed
(`AlgebraicGeometry.Space.isClosed_chartPreimage`) and does not contain the point carried by the
geometric point, so `AlgebraicGeometry.Space.exists_neighborhood_imageInOpen` refines the
neighbourhood into its open complement; a chart mapping into that complement has empty
preimage. -/
theorem exists_hom_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) {x : GeometricPoint B S hS X.1}
    (hx : x.image ∉ Set.range (pointsMap B S hS Z.1 i.hom))
    (N : SmallEtaleNeighborhood x) :
    ∃ (M : SmallEtaleNeighborhood x) (_ : M ⟶ N), chartPreimage B S hS i M.chart = ∅ := by
  obtain ⟨M, f, hf⟩ := exists_neighborhood_imageInOpen B S hS X.1 N
    ((chartPreimage B S hS i N.chart)ᶜ)
    (isClosed_chartPreimage B S hS i hi N.chart).isOpen_compl fun hmem ↦ hx (by
      rwa [chartPreimage, Set.mem_preimage, neighborhoodPoint_image B S hS X.1 N] at hmem)
  exact ⟨M, f, Set.eq_empty_iff_forall_notMem.2 fun y hy ↦
    hf y (chartPreimage_subset_preimage B S hS i f.hom hy)⟩

/-- A presheaf of sets on the small étale site of `X` which has exactly one section over every
chart missing the point set of a closed immersion `i : Z ⟶ X` has exactly one element in its
fibre at every geometric point of `X` whose image misses that point set.

The fibre at the point of the site is the filtered colimit of the sections over the charts
carrying a lift of the geometric point. By
`AlgebraicGeometry.Space.exists_hom_chartPreimage_eq_empty` one such chart misses the point set,
and then so does every chart over it, so the hypothesis applies to a whole cofinal system and
every two elements of the colimit become equal there. -/
theorem nonempty_isTerminal_presheafFiber_of_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ Set.range (pointsMap B S hS Z.1 i.hom))
    (P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type u)
    (hP : ∀ V : SmallEtale B S hS X.1, chartPreimage B S hS i V = ∅ →
      Nonempty (IsTerminal (P.obj (op V)))) :
    Nonempty (IsTerminal
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := Type u)).obj P)) := by
  classical
  set Φ := etaleSitePoint B S hS X.1 x X.2
  obtain ⟨N₀⟩ : Nonempty Φ.fiber.Elements := IsCofiltered.nonempty
  obtain ⟨M, -, hM⟩ := exists_hom_chartPreimage_eq_empty B S hS i hi hx
    (⟨N₀.1, N₀.2.1, N₀.2.2⟩ : SmallEtaleNeighborhood x)
  have hN : ∀ V : SmallEtale B S hS X.1, (V ⟶ M.chart) →
      Nonempty (IsTerminal (P.obj (op V))) := fun V g ↦
    hP V (Set.eq_empty_iff_forall_notMem.2 fun y hy ↦ by
      simpa [hM] using chartPreimage_subset_preimage B S hS i g hy)
  obtain ⟨hterm⟩ := hN M.chart (𝟙 _)
  let Nel : Φ.fiber.Elements := Φ.fiber.elementsMk M.chart ⟨M.point, M.point_comp⟩
  let d := (Types.isTerminalEquivUnique _ hterm).default
  refine ⟨(Types.isTerminalEquivUnique _).symm
    ⟨⟨Φ.toPresheafFiber Nel.1 Nel.2 P d⟩, fun a ↦ ?_⟩⟩
  obtain ⟨V, t, y, z, hy, hz⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := P) a
    (Φ.toPresheafFiber Nel.1 Nel.2 P d)
  let T : Φ.fiber.Elements := Φ.fiber.elementsMk V t
  let W := IsCofiltered.min (C := Φ.fiber.Elements) T Nel
  let l : W ⟶ T := IsCofiltered.minToLeft T Nel
  let r : W ⟶ Nel := IsCofiltered.minToRight T Nel
  obtain ⟨hterm2⟩ := hN W.1 r.1
  have heq : P.map l.1.op y = P.map l.1.op z :=
    ((Types.isTerminalEquivUnique _ hterm2).uniq _).trans
      ((Types.isTerminalEquivUnique _ hterm2).uniq _).symm
  rw [← hy, ← hz]
  simpa only [GrothendieckTopology.Point.toPresheafFiber_w_apply, l.2] using
    congrArg (Φ.toPresheafFiber W.1 W.2 P) heq

/-! ### The direct image away from the closed subspace -/

/-- **Étale Cohomology 04FX away from the closed subspace, for sheaves of sets.** The small étale
direct image along a closed immersion `i : Z ⟶ X` of a sheaf of sets has exactly one section
over an étale chart of `X` whose points avoid the point set of `Z`.

Such a chart has empty base change along `i`
(`AlgebraicGeometry.Space.isEmpty_smallBaseChange_of_disjoint_range`), the empty sieve covers
that base change, and a sheaf has exactly one section over an object covered by the empty
sieve. -/
theorem nonempty_isTerminal_smallEtaleDirectImage_obj_of_chartPreimage_eq_empty (i : Z ⟶ X)
    (hi : yoneda.relativelyRepresentable i.hom)
    (G : Sheaf (SmallEtale.topology B S hS Z.1) (Type u)) (V : SmallEtale B S hS X.1)
    (hV : chartPreimage B S hS i V = ∅) :
    Nonempty (IsTerminal (((smallEtaleDirectImage B S hS i).obj G).obj.obj (op V))) := by
  have hbot : (⊥ : Sieve ((smallBaseChange B S hS i hi).obj V)) ∈
      SmallEtale.topology B S hS Z.1 ((smallBaseChange B S hS i hi).obj V) :=
    SmallEtale.bot_mem_topology B S hS Z.1 _
      (isEmpty_smallBaseChange_of_disjoint_range B S hS i hi V hV)
  exact ⟨(G.isTerminalOfBotCover _ hbot).ofIso
    ((Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) (op V)).mapIso
      ((smallEtaleDirectImageIsoSheafPushforward B S hS i hi).app G)).symm⟩

/-! ### The essential-image clause of Stacks 04E5, part (1) -/

/-- **Stacks 04E5, part (1), the essential image.** For a closed immersion `i : Z ⟶ X` of
algebraic spaces over `S`, a sheaf of sets on the small étale site of `X` lies in the essential
image of the direct image along `i` exactly when it has exactly one section over every étale
chart of `X` whose points avoid the point set of `Z`, that is exactly when its restriction to
`X ∖ Z` is a singleton.

The forward direction is Étale Cohomology 04FX away from `Z`,
`AlgebraicGeometry.Space.nonempty_isTerminal_smallEtaleDirectImage_obj_of_chartPreimage_eq_empty`.
The converse is Étale Cohomology 04CA: the unit of the adjunction is invertible on the fibre at
every geometric point of `X`, on the point set of `Z` by the triangle identity and Stacks 04K2,
part (4), and off it because both fibres are singletons; the geometric points are a conservative
family, and the unit of a fully faithful right adjoint is invertible exactly on its essential
image. -/
@[stacks 04E5 "part (1): the essential image"]
theorem smallEtalePushforward_essImage_iff_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (smallToposMorphismTypeU B S hS i).pushforward.essImage F ↔
      ∀ V : SmallEtale B S hS X.1, chartPreimage B S hS i V = ∅ →
        Nonempty (IsTerminal (F.obj.obj (op V))) := by
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi
  have := hff.full
  have := hff.faithful
  constructor
  · rintro ⟨G, ⟨e⟩⟩ V hV
    exact ⟨((nonempty_isTerminal_smallEtaleDirectImage_obj_of_chartPreimage_eq_empty
      B S hS i hi.rep G V hV).some).ofIso
        ((Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) (op V)).mapIso e)⟩
  · intro h
    have hiso : IsIso ((smallToposMorphismTypeU B S hS i).adj.unit.app F) := by
      refine isConservativeFamily_etaleSitePoint B S hS X.1 X.property _ fun x ↦ ?_
      by_cases hx : x.image ∈ Set.range (pointsMap B S hS Z.1 i.hom)
      · obtain ⟨z, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS i hi x hx
        refine (NatIso.isIso_map_iff (smallEtaleInverseImageFiberIso B S hS i z) _).mpr ?_
        rw [smallEtaleRingedToposHom_toToposHom, Functor.comp_map]
        infer_instance
      · exact isIso_of_isTerminal
          ((nonempty_isTerminal_presheafFiber_of_chartPreimage_eq_empty
            B S hS i hi x hx F.obj h).some)
          ((nonempty_isTerminal_presheafFiber_of_chartPreimage_eq_empty
            B S hS i hi x hx _ fun V hV ↦
              nonempty_isTerminal_smallEtaleDirectImage_obj_of_chartPreimage_eq_empty
                B S hS i hi.rep _ V hV).some) _
    exact (smallToposMorphismTypeU B S hS i).adj.mem_essImage_of_unit_isIso F

end AlgebraicGeometry.Space

end

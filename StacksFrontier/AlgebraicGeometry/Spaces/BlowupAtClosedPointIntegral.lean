module

public import StacksFrontier.AlgebraicGeometry.Spaces.BirationalOfIsoOverOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupReducedFromComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace

/-!
# The blowup of an integral algebraic space at a closed point

Let `S` be a scheme, let `X` be an integral algebraic space over `S` and let `x ∈ |X|` be a
closed point which is not the only point of `|X|`. Let `b : X' ⟶ X` be the blowup of `X` at
`x`, and assume that `X'` is decent. Then `X'` is integral and `b` is birational.

## Main results

* `AlgebraicGeometry.Space.isIntegralSpace_and_isBirational_of_isBlowupAlong_closedPoint`: the
  statement above.

## Implementation notes

Only the universal property of the blowup is used, through Stacks 085T: `b` is an isomorphism
over the open complement `U = X ∖ {x}`, and the inverse image `b⁻¹(U)` is the complement of the
exceptional divisor, an effective Cartier divisor, hence scheme-theoretically dense (Stacks
083S).

* Reducedness of `X'` is
  `AlgebraicGeometry.Space.hasEtaleLocalProperty_isReduced_of_isBlowupAlong'`.
* Irreducibility: `|b⁻¹(U)|` is homeomorphic to `|U|`, a nonempty open subset of the irreducible
  space `|X|` (nonempty because the generic point of `|X|` is not the closed point `x`, `|X|`
  having another point), hence irreducible; it is dense in `|X'|`, so `|X'|` is irreducible.
* Birationality is `AlgebraicGeometry.Space.isBirational_of_isIso_fromPreimage` applied to `U`:
  the generic point of `|X'|` lies in the nonempty open `|b⁻¹(U)|` and the generic point of `|X|`
  in `|U|`.

Decency of `X'` is a hypothesis: it is not a consequence of the universal property alone, and
in the application to normalized blowups it is supplied by the properness of the sequence over
the base.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 0BHE](https://stacks.math.columbia.edu/tag/0BHE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The blowup of an integral algebraic space at a closed point is a birational morphism of
integral spaces.** Let `X` be an integral algebraic space over `S`, let `x ∈ |X|` be a closed
point such that `|X| ≠ {x}`, and let `b : X' ⟶ X` be the blowup of `X` in the reduced closed
subspace supported on `x`, with `X'` decent. Then `X'` is integral and `b` is birational. -/
theorem isIntegralSpace_and_isBirational_of_isBlowupAlong_closedPoint
    {X X' : AlgebraicSpaces B S hS} (hXint : IsIntegralSpace B S hS X.obj)
    {x : points B S hS X.obj} (hx : IsClosed ({x} : Set (points B S hS X.obj)))
    (hne : ∃ y : points B S hS X.obj, y ≠ x) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS (closedPointSubspace B S hS x hx) b)
    (hdec : IsDecentSpace B S hS X'.obj) :
    ∃ hX'int : IsIntegralSpace B S hS X'.obj,
      IsBirational B S hS X'.property X.property (hX'int.isDecentSpace B S hS X'.obj)
        (hXint.isDecentSpace B S hS X.obj)
        (hX'int.finite_irreducibleComponents B S hS X'.obj)
        (hXint.finite_irreducibleComponents B S hS X.obj) b.hom := by
  classical
  set Z := closedPointSubspace B S hS x hx with hZdef
  set U := openComplementOfClosedSubspace B S hS X Z with hUdef
  have hZpts : subspacePointSet B S hS X.obj Z.1 = {x} :=
    range_pointsMap_ι_reducedClosedSubspace B S hS X.obj X.property {x} hx
  have hUpts : subspacePointSet B S hS X.obj U.1 = {x}ᶜ := by
    rw [hUdef, subspacePointSet_openComplement, hZpts]
  have hZU : subspacePointSet B S hS X.obj Z.1 = (subspacePointSet B S hS X.obj U.1)ᶜ := by
    rw [hUdef, subspacePointSet_openComplement, compl_compl]
  have hiso : IsIso (U.1.fromPreimage b.hom) := isIso_fromPreimage_openComplement hb
  set P := U.1.preimage b.hom with hPdef
  have hP : IsOpenSubspace B S hS P := isOpenSubspace_preimage B S hS b.hom U.1 X.2 X'.2 U.2
  -- The topology of `|X|`: sober and irreducible.
  have hXdec : IsDecentSpace B S hS X.obj := hXint.isDecentSpace B S hS X.obj
  obtain ⟨_, _⟩ := stacksSober_iff_t0_and_quasiSober.mp
    (stacksSober_points_of_isDecentSpace B S hS X.property hXdec)
  let : IrreducibleSpace (points B S hS X.obj) := hXint.2.2
  set η := genericPoint (points B S hS X.obj) with hηdef
  have hηx : η ≠ x := by
    intro h
    obtain ⟨y, hy⟩ := hne
    apply hy
    have hsp : η ⤳ y := (genericPoint_spec (points B S hS X.obj)).specializes (Set.mem_univ y)
    rw [h, specializes_iff_mem_closure, hx.closure_eq] at hsp
    exact hsp
  have hηU : η ∈ subspacePointSet B S hS X.obj U.1 := by
    rw [hUpts]; exact hηx
  -- `|P|` is irreducible, being homeomorphic to a nonempty open subset of `|X|`.
  have hiU := isOpenEmbedding_pointsMap_ι B S hS U.2
  have hiP := isOpenEmbedding_pointsMap_ι B S hS hP
  let e := pointsHomeomorphOfIso B S hS (asIso (U.1.fromPreimage b.hom))
  have hj : Topology.IsOpenEmbedding (pointsMap B S hS U.1.toFunctor U.1.ι ∘ e) :=
    hiU.comp e.isOpenEmbedding
  have hsq : ∀ p, pointsMap B S hS X'.obj b.hom (pointsMap B S hS P.toFunctor P.ι p) =
      pointsMap B S hS U.1.toFunctor U.1.ι (e p) := by
    intro p
    change _ = pointsMap B S hS U.1.toFunctor U.1.ι
      (pointsMap B S hS P.toFunctor (U.1.fromPreimage b.hom) p)
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  obtain ⟨u, hu⟩ := hηU
  let : PreirreducibleSpace (points B S hS P.toFunctor) := hj.preirreducibleSpace
  let : Nonempty (points B S hS P.toFunctor) := ⟨e.symm u⟩
  let : IrreducibleSpace (points B S hS P.toFunctor) := ⟨⟨e.symm u⟩⟩
  have hPirr : IsIrreducible (subspacePointSet B S hS X'.obj P) := by
    rw [subspacePointSet, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _
      (continuous_pointsMap B S hS P.ι).continuousOn
  have hPdense : Dense (subspacePointSet B S hS X'.obj P) :=
    dense_subspacePointSet_preimage_of_isBlowupAlong U Z hb hZU
  have hX'irr : IrreducibleSpace (points B S hS X'.obj) := by
    refine (irreducibleSpace_def _).mpr ?_
    rw [Set.top_eq_univ, ← hPdense.closure_eq]
    exact hPirr.closure
  -- Integrality of `X'`.
  have hX'red : HasEtaleLocalProperty B S hS X'.obj (fun T : Scheme.{u} => IsReduced T) :=
    hasEtaleLocalProperty_isReduced_of_isBlowupAlong' hb hXint.1
  have hX'int : IsIntegralSpace B S hS X'.obj := ⟨hX'red, hdec, hX'irr⟩
  refine ⟨hX'int, ?_⟩
  -- Birationality, from the isomorphism over `U`.
  obtain ⟨_, _⟩ := stacksSober_iff_t0_and_quasiSober.mp
    (stacksSober_points_of_isDecentSpace B S hS X'.property hdec)
  have hgenX : genericPoints (points B S hS X'.obj) ⊆
      Set.range (pointsMap B S hS P.toFunctor P.ι) := by
    rw [genericPoints_eq_singleton, Set.singleton_subset_iff]
    refine ((genericPoint_spec (points B S hS X'.obj)).mem_open_set_iff
      hiP.isOpen_range).mpr ?_
    exact ⟨_, Set.mem_univ _, Set.mem_range_self (e.symm u)⟩
  have hgenY : genericPoints (points B S hS X.obj) ⊆
      Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) := by
    rw [genericPoints_eq_singleton, Set.singleton_subset_iff]
    exact ⟨u, hu⟩
  exact isBirational_of_isIso_fromPreimage X'.property X.property _ _ _ _ b.hom U.1 U.2
    hgenX hgenY

end AlgebraicGeometry.Space

end

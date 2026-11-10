module

public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Dimension.Codimension

/-!
# The schematic neighbourhood of a prime divisor meeting the schematic locus

Let `X` be a locally Noetherian integral algebraic space over a scheme `S` and let `Z ⊆ X` be a
prime divisor with generic point `ξ`. The proof of Stacks 0ENM opens with "after shrinking `X`
we may assume `X` is an integral Noetherian scheme": that shrinking is what this file supplies.

If `Z` meets the schematic locus of `X`, then the schematic locus is an open subspace which is
represented by a scheme `V`, and its point set is an open subset of `|X|` meeting `|Z|`, hence
contains `ξ` because `ξ` is a generic point of `|Z|`. The point `v ∈ V` above `ξ` makes `V` an
elementary étale neighbourhood of `ξ` whose structure morphism is an open immersion, and `V` is
integral and locally Noetherian because `|V| → |X|` is an open embedding into an irreducible
space and reducedness and local Noetherianness are étale-local on `X`. Finally `v` has
codimension one in `V` because an open embedding preserves the coheight of an irreducible closed
subset it meets.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.exists_schematic_neighborhood` is the shrinking step of
  Stacks 0ENM: a prime divisor meeting the schematic locus has, at its generic point, an
  elementary étale neighbourhood which is an open immersion and whose scheme is integral,
  locally Noetherian and of codimension one at the marked point.

## Implementation notes

The statement of the hypothesis is that the point set of `Z` meets the point set of the
schematic locus, which is the reading of "the prime divisor `Z ⊂ X` meets the schematic locus of
`X`" of the source; `AlgebraicGeometry.Space.subspacePointSet` is the point set of a subfunctor,
as for `AlgebraicGeometry.Space.PrimeDivisor.support`.

The neighbourhood produced is the *whole* schematic locus, not an open subscheme of it chosen
around `ξ`: no shrinking beyond passing to the schematic locus is needed, since the schematic
locus is already integral and locally Noetherian whenever `X` is, and the order of vanishing at
`ξ` is computed in the local ring there.

That the schematic locus is an open subspace and is representable is taken in the
hypothesis-free form
`AlgebraicGeometry.Space.isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace`
rather than through the cofinality-indexed forms of
`StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocus`.

This supplies exactly the hypothesis that
`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing` carries in place of
the source's "`Z` meets the schematic locus of `X`", and under the hypotheses here the other
side conditions of that result are available too rather than carried: cofilteredness of the
elementary étale neighbourhoods is
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isCofiltered_of_nonempty` applied to the
neighbourhood produced here, locality of `𝒪^h_{X, ξ}` is
`AlgebraicGeometry.Space.henselianLocalRing_isLocalRing`, and its nontriviality,
Noetherianness and dimension bound are
`AlgebraicGeometry.Space.PrimeDivisor.nontrivial_genericHenselianLocalRing`,
`AlgebraicGeometry.Space.PrimeDivisor.isNoetherianRing_genericHenselianLocalRing` and
`AlgebraicGeometry.Space.PrimeDivisor.krullDimLE_genericHenselianLocalRing`. The implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/OrderOfVanishingChartComparison.lean` once
recorded cofilteredness and the injection `R(X) → Q(𝒪^h_{X, ξ})` of Stacks 0ENK as unavailable;
**that reading was false and those notes have since been corrected**, so this sentence no longer
points at anything — they now name
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.isCofiltered_of_nonempty` and
`AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/PrimeDivisorFunctionFieldEmbedding.lean:243`)
themselves.

What still separates the comparison from the full statement of Stacks 0ENM is the presentation
of the rational function, not its hypotheses. The order of vanishing of Definition 0ENL is
evaluated at a rational function of `X` through the embedding `R(X) → Q(𝒪^h_{X, ξ})` of Stacks
0ENK, which is
`AlgebraicGeometry.Space.PrimeDivisor.rationalFunctionsToGenericTotalFractionRing` and is built
from the affine chart `AlgebraicGeometry.Space.PrimeDivisor.genericChart` of Stacks 0BBP, while
`AlgebraicGeometry.Space.PrimeDivisor.ord_functionFieldToTotalFractionRing` evaluates it at a
rational function of the given chart through
`AlgebraicGeometry.Space.PrimeDivisor.functionFieldToTotalFractionRing`. Identifying the two
needs the independence of `AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing` of the
chart — a verification the source omits — which is
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_comp_eq`. The full statement of
Stacks 0ENM, at the hypotheses of the source, is assembled from this lemma and that one in
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_scheme_ord` of
`StacksFrontier/AlgebraicGeometry/Spaces/OrderOfVanishingSchematicLocus.lean`.

## References

* [Stacks Project, Tag 02RJ](https://stacks.math.columbia.edu/tag/02RJ)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hInt : IsIntegralSpace B S hS X)
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (Z : PrimeDivisor B S hS X)

include hX hInt hN in
/-- **Stacks 0ENM**, the shrinking step of the proof. If a prime divisor `Z` of a locally
Noetherian integral algebraic space `X` meets the schematic locus of `X`, then the generic point
of `Z` has an elementary étale neighbourhood whose structure morphism is an open immersion and
whose scheme is integral, locally Noetherian and of codimension one at the marked point.

The neighbourhood is the schematic locus itself: it is an open subspace represented by a scheme
`V` by Stacks 03JH, its point set is open in `|X|` and meets `|Z|`, hence contains the generic
point `ξ` of `Z`, and the point `v ∈ V` over `ξ` has codimension one because `|V| → |X|` is an
open embedding. -/
@[stacks 0ENM "the shrinking step of the proof: from the hypothesis that the prime divisor meets
  the schematic locus, an elementary étale neighbourhood of its generic point which is an open
  immersion and whose scheme is integral, locally Noetherian and of codimension one at the
  marked point"]
theorem PrimeDivisor.exists_schematic_neighborhood
    (hmeet : (Z.support B S hS X ∩
      subspacePointSet B S hS X (schematicLocus B S hS X)).Nonempty) :
    ∃ U : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X),
      IsOpenImmersion B S hS U.toSpace ∧
      AlgebraicGeometry.IsIntegral U.scheme.left.1 ∧
      IsLocallyNoetherian U.scheme.left.1 ∧
      coheight U.point = 1 := by
  classical
  have _ : IrreducibleSpace (points B S hS X) := hInt.2.2
  set L := schematicLocus B S hS X
  obtain ⟨hL, hLrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  let _ := hLrep
  -- The schematic locus is represented by a scheme `V`, open in `X`.
  set V := L.toFunctor.reprX
  set e : yoneda.obj V ≅ L.toFunctor := L.toFunctor.reprW
  set i : yoneda.obj V ⟶ X := e.hom ≫ L.ι with hidef
  have hi : IsOpenImmersion B S hS i :=
    MorphismProperty.RespectsIso.precomp _ e.hom L.ι hL.2
  have hiet : IsEtale B S hS i := isEtale_of_isOpenImmersion B S hS hi
  have hipre := (isEtale_iff_presheaf_of_yoneda B S hS i).1 hiet
  have _ : Mono i := mono_of_isOpenImmersion B S hS i hi
  -- Its points form an open subset of `|X|`, through the open embedding `j`.
  set E := schemePointsHomeomorph B S hS V with hEdef
  set j : ((BigFppfOver.toScheme B S hS).obj V) → points B S hS X :=
    pointsMap B S hS (yoneda.obj V) i ∘ E.symm
  have hj : Topology.IsOpenEmbedding j := by
    refine Topology.IsOpenEmbedding.comp ?_ E.symm.isOpenEmbedding
    exact .of_continuous_injective_isOpenMap (continuous_pointsMap B S hS i)
      (pointsMap_injective_of_mono B S hS i)
      (isOpenMap_pointsMap_of_isEtale B S hS i (isAlgebraicSpace_yoneda B S hS V) hX hiet)
  have hLrange : Set.range j = subspacePointSet B S hS X L := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨pointsMap B S hS (yoneda.obj V) e.hom (E.symm v), ?_⟩
      exact (congrFun (pointsMap_comp B S hS (F := yoneda.obj V) e.hom L.ι) (E.symm v)).symm
    · rintro ⟨q, rfl⟩
      refine ⟨E (pointsMap B S hS L.toFunctor e.inv q), ?_⟩
      have hcomp := congrFun (pointsMap_comp B S hS (F := L.toFunctor) e.inv i) q
      rw [show e.inv ≫ i = L.ι by rw [hidef, Iso.inv_hom_id_assoc]] at hcomp
      change pointsMap B S hS (yoneda.obj V) i (E.symm (E _)) = _
      rw [E.symm_apply_apply]
      exact hcomp.symm
  -- The generic point of `Z` lies in it, since it is a generic point of `|Z|`.
  obtain ⟨v, hv⟩ : Z.genericPoint B S hS X ∈ Set.range j := by
    rw [hLrange]
    exact ((Z.isGenericPoint_genericPoint B S hS X).mem_open_set_iff
      (hLrange ▸ hj.isOpen_range)).2 hmeet
  -- `V` is integral and locally Noetherian.
  have _ : Nonempty ((BigFppfOver.toScheme B S hS).obj V) := ⟨v⟩
  have _ : IrreducibleSpace ((BigFppfOver.toScheme B S hS).obj V) := hj.irreducibleSpace
  have _ : IsReduced ((BigFppfOver.toScheme B S hS).obj V) :=
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsReduced Y) hX).mp
      hInt.1 V i hipre
  have hVint : AlgebraicGeometry.IsIntegral ((BigFppfOver.toScheme B S hS).obj V) :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩
  -- `v` has codimension one, the coheight being preserved by the open embedding `j`.
  have hcodim : coheight v = 1 := by
    have hmap : IrreducibleCloseds.map j hj.continuous (IrreducibleCloseds.closureSingleton v) =
        IrreducibleCloseds.closureSingleton (Z.genericPoint B S hS X) := by
      ext : 1
      simp [closure_image_closure hj.continuous, hv]
    have hc := hj.coheight_map (IrreducibleCloseds.closureSingleton v)
    rw [hmap] at hc
    rw [← coheight_orderIso
      (irreducibleSetEquivPoints (α := ((BigFppfOver.toScheme B S hS).obj V))).symm v]
    exact hc.symm.trans (Z.codimension_genericPoint B S hS X)
  -- Assemble the elementary étale neighbourhood.
  have hk := B.residueField_spec_contains V.left.property v
  have _ : Mono (residueFieldMap B S hS V v hk) := by
    apply (BigFppfOver.toScheme B S hS).mono_of_mono_map
    change Mono (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v)
    infer_instance
  refine ⟨{ scheme := V
            point := v
            residueField_contained := hk
            toSpace := i
            etale_toSpace := hiet
            map_point := ?_
            mono_residueField := inferInstance }, hi, hVint,
    (exists_atlas_iff_forall_etale B S hS X (fun Y : Scheme.{u} => IsLocallyNoetherian Y) hX).mp
      hN V i hipre, hcodim⟩
  have he : presheafPoint B S hS V v hk = E.symm v := by
    refine E.injective ?_
    rw [E.apply_symm_apply, hEdef, schemePointsHomeomorph_apply]
    exact pointsToScheme_presheafPoint B S hS V v hk
  change pointsMap B S hS (yoneda.obj V) i (presheafPoint B S hS V v hk) = _
  rwa [he]

end AlgebraicGeometry.Space

end

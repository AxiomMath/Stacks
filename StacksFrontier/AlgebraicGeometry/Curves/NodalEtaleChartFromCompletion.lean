module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksCore.Tactic.StacksAttribute

/-!
# The étale local chart of a nodal family, from an isomorphism of completed local rings

This file carries out the last step of the first proof of Tag 0CBY: once the completed local
ring of `f : X ⟶ S` at `x` has been identified with the completed local ring of a nodal chart
`Spec R[u, v]/(uv - h)` over an affine étale neighbourhood `Spec R ⟶ S` of the image of `x`,
Artin approximation produces an étale neighbourhood of `x` which maps étale-ly to that chart.
That is the content of `Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood`, and it is
what Tag 0CBY asserts beyond the cartesian square identified in
`StacksFrontier.AlgebraicGeometry.Curves.NodalEtaleLocalStructure`.

The step is an application of Tag 0CAV, `StacksDraft.ArtinApproximation`
`.exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv`: the nodal chart is of
finite type over `R`, hence locally of finite type over `S` through the étale structure morphism
of the chart's base, so `X` and the chart are two schemes locally of finite type over the
locally Noetherian base `S`, and an isomorphism of their completed local rings over `𝒪_{S, s}`
produces a single pointed scheme sitting étale-ly over both.

## Main results

* `Stacks.NodalEtaleLocalStructure.locallyOfFiniteType_specMap_algebraMap_nodalChartRing` — the
  structure morphism of a nodal chart is locally of finite type.
* `Stacks.NodalEtaleLocalStructure.nodalChartNeighbourhood_of_adicCompletion_ringEquiv` — the
  étale local chart from an isomorphism of completed local rings.
* `Stacks.NodalEtaleLocalStructure.NodalChartNeighbourhood.ofEtaleBaseChange` — the chart form
  descends along an étale base change: a chart for the base change of `f` along an étale
  `V ⟶ S` at a point over `x` is a chart for `f` at `x`.

## Implementation notes

The hypothesis of the main result is exactly the hypothesis of Tag 0CAV, written for the chart:
a ring isomorphism of the two completed local rings whose composite with the two structure maps
out of `𝒪_{S, s}` agree. No nodality enters; what nodality is for is the *production* of such
an isomorphism, which is Tag 0CBX together with the étale neighbourhood of the base produced by
Tag 0GDX.

Finite typeness of the chart is read off the presentation `R[u, v]/(uv - h)` of
`Stacks.nodalChartRing` as a quotient of a polynomial ring in two variables, through
`AlgebraicGeometry.HasRingHomProperty.Spec_iff`.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0CAV](https://stacks.math.columbia.edu/tag/0CAV)
* [Stacks Project, Tag 0CBX](https://stacks.math.columbia.edu/tag/0CBX)
* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Stacks.Curves
open StacksDraft.ArtinApproximation

universe u

namespace Stacks.NodalEtaleLocalStructure

section FiniteType

variable {R : Type u} [CommRing R] (h : R)

/-- The nodal chart ring `R[x, y]/(xy - h)` is an `R`-algebra of finite type: it is a quotient of
the polynomial ring in two variables. -/
public theorem finiteType_nodalChartRing : Algebra.FiniteType R (nodalChartRing R h) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ R (Ideal.span {nodalEquation R h}))
    Ideal.Quotient.mk_surjective

/-- The structure morphism `Spec R[x, y]/(xy - h) ⟶ Spec R` of a nodal chart is locally of
finite type. -/
public instance locallyOfFiniteType_specMap_algebraMap_nodalChartRing :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h)))) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr (finiteType_nodalChartRing h))

end FiniteType

/-! ### The étale neighbourhood produced by Artin approximation -/

/-- **The étale local chart of Tag 0CBY, from an isomorphism of completed local rings.** Let
`f : X ⟶ S` be locally of finite type over a locally Noetherian scheme, let `x` be a point of
`X` whose image has a G-ring for local ring, let `Spec R ⟶ S` be an affine étale neighbourhood
of that image and let `h` be an element of `R`. If the completed local ring of `X` at `x` is
isomorphic, as an algebra over the local ring of `S` at the image of `x`, to the completed local
ring of the nodal chart `Spec R[u, v]/(uv - h)` at a point `y` over the image of `x`, then `f`
admits the étale local chart of Tag 0CBY at `x`.

This is Tag 0CAV applied to `X` and the chart, both read as schemes locally of finite
type over `S`. No nodality is used: nodality is what produces the isomorphism of completions,
through Tag 0CBX and the étale neighbourhood of the base of Tag 0GDX. -/
public theorem nonempty_nodalChartNeighbourhood_of_adicCompletion_ringEquiv
    {X S : Scheme.{u}} {f : X ⟶ S} [IsLocallyNoetherian S] [LocallyOfFiniteType f] {x : X}
    {R : Type u} [CommRing R] (e : Spec (.of R) ⟶ S) [Etale e] (h : R)
    (y : Spec (.of (nodalChartRing R h)))
    (hxy : f x = (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))) ≫ e) y)
    (hG : IsGRing (S.presheaf.stalk (f x)))
    (Φ : AdicCompletion
          (maximalIdeal ((Spec (.of (nodalChartRing R h))).presheaf.stalk y))
          ((Spec (.of (nodalChartRing R h))).presheaf.stalk y) ≃+*
        AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (hΦ : Φ.toRingHom.comp
        ((algebraMap ((Spec (.of (nodalChartRing R h))).presheaf.stalk y)
          (AdicCompletion
            (maximalIdeal ((Spec (.of (nodalChartRing R h))).presheaf.stalk y))
            ((Spec (.of (nodalChartRing R h))).presheaf.stalk y))).comp
          ((S.presheaf.stalkCongr (.of_eq hxy)).hom ≫
            (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))) ≫
              e).stalkMap y).hom) =
      (algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (f.stalkMap x).hom) :
    Nonempty (NodalChartNeighbourhood f x) := by
  obtain ⟨U, q, hqEt, hq, -, -, hover, -⟩ :=
    exists_common_elementaryEtaleNeighborhood_of_adicCompletion_ringEquiv f
      (Spec.map (CommRingCat.ofHom (algebraMap R (nodalChartRing R h))) ≫ e) x y hxy hG 1
      le_rfl Φ hΦ
  exact ⟨{ base := R
           param := h
           U := U.scheme
           toSource := U.toBase
           toBase := e
           toChart := q
           pt := U.point
           etale_toSource := U.etale_toBase
           etale_toBase := inferInstance
           etale_toChart := hqEt
           pt_mem := U.map_point
           comm := hover.symm }⟩

/-! ### The chart form is insensitive to an étale localization of source and target -/

/-- **The chart form transfers along étale morphisms of source and target.** Let `f : X ⟶ S` and
`f' : X' ⟶ V` be two morphisms related by étale morphisms `p : X' ⟶ X` and `eV : V ⟶ S` making
the square commute. An étale local chart for `f'` at a point `x'` of `X'` is an étale local
chart for `f` at the image of `x'`: the two étale morphisms are simply composed into the
corresponding legs of the chart.

This is the step by which both reductions of the first proof of Tag 0CBY are discharged: the
reduction to a split node replaces `(S, s)` by an étale neighbourhood `(V, v)` and `X` by
`X ×_S V`, and the reduction to a base of finite type over the integers replaces `f` by a model
over a Noetherian approximation of the base. In both cases the conclusion for the replacement
gives the conclusion for `f` through this lemma. -/
public theorem nonempty_nodalChartNeighbourhood_of_etale {X X' S V : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ V} (p : X' ⟶ X) [Etale p] (eV : V ⟶ S) [Etale eV]
    (hcomm : p ≫ f = f' ≫ eV) {x' : X'} {x : X} (hx : p x' = x)
    (d : NodalChartNeighbourhood f' x') :
    Nonempty (NodalChartNeighbourhood f x) := by
  have hsrc := d.etale_toSource
  have hbase := d.etale_toBase
  have hchart := d.etale_toChart
  refine ⟨{ base := d.base
            param := d.param
            U := d.U
            toSource := d.toSource ≫ p
            toBase := d.toBase ≫ eV
            toChart := d.toChart
            pt := d.pt
            etale_toSource := inferInstance
            etale_toBase := inferInstance
            etale_toChart := hchart
            pt_mem := ?_
            comm := ?_ }⟩
  · show p (d.toSource d.pt) = x
    rw [d.pt_mem, hx]
  · calc (d.toSource ≫ p) ≫ f = d.toSource ≫ f' ≫ eV := by
          rw [Category.assoc, hcomm]
    _ = (d.toSource ≫ f') ≫ eV := (Category.assoc _ _ _).symm
    _ = d.toChart ≫ Spec.map (CommRingCat.ofHom
          (algebraMap d.base (nodalChartRing d.base d.param))) ≫ d.toBase ≫ eV := by
          rw [d.comm, Category.assoc, Category.assoc]

end Stacks.NodalEtaleLocalStructure

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFractionEmbeddingNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaChart.RationalFunctionOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldEmbedding

/-!
# The order of vanishing of the pullback of a rational function along an étale morphism

Let `f : X ⟶ Y` be an étale morphism of decent, locally Noetherian, integral algebraic spaces
over `S` carrying the generic point of `X` to the generic point of `Y`. For prime divisors
`Z ⊆ X` and `Z' ⊆ Y` with the generic point of `Z` over that of `Z'`, and an invertible rational
function `g` on `Y`,

`ord_Z(g ∘ f) = ord_{Z'}(g)`,

both orders of vanishing read at the canonical embeddings of Stacks 0ENK. This is the
multiplicity-one case of Stacks 0EQA, and it is proved on one affine étale chart: the chosen
affine elementary étale neighbourhood of the generic point of `Z` is, through `f`, also an
étale chart of `Y`, and the reading of `g ∘ f` there is the reading of `g`.

## Main definitions

* `AlgebraicGeometry.Space.etaleChartComp`: an étale chart of `X`, read as an étale chart of `Y`
  through the étale morphism `f`.

## Main results

* `AlgebraicGeometry.Space.chartSchemeToPoints_etaleChartComp`: the points of that chart lie over
  the images under `f` of the points they lie over in `X`.
* `AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_ord_of_isEtale`: the order of vanishing
  pulls back unchanged along an étale morphism.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENM](https://stacks.math.columbia.edu/tag/0ENM)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

section EtaleOrd

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y)
    (hintX : IsIntegralSpace B S hS X) (hintY : IsIntegralSpace B S hS Y)
    (hNX : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNY : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {f : X ⟶ Y} (hetale : IsEtale B S hS f)

/-- An étale chart of `X` is an étale chart of `Y` along an étale morphism `f : X ⟶ Y`: the
composite of the chart with `f` is again representable and étale. The underlying object of the
site, and hence the scheme and its local rings, are unchanged. -/
def etaleChartComp (V : SmallEtale B S hS X) : SmallEtale B S hS Y :=
  ⟨CostructuredArrow.mk (V.obj.hom ≫ f),
    (isEtale_iff_presheaf_of_yoneda B S hS (V.obj.hom ≫ f)).1
      (isEtale_comp B S hS
        ((isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property) hetale)⟩

/-- A point of the scheme of a chart of `X` lies, as a point of the same scheme read as a chart
of `Y`, over the image under `f` of the point of `|X|` it lies over. -/
theorem chartSchemeToPoints_etaleChartComp (V : SmallEtale B S hS X)
    (v : V.obj.left.left.1) :
    chartSchemeToPoints B S hS Y (etaleChartComp B S hS hetale V) v =
      pointsMap B S hS X f (chartSchemeToPoints B S hS X V v) := by
  have h1 : chartSchemeToPoints B S hS Y (etaleChartComp B S hS hetale V) v =
      pointsMap B S hS (yoneda.obj V.obj.left) (V.obj.hom ≫ f)
        ((canonicalSiteFieldPoint B S hS V.obj.left v).class B S hS
          (yoneda.obj V.obj.left)) :=
    chartSchemeToPoints_eq_pointsMap B S hS Y (etaleChartComp B S hS hetale V) v
  have h2 : chartSchemeToPoints B S hS X V v =
      pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom
        ((canonicalSiteFieldPoint B S hS V.obj.left v).class B S hS
          (yoneda.obj V.obj.left)) :=
    chartSchemeToPoints_eq_pointsMap B S hS X V v
  rw [h1, h2]
  exact congrFun (pointsMap_comp B S hS (yoneda.obj V.obj.left) V.obj.hom f) _

/-- Restriction of global sections along the identity of a chart is the identity. -/
private theorem chartGlobalSectionsRestrict_id (U : BigFppfOver B S hS) :
    chartGlobalSectionsRestrict B S hS (𝟙 U) = RingHom.id Γ(U.left.1, ⊤) := by
  rw [chartGlobalSectionsRestrict, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction on total rings of fractions along the identity of a chart is the identity. -/
private theorem chartFractionMap_id (U : BigFppfOver B S hS)
    (hj : nonZeroDivisors Γ(U.left.1, ⊤) ≤ (nonZeroDivisors Γ(U.left.1, ⊤)).comap
      (chartGlobalSectionsRestrict B S hS (𝟙 U))) :
    chartFractionMap B S hS (𝟙 U) hj = RingHom.id (FractionRing Γ(U.left.1, ⊤)) :=
  IsLocalization.ringHom_ext (nonZeroDivisors Γ(U.left.1, ⊤)) (RingHom.ext fun a => by
    rw [RingHom.comp_apply, chartFractionMap_algebraMap, chartGlobalSectionsRestrict_id]
    rfl)

include hX hY hintX hintY hetale in
/-- **The order of vanishing of a rational function pulls back unchanged along an étale
morphism.** Let `f : X ⟶ Y` be an étale morphism of decent, locally Noetherian, integral
algebraic spaces over `S` carrying the generic point of `X` to the generic point of `Y`, let
`Z ⊆ X` and `Z' ⊆ Y` be prime divisors and suppose the generic point of `Z` lies over the
generic point of `Z'`. Then for an invertible rational function `g` of `Y`

`ord_Z(g ∘ f) = ord_{Z'}(g)`,

both orders of vanishing being taken at the canonical embeddings of Stacks 0ENK.

This is the multiplicity-one case of Stacks 0EQA, obtained without the henselian local rings:
both sides are computed on *one* affine étale chart, by Stacks 0ENM in the form
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap`.
The chart is the chosen affine elementary étale neighbourhood of the generic point of `Z`;
because `f` is étale it is also an affine étale chart of `Y`, through the generic point of `Z'`,
and the reading of `g ∘ f` on it is the reading of `g` on it, by
`AlgebraicGeometry.Space.rationalFunctionsToTotalFractionRing_rationalFunctionMap` at the
identity morphism of charts. So the two orders of vanishing are the order of vanishing of one
element of the total ring of fractions of one local ring. -/
theorem ord_rationalFunctionMap_eq_ord_of_isEtale
    (hgen : pointsMap B S hS X f (genericPoint B S hS hX hintX) = genericPoint B S hS hY hintY)
    (ZX : PrimeDivisor B S hS X) (ZY : PrimeDivisor B S hS Y)
    (hZ : pointsMap B S hS X f (ZX.genericPoint B S hS X) = ZY.genericPoint B S hS Y)
    (g : (rationalFunctions B S hS hY)ˣ) :
    (genericFractionEmbedding B S hS hX hdecX hintX hNX).ord
        (Units.map (rationalFunctionMap B S hS hX hY hintX hintY f hgen).toMonoidHom g) ZX =
      (genericFractionEmbedding B S hS hY hdecY hintY hNY).ord g ZY := by
  set V := ZX.genericEtaleChart B S hS hX hdecX with hVdef
  have : IsAffine V.obj.left.left.1 := ZX.isAffine_genericChart B S hS hX hdecX
  have : IsReduced V.obj.left.left.1 :=
    (exists_atlas_iff_forall_etale B S hS X (fun T : Scheme.{u} => IsReduced T) hX).mp hintX.1
      V.obj.left V.obj.hom V.property
  have : IsLocallyNoetherian V.obj.left.left.1 :=
    (exists_atlas_iff_forall_etale B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T) hX).mp
      hNX V.obj.left V.obj.hom V.property
  obtain ⟨v, hvdef⟩ : ∃ v : V.obj.left.left.1, v = (ZX.genericChart B S hS hX hdecX).point :=
    ⟨_, rfl⟩
  have hvX : chartSchemeToPoints B S hS X V v = ZX.genericPoint B S hS X := by
    rw [hvdef]
    exact ZX.chartSchemeToPoints_genericEtaleChart_point B S hS hX hdecX
  have := ZX.krullDimLE_chartStalk B S hS hX hdecX V v hvX
  set W := etaleChartComp B S hS hetale V with hWdef
  have : IsAffine W.obj.left.left.1 := ‹IsAffine V.obj.left.left.1›
  have : IsReduced W.obj.left.left.1 := ‹IsReduced V.obj.left.left.1›
  have : IsLocallyNoetherian W.obj.left.left.1 := ‹IsLocallyNoetherian V.obj.left.left.1›
  have hvY : chartSchemeToPoints B S hS Y W v = ZY.genericPoint B S hS Y :=
    (chartSchemeToPoints_etaleChartComp B S hS hetale V v).trans (by rw [hvX, hZ])
  have : Ring.KrullDimLE 1 (W.obj.left.left.1.presheaf.stalk v) :=
    ‹Ring.KrullDimLE 1 (V.obj.left.left.1.presheaf.stalk v)›
  have hj : nonZeroDivisors Γ(V.obj.left.left.1, ⊤) ≤
      (nonZeroDivisors Γ(V.obj.left.left.1, ⊤)).comap
      (chartGlobalSectionsRestrict B S hS (𝟙 V.obj.left)) := by
    rw [chartGlobalSectionsRestrict_id]
    exact fun _ h => h
  have hV := (isEtale_iff_presheaf_of_yoneda B S hS V.obj.hom).2 V.property
  have key := rationalFunctionsToTotalFractionRing_rationalFunctionMap B S hS hX hY hintX hintY
    f hgen V.obj.hom hV (V.obj.hom ≫ f) (isEtale_comp B S hS hV hetale)
    (𝟙 V.obj.left) (by rw [CategoryTheory.Functor.map_id, Category.id_comp]) hj
    (g : rationalFunctions B S hS hY)
  rw [chartFractionMap_id] at key
  have hread : chartPointRationalFunctionMap B S hS hX V v
        (rationalFunctionMap B S hS hX hY hintX hintY f hgen
          (g : rationalFunctions B S hS hY)) =
      chartPointRationalFunctionMap B S hS hY W v (g : rationalFunctions B S hS hY) :=
    congrArg (V.obj.left.left.1.totalFractionRingToStalkFractionRing v) (by rw [key]; rfl)
  rw [ZX.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap B S hS hX hdecX hintX hNX V v hvX
      (Units.map (rationalFunctionMap B S hS hX hY hintX hintY f hgen).toMonoidHom g),
    ZY.ord_eq_ordTotalFracInt_chartPointRationalFunctionMap B S hS hY hdecY hintY hNY W v hvY g]
  exact Ring.ordTotalFracInt_congr (V.obj.left.left.1.presheaf.stalk v) _ _ hread

end EtaleOrd

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeRestriction

/-!
# Chart base change commutes with Zariski opens

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over `S`, let `V` be an étale
scheme chart of `Y` and let `O` be a Zariski open of `chartScheme V`. Base change along `f`
(`AlgebraicGeometry.Space.smallBaseChange`, Stacks 03G2 part (4)) turns `V` into the étale scheme
chart `V ×_Y X` of `X`, and the base change `(openChart V O) ×_Y X` of the smaller chart is the
Zariski open of `V ×_Y X` that `O` pulls back to.

## Main definitions

* `AlgebraicGeometry.Space.smallBaseChangeSchemeProjection`: the cartesian projection
  `V ×_Y X ⟶ V` on underlying schemes.
* `AlgebraicGeometry.Space.openChartSmallBaseChangeProjection`: the cartesian projection of the
  smaller chart, `openChart (V ×_Y X) (preimage of O) ⟶ openChart V O`.
* `AlgebraicGeometry.Space.smallBaseChangeOpenChartIso`: the base change of the open chart
  `openChart V O` is the open chart of `V ×_Y X` cut out by the preimage of `O`, as an
  isomorphism of étale scheme charts of `X`.
* `AlgebraicGeometry.Space.smallBaseChangeOpenChartFunctorIso`: the same isomorphism, as a
  natural isomorphism of functors of the open.
* `AlgebraicGeometry.Space.structureSheafSmallBaseChangeOpenChartIso`: the induced ring
  isomorphism on regular functions.

## Main results

* `AlgebraicGeometry.Space.isPullback_openChart_smallBaseChange`: the open chart of `V ×_Y X`
  cut out by the preimage of `O` is a fibre product of `openChart V O` along `f`.
* `AlgebraicGeometry.Space.openChartBaseChangeIso_hom_comp_hom` and
  `AlgebraicGeometry.Space.openChartBaseChangeIso_hom_comp_projection`: the comparison
  isomorphism is compatible with both cartesian projections.
* `AlgebraicGeometry.Space.smallBaseChangeOpenChartIso_naturality`: the isomorphism is natural
  in the Zariski open.

## Implementation notes

`openChart` is semireducible, so a statement that spells one object as
`AlgebraicGeometry.Space.openSub` and another as `AlgebraicGeometry.Space.openChart` elaborates,
but the resulting term is type-correct only at default transparency and `rw` and `simp` cannot
see inside it. `AlgebraicGeometry.Space.openChartSmallBaseChangeProjection` and
`AlgebraicGeometry.Space.smallBaseChangeSchemeProjection` isolate every such coercion in the type
ascription of a definition, so that each statement below is well typed with reducible unfolding
alone.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)

/-- The cartesian projection `V ×_Y X ⟶ V` of Stacks 03G2, part (4), read on the underlying
schemes of the two charts. -/
def smallBaseChangeSchemeProjection :
    chartScheme ((smallBaseChange B S hS f hf).obj V) ⟶ chartScheme V :=
  (BigFppfOver.toScheme B S hS).map (hf.snd V.obj.hom)

variable (O : (chartScheme V).Opens)

/-- The cartesian projection of the smaller chart: the restriction of the projection
`V ×_Y X ⟶ V` to the Zariski open `O` and its preimage, read as a morphism of the big fppf
category over `S` from the open chart of `V ×_Y X` to the open chart of `V`. -/
def openChartSmallBaseChangeProjection :
    (SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1
        ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O)) ⟶
      (SmallEtale.toOver B S hS Y.1).obj (openChart B S hS Y.1 V O) :=
  openSubHomOfRestrict (hf.snd V.obj.hom) O

/-- **The open chart of `V ×_Y X` cut out by the preimage of `O` is a fibre product of
`openChart V O` along `f`.** -/
theorem isPullback_openChart_smallBaseChange :
    IsPullback (openChart B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O)).obj.hom
      (yoneda.map (openChartSmallBaseChangeProjection B S hS f hf V O)) f.hom
      (openChart B S hS Y.1 V O).obj.hom :=
  ((isPullback_openSubHomOfRestrict (hf.snd V.obj.hom) O).map yoneda).paste_horiz
    (hf.isPullback V.obj.hom)

/-- The object of the big fppf category over `S` representing the base change of the chart
`openChart V O` is isomorphic to the open subobject of the object representing `V ×_Y X` that
the preimage of `O` cuts out. -/
def openChartBaseChangeIso :
    hf.pullback (openChart B S hS Y.1 V O).obj.hom ≅
      (openChart B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O)).obj.left :=
  yoneda.preimageIso ((hf.isPullback (openChart B S hS Y.1 V O).obj.hom).isoIsPullback _ _
    (isPullback_openChart_smallBaseChange B S hS f hf V O))

/-- `AlgebraicGeometry.Space.openChartBaseChangeIso` is, after `CategoryTheory.yoneda`, the
comparison isomorphism of the two fibre products of `openChart V O ⟶ Y ⟵ X`. -/
theorem yoneda_map_openChartBaseChangeIso_hom :
    yoneda.map (openChartBaseChangeIso B S hS f hf V O).hom =
      ((hf.isPullback (openChart B S hS Y.1 V O).obj.hom).isoIsPullback _ _
        (isPullback_openChart_smallBaseChange B S hS f hf V O)).hom :=
  yoneda.map_preimage _

/-- `AlgebraicGeometry.Space.openChartBaseChangeIso` lies over `X`: composed with the chart of
the open subobject of `V ×_Y X` it is the chart of the base change of `openChart V O`. -/
theorem openChartBaseChangeIso_hom_comp_hom :
    yoneda.map (openChartBaseChangeIso B S hS f hf V O).hom ≫
        (openChart B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
          (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O)).obj.hom =
      hf.fst (openChart B S hS Y.1 V O).obj.hom :=
  by
  rw [yoneda_map_openChartBaseChangeIso_hom]
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- `AlgebraicGeometry.Space.openChartBaseChangeIso` lies over `openChart V O`: composed with the
cartesian projection of the smaller chart it is the cartesian projection of the base change of
`openChart V O`. -/
theorem openChartBaseChangeIso_hom_comp_projection :
    (openChartBaseChangeIso B S hS f hf V O).hom ≫
        openChartSmallBaseChangeProjection B S hS f hf V O =
      hf.snd (openChart B S hS Y.1 V O).obj.hom :=
  yoneda.map_injective (by
    rw [yoneda.map_comp, yoneda_map_openChartBaseChangeIso_hom]
    exact IsPullback.isoIsPullback_hom_snd _ _ _ _)

/-- **Chart base change commutes with Zariski opens.**  For a representable morphism
`f : X ⟶ Y` of algebraic spaces, an étale scheme chart `V` of `Y` and a Zariski open `O` of
`chartScheme V`, the base change of the open chart `openChart V O` is the open chart of
`V ×_Y X` cut out by the preimage of `O` along the cartesian projection. -/
def smallBaseChangeOpenChartIso :
    (smallBaseChange B S hS f hf).obj (openChart B S hS Y.1 V O) ≅
      openChart B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O) :=
  (IsEtaleChart B S hS X.1).isoMk (CostructuredArrow.isoMk
    (openChartBaseChangeIso B S hS f hf V O)
    (openChartBaseChangeIso_hom_comp_hom B S hS f hf V O))

/-- `AlgebraicGeometry.Space.openChartBaseChangeIso` with its source spelled as the base change
of the open chart rather than as the fibre product of the representability witness; the two
spellings are definitionally but not syntactically equal. -/
def smallBaseChangeOpenChartLeftIso :
    ((smallBaseChange B S hS f hf).obj (openChart B S hS Y.1 V O)).obj.left ≅
      (openChart B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O)).obj.left :=
  openChartBaseChangeIso B S hS f hf V O

/-- `AlgebraicGeometry.Space.openChartBaseChangeIso_hom_comp_projection` in the spelling of
`AlgebraicGeometry.Space.smallBaseChangeOpenChartLeftIso`: the interchange composed with the
cartesian projection of the smaller chart is the cartesian projection of Stacks 03G2, part (4),
at the open chart. -/
theorem smallBaseChangeOpenChartLeftIso_hom_comp_projection :
    (smallBaseChangeOpenChartLeftIso B S hS f hf V O).hom ≫
        openChartSmallBaseChangeProjection B S hS f hf V O =
      (smallBaseChangeProjection B S hS f hf).app (openChart B S hS Y.1 V O) :=
  openChartBaseChangeIso_hom_comp_projection B S hS f hf V O

/-! ### Naturality in the open -/

section Naturality

variable {O₁ O₂ : (chartScheme V).Opens}

/-- Pulling a Zariski open back along the cartesian projection is monotone. -/
theorem smallBaseChangeSchemeProjection_preimage_mono (hO : O₁ ≤ O₂) :
    smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O₁ ≤
      smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O₂ :=
  fun _ hx ↦ hO hx

/-- The inclusion of the open charts of `V ×_Y X` cut out by the preimages of two nested
Zariski opens of `chartScheme V`, as a morphism of the big fppf category over `S`. -/
def openChartSmallBaseChangeHomOfLE (hO : O₁ ≤ O₂) :
    (SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1
        ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O₁)) ⟶
      (SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1
        ((smallBaseChange B S hS f hf).obj V)
        (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O₂)) :=
  openSubHomOfLE _ (smallBaseChangeSchemeProjection_preimage_mono B S hS f hf V hO)

/-- **The cartesian projections of the smaller charts are natural in the open.**  Restricting
the projection `V ×_Y X ⟶ V` to a smaller open and then including is the same as including and
then restricting to the larger one. -/
theorem openChartSmallBaseChangeHomOfLE_comp_projection (hO : O₁ ≤ O₂) :
    openChartSmallBaseChangeHomOfLE B S hS f hf V hO ≫
        openChartSmallBaseChangeProjection B S hS f hf V O₂ =
      openChartSmallBaseChangeProjection B S hS f hf V O₁ ≫
        (openChartHomOfLE B S hS Y.1 V hO).hom.left := by
  refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
  show (chartScheme ((smallBaseChange B S hS f hf).obj V)).homOfLE
        (smallBaseChangeSchemeProjection_preimage_mono B S hS f hf V hO) ≫
      (smallBaseChangeSchemeProjection B S hS f hf V ∣_ O₂) =
    (smallBaseChangeSchemeProjection B S hS f hf V ∣_ O₁) ≫ (chartScheme V).homOfLE hO
  rw [← cancel_mono O₂.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
    Scheme.homOfLE_ι, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- **The isomorphism `AlgebraicGeometry.Space.smallBaseChangeOpenChartIso` is natural in the
Zariski open.** -/
theorem smallBaseChangeOpenChartIso_naturality (hO : O₁ ≤ O₂) :
    (smallBaseChange B S hS f hf).map (openChartHomOfLE B S hS Y.1 V hO) ≫
        (smallBaseChangeOpenChartIso B S hS f hf V O₂).hom =
      (smallBaseChangeOpenChartIso B S hS f hf V O₁).hom ≫
        openChartHomOfLE B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
          (smallBaseChangeSchemeProjection_preimage_mono B S hS f hf V hO) := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (yoneda.map_injective ?_))
  refine (isPullback_openChart_smallBaseChange B S hS f hf V O₂).hom_ext ?_ ?_
  · exact (CostructuredArrow.w (((smallBaseChange B S hS f hf).map
        (openChartHomOfLE B S hS Y.1 V hO) ≫
        (smallBaseChangeOpenChartIso B S hS f hf V O₂).hom).hom)).trans
      (CostructuredArrow.w (((smallBaseChangeOpenChartIso B S hS f hf V O₁).hom ≫
        openChartHomOfLE B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
          (smallBaseChangeSchemeProjection_preimage_mono B S hS f hf V hO)).hom)).symm
  · refine (yoneda.map_comp _ _).symm.trans
      ((congrArg yoneda.map ?_).trans (yoneda.map_comp _ _))
    show (smallBaseChange B S hS f hf ⋙ SmallEtale.toOver B S hS X.1).map
          (openChartHomOfLE B S hS Y.1 V hO) ≫
        (smallBaseChangeOpenChartLeftIso B S hS f hf V O₂).hom ≫
          openChartSmallBaseChangeProjection B S hS f hf V O₂ =
      (smallBaseChangeOpenChartLeftIso B S hS f hf V O₁).hom ≫
        openChartSmallBaseChangeHomOfLE B S hS f hf V hO ≫
          openChartSmallBaseChangeProjection B S hS f hf V O₂
    rw [smallBaseChangeOpenChartLeftIso_hom_comp_projection,
      openChartSmallBaseChangeHomOfLE_comp_projection, ← Category.assoc,
      smallBaseChangeOpenChartLeftIso_hom_comp_projection]
    exact (smallBaseChangeProjection B S hS f hf).naturality
      (openChartHomOfLE B S hS Y.1 V hO)

/-- **Chart base change commutes with Zariski opens, as a natural isomorphism of functors of the
open.**  Cutting a Zariski open out of `V` and then base changing along `f` is, naturally in the
open, cutting its preimage out of `V ×_Y X`. -/
def smallBaseChangeOpenChartFunctorIso :
    openChartFunctor B S hS Y.1 V ⋙ smallBaseChange B S hS f hf ≅
      Opens.map (smallBaseChangeSchemeProjection B S hS f hf V).base ⋙
        openChartFunctor B S hS X.1 ((smallBaseChange B S hS f hf).obj V) :=
  NatIso.ofComponents (fun O ↦ smallBaseChangeOpenChartIso B S hS f hf V O)
    (fun i ↦ smallBaseChangeOpenChartIso_naturality B S hS f hf V i.le)

end Naturality

/-- The underlying morphism of the big fppf category over `S` of
`AlgebraicGeometry.Space.smallBaseChangeOpenChartIso` is
`AlgebraicGeometry.Space.openChartBaseChangeIso`. -/
theorem smallBaseChangeOpenChartIso_hom_hom_left :
    (smallBaseChangeOpenChartIso B S hS f hf V O).hom.hom.left =
      (openChartBaseChangeIso B S hS f hf V O).hom :=
  rfl

/-- **The ring isomorphism induced on regular functions.**  The regular functions on the base
change of the open chart `openChart V O` are the regular functions on the Zariski open of
`V ×_Y X` that `O` pulls back to. -/
def structureSheafSmallBaseChangeOpenChartIso :
    (structureSheaf B S hS X.1 X.2).obj.obj
        (op ((smallBaseChange B S hS f hf).obj (openChart B S hS Y.1 V O))) ≅
      (structureSheaf B S hS X.1 X.2).obj.obj
        (op (openChart B S hS X.1 ((smallBaseChange B S hS f hf).obj V)
          (smallBaseChangeSchemeProjection B S hS f hf V ⁻¹ᵁ O))) :=
  (structureSheaf B S hS X.1 X.2).obj.mapIso
    (smallBaseChangeOpenChartIso B S hS f hf V O).symm.op

end AlgebraicGeometry.Space

end

module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePushforwardFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Base change of étale charts along an open immersion is a dense subsite

Let `j : U ⟶ X` be an open immersion of algebraic spaces over a scheme `S`. Base change along
`j` carries an étale scheme chart `V` of `X` to the étale scheme chart `V ×_X U` of `U`
(`AlgebraicGeometry.Space.smallBaseChange`). This file shows that the resulting functor between
the small étale sites is *cover dense* and *locally full*, which by
`AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforward` makes the direct image of sheaves
along `j` fully faithful. An étale chart `W` of `U` composed with `j` is an étale chart of `X`
whose base change along `j` is isomorphic to `W`.

## Main definitions

* `AlgebraicGeometry.Space.openImmersionChart` and
  `AlgebraicGeometry.Space.openImmersionChartMap`: an étale chart of `U`, and a morphism of
  such, read as an étale chart of `X` and a morphism of such by composing with `j`.
* `AlgebraicGeometry.Space.baseChangeOpenImmersionChartIso`: the resulting isomorphism
  `(W ⟶ U ⟶ X) ×_X U ≅ W` of étale charts of `U`.

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isOpenImmersion` and
  `AlgebraicGeometry.Space.smallBaseChange_isLocallyFull_of_isOpenImmersion`: chart base change
  along an open immersion is cover dense and locally full for the small étale topology of `U`.
* `AlgebraicGeometry.Space.fullyFaithfulSmallEtaleRestrictionOfIsOpenImmersion` and
  `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsOpenImmersion`: restriction
  along chart base change is fully faithful on sheaves with values in any category, and the
  direct image of sheaves of sets along the morphism of small étale topoi of Stacks 03G2,
  part (3) is fully faithful.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04FV](https://stacks.math.columbia.edu/tag/04FV)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X : AlgebraicSpaces B S hS} (j : U ⟶ X) (hj : IsOpenImmersion B S hS j.hom)

/-! ### Charts of an open subspace as charts of the ambient space -/

/-- An étale scheme chart `W` of `U`, read as an étale scheme chart of `X` by composing its
structure morphism with the open immersion `j : U ⟶ X`. The underlying object of the big fppf
site of `S` is unchanged; the chart is étale because an open immersion is. -/
abbrev openImmersionChart (W : SmallEtale B S hS U.1) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk (W.1.hom ≫ j.hom),
    isEtale_of_isOpenImmersion B S hS hj W.1.left W.1.hom W.2⟩

/-- A morphism of étale charts of `U`, read as a morphism of the étale charts of `X` they
present. The underlying morphism of the big fppf site of `S` is unchanged. -/
def openImmersionChartMap {W W' : SmallEtale B S hS U.1} (k : W ⟶ W') :
    openImmersionChart B S hS j hj W ⟶ openImmersionChart B S hS j hj W' :=
  ObjectProperty.homMk (CostructuredArrow.homMk k.hom.left (by
    change yoneda.map k.hom.left ≫ W'.1.hom ≫ j.hom = W.1.hom ≫ j.hom
    rw [← Category.assoc, CostructuredArrow.w k.hom]))

/-- Base changing along `j` the chart of `X` presented by a chart `W` of `U` returns the
structure morphism of `W`. -/
theorem fst_openImmersionChart_eq (W : SmallEtale B S hS U.1) :
    hj.rep.fst (openImmersionChart B S hS j hj W).1.hom =
      yoneda.map (hj.rep.snd (openImmersionChart B S hS j hj W).1.hom) ≫ W.1.hom := by
  have hmono : Mono j.hom := mono_of_presheaf_isOpenImmersion hj
  refine (cancel_mono j.hom).mp ?_
  rw [hj.rep.w]
  rfl

/-- The projection of the base change along `j` of the chart of `X` presented by a chart `W` of
`U` onto `W` itself. -/
def openImmersionChartProjection (W : SmallEtale B S hS U.1) :
    (smallBaseChange B S hS j hj.rep).obj (openImmersionChart B S hS j hj W) ⟶ W :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hj.rep.snd (openImmersionChart B S hS j hj W).1.hom)
    (fst_openImmersionChart_eq B S hS j hj W).symm)

/-- The diagonal section of `AlgebraicGeometry.Space.openImmersionChartProjection`, given by
the universal property of the base change applied to the identity of `W`. -/
def openImmersionChartSection (W : SmallEtale B S hS U.1) :
    W ⟶ (smallBaseChange B S hS j hj.rep).obj (openImmersionChart B S hS j hj W) :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (hj.rep.lift W.1.hom (𝟙 W.1.left) (by simp)) (hj.rep.lift_fst _ _ _))

/-- For an open immersion `j : U ⟶ X`, base changing along `j` the chart of `X` presented by an
étale chart `W` of `U` gives back `W`: the projection
`AlgebraicGeometry.Space.openImmersionChartProjection` is an isomorphism of charts of `U`. -/
def baseChangeOpenImmersionChartIso (W : SmallEtale B S hS U.1) :
    (smallBaseChange B S hS j hj.rep).obj (openImmersionChart B S hS j hj W) ≅ W where
  hom := openImmersionChartProjection B S hS j hj W
  inv := openImmersionChartSection B S hS j hj W
  hom_inv_id := by
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hj.rep.hom_ext ?_ ?_))
    · exact (CostructuredArrow.w _).trans (CostructuredArrow.w _).symm
    · change (hj.rep.snd _ ≫ hj.rep.lift _ _ _) ≫ _ = _
      rw [Category.assoc, hj.rep.lift_snd]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  inv_hom_id :=
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hj.rep.lift_snd _ _ _))

/-- The isomorphism of `AlgebraicGeometry.Space.baseChangeOpenImmersionChartIso` is natural in
the chart of `U`. -/
theorem openImmersionChartProjection_naturality {W W' : SmallEtale B S hS U.1} (k : W ⟶ W') :
    (smallBaseChange B S hS j hj.rep).map (openImmersionChartMap B S hS j hj k) ≫
        openImmersionChartProjection B S hS j hj W' =
      openImmersionChartProjection B S hS j hj W ≫ k :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (smallBaseChange_map_snd B S hS j hj.rep (openImmersionChartMap B S hS j hj k)))

/-! ### Cover density -/

/-- **Cover density of chart base change along an open immersion.** For an open immersion
`j : U ⟶ X` of algebraic spaces over `S`, every étale scheme chart of `U` is, up to
isomorphism, the base change along `j` of an étale scheme chart of `X` — namely of itself, read
as a chart of `X` — so the base-change functor of Stacks 03G2, part (4) is cover dense for the
small étale topology of `U`. -/
theorem smallBaseChange_isCoverDense_of_isOpenImmersion :
    (smallBaseChange B S hS j hj.rep).IsCoverDense (SmallEtale.topology B S hS U.1) := by
  refine ⟨fun W ↦ (SmallEtale.topology B S hS U.1).covering_of_eq_top
    (Sieve.id_mem_iff_eq_top.1 ⟨⟨openImmersionChart B S hS j hj W,
      (baseChangeOpenImmersionChartIso B S hS j hj W).inv,
      (baseChangeOpenImmersionChartIso B S hS j hj W).hom,
      (baseChangeOpenImmersionChartIso B S hS j hj W).inv_hom_id⟩⟩)⟩

/-! ### Local fullness -/

/-- The morphism of étale charts of `X` from the chart presented by `V ×_X U` to `V` itself,
given by the cartesian projection. -/
def openImmersionChartToChart (V : SmallEtale B S hS X.1) :
    openImmersionChart B S hS j hj ((smallBaseChange B S hS j hj.rep).obj V) ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (hj.rep.snd V.1.hom) (hj.rep.w V.1.hom).symm)

/-- The base change along `j` of `AlgebraicGeometry.Space.openImmersionChartToChart` is the
projection of `AlgebraicGeometry.Space.openImmersionChartProjection`, hence an isomorphism. -/
theorem smallBaseChange_map_openImmersionChartToChart (V : SmallEtale B S hS X.1) :
    (smallBaseChange B S hS j hj.rep).map (openImmersionChartToChart B S hS j hj V) =
      openImmersionChartProjection B S hS j hj
        ((smallBaseChange B S hS j hj.rep).obj V) := by
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hj.rep.hom_ext ?_ ?_))
  · exact (CostructuredArrow.w _).trans (CostructuredArrow.w _).symm
  · exact smallBaseChange_map_snd B S hS j hj.rep (openImmersionChartToChart B S hS j hj V)

/-- **The open-immersion analogue of Stacks 04FV.** Let `j : U ⟶ X` be an open immersion of
algebraic spaces over `S`, let `V` and `V'` be étale scheme charts of `X` and let `φ` be a
morphism over `U` between their base changes along `j`. Then there is an étale chart `W` of `X`
and a morphism of charts `a : W ⟶ V` whose base change along `j` is an isomorphism and which
lies in the image sieve of `φ`. -/
theorem exists_isIso_smallBaseChange_map_of_isOpenImmersion (V V' : SmallEtale B S hS X.1)
    (φ : (smallBaseChange B S hS j hj.rep).obj V ⟶
      (smallBaseChange B S hS j hj.rep).obj V') :
    ∃ (W : SmallEtale B S hS X.1) (a : W ⟶ V),
      IsIso ((smallBaseChange B S hS j hj.rep).map a) ∧
        ((smallBaseChange B S hS j hj.rep).imageSieve φ).arrows a := by
  refine ⟨openImmersionChart B S hS j hj ((smallBaseChange B S hS j hj.rep).obj V),
    openImmersionChartToChart B S hS j hj V, ?_,
    openImmersionChartMap B S hS j hj φ ≫ openImmersionChartToChart B S hS j hj V', ?_⟩
  · rw [smallBaseChange_map_openImmersionChartToChart]
    exact (baseChangeOpenImmersionChartIso B S hS j hj
      ((smallBaseChange B S hS j hj.rep).obj V)).isIso_hom
  · rw [Functor.map_comp, smallBaseChange_map_openImmersionChartToChart,
      openImmersionChartProjection_naturality,
      smallBaseChange_map_openImmersionChartToChart]

/-- **Local fullness of chart base change along an open immersion.** For an open immersion
`j : U ⟶ X` of algebraic spaces over `S`, a morphism over `U` between the base changes of two
étale scheme charts of `X` is, locally on the source, the base change of a morphism of charts
of `X`. -/
theorem smallBaseChange_isLocallyFull_of_isOpenImmersion :
    (smallBaseChange B S hS j hj.rep).IsLocallyFull (SmallEtale.topology B S hS U.1) := by
  refine ⟨fun {V V'} φ ↦ ?_⟩
  obtain ⟨W, a, hiso, ha⟩ :=
    exists_isIso_smallBaseChange_map_of_isOpenImmersion B S hS j hj V V' φ
  refine (SmallEtale.topology B S hS U.1).covering_of_eq_top (Sieve.id_mem_iff_eq_top.1 ?_)
  simpa only [IsIso.inv_hom_id] using
    (((smallBaseChange B S hS j hj.rep).imageSieve φ).functorPushforward
      (smallBaseChange B S hS j hj.rep)).downward_closed
        (Sieve.image_mem_functorPushforward (smallBaseChange B S hS j hj.rep)
          ((smallBaseChange B S hS j hj.rep).imageSieve φ) ha)
        (inv ((smallBaseChange B S hS j hj.rep).map a))

/-! ### Full faithfulness of the direct image -/

/-- **Full faithfulness of restriction along chart base change for an open immersion**, with
coefficients in an arbitrary category: for an open immersion `j : U ⟶ X` of algebraic spaces
over `S`, restriction along the base-change functor on étale scheme charts is fully faithful on
`A`-valued sheaves. -/
def fullyFaithfulSmallEtaleRestrictionOfIsOpenImmersion (A : Type w) [Category.{v} A] :
    letI := (smallBaseChange_isMorphismOfSites B S hS j hj.rep).toIsContinuous
    ((smallBaseChange B S hS j hj.rep).sheafPushforwardContinuous A
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS U.1)).FullyFaithful :=
  fullyFaithfulSmallEtaleRestriction B S hS A j hj.rep
    (smallBaseChange_isCoverDense_of_isOpenImmersion B S hS j hj)
    (smallBaseChange_isLocallyFull_of_isOpenImmersion B S hS j hj)

/-- **The direct image of sheaves of sets along an open immersion of algebraic spaces is fully
faithful.** This is the open-immersion analogue of part (1) of Stacks 04E5: the direct image of
the morphism of small étale topoi of Stacks 03G2, part (3) is fully faithful. -/
def fullyFaithfulSmallEtalePushforwardOfIsOpenImmersion :
    (smallToposMorphismTypeU B S hS j).pushforward.FullyFaithful :=
  fullyFaithfulSmallEtalePushforward B S hS j hj.rep
    (smallBaseChange_isCoverDense_of_isOpenImmersion B S hS j hj)
    (smallBaseChange_isLocallyFull_of_isOpenImmersion B S hS j hj)

end AlgebraicGeometry.Space

end

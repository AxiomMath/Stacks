module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartBiconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothLiftTorsor
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# The sheaf of lifts of an infinitesimal lifting problem has sections étale-locally

Let `f : F ⟶ G` be a morphism of algebraic spaces over a scheme `S`, let `i : T ⟶ T'` be a
square-zero closed immersion of affine objects of the big fppf site, and let `x` be a section of
`F` over `T` and `y` a section of `G` over `T'` agreeing under `f`.  The lifts of that
infinitesimal lifting problem over the étale charts of `T'` form the sheaf
`AlgebraicGeometry.Space.liftsSubfunctor` of [Stacks Project, Tag 061D].

This file proves that **if `f` is étale-locally formally smooth then that sheaf has a section on
a covering sieve of every chart** — the local non-emptiness which, in the Stacks proof of step
(II) of [Stacks Project, Tag 04AM], makes the pseudo-torsor of lifts a torsor.  It is
unconditional: the input is `AlgebraicGeometry.Space.FormallySmoothEtaleLocally`, which step (I)
of that proof supplies and which is already proved for a smooth morphism as
`AlgebraicGeometry.Space.formallySmoothEtaleLocally_of_isSmooth`.

## Main definitions

* `AlgebraicGeometry.Space.liftingProblemChart` is the étale chart of `T'` named by an étale
  morphism of the site, and `AlgebraicGeometry.Space.liftingProblemTopChart` is the chart `T'`
  itself.
* `AlgebraicGeometry.Space.liftingProblemLifts` is the sheaf of lifts of the lifting problem, the
  rule of [Stacks Project, Tag 061D] at the data this file is about.
* `AlgebraicGeometry.Space.liftingProblemLiftSieve` is the sieve of charts over which the lifting
  problem is solvable.

## Main results

* `AlgebraicGeometry.Space.isChartLift_of_formallySmoothEtaleLocally`: the solution that
  étale-local formal smoothness produces over an affine étale neighbourhood of a point **is a
  section of the sheaf of lifts** over the chart that neighbourhood names.
* `AlgebraicGeometry.Space.liftingProblemLiftSieve_mem_topology_topChart`: the sieve of solvable
  charts covers `T'`.  This is where the surjectivity of a square-zero closed immersion on points
  is used, to see that the neighbourhoods produced over the points of `T` exhaust `T'`.
* `AlgebraicGeometry.Space.mem_liftingProblemLifts_topChart_iff`: **a section of the sheaf of
  lifts over the chart `T'` itself is a solution of the lifting problem**, and conversely.  This
  is what turns a global section of the sheaf into the lift
  `AlgebraicGeometry.Space.FormallySmooth` asks for.
* `AlgebraicGeometry.Space.exists_covering_nonempty_liftingProblemLifts`: **the sheaf of lifts has
  a section on a covering sieve of every chart.**  This is the shape
  `CategoryTheory.PseudoTorsor.IsTorsor` consumes.

## Implementation notes

**Why the chart `T'` suffices and no fibre product is formed.**  The sieve of solvable charts is
defined so that its membership does not depend on the arrow, only on its source: a chart either
carries a solution or it does not, and `AlgebraicGeometry.Space.IsChartLift.restrict` makes that
property closed under refinement, which is the downward closure a sieve needs.  So the sieve on an
arbitrary chart `A` is the pullback along `A ⟶ T'` of the sieve on `T'`, and covering descends by
`CategoryTheory.GrothendieckTopology.pullback_stable`.  The alternative — producing neighbourhoods
of the points of `A` directly — would require the fibre product `A ×_{T'} U'` and a surjectivity
statement for it.

The chart `T'` itself is the terminal object of the small étale site of the algebraic space `T'`
represents, by `CategoryTheory.CostructuredArrow.mkIdTerminal`, so the arrow `A ⟶ T'` exists and
is unique; only its existence is used.

**Where each clause of the lifting condition comes from.**  The two clauses of
`AlgebraicGeometry.Space.IsChartLift` are matched one by one by the two final clauses of
`AlgebraicGeometry.Space.FormallySmoothEtaleLocally`: lying over `G` with structure section `y` is
`f(z) = y|_{U'}`, and agreeing with `x` on the part of the chart lying in the thickening is the
agreement of `x` and `z` on every common refinement.  The second needs the identification of the
subspace presenting `T` inside `T'` with the representable presheaf of `T`, which is
`AlgebraicGeometry.Space.squareZeroRangeIso`, together with the fullness and faithfulness of the
Yoneda embedding to pass between a morphism out of that subspace and a morphism of the site.

**What this does not do.**  It does not make the lifts a torsor in the sense of
`CategoryTheory.PseudoTorsor`: that additionally needs the action of the acting sheaf of
[Stacks Project, Tag 061D] on the lifts, compatibly with restriction, which
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/UndeformedLiftDerivationAction.lean` supplies
over one ambient space only; its implementation notes record what the sheaf-level version needs.
Nor does it trivialise anything: that is [Stacks Project, Tag 03AJ] with the vanishing of
[Stacks Project, Tag 061J].

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 04CY](https://stacks.math.columbia.edu/tag/04CY)
* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 061K](https://stacks.math.columbia.edu/tag/061K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T T' : BigFppfOver B S hS}

/-! ### Charts of the ambient space of the thickening -/

/-- **The Yoneda image of an étale morphism of the site is an étale chart.**  Étaleness of a
morphism of schemes becomes the relatively representable property by
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`, and
`CategoryTheory.MorphismProperty.relative_map` carries it to the Yoneda image, the inverse image
property being stable under base change. -/
theorem isEtaleChart_mk_yoneda_map {U : BigFppfOver B S hS} (j : U ⟶ T')
    (hj : Etale ((BigFppfOver.toScheme B S hS).map j)) :
    IsEtaleChart B S hS (liftingProblemAmbient B S hS T').1
      (CostructuredArrow.mk (yoneda.map j)) := by
  have := inverseImage_isStableUnderBaseChange B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  exact MorphismProperty.relative_map
    (show MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) j from hj)

/-- The identity of a representable presheaf is an étale chart. -/
theorem isEtaleChart_mk_id (T' : BigFppfOver B S hS) :
    IsEtaleChart B S hS (liftingProblemAmbient B S hS T').1
      (CostructuredArrow.mk (𝟙 (yoneda.obj T'))) :=
  (isEtale_iff_presheaf_of_yoneda B S hS (𝟙 (yoneda.obj T'))).1
    (isEtale_of_isIso B S hS (𝟙 (yoneda.obj T')))

/-- The étale chart of the algebraic space `T'` represents named by an étale morphism of the
site. -/
abbrev liftingProblemChart {U : BigFppfOver B S hS} (j : U ⟶ T')
    (hj : Etale ((BigFppfOver.toScheme B S hS).map j)) :
    SmallEtale B S hS (liftingProblemAmbient B S hS T').1 :=
  ⟨CostructuredArrow.mk (yoneda.map j), isEtaleChart_mk_yoneda_map B S hS j hj⟩

/-- The chart `T'` itself, the terminal object of the small étale site of the algebraic space
`T'` represents. -/
abbrev liftingProblemTopChart (T' : BigFppfOver B S hS) :
    SmallEtale B S hS (liftingProblemAmbient B S hS T').1 :=
  ⟨CostructuredArrow.mk (𝟙 (yoneda.obj T')), isEtaleChart_mk_id B S hS T'⟩

/-- The arrow from an étale chart named by a morphism of the site to the chart `T'` itself. -/
abbrev liftingProblemChartHom {U : BigFppfOver B S hS} (j : U ⟶ T')
    (hj : Etale ((BigFppfOver.toScheme B S hS).map j)) :
    liftingProblemChart B S hS j hj ⟶ liftingProblemTopChart B S hS T' :=
  ObjectProperty.homMk (CostructuredArrow.homMk j (Category.comp_id _))

/-- Every étale chart of the algebraic space `T'` represents has an arrow to the chart `T'`
itself, that object being terminal in the small étale site. -/
abbrev liftingProblemToTopChart (A : SmallEtale B S hS (liftingProblemAmbient B S hS T').1) :
    A ⟶ liftingProblemTopChart B S hS T' :=
  ObjectProperty.homMk (CostructuredArrow.mkIdTerminal.from A.1)

/-! ### The sheaf of lifts of the lifting problem -/

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)

/-- **The sheaf of lifts of an infinitesimal lifting problem**, the rule of
[Stacks Project, Tag 061D]: the charts of `T'` carrying a section of `F` which lies over `y` and
restricts to `x` on the part of the chart lying in `T`. -/
abbrev liftingProblemLifts (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T')) :=
  liftsSubfunctor B S hS (liftingProblemBase B S hS hG y) (liftingProblemMap B S hS hF hG f)
    (X := (liftingProblemThickening B S hS i hi).1)
    (liftingProblemRestriction B S hS hF i hi x).hom

/-- The inclusion of the thickening, read through
`AlgebraicGeometry.Space.squareZeroRangeIso` as the Yoneda image of `i`. -/
theorem liftingProblemThickening_ι_eq (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    (liftingProblemThickening B S hS i hi).1.ι =
      (squareZeroRangeIso B S hS i hi).inv ≫ yoneda.map i := by
  rw [← squareZeroRangeIso_hom_ι B S hS i hi, Iso.inv_hom_id_assoc]

/-- A map out of the representable `W` into the thickening comes from a map `p : W ⟶ T`, and
composing with the inverse of `squareZeroRangeIso` turns a section of `F` over `T` into its
restriction along `p`. -/
private theorem exists_comp_eq_thickening_ι (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) {W : BigFppfOver B S hS}
    (t : yoneda.obj W ⟶ (liftingProblemThickening B S hS i hi).1.toFunctor) :
    ∃ p : W ⟶ T, t ≫ (liftingProblemThickening B S hS i hi).1.ι = yoneda.map (p ≫ i) ∧
      ∀ x : F.obj (op T), t ≫ (squareZeroRangeIso B S hS i hi).inv ≫ yonedaEquiv.symm x =
        yonedaEquiv.symm (F.map p.op x) := by
  obtain ⟨p, hp⟩ :=
    (yoneda : BigFppfOver B S hS ⥤ _).map_surjective (t ≫ (squareZeroRangeIso B S hS i hi).inv)
  refine ⟨p, ?_, fun x => ?_⟩
  · rw [Functor.map_comp, hp, Category.assoc, liftingProblemThickening_ι_eq]
  · rw [← Category.assoc, ← hp, yonedaEquiv_symm_naturality_left]

/-- **The solution that étale-local formal smoothness produces is a section of the sheaf of
lifts.**  Over the chart named by an affine étale `j : U' ⟶ T'`, a section `z` of `F` lying over
`y` and agreeing with `x` on every common refinement satisfies both clauses of
`AlgebraicGeometry.Space.IsChartLift`. -/
theorem isChartLift_of_formallySmoothEtaleLocally (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    {U : BigFppfOver B S hS} (j : U ⟶ T')
    (hj : Etale ((BigFppfOver.toScheme B S hS).map j)) (z : F.obj (op U))
    (hz : f.app (op U) z = G.map j.op y)
    (hzx : ∀ (W : BigFppfOver B S hS) (p : W ⟶ T) (q : W ⟶ U),
      p ≫ i = q ≫ j → F.map p.op x = F.map q.op z) :
    IsChartLift B S hS (liftingProblemBase B S hS hG y) (liftingProblemMap B S hS hF hG f)
      (X := (liftingProblemThickening B S hS i hi).1)
      (liftingProblemRestriction B S hS hF i hi x).hom
      (liftingProblemChart B S hS j hj) (yonedaEquiv.symm z) := by
  refine ⟨?_, fun W k t hkt => ?_⟩
  · show yonedaEquiv.symm z ≫ f = yoneda.map j ≫ yonedaEquiv.symm y
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left, hz]
  · obtain ⟨p, hp, hpx⟩ := exists_comp_eq_thickening_ι (F := F) B S hS i hi t
    have hkj : k ≫ j = p ≫ i := by
      refine (yoneda : BigFppfOver B S hS ⥤ _).map_injective ?_
      rw [Functor.map_comp]
      exact hkt.trans hp
    show yoneda.map k ≫ yonedaEquiv.symm z =
      t ≫ (squareZeroRangeIso B S hS i hi).inv ≫ yonedaEquiv.symm x
    rw [hpx, yonedaEquiv_symm_naturality_left, hzx W p k hkj.symm]

/-- **A section of the sheaf of lifts over the chart `T'` itself is a solution of the
infinitesimal lifting problem**, and conversely.  This is the statement that converts a global
section of the sheaf of lifts — what the triviality of the torsor of
[Stacks Project, Tag 03AJ] produces — into the lift that
`AlgebraicGeometry.Space.FormallySmooth` asks for.

The clause over the target is the same equation read through the Yoneda correspondence; the
clause along the thickening is read at the one refinement `(T, i, 𝟙)` in the forward direction,
and in the other direction at an arbitrary refinement, factored through
`AlgebraicGeometry.Space.squareZeroRangeIso`. -/
theorem mem_liftingProblemLifts_topChart_iff (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (z : F.obj (op T')) :
    z ∈ (liftingProblemLifts B S hS hF hG f i hi x y).obj
        (op (liftingProblemTopChart B S hS T')) ↔
      IsLift f i x y z := by
  constructor
  · intro h
    refine ⟨yonedaEquiv.symm.injective ?_, yonedaEquiv.symm.injective ?_⟩
    · have hkey := h.2 T i (squareZeroRangeIso B S hS i hi).hom (by
        show yoneda.map i ≫ 𝟙 (yoneda.obj T') =
          (squareZeroRangeIso B S hS i hi).hom ≫ (liftingProblemThickening B S hS i hi).1.ι
        rw [Category.comp_id, squareZeroRangeIso_hom_ι B S hS i hi])
      rw [← yonedaEquiv_symm_naturality_left]
      refine hkey.trans ?_
      show (squareZeroRangeIso B S hS i hi).hom ≫
        (squareZeroRangeIso B S hS i hi).inv ≫ yonedaEquiv.symm x = _
      rw [Iso.hom_inv_id_assoc]
    · have h1 : yonedaEquiv.symm z ≫ f = 𝟙 (yoneda.obj T') ≫ yonedaEquiv.symm y := h.1
      rw [← yonedaEquiv_symm_naturality_right, h1, Category.id_comp]
  · intro h
    refine ⟨?_, fun W k t hkt => ?_⟩
    · show yonedaEquiv.symm z ≫ f = 𝟙 (yoneda.obj T') ≫ yonedaEquiv.symm y
      rw [Category.id_comp, yonedaEquiv_symm_naturality_right, h.2]
    · obtain ⟨p, hp, hpx⟩ := exists_comp_eq_thickening_ι (F := F) B S hS i hi t
      have hk : k = p ≫ i := by
        refine (yoneda : BigFppfOver B S hS ⥤ _).map_injective ?_
        exact (Category.comp_id _).symm.trans (hkt.trans hp)
      show yoneda.map k ≫ yonedaEquiv.symm z =
        t ≫ (squareZeroRangeIso B S hS i hi).inv ≫ yonedaEquiv.symm x
      rw [hpx, yonedaEquiv_symm_naturality_left, ← h.1, hk, op_comp,
        Functor.map_comp_apply]

/-! ### The covering sieve of solvable charts -/

/-- The sieve of charts of `T'` over which the infinitesimal lifting problem has a solution.
Membership does not depend on the arrow, only on its source; the downward closure is
`AlgebraicGeometry.Space.IsChartLift.restrict`. -/
def liftingProblemLiftSieve (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T)) (y : G.obj (op T'))
    (A : SmallEtale B S hS (liftingProblemAmbient B S hS T').1) : Sieve A where
  arrows V _ := Nonempty ((liftingProblemLifts B S hS hF hG f i hi x y).toFunctor.obj (op V))
  downward_closed := by
    rintro V W g ⟨α, hα⟩ h
    exact ⟨(liftingProblemLifts B S hS hF hG f i hi x y).toFunctor.map (op h) ⟨α, hα⟩⟩

/-- **The charts over which the lifting problem is solvable cover `T'`.**  Every point of `T'` is
the image of a point of `T`, the closed immersion `i` being surjective — a square-zero closed
immersion is a thickening — and over every point of `T` étale-local formal smoothness produces an
affine étale neighbourhood carrying a solution, by
`AlgebraicGeometry.Space.isChartLift_of_formallySmoothEtaleLocally`.  The covering criterion is
`AlgebraicGeometry.Space.SmallEtale.mem_topology_iff_exists_mem_range`: a sieve of the small étale
site is covering exactly when its arrows are jointly surjective on points. -/
theorem liftingProblemLiftSieve_mem_topology_topChart
    (hfse : FormallySmoothEtaleLocally B S hS f)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T))
    (y : G.obj (op T')) (hxy : f.app (op T) x = G.map i.op y) :
    liftingProblemLiftSieve B S hS hF hG f i hi x y (liftingProblemTopChart B S hS T') ∈
      SmallEtale.topology B S hS (liftingProblemAmbient B S hS T').1
        (liftingProblemTopChart B S hS T') := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro w
  obtain ⟨t, ht⟩ :=
    (isFirstOrderThickening_of_isSquareZeroClosedImmersion hi).isThickening.2 w
  obtain ⟨U, j, z, -, hjEt, ⟨v, hv⟩, hz, hzx⟩ := hfse T T' hT hT' i hi x y hxy t
  exact ⟨liftingProblemChart B S hS j hjEt, liftingProblemChartHom B S hS j hjEt,
    ⟨⟨z, isChartLift_of_formallySmoothEtaleLocally B S hS hF hG f i hi x y j hjEt z hz hzx⟩⟩,
    v, hv.trans ht⟩

/-- **The sheaf of lifts of an infinitesimal lifting problem has a section on a covering sieve of
every chart**, for an étale-locally formally smooth morphism.  This is the local non-emptiness
that `CategoryTheory.PseudoTorsor.IsTorsor` asks for.

The sieve of solvable charts covers the chart `T'` by
`AlgebraicGeometry.Space.liftingProblemLiftSieve_mem_topology_topChart`, and the sieve on an
arbitrary chart `A` contains the pullback of that one along the arrow `A ⟶ T'`, which is covering
by stability of the topology under pullback. -/
theorem exists_covering_nonempty_liftingProblemLifts
    (hfse : FormallySmoothEtaleLocally B S hS f)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i) (x : F.obj (op T))
    (y : G.obj (op T')) (hxy : f.app (op T) x = G.map i.op y)
    (A : SmallEtale B S hS (liftingProblemAmbient B S hS T').1) :
    ∃ R ∈ SmallEtale.topology B S hS (liftingProblemAmbient B S hS T').1 A,
      ∀ ⦃V : SmallEtale B S hS (liftingProblemAmbient B S hS T').1⦄ ⦃g : V ⟶ A⦄, R.arrows g →
        Nonempty ((liftingProblemLifts B S hS hF hG f i hi x y).toFunctor.obj (op V)) := by
  refine ⟨liftingProblemLiftSieve B S hS hF hG f i hi x y A, ?_, fun V g hg => hg⟩
  exact (SmallEtale.topology B S hS (liftingProblemAmbient B S hS T').1).superset_covering
    (fun {V} g hg => hg) <|
      (SmallEtale.topology B S hS (liftingProblemAmbient B S hS T').1).pullback_stable
        (liftingProblemToTopChart B S hS A)
        (liftingProblemLiftSieve_mem_topology_topChart B S hS hF hG f hfse hT hT' i hi x y hxy)

end AlgebraicGeometry.Space

end

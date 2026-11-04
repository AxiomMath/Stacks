module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModulePullbackSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongApproximationSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackApproximationOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummandsGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives

/-!
# Derived pullback along a representable morphism of algebraic spaces preserves pseudo-coherence

Let `g : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` whose underlying morphism
of presheaves is representable.  Stacks 08H4 says that the derived pullback `Lg^*` carries a
pseudo-coherent object of `D(𝒪_X)` to a pseudo-coherent object of `D(𝒪_{X'})`.  This file
proves it for such `g`.

## The argument

Base change of étale scheme charts along `g` is a continuous functor
`u : X_étale ⥤ X'_étale`, `W ↦ W ×_X X'` (Stacks 03G2, part (4)), whose images cover `X'`.
For a chart `W` of `X` write `g_W : W ×_X X' ⟶ W` for the projection, a morphism of algebraic
spaces.  The localized functor on slices is

`Mod(𝒪_X|_W) ≌ Mod(𝒪_W) --g_W^*--> Mod(𝒪_{W ×_X X'}) ≌ Mod(𝒪_{X'}|_{u(W)})`,

the two equivalences being Stacks 04M0 for the two charts, and the localization square
`(- |_W) ⋙ G_W ≅ g^* ⋙ (- |_{u(W)})` is the composition comparison of Stacks 03LU around the
cartesian square of charts.  `G_W` is not exact, but it carries a strictly perfect approximation
of `K|_W` in degrees `> m` to one when `K` is K-flat with flat terms: the approximation is read
on `W`, where its target is the pullback of `K` along the chart, again K-flat with flat terms by
Stacks 0G7E, and degreewise pullback along the morphism of small étale ringed topoi of `g_W`
preserves approximations between such complexes.  So
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_mapHomologicalComplex_of_approx`
applies to a K-flat resolution of a pseudo-coherent representative of `E`, and the derived
pullback of `E` is the degreewise pullback of that resolution, by Stacks 06YY.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable`:
  Stacks 08H4 for a representable morphism of algebraic spaces.

## References

* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (hg : yoneda.relativelyRepresentable g.hom)

/-! ### The localized pullback on slices -/

/-- The projection `W ×_X X' ⟶ W` of a base-changed chart, as a morphism of the represented
algebraic spaces. -/
abbrev baseChangeChartMap (W : SmallEtale B S hS X.1) :
    chartSpace B S hS X' ((smallBaseChange B S hS g hg).obj W) ⟶ chartSpace B S hS X W :=
  chartSpaceMapOver B S hS (V := W) (W := (smallBaseChange B S hS g hg).obj W) (hg.snd W.1.hom)

/-- The square of charts formed by `W ×_X X' ⟶ W`, the chart maps and `g` commutes. -/
theorem baseChangeChartMap_square (W : SmallEtale B S hS X.1) :
    yoneda.map (hg.snd W.1.hom) ≫ W.obj.hom =
      ((smallBaseChange B S hS g hg).obj W).obj.hom ≫ g.hom :=
  (hg.w W.1.hom).symm

/-- **The localized pullback on slices.**  The slice of `X_étale` at a chart `W`, read on the
chart `W` by Stacks 04M0, pulled back along `W ×_X X' ⟶ W`, and read back on the slice of
`X'_étale` at `W ×_X X'`. -/
def baseChangeSlicePullback (W : SmallEtale B S hS X.1) :
    SheafOfModules.{u} ((structureRingSheaf B S hS X).over W) ⥤
      SheafOfModules.{u} ((structureRingSheaf B S hS X').over
        ((smallBaseChange B S hS g hg).obj W)) :=
  chartModuleSliceReindex B S hS X W ⋙ modulePullback B S hS (baseChangeChartMap B S hS g hg W) ⋙
    (chartModuleSliceEquiv B S hS X' ((smallBaseChange B S hS g hg).obj W)).inverse

/-- **The localization square of the localized pullback**: restricting to the slice at `W` and
pulling back is pulling back and restricting to the slice at `W ×_X X'`. -/
def baseChangeSlicePullbackSquare (W : SmallEtale B S hS X.1) :
    SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) W ⋙
        baseChangeSlicePullback B S hS g hg W ≅
      modulePullback B S hS g ⋙ SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X')
        ((smallBaseChange B S hS g hg).obj W) :=
  let W' := (smallBaseChange B S hS g hg).obj W
  let ov := SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) W
  let ov' := SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X') W'
  let re := chartModuleSliceReindex B S hS X W
  let re' := chartModuleSliceReindex B S hS X' W'
  let pW := modulePullback B S hS (baseChangeChartMap B S hS g hg W)
  let pg := modulePullback B S hS g
  let inv' := (chartModuleSliceEquiv B S hS X' W').inverse
  let e₁ : ov ⋙ re ⋙ pW ⋙ inv' ≅ (ov ⋙ re) ⋙ pW ⋙ inv' :=
    (Functor.associator ov re (pW ⋙ inv')).symm
  let e₂ : (ov ⋙ re) ⋙ pW ⋙ inv' ≅ chartModuleRestriction B S hS X W ⋙ pW ⋙ inv' :=
    Functor.isoWhiskerRight (chartModuleRestrictionSliceIso B S hS X W).symm (pW ⋙ inv')
  let e₃ : chartModuleRestriction B S hS X W ⋙ pW ⋙ inv' ≅
      (chartModuleRestriction B S hS X W ⋙ pW) ⋙ inv' :=
    (Functor.associator (chartModuleRestriction B S hS X W) pW inv').symm
  let e₄ : (chartModuleRestriction B S hS X W ⋙ pW) ⋙ inv' ≅
      (pg ⋙ chartModuleRestriction B S hS X' W') ⋙ inv' :=
    Functor.isoWhiskerRight (chartModuleRestrictionBaseChangeIso B S hS g (V := W) (W := W')
      (hg.snd W.1.hom) (baseChangeChartMap_square B S hS g hg W)) inv'
  let e₅ : (pg ⋙ chartModuleRestriction B S hS X' W') ⋙ inv' ≅
      pg ⋙ chartModuleRestriction B S hS X' W' ⋙ inv' :=
    Functor.associator pg (chartModuleRestriction B S hS X' W') inv'
  let e₆ : chartModuleRestriction B S hS X' W' ⋙ inv' ≅ (ov' ⋙ re') ⋙ inv' :=
    Functor.isoWhiskerRight (chartModuleRestrictionSliceIso B S hS X' W') inv'
  let e₇ : (ov' ⋙ re') ⋙ inv' ≅ ov' :=
    Functor.associator ov' re' inv' ≪≫
      Functor.isoWhiskerLeft ov' (chartModuleSliceEquiv B S hS X' W').unitIso.symm ≪≫
      Functor.rightUnitor ov'
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅ ≪≫ Functor.isoWhiskerLeft pg (e₆ ≪≫ e₇)

/-! ### The base-changed charts cover -/

/-- **The base changes of the étale charts of `X` cover `X'`.**  A point `z` of an étale chart
`V` of `X'` is hit by a geometric point `x` of `X'` lifted into `V`; its image in `X` lifts into
some étale chart `W` of `X`, hence `x` lifts into `W ×_X X'` (Stacks 03G2, part (4), read on
geometric fibres), and the two lifts of `x` are refined by a common one, the fibre functor of a
geometric point being cofiltered. -/
theorem coversTop_smallBaseChange :
    (SmallEtale.topology B S hS X'.1).CoversTop (smallBaseChange B S hS g hg).obj := by
  intro V
  refine smallEtale_sieve_of_pointwise_covering B S hS X'.1 V _ (fun z => ?_)
  obtain ⟨x, p, z', hz⟩ := exists_geo_lift_at_chart_point B S hS X'.1 V z
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 (geometricPointMap g.hom x)
  obtain ⟨N⟩ : Nonempty (SmallEtaleNeighborhood (geometricPointMap g.hom x)) :=
    IsCofiltered.nonempty
  obtain ⟨q, -⟩ := (smallBaseChangeFiberMap_bijective B S hS g hg x N.chart).2
    ⟨N.point, N.point_comp⟩
  have := isCofiltered_geometricFiber_elements B S hS X'.1 X'.2 x
  let a : (geometricFiber B S hS X'.1 x).Elements := ⟨V, p⟩
  let b : (geometricFiber B S hS X'.1 x).Elements :=
    ⟨(smallBaseChange B S hS g hg).obj N.chart, q⟩
  let c := IsCofiltered.min a b
  let ca : c ⟶ a := IsCofiltered.minToLeft a b
  let cb : c ⟶ b := IsCofiltered.minToRight a b
  refine ⟨c.1, ca.1, ⟨N.chart, ⟨cb.1⟩⟩,
    (BigFppfOver.toScheme B S hS).map c.2.1 z', ?_⟩
  have h1 : c.2.1 ≫ (SmallEtale.toOver B S hS X'.1).map ca.1 = p.1 := congrArg Subtype.val ca.2
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, h1, hz]

/-! ### The localized pullback is right exact and carries the unit to the unit -/

/-- The localized pullback on slices preserves finite colimits. -/
instance preservesFiniteColimits_baseChangeSlicePullback (W : SmallEtale B S hS X.1) :
    PreservesFiniteColimits (baseChangeSlicePullback B S hS g hg W) := by
  have := (modulePullbackAdjunction B S hS (baseChangeChartMap B S hS g hg W)).isLeftAdjoint
  dsimp only [baseChangeSlicePullback]
  infer_instance

/-- The localized pullback on slices is additive. -/
instance additive_baseChangeSlicePullback (W : SmallEtale B S hS X.1) :
    (baseChangeSlicePullback B S hS g hg W).Additive :=
  have : PreservesBinaryBiproducts (baseChangeSlicePullback B S hS g hg W) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- Pullback of modules along a morphism of algebraic spaces is additive. -/
instance additive_modulePullback {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z) :
    (modulePullback B S hS k).Additive :=
  have := (modulePullbackAdjunction B S hS k).isLeftAdjoint
  have : PreservesBinaryBiproducts (modulePullback B S hS k) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The localized pullback carries the structure sheaf of the slice to the structure sheaf of
the slice. -/
def baseChangeSlicePullbackUnitIso (W : SmallEtale B S hS X.1) :
    (baseChangeSlicePullback B S hS g hg W).obj
        (SheafOfModules.unit ((structureRingSheaf B S hS X).over W)) ≅
      SheafOfModules.unit ((structureRingSheaf B S hS X').over
        ((smallBaseChange B S hS g hg).obj W)) :=
  (baseChangeSlicePullbackSquare B S hS g hg W).app
      (SheafOfModules.unit (structureRingSheaf B S hS X)) ≪≫
    (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X')
      ((smallBaseChange B S hS g hg).obj W)).mapIso (modulePullbackUnitIso B S hS g) ≪≫
    SheafOfModules.overFunctorUnitIso _ _

/-- Reading the slice at a chart on the chart carries the structure sheaf to the structure
sheaf. -/
def chartModuleSliceReindexUnitIso {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1) :
    (chartModuleSliceReindex B S hS Z W).obj
        (SheafOfModules.unit ((structureRingSheaf B S hS Z).over W)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS (chartSpace B S hS Z W)) :=
  (chartModuleSliceReindex B S hS Z W).mapIso
      (SheafOfModules.overFunctorUnitIso (structureRingSheaf B S hS Z) W).symm ≪≫
    ((chartModuleRestrictionSliceIso B S hS Z W).app
      (SheafOfModules.unit (structureRingSheaf B S hS Z))).symm ≪≫
    modulePullbackUnitIso B S hS (chartToSpace B S hS Z W)

/-- Homology conditions of an approximation transport along an isomorphism of arrows. -/
theorem approximation_of_arrowIso {C : Type*} [Category C] [Abelian C]
    {P K P' K' : CochainComplex C ℤ} (φ : P ⟶ K) (φ' : P' ⟶ K') (e₁ : P ≅ P') (e₂ : K ≅ K')
    (w : φ ≫ e₂.hom = e₁.hom ≫ φ') (m : ℤ)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap φ j))
    (hepi : Epi (HomologicalComplex.homologyMap φ m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap φ' j)) ∧
      Epi (HomologicalComplex.homologyMap φ' m) := by
  have hφ' : φ' = e₁.inv ≫ φ ≫ e₂.hom := by rw [w, Iso.inv_hom_id_assoc]
  have h₁ := fun j => AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso e₁.symm j
  have h₂ := fun j => AlgebraicGeometry.RingedSite.isIso_homologyMap_of_iso e₂ j
  subst hφ'
  refine ⟨fun j hj => ?_, ?_⟩
  · have := hiso j hj
    have := h₁ j
    have := h₂ j
    simp only [HomologicalComplex.homologyMap_comp]
    infer_instance
  · have := h₁ m
    have := h₂ m
    simp only [HomologicalComplex.homologyMap_comp]
    infer_instance

/-- Homology conditions of the degreewise image of an approximation transport along an
equality of additive functors. -/
theorem approximation_mapHomologicalComplex_of_eq {C D : Type*} [Category C] [Abelian C]
    [Category D] [Abelian D] {F G : C ⥤ D} (hFa : F.Additive) (hGa : G.Additive) (h : F = G)
    {P K : CochainComplex C ℤ} (β : P ⟶ K) (m : ℤ)
    (hβ : (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map β) j)) ∧
      Epi (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map β) m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map β) j)) ∧
      Epi (HomologicalComplex.homologyMap
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map β) m) := by
  subst h
  exact hβ

/-- A functor carries `a ≫ e.hom` followed by `e.inv` to `a`. -/
theorem map_comp_hom_map_inv {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {P Q R : C}
    (a : P ⟶ Q) (e : Q ≅ R) : F.map (a ≫ e.hom) ≫ F.map e.inv = 𝟙 _ ≫ F.map a := by
  rw [← F.map_comp, Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]

/-- A complex whose terms vanish outside a finite set of degrees is strictly bounded above. -/
theorem exists_isStrictlyLE_of_finite {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    (K : CochainComplex C ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite) :
    ∃ b : ℤ, K.IsStrictlyLE b := by
  obtain ⟨b, hb⟩ := hK.bddAbove
  refine ⟨b, ?_⟩
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_contra h
  exact not_le.2 hi (hb h)

/-- K-flatness with flat terms of the degreewise image of a complex depends only on the functor:
it transports along an equality of additive functors. -/
theorem isKFlat_mapHomologicalComplex_of_eq {Z Z' : AlgebraicSpaces B S hS}
    {F G : SheafOfModules.{u} (structureRingSheaf B S hS Z) ⥤
      SheafOfModules.{u} (structureRingSheaf B S hS Z')} (hFa : F.Additive) (hGa : G.Additive)
    (h : F = G)
    (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS Z)) ℤ)
    (hF : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z')
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z')
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  subst h
  exact hF

/-- **Stacks 0G7E for modules on algebraic spaces.**  Degreewise pullback of modules along a
morphism of algebraic spaces carries a K-flat complex with flat terms to one. -/
theorem isKFlat_modulePullback {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z)
    (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS Z)) ℤ)
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z')
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((modulePullback B S hS k).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
  isKFlat_mapHomologicalComplex_of_eq B S hS
    ((pullbackModules_eq_modulePullback B S hS k).symm ▸ additive_modulePullback B S hS k)
    (additive_modulePullback B S hS k) (pullbackModules_eq_modulePullback B S hS k) K
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isKFlat_pullbackMapHomotopy
      (smallEtaleRingedToposHom B S hS k) _ hK)

/-! ### The localized pullback preserves approximations of a K-flat complex -/

/-- Reading the slice at a chart on the chart preserves finite limits. -/
instance preservesFiniteLimits_chartModuleSliceReindex {Z : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS Z.1) : PreservesFiniteLimits (chartModuleSliceReindex B S hS Z W) :=
  (chartModuleSliceEquiv_functor B S hS Z W) ▸ inferInstance

/-- Reading the slice at a chart on the chart preserves finite colimits. -/
instance preservesFiniteColimits_chartModuleSliceReindex {Z : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS Z.1) : PreservesFiniteColimits (chartModuleSliceReindex B S hS Z W) :=
  (chartModuleSliceEquiv_functor B S hS Z W) ▸ inferInstance

/-- Reading the slice at a chart on the chart is additive. -/
instance additive_chartModuleSliceReindex {Z : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS Z.1) : (chartModuleSliceReindex B S hS Z W).Additive :=
  have : PreservesBinaryBiproducts (chartModuleSliceReindex B S hS Z W) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- The inverse of the equivalence between modules on the slice at a chart and modules on the
chart is additive. -/
instance additive_chartModuleSliceEquiv_inverse {Z : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS Z.1) : (chartModuleSliceEquiv B S hS Z W).inverse.Additive :=
  have : PreservesBinaryBiproducts (chartModuleSliceEquiv B S hS Z W).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction of modules to a chart is additive. -/
instance additive_chartModuleRestriction {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1) :
    (chartModuleRestriction B S hS Z W).Additive :=
  additive_modulePullback B S hS (chartToSpace B S hS Z W)

/-- Restriction of modules over the structure sheaf to the slice at a chart is additive. -/
instance additive_overFunctor_structureRingSheaf {Z : AlgebraicSpaces B S hS}
    (W : SmallEtale B S hS Z.1) :
    (SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Z) W).Additive :=
  inferInstanceAs
    (SheafOfModules.pushforward.{u} (𝟙 ((structureRingSheaf B S hS Z).over W))).Additive

/-- The restriction of a complex to the slice at a chart, read on the chart, is the pullback of
the complex along the chart (Stacks Equation 03LW, degreewise). -/
def chartRestrictComplexIso {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1)
    (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS Z)) ℤ) :
    ((chartModuleSliceReindex B S hS Z W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS Z) W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((chartModuleRestriction B S hS Z W).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => ((chartModuleRestrictionSliceIso B S hS Z W).app (K.X i)).symm)
    (fun i j _ => ((chartModuleRestrictionSliceIso B S hS Z W).inv.naturality (K.d i j)).symm)

/-- A strictly perfect complex on the slice at a chart, read on the chart, is K-flat with flat
terms (Stacks 06YQ). -/
theorem isKFlat_chartModuleSliceReindex {Z : AlgebraicSpaces B S hS} (W : SmallEtale B S hS Z.1)
    (P : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS Z).over W)) ℤ)
    (hP : IsStrictlyPerfect ((structureRingSheaf B S hS Z).over W) P) :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS Z W))
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((chartModuleSliceReindex B S hS Z W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P)) := by
  have hP₁ : IsStrictlyPerfect (structureRingSheaf B S hS (chartSpace B S hS Z W))
      (((chartModuleSliceReindex B S hS Z W).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    SheafOfModules.isStrictlyPerfect_map _ (chartModuleSliceReindexUnitIso B S hS W) hP
  obtain ⟨b, hb⟩ := exists_isStrictlyLE_of_finite _ hP₁.bounded
  exact Stacks.Cohomology.DerivedPullbackOfToposHom.isKFlat_of_isStrictlyLE
    (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS Z W)) _ b hb
    (fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect_general
      (Y := smallEtaleRingedSite B S hS (chartSpace B S hS Z W).1 (chartSpace B S hS Z W).2) hP₁ i)

/-- **Degreewise pullback of modules along a morphism of algebraic spaces preserves an
approximation between K-flat complexes with flat terms.** -/
theorem modulePullback_approximation {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z)
    {R P : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS Z)) ℤ} (β : R ⟶ P)
    (hR : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R))
    (hP : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS Z)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))
    (m : ℤ) (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j))
    (hepi : Epi (HomologicalComplex.homologyMap β m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
        (((modulePullback B S hS k).mapHomologicalComplex (ComplexShape.up ℤ)).map β) j)) ∧
      Epi (HomologicalComplex.homologyMap
        (((modulePullback B S hS k).mapHomologicalComplex (ComplexShape.up ℤ)).map β) m) :=
  approximation_mapHomologicalComplex_of_eq
    ((pullbackModules_eq_modulePullback B S hS k).symm ▸ additive_modulePullback B S hS k)
    (additive_modulePullback B S hS k) (pullbackModules_eq_modulePullback B S hS k) β m
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackComplex_approximation
      (smallEtaleRingedToposHom B S hS k) β hR hP m hiso hepi)

/-- An exact additive functor, applied degreewise, preserves the homology conditions of an
approximation. -/
private theorem approximation_map_of_exact {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P K : CochainComplex C ℤ} (α : P ⟶ K) (m : ℤ)
    (h : (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) j)) ∧
      Epi (HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) m) :=
  ⟨fun j hj =>
      Stacks.PseudoCoherence.DerivedCharacterization.isIso_homologyMap_mapHomologicalComplex
        F α j (h.1 j hj),
    Stacks.PseudoCoherence.DerivedCharacterization.epi_homologyMap_mapHomologicalComplex
      F α m h.2⟩

/-- **The localized pullback preserves a strictly perfect approximation of the restriction of a
K-flat complex with flat terms**, read on the charts: if `α : P ⟶ K|_W` is an approximation with
`P` strictly perfect, then so is its image under reading on `W` and pulling back along
`W ×_X X' ⟶ W`. -/
theorem chartPullback_approximation
    (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS X)) ℤ)
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (W : SmallEtale B S hS X.1) (m : ℤ)
    (P : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) ℤ)
    (hP : IsStrictlyPerfect ((structureRingSheaf B S hS X).over W) P)
    (α : P ⟶ ((SheafOfModules.overFunctor.{u} (structureRingSheaf B S hS X) W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      (((modulePullback B S hS (baseChangeChartMap B S hS g hg W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (((chartModuleSliceReindex B S hS X W).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α)) j)) ∧
    Epi (HomologicalComplex.homologyMap
      (((modulePullback B S hS (baseChangeChartMap B S hS g hg W)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (((chartModuleSliceReindex B S hS X W).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α)) m) := by
  have e := chartRestrictComplexIso B S hS W K
  have h₁ := approximation_map_of_exact (chartModuleSliceReindex B S hS X W) α m ⟨hiso, hepi⟩
  have h₂ := modulePullback_approximation B S hS (baseChangeChartMap B S hS g hg W)
    ((((chartModuleSliceReindex B S hS X W).mapHomologicalComplex (ComplexShape.up ℤ)).map α) ≫
      e.hom)
    (isKFlat_chartModuleSliceReindex B S hS W P hP)
    (isKFlat_modulePullback B S hS (chartToSpace B S hS X W) K hK) m
    (fun j hj => AlgebraicGeometry.RingedSite.isIso_homologyMap_comp_iso _ e j (h₁.1 j hj))
    (AlgebraicGeometry.RingedSite.epi_homologyMap_comp_iso _ e m h₁.2)
  refine approximation_of_arrowIso _ _ (Iso.refl _)
    (((modulePullback B S hS (baseChangeChartMap B S hS g hg W)).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso e.symm) ?_ m h₂.1 h₂.2
  exact map_comp_hom_map_inv _ _ e

/-- **The localized pullback preserves a strictly perfect approximation of the restriction of a
K-flat complex with flat terms.**  On the chart `W` the target of the approximation is the
pullback of the complex along the chart, again K-flat with flat terms by Stacks 0G7E, and the
source is strictly perfect, hence K-flat with flat terms by Stacks 06YQ; degreewise pullback
along `W ×_X X' ⟶ W` preserves approximations between such complexes, and the two
equivalences of Stacks 04M0 are exact. -/
theorem baseChangeSlicePullback_approximation
    (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS X)) ℤ)
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (W : SmallEtale B S hS X.1) (m : ℤ)
    (P : CochainComplex (SheafOfModules.{u} ((structureRingSheaf B S hS X).over W)) ℤ)
    (hP : IsStrictlyPerfect ((structureRingSheaf B S hS X).over W) P)
    (α : P ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex K W)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      (((baseChangeSlicePullback B S hS g hg W).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α) j)) ∧
    Epi (HomologicalComplex.homologyMap
      (((baseChangeSlicePullback B S hS g hg W).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α) m) := by
  exact approximation_map_of_exact (chartModuleSliceEquiv B S hS X'
    ((smallBaseChange B S hS g hg).obj W)).inverse
    (((modulePullback B S hS (baseChangeChartMap B S hS g hg W)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
      (((chartModuleSliceReindex B S hS X W).mapHomologicalComplex (ComplexShape.up ℤ)).map α)) m
    (chartPullback_approximation B S hS g hg K hK W m P hP α hiso hepi)

/-! ### The transfer of pseudo-coherence -/

include hg in
/-- **Degreewise pullback along a representable morphism of algebraic spaces carries an
`m`-pseudo-coherent complex which is K-flat with flat terms to an `m`-pseudo-coherent
complex.** -/
theorem isPseudoCoherentComplexFrom_modulePullback
    (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS X)) ℤ)
    (hK : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS X)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (m : ℤ) (hKm : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentComplexFrom K m) :
    (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherentComplexFrom
      (((modulePullback B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m := by
  let u : (smallEtaleRingedSite B S hS X.1 X.2).C ⥤ (smallEtaleRingedSite B S hS X'.1 X'.2).C :=
    smallBaseChange B S hS g hg
  exact AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_mapHomologicalComplex_of_approx
    u (modulePullback B S hS g) (baseChangeSlicePullback B S hS g hg)
    (additive_modulePullback B S hS g) (isContinuous_smallBaseChange B S hS g hg)
    (coversTop_smallBaseChange B S hS g hg)
    (additive_baseChangeSlicePullback B S hS g hg)
    (preservesFiniteColimits_baseChangeSlicePullback B S hS g hg)
    (baseChangeSlicePullbackUnitIso B S hS g hg)
    (baseChangeSlicePullbackSquare B S hS g hg) K m
    (fun W P hP α hiso hepi =>
      baseChangeSlicePullback_approximation B S hS g hg K hK W m P hP α hiso hepi)
    hKm

/-- Pseudo-coherence of the degreewise image of a complex depends only on the functor. -/
theorem isPseudoCoherentComplexFrom_mapHomologicalComplex_of_eq {Z Z' : AlgebraicSpaces B S hS}
    {F G : SheafOfModules.{u} (structureRingSheaf B S hS Z) ⥤
      SheafOfModules.{u} (structureRingSheaf B S hS Z')} (hFa : F.Additive) (hGa : G.Additive)
    (h : F = G) (K : CochainComplex (SheafOfModules.{u} (structureRingSheaf B S hS Z)) ℤ) (m : ℤ)
    (hF : (smallEtaleRingedSite B S hS Z'.1 Z'.2).IsPseudoCoherentComplexFrom
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m) :
    (smallEtaleRingedSite B S hS Z'.1 Z'.2).IsPseudoCoherentComplexFrom
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) m := by
  subst h
  exact hF

include hg in
/-- **Stacks 08H4 for a representable morphism of algebraic spaces.**  If `g : X' ⟶ X` is a
morphism of algebraic spaces whose underlying morphism of presheaves is representable, then the
derived pullback `Lg^*` carries a pseudo-coherent object of `D(𝒪_X)` to a pseudo-coherent
object of `D(𝒪_{X'})`.

`E` is represented by a pseudo-coherent complex, which Stacks 06YS resolves by a K-flat complex
`K` with flat terms; `K` is again pseudo-coherent (Stacks 08FU, part (2)), `Lg^*E` is the
degreewise pullback of `K` (Stacks 06YY), and that is pseudo-coherent by
`AlgebraicGeometry.Space.isPseudoCoherentComplexFrom_modulePullback`. -/
theorem isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
    ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E →
        (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent
          ((smallEtaleDerivedModulePullback B S hS g).obj E) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X'.1 X'.2)
  intro E hE
  obtain ⟨K₀, hK₀, ⟨e₀⟩⟩ := hE
  obtain ⟨K', hK, s, hs⟩ :=
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.hasResolutions_isKFlat
    (Y := smallEtaleRingedTopos B S hS X) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K₀)
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ := K'.as
  let Qh := DerivedCategory.Qh (C := Modules.{u, u} B S hS X.1 X.2)
  have hQs : IsIso (Qh.map s) :=
    Localization.inverts Qh (HomotopyCategory.quasiIso _ _) s hs
  let e : DerivedCategory.Q.obj K ≅ E :=
    ((DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS X.1 X.2)).app K).symm ≪≫
      @asIso _ _ _ _ (Qh.map s) hQs ≪≫
      (DerivedCategory.quotientCompQhIso (Modules.{u, u} B S hS X.1 X.2)).app K₀ ≪≫ e₀
  have hKm : ∀ m : ℤ, (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherentComplexFrom K m :=
    fun m => AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_iso_general
      (smallEtaleRingedSite B S hS X.1 X.2) E m ⟨K₀, hK₀ m, ⟨e₀⟩⟩ K e
  have heq := pullbackModules_eq_modulePullback B S hS g
  refine ⟨(((smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K, fun m => ?_, ⟨?_⟩⟩
  · exact isPseudoCoherentComplexFrom_mapHomologicalComplex_of_eq B S hS
      (additive_modulePullback B S hS g)
      (heq.symm ▸ additive_modulePullback B S hS g) heq.symm K m
      (isPseudoCoherentComplexFrom_modulePullback B S hS g hg K hK m (hKm m))
  · exact (derivedPullbackObjIsoOfIsKFlat B S hS g K hK).symm ≪≫
      (smallEtaleDerivedModulePullback B S hS g).mapIso e

end AlgebraicGeometry.Space

end

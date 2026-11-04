module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Restriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullRestrictionTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompIsoChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMapChartFormula

/-!
# Reading a section of a graded algebra on an étale chart as a section of the restriction

Let `X` be an algebraic space, `𝒜` a graded `𝒪_X`-algebra on the small étale site of `X`, and let
`V = (T, v)` be an étale chart of `X`.  A section `a` of `𝒜_n` over `V` determines a section of
the restriction `v^*𝒜` of Stacks 084A (`AlgebraicGeometry.Space.etalePointAlgebra`, read on the
Zariski opens of `T` by `AlgebraicGeometry.Space.zariskiReading`) over every Zariski open `O` of
`T`: the chart component of the unit `𝒜_n ⟶ v_* v^*𝒜_n` of Stacks 03D7 at the chart diagram
`O ⊆ T ⟶ V` (`AlgebraicGeometry.Space.modulePullbackUnitSection`).  This is the reading
`AlgebraicGeometry.Space.chartOpenReading`.

The main result is its compatibility with the restriction maps of Stacks 084A.  For a morphism
`k : V' ⟶ V` of étale charts, with underlying `τ : T' ⟶ T`, the restriction map
`v^*𝒜 ⟶ τ_*(v'^*𝒜)` of `AlgebraicGeometry.Space.pointRestriction` carries the reading of `a` on
`O` to the reading of the restriction `a|_{V'}` on `τ⁻¹(O)`.

## Main definitions

* `AlgebraicGeometry.Space.selfOpensChartDiagram`: the chart diagram `O ⊆ T ⟶ V`.
* `AlgebraicGeometry.Space.chartOpenReading`: the reading of a section over `V` on a Zariski open
  of `T`.
* `AlgebraicGeometry.Space.preimageOpensChartDiagram`: the chart diagram `τ⁻¹(O) ⟶ O` over the
  morphism of represented algebraic spaces of `τ`.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardCounitApp_preimageOpensChartDiagram`: the chart
  component of a direct image along `τ` at `τ⁻¹(O) ⟶ O` is the identification of sections
  `AlgebraicGeometry.Space.directImageSelfOpensSection`.
* `AlgebraicGeometry.Space.modulePullbackCompIso_transport_unitSection`: the comparison of
  Stacks 03LU followed by a transport carries a unit section of a unit section to the unit
  section of the restriction, along a morphism of charts below.
* `AlgebraicGeometry.Space.pointRestriction_chartOpenReading`: **the restriction maps of
  Stacks 084A are the restriction of sections along morphisms of étale charts.**

## References

* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The comparison of Stacks 03LU on unit sections, along a morphism of charts below -/

section Transport

variable {P' P Y : AlgebraicSpaces B S hS}

/-- **The comparison of Stacks 03LU followed by a transport carries a unit section of a unit
section to the unit section of a restriction.**  For `φ : P' ⟶ P`, `f : P ⟶ Y`, `f' = φ ≫ f`,
chart diagrams `U ⟶ V` over `φ` and `V ⟶ W` over `f`, a chart diagram `U ⟶ W'` over `f'` and a
morphism of charts `k : W' ⟶ W` with `a ≫ b = e ≫ k`, the comparison
`φ^*(f^*M) ⟶ f'^*M` sends the unit section along `a` of the unit section along `b` of `s` to the
unit section along `e` of the restriction of `s` to `W'`. -/
theorem modulePullbackCompIso_transport_unitSection (φ : P' ⟶ P) (f : P ⟶ Y) (f' : P' ⟶ Y)
    (h : φ ≫ f = f') (M : Modules.{u, u} B S hS Y.1 Y.2)
    {U : SmallEtale B S hS P'.1} {V : SmallEtale B S hS P.1} {W W' : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS P'.1).obj U ⟶ (SmallEtale.toOver B S hS P.1).obj V)
    (b : (SmallEtale.toOver B S hS P.1).obj V ⟶ (SmallEtale.toOver B S hS Y.1).obj W)
    (ha : U.1.hom ≫ φ.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ f.hom = yoneda.map b ≫ W.1.hom)
    (e : (SmallEtale.toOver B S hS P'.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj W')
    (he : U.1.hom ≫ f'.hom = yoneda.map e ≫ W'.1.hom) (k : W' ⟶ W)
    (hk : a ≫ b = e ≫ (SmallEtale.toOver B S hS Y.1).map k) (s : M.val.obj (op W)) :
    ((modulePullbackCompIso B S hS φ f).hom.app M ≫ pullbackTransport M h).val.app (op U)
        (modulePullbackUnitSection B S hS φ ((modulePullback B S hS f).obj M) ⟨U, V, a, ha⟩
          (modulePullbackUnitSection B S hS f M ⟨V, W, b, hb⟩ s)) =
      modulePullbackUnitSection B S hS f' M ⟨U, W', e, he⟩ (M.val.map k.op s) := by
  subst h
  have h1 := modulePullbackCompIso_hom_val_app_modulePullbackUnitSection B S hS φ f a b ha hb M s
  have h2 := (modulePushforwardHomFMap B S hS (φ ≫ f) _ M
    ((modulePullbackAdjunction B S hS (φ ≫ f)).unit.app M)).naturality
      (ChartDiagram.comp B S hS φ f a b ha hb) ⟨U, W', e, he⟩ (𝟙 U) k
      ((Category.id_comp _).trans hk) s
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (congrArg (fun m => m (modulePullbackUnitSection B S hS (φ ≫ f) M
    (ChartDiagram.comp B S hS φ f a b ha hb) s))
      (((modulePullback B S hS (φ ≫ f)).obj M).val.map_id (op U))).symm

end Transport

/-! ### The chart diagrams of Zariski opens -/

section Charts

variable {X : AlgebraicSpaces B S hS}

/-- **The chart diagram of a Zariski open of an étale chart**: for an étale chart `V = (T, v)` of
`X` and a Zariski open `O` of `T`, the chart of `O` in the small étale site of `T`, over `V` by
the open immersion `O ⊆ T`. -/
def selfOpensChartDiagram (V : SmallEtale B S hS X.1)
    (O : (chartScheme (idEtaleChart B S hS V.1.left)).Opens) :
    ChartDiagram B S hS (yoneda.obj V.1.left) X.1 (pointHom (X := X) V.1.hom).hom where
  U := (selfOpensFunctor B S hS V.1.left).obj O
  V := V
  g := Yoneda.fullyFaithful.preimage ((selfOpensFunctor B S hS V.1.left).obj O).1.hom
  comm := by
    rw [Functor.FullyFaithful.map_preimage]
    rfl

/-- The image under the Yoneda embedding of the structure morphism of `selfOpensChartDiagram V O`
is the structure morphism of the chart of `O` in the small étale site of `V.1.left`. -/
theorem yoneda_map_selfOpensChartDiagram_g (V : SmallEtale B S hS X.1)
    (O : (chartScheme (idEtaleChart B S hS V.1.left)).Opens) :
    yoneda.map (selfOpensChartDiagram V O).g =
      ((selfOpensFunctor B S hS V.1.left).obj O).1.hom :=
  Yoneda.fullyFaithful.map_preimage ((selfOpensFunctor B S hS V.1.left).obj O).1.hom

/-- **The reading of a section over an étale chart on a Zariski open.**  For an étale chart
`V = (T, v)` of `X`, a Zariski open `O` of `T` and a section `a` of `𝒜_n` over `V`, the section of
the restriction `(v^*𝒜)_n` of Stacks 084A over `O`: the chart component of the unit of
Stacks 03D7 at the chart diagram `O ⊆ T ⟶ V`. -/
def chartOpenReading (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
    (V : SmallEtale B S hS X.1) (O : (chartScheme (idEtaleChart B S hS V.1.left)).Opens) (n : ℤ)
    (a : (A.piece n).val.obj (op V)) :
    ((zariskiReading V.1.left (etalePointAlgebra A V.1.left V.1.hom)).piece n).val.obj (op O) :=
  modulePullbackUnitSection B S hS (pointHom V.1.hom) (A.piece n) (selfOpensChartDiagram V O) a

end Charts

/-! ### The chart diagram of a preimage open -/

section Preimage

variable {T T' : BigFppfOver B S hS}

/-- The chart of the preimage `τ⁻¹(O)` of a Zariski open, as an index of the limit computing the
sections over the chart of `O` of a direct image along `τ`: the base-changed chart, restricted
along the identification `AlgebraicGeometry.Space.baseChangeSelfOpensIso`. -/
def preimageOpensIndex (τ : T' ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    StructuredArrow (op (chartBaseChange B S hS (representedSpaceMap B S hS τ)
        ((selfOpensFunctor B S hS T).obj O)))
      (comparisonFunctor B S hS (yonedaSpace B S hS T')).op :=
  StructuredArrow.mk ((smallBaseChangeIndex B S hS (representedSpaceMap B S hS τ)
      (relativelyRepresentable_yoneda_map B S hS τ) ((selfOpensFunctor B S hS T).obj O)).hom ≫
    (comparisonFunctor B S hS (yonedaSpace B S hS T')).op.map (baseChangeSelfOpensIso τ O).inv.op)

/-- **The chart projection at the preimage open is the identification of sections of a direct
image along `τ`.** -/
theorem moduleChartProjection_preimageOpensIndex (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (P : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u))
    (x : ((testToposHom τ).toToposHom.pushforward.obj P).obj.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    (moduleChartProjection B S hS (representedSpaceMap B S hS τ)
        ((selfOpensFunctor B S hS T).obj O) (preimageOpensIndex τ O)).app P x =
      directImageSelfOpensSection τ O P x := by
  refine (moduleChartProjection_app B S hS (representedSpaceMap B S hS τ)
    ((selfOpensFunctor B S hS T).obj O) (preimageOpensIndex τ O) P x).trans ?_
  exact (ranChartCone_π_comp B S hS (yonedaSpace B S hS T') P.obj
    (chartBaseChange B S hS (representedSpaceMap B S hS τ) ((selfOpensFunctor B S hS T).obj O))
    (StructuredArrow.mkPostcomp _ (baseChangeSelfOpensIso τ O).inv.op)
    (((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS τ)).hom.app P).hom.app _
      x)).symm

/-- The morphism of charts `τ⁻¹(O) ⟶ O` over `τ : T' ⟶ T`, for a Zariski open `O` of `T`. -/
def preimageOpensChartMap (τ : T' ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    (SmallEtale.toOver B S hS (yoneda.obj T')).obj
        ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)) ⟶
      (SmallEtale.toOver B S hS (yoneda.obj T)).obj ((selfOpensFunctor B S hS T).obj O) :=
  chartBaseChangeMap B S hS (representedSpaceMap B S hS τ) ((selfOpensFunctor B S hS T).obj O)
    (preimageOpensIndex τ O)

/-- The morphism of charts `τ⁻¹(O) ⟶ O` lies over the morphism of represented algebraic spaces of
`τ`. -/
theorem preimageOpensChartMap_comm (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)).1.hom ≫
        (representedSpaceMap B S hS τ).hom =
      yoneda.map (preimageOpensChartMap τ O) ≫ ((selfOpensFunctor B S hS T).obj O).1.hom :=
  (chartDiagramOfIndex B S hS (representedSpaceMap B S hS τ)
    ((selfOpensFunctor B S hS T).obj O) (preimageOpensIndex τ O)).comm

/-- **The chart diagram `τ⁻¹(O) ⟶ O`** over the morphism of represented algebraic spaces of
`τ : T' ⟶ T`, for a Zariski open `O` of `T`. -/
def preimageOpensChartDiagram (τ : T' ⟶ T) (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    ChartDiagram B S hS (yoneda.obj T') (yoneda.obj T) (representedSpaceMap B S hS τ).hom :=
  ⟨(selfOpensFunctor B S hS T').obj (preimageOpens τ O), (selfOpensFunctor B S hS T).obj O,
    preimageOpensChartMap τ O, preimageOpensChartMap_comm τ O⟩

/-- **The chart component of a direct image along `τ` at `τ⁻¹(O) ⟶ O` is the identification of
sections `AlgebraicGeometry.Space.directImageSelfOpensSection`.** -/
theorem modulePushforwardCounitApp_preimageOpensChartDiagram (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (G : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (x : ((modulePushforward B S hS (representedSpaceMap B S hS τ)).obj G).val.obj
      (op ((selfOpensFunctor B S hS T).obj O))) :
    modulePushforwardCounitApp B S hS (representedSpaceMap B S hS τ) G
        (preimageOpensChartDiagram τ O) x =
      directImageSelfOpensSection τ O (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) x := by
  have e1 := moduleChartProjection_app B S hS (representedSpaceMap B S hS τ)
    ((selfOpensFunctor B S hS T).obj O)
    (indexOfChartDiagram B S hS (representedSpaceMap B S hS τ) (preimageOpensChartDiagram τ O))
    (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) x
  have e2 := ranChartCone_π_congr B S hS (yonedaSpace B S hS T')
    (moduleSetSheaf B S hS (yonedaSpace B S hS T') G).obj
    (chartBaseChange B S hS (representedSpaceMap B S hS τ) ((selfOpensFunctor B S hS T).obj O))
    (indexOfChartDiagram_chartDiagramOfIndex B S hS (representedSpaceMap B S hS τ)
      ((selfOpensFunctor B S hS T).obj O) (preimageOpensIndex τ O))
    (((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS τ)).hom.app
      (moduleSetSheaf B S hS (yonedaSpace B S hS T') G)).hom.app _ x)
  have e3 := (moduleChartProjection_app B S hS (representedSpaceMap B S hS τ)
    ((selfOpensFunctor B S hS T).obj O) (preimageOpensIndex τ O)
    (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) x).symm.trans
      (moduleChartProjection_preimageOpensIndex τ O
        (moduleSetSheaf B S hS (yonedaSpace B S hS T') G) x)
  exact eq_of_heq ((heq_of_eq e1).trans (e2.trans (heq_of_eq e3)))

/-- The chart diagram `τ⁻¹(O) ⟶ O` lies over `τ`. -/
theorem yoneda_map_preimageOpensChartMap (τ : T' ⟶ T)
    (O : (chartScheme (idEtaleChart B S hS T)).Opens) :
    yoneda.map (preimageOpensChartMap τ O) ≫ ((selfOpensFunctor B S hS T).obj O).1.hom =
      ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)).1.hom ≫ yoneda.map τ :=
  (preimageOpensChartMap_comm τ O).symm

end Preimage

/-! ### The restriction maps of Stacks 084A on readings -/

section Main

/-- The unit of the adjunction of the morphism of small étale ringed topoi is, on sections, the
unit of the Stacks 03D7 adjunction. -/
theorem etaleModuleAdjunction_unit_val_app {P P' : AlgebraicSpaces B S hS} (φ : P' ⟶ P)
    (N : Modules.{u, u} B S hS P.1 P.2) (W : (SmallEtale B S hS P.1)ᵒᵖ) (y : N.val.obj W) :
    ((etaleModuleAdjunction φ).unit.app N).val.app W y =
      ((modulePullbackAdjunction B S hS φ).unit.app N).val.app W y := by
  have hu : (etaleModuleAdjunction φ).unit.app N =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
          (smallEtaleRingedToposModulesHom B S hS φ)).unit.app N ≫
        (smallEtaleRingedToposHom B S hS φ).pushforwardModulesIso.hom.app
          ((modulePullback B S hS φ).obj N) :=
    Adjunction.unit_app_ofNatIsoRight _ _ N
  have h1 := congrArg (fun m : N ⟶ (smallEtaleRingedToposHom B S hS φ).pushforwardModules.obj
      ((modulePullback B S hS φ).obj N) => m.val.app W y) hu
  exact (h1.trans ((comp_val_app_apply B S hS _ _ W y).trans
    (pushforwardModulesIso_hom_app_val_app B S hS φ _ W _))).trans
      (modulePullbackAdjunction_unit_val_app B S hS φ N W y).symm

/-- **The transposed restriction map of the pulled-back algebras on unit sections.**  For
`φ : P' ⟶ P`, `f : P ⟶ X`, `f' = φ ≫ f`, chart diagrams `U ⟶ V` over `φ` and `V ⟶ W` over `f`, a
chart diagram `U ⟶ W'` over `f'` and a morphism of charts `k : W' ⟶ W` with `a ≫ b = e ≫ k`, the
transpose `φ^*(f^*𝒜_n) ⟶ f'^*𝒜_n` of the restriction map
(`AlgebraicGeometry.Space.gradedPullRestrictionApp`) sends the unit section along `a` of the
unit section along `b` of `s` to the unit section along `e` of `s|_{W'}`: the transpose is the
comparison of Stacks 03LU (`AlgebraicGeometry.Space.homEquiv_symm_gradedPullRestrictionApp`). -/
theorem homEquiv_symm_gradedPullRestrictionApp_unitSection {P' P X : AlgebraicSpaces B S hS}
    (φ : P' ⟶ P) (f : P ⟶ X) (f' : P' ⟶ X) (h : φ ≫ f = f')
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X)) (n : ℤ)
    {U : SmallEtale B S hS P'.1} {V : SmallEtale B S hS P.1} {W W' : SmallEtale B S hS X.1}
    (a : (SmallEtale.toOver B S hS P'.1).obj U ⟶ (SmallEtale.toOver B S hS P.1).obj V)
    (b : (SmallEtale.toOver B S hS P.1).obj V ⟶ (SmallEtale.toOver B S hS X.1).obj W)
    (ha : U.1.hom ≫ φ.hom = yoneda.map a ≫ V.1.hom)
    (hb : V.1.hom ≫ f.hom = yoneda.map b ≫ W.1.hom)
    (e : (SmallEtale.toOver B S hS P'.1).obj U ⟶ (SmallEtale.toOver B S hS X.1).obj W')
    (he : U.1.hom ≫ f'.hom = yoneda.map e ≫ W'.1.hom) (k : W' ⟶ W)
    (hk : a ≫ b = e ≫ (SmallEtale.toOver B S hS X.1).map k) (s : (A.piece n).val.obj (op W)) :
    (((etaleModuleAdjunction φ).homEquiv _ _).symm
        (gradedPullRestrictionApp φ f f' h A n)).val.app (op U)
        (modulePullbackUnitSection B S hS φ ((modulePullback B S hS f).obj (A.piece n))
          ⟨U, V, a, ha⟩
          (modulePullbackUnitSection B S hS f (A.piece n) ⟨V, W, b, hb⟩ s)) =
      modulePullbackUnitSection B S hS f' (A.piece n) ⟨U, W', e, he⟩
        ((A.piece n).val.map k.op s) := by
  refine (congrArg (fun m : (modulePullback B S hS φ).obj
        ((modulePullback B S hS f).obj (A.piece n))
      ⟶ (modulePullback B S hS f').obj (A.piece n) => m.val.app (op U)
    (modulePullbackUnitSection B S hS φ ((modulePullback B S hS f).obj (A.piece n))
      ⟨U, V, a, ha⟩ (modulePullbackUnitSection B S hS f (A.piece n) ⟨V, W, b, hb⟩ s)))
    (homEquiv_symm_gradedPullRestrictionApp φ f f' h A n)).trans ?_
  exact modulePullbackCompIso_transport_unitSection φ f f' h (A.piece n) a b ha hb e he k hk s

variable {X : AlgebraicSpaces B S hS}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1)
  (f' : yoneda.obj T' ⟶ X.1) (hf : yoneda.map τ ≫ f = f') (n : ℤ)
  (O : (chartScheme (idEtaleChart B S hS T)).Opens)

/-- The restriction map of Stacks 084A on a section over a Zariski open, unfolded: the
identification of sections of the direct image along `τ`, applied to the restriction map of the
pulled-back algebras. -/
theorem pointRestriction_app_val_app
    (x : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op O)) :
    ((pointRestriction A τ f f' hf).app n).val.app (op O) x =
      directImageSelfOpensSection τ O
        ((Sheaf.moduleSheafFunctor (testRing T')).obj ((etalePointAlgebra A T' f').piece n))
        (((gradedPullRestriction (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
          (pointHom_comp τ hf) A).app n).val.app (op ((selfOpensFunctor B S hS T).obj O)) x) :=
  rfl

/-- The identification of sections of a direct image along `τ`, on the unit of the étale
adjunction, is the unit section at the chart diagram `τ⁻¹(O) ⟶ O`. -/
theorem directImageSelfOpensSection_etaleModuleAdjunction_unit
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection τ O
        (moduleSetSheaf B S hS (yonedaSpace B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N))
        (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).unit.app N).val.app
          (op ((selfOpensFunctor B S hS T).obj O)) x) =
      modulePullbackUnitSection B S hS (representedSpaceMap B S hS τ) N
        (preimageOpensChartDiagram τ O) x := by
  refine (congrArg (directImageSelfOpensSection τ O
    (moduleSetSheaf B S hS (yonedaSpace B S hS T')
      ((modulePullback B S hS (representedSpaceMap B S hS τ)).obj N)))
    (etaleModuleAdjunction_unit_val_app (representedSpaceMap B S hS τ) N _ x)).trans ?_
  exact (modulePushforwardCounitApp_preimageOpensChartDiagram τ O _ _).symm

/-- The identification of sections of a direct image along `τ`, on the transpose of a morphism
`g : φ^*N ⟶ N'` along the étale adjunction, is `g` applied to the unit section at the chart diagram
`τ⁻¹(O) ⟶ O`. -/
theorem directImageSelfOpensSection_homEquiv
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (N' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
    (g : (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS τ)).toRingedToposModulesHom.pullbackModules.obj N ⟶ N')
    (x : N.val.obj (op ((selfOpensFunctor B S hS T).obj O))) :
    directImageSelfOpensSection τ O (moduleSetSheaf B S hS (yonedaSpace B S hS T') N')
        (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv N N' g).val.app
          (op ((selfOpensFunctor B S hS T).obj O)) x) =
      g.val.app (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)))
        (modulePullbackUnitSection B S hS (representedSpaceMap B S hS τ) N
          (preimageOpensChartDiagram τ O) x) := by
  have h1 := congrArg (fun m : N ⟶ (smallEtaleRingedToposHom B S hS
      (representedSpaceMap B S hS τ)).pushforwardModules.obj N' =>
    m.val.app (op ((selfOpensFunctor B S hS T).obj O)) x)
      (Adjunction.homEquiv_unit (etaleModuleAdjunction (representedSpaceMap B S hS τ)) N N' g)
  refine (congrArg (directImageSelfOpensSection τ O
    (moduleSetSheaf B S hS (yonedaSpace B S hS T') N')) h1).trans ?_
  refine (directImageSelfOpensSection_map τ O ((Sheaf.moduleSheafFunctor (testRing T')).map g)
    _).trans ?_
  exact congrArg (g.val.app (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O))))
    (directImageSelfOpensSection_etaleModuleAdjunction_unit τ O N x)

/-- The restriction map of Stacks 084A on a section over a Zariski open, as the identification
of sections of the direct image along `τ` applied to the transpose of the transposed restriction
map. -/
theorem pointRestriction_app_val_app_homEquiv
    (x : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op O)) :
    ((pointRestriction A τ f f' hf).app n).val.app (op O) x =
      directImageSelfOpensSection τ O
        ((Sheaf.moduleSheafFunctor (testRing T')).obj ((etalePointAlgebra A T' f').piece n))
        (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv
          ((etalePointAlgebra A T f).piece n) ((etalePointAlgebra A T' f').piece n)
          (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv _ _).symm
            (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
              (pointHom_comp τ hf) A n))).val.app (op ((selfOpensFunctor B S hS T).obj O)) x) := by
  refine (pointRestriction_app_val_app A τ f f' hf n O x).trans ?_
  exact congrArg (fun m : ((Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPull
          (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T))
          (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS (pointHom f))).obj A).piece n ⟶
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS τ)).pushforwardModules.obj
          (((Stacks.Sheaves.GradedAlgebraEssentiallySmall.gradedPull
          (X := smallEtaleRingedTopos B S hS (yonedaSpace B S hS T'))
          (Y := smallEtaleRingedTopos B S hS X)
          (smallEtaleRingedToposHom B S hS (pointHom f'))).obj A).piece n) =>
      directImageSelfOpensSection τ O
        ((Sheaf.moduleSheafFunctor (testRing T')).obj ((etalePointAlgebra A T' f').piece n))
        (m.val.app (op ((selfOpensFunctor B S hS T).obj O)) x))
    (Equiv.apply_symm_apply ((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv
      ((etalePointAlgebra A T f).piece n) ((etalePointAlgebra A T' f').piece n))
      (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
        (pointHom_comp τ hf) A n)).symm

/-- The restriction map of Stacks 084A on a section over a Zariski open: the transposed
restriction map applied to the unit section at the chart diagram `τ⁻¹(O) ⟶ O`. -/
theorem pointRestriction_app_val_app_unitSection
    (x : ((zariskiReading T (etalePointAlgebra A T f)).piece n).val.obj (op O)) :
    ((pointRestriction A τ f f' hf).app n).val.app (op O) x =
      (((etaleModuleAdjunction (representedSpaceMap B S hS τ)).homEquiv _ _).symm
          (gradedPullRestrictionApp (representedSpaceMap B S hS τ) (pointHom f) (pointHom f')
            (pointHom_comp τ hf) A n)).val.app
        (op ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)))
        (modulePullbackUnitSection B S hS (representedSpaceMap B S hS τ)
          ((etalePointAlgebra A T f).piece n) (preimageOpensChartDiagram τ O) x) :=
  (pointRestriction_app_val_app_homEquiv A τ f f' hf n O x).trans
    (directImageSelfOpensSection_homEquiv τ O _ _ _ x)

omit f' hf in
/-- The unit section along `τ⁻¹(O) ⟶ O` of a section of the restriction `f^*𝒜_n`, read in the
two spellings of `f^*𝒜_n`. -/
theorem modulePullbackUnitSection_etalePointAlgebra_piece
    (y : ((etalePointAlgebra A T f).piece n).val.obj (op ((selfOpensFunctor B S hS T).obj O))) :
    modulePullbackUnitSection B S hS (representedSpaceMap B S hS τ)
        ((etalePointAlgebra A T f).piece n) (preimageOpensChartDiagram τ O) y =
      modulePullbackUnitSection B S hS (representedSpaceMap B S hS τ)
        ((modulePullback B S hS (pointHom f)).obj (A.piece n)) (preimageOpensChartDiagram τ O) y :=
  rfl

/-- **The restriction maps of Stacks 084A on unit sections.**  For `τ : T' ⟶ T`, scheme points
`f` of `X` at `T` and `f' = f ∘ τ` at `T'`, a Zariski open `O` of `T`, chart diagrams
`O ⟶ W` over `f` and `τ⁻¹(O) ⟶ W'` over `f'` and a morphism of charts `k : W' ⟶ W` compatible
with them, the restriction map `f^*𝒜 ⟶ τ_*(f'^*𝒜)` (`AlgebraicGeometry.Space.pointRestriction`)
carries the unit section of a section `s` of `𝒜_n` over `W` to the unit section of `s|_{W'}`.

The restriction map is the transpose of the comparison of Stacks 03LU
(`AlgebraicGeometry.Space.homEquiv_symm_gradedPullRestrictionApp`); its value on a unit section
is that comparison applied to a unit section along `τ⁻¹(O) ⟶ O`
(`AlgebraicGeometry.Space.modulePushforwardCounitApp_preimageOpensChartDiagram`), and the
comparison of a unit section of a unit section is the unit section of the composite
(`AlgebraicGeometry.Space.modulePullbackCompIso_transport_unitSection`). -/
theorem pointRestriction_modulePullbackUnitSection {W W' : SmallEtale B S hS X.1}
    (b : (SmallEtale.toOver B S hS (yoneda.obj T)).obj ((selfOpensFunctor B S hS T).obj O) ⟶
      (SmallEtale.toOver B S hS X.1).obj W)
    (hb : ((selfOpensFunctor B S hS T).obj O).1.hom ≫ (pointHom (X := X) f).hom =
      yoneda.map b ≫ W.1.hom)
    (e : (SmallEtale.toOver B S hS (yoneda.obj T')).obj
        ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)) ⟶
      (SmallEtale.toOver B S hS X.1).obj W')
    (he : ((selfOpensFunctor B S hS T').obj (preimageOpens τ O)).1.hom ≫
        (pointHom (X := X) f').hom = yoneda.map e ≫ W'.1.hom)
    (k : W' ⟶ W)
    (hk : preimageOpensChartMap τ O ≫ b = e ≫ (SmallEtale.toOver B S hS X.1).map k)
    (s : (A.piece n).val.obj (op W)) :
    ((pointRestriction A τ f f' hf).app n).val.app (op O)
        (modulePullbackUnitSection B S hS (pointHom f) (A.piece n)
          ⟨(selfOpensFunctor B S hS T).obj O, W, b, hb⟩ s) =
      modulePullbackUnitSection B S hS (pointHom f') (A.piece n)
        ⟨(selfOpensFunctor B S hS T').obj (preimageOpens τ O), W', e, he⟩
        ((A.piece n).val.map k.op s) := by
  refine (pointRestriction_app_val_app_unitSection A τ f f' hf n O _).trans ?_
  exact homEquiv_symm_gradedPullRestrictionApp_unitSection (representedSpaceMap B S hS τ)
    (pointHom f) (pointHom f') (pointHom_comp τ hf) A n
    (U := (selfOpensFunctor B S hS T').obj (preimageOpens τ O))
    (V := (selfOpensFunctor B S hS T).obj O) (W := W) (W' := W')
    (preimageOpensChartMap τ O) b (preimageOpensChartMap_comm τ O) hb e he k hk s

omit A in
/-- The chart diagrams of a Zariski open, of its preimage, and the morphism of charts below
commute. -/
theorem preimageOpensChartDiagram_g_comp_selfOpensChartDiagram_g {V V' : SmallEtale B S hS X.1}
    (k : V' ⟶ V) (O : (chartScheme (idEtaleChart B S hS V.1.left)).Opens) :
    preimageOpensChartMap k.hom.left O ≫ (selfOpensChartDiagram V O).g =
      (selfOpensChartDiagram V' (preimageOpens k.hom.left O)).g ≫
        (SmallEtale.toOver B S hS X.1).map k := by
  refine Yoneda.fullyFaithful.map_injective ?_
  refine (Functor.map_comp yoneda _ _).trans (Eq.trans ?_ (Functor.map_comp yoneda _ _).symm)
  refine (congrArg (yoneda.map (preimageOpensChartMap k.hom.left O) ≫ ·)
    (yoneda_map_selfOpensChartDiagram_g V O)).trans ?_
  refine (yoneda_map_preimageOpensChartMap k.hom.left O).trans ?_
  exact congrArg (· ≫ yoneda.map k.hom.left)
    (yoneda_map_selfOpensChartDiagram_g V' (preimageOpens k.hom.left O)).symm

omit τ f f' hf O in
/-- **The restriction maps of Stacks 084A are the restriction of sections along morphisms of
étale charts.**  For a morphism `k : V' ⟶ V` of étale charts of `X`, with underlying
`τ : T' ⟶ T`, a Zariski open `O` of `T` and a section `a` of `𝒜_n` over `V`, the restriction map
`v^*𝒜 ⟶ τ_*(v'^*𝒜)` (`AlgebraicGeometry.Space.pointRestriction`) carries the reading of `a` on
`O` to the reading of `a|_{V'}` on `τ⁻¹(O)`. -/
theorem pointRestriction_chartOpenReading {V V' : SmallEtale B S hS X.1} (k : V' ⟶ V)
    (O : (chartScheme (idEtaleChart B S hS V.1.left)).Opens) (a : (A.piece n).val.obj (op V)) :
    ((pointRestriction A k.hom.left V.1.hom V'.1.hom (CostructuredArrow.w k.hom)).app n).val.app
        (op O) (chartOpenReading A V O n a) =
      chartOpenReading A V' (preimageOpens k.hom.left O) n ((A.piece n).val.map k.op a) :=
  pointRestriction_modulePullbackUnitSection A k.hom.left V.1.hom V'.1.hom
    (CostructuredArrow.w k.hom) n O _ (selfOpensChartDiagram V O).comm _
    (selfOpensChartDiagram V' (preimageOpens k.hom.left O)).comm k
    (preimageOpensChartDiagram_g_comp_selfOpensChartDiagram_g k O) a

end Main

end AlgebraicGeometry.Space

end

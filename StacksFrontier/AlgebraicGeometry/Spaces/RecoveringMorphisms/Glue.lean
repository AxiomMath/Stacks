module

public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheaf

/-!
# Gluing the chart morphisms `f_s` to a morphism of algebraic spaces

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces `X` and `Y`
over a terminal base scheme `S`.  For an affine étale chart `V` of `Y` and a section `s` over
an étale chart `U` of `X` of `g⁻¹h_V`, `AlgebraicGeometry.Space.OverBase.chartOverHom` is a
morphism `f_s : U ⟶ V`.  This file glues the composites `U ⟶ V ⟶ Y` to a morphism `f : X ⟶ Y` of
algebraic spaces, which is the gluing step of the proof of Stacks 04KL.

## Main results

* `AlgebraicGeometry.Space.exists_hom_of_chartFamily`: a family of points of a sheaf `G` over
  the étale charts of an algebraic space `F`, compatible with the morphisms of charts, comes
  from a morphism `F ⟶ G`.
* `AlgebraicGeometry.Space.recoveredHom'` and
  `AlgebraicGeometry.Space.isChartCompatible_recoveredHom'`: the glued morphism `f : X ⟶ Y`, and
  its compatibility with every `f_s`.

## Implementation notes

The composites `U ⟶ V ⟶ Y` are maps `g⁻¹h_V ⟶ Ŷ`, where `Ŷ` is the sheaf `U ↦ Y(U)` on the
small étale site of `X`, natural in the affine chart `V`.  By adjunction they are sections of
`g_*Ŷ` over the affine étale charts of `Y`, compatible with restriction, hence (the affine
charts being a dense subsite, Stacks 04JS) a global section of `g_*Ŷ`, whose adjoint is a map
from the terminal sheaf to `Ŷ`.  This is a compatible family of points of `Y` over the étale
charts of `X`, and such a family descends along an étale atlas.  No local existence or gluing
argument is needed: the sheaf condition is carried by the adjunction and the dense subsite.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Descending a compatible family of chart points -/

section Descent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A compatible family of points over the étale charts descends.** Let `F` be an algebraic
space and `G` a sheaf on the big fppf site of `S`.  A family of points `y U ∈ G(U)` indexed by
the étale charts `U` of `F`, compatible with the morphisms of charts, is induced by a morphism
`d : F ⟶ G`: the restriction of `d` to every chart `U` is `y U`. -/
theorem exists_hom_of_chartFamily {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (y : (U : SmallEtale B S hS F) → G.obj (op U.obj.left))
    (hy : ∀ {U U' : SmallEtale B S hS F} (i : U' ⟶ U), G.map i.hom.left.op (y U) = y U') :
    ∃ d : F ⟶ G, ∀ U : SmallEtale B S hS F, U.obj.hom ≫ d = yonedaEquiv.symm (y U) := by
  let PE := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
  let PS := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : PE.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have : PS.presheaf.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨U₀, p, hsurj, hetale⟩ := hF.exists_atlas
  let c₀ : SmallEtale B S hS F := ⟨CostructuredArrow.mk p, hetale⟩
  obtain ⟨R, s, t, hR⟩ := exists_kernelPair_of_etale_atlas B S hS p hetale
  have hs : PE.presheaf (yoneda.map s) := MorphismProperty.of_isPullback hR.flip hetale
  let r₀ : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map s ≫ p), MorphismProperty.comp_mem _ _ _ hs hetale⟩
  let is : r₀ ⟶ c₀ := ObjectProperty.homMk (CostructuredArrow.homMk s rfl)
  let it : r₀ ⟶ c₀ := ObjectProperty.homMk (CostructuredArrow.homMk t hR.w.symm)
  have key : ∀ {W C C' : SmallEtale B S hS F} (i : W ⟶ C) (j : W ⟶ C'),
      yoneda.map i.hom.left ≫ yonedaEquiv.symm (y C) =
        yoneda.map j.hom.left ≫ yonedaEquiv.symm (y C') := fun i j ↦ by
    refine yonedaEquiv.injective ?_
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    exact (hy i).trans (hy j).symm
  obtain ⟨d, hd, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hF.isSheaf p hR hsurj
    hetale hG (yonedaEquiv.symm (y c₀)) (key is it)
  refine ⟨d, fun U ↦ ?_⟩
  let hrep := hetale.rep
  let W := hrep.pullback U.obj.hom
  let a : W ⟶ U₀ := yoneda.preimage (hrep.fst U.obj.hom)
  let b : W ⟶ U.obj.left := hrep.snd U.obj.hom
  have hpb : IsPullback (yoneda.map b) (yoneda.map a) U.obj.hom p := by
    simpa only [a, b, Functor.map_preimage] using (hrep.isPullback U.obj.hom).flip
  have hbE : PE.presheaf (yoneda.map b) := MorphismProperty.of_isPullback hpb.flip hetale
  have hbS : PS.presheaf (yoneda.map b) := MorphismProperty.of_isPullback hpb.flip hsurj
  let w₀ : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map b ≫ U.obj.hom),
      MorphismProperty.comp_mem _ _ _ hbE U.property⟩
  let ib : w₀ ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk b rfl)
  let ia : w₀ ⟶ c₀ := ObjectProperty.homMk (CostructuredArrow.homMk a hpb.w.symm)
  refine hom_ext_of_etale_atlas B S hS (isSheaf_yoneda_obj B S hS U.obj.left) hG
    (yoneda.map b) hbS hbE ?_
  rw [← Category.assoc, hpb.w, Category.assoc, hd]
  exact key ia ib

end Descent

/-! ### The chart points of `g` -/

section Recovered

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (hover : IsChartOverBase g)

attribute [local instance] smallEtaleTopology_subcanonical

variable (X Y) in
/-- The sheaf `U ↦ Y(U)` on the small étale site of `X`: the morphisms from the étale charts of
`X` into the algebraic space `Y`. -/
def chartPointSheaf : Sheaf (SmallEtale.topology B S hS X.1) (Type u) :=
  ⟨(SmallEtale.toOver B S hS X.1).op ⋙ Y.1,
    SmallEtale.isSheaf_comp_toOver B S hS X.1 Y.2.isSheaf⟩

/-- For an affine étale chart `V` of `Y`, the map of sheaves `g⁻¹h_V ⟶ Ŷ` sending a section `s`
over `U` to the composite `U ⟶ V ⟶ Y`, the first map being `f_s`. -/
def chartPointMap' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    invRep g V ⟶ chartPointSheaf X Y :=
  ⟨{ app U := ↾fun s ↦ Y.1.map (OverBase.chartOverHom hover V U.unop s).op (yonedaEquiv V.obj.hom)
     naturality U U' i := by
      ext s
      change Y.1.map (OverBase.chartOverHom hover V U'.unop ((invRep g V).obj.map i s)).op _ =
        Y.1.map i.unop.hom.left.op (Y.1.map (OverBase.chartOverHom hover V U.unop s).op _)
      rw [show i = i.unop.op from rfl, OverBase.chartOverHom_restrict, op_comp,
        Functor.map_comp_apply]
      rfl }⟩

/-- The value of `g⁻¹h_V ⟶ Ŷ` at a section `s`: the composite of `f_s` with the chart `V`. -/
theorem chartPointMap_app' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (chartPointMap' g hover V).hom.app (op U) s =
      Y.1.map (OverBase.chartOverHom hover V U s).op (yonedaEquiv V.obj.hom) :=
  rfl

/-- The maps `g⁻¹h_V ⟶ Ŷ` are natural in the affine chart `V`. -/
theorem map_comp_chartPointMap' {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (c : V' ⟶ V) :
    g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map c) ≫
      chartPointMap' g hover V = chartPointMap' g hover V' := by
  apply Sheaf.hom_ext
  ext U s
  show Y.1.map (OverBase.chartOverHom hover V U.unop ((g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U.unop) s)).op _ =
    Y.1.map (OverBase.chartOverHom hover V' U.unop s).op _
  rw [OverBase.chartOverHom_map, op_comp, Functor.map_comp_apply, yonedaEquiv_naturality]
  congr 2
  exact CostructuredArrow.w c.hom

/-- The section of `g_*Ŷ` over an affine chart `V` of `Y` adjoint to `g⁻¹h_V ⟶ Ŷ`. -/
def chartPointSection' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj.obj (op V) :=
  (SmallEtale.topology B S hS Y.1).yonedaEquiv
    (g.toToposHom.adj.homEquiv _ _ (chartPointMap' g hover V))

/-- The sections of `g_*Ŷ` over the affine charts are compatible with restriction. -/
theorem chartPointSection_restrict' {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (c : V' ⟶ V) :
    (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj.map c.op
      (chartPointSection' g hover V) = chartPointSection' g hover V' := by
  rw [chartPointSection', GrothendieckTopology.yonedaEquiv_naturality,
    ← Adjunction.homEquiv_naturality_left, map_comp_chartPointMap']
  rfl

/-- The sections of `g_*Ŷ` over the affine charts of `Y`, as a map of presheaves on the affine
étale site out of the terminal presheaf. -/
def chartPointSectionsAffine' :
    (AffineEtale.inclusion B S hS Y.1).op ⋙ (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
      (Type u)).obj ⟶
      (AffineEtale.inclusion B S hS Y.1).op ⋙
        (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj where
  app V := ↾fun _ ↦
    haveI : IsAffine (chartSch V.unop.obj) := V.unop.property
    chartPointSection' g hover V.unop.obj
  naturality V V' c := by
    ext x
    have : IsAffine (chartSch V.unop.obj) := V.unop.property
    have : IsAffine (chartSch V'.unop.obj) := V'.unop.property
    exact (chartPointSection_restrict' g hover c.unop.hom).symm

/-- The global section of `g_*Ŷ` glued from the sections over the affine charts of `Y`. -/
def chartPointGlobalSection' :
    ⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⟶
      g.toToposHom.pushforward.obj (chartPointSheaf X Y) :=
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  ⟨Functor.IsCoverDense.restrictHomEquivHom (chartPointSectionsAffine' g hover)⟩

/-- Over an affine chart, the glued global section is the section attached to that chart. -/
theorem chartPointGlobalSection_app' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (x : (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)).obj.obj (op V)) :
    (chartPointGlobalSection' g hover).hom.app (op V) x = chartPointSection' g hover V := by
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have h := congr_app ((Functor.IsCoverDense.restrictHomEquivHom
    (G := AffineEtale.inclusion B S hS Y.1)
    (ℱ' := g.toToposHom.pushforward.obj (chartPointSheaf X Y))).symm_apply_apply
      (chartPointSectionsAffine' g hover))
    (op (⟨V, (inferInstance : IsAffine (chartSch V))⟩ : AffineEtale B S hS Y.1))
  exact ConcreteCategory.congr_hom h x

/-- The map from the terminal sheaf to `Ŷ` adjoint to the glued global section. -/
def chartPointFamily' : g.toToposHom.inverseImage.obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
    (Type u)) ⟶ chartPointSheaf X Y :=
  (g.toToposHom.adj.homEquiv _ _).symm (chartPointGlobalSection' g hover)

/-- The sections of the inverse image of the terminal sheaf are singletons. -/
instance uniqueInverseImageTerminal (U : SmallEtale B S hS X.1) :
    Unique ((g.toToposHom.inverseImage.obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
      (Type u))).obj.obj (op U)) :=
  have hF : PreservesFiniteProducts g.toToposHom.inverseImage :=
    ⟨fun n => g.toToposHom.preservesFiniteLimits.preservesFiniteLimits (Discrete (Fin n))⟩
  have hG : PreservesFiniteProducts
      (Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) (op U)) := inferInstance
  @Functor.uniqueTerminalObj _ _
    (inferInstanceAs (HasFiniteProducts (Sheaf (SmallEtale.topology B S hS Y.1) (Type u))))
    (g.toToposHom.inverseImage ⋙ Sheaf.sectionsFunctor (SmallEtale.topology B S hS X.1) (op U))
    (@comp_preservesFiniteProducts _ _ _ _ _ _ _ _ hF hG)

/-- **The point of `Y` over an étale chart `U` of `X` recovered from `g`.** -/
def recoveredPoint' (U : SmallEtale B S hS X.1) : Y.1.obj (op U.obj.left) :=
  (chartPointFamily' g hover).hom.app (op U) default

/-- The recovered points are compatible with the morphisms of charts. -/
theorem recoveredPoint_restrict' {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U) :
    Y.1.map i.hom.left.op (recoveredPoint' g hover U) = recoveredPoint' g hover U' := by
  refine (ConcreteCategory.congr_hom ((chartPointFamily' g hover).hom.naturality i.op)
    default).symm.trans ?_
  exact congrArg ((chartPointFamily' g hover).hom.app (op U')) (Subsingleton.elim _ _)

/-- **The recovered point over `U` is the composite `U ⟶ V ⟶ Y` for every section `s` over
`U` of `g⁻¹h_V`**, `V` an affine étale chart of `Y`. -/
theorem recoveredPoint_eq' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    recoveredPoint' g hover U = (chartPointMap' g hover V).hom.app (op U) s := by
  let k := terminal.from ((SmallEtale.topology B S hS Y.1).yoneda.obj V)
  have hk : k ≫ chartPointGlobalSection' g hover =
      g.toToposHom.adj.homEquiv _ _ (chartPointMap' g hover V) := by
    apply (SmallEtale.topology B S hS Y.1).yonedaEquiv.injective
    rw [GrothendieckTopology.yonedaEquiv_comp, chartPointGlobalSection_app']
    rfl
  have h :
      g.toToposHom.inverseImage.map k ≫ chartPointFamily' g hover = chartPointMap' g hover V := by
    rw [chartPointFamily', ← Adjunction.homEquiv_naturality_left_symm, hk,
      Equiv.symm_apply_apply]
  rw [← h]
  exact congrArg ((chartPointFamily' g hover).hom.app (op U)) (Subsingleton.elim _ _)

/-- **The morphism of algebraic spaces recovered from `g`**: the descent of the recovered
points along the étale charts of `X`. -/
def recoveredHom' : X ⟶ Y :=
  ObjectProperty.homMk (Classical.choose (exists_hom_of_chartFamily B S hS X.2 Y.2.isSheaf
    (recoveredPoint' g hover) (fun i ↦ recoveredPoint_restrict' g hover i)))

/-- The recovered morphism restricts on every étale chart `U` of `X` to the recovered point
over `U`. -/
theorem chart_comp_recoveredHom' (U : SmallEtale B S hS X.1) :
    U.obj.hom ≫ (recoveredHom' g hover).hom = yonedaEquiv.symm (recoveredPoint' g hover U) :=
  Classical.choose_spec (exists_hom_of_chartFamily B S hS X.2 Y.2.isSheaf
    (recoveredPoint' g hover) (fun i ↦ recoveredPoint_restrict' g hover i)) U

/-- **The recovered morphism is compatible with every chart morphism `f_s`.** -/
theorem isChartCompatible_recoveredHom' :
    OverBase.IsChartCompatible hover (recoveredHom' g hover) := by
  intro V _ U s
  rw [chart_comp_recoveredHom', recoveredPoint_eq' g hover V U s, chartPointMap_app',
    yonedaEquiv_naturality, Equiv.symm_apply_apply]

/-- **Stacks 04KL, the gluing step.** For a terminal base scheme, every morphism of the small
étale ringed topoi of two algebraic spaces admits a morphism of algebraic spaces compatible
with all its chart morphisms `f_s`. -/
theorem exists_isChartCompatible' : ∃ f : X ⟶ Y, OverBase.IsChartCompatible hover f :=
  ⟨recoveredHom' g hover, isChartCompatible_recoveredHom' g hover⟩

end Recovered

/-! ### The original forms, over a terminal base

The declarations of this section are the forms over a terminal base `S`, with
`hS₀ : IsTerminal S` as their hypothesis on the base. The primed declarations above are the same
constructions under `hover : AlgebraicGeometry.Space.IsChartOverBase g`, which
`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` derives from `hS₀`. -/

section RecoveredBaseForm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (hS₀ : IsTerminal S)
  {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

attribute [local instance] smallEtaleTopology_subcanonical

/-- For an affine étale chart `V` of `Y`, the map of sheaves `g⁻¹h_V ⟶ Ŷ` sending a section `s`
over `U` to the composite `U ⟶ V ⟶ Y`, the first map being `f_s`. -/
def chartPointMap (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    invRep g V ⟶ chartPointSheaf X Y :=
  ⟨{ app U := ↾fun s ↦ Y.1.map (chartOverHom hS₀ g V U.unop s).op (yonedaEquiv V.obj.hom)
     naturality U U' i := by
      ext s
      change Y.1.map (chartOverHom hS₀ g V U'.unop ((invRep g V).obj.map i s)).op _ =
        Y.1.map i.unop.hom.left.op (Y.1.map (chartOverHom hS₀ g V U.unop s).op _)
      rw [show i = i.unop.op from rfl, chartOverHom_restrict, op_comp,
        Functor.map_comp_apply]
      rfl }⟩

/-- The value of `g⁻¹h_V ⟶ Ŷ` at a section `s`: the composite of `f_s` with the chart `V`. -/
theorem chartPointMap_app (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    (chartPointMap hS₀ g V).hom.app (op U) s =
      Y.1.map (chartOverHom hS₀ g V U s).op (yonedaEquiv V.obj.hom) :=
  rfl

/-- The maps `g⁻¹h_V ⟶ Ŷ` are natural in the affine chart `V`. -/
theorem map_comp_chartPointMap {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (c : V' ⟶ V) :
    g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map c) ≫
      chartPointMap hS₀ g V = chartPointMap hS₀ g V' := by
  apply Sheaf.hom_ext
  ext U s
  show Y.1.map (chartOverHom hS₀ g V U.unop ((g.toToposHom.inverseImage.map
      ((SmallEtale.topology B S hS Y.1).yoneda.map c)).hom.app (op U.unop) s)).op _ =
    Y.1.map (chartOverHom hS₀ g V' U.unop s).op _
  rw [chartOverHom_map, op_comp, Functor.map_comp_apply, yonedaEquiv_naturality]
  congr 2
  exact CostructuredArrow.w c.hom

/-- The section of `g_*Ŷ` over an affine chart `V` of `Y` adjoint to `g⁻¹h_V ⟶ Ŷ`. -/
def chartPointSection (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] :
    (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj.obj (op V) :=
  (SmallEtale.topology B S hS Y.1).yonedaEquiv
    (g.toToposHom.adj.homEquiv _ _ (chartPointMap hS₀ g V))

/-- The sections of `g_*Ŷ` over the affine charts are compatible with restriction. -/
theorem chartPointSection_restrict {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (c : V' ⟶ V) :
    (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj.map c.op
      (chartPointSection hS₀ g V) = chartPointSection hS₀ g V' := by
  rw [chartPointSection, GrothendieckTopology.yonedaEquiv_naturality,
    ← Adjunction.homEquiv_naturality_left, map_comp_chartPointMap]
  rfl

/-- The sections of `g_*Ŷ` over the affine charts of `Y`, as a map of presheaves on the affine
étale site out of the terminal presheaf. -/
def chartPointSectionsAffine :
    (AffineEtale.inclusion B S hS Y.1).op ⋙ (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
      (Type u)).obj ⟶
      (AffineEtale.inclusion B S hS Y.1).op ⋙
        (g.toToposHom.pushforward.obj (chartPointSheaf X Y)).obj where
  app V := ↾fun _ ↦
    haveI : IsAffine (chartSch V.unop.obj) := V.unop.property
    chartPointSection hS₀ g V.unop.obj
  naturality V V' c := by
    ext x
    have : IsAffine (chartSch V.unop.obj) := V.unop.property
    have : IsAffine (chartSch V'.unop.obj) := V'.unop.property
    exact (chartPointSection_restrict hS₀ g c.unop.hom).symm

/-- The global section of `g_*Ŷ` glued from the sections over the affine charts of `Y`. -/
def chartPointGlobalSection :
    ⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u) ⟶
      g.toToposHom.pushforward.obj (chartPointSheaf X Y) :=
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  ⟨Functor.IsCoverDense.restrictHomEquivHom (chartPointSectionsAffine hS₀ g)⟩

/-- Over an affine chart, the glued global section is the section attached to that chart. -/
theorem chartPointGlobalSection_app (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (x : (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)).obj.obj (op V)) :
    (chartPointGlobalSection hS₀ g).hom.app (op V) x = chartPointSection hS₀ g V := by
  have := (AffineEtale.inclusion_isSpecialCocontinuous B S hS Y.1 Y.2).2
  have := Functor.IsDenseSubsite.isCoverDense (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have := Functor.IsDenseSubsite.isLocallyFull (AffineEtale.topology B S hS Y.1)
    (SmallEtale.topology B S hS Y.1) (AffineEtale.inclusion B S hS Y.1)
  have h := congr_app ((Functor.IsCoverDense.restrictHomEquivHom
    (G := AffineEtale.inclusion B S hS Y.1)
    (ℱ' := g.toToposHom.pushforward.obj (chartPointSheaf X Y))).symm_apply_apply
      (chartPointSectionsAffine hS₀ g))
    (op (⟨V, (inferInstance : IsAffine (chartSch V))⟩ : AffineEtale B S hS Y.1))
  exact ConcreteCategory.congr_hom h x

/-- The map from the terminal sheaf to `Ŷ` adjoint to the glued global section. -/
def chartPointFamily : g.toToposHom.inverseImage.obj (⊤_ Sheaf (SmallEtale.topology B S hS Y.1)
    (Type u)) ⟶ chartPointSheaf X Y :=
  (g.toToposHom.adj.homEquiv _ _).symm (chartPointGlobalSection hS₀ g)

/-- **The point of `Y` over an étale chart `U` of `X` recovered from `g`.** -/
def recoveredPoint (U : SmallEtale B S hS X.1) : Y.1.obj (op U.obj.left) :=
  (chartPointFamily hS₀ g).hom.app (op U) default

/-- The recovered points are compatible with the morphisms of charts. -/
theorem recoveredPoint_restrict {U U' : SmallEtale B S hS X.1} (i : U' ⟶ U) :
    Y.1.map i.hom.left.op (recoveredPoint hS₀ g U) = recoveredPoint hS₀ g U' := by
  refine (ConcreteCategory.congr_hom ((chartPointFamily hS₀ g).hom.naturality i.op)
    default).symm.trans ?_
  exact congrArg ((chartPointFamily hS₀ g).hom.app (op U')) (Subsingleton.elim _ _)

/-- **The recovered point over `U` is the composite `U ⟶ V ⟶ Y` for every section `s` over
`U` of `g⁻¹h_V`**, `V` an affine étale chart of `Y`. -/
theorem recoveredPoint_eq (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) :
    recoveredPoint hS₀ g U = (chartPointMap hS₀ g V).hom.app (op U) s := by
  let k := terminal.from ((SmallEtale.topology B S hS Y.1).yoneda.obj V)
  have hk : k ≫ chartPointGlobalSection hS₀ g =
      g.toToposHom.adj.homEquiv _ _ (chartPointMap hS₀ g V) := by
    apply (SmallEtale.topology B S hS Y.1).yonedaEquiv.injective
    rw [GrothendieckTopology.yonedaEquiv_comp, chartPointGlobalSection_app]
    rfl
  have h : g.toToposHom.inverseImage.map k ≫ chartPointFamily hS₀ g = chartPointMap hS₀ g V := by
    rw [chartPointFamily, ← Adjunction.homEquiv_naturality_left_symm, hk,
      Equiv.symm_apply_apply]
  rw [← h]
  exact congrArg ((chartPointFamily hS₀ g).hom.app (op U)) (Subsingleton.elim _ _)

/-- **The morphism of algebraic spaces recovered from `g`**: the descent of the recovered
points along the étale charts of `X`. -/
def recoveredHom : X ⟶ Y :=
  ObjectProperty.homMk (Classical.choose (exists_hom_of_chartFamily B S hS X.2 Y.2.isSheaf
    (recoveredPoint hS₀ g) (fun i ↦ recoveredPoint_restrict hS₀ g i)))

/-- The recovered morphism restricts on every étale chart `U` of `X` to the recovered point
over `U`. -/
theorem chart_comp_recoveredHom (U : SmallEtale B S hS X.1) :
    U.obj.hom ≫ (recoveredHom hS₀ g).hom = yonedaEquiv.symm (recoveredPoint hS₀ g U) :=
  Classical.choose_spec (exists_hom_of_chartFamily B S hS X.2 Y.2.isSheaf
    (recoveredPoint hS₀ g) (fun i ↦ recoveredPoint_restrict hS₀ g i)) U

/-- **The recovered morphism is compatible with every chart morphism `f_s`.** -/
theorem isChartCompatible_recoveredHom : IsChartCompatible hS₀ g (recoveredHom hS₀ g) := by
  intro V _ U s
  rw [chart_comp_recoveredHom, recoveredPoint_eq hS₀ g V U s, chartPointMap_app,
    yonedaEquiv_naturality, Equiv.symm_apply_apply]

/-- **Stacks 04KL, the gluing step.** For a terminal base scheme, every morphism of the small
étale ringed topoi of two algebraic spaces admits a morphism of algebraic spaces compatible
with all its chart morphisms `f_s`. -/
theorem exists_isChartCompatible : ∃ f : X ⟶ Y, IsChartCompatible hS₀ g f :=
  ⟨recoveredHom hS₀ g, isChartCompatible_recoveredHom hS₀ g⟩

end RecoveredBaseForm

end AlgebraicGeometry.Space

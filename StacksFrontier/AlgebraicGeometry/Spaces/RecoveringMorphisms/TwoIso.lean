module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartComparison

/-!
# The 2-isomorphism of Stacks 04KL from the chart comparison

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces over a
terminal scheme, and let `f : X ⟶ Y` be a morphism of algebraic spaces compatible with the
charts of `g` (`AlgebraicGeometry.Space.OverBase.IsChartCompatible`). For every affine étale
chart `V` of `Y` there is then the comparison `g⁻¹h_V ⟶ chartFiber f V`
(`AlgebraicGeometry.Space.OverBase.invRepComparison`). This file shows that if each of these
comparisons is a local isomorphism, then `(g, g♯)` is 2-isomorphic to `(f_small, f♯)`: this is
the last step of the proof of Stacks 04KL.

Over an affine chart `V` of `Y`, a section over `V` of the direct image along `g` of a sheaf `F`
is a map `g⁻¹h_V ⟶ F`, and a section of the direct image along `f` is a map out of the presheaf
`chartFiber f V` (`AlgebraicGeometry.Space.sectionEquivChartFiberHom`).  A local isomorphism
between the two sources identifies these sets of maps; the identifications are natural in `F`
and in the affine chart `V`, so they glue, the affine charts being a dense subsite.

## Main definitions

* `AlgebraicGeometry.Space.chartFiberMap`: postcomposition of chart maps over `f` with a
  morphism of étale charts of `Y`.
* `AlgebraicGeometry.Space.chartSectionEquiv'`: the bijection `(g_*F)(V) ≃ (f_*F)(V)` over an
  affine chart `V`.
* `AlgebraicGeometry.Space.pushforwardIsoOfChartComparison'`: the isomorphism `g_* ≅ f_*` of
  direct images glued from these bijections.
* `AlgebraicGeometry.Space.twoIsoOfChartComparison'`: the 2-isomorphism of morphisms of ringed
  topoi `(g, g♯) ≅ (f_small, f♯)`.

## Main results

* `AlgebraicGeometry.Space.sectionEquivChartFiberHom_restrict`: the description of the sections
  of `f_*F` by maps out of `chartFiber f V` is natural in an affine chart `V`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

/-! ### Chart maps over `f` and morphisms of charts of the target -/

section ChartFiberMap

variable (f : X ⟶ Y)

/-- Postcomposition of the chart maps over `f` with a morphism `j : V' ⟶ V` of étale charts of
`Y`. -/
def chartFiberMap {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V) :
    (chartFiber B S hS f V').toFunctor ⟶ (chartFiber B S hS f V).toFunctor where
  app U := ↾fun c ↦ ⟨c.1 ≫ j.hom.left, by
    change U.unop.1.hom ≫ f.hom = yoneda.map (c.1 ≫ j.hom.left) ≫ V.1.hom
    rw [Functor.map_comp, Category.assoc, CostructuredArrow.w j.hom]
    exact c.2⟩
  naturality U U' i := by
    ext c
    exact Subtype.ext (Category.assoc _ _ _)

/-- The chart map underlying the postcomposition of a chart map with `j`. -/
@[simp]
theorem chartFiberMap_app_val {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (c : (chartFiber B S hS f V').toFunctor.obj U) :
    ((chartFiberMap f j).app U c).val = c.val ≫ j.hom.left :=
  rfl

/-- Pulling back a regular function along a chart map postcomposed with `j` is pulling back its
restriction along `j`. -/
theorem chartFiberMap_comp_chartFiberCoordinate {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    chartFiberMap f j ≫ chartFiberCoordinate B S hS f V b =
      chartFiberCoordinate B S hS f V' ((structureSetSheaf B S hS Y).obj.map j.op b) := by
  ext U c
  show (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (c.val ≫ j.hom.left)).op) b = (forget CommRingCat.{u}).map (Scheme.Γ.map
      ((BigFppfOver.toScheme B S hS).map c.val).op)
      ((forget CommRingCat.{u}).map (Scheme.Γ.map
        ((BigFppfOver.toScheme B S hS).map j.hom.left).op) b)
  rw [Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- The direct image along `f` of sheaves of sets on the small étale sites. -/
abbrev fPush : Sheaf (SmallEtale.topology B S hS X.1) (Type u) ⥤
    Sheaf (SmallEtale.topology B S hS Y.1) (Type u) :=
  (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward

/-- The structure map of `f` on a regular function on `V` corresponds to the coordinate of that
function, as a map out of `chartFiber f V`. -/
private theorem sectionEquiv_forgetFSharp (V : SmallEtale B S hS Y.1)
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    sectionEquivChartFiberHom B S hS f V (structureSetSheaf B S hS X)
        ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b) =
      chartFiberCoordinate B S hS f V b :=
  sectionEquivChartFiberHom_fSharp B S hS f V b

-- The product instances on sheaves of sets need more than the default budget under Lean v4.35.0.
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The description of the sections of `f_*F` by maps out of `chartFiber f V` is natural in
`V`**, for `V` affine: restricting a section along `j : V' ⟶ V` precomposes the corresponding
map with postcomposition by `j`.

The sections of `f_*` over `V` are corepresented, among sheaves, by the subsheaf `Q` of a
product of copies of `𝒪_X` generated by `chartFiber f V`; so it suffices to treat the universal
section, whose image under restriction is detected by its coordinates, and those are computed
by the structure map. -/
theorem sectionEquivChartFiberHom_restrict {V V' : SmallEtale B S hS Y.1}
    [IsAffine (chartSch V)] (j : V' ⟶ V) (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (y : ((fPush f).obj F).obj.obj (op V)) :
    sectionEquivChartFiberHom B S hS f V' F (((fPush f).obj F).obj.map j.op y) =
      chartFiberMap f j ≫ sectionEquivChartFiberHom B S hS f V F y := by
  let E := sectionEquivChartFiberHom B S hS f
  let D := fun _ : (structureSetSheaf B S hS Y).obj.obj (op V) => structureSetSheaf B S hS X
  let m := chartCoordinateMap B S hS f V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left) := ‹_›
  let Q := sheafOfMono m
  let u := sheafOfMonoUnit m
  let x₀ := (E V Q).symm u
  let φ := sheafOfMonoLift m (E V F y)
  have hy : ((fPush f).map φ).hom.app (op V) x₀ = y := by
    apply (E V F).injective
    rw [sectionEquivChartFiberHom_naturality, Equiv.apply_symm_apply, sheafOfMonoUnit_lift]
  have hr : ∀ {G H : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (q : G ⟶ H)
      (z : ((fPush f).obj G).obj.obj (op V)),
      ((fPush f).obj H).obj.map j.op (((fPush f).map q).hom.app (op V) z) =
        ((fPush f).map q).hom.app (op V') (((fPush f).obj G).obj.map j.op z) := fun q z ↦
    (ConcreteCategory.congr_hom (((fPush f).map q).hom.naturality j.op) z).symm
  have hK : E V' Q (((fPush f).obj Q).obj.map j.op x₀) = chartFiberMap f j ≫ u := by
    have hmono : Mono (sheafOfMonoι m).hom := by
      show Mono (((Subfunctor.range m).sheafify _).ι)
      infer_instance
    refine (cancel_mono (sheafOfMonoι m).hom).1 ?_
    refine (cancel_mono (piComparison (sheafToPresheaf (SmallEtale.topology B S hS X.1)
      (Type u)) D)).1 (Pi.hom_ext _ _ fun b ↦ ?_)
    simp only [Category.assoc, piComparison_comp_π]
    have h1 : ((fPush f).map (sheafOfMonoι m ≫ Pi.π D b)).hom.app (op V) x₀ =
        (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b := by
      apply (E V _).injective
      rw [sectionEquivChartFiberHom_naturality, Equiv.apply_symm_apply, sectionEquiv_forgetFSharp,
        ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, sheafOfMonoUnit_ι]
      exact chartCoordinateMap_π B S hS f V b
    have h2 : E V' _ (((fPush f).map (sheafOfMonoι m ≫ Pi.π D b)).hom.app (op V')
        (((fPush f).obj Q).obj.map j.op x₀)) =
        E V' Q (((fPush f).obj Q).obj.map j.op x₀) ≫ (sheafOfMonoι m).hom ≫ (Pi.π D b).hom := by
      rw [sectionEquivChartFiberHom_naturality]
      rfl
    refine h2.symm.trans ?_
    have h3 := ConcreteCategory.congr_hom
      ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.naturality j.op) b
    change (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V')
        ((structureSetSheaf B S hS Y).obj.map j.op b) =
      ((fPush f).obj (structureSetSheaf B S hS X)).obj.map j.op
      ((RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b) at h3
    rw [← hr, h1, ← h3, sectionEquiv_forgetFSharp, ← chartFiberMap_comp_chartFiberCoordinate,
      ← chartCoordinateMap_π B S hS f V b, ← Category.assoc (sheafOfMonoUnit m),
      sheafOfMonoUnit_ι]
  calc E V' F (((fPush f).obj F).obj.map j.op y)
      = E V' F (((fPush f).obj F).obj.map j.op (((fPush f).map φ).hom.app (op V) x₀)) := by
        rw [hy]
    _ = chartFiberMap f j ≫ u ≫ φ.hom := by
        rw [hr, sectionEquivChartFiberHom_naturality, hK, Category.assoc]
    _ = chartFiberMap f j ≫ E V F y := by
        rw [sheafOfMonoUnit_lift]

end ChartFiberMap

/-! ### Sections of the direct image along `g` -/

section Comparison

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {hover : IsChartOverBase g}

variable (g) in
/-- The sections over `V` of the direct image along `g` of a sheaf `F` are the maps
`g⁻¹h_V ⟶ F`, read as maps of presheaves. -/
def invSectionEquiv (V : SmallEtale B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (g.toToposHom.pushforward.obj F).obj.obj (op V) ≃ ((invRep g V).obj ⟶ F.obj) :=
  (SmallEtale.topology B S hS Y.1).yonedaEquiv.symm.trans
    ((g.toToposHom.adj.homEquiv _ _).symm.trans Sheaf.homEquiv)

/-- `AlgebraicGeometry.Space.invSectionEquiv` on a section: the adjoint of the map `h_V ⟶ g_*F`
it corresponds to. -/
theorem invSectionEquiv_apply (V : SmallEtale B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    invSectionEquiv g V F x = ((g.toToposHom.adj.homEquiv _ _).symm
      ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x)).hom :=
  rfl

/-- `AlgebraicGeometry.Space.invSectionEquiv` is natural in the sheaf. -/
theorem invSectionEquiv_naturality (V : SmallEtale B S hS Y.1)
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (q : F ⟶ G)
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    invSectionEquiv g V G ((g.toToposHom.pushforward.map q).hom.app (op V) x) =
      invSectionEquiv g V F x ≫ q.hom := by
  have h1 := GrothendieckTopology.yonedaEquiv_symm_naturality_right
    (SmallEtale.topology B S hS Y.1) V (g.toToposHom.pushforward.map q) x
  rw [invSectionEquiv_apply, invSectionEquiv_apply, ← h1,
    Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- `AlgebraicGeometry.Space.invSectionEquiv` is natural in the chart of the target. -/
theorem invSectionEquiv_restrict {V V' : SmallEtale B S hS Y.1} (j : V' ⟶ V)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    invSectionEquiv g V' F ((g.toToposHom.pushforward.obj F).obj.map j.op x) =
      (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map j)).hom ≫
        invSectionEquiv g V F x := by
  have h1 := GrothendieckTopology.yonedaEquiv_symm_naturality_left
    (SmallEtale.topology B S hS Y.1) j (g.toToposHom.pushforward.obj F) x
  rw [invSectionEquiv_apply, invSectionEquiv_apply, ← h1,
    Adjunction.homEquiv_naturality_left_symm]
  rfl

variable {f : X ⟶ Y} (hf : OverBase.IsChartCompatible hover f)

/-- The comparison `g⁻¹h_V ⟶ chartFiber f V` is natural in the affine chart `V`. -/
theorem invRepComparison_naturality' {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V) :
    (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map j)).hom ≫
        OverBase.invRepComparison hf V =
      OverBase.invRepComparison hf V' ≫ chartFiberMap f j := by
  ext U s
  exact Subtype.ext (OverBase.chartOverHom_map hover U.unop j s)

/-- The coordinate of `b` along the comparison is the coordinate map attached to `b` by `g`. -/
theorem invRepComparison_comp_chartFiberCoordinate' (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    OverBase.invRepComparison hf V ≫ chartFiberCoordinate B S hS f V b = (invCoord g V b).hom := by
  ext U s
  show (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (OverBase.chartOverHom hover V U.unop s)).op) b = _
  rw [OverBase.toScheme_map_chartOverHom, Scheme.Γ_map_op, chartSchemeHom_appTop]
  exact chartRingHom_apply g V U.unop s b

variable (hW : ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)],
  (SmallEtale.topology B S hS X.1).W (OverBase.invRepComparison hf V))

/-- **The bijection `(g_*F)(V) ≃ (f_*F)(V)`** over an affine étale chart `V` of `Y`: both sets
are sets of maps of presheaves, out of `g⁻¹h_V` and out of `chartFiber f V`, and the comparison
`g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism. -/
def chartSectionEquiv' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (g.toToposHom.pushforward.obj F).obj.obj (op V) ≃ ((fPush f).obj F).obj.obj (op V) :=
  (invSectionEquiv g V F).trans (((hW V).homEquiv F.obj F.property).symm.trans
    (sectionEquivChartFiberHom B S hS f V F).symm)

/-- The defining property of `AlgebraicGeometry.Space.chartSectionEquiv'`. -/
theorem invRepComparison_comp_chartSectionEquiv' (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    OverBase.invRepComparison hf V ≫
        sectionEquivChartFiberHom B S hS f V F (chartSectionEquiv' hf hW V F x) =
      invSectionEquiv g V F x := by
  rw [chartSectionEquiv', Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact ((hW V).homEquiv F.obj F.property).apply_symm_apply _

/-- `AlgebraicGeometry.Space.chartSectionEquiv'` is characterized by its defining property. -/
theorem chartSectionEquiv_eq_iff' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V))
    (y : ((fPush f).obj F).obj.obj (op V)) :
    chartSectionEquiv' hf hW V F x = y ↔
      OverBase.invRepComparison hf V ≫ sectionEquivChartFiberHom B S hS f V F y =
        invSectionEquiv g V F x := by
  constructor
  · rintro rfl
    exact invRepComparison_comp_chartSectionEquiv' hf hW V F x
  · intro h
    apply (sectionEquivChartFiberHom B S hS f V F).injective
    apply ((hW V).homEquiv F.obj F.property).injective
    show OverBase.invRepComparison hf V ≫ _ = OverBase.invRepComparison hf V ≫ _
    rw [invRepComparison_comp_chartSectionEquiv', h]

/-- `AlgebraicGeometry.Space.chartSectionEquiv'` is natural in the sheaf. -/
theorem chartSectionEquiv_naturality' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (q : F ⟶ G)
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    chartSectionEquiv' hf hW V G ((g.toToposHom.pushforward.map q).hom.app (op V) x) =
      ((fPush f).map q).hom.app (op V) (chartSectionEquiv' hf hW V F x) := by
  rw [chartSectionEquiv_eq_iff', sectionEquivChartFiberHom_naturality, ← Category.assoc,
    invRepComparison_comp_chartSectionEquiv', invSectionEquiv_naturality]

/-- `AlgebraicGeometry.Space.chartSectionEquiv'` is natural in the affine chart. -/
theorem chartSectionEquiv_restrict' {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V) (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    chartSectionEquiv' hf hW V' F ((g.toToposHom.pushforward.obj F).obj.map j.op x) =
      ((fPush f).obj F).obj.map j.op (chartSectionEquiv' hf hW V F x) := by
  rw [chartSectionEquiv_eq_iff', sectionEquivChartFiberHom_restrict, ← Category.assoc,
    ← invRepComparison_naturality', Category.assoc, invRepComparison_comp_chartSectionEquiv',
    invSectionEquiv_restrict]

/-- The structure map of `g` corresponds to the structure map of `f`. -/
theorem chartSectionEquiv_forgetFSharp' (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    chartSectionEquiv' hf hW V (structureSetSheaf B S hS X)
        ((RingedToposHom.forgetFSharp g).hom.app (op V) b) =
      (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b := by
  refine (chartSectionEquiv_eq_iff' hf hW V (structureSetSheaf B S hS X) _ _).2 ?_
  refine ((congrArg (OverBase.invRepComparison hf V ≫ ·) (sectionEquiv_forgetFSharp f V b)).trans
    (invRepComparison_comp_chartFiberCoordinate' hf V b)).trans ?_
  exact (congrArg (fun φ ↦ φ.hom) (homEquiv_symm_forgetFSharp g V b)).symm

/-! ### Gluing over the affine charts -/

/-- The inclusion of the affine étale charts of an algebraic space into all its étale charts is a
dense subsite (Stacks 04JS). -/
theorem affineEtaleInclusion_isDenseSubsite (Z : AlgebraicSpaces B S hS) :
    (AffineEtale.inclusion B S hS Z.1).IsDenseSubsite (AffineEtale.topology B S hS Z.1)
      (SmallEtale.topology B S hS Z.1) :=
  (AffineEtale.inclusion_isSpecialCocontinuous B S hS Z.1 Z.2).2

attribute [local instance] affineEtaleInclusion_isDenseSubsite

/-- The bijections `AlgebraicGeometry.Space.chartSectionEquiv'`, as an isomorphism of the
restrictions of `g_*F` and `f_*F` to the affine étale charts of `Y`. -/
def affinePushforwardIso' (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).obj
        (g.toToposHom.pushforward.obj F) ≅
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).obj ((fPush f).obj F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun W ↦
      haveI : IsAffine (chartSch W.unop.obj) := W.unop.property
      (chartSectionEquiv' hf hW W.unop.obj F).toIso)
    (by
      intro W W' k
      have : IsAffine (chartSch W.unop.obj) := W.unop.property
      have : IsAffine (chartSch W'.unop.obj) := W'.unop.property
      ext x
      exact chartSectionEquiv_restrict' hf hW k.unop.hom F x))

/-- The components of `AlgebraicGeometry.Space.affinePushforwardIso'` are the bijections
`AlgebraicGeometry.Space.chartSectionEquiv'`. -/
theorem affinePushforwardIso_hom_app (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (W : AffineEtale B S hS Y.1) (x : (g.toToposHom.pushforward.obj F).obj.obj (op W.obj)) :
    haveI : IsAffine (chartSch W.obj) := W.property
    (affinePushforwardIso' hf hW F).hom.hom.app (op W) x = chartSectionEquiv' hf hW W.obj F x :=
  rfl

/-- **The isomorphism `g_* ≅ f_*` of direct images**, glued from the bijections
`AlgebraicGeometry.Space.chartSectionEquiv'` over the affine étale charts of `Y`, which are a
dense subsite. -/
def pushforwardIsoOfChartComparison' :
    g.toToposHom.pushforward ≅ fPush f :=
  ((Functor.FullyFaithful.ofFullyFaithful
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1))).whiskeringRight
    (Sheaf (SmallEtale.topology B S hS X.1) (Type u))).preimageIso
    (NatIso.ofComponents (affinePushforwardIso' hf hW) (by
      intro F G q
      apply Sheaf.hom_ext
      ext W x
      have : IsAffine (chartSch W.unop.obj) := W.unop.property
      exact chartSectionEquiv_naturality' hf hW W.unop.obj q x))

/-- Restricted to the affine étale charts of `Y`, the isomorphism of direct images is
`AlgebraicGeometry.Space.affinePushforwardIso'`. -/
theorem affineRestriction_map_pushforwardIsoOfChartComparison_hom_app'
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map
        ((pushforwardIsoOfChartComparison' hf hW).hom.app F) =
      (affinePushforwardIso' hf hW F).hom := by
  show ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map
    ((Functor.FullyFaithful.ofFullyFaithful
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1))).preimage _) = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- **The 2-isomorphism of Stacks 04KL from the chart comparison.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces compatible with the charts of `(g, g♯)`, such that for every
affine étale chart `V` of `Y` the comparison `g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism.
Then `(g, g♯)` is 2-isomorphic to `(f_small, f♯)`. -/
def twoIsoOfChartComparison' :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f) where
  e := pushforwardIsoOfChartComparison' hf hW
  commutes := by
    apply ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map_injective
    rw [Functor.map_comp, affineRestriction_map_pushforwardIsoOfChartComparison_hom_app']
    apply Sheaf.hom_ext
    ext W b
    have : IsAffine (chartSch W.unop.obj) := W.unop.property
    exact chartSectionEquiv_forgetFSharp' hf hW W.unop.obj b

end Comparison

/-! ### The original forms, over a terminal base

The declarations of this section are the forms over a terminal base `S`, with
`hS₀ : IsTerminal S` as their hypothesis on the base. The primed declarations above are the same
constructions under `hover : AlgebraicGeometry.Space.IsChartOverBase g`, which
`AlgebraicGeometry.Space.isChartOverBase_of_isTerminal` derives from `hS₀`. -/

section ComparisonBaseForm

variable {hS₀ : IsTerminal S}
  {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}

variable {f : X ⟶ Y} (hf : IsChartCompatible hS₀ g f)

/-- The comparison `g⁻¹h_V ⟶ chartFiber f V` is natural in the affine chart `V`. -/
theorem invRepComparison_naturality {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V) :
    (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map j)).hom ≫
        invRepComparison hf V =
      invRepComparison hf V' ≫ chartFiberMap f j :=
  invRepComparison_naturality' (hover := isChartOverBase_of_isTerminal hS₀ g) hf j

/-- The coordinate of `b` along the comparison is the coordinate map attached to `b` by `g`. -/
theorem invRepComparison_comp_chartFiberCoordinate (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    invRepComparison hf V ≫ chartFiberCoordinate B S hS f V b = (invCoord g V b).hom :=
  invRepComparison_comp_chartFiberCoordinate' (hover := isChartOverBase_of_isTerminal hS₀ g) hf V b

variable (hW : ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)],
  (SmallEtale.topology B S hS X.1).W (invRepComparison hf V))

/-- **The bijection `(g_*F)(V) ≃ (f_*F)(V)`** over an affine étale chart `V` of `Y`: both sets
are sets of maps of presheaves, out of `g⁻¹h_V` and out of `chartFiber f V`, and the comparison
`g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism. -/
def chartSectionEquiv (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (g.toToposHom.pushforward.obj F).obj.obj (op V) ≃ ((fPush f).obj F).obj.obj (op V) :=
  (invSectionEquiv g V F).trans (((hW V).homEquiv F.obj F.property).symm.trans
    (sectionEquivChartFiberHom B S hS f V F).symm)

/-- The defining property of `AlgebraicGeometry.Space.chartSectionEquiv`. -/
theorem invRepComparison_comp_chartSectionEquiv (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    invRepComparison hf V ≫
        sectionEquivChartFiberHom B S hS f V F (chartSectionEquiv hf hW V F x) =
      invSectionEquiv g V F x :=
  invRepComparison_comp_chartSectionEquiv' (hover := isChartOverBase_of_isTerminal hS₀ g) hf hW V F
    x

/-- `AlgebraicGeometry.Space.chartSectionEquiv` is characterized by its defining property. -/
theorem chartSectionEquiv_eq_iff (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V))
    (y : ((fPush f).obj F).obj.obj (op V)) :
    chartSectionEquiv hf hW V F x = y ↔
      invRepComparison hf V ≫ sectionEquivChartFiberHom B S hS f V F y =
        invSectionEquiv g V F x :=
  chartSectionEquiv_eq_iff' (hover := isChartOverBase_of_isTerminal hS₀ g) hf hW V F x y

/-- `AlgebraicGeometry.Space.chartSectionEquiv` is natural in the sheaf. -/
theorem chartSectionEquiv_naturality (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (q : F ⟶ G)
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    chartSectionEquiv hf hW V G ((g.toToposHom.pushforward.map q).hom.app (op V) x) =
      ((fPush f).map q).hom.app (op V) (chartSectionEquiv hf hW V F x) :=
  chartSectionEquiv_naturality' (hover := isChartOverBase_of_isTerminal hS₀ g) hf hW V q x

/-- `AlgebraicGeometry.Space.chartSectionEquiv` is natural in the affine chart. -/
theorem chartSectionEquiv_restrict {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V) (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    chartSectionEquiv hf hW V' F ((g.toToposHom.pushforward.obj F).obj.map j.op x) =
      ((fPush f).obj F).obj.map j.op (chartSectionEquiv hf hW V F x) :=
  chartSectionEquiv_restrict' (hover := isChartOverBase_of_isTerminal hS₀ g) hf hW j F x

/-- The structure map of `g` corresponds to the structure map of `f`. -/
theorem chartSectionEquiv_forgetFSharp (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    chartSectionEquiv hf hW V (structureSetSheaf B S hS X)
        ((RingedToposHom.forgetFSharp g).hom.app (op V) b) =
      (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b :=
  chartSectionEquiv_forgetFSharp' (hover := isChartOverBase_of_isTerminal hS₀ g) hf hW V b

attribute [local instance] affineEtaleInclusion_isDenseSubsite

/-- The bijections `AlgebraicGeometry.Space.chartSectionEquiv`, as an isomorphism of the
restrictions of `g_*F` and `f_*F` to the affine étale charts of `Y`. -/
def affinePushforwardIso (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).obj
        (g.toToposHom.pushforward.obj F) ≅
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).obj ((fPush f).obj F) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun W ↦
      haveI : IsAffine (chartSch W.unop.obj) := W.unop.property
      (chartSectionEquiv hf hW W.unop.obj F).toIso)
    (by
      intro W W' k
      have : IsAffine (chartSch W.unop.obj) := W.unop.property
      have : IsAffine (chartSch W'.unop.obj) := W'.unop.property
      ext x
      exact chartSectionEquiv_restrict hf hW k.unop.hom F x))

/-- **The isomorphism `g_* ≅ f_*` of direct images**, glued from the bijections
`AlgebraicGeometry.Space.chartSectionEquiv` over the affine étale charts of `Y`, which are a
dense subsite. -/
def pushforwardIsoOfChartComparison :
    g.toToposHom.pushforward ≅ fPush f :=
  ((Functor.FullyFaithful.ofFullyFaithful
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1))).whiskeringRight
    (Sheaf (SmallEtale.topology B S hS X.1) (Type u))).preimageIso
    (NatIso.ofComponents (affinePushforwardIso hf hW) (by
      intro F G q
      apply Sheaf.hom_ext
      ext W x
      have : IsAffine (chartSch W.unop.obj) := W.unop.property
      exact chartSectionEquiv_naturality hf hW W.unop.obj q x))

/-- Restricted to the affine étale charts of `Y`, the isomorphism of direct images is
`AlgebraicGeometry.Space.affinePushforwardIso`. -/
theorem affineRestriction_map_pushforwardIsoOfChartComparison_hom_app
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map
        ((pushforwardIsoOfChartComparison hf hW).hom.app F) =
      (affinePushforwardIso hf hW F).hom :=
  affineRestriction_map_pushforwardIsoOfChartComparison_hom_app'
    (hover := isChartOverBase_of_isTerminal hS₀ g) hf hW F

/-- **The 2-isomorphism of Stacks 04KL from the chart comparison.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces compatible with the charts of `(g, g♯)`, such that for every
affine étale chart `V` of `Y` the comparison `g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism.
Then `(g, g♯)` is 2-isomorphic to `(f_small, f♯)`. -/
def twoIsoOfChartComparison :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f) where
  e := pushforwardIsoOfChartComparison hf hW
  commutes := by
    apply ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map_injective
    rw [Functor.map_comp, affineRestriction_map_pushforwardIsoOfChartComparison_hom_app]
    apply Sheaf.hom_ext
    ext W b
    have : IsAffine (chartSch W.unop.obj) := W.unop.property
    exact chartSectionEquiv_forgetFSharp hf hW W.unop.obj b

end ComparisonBaseForm

end AlgebraicGeometry.Space

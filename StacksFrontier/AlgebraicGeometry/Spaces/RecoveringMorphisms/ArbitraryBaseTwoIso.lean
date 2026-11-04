module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.TwoIso

/-!
# The 2-isomorphism of Stacks 04KL from the chart comparison, over an arbitrary base scheme

Let `(g, g♯)` be a morphism of the small étale ringed topoi of two algebraic spaces over a base
scheme `S` whose chart morphisms are over `S` (`AlgebraicGeometry.Space.IsChartOverBase`), and
let `f : X ⟶ Y` be a morphism of algebraic spaces compatible with the charts of `g`
(`AlgebraicGeometry.Space.OverBase.IsChartCompatible`).  If for every affine étale chart `V` of
`Y` the comparison `g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism, then `(g, g♯)` is
2-isomorphic to `(f_small, f♯)`.

## Main definitions

* `AlgebraicGeometry.Space.OverBase.chartSectionEquiv`: the bijection `(g_*F)(V) ≃ (f_*F)(V)`
  over an affine chart `V`.
* `AlgebraicGeometry.Space.OverBase.pushforwardIsoOfChartComparison`: the isomorphism
  `g_* ≅ f_*` of direct images glued from these bijections.
* `AlgebraicGeometry.Space.OverBase.twoIsoOfChartComparison`: the 2-isomorphism of morphisms of
  ringed topoi `(g, g♯) ≅ (f_small, f♯)`.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites

universe u

namespace AlgebraicGeometry.Space.OverBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [local instance] smallEtaleTopology_subcanonical

variable {g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)}
  {hb : IsChartOverBase g}

variable {f : X ⟶ Y} (hfb : IsChartCompatible hb f)

/-- The comparison `g⁻¹h_V ⟶ chartFiber f V` is natural in the affine chart `V`. -/
theorem invRepComparison_naturality {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V) :
    (g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yoneda.map j)).hom ≫
        invRepComparison hfb V =
      invRepComparison hfb V' ≫ chartFiberMap f j := by
  ext U s
  exact Subtype.ext (chartOverHom_map hb U.unop j s)

/-- The coordinate of `b` along the comparison is the coordinate map attached to `b` by `g`. -/
theorem invRepComparison_comp_chartFiberCoordinate (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    invRepComparison hfb V ≫ chartFiberCoordinate B S hS f V b = (invCoord g V b).hom := by
  ext U s
  show (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (chartOverHom hb V U.unop s)).op) b = _
  rw [toScheme_map_chartOverHom, Scheme.Γ_map_op, chartSchemeHom_appTop]
  exact chartRingHom_apply g V U.unop s b

variable (hWb : ∀ (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)],
  (SmallEtale.topology B S hS X.1).W (invRepComparison hfb V))

/-- **The bijection `(g_*F)(V) ≃ (f_*F)(V)`** over an affine étale chart `V` of `Y`: both sets
are sets of maps of presheaves, out of `g⁻¹h_V` and out of `chartFiber f V`, and the comparison
`g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism. -/
def chartSectionEquiv (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    (g.toToposHom.pushforward.obj F).obj.obj (op V) ≃ ((fPush f).obj F).obj.obj (op V) :=
  (invSectionEquiv g V F).trans (((hWb V).homEquiv F.obj F.cond).symm.trans
    (sectionEquivChartFiberHom B S hS f V F).symm)

/-- The defining property of `AlgebraicGeometry.Space.OverBase.chartSectionEquiv`. -/
theorem invRepComparison_comp_chartSectionEquiv (V : SmallEtale B S hS Y.1)
    [IsAffine (chartSch V)] (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    invRepComparison hfb V ≫
        sectionEquivChartFiberHom B S hS f V F (chartSectionEquiv hfb hWb V F x) =
      invSectionEquiv g V F x := by
  rw [chartSectionEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  exact ((hWb V).homEquiv F.obj F.cond).apply_symm_apply _

/-- `AlgebraicGeometry.Space.OverBase.chartSectionEquiv` is characterized by its defining
property. -/
theorem chartSectionEquiv_eq_iff (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V))
    (y : ((fPush f).obj F).obj.obj (op V)) :
    chartSectionEquiv hfb hWb V F x = y ↔
      invRepComparison hfb V ≫ sectionEquivChartFiberHom B S hS f V F y =
        invSectionEquiv g V F x := by
  refine ⟨fun h ↦ h ▸ invRepComparison_comp_chartSectionEquiv hfb hWb V F x, fun h ↦ ?_⟩
  apply (sectionEquivChartFiberHom B S hS f V F).injective
  apply ((hWb V).homEquiv F.obj F.cond).injective
  show invRepComparison hfb V ≫ _ = invRepComparison hfb V ≫ _
  rw [invRepComparison_comp_chartSectionEquiv, h]

/-- `AlgebraicGeometry.Space.OverBase.chartSectionEquiv` is natural in the sheaf. -/
theorem chartSectionEquiv_naturality (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    {F G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (q : F ⟶ G)
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    chartSectionEquiv hfb hWb V G ((g.toToposHom.pushforward.map q).hom.app (op V) x) =
      ((fPush f).map q).hom.app (op V) (chartSectionEquiv hfb hWb V F x) := by
  rw [chartSectionEquiv_eq_iff, sectionEquivChartFiberHom_naturality, ← Category.assoc,
    invRepComparison_comp_chartSectionEquiv, invSectionEquiv_naturality]

/-- `AlgebraicGeometry.Space.OverBase.chartSectionEquiv` is natural in the affine chart. -/
theorem chartSectionEquiv_restrict {V V' : SmallEtale B S hS Y.1} [IsAffine (chartSch V)]
    [IsAffine (chartSch V')] (j : V' ⟶ V) (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (x : (g.toToposHom.pushforward.obj F).obj.obj (op V)) :
    chartSectionEquiv hfb hWb V' F ((g.toToposHom.pushforward.obj F).obj.map j.op x) =
      ((fPush f).obj F).obj.map j.op (chartSectionEquiv hfb hWb V F x) := by
  rw [chartSectionEquiv_eq_iff, sectionEquivChartFiberHom_restrict, ← Category.assoc,
    ← invRepComparison_naturality, Category.assoc, invRepComparison_comp_chartSectionEquiv,
    invSectionEquiv_restrict]

/-- The structure map of `g` corresponds to the structure map of `f`. -/
theorem chartSectionEquiv_forgetFSharp (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)]
    (b : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    chartSectionEquiv hfb hWb V (structureSetSheaf B S hS X)
        ((RingedToposHom.forgetFSharp g).hom.app (op V) b) =
      (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS f)).hom.app (op V) b := by
  refine (chartSectionEquiv_eq_iff hfb hWb V (structureSetSheaf B S hS X) _ _).2 ?_
  refine ((congrArg (invRepComparison hfb V ≫ ·)
    (sectionEquivChartFiberHom_fSharp B S hS f V b)).trans
    (invRepComparison_comp_chartFiberCoordinate hfb V b)).trans ?_
  exact (congrArg (fun φ ↦ φ.hom) (homEquiv_symm_forgetFSharp g V b)).symm

/-! ### Gluing over the affine charts -/

attribute [local instance] affineEtaleInclusion_isDenseSubsite

/-- The bijections `AlgebraicGeometry.Space.OverBase.chartSectionEquiv`, as an isomorphism of the
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
      (chartSectionEquiv hfb hWb W.unop.obj F).toIso)
    (by
      intro W W' k
      have : IsAffine (chartSch W.unop.obj) := W.unop.property
      have : IsAffine (chartSch W'.unop.obj) := W'.unop.property
      ext x
      exact chartSectionEquiv_restrict hfb hWb k.unop.hom F x))

/-- The components of `AlgebraicGeometry.Space.OverBase.affinePushforwardIso` are the bijections
`AlgebraicGeometry.Space.OverBase.chartSectionEquiv`. -/
theorem affinePushforwardIso_hom_app (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (W : AffineEtale B S hS Y.1) (x : (g.toToposHom.pushforward.obj F).obj.obj (op W.obj)) :
    haveI : IsAffine (chartSch W.obj) := W.property
    (affinePushforwardIso hfb hWb F).hom.hom.app (op W) x = chartSectionEquiv hfb hWb W.obj F x :=
  rfl

/-- **The isomorphism `g_* ≅ f_*` of direct images**, glued from the bijections
`AlgebraicGeometry.Space.OverBase.chartSectionEquiv` over the affine étale charts of `Y`, which
are a dense subsite. -/
def pushforwardIsoOfChartComparison :
    g.toToposHom.pushforward ≅ fPush f :=
  ((Functor.FullyFaithful.ofFullyFaithful
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1))).whiskeringRight
    (Sheaf (SmallEtale.topology B S hS X.1) (Type u))).preimageIso
    (NatIso.ofComponents (affinePushforwardIso hfb hWb) (by
      intro F G q
      apply Sheaf.hom_ext
      ext W x
      have : IsAffine (chartSch W.unop.obj) := W.unop.property
      exact chartSectionEquiv_naturality hfb hWb W.unop.obj q x))

/-- Restricted to the affine étale charts of `Y`, the isomorphism of direct images is
`AlgebraicGeometry.Space.OverBase.affinePushforwardIso`. -/
theorem affineRestriction_map_pushforwardIsoOfChartComparison_hom_app
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map
        ((pushforwardIsoOfChartComparison hfb hWb).hom.app F) =
      (affinePushforwardIso hfb hWb F).hom := by
  show ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map
    ((Functor.FullyFaithful.ofFullyFaithful
      ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1))).preimage _) = _
  rw [Functor.FullyFaithful.map_preimage]
  rfl

/-- **The 2-isomorphism from the chart comparison.** Let `f : X ⟶ Y` be a morphism of algebraic
spaces compatible with the charts of `(g, g♯)`, such that for every affine étale chart `V` of `Y`
the comparison `g⁻¹h_V ⟶ chartFiber f V` is a local isomorphism. Then `(g, g♯)` is 2-isomorphic to
`(f_small, f♯)`. -/
def twoIsoOfChartComparison :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} g (smallEtaleRingedToposHom B S hS f) where
  e := pushforwardIsoOfChartComparison hfb hWb
  commutes := by
    apply ((AffineEtale.inclusion B S hS Y.1).sheafPushforwardContinuous (Type u)
      (AffineEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Y.1)).map_injective
    rw [Functor.map_comp, affineRestriction_map_pushforwardIsoOfChartComparison_hom_app]
    apply Sheaf.hom_ext
    ext W b
    have : IsAffine (chartSch W.unop.obj) := W.unop.property
    exact chartSectionEquiv_forgetFSharp hfb hWb W.unop.obj b

end AlgebraicGeometry.Space.OverBase

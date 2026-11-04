module

public import StacksFrontier.AlgebraicGeometry.RelativeCech.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionComparisonSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionPullbackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecChartMapComp

/-!
# The cocycle law of the chart comparison of a module on an algebraic space

Let `F` be an algebraic space over a scheme `S` and `M` an `𝒪_F`-module on its small étale
site.  For a morphism `g : V ⟶ U` of étale scheme charts of `F` the restrictions of `M` to the
two chart schemes are compared by
`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison`, a morphism
`M|_U ⟶ (chartSchemeMap g)_* M|_V`, and by its transpose
`AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison`, a morphism
`(chartSchemeMap g)^* M|_U ⟶ M|_V`.  This file proves that these comparisons satisfy the
cocycle condition: along a composite `g' ≫ g` of morphisms of charts the comparison is the
composite of the comparisons along `g` and along `g'`.

On sections over a Zariski open the comparison is a restriction map of `M` along a morphism of
étale charts, so the cocycle law is the functoriality of `M` as a presheaf on the small étale
site, through the composition law `AlgebraicGeometry.Space.openChartRestrict_comp` of the
restriction of chart morphisms to opens.

## Main results

* `AlgebraicGeometry.Space.map_openChartRestrict_comp_apply`: the restriction maps of a presheaf
  of modules on the small étale site along the restrictions of a composite of chart morphisms
  compose.
* `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison_comp`: the cocycle law in
  the direct-image form, `M|_U ⟶ (g' ≫ g)_* M|_W` is `M|_U ⟶ g_* M|_V ⟶ g_* g'_* M|_W`.
* `AlgebraicGeometry.Space.restrictToChartSchemePullbackComparison_comp`: the cocycle law in the
  inverse-image form: the canonical comparison `g'^* g^* M|_U ≅ (g' ≫ g)^* M|_U` followed by the
  comparison along `g' ≫ g` is `g'^*` of the comparison along `g` followed by the comparison
  along `g'`.
* `AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_homEquiv_symm`: for morphisms of
  schemes, a cocycle of direct-image comparisons transposes to a cocycle of inverse-image
  comparisons.

## Implementation notes

The direct image along a composite of morphisms of schemes is the composite of the direct
images on the nose (`Stacks.AlgebraicGeometry.RelativeCech.pushforwardComp_hom_app`), so the
direct-image form needs no transport; it is checked on sections, where every section of the
chart restriction is a sheafification unit.  The section computation is stated for an arbitrary
presheaf of modules and only then specialised to the universe-lifted module, so that the
comparison of the two opens `(g' ≫ g)⁻¹ O` and `g'⁻¹ (g⁻¹ O)` — equal by definition — is made
between variables.  The inverse-image form is the transpose of the direct-image form along the
composite adjunction, through `Stacks.AlgebraicGeometry.RelativeCech.homEquiv_pullbackComp`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The restriction map of a presheaf of modules on the small étale site along
`AlgebraicGeometry.Space.openChartRestrict` of a composite of morphisms of charts is the composite
of the restriction maps. -/
theorem map_openChartRestrict_comp_apply
    (N : PresheafOfModules.{u} (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat))
    {U V W : SmallEtale B S hS F} (g : V ⟶ U) (g' : W ⟶ V) (O : (chartScheme U).Opens)
    (m : ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
      N).obj (op O)) :
    N.map (openChartRestrict B S hS F (g' ≫ g) O).op m =
      N.map (openChartRestrict B S hS F g' (chartSchemeMap g ⁻¹ᵁ O)).op
        (N.map (openChartRestrict B S hS F g O).op m) :=
  let m' : N.obj (op (openChart B S hS F U O)) := m
  (PresheafOfModules.congr_map_apply N
      (congrArg Quiver.Hom.op (openChartRestrict_comp g' g O)) m').trans
    (PresheafOfModules.map_comp_apply N (openChartRestrict B S hS F g O).op
      (openChartRestrict B S hS F g' (chartSchemeMap g ⁻¹ᵁ O)).op m')

/-- `AlgebraicGeometry.Space.map_openChartRestrict_comp_apply` followed by the Zariski
sheafification unit of the chart restriction of `N` to the smallest chart, in the shape the
section computation of the chart comparison produces. -/
theorem toSheafify_app_map_openChartRestrict_comp_apply
    (N : PresheafOfModules.{u} (structurePresheaf B S hS F ⋙ forget₂ CommRingCat RingCat))
    {U V W : SmallEtale B S hS F} (g : V ⟶ U) (g' : W ⟶ V) (O : (chartScheme U).Opens)
    [HasSheafify (Opens.grothendieckTopology (chartScheme W)) AddCommGrpCat.{u}]
    (m : ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
      N).presheaf.obj (op O)) :
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme W))
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F W)).obj
          N).presheaf).app (op (chartSchemeMap (g' ≫ g) ⁻¹ᵁ O))
        (N.map (openChartRestrict B S hS F (g' ≫ g) O).op m) =
      (CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme W))
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F W)).obj
          N).presheaf).app (op (chartSchemeMap g' ⁻¹ᵁ chartSchemeMap g ⁻¹ᵁ O))
        (N.map (openChartRestrict B S hS F g' (chartSchemeMap g ⁻¹ᵁ O)).op
          (N.map (openChartRestrict B S hS F g O).op m)) :=
  congrArg (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme W))
        ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F W)).obj
          N).presheaf).app (op (chartSchemeMap g' ⁻¹ᵁ chartSchemeMap g ⁻¹ᵁ O))))
    (map_openChartRestrict_comp_apply B S hS F N g g' O m)

variable (hF : IsAlgebraicSpace B S hS F) (M : Modules.{u, u} B S hS F hF)

/-- **The cocycle law of the chart comparison, direct-image form.**  Along a composite
`g' ≫ g` of morphisms of étale charts the comparison `M|_U ⟶ (g' ≫ g)_* M|_W` is the
comparison along `g` followed by the direct image along `chartSchemeMap g` of the comparison
along `g'`.

Every section of `M|_U` over a Zariski open is a sheafification unit
(`AlgebraicGeometry.Space.surjective_toSheafify_app_pushforward_uliftForPresentation`), and on a
sheafification unit each comparison is a restriction map of `M`
(`AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison_app_toSheafify`), so the
law is the functoriality of `M` along `AlgebraicGeometry.Space.openChartRestrict_comp`. -/
theorem restrictToChartSchemePushforwardComparison_comp {U V W : SmallEtale B S hS F}
    (g : V ⟶ U) (g' : W ⟶ V) :
    restrictToChartSchemePushforwardComparison B S hS F hF M (g' ≫ g) =
      restrictToChartSchemePushforwardComparison B S hS F hF M g ≫
        (Scheme.Modules.pushforward (chartSchemeMap g)).map
          (restrictToChartSchemePushforwardComparison B S hS F hF M g') := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun Oop => ?_)
  obtain ⟨O⟩ := Oop
  ext a
  obtain ⟨m, rfl⟩ :=
    surjective_toSheafify_app_pushforward_uliftForPresentation B S hS F hF M U O a
  refine (restrictToChartSchemePushforwardComparison_app_toSheafify B S hS F hF M (g' ≫ g)
    O m).trans ?_
  change _ = (restrictToChartSchemePushforwardComparison B S hS F hF M g').val.app
      (op (chartSchemeMap g ⁻¹ᵁ O))
      ((restrictToChartSchemePushforwardComparison B S hS F hF M g).val.app (op O)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (chartScheme U))
          ((PresheafOfModules.pushforward (chartSchemeRestrictionRingHom B S hS F U)).obj
            (SheafOfModules.uliftForPresentation M).val).presheaf).app (op O) m))
  rw [restrictToChartSchemePushforwardComparison_app_toSheafify B S hS F hF M g O m,
    restrictToChartSchemePushforwardComparison_app_toSheafify B S hS F hF M g'
      (chartSchemeMap g ⁻¹ᵁ O) ((SheafOfModules.uliftForPresentation M).val.map
        (openChartRestrict B S hS F g O).op m)]
  exact toSheafify_app_map_openChartRestrict_comp_apply B S hS F
    (SheafOfModules.uliftForPresentation M).val g g' O m

/-- Transposing a cocycle of direct-image comparisons along a composite of morphisms of
schemes: if `p_{u ≫ v} = p_v ≫ v_* p_u` for morphisms `p_v : A ⟶ v_* B`, `p_u : B ⟶ u_* C` and
`p_{u ≫ v} : A ⟶ (u ≫ v)_* C`, then the transposes satisfy the cocycle law through the canonical
comparison `u^* v^* A ≅ (u ≫ v)^* A`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackComp_hom_app_comp_homEquiv_symm
    {X Y Z : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ Z) {A : Z.Modules} {B : Y.Modules}
    {C : X.Modules} {pv : A ⟶ (Scheme.Modules.pushforward v).obj B}
    {pu : B ⟶ (Scheme.Modules.pushforward u).obj C}
    {puv : A ⟶ (Scheme.Modules.pushforward (u ≫ v)).obj C}
    (h : puv = pv ≫ (Scheme.Modules.pushforward v).map pu) :
    (Scheme.Modules.pullbackComp u v).hom.app A ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction (u ≫ v)).homEquiv _ _).symm puv =
      (Scheme.Modules.pullback u).map
          (((Scheme.Modules.pullbackPushforwardAdjunction v).homEquiv _ _).symm pv) ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction u).homEquiv _ _).symm pu := by
  apply (((Scheme.Modules.pullbackPushforwardAdjunction v).comp
    (Scheme.Modules.pullbackPushforwardAdjunction u)).homEquiv _ _).injective
  rw [Stacks.AlgebraicGeometry.RelativeCech.homEquiv_pullbackComp u v _ _ (fun _ => rfl),
    Stacks.AlgebraicGeometry.RelativeCech.comp_homEquiv_apply,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, h]
  exact Category.comp_id _

/-- **The cocycle law of the chart comparison, inverse-image form.**  Along a composite
`g' ≫ g` of morphisms of étale charts, the canonical comparison
`g'^* g^* M|_U ≅ (g' ≫ g)^* M|_U` followed by the comparison along `g' ≫ g` is the inverse image
along `chartSchemeMap g'` of the comparison along `g` followed by the comparison along `g'`.

Both sides are transposed along the composite adjunction
`g^* ⋙ g'^* ⊣ g'_* ⋙ g_*`: the left side to the comparison along `g' ≫ g` by
`Stacks.AlgebraicGeometry.RelativeCech.homEquiv_pullbackComp`, the right side to the composite
of the comparisons along `g` and `g'` by naturality of the two transpositions, and these agree
by `AlgebraicGeometry.Space.restrictToChartSchemePushforwardComparison_comp`. -/
theorem restrictToChartSchemePullbackComparison_comp {U V W : SmallEtale B S hS F}
    (g : V ⟶ U) (g' : W ⟶ V) :
    (Scheme.Modules.pullbackComp (chartSchemeMap g') (chartSchemeMap g)).hom.app
          (restrictToChartScheme B S hS F hF M U) ≫
        restrictToChartSchemePullbackComparison B S hS F hF M (g' ≫ g) =
      (Scheme.Modules.pullback (chartSchemeMap g')).map
          (restrictToChartSchemePullbackComparison B S hS F hF M g) ≫
        restrictToChartSchemePullbackComparison B S hS F hF M g' :=
  Scheme.Modules.pullbackComp_hom_app_comp_homEquiv_symm (chartSchemeMap g') (chartSchemeMap g)
    (restrictToChartSchemePushforwardComparison_comp B S hS F hF M g g')

end AlgebraicGeometry.Space

end

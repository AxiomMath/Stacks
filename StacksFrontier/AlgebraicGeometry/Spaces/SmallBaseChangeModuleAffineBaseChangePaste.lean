module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangePaste
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp

/-!
# Pasting of the affine base change isomorphisms for the base-change direct image

For two cartesian squares stacked along the base,

```
Y₂ ──g₂'──▶ Y₁ ──g₁'──▶ Y₀
│π₂         │π₁         │π₀
▼           ▼           ▼
X₂ ──g₂───▶ X₁ ──g₁───▶ X₀
```

with `π₀` and `π₁` affine, and the outer rectangle along `k = g₂ ≫ g₁`, `k' = g₂' ≫ g₁'` (also
cartesian), the affine base change isomorphism
`AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso` of the outer rectangle is the
comparison `k^* ≅ g₂^* g₁^*` of Stacks 03LU, followed by `g₂^*` of the isomorphism of the right
square, the isomorphism of the left square, and the comparison `g₂'^* g₁'^* ≅ k'^*`.  At the
structure sheaf the last comparison is absorbed into the identifications `h^*𝒪 ≅ 𝒪`, and the
isomorphisms `g^*(π_*𝒪_Y) ≅ π'_*𝒪_{Y'}` paste on the nose.

## Main results

* `AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso_hom_paste`: the pasting law
  at a quasi-coherent module.
* `AlgebraicGeometry.Space.modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom_paste`: the
  pasting law at the structure sheaf.

## Implementation notes

The isomorphisms of `AlgebraicGeometry.Space.smallBaseChangeModuleAffineBaseChangeIso` are
`AlgebraicGeometry.Space.moduleAffineBaseChangeIso` (for the direct image of Stacks 03LU)
conjugated by the chart identification `AlgebraicGeometry.Space.modulePushforwardChartIso`, and
the pasting law for the former is `AlgebraicGeometry.Space.moduleBaseChangeMap_paste`.  The
direct image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` is indexed by
`AlgebraicGeometry.Space.smallEtaleRingSheaf`, which is the ring sheaf of
`AlgebraicGeometry.Space.Modules` only after unfolding, so rewriting across the two spellings
fails and definitional unfolding across them times out.  The conjugation is therefore done in an
arbitrary category (`paste_conj`, `paste_unit`), in which the objects carrying the other spelling
are variables, and the lemma is applied with every such object unified from the goal.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The conjugation step of the pasting law in an arbitrary category: if isomorphisms `M`, `M₁`,
`M₂` paste along `T` and `T'`, then so do their conjugates `N`, `N₁`, `N₂` by the
identifications `c₀`, `c₁`, `c₂`, `c₂'`, provided `c₂` and `c₂'` are compatible with the last
map `q`. -/
private theorem paste_conj {𝒴₀ 𝒴₁ 𝒴₂ 𝒳₀ 𝒳₁ 𝒳₂ : Type*} [Category 𝒴₀] [Category 𝒴₁]
    [Category 𝒴₂] [Category 𝒳₀] [Category 𝒳₁] [Category 𝒳₂]
    {P₀ : 𝒴₀ ⥤ 𝒳₀} {P₁ : 𝒴₁ ⥤ 𝒳₁} {P₂ : 𝒴₂ ⥤ 𝒳₂}
    {G₁ : 𝒳₀ ⥤ 𝒳₁} {G₂ : 𝒳₁ ⥤ 𝒳₂} {K : 𝒳₀ ⥤ 𝒳₂} (T : K ≅ G₁ ⋙ G₂)
    {G₁' : 𝒴₀ ⥤ 𝒴₁} {G₂' : 𝒴₁ ⥤ 𝒴₂} {K' : 𝒴₀ ⥤ 𝒴₂} (T' : K' ≅ G₁' ⋙ G₂') {F : 𝒴₀}
    {A₀ : 𝒳₀} {A₁ : 𝒳₁} {A₂ A₂' : 𝒳₂}
    (c₀ : P₀.obj F ≅ A₀) (c₁ : P₁.obj (G₁'.obj F) ≅ A₁) (c₂ : P₂.obj (K'.obj F) ≅ A₂)
    (c₂' : P₂.obj (G₂'.obj (G₁'.obj F)) ≅ A₂') {q : A₂' ⟶ A₂}
    (hq : P₂.map (T'.inv.app F) ≫ c₂.hom = c₂'.hom ≫ q)
    (M : K.obj (P₀.obj F) ≅ P₂.obj (K'.obj F)) (M₁ : G₁.obj (P₀.obj F) ≅ P₁.obj (G₁'.obj F))
    (M₂ : G₂.obj (P₁.obj (G₁'.obj F)) ≅ P₂.obj (G₂'.obj (G₁'.obj F)))
    {N : K.obj A₀ ≅ A₂} {N₁ : G₁.obj A₀ ≅ A₁} {N₂ : G₂.obj A₁ ≅ A₂'}
    (hN : N = K.mapIso c₀.symm ≪≫ M ≪≫ c₂) (hN₁ : N₁ = G₁.mapIso c₀.symm ≪≫ M₁ ≪≫ c₁)
    (hN₂ : N₂ = G₂.mapIso c₁.symm ≪≫ M₂ ≪≫ c₂')
    (h : M.hom = T.hom.app _ ≫ G₂.map M₁.hom ≫ M₂.hom ≫ P₂.map (T'.inv.app F)) :
    N.hom = T.hom.app A₀ ≫ G₂.map N₁.hom ≫ N₂.hom ≫ q := by
  subst hN hN₁ hN₂
  simp [h, hq]

/-- The structure-sheaf step of the pasting law in an arbitrary category: composites
`b₁ = n₁ ≫ p₁`, `b₂ = n₂ ≫ p₂`, `b = nout ≫ qk` paste along `T` once `nout` pastes (`hgen`),
`n₂` is natural with respect to `p₁` (`hnat`), and the last maps agree (`hU`). -/
private theorem paste_unit {𝒳₀ 𝒳₁ 𝒳₂ : Type*} [Category 𝒳₀] [Category 𝒳₁] [Category 𝒳₂]
    {G₁ : 𝒳₀ ⥤ 𝒳₁} {G₂ : 𝒳₁ ⥤ 𝒳₂} {K : 𝒳₀ ⥤ 𝒳₂} (T : K ≅ G₁ ⋙ G₂) {A₀ : 𝒳₀}
    {V₁ V₁' : 𝒳₁} {R₁ R₂ R₃ R₄ : 𝒳₂}
    {n₁ : G₁.obj A₀ ⟶ V₁} {p₁ : V₁ ⟶ V₁'} {b₁ : G₁.obj A₀ ⟶ V₁'} (hb₁ : b₁ = n₁ ≫ p₁)
    {n₂ : G₂.obj V₁' ⟶ R₁} {p₂ : R₁ ⟶ R₂} {b₂ : G₂.obj V₁' ⟶ R₂} (hb₂ : b₂ = n₂ ≫ p₂)
    {n₂' : G₂.obj V₁ ⟶ R₃} {r : R₃ ⟶ R₁} (hnat : G₂.map p₁ ≫ n₂ = n₂' ≫ r)
    {nout : K.obj A₀ ⟶ R₄} {qk : R₄ ⟶ R₂} {b : K.obj A₀ ⟶ R₂} (hb : b = nout ≫ qk)
    {m : G₂.obj V₁ ⟶ R₄} (hgen : nout = T.hom.app A₀ ≫ G₂.map n₁ ≫ m)
    (hU : m ≫ qk = n₂' ≫ r ≫ p₂) :
    b = T.hom.app A₀ ≫ G₂.map b₁ ≫ b₂ := by
  subst hb₁ hb₂ hb hgen
  simp [reassoc_of% hnat, hU]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X₀ X₁ X₂ Y₀ Y₁ Y₂ : AlgebraicSpaces B S hS} {π₀ : Y₀ ⟶ X₀} {π₁ : Y₁ ⟶ X₁} {π₂ : Y₂ ⟶ X₂}
  {g₁ : X₁ ⟶ X₀} {g₁' : Y₁ ⟶ Y₀} {g₂ : X₂ ⟶ X₁} {g₂' : Y₂ ⟶ Y₁}

/-- The pasting law for the affine base change isomorphisms of Stacks 03LU direct images. -/
private theorem moduleAffineBaseChangeIso_hom_paste
    (sq₁ : IsPullback g₁' π₁ π₀ g₁) (sq₂ : IsPullback g₂' π₂ π₁ g₂)
    {k : X₂ ⟶ X₀} {k' : Y₂ ⟶ Y₀} (hk : g₂ ≫ g₁ = k) (hk' : g₂' ≫ g₁' = k')
    (sq : IsPullback k' π₂ π₀ k)
    (hπa₀ : IsAffineHom B S hS π₀.hom) (hπa₁ : IsAffineHom B S hS π₁.hom)
    (F : Modules.{u, u} B S hS Y₀.1 Y₀.2) (hF : F.IsQuasicoherentOnSite)
    (hF' : ((modulePullback B S hS g₁').obj F).IsQuasicoherentOnSite) :
    (moduleAffineBaseChangeIso sq hπa₀ F hF).hom =
      (modulePullbackTriangle B S hS hk).hom.app ((modulePushforward B S hS π₀).obj F) ≫
        (modulePullback B S hS g₂).map (moduleAffineBaseChangeIso sq₁ hπa₀ F hF).hom ≫
        (moduleAffineBaseChangeIso sq₂ hπa₁ _ hF').hom ≫
        (modulePushforward B S hS π₂).map ((modulePullbackTriangle B S hS hk').inv.app F) := by
  subst hk hk'
  rw [modulePullbackTriangle_rfl, modulePullbackTriangle_rfl, Iso.symm_hom, Iso.symm_inv,
    moduleAffineBaseChangeIso_hom, moduleAffineBaseChangeIso_hom, moduleAffineBaseChangeIso_hom,
    moduleBaseChangeApp_eq, moduleBaseChangeApp_eq, moduleBaseChangeApp_eq]
  exact moduleBaseChangeMap_paste π₀ g₁ π₁ g₁' g₂ π₂ g₂' sq₁.w sq₂.w sq.w F

/-- The affine base change isomorphism of the base-change direct image, unfolded, for a module
that is a variable. -/
private theorem smallBaseChangeModuleAffineBaseChangeIso_eq {X Y X' Y' : AlgebraicSpaces B S hS}
    {π : Y ⟶ X} {g : X' ⟶ X} {π' : Y' ⟶ X'} {g' : Y' ⟶ Y} (sq : IsPullback g' π' π g)
    (hπa : IsAffineHom B S hS π.hom) (hπ : yoneda.relativelyRepresentable π.hom)
    (hπ' : yoneda.relativelyRepresentable π'.hom) (F : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : F.IsQuasicoherentOnSite) :
    smallBaseChangeModuleAffineBaseChangeIso sq hπa hπ hπ' F hF =
      (modulePullback B S hS g).mapIso ((modulePushforwardChartIso B S hS π hπ).app F).symm ≪≫
        moduleAffineBaseChangeIso sq hπa F hF ≪≫
          (modulePushforwardChartIso B S hS π' hπ').app ((modulePullback B S hS g').obj F) :=
  rfl

/-- **The affine base change isomorphisms paste**, at a quasi-coherent module `F` on `Y₀`.  For
cartesian squares `(g₁', π₁, π₀, g₁)` and `(g₂', π₂, π₁, g₂)` with `π₀` and `π₁` affine, and the
outer cartesian square along `k = g₂ ≫ g₁`, `k' = g₂' ≫ g₁'`, the isomorphism
`k^*(π₀_*F) ≅ π₂_*(k'^*F)` of the outer square is the comparison `k^* ≅ g₂^* g₁^*`
(`AlgebraicGeometry.Space.modulePullbackTriangle`), `g₂^*` of the isomorphism of the right
square, the isomorphism of the left square at `g₁'^*F`, and the direct image of the comparison
`g₂'^* g₁'^* ≅ k'^*`. -/
theorem smallBaseChangeModuleAffineBaseChangeIso_hom_paste
    (sq₁ : IsPullback g₁' π₁ π₀ g₁) (sq₂ : IsPullback g₂' π₂ π₁ g₂)
    {k : X₂ ⟶ X₀} {k' : Y₂ ⟶ Y₀} (hk : g₂ ≫ g₁ = k) (hk' : g₂' ≫ g₁' = k')
    (sq : IsPullback k' π₂ π₀ k)
    (hπa₀ : IsAffineHom B S hS π₀.hom) (hπa₁ : IsAffineHom B S hS π₁.hom)
    (hπ₀ : yoneda.relativelyRepresentable π₀.hom) (hπ₁ : yoneda.relativelyRepresentable π₁.hom)
    (hπ₂ : yoneda.relativelyRepresentable π₂.hom) (F : Modules.{u, u} B S hS Y₀.1 Y₀.2)
    (hF : F.IsQuasicoherentOnSite)
    (hF' : ((modulePullback B S hS g₁').obj F).IsQuasicoherentOnSite) :
    (smallBaseChangeModuleAffineBaseChangeIso sq hπa₀ hπ₀ hπ₂ F hF).hom =
      (modulePullbackTriangle B S hS hk).hom.app
          ((smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj F) ≫
        (modulePullback B S hS g₂).map
          (smallBaseChangeModuleAffineBaseChangeIso sq₁ hπa₀ hπ₀ hπ₁ F hF).hom ≫
        (smallBaseChangeModuleAffineBaseChangeIso sq₂ hπa₁ hπ₁ hπ₂ _ hF').hom ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map
          ((modulePullbackTriangle B S hS hk').inv.app F) := by
  refine paste_conj (P₀ := modulePushforward B S hS π₀) (P₁ := modulePushforward B S hS π₁)
    (P₂ := modulePushforward B S hS π₂) (F := F)
    (modulePullbackTriangle B S hS hk) (modulePullbackTriangle B S hS hk')
    ?c₀ ?c₁ ?c₂ ?c₂' ?hq ?M ?M₁ ?M₂ ?hN ?hN₁ ?hN₂ ?h
  case c₀ => exact (modulePushforwardChartIso B S hS π₀ hπ₀).app F
  case c₁ => exact (modulePushforwardChartIso B S hS π₁ hπ₁).app _
  case c₂ => exact (modulePushforwardChartIso B S hS π₂ hπ₂).app _
  case c₂' => exact (modulePushforwardChartIso B S hS π₂ hπ₂).app _
  case M => exact moduleAffineBaseChangeIso sq hπa₀ F hF
  case M₁ => exact moduleAffineBaseChangeIso sq₁ hπa₀ F hF
  case M₂ => exact moduleAffineBaseChangeIso sq₂ hπa₁ _ hF'
  case hq => exact (modulePushforwardChartIso B S hS π₂ hπ₂).hom.naturality _
  case hN => exact smallBaseChangeModuleAffineBaseChangeIso_eq sq hπa₀ hπ₀ hπ₂ F hF
  case hN₁ => exact smallBaseChangeModuleAffineBaseChangeIso_eq sq₁ hπa₀ hπ₀ hπ₁ F hF
  case hN₂ => exact smallBaseChangeModuleAffineBaseChangeIso_eq sq₂ hπa₁ hπ₁ hπ₂ _ hF'
  case h => exact moduleAffineBaseChangeIso_hom_paste sq₁ sq₂ hk hk' sq hπa₀ hπa₁ F hF hF'

/-- At the structure sheaf, the comparison `g₂'^* g₁'^* ≅ k'^*` followed by `k'^*𝒪 ≅ 𝒪` is
`g₂'^*` of `g₁'^*𝒪 ≅ 𝒪` followed by `g₂'^*𝒪 ≅ 𝒪`. -/
private theorem modulePullbackTriangle_inv_app_comp_modulePullbackUnitIso_hom
    {k' : Y₂ ⟶ Y₀} (hk' : g₂' ≫ g₁' = k') :
    (modulePullbackTriangle B S hS hk').inv.app
          (SheafOfModules.unit (structureRingSheaf B S hS Y₀)) ≫
        (modulePullbackUnitIso B S hS k').hom =
      (modulePullback B S hS g₂').map (modulePullbackUnitIso B S hS g₁').hom ≫
        (modulePullbackUnitIso B S hS g₂').hom := by
  subst hk'
  rw [modulePullbackTriangle_rfl, Iso.symm_inv]
  exact modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom B S hS g₂' g₁'

/-- The direct image along `π₂` of
`modulePullbackTriangle_inv_app_comp_modulePullbackUnitIso_hom`. -/
private theorem smallBaseChangeModulePushforward_map_triangle_unit
    (hπ₂ : yoneda.relativelyRepresentable π₂.hom) {k' : Y₂ ⟶ Y₀} (hk' : g₂' ≫ g₁' = k') :
    (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map
          ((modulePullbackTriangle B S hS hk').inv.app
            (SheafOfModules.unit (structureRingSheaf B S hS Y₀))) ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map
          (modulePullbackUnitIso B S hS k').hom =
      (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map
          ((modulePullback B S hS g₂').map (modulePullbackUnitIso B S hS g₁').hom) ≫
        (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map
          (modulePullbackUnitIso B S hS g₂').hom :=
  ((smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map_comp _ _).symm.trans
    ((congrArg (smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map
        (modulePullbackTriangle_inv_app_comp_modulePullbackUnitIso_hom hk')).trans
      ((smallBaseChangeModulePushforward.{u, u} B S hS π₂ hπ₂).map_comp _ _))

/-- **The affine base change isomorphisms of `π_*𝒪` paste.**  For cartesian squares
`(g₁', π₁, π₀, g₁)` and `(g₂', π₂, π₁, g₂)` with `π₀` and `π₁` affine, and the outer cartesian
square along `k = g₂ ≫ g₁`, `k' = g₂' ≫ g₁'`, the isomorphism `k^*(π₀_*𝒪_{Y₀}) ≅ π₂_*𝒪_{Y₂}` of
the outer square is the comparison `k^* ≅ g₂^* g₁^*`
(`AlgebraicGeometry.Space.modulePullbackTriangle`) followed by `g₂^*` of the isomorphism
`g₁^*(π₀_*𝒪_{Y₀}) ≅ π₁_*𝒪_{Y₁}` of the right square and the isomorphism
`g₂^*(π₁_*𝒪_{Y₁}) ≅ π₂_*𝒪_{Y₂}` of the left square. -/
theorem modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom_paste
    (sq₁ : IsPullback g₁' π₁ π₀ g₁) (sq₂ : IsPullback g₂' π₂ π₁ g₂)
    {k : X₂ ⟶ X₀} {k' : Y₂ ⟶ Y₀} (hk : g₂ ≫ g₁ = k) (hk' : g₂' ≫ g₁' = k')
    (sq : IsPullback k' π₂ π₀ k)
    (hπa₀ : IsAffineHom B S hS π₀.hom) (hπa₁ : IsAffineHom B S hS π₁.hom)
    (hπ₀ : yoneda.relativelyRepresentable π₀.hom) (hπ₁ : yoneda.relativelyRepresentable π₁.hom)
    (hπ₂ : yoneda.relativelyRepresentable π₂.hom) :
    (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq hπa₀ hπ₀ hπ₂).hom =
      (modulePullbackTriangle B S hS hk).hom.app
          ((smallBaseChangeModulePushforward.{u, u} B S hS π₀ hπ₀).obj
            (SheafOfModules.unit (structureRingSheaf B S hS Y₀))) ≫
        (modulePullback B S hS g₂).map
          (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₁ hπa₀ hπ₀ hπ₁).hom ≫
        (modulePullbackSmallBaseChangeModulePushforwardUnitIso sq₂ hπa₁ hπ₁ hπ₂).hom := by
  have hF' : ((modulePullback B S hS g₁').obj
      (SheafOfModules.unit (structureRingSheaf B S hS Y₀))).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (modulePullbackUnitIso B S hS g₁').symm
      (SheafOfModules.isQuasicoherentOnSite_unit _)
  have hgen := smallBaseChangeModuleAffineBaseChangeIso_hom_paste sq₁ sq₂ hk hk' sq hπa₀ hπa₁
    hπ₀ hπ₁ hπ₂ (SheafOfModules.unit (structureRingSheaf B S hS Y₀))
    (SheafOfModules.isQuasicoherentOnSite_unit _) hF'
  have hb := modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom sq hπa₀ hπ₀ hπ₂
  have hb₁ := modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom sq₁ hπa₀ hπ₀ hπ₁
  have hb₂ := modulePullbackSmallBaseChangeModulePushforwardUnitIso_hom sq₂ hπa₁ hπ₁ hπ₂
  have hnat := smallBaseChangeModuleAffineBaseChangeIso_hom_naturality sq₂ hπa₁ hπ₁ hπ₂
    (F := (modulePullback B S hS g₁').obj (SheafOfModules.unit (structureRingSheaf B S hS Y₀)))
    (G := SheafOfModules.unit (structureRingSheaf B S hS Y₁)) hF'
    (SheafOfModules.isQuasicoherentOnSite_unit _) (modulePullbackUnitIso B S hS g₁').hom
  refine paste_unit (modulePullbackTriangle B S hS hk) (n₁ := ?n₁) (p₁ := ?p₁) (n₂ := ?n₂)
    (p₂ := ?p₂) (n₂' := ?n₂') (r := ?r) (nout := ?nout) (qk := ?qk) (m := ?m)
    (A₀ := ?A₀) (V₁ := ?V₁) (V₁' := ?V₁') (R₁ := ?R₁) (R₂ := ?R₂) (R₃ := ?R₃) (R₄ := ?R₄)
    (b := ?b) (b₁ := ?b₁) (b₂ := ?b₂)
    ?hb₁ ?hb₂ ?hnat ?hb ?hgen ?hU
  case hb₁ => exact hb₁
  case hb₂ => exact hb₂
  case hb => exact hb
  case hnat => exact hnat
  case hgen =>
    refine hgen.trans ?_
    rfl
  case hU =>
    exact (Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (smallBaseChangeModulePushforward_map_triangle_unit hπ₂ hk'))

end AlgebraicGeometry.Space

end


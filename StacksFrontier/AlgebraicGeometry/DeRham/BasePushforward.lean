module

public import StacksFrontier.AlgebraicGeometry.DeRham.InverseImageLinear
public import StacksFrontier.Topology.Sheaves.Functors.Pullback.Comp
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpaceTransitivityTriangle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.DeRhamOrderOne
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness

/-!
# The direct image of sheaves of modules over the base rings

Let `g : Y ⟶ X` and `f : X ⟶ S` be morphisms of schemes. The relative de Rham complex of `Y`
over `S` lives in sheaves of `(g ≫ f)^{-1}𝒪_S`-modules on `Y` and that of `X` in sheaves of
`f^{-1}𝒪_S`-modules on `X`. This file constructs the direct image between the two categories,
along the comparison of base rings `f^{-1}𝒪_S ⟶ g_*((g ≫ f)^{-1}𝒪_S)`, and shows that for a
closed immersion it is exact.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.baseRingCompHom`: the comparison of base rings.
* `AlgebraicGeometry.Scheme.Hom.basePushforward`: **the direct image over the base rings.**
* `AlgebraicGeometry.Scheme.Hom.basePushforwardToBaseModulesIso`: the direct image of an
  `𝒪_Y`-module read over the base is the direct image `g_*` read over the base.

## Main results

* `AlgebraicGeometry.Scheme.Hom.baseRingCompHom_comp_inverseImageStructureMap`: the comparison
  of base rings is compatible with the structural maps and `g^♯`.
* `AlgebraicGeometry.Scheme.Hom.preservesFiniteLimits_basePushforward`,
  `AlgebraicGeometry.Scheme.Hom.preservesFiniteColimits_basePushforward`: for a closed immersion
  the direct image is exact (Stacks Tag 01AX).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Y X S : Scheme.{u}} (g : Y ⟶ X) (f : X ⟶ S)

/-- The comparison of base rings along `g : Y ⟶ X`, `f^{-1}𝒪_S ⟶ g_*((g ≫ f)^{-1}𝒪_S)`: the unit
of `g^{-1} ⊣ g_*` followed by the identification `g^{-1}f^{-1}𝒪_S ≅ (g ≫ f)^{-1}𝒪_S`. -/
def baseRingCompHom :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} (g ≫ f).base).obj S.sheaf) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit.app
      ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf) ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
      ((sheafPullbackCompIso g.base f.base CommRingCat.{u}).inv.app S.sheaf)

/-- **The comparison of base rings is compatible with the structural maps**: followed by the
direct image of `(g ≫ f)^{-1}𝒪_S ⟶ 𝒪_Y` it is `f^{-1}𝒪_S ⟶ 𝒪_X` followed by `g^♯`. -/
theorem baseRingCompHom_comp_inverseImageStructureMap :
    baseRingCompHom g f ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).map
        (inverseImageStructureMap (g ≫ f)) =
      inverseImageStructureMap f ≫
        (⟨g.c⟩ : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Y.sheaf) := by
  have hinv : (sheafPullbackCompIso g.base f.base CommRingCat.{u}).inv.app S.sheaf ≫
      inverseImageStructureMap (g ≫ f) =
      (TopCat.Sheaf.pullback CommRingCat.{u} g.base).map (inverseImageStructureMap f) ≫
        inverseImageStructureMap g :=
    (Iso.inv_comp_eq ((sheafPullbackCompIso g.base f.base CommRingCat.{u}).app S.sheaf)).mpr <|
      Eq.symm <|
      Stacks.Sheaves.RingedSpaceCotangent.sheafPullbackCompIso_hom_app_comp_inverseImageStructureMap
        (Stacks.Smooth.ringedSpaceHom g) (Stacks.Smooth.ringedSpaceHom f)
  let P := TopCat.Sheaf.pushforward CommRingCat.{u} g.base
  let ε := (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.base).unit
  calc ε.app _ ≫ P.map ((sheafPullbackCompIso g.base f.base CommRingCat.{u}).inv.app S.sheaf) ≫
        P.map (inverseImageStructureMap (g ≫ f))
      = ε.app _ ≫ P.map ((sheafPullbackCompIso g.base f.base CommRingCat.{u}).inv.app S.sheaf ≫
          inverseImageStructureMap (g ≫ f)) :=
        congrArg (ε.app _ ≫ ·) (P.map_comp _ _).symm
    _ = ε.app _ ≫ P.map ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).map
          (inverseImageStructureMap f) ≫ inverseImageStructureMap g) :=
        congrArg (fun k => ε.app _ ≫ P.map k) hinv
    _ = (ε.app _ ≫ P.map ((TopCat.Sheaf.pullback CommRingCat.{u} g.base).map
          (inverseImageStructureMap f))) ≫ P.map (inverseImageStructureMap g) :=
        (congrArg (ε.app _ ≫ ·) (P.map_comp _ _)).trans (Category.assoc _ _ _).symm
    _ = (inverseImageStructureMap f ≫ ε.app X.sheaf) ≫ P.map (inverseImageStructureMap g) :=
        congrArg (· ≫ P.map (inverseImageStructureMap g)) (ε.naturality _).symm
    _ = inverseImageStructureMap f ≫
          (⟨g.c⟩ : X.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj Y.sheaf) :=
        (Category.assoc _ _ _).trans (congrArg (inverseImageStructureMap f ≫ ·)
          (unit_comp_pushforward_inverseImageStructureMap g))

/-- The comparison of base rings, as a morphism of sheaves of rings
`f^{-1}𝒪_S ⟶ g_*((g ≫ f)^{-1}𝒪_S)`. -/
abbrev baseRingCompRingHom :
    baseRingSheaf f ⟶ ((Opens.map g.base).sheafPushforwardContinuous RingCat.{u} _ _).obj
      (baseRingSheaf (g ≫ f)) :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (baseRingCompHom g f)

/-- **The direct image of sheaves of modules over the base rings** along `g : Y ⟶ X`:
sheaves of `(g ≫ f)^{-1}𝒪_S`-modules on `Y` to sheaves of `f^{-1}𝒪_S`-modules on `X`. -/
abbrev basePushforward :
    _root_.SheafOfModules.{u} (baseRingSheaf (g ≫ f)) ⥤
      _root_.SheafOfModules.{u} (baseRingSheaf f) :=
  _root_.SheafOfModules.pushforward (baseRingCompRingHom g f)

/-- On sections over `U`, the comparison of base rings followed by the structural map of
`g ≫ f` is the structural map of `f` followed by `g^♯`. -/
theorem baseFn_baseRingCompHom (U : X.Opens) (a : (baseRingSheaf f).obj.obj (op U)) :
    baseFn (g ≫ f) ((baseRingCompRingHom g f).hom.app (op U) a) = (g.app U).hom (baseFn f a) :=
  congrArg (fun φ => (φ.hom.app (op U)).hom a) (baseRingCompHom_comp_inverseImageStructureMap g f)

/-- **The direct image of an `𝒪_Y`-module read over the base is the direct image read over the
base**: `g_*` of `M` read as a `(g ≫ f)^{-1}𝒪_S`-module is `g_*M` read as an `f^{-1}𝒪_S`-module,
the identity on underlying abelian sheaves. -/
def basePushforwardToBaseModulesHom (M : Y.Modules) :
    (basePushforward g f).obj ((toBaseModules (g ≫ f)).obj M) ⟶
      (toBaseModules f).obj ((Scheme.Modules.pushforward g).obj M) :=
  ⟨PresheafOfModules.homMk (𝟙 _) fun U a m =>
    (congrArg (fun r : Γ(Y, g ⁻¹ᵁ U.unop) => r • (show Γ(M, g ⁻¹ᵁ U.unop) from m))
      (baseFn_baseRingCompHom g f U.unop a) :)⟩

/-- The inverse of `AlgebraicGeometry.Scheme.Hom.basePushforwardToBaseModulesHom`. -/
def toBaseModulesBasePushforwardHom (M : Y.Modules) :
    (toBaseModules f).obj ((Scheme.Modules.pushforward g).obj M) ⟶
      (basePushforward g f).obj ((toBaseModules (g ≫ f)).obj M) :=
  ⟨PresheafOfModules.homMk (𝟙 _) fun U a m =>
    ((congrArg (fun r : Γ(Y, g ⁻¹ᵁ U.unop) => r • (show Γ(M, g ⁻¹ᵁ U.unop) from m))
      (baseFn_baseRingCompHom g f U.unop a)).symm :)⟩

/-- The identification of the two readings of a direct image over the base. -/
def basePushforwardToBaseModulesIso (M : Y.Modules) :
    (basePushforward g f).obj ((toBaseModules (g ≫ f)).obj M) ≅
      (toBaseModules f).obj ((Scheme.Modules.pushforward g).obj M) where
  hom := basePushforwardToBaseModulesHom g f M
  inv := toBaseModulesBasePushforwardHom g f M
  hom_inv_id := _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))
  inv_hom_id := _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ =>
    ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-- The direct image over the base, read in abelian sheaves, is the direct image of abelian
sheaves. -/
def basePushforwardCompToSheafIso :
    basePushforward g f ⋙ _root_.SheafOfModules.toSheaf (baseRingSheaf f) ≅
      _root_.SheafOfModules.toSheaf (baseRingSheaf (g ≫ f)) ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-- The inverse of `AlgebraicGeometry.Scheme.Hom.basePushforwardToBaseModulesIso` is the
identity on underlying abelian sheaves. -/
theorem toSheaf_map_basePushforwardToBaseModulesIso_inv (M : Y.Modules) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).map
        (basePushforwardToBaseModulesIso g f M).inv = 𝟙 _ :=
  rfl

/-- The forward map of `AlgebraicGeometry.Scheme.Hom.basePushforwardToBaseModulesIso` is the
identity on underlying abelian sheaves. -/
theorem toSheaf_map_basePushforwardToBaseModulesIso_hom (M : Y.Modules) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).map
        (basePushforwardToBaseModulesIso g f M).hom = 𝟙 _ :=
  rfl

/-- On underlying abelian sheaves, the direct image over the base of a morphism `φ` is the direct
image `g_*` of the underlying morphism of abelian sheaves. -/
theorem toSheaf_map_basePushforward_map {M N : _root_.SheafOfModules.{u} (baseRingSheaf (g ≫ f))}
    (φ : M ⟶ N) :
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).map ((basePushforward g f).map φ) =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).map
        ((_root_.SheafOfModules.toSheaf (baseRingSheaf (g ≫ f))).map φ) :=
  rfl

/-- The direct image over the base is an additive functor. -/
instance additive_basePushforward : (basePushforward g f).Additive where
  map_add := rfl

variable [IsClosedImmersion g]

/-- **The direct image over the base along a closed immersion preserves finite colimits.** -/
instance preservesFiniteColimits_basePushforward :
    Limits.PreservesFiniteColimits (basePushforward g f) := by
  have : (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).ReflectsIsomorphisms :=
    Stacks.SheafOfModules.Constant.reflectsIsomorphisms_toSheaf _
  have h1 := Stacks.ClosedImmersion.preservesFiniteColimits_closedInclusionPushforward g.base
    g.isClosedEmbedding
  have h2 : Limits.PreservesFiniteColimits
      (_root_.SheafOfModules.toSheaf (baseRingSheaf (g ≫ f))) := inferInstance
  have h3 := @Limits.comp_preservesFiniteColimits _ _ _ _ _ _ _ _ h2 h1
  have : Limits.PreservesFiniteColimits (basePushforward g f ⋙
      _root_.SheafOfModules.toSheaf (baseRingSheaf f)) :=
    @Limits.preservesFiniteColimits_of_natIso _ _ _ _ _ _
      (basePushforwardCompToSheafIso g f).symm h3
  exact Limits.preservesFiniteColimits_of_reflects_of_preserves _
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f))

/-- **The direct image over the base along a closed immersion preserves finite limits.** -/
instance preservesFiniteLimits_basePushforward :
    Limits.PreservesFiniteLimits (basePushforward g f) := by
  have : (_root_.SheafOfModules.toSheaf (baseRingSheaf f)).ReflectsIsomorphisms :=
    Stacks.SheafOfModules.Constant.reflectsIsomorphisms_toSheaf _
  have h1 := Stacks.ClosedImmersion.preservesFiniteLimits_closedInclusionPushforward g.base
    g.isClosedEmbedding
  have h2 : Limits.PreservesFiniteLimits
      (_root_.SheafOfModules.toSheaf (baseRingSheaf (g ≫ f))) := inferInstance
  have h3 := @Limits.comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h2 h1
  have : Limits.PreservesFiniteLimits (basePushforward g f ⋙
      _root_.SheafOfModules.toSheaf (baseRingSheaf f)) :=
    @Limits.preservesFiniteLimits_of_natIso _ _ _ _ _ _ (basePushforwardCompToSheafIso g f).symm h3
  exact Limits.preservesFiniteLimits_of_reflects_of_preserves _
    (_root_.SheafOfModules.toSheaf (baseRingSheaf f))

end AlgebraicGeometry.Scheme.Hom

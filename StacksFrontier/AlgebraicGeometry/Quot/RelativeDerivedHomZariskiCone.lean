module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomZariskiDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMonomorphismModuleCounit

/-!
# The base changes over the opens of a test scheme

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `T` a test scheme over `Y` and
`h₀ : Z₀ ⟶ T` a morphism of the site.  The opens `W` of the underlying scheme of `Z₀` give test
schemes `T_W = restrictTest T (W ⟶ Z₀ ⟶ T)` (`AlgebraicGeometry.Space.zarOpensTest`), and the
base changes `X_{T_W}` form a cone over `X_{T_{Z₀}}` (`AlgebraicGeometry.Space.zarCone`) whose
legs and transition morphisms are étale monomorphisms, being base changes of open immersions.
This is the cone along which the Zariski gluing of `T ↦ Hom(K_T, E_T)` is carried out.

Nothing here is registered.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The inclusion of an open `W` of `Z` into itself is the identity. -/
theorem BigFppfOver.openSubHomOfLE_self (Z : BigFppfOver B S hS) (W : Z.left.obj.Opens) :
    BigFppfOver.openSubHomOfLE B S hS Z (le_refl W) = 𝟙 _ :=
  Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <| Scheme.homOfLE_rfl _ _

/-- The inclusions of opens `V ≤ W ≤ W'` of `Z` compose to the inclusion of `V` into `W'`. -/
theorem BigFppfOver.openSubHomOfLE_comp_openSubHomOfLE (Z : BigFppfOver B S hS)
    {V W W' : Z.left.obj.Opens} (h : V ≤ W) (h' : W ≤ W') :
    BigFppfOver.openSubHomOfLE B S hS Z h ≫ BigFppfOver.openSubHomOfLE B S hS Z h' =
      BigFppfOver.openSubHomOfLE B S hS Z (h.trans h') :=
  Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <| Scheme.homOfLE_homOfLE _ h h'

variable {X Y : AlgebraicSpaces B S hS}

/-- **The test schemes over the opens of `Z₀`**, `W ↦ T_W`. -/
def zarOpensTest (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left) :
    Z₀.left.obj.Opens ⥤ SchemesOver Y where
  obj W := restrictTest T (BigFppfOver.openSubHom B S hS Z₀ W ≫ h₀)
  map g := restrictTestMap T (BigFppfOver.openSubHomOfLE B S hS Z₀ (leOfHom g))
    (openSubHomOfLE_comp_openSubHom_comp h₀ _)
  map_id W := CostructuredArrow.hom_ext _ _ (BigFppfOver.openSubHomOfLE_self Z₀ W)
  map_comp _ _ := CostructuredArrow.hom_ext _ _
    (BigFppfOver.openSubHomOfLE_comp_openSubHomOfLE Z₀ _ _).symm

/-- The morphism `T_W ⟶ T_{Z₀}`. -/
abbrev zarLeg (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)
    (W : Z₀.left.obj.Opens) : (zarOpensTest T h₀).obj W ⟶ restrictTest T h₀ :=
  restrictTestMap T (BigFppfOver.openSubHom B S hS Z₀ W) rfl

/-- The legs `T_W ⟶ T_{Z₀}` commute with the transition morphisms `T_V ⟶ T_W`. -/
theorem zarLeg_w (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)
    {V W : Z₀.left.obj.Opens} (g : V ⟶ W) :
    (zarOpensTest T h₀).map g ≫ zarLeg T h₀ W = zarLeg T h₀ V :=
  CostructuredArrow.hom_ext _ _ (BigFppfOver.openSubHomOfLE_comp_openSubHom B S hS Z₀ _)

variable (f : X ⟶ Y)

/-- **The base changes over the opens of `Z₀`**, `W ↦ X_{T_W}`. -/
abbrev zarSpaces (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left) :
    Z₀.left.obj.Opens ⥤ AlgebraicSpaces B S hS :=
  zarOpensTest T h₀ ⋙ schemesOverToOver Y ⋙ overBaseChangeFunctor f ⋙ Over.forget X

/-- **The cone of the base changes over the opens of `Z₀`**, over `X_{T_{Z₀}}`. -/
def zarCone (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left) :
    PullbackData.ConeTo (zarSpaces f T h₀) (baseChangeSpace f (restrictTest T h₀)) where
  leg W := overBaseChangeMap f ((schemesOverToOver Y).map (zarLeg T h₀ W))
  w {V W} g := by
    have := (overBaseChangeMap_comp f ((schemesOverToOver Y).map ((zarOpensTest T h₀).map g))
      ((schemesOverToOver Y).map (zarLeg T h₀ W))).symm
    rw [← Functor.map_comp, zarLeg_w] at this
    exact this

/-- The base change of a morphism of test schemes whose underlying morphism is étale is
étale. -/
theorem isEtale_overBaseChangeMap_of_etale {U T : SchemesOver Y} (g : U ⟶ T)
    (hg : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map g.left)) :
    IsEtale B S hS (overBaseChangeMap f ((schemesOverToOver Y).map g)).hom :=
  isEtale_of_isPullback B S hS _ _ _ _ (isPullback_overBaseChangeMap f _).flip
    (isEtale_schemeSpaceMap B S hS U.left g.left hg)

/-- The base change of a morphism of test schemes whose underlying morphism is a monomorphism is
a monomorphism. -/
theorem mono_overBaseChangeMap_of_mono {U T : SchemesOver Y} (g : U ⟶ T)
    [Mono ((BigFppfOver.toScheme B S hS).map g.left)] :
    Mono (overBaseChangeMap f ((schemesOverToOver Y).map g)).hom := by
  have : Mono g.left := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have : Mono ((schemesOverToOver Y).map g).left.hom :=
    inferInstanceAs (Mono (yoneda.map g.left))
  exact (AlgebraicSpaces.isPullback_hom B S hS
    (isPullback_overBaseChangeMap f ((schemesOverToOver Y).map g))).mono_fst_of_mono

/-- The legs `X_{T_W} ⟶ X_{T_{Z₀}}` of the cone are étale. -/
theorem isEtale_zarCone_leg (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)
    (W : Z₀.left.obj.Opens) : IsEtale B S hS ((zarCone f T h₀).leg W).hom :=
  isEtale_overBaseChangeMap_of_etale f _ (inferInstanceAs (AlgebraicGeometry.Etale W.ι))

/-- The legs `X_{T_W} ⟶ X_{T_{Z₀}}` of the cone are monomorphisms. -/
instance mono_zarCone_leg (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)
    (W : Z₀.left.obj.Opens) : Mono ((zarCone f T h₀).leg W).hom :=
  haveI : Mono ((BigFppfOver.toScheme B S hS).map (zarLeg T h₀ W).left) :=
    inferInstanceAs (Mono W.ι)
  mono_overBaseChangeMap_of_mono f _

/-- The transition morphisms `X_{T_V} ⟶ X_{T_W}` are étale. -/
theorem isEtale_zarSpaces_map (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)
    {V W : Z₀.left.obj.Opens} (g : V ⟶ W) : IsEtale B S hS ((zarSpaces f T h₀).map g).hom :=
  isEtale_overBaseChangeMap_of_etale f ((zarOpensTest T h₀).map g)
    (inferInstanceAs (AlgebraicGeometry.Etale (Z₀.left.obj.homOfLE (leOfHom g))))

/-- The transition morphisms `X_{T_V} ⟶ X_{T_W}` are monomorphisms. -/
instance mono_zarSpaces_map (T : SchemesOver Y) {Z₀ : BigFppfOver B S hS} (h₀ : Z₀ ⟶ T.left)
    {V W : Z₀.left.obj.Opens} (g : V ⟶ W) : Mono ((zarSpaces f T h₀).map g).hom :=
  haveI : Mono ((BigFppfOver.toScheme B S hS).map ((zarOpensTest T h₀).map g).left) :=
    inferInstanceAs (Mono (Z₀.left.obj.homOfLE (leOfHom g)))
  mono_overBaseChangeMap_of_mono f ((zarOpensTest T h₀).map g)

end AlgebraicGeometry.Space

end

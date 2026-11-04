module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleKunnethMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CoefficientChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoOfIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionMapComposite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.TensorBaseChangeProjection

/-!
# Change of coefficients on `D(-_étale, Λ)`

Let `φ : Λ ⟶ Λ'` be a map of commutative rings. On the small model of the small étale site of a
scheme `Z` it induces a map of constant sheaves of rings `Λ̲ ⟶ Λ̲'` (`coefficientMap`), and so a
morphism of ringed topoi `c_Z : (Z_étale, Λ̲') ⟶ (Z_étale, Λ̲)` whose underlying morphism of sites
is the identity (`coefficientHom`, the change of coefficients
`AlgebraicGeometry.RingedToposSiteHom.coefficientChange`). Its derived pullback
`Lc_Z^* : D(Z_étale, Λ) ⥤ D(Z_étale, Λ')` is `- ⊗^L_Λ Λ'`, its derived direct image
`Rc_{Z,*} : D(Z_étale, Λ') ⥤ D(Z_étale, Λ)` is restriction of scalars, and it has a projection
map `K ⊗^L_Λ Rc_*N ⟶ Rc_*(Lc^*K ⊗^L_{Λ'} N)` (`coefficientProjectionMap`).

For a morphism of schemes `h : Y ⟶ X` the morphisms of ringed topoi `h ∘ c_Y` and `c_X ∘ h`
from `(Y_étale, Λ̲')` to `(X_étale, Λ̲)` agree (`fSharpCompatible_coefficientHom_square`), so the
derived pullbacks commute (`coefficientPullbackSquareIso`), compatibly with the comparisons of
[Stacks, Tag 07A4] (`tensorCompat_coefficientPullbackSquareIso`).

The projection map of `h` over `Λ` at `(A, Rc_{Y,*}N)` is invertible as soon as the one over `Λ'`
at `(Lc_X^*A, N)` is and the projection maps of the coefficient changes at `(A, Rh_*N)` and
`(h⁻¹A, N)` are (`isIso_projectionMap_coefficientPushforward_of_isIso`).

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

attribute [local instance] HasDerivedCategory.standard

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

section Hom

/-- **The map of constant sheaves of rings `Λ̲ ⟶ Λ̲'`** induced by `φ` on the small model of the
small étale site of `Z`. -/
def coefficientMap (Z : Scheme.{u}) : (ringedTopos Λ Z).O ⟶ (ringedTopos Λ' Z).O :=
  (constantSheaf (topology Z) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ)

/-- **The change of coefficients `c_Z : (Z_étale, Λ̲') ⟶ (Z_étale, Λ̲)`** along `φ`, a morphism of
ringed topoi over the identity of the site. -/
abbrev coefficientHom (Z : Scheme.{u}) :
    RingedToposSiteHom (ringedTopos Λ' Z) (ringedTopos Λ Z) :=
  RingedToposSiteHom.coefficientChange (topology Z) (coefficientMap φ Z)

/-- The underlying functor of a change of coefficients is a morphism of sites. -/
theorem isMorphismOfSites_coefficientHom (Z : Scheme.{u}) :
    (coefficientHom φ Z).u.IsMorphismOfSites (ringedTopos Λ Z).J (ringedTopos Λ' Z).J :=
  Functor.isMorphismOfSites_id _

/-- The derived pullback along a change of coefficients exists (Stacks 06YY). -/
instance hasLeftDerivedFunctor_coefficientHom (Z : Scheme.{u}) :
    (pullbackOnHomotopy (coefficientHom φ Z)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Z).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ' Z) (Y := ringedTopos Λ Z) _ (isMorphismOfSites_coefficientHom φ Z)

/-- **The derived change of coefficients** `Lc_Z^* : D(Z_étale, Λ) ⥤ D(Z_étale, Λ')`. -/
abbrev coefficientPullback (Z : Scheme.{u}) : DerivedModules Λ Z ⥤ DerivedModules Λ' Z :=
  derivedPullback (X := ringedTopos Λ' Z) (Y := ringedTopos Λ Z) (coefficientHom φ Z)

/-- **The derived restriction of scalars** `Rc_{Z,*} : D(Z_étale, Λ') ⥤ D(Z_étale, Λ)`. -/
abbrev coefficientPushforward (Z : Scheme.{u}) : DerivedModules Λ' Z ⥤ DerivedModules Λ Z :=
  derivedPushforward (X := ringedTopos Λ' Z) (Y := ringedTopos Λ Z) (coefficientHom φ Z)

/-- The adjunction `Lc_Z^* ⊣ Rc_{Z,*}` (Stacks 07A6). -/
def coefficientAdjunction (Z : Scheme.{u}) :
    coefficientPullback φ Z ⊣ coefficientPushforward φ Z :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction (X := ringedTopos Λ' Z)
    (Y := ringedTopos Λ Z) (coefficientHom φ Z) (isMorphismOfSites_coefficientHom φ Z)

/-- The comparison `Lc^*(M ⊗^L N) ≅ Lc^*M ⊗^L Lc^*N` (Stacks 07A4). -/
def coefficientTensorIso (Z : Scheme.{u}) :
    Functor.uncurry.obj (tensor Λ Z) ⋙ coefficientPullback φ Z ≅
      (coefficientPullback φ Z).prod (coefficientPullback φ Z) ⋙
        Functor.uncurry.obj (tensor Λ' Z) :=
  Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (X := ringedTopos Λ' Z)
    (Y := ringedTopos Λ Z) (coefficientHom φ Z) (isMorphismOfSites_coefficientHom φ Z)

/-- **The projection map of a change of coefficients**,
`K ⊗^L_Λ Rc_*N ⟶ Rc_*(Lc^*K ⊗^L_{Λ'} N)`. -/
def coefficientProjectionMap (Z : Scheme.{u}) (K : DerivedModules Λ Z)
    (N : DerivedModules Λ' Z) :
    ((tensor Λ Z).obj K).obj ((coefficientPushforward φ Z).obj N) ⟶
      (coefficientPushforward φ Z).obj
        (((tensor Λ' Z).obj ((coefficientPullback φ Z).obj K)).obj N) :=
  Stacks.Cohomology.AbstractKunnethMap.projectionMap (Functor.uncurry.obj (tensor Λ Z))
    (Functor.uncurry.obj (tensor Λ' Z)) (coefficientAdjunction φ Z)
    (coefficientTensorIso φ Z).hom K N

end Hom

section Square

/-- The sheafification unit of the constant presheaf, followed by the coefficient map, is `φ`
followed by the sheafification unit. -/
theorem toSheafify_app_comp_coefficientMap_app (Z : Scheme.{u}) (V : (Site Z)ᵒᵖ) :
    (toSheafify (topology Z) ((Functor.const _).obj (CommRingCat.of Λ))).app V ≫
        (coefficientMap φ Z).hom.app V =
      CommRingCat.ofHom φ ≫
        (toSheafify (topology Z) ((Functor.const _).obj (CommRingCat.of Λ'))).app V :=
  (congr_app (toSheafify_naturality (topology Z)
    ((Functor.const (Site Z)ᵒᵖ).map (CommRingCat.ofHom φ))) V).symm

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- The underlying functors of the two factorizations of `(Y_étale, Λ̲') ⟶ (X_étale, Λ̲)` are
both base change along `h`. -/
def coefficientSquareIso :
    ((coefficientHom (Λ := Λ) φ X).comp (ringedToposHom Λ' h)).u ≅
      ((ringedToposHom Λ h).comp (coefficientHom φ Y)).u :=
  Functor.leftUnitor (baseChange h) ≪≫ (Functor.rightUnitor (baseChange h)).symm

/-- **The two factorizations of `(Y_étale, Λ̲') ⟶ (X_étale, Λ̲)` agree**: `h` after the change of
coefficients on `Y`, and the change of coefficients on `X` after `h`. -/
theorem fSharpCompatible_coefficientHom_square :
    RingedToposSiteHom.FSharpCompatible ((ringedToposHom Λ h).comp (coefficientHom φ Y))
      ((coefficientHom φ X).comp (ringedToposHom Λ' h)) (coefficientSquareIso φ h) := by
  have := ((coefficientHom φ X).comp (ringedToposHom Λ' h)).isContinuous
  have := ((ringedToposHom Λ h).comp (coefficientHom φ Y)).isContinuous
  have c₂ : (Functor.sheafPushforwardContinuousNatTrans (coefficientSquareIso φ h).hom
      CommRingCat.{u + 1} (ringedTopos Λ X).J (ringedTopos Λ' Y).J).app (ringedTopos Λ' Y).O =
        𝟙 _ := by
    have e : ∀ V, (coefficientSquareIso φ h).hom.app V = 𝟙 _ := fun V =>
      Category.id_comp _
    ext V : 3
    simp only [Functor.sheafPushforwardContinuousNatTrans, Functor.whiskerRight_app,
      NatTrans.op_app, e]
    exact CategoryTheory.Functor.map_id _ _
  unfold RingedToposSiteHom.FSharpCompatible
  rw [c₂]
  refine (Category.comp_id _).trans ?_
  show structureMap Λ h ≫
      ((baseChange h).sheafPushforwardContinuous CommRingCat.{u + 1} (topology X) (topology Y)).map
        (coefficientMap φ Y) ≫ 𝟙 _ =
    coefficientMap φ X ≫ structureMap Λ' h ≫ 𝟙 _
  refine Sheaf.hom_ext (sheafify_hom_ext (topology X) _ _
    (ObjectProperty.FullSubcategory.property _) ?_)
  refine NatTrans.ext (funext fun V => ?_)
  have h₁ := toSheafify_app_comp_structureMap_app Λ h V
  have h₂ := toSheafify_app_comp_coefficientMap_app φ Y
    (Opposite.op ((baseChange h).obj V.unop))
  have h₃ := toSheafify_app_comp_coefficientMap_app φ X V
  have h₄ := toSheafify_app_comp_structureMap_app Λ' h V
  show (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ))).app V ≫
      (structureMap Λ h).hom.app V ≫ (coefficientMap φ Y).hom.app
        (Opposite.op ((baseChange h).obj V.unop)) =
    (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ))).app V ≫
      (coefficientMap φ X).hom.app V ≫ (structureMap Λ' h).hom.app V
  exact ((Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans h₂)).trans
    ((Category.assoc _ _ _).symm.trans ((h₃ =≫ _).trans
      ((Category.assoc _ _ _).trans (_ ≫= h₄)))).symm

/-- The derived pullback along `h` after the change of coefficients on `Y` exists. -/
instance hasLeftDerivedFunctor_ringedToposHom_comp_coefficientHom :
    (pullbackOnHomotopy ((ringedToposHom Λ h).comp (coefficientHom φ Y))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ' Y) (Y := ringedTopos Λ X) _
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_coefficientHom φ Y)
      (isMorphismOfSites_ringedToposHom Λ h))

/-- The derived pullback along the change of coefficients on `X` after `h` exists. -/
instance hasLeftDerivedFunctor_coefficientHom_comp_ringedToposHom :
    (pullbackOnHomotopy ((coefficientHom φ X).comp (ringedToposHom Λ' h))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ' Y) (Y := ringedTopos Λ X) _
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ' h)
      (isMorphismOfSites_coefficientHom φ X))

/-- **Change of coefficients commutes with inverse images**, `h⁻¹ ⋙ Lc_Y^* ≅ Lc_X^* ⋙ h⁻¹`:
Stacks 0D6D for the two factorizations of `(Y_étale, Λ̲') ⟶ (X_étale, Λ̲)`, which agree by
`fSharpCompatible_coefficientHom_square`. -/
def coefficientPullbackSquareIso :
    pullback Λ h ⋙ coefficientPullback φ Y ≅ coefficientPullback φ X ⋙ pullback Λ' h :=
  Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
      (coefficientHom φ Y) (ringedToposHom Λ h) (isMorphismOfSites_coefficientHom φ Y)
      (isMorphismOfSites_ringedToposHom Λ h) ≪≫
    derivedPullbackIsoOfIso (fSharpCompatible_coefficientHom_square φ h) ≪≫
    (Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
      (ringedToposHom Λ' h) (coefficientHom φ X) (isMorphismOfSites_ringedToposHom Λ' h)
      (isMorphismOfSites_coefficientHom φ X)).symm

open Stacks.Cohomology.AbstractKunnethMap in
/-- **`coefficientPullbackSquareIso` is compatible with the comparisons of Stacks 07A4**: it
carries the composite comparison of `h⁻¹ ⋙ Lc_Y^*` to that of `Lc_X^* ⋙ h⁻¹`. -/
theorem tensorCompat_coefficientPullbackSquareIso :
    TensorCompat (TC := Functor.uncurry.obj (tensor Λ X))
      (TD := Functor.uncurry.obj (tensor Λ' Y))
      (compTensor (pullbackTensorIso Λ h).hom (coefficientTensorIso φ Y).hom)
      (compTensor (coefficientTensorIso φ X).hom (pullbackTensorIso Λ' h).hom)
      (coefficientPullbackSquareIso φ h).hom := by
  have h₁ := Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp
    (coefficientHom φ Y) (ringedToposHom Λ h) (isMorphismOfSites_coefficientHom φ Y)
    (isMorphismOfSites_ringedToposHom Λ h)
  have h₂ := Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_isoOfIso
    (fSharpCompatible_coefficientHom_square φ h)
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_coefficientHom φ Y)
      (isMorphismOfSites_ringedToposHom Λ h))
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ' h)
      (isMorphismOfSites_coefficientHom φ X))
  have h₃ := Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_comp
    (ringedToposHom Λ' h) (coefficientHom φ X) (isMorphismOfSites_ringedToposHom Λ' h)
    (isMorphismOfSites_coefficientHom φ X)
  have t₁ : TensorCompat (TC := Functor.uncurry.obj (tensor Λ X))
      (TD := Functor.uncurry.obj (tensor Λ' Y))
      (compTensor (pullbackTensorIso Λ h).hom (coefficientTensorIso φ Y).hom) _
      (Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
        (coefficientHom φ Y) (ringedToposHom Λ h) (isMorphismOfSites_coefficientHom φ Y)
        (isMorphismOfSites_ringedToposHom Λ h)).hom := fun P Q => by
    have := NatTrans.congr_app h₁ (P, Q)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at this
    rw [this]
    simp [pullbackTensorIso, coefficientTensorIso]
  have t₃ : TensorCompat (TC := Functor.uncurry.obj (tensor Λ X))
      (TD := Functor.uncurry.obj (tensor Λ' Y))
      (compTensor (coefficientTensorIso φ X).hom (pullbackTensorIso Λ' h).hom) _
      (Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
        (ringedToposHom Λ' h) (coefficientHom φ X) (isMorphismOfSites_ringedToposHom Λ' h)
        (isMorphismOfSites_coefficientHom φ X)).hom := fun P Q => by
    have := NatTrans.congr_app h₃ (P, Q)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at this
    rw [this]
    simp [pullbackTensorIso, coefficientTensorIso]
  exact t₁.comp ((TensorCompat.of_eq h₂).comp t₃.symm)

end Square

section Reduction

open Stacks.Cohomology.AbstractKunnethMap

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- **The projection map over `Λ` at a restriction of scalars, from the one over `Λ'`.** For
`h : Y ⟶ X`, `A ∈ D(X_étale, Λ)` and `N ∈ D(Y_étale, Λ')`, the projection map
`A ⊗^L_Λ Rh_*Rc_*N ⟶ Rh_*(h⁻¹A ⊗^L_Λ Rc_*N)` of `h` over `Λ` is invertible as soon as the
projection map `Lc^*A ⊗^L_{Λ'} Rh_*N ⟶ Rh_*(h⁻¹Lc^*A ⊗^L_{Λ'} N)` of `h` over `Λ'` is, and the
projection maps of the changes of coefficients on `X` at `(A, Rh_*N)` and on `Y` at
`(h⁻¹A, N)` are. -/
theorem isIso_projectionMap_coefficientPushforward_of_isIso (A : DerivedModules Λ X)
    (N : DerivedModules Λ' Y)
    (h₁ : IsIso (coefficientProjectionMap φ X A ((pushforward Λ' h).obj N)))
    (h₂ : IsIso (coefficientProjectionMap φ Y ((pullback Λ h).obj A) N))
    (h₃ : IsIso (projectionMap Λ' h ((coefficientPullback φ X).obj A) N)) :
    IsIso (projectionMap Λ h A ((coefficientPushforward φ Y).obj N)) := by
  have e₁ := projectionMap_comp (Functor.uncurry.obj (tensor Λ X))
    (Functor.uncurry.obj (tensor Λ Y)) (Functor.uncurry.obj (tensor Λ' Y)) (adjunction Λ h)
    (coefficientAdjunction φ Y) (pullbackTensorIso Λ h).hom (coefficientTensorIso φ Y).hom A N
  have e₂ := projectionMap_comp (Functor.uncurry.obj (tensor Λ X))
    (Functor.uncurry.obj (tensor Λ' X)) (Functor.uncurry.obj (tensor Λ' Y))
    (coefficientAdjunction φ X) (adjunction Λ' h) (coefficientTensorIso φ X).hom
    (pullbackTensorIso Λ' h).hom A N
  have key := isIso_projectionMap_iff_of_iso ((adjunction Λ h).comp (coefficientAdjunction φ Y))
    ((coefficientAdjunction φ X).comp (adjunction Λ' h)) (coefficientPullbackSquareIso φ h) _ _
    (tensorCompat_coefficientPullbackSquareIso φ h) A N
  have hP₂ : IsIso (Stacks.Cohomology.AbstractKunnethMap.projectionMap
      (Functor.uncurry.obj (tensor Λ X))
      (Functor.uncurry.obj (tensor Λ' Y)) ((coefficientAdjunction φ X).comp (adjunction Λ' h))
      (compTensor (coefficientTensorIso φ X).hom (pullbackTensorIso Λ' h).hom) A N) := by
    rw [e₂]
    have : IsIso ((coefficientPushforward φ X).map
        (projectionMap Λ' h ((coefficientPullback φ X).obj A) N)) := Functor.map_isIso _ _
    exact IsIso.comp_isIso' h₁ this
  have hP₁ := key.2 hP₂
  rw [e₁] at hP₁
  have hP₁' : IsIso (projectionMap Λ h A ((coefficientPushforward φ Y).obj N) ≫
      (pushforward Λ h).map (coefficientProjectionMap φ Y ((pullback Λ h).obj A) N)) := hP₁
  have : IsIso ((pushforward Λ h).map
      (coefficientProjectionMap φ Y ((pullback Λ h).obj A) N)) := Functor.map_isIso _ _
  exact IsIso.of_isIso_comp_right (projectionMap Λ h A ((coefficientPushforward φ Y).obj N))
    ((pushforward Λ h).map (coefficientProjectionMap φ Y ((pullback Λ h).obj A) N))

end Reduction

end Stacks.EtaleCohomology.EtaleCoefficients

end

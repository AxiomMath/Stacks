module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsRingedTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackCongrOfSiteIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AbstractKunnethMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Künneth map, the projection map and the base change map on `D(X_étale, Λ)`

Let `Λ` be a commutative ring. For a scheme `X`, `D(X_étale, Λ)` is here the derived category of
sheaves of modules over the ringed topos `(X_étale, Λ̲)` of
`Stacks.EtaleCohomology.EtaleCoefficients.ringedTopos`. It has a derived tensor product
`⊗^L_Λ` (Stacks 06YU). A morphism of schemes `f` gives a derived pullback `f⁻¹` with right
adjoint `Rf_*` (Stacks 06YY, 07A6), and `f⁻¹` is compatible with `⊗^L_Λ` (Stacks 07A4). This
file assembles from these the canonical maps of the Künneth section of the étale cohomology
chapter, as instances of `Stacks.Cohomology.AbstractKunnethMap`:

* the **Künneth map** `Rf_*E ⊗^L_Λ Rg_*K ⟶ Rc_*(p⁻¹E ⊗^L_Λ q⁻¹K)` of a commutative square
  `p ≫ f = q ≫ g` with diagonal `c = p ≫ f` (Stacks 0F1E);
* the **base change map** `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` of a commutative square `h ≫ f' = e ≫ g`;
* the **canonical map** `A ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)` of Stacks 0F1J and
  0F1N (there with `A = p⁻¹E`).

## Main definitions

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `pullback`, `pushforward`, `adjunction`, `tensor`, `pullbackTensorIso` — `f⁻¹`, `Rf_*`,
  `f⁻¹ ⊣ Rf_*`, `⊗^L_Λ`, and `f⁻¹(M ⊗^L N) ≅ f⁻¹M ⊗^L f⁻¹N`.
* `pullbackCompIso` — `f⁻¹ ⋙ p⁻¹ ≅ (p ≫ f)⁻¹`.
* `kunnethMap`, `baseChangeMap`, `tensorBaseChangeMap` — the three canonical maps.

## Main results

* `fSharpCompatible_comp` — the morphism of ringed topoi of `p ≫ f` is the composite of those of
  `f` and `p`, up to `baseChangeComp p f`.

## Implementation notes

The derived categories are the standard model `HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0F1E](https://stacks.math.columbia.edu/tag/0F1E)
* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 0F1N](https://stacks.math.columbia.edu/tag/0F1N)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The structure maps of composite base changes -/

section StructureMap

variable {W X S : Scheme.{u}}

/-- The structure map `Λ̲ ⟶ f_*Λ̲`, precomposed with the sheafification unit of the constant
presheaf, is the sheafification unit on `X` at the base changed objects. -/
theorem toSheafify_app_comp_structureMap_app (f : X ⟶ S) (V : (Site S)ᵒᵖ) :
    (toSheafify (topology S) ((Functor.const _).obj (CommRingCat.of Λ))).app V ≫
        (structureMap Λ f).hom.app V =
      (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ))).app
        (Opposite.op ((baseChange f).obj V.unop)) := by
  have h := ((sheafificationAdjunction (topology S) CommRingCat.{u + 1}).homEquiv
    ((Functor.const _).obj (CommRingCat.of Λ))
    (((baseChange f).sheafPushforwardContinuous CommRingCat.{u + 1} (topology S)
        (topology X)).obj (ringedTopos Λ X).O)).apply_symm_apply
    (Functor.whiskerLeft (baseChange f).op
      (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ))))
  rw [Adjunction.homEquiv_unit] at h
  exact congr_app h V

/-- The composite of two base changes on the small models is continuous. -/
instance isContinuous_baseChange_comp (p : W ⟶ X) (f : X ⟶ S) :
    (baseChange f ⋙ baseChange p).IsContinuous (topology S) (topology W) :=
  Functor.isContinuous_comp _ _ _ (topology X) _

/-- The structure map of the composite morphism of ringed topoi, unfolded. -/
theorem comp_fSharp (p : W ⟶ X) (f : X ⟶ S) :
    ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).fSharp =
      structureMap Λ f ≫
        ((baseChange f).sheafPushforwardContinuous CommRingCat.{u + 1} (topology S)
          (topology X)).map (structureMap Λ p) ≫
        ((baseChange f).sheafPushforwardContinuousComp (baseChange p) CommRingCat.{u + 1}
          (topology S) (topology X) (topology W)).hom.app (ringedTopos Λ W).O :=
  rfl

/-- The structure maps along `f`, then along `p`, carried along `baseChangeComp p f`, give the
structure map along `p ≫ f`. -/
theorem structureMap_comp (p : W ⟶ X) (f : X ⟶ S) :
    structureMap Λ f ≫
        ((baseChange f).sheafPushforwardContinuous CommRingCat.{u + 1} (topology S)
          (topology X)).map (structureMap Λ p) ≫
        ((baseChange f).sheafPushforwardContinuousComp (baseChange p) CommRingCat.{u + 1}
          (topology S) (topology X) (topology W)).hom.app (ringedTopos Λ W).O ≫
        (Functor.sheafPushforwardContinuousNatTrans (baseChangeComp p f).hom CommRingCat.{u + 1}
          (topology S) (topology W)).app (ringedTopos Λ W).O =
      structureMap Λ (p ≫ f) := by
  refine Sheaf.hom_ext (sheafify_hom_ext (topology S) _ _
    (ObjectProperty.FullSubcategory.property _) ?_)
  refine NatTrans.ext (funext fun V => ?_)
  have h₁ := toSheafify_app_comp_structureMap_app Λ f V
  have h₂ := toSheafify_app_comp_structureMap_app Λ p (Opposite.op ((baseChange f).obj V.unop))
  have h₃ := toSheafify_app_comp_structureMap_app Λ (p ≫ f) V
  have hn := (toSheafify (topology W) ((Functor.const _).obj (CommRingCat.of Λ))).naturality
    ((baseChangeComp p f).hom.app V.unop).op
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hn
  show (toSheafify (topology S) ((Functor.const _).obj (CommRingCat.of Λ))).app V ≫
      (structureMap Λ f).hom.app V ≫
      (structureMap Λ p).hom.app (Opposite.op ((baseChange f).obj V.unop)) ≫
      (sheafify (topology W) ((Functor.const _).obj (CommRingCat.of Λ))).map
        ((baseChangeComp p f).hom.app V.unop).op =
    (toSheafify (topology S) ((Functor.const _).obj (CommRingCat.of Λ))).app V ≫
      (structureMap Λ (p ≫ f)).hom.app V
  exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans ((Category.assoc _ _ _).symm.trans
    ((h₂ =≫ _).trans (hn.symm.trans h₃.symm))))

/-- **The morphism of ringed topoi of `p ≫ f` is the composite of those of `f` and `p`, up to
`baseChangeComp p f`**: the isomorphism of underlying functors carries the structure map of
the composite to that of `p ≫ f`. -/
theorem fSharpCompatible_comp (p : W ⟶ X) (f : X ⟶ S) :
    RingedToposSiteHom.FSharpCompatible ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
      (ringedToposHom Λ (p ≫ f)) (baseChangeComp p f) :=
  (Category.assoc _ _ _).trans (structureMap_comp Λ p f)

end StructureMap

/-! ### The derived functors -/

section Derived

/-- `D(X_étale, Λ)`: the derived category of sheaves of `Λ̲`-modules on the small étale site. -/
@[sga "5 III 1.1"]
abbrev DerivedModules (X : Scheme.{u}) : Type _ :=
  DerivedCategory (SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))

/-- The tensor product of sheaves of `Λ̲`-modules is additive in the first variable. -/
instance sheafTensor_additive (X : Scheme.{u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (ringedTopos Λ X).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive _

/-- The tensor product of sheaves of `Λ̲`-modules is additive in the second variable. -/
instance sheafTensor_obj_additive (X : Scheme.{u})
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (ringedTopos Λ X).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive _ M

/-- Total tensor complexes of complexes of sheaves of `Λ̲`-modules exist. -/
instance hasMapBifunctor_sheafTensor (X : Scheme.{u})
    (A B : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor (ringedTopos Λ X).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ A B

/-- The derived pullback along the morphism of ringed topoi of a morphism of schemes exists
(Stacks 06YY). -/
instance hasLeftDerivedFunctor_ringedToposHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackOnHomotopy (ringedToposHom Λ f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Y).O)) (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ X) (Y := ringedTopos Λ Y) _ (isMorphismOfSites_ringedToposHom Λ f)

/-- **The derived tensor product** `⊗^L_Λ` on `D(X_étale, Λ)` (Stacks 06YU). -/
abbrev tensor (X : Scheme.{u}) : DerivedModules Λ X ⥤ DerivedModules Λ X ⥤ DerivedModules Λ X :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (ringedTopos Λ X).O

variable {X Y : Scheme.{u}}

/-- **The inverse image** `f⁻¹ : D(Y_étale, Λ) ⥤ D(X_étale, Λ)` (Stacks 06YY). -/
abbrev pullback (f : X ⟶ Y) : DerivedModules Λ Y ⥤ DerivedModules Λ X :=
  derivedPullback (X := ringedTopos Λ X) (Y := ringedTopos Λ Y) (ringedToposHom Λ f)

/-- **The derived direct image** `Rf_* : D(X_étale, Λ) ⥤ D(Y_étale, Λ)`. -/
abbrev pushforward (f : X ⟶ Y) : DerivedModules Λ X ⥤ DerivedModules Λ Y :=
  derivedPushforward (X := ringedTopos Λ X) (Y := ringedTopos Λ Y) (ringedToposHom Λ f)

/-- **The adjunction** `f⁻¹ ⊣ Rf_*` (Stacks 07A6). -/
def adjunction (f : X ⟶ Y) : pullback Λ f ⊣ pushforward Λ f :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction (X := ringedTopos Λ X)
    (Y := ringedTopos Λ Y) (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ f)

/-- **The compatibility of inverse image with the derived tensor product**,
`f⁻¹(M ⊗^L N) ≅ f⁻¹M ⊗^L f⁻¹N` (Stacks 07A4). -/
def pullbackTensorIso (f : X ⟶ Y) :
    Functor.uncurry.obj (tensor Λ Y) ⋙ pullback Λ f ≅
      (pullback Λ f).prod (pullback Λ f) ⋙ Functor.uncurry.obj (tensor Λ X) :=
  Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (X := ringedTopos Λ X)
    (Y := ringedTopos Λ Y) (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ f)

/-- Inverse images along equal morphisms are isomorphic. -/
def pullbackCongr {f f' : X ⟶ Y} (h : f = f') : pullback Λ f ≅ pullback Λ f' :=
  eqToIso (by subst h; rfl)

/-- **The composite inverse image**, `f⁻¹ ⋙ p⁻¹ ≅ (p ≫ f)⁻¹`: Stacks 0D6D for the composite
morphism of ringed topoi, followed by the comparison of the composite with the morphism of
ringed topoi of `p ≫ f` along `baseChangeComp p f`. -/
def pullbackCompIso {W : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ Y) :
    pullback Λ f ⋙ pullback Λ p ≅ pullback Λ (p ≫ f) :=
  letI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ W) (Y := ringedTopos Λ Y) ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ p)
      (isMorphismOfSites_ringedToposHom Λ f))
  Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
      (ringedToposHom Λ p) (ringedToposHom Λ f) (isMorphismOfSites_ringedToposHom Λ p)
      (isMorphismOfSites_ringedToposHom Λ f) ≪≫
    derivedPullbackIsoOfIso (fSharpCompatible_comp Λ p f)

end Derived

/-! ### The three canonical maps -/

section Maps

variable {W X Y S : Scheme.{u}}

/-- **The Künneth map** of [Stacks, Tag 0F1E] on `D(-_étale, Λ)`: for a commutative square
`p ≫ f = q ≫ g` of schemes, with diagonal `c = p ≫ f`, and `E ∈ D(X_étale, Λ)`,
`K ∈ D(Y_étale, Λ)`, the canonical map

`Rf_*E ⊗^L_Λ Rg_*K ⟶ Rc_*(p⁻¹E ⊗^L_Λ q⁻¹K)`. -/
def kunnethMap (p : W ⟶ X) (f : X ⟶ S) (q : W ⟶ Y) (g : Y ⟶ S) (w : p ≫ f = q ≫ g)
    (E : DerivedModules Λ X) (K : DerivedModules Λ Y) :
    ((tensor Λ S).obj ((pushforward Λ f).obj E)).obj ((pushforward Λ g).obj K) ⟶
      (pushforward Λ (p ≫ f)).obj (((tensor Λ W).obj ((pullback Λ p).obj E)).obj
        ((pullback Λ q).obj K)) :=
  Stacks.Cohomology.AbstractKunnethMap.kunnethMap (Functor.uncurry.obj (tensor Λ S))
    (Functor.uncurry.obj (tensor Λ W)) (adjunction Λ f) (adjunction Λ g) (adjunction Λ (p ≫ f))
    (pullback Λ p) (pullback Λ q) (pullbackTensorIso Λ (p ≫ f)).hom (pullbackCompIso Λ p f)
    (pullbackCompIso Λ q g ≪≫ pullbackCongr Λ w.symm) E K

/-- **The base change map** `(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` on `D(-_étale, Λ)` of a commutative square
`h ≫ f' = e ≫ g`. It is the mate of the isomorphism `(f')⁻¹ ⋙ h⁻¹ ≅ g⁻¹ ⋙ e⁻¹` of composite
inverse images. -/
def baseChangeMap {X' S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X') (e : Y ⟶ T)
    (w : h ≫ f' = e ≫ g) :
    pushforward Λ g ⋙ pullback Λ f' ⟶ pullback Λ e ⋙ pushforward Λ h :=
  Stacks.Cohomology.AbstractKunnethMap.baseChangeMap (adjunction Λ g) (adjunction Λ h)
    (pullback Λ f') (pullback Λ e)
    (pullbackCompIso Λ h f' ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ e g).symm)

/-- **The canonical map of [Stacks, Tag 0F1J] and [Stacks, Tag 0F1N]** on `D(-_étale, Λ)`: for
a commutative square `h ≫ f' = e ≫ g`, `A ∈ D(X'_étale, Λ)` and `F ∈ D(T_étale, Λ)`, the map

`A ⊗^L_Λ (f')⁻¹Rg_*F ⟶ Rh_*(h⁻¹A ⊗^L_Λ e⁻¹F)`,

the base change map in the second factor followed by the projection map. -/
def tensorBaseChangeMap {X' S' T : Scheme.{u}} (f' : X' ⟶ S') (g : T ⟶ S') (h : Y ⟶ X')
    (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (A : DerivedModules Λ X') (F : DerivedModules Λ T) :
    ((tensor Λ X').obj A).obj ((pullback Λ f').obj ((pushforward Λ g).obj F)) ⟶
      (pushforward Λ h).obj (((tensor Λ Y).obj ((pullback Λ h).obj A)).obj
        ((pullback Λ e).obj F)) :=
  Stacks.Cohomology.AbstractKunnethMap.tensorBaseChangeMap (adjunction Λ g) (adjunction Λ h)
    (pullback Λ f') (pullback Λ e)
    (pullbackCompIso Λ h f' ≪≫ pullbackCongr Λ w ≪≫ (pullbackCompIso Λ e g).symm)
    (Functor.uncurry.obj (tensor Λ X')) (Functor.uncurry.obj (tensor Λ Y))
    (pullbackTensorIso Λ h).hom A F

end Maps

end Stacks.EtaleCohomology.EtaleCoefficients

end

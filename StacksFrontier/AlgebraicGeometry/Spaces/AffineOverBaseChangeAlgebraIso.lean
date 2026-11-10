module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartTensorBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramIsoDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAlgebraFunctor

/-!
# The base-change comparison of a direct-image algebra is an isomorphism

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, and `Z` an algebraic space affine over `X` with base change `Z' = Y ×_X Z`.  This file
shows that the comparison of `𝒪_Y`-algebras

`g^* (f_* 𝒪_Z) ⟶ f'_* 𝒪_{Z'}`

of `AlgebraicGeometry.Space.affineOverBaseChangeAlgebraHom` is an isomorphism, and assembles the
comparisons into a natural isomorphism of functors on the algebraic spaces affine over `X`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isIso_of_bijective_affineChartDiagram`: a morphism of
  algebra sheaves on the small étale site of `Y` which is bijective over the source charts of
  the affine chart diagrams over `g` is an isomorphism.
* `AlgebraicGeometry.Space.affineOverBaseChangeAlgebraNatTrans`: the comparisons as a natural
  transformation, and `AlgebraicGeometry.Space.affineOverBaseChangeAlgebraNatIsoOfIsIso` the
  natural isomorphism once each component is invertible.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Detecting isomorphisms of algebra sheaves on affine chart diagrams -/

/-- An isomorphism of sheaves of modules is bijective on sections. -/
private theorem bijective_hom_val_app_of_isIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (f : M ⟶ N) [IsIso f] (V : Cᵒᵖ) : Function.Bijective (f.val.app V).hom :=
  ConcreteCategory.bijective_of_isIso
    (((SheafOfModules.forget R ⋙ PresheafOfModules.evaluation _ V).map f))

namespace AlgebraSheaf

variable {X Y : AlgebraicSpaces B S hS}

/-- A morphism of algebra sheaves which is bijective on the sections over the source chart of
every affine chart diagram over `g` is an isomorphism. -/
theorem isIso_of_bijective_affineChartDiagram (g : Y ⟶ X)
    {A C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} (φ : A ⟶ C)
    (h : ∀ d : ChartDiagram B S hS Y.1 X.1 g.hom,
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
        Function.Bijective (φ.right.hom.app (op d.U)).hom) :
    IsIso φ := by
  have hmod : IsIso (underlyingModuleMap φ) :=
    Space.isIso_of_bijective_affineChartDiagram B S hS g (underlyingModuleMap φ)
      fun d hU hV => h d hU hV
  exact isIso_of_bijective_right_app φ fun U =>
    bijective_hom_val_app_of_isIso (underlyingModuleMap φ) U

end AlgebraSheaf

/-! ### The functor-level comparison -/

section Functor

variable {X Y : AlgebraicSpaces B S hS}

/-- The direct-image functor on the algebraic spaces affine over `X`, on morphisms. -/
theorem affinePushforwardAlgebraFunctor_map {Z₁ Z₂ : (AffineOver B S hS X)ᵒᵖ} (φ : Z₁ ⟶ Z₂) :
    (affinePushforwardAlgebraFunctor B S hS X).map φ =
      pushforwardAlgebraMap B S hS φ.unop.hom :=
  rfl

/-- The base change along `g` followed by the direct image, on morphisms. -/
theorem affinePushforwardAlgebraFunctor_map_affineOverBaseChangeFunctor_op_map (g : Y ⟶ X)
    {Z₁ Z₂ : (AffineOver B S hS X)ᵒᵖ} (φ : Z₁ ⟶ Z₂) :
    (affinePushforwardAlgebraFunctor B S hS Y).map
        ((affineOverBaseChangeFunctor B S hS g).op.map φ) =
      pushforwardAlgebraMap B S hS (affineOverBaseChangeMap B S hS g φ.unop).hom :=
  rfl

/-- `AlgebraicGeometry.Space.affineOverBaseChangeAlgebraHom_naturality` stated for the two
composite functors on the opposite of the algebraic spaces affine over `X`. -/
theorem affineOverBaseChangeAlgebraHom_naturality_op (g : Y ⟶ X)
    {Z₁ Z₂ : (AffineOver B S hS X)ᵒᵖ} (φ : Z₁ ⟶ Z₂) :
    (affinePushforwardAlgebraFunctor B S hS X ⋙ algebraPullback B S hS g).map φ ≫
        affineOverBaseChangeAlgebraHom B S hS g Z₂.unop =
      affineOverBaseChangeAlgebraHom B S hS g Z₁.unop ≫
        ((affineOverBaseChangeFunctor B S hS g).op ⋙
          affinePushforwardAlgebraFunctor B S hS Y).map φ := by
  rw [Functor.comp_map, Functor.comp_map, affinePushforwardAlgebraFunctor_map,
    affinePushforwardAlgebraFunctor_map_affineOverBaseChangeFunctor_op_map]
  exact affineOverBaseChangeAlgebraHom_naturality B S hS g φ.unop

/-- The base-change comparison as a natural transformation: the direct image on the
algebraic spaces affine over `X` followed by algebra pullback along `g`, to the base change along
`g` followed by the direct image on the algebraic spaces affine over `Y`. -/
def affineOverBaseChangeAlgebraNatTrans (g : Y ⟶ X) :
    affinePushforwardAlgebraFunctor B S hS X ⋙ algebraPullback B S hS g ⟶
      (affineOverBaseChangeFunctor B S hS g).op ⋙ affinePushforwardAlgebraFunctor B S hS Y where
  app Z := affineOverBaseChangeAlgebraHom B S hS g Z.unop
  naturality _ _ φ := affineOverBaseChangeAlgebraHom_naturality_op B S hS g φ

/-- The base-change comparisons, assembled into a natural isomorphism, given that each of them is
an isomorphism. -/
def affineOverBaseChangeAlgebraNatIsoOfIsIso (g : Y ⟶ X)
    (h : ∀ Z : AffineOver B S hS X, IsIso (affineOverBaseChangeAlgebraHom B S hS g Z)) :
    affinePushforwardAlgebraFunctor B S hS X ⋙ algebraPullback B S hS g ≅
      (affineOverBaseChangeFunctor B S hS g).op ⋙ affinePushforwardAlgebraFunctor B S hS Y :=
  haveI : ∀ Z, IsIso ((affineOverBaseChangeAlgebraNatTrans B S hS g).app Z) := fun Z => h Z.unop
  haveI : IsIso (affineOverBaseChangeAlgebraNatTrans B S hS g) := NatIso.isIso_of_isIso_app _
  asIso (affineOverBaseChangeAlgebraNatTrans B S hS g)

/-- Algebra pullback along `g`, on quasi-coherent algebras. -/
def quasicoherentAlgebraPullback (g : Y ⟶ X) :
    QuasicoherentAlgebra B S hS X ⥤ QuasicoherentAlgebra B S hS Y :=
  ObjectProperty.lift _ (quasicoherentAlgebraInclusion B S hS X ⋙ algebraPullback B S hS g)
    fun A => algebraPullback_isQuasicoherent B S hS g A.obj A.property

/-- The base-change comparisons as a natural isomorphism of functors to the quasi-coherent
`𝒪_Y`-algebras, given that each of them is an isomorphism. -/
def quasicoherentAffineOverBaseChangeNatIsoOfIsIso (g : Y ⟶ X)
    (h : ∀ Z : AffineOver B S hS X, IsIso (affineOverBaseChangeAlgebraHom B S hS g Z)) :
    quasicoherentPushforwardAlgebraFunctor B S hS X ⋙ quasicoherentAlgebraPullback B S hS g ≅
      (affineOverBaseChangeFunctor B S hS g).op ⋙ quasicoherentPushforwardAlgebraFunctor B S hS Y :=
  NatIso.ofComponents
    (fun Z => (ObjectProperty.fullyFaithfulι _).preimageIso
      (@asIso _ _ _ _ (affineOverBaseChangeAlgebraHom B S hS g Z.unop) (h Z.unop)))
    (fun {Z₁ Z₂} φ => by
      refine ObjectProperty.hom_ext _ ?_
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom]
      exact affineOverBaseChangeAlgebraHom_naturality_op B S hS g φ)

end Functor

/-! ### The comparison on chart sections -/

section ChartSections

variable {X Y : AlgebraicSpaces B S hS}

/-- On sections, the direct image of a morphism of sheaves of commutative rings is the direct
image of its underlying morphism of sheaves of sets. -/
theorem pushforwardCommRingFunctor_map_app_apply (g : Y ⟶ X)
    {P Q : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (β : P ⟶ Q)
    (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
      P).obj.obj V) :
    ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
        β).hom.app V x =
      ((smallEtaleDirectImage B S hS g).map
        ((smallEtaleRingedTopos B S hS Y).forgetRing.map β)).hom.app V x :=
  congrArg (fun m => m.hom.app V x)
    (underlyingRingSheaf_map_pullbackCommRingSheafMap (SmallEtale.topology B S hS X.1)
      (Φ := (smallEtaleRingedToposHom B S hS g).toToposHom.pushforward) β)

/-- A factorization through the direct image of a morphism of sheaves of commutative rings, read
on sections through the direct image of sheaves of sets. -/
theorem smallEtaleDirectImage_map_app_apply_of_comp_eq (g : Y ⟶ X)
    {P₀ : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {P Q : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}}
    (a : P₀ ⟶ (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj P)
    (β : P ⟶ Q)
    (c : P₀ ⟶ (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj Q)
    (h : a ≫ (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map β = c)
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (s : P₀.obj.obj V) :
    ((smallEtaleDirectImage B S hS g).map
        ((smallEtaleRingedTopos B S hS Y).forgetRing.map β)).hom.app V (a.hom.app V s) =
      c.hom.app V s :=
  (pushforwardCommRingFunctor_map_app_apply B S hS g β V (a.hom.app V s)).symm.trans
    (congrArg (fun m => m.hom.app V s) h)

/-- The chart projection of the direct image is natural in the sheaf of sets, on sections. -/
theorem moduleChartProjection_app_map_apply (g : Y ⟶ X) (V : SmallEtale B S hS X.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g V)) (comparisonFunctor B S hS Y).op)
    {P Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u)} (β : P ⟶ Q)
    (x : ((smallEtaleDirectImage B S hS g).obj P).obj.obj (op V)) :
    (moduleChartProjection B S hS g V j).app Q
        (((smallEtaleDirectImage B S hS g).map β).hom.app (op V) x) =
      β.hom.app j.right ((moduleChartProjection B S hS g V j).app P x) := by
  have h := NatTrans.naturality_apply (moduleChartProjection B S hS g V j) β x
  refine (congrArg ((moduleChartProjection B S hS g V j).app Q)
    (Sheaf.sectionsFunctor_map_apply ((smallEtaleDirectImage B S hS g).map β) x).symm).trans ?_
  exact h.trans (Sheaf.sectionsFunctor_map_apply β _)

/-- The comparison carries the chart section of the inverse image to the chart projection of the
square comparison. Let `d` be a chart diagram over `g` and `s` a section of `f_* 𝒪_Z` over the
chart `d.V` of `X`. The adjunct of the inclusion `g⁻¹ (f_* 𝒪_Z) ⟶ g^* (f_* 𝒪_Z)` sends `s`
to a section of the direct image of `g^* (f_* 𝒪_Z)` over `d.V`, whose chart projection to `d.U`
is a section of `g^* (f_* 𝒪_Z)` over `d.U`; the comparison carries it to the chart projection of
the image of `s` under the square comparison `f_* 𝒪_Z ⟶ g_* (f'_* 𝒪_W)`. -/
theorem baseChangeAlgebraHom_app_chartProjection (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (s : (pushforwardAlgebra B S hS Z).right.obj.obj (op d.V)) :
    (baseChangeAlgebraHom B S hS g Z W p hw).hom.app (op d.U)
        ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            ((algebraPullback B S hS g).obj (pushforwardAlgebra B S hS Z)).right)
          ((((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
              _ _) ((algebraPullbackMap B S hS g).app (pushforwardAlgebra B S hS Z))).hom.app
            (op d.V) s)) =
      (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (pushforwardAlgebra B S hS W).right)
        ((pushforwardSquareMap B S hS g Z W p hw).hom.app (op d.V) s) := by
  have hadj : ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        _ _) ((algebraPullbackMap B S hS g).app (pushforwardAlgebra B S hS Z)) ≫
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).map
        (baseChangeAlgebraHom B S hS g Z W p hw) =
      pushforwardSquareMap B S hS g Z W p hw :=
    ((commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv_naturality_right
        ((algebraPullbackMap B S hS g).app (pushforwardAlgebra B S hS Z))
        (baseChangeAlgebraHom B S hS g Z W p hw)).symm.trans
      ((congrArg ((commRingImageAdjunction
          (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
        (algebraPullbackMap_comp_baseChangeAlgebraHom B S hS g Z W p hw)).trans
        (pushforwardSquareBaseChangeMap_canonical B S hS g Z W p hw))
  refine (moduleChartProjection_app_map_apply B S hS g d.V (indexOfChartDiagram B S hS g d)
    ((smallEtaleRingedTopos B S hS Y).forgetRing.map (baseChangeAlgebraHom B S hS g Z W p hw))
    ((((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        _ _) ((algebraPullbackMap B S hS g).app (pushforwardAlgebra B S hS Z))).hom.app
          (op d.V) s)).symm.trans ?_
  refine congrArg ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
    ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (pushforwardAlgebra B S hS W).right)) ?_
  exact smallEtaleDirectImage_map_app_apply_of_comp_eq B S hS g _
    (baseChangeAlgebraHom B S hS g Z W p hw) _ hadj (op d.V) s

end ChartSections

/-! ### Bijectivity over an affine chart diagram -/

section ChartBijective

variable {X Y : AlgebraicSpaces B S hS}

/-- An isomorphism of sheaves of modules is bijective on sections. -/
theorem _root_.SheafOfModules.bijective_hom_val_app_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (V : Cᵒᵖ) : Function.Bijective (e.hom.val.app V).hom :=
  bijective_hom_val_app_of_isIso e.hom V

/-- Let `Φ : S ⊗_R M ⟶ N` and `ι : N ⟶ P` be bijective `S`-linear maps and `f : P ⟶ T` an
`S`-linear map. If the
`S`-linear extension of an `R`-linear map `τ : M ⟶ T` agreeing with `f ∘ ι ∘ Φ` on the `1 ⊗ s`
is bijective, then so is `f`. -/
theorem _root_.Function.Bijective.of_liftBaseChange {R S M N P T : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    [AddCommGroup P] [Module S P] [AddCommGroup T] [Module S T] [hRT : Module R T]
    [hT : IsScalarTower R S T] (Φ : TensorProduct R S M →ₗ[S] N) (hΦ : Function.Bijective Φ)
    (ι : N →ₗ[S] P) (hι : Function.Bijective ι) (f : P →ₗ[S] T) (τ : M →ₗ[R] T)
    (hτ : ∀ s, τ s = f (ι (Φ (1 ⊗ₜ s))))
    (h : Function.Bijective (τ.liftBaseChange S)) : Function.Bijective f := by
  have hcomp : (fun x => f (ι (Φ x))) = τ.liftBaseChange S := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul a s =>
      have ha : (a ⊗ₜ[R] s : TensorProduct R S M) = a • (1 ⊗ₜ s) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ha]
      simp only [map_smul, LinearMap.liftBaseChange_tmul, one_smul, hτ]
    | add x y hx hy =>
      simp only [map_add]
      exact congrArg₂ (· + ·) hx hy
  have hall : Function.Bijective (fun x => f (ι (Φ x))) := hcomp ▸ h
  exact (Function.Bijective.of_comp_iff _ (hι.comp hΦ)).1 hall

/-- The `𝒪_X(d.V)`-module structure on the sections over `d.U` of an `𝒪_Y`-module, by
restriction of scalars along the vertical pullback of regular functions of a chart diagram `d`
over `g`. -/
@[instance_reducible]
def chartDiagramSectionModule (g : Y ⟶ X) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    Module (chartRing B S hS X.1 X.2 d.V) (N.val.obj (op d.U)) :=
  Module.compHom _ (chartDiagramRestrict B S hS g d)

/-- The two scalar actions on the sections over `d.U` of an `𝒪_Y`-module are compatible. -/
theorem chartDiagramSection_isScalarTower (g : Y ⟶ X) (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (N : Modules.{u, u} B S hS Y.1 Y.2) :
    letI := chartDiagramAlgebra B S hS g d
    letI := chartDiagramSectionModule B S hS g d N
    IsScalarTower (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
      (N.val.obj (op d.U)) :=
  let _ := chartDiagramAlgebra B S hS g d
  let _ := chartDiagramSectionModule B S hS g d N
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)

/-- Let `A` be a quasi-coherent `𝒪_X`-algebra, `φ : g^* A ⟶ C` a morphism of `𝒪_Y`-algebras and
`d` a chart diagram over `g` between affine charts. Let `τ : A(d.V) ⟶ C(d.U)` be an
`𝒪_X(d.V)`-linear map which is `φ` applied to the chart section of the pullback of the module
underlying `A`, read in `g^* A`. If the `𝒪_Y(d.U)`-linear extension
`𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ C(d.U)` of `τ` is bijective then so is `φ` over `d.U`. -/
theorem bijective_app_of_bijective_liftBaseChange (g : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (hA : A.IsQuasicoherent)
    {C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2} (φ : (algebraPullback B S hS g).obj A ⟶ C)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (haU : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (haV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (τ : letI := chartDiagramSectionModule B S hS g d C.underlyingModule
      A.underlyingModule.val.obj (op d.V) →ₗ[chartRing B S hS X.1 X.2 d.V]
        C.underlyingModule.val.obj (op d.U))
    (hτ : ∀ s, τ s = AlgebraSheaf.underlyingModuleLinear φ (op d.U)
      (((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom.val.app (op d.U)).hom
        (modulePullbackChartSection B S hS g A.underlyingModule d s)))
    (h : letI := chartDiagramAlgebra B S hS g d
      letI := chartDiagramSectionModule B S hS g d C.underlyingModule
      haveI := chartDiagramSection_isScalarTower B S hS g d C.underlyingModule
      Function.Bijective (τ.liftBaseChange (chartRing B S hS Y.1 Y.2 d.U))) :
    Function.Bijective (φ.right.hom.app (op d.U)).hom := by
  let := chartDiagramAlgebra B S hS g d
  let := chartDiagramSectionModule B S hS g d C.underlyingModule
  have := chartDiagramSection_isScalarTower B S hS g d C.underlyingModule
  exact Function.Bijective.of_liftBaseChange (R := chartRing B S hS X.1 X.2 d.V)
    (S := chartRing B S hS Y.1 Y.2 d.U) (M := A.underlyingModule.val.obj (op d.V))
    (T := C.underlyingModule.val.obj (op d.U))
    (hRT := chartDiagramSectionModule B S hS g d C.underlyingModule)
    (hT := chartDiagramSection_isScalarTower B S hS g d C.underlyingModule)
    (modulePullbackChartBaseChange B S hS g A.underlyingModule d)
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g
      A.underlyingModule hA d haU haV)
    ((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom.val.app (op d.U)).hom
    (SheafOfModules.bijective_hom_val_app_of_iso
      (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A) (op d.U))
    (AlgebraSheaf.underlyingModuleLinear φ (op d.U)) τ
    (fun s => (hτ s).trans (congrArg (fun y => AlgebraSheaf.underlyingModuleLinear φ (op d.U)
      (((underlyingModuleAlgebraPullbackModulePullbackIso B S hS g A).hom.val.app (op d.U)).hom y))
      ((modulePullbackChartBaseChange_tmul B S hS g A.underlyingModule d 1 s).trans
        (one_smul _ _)).symm)) h

/-- The chart-section linear map underlying a morphism of algebra sheaves is that morphism on
sections. -/
theorem _root_.AlgebraicGeometry.Space.AlgebraSheaf.underlyingModuleLinear_apply
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) (U : (SmallEtale B S hS F)ᵒᵖ)
    (x : (AlgebraSheaf.underlyingModule A).val.obj U) :
    AlgebraSheaf.underlyingModuleLinear f U x = f.right.hom.app U x :=
  rfl

end ChartBijective

/-! ### Reduction of invertibility to a pushout square on each affine chart diagram -/

section ChartReduction

variable {X Y : AlgebraicSpaces B S hS}

/-- The base-change comparison is an isomorphism as soon as, on every affine chart diagram, the
chart map of the square comparison completes a pushout square of section rings. The inputs are
the identification of the module-level chart section of `g^* (f_* 𝒪_Z)` with the ring-level one
(`hH1`), a ring map `γ d : (f_* 𝒪_Z)(d.V) → (f'_* 𝒪_{Z'})(d.U)` which is the chart projection of
the square comparison (`hγ`), and, for affine charts, the pushout square formed by `γ d`, the two
structure maps and the vertical pullback of regular functions (`hsq`). -/
theorem isIso_affineOverBaseChangeAlgebraHom_of_chart (g : Y ⟶ X) (Z : AffineOver B S hS X)
    (hH1 : ∀ (d : ChartDiagram B S hS Y.1 X.1 g.hom)
      (s : (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V)),
      (underlyingModuleAlgebraPullbackModulePullbackIso B S hS g
          (pushforwardAlgebra B S hS Z.obj)).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS g (pushforwardAlgebra B S hS Z.obj).underlyingModule
          d s) =
      (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          ((algebraPullback B S hS g).obj (pushforwardAlgebra B S hS Z.obj)).right)
        ((((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
            _ _) ((algebraPullbackMap B S hS g).app (pushforwardAlgebra B S hS Z.obj))).hom.app
          (op d.V) s))
    (γ : ∀ d : ChartDiagram B S hS Y.1 X.1 g.hom,
      (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V) →+*
        (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right.obj.obj (op d.U))
    (hγ : ∀ d s, γ d s =
      (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
          (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right)
        ((pushforwardSquareMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
          (affineOverBaseChangeProjection B S hS g Z)
          (affineOverBaseChange_isPullback B S hS g Z).w).hom.app (op d.V) s))
    (hsq : ∀ d : ChartDiagram B S hS Y.1 X.1 g.hom,
      IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U) →
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V) →
      IsPushout (CommRingCat.ofHom ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V)))
        (CommRingCat.ofHom (chartDiagramRestrict B S hS g d)) (CommRingCat.ofHom (γ d))
        (CommRingCat.ofHom
          ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap
            (op d.U)))) :
    IsIso (affineOverBaseChangeAlgebraHom B S hS g Z) := by
  have hqc : (pushforwardAlgebra B S hS Z.obj).IsQuasicoherent :=
    ((quasicoherentPushforwardAlgebraFunctor B S hS X).obj (op Z)).property
  refine AlgebraSheaf.isIso_of_bijective_affineChartDiagram B S hS g _ fun d hU hV => ?_
  have hw : ∀ r, γ d ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V) r) =
      (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap (op d.U)
        (chartDiagramRestrict B S hS g d r) := fun r =>
    congrArg (fun f => f.hom r) (hsq d hU hV).w
  let := chartDiagramAlgebra B S hS g d
  let := chartDiagramSectionModule B S hS g d
    (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule
  have := chartDiagramSection_isScalarTower B S hS g d
    (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule
  let τ : (pushforwardAlgebra B S hS Z.obj).underlyingModule.val.obj (op d.V) →ₗ[
        chartRing B S hS X.1 X.2 d.V]
      (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule.val.obj
        (op d.U) :=
    { toFun := γ d
      map_add' := map_add (γ d)
      map_smul' := fun r s => by
        change γ d ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V) r *
            (show (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V) from s)) =
          (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap (op d.U)
            (chartDiagramRestrict B S hS g d r) * γ d s
        exact (map_mul _ _ _).trans (congrArg (· * γ d s) (hw r)) }
  refine bijective_app_of_bijective_liftBaseChange B S hS g _ hqc _ d hU hV τ
    (fun s => ?_) ?_
  · refine (hγ d s).trans ?_
    refine Eq.trans ?_ (AlgebraSheaf.underlyingModuleLinear_apply B S hS _ _ _).symm
    refine Eq.trans ?_ (congrArg
      ((affineOverBaseChangeAlgebraHom B S hS g Z).right.hom.app (op d.U)) (hH1 d s)).symm
    exact (baseChangeAlgebraHom_app_chartProjection B S hS g Z.obj
      (affineOverBaseChange B S hS g Z).obj (affineOverBaseChangeProjection B S hS g Z)
      (affineOverBaseChange_isPullback B S hS g Z).w d s).symm
  · exact RingHom.bijective_liftBaseChange_of_isPushout (R := chartRing B S hS X.1 X.2 d.V)
      (S := chartRing B S hS Y.1 Y.2 d.U)
      (M := (pushforwardAlgebra B S hS Z.obj).right.obj.obj (op d.V))
      (T := (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right.obj.obj
        (op d.U))
      (iRM := inferInstanceAs (Module (chartRing B S hS X.1 X.2 d.V)
        ((pushforwardAlgebra B S hS Z.obj).underlyingModule.val.obj (op d.V))))
      (iST := inferInstanceAs (Module (chartRing B S hS Y.1 Y.2 d.U)
        ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule.val.obj
          (op d.U))))
      (iRT := chartDiagramSectionModule B S hS g d
        (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule)
      (hRST := chartDiagramSection_isScalarTower B S hS g d
        (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).underlyingModule)
      (chartDiagramRestrict B S hS g d) ((pushforwardAlgebra B S hS Z.obj).algebraMap (op d.V))
      ((pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).algebraMap (op d.U))
      (γ d) (hsq d hU hV) rfl (fun _ _ => rfl) (fun _ _ => rfl) τ (fun _ => rfl)

end ChartReduction

end AlgebraicGeometry.Space

end

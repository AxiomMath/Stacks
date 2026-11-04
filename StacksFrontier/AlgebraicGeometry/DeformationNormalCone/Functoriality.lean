module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.GlobalParameter
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraComap

/-!
# Functoriality of the deformation space

Let `h : U' ⟶ U` be a morphism of schemes and `ℐ ⊆ 𝒪_U`, `ℐ' ⊆ 𝒪_{U'}` quasi-coherent ideal
sheaves with `ℐ𝒪_{U'} ⊆ ℐ'`. Pulling sections back along `h` maps `ℐⁿ` into `h_*(ℐ'ⁿ)` for every
`n`, compatibly with the products, so it gives a morphism of extended Rees algebras
`𝒪_U[t⁻¹, ℐt] ⟶ h_* 𝒪_{U'}[t⁻¹, ℐ't]` and hence a morphism of deformation spaces

  `D(ℐ') ⟶ D(ℐ)`

over `h`. On a homogeneous section `x t^k` it is `h^♯(x) t^k`; in particular it pulls `t⁻¹` back
to `t⁻¹`.

## Main definitions

* `Stacks.Deformation.deformationMap`: the morphism `D(ℐ') ⟶ D(ℐ)`.

## Main results

* `Stacks.Deformation.deformationMap_toBase`: it lies over `h`.
* `Stacks.Deformation.deformationMap_appLE_chartIncl`: its value on a homogeneous section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec Stacks.Blowup

universe u

namespace Stacks.Blowup

/-- A local section of `𝒪_X` lying in an ideal sheaf `P` lies in every larger ideal sheaf `Q`:
its image in the ideal sheaf of the subscheme cut out by `Q` vanishes. -/
theorem idealKernel_ι_comp_eq_zero_of_le {X : Scheme.{u}} {P Q : X.IdealSheafData} (hle : P ≤ Q) :
    kernel.ι (SheafOfModules.unitToPushforwardObjUnit P.subschemeι.toRingCatSheafHom) ≫
      SheafOfModules.unitToPushforwardObjUnit Q.subschemeι.toRingCatSheafHom = 0 := by
  ext U x
  have hx := congrArg (fun φ => φ.val.app U x)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit P.subschemeι.toRingCatSheafHom))
  simp only at hx
  show (Q.subschemeι.app U.unop).hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        P.subschemeι.toRingCatSheafHom)).val.app U x) = 0
  change (P.subschemeι.app U.unop).hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        P.subschemeι.toRingCatSheafHom)).val.app U x) = 0 at hx
  have key : ∀ (φ : Q.subscheme ⟶ X) (hφ : Scheme.IdealSheafData.inclusion hle ≫
      P.subschemeι = φ) (a : Γ(X, U.unop)), (P.subschemeι.app U.unop).hom a = 0 →
      (φ.app U.unop).hom a = 0 := by
    rintro φ rfl a ha
    exact (congrArg (Scheme.Hom.app (Scheme.IdealSheafData.inclusion hle)
      (P.subschemeι ⁻¹ᵁ U.unop)).hom ha).trans (map_zero _)
  exact key _ (Scheme.IdealSheafData.inclusion_subschemeι hle) _ hx

/-- The inclusion `Pⁿ ⟶ Qⁿ` of powers of two ideal sheaves `P ≤ Q`. -/
def idealPowerKernelMono {X : Scheme.{u}} {P Q : X.IdealSheafData} (hle : P ≤ Q) (n : ℕ) :
    idealPowerKernel P n ⟶ idealPowerKernel Q n :=
  kernel.lift (C := X.Modules) _ (kernel.ι _)
    (idealKernel_ι_comp_eq_zero_of_le (pow_le_pow_left' hle n))

/-- The inclusion `Pⁿ ⟶ Qⁿ` does not change the underlying section of `𝒪_X`. -/
theorem idealPowerKernelAmbient_mono {X : Scheme.{u}} {P Q : X.IdealSheafData} (hle : P ≤ Q)
    (n : ℕ) (U : X.Opens) (x : (idealPowerKernel P n).val.obj (op U)) :
    idealPowerKernelAmbient Q n U ((idealPowerKernelMono hle n).val.app (op U) x) =
      idealPowerKernelAmbient P n U x :=
  congrArg (fun φ => φ.val.app (op U) x) (kernel.lift_ι (C := X.Modules) _ (kernel.ι _)
    (idealKernel_ι_comp_eq_zero_of_le (pow_le_pow_left' hle n)))

end Stacks.Blowup

namespace Stacks.Deformation

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData) (J' : U'.IdealSheafData)
  (hJ : J.comap h ≤ J')

/-! ### The pullback of homogeneous sections -/

/-- **The pullback of a homogeneous section of degree `k`** of the extended Rees algebra of `ℐ`
along `h`, a homogeneous section of degree `k` of the extended Rees algebra of `ℐ'`. -/
def extReesPullback (k : ℤ) (W : U.Opens) :
    (extReesPiece J k).val.obj (op W) →+ (extReesPiece J' k).val.obj (op (h ⁻¹ᵁ W)) :=
  (((idealPowerKernelMono hJ k.toNat).val.app (op (h ⁻¹ᵁ W))).hom.toAddMonoidHom).comp
    (((reesPieceComap h J (k.toNat : ℤ)).val.app (op W)).hom.toAddMonoidHom)

include hJ in
/-- On underlying sections the pullback of a homogeneous section is `h^♯`. -/
theorem extReesAmbient_extReesPullback (k : ℤ) (W : U.Opens)
    (x : (extReesPiece J k).val.obj (op W)) :
    extReesAmbient J' k (h ⁻¹ᵁ W) (extReesPullback h J J' hJ k W x) =
      (h.app W).hom (extReesAmbient J k W x) :=
  (idealPowerKernelAmbient_mono hJ k.toNat (h ⁻¹ᵁ W) _).trans
    (reesPieceAmbient_comap h J (k.toNat : ℤ) W x)

/-- The pullback of homogeneous sections sends `r • x` to `h^♯(r) • h^*(x)`. -/
theorem extReesPullback_smul (k : ℤ) (W : U.Opens) (r : U.ringCatSheaf.obj.obj (op W))
    (x : (extReesPiece J k).val.obj (op W)) :
    extReesPullback h J J' hJ k W (r • x) =
      (show U'.ringCatSheaf.obj.obj (op (h ⁻¹ᵁ W)) from (h.app W).hom r) •
        extReesPullback h J J' hJ k W x := by
  refine extReesAmbient_injective J' k (h ⁻¹ᵁ W) ?_
  rw [extReesAmbient_extReesPullback, extReesAmbient_smul, extReesAmbient_smul,
    extReesAmbient_extReesPullback]
  exact map_mul (h.app W).hom _ _

/-- The pullback of homogeneous sections commutes with restriction to a smaller open. -/
theorem extReesPullback_restrict (k : ℤ) {W W' : U.Opens} (hle : W' ≤ W)
    (x : (extReesPiece J k).val.obj (op W)) :
    (extReesPiece J' k).val.map (homOfLE (Scheme.Hom.preimage_mono h hle)).op
        (extReesPullback h J J' hJ k W x) =
      extReesPullback h J J' hJ k W' ((extReesPiece J k).val.map (homOfLE hle).op x) := by
  refine extReesAmbient_injective J' k (h ⁻¹ᵁ W') ?_
  refine (extReesAmbient_restrict J' k _ _ _ _).trans ?_
  refine (congrArg _ (extReesAmbient_extReesPullback h J J' hJ k W x)).trans ?_
  refine Eq.trans ?_ (extReesAmbient_extReesPullback h J J' hJ k W' _).symm
  refine Eq.trans ?_ (congrArg (h.app W').hom (extReesAmbient_restrict J k W' W hle x).symm)
  exact (ConcreteCategory.congr_hom (h.naturality (homOfLE hle).op) _).symm

/-- The pullback of homogeneous sections is multiplicative: it sends `x y` to `h^*(x) h^*(y)`. -/
theorem extReesPullback_mul (p q : ℤ) (W : U.Opens) (x : (extReesPiece J p).val.obj (op W))
    (y : (extReesPiece J q).val.obj (op W)) :
    extReesPullback h J J' hJ (p + q) W ((extReesMul J p q).app (op W) x y) =
      (extReesMul J' p q).app (op (h ⁻¹ᵁ W)) (extReesPullback h J J' hJ p W x)
        (extReesPullback h J J' hJ q W y) := by
  refine extReesAmbient_injective J' (p + q) (h ⁻¹ᵁ W) ?_
  rw [extReesAmbient_extReesPullback, extReesAmbient_extReesMul, extReesAmbient_extReesMul,
    extReesAmbient_extReesPullback, extReesAmbient_extReesPullback]
  exact map_mul (h.app W).hom _ _

/-- The pullback of homogeneous sections sends the unit `1` of degree `0` to `1`. -/
theorem extReesPullback_one (W : U.Opens) :
    extReesPullback h J J' hJ 0 W ((extReesOne J).eval (op W)) =
      (extReesOne J').eval (op (h ⁻¹ᵁ W)) := by
  refine extReesAmbient_injective J' 0 (h ⁻¹ᵁ W) ?_
  rw [extReesAmbient_extReesPullback, extReesAmbient_extReesOne, extReesAmbient_extReesOne]
  exact map_one (h.app W).hom

/-- **The pullback of `t⁻¹` is `t⁻¹`.** -/
theorem extReesPullback_paramPiece (W : U.Opens) :
    extReesPullback h J J' hJ (-1) W (paramPiece J W) = paramPiece J' (h ⁻¹ᵁ W) := by
  refine extReesAmbient_injective J' (-1) (h ⁻¹ᵁ W) ?_
  rw [extReesAmbient_extReesPullback, extReesAmbient_paramPiece, extReesAmbient_paramPiece]
  exact map_one (h.app W).hom

/-! ### The morphism of algebras -/

/-- The direct image along `h` of the ungraded extended Rees algebra of `ℐ'`. -/
abbrev extReesPushforwardAlgebra : AlgebraSheaf U :=
  (algebraPushforward h).obj
    (ungradedAlgebraSheaf U' (extReesGradedAlgebra J') (extReesGradedAlgebra_mul_comm J'))

/-- The degree-`k` component of the morphism of algebras on sections over `W`. -/
def deformationAdd (k : ℤ) (W : (Opens U)ᵒᵖ) :
    ((extReesPiece J k).val.obj W : Type u) →+ algSections (extReesPushforwardAlgebra h J') W :=
  AddMonoidHom.mk'
    (fun x => ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
      (extReesGradedAlgebra_mul_comm J') k (h ⁻¹ᵁ W.unop) (extReesPullback h J J' hJ k W.unop x))
    (fun x y => by
      refine Eq.trans (congrArg (ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
        (extReesGradedAlgebra_mul_comm J') k (h ⁻¹ᵁ W.unop)) (map_add _ x y))
        (ungradedAlgebraSheafIncl_add U' (extReesGradedAlgebra J')
          (extReesGradedAlgebra_mul_comm J') k (h ⁻¹ᵁ W.unop) _ _))

/-- The degree-`k` component sends `x` to the image of its pullback `h^*(x)` in the ungraded
extended Rees algebra of `ℐ'`. -/
theorem deformationAdd_apply (k : ℤ) (W : (Opens U)ᵒᵖ) (x : (extReesPiece J k).val.obj W) :
    deformationAdd h J J' hJ k W x = ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
      (extReesGradedAlgebra_mul_comm J') k (h ⁻¹ᵁ W.unop)
      (extReesPullback h J J' hJ k W.unop x) := rfl

/-- The degree-`k` component commutes with restriction to a smaller open. -/
theorem deformationAdd_naturality (k : ℤ) {W W' : (Opens U)ᵒᵖ} (f : W ⟶ W')
    (x : (extReesPiece J k).val.obj W) :
    ((extReesPushforwardAlgebra h J').right.obj.map f).hom (deformationAdd h J J' hJ k W x) =
      deformationAdd h J J' hJ k W' ((extReesPiece J k).val.map f x) := by
  have hle : W'.unop ≤ W.unop := leOfHom f.unop
  have hf : f = (homOfLE hle).op := Subsingleton.elim _ _
  subst hf
  refine Eq.trans (ungradedAlgebraSheafIncl_restrict U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') k (Scheme.Hom.preimage_mono h hle) _) ?_
  exact congrArg (ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') k (h ⁻¹ᵁ W'.unop))
    (extReesPullback_restrict h J J' hJ k hle x)

/-- The degree-`k` component is semilinear: it sends `r • x` to the product of the image of `r`
with the image of `x`. -/
theorem deformationAdd_smul (k : ℤ) (W : (Opens U)ᵒᵖ) (r : U.ringCatSheaf.obj.obj W)
    (x : (extReesPiece J k).val.obj W) :
    deformationAdd h J J' hJ k W (r • x) =
      ((extReesPushforwardAlgebra h J').hom.hom.app W).hom r * deformationAdd h J J' hJ k W x := by
  refine (congrArg (ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') k (h ⁻¹ᵁ W.unop))
    (extReesPullback_smul h J J' hJ k W.unop r x)).trans ?_
  refine (congrArg (ungradedCommUnit U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') (h ⁻¹ᵁ W.unop)).hom
    (Stacks.RelativeSpec.structureMap_mul_incl (extReesGradedAlgebra J') k
      (op (h ⁻¹ᵁ W.unop)) ((h.app W.unop).hom r)
      (extReesPullback h J J' hJ k W.unop x)).symm).trans ?_
  exact map_mul (ungradedCommUnit U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') (h ⁻¹ᵁ W.unop)).hom _ _

/-- The components are multiplicative: the product of homogeneous sections of degrees `p` and `q`
goes to the product of their images. -/
theorem deformationAdd_mul (p q : ℤ) (W : (Opens U)ᵒᵖ) (x : (extReesPiece J p).val.obj W)
    (y : (extReesPiece J q).val.obj W) :
    deformationAdd h J J' hJ (p + q) W ((extReesMul J p q).app W x y) =
      deformationAdd h J J' hJ p W x * deformationAdd h J J' hJ q W y :=
  (congrArg (ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') (p + q) (h ⁻¹ᵁ W.unop))
    (extReesPullback_mul h J J' hJ p q W.unop x y)).trans
    (ungradedAlgebraSheafIncl_mul U' (extReesGradedAlgebra J') (extReesGradedAlgebra_mul_comm J')
      p q (h ⁻¹ᵁ W.unop) _ _).symm

/-- The degree-`0` component sends the unit `1` to `1`. -/
theorem deformationAdd_one (W : (Opens U)ᵒᵖ) :
    deformationAdd h J J' hJ 0 W ((extReesOne J).eval W) = 1 :=
  (congrArg (ungradedAlgebraSheafIncl U' (extReesGradedAlgebra J')
    (extReesGradedAlgebra_mul_comm J') 0 (h ⁻¹ᵁ W.unop))
    (extReesPullback_one h J J' hJ W.unop)).trans
    (ungradedAlgebraSheafIncl_one U' (extReesGradedAlgebra J') (extReesGradedAlgebra_mul_comm J')
      (h ⁻¹ᵁ W.unop))

/-- The degree-`k` component as a morphism of sheaves of modules. -/
def deformationPiece (k : ℤ) :
    (extReesGradedAlgebra J).piece k ⟶ (constGraded (extReesPushforwardAlgebra h J')).piece k where
  val :=
    { app := fun W => ModuleCat.homMk
        (AddCommGrpCat.ofHom (deformationAdd h J J' hJ k W)) (fun r => by
          ext x
          exact (deformationAdd_smul h J J' hJ k W r x).symm)
      naturality := fun f => by
        ext x
        exact (deformationAdd_naturality h J J' hJ k f x).symm }

/-- The morphism of extended Rees algebras, as a unital homomorphism of sheaves of graded
algebras into the degenerate grading of the direct image. -/
def deformationUnitalHom :
    SheafOfModules.GradedAlgebra.UnitalHom (extReesGradedAlgebra J)
      (constGraded (extReesPushforwardAlgebra h J')) where
  app := deformationPiece h J J' hJ
  map_mul p q W x y := deformationAdd_mul h J J' hJ p q W x y
  map_one W := deformationAdd_one h J J' hJ W

/-- The ungraded form of the morphism of algebras. -/
def deformationUngradedHom :
    ungradedAlgebraSheaf U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) ⟶
      extReesPushforwardAlgebra h J' :=
  ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)
      (extReesPushforwardAlgebra h J')).trans
    (ungradedCommHomEquiv (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)
      (extReesPushforwardAlgebra h J'))).symm (deformationUnitalHom h J J' hJ)

/-- On a homogeneous section `x` of degree `k`, the ungraded morphism of algebras agrees with the
degree-`k` component `deformationAdd`. -/
theorem deformationUngradedHom_app_incl (k : ℤ) (W : U.Opens)
    (x : ((extReesGradedAlgebra J).piece k).val.obj (op W)) :
    ((deformationUngradedHom h J J' hJ).right.hom.app (op W)).hom
        (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k W
          x) =
      deformationAdd h J J' hJ k (op W) x := by
  have hcomp : ungradedCommToSheaf U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) ≫
      (deformationUngradedHom h J J' hJ).right.hom =
      ungradedCommHom (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)
        (extReesPushforwardAlgebra h J') (deformationUnitalHom h J J' hJ) :=
    congrArg Subtype.val
      ((ungradedAlgebraSheafHomEquiv (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)
        (extReesPushforwardAlgebra h J')).apply_symm_apply
        ((ungradedCommHomEquiv (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)
          (extReesPushforwardAlgebra h J')).symm (deformationUnitalHom h J J' hJ)))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hcomp (op W))
      ((extReesGradedAlgebra J).toPresheafGradedAlgebra.incl k x)).trans
    (ungradedTotal_incl (extReesGradedAlgebra J) (extReesPushforwardAlgebra h J')
      (deformationUnitalHom h J J' hJ) k (op W) x)

/-- **The morphism of algebras `𝒪_U[t⁻¹, ℐt] ⟶ (π' ≫ h)_* 𝒪_{D(ℐ')}`** whose relative spectrum
morphism is the morphism of deformation spaces. -/
def deformationAlgebraHom :
    extReesAlgebraSheaf J ⟶ pushforwardAlgebra (deformationSpaceToBase J' ≫ h) :=
  (ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
      (extReesGradedAlgebra_mul_comm J)).inv ≫
    deformationUngradedHom h J J' hJ ≫
    (algebraPushforward h).map (ungradedAlgebraSheafIsoGradedAlgebraSheaf U'
      (extReesGradedAlgebra J') (extReesGradedAlgebra_mul_comm J')).hom ≫
    (algebraPushforward h).map (pushforwardAlgebraIso (extReesAlgebraSheaf J')).inv

/-! ### The morphism of deformation spaces -/

/-- The relative-spectrum pair of the morphism of deformation spaces. -/
def deformationPair : RelativeSpecPair (extReesSituation J) (deformationSpace J') :=
  ⟨deformationSpaceToBase J' ≫ h,
    (extReesAlgebraSheaf J).pairHomEquiv (deformationSpaceToBase J' ≫ h)
      (deformationAlgebraHom h J J' hJ)⟩

/-- **The morphism of deformation spaces `D(ℐ') ⟶ D(ℐ)` over `h`.** -/
def deformationMap : deformationSpace J' ⟶ deformationSpace J :=
  pairToHom (deformationPair h J J' hJ)

/-- **The morphism of deformation spaces lies over `h`.** -/
theorem deformationMap_toBase :
    deformationMap h J J' hJ ≫ deformationSpaceToBase J = deformationSpaceToBase J' ≫ h :=
  pairToHom_toBase _

/-- The image in `Γ(D(ℐ), π⁻¹W)` of a homogeneous section of the extended Rees algebra. -/
def chartIncl (I : U.IdealSheafData) (k : ℤ) (W : U.Opens)
    (x : ((extReesGradedAlgebra I).piece k).val.obj (op W)) :
    Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W) :=
  ((universalAlgebraMap (extReesSituation I)).right.app (op W)).hom
    (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)).hom.right.hom.app (op W)).hom
      (ungradedAlgebraSheafIncl U (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) k W x))

/-- The section `t⁻¹` of `D(ℐ)` over `π⁻¹W` is the image of the homogeneous section `t⁻¹` of degree
`-1`. -/
theorem paramChartOf_eq_chartIncl (I : U.IdealSheafData) (W : U.Opens) :
    paramChartOf I W = chartIncl I (-1) W (paramPiece I W) := rfl

/-- **The morphism of deformation spaces on a homogeneous section**: it sends `x t^k` over `W` to
`h^♯(x) t^k` over `h⁻¹W`. -/
theorem deformationMap_appLE_chartIncl (W : U.affineOpens) (k : ℤ)
    (x : ((extReesGradedAlgebra J).piece k).val.obj (op W.1))
    (hle : (deformationSpaceToBase J' ≫ h) ⁻¹ᵁ W.1 ≤
      deformationMap h J J' hJ ⁻¹ᵁ (deformationSpaceToBase J ⁻¹ᵁ W.1)) :
    ((deformationMap h J J' hJ).appLE (deformationSpaceToBase J ⁻¹ᵁ W.1)
        ((deformationSpaceToBase J' ≫ h) ⁻¹ᵁ W.1) hle).hom (chartIncl J k W.1 x) =
      chartIncl J' k (h ⁻¹ᵁ W.1) (extReesPullback h J J' hJ k W.1 x) := by
  have happLE := pairToHom_appLE (deformationPair h J J' hJ) W hle
  refine (congrArg (fun φ => φ.hom (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U
    (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)).hom.right.hom.app (op W.1)).hom
      (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
        W.1 x))) happLE).trans ?_
  have hinv : ((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
      (extReesGradedAlgebra_mul_comm J)).inv.right.hom.app (op W.1)).hom
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J)).hom.right.hom.app (op W.1)).hom
        (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
          W.1 x)) =
      ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
        W.1 x :=
    congrArg (fun k' : ungradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J) ⟶ ungradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J) => (k'.right.hom.app (op W.1)).hom
          (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
            W.1 x))
      (ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J)).hom_inv_id
  show ((universalAlgebraMap (extReesSituation J')).right.app (op (h ⁻¹ᵁ W.1))).hom
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U' (extReesGradedAlgebra J')
        (extReesGradedAlgebra_mul_comm J')).hom.right.hom.app (op (h ⁻¹ᵁ W.1))).hom
        (((deformationUngradedHom h J J' hJ).right.hom.app (op W.1)).hom
          (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
            (extReesGradedAlgebra_mul_comm J)).inv.right.hom.app (op W.1)).hom
            (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
              (extReesGradedAlgebra_mul_comm J)).hom.right.hom.app (op W.1)).hom
              (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J)
                (extReesGradedAlgebra_mul_comm J) k W.1 x))))) = _
  rw [hinv, deformationUngradedHom_app_incl]
  rfl

end Stacks.Deformation

namespace Stacks.Deformation

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData) (J' : U'.IdealSheafData)
  (hJ : J.comap h ≤ J')

/-- The preimage under `π'` of a subset of `h⁻¹W` lies in the preimage of `π⁻¹W` under the
morphism of deformation spaces. -/
private theorem preimage_le_deformationMap_preimage (W : U.Opens) {W' : U'.Opens}
    (hW' : W' ≤ h ⁻¹ᵁ W) :
    deformationSpaceToBase J' ⁻¹ᵁ W' ≤
      deformationMap h J J' hJ ⁻¹ᵁ (deformationSpaceToBase J ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, deformationMap_toBase, Scheme.Hom.comp_preimage]
  exact Scheme.Hom.preimage_mono _ hW'

/-- **The morphism of deformation spaces pulls `t⁻¹` back to `t⁻¹` on charts.** -/
theorem deformationMap_appLE_paramChartOf (W : U.affineOpens) (W' : U'.Opens)
    (hW' : W' ≤ h ⁻¹ᵁ W.1)
    (hle : deformationSpaceToBase J' ⁻¹ᵁ W' ≤
      deformationMap h J J' hJ ⁻¹ᵁ (deformationSpaceToBase J ⁻¹ᵁ W.1)) :
    ((deformationMap h J J' hJ).appLE (deformationSpaceToBase J ⁻¹ᵁ W.1)
        (deformationSpaceToBase J' ⁻¹ᵁ W') hle).hom (paramChartOf J W.1) =
      paramChartOf J' W' := by
  have hle' := preimage_le_deformationMap_preimage h J J' hJ W.1 (le_refl (h ⁻¹ᵁ W.1))
  have hres : deformationSpaceToBase J' ⁻¹ᵁ W' ≤ (deformationSpaceToBase J' ≫ h) ⁻¹ᵁ W.1 :=
    Scheme.Hom.preimage_mono _ hW'
  have hcomp := Scheme.Hom.appLE_map (deformationMap h J J' hJ) hle' (homOfLE hres).op
  rw [← hcomp]
  refine (congrArg ((deformationSpace J').presheaf.map (homOfLE hres).op).hom
    ((deformationMap_appLE_chartIncl h J J' hJ W (-1) (paramPiece J W.1) hle').trans
      (congrArg (chartIncl J' (-1) (h ⁻¹ᵁ W.1))
        (extReesPullback_paramPiece h J J' hJ W.1)))).trans ?_
  exact paramChartOf_restrict J' hW'

/-- **The inverse image of `Z(t⁻¹)` under the morphism of deformation spaces is `Z(t⁻¹)`.** -/
theorem comap_zeroScheme_paramGlobal :
    (Stacks.Divisors.zeroScheme (deformationSpace J) (Scheme.unitModule (deformationSpace J))
        (paramGlobal J)).comap (deformationMap h J J' hJ) =
      Stacks.Divisors.zeroScheme (deformationSpace J') (Scheme.unitModule (deformationSpace J'))
        (paramGlobal J') := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun P : Σ W : U.affineOpens, {W' : U'.affineOpens // W'.1 ≤ h ⁻¹ᵁ W.1} =>
      (⟨deformationSpaceToBase J' ⁻¹ᵁ P.2.1.1,
        Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation J') P.2.1⟩ :
          (deformationSpace J').affineOpens)) ?_ fun P => ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨W, hW⟩ := Stacks.Divisors.exists_affineOpens_mem (h (deformationSpaceToBase J' x))
    obtain ⟨W', hW'⟩ := Stacks.Divisors.exists_affineOpens_mem (deformationSpaceToBase J' x)
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := U'.isBasis_affineOpens.exists_subset_of_mem_open
      (show deformationSpaceToBase J' x ∈ (W'.1 ⊓ h ⁻¹ᵁ W.1 : U'.Opens) from ⟨hW', hW⟩)
      (W'.1 ⊓ h ⁻¹ᵁ W.1).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, ⟨⟨V, hV⟩, fun y hy => (hVle hy).2⟩⟩, hxV⟩
  · obtain ⟨W, W', hW'⟩ := P
    have hle := preimage_le_deformationMap_preimage h J J' hJ W.1 hW'
    refine (Stacks.IdealSheaf.ideal_comap_appLE _ _
      ⟨_, Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation J) W⟩ _ hle).trans ?_
    refine (congrArg (Ideal.map _) (zeroScheme_paramGlobal_ideal J W)).trans ?_
    refine (Ideal.map_span _ _).trans ?_
    refine Eq.trans ?_ (zeroScheme_paramGlobal_ideal J' W').symm
    refine congrArg Ideal.span ((Set.image_singleton).trans ?_)
    exact congrArg _ (deformationMap_appLE_paramChartOf h J J' hJ W W'.1 hW' hle)

end Stacks.Deformation

namespace Stacks.Deformation

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData) (J' : U'.IdealSheafData)
  (hJ : J.comap h ≤ J')

/-- Every section of the ungraded extended Rees algebra over an affine open is a finite sum of
homogeneous ones. -/
theorem ungradedIncl_induction (I : U.IdealSheafData) (W : U.affineOpens)
    {P : AlgebraSheaf.sections (ungradedAlgebraSheaf U (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I)) W.1 → Prop}
    (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (hincl : ∀ k x, P (ungradedAlgebraSheafIncl U (extReesGradedAlgebra I)
      (extReesGradedAlgebra_mul_comm I) k W.1 x)) (y) : P y := by
  let F : (extReesGradedAlgebra I).toPresheafGradedAlgebra.Total (op W.1) →+*
      AlgebraSheaf.sections (ungradedAlgebraSheaf U (extReesGradedAlgebra I)
        (extReesGradedAlgebra_mul_comm I)) W.1 :=
    (ungradedCommUnit U (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) W.1).hom
  have hF : Function.Surjective F := (bijective_ungradedCommUnit_of_isAffineOpen U
    (extReesGradedAlgebra I) (extReesGradedAlgebra_mul_comm I) W.2).2
  obtain ⟨t, rfl⟩ := hF y
  induction t using Stacks.GradedAlgebra.incl_induction with
  | zero => rw [map_zero]; exact h0
  | incl k x => exact hincl k x
  | add t t' ht ht' => rw [map_add]; exact hadd _ _ ht ht'

include hJ in
/-- **Over a closed immersion, the pullback of homogeneous sections is surjective on affines**
when `ℐ' = ℐ𝒪_{U'}`. -/
theorem extReesPullback_surjective [IsClosedImmersion h] (hJ' : J' = J.comap h)
    (W : U.affineOpens) (k : ℤ) :
    Function.Surjective (extReesPullback h J J' hJ k W.1) := by
  intro z
  have hW' : IsAffineOpen (h ⁻¹ᵁ W.1) := W.2.preimage h
  have hmem := reesPieceAmbient_mem_affine J' (k.toNat : ℤ) (Int.natCast_nonneg _)
    ⟨h ⁻¹ᵁ W.1, hW'⟩ z
  have hsurj : Function.Surjective (h.app W.1).hom := h.app_surjective W.1 W.2
  have hmap : J'.ideal ⟨h ⁻¹ᵁ W.1, hW'⟩ = (J.ideal W).map (h.app W.1).hom := by
    rw [hJ', Stacks.IdealSheaf.ideal_comap_appLE _ _ W ⟨h ⁻¹ᵁ W.1, hW'⟩ le_rfl,
      ← Scheme.Hom.app_eq_appLE]
  rw [hmap, ← Ideal.map_pow, Int.toNat_natCast] at hmem
  obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  refine ⟨(reesPieceAffineEquiv J (k.toNat : ℤ) (Int.natCast_nonneg _) W).symm
    ⟨a, by rw [Int.toNat_natCast]; exact ha⟩, ?_⟩
  refine extReesAmbient_injective J' k (h ⁻¹ᵁ W.1) ?_
  rw [extReesAmbient_extReesPullback]
  have h1 := reesPieceAffineEquiv_coe J (k.toNat : ℤ) (Int.natCast_nonneg _) W
    ((reesPieceAffineEquiv J (k.toNat : ℤ) (Int.natCast_nonneg _) W).symm
      ⟨a, by rw [Int.toNat_natCast]; exact ha⟩)
  rw [AddEquiv.apply_symm_apply] at h1
  show (h.app W.1).hom (reesPieceAmbient J (k.toNat : ℤ) W.1 _) = _
  rw [← h1]
  exact hax

include hJ in
/-- **Over a closed immersion with `ℐ' = ℐ𝒪_{U'}`, the morphism of deformation spaces is a
closed immersion.** -/
theorem isClosedImmersion_deformationMap [IsClosedImmersion h] (hJ' : J' = J.comap h) :
    IsClosedImmersion (deformationMap h J J' hJ) := by
  refine Stacks.RelativeSpec.isClosedImmersion_pairToHom (s := extReesSituation J) _
    (fun W : U.affineOpens => W) (iSup_affineOpens_eq_top _) (fun W => ?_) (fun W => ?_)
  · exact (Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation J')
      ⟨h ⁻¹ᵁ W.1, W.2.preimage h⟩)
  · have hW' : IsAffineOpen (h ⁻¹ᵁ W.1) := W.2.preimage h
    have := isIso_universalAlgebraMap_app (extReesSituation J') ⟨h ⁻¹ᵁ W.1, hW'⟩
    show Function.Surjective ((deformationAlgebraHom h J J' hJ).right.hom.app (op W.1)).hom
    have hU := ConcreteCategory.bijective_of_isIso
      ((universalAlgebraMap (extReesSituation J')).right.app (op (h ⁻¹ᵁ W.1)))
    have he' := bijective_algebraSheafIso_app (ungradedAlgebraSheafIsoGradedAlgebraSheaf U'
      (extReesGradedAlgebra J') (extReesGradedAlgebra_mul_comm J')) (h ⁻¹ᵁ W.1)
    have he := bijective_algebraSheafIso_app (ungradedAlgebraSheafIsoGradedAlgebraSheaf U
      (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)).symm W.1
    have hmid : Function.Surjective
        ((deformationUngradedHom h J J' hJ).right.hom.app (op W.1)).hom := by
      intro y
      induction y using ungradedIncl_induction J' ⟨h ⁻¹ᵁ W.1, hW'⟩ with
      | h0 => exact ⟨0, map_zero _⟩
      | hadd a b ha hb =>
        obtain ⟨a', rfl⟩ := ha
        obtain ⟨b', rfl⟩ := hb
        exact ⟨a' + b', map_add _ _ _⟩
      | hincl k z =>
        obtain ⟨x, rfl⟩ := extReesPullback_surjective h J J' hJ hJ' W k z
        exact ⟨_, deformationUngradedHom_app_incl h J J' hJ k W.1 x⟩
    exact hU.2.comp (he'.2.comp (hmid.comp he.2))

end Stacks.Deformation

namespace Stacks.Deformation

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData) (J' : U'.IdealSheafData)
  (hJ : J.comap h ≤ J')

/-- `Stacks.Deformation.deformationMap_appLE_chartIncl` with the chart of the source written as
`π'⁻¹(h⁻¹W)`. -/
theorem deformationMap_appLE_chartIncl' (W : U.affineOpens) (k : ℤ)
    (x : ((extReesGradedAlgebra J).piece k).val.obj (op W.1))
    (hle : deformationSpaceToBase J' ⁻¹ᵁ (h ⁻¹ᵁ W.1) ≤
      deformationMap h J J' hJ ⁻¹ᵁ (deformationSpaceToBase J ⁻¹ᵁ W.1)) :
    ((deformationMap h J J' hJ).appLE (deformationSpaceToBase J ⁻¹ᵁ W.1)
        (deformationSpaceToBase J' ⁻¹ᵁ (h ⁻¹ᵁ W.1)) hle).hom (chartIncl J k W.1 x) =
      chartIncl J' k (h ⁻¹ᵁ W.1) (extReesPullback h J J' hJ k W.1 x) :=
  deformationMap_appLE_chartIncl h J J' hJ W k x hle

end Stacks.Deformation

end

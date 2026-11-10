module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebraSheaf

/-!
# The extended Rees algebra of a quasi-coherent ideal sheaf

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals. The *extended Rees algebra*
of `ℐ` is the `ℤ`-graded `𝒪_X`-algebra

  `⨁_{k ∈ ℤ} ℐ^{max(k,0)} = ⋯ ⊕ 𝒪_X ⊕ 𝒪_X ⊕ ℐ ⊕ ℐ² ⊕ ⋯`,

the subalgebra `𝒪_X[t⁻¹, ℐt]` of `𝒪_X[t, t⁻¹]`, whose multiplication is the multiplication of
`𝒪_X`. Its relative spectrum is the deformation of `X` to the normal cone of the closed subscheme
cut out by `ℐ`: the section `1` of the degree `-1` piece is the parameter `t⁻¹` of the family,
and the quotient by it is the associated graded algebra `⨁ₖ ℐᵏ/ℐᵏ⁺¹`.

The pieces in nonnegative degree are the pieces `Stacks.Blowup.reesPiece` of the Rees algebra
`⨁_{n ≥ 0} ℐⁿ`, on the nose, so that the conormal algebra, which is a pullback of that Rees
algebra, is reached from here without transport.

## Main definitions

* `Stacks.Blowup.reesPieceLower`: the inclusion `ℐᵐ ⟶ ℐⁿ` for `n ≤ m`.
* `Stacks.Deformation.extReesPiece`: the degree-`k` piece `ℐ^{max(k,0)}`.
* `Stacks.Deformation.extReesGradedAlgebra`: the extended Rees algebra.

## Main results

* `Stacks.Deformation.extReesAmbient_mul`: in `Γ(X, U)` the multiplication is the
  multiplication of sections; every identity of the algebra is reduced to this one, because a
  homogeneous section is determined by its image in `Γ(X, U)`
  (`Stacks.Deformation.extReesAmbient_injective`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- For `n ≤ m`, every local section of `ℐᵐ` lies in `ℐⁿ`: its image in the ideal sheaf of the
subscheme cut out by `ℐⁿ` vanishes. -/
theorem idealPowerKernel_ι_comp_eq_zero {n m : ℕ} (h : n ≤ m) :
    kernel.ι (SheafOfModules.unitToPushforwardObjUnit (I ^ m).subschemeι.toRingCatSheafHom) ≫
      SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom = 0 := by
  have hle : I ^ m ≤ I ^ n := pow_le_pow_right_of_le_one' le_top h
  ext U x
  have hx := congrArg (fun φ => φ.val.app U x)
    (kernel.condition (SheafOfModules.unitToPushforwardObjUnit
      (I ^ m).subschemeι.toRingCatSheafHom))
  change ((I ^ n).subschemeι.app U.unop).hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (I ^ m).subschemeι.toRingCatSheafHom)).val.app U x) = 0
  change ((I ^ m).subschemeι.app U.unop).hom
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
        (I ^ m).subschemeι.toRingCatSheafHom)).val.app U x) = 0 at hx
  have key : ∀ (φ : (I ^ n).subscheme ⟶ X) (hφ : Scheme.IdealSheafData.inclusion hle ≫
      (I ^ m).subschemeι = φ) (a : Γ(X, U.unop)), ((I ^ m).subschemeι.app U.unop).hom a = 0 →
      (φ.app U.unop).hom a = 0 := by
    rintro φ rfl a ha
    exact (congrArg (Scheme.Hom.app (Scheme.IdealSheafData.inclusion hle)
      ((I ^ m).subschemeι ⁻¹ᵁ U.unop)).hom ha).trans (map_zero _)
  exact key _ (Scheme.IdealSheafData.inclusion_subschemeι hle) _ hx

/-- The inclusion `ℐᵐ ⟶ ℐⁿ` of powers of an ideal sheaf, for `n ≤ m`. -/
def reesPieceLower {n m : ℕ} (h : n ≤ m) : idealPowerKernel I m ⟶ idealPowerKernel I n :=
  kernel.lift (C := X.Modules) _ (kernel.ι _) (idealPowerKernel_ι_comp_eq_zero I h)

/-- The inclusion `ℐᵐ ⟶ ℐⁿ` does not change the underlying section of `𝒪_X`. -/
theorem reesPieceAmbient_reesPieceLower {n m : ℕ} (h : n ≤ m) (U : X.Opens)
    (x : (idealPowerKernel I m).val.obj (op U)) :
    idealPowerKernelAmbient I n U ((reesPieceLower I h).val.app (op U) x) =
      idealPowerKernelAmbient I m U x :=
  congrArg (fun φ => φ.val.app (op U) x) (kernel.lift_ι (C := X.Modules) _ (kernel.ι _)
    (idealPowerKernel_ι_comp_eq_zero I h))

end Stacks.Blowup

namespace Stacks.Deformation

open Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The degree-`k` piece `ℐ^{max(k,0)}` of the extended Rees algebra. -/
abbrev extReesPiece (k : ℤ) : SheafOfModules.{u} X.ringCatSheaf :=
  reesPiece I (k.toNat : ℤ)

/-- The image in `Γ(X, U)` of a homogeneous section of the extended Rees algebra. -/
abbrev extReesAmbient (k : ℤ) (U : X.Opens) (x : (extReesPiece I k).val.obj (op U)) : Γ(X, U) :=
  reesPieceAmbient I (k.toNat : ℤ) U x

/-- A homogeneous section of the extended Rees algebra is determined by its image in
`Γ(X, U)`. -/
theorem extReesAmbient_injective (k : ℤ) (U : X.Opens) :
    Function.Injective (extReesAmbient I k U) :=
  reesPieceAmbient_injective I _ (Int.natCast_nonneg _) U

/-- Multiplication of homogeneous sections of the extended Rees algebra, in the second
variable: the product in degrees `max(i,0) + max(j,0)` of the Rees algebra, followed by the
inclusion into degree `max(i+j, 0)`. -/
def extReesMulApp (i j : ℤ) (U : (Opens X)ᵒᵖ) (x : (extReesPiece I i).val.obj U) :
    (extReesPiece I j).val.obj U →+ (extReesPiece I (i + j)).val.obj U :=
  AddMonoidHom.comp
    (LinearMap.toAddMonoidHom
      ((reesPieceLower I (show (i + j).toNat ≤ i.toNat + j.toNat by omega)).val.app U).hom)
    ((reesMultiplication I (i.toNat : ℤ) (j.toNat : ℤ)).app U x)

/-- **The multiplication of the extended Rees algebra is the multiplication of `𝒪_X`.** -/
theorem extReesAmbient_extReesMulApp (i j : ℤ) (U : X.Opens) (x : (extReesPiece I i).val.obj (op U))
    (y : (extReesPiece I j).val.obj (op U)) :
    extReesAmbient I (i + j) U (extReesMulApp I i j (op U) x y) =
      extReesAmbient I i U x * extReesAmbient I j U y :=
  (reesPieceAmbient_reesPieceLower I (by omega) U _).trans
    (reesMultiplication_ambient I (i.toNat : ℤ) (j.toNat : ℤ) U x y)

/-- The image in `Γ(X, U)` of a sum of homogeneous sections is the sum of their images. -/
theorem extReesAmbient_add (k : ℤ) (U : X.Opens) (x y : (extReesPiece I k).val.obj (op U)) :
    extReesAmbient I k U (x + y) = extReesAmbient I k U x + extReesAmbient I k U y :=
  reesPieceAmbient_add I _ U x y

/-- The image in `Γ(X, U)` of `r • x` is the product of `r` with the image of `x`. -/
theorem extReesAmbient_smul (k : ℤ) (U : X.Opens) (r : X.ringCatSheaf.obj.obj (op U))
    (x : (extReesPiece I k).val.obj (op U)) :
    extReesAmbient I k U (r • x) = ringSectionToGamma r * extReesAmbient I k U x :=
  reesPieceAmbient_smul I _ U r x

/-- Taking the image in `Γ(X, -)` commutes with restriction along `U ≤ V`. -/
theorem extReesAmbient_restrict (k : ℤ) (U V : X.Opens) (h : U ≤ V)
    (x : (extReesPiece I k).val.obj (op V)) :
    extReesAmbient I k U ((extReesPiece I k).val.map (homOfLE h).op x) =
      X.presheaf.map (homOfLE h).op (extReesAmbient I k V x) :=
  reesPieceAmbient_restrict I _ U V h x

/-- Transporting a homogeneous section along an equality of degrees does not change its image
in `Γ(X, U)`. -/
theorem extReesAmbient_cast {k l : ℤ} (h : k = l) (U : X.Opens)
    (x : (extReesPiece I k).val.obj (op U)) :
    extReesAmbient I l U (cast (congrArg (fun d => ↥((extReesPiece I d).val.obj (op U))) h) x) =
      extReesAmbient I k U x := by
  cases h
  rfl

/-- Two homogeneous sections whose degrees agree and whose images in `Γ(X, U)` agree are
heterogeneously equal. -/
theorem extRees_heq {k l : ℤ} (h : k = l) (U : X.Opens) (x : (extReesPiece I k).val.obj (op U))
    (y : (extReesPiece I l).val.obj (op U))
    (hxy : extReesAmbient I k U x = extReesAmbient I l U y) : HEq x y := by
  cases h
  exact heq_of_eq (extReesAmbient_injective I k U hxy)

/-- **The multiplication of the extended Rees algebra**: the multiplication of sections of
`𝒪_X`, which adds the degrees. -/
def extReesMul (i j : ℤ) :
    SheafOfModules.BilinearMap (extReesPiece I i) (extReesPiece I j) (extReesPiece I (i + j)) where
  app U := AddMonoidHom.mk' (extReesMulApp I i j U) (fun x x' => by
    ext y
    apply extReesAmbient_injective I (i + j) U.unop
    change extReesAmbient I (i + j) U.unop (extReesMulApp I i j U (x + x') y) =
      extReesAmbient I (i + j) U.unop (extReesMulApp I i j U x y + extReesMulApp I i j U x' y)
    rw [extReesAmbient_add, extReesAmbient_extReesMulApp, extReesAmbient_extReesMulApp,
      extReesAmbient_extReesMulApp, extReesAmbient_add, add_mul])
  map_smul_left U r x y := by
    apply extReesAmbient_injective I (i + j) U.unop
    change extReesAmbient I (i + j) U.unop (extReesMulApp I i j U (r • x) y) =
      extReesAmbient I (i + j) U.unop (r • extReesMulApp I i j U x y)
    rw [extReesAmbient_smul, extReesAmbient_extReesMulApp, extReesAmbient_extReesMulApp,
      extReesAmbient_smul, mul_assoc]
  map_smul_right U r x y := by
    apply extReesAmbient_injective I (i + j) U.unop
    change extReesAmbient I (i + j) U.unop (extReesMulApp I i j U x (r • y)) =
      extReesAmbient I (i + j) U.unop (r • extReesMulApp I i j U x y)
    rw [extReesAmbient_smul, extReesAmbient_extReesMulApp, extReesAmbient_extReesMulApp,
      extReesAmbient_smul, mul_left_comm]
  naturality {U V} f x y := by
    have h : V.unop ≤ U.unop := leOfHom f.unop
    obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
    apply extReesAmbient_injective I (i + j) V.unop
    exact (extReesAmbient_restrict I (i + j) V.unop U.unop h _).trans
      ((congrArg (X.presheaf.map (homOfLE h).op)
          (extReesAmbient_extReesMulApp I i j U.unop x y)).trans
        ((map_mul (X.presheaf.map (homOfLE h).op).hom _ _).trans
          ((congrArg₂ (· * ·) (extReesAmbient_restrict I i V.unop U.unop h x).symm
            (extReesAmbient_restrict I j V.unop U.unop h y).symm).trans
            (extReesAmbient_extReesMulApp I i j V.unop _ _).symm)))

/-- The image in `Γ(X, U)` of a product under `extReesMul` is the product of the images. -/
theorem extReesAmbient_extReesMul (i j : ℤ) (U : X.Opens)
    (x : (extReesPiece I i).val.obj (op U)) (y : (extReesPiece I j).val.obj (op U)) :
    extReesAmbient I (i + j) U ((extReesMul I i j).app (op U) x y) =
      extReesAmbient I i U x * extReesAmbient I j U y :=
  extReesAmbient_extReesMulApp I i j U x y

/-- The unit of the extended Rees algebra: the global section `1` of `𝒪_X` in degree zero. -/
def extReesOne : (extReesPiece I 0).val.sections :=
  reesUnit I

/-- The image in `Γ(X, U)` of the unit `extReesOne` is `1`. -/
theorem extReesAmbient_extReesOne (U : (Opens X)ᵒᵖ) :
    extReesAmbient I 0 U.unop ((extReesOne I).eval U) = 1 :=
  reesUnit_ambient I U

/-- **The extended Rees algebra `⨁_{k ∈ ℤ} ℐ^{max(k,0)}`** of a quasi-coherent ideal sheaf, as a
sheaf of `ℤ`-graded `𝒪_X`-algebras. -/
def extReesGradedAlgebra : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf where
  piece := extReesPiece I
  mul := extReesMul I
  one := extReesOne I
  mul_assoc i j k U x y z := by
    refine extRees_heq I (add_assoc i j k) U.unop _ _ ?_
    refine (extReesAmbient_extReesMul I (i + j) k U.unop _ z).trans ?_
    refine Eq.trans ?_ (extReesAmbient_extReesMul I i (j + k) U.unop x _).symm
    rw [extReesAmbient_extReesMul I i j U.unop x y, extReesAmbient_extReesMul I j k U.unop y z,
      mul_assoc]
  one_mul i U x := by
    refine extRees_heq I (zero_add i) U.unop _ _ ?_
    refine (extReesAmbient_extReesMul I 0 i U.unop _ x).trans ?_
    rw [extReesAmbient_extReesOne, one_mul]
  mul_one i U x := by
    refine extRees_heq I (add_zero i) U.unop _ _ ?_
    refine (extReesAmbient_extReesMul I i 0 U.unop x _).trans ?_
    rw [extReesAmbient_extReesOne, mul_one]

/-- The homogeneous multiplication of the extended Rees algebra is commutative. -/
theorem extReesGradedAlgebra_mul_comm (i j : ℤ) (U : (Opens X)ᵒᵖ)
    (x : ((extReesGradedAlgebra I).piece i).val.obj U)
    (y : ((extReesGradedAlgebra I).piece j).val.obj U) :
    HEq (((extReesGradedAlgebra I).mul i j).app U x y)
      (((extReesGradedAlgebra I).mul j i).app U y x) := by
  refine extRees_heq I (add_comm i j) U.unop _ _ ?_
  exact (extReesAmbient_extReesMul I i j U.unop x y).trans
    ((mul_comm _ _).trans (extReesAmbient_extReesMul I j i U.unop y x).symm)

/-- Every homogeneous piece of the extended Rees algebra is quasi-coherent. -/
theorem extReesPiece_isQuasicoherent (k : ℤ) : (extReesPiece I k).IsQuasicoherent :=
  reesPiece_isQuasicoherent I _

end Stacks.Deformation

end

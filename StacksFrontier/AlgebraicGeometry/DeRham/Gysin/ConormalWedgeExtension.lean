module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgePair
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Bilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.DerivedLeftUnitorSingle

/-!
# The wedge with a section over an open, extended to the whole scheme

For an open `V ⊆ X` write `A' = (V.ι)_*(Ω^p|_V)` and `G' = (V.ι)_*(Ω^{p+c}|_V)`. The wedge of
forms on `V` pushes forward to a bilinear map `A' × Ω^c ⟶ G'` (the second factor restricted to `V`
by the unit of the restriction adjunction), `extendedFormWedgePair`. Its two properties listed
under the main results are the ones used in the identification of the multiplication of
Tag 0G75 with the pairing of Tag 0G88.

## Main definitions

* `Stacks.Gysin.pushforwardOpenBilinear`: the direct image along `V.ι` of a bilinear map of
  modules on `V`.
* `Stacks.Gysin.extendedFormWedgePair`: the bilinear map `A' × Ω^c ⟶ G'`.
* `Stacks.Gysin.extendedSectionHom`: the morphism `𝒪_X ⟶ A'` given by a section `ω` of `Ω^p`
  over `V`.

## Main results

* `Stacks.Gysin.openUnit_tensor_extendedFormWedge`: precomposed with the unit `Ω^p ⟶ A'` the
  extended wedge is the wedge of forms followed by the unit `Ω^{p+c} ⟶ G'`.
* `Stacks.Gysin.extendedSectionHom_tensor_extendedFormWedge`: on the global section of `A'` given
  by `ω` the extended wedge is `Stacks.Gysin.localFormWedgeExt`, multiplication by `ω`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open Stacks.AlgebraicGeometry.ModuleLimits
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.Gysin

variable {X S : Scheme.{u}}

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- **A bilinear map on an open subscheme, pushed forward to the ambient scheme.** The sections of
the direct image over an open `U` are the sections over `V.ι ⁻¹ᵁ U`, where the bilinear map is
evaluated. -/
def pushforwardOpenBilinear (V : X.Opens) {M N P : V.toScheme.Modules}
    (β : SheafOfModules.BilinearMap M N P) :
    SheafOfModules.BilinearMap ((Scheme.Modules.pushforward V.ι).obj M)
      ((Scheme.Modules.pushforward V.ι).obj N) ((Scheme.Modules.pushforward V.ι).obj P) where
  app U := β.app (op (V.ι ⁻¹ᵁ U.unop))
  map_smul_left _ _ x y := β.map_smul_left _ _ x y
  map_smul_right _ _ x y := β.map_smul_right _ _ x y
  naturality h x y := β.naturality (homOfLE (V.ι.preimage_mono (leOfHom h.unop))).op x y

/-- Over an open `U`, the pushed-forward bilinear map is the original one over `V.ι ⁻¹ᵁ U`. -/
@[simp]
theorem pushforwardOpenBilinear_app (V : X.Opens) {M N P : V.toScheme.Modules}
    (β : SheafOfModules.BilinearMap M N P) (U : X.Opens)
    (x : ((Scheme.Modules.pushforward V.ι).obj M).val.obj (op U))
    (y : ((Scheme.Modules.pushforward V.ι).obj N).val.obj (op U)) :
    (pushforwardOpenBilinear V β).app (op U) x y = β.app (op (V.ι ⁻¹ᵁ U)) x y :=
  rfl

/-- `f ⊗ 𝟙` on a local pure tensor. -/
theorem sheafTensor_map_app_tensorSheafUnit
    {A A' G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (f : A ⟶ A') (U : X.Opensᵒᵖ) (x : A.val.obj U) (y : G.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map f).app G).val.app U
        ((PresheafOfModules.tensorSheafUnit A G).app U (x ⊗ₜ y)) =
      (PresheafOfModules.tensorSheafUnit A' G).app U (f.val.app U x ⊗ₜ y) := by
  have h₁ := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit X.sheaf
    (F := A) (G := G) (F' := A') (G' := G) f (𝟙 G) U x y
  have e₁ := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A').map_id G
  exact (congrArg (fun t => (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.sheaf).map f).app G ≫ t).val.app U
      ((PresheafOfModules.tensorSheafUnit A G).app U (x ⊗ₜ y))) e₁).symm.trans h₁

variable (π : X ⟶ S) (c p : ℕ) (V : X.Opens)

/-- **The wedge of forms on `V`, pushed forward to `X`**, with its second factor a form on `X`
restricted to `V`. -/
def extendedFormWedgePair :
    SheafOfModules.BilinearMap
      ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π (p : ℤ))))
      (relativeDifferentialForms π (c : ℤ))
      ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) :=
  (pushforwardOpenBilinear V (restrictBilinear V.ι (formWedgePair π p c))).compRight
    (openUnit V (relativeDifferentialForms π (c : ℤ))).val

/-- The extended wedge on local sections. -/
theorem extendedFormWedgePair_app (U : X.Opens)
    (x : ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
      (relativeDifferentialForms π (p : ℤ)))).val.obj (op U))
    (y : (relativeDifferentialForms π (c : ℤ)).val.obj (op U)) :
    (extendedFormWedgePair π c p V).app (op U) x y =
      (formWedgePair π p c).app (op (V.ι ''ᵁ (V.ι ⁻¹ᵁ U))) x
        ((relativeDifferentialForms π (c : ℤ)).val.map (homOfLE (V.ι.image_preimage_le U)).op y) :=
  rfl

/-- **The section of `(V.ι)_*(Ω^p|_V)` given by a section of `Ω^p` over `V`.** -/
def extendedSection (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
      (relativeDifferentialForms π (p : ℤ)))).val.sections :=
  PresheafOfModules.sectionsMk
    (fun U => (localSections V (relativeDifferentialForms π (p : ℤ)) ω).eval (op (V.ι ⁻¹ᵁ U.unop)))
    (fun {_ _} h => (localSections V (relativeDifferentialForms π (p : ℤ)) ω).property
      (homOfLE (V.ι.preimage_mono (leOfHom h.unop))).op)

/-- **The extended wedge restricts the ordinary one**: precomposed with the unit
`Ω^p ⟶ (V.ι)_*(Ω^p|_V)` it is the wedge of forms followed by the unit of `Ω^{p+c}`. -/
theorem openUnit_tensor_extendedFormWedge :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
        (openUnit V (relativeDifferentialForms π (p : ℤ)))).app
        (relativeDifferentialForms π (c : ℤ)) ≫
      Stacks.RingedSpace.ofBilinearSheaf (extendedFormWedgePair π c p V) =
    SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (p : ℤ) (c : ℤ) ≫
      openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))) := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf)
    (F := relativeDifferentialForms π (p : ℤ)) (G := relativeDifferentialForms π (c : ℤ))
    fun U x y => ?_
  have h₁ := sheafTensor_map_app_tensorSheafUnit (G := relativeDifferentialForms π (c : ℤ))
    (openUnit V (relativeDifferentialForms π (p : ℤ))) U x y
  have h₂ := Stacks.RingedSpace.ofBilinearSheaf_unit_tmul (Y := X.toRingedSpace)
    (extendedFormWedgePair π c p V) U
    ((openUnit V (relativeDifferentialForms π (p : ℤ))).val.app U x) y
  have h₃ := SheafOfModules.GradedAlgebra.mulSheaf_unit (relativeDifferentialFormsAlgebra π)
    (p : ℤ) (c : ℤ) U x y
  have h₄ := (formWedgePair π p c).naturality (homOfLE (V.ι.image_preimage_le U.unop)).op x y
  exact ((congrArg (fun t => (Stacks.RingedSpace.ofBilinearSheaf
    (extendedFormWedgePair π c p V)).val.app U t) h₁).trans h₂).trans
    ((congrArg (fun t => (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))).val.app U t)
      h₃).trans h₄).symm

/-- **The global section of `(V.ι)_*(Ω^p|_V)` given by `ω`, as a morphism out of `𝒪_X`.** -/
def extendedSectionHom (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    Stacks.DeRham.GysinCupHodge.unitModule X.toRingedSpace ⟶
      (Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
        (relativeDifferentialForms π (p : ℤ))) :=
  (SheafOfModules.unitHomEquiv _).symm (extendedSection π p V ω)

/-- Over an open `U`, `extendedSectionHom` sends a local function `r` to `r` times the section
given by `ω`. -/
theorem extendedSectionHom_app (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) (U : X.Opens)
    (r : (Stacks.DeRham.GysinCupHodge.unitModule X.toRingedSpace).val.obj (op U)) :
    (extendedSectionHom π p V ω).val.app (op U) r =
      (show X.ringCatSheaf.obj.obj (op U) from r) •
        (show ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.restrictFunctor V.ι).obj
          (relativeDifferentialForms π (p : ℤ)))).val.obj (op U) from
            (extendedSection π p V ω).val (op U)) := by
  simp only [extendedSectionHom, SheafOfModules.unitHomEquiv]
  change ((PresheafOfModules.unitHomEquiv _).symm (extendedSection π p V ω)).app (op U) r = _
  simp [PresheafOfModules.unitHomEquiv]
  rfl

/-- **On the section given by `ω` the extended wedge is multiplication by `ω`.** -/
theorem extendedSectionHom_tensor_extendedFormWedge
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).map
        (extendedSectionHom π p V ω)).app (relativeDifferentialForms π (c : ℤ)) ≫
      Stacks.RingedSpace.ofBilinearSheaf (extendedFormWedgePair π c p V) =
    (Stacks.DeRham.GysinCupHodge.sheafLeftUnitor (X := X.toRingedSpace)
        (relativeDifferentialForms π (c : ℤ))).hom ≫ localFormWedgeExt π p V ω := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf)
    (F := Stacks.DeRham.GysinCupHodge.unitModule X.toRingedSpace)
    (G := relativeDifferentialForms π (c : ℤ)) fun U r m => ?_
  have h₁ := sheafTensor_map_app_tensorSheafUnit (G := relativeDifferentialForms π (c : ℤ))
    (extendedSectionHom π p V ω) U r m
  have h₂ := Stacks.RingedSpace.ofBilinearSheaf_unit_tmul (Y := X.toRingedSpace)
    (extendedFormWedgePair π c p V) U ((extendedSectionHom π p V ω).val.app U r) m
  have h₃ := Stacks.DeRham.GysinCupHodge.sheafLeftUnitor_hom_apply (X := X.toRingedSpace)
    (relativeDifferentialForms π (c : ℤ)) U r m
  refine ((congrArg (fun t => (Stacks.RingedSpace.ofBilinearSheaf
    (extendedFormWedgePair π c p V)).val.app U t) h₁).trans h₂).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (localFormWedgeExt π p V ω).val.app U t) h₃).symm
  rw [map_smul, extendedSectionHom_app π p V ω U.unop r, extendedFormWedgePair_app]
  refine ((formWedgePair π p c).map_smul_left _ _ _ _).trans ?_
  congr 1

end StandardModel

end Stacks.Gysin



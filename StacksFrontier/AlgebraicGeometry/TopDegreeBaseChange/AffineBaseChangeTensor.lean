module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseChangeCore
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayTopDegreeMap
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionFormula
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TensorComparisonUnitIso
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPushforwardLinear
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.AffineOpen
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] over affine bases

Let
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
be a cartesian square with `Y'` and `Y''` affine, `F'` a quasi-coherent module on `X'`, and write
`R' = Γ(Y', ⊤)`, `R'' = Γ(Y'', ⊤)`, `M = Γ(R^d f'_* F', ⊤)` and `P = R^d f''_* (h')^* F'`. The
source's computation of the canonical map `γ` of conclusion (c) over affine bases is the chain of
bijections

`R'' ⊗_{R'} M ≅ M ⊗_{R'} Γ(h_* 𝒪_{Y''}, ⊤) ≅ Γ(R^d f'_* F' ⊗ h_* 𝒪_{Y''}, ⊤)`
`  ≅ Γ(R^d f'_*(F' ⊗ (f')^* h_* 𝒪_{Y''}), ⊤) ≅ Γ(R^d f'_*((h')_*(h')^* F'), ⊤) ≅ Γ(P, ⊤)`:

the symmetry of the tensor product, the section formula for a tensor product over an affine open
(`Stacks.SectionTensorFormula.bijective_tensorSectionLinear`), conclusion (b)
(`…TopDegreeBaseChange.isIso_higherDirectImageTensorMap`), the projection formula
(`…TopDegreeBaseChange.pushforwardPullbackTensorIsoRight`), and the Leray comparison `Θ` of the
transpose of `γ⁺` (`…TopDegreeBaseChange.isIso_lerayTail`) followed by the restriction along
`⊤ = h⁻¹ ⊤`. This file builds that bijection, computes it on pure tensors — `r ⊗ a ↦ r • γ⁺(a)` —
and so, by `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isAffine_of_tensor`, proves
that `γ` is an isomorphism.

The computation on pure tensors runs through the sheaf identity
`tensorGlobalSection_comp_pushforwardPullbackTensorIsoRight`: tensoring with the pullback of the
global function `r` of `Y''`, followed by the projection formula, is the unit of `h'^* ⊣ h'_*`
followed by `h'_*`(multiplication by `f''^♯ r`). The naturality of `Θ`
(`…TopDegreeBaseChange.lerayTail_naturality`) carries that multiplication down to
`h_*(R^d f''_*(f''^♯ r))`, which is multiplication by `r`.

## Main results

* `…TopDegreeBaseChange.tensorBaseChangeAddHom` and
  `…TopDegreeBaseChange.bijective_tensorBaseChangeAddHom`: the bijection, for any isomorphism `Θ`.
* `…TopDegreeBaseChange.tensorGlobalSection_comp_pushforwardPullbackTensorIsoRight`: the sheaf
  identity.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isAffine_of_tail`: `γ` is an
  isomorphism, given an isomorphism `Θ` that is the tail of the transpose of `γ⁺` and natural in
  the module upstairs.
* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isAffine`: **conclusion (c) of
  [Stacks, Tag 0EX3] for affine `Y'` and `Y''`.**

## Implementation notes

*The tail is a variable.* As explained in `LerayTopDegreeMap.lean`, a declaration naming the tail
`Θ` of the transpose of `γ⁺` together with that transpose does not pass the kernel. So everything
here takes `Θ` as a variable, with its two properties as hypotheses, and the final theorem
supplies the proved equation of the transpose, `isIso_lerayTail` and `lerayTail_naturality`, for
unification to fill `Θ` in.

*Rewriting under the tensor product sheaf.* A goal mentioning
`Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩` is not type-correct at
`implicit` transparency, so `rw` cannot abstract in it; those steps are chained with `Eq.trans`
and `congrArg` instead.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.TensorStalkRingedSpace
open AlgebraicGeometry.IntegralTransformQcoh
open scoped ChangeOfRings CategoryTheory.Prod

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- The extension of scalars `S ⊗_R M` along `φ : R ⟶ S`, written as `M ⊗_R Q` for an `R`-linear
identification `ρ : S ≃ Q`: the symmetry of the tensor product followed by `ρ`. -/
def extendScalarsSwapEquiv {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} R)
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (ρ : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ≃ₗ[R] Q) :
    (ModuleCat.extendScalars φ.hom).obj M ≃+ TensorProduct R M Q :=
  (TensorProduct.comm R _ M ≪≫ₗ TensorProduct.congr (LinearEquiv.refl R M) ρ).toAddEquiv

/-- `extendScalarsSwapEquiv` sends `s ⊗ m` to `m ⊗ ρ s`. -/
theorem extendScalarsSwapEquiv_tmul {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} R)
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (ρ : (ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of S S) ≃ₗ[R] Q) (s : S) (m : M) :
    extendScalarsSwapEquiv φ M ρ (s ⊗ₜ[R, φ.hom] m) = m ⊗ₜ[R] ρ s := rfl

variable {Y' Y'' : Scheme.{u}}

/-- For `h : Y'' ⟶ Y'`, the global functions of `Y''`, as an `R'`-module through `h`, are the
global sections of `h_* 𝒪_{Y''}`: restriction from `⊤` to `h⁻¹ ⊤`, which is the same open. -/
def unitPushforwardTopEquiv (h : Y'' ⟶ Y') (hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤) :
    (ModuleCat.restrictScalars (h.appLE ⊤ ⊤ hle).hom).obj (ModuleCat.of Γ(Y'', ⊤) Γ(Y'', ⊤))
      ≃ₗ[Γ(Y', ⊤)] Γ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''), ⊤) where
  toFun x := (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom x
  invFun y := (Y''.presheaf.map (homOfLE hle).op).hom y
  map_add' x y := map_add _ x y
  map_smul' r x := by
    change (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom
        ((h.appLE ⊤ ⊤ hle).hom r * (show Γ(Y'', ⊤) from x)) =
      (h.app ⊤).hom r * (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom (show Γ(Y'', ⊤) from x)
    rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE]
  left_inv x := by
    change (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op ≫ Y''.presheaf.map (homOfLE hle).op).hom x = x
    rw [← Functor.map_comp, show (h ⁻¹ᵁ ⊤).leTop.op ≫ (homOfLE hle).op = 𝟙 _ from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  right_inv y := by
    change (Y''.presheaf.map (homOfLE hle).op ≫ Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom y = y
    rw [← Functor.map_comp, show (homOfLE hle).op ≫ (h ⁻¹ᵁ ⊤).leTop.op = 𝟙 _ from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl

variable {X'' : Scheme.{u}} (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)

/-- **The bijection `R'' ⊗_{R'} M ⟶ Γ(R^d f''_* (h')^* F', ⊤)` of the source's affine computation
of conclusion (c) of [Stacks, Tag 0EX3]**, for a morphism `Θ` standing for the tail of the
transpose of `γ⁺`: the symmetry of the tensor product, the sheafification unit of the sectionwise
tensor product, the canonical map of conclusion (b) at `h_* 𝒪_{Y''}`, the higher direct image of
the projection formula, `Θ`, and the restriction along `⊤ ≤ h⁻¹ ⊤`. -/
def tensorBaseChangeAddHom [IsAffineHom h] (hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤)
    (Θ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
        ((modulePullback h'.toLRSHom.toShHom ⋙ modulePushforward h'.toLRSHom.toShHom).obj F') ⟶
      (Scheme.Modules.pushforward h).obj
        (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pullback h').obj F'))) :
    (ModuleCat.extendScalars (h.appLE ⊤ ⊤ hle).hom).obj
        (ModuleCat.of Γ(S.Y', ⊤) Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus
          (S.d : ℤ)).obj F', ⊤)) →+
      Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F'), ⊤) :=
  (((((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F')).presheaf.map (homOfLE hle).op).hom).comp
   ((Scheme.Modules.Hom.app Θ ⊤).hom.comp
   ((Scheme.Modules.Hom.app (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
      (pushforwardPullbackTensorIsoRight S.f' h' f'' h hsq F' inferInstance).hom) ⊤).hom.comp
   ((Scheme.Modules.Hom.app (higherDirectImageTensorMap S.f' F'
      ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')) S.d) ⊤).hom.comp
   ((Stacks.SectionTensorFormula.tensorSheafUnitAdd
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
      ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')) ⊤).comp
    (extendScalarsSwapEquiv _ _ (unitPushforwardTopEquiv h hle)).toAddMonoidHom))))

/-- **The map `tensorBaseChangeAddHom` is bijective** when `Y'` is affine and `Θ` is an
isomorphism: each factor is. -/
theorem bijective_tensorBaseChangeAddHom [IsAffine S.Y'] [IsAffineHom h]
    (hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤)
    (Θ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
        ((modulePullback h'.toLRSHom.toShHom ⋙ modulePushforward h'.toLRSHom.toShHom).obj F') ⟶
      (Scheme.Modules.pushforward h).obj
        (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pullback h').obj F'))) [IsIso Θ] :
    Function.Bijective (tensorBaseChangeAddHom S F' h' f'' h hsq hle Θ) := by
  have := S.quasiCompact_f'
  have := S.quasiSeparated_f'
  have : (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F').IsQuasicoherent :=
    AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_rightDerivedPlus S.f' F'
      inferInstance (S.d : ℤ)
  have : ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')).IsQuasicoherent :=
    AlgebraicGeometry.ClosedImmersionCoherentImage.isQuasicoherent_pushforward_unit h
  have := isIso_higherDirectImageTensorMap S F'
    ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))
  have e : (⊤ : Y''.Opens) = h ⁻¹ᵁ ⊤ := le_antisymm hle le_top
  have hres : homOfLE hle = eqToHom e := Subsingleton.elim _ _
  have hc : ∀ {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
      {f : B →+ C} {g : A →+ B}, Function.Bijective f → Function.Bijective g →
        Function.Bijective (f.comp g) := fun hf hg => hf.comp hg
  refine hc ?_ (hc ?_ (hc ?_ (hc ?_ (hc ?_ (AddEquiv.bijective _)))))
  · rw [hres]
    exact ConcreteCategory.bijective_of_isIso _
  · exact ConcreteCategory.bijective_of_isIso _
  · exact @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _
      (Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).mapIso
        (pushforwardPullbackTensorIsoRight S.f' h' f'' h hsq F' inferInstance)).isIso_hom ⊤)
  · exact @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _
      (Scheme.Modules.Hom.isIso_iff_isIso_app.mp this ⊤)
  · exact (Stacks.SectionTensorFormula.bijective_tensorSectionLinear_iff _ _ ⊤).mp
      (Stacks.SectionTensorFormula.bijective_tensorSectionLinear _ _ (isAffineOpen_top S.Y'))

section Sheaf

variable {X₁ Y₁ X₂ Y₂ : Scheme.{u}} (f₁ : X₁ ⟶ Y₁) (a' : X₂ ⟶ X₁) (b : X₂ ⟶ Y₂) (a : Y₂ ⟶ Y₁)

/-- The tensor product sheaf, uncurried, on a morphism whose first leg is an identity. -/
theorem sheafTensor_uncurry_map_id_left (F : X₁.Modules) {G G' : X₁.Modules} (g : G ⟶ G') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X₁.toRingedSpace.presheaf, X₁.toRingedSpace.IsSheaf⟩)).map
      ((𝟙 F ×ₘ g : ((F, G) : _ × _) ⟶ (F, G'))) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X₁.toRingedSpace.presheaf, X₁.toRingedSpace.IsSheaf⟩).obj F).map g :=
  Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map _ (𝟙 F) g

/-- The two spellings of the inverse right unitor `F ⟶ F ⊗ 𝒪` agree. -/
theorem tensorUnitInv_eq_tensorSheafUnitRightIso_inv (F : X₁.Modules) :
    tensorUnitInv F = (Stacks.RingedSpace.tensorSheafUnitRightIso X₁.toRingedSpace F).inv := rfl

/-- `unitGlobalSection` is natural in the module. -/
theorem unitGlobalSection_naturality {G G' : Y₁.Modules} (φ : G ⟶ G') (s : Γ(G, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback f₁).map φ) ⊤ (unitGlobalSection f₁ G s) =
      unitGlobalSection f₁ G' (Scheme.Modules.Hom.app φ ⊤ s) :=
  Scheme.Modules.unit_app_val_app_naturality f₁ φ ⊤ s

/-- Multiplication by `r` on `h_* 𝒪_{Y''}` sends the unit section to the restriction of `r`. -/
theorem unitToPushforwardUnit_sectionScalar_one (r : Γ(Y₂, ⊤)) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pushforward a).map
          (sectionScalar Y₂ r (Scheme.unitModule Y₂))) ⊤
        (Scheme.Modules.Hom.app (Scheme.Modules.unitToPushforwardUnit a) ⊤
          (1 : ↑(Y₁.presheaf.obj (op ⊤)))) =
      (show Γ((Scheme.Modules.pushforward a).obj (Scheme.unitModule Y₂), ⊤) from
          (Y₂.presheaf.map (a ⁻¹ᵁ ⊤).leTop.op).hom r) := by
  change (Y₂.presheaf.map (a ⁻¹ᵁ ⊤).leTop.op).hom r * (a.app ⊤).hom 1 = _
  rw [map_one, mul_one]

/-- **Tensoring with the pullback of a global function, followed by the projection formula, is
the unit followed by multiplication upstairs.** For a cartesian square with `h` and `h'` affine,
a quasi-coherent `F'` and a global function `r` on `Y''`, the morphism
`F' ⟶ F' ⊗ (f')^* h_* 𝒪_{Y''}`, `x ↦ x ⊗ (f')^* r`, followed by
`…TopDegreeBaseChange.pushforwardPullbackTensorIsoRight`, is the unit `F' ⟶ h'_* (h')^* F'`
followed by `h'_*`(multiplication by `f''^♯ r`).

The section `r` is the image of the unit section under multiplication by `r`, so the left-hand
side is the inverse unitor followed by the structure morphisms tensored in, then multiplication
by `r`; the projection formula carries the multiplication upstairs
(`…TopDegreeBaseChange.sectionScalar_comp_pushforwardPullbackTensorIsoRight`) and the rest is
the unit (`…TopDegreeBaseChange.unit_eq_pushforwardPullbackTensorIsoRight`). -/
theorem tensorGlobalSection_comp_pushforwardPullbackTensorIsoRight (hsq : IsPullback a' b f₁ a)
    [IsAffineHom a] [IsAffineHom a'] (F : X₁.Modules) (hF : F.IsQuasicoherent) (r : Γ(Y₂, ⊤)) :
    tensorGlobalSection F ((Scheme.Modules.pullback f₁).obj
        ((Scheme.Modules.pushforward a).obj (Scheme.unitModule Y₂)))
      (unitGlobalSection f₁ ((Scheme.Modules.pushforward a).obj (Scheme.unitModule Y₂))
        (show Γ((Scheme.Modules.pushforward a).obj (Scheme.unitModule Y₂), ⊤) from
          (Y₂.presheaf.map (a ⁻¹ᵁ ⊤).leTop.op).hom r)) ≫
      (pushforwardPullbackTensorIsoRight f₁ a' b a hsq F hF).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction a').unit.app F ≫
      (Scheme.Modules.pushforward a').map
        (sectionScalar X₂ (b.appTop.hom r) ((Scheme.Modules.pullback a').obj F)) := by
  have e1 : unitGlobalSection f₁ ((Scheme.Modules.pushforward a).obj (Scheme.unitModule Y₂))
      (show Γ((Scheme.Modules.pushforward a).obj (Scheme.unitModule Y₂), ⊤) from
          (Y₂.presheaf.map (a ⁻¹ᵁ ⊤).leTop.op).hom r) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback f₁).map ((Scheme.Modules.pushforward a).map
          (sectionScalar Y₂ r (Scheme.unitModule Y₂)))) ⊤
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f₁).map
            (Scheme.Modules.unitToPushforwardUnit a)) ⊤
          (unitGlobalSection f₁ (Scheme.unitModule Y₁) (1 : ↑(Y₁.presheaf.obj (op ⊤))))) :=
    ((congrArg (Scheme.Modules.Hom.app ((Scheme.Modules.pullback f₁).map
          ((Scheme.Modules.pushforward a).map (sectionScalar Y₂ r (Scheme.unitModule Y₂)))) ⊤)
        (unitGlobalSection_naturality f₁ (Scheme.Modules.unitToPushforwardUnit a) _)).trans
      ((unitGlobalSection_naturality f₁ _ _).trans
        (congrArg (unitGlobalSection f₁ _) (unitToPushforwardUnit_sectionScalar_one a r)))).symm
  have e2 := (congrArg (tensorGlobalSection F _) e1).trans
    ((tensorGlobalSection_naturality F _ _ _).symm.trans
      (congrArg (· ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X₁.toRingedSpace.presheaf, X₁.toRingedSpace.IsSheaf⟩).obj F).map
          ((Scheme.Modules.pullback f₁).map ((Scheme.Modules.pushforward a).map
            (sectionScalar Y₂ r (Scheme.unitModule Y₂)))))
        ((tensorGlobalSection_naturality F _ _ _).symm.trans
          (congrArg (· ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨X₁.toRingedSpace.presheaf, X₁.toRingedSpace.IsSheaf⟩).obj F).map
              ((Scheme.Modules.pullback f₁).map (Scheme.Modules.unitToPushforwardUnit a)))
            (tensorGlobalSection_unitGlobalSection_eq f₁ F)))))
  have hnat := sectionScalar_comp_pushforwardPullbackTensorIsoRight f₁ a' b a hsq F hF r
    (b.appTop.hom r) rfl
  have hunit := unit_eq_pushforwardPullbackTensorIsoRight f₁ a' b a hsq F hF
  have hnat' := (congrArg (· ≫ (pushforwardPullbackTensorIsoRight f₁ a' b a hsq F hF).hom)
    (sheafTensor_uncurry_map_id_left F ((Scheme.Modules.pullback f₁).map
      ((Scheme.Modules.pushforward a).map (sectionScalar Y₂ r (Scheme.unitModule Y₂)))))).symm.trans
    hnat
  have hunit' := (congrArg (fun z => (Stacks.RingedSpace.tensorSheafUnitRightIso
      X₁.toRingedSpace F).inv ≫ z ≫ (pushforwardPullbackTensorIsoRight f₁ a' b a hsq F hF).hom)
    ((sheafTensor_uncurry_map_id_left F ((Scheme.Modules.pullbackUnitIso f₁).inv ≫
      (Scheme.Modules.pullback f₁).map (Scheme.Modules.unitToPushforwardUnit a))).trans
      (Functor.map_comp _ _ _))).symm.trans hunit
  refine (congrArg (· ≫ (pushforwardPullbackTensorIsoRight f₁ a' b a hsq F hF).hom) e2).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hnat').trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) ?_)))
  exact (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans hunit'))

/-- **The higher direct image of multiplication by the pullback of a global function is
multiplication by that function.** -/
theorem rightDerivedPlus_pushforward_map_sectionScalar_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ) (r : Γ(Y, ⊤)) (M : X.Modules) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map
        (sectionScalar X (f.appTop.hom r) M) =
      sectionScalar Y r (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj M) := by
  have e1 := (congrArg (fun z => sectionScalar X z M)
    (baseRingToSections_comp_toSpecΓ_top f r)).symm.trans
      (sectionScalar_eq_baseScalar ↑Γ(Y, ⊤) (Over.mk (f ≫ Y.toSpecΓ)) r M)
  exact (congrArg (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).map) e1).trans
    ((SchemeHigherDirectImage.rightDerivedPlus_pushforward_map_baseScalar_toSpecΓ f n r M).trans
      (sectionScalar_eq_baseScalar_toSpecΓ Y r _).symm)

/-- Multiplication by a global function, on global sections. -/
theorem sectionScalar_app_top {X : Scheme.{u}} (r : Γ(X, ⊤)) (M : X.Modules) (x : Γ(M, ⊤)) :
    Scheme.Modules.Hom.app (sectionScalar X r M) ⊤ x = r • x := by
  change (X.presheaf.map (⊤ : X.Opens).leTop.op).hom r • x = r • x
  rw [show (⊤ : X.Opens).leTop = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restricting a global section to the top open does nothing. -/
theorem globalRestrict_top {X : Scheme.{u}} (G : X.Modules) (s : Γ(G, ⊤)) :
    globalRestrict G s ⊤ = s := by
  change G.presheaf.map (homOfLE le_top).op s = s
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

end Sheaf

/-- `tensorBaseChangeAddHom` on a pure tensor `r ⊗ x`: the restriction of the value at `x` of
`R^d f'_*(x ↦ x ⊗ (f')^* r)`, then the higher direct image of the projection formula, then `Θ`. -/
theorem tensorBaseChangeAddHom_tmul [IsAffineHom h] (hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤)
    (Θ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
        ((modulePullback h'.toLRSHom.toShHom ⋙ modulePushforward h'.toLRSHom.toShHom).obj F') ⟶
      (Scheme.Modules.pushforward h).obj
        (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pullback h').obj F'))) (r : Γ(Y'', ⊤))
    (x : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', ⊤)) :
    tensorBaseChangeAddHom S F' h' f'' h hsq hle Θ (r ⊗ₜ[Γ(S.Y', ⊤), (h.appLE ⊤ ⊤ hle).hom] x) =
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F')).presheaf.map (homOfLE hle).op
        (Scheme.Modules.Hom.app
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
            (tensorGlobalSection F' ((Scheme.Modules.pullback S.f').obj
                ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')))
              (unitGlobalSection S.f' ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))
                (show Γ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''), ⊤) from
                  (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom r))) ≫
            ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
              (pushforwardPullbackTensorIsoRight S.f' h' f'' h hsq F' inferInstance).hom ≫ Θ)
          ⊤ x) := by
  have h1 := higherDirectImageTensorMap_tmul S.f' F'
    ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')) S.d ⊤ x
    (show Γ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''), ⊤) from
                  (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom r)
  have h2 := tensorTopSection_globalRestrict S.f' F'
    ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')) S.d
    (show Γ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''), ⊤) from
                  (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom r) ⊤ x
  rw [globalRestrict_top] at h2
  have h3 := h1.trans h2
  refine congrArg (fun z => (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F')).presheaf.map (homOfLE hle).op
      (Scheme.Modules.Hom.app Θ ⊤ (Scheme.Modules.Hom.app
        (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          (pushforwardPullbackTensorIsoRight S.f' h' f'' h hsq F' inferInstance).hom) ⊤ z)))
      h3 |>.trans ?_
  rfl

/-- **Conclusion (c) of [Stacks, Tag 0EX3] over affine bases, given the tail.** For `Y'` and
`Y''` affine and an isomorphism `Θ` through which the transpose of `γ⁺` factors after the higher
direct image of the unit, and which is natural in endomorphisms of `(h')^* F'`, the canonical map
`γ` is an isomorphism: `tensorBaseChangeAddHom` is a bijection with value `r • γ⁺(a)` on `r ⊗ a`.
-/
theorem isIso_topDirectImageBaseChangeMap_of_isAffine_of_tail [IsAffine S.Y'] [IsAffine Y'']
    [IsAffineHom h] [IsAffineHom h']
    (Θ : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj
        ((modulePullback h'.toLRSHom.toShHom ⋙ modulePushforward h'.toLRSHom.toShHom).obj F') ⟶
      (Scheme.Modules.pushforward h).obj
        (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
          ((Scheme.Modules.pullback h').obj F'))) [IsIso Θ]
    (hT : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h
          (toShHom_comm_of_isPullback h' f'' h hsq)) =
      ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') ≫ Θ)
    (hTnat : ∀ φ : (modulePullback h'.toLRSHom.toShHom).obj F' ⟶
        (modulePullback h'.toLRSHom.toShHom).obj F',
      ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          ((modulePushforward h'.toLRSHom.toShHom).map φ) ≫ Θ =
        Θ ≫ (Scheme.Modules.pushforward h).map
          (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).map
            (X := (Scheme.Modules.pullback h').obj F') (Y := (Scheme.Modules.pullback h').obj F')
            φ)) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h
      (toShHom_comm_of_isPullback h' f'' h hsq)) := by
  have hle : (⊤ : Y''.Opens) ≤ h ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine isIso_topDirectImageBaseChangeMap_of_isAffine_of_tensor S F' h' f'' h hsq hle
    (tensorBaseChangeAddHom S F' h' f'' h hsq hle Θ)
    (bijective_tensorBaseChangeAddHom S F' h' f'' h hsq hle Θ) (fun r x => ?_)
  refine (tensorBaseChangeAddHom_tmul S F' h' f'' h hsq hle Θ r x).trans ?_
  have s2 := tensorGlobalSection_comp_pushforwardPullbackTensorIsoRight S.f' h' f'' h hsq F'
    inferInstance r
  have M : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          (tensorGlobalSection F' ((Scheme.Modules.pullback S.f').obj
              ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y'')))
            (unitGlobalSection S.f' ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''))
              (show Γ((Scheme.Modules.pushforward h).obj (Scheme.unitModule Y''), ⊤) from
                (Y''.presheaf.map (h ⁻¹ᵁ ⊤).leTop.op).hom r))) ≫
        ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          (pushforwardPullbackTensorIsoRight S.f' h' f'' h hsq F' inferInstance).hom ≫ Θ =
      (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h
            (toShHom_comm_of_isPullback h' f'' h hsq)) ≫
        (Scheme.Modules.pushforward h).map
          (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).map
            (sectionScalar X'' (f''.appTop.hom r) ((Scheme.Modules.pullback h').obj F'))) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ Θ) (Functor.map_comp _ _ _).symm).trans ?_
    refine (congrArg (fun z => ((Scheme.Modules.pushforward S.f').rightDerivedPlus
      (S.d : ℤ)).map z ≫ Θ) s2).trans ?_
    refine (congrArg (· ≫ Θ) (Functor.map_comp _ _ _)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') ≫ ·)
      (hTnat (sectionScalar X'' (f''.appTop.hom r) ((Scheme.Modules.pullback h').obj F')))).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (· ≫ _) hT.symm
  refine (congrArg (fun z : ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F' ⟶
        (Scheme.Modules.pushforward h).obj
          (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F')) =>
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.pullback h').obj F')).presheaf.map (homOfLE hle).op
      (Scheme.Modules.Hom.app z ⊤ x)) M).trans ?_
  refine (ModuleLimits.Hom_app_presheaf_map _ hle _).trans ?_
  refine (congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ _)
    (rightDerivedPlus_pushforward_map_sectionScalar_appTop f'' S.d r
      ((Scheme.Modules.pullback h').obj F'))).trans ((sectionScalar_app_top r _ _).trans ?_)
  exact congrArg (r • ·) (Scheme.Modules.pullbackSection_homEquiv h _ _ _ ⊤ ⊤ hle x).symm

/-- **Conclusion (c) of [Stacks, Tag 0EX3] over affine bases.** For a top-degree base-change
situation with affine base `Y'`, a cartesian square
```
X₂ --a'--> X'
|b         |f'
Y₂ --a-->  Y'
```
with `Y₂` affine and a quasi-coherent module `G` on `X'`, the canonical map
`a^* R^d f'_* G ⟶ R^d b_* (a')^* G` is an isomorphism. -/
theorem isIso_topDirectImageBaseChangeMap_of_isAffine
    (T : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) [IsAffine T.Y']
    {X₂ Y₂ : Scheme.{u}} [IsAffine Y₂] (a' : X₂ ⟶ T.X') (b : X₂ ⟶ Y₂) (a : Y₂ ⟶ T.Y')
    (sq : IsPullback a' b T.f' a) (G : T.X'.Modules) [G.IsQuasicoherent] :
    IsIso (topDirectImageBaseChangeMap T G a' b a (toShHom_comm_of_isPullback a' b a sq)) := by
  have : IsAffineHom a' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance
  have : QuasiCompact b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq
      T.quasiCompact_f'
  have : QuasiSeparated b :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated) sq
      T.quasiSeparated_f'
  have := isIso_lerayTail T a' b a (toShHom_comm_of_isPullback a' b a sq) G
  exact isIso_topDirectImageBaseChangeMap_of_isAffine_of_tail T G a' b a sq _
    (homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit T G a' b a
      (toShHom_comm_of_isPullback a' b a sq))
    (lerayTail_naturality T a' b a (toShHom_comm_of_isPullback a' b a sq) G)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BoundednessTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing

/-!
# Composition of derived lower shrieks: the compactifications

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and
quasi-separated schemes. The proof of [Stacks, Tag 0F7J] chooses a compactification
`i : Y ⟶ Ȳ` of `Y` over `Z` and a compactification `X ⟶ X̄` of `X` over `Ȳ`. With
`U = X̄ ×_Ȳ Y` it reads off the diagram
```
X --j--> U --j'--> X̄
 \f      |f'       |f̄
  \----> Y --i---> Ȳ --ḡ--> Z
```
three compactifications: `j` of `X` over `Y`, `i` of `Y` over `Z` and `j' ∘ j` of `X` over `Z`.
It then identifies
```
R(g ∘ f)_! = R(ḡ ∘ f̄)_* (j' ∘ j)_! = Rḡ_* Rf̄_* j'_! j_! = Rḡ_* i_! Rf'_* j_! = Rg_! Rf_!.
```
This file constructs the compactifications, proves that `Rf_*` preserves `D⁺_tors` for a
quasi-compact quasi-separated `f`, and assembles the identification on `D⁺_tors` from the open
immersion case.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.restrictBase`: the compactification `j : X ⟶ X̄ ×_Ȳ Y`
  of `X` over `Y` induced by a compactification of `X` over `Ȳ`.
* `AlgebraicGeometry.CompactificationOf.compOver`: the compactification `j' ∘ j` of `X` over
  `Z`.
* `Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoOfBaseChange`: the isomorphism
  `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on `D⁺_tors(X_étale, Λ)` for these compactifications, given the open
  immersion case.

## Main results

* `Stacks.EtaleCohomology.isTorsionPlus_etaleModuleDerivedDirectImage_obj`: `Rf_*` carries
  `D⁺_tors` into `D⁺_tors`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- `X` is the inverse image of `Y` along `X ⟶ Ȳ`: the square with sides `𝟙 X`, `f`,
`f ≫ i` and the open immersion `i : Y ⟶ Ȳ` is cartesian. -/
theorem isPullback_id_comp_immersion :
    IsPullback (𝟙 X) f (f ≫ jg.immersion) jg.immersion := by
  have h1 : IsPullback (𝟙 X) f f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have h2 : IsPullback (𝟙 Y) (𝟙 Y) jg.immersion jg.immersion :=
    (mono_iff_isPullback jg.immersion).1 inferInstance
  simpa using h1.paste_vert h2

/-- The compactification `X ⟶ X̄ ×_Ȳ Y` of `X` over `Y` induced by a compactification
`X ⟶ X̄` of `X` over `Ȳ`, for a compactification `Y ⟶ Ȳ` of `Y`: the base change of the latter
along the open immersion `Y ⟶ Ȳ`. -/
abbrev restrictBase : CompactificationOf (Over.mk f) :=
  jX.baseChange (isPullback_id_comp_immersion jg)

/-- The open immersion `X̄ ×_Ȳ Y ⟶ X̄`. -/
abbrev restrictBaseι : (CompactificationOf.restrictBase jg jX).space ⟶ jX.space :=
  pullback.fst jX.toBase jg.immersion

/-- The morphism `X̄ ×_Ȳ Y ⟶ X̄` is an open immersion. -/
instance isOpenImmersion_restrictBaseι : IsOpenImmersion (restrictBaseι jg jX) :=
  MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ inferInstance

/-- The open immersion `X̄ ×_Ȳ Y ⟶ X̄` is étale. -/
instance etale_restrictBaseι : Etale (restrictBaseι jg jX) := inferInstance

/-- The compactification `X ⟶ X̄ ×_Ȳ Y ⟶ X̄` of `X` over `Z`, with structure morphism
`X̄ ⟶ Ȳ ⟶ Z`. -/
def compOver : CompactificationOf (Over.mk (f ≫ g)) :=
  ⟨StructuredArrow.mk (Y := Over.mk (jX.toBase ≫ jg.toBase))
      (Over.homMk (U := Over.mk (f ≫ g))
        ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX) (by
          change ((CompactificationOf.restrictBase jg jX).immersion ≫
            pullback.fst jX.toBase jg.immersion) ≫ jX.toBase ≫ jg.toBase = f ≫ g
          simp [restrictBase])),
    ⟨(inferInstance : IsOpenImmersion
        ((CompactificationOf.restrictBase jg jX).immersion ≫
          CompactificationOf.restrictBaseι jg jX)),
      (inferInstance : IsProper (jX.toBase ≫ jg.toBase))⟩⟩

/-- The space of `compOver jg jX` is `X̄`. -/
@[simp]
lemma compOver_space : (CompactificationOf.compOver jg jX).space = jX.space := rfl

/-- The immersion of `compOver jg jX` is the composite `X ⟶ X̄ ×_Ȳ Y ⟶ X̄`. -/
@[simp]
lemma compOver_immersion :
    (CompactificationOf.compOver jg jX).immersion =
      (CompactificationOf.restrictBase jg jX).immersion ≫
        CompactificationOf.restrictBaseι jg jX := rfl

/-- The structure morphism of `compOver jg jX` is the composite `X̄ ⟶ Ȳ ⟶ Z`. -/
@[simp]
lemma compOver_toBase : (CompactificationOf.compOver jg jX).toBase = jX.toBase ≫ jg.toBase := rfl

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### The derived direct image preserves torsion cohomology -/

section Torsion

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Rf_*` carries `D⁺_tors` into `D⁺_tors`** for sheaves of `Λ`-modules and a quasi-compact
quasi-separated `f` ([Stacks, Tag 0DDD] (2), module coefficients). -/
theorem isTorsionPlus_etaleModuleDerivedDirectImage_obj [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K) :
    isTorsionPlus.{u, 0} Λ Y ((etaleModuleDerivedDirectImage.{u, 0} Λ f).obj K) := by
  let Q : ObjectProperty (EtaleModules.{u, 0} Λ Y) :=
    (Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology).inverseImage
      (etaleModuleForgetAb.{u, 0} Λ Y)
  exact (Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj
    (etaleModuleDirectImage.{u, 0} Λ f) (IsTorsionEtaleModule.{u, 0} Λ X) Q
    (fun M hM p => Stacks.Torsion.torsionSheafProperty_of_iso Y.smallEtaleTopology
      (etaleModuleForgetRightDerivedDirectImageIso Λ f M p).symm
      (torsionSheafProperty_rightDerived_smallEtaleDirectImageAb.{0} f p _
        (torsionSheafProperty_etaleModuleForget_obj_of_isTorsionEtaleModule Λ X hM))) K hK).2

end Torsion

/-! ### `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` from the base change of the open immersion case -/

section Composition

variable (Λ : Type) [Ring Λ] {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` for the compactifications of the proof of [Stacks, Tag 0F7J]**,
on `D⁺_tors(X_étale, Λ)`, from the open immersion case `β` of [Stacks, Tag 0F7B]:
`Rf̄_* ∘ j'_! ≅ i_! ∘ Rf'_*` on `D⁺_tors(U_étale, Λ)`, and the preservation of torsion
cohomology by `j_!`. The chain is
`R(ḡ ∘ f̄)_* (j' ∘ j)_! ≅ Rḡ_* Rf̄_* j'_! j_! ≅ Rḡ_* i_! Rf'_* j_!`, the first isomorphism being
the composition of direct images and of extensions by zero. -/
def derivedLowerShriekCompOverIsoOfBaseChange
    (β : (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space).ι ⋙
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ (CompactificationOf.restrictBaseι jg jX) ⋙
          etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase) ≅
      (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space).ι ⋙
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase ⋙
          etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion))
    (hj : ∀ K, isTorsionPlus.{u, 0} Λ X K →
      isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion).obj K)) :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ ⋙
          derivedLowerShriek.{u, 0} g jg Λ := by
  let a := (CompactificationOf.restrictBase jg jX).immersion
  let b := CompactificationOf.restrictBaseι jg jX
  let e₁ : etaleModuleDerivedExtensionByZero.{u, 0} Λ (a ≫ b) ≅
      etaleModuleDerivedExtensionByZero.{u, 0} Λ a ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ b :=
    (Functor.rightDerivedFunctorPlusCompIsoOfExact
      (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleExtensionByZero.{u, 0} Λ b)
      (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).symm
  let e₂ := etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl
  let L := ObjectProperty.lift
    (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space)
    ((isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ a)
    (fun K => hj K.obj K.property)
  let eL : L ⋙ (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space).ι ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ a :=
    ObjectProperty.liftCompιIso _ _ _
  let ιX := (isTorsionPlus.{u, 0} Λ X).ι
  let ιU := (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space).ι
  let Ra := etaleModuleDerivedExtensionByZero.{u, 0} Λ a
  let Rb := etaleModuleDerivedExtensionByZero.{u, 0} Λ b
  let Rfb := etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase
  let Rgb := etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase
  let Rf' := etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase
  let Ri := etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion
  let s₁ : ιX ⋙ derivedLowerShriek.{u, 0} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (ιX ⋙ Ra) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) :=
    Functor.isoWhiskerLeft ιX (Functor.isoWhiskerRight e₁ _ ≪≫ Functor.isoWhiskerLeft _ e₂)
  let s₂ : (ιX ⋙ Ra) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) ≅ (L ⋙ ιU) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) :=
    Functor.isoWhiskerRight eL.symm _
  let s₃ : (L ⋙ ιU) ⋙ ((Rb ⋙ Rfb) ⋙ Rgb) ≅ (L ⋙ ιU) ⋙ ((Rf' ⋙ Ri) ⋙ Rgb) :=
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight β Rgb)
  let s₄ : (L ⋙ ιU) ⋙ ((Rf' ⋙ Ri) ⋙ Rgb) ≅ (ιX ⋙ Ra) ⋙ ((Rf' ⋙ Ri) ⋙ Rgb) :=
    Functor.isoWhiskerRight eL _
  exact s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄

end Composition

end Stacks.EtaleCohomology

end

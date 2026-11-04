module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCube
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedAdjunctionUnit

/-!
# The composition isomorphism of [Stacks, Tag 0F7J] through the open immersion

For a compactification `i : Y ⟶ Ȳ` of `g : Y ⟶ Z` and a compactification `X ⟶ X̄` of `X` over
`Ȳ`, with `U = X̄ ×_Ȳ Y`, `a : X ⟶ U`, `b : U ⟶ X̄` and `f' : U ⟶ Y`, the isomorphism
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of `Stacks.EtaleCohomology.derivedLowerShriekCompOverIso` is
`Rḡ_*` applied to an isomorphism
`Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!`,
`Rf̄_* (b ∘ a)_! ≅ Rf̄_* b_! a_! ≅ i_! Rf'_* a_!`, where `Rf_!` is computed through `a`. Restricted
to `Y` along `i`, the isomorphism `Ψ` is the base change map of `Rf̄_*` along the open immersion
`i`.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.overBar`: the compactification `b ∘ a : X ⟶ X̄` of `X`
  over `Ȳ`.
* `Stacks.EtaleCohomology.derivedLowerShriekRestrictBaseIso`: the isomorphism `Ψ`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekCompOverIso_eq`: the isomorphism of
  `derivedLowerShriekCompOverIso` through `Ψ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (jg : CompactificationOf (Over.mk g))
  (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- The compactification `X ⟶ X̄ ×_Ȳ Y ⟶ X̄` of `X` over `Ȳ`: the compactification `jX` with
its open immersion written as `b ∘ a`. -/
def overBar : CompactificationOf (Over.mk (f ≫ jg.immersion)) :=
  ⟨StructuredArrow.mk (Y := Over.mk jX.toBase)
      (Over.homMk (U := Over.mk (f ≫ jg.immersion))
        ((CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX)
        (by
          change ((CompactificationOf.restrictBase jg jX).immersion ≫
            pullback.fst jX.toBase jg.immersion) ≫ jX.toBase = f ≫ jg.immersion
          simp [restrictBase])),
    ⟨(inferInstance : IsOpenImmersion
        ((restrictBase jg jX).immersion ≫ restrictBaseι jg jX)),
      (inferInstance : IsProper jX.toBase)⟩⟩

/-- The space of `overBar jg jX` is the space `X̄` of `jX`. -/
@[simp]
lemma overBar_space : (overBar jg jX).space = jX.space := rfl

/-- The open immersion of `overBar jg jX` is the composite `b ∘ a : X ⟶ X̄ ×_Ȳ Y ⟶ X̄`. -/
@[simp]
lemma overBar_immersion : (overBar jg jX).immersion =
    (CompactificationOf.restrictBase jg jX).immersion ≫ CompactificationOf.restrictBaseι jg jX :=
  rfl

/-- The proper map of `overBar jg jX` to `Ȳ` is that of `jX`. -/
@[simp]
lemma overBar_toBase : (overBar jg jX).toBase = jX.toBase := rfl

/-- The open immersion of `overBar jg jX` is étale, being a composite of étale maps. -/
instance etale_overBar_immersion : Etale (overBar jg jX).immersion :=
  (inferInstance : Etale ((CompactificationOf.restrictBase jg jX).immersion ≫
    CompactificationOf.restrictBaseι jg jX))

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [Ring Λ]

/-! ### The open immersion case of [Stacks, Tag 0F7B] restricted to the open -/

section OpenRestriction

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

/-- **The unit of `Rj_! ⊣ Rj^{-1}`** is the inverse of the comparison
`Rj^{-1} ∘ Rj_! ≅ 𝟭`, for an open immersion `j`. -/
lemma etaleModuleDerivedExtensionByZeroAdj_unit_eq {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ j).unit =
      (etaleModuleDerivedExtensionByZeroCompRestrictionIso Λ j).inv :=
  Adjunction.rightDerivedFunctorPlus_unit_eq _

/-- The inverse of `etaleModuleDerivedDirectImageIsoRestrictionOfIsProper` at an object:
`i^{-1} Rf̄_* Rb_! K ⟶ Rf'_* b^{-1} Rb_! K ⟶ Rf'_* K`. -/
lemma etaleModuleDerivedDirectImageIsoRestrictionOfIsProper_inv_app
    (N : (isTorsionPlus.{u, 0} Λ P).FullSubcategory) :
    (etaleModuleDerivedDirectImageIsoRestrictionOfIsProper Λ fb i b f' sq).inv.app N =
      (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.app
          ((etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj
            ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj N.obj)) ≫
        (etaleModuleDerivedBaseChange.{u, 0} Λ fb f' i b sq.w.symm).app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj N.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ f').map
          ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).hom.app N.obj) := by
  simp [etaleModuleDerivedDirectImageIsoRestrictionOfIsProper]

/-- **The open immersion case of [Stacks, Tag 0F7B], restricted to the open**: the restriction
along `i` of `β : Rf̄_* Rb_! ≅ Ri_! Rf'_*`, followed by `i^{-1} Ri_! ≅ 𝟭`, is the base change map
of `Rf̄_*` along `i` followed by `b^{-1} Rb_! ≅ 𝟭`. -/
theorem etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper_restrict
    (N : (isTorsionPlus.{u, 0} Λ P).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map
        ((etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper Λ fb i b f' sq).hom.app N) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ i).hom.app
        ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj N.obj) =
    (etaleModuleDerivedBaseChange.{u, 0} Λ fb f' i b sq.w.symm).app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj N.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ f').map
        ((etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).hom.app N.obj) := by
  let M := etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper Λ fb i b f' sq
  let E := etaleModuleDerivedDirectImageIsoRestrictionOfIsProper Λ fb i b f' sq
  let adj := etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i
  have hMi : ∀ X, IsIso (M.app X) := fun X =>
    isIso_etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper_app Λ fb i b f' sq X
  have hβ : (etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper Λ fb i b f' sq).hom.app N =
      inv (M.app N) := by
    have : IsIso M := NatIso.isIso_of_isIso_app _
    show (inv M).app N = _
    exact NatIso.isIso_inv_app _ _
  have hM : M.app N = (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).map (E.hom.app N) ≫
      adj.counit.app ((etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj N.obj)) := rfl
  -- the restriction of `M` is `E` up to the unit
  have hu : adj.unit.app ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj N.obj) ≫
      (etaleModuleDerivedRestriction.{u, 0} Λ i).map (M.app N) = E.hom.app N := by
    have n := adj.unit.naturality (E.hom.app N)
    have t := adj.right_triangle_components ((etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj N.obj))
    simp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at n t
    rw [hM, Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans ((eq_whisker n.symm _).trans
      ((Category.assoc _ _ _).trans ((whisker_eq _ t).trans (Category.comp_id _))))
  have hU := congrArg (fun t => NatTrans.app t ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj
    N.obj)) (etaleModuleDerivedExtensionByZeroAdj_unit_eq Λ i)
  have hρ := (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.naturality (M.app N)
  have hD : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map (M.app N) =
      (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).inv.app _ ≫
        (etaleModuleDerivedRestriction.{u, 0} Λ i).map (M.app N) ≫
        (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).hom.app _ := by
    rw [hρ, Iso.inv_hom_id_app_assoc]
  rw [hβ, Functor.map_inv, IsIso.inv_comp_eq, hD, Category.assoc, Category.assoc]
  refine Eq.trans ?_ (whisker_eq _ (whisker_eq _
    (etaleModuleDerivedDirectImageIsoRestrictionOfIsProper_inv_app Λ fb i b f' sq N)))
  show (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).inv.app _ ≫
    (etaleModuleDerivedExtensionByZeroCompRestrictionIso Λ i).hom.app _ = _
  refine whisker_eq _ ?_
  rw [← cancel_epi (adj.unit.app ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj N.obj)),
    ← Category.assoc, hu, Iso.hom_inv_id_app]
  exact (eq_whisker hU _).trans (Iso.inv_hom_id_app _ _)

end OpenRestriction

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- **`Ψ : R(f ≫ i)_! ≅ i_! ∘ Rf_!`** on `D⁺_tors`, for `Rf_!` computed through the induced
compactification `X ⟶ X̄ ×_Ȳ Y` and `R(f ≫ i)_!` through `X ⟶ X̄ ×_Ȳ Y ⟶ X̄`: the composition of
extensions by zero followed by the open immersion case of [Stacks, Tag 0F7B]. -/
def derivedLowerShriekRestrictBaseIso :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} (f ≫ jg.immersion) (CompactificationOf.overBar jg jX) Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ ⋙
          etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion := by
  let a := (CompactificationOf.restrictBase jg jX).immersion
  let b := CompactificationOf.restrictBaseι jg jX
  let e₁ : etaleModuleDerivedExtensionByZero.{u, 0} Λ (a ≫ b) ≅
      etaleModuleDerivedExtensionByZero.{u, 0} Λ a ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ b :=
    (Functor.rightDerivedFunctorPlusCompIsoOfExact
      (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleExtensionByZero.{u, 0} Λ b)
      (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
      (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).symm
  let L := ObjectProperty.lift
    (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space)
    ((isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ a)
    (fun K => isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K.obj K.property)
  let eL : L ⋙ (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space).ι ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ a :=
    ObjectProperty.liftCompιIso _ _ _
  let β := etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper Λ jX.toBase jg.immersion b
    (CompactificationOf.restrictBase jg jX).toBase
    (IsPullback.of_hasPullback jX.toBase jg.immersion)
  let ιX := (isTorsionPlus.{u, 0} Λ X).ι
  let ιU := (isTorsionPlus.{u, 0} Λ (CompactificationOf.restrictBase jg jX).space).ι
  let Ra := etaleModuleDerivedExtensionByZero.{u, 0} Λ a
  let Rb := etaleModuleDerivedExtensionByZero.{u, 0} Λ b
  let Rfb := etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase
  let Rf' := etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase
  let Ri := etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion
  let s₁ : ιX ⋙ derivedLowerShriek.{u, 0} (f ≫ jg.immersion)
      (CompactificationOf.overBar jg jX) Λ ≅ (ιX ⋙ Ra) ⋙ (Rb ⋙ Rfb) :=
    Functor.isoWhiskerLeft ιX (Functor.isoWhiskerRight e₁ Rfb)
  let s₂ : (ιX ⋙ Ra) ⋙ (Rb ⋙ Rfb) ≅ (L ⋙ ιU) ⋙ (Rb ⋙ Rfb) :=
    Functor.isoWhiskerRight eL.symm _
  let s₃ : (L ⋙ ιU) ⋙ (Rb ⋙ Rfb) ≅ (L ⋙ ιU) ⋙ (Rf' ⋙ Ri) :=
    Functor.isoWhiskerLeft L β
  let s₄ : (L ⋙ ιU) ⋙ (Rf' ⋙ Ri) ≅ (ιX ⋙ Ra) ⋙ (Rf' ⋙ Ri) :=
    Functor.isoWhiskerRight eL _
  exact s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄

/-- The composition isomorphism `(b ∘ a)_! ≅ b_! ∘ a_!` of derived extensions by zero. -/
def derivedExtensionByZeroRestrictBaseIso :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ (CompactificationOf.overBar jg jX).immersion ≅
      Functor.comp
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ
          (CompactificationOf.restrictBase jg jX).immersion)
        (@etaleModuleDerivedExtensionByZero.{u, 0} Λ _ _ _ (CompactificationOf.restrictBaseι jg jX)
          (CompactificationOf.etale_restrictBaseι jg jX)) := by
  let a := (CompactificationOf.restrictBase jg jX).immersion
  let b := CompactificationOf.restrictBaseι jg jX
  exact (Functor.rightDerivedFunctorPlusCompIsoOfExact
    (etaleModuleExtensionByZero.{u, 0} Λ a) (etaleModuleExtensionByZero.{u, 0} Λ b)
    (etaleModuleExtensionByZero.{u, 0} Λ (a ≫ b))
    (etaleModuleExtensionByZeroCompIso.{u, 0} Λ a b).symm).symm

/-- The open immersion case of [Stacks, Tag 0F7B] used in `derivedLowerShriekRestrictBaseIso`. -/
def restrictBaseDirectImageIso :=
  etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper Λ jX.toBase jg.immersion
    (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
    (IsPullback.of_hasPullback jX.toBase jg.immersion)

/-- Composing with identity morphisms `u` and `v` at both ends of a middle factor is trivial. -/
private lemma comp_eq_of_eq_id_of_eq_id {C : Type*} [Category C] {P Q R : C} (a : P ⟶ Q)
    (u : Q ⟶ Q) (b : Q ⟶ R) (v : R ⟶ R) (hu : u = 𝟙 Q) (hv : v = 𝟙 R) :
    a ≫ u ≫ b ≫ v = a ≫ b := by
  simp [hu, hv]

/-- The components of `derivedLowerShriekRestrictBaseIso`. -/
lemma derivedLowerShriekRestrictBaseIso_hom_app (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K =
      (etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase).map
          ((derivedExtensionByZeroRestrictBaseIso Λ jg jX).hom.app K.obj) ≫
        (restrictBaseDirectImageIso Λ jg jX).hom.app
          ⟨(etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K.obj,
            isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K.obj K.property⟩ := by
  have h : (derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K =
      (etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase).map
          ((derivedExtensionByZeroRestrictBaseIso Λ jg jX).hom.app K.obj) ≫
        (etaleModuleDerivedExtensionByZero.{u, 0} Λ (CompactificationOf.restrictBaseι jg jX) ⋙
          etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase).map (𝟙 _) ≫
        (restrictBaseDirectImageIso Λ jg jX).hom.app
          ⟨(etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K.obj,
            isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K.obj K.property⟩ ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase ⋙
          etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion).map (𝟙 _) :=
    rfl
  rw [h]
  exact comp_eq_of_eq_id_of_eq_id _ _ _ _ (CategoryTheory.Functor.map_id _ _)
    (CategoryTheory.Functor.map_id _ _)

/-- `(b ∘ a)_! ⋙ b^{-1} ≅ a_!`: the composition of extensions by zero followed by
`b^{-1} b_! ≅ 𝟭` for the open immersion `b`. -/
def restrictBaseExtensionByZeroIso :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ (CompactificationOf.overBar jg jX).immersion ⋙
        etaleModuleDerivedInverseImagePlus.{u, 0} Λ (CompactificationOf.restrictBaseι jg jX) ≅
      etaleModuleDerivedExtensionByZero.{u, 0} Λ
        (CompactificationOf.restrictBase jg jX).immersion :=
  Functor.isoWhiskerRight (derivedExtensionByZeroRestrictBaseIso Λ jg jX) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ
        (CompactificationOf.restrictBaseι jg jX)) ≪≫
    Functor.rightUnitor _

/-- **`Ψ` restricted to `Y` is the base change map of `Rf̄_*` along `i`**: for `K` in
`D⁺_tors(X_étale, Λ)`, `i^{-1} Ψ` followed by `i^{-1} i_! ≅ 𝟭` is the base change map
`i^{-1} Rf̄_* (b ∘ a)_! K ⟶ Rf'_* b^{-1} (b ∘ a)_! K` followed by `Rf'_*` of
`b^{-1} (b ∘ a)_! ≅ a_!`. -/
theorem derivedLowerShriekRestrictBaseIso_restrict
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
        ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) ≫
      (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ jg.immersion).hom.app
        ((derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ).obj K.obj) =
    (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase (CompactificationOf.restrictBase jg jX).toBase
        jg.immersion (CompactificationOf.restrictBaseι jg jX)
        (IsPullback.of_hasPullback jX.toBase jg.immersion).w.symm).app
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
          (CompactificationOf.overBar jg jX).immersion).obj K.obj) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase).map
        ((restrictBaseExtensionByZeroIso Λ jg jX).hom.app K.obj) := by
  have core := etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper_restrict Λ jX.toBase
    jg.immersion (CompactificationOf.restrictBaseι jg jX)
    (CompactificationOf.restrictBase jg jX).toBase
    (IsPullback.of_hasPullback jX.toBase jg.immersion)
    ⟨(etaleModuleDerivedExtensionByZero.{u, 0} Λ
      (CompactificationOf.restrictBase jg jX).immersion).obj K.obj,
      isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K.obj K.property⟩
  have n := (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase
    (CompactificationOf.restrictBase jg jX).toBase jg.immersion
    (CompactificationOf.restrictBaseι jg jX)
    (IsPullback.of_hasPullback jX.toBase jg.immersion).w.symm).naturality
      ((derivedExtensionByZeroRestrictBaseIso Λ jg jX).hom.app K.obj)
  simp only [Functor.comp_obj] at n
  refine (eq_whisker ((congrArg (etaleModuleDerivedInverseImagePlus.{u, 0} Λ jg.immersion).map
    (derivedLowerShriekRestrictBaseIso_hom_app Λ jg jX K)).trans (Functor.map_comp _ _ _))
      _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ core).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((eq_whisker n _).trans ?_)
  refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
  refine (Functor.map_comp (etaleModuleDerivedDirectImage.{u, 0} Λ
    (CompactificationOf.restrictBase jg jX).toBase) _ _).symm.trans (congrArg _ ?_)
  simp only [restrictBaseExtensionByZeroIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  exact whisker_eq _ (Category.comp_id _).symm

/-- **The isomorphism of [Stacks, Tag 0F7J] through `Ψ`**: the components of
`Stacks.EtaleCohomology.derivedLowerShriekCompOverIso` are the composition isomorphism
`R(f̄ ≫ ḡ)_* ≅ Rf̄_* ⋙ Rḡ_*` followed by `Rḡ_*` of `Ψ`. -/
theorem derivedLowerShriekCompOverIso_hom_app (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K =
      (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase (jX.toBase ≫ jg.toBase)
          rfl).hom.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (CompactificationOf.overBar jg jX).immersion).obj K.obj) ≫
        (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
          ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K) := by
  have hCO : (derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K =
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (jX.toBase ≫ jg.toBase)).map
          ((derivedExtensionByZeroRestrictBaseIso Λ jg jX).hom.app K.obj) ≫
        (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase (jX.toBase ≫ jg.toBase)
          rfl).hom.app ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBaseι jg jX)).obj
              ((etaleModuleDerivedExtensionByZero.{u, 0} Λ
                (CompactificationOf.restrictBase jg jX).immersion).obj K.obj))) ≫
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ (CompactificationOf.restrictBaseι jg jX) ⋙
          etaleModuleDerivedDirectImage.{u, 0} Λ jX.toBase) ⋙
          etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map (𝟙 _) ≫
      (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map
        ((restrictBaseDirectImageIso Λ jg jX).hom.app
          ⟨(etaleModuleDerivedExtensionByZero.{u, 0} Λ
            (CompactificationOf.restrictBase jg jX).immersion).obj K.obj,
            isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K.obj K.property⟩) ≫
      ((etaleModuleDerivedDirectImage.{u, 0} Λ (CompactificationOf.restrictBase jg jX).toBase ⋙
          etaleModuleDerivedExtensionByZero.{u, 0} Λ jg.immersion) ⋙
          etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase).map (𝟙 _) := rfl
  have n := (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase
    (jX.toBase ≫ jg.toBase) rfl).hom.naturality
      ((derivedExtensionByZeroRestrictBaseIso Λ jg jX).hom.app K.obj)
  rw [hCO, derivedLowerShriekRestrictBaseIso_hom_app]
  refine (eq_whisker n _).trans ?_
  refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
  refine Eq.trans ?_
    (Functor.map_comp (etaleModuleDerivedDirectImage.{u, 0} Λ jg.toBase) _ _).symm
  exact comp_eq_of_eq_id_of_eq_id _ _ _ _ (CategoryTheory.Functor.map_id _ _)
    (CategoryTheory.Functor.map_id _ _)

end Stacks.EtaleCohomology

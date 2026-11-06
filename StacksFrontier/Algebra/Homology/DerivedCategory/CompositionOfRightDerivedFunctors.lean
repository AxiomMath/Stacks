module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition of right derived functors

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜` and
`ℬ` having enough injectives, so that the right derived functors `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`,
`RG : D⁺(ℬ) ⥤ D⁺(𝒞)` and `R(G ∘ F) : D⁺(𝒜) ⥤ D⁺(𝒞)` are everywhere defined. As `R(G ∘ F)` is
the right derived functor of `K⁺(𝒜) ⥤ D⁺(𝒞)` along the localization `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)` at
the quasi-isomorphisms, there is exactly one transformation

`t : R(G ∘ F) ⟶ RG ∘ RF`

whose composite with the unit of `R(G ∘ F)` is the transformation
`G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))` assembled from the units of `RG` and of `RF`; it is the
canonical map of [Stacks, Tag 05T2], and it need not be an isomorphism. It is one precisely when
`F` carries the injective objects of `𝒜` to objects that are right acyclic for `G`.

## Main definitions

* `CategoryTheory.Functor.rightComparisonUnit`: the transformation
  `G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))` of functors `K⁺(𝒜) ⥤ D⁺(𝒞)` through which the canonical
  map `t` factors.

## Main results

* `CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective`: the canonical transformation
  `t : R(G ∘ F) ⟶ RG ∘ RF`, characterised by that factorization through the unit of
  `R(G ∘ F)`, is an isomorphism if and only if `F(I)` is right acyclic for `G` for every
  injective object `I` of `𝒜`.
* `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`: Leray's
  acyclicity lemma, that a bounded below complex of objects right acyclic for `G` computes `RG`.

## References

* [Stacks, Tag 015M]
* [Stacks, Tag 015E], Leray's acyclicity lemma
* [Stacks, Tag 0157], right acyclic objects
* [Stacks, Tag 05T2], the comparison transformation
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]

section

variable {C₁ : Type*} {C₂ : Type*} [Category* C₁] [Category* C₂]
  [Preadditive C₁] [Preadditive C₂] [HasZeroObject C₁] [HasZeroObject C₂]
  [HasBinaryBiproducts C₁] [HasBinaryBiproducts C₂] (Φ : C₁ ⥤ C₂) [Φ.Additive]

/-- The single complex on an object `X`, placed in degree `n`, is sent by an additive functor
`Φ` to the single complex on `Φ(X)` in degree `n`. -/
private noncomputable def mapHomotopyCategoryPlusObjSingleIso (n : ℤ) (X : C₁) :
    Φ.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C₁ n).obj X) ≅
      (HomotopyCategory.Plus.singleFunctor C₂ n).obj (Φ.obj X) :=
  (HomotopyCategory.Plus.ι C₂).preimageIso
    ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) n).app X))

end

omit [HasDerivedCategory.{w} C] in
/-- Every term of the single complex on an injective object is injective. -/
private lemma injective_single_obj_as_X (n : ℤ) (I : C) [Injective I] (m : ℤ) :
    Injective (((HomotopyCategory.Plus.singleFunctor C n).obj I).obj.as.X m) := by
  rcases eq_or_ne m n with rfl | hm
  · exact Injective.of_iso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m I).symm inferInstance
  · exact Injective.of_iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n I m hm).isoZero.symm
      inferInstance

section

variable {H : Type*} [Category* H] [EnoughInjectives C]

/-- A transformation `t : RΨ ⟶ R` out of a right derived functor of `Ψ : K⁺(𝒜) ⥤ ℋ` along the
localization `Qh : K⁺(𝒜) ⥤ D⁺(𝒜)` at the quasi-isomorphisms is invertible if and only if the
transformation `β : Ψ ⟶ Qh ⋙ R` it is factored from by the unit `α` of `RΨ` is invertible at
every bounded below complex of injective objects of `𝒜`. -/
private theorem isIso_iff_forall_isIso_app {Ψ : HomotopyCategory.Plus C ⥤ H}
    {RΨ R : DerivedCategory.Plus C ⥤ H} (α : Ψ ⟶ DerivedCategory.Plus.Qh ⋙ RΨ)
    [RΨ.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]
    {β : Ψ ⟶ DerivedCategory.Plus.Qh ⋙ R} (t : RΨ ⟶ R)
    (ht : α ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh t = β) :
    IsIso t ↔ ∀ K : HomotopyCategory.Plus C,
      (∀ n : ℤ, Injective (K.obj.as.X n)) → IsIso (β.app K) := by
  refine ⟨fun _ K hK => ?_, fun h => ?_⟩
  · rw [← ht, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · rw [show t = RΨ.rightDerivedDesc α (HomotopyCategory.Plus.quasiIso C) R β from
        RΨ.rightDerived_ext α (HomotopyCategory.Plus.quasiIso C) R _ _
          (by rw [ht, Functor.rightDerived_fac]),
      ← Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc,
      (HomotopyCategory.Plus.localizerMorphism_derives Ψ).isRightDerivedFunctor_iff_isIso β]
    exact fun X => h _ fun n => inferInstance

end

/-- The unit of `RG` (Mathlib's `rightDerivedFunctorPlusUnith`, whose definition is not exposed)
is invertible at `K` exactly when the unit of `Functor.totalRightDerived` is: both are units of
right derived functors of the same functor. -/
private lemma isIso_rightDerivedFunctorPlusUnith_app_iff (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (K : HomotopyCategory.Plus D) :
    IsIso (G.rightDerivedFunctorPlusUnith.app K) ↔
      IsIso (((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)).app K) := by
  have : IsIso (G.rightDerivedFunctorPlus.rightDerivedDesc G.rightDerivedFunctorPlusUnith
      (HomotopyCategory.Plus.quasiIso D) _
      ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D))) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 inferInstance
  rw [← Functor.rightDerived_fac_app G.rightDerivedFunctorPlus G.rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso D) _
    ((G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso D)) K]
  exact (isIso_comp_right_iff _ _).symm

/-- Leray's acyclicity lemma: if every term of a bounded below complex `K` of objects of `ℬ` is
right acyclic for the additive functor `G`, then `K` computes `RG`, i.e. the canonical map
`G(K) ⟶ RG(K)` is an isomorphism. -/
@[sga "4 V 0.4" "more general", sga "4 XVII 1.2.7" "Adaptation clause for RF"]
public theorem isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (K : HomotopyCategory.Plus D)
    (hK : ∀ n : ℤ, G.rightAcyclic (K.obj.as.X n)) :
    IsIso (G.rightDerivedFunctorPlusUnith.app K) := by
  rw [isIso_rightDerivedFunctorPlusUnith_app_iff]
  exact Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic G K.obj.as
    ((HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.2) hK

/-- An object of `ℬ` is right acyclic for `G` exactly when the unit of `RG` is invertible at the
single complex on it in degree zero. -/
private lemma rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnit_app (G : D ⥤ E) [G.Additive]
    [EnoughInjectives D] (A : D) :
    G.rightAcyclic A ↔ IsIso (G.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.singleFunctor D 0).obj A)) := by
  rw [isIso_rightDerivedFunctorPlusUnith_app_iff]
  rfl

/-- The comparison transformation `G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))` of functors
`K⁺(𝒜) ⥤ D⁺(𝒞)`, assembled from the units of `RG` and of `RF`, preceded by the identification of
the functor induced by `G ∘ F` on `K⁺` with the composite of those induced by `F` and `G`. -/
public noncomputable def rightComparisonUnit (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [EnoughInjectives C] [EnoughInjectives D] :
    (F ⋙ G).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus

/-- The component of the comparison transformation at a bounded below complex `K`. -/
public lemma rightComparisonUnit_app (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [EnoughInjectives C] [EnoughInjectives D]
    (K : HomotopyCategory.Plus C) :
    (rightComparisonUnit F G).app K =
      DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app K) ≫
        G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K) ≫
        G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K) :=
  rfl

/-- The comparison transformation is invertible at a bounded below complex `K` of injective
objects of `𝒜` if and only if the unit of `RG` is invertible at `F(K)`. -/
private theorem isIso_app_iff_isIso_rightDerivedFunctorPlusUnit_app (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [EnoughInjectives C] [EnoughInjectives D]
    (K : HomotopyCategory.Plus C) (hK : ∀ n : ℤ, Injective (K.obj.as.X n)) :
    IsIso ((rightComparisonUnit F G).app K) ↔
      IsIso (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj K)) := by
  rw [rightComparisonUnit_app, isIso_comp_left_iff, isIso_comp_right_iff]

/-- The comparison transformation is invertible at the single complex on an injective object
`I` of `𝒜` in degree zero if and only if `F(I)` is right acyclic for `G`. -/
private theorem isIso_app_singleFunctor_obj_iff_rightAcyclic (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [EnoughInjectives C] [EnoughInjectives D] (I : C) [Injective I] :
    IsIso ((rightComparisonUnit F G).app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj I)) ↔ G.rightAcyclic (F.obj I) := by
  rw [isIso_app_iff_isIso_rightDerivedFunctorPlusUnit_app F G _ (injective_single_obj_as_X 0 I),
    NatTrans.isIso_app_iff_of_iso G.rightDerivedFunctorPlusUnith
      (mapHomotopyCategoryPlusObjSingleIso F 0 I),
    rightAcyclic_iff_isIso_rightDerivedFunctorPlusUnit_app]

/-- Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ 𝒞` be additive functors between abelian categories, with `𝒜`
and `ℬ` having enough injectives. The canonical transformation `t : R(G ∘ F) ⟶ RG ∘ RF` of
functors `D⁺(𝒜) ⥤ D⁺(𝒞)`, namely the unique one whose composite with the unit of `R(G ∘ F)` is
the transformation `G(F(K)) ⟶ RG(F(K)) ⟶ RG(RF(K))` built from the units of `RG` and of `RF`
(the hypothesis `ht`), is an isomorphism if and only if `F(I)` is right acyclic for `G` for every
injective object `I` of `𝒜`. -/
@[stacks 015M, sga "4½ Etat_0 4.3.1" "enough injectives"]
public theorem isIso_iff_rightAcyclic_obj_injective (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [EnoughInjectives C] [EnoughInjectives D]
    (t : (F ⋙ G).rightDerivedFunctorPlus ⟶
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
    (ht : (F ⋙ G).rightDerivedFunctorPlusUnith ≫ whiskerLeft DerivedCategory.Plus.Qh t =
      whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv
          DerivedCategory.Plus.Qh ≫
        whiskerLeft F.mapHomotopyCategoryPlus G.rightDerivedFunctorPlusUnith ≫
        whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus) :
    IsIso t ↔ ∀ I : C, Injective I → G.rightAcyclic (F.obj I) :=
  (isIso_iff_forall_isIso_app (β := rightComparisonUnit F G)
    (F ⋙ G).rightDerivedFunctorPlusUnith t ht).trans
    ⟨fun h I _ ↦ (isIso_app_singleFunctor_obj_iff_rightAcyclic F G I).1
      (h _ (injective_single_obj_as_X 0 I)),
    fun h K hK ↦ (isIso_app_iff_isIso_rightDerivedFunctorPlusUnit_app F G K hK).2
      (isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic G _ fun n ↦ h _ (hK n))⟩

end CategoryTheory.Functor

end

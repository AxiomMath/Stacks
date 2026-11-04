module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Raising the universe of the sections by an arbitrary amount

Raising the universe of the sections of a sheaf of modules carries a global presentation in the
sense of Stacks 03DE(6), and hence quasi-coherence in the sense of Stacks 03DL(6), upwards by an
*arbitrary* amount. To that end it shows that raising the universe of the sections of a sheaf of
modules preserves colimits.

## Main definitions

* `SheafOfModules.uliftForPresentationFunctor`: raising the universe of the sections of a sheaf
  of modules, as a functor.
* `PresheafOfModules.sheafificationUliftObjNatIso`:
  `PresheafOfModules.sheafificationUliftObjIso` as an isomorphism of functors.

## Main results

* `ModuleCat.preservesColimitsOfSize_uliftFunctor` and
  `PresheafOfModules.preservesColimitsOfSize_ulift`,
  `PresheafOfModules.preservesFiniteColimits_ulift`: raising the universe of the sections of a
  module, resp. of a presheaf of modules, preserves colimits.
* `SheafOfModules.preservesColimitsOfSize_uliftForPresentationFunctor` and
  `SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor`: **raising the universe of
  the sections of a sheaf of modules preserves colimits.**
* `CategoryTheory.Limits.isColimit_cofan_ulift`: a coproduct of copies of an object stays one
  after the index type is replaced by its universe lift.
* `SheafOfModules.hasGlobalPresentation_uliftForPresentation'` and
  `SheafOfModules.isQuasicoherentOnSite_uliftForPresentation'`: **a global presentation, resp.
  quasi-coherence, of a sheaf of modules is one of the universe lift of its sections, by an
  arbitrary amount.**

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m t ku kv

namespace CategoryTheory.Limits

/-- A coproduct of copies of a fixed object stays a coproduct after the index type is replaced
by its universe lift. -/
noncomputable def isColimit_cofan_ulift {D : Type u} [Category.{v} D] {I : Type*} {O Z : D}
    (f : I → (O ⟶ Z)) (h : IsColimit (Cofan.mk Z f)) :
    IsColimit (Cofan.mk Z (fun j : ULift.{t} I ↦ f j.down)) := by
  refine Cofan.IsColimit.mk _
    (fun s ↦ Cofan.IsColimit.desc h (fun i ↦ s.inj (ULift.up i))) (fun s j ↦ ?_)
    (fun s n hn ↦ Cofan.IsColimit.hom_ext h _ _ (fun i ↦ ?_))
  · obtain ⟨i⟩ := j
    exact Cofan.IsColimit.fac h (fun i ↦ s.inj (ULift.up i)) i
  · rw [Cofan.IsColimit.fac h (fun i ↦ s.inj (ULift.up i)) i]
    exact hn (ULift.up i)

end CategoryTheory.Limits

namespace ModuleCat

/-- **Raising the universe of a module preserves colimits.** -/
theorem preservesColimitsOfSize_uliftFunctor (A : Type r) [Ring A] :
    PreservesColimitsOfSize.{max r m, max r m} (uliftFunctor.{t, max r m} A) :=
  let e : uliftFunctor.{t, max r m} A ⋙
        forget₂ (ModuleCat.{max r m t} A) AddCommGrpCat.{max r m t} ≅
      forget₂ (ModuleCat.{max r m} A) AddCommGrpCat.{max r m} ⋙
        AddCommGrpCat.uliftFunctor.{t, max r m} := Iso.refl _
  let _hp : PreservesColimitsOfSize.{max r m, max r m}
      (uliftFunctor.{t, max r m} A ⋙
        forget₂ (ModuleCat.{max r m t} A) AddCommGrpCat.{max r m t}) :=
    preservesColimits_of_natIso e.symm
  let _hr : ReflectsColimitsOfSize.{max r m, max r m}
      (forget₂ (ModuleCat.{max r m t} A) AddCommGrpCat.{max r m t}) :=
    { reflectsColimitsOfShape := fun {_} _ ↦ inferInstance }
  preservesColimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{max r m t} A) AddCommGrpCat.{max r m t})

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R₀ : Cᵒᵖ ⥤ RingCat.{r}}

/-- The universe lift of presheaves of modules preserves the colimits of a shape if it does so
sectionwise. -/
private theorem preservesColimitsOfShape_ulift_of_forall {K : Type ku} [Category.{kv} K]
    [HasColimitsOfShape K (PresheafOfModules.{max r m} R₀)]
    (h : ∀ X, PreservesColimitsOfShape K
      (evaluation.{max r m, v, u, r} R₀ X ⋙ ModuleCat.uliftFunctor.{t, max r m} (R₀.obj X))) :
    PreservesColimitsOfShape K (ulift.{t, max r m, v, u, r} (R₀ := R₀)) where
  preservesColimit := fun {F} ↦ by
    refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F) ?_
    refine evaluationJointlyReflectsColimits _ _ (fun X ↦ ?_)
    exact isColimitOfPreserves (evaluation.{max r m, v, u, r} R₀ X ⋙
      ModuleCat.uliftFunctor.{t, max r m} (R₀.obj X)) (colimit.isColimit F)

/-- **Raising the universe of the sections of a presheaf of modules preserves colimits** over
shapes contained in the universe of the sections. -/
theorem preservesColimitsOfSize_ulift :
    PreservesColimitsOfSize.{max r m, max r m} (ulift.{t, max r m, v, u, r} (R₀ := R₀)) where
  preservesColimitsOfShape {_} _ :=
    preservesColimitsOfShape_ulift_of_forall fun X ↦
      have := ModuleCat.preservesColimitsOfSize_uliftFunctor.{r, m, t} (R₀.obj X)
      inferInstance

/-- Raising the universe of the sections of a presheaf of modules preserves finite colimits. -/
theorem preservesFiniteColimits_ulift :
    PreservesFiniteColimits (ulift.{t, max r m, v, u, r} (R₀ := R₀)) where
  preservesFiniteColimits _ _ _ :=
    preservesColimitsOfShape_ulift_of_forall fun X ↦
      have := ModuleCat.preservesColimitsOfSize_uliftFunctor.{r, m, t} (R₀.obj X)
      inferInstance

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- Raising the universe of the sections of a sheaf of modules, as a functor; its action on
morphisms is `SheafOfModules.uliftForPresentationMap`. -/
noncomputable def uliftForPresentationFunctor :
    SheafOfModules.{m} R ⥤ SheafOfModules.{max t m} R where
  obj M := uliftForPresentation.{u, v, r, m, t} M
  map f := uliftForPresentationMap.{u, v, r, m, t} f
  map_id _ := uliftForPresentationMap_id _
  map_comp _ _ := uliftForPresentationMap_comp _ _

/-- Raising the universe of the sections preserves zero morphisms. -/
instance preservesZeroMorphisms_uliftForPresentationFunctor :
    (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext _ _
    exact ULift.ext _ _ rfl

end SheafOfModules

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{r}}

section

variable {R₀ : Cᵒᵖ ⥤ RingCat.{r}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}]
  [HasWeakSheafify J AddCommGrpCat.{max t m}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max t m}]
  [HasWeakSheafify J AddCommGrpCat.{max t m}] in
/-- The universe lift of the sheafification unit of a presheaf of modules is natural in the
presheaf. -/
theorem uliftSheafificationUnit_naturality {M N : PresheafOfModules.{m} R₀} (φ : M ⟶ N) :
    ulift.{t}.map φ ≫ uliftSheafificationUnit.{u, v, r, m, t} α N =
      uliftSheafificationUnit.{u, v, r, m, t} α M ≫
        (SheafOfModules.forget R ⋙ restrictScalars α).map
          (SheafOfModules.uliftForPresentationFunctor.{u, v, r, m, t}.map
            ((sheafification.{m} α).map φ)) :=
  Eq.trans (Eq.symm (ulift.{t}.map_comp φ ((sheafificationAdjunction.{m} α).unit.app N)))
    (Eq.trans (congrArg ulift.{t}.map ((sheafificationAdjunction.{m} α).unit.naturality φ))
      (ulift.{t}.map_comp _ _))

/-- **Raising the universe of the sections commutes with sheafification of presheaves of
modules, naturally in the presheaf.**  This is `PresheafOfModules.sheafificationUliftObjIso`
promoted to an isomorphism of functors. -/
noncomputable def sheafificationUliftObjNatIso :
    ulift.{t} ⋙ sheafification.{max t m} α ≅
      sheafification.{m} α ⋙ SheafOfModules.uliftForPresentationFunctor.{u, v, r, m, t} :=
  NatIso.ofComponents (fun M ↦ sheafificationUliftObjIso.{u, v, r, m, t} α M) (by
    intro M N φ
    have h : (sheafification.{max t m} α).map (ulift.{t}.map φ) ≫
          (sheafification.{max t m} α).map (uliftSheafificationUnit.{u, v, r, m, t} α N) =
        (sheafification.{max t m} α).map (uliftSheafificationUnit.{u, v, r, m, t} α M) ≫
          (sheafification.{max t m} α).map
            ((SheafOfModules.forget R ⋙ restrictScalars α).map
              (SheafOfModules.uliftForPresentationFunctor.{u, v, r, m, t}.map
                ((sheafification.{m} α).map φ))) :=
      Eq.trans (Eq.symm ((sheafification.{max t m} α).map_comp _ _))
        (Eq.trans (congrArg (sheafification.{max t m} α).map
          (uliftSheafificationUnit_naturality α φ))
          ((sheafification.{max t m} α).map_comp _ _))
    change (sheafification.{max t m} α).map (ulift.{t}.map φ) ≫
        ((sheafification.{max t m} α).map (uliftSheafificationUnit.{u, v, r, m, t} α N) ≫
          (sheafificationAdjunction.{max t m} α).counit.app _) =
      ((sheafification.{max t m} α).map (uliftSheafificationUnit.{u, v, r, m, t} α M) ≫
          (sheafificationAdjunction.{max t m} α).counit.app _) ≫
        SheafOfModules.uliftForPresentationFunctor.{u, v, r, m, t}.map
          ((sheafification.{m} α).map φ)
    rw [← Category.assoc, h]
    exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun g ↦ (sheafification.{max t m} α).map
            (uliftSheafificationUnit.{u, v, r, m, t} α M) ≫ g)
          ((sheafificationAdjunction.{max t m} α).counit.naturality
            (SheafOfModules.uliftForPresentationFunctor.{u, v, r, m, t}.map
              ((sheafification.{m} α).map φ))))
        (Category.assoc _ _ _).symm))

end

/-- **Raising the universe of the sections of a sheaf of modules preserves colimits** over any
shape for which the presheaves of modules below it have colimits and the universe lift of
presheaves of modules preserves them. -/
theorem preservesColimitsOfShape_uliftForPresentationFunctor
    {R₀ : Cᵒᵖ ⥤ RingCat.{r}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
    [HasWeakSheafify J AddCommGrpCat.{max r m}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max r m t}]
    [HasWeakSheafify J AddCommGrpCat.{max r m t}] (K : Type ku) [Category.{kv} K]
    [HasColimitsOfShape K (PresheafOfModules.{max r m} R₀)]
    [PreservesColimitsOfShape K (ulift.{t, max r m, v, u, r} (R₀ := R₀))] :
    PreservesColimitsOfShape K
      (SheafOfModules.uliftForPresentationFunctor.{u, v, r, max r m, t} (R := R)) where
  preservesColimit {D} := by
    have _ : PreservesColimitsOfShape K (sheafification.{max r m} α) :=
      ((sheafificationAdjunction.{max r m}
        α).leftAdjoint_preservesColimits).preservesColimitsOfShape
    have _ : PreservesColimitsOfShape K (sheafification.{max r m t} α) :=
      ((sheafificationAdjunction.{max r m t}
        α).leftAdjoint_preservesColimits).preservesColimitsOfShape
    have e : (D ⋙ (SheafOfModules.forget R ⋙ restrictScalars α)) ⋙
        sheafification.{max r m} α ≅ D :=
      Functor.isoWhiskerLeft D (asIso (sheafificationAdjunction.{max r m} α).counit) ≪≫
        D.rightUnitor
    have _ : PreservesColimit (D ⋙ (SheafOfModules.forget R ⋙ restrictScalars α))
        (sheafification.{max r m} α ⋙
          SheafOfModules.uliftForPresentationFunctor.{u, v, r, max r m, t}) :=
      preservesColimit_of_natIso _ (sheafificationUliftObjNatIso.{u, v, r, max r m, t} α)
    have _ : PreservesColimit
        ((D ⋙ (SheafOfModules.forget R ⋙ restrictScalars α)) ⋙ sheafification.{max r m} α)
        (SheafOfModules.uliftForPresentationFunctor.{u, v, r, max r m, t} (R := R)) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves (sheafification.{max r m} α)
          (colimit.isColimit (D ⋙ (SheafOfModules.forget R ⋙ restrictScalars α))))
        (isColimitOfPreserves (sheafification.{max r m} α ⋙
          SheafOfModules.uliftForPresentationFunctor.{u, v, r, max r m, t})
          (colimit.isColimit (D ⋙ (SheafOfModules.forget R ⋙ restrictScalars α))))
    exact preservesColimit_of_iso_diagram _ e

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The identity of the underlying presheaf of a sheaf of rings is locally injective. -/
theorem isLocallyInjective_id_structure :
    Presheaf.IsLocallyInjective J (𝟙 R.obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h ↦ h

/-- The identity of the underlying presheaf of a sheaf of rings is locally surjective. -/
theorem isLocallySurjective_id_structure :
    Presheaf.IsLocallySurjective J (𝟙 R.obj) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ x ↦ ⟨x, rfl⟩

section

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max r m}]
  [HasWeakSheafify J AddCommGrpCat.{max r m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max r m t}]
  [HasWeakSheafify J AddCommGrpCat.{max r m t}]

/-- Raising the universe of the sections of a sheaf of modules preserves the colimits of a shape
if the universe lift of its structure presheaf of modules does. -/
private theorem preservesColimitsOfShape_uliftForPresentationFunctor_of_structure
    {K : Type ku} [Category.{kv} K] [HasColimitsOfShape K (PresheafOfModules.{max r m} R.obj)]
    [PreservesColimitsOfShape K
      (PresheafOfModules.ulift.{t, max r m, v, u, r} (R₀ := R.obj))] :
    PreservesColimitsOfShape K
      (uliftForPresentationFunctor.{u, v, r, max r m, t} (R := R)) :=
  have := isLocallyInjective_id_structure.{u, v, r} (R := R)
  have := isLocallySurjective_id_structure.{u, v, r} (R := R)
  PresheafOfModules.preservesColimitsOfShape_uliftForPresentationFunctor.{u, v, r, m, t,
    ku, kv} (R := R) (𝟙 R.obj) K

/-- **Raising the universe of the sections of a sheaf of modules preserves colimits** over
shapes contained in the universe of the sections. -/
theorem preservesColimitsOfSize_uliftForPresentationFunctor :
    PreservesColimitsOfSize.{max r m, max r m}
      (uliftForPresentationFunctor.{u, v, r, max r m, t} (R := R)) where
  preservesColimitsOfShape {K} _ :=
    have _ : PreservesColimitsOfShape K
        (PresheafOfModules.ulift.{t, max r m, v, u, r} (R₀ := R.obj)) :=
      (PresheafOfModules.preservesColimitsOfSize_ulift
        (R₀ := R.obj)).preservesColimitsOfShape
    preservesColimitsOfShape_uliftForPresentationFunctor_of_structure.{u, v, r, m, t,
      max r m, max r m}

/-- Raising the universe of the sections of a sheaf of modules preserves finite colimits. -/
theorem preservesFiniteColimits_uliftForPresentationFunctor :
    PreservesFiniteColimits (uliftForPresentationFunctor.{u, v, r, max r m, t} (R := R)) where
  preservesFiniteColimits K _ _ :=
    have _ : PreservesColimitsOfShape K
        (PresheafOfModules.ulift.{t, max r m, v, u, r} (R₀ := R.obj)) :=
      (PresheafOfModules.preservesFiniteColimits_ulift
        (R₀ := R.obj)).preservesFiniteColimits K
    preservesColimitsOfShape_uliftForPresentationFunctor_of_structure.{u, v, r, m, t, 0, 0}

end

/-- **A global presentation of a sheaf of modules is one of the universe lift of its sections, by
an arbitrary amount.**  At the amount `max u v r` this is
`SheafOfModules.hasGlobalPresentation_uliftForPresentation`. -/
theorem hasGlobalPresentation_uliftForPresentation' {M : SheafOfModules.{m} R}
    (h : M.HasGlobalPresentation) :
    (uliftForPresentation.{u, v, r, m, t} M).HasGlobalPresentation := by
  obtain ⟨I, K, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := h
  have hs₁ : HasSheafify J AddCommGrpCat.{max u v r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, u} J
  have hw₁ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m, u, v} J
  have hs₂ : HasSheafify J AddCommGrpCat.{max u v r t m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r t m, v, u} J
  have hw₂ : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r t m, u, v} J
  have _ : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R)) :=
    preservesColimitsOfSize_uliftForPresentationFunctor.{u, v, r, max u v m, t}
  have _ : PreservesFiniteColimits
      (uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R)) :=
    preservesFiniteColimits_uliftForPresentationFunctor.{u, v, r, max u v m, t}
  let Φ := uliftForPresentationFunctor.{u, v, r, max u v r m, t} (R := R)
  let γ : Φ.obj (uliftForPresentation.{u, v, r, r, max u v m} (unit R)) ≅
      uliftForPresentation.{u, v, r, r, max u v t m} (unit R) :=
    uliftForPresentationCompIso.{u, v, r, r, max u v m, t} (unit R)
  let δ : Φ.obj (uliftForPresentation.{u, v, r, m, max u v r} M) ≅
      uliftForPresentation.{u, v, r, max t m, max u v r}
        (uliftForPresentation.{u, v, r, m, t} M) :=
    uliftForPresentationCompIso.{u, v, r, m, max u v r, t} M ≪≫
      (uliftForPresentationCompIso.{u, v, r, m, t, max u v r} M).symm
  refine ⟨ULift.{t} I, ULift.{t} K, Φ.obj P, Φ.obj Q,
    fun j ↦ γ.inv ≫ Φ.map (ι j.down), fun j ↦ γ.inv ≫ Φ.map (κ j.down),
    ⟨isColimit_cofan_ulift _ (isColimit_cofan_comp_iso γ.symm _
      (isColimitCofanMkObjOfIsColimit Φ _ ι hP))⟩,
    ⟨isColimit_cofan_ulift _ (isColimit_cofan_comp_iso γ.symm _
      (isColimitCofanMkObjOfIsColimit Φ _ κ hQ))⟩,
    Φ.map a, Φ.map b ≫ δ.hom, ?_, ⟨?_⟩⟩
  · rw [← Category.assoc, ← Φ.map_comp, hab, Functor.map_zero, zero_comp]
  · exact (isColimitCoforkMapOfIsColimit' Φ hab hb).ofIsoColimit (Cofork.ext δ rfl)

/-- **Quasi-coherence of a sheaf of modules is quasi-coherence of the universe lift of its
sections, by an arbitrary amount.** -/
theorem isQuasicoherentOnSite_uliftForPresentation' {M : SheafOfModules.{m} R}
    (h : M.IsQuasicoherentOnSite) :
    (uliftForPresentation.{u, v, r, m, t} M).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcover, hpres⟩ := h.locally_hasGlobalPresentation U
    exact ⟨I, V, f, hcover,
      fun i ↦ hasGlobalPresentation_uliftForPresentation'.{max u v, v, r, m, t} (hpres i)⟩

end SheafOfModules

end

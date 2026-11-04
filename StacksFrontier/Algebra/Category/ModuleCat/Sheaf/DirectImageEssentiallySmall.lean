module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfLe
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image of sheaves of modules from an essentially small site

Let `f : C ⥤ D` be a functor which is continuous and cocontinuous for topologies `J` on `C` and
`K` on `D`, let `O` be a sheaf of rings on `D`, and let `T` be a sheaf of rings on `C` whose
underlying presheaf is `f.op ⋙ O`. The inverse image of sheaves of modules is restriction along
`f`, and its right adjoint, the direct image `f_*`, sends a `T`-module `M` to the `O`-module whose
sections over `y` are the compatible families of sections of `M` over the arrows `y ⟶ f x`: the
right Kan extension along `f.op`.

`SheafOfModules.directImage` constructs it with module sections in a universe containing the
*objects* of `C`. When `C` is essentially small relative to the universe `u` of the morphisms of
both sites, this file constructs the direct image with sections in `u`.

## Main definitions

* `SheafOfModules.directImageSmall`: the direct image `f_*`, as restriction to the small model
  followed by `SheafOfModules.directImage`.
* `SheafOfModules.inverseImageOfObjEq`: the inverse image `f⁻¹`, restriction along `f`.

## Main results

* `SheafOfModules.inverseImageDirectImageSmallAdjunction`: `f⁻¹ ⊣ f_*`.
* `SheafOfModules.additive_directImageSmall`: `f_*` is additive.
* `SheafOfModules.directImageSmallCompComparisonIso`: `f_*` does not see the topologies: for
  coarser topologies `J₁ ≤ J₂` and `K₁ ≤ K₂` for which `f` is still continuous and cocontinuous,
  reading modules for the coarser topologies commutes with the direct images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe r u v₁ v₂

namespace SheafOfModules

variable {C : Type v₁} [Category.{u} C] [EssentiallySmall.{u} C] {D : Type v₂} [Category.{u} D]
  (f : C ⥤ D)

/-- The small model of an essentially small site is a dense subsite of it. -/
theorem isDenseSubsite_smallModel (J : GrothendieckTopology C) :
    (equivSmallModel.{u} C).inverse.IsDenseSubsite
      ((equivSmallModel.{u} C).inverse.inducedTopology J) J :=
  have : (equivSmallModel.{u} C).symm.inverse.IsDenseSubsite J
      ((equivSmallModel.{u} C).inverse.inducedTopology J) :=
    inferInstanceAs ((equivSmallModel.{u} C).functor.IsDenseSubsite J
      ((equivSmallModel.{u} C).inverse.inducedTopology J))
  inferInstanceAs ((equivSmallModel.{u} C).symm.functor.IsDenseSubsite
    ((equivSmallModel.{u} C).inverse.inducedTopology J) J)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K]

omit [f.IsCocontinuous J K] in
/-- The composite of the inclusion of the small model with `f` is continuous. -/
theorem isContinuous_smallModel_comp :
    ((equivSmallModel.{u} C).inverse ⋙ f).IsContinuous
      ((equivSmallModel.{u} C).inverse.inducedTopology J) K :=
  have := isDenseSubsite_smallModel J
  Functor.isContinuous_comp _ _ _ J K

omit [f.IsContinuous J K] in
/-- The composite of the inclusion of the small model with `f` is cocontinuous. -/
theorem isCocontinuous_smallModel_comp :
    ((equivSmallModel.{u} C).inverse ⋙ f).IsCocontinuous
      ((equivSmallModel.{u} C).inverse.inducedTopology J) K :=
  have := isDenseSubsite_smallModel J
  isCocontinuous_comp _ _ _ J

variable (O : Sheaf K RingCat.{r}) {T : Sheaf J RingCat.{r}} (hT : T.obj = f.op ⋙ O.obj)

include hT in
/-- The identification of the structure sheaf of the small model with the inverse image of `O`
along the composite to `D`. -/
def smallModelRingHom :
    letI := isDenseSubsite_smallModel J
    letI := isContinuous_smallModel_comp f J K
    (((equivSmallModel.{u} C).inverse ⋙ f).sheafPushforwardContinuous RingCat.{r}
        ((equivSmallModel.{u} C).inverse.inducedTopology J) K).obj O ⟶
      ((equivSmallModel.{u} C).inverse.sheafPushforwardContinuous RingCat.{r}
        ((equivSmallModel.{u} C).inverse.inducedTopology J) J).obj T :=
  ⟨eqToHom (by
    change _ = (equivSmallModel.{u} C).inverse.op ⋙ T.obj
    rw [hT]
    rfl)⟩

/-- **The direct image of sheaves of modules along a continuous and cocontinuous functor from an
essentially small site**, at the module universe of the morphisms of the two sites. -/
def directImageSmall : SheafOfModules.{u} T ⥤ SheafOfModules.{u} O :=
  letI := isDenseSubsite_smallModel J
  letI := isContinuous_smallModel_comp f J K
  letI := isCocontinuous_smallModel_comp f J K
  SheafOfModules.pushforward.{u} (smallModelRingHom f J K O hT) ⋙
    SheafOfModules.directImage.{r, u} ((equivSmallModel.{u} C).inverse ⋙ f)
      ((equivSmallModel.{u} C).inverse.inducedTopology J) K O

omit [EssentiallySmall.{u} C] in
/-- The direct image of sheaves of modules along a continuous and cocontinuous functor is
additive. -/
theorem additive_directImage {C₀ : Type u} [SmallCategory C₀] (g : C₀ ⥤ D)
    (J₀ : GrothendieckTopology C₀) [g.IsContinuous J₀ K] [g.IsCocontinuous J₀ K] :
    (SheafOfModules.directImage.{r, u} g J₀ K O).Additive where
  map_add {_ _} _ _ := by
    apply SheafOfModules.hom_ext
    ext x s
    apply Subtype.ext
    funext j
    rfl

/-- The direct image of sheaves of modules from an essentially small site is additive. -/
theorem additive_directImageSmall : (directImageSmall f J K O hT).Additive :=
  let := isDenseSubsite_smallModel J
  let := isContinuous_smallModel_comp f J K
  let := isCocontinuous_smallModel_comp f J K
  have := additive_directImage.{r, u} K O ((equivSmallModel.{u} C).inverse ⋙ f)
    ((equivSmallModel.{u} C).inverse.inducedTopology J)
  inferInstanceAs (SheafOfModules.pushforward.{u} (smallModelRingHom f J K O hT) ⋙
    SheafOfModules.directImage.{r, u} ((equivSmallModel.{u} C).inverse ⋙ f)
      ((equivSmallModel.{u} C).inverse.inducedTopology J) K O).Additive

/-- The inverse image of sheaves of modules along `f`, for a structure sheaf `T` of the source
whose underlying presheaf is that of the inverse image of `O`: restriction along `f`. -/
abbrev inverseImageOfObjEq : SheafOfModules.{u} O ⥤ SheafOfModules.{u} T :=
  SheafOfModules.pushforward.{u}
    (⟨eqToHom hT⟩ : T ⟶ (f.sheafPushforwardContinuous RingCat.{r} J K).obj O)

/-- Sheaves of modules on an essentially small site are sheaves of modules on its small model. -/
def smallModelEquivalence (R : Sheaf J RingCat.{r}) :
    letI := isDenseSubsite_smallModel J
    SheafOfModules.{u} R ≌ SheafOfModules.{u}
      (((equivSmallModel.{u} C).inverse.sheafPushforwardContinuous RingCat.{r}
        ((equivSmallModel.{u} C).inverse.inducedTopology J) J).obj R) := by
  letI := isDenseSubsite_smallModel J
  let e := (equivSmallModel.{u} C).symm
  have : e.inverse.IsDenseSubsite J ((equivSmallModel.{u} C).inverse.inducedTopology J) :=
    inferInstanceAs ((equivSmallModel.{u} C).functor.IsDenseSubsite J
      ((equivSmallModel.{u} C).inverse.inducedTopology J))
  let J₀ := (equivSmallModel.{u} C).inverse.inducedTopology J
  let T := (e.functor.sheafPushforwardContinuous RingCat.{r} J₀ J).obj R
  let φ : T ⟶ (e.functor.sheafPushforwardContinuous RingCat.{r} J₀ J).obj R := 𝟙 T
  let ψ : R ⟶ (e.inverse.sheafPushforwardContinuous RingCat.{r} J J₀).obj T :=
    ⟨Functor.whiskerRight (NatTrans.op e.counit) R.obj⟩
  exact SheafOfModules.pushforwardPushforwardEquivalence.{u} e φ ψ
    (by
      change _ = _ ≫ 𝟙 _
      exact (Category.comp_id _).symm) (by
      ext U : 2
      dsimp [φ, ψ, T]
      refine (Category.id_comp _).trans ?_
      change R.obj.map (e.counit.app (e.functor.obj U.unop)).op ≫
        R.obj.map (e.functor.map (e.unit.app U.unop)).op = 𝟙 _
      rw [← R.obj.map_comp, ← op_comp]
      exact (congrArg (fun f ↦ R.obj.map f.op)
        (e.functor_unit_comp U.unop)).trans (R.obj.map_id _))

/-- The functor of `SheafOfModules.smallModelEquivalence` is restriction to the small model. -/
theorem smallModelEquivalence_functor (R : Sheaf J RingCat.{r}) :
    letI := isDenseSubsite_smallModel J
    (smallModelEquivalence J R).functor = SheafOfModules.pushforward.{u}
      (𝟙 (((equivSmallModel.{u} C).inverse.sheafPushforwardContinuous RingCat.{r}
        ((equivSmallModel.{u} C).inverse.inducedTopology J) J).obj R)) :=
  rfl

/-- **The inverse image of sheaves of modules from an essentially small site is left adjoint to
the direct image.** -/
@[sga "4 Vbis 2.4.0" "partial"]
def inverseImageDirectImageSmallAdjunction :
    inverseImageOfObjEq f J K O hT ⊣ directImageSmall f J K O hT := by
  obtain ⟨T, hTs⟩ := T
  change T = f.op ⋙ O.obj at hT
  subst hT
  letI := isDenseSubsite_smallModel J
  letI := isContinuous_smallModel_comp f J K
  letI := isCocontinuous_smallModel_comp f J K
  let E := smallModelEquivalence.{r, u} J (⟨f.op ⋙ O.obj, hTs⟩ : Sheaf J RingCat.{r})
  let adj := SheafOfModules.pushforwardDirectImageAdjunction.{r, u}
    ((equivSmallModel.{u} C).inverse ⋙ f) ((equivSmallModel.{u} C).inverse.inducedTopology J) K O
  let e₁ : inverseImageOfObjEq f J K O (T := ⟨f.op ⋙ O.obj, hTs⟩) rfl ⋙ E.functor ≅
      SheafOfModules.pushforward.{u}
        (𝟙 ((((equivSmallModel.{u} C).inverse ⋙ f).sheafPushforwardContinuous
          RingCat.{r} ((equivSmallModel.{u} C).inverse.inducedTopology J) K).obj O)) :=
    Functor.isoWhiskerLeft _ (eqToIso (smallModelEquivalence_functor J _)) ≪≫
    SheafOfModules.pushforwardComp (F := (equivSmallModel.{u} C).inverse) (G := f)
      (𝟙 _) (⟨eqToHom rfl⟩ : (⟨f.op ⋙ O.obj, hTs⟩ : Sheaf J RingCat.{r}) ⟶
        (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext1
      exact Category.id_comp _)
  exact Adjunction.ofNatIsoLeft ((adj.ofNatIsoLeft e₁.symm).comp E.symm.toAdjunction)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ E.unitIso.symm ≪≫
      Functor.rightUnitor _)

section Comparison

variable {J₁ J₂ : GrothendieckTopology C} (hJ : J₁ ≤ J₂) {K₁ K₂ : GrothendieckTopology D}
  (hK : K₁ ≤ K₂) [f.IsContinuous J₁ K₁] [f.IsCocontinuous J₁ K₁] [f.IsContinuous J₂ K₂]
  [f.IsCocontinuous J₂ K₂] (O₂ : Sheaf K₂ RingCat.{r}) {T₂ : Sheaf J₂ RingCat.{r}}
  (hT₂ : T₂.obj = f.op ⋙ O₂.obj)

/-- **The direct image does not see the topologies**: reading a sheaf of modules for coarser
topologies on both sides commutes with the direct image. -/
def directImageSmallCompComparisonIso :
    directImageSmall f J₂ K₂ O₂ hT₂ ⋙
        Stacks.SheafOfModules.comparisonPushforward.{v₂, u, r, u} hK O₂ ≅
      Stacks.SheafOfModules.comparisonPushforward.{v₁, u, r, u} hJ T₂ ⋙
        directImageSmall f J₁ K₁ (Stacks.SheafOfModules.ringOfLe hK O₂)
          (T := Stacks.SheafOfModules.ringOfLe hJ T₂) hT₂ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

end Comparison

end SheafOfModules

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Raising the coefficient universe of an abelian sheaf does not change its cohomology

Let `(C, J)` be a site. An abelian sheaf `F` with values in `AddCommGrpCat.{v}` can be read at a
larger coefficient universe by raising all of its groups of sections, which is the functor
`CategoryTheory.sheafCompose J AddCommGrpCat.uliftFunctor`. This file shows that, when the sheaf
category at the smaller universe has enough injectives and the lift preserves injective objects,
the two sheaves have the same cohomology:

  `H ^ n(J, F) ≅ H ^ n(J, F ⋙ uliftFunctor)`.

## Main definitions

* `Stacks.Cohomology.CoefficientLift.constantSheafUliftIso`: the constant sheaf on `ULift ℤ` at
  the larger coefficient universe is the universe lift of the constant sheaf on `ULift ℤ` at the
  smaller one.
* `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`: the comparison of the cohomology of `F`
  with that of its universe lift, as an additive equivalence.

## Main results

* `Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_ulift_iff`: the two cohomology groups
  vanish together.
* `Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift`: if the cohomology of the
  universe lift of `F` vanishes in degree `n`, so does the cohomology of `F`.
* `Stacks.Cohomology.CoefficientLift.sheafUlift_properties_of_small_subsite`: on a site with a
  small dense subsite the universe lift of the coefficients is compatible with sheafification and
  preserves injective objects.

## References

* [Stacks Project, Tag 0DV3](https://stacks.math.columbia.edu/tag/0DV3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w t z

namespace Stacks.Cohomology.CoefficientLift

section Transfer

/-- The universe lift commutes with the right adjoint of evaluation at an object of a small
category, by the product comparison of `AddCommGrpCat.uliftFunctor`. -/
noncomputable def evaluationRightAdjointUliftIso {C : Type u} [SmallCategory C] (c : C)
    (a : Ab.{u}) :
    (evaluationRightAdjoint Ab.{u} c).obj a ⋙ AddCommGrpCat.uliftFunctor.{w, u} ≅
      (evaluationRightAdjoint Ab.{max u w} c).obj (AddCommGrpCat.uliftFunctor.{w, u}.obj a) := by
  refine NatIso.ofComponents
    (fun t ↦ PreservesProduct.iso AddCommGrpCat.uliftFunctor.{w, u} (fun _ : t ⟶ c ↦ a))
    fun f ↦ Pi.hom_ext _ _ fun g ↦ ?_
  dsimp [evaluationRightAdjoint, getLimitCone]
  simp only [Category.assoc, piComparison_comp_π, limit.lift_π,
    ← AddCommGrpCat.uliftFunctor.{w, u}.map_comp, Fan.mk_π_app]

/-- On a small site the universe lift of abelian sheaves is compatible with sheafification and
preserves injective objects. -/
public lemma sheafUlift_properties_of_small {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) :
    haveI : HasSheafify J Ab.{max u w} :=
      hasSheafifyEssentiallySmallSite.{u, max u w, u, (max u w) + 1, max u w} J _
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u} ∧
      (sheafCompose J AddCommGrpCat.uliftFunctor.{w, u}).PreservesInjectiveObjects := by
  have : HasSheafify J Ab.{max u w} :=
    hasSheafifyEssentiallySmallSite.{u, max u w, u, (max u w) + 1, max u w} J _
  refine ⟨?_, ?_⟩
  · have : PreservesLimitsOfSize.{u, u} (forget Ab.{max u w}) :=
      preservesLimitsOfSize_shrink (forget Ab.{max u w})
    have : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{max u w}) :=
      preservesFilteredColimitsOfSize_shrink (forget Ab.{max u w})
    have (X : C) : PreservesColimitsOfShape (J.Cover X)ᵒᵖ
        (forget Ab.{max u w}) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
    exact GrothendieckTopology.instPreservesSheafification J AddCommGrpCat.uliftFunctor.{w, u}
  · classical
    let G := AddCommGrpCat.uliftFunctor.{w, u}
    have hG : G.PreservesInjectiveObjects := ⟨fun {M} hM ↦ by
      apply (AddCommGrpCat.injective_as_module_iff _).mp
      have := (AddCommGrpCat.injective_as_module_iff M).mpr hM
      exact (ModuleCat.uliftFunctor.{w, u} ℤ).injective_obj (ModuleCat.of ℤ M)⟩
    let W := (Functor.whiskeringRight Cᵒᵖ Ab.{u} Ab.{max u w}).obj G
    have hW : W.PreservesInjectiveObjects := by
      refine ⟨fun {F} hF ↦ ?_⟩
      let Q (c : Cᵒᵖ) := (evaluationRightAdjoint Ab.{u} c).obj (Injective.under (F.obj c))
      let a (c : Cᵒᵖ) : F ⟶ Q c :=
        ((evaluationAdjunctionLeft Ab.{u} c).homEquiv F _) (Injective.ι (F.obj c))
      let i : F ⟶ ∏ᶜ Q := Pi.lift a
      have hi (c : Cᵒᵖ) : i.app c ≫ (Pi.π Q c).app c ≫
          (evaluationAdjunctionLeft Ab.{u} c).counit.app (Injective.under (F.obj c)) =
            Injective.ι (F.obj c) := by
        rw [← Category.assoc]
        have hh := congrArg (fun k : F ⟶ Q c ↦ k.app c) (Pi.lift_comp_π a c)
        change i.app c ≫ (Pi.π Q c).app c = (a c).app c at hh
        rw [hh]
        exact ((evaluationAdjunctionLeft Ab.{u} c).homEquiv F _).symm_apply_apply _
      have : Mono i := by
        have (c : Cᵒᵖ) : Mono (i.app c) := mono_of_mono_fac (hi c)
        exact NatTrans.mono_of_mono_app i
      let r : Retract F (∏ᶜ Q) :=
        ⟨i, Injective.factorThru (𝟙 F) i, Injective.comp_factorThru (𝟙 F) i⟩
      have hQ (c : Cᵒᵖ) : Injective (W.obj (Q c)) :=
        Injective.of_iso (evaluationRightAdjointUliftIso.{u, w} c _).symm
          ((evaluationAdjunctionLeft Ab.{max u w} c).map_injective _
            (G.injective_obj (Injective.under (F.obj c))))
      have : Injective (W.obj (∏ᶜ Q)) :=
        Injective.of_iso (asIso (piComparison W Q)).symm inferInstance
      exact (r.map W).injective
    refine ⟨fun {F} hF ↦ ?_⟩
    have : Injective F.obj := (sheafificationAdjunction J Ab.{u}).map_injective _ hF
    exact Functor.injective_of_map_injective (sheafToPresheaf J Ab.{max u w})
      (W.injective_obj F.obj)

/-- Preservation of injective objects by postcomposition transports along a restriction of sites
which is an equivalence on sheaves for both coefficient categories. -/
public lemma sheafCompose_preservesInjectives_of_restriction
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (i : C ⥤ D) [i.IsContinuous J K]
    {A B : Type*} [Category* A] [Category* B]
    (G : A ⥤ B) [J.HasSheafCompose G] [K.HasSheafCompose G]
    [(i.sheafPushforwardContinuous A J K).IsEquivalence]
    [(i.sheafPushforwardContinuous B J K).IsEquivalence]
    [(sheafCompose J G).PreservesInjectiveObjects] :
    (sheafCompose K G).PreservesInjectiveObjects := by
  constructor
  intro F hF
  have : Injective ((i.sheafPushforwardContinuous A J K).obj F) :=
    (i.sheafPushforwardContinuous A J K).injective_obj F
  have : Injective ((sheafCompose J G).obj
      ((i.sheafPushforwardContinuous A J K).obj F)) :=
    (sheafCompose J G).injective_obj _
  exact (i.sheafPushforwardContinuous B J K).injective_of_map_injective this

/-- Universe lifting of abelian groups on a site with a small dense subsite is compatible with
sheafification and preserves injective objects. -/
public lemma sheafUlift_properties_of_small_subsite
    {C : Type v} [SmallCategory C] {D : Type*} [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (i : C ⥤ D) [i.Full] [i.IsCoverDense K] [i.IsContinuous J K]
    [(i.sheafPushforwardContinuous Ab.{v} J K).IsEquivalence]
    [(i.sheafPushforwardContinuous Ab.{max v t} J K).IsEquivalence] :
    K.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v} ∧
    (sheafCompose K AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects := by
  have : HasSheafify J Ab.{max v t} :=
    hasSheafifyEssentiallySmallSite.{v, max v t, v, (max v t) + 1, max v t} J _
  obtain ⟨h₁, h₂⟩ := sheafUlift_properties_of_small.{v, t} J
  exact ⟨GrothendieckTopology.PreservesSheafification.transport K J i _ _,
    sheafCompose_preservesInjectives_of_restriction J K i _⟩

/-- The universe lift of abelian sheaves preserves finite limits. -/
public lemma uliftSheafCompose_preservesFiniteLimits.{v₂, t₂, u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v₂}] [HasSheafify J Ab.{max v₂ t₂}] :
    PreservesFiniteLimits (sheafCompose J AddCommGrpCat.uliftFunctor.{t₂, v₂}) := by
  refine ⟨fun I _ _ ↦ ?_⟩
  have : PreservesLimitsOfShape I (sheafCompose J AddCommGrpCat.uliftFunctor.{t₂, v₂} ⋙
      sheafToPresheaf J Ab.{max v₂ t₂}) :=
    inferInstanceAs (PreservesLimitsOfShape I
      (sheafToPresheaf J Ab.{v₂} ⋙ (Functor.whiskeringRight Cᵒᵖ Ab.{v₂} Ab.{max v₂ t₂}).obj
        AddCommGrpCat.uliftFunctor.{t₂, v₂}))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J Ab.{max v₂ t₂})

/-- The universe lift of abelian sheaves preserves finite colimits when it is compatible with
sheafification. -/
public lemma uliftSheafCompose_preservesFiniteColimits.{v₂, t₂, u₁, v₁}
    {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v₂}] [HasSheafify J Ab.{max v₂ t₂}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t₂, v₂}] :
    PreservesFiniteColimits (sheafCompose J AddCommGrpCat.uliftFunctor.{t₂, v₂}) := by
  refine ⟨fun I _ _ ↦ ?_⟩
  let G := sheafCompose J AddCommGrpCat.uliftFunctor.{t₂, v₂}
  let adj := sheafificationAdjunction J Ab.{v₂}
  have : PreservesColimitsOfShape I (presheafToSheaf J Ab.{v₂} ⋙ G) :=
    preservesColimitsOfShape_of_natIso
      (sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{t₂, v₂} adj
        (sheafificationAdjunction J Ab.{max v₂ t₂}))
  refine ⟨fun {F} ↦ ?_⟩
  have : PreservesColimitsOfSize.{0, 0} (presheafToSheaf J Ab.{v₂}) :=
    adj.leftAdjoint_preservesColimits
  let e : (F ⋙ sheafToPresheaf J Ab.{v₂}) ⋙ presheafToSheaf J Ab.{v₂} ≅ F :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫
      Functor.rightUnitor F
  have : PreservesColimit ((F ⋙ sheafToPresheaf J Ab.{v₂}) ⋙ presheafToSheaf J Ab.{v₂}) G :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves (presheafToSheaf J Ab.{v₂})
        (colimit.isColimit (F ⋙ sheafToPresheaf J Ab.{v₂})))
      (isColimitOfPreserves (presheafToSheaf J Ab.{v₂} ⋙ G)
        (colimit.isColimit (F ⋙ sheafToPresheaf J Ab.{v₂})))
  exact preservesColimit_of_iso_diagram G e

/-- The constant sheaf on `ULift ℤ` at a large coefficient universe is the universe lift of the
constant sheaf on `ULift ℤ` at the small one. -/
public noncomputable def constantSheafUliftIso
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v}] [HasSheafify J Ab.{max v t}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v}] :
    (constantSheaf J Ab.{max v t}).obj (AddCommGrpCat.of (ULift.{max v t} ℤ)) ≅
      (sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).obj
        ((constantSheaf J Ab.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))) := by
  let e : AddCommGrpCat.of (ULift.{max v t} ℤ) ≅
      AddCommGrpCat.uliftFunctor.{t, v}.obj (AddCommGrpCat.of (ULift.{v} ℤ)) :=
    AddEquiv.toAddCommGrpIso
      { toFun := fun x ↦ ⟨⟨x.down⟩⟩
        invFun := fun x ↦ ⟨x.down.down⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
  exact (constantSheaf J Ab.{max v t}).mapIso e ≪≫
    (sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{t, v}
      (sheafificationAdjunction J Ab.{v})
      (sheafificationAdjunction J Ab.{max v t})).app
      ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{v} ℤ)))

/-- Descent of a vanishing statement along universe lifting of the coefficients: if the
cohomology of the universe lift of `F` vanishes in degree `n`, so does the cohomology of `F`. -/
public theorem subsingleton_cohomology_of_ulift
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v}] [HasSheafify J Ab.{max v t}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v}]
    [(sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects]
    [EnoughInjectives (Sheaf J Ab.{v})]
    [HasExt.{w} (Sheaf J Ab.{v})] [HasExt.{z} (Sheaf J Ab.{max v t})]
    (F : Sheaf J Ab.{v}) (n : ℕ)
    (h : Subsingleton (Sheaf.H.{z} ((sheafCompose J
      AddCommGrpCat.uliftFunctor.{t, v}).obj F) n)) :
    Subsingleton (Sheaf.H.{w} F n) := by
  let L := sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}
  have : L.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits L := uliftSheafCompose_preservesFiniteLimits.{v, t} J
  have : PreservesFiniteColimits L := uliftSheafCompose_preservesFiniteColimits.{v, t} J
  have h' : Subsingleton (Abelian.Ext.{z}
      (L.obj ((constantSheaf J Ab.{v}).obj (AddCommGrpCat.of (ULift ℤ)))) (L.obj F) n) := by
    let e := constantSheafUliftIso.{v, t} J
    refine ⟨fun x y ↦ ?_⟩
    have he : (Abelian.Ext.mk₀ e.hom).comp x (zero_add n) =
        (Abelian.Ext.mk₀ e.hom).comp y (zero_add n) := Subsingleton.elim _ _
    simpa [Abelian.Ext.mk₀_comp_mk₀_assoc] using
      congrArg (fun z ↦ (Abelian.Ext.mk₀ e.inv).comp z (zero_add n)) he
  exact Function.Injective.subsingleton
    (L.mapExt_bijective_of_preservesInjectiveObjects _ F n).injective

/-- Cohomology of an abelian sheaf, transported along an isomorphism of sheaves. -/
public def sheafHIsoCongr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{v}] [HasExt.{w} (Sheaf J Ab.{v})]
    {F G : Sheaf J Ab.{v}} (e : F ≅ G) (n : ℕ) :
    Sheaf.H.{w} F n ≃+ Sheaf.H.{w} G n :=
  (((extFunctor.{w} n).obj (Opposite.op ((constantSheaf J Ab.{v}).obj
    (AddCommGrpCat.of (ULift ℤ))))).mapIso e).addCommGroupIsoToAddEquiv

/-- Vanishing of the cohomology of an abelian sheaf depends only on its isomorphism class. -/
public theorem subsingleton_sheafH_congr {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J Ab.{v}] [HasExt.{w} (Sheaf J Ab.{v})]
    {F G : Sheaf J Ab.{v}} (e : F ≅ G) (n : ℕ) :
    Subsingleton (Sheaf.H.{w} F n) ↔ Subsingleton (Sheaf.H.{w} G n) :=
  (sheafHIsoCongr.{v, w} e n).toEquiv.subsingleton_congr

/-- Raising the coefficient universe of an abelian sheaf does not change its cohomology: the
additive equivalence induced by `CategoryTheory.Functor.mapExtAddHom` of the universe lift, read
through the identification `constantSheafUliftIso` of the two constant sheaves on `ULift ℤ`. -/
public noncomputable def sheafHUliftAddEquiv
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v}] [HasSheafify J Ab.{max v t}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v}]
    [(sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects]
    [EnoughInjectives (Sheaf J Ab.{v})]
    [HasExt.{w} (Sheaf J Ab.{v})] [HasExt.{z} (Sheaf J Ab.{max v t})]
    (F : Sheaf J Ab.{v}) (n : ℕ) :
    Sheaf.H.{w} F n ≃+
      Sheaf.H.{z} ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).obj F) n := by
  let L := sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}
  have : L.Additive := ⟨by intros; rfl⟩
  have : PreservesFiniteLimits L := uliftSheafCompose_preservesFiniteLimits.{v, t} J
  have : PreservesFiniteColimits L := uliftSheafCompose_preservesFiniteColimits.{v, t} J
  exact (AddEquiv.ofBijective
      (L.mapExtAddHom ((constantSheaf J Ab.{v}).obj (AddCommGrpCat.of (ULift ℤ))) F n)
      (L.mapExt_bijective_of_preservesInjectiveObjects _ F n)).trans
    (((extFunctor.{z} n).mapIso
      (constantSheafUliftIso.{v, t} J).symm.op).app (L.obj F)).addCommGroupIsoToAddEquiv.symm

/-- The cohomology of an abelian sheaf and of its coefficient-universe lift vanish together. -/
public theorem subsingleton_sheafH_ulift_iff
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{v}] [HasSheafify J Ab.{max v t}]
    [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v}]
    [(sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects]
    [EnoughInjectives (Sheaf J Ab.{v})]
    [HasExt.{w} (Sheaf J Ab.{v})] [HasExt.{z} (Sheaf J Ab.{max v t})]
    (F : Sheaf J Ab.{v}) (n : ℕ) :
    Subsingleton (Sheaf.H.{z}
        ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, v}).obj F) n) ↔
      Subsingleton (Sheaf.H.{w} F n) :=
  ((sheafHUliftAddEquiv.{v, w, t, z} J F n).toEquiv.subsingleton_congr).symm

end Transfer

end Stacks.Cohomology.CoefficientLift

end

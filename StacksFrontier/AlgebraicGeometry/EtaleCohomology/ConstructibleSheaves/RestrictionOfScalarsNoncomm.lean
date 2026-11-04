module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalars

/-!
# Restriction of scalars of constructible sheaves, for not necessarily commutative rings

Let `f : R →+* S` be a homomorphism of rings, not necessarily commutative, such that every
finitely generated `S`-module is finitely generated over `R` — for instance `ℤ →+* Λ` with `Λ` a
finite ring. Restriction of scalars along `f` carries a constructible sheaf of `S`-modules on the
small étale site of a scheme to a constructible sheaf of `R`-modules. The proof is the one of
`Stacks.EtaleCohomology.isConstructibleModuleSheaf_restrictScalars`, which is stated for a
surjection of commutative Noetherian rings: restriction of scalars commutes with the constant sheaf
functor and with inverse images, both being left adjoints of functors which commute on the nose
with restriction of scalars, and on the constant values only finite generation has to be checked.

## Main results

* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_restrictScalars_of_isFG`: restriction of
  scalars along a ring homomorphism preserving finite generation preserves constructibility.
* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_restrictScalarsInt`: the case `ℤ →+* Λ`
  with `Λ` finite.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w r s v c

namespace Stacks.EtaleCohomology

section General

variable {R : Type r} {S : Type s} [Ring R] [Ring S] (f : R →+* S)

/-- Restriction of scalars of a sheaf of modules along a homomorphism of not necessarily
commutative rings, applied sectionwise. -/
public abbrev restrictScalarsSheafNoncomm {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Sheaf J (ModuleCat.{max r s w} S) ⥤ Sheaf J (ModuleCat.{max r s w} R) :=
  letI : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max r s w}
      f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩
  sheafCompose J (ModuleCat.restrictScalars.{max r s w, r, s} f)

/-- Coextension of scalars along a homomorphism of not necessarily commutative rings, applied
sectionwise, carries sheaves of modules to sheaves of modules. -/
lemma hasSheafCompose_coextendScalars_noncomm {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (ModuleCat.coextendScalars.{r, s, max r s w} f) := by
  let : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.coextendScalars.{r, s, max r s w} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  exact ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩

/-- Restriction of scalars of the constant sheaf on `E` is the constant sheaf on the restriction
of scalars of `E`. -/
def restrictScalarsSheafNoncommConstantSheafIso
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J (ModuleCat.{max r s w} R)]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    (E : ModuleCat.{max r s w} S) :
    (restrictScalarsSheafNoncomm.{w} f J).obj ((constantSheaf J (ModuleCat.{max r s w} S)).obj E) ≅
      (constantSheaf J (ModuleCat.{max r s w} R)).obj
        ((ModuleCat.restrictScalars.{max r s w, r, s} f).obj E) := by
  letI : J.HasSheafCompose (ModuleCat.coextendScalars.{r, s, max r s w} f) :=
    hasSheafCompose_coextendScalars_noncomm f J
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f)
  letI : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max r s w}
      f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩
  exact (sheafToPresheaf J (ModuleCat.{max r s w} R)).preimageIso
    ((sheafifyComposeIso J (ModuleCat.restrictScalars.{max r s w, r, s} f)
      ((Functor.const Cᵒᵖ).obj E)).symm ≪≫
    (sheafification J (ModuleCat.{max r s w} R)).mapIso
      (Functor.constComp Cᵒᵖ E (ModuleCat.restrictScalars.{max r s w, r, s} f)))

/-- Restriction of scalars commutes with inverse image along a continuous functor. -/
def sheafPullbackRestrictScalarsSheafNoncommIso
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous G J K]
    [HasWeakSheafify J (ModuleCat.{max r s w} R)]
    [HasWeakSheafify K (ModuleCat.{max r s w} R)]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K).IsRightAdjoint]
    (F : Sheaf J (ModuleCat.{max r s w} S)) :
    (restrictScalarsSheafNoncomm.{w} f K).obj
        ((G.sheafPullback (ModuleCat.{max r s w} S) J K).obj F) ≅
      (G.sheafPullback (ModuleCat.{max r s w} R) J K).obj
        ((restrictScalarsSheafNoncomm.{w} f J).obj F) := by
  let T := ModuleCat.coextendScalars.{r, s, max r s w} f
  letI : J.HasSheafCompose T := hasSheafCompose_coextendScalars_noncomm f J
  letI : K.HasSheafCompose T := hasSheafCompose_coextendScalars_noncomm f K
  letI : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{max r s w}
      f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩
  letI : K.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf K P _ hP⟩
  let adjSheaf : ∀ (L : GrothendieckTopology C) [L.HasSheafCompose T]
      [L.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f)],
      sheafCompose L (ModuleCat.restrictScalars.{max r s w, r, s} f) ⊣ sheafCompose L T :=
    fun L _ _ => ((ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f).whiskerRight
      Cᵒᵖ).restrictFullyFaithful (fullyFaithfulSheafToPresheaf L _)
      (fullyFaithfulSheafToPresheaf L _) (Iso.refl _) (Iso.refl _)
  let adjSheafK : sheafCompose K (ModuleCat.restrictScalars.{max r s w, r, s} f) ⊣
      sheafCompose K T :=
    ((ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f).whiskerRight
      Dᵒᵖ).restrictFullyFaithful (fullyFaithfulSheafToPresheaf K _)
      (fullyFaithfulSheafToPresheaf K _) (Iso.refl _) (Iso.refl _)
  let pR := G.sheafAdjunctionContinuous (ModuleCat.{max r s w} R) J K
  let pS := G.sheafAdjunctionContinuous (ModuleCat.{max r s w} S) J K
  let rightIso :
      G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K ⋙ sheafCompose J T ≅
        sheafCompose K T ⋙ G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  have adj₁ := pS.comp adjSheafK
  have adj₂ := ((adjSheaf J).comp pR).ofNatIsoRight rightIso
  exact (Adjunction.leftAdjointUniq adj₁ adj₂).app F

/-- Restriction of scalars preserves local constancy of finite type, given that it preserves
finite generation of modules. -/
theorem isFiniteTypeLocallyConstant_restrictScalarsSheafNoncomm
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} S)]
    (hfg : ∀ E : ModuleCat.{max r s w} S, ModuleCat.isFG S E →
      ModuleCat.isFG R ((ModuleCat.restrictScalars.{max r s w, r, s} f).obj E))
    (F : Sheaf J (ModuleCat.{max r s w} S))
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant S J F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R J
      ((restrictScalarsSheafNoncomm.{w} f J).obj F) := by
  intro U
  rcases hF U with ⟨I, V, g, hg, hV⟩
  refine ⟨I, V, g, hg, fun i => ?_⟩
  rcases hV i with ⟨E, hE, ⟨e⟩⟩
  refine ⟨(ModuleCat.restrictScalars.{max r s w, r, s} f).obj E, hfg E hE, ⟨?_⟩⟩
  exact (restrictScalarsSheafNoncommConstantSheafIso f (J.over (V i)) E).symm ≪≫
    (restrictScalarsSheafNoncomm.{w} f (J.over (V i))).mapIso e ≪≫
    (NatIso.ofComponents (F := J.overPullback (ModuleCat.{max r s w} S) (V i) ⋙
        restrictScalarsSheafNoncomm.{w} f (J.over (V i)))
      (G := restrictScalarsSheafNoncomm.{w} f J ⋙ J.overPullback (ModuleCat.{max r s w} R) (V i))
      (fun _ => Iso.refl _) (fun _ => rfl)).app F

end General

/-- **Restriction of scalars preserves constructibility**, along a homomorphism of not
necessarily commutative rings which preserves finite generation. -/
public theorem isConstructibleModuleSheaf_restrictScalars_of_isFG
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {R : Type r} {S : Type s} [Ring R] [Ring S] (f : R →+* S)
    (hfg : ∀ E : ModuleCat.{max r s w} S, ModuleCat.isFG S E →
      ModuleCat.isFG R ((ModuleCat.restrictScalars.{max r s w, r, s} f).obj E))
    [HasWeakSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} R)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} S)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} S)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r s w} S))
    (hF : IsConstructibleModuleSheaf B X S F) :
    IsConstructibleModuleSheaf B X R
      ((restrictScalarsSheafNoncomm.{w} f (SmallEtale.topology B X.1 X.property)).obj F) := by
  intro U
  rcases hF U with ⟨stratification, hstratification⟩
  refine ⟨stratification, fun i => ?_⟩
  let J := SmallEtale.topology B (stratification.piece i).1 (stratification.piece i).property
  let V := SmallEtale.final B (stratification.piece i).1 (stratification.piece i).property
  have : HasWeakSheafify J (ModuleCat.{max r s w} R) :=
    AlgebraicGeometry.SmallEtale.hasWeakSheafify_of_overTerminal J V
      (SmallEtale.finalIsTerminal B (stratification.piece i).1 (stratification.piece i).property)
  have hᵢ := isFiniteTypeLocallyConstant_restrictScalarsSheafNoncomm f J hfg _
    (hstratification i)
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr J R
    (sheafPullbackRestrictScalarsSheafNoncommIso f
      (AlgebraicGeometry.smallEtaleBaseChange B (stratification.inclusion i))
      (SmallEtale.topology B X.1 X.property) J F) hᵢ

/-- A finitely generated module over a finite ring is finitely generated over `ℤ`. -/
theorem isFG_restrictScalars_int_of_finite (Λ : Type s) [Ring Λ] [Finite Λ]
    (E : ModuleCat.{v} Λ) (hE : ModuleCat.isFG Λ E) :
    ModuleCat.isFG ℤ ((ModuleCat.restrictScalars.{v, 0, s} (Int.castRingHom Λ)).obj E) := by
  rw [ModuleCat.isFG_iff] at hE ⊢
  have : Finite E := Module.finite_of_finite Λ
  have : Finite ((ModuleCat.restrictScalars.{v, 0, s} (Int.castRingHom Λ)).obj E) :=
    inferInstanceAs (Finite E)
  exact Module.Finite.of_finite

/-- **Restriction of scalars from a finite ring to `ℤ` preserves constructibility.** -/
public theorem isConstructibleModuleSheaf_restrictScalarsInt
    (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type s) [Ring Λ] [Finite Λ]
    [HasWeakSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{max s w} ℤ)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max s w} ℤ)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max s w} ℤ)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max s w} Λ)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max s w} Λ)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max s w} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    IsConstructibleModuleSheaf B X ℤ
      ((restrictScalarsSheafNoncomm.{w} (Int.castRingHom Λ)
        (SmallEtale.topology B X.1 X.property)).obj F) :=
  isConstructibleModuleSheaf_restrictScalars_of_isFG.{u, w, 0, s} B X (Int.castRingHom Λ)
    (isFG_restrictScalars_int_of_finite Λ) F hF

end Stacks.EtaleCohomology

end

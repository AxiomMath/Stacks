module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleRestrictionTrace
public import StacksFrontier.CategoryTheory.Sites.SurjectivityFromGraphCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Trace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.FinitePushforwardSheetCount
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.ModuleExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.ConstantModuleFiltration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.FinitePushforward
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A sheaf on which the degree is invertible is a direct summand of `f_*f^{-1}`

Let `f : V ⟶ U` be a finite étale morphism of constant degree `d`, and let `𝒢` be a sheaf of
`Λ`-modules on `U_étale` on which multiplication by `d` is an isomorphism. The discussion of
Stacks, Section 03SH, gives maps `𝒢 ⟶ f_*f^{-1}𝒢 ⟶ 𝒢` — restriction followed by the trace —
whose composite is multiplication by `d`, hence an isomorphism; so `𝒢` is a retract of
`f_*f^{-1}𝒢`. This is the form in which the method of the trace enters the proof of Stacks
0GJH.

## Main results

* `Stacks.EtaleCohomology.exists_retraction_directImage_pullback_of_finiteEtale` — the retraction,
  for sheaves of `Λ`-modules on Mathlib's small étale site.

## Implementation notes

Restriction followed by the trace is computed on the small étale site of Stacks 021B cut out of
a big étale site, `AlgebraicGeometry.moduleRestrictionUnit_comp_moduleTrace`. It is carried to
Mathlib's small étale site along the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv` of the
two sheaf categories, which commutes with direct image
(`AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`) and with inverse image
(`AlgebraicGeometry.SmallEtale.restrictionPullbackBaseChangeIso`). On the bounded site the inverse
image along the étale morphism is restriction along composition with it, the left adjoint of the
direct image by `AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction`. Only the existence
of the retraction is transported, which is all Stacks 0GJH uses.

## References

* [Stacks Project, Tag 03SH](https://stacks.math.columbia.edu/tag/03SH)
* [Stacks Project, Tag 0GJH](https://stacks.math.columbia.edu/tag/0GJH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **The method of the trace: `𝒢` is a direct summand of `f_*f^{-1}𝒢`** (Stacks, Section
03SH). Let `f : V ⟶ U` be finite étale of constant degree `d` and let `𝒢` be a sheaf of
`Λ`-modules on `U_étale` on which multiplication by `d` is an isomorphism. Then there are maps
`𝒢 ⟶ f_*f^{-1}𝒢 ⟶ 𝒢` whose composite is the identity. -/
theorem exists_retraction_directImage_pullback_of_finiteEtale (Λ : Type v) [CommRing Λ]
    {U V : Scheme.{u}} (f : V ⟶ U) [IsFinite f] [Etale f] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{max (u + 1) v} Λ)) [IsIso (d • 𝟙 G)] :
    ∃ (i : G ⟶ (etaleModuleDirectImage.{u, v} Λ f).obj ((smallEtalePullbackModuleCat Λ f).obj G))
      (r : (etaleModuleDirectImage.{u, v} Λ f).obj ((smallEtalePullbackModuleCat Λ f).obj G) ⟶ G),
      i ≫ r = 𝟙 G := by
  let A := ModuleCat.{max (u + 1) v} Λ
  let B := BigEtaleSite.containing U
  let hU : B.Contains U := BigEtaleSite.contains_containing U
  have hV : B.Contains V :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact f).trans_lt hU
  let S : B.Scheme := B.obj U hU
  let T : B.Scheme := B.obj V hV
  let fB : T ⟶ S := ObjectProperty.homMk f
  let Ub : SmallEtale B U hU := ⟨Over.mk fB, (inferInstance : Etale f)⟩
  have : IsFinite (B.inclusion.map Ub.obj.hom) := (inferInstance : IsFinite f)
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map Ub.obj.hom) d :=
    (inferInstance : Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d)
  let ρU := (SmallEtale.toEtaleSite B S.obj S.property).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property) S.obj.smallEtaleTopology
  let adjU := (smallEtaleBaseChange f).sheafAdjunctionContinuous A
    U.smallEtaleTopology V.smallEtaleTopology
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B Ub.obj.hom
  have := smallEtalePostcompose_isContinuous B U hU Ub
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B fB
  have : Etale (B.inclusion.map Ub.obj.hom) := Ub.property
  let adjSite :
      smallEtalePostcompose B U hU Ub ⊣ AlgebraicGeometry.smallEtaleBaseChange B Ub.obj.hom :=
    smallEtalePostcomposeBaseChangeAdjunction B Ub.obj.hom
  let adjB := adjSite.sheafPushforwardContinuous
    (E := A) (SmallEtale.topology B Ub.obj.left.1 Ub.obj.left.property)
    (SmallEtale.topology B U hU)
  let e₁ := (SmallEtale.toEtaleSitePushforwardBaseChangeIso B fB A).app
    ((smallEtalePullbackModuleCat Λ f).obj G)
  let e₂ := (SmallEtale.restrictionPullbackBaseChangeIso B A fB (adjU := adjU) (adjB := adjB)).app G
  let fB_ := (AlgebraicGeometry.smallEtaleBaseChange B fB).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
  let φ : ρU.obj ((etaleModuleDirectImage.{u, v} Λ f).obj
      ((smallEtalePullbackModuleCat Λ f).obj G)) ≅
      fB_.obj ((moduleRestriction B U hU Ub Λ).obj (ρU.obj G)) :=
    e₁ ≪≫ fB_.mapIso e₂.symm
  let H := ρU.obj G
  have : ρU.IsEquivalence := (SmallEtale.sheafEquiv B S.obj S.property A).isEquivalence_inverse
  have : ρU.Additive := Functor.additive_of_preserves_binary_products _
  have hH : IsIso (d • 𝟙 H) := by
    have : ρU.map (d • 𝟙 G) = d • 𝟙 H := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rw [← this]
    infer_instance
  have hres := moduleRestrictionUnit_comp_moduleTrace B U hU Ub Λ d H
  let e := @asIso _ _ _ _ (d • 𝟙 H) hH
  let ff := (SmallEtale.sheafEquiv B S.obj S.property A).fullyFaithfulInverse
  refine ⟨ff.preimage ((moduleRestrictionUnit B U hU Ub Λ).app H ≫ φ.inv),
    ff.preimage (φ.hom ≫ (moduleTrace B U hU Ub Λ).app H ≫ e.inv), ?_⟩
  apply ff.map_injective
  rw [Functor.map_comp, ff.map_preimage, ff.map_preimage, CategoryTheory.Functor.map_id]
  calc ((moduleRestrictionUnit B U hU Ub Λ).app H ≫ φ.inv) ≫ φ.hom ≫
        (moduleTrace B U hU Ub Λ).app H ≫ e.inv =
      ((moduleRestrictionUnit B U hU Ub Λ).app H ≫ (moduleTrace B U hU Ub Λ).app H) ≫ e.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = 𝟙 H := by rw [hres]; exact e.hom_inv_id

end Stacks.EtaleCohomology

namespace Stacks.EtaleCohomology.TorsionModules

attribute [local instance] moduleCat_hasLimitsOfSize AlgebraicGeometry.moduleSheaf_hasSheafify

/-- Sheaves of `Λ`-modules on the small étale site of Tag 021B form a Grothendieck abelian
category: the site is essentially small at the coefficient universe. -/
instance isGrothendieckAbelian_sheaf_smallEtale_moduleCat (B : BigEtaleSite.{u}) (X : Scheme.{u})
    (hX : B.Contains X) (Λ : Type v) [Ring Λ] :
    IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) :=
  have : ∀ W : (SmallEtale B X hX)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow W
        (equivSmallModel.{max (u + 1) v} (SmallEtale B X hX)).inverse.op)
        (ModuleCat.{max (u + 1) v} Λ) := fun _ ↦ inferInstance
  Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max (u + 1) v} (SmallEtale.topology B X hX) _

/-- Sheaves of `Λ`-modules on the small étale site of Tag 021B have injective resolutions. -/
instance hasInjectiveResolutions_sheaf_smallEtale_moduleCat (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) (Λ : Type v) [Ring Λ] :
    HasInjectiveResolutions
      (Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) :=
  have := IsGrothendieckAbelian.enoughInjectives
    (C := Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ))
  inferInstance

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (Λ : Type v) [CommRing Λ] [IsFinite (B.inclusion.map U.obj.hom)]

/-- The direct image along a finite étale morphism is exact on sheaves of `Λ`-modules: it is a
right adjoint, and it is isomorphic to extension by zero (Stacks 03S7), a left adjoint. Hence its
higher right derived functors vanish. -/
@[sga "4½ Arcata 2.3.6" "special case"]
theorem isZero_rightDerived_modulePushforward_of_finiteEtale
    (𝒢 : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ)) (q : ℕ) (hq : 0 < q) :
    haveI := modulePushforward_additive.{u, v} B Λ U.obj.hom
    IsZero (((modulePushforward.{u, v} B Λ U.obj.hom).rightDerived q).obj 𝒢) := by
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B U.obj.hom
  have := modulePushforward_additive.{u, v} B Λ U.obj.hom
  have : PreservesFiniteLimits (modulePushforward.{u, v} B Λ U.obj.hom) :=
    have : PreservesLimitsOfSize.{0, 0} (modulePushforward.{u, v} B Λ U.obj.hom) :=
      (Functor.sheafAdjunctionContinuous (AlgebraicGeometry.smallEtaleBaseChange B U.obj.hom)
        (ModuleCat.{max (u + 1) v} Λ) _ _).rightAdjoint_preservesLimits
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteColimits (modulePushforward.{u, v} B Λ U.obj.hom) :=
    have : PreservesColimitsOfSize.{0, 0} (AlgebraicGeometry.moduleExtensionByZero B X hX U Λ) :=
      (AlgebraicGeometry.moduleExtensionByZeroAdjunction B X hX U Λ).leftAdjoint_preservesColimits
    have : PreservesFiniteColimits (AlgebraicGeometry.moduleExtensionByZero B X hX U Λ) :=
      ⟨fun _ _ _ => inferInstance⟩
    preservesFiniteColimits_of_natIso
      (AlgebraicGeometry.moduleExtensionByZeroIsoPushforward B X hX U Λ)
  exact Functor.isZero_rightDerived_of_exact _ 𝒢 q hq

omit [IsFinite (B.inclusion.map U.obj.hom)] in
/-- The direct image along an étale morphism is a right adjoint, of restriction. -/
theorem isRightAdjoint_modulePushforward_smallEtale :
    (modulePushforward.{u, v} B Λ U.obj.hom).IsRightAdjoint :=
  have := AlgebraicGeometry.smallEtaleBaseChange_isContinuous B U.obj.hom
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  let adjSite :
      smallEtalePostcompose B X hX U ⊣ AlgebraicGeometry.smallEtaleBaseChange B U.obj.hom :=
    AlgebraicGeometry.smallEtalePostcomposeBaseChangeAdjunction B U.obj.hom
  ⟨_, ⟨adjSite.sheafPushforwardContinuous (E := ModuleCat.{max (u + 1) v} Λ)
      (SmallEtale.topology B U.obj.left.1 U.obj.left.property) (SmallEtale.topology B X hX)⟩⟩

/-- **Stacks, Section 03SH: the méthode de la trace.** Let `f : Y ⟶ X` be a finite étale
morphism of constant degree `d` and let `ℱ` be a sheaf of `Λ`-modules on `X_étale` on which
multiplication by `d` is an isomorphism. Then the map

`H^n(X, ℱ) ⟶ H^n(X, f_*f^{-1}ℱ) = H^n(Y, f^{-1}ℱ)`

is injective. The first map is induced by restriction `ℱ ⟶ f_*f^{-1}ℱ`; the identification is the
one given by the vanishing of the higher direct images of `f` and the Leray spectral sequence
(`Stacks.EtaleCohomology.TorsionModules.moduleCohomologyPushforwardIso`). -/
theorem injective_moduleCohomology_restriction_of_finiteEtale (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (B.inclusion.map U.obj.hom) d]
    (F : Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) [IsIso (d • 𝟙 F)]
    (n : ℕ) :
    haveI := isRightAdjoint_modulePushforward_smallEtale B X hX U Λ
    Function.Injective
      ((((moduleGlobalSections.{u, v} B Λ (B.obj X hX)).rightDerived n).map
          ((AlgebraicGeometry.moduleRestrictionUnit B X hX U Λ).app F) ≫
        (moduleCohomologyPushforwardIso.{u, v} B Λ U.obj.hom
          ((AlgebraicGeometry.moduleRestriction B X hX U Λ).obj F)
          (isZero_rightDerived_modulePushforward_of_finiteEtale B X hX U Λ _) n).inv).hom) := by
  have := isRightAdjoint_modulePushforward_smallEtale B X hX U Λ
  have hm := AlgebraicGeometry.mono_rightDerived_map_moduleRestrictionUnit_app B X hX U Λ d
    (moduleGlobalSections.{u, v} B Λ (B.obj X hX)) F n
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

end Stacks.EtaleCohomology.TorsionModules

end

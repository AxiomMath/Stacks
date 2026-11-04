module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquareObjectwise
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleRingedModules
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteSheafPushforwardBaseChange
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare

/-!
# The identity `g'_!(f')^{-1} = f^{-1}g_!` of Stacks 07AT on sheaves of modules

Let `f : 𝒳 ⟶ 𝒴` be a smooth (respectively flat) 1-morphism of algebraic stacks, let `f'` be its
restriction to the lisse-étale (respectively flat-fppf) sites of **Stacks 07AT**, and let `g`,
`g'` be the morphisms of ringed topoi of **Stacks 0788** attached to the inclusions of the two
subsites. **Stacks 07AT** asserts `g'_!(f')^{-1} = f^{-1}g_!`. The library has that identity on
sheaves of sets (`AlgebraicGeometry.Stack.LisseEtale.shriekBaseChangeIso`), at the coefficient
universe `Type (u + 1)`; this file proves it **on sheaves of modules**, for the lower shriek
`g_!` of **Stacks 0789** (`AlgebraicGeometry.Stack.subsiteModuleLowerShriek`), at the module
universe `u` of the structure sheaf, where `f^{-1}` is the inverse image of sheaves of modules of
**Stacks 06WE** (`AlgebraicGeometry.Stack.modulePullback`, restriction along `f`).

## Main results

* `AlgebraicGeometry.Stack.subsiteModulePullbackIsoRestriction`: the pullback of sheaves of
  modules along the morphism of ringed topoi of a full subsite is restriction along the
  inclusion; this is `AlgebraicGeometry.Stack.subsiteModulePullbackIso` read at the spelling of
  the pullback that `AlgebraicGeometry.Stack.subsiteModuleLowerShriek` is the left adjoint of.
* `AlgebraicGeometry.Stack.subsiteModuleShriekBaseChangeIso`: the identity for a 1-morphism of
  algebraic stacks carrying one continuous and cocontinuous full subsite into another, given the
  identity `f'_*(g')^{-1} = g^{-1}f_*` on sheaves of sets objectwise.
* `AlgebraicGeometry.Stack.LisseEtale.moduleShriekBaseChangeIso` and
  `AlgebraicGeometry.Stack.FlatFppf.moduleShriekBaseChangeIso`: **Stacks 07AT** (1) and (2), the
  identity `g'_!(f')^{-1} = f^{-1}g_!` on sheaves of modules, with no hypothesis.

## Implementation notes

The source deduces the identity from `f'_*(g')^{-1} = g^{-1}f_*` by conjugating along the four
adjunctions, and so does this file. The direct images of sheaves of modules are the canonical ones
of `Stacks.SheafOfModules.pushforwardCocontinuous`, and the comparison of the two composites is
`Stacks.SheafOfModules.squareComparison`, linear over the structure sheaf by construction; that
it is invertible is reduced by
`Stacks.SheafOfModules.isIso_squareComparison_of_forget` to the objectwise bijectivity on
sheaves of sets, `CategoryTheory.SubsitePushforward.bijective_subsiteRanBaseChange_app_app`, here
instantiated at the coefficient universe `Type u` of the module sections rather than at
`Type (u + 1)`. The right Kan extensions involved exist there because the sites of an algebraic
stack are essentially small in `u`.

The identity is not registered under `@[stacks 07AT]`: Stacks 07AT is a separate
statement, and its parts are registered elsewhere.

## References

* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Subsite

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)
  [EssentiallySmall.{u} X]
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- The pullback of sheaves of modules along a four-field morphism of ringed topoi depends only on
its morphism of topoi and its inverse-image structure map. -/
theorem _root_.Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules_congr
    {X : RingedTopos.{w, v, u}} {Y : RingedTopos.{w, v, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (f g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
    (h₁ : f.toToposHom = g.toToposHom) (h₂ : HEq f.fSharpInverseImage g.fSharpInverseImage) :
    f.pullbackModules = g.pullbackModules := by
  obtain ⟨a, b, c, d⟩ := f
  obtain ⟨a', b', c', d'⟩ := g
  cases h₁
  cases h₂
  rfl

/-- **`g^* = g^{-1}` on sheaves of modules for a full subsite**, at the spelling of the pullback
whose left adjoint is `AlgebraicGeometry.Stack.subsiteModuleLowerShriek`: pullback of sheaves of
modules along the morphism of ringed topoi of a full subsite is restriction of sheaves of modules
along the inclusion. This is `AlgebraicGeometry.Stack.subsiteModulePullbackIso` across
`AlgebraicGeometry.Stack.subsiteRingedToposHom_toModulesHom`. -/
def subsiteModulePullbackIsoRestriction :
    subsiteModulePullback B S hS p hp τ hτ P ≅
      Stacks.SheafOfModules.inverseImage.{u} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι (ringStructureSheafCore B S hS p hp τ hτ) :=
  eqToIso (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules_congr
      (subsiteRingedToposHom B S hS p hp τ hτ P).toModulesHom
      (subsiteRingedToposModulesHom B S hS p hp τ hτ P) rfl
      (heq_of_eq (RingedToposHom.fSharpInverseImageRing_eq_ringFsharpInverseImage
        (subsiteRingedToposHom B S hS p hp τ hτ P)))) ≪≫
    subsiteModulePullbackIso B S hS p hp τ hτ P

/-- The adjunction `g_! ⊣ g^{-1}` of **Stacks 0789** on sheaves of modules for a full subsite, with
`g^{-1}` read as restriction along the inclusion. -/
def subsiteModuleLowerShriekAdjunctionRestriction :
    subsiteModuleLowerShriek B S hS p hp τ hτ P ⊣
      Stacks.SheafOfModules.inverseImage.{u} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι (ringStructureSheafCore B S hS p hp τ hτ) :=
  (subsiteModuleLowerShriekAdjunction B S hS p hp τ hτ P).ofNatIsoRight
    (subsiteModulePullbackIsoRestriction B S hS p hp τ hτ P)

end Subsite

section Kan

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u} C]
  {D : Type (u + 1)} [Category.{u} D] (F : C ⥤ D)

/-- Restriction along a functor out of an essentially small category with values in a category
with all limits of size `u` admits pointwise right Kan extensions. -/
theorem hasPointwiseRightKanExtension_of_essentiallySmall (A : Type*) [Category A]
    [HasLimitsOfSize.{u, u} A] (G : Cᵒᵖ ⥤ A) : F.op.HasPointwiseRightKanExtension G :=
  fun Y => by
    have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Y F.op) A
    infer_instance

/-- The forgetful functor from abelian groups to sets preserves the limits computing right Kan
extensions along a functor out of an essentially small category. -/
theorem preservesLimitsOfShape_structuredArrow_forget (Y : Dᵒᵖ) :
    PreservesLimitsOfShape (StructuredArrow Y F.op) (forget AddCommGrpCat.{u}) :=
  preservesLimitsOfShape_of_equiv (equivSmallModel.{u} (StructuredArrow Y F.op)).symm _

end Kan

section General

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  (P : ObjectProperty 𝒳.val.val.obj) (Q : ObjectProperty 𝒴.val.val.obj)
  (hPQ : ∀ x : P.FullSubcategory, Q (f.hom.hom.toFunctor.obj x.obj))
  [P.ι.IsContinuous (subsiteTopology B S hS 𝒳.val.val.p τ P)
    (associatedTopology B S hS 𝒳.val.val.p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS 𝒳.val.val.p τ P)
    (associatedTopology B S hS 𝒳.val.val.p τ)]
  [Q.ι.IsContinuous (subsiteTopology B S hS 𝒴.val.val.p τ Q)
    (associatedTopology B S hS 𝒴.val.val.p τ)]
  [Q.ι.IsCocontinuous (subsiteTopology B S hS 𝒴.val.val.p τ Q)
    (associatedTopology B S hS 𝒴.val.val.p τ)]
  [(SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ).IsContinuous
    (subsiteTopology B S hS 𝒳.val.val.p τ P) (subsiteTopology B S hS 𝒴.val.val.p τ Q)]
  [(SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ).IsCocontinuous
    (subsiteTopology B S hS 𝒳.val.val.p τ P) (subsiteTopology B S hS 𝒴.val.val.p τ Q)]

omit [P.ι.IsCocontinuous (subsiteTopology B S hS 𝒳.val.val.p τ P)
    (associatedTopology B S hS 𝒳.val.val.p τ)]
  [Q.ι.IsCocontinuous (subsiteTopology B S hS 𝒴.val.val.p τ Q)
    (associatedTopology B S hS 𝒴.val.val.p τ)]
  [(SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ).IsContinuous
    (subsiteTopology B S hS 𝒳.val.val.p τ P) (subsiteTopology B S hS 𝒴.val.val.p τ Q)]
  [(SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ).IsCocontinuous
    (subsiteTopology B S hS 𝒳.val.val.p τ P) (subsiteTopology B S hS 𝒴.val.val.p τ Q)] in
/-- The structure presheaf of rings of a subsite of the source is the restriction along the
restricted 1-morphism of the one of the subsite of the target. -/
theorem subsiteRing_obj_eq :
    (Stacks.SheafOfModules.inverseImageRing (subsiteTopology B S hS 𝒳.val.val.p τ P)
        (associatedTopology B S hS 𝒳.val.val.p τ) P.ι
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ)).obj =
      (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ).op ⋙
        (Stacks.SheafOfModules.inverseImageRing (subsiteTopology B S hS 𝒴.val.val.p τ Q)
          (associatedTopology B S hS 𝒴.val.val.p τ) Q.ι
          (ringStructureSheafCore B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ)).obj :=
  congrArg (fun G => P.ι.op ⋙ G)
    (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ hτ)

/-- **The identity `g'_!(f')^{-1} = f^{-1}g_!` of Stacks 07AT on sheaves of modules, for a
general pair of full subsites**, given the identity `f'_*(g')^{-1} = g^{-1}f_*` on sheaves of
sets objectwise, at the universe of the sections. -/
def subsiteModuleShriekBaseChangeIso
    (H : ∀ (G : (𝒳.val.val.obj)ᵒᵖ ⥤ Type u),
      Presieve.IsSheaf (associatedTopology B S hS 𝒳.val.val.p τ) G →
      ∀ y : Q.FullSubcategory,
        letI := hasPointwiseRightKanExtension_of_essentiallySmall
          (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ) (Type u)
        letI := hasPointwiseRightKanExtension_of_essentiallySmall f.hom.hom.toFunctor (Type u)
        Function.Bijective
          (((SubsitePushforward.subsiteRanBaseChange.{_, _, _, _, u} f.hom.hom.toFunctor P
            hPQ).app G).app (op y))) :
    letI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f τ).1
    _root_.SheafOfModules.pushforward.{u}
        (F := SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ)
        (ObjectProperty.homMk (eqToHom (subsiteRing_obj_eq B S hS f τ hτ P Q hPQ))) ⋙
        subsiteModuleLowerShriek B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ hτ P ≅
      subsiteModuleLowerShriek B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids τ hτ Q ⋙
        modulePullback B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
          𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ hτ := by
  letI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f τ).1
  letI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f τ).2
  letI := hasPointwiseRightKanExtension_of_essentiallySmall
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ) (Type u)
  letI := hasPointwiseRightKanExtension_of_essentiallySmall f.hom.hom.toFunctor (Type u)
  letI := hasPointwiseRightKanExtension_of_essentiallySmall
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ) AddCommGrpCat.{u}
  letI := hasPointwiseRightKanExtension_of_essentiallySmall f.hom.hom.toFunctor AddCommGrpCat.{u}
  letI := hasPointwiseRightKanExtension_of_essentiallySmall
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ) RingCat.{u}
  letI := hasPointwiseRightKanExtension_of_essentiallySmall f.hom.hom.toFunctor RingCat.{u}
  letI := preservesLimitsOfShape_structuredArrow_forget
    (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor P hPQ)
  letI := preservesLimitsOfShape_structuredArrow_forget f.hom.hom.toFunctor
  refine Stacks.SheafOfModules.restrictionCompLowerShriekIso
    (J' := subsiteTopology B S hS 𝒳.val.val.p τ P)
    (J := associatedTopology B S hS 𝒳.val.val.p τ)
    (K' := subsiteTopology B S hS 𝒴.val.val.p τ Q)
    (K := associatedTopology B S hS 𝒴.val.val.p τ)
    (hsq := SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor P hPQ)
    (ringStructureSheafCore_obj_eq B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
      𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom) τ hτ)
    (subsiteRing_obj_eq B S hS f τ hτ P Q hPQ)
    (subsiteModuleLowerShriekAdjunctionRestriction B S hS 𝒴.val.val.p
      𝒴.val.isFiberedInGroupoids τ hτ Q)
    (subsiteModuleLowerShriekAdjunctionRestriction B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ hτ P) ?_
  intro M V'
  rw [isIso_iff_bijective]
  exact H _ ((isSheaf_iff_isSheaf_of_type _ _).mp
    ((sheafCompose (associatedTopology B S hS 𝒳.val.val.p τ) (forget AddCommGrpCat.{u})).obj
      ((_root_.SheafOfModules.toSheaf _).obj M)).property) V'.unop

end General

/-! ### The lisse-étale site -/

namespace LisseEtale

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsSmooth B S hS f)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Stacks 07AT (1), the identity `g'_!(f')^{-1} = f^{-1}g_!` on sheaves of modules.** For a
smooth 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, restriction of sheaves of modules along the
restriction `f'` of `f` to the lisse-étale sites followed by the lower shriek `g'_!` of
**Stacks 0789** (1) for `𝒳` is the lower shriek `g_!` for `𝒴` followed by the inverse image
`f^{-1}` of sheaves of modules on the étale sites of **Stacks 06WE**. -/
def moduleShriekBaseChangeIso :
    letI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      (etaleTopology B)).1
    letI := isContinuous_subsiteFunctor B S hS f hf
    letI := isCocontinuous_subsiteFunctor B S hS f hf
    _root_.SheafOfModules.pushforward.{u}
        (F := SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
          (smoothObject.{u, w} B S hS 𝒳) (smoothObject_map.{u, w} B S hS f hf))
        (ObjectProperty.homMk (eqToHom (subsiteRing_obj_eq B S hS f (etaleTopology B)
          (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳)
          (smoothObject.{u, w} B S hS 𝒴) (smoothObject_map.{u, w} B S hS f hf)))) ⋙
        subsiteModuleLowerShriek B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒳) ≅
      subsiteModuleLowerShriek B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          (etaleTopology B) (etaleTopology_le_topology B) (smoothObject.{u, w} B S hS 𝒴) ⋙
        AlgebraicGeometry.Stack.modulePullback B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) (etaleTopology B)
          (etaleTopology_le_topology B) :=
  letI := isContinuous_subsiteFunctor B S hS f hf
  letI := isCocontinuous_subsiteFunctor B S hS f hf
  subsiteModuleShriekBaseChangeIso B S hS f (etaleTopology B) (etaleTopology_le_topology B)
    (smoothObject.{u, w} B S hS 𝒳) (smoothObject.{u, w} B S hS 𝒴)
    (smoothObject_map.{u, w} B S hS f hf) fun G hG y =>
      letI := hasPointwiseRightKanExtension_of_essentiallySmall
        (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
          (smoothObject_map.{u, w} B S hS f hf)) (Type u)
      letI := hasPointwiseRightKanExtension_of_essentiallySmall f.hom.hom.toFunctor (Type u)
      letI := hasPointwiseRightKanExtension_of_essentiallySmall
        ((smoothObject.{u, w} B S hS 𝒳).ι ⋙ f.hom.hom.toFunctor) (Type u)
      SubsitePushforward.bijective_subsiteRanBaseChange_app_app.{_, _, _, _, _, _, u}
        𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor (smoothObject.{u, w} B S hS 𝒳)
        (ambientChoiceOfPullbacks B S hS 𝒴) (smoothObject_map.{u, w} B S hS f hf)
        𝒴.val.isFiberedInGroupoids f.hom.hom.w y G
        (ambientTwoFibreProductTopology B S hS f y .etale)
        (isSheaf_comp_ambientProjection B S hS f y .etale G hG)
        (hasLocalFactorizations_primedInclusion B S hS f y)
        (hasLocallyConnectedFactorizations_primedInclusion B S hS f y)

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
  (hf : AlgebraicStacks.IsFlat B S hS f)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Stacks 07AT (2), the identity `g'_!(f')^{-1} = f^{-1}g_!` on sheaves of modules.** For a
flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, restriction of sheaves of modules along the
restriction `f'` of `f` to the flat-fppf sites followed by the lower shriek `g'_!` of
**Stacks 0789** (2) for `𝒳` is the lower shriek `g_!` for `𝒴` followed by the inverse image
`f^{-1}` of sheaves of modules on the fppf sites of **Stacks 06WE**. -/
def moduleShriekBaseChangeIso :
    letI := (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f
      B.topology).1
    letI := isContinuous_subsiteFunctor B S hS f hf
    letI := isCocontinuous_subsiteFunctor B S hS f hf
    _root_.SheafOfModules.pushforward.{u}
        (F := SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor
          (objectProperty B S hS 𝒳) (flatObject_map B S hS f hf))
        (ObjectProperty.homMk (eqToHom (subsiteRing_obj_eq B S hS f B.topology le_rfl
          (objectProperty B S hS 𝒳) (objectProperty B S hS 𝒴) (flatObject_map B S hS f hf)))) ⋙
        subsiteModuleLowerShriek B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          B.topology le_rfl (objectProperty B S hS 𝒳) ≅
      subsiteModuleLowerShriek B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
          B.topology le_rfl (objectProperty B S hS 𝒴) ⋙
        AlgebraicGeometry.Stack.modulePullback B S hS 𝒳.val.val.p
          𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
          (CatFiberedInGroupoids.homFunctor_comp_p f.hom) B.topology le_rfl :=
  letI := isContinuous_subsiteFunctor B S hS f hf
  letI := isCocontinuous_subsiteFunctor B S hS f hf
  subsiteModuleShriekBaseChangeIso B S hS f B.topology le_rfl
    (objectProperty B S hS 𝒳) (objectProperty B S hS 𝒴)
    (flatObject_map B S hS f hf) fun G hG y =>
      letI := hasPointwiseRightKanExtension_of_essentiallySmall
        (SubsitePushforward.subsiteFunctor f.hom.hom.toFunctor (objectProperty B S hS 𝒳)
          (flatObject_map B S hS f hf)) (Type u)
      letI := hasPointwiseRightKanExtension_of_essentiallySmall f.hom.hom.toFunctor (Type u)
      letI := hasPointwiseRightKanExtension_of_essentiallySmall
        ((objectProperty B S hS 𝒳).ι ⋙ f.hom.hom.toFunctor) (Type u)
      SubsitePushforward.bijective_subsiteRanBaseChange_app_app.{_, _, _, _, _, _, u}
        𝒳.val.val.p 𝒴.val.val.p f.hom.hom.toFunctor (objectProperty B S hS 𝒳)
        (ambientChoiceOfPullbacks B S hS 𝒴) (flatObject_map B S hS f hf)
        𝒴.val.isFiberedInGroupoids f.hom.hom.w y G
        (ambientTwoFibreProductTopology B S hS f y .fppf)
        (isSheaf_comp_ambientProjection B S hS f y .fppf G hG)
        (hasLocalFactorizations_primedInclusion B S hS f y)
        (hasLocallyConnectedFactorizations_primedInclusion B S hS f y)

end FlatFppf

end AlgebraicGeometry.Stack

end

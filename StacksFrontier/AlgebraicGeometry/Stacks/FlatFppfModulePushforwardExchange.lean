module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquareSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardIndexComparison

/-!
# The identity `g^{-1}f_* = f'_*(g')^{-1}` of Stacks 07AT (2) on sheaves of modules

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, let
`g : Sh(𝒴_{flat,fppf}) ⟶ Sh(𝒴_{fppf})` and `g' : Sh(𝒳_{flat,fppf}) ⟶ Sh(𝒳_{fppf})` be the
morphisms of topoi of Stacks 0788 (2), and let `f'` be the restriction of `f` to the flat-fppf
sites, the site functor of the first assertion of Stacks 07AT (2). The square
```
  𝒳_{flat} --g'--> 𝒳_{fppf}
     |f'              |f
     v                v
  𝒴_{flat} --g-->  𝒴_{fppf}
```
commutes, and **Stacks 07AT** (2) asserts `f'_*(g')^{-1} = g^{-1}f_*`. This file proves that
identity on **sheaves of modules**, as an isomorphism of functors, with sections in the universe
of the structure sheaf and no hypothesis.

The comparison is `Stacks.SheafOfModules.squareComparison`, the base change of right Kan
extensions of Stacks 0FN1 for the square with the structure maps of Stacks 06TW. Its component
at a flat object `y` of `𝒴` is restriction of compatible families of sections along the
comparison functor of index categories
(`Stacks.SheafOfModules.isIso_squareComparison_app_of_bijective`), and that restriction is
bijective for a sheaf by
`CategoryTheory.SubsitePushforward.bijective_sectionsPrecomp_structuredArrowDownwards`, whose
geometric inputs — the sheaf condition on the 2-fibre product `V ×_{y, 𝒴} 𝒳` and the two
local-factorization conditions of Stacks 07AK for its flat objects — are
`AlgebraicGeometry.Stack.isSheaf_comp_ambientProjection`,
`AlgebraicGeometry.Stack.FlatFppf.hasLocalFactorizations_primedInclusion` and
`AlgebraicGeometry.Stack.FlatFppf.hasLocallyConnectedFactorizations_primedInclusion`.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isIso_moduleSquareComparison_app`: the comparison
  `g^{-1}f_*M ⟶ f'_*(g')^{-1}M` is an isomorphism at every sheaf of modules `M`.
* `AlgebraicGeometry.Stack.FlatFppf.moduleInverseImageCompPushforwardIso`: Stacks 07AT (2), the
  identity `g^{-1}f_* ≅ f'_*(g')^{-1}` on sheaves of modules.
* `AlgebraicGeometry.Stack.FlatFppf.lowerShriekCompInverseImageIso`: Stacks 07AT (2), the second
  identity `f^{-1}g_! ≅ g'_!(f')^{-1}` on sheaves of modules, for any choice of the four left
  adjoints.

## References

* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

universe u w

namespace FlatFppf

attribute [local instance] isContinuous_inclusion_topology isCocontinuous_inclusion_topology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f)

/-- Continuity of the underlying functor of a 1-morphism for the fppf sites, as a local
instance. -/
local instance instIsContinuousHomFunctorFppf :
    f.hom.hom.toFunctor.IsContinuous (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) :=
  (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f B.topology).1

/-- Cocontinuity of the underlying functor of a 1-morphism for the fppf sites, as a local
instance. -/
local instance instIsCocontinuousHomFunctorFppf :
    f.hom.hom.toFunctor.IsCocontinuous (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) :=
  (isContinuous_and_isCocontinuous_homFunctor_associatedTopology B S hS f B.topology).2

/-- Right Kan extensions of presheaves with values in a category with limits indexed by
essentially small categories exist along a functor between essentially small categories whose
objects lie in `Type (u + 1)` and morphisms in `Type u`. -/
local instance instHasPointwiseRightKanExtensionSmall {X : Type (u + 1)} [Category.{u} X]
    {Y : Type (u + 1)} [Category.{u} Y] [EssentiallySmall.{u} X] [EssentiallySmall.{u} Y]
    {A : Type (u + 1)} [Category.{u} A] [HasLimitsOfSize.{u, u} A]
    (F : X ⥤ Y) (G : Xᵒᵖ ⥤ A) : F.op.HasPointwiseRightKanExtension G := fun Z => by
  have := hasLimitsOfShape_of_essentiallySmall.{u} (StructuredArrow Z F.op) A
  infer_instance

/-- **The comparison `g^{-1}f_*M ⟶ f'_*(g')^{-1}M` is an isomorphism**, for a flat 1-morphism
`f` of algebraic stacks and every sheaf of modules `M` on the fppf site of the source, with
sections in the universe of the structure sheaf. -/
theorem isIso_moduleSquareComparison_app
    (M : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :
    haveI : (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳)
      (topology B S hS 𝒴) := siteFunctor_isCocontinuous B S hS f hf
    IsIso ((squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf))).app M) := by
  have : (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳)
    (topology B S hS 𝒴) := siteFunctor_isCocontinuous B S hS f hf
  refine isIso_squareComparison_app_of_bijective _ _ M fun V' => ?_
  exact SubsitePushforward.bijective_sectionsPrecomp_structuredArrowDownwards 𝒳.val.val.p
    𝒴.val.val.p f.hom.hom.toFunctor (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)
    𝒴.val.isFiberedInGroupoids f.hom.hom.w (ambientChoiceOfPullbacks B S hS 𝒴) V'.unop
    (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u})
    (ambientTwoFibreProductTopology B S hS f V'.unop .fppf)
    (isSheaf_comp_ambientProjection B S hS f V'.unop .fppf _
      (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget M))
    (hasLocalFactorizations_primedInclusion B S hS f V'.unop)
    (hasLocallyConnectedFactorizations_primedInclusion B S hS f V'.unop)

/-- The direct image `f'_*` of sheaves of modules along the restriction `f'` of a flat
1-morphism to the flat-fppf sites, with sections in the universe of the structure sheaf, for the
structure map `(f')^♯` that the square of Stacks 07AT (2) forces. -/
abbrev restrictedModulePushforwardU :
    _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒴) :=
  haveI : (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳)
    (topology B S hS 𝒴) := siteFunctor_isCocontinuous B S hS f hf
  pushforwardCocontinuous.{u} (primedSiteFunctor B S hS f hf)
    (structureMapSquare (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor
        (flatObject B S hS 𝒳.val) (flatObject_map B S hS f hf)))

/-- **Stacks 07AT (2), the identity `g^{-1}f_* = f'_*(g')^{-1}`, on sheaves of modules.** For a
flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, restricting the direct image `f_*M` of a sheaf
of modules on the fppf site of `𝒳` to the flat-fppf site of `𝒴` is the direct image along the
restriction `f'` of `f` of the restriction of `M` to the flat-fppf site of `𝒳`, naturally in `M`.
It is the inverse of the comparison `Stacks.SheafOfModules.squareComparison` of Stacks 0FN1, which
is invertible by `AlgebraicGeometry.Stack.FlatFppf.isIso_moduleSquareComparison_app`. -/
def moduleInverseImageCompPushforwardIso :
    inverseImage.{u} (topology B S hS 𝒳) (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (objectProperty B S hS 𝒳).ι (ambientRingStructureSheaf B S hS 𝒳) ⋙
      restrictedModulePushforwardU B S hS f hf ≅
      pushforwardCocontinuous.{u} f.hom.hom.toFunctor
          (structureMapHomFunctor B S hS B.topology le_rfl f) ⋙
        inverseImage.{u} (topology B S hS 𝒴) (associatedTopology B S hS 𝒴.val.val.p B.topology)
          (objectProperty B S hS 𝒴).ι (ambientRingStructureSheaf B S hS 𝒴) := by
  haveI : (primedSiteFunctor B S hS f hf).IsCocontinuous (topology B S hS 𝒳)
    (topology B S hS 𝒴) := siteFunctor_isCocontinuous B S hS f hf
  haveI : ∀ M, IsIso ((squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
      (structureMapHomFunctor B S hS B.topology le_rfl f)
      (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
        (flatObject_map B S hS f hf))).app M) :=
    isIso_moduleSquareComparison_app B S hS f hf
  haveI := NatIso.isIso_of_isIso_app (squareComparison (J' := topology B S hS 𝒳)
    (K' := topology B S hS 𝒴) (structureMapHomFunctor B S hS B.topology le_rfl f)
    (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)))
  exact (asIso (squareComparison (J' := topology B S hS 𝒳) (K' := topology B S hS 𝒴)
    (structureMapHomFunctor B S hS B.topology le_rfl f)
    (SubsitePushforward.subsiteFunctor_comp_ι f.hom.hom.toFunctor (flatObject B S hS 𝒳.val)
      (flatObject_map B S hS f hf)))).symm

/-- **Stacks 07AT (2), the identity `g'_!(f')^{-1} = f^{-1}g_!`, on sheaves of modules**, for any
choice of the four left adjoints. Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks, `g_!`
and `g'_!` left adjoints of the restrictions `g^{-1}`, `(g')^{-1}` of sheaves of modules to the
flat-fppf sites of `𝒴` and `𝒳`, and `f^{-1}`, `(f')^{-1}` left adjoints of the direct images
`f_*`, `f'_*` along `f` and along its restriction `f'` to the flat-fppf sites. Then
`f^{-1} ∘ g_! ≅ g'_! ∘ (f')^{-1}`.

Both composites are left adjoint to the two sides of
`AlgebraicGeometry.Stack.FlatFppf.moduleInverseImageCompPushforwardIso`, so uniqueness of left
adjoints identifies them. -/
def lowerShriekCompInverseImageIso
    {Lg : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒴)}
    (adjg : Lg ⊣ inverseImage.{u} (topology B S hS 𝒴)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) (objectProperty B S hS 𝒴).ι
      (ambientRingStructureSheaf B S hS 𝒴))
    {Lg' : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳) ⥤
      _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (adjg' : Lg' ⊣ inverseImage.{u} (topology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) (objectProperty B S hS 𝒳).ι
      (ambientRingStructureSheaf B S hS 𝒳))
    {Lf : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)}
    (adjf : Lf ⊣ pushforwardCocontinuous.{u} f.hom.hom.toFunctor
      (structureMapHomFunctor B S hS B.topology le_rfl f))
    {Lf' : _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒴) ⥤
      _root_.SheafOfModules.{u} (subsiteRingStructureSheaf B S hS 𝒳)}
    (adjf' : Lf' ⊣ restrictedModulePushforwardU B S hS f hf) :
    Lg ⋙ Lf ≅ Lf' ⋙ Lg' :=
  (adjg.comp adjf).leftAdjointUniq
    ((adjf'.comp adjg').ofNatIsoRight (moduleInverseImageCompPushforwardIso B S hS f hf))

end FlatFppf

end AlgebraicGeometry.Stack

end

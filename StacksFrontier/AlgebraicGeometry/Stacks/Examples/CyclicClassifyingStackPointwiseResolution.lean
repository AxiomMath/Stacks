module

public import StacksFrontier.AlgebraicGeometry.Stacks.Examples.CyclicClassifyingStackPointwise
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFreeModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative

/-!
# An injective resolution of `𝒪` on the pointwise quotient `[S/_p(ℤ/pℤ)]`

Restriction of modules from `𝒳 = [S/(ℤ/pℤ)]` to its dense subsite `𝒫 = [S/_p(ℤ/pℤ)]` is an
equivalence
(`Stacks.Examples.UnboundedDerivedPushforward.isEquivalence_cyclicPointwiseRestriction`),
so it carries an injective resolution `𝒪_𝒳 → I^•` to an injective resolution of the restriction
of `𝒪_𝒳`. Its sections over an object `x` of `𝒫` are the sections of `I^•` over the image of `x`
in `𝒳`; when `x` lies over an affine scheme, the higher cohomology of `𝒪_𝒳` vanishes there
(Stacks 08IY's opening vanishing), so these sections are exact away from degree `0`. This is the
acyclicity input to the computation of `H^m(𝒳, 𝒪_𝒳)` by Čech cochains in Stacks 07DC.

## Main results

* `CategoryTheory.InjectiveResolution.mapOfPreservesHomology`: an additive functor preserving
  homology and injective objects carries an injective resolution to an injective resolution.
* `CategoryTheory.InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex_of_exactAt`:
  exactness away from degree `0` of the `ℤ`-graded image of a resolution, from exactness of the
  `ℕ`-graded one in positive degrees.
* `Stacks.Examples.UnboundedDerivedPushforward.cyclicPointwiseInjectiveResolution`: the
  restriction of an injective resolution of `𝒪_𝒳` to `𝒫`.
* `exactAt_evaluation_cyclicPointwiseInjectiveResolution` (in the namespace
  `Stacks.Examples.UnboundedDerivedPushforward`): its sections over an object lying over an affine
  scheme are exact away from degree `0`.

## References

* [Stacks Project, Tag 07DC](https://stacks.math.columbia.edu/tag/07DC)
* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  AlgebraicGeometry.Stack.enoughInjectives_fppfSiteModules_of_essentiallySmall
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

namespace CategoryTheory.InjectiveResolution

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

/-- **An additive functor preserving homology and injective objects carries an injective
resolution of `X` to an injective resolution of `G.obj X`**: the image of the resolution, with
the image of its augmentation. -/
@[simps! cocomplex]
def mapOfPreservesHomology (G : C ⥤ D) [G.Additive] [G.PreservesHomology]
    [G.PreservesInjectiveObjects] {X : C} (I : InjectiveResolution X) :
    InjectiveResolution (G.obj X) where
  cocomplex := (G.mapHomologicalComplex _).obj I.cocomplex
  injective _ := G.injective_obj _
  ι := (HomologicalComplex.singleMapHomologicalComplex G _ 0).inv.app X ≫
    (G.mapHomologicalComplex _).map I.ι
  quasiIso := inferInstance

/-- **The `ℤ`-graded image of an injective resolution is exact away from degree `0`** as soon as
the `ℕ`-graded image is exact in every positive degree: in negative degrees the extension by zero
vanishes, and in positive degrees it is the `ℕ`-graded complex. -/
theorem exactAt_mapHomologicalComplex_cochainComplex_of_exactAt (G : C ⥤ D) [G.Additive]
    {X : C} (I : InjectiveResolution X)
    (h : ∀ n : ℕ, 0 < n → ((G.mapHomologicalComplex _).obj I.cocomplex).ExactAt n)
    (q : ℤ) (hq : q ≠ 0) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex).ExactAt q := by
  rcases lt_or_gt_of_ne hq with hlt | hgt
  · exact HomologicalComplex.ExactAt.of_isZero
      (G.map_isZero (I.cochainComplex.isZero_of_isStrictlyGE 0 q hlt))
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℤ) = q := ⟨q.toNat, by omega⟩
    refine HomologicalComplex.ExactAt.of_iso ?_
      (Stacks.DerivedIndexing.mapExtendIso G ComplexShape.embeddingUpNat I.cocomplex)
    exact (HomologicalComplex.extend_exactAt_iff _ ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f m)).2 (h m (by omega))

end CategoryTheory.InjectiveResolution

namespace Stacks.Examples.UnboundedDerivedPushforward

variable (p : ℕ) [NeZero p] {k : Type u} [Field k] (𝒞 : BigFppfSite.{u})
  (hS : 𝒞.Contains (Spec (.of (Polynomial k))))

/-- **The restriction to `[S/_p(ℤ/pℤ)]` of an injective resolution of `𝒪_𝒳`**: restriction of
modules is an equivalence, so it carries injective resolutions to injective resolutions. -/
def cyclicPointwiseInjectiveResolution
    (R : InjectiveResolution (SheafOfModules.unit (cyclicStackRing p 𝒞 hS))) :
    InjectiveResolution
      ((cyclicPointwiseRestriction p 𝒞 hS).obj (SheafOfModules.unit (cyclicStackRing p 𝒞 hS))) :=
  haveI : PreservesFiniteLimits (cyclicPointwiseRestriction p 𝒞 hS) := inferInstance
  haveI : PreservesFiniteColimits (cyclicPointwiseRestriction p 𝒞 hS) :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _
      (cyclicPointwiseRestriction p 𝒞 hS)
      (cyclicPointwiseRestriction p 𝒞 hS).asEquivalence.toAdjunction.leftAdjoint_preservesColimits
  haveI : (cyclicPointwiseRestriction p 𝒞 hS).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_isEquivalence
  R.mapOfPreservesHomology (cyclicPointwiseRestriction p 𝒞 hS)

/-- The complex of the restricted resolution is the restriction of the complex. -/
@[simp]
theorem cyclicPointwiseInjectiveResolution_cocomplex
    (R : InjectiveResolution (SheafOfModules.unit (cyclicStackRing p 𝒞 hS))) :
    (cyclicPointwiseInjectiveResolution p 𝒞 hS R).cocomplex =
      ((cyclicPointwiseRestriction p 𝒞 hS).mapHomologicalComplex _).obj R.cocomplex :=
  rfl

/-- **The sections of the restricted resolution over an object lying over an affine scheme are
exact away from degree `0`.** They are the sections of the resolution of `𝒪_𝒳` over the image of
the object in `𝒳`, whose cohomology is the higher fppf cohomology of `𝒪_𝒳` there, which vanishes
(`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`,
`𝒪_𝒳` lying in `LQCoh^fbc(𝒪_𝒳)`). -/
theorem exactAt_evaluation_cyclicPointwiseInjectiveResolution
    (R : InjectiveResolution (SheafOfModules.unit (cyclicStackRing p 𝒞 hS)))
    (x : (cyclicPointwise p 𝒞 hS).obj)
    (hx : IsAffine ((BigFppfOver.toScheme 𝒞 _ hS).obj ((cyclicPointwise p 𝒞 hS).p.obj x)))
    (q : ℤ) (hq : q ≠ 0) :
    (((_root_.SheafOfModules.evaluation (cyclicPointwiseRing p 𝒞 hS) (op x)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cyclicPointwiseInjectiveResolution p 𝒞 hS R).cochainComplex).ExactAt
        q := by
  refine InjectiveResolution.exactAt_mapHomologicalComplex_cochainComplex_of_exactAt _ _
    (fun n hn => ?_) q hq
  have hz := Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack 𝒞
    𝒞.toBigEtaleSite rfl _ hS (cyclicClassifyingStack.{u, u} p 𝒞 hS)
    (SheafOfModules.unit (cyclicStackRing p 𝒞 hS))
    (Stack.isLocallyQuasicoherentWithSheafFlatBaseChange_unit 𝒞 𝒞.toBigEtaleSite rfl _ hS
      (cyclicStackModel p 𝒞 hS).p (isFiberedInGroupoids_cyclicStackModel p 𝒞 hS))
    ((cyclicPointwiseInclusion p 𝒞 hS).obj x) hx n hn
  have : (_root_.SheafOfModules.evaluation.{u} (cyclicStackRing p 𝒞 hS)
      (op ((cyclicPointwiseInclusion p 𝒞 hS).obj x))).Additive :=
    Stacks.SheafOfModulesEvaluation.evaluation_additive _ _
  have h₂ : (((_root_.SheafOfModules.evaluation (cyclicStackRing p 𝒞 hS)
      (op ((cyclicPointwiseInclusion p 𝒞 hS).obj x))).mapHomologicalComplex _).obj
        R.cocomplex).ExactAt n :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ n).2
      (hz.of_iso (R.isoRightDerivedObj (_root_.SheafOfModules.evaluation.{u}
        (cyclicStackRing p 𝒞 hS) (op ((cyclicPointwiseInclusion p 𝒞 hS).obj x))) n).symm)
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff] at h₂ ⊢
  exact h₂

end Stacks.Examples.UnboundedDerivedPushforward

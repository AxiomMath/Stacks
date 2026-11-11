module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleDegreeLimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafModulesGrothendieck
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback of sheaves of graded modules, and the adjunction

Let `f : (C, J, R) ⟶ (C', J', R')` be a morphism of ringed sites, presented as a functor
`u : C' ⥤ C` in the direction opposite to `f` together with the structure map `σ : R' ⟶ f_*R`,
let `A` be a sheaf of graded `R`-algebras, let `B` be a sheaf of graded `R'`-algebras and let
`φ : B ⟶ f_*A` be a homomorphism of sheaves of graded algebras. The direct image
`f_* : Mod(A) ⥤ Mod(B)` is constructed in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedPushforward.lean`, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullback.lean` derives, from a
`SheafOfModules.GradedModule.PullbackData` for `φ` — a pullback `f^*N` of every right graded
`B`-module together with its unit and the universal property of the unit — the identification

`Hom_{Mod^gr(B)}(N, f_*M) = Hom_{Mod^gr(A)}(f^*N, M)`

of [Stacks, Tag 0FR8](https://stacks.math.columbia.edu/tag/0FR8) in every homogeneous degree.

This file builds such a datum, so that the identification holds under the hypotheses of the
source alone: `f_*` **has a left adjoint**, and the pullback is its value.

## Main definitions

* `SheafOfModules.GradedModule.pullbackData` is the pullback of every right graded `B`-module at
  once, with its unit and the universal property of the unit, and
  `SheafOfModules.GradedModule.pullbackFunctor` is the resulting pullback functor
  `f^* : Mod(B) ⥤ Mod(A)`.

## Main results

* `SheafOfModules.GradedModule.preservesLimitsOfSize_pushforwardFunctor`: **the direct image of
  sheaves of graded modules preserves all limits** of the size of the module universe.
* `SheafOfModules.GradedModule.isRightAdjoint_pushforwardFunctor`: **the direct image of sheaves
  of graded modules has a left adjoint.**
* `SheafOfModules.GradedModule.pullbackHomOfDegreeEquiv`:
  `Hom^n(f^*N, M) = Hom^n(N, f_*M)` in every homogeneous degree `n`, for the pullback built
  here as the left adjoint of `f_*`; `SheafOfModules.GradedModule.pullbackPushforwardAdjunction`
  is its degree-zero case read as an adjunction `f^* ⊣ f_*`. Both are the defining adjunction
  of that left adjoint read in every degree; the statement of Tag 0FR8 itself, for the explicit
  pullback `f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`, is
  `SheafOfModules.GradedTensorPullback.tensorPullbackHomOfDegreeEquiv` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullbackTensor.lean`.

## Implementation notes

**How the pullback is obtained.** A `PullbackData` for `φ` is exactly a pointwise left adjoint
of `f_*`: by `SheafOfModules.GradedModule.semilinearHomEquiv` a `φ`-semilinear homomorphism
`N ⟶ P` of right graded modules is a homomorphism `N ⟶ f_*P` of right graded `B`-modules, so a
module `f^*N` carrying a universal semilinear homomorphism out of `N` is a module corepresenting
`P ↦ (N ⟶ f_*P)`. The existence of that left adjoint is the special adjoint functor theorem,
`CategoryTheory.isRightAdjoint_of_preservesLimits_of_isCoseparating`, whose hypotheses are all
available: right graded `A`-modules form a Grothendieck abelian category
([Stacks, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD),
`SheafOfModules.GradedModule.isGrothendieckAbelian`), which gives local smallness,
well-poweredness and a coseparator; they have all limits of the size of the module universe
([Stacks, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)); and `f_*` preserves those
limits. The unit of the adjunction, read as a semilinear homomorphism, is the unit of the
pullback, and the universal property of the unit is the hom-bijection of the adjunction.

**Why `f_*` preserves limits.** Limits of graded modules are formed degreewise, so taking the
degree-`n` piece preserves them (`pieceFunctor_preservesLimitsOfSize`, Tag 0FR0) and the family
of all pieces reflects isomorphisms and hence limits. The degree-`n` piece of `f_*M` is the
direct image `f_*(M^n)` of the degree-`n` piece on the nose — that is
`pushforwardFunctor_comp_pieceFunctor` — and the direct image of sheaves of modules preserves
limits of the size of the module universe, `SheafOfModules.preservesLimitsOfSize_pushforward`,
because limits of sheaves of modules are computed in `AddCommGrpCat`-valued sheaves, where the
direct image is restriction along `u.op`.

**The explicit pullback `f^{-1}N ⊗_{f^{-1}B, φ} A`** is not used here: the pullback of this
file is whatever left adjoint `f_*` has, so the identification of hom-sets below holds by
construction. The explicit construction of the source, the inverse image `f⁻¹N` tensored with
`A` over `f⁻¹B`, together with the identification of Tag 0FR8 for it, is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModulePullbackTensor.lean`, at a continuous,
representably flat and final functor of small sites in one universe, the setting in which the
inverse image of sheaves of modules is formed in this development.
The same composite along a morphism of ringed topoi, the inverse image `f⁻¹N` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleInverseImage.lean` tensored with `A`
over `f⁻¹B` and read as a right graded `A`-module over `O_C`, is
`Stacks.Sheaves.GradedModuleToposPullback.pullbackFunctor` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedModuleToposPullback.lean`.

**Universes.** The module universe is `max u v a u' v' a' w` for sites `C : Type u` with
`Category.{v} C` and `C' : Type u'` with `Category.{v'} C'` and algebra pieces in
`SheafOfModules.{a} R`, `SheafOfModules.{a'} R'`, with `w` free. This is forced by Tag 0FRD,
which holds at a module universe dominating its site and algebra universes, and here *both*
sites must be dominated at once because the two categories of graded modules share their module
universe: `SheafOfModules.pushforward` preserves it. The sheafification hypotheses are those of
Tag 0FRD on each of the two sites.

## References

* [Stacks Project, Tag 0FR8](https://stacks.math.columbia.edu/tag/0FR8)
* [Stacks Project, Tag 0FR7](https://stacks.math.columbia.edu/tag/0FR7)
* [Stacks Project, Tag 0FRD](https://stacks.math.columbia.edu/tag/0FRD)
* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a w v u a' v' u'

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : GradedAlgebra.{t, a} R} {B : GradedAlgebra.{t, a'} R'}

/-- The direct image of sheaves of graded modules, read in a fixed degree, is the direct image
of the degree-`n` piece. -/
theorem pushforwardFunctor_comp_pieceFunctor (φ : GradedAlgebra.SemilinearHom u σ B A) (n : ℤ) :
    pushforwardFunctor.{t, a, max u v a u' v' a' w} φ ⋙ pieceFunctor B n =
      pieceFunctor.{t, a, max u v a u' v' a' w} A n ⋙
        (sitePushforward u σ : SheafOfModules.{max u v a u' v' a' w} R ⥤ SheafOfModules.{_} R') :=
  rfl

/-- **The direct image of sheaves of graded modules preserves all limits** of the size of the
module universe: limits of graded modules are formed degreewise, and the direct image of sheaves
of modules preserves limits. -/
theorem preservesLimitsOfSize_pushforwardFunctor
    (φ : GradedAlgebra.SemilinearHom u σ B A) :
    PreservesLimitsOfSize.{max u v a u' v' a' w, max u v a u' v' a' w}
      (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ) := by
  refine ⟨fun {I} _ => ?_⟩
  have hpieces : PreservesLimitsOfShape I (pieceFunctors.{max u v a u' v' a' w} B) :=
    preservesLimitsOfShape_of_evaluation _ _ fun n =>
      preservesLimitsOfShape_of_natIso (pieceFunctorsCompEval.{max u v a u' v' a' w} B n.as).symm
  have hcomp : PreservesLimitsOfShape I
      (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ ⋙
        pieceFunctors.{max u v a u' v' a' w} B) :=
    preservesLimitsOfShape_of_evaluation _ _ fun n =>
      preservesLimitsOfShape_of_natIso
        (F := pieceFunctor.{t, a, max u v a u' v' a' w} A n.as ⋙
          (sitePushforward u σ :
            SheafOfModules.{max u v a u' v' a' w} R ⥤ SheafOfModules.{_} R')) (Iso.refl _)
  have : ReflectsLimitsOfShape I (pieceFunctors.{max u v a u' v' a' w} B) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (pieceFunctors.{max u v a u' v' a' w} B)

section Adjoint

variable [HasWeakSheafify J (Type max u v a u' v' a' w)]
  [HasSheafify J AddCommGrpCat.{max u v a u' v' a' w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v a u' v' a' w}]
  [HasWeakSheafify J' (Type max u v a u' v' a' w)]
  [HasSheafify J' AddCommGrpCat.{max u v a u' v' a' w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v a u' v' a' w}]

/-- **The direct image of sheaves of graded modules has a left adjoint.** -/
theorem isRightAdjoint_pushforwardFunctor (φ : GradedAlgebra.SemilinearHom u σ B A) :
    (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ).IsRightAdjoint := by
  have hA : IsGrothendieckAbelian.{max u v a u' v' a' w}
      (GradedModule.{t, a, max u v a u' v' a' w} A) :=
    isGrothendieckAbelian.{max u' v' a' w, a, t, v, u} A
  have hB : IsGrothendieckAbelian.{max u v a u' v' a' w}
      (GradedModule.{t, a', max u v a u' v' a' w} B) :=
    isGrothendieckAbelian.{max u v a w, a', t, v', u'} B
  have hpres : PreservesLimitsOfSize.{max u v a u' v' a' w, max u v a u' v' a' w}
      (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ) :=
    preservesLimitsOfSize_pushforwardFunctor.{t, a, w, v, u, a', v', u'} φ
  exact isRightAdjoint_of_preservesLimits_of_isCoseparating.{max u v a u' v' a' w}
    (isCoseparator_coseparator (GradedModule.{t, a, max u v a u' v' a' w} A)) _

/-- **The pullback of every right graded `B`-module at once**: the module `f^*N`, the unit
`N ⟶ f^*N` and the universal property of the unit, as the datum
`SheafOfModules.GradedModule.PullbackData`. The pullback is the value of the left adjoint of the
direct image, and the unit is the unit of that adjunction read as a `φ`-semilinear
homomorphism. -/
noncomputable def pullbackData (φ : GradedAlgebra.SemilinearHom u σ B A) :
    PullbackData.{t, a, max u v a u' v' a' w} φ :=
  letI : (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ).IsRightAdjoint :=
    isRightAdjoint_pushforwardFunctor.{t, a, w, v, u, a', v', u'} φ
  letI adj := Adjunction.ofIsRightAdjoint (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ)
  { obj := fun N => (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ).leftAdjoint.obj N
    unit := fun N => (semilinearHomEquiv φ N _).symm (adj.unit.app N)
    isPullback := fun N => by
      have hbridge : ∀ {P' : GradedModule.{t, a, max u v a u' v' a' w} A}
          (h : (pushforwardFunctor.{t, a, max u v a u' v' a' w} φ).leftAdjoint.obj N ⟶ P'),
          semilinearHomEquiv φ N P'
              (((semilinearHomEquiv φ N _).symm (adj.unit.app N)).postcomp h) =
            adj.homEquiv N P' h := by
        intro P' h
        refine (SemilinearHom.semilinearHomEquiv_postcomp _ h).trans ?_
        refine Eq.trans (congrArg (fun z => z ≫ pushforwardMap φ h)
          ((semilinearHomEquiv φ N _).apply_symm_apply (adj.unit.app N))) ?_
        exact (adj.homEquiv_unit N P' h).symm
      exact
        { desc := fun {P'} θ' => (adj.homEquiv N P').symm (semilinearHomEquiv φ N P' θ')
          fac := fun {P'} θ' => (semilinearHomEquiv φ N P').injective
            ((hbridge _).trans ((adj.homEquiv N P').apply_symm_apply _))
          uniq := fun {P'} θ' h hh => (adj.homEquiv N P').injective
            (((hbridge h).symm.trans (congrArg (semilinearHomEquiv φ N P') hh)).trans
              ((adj.homEquiv N P').apply_symm_apply _).symm) } }

/-- **The pullback functor `f^* : Mod(B) ⥤ Mod(A)` of sheaves of graded modules**, along a
morphism of ringed sites `f` and a homomorphism `φ : B ⟶ f_*A` of sheaves of graded algebras. -/
noncomputable def pullbackFunctor (φ : GradedAlgebra.SemilinearHom u σ B A) :
    GradedModule.{t, a', max u v a u' v' a' w} B ⥤
      GradedModule.{t, a, max u v a u' v' a' w} A :=
  (pullbackData.{t, a, w, v, u, a', v', u'} φ).functor

/-- For a morphism of ringed sites `f`, a sheaf of graded `R`-algebras `A` on the source, a sheaf
of graded `R'`-algebras `B` on the target and a homomorphism `φ : B ⟶ f_*A` of sheaves of graded
algebras, the homomorphisms `f^*N ⟶ M` of right graded `A`-modules homogeneous of degree `n` are
exactly the homomorphisms `N ⟶ f_*M` of right graded `B`-modules homogeneous of degree `n`, for
the pullback `f^*` obtained as the left adjoint of the direct image:

`Hom_{Mod^gr(B)}(N, f_*M) = Hom_{Mod^gr(A)}(f^*N, M)`

Since `f^*` is defined here as the left adjoint of `f_*`, this is the defining adjunction read
in every homogeneous degree. Tag 0FR8 is the same identification for the explicit pullback
`f^*N = f⁻¹N ⊗_{f⁻¹B, φ} A`, which is
`SheafOfModules.GradedTensorPullback.tensorPullbackHomOfDegreeEquiv`. -/
noncomputable def pullbackHomOfDegreeEquiv (φ : GradedAlgebra.SemilinearHom u σ B A)
    (N : GradedModule.{t, a', max u v a u' v' a' w} B)
    (M : GradedModule.{t, a, max u v a u' v' a' w} A) (n : ℤ) :
    GradedHomOfDegree ((pullbackFunctor.{t, a, w, v, u, a', v', u'} φ).obj N) M n ≃
      GradedHomOfDegree N (pushforwardObj φ M) n :=
  (pullbackData.{t, a, w, v, u, a', v', u'} φ).homOfDegreeEquiv N M n

/-- **The pullback of sheaves of graded modules is left adjoint to the direct image**, which is
the degree-zero case of `pullbackHomOfDegreeEquiv` read as an adjunction. -/
noncomputable def pullbackPushforwardAdjunction (φ : GradedAlgebra.SemilinearHom u σ B A) :
    pullbackFunctor.{t, a, w, v, u, a', v', u'} φ ⊣
      pushforwardFunctor.{t, a, max u v a u' v' a' w} φ :=
  (pullbackData.{t, a, w, v, u, a', v', u'} φ).pullbackPushforwardAdjunction

end Adjoint

end GradedModule

end SheafOfModules

end

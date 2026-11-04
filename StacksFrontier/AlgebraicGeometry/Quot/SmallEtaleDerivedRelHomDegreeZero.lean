module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedRelHomDegreeZeroBijection
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedPullbackCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomSupplement

/-!
# The degree-zero step of the relative Hom functor on algebraic spaces

For the inverse image of `𝒪`-modules along morphisms of algebraic spaces,
`AlgebraicGeometry.Space.toposPullbackData`, with the derived pullbacks `Lg^*` and their
comparisons `Lg^* ∘ Q ⟶ Q ∘ g^*` of Stacks 06YY, the comparison
`CategoryTheory.PullbackData.singleComparison` at an object placed in degree zero is the
comparison `AlgebraicGeometry.Space.smallEtaleDerivedPullbackQComparison` from the derived to the
degreewise pullback of the complex `N[0]`, read through `g^*(N[0]) = (g^*N)[0]`.  With the
degreewise pullback spelled through `AlgebraicGeometry.Space.modulePullback`, as in the base
change map of Stacks 08JQ, it is the comparison
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackQComparison` followed by an isomorphism.

So the morphism `CategoryTheory.PullbackData.relHomDegreeZero` of relative Hom functors sends `ψ`
to the image of `ψ ≫ smallEtaleDerivedModulePullbackQComparison` under a bijection; in particular
it is bijective at a test object exactly when composing with that comparison is.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `smallEtaleDegreeZeroTargetIso`: `Q(g^*(N[0])) ≅ (g^*N)[0]`, the degreewise pullback spelled
  through `modulePullback` on the left.

## Main results

* `smallEtaleDerivedPullbackQComparison_eq_complexComparison`: the comparison from the derived to
  the degreewise pullback is `CategoryTheory.PullbackData.complexComparison`.
* `singleComparison_toposPullbackData_eq`: the comparison of `Lg^*` at `N[0]` is the comparison
  from the derived to the degreewise pullback of `N[0]`, followed by `g^*(N[0]) = (g^*N)[0]`.
* `smallEtaleDerivedModulePullbackQComparison_single_comp`: the same, with the degreewise
  pullback spelled through `modulePullback`.
* `relHomDegreeZero_toposPullbackData_app_apply`: the value of `relHomDegreeZero` at `ψ`.
* `bijective_relHomDegreeZero_toposPullbackData_app_iff`: `relHomDegreeZero` is bijective at a
  test object exactly when composing with `smallEtaleDerivedModulePullbackQComparison` is.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/- The derived pullbacks of algebraic spaces are stated on the standard model of the derived
category, so the comparisons with them must be too. -/
attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The comparison from the derived to the degreewise pullback of a complex is the comparison
`CategoryTheory.PullbackData.complexComparison` of the inverse image of modules. -/
theorem smallEtaleDerivedPullbackQComparison_eq_complexComparison {X X' : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) (K : CochainComplex (toposModules B S hS X) ℤ) :
    smallEtaleDerivedPullbackQComparison g K =
      (toposPullbackData B S hS).complexComparison
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) g K :=
  rfl

/-- **The comparison of `Lg^*` at an object placed in degree zero** is the comparison from the
derived to the degreewise pullback of `N[0]`, followed by `g^*(N[0]) = (g^*N)[0]`. -/
theorem singleComparison_toposPullbackData_eq {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (N : toposModules B S hS X) :
    (toposPullbackData B S hS).singleComparison
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) g N =
      smallEtaleDerivedPullbackQComparison g
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          ((toposPullbackData B S hS).pull g) (ComplexShape.up ℤ) 0).hom.app N) :=
  PullbackData.singleComparison_eq_complexComparison_comp _ _ _ g N

/-- **`Q(g^*(N[0])) ≅ (g^*N)[0]`**, with the degreewise pullback on the left spelled through
`AlgebraicGeometry.Space.modulePullback` and the pullback on the right that of the pullback
datum `AlgebraicGeometry.Space.toposPullbackData`. -/
def smallEtaleDegreeZeroTargetIso {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
    (N : toposModules B S hS X) :
    (DerivedCategory.Q.obj
        (((modulePullback B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N)) :
          DerivedCategory (toposModules B S hS X')) ≅
      (DerivedCategory.singleFunctor (toposModules B S hS X') 0).obj
        (((toposPullbackData B S hS).pull g).obj N) :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (modulePullback B S hS g)
        (ComplexShape.up ℤ) 0).app N) ≪≫
    (DerivedCategory.singleFunctor (toposModules B S hS X') 0).mapIso
      ((pullbackModulesIsoModulePullback B S hS g).app N).symm

/-- **The comparison of `Lg^*` at an object placed in degree zero, with the degreewise pullback
spelled through `modulePullback`**: it is the comparison
`smallEtaleDerivedModulePullbackQComparison` of Stacks 08JQ at `N[0]`, followed by
`smallEtaleDegreeZeroTargetIso`. -/
theorem smallEtaleDerivedModulePullbackQComparison_single_comp {X X' : AlgebraicSpaces B S hS}
    (g : X' ⟶ X) (N : toposModules B S hS X) :
    smallEtaleDerivedModulePullbackQComparison g
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≫
        (smallEtaleDegreeZeroTargetIso g N).hom =
      (toposPullbackData B S hS).singleComparison
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) g N := by
  let F := (smallEtaleRingedToposHom B S hS g).toModulesHom.pullbackModules
  let G' : type_of% F := modulePullback B S hS g
  have : G'.Additive := modulePullback_additive g
  have key :=
    HomologicalComplex.mapHomologicalComplex_hom_app_single_comp_singleMapHomologicalComplex_hom_app
      (F := F) (G := G') (pullbackModulesIsoModulePullback B S hS g) (ComplexShape.up ℤ) 0 N
  have key' : (NatIso.mapHomologicalComplex (F := F) (G := G')
        (pullbackModulesIsoModulePullback B S hS g)
        (ComplexShape.up ℤ)).hom.app ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex G' (ComplexShape.up ℤ) 0).hom.app N ≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        ((pullbackModulesIsoModulePullback B S hS g).inv.app N) =
      (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N := by
    rw [reassoc_of% key, ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.comp_id]
  have h2 := congrArg DerivedCategory.Q.map key'
  rw [Functor.map_comp, Functor.map_comp] at h2
  rw [singleComparison_toposPullbackData_eq, ← h2]
  refine (Category.assoc _ _ _).trans ?_
  rfl

section RelHom

variable {I : Type*} [Category* I] {π : I ⥤ AlgebraicSpaces B S hS} {X : AlgebraicSpaces B S hS}
  (κ : PullbackData.ConeTo π X) (E : toposDerived B S hS X) {F : toposModules B S hS X}
  (α : E ⟶ (DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj F)
  [hZ : ∀ i : I, ((smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj E).IsLE 0]
  [hθ : ∀ i : I, IsIso ((toposPullbackData B S hS).degreeZeroCompare
    (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) κ E α i)]

/-- **The degree-zero step on algebraic spaces**: `relHomDegreeZero` sends
`ψ : L(κ i)^*E ⟶ L(κ i)^*(G[0])` to the image under the degree-zero bijection of `ψ` followed by
the comparison `smallEtaleDerivedModulePullbackQComparison` of Stacks 08JQ at `G[0]` and by
`smallEtaleDegreeZeroTargetIso`. -/
theorem relHomDegreeZero_toposPullbackData_app_apply (G : toposModules B S hS X) (i : I)
    (ψ : (smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj E ⟶
      (smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj
        ((DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj G)) :
    ((toposPullbackData B S hS).relHomDegreeZero
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
        (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
        (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
        (hid := fun X => isIso_smallEtaleDerivedIdLift X) κ E α
        (toposPullbackData_isCoherent B S hS) G).app (Opposite.op i) ψ =
      (toposPullbackData B S hS).degreeZeroHomEquiv
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f) κ E α i G
        (ψ ≫ smallEtaleDerivedModulePullbackQComparison (κ.leg i)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) ≫
          (smallEtaleDegreeZeroTargetIso (κ.leg i) G).hom) := by
  rw [smallEtaleDerivedModulePullbackQComparison_single_comp]
  rfl

/-- **The degree-zero step of the bijectivity on algebraic spaces**: `relHomDegreeZero` is
bijective at a test object exactly when composing with the comparison
`smallEtaleDerivedModulePullbackQComparison` of Stacks 08JQ at `G[0]` is. -/
theorem bijective_relHomDegreeZero_toposPullbackData_app_iff (G : toposModules B S hS X) (i : I) :
    Function.Bijective (((toposPullbackData B S hS).relHomDegreeZero
        (fun f => smallEtaleDerivedModulePullback B S hS f)
        (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
        (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
        (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
        (hid := fun X => isIso_smallEtaleDerivedIdLift X) κ E α
        (toposPullbackData_isCoherent B S hS) G).app (Opposite.op i)) ↔
      Function.Bijective (fun ψ : (smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj E ⟶
          (smallEtaleDerivedModulePullback B S hS (κ.leg i)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS X) 0).obj G) =>
        ψ ≫ smallEtaleDerivedModulePullbackQComparison (κ.leg i)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) := by
  rw [PullbackData.bijective_relHomDegreeZero_app_iff (toposPullbackData B S hS)
    (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
    (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
    (hid := fun X => isIso_smallEtaleDerivedIdLift X) κ E α
    (toposPullbackData_isCoherent B S hS) G i,
    ← smallEtaleDerivedModulePullbackQComparison_single_comp]
  exact Iso.bijective_comp_comp_hom_iff _ _

end RelHom

end AlgebraicGeometry.Space

end

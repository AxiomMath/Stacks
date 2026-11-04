module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageLeray
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite

/-!
# Cohomology of a direct image with no higher direct images, over an affine base

Let `A` be a ring, `V` an object of the big fppf site over `Spec A` and `g : X ⟶ V` a morphism of
algebraic spaces over `Spec A`.  For a morphism `h : Y ⟶ X` and an `𝒪_Y`-module `𝒩` whose higher
direct images `R^q h_*𝒩`, `q > 0`, vanish,

`H^i(X, h_*𝒩) ≅ H^i(Y, 𝒩)`

as `A`-modules, in every degree.  This is the degeneration of the Leray spectral sequence of
`h` ([Stacks, Tag 0733]), read through the cohomology along `g` and along `h ≫ g` over the
identity chart of `V`.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyRestrictScalarsIsoPushforwardEvaluation`: the cohomology
  `H^i(X, F)`, read as an `A`-module, is the cohomology along `g` read over the identity chart
  of `V`.  This is the identification behind
  `AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper` ([Stacks, Tag 08AS]), as an
  isomorphism.
* `AlgebraicGeometry.Space.cohomologyRestrictScalarsIsoOfAcyclic`: **`H^i(X, h_*𝒩) ≅ H^i(Y, 𝒩)`
  as `A`-modules**, when the higher direct images of `𝒩` along `h` vanish.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {hA : B.Contains (Spec (.of A))}
    (V : BigFppfOver B (Spec (.of A)) hA)

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The cohomology of `X` over the base ring is the cohomology along `g : X ⟶ V` over the
identity chart of `V`**, as `A`-modules: global sections on `X` are the sections over `V` of the
direct image along `g` (`AlgebraicGeometry.Space.globalSectionsOverBaseIso`), and restriction of
scalars and the universe lift are exact, so they pass through the right derived functors. -/
def cohomologyRestrictScalarsIsoPushforwardEvaluation {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (g : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
      AlgebraicSpaces B (Spec (.of A)) hA))
    (F : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2) (i : ℕ) :
    haveI := modulePushforward_additive B (Spec (.of A)) hA g
    haveI : (SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA (yoneda.obj V)
          (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O)
        (op (idEtaleChart B (Spec (.of A)) hA V))).Additive := ⟨fun {_ _ _ _} => rfl⟩
    (ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived i).obj F) ≅
      (ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
          ModuleCat.uliftFunctor.{u + 1} A).obj
        (((modulePushforward B (Spec (.of A)) hA g ⋙
          SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA (yoneda.obj V)
              (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O)
            (op (idEtaleChart B (Spec (.of A)) hA V))).rightDerived i).obj F) := by
  have := modulePushforward_additive B (Spec (.of A)) hA g
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
    (yoneda.obj V) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O)
  have : (SheafOfModules.evaluation.{u} O (op (idEtaleChart B (Spec (.of A)) hA V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X.1 X.2)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits
      (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X.1 X.2)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X.1 X.2)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let E := ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
    ModuleCat.uliftFunctor.{u + 1} A
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V)) :=
    ⟨fun _ _ _ => ⟨fun {_} => inferInstance⟩⟩
  have : PreservesFiniteLimits E := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits E := comp_preservesFiniteColimits _ _
  have : E.PreservesHomology := Functor.preservesHomologyOfExact _
  let Q := modulePushforward B (Spec (.of A)) hA g ⋙
    SheafOfModules.evaluation.{u} O (op (idEtaleChart B (Spec (.of A)) hA V))
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
  exact ((Functor.rightDerivedCompIso Γ
      (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X.1 X.2)) i).app F).symm ≪≫
    (Functor.rightDerivedIsoOfNatIso
      (F := Γ ⋙ ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X.1 X.2)) (G := Q ⋙ E)
      (globalSectionsOverBaseIso V g) i).app F ≪≫
    (Functor.rightDerivedCompIso Q E i).app F

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The cohomology of a direct image with no higher direct images**: for `h : Y ⟶ X` and an
`𝒪_Y`-module `𝒩` with `R^q h_*𝒩 = 0` for `q > 0`, `H^i(X, h_*𝒩) ≅ H^i(Y, 𝒩)` as `A`-modules, in
every degree.  Both sides are read along the morphisms `g` and `h ≫ g` to `V` by
`AlgebraicGeometry.Space.cohomologyRestrictScalarsIsoPushforwardEvaluation`, where they are
identified by the degeneration of the Leray spectral sequence of `h`,
`AlgebraicGeometry.Space.pushforwardEvaluationRightDerivedCompIso`. -/
def cohomologyRestrictScalarsIsoOfAcyclic {X Y : AlgebraicSpaces B (Spec (.of A)) hA}
    (g : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
      AlgebraicSpaces B (Spec (.of A)) hA)) (h : Y ⟶ X)
    (N : Modules.{u, u} B (Spec (.of A)) hA Y.1 Y.2)
    (hN : ∀ q, 0 < q → IsZero (((modulePushforward B (Spec (.of A)) hA h).rightDerived q).obj N))
    (i : ℕ) :
    (ModuleCat.restrictScalars (baseRingHom A B hA X.1 X.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)).rightDerived i).obj
          ((modulePushforward B (Spec (.of A)) hA h).obj N)) ≅
      (ModuleCat.restrictScalars (baseRingHom A B hA Y.1 Y.2)).obj
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B (Spec (.of A)) hA Y.1 Y.2).O)).rightDerived i).obj N) :=
  cohomologyRestrictScalarsIsoPushforwardEvaluation V g _ i ≪≫
    (ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
      ModuleCat.uliftFunctor.{u + 1} A).mapIso
      (pushforwardEvaluationRightDerivedCompIso B (Spec (.of A)) hA
        (isTerminalIdEtaleChart B (Spec (.of A)) hA V) h g N hN i).symm ≪≫
    (cohomologyRestrictScalarsIsoPushforwardEvaluation V (h ≫ g) N i).symm

end AlgebraicGeometry.Space

end

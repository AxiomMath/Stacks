module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PushforwardInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology along a flat affine morphism of algebraic spaces

For a flat affine morphism `f : X ⟶ Y` of algebraic spaces and a quasi-coherent `𝒪_X`-module `𝓕`,
the derived functors of `Γ(Y, f_*−)` evaluated at `𝓕` are the cohomology of `f_*𝓕` on `Y`.

## Main results

* `AlgebraicGeometry.Space.preservesInjectiveObjects_modulePushforward_of_isFlat`: the direct
  image along a flat morphism carries injective `𝒪_X`-modules to injective `𝒪_Y`-modules.
* `AlgebraicGeometry.Space.acyclicPushforwardOfInjective_of_isFlat`: the direct image along a flat
  morphism of an injective `𝒪_X`-module has vanishing higher cohomology on `Y`.
* `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsFlatOfIsAffineHom`: for a flat affine `f` and
  a quasi-coherent `𝓕`, `R^i Γ(Y, f_*−) 𝓕 ≅ H^i(Y, f_*𝓕)` for every `i`.

## References

* [Stacks Project, Lemma 69.6.3 (Tag 0D2U)](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Lemma 69.3.3 (Tag 073H)](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Lemma 21.13.5 (Tag 0730)](https://stacks.math.columbia.edu/tag/0730)
* [Stacks Project, Lemma 21.13.3 (Tag 072Z)](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The direct image along a flat morphism `f : X ⟶ Y` of algebraic spaces carries injective
`𝒪_X`-modules to injective `𝒪_Y`-modules. -/
@[stacks 0730 "for a flat morphism of algebraic spaces, on the small étale ringed topoi",
  sga "4 V 4.9" "clause 3"]
theorem preservesInjectiveObjects_modulePushforward_of_isFlat (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) :
    (modulePushforward B S hS f).PreservesInjectiveObjects := by
  rw [← pushforwardModules_eq_modulePushforward B S hS f]
  exact ⟨fun {Z} hZ => @RingedToposHom.pushforwardModules_injective _ _ _ _ _
    (smallEtaleRingedToposHom B S hS f)
    ((isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS f).1 hf) Z hZ⟩

/-- The direct image along a flat morphism `f : X ⟶ Y` of algebraic spaces of an injective
`𝒪_X`-module has vanishing higher cohomology on `Y`. -/
theorem acyclicPushforwardOfInjective_of_isFlat (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) :
    AcyclicPushforwardOfInjective B S hS f := by
  have henough := enoughInjectives_modules B S hS Y.1 Y.2
  have := preservesInjectiveObjects_modulePushforward_of_isFlat B S hS f hf
  intro Z (_ : Injective Z)
  have := Functor.injective_obj (modulePushforward B S hS f) Z
  exact Stacks.RightDerivedComp.acyclic_of_injective (globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)) _

/-- Let `f : X ⟶ Y` be a flat affine morphism of algebraic spaces over `S` and `𝓕` a
quasi-coherent `𝒪_X`-module. Then for every `i` the `i`-th right derived functor of `Γ(Y, f_*−)`
at `𝓕` is isomorphic to the `i`-th cohomology of `f_*𝓕` on `Y`.

Here the acyclicity of the direct image of an injective module is reached through Stacks 0730;
it holds without flatness (`AlgebraicGeometry.Space.acyclicPushforwardOfInjective`), and the
isomorphism for any affine morphism is `AlgebraicGeometry.Space.cohomologyCollapseIsoOfIsAffineHom`
(Stacks 0D2U). -/
def cohomologyCollapseIsoOfIsFlatOfIsAffineHom (f : X ⟶ Y) (haff : IsAffineHom B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have := enoughInjectives_modules B S hS Y.1 Y.2
    (((modulePushforward B S hS f ⋙ globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).obj F ≅
      ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived i).obj
        ((modulePushforward B S hS f).obj F)) :=
  cohomologyCollapseIsoOfIsAffineHomOfChartwise B S hS f haff F
    (fun n hn => chartwiseIsZeroHigherDirectImage_of_isAffineHom B S hS f haff
      (relativelyRepresentable_of_isAffineHom B S hS f haff) F hF n hn)
    (acyclicPushforwardOfInjective_of_isFlat B S hS f hflat) i

end AlgebraicGeometry.Space

end

end

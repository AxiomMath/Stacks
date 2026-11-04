module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleUnitCompLaw
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMap

/-!
# The spaces side of the naturality square of Stacks 04CS, on the canonical derivations

`AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMap.lean`) compares
two morphisms out of an inverse image of modules.  Transposed across the adjunction of
Stacks 03LU, each side becomes a morphism out of `(Ω_{V/W})^a`, and such a morphism is
determined by its effect on the canonical derivation `d^a` of Stacks 04CS
(`AlgebraicGeometry.Space.eq_of_representedUniversalDerivation`).  This file computes the side
of that square built from the comparison map of Stacks 04CX.

The answer is the expected one: it carries `d^a` of `χ` to the direct image along `ψ̃` of `d^a`
of `ψ ≫ χ`, evaluated on the pulled-back regular function.  Three already-proved
compatibilities are chained — the identification of Stacks 04CS on the derivations, in both
directions, and the characterizing property of the comparison map of Stacks 04CX.

## Main definitions

* `AlgebraicGeometry.Space.representedUniversalDerivationHom`: the canonical derivation `d^a` of
  Stacks 04CS as a morphism of the underlying sheaves of sets, the form in which the direct
  image along a morphism of algebraic spaces applies to it.  This mirrors
  `AlgebraicGeometry.Space.universalDerivationHom` for the universal derivation of Stacks 04CT.

## Main results

* `AlgebraicGeometry.Space.homEquiv_comp_apply_of_eq_universalDerivation`: the step of the
  chain, stated on variables — if a morphism carries a local section to a universal differential
  then, followed by the transpose of a comparison map of Stacks 04CX, it carries that section to
  the direct image of the universal derivation of the source, evaluated on the pulled-back
  function.
* `Space.representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation`:
  **the spaces side of the square, on the canonical derivations.**

## Implementation notes

The direct image of modules along a morphism of algebraic spaces is not a reindexing: its
sections over an object of the small étale site are a limit over the étale scheme charts above a
fibre product (`AlgebraicGeometry.Space.directImageChartProjection`), so there is no formula
turning the direct image of a morphism of modules, read on sections, into that morphism read at
a reindexed object.  The right-hand side is therefore stated with the direct image of the
derivation in its sheaf-of-sets form, which is the form the characterizing property of
Stacks 04CX already produces through
`AlgebraicGeometry.Space.pushforwardUniversalDerivationHom`.

The step lemma is stated on variables rather than on the concrete terms of the application
because `AlgebraicGeometry.Space.representedRelativeDifferentials` is a `SheafOfModules` over
the structure ring sheaf and is not type-correct against `AlgebraicGeometry.Space.Modules` at
the transparency `rw` uses to build a motive; on variables the proof is a chain of `congrArg`
and needs no motive.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U V W : BigFppfOver B S hS}

/-- The canonical derivation `d^a` of Stacks 04CS, on the small étale site of the represented
algebraic space, as a morphism of the underlying sheaves of sets. -/
noncomputable def representedUniversalDerivationHom (α : U ⟶ V) :
    CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1}
        (structureRingSheaf B S hS (schemeSpace U)) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1}
        (structureRingSheaf B S hS (schemeSpace U))
        (representedRelativeDifferentials B S hS α) :=
  CategoryTheory.Sheaf.unaryOpHom (fun _ a ↦ (representedUniversalDerivation B S hS α).d a)
    (fun g a ↦ ((representedUniversalDerivation B S hS α).d_map g a).symm)

/-- `representedUniversalDerivationHom` on a section. -/
theorem representedUniversalDerivationHom_hom_app (α : U ⟶ V)
    (Z : (SmallEtale B S hS (schemeSpace U).1)ᵒᵖ)
    (x : (structureSetSheaf B S hS (schemeSpace U)).obj.obj Z) :
    (representedUniversalDerivationHom B S hS α).hom.app Z x =
      (representedUniversalDerivation B S hS α).d x :=
  rfl

section General

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- One step of the chain, stated on variables: if `J` carries the local section `m` to the
universal differential `d_{X/Y}(t)`, then `J` followed by the adjoint transpose of `c ≫ k`
carries `m` to the direct image of `d_{X'/Y'} ≫ k` evaluated on `f♯ t`. -/
theorem homEquiv_comp_apply_of_eq_universalDerivation (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    {M : Modules.{u, u} B S hS X.1 X.2} {N : Modules.{u, u} B S hS X'.1 X'.2}
    (J : M ⟶ sheafOfDifferentials B S hS p)
    {c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (hc : IsSheafOfDifferentialsMap B S hS f p p' c)
    (k : sheafOfDifferentials B S hS p' ⟶ N)
    (Z : (SmallEtale B S hS X.1)ᵒᵖ) (m : M.val.obj Z)
    (t : (structureRingSheaf B S hS X).obj.obj Z)
    (hJ : J.val.app Z m = (universalDerivation B S hS p).d t) :
    (J ≫ (modulePullbackAdjunction B S hS f).homEquiv
        (sheafOfDifferentials B S hS p) N (c ≫ k)).val.app Z m =
      ((smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p' ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k)).hom.app Z
        ((structureSharpSet B S hS f).hom.app Z t) := by
  have e1 : (J ≫ (modulePullbackAdjunction B S hS f).homEquiv
        (sheafOfDifferentials B S hS p) N (c ≫ k)).val.app Z m =
      ((modulePullbackAdjunction B S hS f).homEquiv
        (sheafOfDifferentials B S hS p) N (c ≫ k)).val.app Z
          ((universalDerivation B S hS p).d t) :=
    congrArg (fun z ↦ ((modulePullbackAdjunction B S hS f).homEquiv
      (sheafOfDifferentials B S hS p) N (c ≫ k)).val.app Z z) hJ
  have e2 : ((modulePullbackAdjunction B S hS f).homEquiv
        (sheafOfDifferentials B S hS p) N (c ≫ k)).val.app Z
          ((universalDerivation B S hS p).d t) =
      ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS p') c ≫
            (modulePushforward B S hS f).map k).val.app Z
          ((universalDerivation B S hS p).d t) :=
    congrArg (fun T ↦ T.val.app Z ((universalDerivation B S hS p).d t))
      ((modulePullbackAdjunction B S hS f).homEquiv_naturality_right c k)
  have e3 : ((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS p') c ≫
            (modulePushforward B S hS f).map k).val.app Z
          ((universalDerivation B S hS p).d t) =
      ((smallEtaleDirectImage B S hS f).map
          ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k)).hom.app Z
        (((smallEtaleDirectImage B S hS f).map
            (universalDerivationHom B S hS p')).hom.app Z
          ((structureSharpSet B S hS f).hom.app Z t)) :=
    congrArg (fun z ↦ ((smallEtaleDirectImage B S hS f).map
        ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k)).hom.app Z z)
      (hc Z t)
  exact e1.trans (e2.trans (e3.trans
    (Sheaf.map_comp_hom_app_apply (smallEtaleDirectImage B S hS f)
      (universalDerivationHom B S hS p')
      ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X')).map k) Z
      ((structureSharpSet B S hS f).hom.app Z t) rfl rfl).symm))

end General

/-- **The derivation chain for the naturality of Stacks 04CS.**  For `ψ : U ⟶ V` and
`χ : V ⟶ W` in the big fppf site over `S`, write `ψ̃ = schemeSpaceMap ψ` and
`χ̃ = schemeSpaceMap χ`.  The comparison map `(Ω_{V/W})^a ⟶ Ω_{χ̃}` of Stacks 04CS, followed by
the adjoint transpose of the comparison map `c_ψ̃ : ψ̃^*Ω_{χ̃} ⟶ Ω_{ψ̃ ≫ χ̃}` of Stacks 04CX
composed with the identification `Ω_{ψ̃ ≫ χ̃} ≅ (Ω_{U/W})^a` of Stacks 04CS, carries the
canonical derivation `d^a` of `χ` to the direct image along `ψ̃` of the canonical derivation
`d^a` of `ψ ≫ χ`, evaluated on the pullback `ψ♯ x` of the regular function `x`. -/
theorem representedDifferentialsComparison_comp_homEquiv_representedUniversalDerivation
    (ψ : U ⟶ V) (χ : V ⟶ W)
    (Z : (SmallEtale B S hS (schemeSpace V).1)ᵒᵖ)
    (x : (structureSetSheaf B S hS (schemeSpace V)).obj.obj Z) :
    (representedDifferentialsComparison B S hS χ ≫
        (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv
          (sheafOfDifferentials B S hS (schemeSpaceMap χ))
          (representedRelativeDifferentials B S hS (ψ ≫ χ))
          (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
            (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom)).val.app Z
        ((representedUniversalDerivation B S hS χ).d x) =
      ((smallEtaleDirectImage B S hS (schemeSpaceMap ψ)).map
          (representedUniversalDerivationHom B S hS (ψ ≫ χ))).hom.app Z
        ((structureSharpSet B S hS (schemeSpaceMap ψ)).hom.app Z x) := by
  have hc : IsSheafOfDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ)
      (schemeSpaceMap ψ ≫ schemeSpaceMap χ)
      (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ)) :=
    isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS (schemeSpaceMap ψ)
      (schemeSpaceMap χ) (schemeSpaceMap ψ ≫ schemeSpaceMap χ) (𝟙 _) (by simp)
  have key : universalDerivationHom B S hS (schemeSpaceMap ψ ≫ schemeSpaceMap χ) ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace U))).map
        (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom =
      representedUniversalDerivationHom B S hS (ψ ≫ χ) :=
    Sheaf.hom_ext_sections fun T y ↦
      sheafOfDifferentialsRepresentedIso_hom_universalDerivation B S hS (ψ ≫ χ) T y
  refine Eq.trans (homEquiv_comp_apply_of_eq_universalDerivation B S hS (schemeSpaceMap ψ)
    (schemeSpaceMap χ) (schemeSpaceMap ψ ≫ schemeSpaceMap χ)
    (representedDifferentialsComparison B S hS χ) hc
    (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom Z _ x
    (representedDifferentialsComparison_representedUniversalDerivation B S hS χ Z x)) ?_
  exact Sheaf.map_hom_app_congr (smallEtaleDirectImage B S hS (schemeSpaceMap ψ)) key Z _

end AlgebraicGeometry.Space

end

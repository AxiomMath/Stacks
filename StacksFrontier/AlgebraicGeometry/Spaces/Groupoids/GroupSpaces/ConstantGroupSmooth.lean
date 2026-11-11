module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.ConstantFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ConstantGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.ActionInSitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.GroupSpaceTranslation

/-!
# The constant group algebraic space over the final algebraic space is étale

Let `G` be an abstract group and `S` a scheme of a big fppf site containing the constant group
scheme `G_S`. The structure morphism `G_S ⟶ S` is étale, being the base change of
`∐_G Spec ℤ ⟶ Spec ℤ`; hence the constant group algebraic space `G_S` over the final algebraic
space (**Stacks 043O**) has a smooth structure morphism, and a proper one when `G` is finite.
For `G` finite and `S` quasi-compact, the big fppf site containing `S` contains `G_S`.

## Main results

* `AlgebraicGeometry.etale_constantGroupScheme`: `G_S ⟶ S` is étale.
* `AlgebraicGeometry.Space.isSmooth_constantGroupSpace_terminal`: the constant group algebraic
  space over the final algebraic space is smooth.
* `AlgebraicGeometry.Space.isProper_constantGroupSpace_terminal`: and proper for `G` finite.
* `AlgebraicGeometry.Space.contains_constantGroupScheme`: the site contains `G_S` for `G` finite
  and `S` quasi-compact.

## References

* [Stacks Project, Tag 043O](https://stacks.math.columbia.edu/tag/043O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (G : Type) [Small.{u} G] [Group G]

/-- The structure morphism `∐_G Spec ℤ ⟶ Spec ℤ` of the constant group scheme over the integers
is étale: it is a coproduct of identities. -/
instance etale_terminal_from_constantSchemeOverIntegers :
    Etale (terminal.from (constantSchemeOverIntegers.{u} G)) := by
  rw [show terminal.from (constantSchemeOverIntegers.{u} G) =
    Sigma.desc (fun _ : G => 𝟙 (⊤_ Scheme.{u})) from terminal.hom_ext _ _]
  haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)

/-- **The constant group scheme `G_S ⟶ S` is étale**, as a base change of the étale morphism
`∐_G Spec ℤ ⟶ Spec ℤ`. -/
instance etale_constantGroupScheme (S : Scheme.{u}) :
    Etale (constantGroupScheme.{u} G S).X.hom :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
    (IsPullback.of_hasPullback (terminal.from (constantSchemeOverIntegers.{u} G))
      (terminal.from S))
    (etale_terminal_from_constantSchemeOverIntegers G)

/-- For a finite group `G` the constant group scheme `G_S ⟶ S` is finite. -/
theorem isFinite_constantGroupScheme [Finite G] (S : Scheme.{u}) :
    IsFinite (constantGroupScheme.{u} G S).X.hom :=
  ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
    inferInstance).1

namespace Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} (hS : 𝒞.Contains S)
  (hG : 𝒞.Contains (constantGroupScheme.{u} G S).X.left)

/-- The underlying algebraic space of the constant group algebraic space over the final
algebraic space is represented by `G_S`, compatibly with the structure morphisms. -/
private theorem constantGroupSpace_terminal_hom_eq :
    ∃ e : (constantGroupSpace 𝒞 S hS G (terminalSpace 𝒞 S hS).obj
        (terminalSpace 𝒞 S hS).property hG).obj.X.left ≅
        yoneda.obj (constantGroupSiteObject 𝒞 S hS G hG),
      (constantGroupSpace 𝒞 S hS G (terminalSpace 𝒞 S hS).obj
        (terminalSpace 𝒞 S hS).property hG).obj.X.hom = e.hom ≫ yoneda.map
          (Over.homMk (constantGroupSiteObject 𝒞 S hS G hG).hom (Category.comp_id _) :
            constantGroupSiteObject 𝒞 S hS G hG ⟶ baseTerminal 𝒞 S hS) :=
  ⟨terminalSpaceProdIso 𝒞 S hS _ ≪≫
      (pointsOnSiteRepresentableBy 𝒞 S hS _
        (constantGroupSiteObjectGrpObj 𝒞 S hS G hG)).toIso.symm,
    (baseTerminal_yonedaIsTerminal 𝒞 S hS).hom_ext _ _⟩

/-- A property of morphisms of schemes which is étale local on source and target and holds for
`G_S ⟶ S` holds on every étale chart of the constant group algebraic space over the final
algebraic space. -/
theorem holdsOnEveryEtaleChart_constantGroupSpace_terminal {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P) (hproj : P (constantGroupScheme.{u} G S).X.hom) :
    HoldsOnEveryEtaleChart 𝒞 S hS P (constantGroupSpace 𝒞 S hS G (terminalSpace 𝒞 S hS).obj
      (terminalSpace 𝒞 S hS).property hG).obj.X.hom := by
  obtain ⟨e, heq⟩ := constantGroupSpace_terminal_hom_eq G hS hG
  rw [heq]
  exact (holdsOnEveryEtaleChart_precomp_iso 𝒞 S hS P _ _).1
    (holdsOnEveryEtaleChart_yoneda_map 𝒞 S hS hP _ hproj)

/-- **The constant group algebraic space over the final algebraic space is smooth.** -/
theorem isSmooth_constantGroupSpace_terminal :
    IsSmooth 𝒞 S hS (constantGroupSpace 𝒞 S hS G (terminalSpace 𝒞 S hS).obj
      (terminalSpace 𝒞 S hS).property hG).obj.X.hom :=
  holdsOnEveryEtaleChart_constantGroupSpace_terminal G hS hG Smooth.isEtaleLocalOnSourceAndTarget
    inferInstance

/-- **The constant group algebraic space of a finite group over the final algebraic space is
proper.** -/
theorem isProper_constantGroupSpace_terminal [Finite G] :
    IsProper 𝒞 S hS (constantGroupSpace 𝒞 S hS G (terminalSpace 𝒞 S hS).obj
      (terminalSpace 𝒞 S hS).property hG).obj.X.hom := by
  have := isFinite_constantGroupScheme (S := S) G
  obtain ⟨e, heq⟩ := constantGroupSpace_terminal_hom_eq G hS hG
  rw [heq]
  exact (isProper_isIso_comp_iff 𝒞 S hS e.hom _).2
    (isProper_yoneda_map 𝒞 S hS _ (inferInstanceAs
      (AlgebraicGeometry.IsProper (constantGroupScheme.{u} G S).X.hom)))

include hS in
/-- **A big fppf site containing a quasi-compact scheme `S` contains the constant group scheme
`G_S` of a finite group**, which is finite over `S`. -/
theorem contains_constantGroupScheme [Finite G] [CompactSpace S] :
    𝒞.Contains (constantGroupScheme.{u} G S).X.left := by
  have := isFinite_constantGroupScheme (S := S) G
  have : CompactSpace (constantGroupScheme.{u} G S).X.left :=
    QuasiCompact.compactSpace_of_compactSpace (constantGroupScheme.{u} G S).X.hom
  exact contains_of_locallyOfFiniteType 𝒞 (U := 𝒞.obj hS)
    (constantGroupScheme.{u} G S).X.hom

end Space

end AlgebraicGeometry

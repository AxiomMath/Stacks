module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomMapLeftConjugate
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMap

/-!
# The naturality square of Stacks 04CS, transposed

`AlgebraicGeometry.Space.SchemeDifferentialsComparisonMapNaturality`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparisonMap.lean`) is the
square which says that the identification of Stacks 04CS between the small Zariski and the small
étale relative differentials of a morphism of schemes of the site is compatible with the
comparison maps of a composable pair.  Both of its sides are morphisms out of an inverse image
of modules, and nothing computes an inverse image on sections.  This file moves the square
across the adjunctions, where both sides become computable, and records the two
determinacy statements that make that move legitimate.

## The two transposes

For `ψ : U ⟶ V` and `χ : V ⟶ W` of the big fppf category over `S`, the square compares two
morphisms `ψ̃^*Ω_{χ̃} ⟶ (Ω_{U/W})^a`.  There are two useful ways to transpose it.

* Across the inverse image of Stacks 03LU alone: by
  `AlgebraicGeometry.Space.eq_of_homEquiv_universalDerivation` the square follows from the
  agreement of the two transposes on the universal differentials `d_{χ̃}(t)` of local sections
  of `𝒪` on the small étale site of the represented algebraic space of `V`.
* Across the whole composite from Zariski modules on the scheme underlying `V`: both sides of
  the square, read with the identification of Stacks 04CS cancelled, are morphisms out of
  `(ψ^*Ω_{V/W})^a`, and by
  `AlgebraicGeometry.Space.eq_of_postcomp_universalRelativeDerivation` the square follows from
  the agreement of the composite transposes on the *Zariski* universal derivation `d_{V/W}`.
  This is the useful one: it lands on sections over the opens of a scheme, which is where the
  pinning of Stacks 03LC (1) is available.

## Main definitions

* `AlgebraicGeometry.Space.representedAssociatedModuleAdjunction`: the transported
  associated-module functor of a represented algebraic space is a left adjoint.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackAdjunction` and
  `AlgebraicGeometry.Space.representedAssociatedModuleSpacePullbackAdjunction`: the two
  composite adjunctions round the square of Stacks 03LC (1).

## Main results

* `AlgebraicGeometry.Space.eq_of_homEquiv_universalDerivation` and
  `AlgebraicGeometry.Space.eq_of_postcomp_universalRelativeDerivation`: the two determinacy
  statements described above.
* `AlgebraicGeometry.Space.homEquiv_representedAssociatedModule_map_schemeChartDifferentialsMap`:
  **the side of the square carrying the Zariski comparison map, transposed.**  It is the
  transpose of that comparison map itself, followed by the unit of the associated-module
  adjunction — so this side of the square is computed by the characterizing property of
  Stacks 01UV, `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d`.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transpose

variable {X X' Y : AlgebraicSpaces B S hS}

/-- **A morphism out of an inverse image of a sheaf of differentials is determined by the
derivation its transpose induces.**  Its transpose is a morphism out of `Ω_p`, and `Ω_p`
corepresents the derivations of Stacks 04CT.

This is the determinacy clause of Stacks 04CX,
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`, with the target freed of the
requirement that it be a sheaf of differentials: that proof never uses it. -/
theorem eq_of_homEquiv_universalDerivation (f : X' ⟶ X) (p : X ⟶ Y)
    {G : Modules.{u, u} B S hS X'.1 X'.2}
    {c₁ c₂ : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶ G}
    (h : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U),
      (((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p) G
          c₁).val.app U).hom ((universalDerivation B S hS p).d t) =
        (((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p) G
          c₂).val.app U).hom ((universalDerivation B S hS p).d t)) :
    c₁ = c₂ := by
  set e := (modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p) G
  have hD : (universalDerivation B S hS p).postcomp (e c₁).val =
      (universalDerivation B S hS p).postcomp (e c₂).val := by
    apply PresheafOfModulesOfCommRing.Derivation.ext
    ext U t
    exact h U t
  obtain ⟨_, _, hu⟩ := universalDerivation_isUniversal B S hS p
    ((modulePushforward B S hS f).obj G)
    ((universalDerivation B S hS p).postcomp (e c₁).val)
  exact e.injective ((hu _ rfl).trans (hu _ hD.symm).symm)

end Transpose

section AssociatedAdjunction

/-- **The transported associated-module functor of a represented algebraic space is a left
adjoint**: it is the associated-module functor of the small étale site of the scheme, which is
one by Stacks 03DU (4), followed by the equivalence of module categories of Stacks 03DX (2). -/
def representedAssociatedModuleAdjunction (U : BigFppfOver B S hS) :
    representedAssociatedModule B S hS U (schemeSpace U).property ⊣
      (representedModuleSiteEquivalence B S hS U).inverse ⋙
        _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).comp
    (representedModuleSiteEquivalence B S hS U).toAdjunction

/-- One composite left adjoint round the square of Stacks 03LC (1): pull a Zariski module back
along the morphism of schemes underlying `ψ`, then transport it to the small étale site of the
represented algebraic space. -/
def representedAssociatedModulePullbackAdjunction {U V : BigFppfOver B S hS} (ψ : U ⟶ V) :
    Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ) ⋙
        representedAssociatedModule B S hS U (schemeSpace U).property ⊣
      ((representedModuleSiteEquivalence B S hS U).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
        Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ) :=
  (Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map ψ)).comp
    (representedAssociatedModuleAdjunction B S hS U)

/-- The other composite left adjoint round the square of Stacks 03LC (1): transport a Zariski
module on the scheme underlying `V` to the small étale site of the represented algebraic space,
then take the inverse image of Stacks 03LU along the represented morphism. -/
def representedAssociatedModuleSpacePullbackAdjunction {U V : BigFppfOver B S hS} (ψ : U ⟶ V) :
    representedAssociatedModule B S hS V (schemeSpace V).property ⋙
        modulePullback B S hS (schemeSpaceMap ψ) ⊣
      modulePushforward B S hS (schemeSpaceMap ψ) ⋙
        ((representedModuleSiteEquivalence B S hS V).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj V) V.left.property) :=
  (representedAssociatedModuleAdjunction B S hS V).comp
    (modulePullbackAdjunction B S hS (schemeSpaceMap ψ))

/-- **A morphism out of the transported pullback `(ψ^*Ω_{V/W})^a` is determined by the Zariski
derivation it induces.**  Morphisms out of it correspond, under the composite adjunction, to
morphisms out of the Zariski sheaf of differentials `Ω_{V/W}`, and those are determined by their
effect on the universal relative derivation of Stacks 01UV. -/
theorem eq_of_postcomp_universalRelativeDerivation {U V W : BigFppfOver B S hS}
    (ψ : U ⟶ V) (χ : V ⟶ W)
    {G : Modules.{u, u} B S hS (schemeSpace U).1 (schemeSpace U).2}
    {u₁ u₂ : (representedAssociatedModule B S hS U (schemeSpace U).property).obj
        ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map ψ)).obj
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))) ⟶ G}
    (h : (Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map χ)).postcomp
          ((representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv _ G u₁).val =
        (Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map χ)).postcomp
          ((representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv _ G u₂).val) :
    u₁ = u₂ :=
  ((representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv _ G).injective
    (Scheme.Hom.eq_of_postcomp_eq_universalRelativeDerivation
      ((BigFppfOver.toScheme B S hS).map χ) h)

/-- **The side of the naturality square of Stacks 04CS carrying the Zariski comparison map,
transposed.**  Across the composite adjunction, the transposed associated module of the Zariski
comparison map of Stacks 01UV is the transpose of that comparison map itself, followed by the
unit of the associated-module adjunction at its target.

Both steps are formal: the transpose across a composite adjunction is the two transposes in
turn, and the inner one is the unit of the associated-module adjunction, which is natural.  The
point of the statement is that its right-hand side is computable: the transpose of the Zariski
comparison map on the universal derivation is the characterizing property of Stacks 01UV,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d`. -/
theorem homEquiv_representedAssociatedModule_map_schemeChartDifferentialsMap
    {U V W : BigFppfOver B S hS} (ψ : U ⟶ V) (χ : V ⟶ W) :
    (representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv
        (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ)) _
        ((representedAssociatedModule B S hS U (schemeSpace U).property).map
          (schemeChartDifferentialsMap B S hS ψ χ)) =
      (Scheme.Modules.pullbackPushforwardAdjunction
            ((BigFppfOver.toScheme B S hS).map ψ)).homEquiv _ _
          (schemeChartDifferentialsMap B S hS ψ χ) ≫
        (Scheme.Modules.pushforward ((BigFppfOver.toScheme B S hS).map ψ)).map
          ((representedAssociatedModuleAdjunction B S hS U).unit.app
            (Scheme.Hom.relativeDifferentials
              ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ)))) := by
  have h1 : (representedAssociatedModuleAdjunction B S hS U).homEquiv _ _
        ((representedAssociatedModule B S hS U (schemeSpace U).property).map
          (schemeChartDifferentialsMap B S hS ψ χ)) =
      schemeChartDifferentialsMap B S hS ψ χ ≫
        (representedAssociatedModuleAdjunction B S hS U).unit.app
          (Scheme.Hom.relativeDifferentials
            ((BigFppfOver.toScheme B S hS).map (ψ ≫ χ))) := by
    rw [Adjunction.homEquiv_unit]
    exact ((representedAssociatedModuleAdjunction B S hS U).unit.naturality
      (schemeChartDifferentialsMap B S hS ψ χ)).symm
  rw [representedAssociatedModulePullbackAdjunction, Adjunction.comp_homEquiv, Equiv.trans_apply,
    h1, Adjunction.homEquiv_naturality_right]

end AssociatedAdjunction

end AlgebraicGeometry.Space

end

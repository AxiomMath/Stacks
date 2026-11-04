module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalLeadingIdentityStack
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent

/-!
# Invertibility of the canonical conormal map descends from represented spaces to schemes

Let
```
R --b--→ R'
|j       |j'
V --a--→ V'
```
be a commutative square of the big fppf site over `S` whose vertical morphisms are immersions of
schemes.  If the canonical map of conormal modules of [Stacks Project, Tag 04CP] of the square
of represented algebraic spaces is an isomorphism, then so is the canonical map
`b^*𝒞_{R'/V'} ⟶ 𝒞_{R/V}` of Morphisms, Lemma [Stacks Project, Tag 01R4] of the square of
schemes.

This is the step of the proof of [Stacks Project, Tag 06BH] that hands condition (2), once it
has been moved to a square of étale charts, to the scheme-level [Stacks Project, Tag 063Y].

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_of_isIso_associatedModule_map`: the associated-module
  functor `𝓕 ↦ 𝓕^a` of the small étale site reflects isomorphisms between quasi-coherent modules.
* `AlgebraicGeometry.Space.isIso_immersionConormalSheafMap_of_isIso_conormalMapOfImmersions`:
  the implication above.

## Route

Part (2) of [Stacks Project, Tag 04G2]
(`AlgebraicGeometry.Space.conormalModuleOfImmersionRepresentedIso_naturality`) writes the
canonical map of the represented square, up to isomorphisms on both sides, as the image of the
scheme-level map under the associated-module functor followed by the equivalence
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`.  The equivalence reflects
isomorphisms, and so does the associated-module functor on quasi-coherent modules, being fully
faithful there ([Stacks Project, Tag 06VE] part (1)); both conormal sheaves are quasi-coherent by
[Stacks Project, Tag 01R2] and [Stacks Project, Tag 01BG].

## References

* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The associated-module functor of the small étale site reflects isomorphisms between
quasi-coherent modules. -/
theorem isIso_of_isIso_associatedModule_map {F G : S.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (φ : F ⟶ G) (h : IsIso ((associatedModule B S hS).map φ)) :
    IsIso φ := by
  let φ' : (⟨F, inferInstance⟩ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
      ⟶ ⟨G, inferInstance⟩ := ObjectProperty.homMk φ
  have : IsIso ((associatedModuleQcoh B S hS).map φ') := h
  have := (fullyFaithfulAssociatedModuleQcoh' B S hS).isIso_of_isIso_map φ'
  exact (inferInstance : IsIso ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map φ'))

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R V R' V' : BigFppfOver B S hS} (j : R ⟶ V) (j' : R' ⟶ V') (b : R ⟶ R') (a : V ⟶ V')
    [hj : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j)]
    [hj' : AlgebraicGeometry.IsImmersion ((BigFppfOver.toScheme B S hS).map j')]

/-- **Condition (2) of Stacks 06BH passes from represented spaces to schemes.**  For a commutative
square `j ≫ a = b ≫ j'` of the big fppf site over `S` whose vertical morphisms `j`, `j'` are
immersions of schemes, if the canonical map of conormal modules of [Stacks Project, Tag 04CP] of
the square of represented algebraic spaces is an isomorphism, then so is the canonical map
`b^*𝒞_{R'/V'} ⟶ 𝒞_{R/V}` of Morphisms, Lemma [Stacks Project, Tag 01R4] of the square of
schemes. -/
theorem isIso_immersionConormalSheafMap_of_isIso_conormalMapOfImmersions
    (hsq : j ≫ a = b ≫ j')
    (h : IsIso (conormalMapOfImmersions B S hS (representedSpaceMap B S hS j)
          (representedSpaceMap B S hS j') (representedSpaceMap B S hS b)
          (representedSpaceMap B S hS a) (isImmersion_representedSpaceMap B S hS j)
          (isImmersion_representedSpaceMap B S hS j')
          (representedSpaceMap_square_of_comp_eq B S hS j j' b a hsq))) :
    IsIso (Stacks.Immersion.immersionConormalSheafMap
                ((BigFppfOver.toScheme B S hS).map j)
                ((BigFppfOver.toScheme B S hS).map j')
                ((BigFppfOver.toScheme B S hS).map b)
                ((BigFppfOver.toScheme B S hS).map a)
                (toShHom_square_of_comp_eq B S hS j j' b a hsq)) := by
  have hnat := conormalModuleOfImmersionRepresentedIso_naturality B S hS j j' b a hsq
  have h₀ := IsIso.comp_isIso' h (Iso.isIso_hom (conormalModuleOfImmersionRepresentedIso B S hS j))
  rw [hnat] at h₀
  have hi : IsIso ((modulePullback B S hS (representedSpaceMap B S hS b)).map
      (conormalModuleOfImmersionRepresentedIso B S hS j').hom) :=
    Iso.isIso_hom ((modulePullback B S hS (representedSpaceMap B S hS b)).mapIso
      (conormalModuleOfImmersionRepresentedIso B S hS j'))
  have h₁ := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hi h₀
  have h₁' := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) h₁
  have h₂ := @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _
    (representedSmallEtaleModuleEquivalence B S hS R).fullyFaithfulFunctor _ _ _ h₁'
  exact @SmallEtale.isIso_of_isIso_associatedModule_map _ _ _ _ _
    (@AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _ _ _
      (Stacks.Conormal.conormalSheaf_isQuasicoherent _))
    (Stacks.Conormal.conormalSheaf_isQuasicoherent _) _ h₂

end AlgebraicGeometry.Space

end

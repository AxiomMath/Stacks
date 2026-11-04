module

public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.DerivedPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeModulePushforward

/-!
# Direct images along arbitrary morphisms under the change of base scheme

Let `h : W ⟶ S` be a morphism of a big fppf site and `φ : X ⟶ Y` an arbitrary morphism of
algebraic spaces over `W`, with lower-shriek extension `Λ_h φ : Λ_h X ⟶ Λ_h Y` over `S`.  The
restrictions `Ψ : Mod(𝒪_{Λ_h X}) ⥤ Mod(𝒪_X)` along the equivalence of small étale sites commute
with direct image of modules and with derived direct image:
`(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ φ_*` and `R(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ Rφ_*`.

For a representable `φ` this is `AlgebraicGeometry.Space.rebaseDerivedPushforwardIso`; in general
the direct image is computed through the spaces-étale sites (Stacks 03G2), and the comparison is
`AlgebraicGeometry.Space.relocalizeModulePushforwardIso`, stated for the restriction along the
equivalence of small étale sites `AlgebraicGeometry.Space.SmallEtale.relocalize`.  The two
equivalences of small étale sites have isomorphic functors, both sending a chart of `X` to its
extension, a chart of `Λ_h X` on the same scheme; the isomorphism is the identity on schemes, so
the two restrictions of modules are isomorphic.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.relocalizeFunctorIso`: the two equivalences of small étale
  sites have isomorphic functors.
* `AlgebraicGeometry.Space.rebaseRestrictionIsoRelocalize`: the two restrictions of modules agree.
* `AlgebraicGeometry.Space.rebaseModuleDirectImageIso`: `(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ φ_*`.
* `AlgebraicGeometry.Space.rebaseDerivedDirectImageIso`: `R(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ Rφ_*`.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- The two equivalences of small étale sites of `F` and of `Λ_h F` have isomorphic functors: both
send a chart of `F` to its extension, a chart of `Λ_h F` on the same scheme. -/
def SmallEtale.relocalizeFunctorIso (F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B W hW F) :
    (SmallEtale.relocalize B hW hS h F hF).functor ≅
      (SmallEtale.relocalizeEquivalence B W S hW hS h F).functor :=
  NatIso.ofComponents (fun V => ObjectProperty.isoMk _ (CostructuredArrow.isoMk (Iso.refl _) (by
      refine (congrArg (· ≫ _) (yoneda.map_id _)).trans ((Category.id_comp _).trans ?_)
      change relocalizeChart B W S hW hS h V.obj.hom =
        yonedaEquiv.symm (OverShriek.relocalizeChartSection h F V.obj)
      rw [relocalizeChart_eq, OverShriek.relocalizeChart_hom]
      congr 1
      rw [← cancel_mono ((OverShriek.relocalizeYonedaIso h).hom.app V.obj.left), Iso.inv_hom_id_app,
        OverShriek.relocalizeYonedaIso_hom]
      refine Eq.trans ?_
        (OverShriek.relocalizeYonedaFactorHom_comp h (W := (Over.map h).obj V.obj.left) rfl).symm
      exact (yoneda.map_id _).symm.trans (congrArg _ (Over.OverMorphism.ext rfl)))))
    (fun k => ObjectProperty.hom_ext (IsEtaleChart B S hS _) (CostructuredArrow.hom_ext _ _
      (Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))))

/-- The two restrictions of modules from `Λ_h X` to `X`, along the two equivalences of small étale
sites, are isomorphic. -/
def rebaseRestrictionIsoRelocalize (X : AlgebraicSpaces B W hW) :
    rebaseRestriction B W S hW hS h X ≅
      (relocalizeModulesEquivalence B hW hS h X.1 X.2).inverse :=
  SheafOfModules.pushforwardNatIso _ (SmallEtale.relocalizeFunctorIso B W S hW hS h X.1 X.2) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext U x
      have e : (relocalizeRingSheafSE B W S hW hS h (relocalizeSpaceSE B W S hW hS h X).2).obj.map
          ((SmallEtale.relocalizeFunctorIso B W S hW hS h X.1 X.2).hom.app U.unop).op = 𝟙 _ := by
        have e0 : (SmallEtale.toOver B S hS _ ⋙ BigFppfOver.toScheme B S hS).map
            ((SmallEtale.relocalizeFunctorIso B W S hW hS h X.1 X.2).hom.app U.unop) = 𝟙 _ :=
          rfl
        change (forget₂ CommRingCat RingCat).map (Scheme.Γ.map
          ((SmallEtale.toOver B S hS _ ⋙ BigFppfOver.toScheme B S hS).map
            ((SmallEtale.relocalizeFunctorIso B W S hW hS h X.1 X.2).hom.app U.unop)).op) = 𝟙 _
        rw [e0]
        exact (congrArg (forget₂ CommRingCat RingCat).map (Scheme.Γ.map_id _)).trans
          (CategoryTheory.Functor.map_id _ _)
      exact congrArg (fun φ => (RingCat.Hom.hom φ) x) e)

variable {X Y : AlgebraicSpaces B W hW} (φ : X ⟶ Y)

/-- **The direct image of modules commutes with the change of base scheme**, for an arbitrary
morphism `φ : X ⟶ Y` of algebraic spaces over `W`: `(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ φ_*`. -/
def rebaseModuleDirectImageIso :
    modulePushforward B S hS (relocalizeHomSE B W S hW hS h φ) ⋙ rebaseRestriction B W S hW hS h Y ≅
      rebaseRestriction B W S hW hS h X ⋙ modulePushforward B W hW φ :=
  Functor.isoWhiskerLeft _ (rebaseRestrictionIsoRelocalize B W S hW hS h Y) ≪≫
    relocalizeModulePushforwardIso B hW hS h φ ≪≫
    Functor.isoWhiskerRight (rebaseRestrictionIsoRelocalize B W S hW hS h X).symm _

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

/-- **The derived direct image commutes with the change of base scheme**, for an arbitrary
morphism `φ : X ⟶ Y` of algebraic spaces over `W`: `R(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ Rφ_*`. -/
def rebaseDerivedDirectImageIso :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2)
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW Y.1 Y.2)
    (Stacks.DerivedFunctor.totalRightDerived
        (modulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)) :
        DerivedCategory (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2) ⥤
          DerivedCategory (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2)) ⋙
        (rebaseRestriction B W S hW hS h Y).mapDerivedCategory ≅
      (rebaseRestriction B W S hW hS h X).mapDerivedCategory ⋙
        (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B W hW φ) :
          DerivedCategory (Modules.{u, u} B W hW X.1 X.2) ⥤
            DerivedCategory (Modules.{u, u} B W hW Y.1 Y.2)) :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2)
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW X.1 X.2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW Y.1 Y.2)
  haveI : (modulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)).Additive :=
    ⟨fun {_ _ _ _} => Functor.map_add _⟩
  haveI : (modulePushforward B W hW φ).Additive := ⟨fun {_ _ _ _} => Functor.map_add _⟩
  Functor.totalRightDerivedMapHomotopyCompIsoOfEquivalence
    (hP₁ := modulePushforward_additive B S hS (relocalizeHomSE B W S hW hS h φ))
    (hP₂ := modulePushforward_additive B W hW φ)
    (hG := relocalizeModulesEquivalenceSE_inverse_additive B W S hW hS h X.2
      (relocalizeSpaceSE B W S hW hS h X).2)
    (hH := relocalizeModulesEquivalenceSE_inverse_additive B W S hW hS h Y.2
      (relocalizeSpaceSE B W S hW hS h Y).2)
    (rebaseRestriction B W S hW hS h X)
    (modulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)) (modulePushforward B W hW φ)
    (rebaseRestriction B W S hW hS h Y)
    (rebaseModuleDirectImageIso B W S hW hS h φ)

end Derived

end AlgebraicGeometry.Space

end

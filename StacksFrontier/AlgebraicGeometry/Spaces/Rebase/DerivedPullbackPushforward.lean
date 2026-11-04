module

public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.SmallEtaleModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesHomEq
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModulePullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackOfIso

/-!
# Derived pullback and derived direct image along the lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site and let `φ : X ⟶ Y` be a representable morphism
of algebraic spaces over `W`, with lower-shriek extension `Λ_h φ : Λ_h X ⟶ Λ_h Y` over `S`.  The
equivalences `Ψ : D(𝒪_{Λ_h X}) ≌ D(𝒪_X)` and `Ψ : D(𝒪_{Λ_h Y}) ≌ D(𝒪_Y)` of
`AlgebraicGeometry.Space.rebaseDerived` commute with derived pullback and with derived direct
image:

`Ψ ∘ L(Λ_h φ)^* ≅ Lφ^* ∘ Ψ` and `Ψ ∘ R(Λ_h φ)_* ≅ Rφ_* ∘ Ψ`.

Both come from the corresponding statements for the underived functors on modules, which are
`AlgebraicGeometry.Space.relocalizeModulePullbackIsoSE` and
`AlgebraicGeometry.Space.relocalizePushforwardIsoSE`, by
`CategoryTheory.Functor.totalLeftDerivedMapHomotopyCompIsoOfEquivalence` and its right-derived
counterpart.

## Main definitions

* `AlgebraicGeometry.Space.rebaseModulePullbackRestrictionIso`: `(Λ_h φ)^* ⋙ Ψ ≅ Ψ ⋙ φ^*` on
  modules.
* `AlgebraicGeometry.Space.rebaseDerivedPullbackIso`: `L(Λ_h φ)^* ⋙ Ψ ≅ Ψ ⋙ Lφ^*`.
* `AlgebraicGeometry.Space.rebaseModulePushforwardRestrictionIso`: `(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ φ_*`
  on modules.
* `AlgebraicGeometry.Space.rebaseDerivedPushforwardIso`: `R(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ Rφ_*`.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {X Y : AlgebraicSpaces B W hW} (φ : X ⟶ Y)
  (hφ : yoneda.relativelyRepresentable φ.hom)

/-- The equivalence `Mod(𝒪_{Λ_h X}) ≌ Mod(𝒪_X)` of restriction along the equivalence of small
étale sites. -/
abbrev rebaseRestriction (X : AlgebraicSpaces B W hW) :
    Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2 ⥤ Modules.{u, u} B W hW X.1 X.2 :=
  (relocalizeModulesEquivalenceSE B W S hW hS h X.2 (relocalizeSpaceSE B W S hW hS h X).2).inverse

/-- An equality of morphisms of ringed topoi gives an isomorphism of the inverse images of
modules. -/
def pullbackModulesIsoOfEq {X Y : RingedTopos.{u, u + 1, u}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {f g : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y} (e : f = g) :
    f.pullbackModules ≅ g.pullbackModules :=
  eqToIso (by rw [e])

/-- The inverse image of modules along a morphism of algebraic spaces, as the pullback of modules
along the associated morphism of ringed topoi, is additive. -/
theorem additive_toModulesHom_pullbackModules (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.Additive :=
  have : (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.pullbackModules.Additive :=
    (modulePullbackAdjunction B S hS f).left_adjoint_additive
  Functor.additive_of_iso
    (pullbackModulesIsoOfEq
      (smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom_eq_toModulesHom)

/-- The direct image of modules along the lower-shriek extension `Λ_h φ` is additive. -/
instance additive_modulePushforward_rebaseHom :
    (modulePushforward B S hS (relocalizeHomSE B W S hW hS h φ)).Additive :=
  modulePushforward_additive B S hS _

/-- **Inverse image of modules along `Λ_h φ`, read on `X`**: `(Λ_h φ)^* ⋙ Ψ ≅ Ψ ⋙ φ^*`, where
`Ψ` is restriction of modules along the equivalences of small étale sites. -/
def rebaseModulePullbackRestrictionIso :
    modulePullback B S hS (relocalizeHomSE B W S hW hS h φ) ⋙
        (rebaseRestriction B W S hW hS h X) ≅
      (rebaseRestriction B W S hW hS h Y) ⋙ modulePullback B W hW φ :=
  let EX := relocalizeModulesEquivalenceSE B W S hW hS h X.2 (relocalizeSpaceSE B W S hW hS h X).2
  let EY := relocalizeModulesEquivalenceSE B W S hW hS h Y.2 (relocalizeSpaceSE B W S hW hS h Y).2
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight EY.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft EY.inverse ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (relocalizeModulePullbackIsoSE B W S hW hS h φ hφ).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ EX.unitIso.symm ≪≫
      Functor.rightUnitor _)

section Pushforward

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

/-- **`Ψ ∘ L(Λ_h φ)^* ≅ Lφ^* ∘ Ψ`**: restriction along the equivalences of small étale sites
commutes with derived pullback. -/
def rebaseDerivedPullbackIso :
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2)
    letI := HasDerivedCategory.standard
      (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW X.1 X.2)
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW Y.1 Y.2)
    smallEtaleDerivedModulePullback B S hS (relocalizeHomSE B W S hW hS h φ) ⋙
        (rebaseRestriction B W S hW hS h X).mapDerivedCategory ≅
      (rebaseRestriction B W S hW hS h Y).mapDerivedCategory ⋙
        smallEtaleDerivedModulePullback B W hW φ :=
  letI := HasDerivedCategory.standard
    (Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2)
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW Y.1 Y.2)
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS
        (relocalizeSpaceSE B W S hW hS h X)).O))
  letI := HasDerivedCategory.standard (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B W hW X).O))
  Functor.totalLeftDerivedMapHomotopyCompIsoOfEquivalence
    (hP₁ := additive_toModulesHom_pullbackModules B S hS (relocalizeHomSE B W S hW hS h φ))
    (hP₂ := additive_toModulesHom_pullbackModules B W hW φ)
    (hG := relocalizeModulesEquivalenceSE_inverse_additive B W S hW hS h Y.2
      (relocalizeSpaceSE B W S hW hS h Y).2)
    (hH := relocalizeModulesEquivalenceSE_inverse_additive B W S hW hS h X.2
      (relocalizeSpaceSE B W S hW hS h X).2)
    (hHl := preservesFiniteLimits_relocalizeModulesEquivalenceSE_inverse B W S hW hS h X.2
      (relocalizeSpaceSE B W S hW hS h X).2)
    (hHc := preservesFiniteColimits_relocalizeModulesEquivalenceSE_inverse B W S hW hS h X.2
      (relocalizeSpaceSE B W S hW hS h X).2)
    (hHe := (relocalizeModulesEquivalenceSE B W S hW hS h X.2
      (relocalizeSpaceSE B W S hW hS h X).2).isEquivalence_inverse)
    (hL₁ := (inferInstance : (smallEtaleModulePullbackOnHomotopy B S hS
      (relocalizeHomSE B W S hW hS h φ)).HasLeftDerivedFunctor
        (smallEtaleModuleQuasiIso B S hS (relocalizeSpaceSE B W S hW hS h Y))))
    (hL₂ := (inferInstance : (smallEtaleModulePullbackOnHomotopy B W hW φ).HasLeftDerivedFunctor
        (smallEtaleModuleQuasiIso B W hW Y)))
    (rebaseRestriction B W S hW hS h Y)
    ((smallEtaleRingedToposHom B S hS
        (relocalizeHomSE B W S hW hS h φ)).toModulesHom.pullbackModules :
      Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h Y).2 ⥤
        Modules.{u, u} B S hS _ (relocalizeSpaceSE B W S hW hS h X).2)
    ((smallEtaleRingedToposHom B W hW φ).toModulesHom.pullbackModules :
      Modules.{u, u} B W hW Y.1 Y.2 ⥤ Modules.{u, u} B W hW X.1 X.2)
    (rebaseRestriction B W S hW hS h X)
    (Functor.isoWhiskerRight (pullbackModulesIsoOfEq (smallEtaleRingedToposHom B S hS
        (relocalizeHomSE B W S hW hS h φ)).toRingedToposModulesHom_eq_toModulesHom).symm _ ≪≫
      rebaseModulePullbackRestrictionIso B W S hW hS h φ hφ ≪≫
      Functor.isoWhiskerLeft _ (pullbackModulesIsoOfEq
        (smallEtaleRingedToposHom B W hW φ).toRingedToposModulesHom_eq_toModulesHom))

/-- **Direct image of modules along `Λ_h φ`, read on `Y`**: `(Λ_h φ)_* ⋙ Ψ ≅ Ψ ⋙ φ_*`. -/
def rebaseModulePushforwardRestrictionIso :
    modulePushforward B S hS (relocalizeHomSE B W S hW hS h φ) ⋙
        (rebaseRestriction B W S hW hS h Y) ≅
      (rebaseRestriction B W S hW hS h X) ⋙ modulePushforward B W hW φ :=
  Functor.isoWhiskerRight (modulePushforwardChartIso B S hS (relocalizeHomSE B W S hW hS h φ)
      (relocalizeRepSE B W S hW hS h φ hφ)) _ ≪≫
    relocalizePushforwardIsoSE B W S hW hS h φ hφ ≪≫
    Functor.isoWhiskerLeft _ (modulePushforwardChartIso B W hW φ hφ).symm

/-- **`Ψ ∘ R(Λ_h φ)_* ≅ Rφ_* ∘ Ψ`**: restriction along the equivalences of small étale sites
commutes with derived direct image. -/
def rebaseDerivedPushforwardIso :
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
    (rebaseModulePushforwardRestrictionIso B W S hW hS h φ hφ)

end Pushforward

end AlgebraicGeometry.Space

end

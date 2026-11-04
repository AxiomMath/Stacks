module

public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedIsoMapDerivedCategoryOfIsoComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceDictionarySquares
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqCompChange
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfExactPullbacks

/-!
# The derived pullback along étale morphisms and composition

For étale morphisms `h : D ⟶ A` and `g : A ⟶ C` of algebraic spaces, the identification
`La^* ≅ D(a^*)` of the derived pullback along an étale morphism with the functor that étale
restriction induces on derived categories carries the composition isomorphism
`Lg^* ⋙ Lh^* ≅ L(h ≫ g)^*` of Stacks 0D6D to the composition isomorphism of the induced functors,
built from the strict composition of étale restrictions.

## Main results

* `AlgebraicGeometry.Space.pullbackModulesCompIso_inv_comp_pullbackModulesIsoModulePullback`: the
  pullbacks of modules of the small étale ringed topoi and the pullbacks of Stacks 03LU have the
  same composition law.
* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_hom_comp_isoEtale`: the
  compatibility on derived categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y Z : AlgebraicSpaces B S hS}

/-- **The composition laws of the two pullbacks of modules agree**: the comparison of the
pullbacks of modules of the small étale ringed topoi with the pullbacks of Stacks 03LU carries the
composition isomorphism of the ringed topoi, transported to the morphism of the composite, to
the composition isomorphism of Stacks 03LU. -/
theorem pullbackModulesCompIso_inv_comp_pullbackModulesIsoModulePullback (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (RingedToposHom.pullbackModulesCompIso (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) (Z := smallEtaleRingedTopos B S hS Z)
        (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)).inv ≫
        (pullbackModulesCompTransport B S hS f g).hom ≫
          (pullbackModulesIsoModulePullback B S hS (f ≫ g)).hom =
      Functor.whiskerRight (pullbackModulesIsoModulePullback B S hS g).hom
          (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
            (smallEtaleRingedToposHom B S hS f).toModulesHom) ≫
        Functor.whiskerLeft (modulePullback B S hS g)
          (pullbackModulesIsoModulePullback B S hS f).hom ≫
          (modulePullbackCompIso B S hS f g).hom := by
  simp only [pullbackModulesIsoModulePullback, pushforwardModulesIsoModulePushforward_eq_eqToIso]
  exact Stacks.CategoryTheory.leftAdjointUniq_comp_change _ _ _ _ _ _ _ _ _
    (pushforwardModules_eq_modulePushforward B S hS f)
    (pushforwardModules_eq_modulePushforward B S hS g)
    (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
    (modulePushforward_comp_eq B S hS f g)

variable {A C D : AlgebraicSpaces B S hS}

/-- The composition law of the pullbacks of modules of the small étale ringed topoi is, along
étale representable morphisms, the strict composition of étale restrictions. -/
theorem pullbackModulesCompIso_inv_comp_isoEtaleModulePullback
    (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom) (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom) :
    ((RingedToposHom.pullbackModulesCompIso (X := smallEtaleRingedTopos B S hS D)
        (Y := smallEtaleRingedTopos B S hS A) (Z := smallEtaleRingedTopos B S hS C)
        (smallEtaleRingedToposHom B S hS h) (smallEtaleRingedToposHom B S hS g)).symm ≪≫
        pullbackModulesCompTransport B S hS h g).hom ≫
        (pullbackModulesIsoModulePullback B S hS (h ≫ g) ≪≫
          modulePullbackIsoEtaleModulePullback B S hS (h ≫ g) hhg).hom =
      Functor.whiskerRight (pullbackModulesIsoModulePullback B S hS g ≪≫
            modulePullbackIsoEtaleModulePullback B S hS g hg).hom
          (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
            (X := smallEtaleRingedTopos B S hS D) (Y := smallEtaleRingedTopos B S hS A)
            (smallEtaleRingedToposHom B S hS h).toModulesHom) ≫
        Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
          (pullbackModulesIsoModulePullback B S hS h ≪≫
            modulePullbackIsoEtaleModulePullback B S hS h hh).hom ≫
          (etaleModulePullbackComp B S hS h g hh hg hhg).hom :=
  Stacks.CategoryTheory.comp_trans_hom_eq_of_comp_hom_eq _ _ _ _ _ _ _ _ _
    (pullbackModulesCompIso_inv_comp_pullbackModulesIsoModulePullback h g)
    (modulePullbackCompIso_hom_comp_etaleRestriction_of_representable B S hS h g hh hg hhg
      hreph hrepg hrephg)

/-- Étale restriction of modules is additive and preserves finite limits and colimits. -/
private theorem etaleModulePullback_additive_and_preserves_finite (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) :
    (etaleModulePullback.{u, u} B S hS f hf).Additive ∧
      PreservesFiniteLimits (etaleModulePullback.{u, u} B S hS f hf) ∧
      PreservesFiniteColimits (etaleModulePullback.{u, u} B S hS f hf) :=
  ⟨etaleModulePullback_additive B S hS f hf, preservesFiniteLimits_etaleModulePullback B S hS f hf,
    preservesFiniteColimits_etaleModulePullback B S hS f hf⟩

/-- **The derived pullback along étale morphisms is étale restriction, compatibly with
composition.** For étale representable `h : D ⟶ A` and `g : A ⟶ C`, the composition isomorphism
`Lg^* ⋙ Lh^* ≅ L(h ≫ g)^*` of Stacks 0D6D, read through `La^* ≅ D(a^*)`, is the composition
isomorphism `D(g^*) ⋙ D(h^*) ≅ D((h ≫ g)^*)` induced by the strict composition of étale
restrictions. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_comp_isoEtale
    (h : D ⟶ A) (g : A ⟶ C) (hh : IsEtale B S hS h.hom) (hg : IsEtale B S hS g.hom)
    (hhg : IsEtale B S hS (h ≫ g).hom)
    (hreph : yoneda.relativelyRepresentable h.hom) (hrepg : yoneda.relativelyRepresentable g.hom)
    (hrephg : yoneda.relativelyRepresentable (h ≫ g).hom) :
    (smallEtaleDerivedModulePullbackCompIso B S hS h g).hom ≫
        (smallEtaleDerivedModulePullbackIsoEtale B S hS (h ≫ g) hhg).hom =
      Functor.whiskerRight (smallEtaleDerivedModulePullbackIsoEtale B S hS g hg).hom
          (smallEtaleDerivedModulePullback B S hS h) ≫
        Functor.whiskerLeft (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory
          (smallEtaleDerivedModulePullbackIsoEtale B S hS h hh).hom ≫
          (Stacks.Homology.mapDerivedCategoryCompIso (etaleModulePullback.{u, u} B S hS g hg)
            (etaleModulePullback.{u, u} B S hS h hh)
            (etaleModulePullback.{u, u} B S hS (h ≫ g) hhg)
            (etaleModulePullbackComp B S hS h g hh hg hhg)).hom := by
  let F₁ := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS A)
    (Y := smallEtaleRingedTopos B S hS C) (smallEtaleRingedToposHom B S hS g).toModulesHom
  let G₁ : type_of% F₁ := etaleModulePullback.{u, u} B S hS g hg
  let F₂ := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS D)
    (Y := smallEtaleRingedTopos B S hS A) (smallEtaleRingedToposHom B S hS h).toModulesHom
  let G₂ : type_of% F₂ := etaleModulePullback.{u, u} B S hS h hh
  let F₃ := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS D)
    (Y := smallEtaleRingedTopos B S hS C) (smallEtaleRingedToposHom B S hS (h ≫ g)).toModulesHom
  let G₃ : type_of% F₃ := etaleModulePullback.{u, u} B S hS (h ≫ g) hhg
  obtain ⟨_, _, _⟩ : G₁.Additive ∧ PreservesFiniteLimits G₁ ∧ PreservesFiniteColimits G₁ :=
    etaleModulePullback_additive_and_preserves_finite g hg
  obtain ⟨_, _, _⟩ : G₂.Additive ∧ PreservesFiniteLimits G₂ ∧ PreservesFiniteColimits G₂ :=
    etaleModulePullback_additive_and_preserves_finite h hh
  obtain ⟨_, _, _⟩ : G₃.Additive ∧ PreservesFiniteLimits G₃ ∧ PreservesFiniteColimits G₃ :=
    etaleModulePullback_additive_and_preserves_finite (h ≫ g) hhg
  open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom in
  exact derivedPullbackCompIso_hom_comp_leftDerivedIsoMapDerivedCategoryOfIso
    (smallEtaleRingedToposHom B S hS h) (smallEtaleRingedToposHom B S hS g)
    (pullbackModulesCompTransport B S hS h g) G₁ G₂ G₃
    (pullbackModulesIsoModulePullback B S hS g ≪≫ modulePullbackIsoEtaleModulePullback B S hS g hg)
    (pullbackModulesIsoModulePullback B S hS h ≪≫ modulePullbackIsoEtaleModulePullback B S hS h hh)
    (pullbackModulesIsoModulePullback B S hS (h ≫ g) ≪≫
      modulePullbackIsoEtaleModulePullback B S hS (h ≫ g) hhg)
    (etaleModulePullbackComp B S hS h g hh hg hhg)
    (pullbackModulesCompIso_inv_comp_isoEtaleModulePullback h g hh hg hhg hreph hrepg hrephg)

end AlgebraicGeometry.Space

end

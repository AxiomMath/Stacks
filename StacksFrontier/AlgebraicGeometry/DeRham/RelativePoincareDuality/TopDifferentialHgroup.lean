module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinDeRhamTarget
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialStein
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UnderlyingAbelianSheafRightDerived

/-!
# The action of a morphism of abelian sheaves on cohomology, two ways

A morphism `ψ : ℱ_ab ⟶ 𝒢_ab` between the underlying abelian sheaves of two sheaves of modules on
a ringed space `X` (for instance a de Rham differential, which is not `𝒪_X`-linear) acts on
cohomology in two ways: through the unbounded derived category, as
`Stacks.DeRham.GysinCohomologyDeRham.abelianHgroupMap` — the arrow in which
[Stacks, Tag 0G8B] states the compatibility of the Gysin maps with the de Rham differentials — and
as Mathlib's classical right derived functor of sections of abelian sheaves,
`(sectionsFunctor X ⊤).rightDerived n`. This file shows that one vanishes exactly when the other
does: both are conjugate to `Hⁿ(RΓ(X, ψ[0]))`, the latter through
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`.

## Main results

* `Stacks.DeRham.GysinCohomologyDeRham.abelianHgroupMap_eq_zero_iff`: `abelianHgroupMap` of a
  morphism of underlying abelian sheaves vanishes in degree `n` exactly when
  `(sectionsFunctor X ⊤).rightDerived n` kills it.
* `AlgebraicGeometry.TopDegreeDifferential.topDifferentialVanishes_succ_iff_abelianHgroupMap`:
  the top de Rham differential vanishes on `H^{e+1}(Y, -)` exactly when its abelian action on the
  cohomology groups `Hgroup` does.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Cohomology.UnderlyingAbelianSheaf
open Stacks.Cohomology.Leray (sectionsFunctor)
open Stacks.DeRham.CohomologicalGysin

universe u

namespace Stacks.DeRham.GysinCohomologyDeRham

open DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-- **The abelian action on cohomology groups vanishes exactly when the classical right derived
functor of sections of abelian sheaves does.** For a morphism `ψ` of underlying abelian sheaves,
`abelianHgroupMap` in degree `n`, with the modules placed in degree `0`, is zero if and only if
`(sectionsFunctor X ⊤).rightDerived n` kills `ψ`. -/
theorem abelianHgroupMap_eq_zero_iff (X : RingedSpace.{u, u}) (n : ℕ) {A B : RModules X}
    (ψ : (forgetModules X).obj A ⟶ (forgetModules X).obj B) :
    abelianHgroupMap X 0 n n (by simp) ψ = 0 ↔
      ((sectionsFunctor X.carrier ⊤).rightDerived n).map ψ = 0 := by
  let E := Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (sectionsFunctor X.carrier ⊤) (derivedAbelianSectionsOnOpen X.carrier ⊤)
    (derivedAbelianSectionsOnOpenUnit X.carrier ⊤)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective n
  have h1 : abelianHgroupMap X 0 n n (by simp) ψ = 0 ↔
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).map
        (abelianDerivedMap X 0 ψ) = 0 := by
    unfold abelianHgroupMap
    simp only [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero]
  have h2 : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).map
        (abelianDerivedMap X 0 ψ) = 0 ↔
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} (n : ℤ)).map
        ((derivedAbelianSectionsOnOpen X.carrier ⊤).map
          ((DerivedCategory.singleFunctor (AbSheaves X) 0).map ψ)) = 0 := by
    unfold abelianDerivedMap forgetSingleMap
    simp only [Functor.map_comp, Category.assoc, Preadditive.IsIso.comp_left_eq_zero,
      Preadditive.IsIso.comp_right_eq_zero]
  have hnat := E.hom.naturality ψ
  simp only [Functor.comp_map] at hnat
  rw [h1, h2, ← Preadditive.IsIso.comp_right_eq_zero (g := E.hom.app ((forgetModules X).obj B)),
    hnat, Preadditive.IsIso.comp_left_eq_zero]

end Stacks.DeRham.GysinCohomologyDeRham

namespace AlgebraicGeometry.TopDegreeDifferential

open Stacks.DeRham.GysinCohomologyDeRham

/-- **The top de Rham differential vanishes on cohomology exactly when its abelian action on the
cohomology groups does**: `d : H^{e+1}(Y, Ω^e_{Y/S}) ⟶ H^{e+1}(Y, Ω^{e+1}_{Y/S})` taken as the
classical right derived functor of sections of abelian sheaves is zero if and only if the arrow
`abelianHgroupMap` of [Stacks, Tag 0G8B] induced by the de Rham differential is. -/
theorem topDifferentialVanishes_succ_iff_abelianHgroupMap {Y S : Scheme.{u}} (g : Y ⟶ S)
    (e : ℕ) :
    TopDifferentialVanishes g (e + 1) ↔
      abelianHgroupMap Y.toRingedSpace 0 ((e + 1 : ℕ) : ℤ) (e + 1) (by simp)
        (Scheme.Hom.deRhamDifferentialAbHom g e) = 0 :=
  (abelianHgroupMap_eq_zero_iff Y.toRingedSpace (e + 1)
    (Scheme.Hom.deRhamDifferentialAbHom g e)).symm

end AlgebraicGeometry.TopDegreeDifferential

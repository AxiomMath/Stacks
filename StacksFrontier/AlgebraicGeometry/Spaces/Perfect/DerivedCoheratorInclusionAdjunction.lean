module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffineEtaleDerivedPushforwardSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.ComparisonEquivalence

/-!
# The derived coherator of an algebraic space as a right adjoint, with its unit on complexes

Let `Z` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The inclusion
`ι : QCoh(𝒪_Z) ⥤ Mod(𝒪_Z)` has a right adjoint, the coherator `Q_Z` of Stacks 077V (2).  This
file fixes one such right adjoint, its total right derived functor
`RQ_Z : D(𝒪_Z) ⥤ D(QCoh(𝒪_Z))` relative to the localizations of the homotopy categories, and the
derived adjunction `D(ι) ⊣ RQ_Z` of [Stacks, Tag 09T5], built by
`Stacks.DerivedCoherator.inclusionDerivedAdjunction` so that its unit on complexes is known.

It also records the two facts about `D(ι)` that the proof of [Stacks, Tag 09TG] uses: `D(ι)`
reflects isomorphisms, and an equivalence criterion in terms of the counit on `D_QCoh(𝒪_Z)`.

## Main definitions

* `AlgebraicGeometry.Space.spaceCoherator` and `AlgebraicGeometry.Space.spaceCoheratorAdjunction`
  — a coherator `Q_Z` with its adjunction `ι ⊣ Q_Z`.
* `AlgebraicGeometry.Space.spaceDerivedCoherator` and
  `AlgebraicGeometry.Space.spaceDerivedCoheratorUnit` — its total right derived functor `RQ_Z`
  with its comparison map.
* `AlgebraicGeometry.Space.spaceDerivedInclusionAdjunction` — `D(ι) ⊣ RQ_Z`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_mapDerivedCategory_quasicoherentSheavesι` — `D(ι)`
  reflects isomorphisms.
* `AlgebraicGeometry.Space.quasicoherentDerivedComparison_isEquivalence_of_isIso_counit` — the
  comparison functor of Stacks 08F1 is an equivalence as soon as the counit of
  `D(ι) ⊣ RQ_Z` is invertible at every object of `D_QCoh(𝒪_Z)`.

## Implementation notes

The derived categories are the standard models, those of the comparison functor of Stacks 08F1.
The existence of a left adjoint of `D(ι)` comes from
`AlgebraicGeometry.Space.derivedCoheratorAdjunction` at a model of `RQ_Z` relative to
`DerivedCategory.Q`; the adjunction used everywhere is then rebuilt with
`CategoryTheory.Adjunction.derived` at the localizations `DerivedCategory.Qh`, which is what makes
its unit computable.

## References

* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Z : AlgebraicSpaces B S hS)

/-- The inclusion of the quasi-coherent modules on an algebraic space is a left adjoint
(Stacks 077V (2)). -/
instance isLeftAdjoint_quasicoherentSheavesι : (quasicoherentSheavesι B S hS Z).IsLeftAdjoint :=
  isLeftAdjoint_ι_quasicoherentSheaves B S hS Z.1 Z.2

/-- A coherator `Q_Z` of the algebraic space `Z`: a right adjoint of the inclusion of the
quasi-coherent modules. -/
abbrev spaceCoherator :
    Modules.{u, u} B S hS Z.1 Z.2 ⥤ QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2 :=
  (quasicoherentSheavesι B S hS Z).rightAdjoint

/-- The coherator adjunction `ι ⊣ Q_Z`. -/
def spaceCoheratorAdjunction : quasicoherentSheavesι B S hS Z ⊣ spaceCoherator B S hS Z :=
  Adjunction.ofIsLeftAdjoint _

/-- The coherator is an additive functor. -/
instance spaceCoherator_additive : (spaceCoherator B S hS Z).Additive :=
  (spaceCoheratorAdjunction B S hS Z).right_adjoint_additive

/-- `Mod(𝒪_Z)` is Grothendieck abelian at the universe of the schemes. -/
instance isGrothendieckAbelian_modules_algebraicSpace :
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Z.1 Z.2) :=
  isGrothendieckAbelian_modules B S hS Z.1 Z.2

/-- `QCoh(𝒪_Z)` is Grothendieck abelian at the universe of the schemes. -/
instance isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace' :
    IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) :=
  isGrothendieckAbelian_quasicoherentSheaves_algebraicSpace B S hS Z

/-- The coherator, on homotopy categories followed by the localization, has a total right derived
functor with respect to the quasi-isomorphisms. -/
instance hasRightDerivedFunctor_spaceCoherator :
    ((spaceCoherator B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :=
  Stacks.DerivedCoherator.hasRightDerivedFunctor_of_isGrothendieckAbelian.{u} _

/-- The derived coherator `RQ_Z : D(𝒪_Z) ⥤ D(QCoh(𝒪_Z))`, the total right derived functor of the
coherator. -/
abbrev spaceDerivedCoherator :
    DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2) :=
  ((spaceCoherator B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ))

/-- The comparison map of the derived coherator. -/
abbrev spaceDerivedCoheratorUnit :
    (spaceCoherator B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ spaceDerivedCoherator B S hS Z :=
  ((spaceCoherator B S hS Z).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ))

/-- The functor `D(ι)` induced by the inclusion of the quasi-coherent modules is a left adjoint
(Stacks 09T5). -/
instance isLeftAdjoint_mapDerivedCategory_quasicoherentSheavesι :
    (quasicoherentSheavesι B S hS Z).mapDerivedCategory.IsLeftAdjoint := by
  obtain ⟨RQ, η, hRQ⟩ := exists_rightDerivedCoherator B S hS Z.1 Z.2 (spaceCoherator B S hS Z)
  have adj := derivedCoheratorAdjunction B S hS Z.1 Z.2 (spaceCoherator B S hS Z)
    (spaceCoheratorAdjunction B S hS Z) RQ η
  have : (Stacks.DerivedModel.derivedFunctorOfExact (quasicoherentSheavesι B S hS Z)
      (DerivedCategory.Q (C := Modules.{u, u} B S hS Z.1 Z.2))
      (DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2))).IsLeftAdjoint :=
    ⟨_, ⟨adj⟩⟩
  exact Functor.isLeftAdjoint_of_iso
    (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory (quasicoherentSheavesι B S hS Z))

/-- **The derived coherator adjunction** `D(ι) ⊣ RQ_Z` of [Stacks, Tag 09T5], with the unit of
`Stacks.DerivedCoherator.inclusionDerivedAdjunction_unit_fac_app`. -/
def spaceDerivedInclusionAdjunction :
    (quasicoherentSheavesι B S hS Z).mapDerivedCategory ⊣ spaceDerivedCoherator B S hS Z :=
  Stacks.DerivedCoherator.inclusionDerivedAdjunction (quasicoherentSheavesι B S hS Z)
    (spaceCoheratorAdjunction B S hS Z) (spaceDerivedCoherator B S hS Z)
    (spaceDerivedCoheratorUnit B S hS Z)

/-- **`D(ι)` reflects isomorphisms**: a morphism of `D(QCoh(𝒪_Z))` whose image under the functor
induced by the inclusion of the quasi-coherent modules is an isomorphism is an isomorphism. -/
lemma isIso_of_isIso_mapDerivedCategory_quasicoherentSheavesι
    {K L : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS Z.1 Z.2)} (f : K ⟶ L)
    (h : IsIso ((quasicoherentSheavesι B S hS Z).mapDerivedCategory.map f)) : IsIso f :=
  Stacks.DerivedCoherator.isIso_of_isIso_mapDerivedCategory_map_of_reflectsIsomorphisms
    (quasicoherentSheavesι B S hS Z) f h

/-- **The comparison functor of Stacks 08F1 is an equivalence as soon as the counit of
`D(ι) ⊣ RQ_Z` is invertible at every complex with quasi-coherent cohomology.** -/
theorem quasicoherentDerivedComparison_isEquivalence_of_isIso_counit
    (h : ∀ M : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2),
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) M →
      IsIso ((spaceDerivedInclusionAdjunction B S hS Z).counit.app M)) :
    (quasicoherentDerivedComparison B S hS Z.1 Z.2).IsEquivalence := by
  set J := (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)))).ι
  let a : quasicoherentDerivedComparison B S hS Z.1 Z.2 ⊣ J ⋙ spaceDerivedCoherator B S hS Z :=
    (spaceDerivedInclusionAdjunction B S hS Z).restrictFullyFaithful
      (Functor.FullyFaithful.id _) (Functor.FullyFaithful.ofFullyFaithful J)
      (Functor.leftUnitor _ ≪≫ (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2).symm)
      (Functor.rightUnitor _).symm
  have hc : ∀ E, IsIso (a.counit.app E) := by
    intro E
    have h1 : IsIso ((spaceDerivedInclusionAdjunction B S hS Z).counit.app (J.obj E)) :=
      h E.obj E.property
    have h2 : IsIso (J.map (a.counit.app E)) := by
      dsimp only [a]
      rw [Adjunction.map_restrictFullyFaithful_counit_app]
      infer_instance
    exact isIso_of_reflects_iso _ J
  have := NatIso.isIso_of_isIso_app a.counit
  have : (quasicoherentDerivedComparison B S hS Z.1 Z.2).ReflectsIsomorphisms := ⟨fun f _ =>
    isIso_of_isIso_mapDerivedCategory_quasicoherentSheavesι B S hS Z f
      ((NatIso.isIso_map_iff (quasicoherentDerivedComparisonCompιIso B S hS Z.1 Z.2) f).1
        (J.map_isIso ((quasicoherentDerivedComparison B S hS Z.1 Z.2).map f)))⟩
  exact Stacks.DerivedQCoh.isEquivalence_of_reflectsIsomorphisms_of_isIso_counit a

end AlgebraicGeometry.Space

end

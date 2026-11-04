module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAssociatedModuleEtalePullback

/-!
# `ε^*` on a represented algebraic space is fully faithful on `D_QCoh`

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let
`h_U = yoneda.obj U` be the algebraic space it represents.  The derived associated-module functor
`ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})`, `AlgebraicGeometry.Space.representedDerivedAssociatedModule`, is
fully faithful on the objects with quasi-coherent cohomology.  It factors as the derived functor
of `ε^* : Mod(𝒪_T) ⥤ Mod(T_étale, 𝒪)` followed by the equivalence `D(T_étale, 𝒪) ≌ D(𝒪_{h_U})`
induced by the identification of the two small étale sites, and the first factor restricts to the
equivalence `D_QCoh(𝒪_T) ≌ D_QCoh(T_étale, 𝒪)` of Stacks 071Q
(`AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`).

Together with `AlgebraicGeometry.Space.exists_representedDerivedAssociatedModule_iso` (every
object of `D_QCoh(𝒪_{h_U})` is `ε^*ω` for some `ω` of `D_QCoh(𝒪_T)`) this is the statement that
`ε^*` identifies `D_QCoh(𝒪_T)` with `D_QCoh(𝒪_{h_U})`, the form in which the source moves
statements about an affine scheme to an affine algebraic space (the first lines of the proofs of
Stacks 09IV, 09IY and 0AEC: "we will use Lemma 75.4.2 for the representable algebraic spaces").

## Main results

* `AlgebraicGeometry.Space.representedDerivedAssociatedModuleFullyFaithful`: the restriction of
  `ε^*` to `D_QCoh(𝒪_T)` is fully faithful.
* `AlgebraicGeometry.Space.representedDerivedAssociatedModuleHomEquiv`: morphisms between objects
  of `D_QCoh(𝒪_T)` are morphisms between their images under `ε^*`.
* `AlgebraicGeometry.Space.eq_zero_of_representedDerivedAssociatedModule_map_eq_zero`: `ε^*`
  is faithful on such morphisms.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 09IY](https://stacks.math.columbia.edu/tag/09IY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance]
  _root_.AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] HasDerivedCategory.standard

variable (T : BigFppfOver B S hS)

/-- The objects of `D(𝒪_T)` with quasi-coherent cohomology, `D_QCoh(𝒪_T)`, for the scheme `T`
underlying an object of the big fppf site. -/
abbrev representedSchemeDerivedQcoh :
    ObjectProperty (DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)

/-- **`ε^*` is fully faithful on `D_QCoh(𝒪_T)`.**  The functor
`ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})` is the derived functor of `ε^* : Mod(𝒪_T) ⥤ Mod(T_étale, 𝒪)`
followed by the equivalence `D(T_étale, 𝒪) ≌ D(𝒪_{h_U})`; on `D_QCoh(𝒪_T)` the first factor is
the equivalence of Stacks 071Q followed by the inclusion of `D_QCoh(T_étale, 𝒪)`. -/
def representedDerivedAssociatedModuleFullyFaithful :
    ((representedSchemeDerivedQcoh B S hS T).ι ⋙
      representedDerivedAssociatedModule B S hS T).FullyFaithful := by
  haveI := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  haveI : (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor).Additive :=
    additive_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  haveI : PreservesFiniteLimits (_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
    preservesFiniteLimits_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  haveI : PreservesFiniteColimits (_root_.AlgebraicGeometry.SmallEtale.associatedModule
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS T).functor) :=
    preservesFiniteColimits_representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)
  exact (((Functor.FullyFaithful.ofFullyFaithful
      (_root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule.{u + 1}
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
        T.left.property)).comp (ObjectProperty.fullyFaithfulι _)).comp
      (representedDerivedModuleEquivalence B S hS T).fullyFaithfulFunctor).ofIso
    (Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
        (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
          (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
          (representedSmallEtaleModuleEquivalence B S hS T).functor))

/-- Morphisms between two objects of `D_QCoh(𝒪_T)` are the morphisms between their images under
`ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})`. -/
def representedDerivedAssociatedModuleHomEquiv
    (ω ω' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hω : representedSchemeDerivedQcoh B S hS T ω)
    (hω' : representedSchemeDerivedQcoh B S hS T ω') :
    (ω ⟶ ω') ≃ ((representedDerivedAssociatedModule B S hS T).obj ω ⟶
      (representedDerivedAssociatedModule B S hS T).obj ω') :=
  ((ObjectProperty.fullyFaithfulι (representedSchemeDerivedQcoh B S hS T)).homEquiv
      (X := ⟨ω, hω⟩) (Y := ⟨ω', hω'⟩)).symm.trans
    ((representedDerivedAssociatedModuleFullyFaithful B S hS T).homEquiv (X := ⟨ω, hω⟩)
      (Y := ⟨ω', hω'⟩))

/-- The bijection `representedDerivedAssociatedModuleHomEquiv` sends a morphism `f` to its image
`ε^* f`. -/
@[simp]
theorem representedDerivedAssociatedModuleHomEquiv_apply
    (ω ω' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hω : representedSchemeDerivedQcoh B S hS T ω)
    (hω' : representedSchemeDerivedQcoh B S hS T ω') (f : ω ⟶ ω') :
    representedDerivedAssociatedModuleHomEquiv B S hS T ω ω' hω hω' f =
      (representedDerivedAssociatedModule B S hS T).map f := by
  simp only [representedDerivedAssociatedModuleHomEquiv, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv_apply, Functor.comp_map]
  rfl

/-- `ε^*` is faithful on morphisms between objects of `D_QCoh(𝒪_T)`: a morphism whose image
vanishes is zero. -/
theorem eq_zero_of_representedDerivedAssociatedModule_map_eq_zero
    {ω ω' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (hω : representedSchemeDerivedQcoh B S hS T ω)
    (hω' : representedSchemeDerivedQcoh B S hS T ω') (f : ω ⟶ ω')
    (hf : (representedDerivedAssociatedModule B S hS T).map f = 0) : f = 0 := by
  have : (representedDerivedAssociatedModule B S hS T).Additive := by
    unfold representedDerivedAssociatedModule; infer_instance
  apply (representedDerivedAssociatedModuleHomEquiv B S hS T ω ω' hω hω').injective
  rw [representedDerivedAssociatedModuleHomEquiv_apply, hf,
    representedDerivedAssociatedModuleHomEquiv_apply, Functor.map_zero]

end AlgebraicGeometry.Space

end

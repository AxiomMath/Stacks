module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatRepresentative
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.HomologyEdge

/-!
# The top-degree pullback comparison against the cohomology edge morphism

Let `h : X ⟶ Y` be a morphism of ringed spaces, let `d : ℤ`, and let `K` be an object of the
derived category of `𝒪_Y`-modules with no cohomology above `d`. Writing `η` for the unit of the
adjunction `h^* ⊣ h_*`, the top-degree comparison `H^d(Lh^* K) ≅ h^* H^d(K)` and the cohomology
edge morphism `H^d(Rh_* -) ⟶ h_* H^d(-)` satisfy

> `η ≫ h_*(H^d(Lh^* K) ≅ h^* H^d(K))⁻¹ = H^d(derived unit) ≫ edge`,

where the derived unit is that of `Lh^* ⊣ Rh_*`. In the base-change situation of
[Stacks, Tag 0EX3] this is a compatibility of the identification
`topDirectImagePullbackIso : h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_* F')` with the edge morphism. The
right-hand side is the shape in which
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac` — the derived base change
map transposed along the bottom of the square, written through the degreewise units of
[Stacks, Tag 0096] — presents itself.

## Main results

* `exists_representative_isStrictlyLE`: every object of a derived category with no cohomology
  above `d` is represented by a cochain complex with no terms above `d`.
* `isIso_comparisonOfRepresentative_modulePullback`: the derived-pullback comparison read through
  such a representative is invertible.
* `unit_comp_map_derivedPullbackTopDegreeIsoPullback_inv_of_representative` and
  `unit_comp_map_derivedPullbackTopDegreeIsoPullback_inv`: the identity above for a morphism of
  ringed spaces, at a given representative and then with none.
* `unit_comp_map_topDirectImagePullbackIso`: the identity for `topDirectImagePullbackIso` in the
  base-change situation of [Stacks, Tag 0EX3].

## Implementation notes

The identity is proved at a representative `P` of `K` with no terms above `d`, on which both
sides are computed through the cohomology class of `P` and the canonical right-exact comparison
`Stacks.MapHomologyCycles.mapHomology`.

*The invertibility of the representative comparison is assembled by hand.* `IsIso` of a composite
whose factors are components of **natural** isomorphisms is not found by instance search at these
spellings; it is found once the factors are packaged as the `hom` of an `Iso`, which is the same
cure `Stacks.RepresentativeSingle.isIso_classOfRepresentative` uses, and the two halves of the
composite are then handed to `CategoryTheory.IsIso.comp_isIso` explicitly.

*Three `rfl`s are discharged in argument position.* The degreewise unit of `h^* ⊣ h_*` on
complexes has target `(h^*(-) ⋙ h_*(-))(P)` where `Stacks.EdgeCompat` wants
`h_*(h^*(P))`; the unit of the induced adjunction on the homotopy category at the class of `P` is
the class of the degreewise one; and the comparison `Lh^*(Q P) ⟶ Q(h^* P)` has its target spelled
through the composite functor. All three are `rfl` and all three are supplied as arguments, where
the elaborator checks them at default transparency, rather than rewritten — the discipline
`RepresentativeHomology.lean` records.

*`CochainComplex.truncLE` is named, not reached by dot notation.* For an object produced as a
`HomologicalComplex _ (ComplexShape.up ℤ)` rather than as a `CochainComplex _ ℤ`, `P.truncLE d`
resolves to Mathlib's embedding-indexed `HomologicalComplex.truncLE` and the degree argument no
longer typechecks.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0BDL](https://stacks.math.columbia.edu/tag/0BDL)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
open Stacks.RepresentativeHomology

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback

section Generic

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Every object of the derived category with no cohomology above `d` is isomorphic to the image
of a cochain complex with no terms above `d`. -/
theorem exists_representative_isStrictlyLE (K : DerivedCategory C) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    ∃ P : CochainComplex C ℤ,
      Nonempty (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ≅ K) ∧
      P.IsStrictlyLE d := by
  obtain ⟨Z, hZ⟩ := HomotopyCategory.quotient_obj_surjective (Qh.objPreimage K)
  have e₀ : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Z) ≅ K :=
    eqToIso (congrArg Qh.obj hZ) ≪≫ Qh.objObjPreimageIso K
  have hZLE : CochainComplex.IsLE Z d :=
    Stacks.RepresentativeSingle.isLE_of_representative Z d e₀ hK
  exact ⟨CochainComplex.truncLE Z d,
    ⟨@asIso _ _ _ _ _
      (isIso_Qh_map_quotient_map (CochainComplex.ιTruncLE Z d) inferInstance) ≪≫ e₀⟩,
    inferInstance⟩

end Generic

section RingedSpaces

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The degree-`d` comparison between `Lh^*` and `h^*`, read through a representative `P` of `K`
with no terms above `d`, is an isomorphism. -/
theorem isIso_comparisonOfRepresentative_modulePullback
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (d : ℤ)
    (hP : P.IsStrictlyLE d)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))}
    (e : Qh.obj ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)).obj P) ≅ K) :
    IsIso (comparisonOfRepresentative (modulePullback h) (derivedPullback h)
      (fun P => (derivedPullbackComparison h).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj P)) P e d) := by
  have h1 : IsIso ((homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
      ((derivedPullback h).map e.inv ≫ (derivedPullbackComparison h).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj P))) := by
    have hcmp := isIso_homologyFunctor_map_derivedPullbackComparison_app h P d hP
    rw [(homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map_comp]
    exact inferInstanceAs (IsIso (((homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) d).mapIso
        ((derivedPullback h).mapIso e.symm)).hom ≫ (@asIso _ _ _ _ _ hcmp).hom))
  have h2 : IsIso
      (((homologyFunctorFactorsh (SheafOfModules.{u} (structureSheafRing X)) d).app
            ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
              (ComplexShape.up ℤ)).obj
              (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) ≪≫
          (HomotopyCategory.homologyFunctorFactors
            (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) d).app
            (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).hom) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

/-- **The top-degree pullback comparison against the cohomology edge morphism, at a
representative with no terms above `d`.**

> `η ≫ h_*(H^d(Lh^* K) ≅ h^* H^d(K))⁻¹ = H^d(derived unit) ≫ edge`

Both sides are morphisms `H^d(K) ⟶ h_* H^d(Lh^* K)`: on the left the unit of the ordinary
adjunction `h^* ⊣ h_*` followed by the direct image of the comparison of [Stacks, Tag 0EX3], on
the right `H^d` of the unit of the derived adjunction `Lh^* ⊣ Rh_*` followed by the cohomology
edge morphism `H^d(Rh_* -) ⟶ h_* H^d(-)`. -/
theorem unit_comp_map_derivedPullbackTopDegreeIsoPullback_inv_of_representative
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hP : P.IsStrictlyLE d)
    (e : Qh.obj ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
      (ComplexShape.up ℤ)).obj P) ≅ K) :
    (modulePullbackPushforwardAdjunction h).unit.app
          ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) ≫
        (modulePushforward h).map (derivedPullbackTopDegreeIsoPullback h K d hK).inv =
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map
          ((derivedAdjunction h).unit.app K) ≫
        (derivedPushforwardHomologyComparison h d).app ((derivedPullback h).obj K) := by
  have hC := isIso_comparisonOfRepresentative_modulePullback h P d hP e
  have hI := representativeClass_comp_eq_mapHomology h P d hP e hK
  have hII := Stacks.EdgeCompat.classOfRepresentative_comp_unit_comp_edge
    (modulePullbackPushforwardAdjunction h) (derivedAdjunction h) (derivedPushforwardUnit h)
    (exists_quasiIso_isKInjective X)
    (fun P => (derivedPullbackComparison h).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P)) d P e
    ((Adjunction.mapHomologicalComplexAdjunction (modulePullbackPushforwardAdjunction h)
      (ComplexShape.up ℤ)).unit.app P) (fun _ => rfl)
    (derivedAdjunction_unit_fac h
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P))
  generalize comparisonOfRepresentative (modulePullback h) (derivedPullback h)
    (fun P => (derivedPullbackComparison h).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
        (ComplexShape.up ℤ)).obj P)) P e d = c at hC hI hII ⊢
  have hA := congrArg (fun z => (modulePullbackPushforwardAdjunction h).unit.app (P.homology d) ≫
    (modulePushforward h).map z) hI
  have nat := (modulePullbackPushforwardAdjunction h).unit.naturality (classOfRepresentative P e d)
  simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at hA nat
  simp only [← assoc, ← nat] at hA
  refine (cancel_mono ((modulePushforward h).map c)).1
    ((cancel_epi (classOfRepresentative P e d)).1 ?_)
  simp only [assoc]
  exact hA.trans hII.symm

/-- **The top-degree pullback comparison against the cohomology edge morphism**: for `K` with no
cohomology above `d`,

> `η ≫ h_*(H^d(Lh^* K) ≅ h^* H^d(K))⁻¹ = H^d(derived unit) ≫ edge`. -/
theorem unit_comp_map_derivedPullbackTopDegreeIsoPullback_inv
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (d : ℤ)
    (hK : TStructure.t.IsLE K d) :
    (modulePullbackPushforwardAdjunction h).unit.app
          ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).obj K) ≫
        (modulePushforward h).map (derivedPullbackTopDegreeIsoPullback h K d hK).inv =
      (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y)) d).map
          ((derivedAdjunction h).unit.app K) ≫
        (derivedPushforwardHomologyComparison h d).app ((derivedPullback h).obj K) := by
  obtain ⟨P, ⟨e⟩, hP⟩ := exists_representative_isStrictlyLE K d hK
  exact unit_comp_map_derivedPullbackTopDegreeIsoPullback_inv_of_representative h K d hK P hP e

end RingedSpaces

section Card

/-- **The compatibility of `topDirectImagePullbackIso` with the cohomology edge morphism of the
derived direct image**, in the base-change situation of [Stacks, Tag 0EX3] and with no hypothesis
beyond it:

> `η ≫ h_*(topDirectImagePullbackIso) = H^d(derived unit) ≫ edge`. -/
theorem unit_comp_map_topDirectImagePullbackIso
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent] {Y'' : Scheme.{u}} (h : Y'' ⟶ S.Y') :
    (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
          ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
            ((derivedPushforward S.f'.toLRSHom.toShHom).obj
              ((singleFunctor S.X'.Modules 0).obj F'))) ≫
        (Scheme.Modules.pushforward h).map (topDirectImagePullbackIso S F' h).hom =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedAdjunction h.toLRSHom.toShHom).unit.app
            ((derivedPushforward S.f'.toLRSHom.toShHom).obj
              ((singleFunctor S.X'.Modules 0).obj F'))) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPullback h.toLRSHom.toShHom).obj
            ((derivedPushforward S.f'.toLRSHom.toShHom).obj
              ((singleFunctor S.X'.Modules 0).obj F'))) :=
  unit_comp_map_derivedPullbackTopDegreeIsoPullback_inv h.toLRSHom.toShHom _ (S.d : ℤ)
    (isLE_derivedPushforward_baseChange S F')

end Card

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end

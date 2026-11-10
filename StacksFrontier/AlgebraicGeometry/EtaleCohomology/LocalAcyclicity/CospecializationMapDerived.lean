module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.CospecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedStalkConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DerivedPushforwardStalkStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# The comparison `β_{K,s,t}` through the derived adjunction, and the cospecialization map

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S`, `t` a geometric point of
`Spec 𝒪^{sh}_{S,s}`, `Y = X ×_S Spec 𝒪^{sh}_{S,s}` with projection `p : Y ⟶ X`, and
`h : X_t ⟶ Y` the fibre of `Y ⟶ Spec 𝒪^{sh}_{S,s}` over `t`. The comparison of Section 0GJT

`β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})`

is `AlgebraicGeometry.cospecializationUnit`, defined as the descent to unbounded derived
categories of the degreewise adjunction unit. This file identifies it with the unit of the
derived adjunction `h⁻¹ ⊣ Rh_*` (`Stacks.EtaleCohomology.smallEtaleDerivedAdjunctionAb`) at
`K|_Y`, followed by the direct image of the composition isomorphism `h⁻¹(K|_Y) ≅ K|_{X_t}`, and
builds from it the cospecialization map `RΓ(X_t, K) ⟶ RΓ(X_s, K)` of Section 0GJT.

It also records the statement of Tag 03Q9 in the form in which the results of this directory
consume it, `AlgebraicGeometry.DerivedPushforwardStalkFormula`, and proves it from
Tag 03Q9
(`Stacks.EtaleCohomology.isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE`).

The unbounded derived functors of the small étale sites are defined in the model
`HasDerivedCategory.standard`, which is therefore the local instance here.

## Main results

* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbPullbackUnit_app_eq` — the descended unit
  is the derived adjunction unit followed by the composition isomorphism.
* `AlgebraicGeometry.cospecializationUnit_eq` — the same for `β_{K,s,t}`.
* `AlgebraicGeometry.DerivedPushforwardStalkFormula`,
  `AlgebraicGeometry.derivedPushforwardStalkFormula` — Tag 03Q9 for bounded below objects, and its
  proof.
* `AlgebraicGeometry.cospecializationMap`, `AlgebraicGeometry.isIso_cospecializationMap_iff` —
  the cospecialization map, and the reduction the proof of Tag 0GJW opens with.

## References

* [Stacks Project, Tag 0GJT](https://stacks.math.columbia.edu/tag/0GJT)
* [Stacks Project, Tag 0GJU](https://stacks.math.columbia.edu/tag/0GJU)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section PullbackUnit

variable {Z W T : Scheme.{u}} (c : W ⟶ Z) (h : T ⟶ W)

/-- On homotopy categories, the degreewise action of the comparison
`c⁻¹ ⟶ (h ≫ c)⁻¹ ⋙ h_*` is the unit of the adjunction on homotopy categories at `c⁻¹J`,
followed by the direct image of the composition isomorphism of inverse images. -/
theorem mapHomotopyCategory_unit_comp_compIso
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (Adjunction.mapHomotopyCategoryAdjunction (smallEtaleAdjunctionAb h) (.up ℤ)).unit.app
          (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J) ≫
        ((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso h c) (.up ℤ)).hom.app
            J) =
      (Stacks.DerivedFunctor.mapHomotopyCategoryOfComp (smallEtalePullbackAb c)
        (smallEtalePullbackAb (h ≫ c)) (smallEtalePushforwardAb h)
        (smallEtalePushforwardAbPullbackUnit c h)).app J := by
  rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app]
  change (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((smallEtaleAdjunctionAb h).mapHomologicalComplexAdjunction (ComplexShape.up ℤ)).unit.app
        (((smallEtalePullbackAb c).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.as)) ≫
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (((smallEtalePushforwardAb h).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (smallEtalePullbackAbCompIso h c)
          (ComplexShape.up ℤ)).hom.app J.as)) = _
  rw [← Functor.map_comp]
  congr 1

variable
  [((smallEtalePushforwardAb h).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]

/-- **The descended unit is the derived adjunction unit.** The comparison
`c⁻¹M ⟶ Rh_*((h ≫ c)⁻¹M)` of `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbPullbackUnit`
is the unit of `h⁻¹ ⊣ Rh_*` at `c⁻¹M` followed by the direct image of the composition isomorphism
`h⁻¹c⁻¹M ≅ (h ≫ c)⁻¹M`.

Both are transformations out of the degreewise action of the exact functor `c⁻¹`, a right derived
functor of itself, so it suffices that they agree on the image of every complex; there the derived
unit is the degreewise unit followed by the unit of the derivation of `h_*`, and the composition
isomorphism is degreewise, which is the factorization of the descended unit. -/
theorem smallEtaleDerivedPushforwardAbPullbackUnit_app_eq (K : smallEtaleDerivedCategory Z) :
    (smallEtaleDerivedPushforwardAbPullbackUnit c h).app K =
      (smallEtaleDerivedAdjunctionAb h).unit.app ((smallEtaleDerivedPullbackAb c).obj K) ≫
        (smallEtaleDerivedPushforwardAb h).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift
            (smallEtalePullbackAbCompIso h c)).hom.app K) := by
  let γ : smallEtaleDerivedPullbackAb c ⟶
      smallEtaleDerivedPullbackAb (h ≫ c) ⋙ smallEtaleDerivedPushforwardAb h :=
    (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft _ (smallEtaleDerivedAdjunctionAb h).unit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight
        (smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso h c)).hom _
  have hγ : smallEtaleDerivedPushforwardAbPullbackUnit c h = γ := by
    refine Functor.rightDerived_ext (smallEtaleDerivedPullbackAb c)
      (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) _ _ _ ?_
    ext J
    change (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J ≫
        (smallEtaleDerivedPushforwardAbPullbackUnit c h).app (DerivedCategory.Qh.obj J) =
      (smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J ≫ γ.app _
    rw [smallEtaleDerivedPushforwardAbPullbackUnit_fac_app]
    have hnat := (smallEtaleDerivedAdjunctionAb h).unit.naturality
      ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J)
    have hu := smallEtaleDerivedAdjunctionAb_unit_app_Qh h
      (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J)
    have hq := smallEtaleDerivedPullbackAbCompIsoQhLift_hom_app
      (smallEtalePullbackAbCompIso h c) J
    have hη := (smallEtaleDerivedPushforwardAbUnit h).naturality
      ((Functor.mapHomotopyCategoryCompIso (smallEtalePullbackAbCompIso h c) (.up ℤ)).hom.app J)
    have hH := mapHomotopyCategory_unit_comp_compIso c h J
    have c1 : (smallEtaleDerivedPushforwardAb h).map ((smallEtaleDerivedPullbackAb h).map
          ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J)) ≫
        (smallEtaleDerivedPushforwardAb h).map ((smallEtaleDerivedPullbackAb h).map
          ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.hom.app J)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app,
        CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    have c2 : (smallEtaleDerivedPushforwardAb h).map
          ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.inv.app
            (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J)) ≫
        (smallEtaleDerivedPushforwardAb h).map
          ((smallEtalePullbackAb h).mapDerivedCategoryFactorsh.hom.app
            (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J)) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    simp only [γ, NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnat
    rw [reassoc_of% hnat, hu, hq]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% c1, reassoc_of% c2]
    simp only [Functor.comp_map] at hη
    rw [← reassoc_of% hη, ← Functor.map_comp_assoc, hH]
  rw [hγ]
  simp [γ]

end PullbackUnit

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Unit

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- **The comparison `β_{K,s,t}` is the unit of the derived adjunction.** It is the unit of
`h⁻¹ ⊣ Rh_*` (`Stacks.EtaleCohomology.smallEtaleDerivedAdjunctionAb`) at `K|_Y`, followed by the
direct image of the composition isomorphism `h⁻¹(K|_Y) ≅ K|_{X_t}` for inverse images along
`X_t ⟶ Y ⟶ X`. -/
theorem cospecializationUnit_eq (K : smallEtaleDerivedCategory X) :
    cospecializationUnit B hS f s t K =
      (smallEtaleDerivedAdjunctionAb (cospecializationFibreToBaseChange B hS f s t)).unit.app
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s)).obj K) ≫
        (smallEtaleDerivedPushforwardAb (cospecializationFibreToBaseChange B hS f s t)).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift
            (smallEtalePullbackAbCompIso (cospecializationFibreToBaseChange B hS f s t)
              (strictHenselizationBaseChangeToSource B hS f s))).hom.app K) :=
  smallEtaleDerivedPushforwardAbPullbackUnit_app_eq _ _ K

end Unit

/-! ### The stalk of a derived direct image over the strict henselization (Tag 03Q9) -/

/-- **The statement of Stacks 03Q9** in the form the source's last display gives it: for every
quasi-compact and quasi-separated morphism of schemes `f : X ⟶ S`, every geometric point `s` of
`S` and every bounded below object `K` of `D(X_étale)`, the canonical map of Tag 0GIX

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec 𝒪^{sh}_{S,s}, p⁻¹K)`

(`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections`) is an isomorphism.
The strict henselizations are those of the big étale site `B`, which contains `S`.

The source's first two displays, for an abelian sheaf and for the cohomology sheaves of `K`,
are the cohomology of this one. It is proved, as
`AlgebraicGeometry.derivedPushforwardStalkFormula`, from
`Stacks.EtaleCohomology.isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE`. -/
def DerivedPushforwardStalkFormula (B : BigEtaleSite.{u}) : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (hS : B.Contains S) (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (s : GeometricPoint S) (K : smallEtaleDerivedCategory X) (m : ℤ), K.IsGE m →
    IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app K)

/-- **Stacks 03Q9 holds** in the form `AlgebraicGeometry.DerivedPushforwardStalkFormula`, at every
big étale site: this is
`Stacks.EtaleCohomology.isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE`. -/
theorem derivedPushforwardStalkFormula (B : BigEtaleSite.{u}) : DerivedPushforwardStalkFormula B :=
  fun _ _ hS f _ _ s K m hK =>
    have := hK
    isIso_derivedPushforwardStalkToStrictHenselizationSections_of_isGE B hS f s K m

/-! ### The cospecialization map -/

section Cospecialization

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

variable (K : smallEtaleDerivedCategory X)
  [IsIso ((smallEtaleDerivedPullbackAb
    (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
      (cospecializationUnit B hS f s t K))]

/-- **The cospecialization map** (Section 0GJT)

`cosp : RΓ(X_t, K) ⟶ RΓ(X_s, K)`

for an object `K` of `D(X_étale)`, a geometric point `s` of `S` and a geometric point `t` of
`Spec 𝒪^{sh}_{S,s}`, defined whenever the inverse image `i⁻¹β_{K,s,t}` on the closed geometric
fibre of the comparison `β_{K,s,t} : K|_Y ⟶ Rh_*(K|_{X_t})` is an isomorphism — which is Tag
0GJU when `K` is bounded below and `f` is locally acyclic relative to `K`. It is the composite

`RΓ(X_t, K) = RΓ(Y, Rh_*(K|_{X_t})) ⟶ RΓ(X_s, i⁻¹Rh_*(K|_{X_t}))`
`  ⟶ RΓ(X_s, i⁻¹(K|_Y)) = RΓ(X_s, K)`

of the inverse of Leray for `h`
(`Stacks.EtaleCohomology.smallEtaleDerivedPushforwardGlobalSectionsIso`:
direct image along `h` has the exact left adjoint `h⁻¹`, so it carries K-injective complexes to
K-injective complexes, and global sections on `Y` of a direct image are global sections on
`X_t`), pullback by `i`, the inverse of `i⁻¹β_{K,s,t}`, and the composition isomorphism for
inverse images along `X_s ⟶ Y ⟶ X`. -/
def cospecializationMap :
    (smallEtaleDerivedGlobalSections (cospecializationFibre B hS f s t)).obj
        ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K) ⟶
      (smallEtaleDerivedGlobalSections (geometricFibre f s)).obj
        ((smallEtaleDerivedPullbackAb (geometricFibreToSource f s)).obj K) :=
  (smallEtaleDerivedPushforwardGlobalSectionsIso
    (cospecializationFibreToBaseChange B hS f s t)).inv.app _ ≫
    (smallEtaleDerivedGlobalSectionsRestriction
      (geometricFibreToStrictHenselizationBaseChange B hS f s)).app _ ≫
    (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
      (inv ((smallEtaleDerivedPullbackAb
        (geometricFibreToStrictHenselizationBaseChange B hS f s)).map
          (cospecializationUnit B hS f s t K))) ≫
    (smallEtaleDerivedGlobalSections (geometricFibre f s)).map
      ((smallEtaleDerivedPullbackAbCompIsoQhLift
        (geometricFibrePullbackAbCompIso B hS f s)).hom.app K)

/-- **The cospecialization map is an isomorphism exactly when pullback by `i` is**, on derived
sections of `Rh_*(K|_{X_t})`: every other step of `AlgebraicGeometry.cospecializationMap` is an
isomorphism. This is the reduction the proof of Tag 0GJW opens with. -/
theorem isIso_cospecializationMap_iff :
    IsIso (cospecializationMap B hS f s t K) ↔
      IsIso ((smallEtaleDerivedGlobalSectionsRestriction
        (geometricFibreToStrictHenselizationBaseChange B hS f s)).app
          ((smallEtaleDerivedPushforwardAb (cospecializationFibreToBaseChange B hS f s t)).obj
            ((smallEtaleDerivedPullbackAb (cospecializationFibreToSource B hS f s t)).obj K))) := by
  unfold cospecializationMap
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

end Cospecialization

end AlgebraicGeometry

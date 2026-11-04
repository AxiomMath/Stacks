module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree

/-!
# Stalks of higher direct images and cohomology over the strict henselization

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S` and
`p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` the projection. When the canonical map
`(Rf_*G)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹G)` of [Stacks, Tag 0GIX] is an isomorphism at an
abelian sheaf `G` ([Stacks, Tag 03Q9]), the stalk at `s` of `R^q f_* G` vanishes exactly when
`H^q(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹G)` does. Only the existence of an isomorphism between the two
groups is used: the stalk functor is exact, so it commutes with taking cohomology of a complex,
and the cohomology of derived global sections at a sheaf placed in degree zero is the classical
right derived functor of global sections, which is sheaf cohomology.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_iff_isZero_homology_smallEtaleDerivedGlobalSections` —
  `H^q(Z, G) = 0` exactly when the degree-`q` cohomology of `RΓ(Z, G)` vanishes.
* `AlgebraicGeometry.isZero_stalk_homology_iff_subsingleton_H_strictHenselization` — the
  vanishing criterion above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

/-- **Sheaf cohomology vanishes in degree `q` exactly when the degree-`q` cohomology of derived
global sections at the sheaf placed in degree zero does.** -/
theorem subsingleton_H_iff_isZero_homology_smallEtaleDerivedGlobalSections {Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} G q) ↔
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives Z
  have : IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Z
  rw [Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0, u, u + 1}]
  exact (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
    (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtaleDerivedGlobalSections Z)
    (smallEtaleDerivedGlobalSectionsUnit Z)
    (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2}) G q).isZero_iff.symm

/-- Sheaf cohomology of isomorphic sheaves vanishes together. -/
theorem subsingleton_H_iff_of_iso {Z : Scheme.{u}}
    [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {G G' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : G ≅ G') (q : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} G q) ↔ Subsingleton (Sheaf.H.{u + 1} G' q) := by
  let E : Sheaf.H.{u + 1} G q ≃ Sheaf.H.{u + 1} G' q :=
    { toFun := Sheaf.H.map e.hom q
      invFun := Sheaf.H.map e.inv q
      left_inv := fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv := fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply] }
  exact E.subsingleton_congr

/-- The stalk at a geometric point commutes with taking cohomology of a complex of abelian
sheaves, the stalk functor being exact. -/
theorem isZero_stalk_homology_iff {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (t : Spec (.of Ω) ⟶ Y) (K : DerivedCategory (Sheaf (smallEtaleTopology Y) Ab.{u + 1}))
    (q : ℤ) :
    IsZero ((smallEtaleStalkAb t).obj ((DerivedCategory.homologyFunctor _ q).obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
        ((smallEtaleDerivedStalkAb t).obj K)) :=
  (((smallEtaleStalkAb t).mapDerivedCategoryHomologyFunctorIso q).app K).isZero_iff.symm

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-- Derived direct image exists on the small étale sites: every complex of abelian sheaves has a
K-injective resolution. -/
instance smallEtalePushforwardAb_hasRightDerivedFunctor {X S : Scheme.{u}} (f : X ⟶ S) :
    ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :=
  have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  have := Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective
    ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-- **The stalk of a higher direct image at a geometric point vanishes exactly when the
cohomology over the strict henselization does**, granted that the canonical map
`(Rf_*G)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹G)` of [Stacks, Tag 0GIX] is an isomorphism at
`G` ([Stacks, Tag 03Q9]). -/
theorem isZero_stalk_homology_iff_subsingleton_H_strictHenselization
    [HasExt.{u + 1} (Sheaf (strictHenselizationBaseChange B hS f s).smallEtaleTopology
      AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h03Q9 : IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
      ((DerivedCategory.singleFunctor _ 0).obj G))) (q : ℕ) :
    IsZero ((smallEtaleStalkAb s.hom).obj ((DerivedCategory.homologyFunctor _ (q : ℤ)).obj
        ((smallEtaleDerivedPushforwardAb f).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)))) ↔
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
        (strictHenselizationBaseChangeToSource B hS f s)).obj G) q) := by
  rw [isZero_stalk_homology_iff, ← subsingleton_H_iff_of_iso
    ((Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtaleBaseChange (strictHenselizationBaseChangeToSource B hS f s))
      AddCommGrpCat.{u + 1} _ _).app G),
    subsingleton_H_iff_isZero_homology_smallEtaleDerivedGlobalSections]
  refine ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).mapIso
    (asIso ((derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
      ((DerivedCategory.singleFunctor _ 0).obj G)) ≪≫
    (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s)).mapIso
      (((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
        |>.mapDerivedCategorySingleFunctor 0).app G))).isZero_iff

end AlgebraicGeometry

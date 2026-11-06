module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedDescAlongPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence

/-!
# The stalk at a geometric point is the cohomology of the strict henselization

Let `x` be a geometric point of a scheme `X` and write `p : Spec 𝒪^{sh}_{X,x} ⟶ X` for the
structure morphism of the strict henselization. The source, in the discussion preceding
Definition 0GJP, records

`K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)`

for every object `K` of `D(X_étale)`, because `𝒪^{sh}_{X,x}` is strictly henselian. This file
proves that statement for the canonical map `AlgebraicGeometry.vanishingCyclesMap` of Tag 0GJN
taken at the strict henselization itself, and draws the consequence the source uses it for: the
map `α_{K,x,t} : K_x ⟶ RΓ(T, K)` of Tag 0GJN, for any scheme `T` over `Spec 𝒪^{sh}_{X,x}`, is that
identification followed by restriction of derived global sections along `T ⟶ Spec 𝒪^{sh}_{X,x}`.
So whether `α_{K,x,t}` is an isomorphism depends only on the inverse image `p⁻¹K`.

## The argument

The identification itself is `AlgebraicGeometry.isIso_vanishingCyclesMap_id`
(`HenselianRings/StrictHenselizationStalkSections.lean`): on abelian sheaves it is
`F_x = Γ(Spec 𝒪^{sh}_{X,x}, p⁻¹F)` (`AlgebraicGeometry.isIso_etaleStalkToSectionsAb_id`), global
sections over a strictly henselian local scheme being the stalk at a geometric point over the
closed point (Tag 03QO), and the derived map factors it through the unit of the derivation of
global sections, which is invertible because those global sections are exact.

The factorization through the strict henselization is the derived form of
`AlgebraicGeometry.etaleStalkToSectionsAb_comp`, obtained by the uniqueness of a transformation out
of the degreewise action of the exact stalk functor
(`Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc`).

## Main results

* `AlgebraicGeometry.vanishingCyclesMap_comp` — the map of Tag 0GJN for `T' ⟶ T` over the strict
  henselization is the one for `T` followed by restriction of derived global sections.
* `AlgebraicGeometry.isIso_vanishingCyclesMap_app_iff_of_iso` — the map of Tag 0GJN is an
  isomorphism at `K` exactly when it is one at any `K'` with `p⁻¹K ≅ p⁻¹K'`.

## References

* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Comp

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T T' : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x) (c : T' ⟶ T)
  [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T') Ab.{u + 1}) (.up ℤ))]

/-- **Transitivity of the map of Tag 0GJN in the scheme over the strict henselization**, on
unbounded derived categories. For a morphism `c : T' ⟶ T` of schemes over `Spec 𝒪^{sh}_{X,x}`,
the map `K_x ⟶ RΓ(T', K)` is the map `K_x ⟶ RΓ(T, K)` followed by restriction of unbounded
derived global sections along `c`, read through the composition isomorphism of inverse images.

This is the derived form of `AlgebraicGeometry.etaleStalkToSectionsAb_comp`: both sides are
transformations out of the degreewise action of the exact stalk functor descending the two sides
of that identity. -/
theorem vanishingCyclesMap_comp :
    vanishingCyclesMap B X hX x (c ≫ q) =
      vanishingCyclesMap B X hX x q ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb (q ≫ strictHenselizationToBase B X hX x))
          (smallEtaleDerivedGlobalSectionsRestriction c) ≫
        (Functor.associator
            (smallEtaleDerivedPullbackAb (q ≫ strictHenselizationToBase B X hX x))
            (smallEtaleDerivedPullbackAb c) (smallEtaleDerivedGlobalSections T')).inv ≫
          Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso
              (etaleStalkSectionsRestrictionCompIso B X hX x q c)).hom
            (smallEtaleDerivedGlobalSections T') := by
  rw [Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc
      (smallEtaleStalkAb x.hom) _ (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})
      (smallEtaleDerivedGlobalSections T') (smallEtaleDerivedGlobalSectionsUnit T')
      (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) (smallEtalePullbackAb c)
      (smallEtaleDerivedGlobalSections T) (smallEtaleDerivedGlobalSectionsUnit T) _
      (etaleStalkToSectionsAb B X hX x q) (smallEtaleGlobalSectionsRestrictionAb c)
      (vanishingCyclesMap B X hX x q) (smallEtaleDerivedGlobalSectionsRestriction c)
      (vanishingCyclesMap_fac_app B X hX x q)
      (smallEtaleDerivedGlobalSectionsRestriction_fac_app c),
    ← etaleStalkToSectionsAb_comp]
  rfl

end Comp

section Dependence

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}}
  [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]

/-- Whether the map of Tag 0GJN is an isomorphism at an object depends on the structure morphism
of `T` over the strict henselization only up to equality. -/
private theorem isIso_vanishingCyclesMap_app_congr {q₁ q₂ : T ⟶ strictHenselization B X hX x}
    (h : q₁ = q₂) (K : smallEtaleDerivedCategory X) :
    IsIso ((vanishingCyclesMap B X hX x q₁).app K) ↔
      IsIso ((vanishingCyclesMap B X hX x q₂).app K) := by
  subst h
  rfl

/-- **The map of Tag 0GJN is an isomorphism exactly when restriction from the strict henselization
is.** For a scheme `T` over `Spec 𝒪^{sh}_{X,x}` with structure morphism `q`, the map
`α_{K,x,t} : K_x ⟶ RΓ(T, K)` is an isomorphism at `K` if and only if restriction of unbounded
derived global sections `RΓ(Spec 𝒪^{sh}_{X,x}, p⁻¹K) ⟶ RΓ(T, q⁻¹p⁻¹K)` is: the former is the
identification `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)` followed by the latter. -/
theorem isIso_vanishingCyclesMap_app_iff (q : T ⟶ strictHenselization B X hX x)
    (K : smallEtaleDerivedCategory X) :
    haveI := smallEtaleGlobalSectionsAb_hasRightDerivedFunctor (strictHenselization B X hX x)
    IsIso ((vanishingCyclesMap B X hX x q).app K) ↔
      IsIso ((smallEtaleDerivedGlobalSectionsRestriction q).app
        ((smallEtaleDerivedPullbackAb (𝟙 _ ≫ strictHenselizationToBase B X hX x)).obj K)) := by
  have := smallEtaleGlobalSectionsAb_hasRightDerivedFunctor (strictHenselization B X hX x)
  rw [← isIso_vanishingCyclesMap_app_congr B X hX x (Category.comp_id q) K,
    vanishingCyclesMap_comp B X hX x (𝟙 _) q]
  have := isIso_vanishingCyclesMap_id B X hX x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]

/-- **The map of Tag 0GJN depends only on the inverse image on the strict henselization.** If two
objects `K` and `K'` of `D(X_étale)` have isomorphic inverse images on `Spec 𝒪^{sh}_{X,x}`, then
for every scheme `T` over `Spec 𝒪^{sh}_{X,x}` the map `α_{K,x,t} : K_x ⟶ RΓ(T, K)` is an
isomorphism exactly when `α_{K',x,t}` is.

This is how the source uses the identification `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)`: both source and
target of `α` are computed from the inverse image of `K` on the strict henselization. -/
theorem isIso_vanishingCyclesMap_app_iff_of_iso (q : T ⟶ strictHenselization B X hX x)
    {K K' : smallEtaleDerivedCategory X}
    (e : (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K ≅
      (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K') :
    IsIso ((vanishingCyclesMap B X hX x q).app K) ↔
      IsIso ((vanishingCyclesMap B X hX x q).app K') := by
  have := smallEtaleGlobalSectionsAb_hasRightDerivedFunctor (strictHenselization B X hX x)
  let c := eqToIso (congrArg (fun m : strictHenselization B X hX x ⟶ X =>
    smallEtaleDerivedPullbackAb m) (Category.id_comp (strictHenselizationToBase B X hX x)))
  rw [isIso_vanishingCyclesMap_app_iff, isIso_vanishingCyclesMap_app_iff]
  exact NatTrans.isIso_app_iff_of_iso _ (c.app K ≪≫ e ≪≫ c.symm.app K')

end Dependence

end AlgebraicGeometry

end

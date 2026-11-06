module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactDerivedDescAlongPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# The canonical map on unbounded derived categories under inverse image along a morphism

Let `g : X' ⟶ X` be a morphism of schemes, let `x'` be a geometric point of `X'` with image `x`
in `X`, let `T` be a scheme over `Spec 𝒪^{sh}_{X,x}`, let `T'` be a scheme over
`Spec 𝒪^{sh}_{X',x'}`, and let `ι : T' ⟶ T` be compatible with the induced morphism of strict
henselizations. The canonical map of Tag 0GJN on unbounded derived categories of abelian étale
sheaves, `AlgebraicGeometry.vanishingCyclesMap`, is then formed twice: on `X'` for `T'`, and on
`X` for `T`. This file proves that the first, read through the identification of the derived
stalk of an inverse image with the derived stalk at the image point, is the second followed by
restriction of unbounded derived global sections along `ι`
(`AlgebraicGeometry.vanishingCyclesMap_pullback`).

This is the derived form of `AlgebraicGeometry.etaleStalkToSectionsAb_pullback`, and the
statement on abelian sheaves is the only input: both sides are transformations out of the
degreewise action of the stalk functor at `x`, which is exact, hence a right derived functor of
its own action on homotopy categories, so a transformation out of it is determined by its
factorization through `CategoryTheory.Functor.mapDerivedCategoryFactorsh`. Each side is one of
the two shapes of
`Stacks.DerivedFunctor.compIso_whiskerLeft_eq_exactDerivedDesc` and
`Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc`, whose factorizations are
`AlgebraicGeometry.vanishingCyclesMap_fac_app` and
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_fac_app`; the two descents
therefore agree as soon as the transformations on abelian sheaves they descend do.

Both sides are read in the unbounded derived global sections on `T'` of the inverse image along
the structure morphism of `T'` over `X`, which the two composition isomorphisms for inverse image
provide on derived categories through
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso`.

## Main results

* `AlgebraicGeometry.vanishingCyclesMap_pullback` — the canonical map of Tag 0GJN on unbounded
  derived categories is compatible with inverse image along a morphism of the ambient scheme.

## References

* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 0GJS](https://stacks.math.columbia.edu/tag/0GJS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Pullback

variable (B : BigEtaleSite.{u}) {X X' : Scheme.{u}} (hX : B.Contains X) (hX' : B.Contains X')
  (g : X' ⟶ X) (x' : GeometricPoint X') {T T' : Scheme.{u}}
  (q : T ⟶ strictHenselization B X hX (x'.map g))
  (q' : T' ⟶ strictHenselization B X' hX' x') (ι : T' ⟶ T)
  [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T') Ab.{u + 1}) (.up ℤ))]

/-- **The map of Tag 0GJN on unbounded derived categories under inverse image along a morphism of
the ambient scheme.** For `g : X' ⟶ X`, a geometric point `x'` of `X'` with image `x` in `X`,
schemes `T` over `Spec 𝒪^{sh}_{X,x}` and `T'` over `Spec 𝒪^{sh}_{X',x'}` and a morphism
`ι : T' ⟶ T` compatible with the induced morphism of strict henselizations, the canonical map
`AlgebraicGeometry.vanishingCyclesMap` formed on `X'` for `T'`, read through the identification of
the derived stalk of an inverse image with the derived stalk at the image point, is the map formed
on `X` for `T` followed by restriction of unbounded derived global sections along `ι`.

This is the derived form of `AlgebraicGeometry.etaleStalkToSectionsAb_pullback`, which is the
whole input: each side is a transformation out of the degreewise action of the stalk functor at
`x` descending one side of that identity, and the degreewise action of an exact functor is a
right derived functor of its action on homotopy categories. -/
public theorem vanishingCyclesMap_pullback
    (hι : q' ≫ strictHenselizationSquareMap B hX' hX g x' = ι ≫ q) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso (smallEtaleStalkPullbackAbIso g x'.hom)).inv ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb g)
            (vanishingCyclesMap B X' hX' x' q') ≫
          (Functor.associator (smallEtaleDerivedPullbackAb g)
              (smallEtaleDerivedPullbackAb
                (q' ≫ strictHenselizationToBase B X' hX' x'))
              (smallEtaleDerivedGlobalSections T')).inv ≫
            Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso
                (smallEtalePullbackAbCompIso
                  (q' ≫ strictHenselizationToBase B X' hX' x') g)).hom
              (smallEtaleDerivedGlobalSections T') =
      vanishingCyclesMap B X hX (x'.map g) q ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb
              (q ≫ strictHenselizationToBase B X hX (x'.map g)))
            (smallEtaleDerivedGlobalSectionsRestriction ι) ≫
          (Functor.associator (smallEtaleDerivedPullbackAb
                (q ≫ strictHenselizationToBase B X hX (x'.map g)))
              (smallEtaleDerivedPullbackAb ι)
              (smallEtaleDerivedGlobalSections T')).inv ≫
            Functor.whiskerRight (Functor.mapDerivedCategoryCompIsoOfCompIso
                (smallEtalePullbackAbCompIso ι
                    (q ≫ strictHenselizationToBase B X hX (x'.map g)) ≪≫
                  eqToIso (congrArg (fun m : T' ⟶ X => smallEtalePullbackAb m)
                    (comp_strictHenselizationToBase_of_comp B hX hX' g x' q q' ι hι)))).hom
              (smallEtaleDerivedGlobalSections T') := by
  rw [Stacks.DerivedFunctor.compIso_whiskerLeft_eq_exactDerivedDesc
      (smallEtaleStalkAb (x'.map g).hom) _ (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})
      (smallEtaleDerivedGlobalSections T') (smallEtaleDerivedGlobalSectionsUnit T')
      (smallEtalePullbackAb g) (smallEtaleStalkAb x'.hom) _ _ _
      (etaleStalkToSectionsAb B X' hX' x' q') (vanishingCyclesMap B X' hX' x' q')
      (vanishingCyclesMap_fac_app B X' hX' x' q'),
    Stacks.DerivedFunctor.whiskerLeft_compIso_eq_exactDerivedDesc
      (smallEtaleStalkAb (x'.map g).hom) _ (Sheaf.Γ (smallEtaleTopology T') Ab.{u + 1})
      (smallEtaleDerivedGlobalSections T') (smallEtaleDerivedGlobalSectionsUnit T')
      (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX (x'.map g)))
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) (smallEtalePullbackAb ι)
      (smallEtaleDerivedGlobalSections T) (smallEtaleDerivedGlobalSectionsUnit T) _
      (etaleStalkToSectionsAb B X hX (x'.map g) q) (smallEtaleGlobalSectionsRestrictionAb ι)
      (vanishingCyclesMap B X hX (x'.map g) q)
      (smallEtaleDerivedGlobalSectionsRestriction ι)
      (vanishingCyclesMap_fac_app B X hX (x'.map g) q)
      (smallEtaleDerivedGlobalSectionsRestriction_fac_app ι),
    etaleStalkToSectionsAb_pullback B hX hX' g x' q q' ι hι]
  rfl

end Pullback

end AlgebraicGeometry

end

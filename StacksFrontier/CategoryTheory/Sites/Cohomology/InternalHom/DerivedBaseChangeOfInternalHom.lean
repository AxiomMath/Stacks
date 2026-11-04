module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the internal hom in the derived category of a ringed topos

Let

```
                   h
  (Sh(C'), O_{C'}) --→ (Sh(C), O_C)
        |  f'                |  f
        v                    v
  (Sh(D'), O_{D'}) --→ (Sh(D), O_D)
                   g
```

be a commutative diagram of ringed topoi and let `K`, `L` be objects of `D(O_C)`.
**Stacks 08JG** asserts a canonical base change map

`Lg^* Rf_* RSheafHom(K, L) ⟶ R(f')_* RSheafHom(Lh^* K, Lh^* L)`

in `D(O_{D'})`.  The source takes it to be the map adjoint, under `L(f')^* ⊣ R(f')_*`, to the
composition of three steps: the identification
`L(f')^* Lg^* Rf_* RSheafHom(K, L) = Lh^* Lf^* Rf_* RSheafHom(K, L)` supplied by commutativity
of the square, the derived counit `Lf^* Rf_* ⟶ id`, and the canonical map of Stacks 08JF.

This file treats the special case of a square of morphisms of ringed topoi presented by morphisms
of sites. Stacks 08JG itself, for an arbitrary commutative square of morphisms of ringed topoi,
is `Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom.derivedBaseChangeSheafHomMap`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomBaseChangeOnTopoi.derivedBaseChangeSheafHomMap`:
  the canonical base change map, for a square presented by morphisms of sites.

## Main results

* `Stacks.Cohomology.DerivedInternalHomBaseChangeOnTopoi.derivedBaseChangeSheafHomMap_adjoint`:
  the adjoint characterization, which is the description the source gives of the map.  Since
  transposition along `L(f')^* ⊣ R(f')_*` is a bijection, this determines the map, and it is
  what makes the definition below the canonical one rather than some morphism of its type.

Beyond its existence and that characterization Stacks 08JG asserts nothing — no functoriality
in `K` or `L`, no compatibility with pasting of squares, and no criterion for the map to be an
isomorphism — so the definition and this one equation are the whole of it.

## Implementation notes

*How the three steps enter.*  The first two steps are exactly the derived base change map of
Stacks 07A7 for this square,
`Stacks.Cohomology.DerivedBaseChangeOnTopoi.derivedBaseChangeMap`, whose adjoint
characterization `derivedBaseChangeMap_adjoint` is the two identifications of the iterated
derived pullbacks around the square followed by the derived pullback along `h` of the derived
counit — steps one and two of the source, read at the object `RSheafHom(K, L)`.  So the map
below is that one at `RSheafHom(K, L)`, followed by `R(f')_*` of the map of Stacks 08JF,
`AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`, which is step three.

*Why that composite is the adjoint of the three-step composition.*  Transposing a morphism of
the shape `a ≫ R(f')_* b` along `L(f')^* ⊣ R(f')_*` gives the transpose of `a` followed by `b`,
which is `CategoryTheory.Adjunction.homEquiv_naturality_right_symm`.  Applied to the definition
it reduces the transpose to the transpose of `derivedBaseChangeMap` followed by the map of
Stacks 08JF, and Stacks 07A7's adjoint characterization rewrites the first factor into the two
identifications and the derived counit.  That chain is the proof of
`derivedBaseChangeSheafHomMap_adjoint`, and composing in the stated order is therefore the same
as taking the adjoint of the three-step composition, as the source does.

*Why the morphisms of sites are hypotheses.*  `AlgebraicGeometry.RingedToposSiteHom` asks only
that the presenting functor be continuous, and the inverse image along a merely continuous
functor need not be exact, so such a morphism need not present a morphism of topoi at all.  Each
of the four `hmos` hypotheses is what makes the corresponding edge of the square one, and each
is required by the derived adjunction of Stacks 07A6 that the construction transposes along.
They are carried in the same shape by Stacks 07A7 and by Stacks 08JF in this development; they
are not an extra hypothesis on the square.

*Two presentations of one structure sheaf.*  A ringed topos and a ringed site carry the same
data.  The derived internal hom of Stacks 0A97 is stated for a ringed site, and is read off the
presenting sites `AlgebraicGeometry.RingedTopos.toRingedSite` of the two topoi on the top row;
the derived pullback and pushforward of Stacks 07A5 and 06YY are stated for the ringed topoi
themselves.  Nothing is transported: the structure sheaf is the same, hence so are the sheaf of
rings and the category of modules.

*The universes.*  The source statement has four independent pairs of site universes.  Both rows
are taken at `RingedTopos.{u, u, u}`, so that the object, morphism and section universes agree
and the sites are small.  The narrowing is not chosen here: it is the one carried by Stacks 07A7
and by Stacks 08JF in this development, which inherit it in turn from the K-injective
resolutions behind `Rf_*` and the K-flat resolutions of Stacks 06YS behind the derived tensor
product of Stacks 06YU.  The derived categories' own hom universe is the standard one.

## References

* [Stacks Project, Tag 08JG](https://stacks.math.columbia.edu/tag/08JG)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedBaseChangeOnTopoi
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.DerivedInternalHomBaseChangeOnTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C' C D' D : RingedTopos.{u, u, u}}
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify C'.J AddCommGrpCat.{u}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify C.J AddCommGrpCat.{u}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify D'.J AddCommGrpCat.{u}] [D'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify D.J AddCommGrpCat.{u}] [D.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} C'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} C'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} C.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} C.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf C'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} C'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf C.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} C.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom C D) (h : RingedToposSiteHom C' C)
  (f' : RingedToposSiteHom C' D') (g : RingedToposSiteHom D' D)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D'.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy g).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (g.comp f')).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f.comp h)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf D.O))
      (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites D.J C.J) (hmosh : h.u.IsMorphismOfSites C.J C'.J)
  (hmosf' : f'.u.IsMorphismOfSites D'.J C'.J) (hmosg : g.u.IsMorphismOfSites D.J D'.J)
  (sq : g.comp f' = f.comp h)
  (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)))

/-- The base change map for the internal hom in the derived category (Stacks 08JG), for a square
of morphisms of sites.  For a
commutative square of ringed topoi with `h : (Sh(C'), O_{C'}) ⟶ (Sh(C), O_C)` over
`g : (Sh(D'), O_{D'}) ⟶ (Sh(D), O_D)` and objects `K`, `L` of `D(O_C)`, the canonical map

`Lg^* Rf_* RSheafHom(K, L) ⟶ R(f')_* RSheafHom(Lh^* K, Lh^* L)`

in `D(O_{D'})`.  It is the derived base change map of Stacks 07A7 at `RSheafHom(K, L)` followed
by `R(f')_*` of the canonical map of Stacks 08JF, which is the adjoint of the three-step
composition the source describes. -/
@[stacks 08JG "derived_base_change_sheaf_hom_map, variant: the special case of a square of
morphisms of ringed topoi presented by morphisms of sites; the tag for an arbitrary commutative
square of morphisms of ringed topoi is
Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom.derivedBaseChangeSheafHomMap"]
def derivedBaseChangeSheafHomMap :
    (derivedPullback g).obj
        ((derivedPushforward f).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ⟶
      (derivedPushforward f').obj
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite C')).obj
            (op ((derivedPullback h).obj K))).obj ((derivedPullback h).obj L)) :=
  derivedBaseChangeMap f h f' g hmosf hmosh hmosf' hmosg sq
      (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite C)).obj (op K)).obj L) ≫
    (derivedPushforward f').map
      (RingedToposSiteHom.derivedPullbackSheafHomMap h hmosh K L)

/-- The adjoint characterization of the base change map (Stacks 08JG), for a square of morphisms
of sites.  Under the derived adjunction
`L(f')^* ⊣ R(f')_*` of Stacks 07A6, the base change map for the internal hom is the three-step
composition the source prescribes: the two identifications of the iterated derived pullbacks
around the square with the derived pullback along its common composite, then the derived
pullback along `h` of the derived counit `Lf^* Rf_* ⟶ id` at `RSheafHom(K, L)`, then the
canonical map of Stacks 08JF.

Since transposition is a bijection this determines the map. -/
@[stacks 08JG "derived_base_change_sheaf_hom_map: adjoint characterization, variant: the special
case of a square of morphisms of ringed topoi presented by morphisms of sites; the tag for an
arbitrary commutative square of morphisms of ringed topoi is
Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom.derivedBaseChangeSheafHomMap_adjoint"]
theorem derivedBaseChangeSheafHomMap_adjoint :
    ((derivedAdjunction f' hmosf').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite C)).obj (op K)).obj L)))
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite C')).obj
            (op ((derivedPullback h).obj K))).obj ((derivedPullback h).obj L))).symm
        (derivedBaseChangeSheafHomMap f h f' g hmosf hmosh hmosf' hmosg sq K L) =
      (derivedPullbackCompIsoLeft f' g hmosf' hmosg).hom.app
          ((derivedPushforward f).obj
            (((RingedSite.derivedSheafHomBifunctor
              (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫
        (derivedPullbackCompIsoRight f h f' g hmosf hmosh sq).inv.app
          ((derivedPushforward f).obj
            (((RingedSite.derivedSheafHomBifunctor
              (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫
        (derivedPullback h).map ((derivedAdjunction f hmosf).counit.app
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫
        RingedToposSiteHom.derivedPullbackSheafHomMap h hmosh K L := by
  refine (Adjunction.homEquiv_naturality_right_symm _ _ _).trans
    ((congrArg (· ≫ RingedToposSiteHom.derivedPullbackSheafHomMap h hmosh K L)
      (Stacks.CategoryTheory.BaseChange.homEquiv_symm_map
        (derivedAdjunction f hmosf) (derivedAdjunction f' hmosf')
        (derivedPullbackCompIsoLeft f' g hmosf' hmosg)
        (derivedPullbackCompIsoRight f h f' g hmosf hmosh sq)
        (((RingedSite.derivedSheafHomBifunctor
          (RingedTopos.toRingedSite C)).obj (op K)).obj L))).trans ?_)
  simp only [Category.assoc]

end Stacks.Cohomology.DerivedInternalHomBaseChangeOnTopoi

end

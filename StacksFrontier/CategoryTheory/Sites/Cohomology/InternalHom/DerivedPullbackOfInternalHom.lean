module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback and the internal hom in the derived category

Let `h : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi and let `K`, `L` be objects of
`D(O')`. **Stacks 08JF** asserts a canonical map

`Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)`

in `D(O)`, and this file constructs it by the three steps of the source.

By the tensor–internal-Hom bijection of Stacks 08J8 such a map is the same thing as a map
`Lh^* RSheafHom(K, L) ⊗^L_O Lh^* K ⟶ Lh^* L`. The source of that arrow is
`Lh^*(RSheafHom(K, L) ⊗^L_{O'} K)` by the monoidality of derived pullback, Stacks 07A4, so it
suffices to construct `RSheafHom(K, L) ⊗^L_{O'} K ⟶ L` and apply `Lh^*`; and that evaluation
map is the arrow corresponding to the identity of `RSheafHom(K, L)` under Stacks 08J8 again.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomCounit`: the evaluation map
  `RSheafHom(K, L) ⊗^L_O K ⟶ L`, the arrow corresponding to the identity of `RSheafHom(K, L)`
  under Stacks 08J8. It is the counit of that bijection, the companion of the unit
  `AlgebraicGeometry.RingedSite.derivedDiagonal`.
* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomPairing`: the map
  `Lh^* RSheafHom(K, L) ⊗^L_O Lh^* K ⟶ Lh^* L`, namely the pullback of the evaluation map read
  through the comparison of Stacks 07A4.
* `AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`: **Stacks 08JF**, the
  canonical map `Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)`, the arrow corresponding to
  that pairing under Stacks 08J8.

## Main results

Stacks 08JF asserts nothing about the map beyond its existence and the construction above — in
particular no functoriality in `K` or `L` and no compatibility with composition of morphisms of
ringed topoi — so the three definitions are the whole of it, and there is no separate theorem to
prove. Each map is pinned by its definition rather than by a characterising equation: it *is*
the composite the source prescribes, so it is not an unconstrained morphism of its type. The
equation `derivedCurryHomEquiv … (derivedPullbackSheafHomMap …) = derivedPullbackSheafHomPairing
…`, which holds by `AddEquiv.apply_symm_apply`, cannot be stated: elaborating the coercion of
the morphism-group `AddEquiv` of Stacks 08J8 at these arguments exhausts the recursion depth,
and raising the recursion limit is a workaround this development does not accept. The same
limitation is recorded for the unit in the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDiagonal`.

## Implementation notes

A ringed topos and a ringed site carry the same data, and both the derived internal Hom of
Stacks 0A97 and the bijection of Stacks 08J8 are stated for a ringed site, so they are read off
the presenting ringed sites `AlgebraicGeometry.RingedTopos.toRingedSite` of the two ringed
topoi; the derived pullback of Stacks 06YY and the comparison of Stacks 07A4 are stated for the
ringed topoi themselves. Nothing is transported: the two structures have the same structure
sheaf, hence the same sheaf of rings and the same category of modules.

The two sides also present the derived tensor product of Stacks 06YU differently — the
internal-Hom side through `Stacks.SheafOfModules.derivedTensorProductFunctor` of a ringed site,
the pullback side through `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of a
structure sheaf — and those are two independent choices of one and the same bifunctor up to
isomorphism. `AlgebraicGeometry.RingedSite.derivedTensorObjIso` identifies them, and it appears
exactly twice: once on the target topos, to read the evaluation map at the bifunctor Stacks 07A4
is stated for, and once on the source topos, to read the pairing at the bifunctor Stacks 08J8 is
stated for.

The hypothesis `hmos` that the continuous functor presenting `h` is a morphism of sites is not a
weakening. `AlgebraicGeometry.RingedToposSiteHom` asks only for continuity, and the inverse
image along a merely continuous functor need not be exact, so such an `h` need not present a
morphism of topoi at all; `hmos` is what makes it one. It is carried for the same reason, and in
the same shape, by Stacks 07A4 in this development.

Both ringed topoi are taken at `RingedTopos.{u, u, u}`, so that the object, morphism and
section universes agree and the sites are small. This narrowing is not chosen here: it is the
one carried by Stacks 07A4 and by Stacks 08J8 in this development, which inherit it in turn
from the K-flat resolutions of Stacks 06YS behind the derived tensor product of Stacks 06YU.
The derived categories' own hom universe is the standard one.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSite

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- The evaluation map `RSheafHom(K, L) ⊗^L_O K ⟶ L` on a ringed site: the morphism
corresponding to the identity of `RSheafHom(K, L)` under the tensor–internal-Hom bijection of
Stacks 08J8. It is the counit of that bijection, as `derivedDiagonal` is its unit. -/
def derivedSheafHomCounit
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor Z).obj
        (((derivedSheafHomBifunctor Z).obj (op K)).obj L)).obj K ⟶ L :=
  derivedCurryHomEquiv Z (((derivedSheafHomBifunctor Z).obj (op K)).obj L) K L (𝟙 _)

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (h : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy h).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : h.u.IsMorphismOfSites Y.J X.J)
  (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- The map `Lh^* RSheafHom(K, L) ⊗^L_O Lh^* K ⟶ Lh^* L` of Stacks 08JF: the derived pullback of
the evaluation map `RSheafHom(K, L) ⊗^L_{O'} K ⟶ L`, whose source is identified with the derived
tensor product of the pullbacks by the monoidality of derived pullback, Stacks 07A4. -/
def derivedPullbackSheafHomPairing :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor (RingedTopos.toRingedSite X)).obj
        ((derivedPullback h).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite Y)).obj (op K)).obj L))).obj
      ((derivedPullback h).obj K) ⟶ (derivedPullback h).obj L :=
  (RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite X)
        ((derivedPullback h).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite Y)).obj (op K)).obj L))
        ((derivedPullback h).obj K)).hom ≫
    ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso h hmos).app
        ((((RingedSite.derivedSheafHomBifunctor
          (RingedTopos.toRingedSite Y)).obj (op K)).obj L), K)).inv ≫
      (derivedPullback h).map
        ((RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite Y)
              (((RingedSite.derivedSheafHomBifunctor
                (RingedTopos.toRingedSite Y)).obj (op K)).obj L) K).inv ≫
          RingedSite.derivedSheafHomCounit (RingedTopos.toRingedSite Y) K L)

/-- **Stacks 08JF: the canonical map `Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)`** in
`D(O)`, for a morphism of ringed topoi `h : (Sh(C), O) ⟶ (Sh(C'), O')` and objects `K`, `L` of
`D(O')`. It is the arrow corresponding to `derivedPullbackSheafHomPairing` under the
tensor–internal-Hom bijection of Stacks 08J8 on the source topos. -/
@[stacks 08JF]
def derivedPullbackSheafHomMap :
    (derivedPullback h).obj
        (((RingedSite.derivedSheafHomBifunctor
          (RingedTopos.toRingedSite Y)).obj (op K)).obj L) ⟶
      ((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj
        (op ((derivedPullback h).obj K))).obj ((derivedPullback h).obj L) :=
  (RingedSite.derivedCurryHomEquiv (RingedTopos.toRingedSite X)
      ((derivedPullback h).obj
        (((RingedSite.derivedSheafHomBifunctor
          (RingedTopos.toRingedSite Y)).obj (op K)).obj L))
      ((derivedPullback h).obj K) ((derivedPullback h).obj L)).symm
    (derivedPullbackSheafHomPairing h hmos K L)

end AlgebraicGeometry.RingedToposSiteHom

end

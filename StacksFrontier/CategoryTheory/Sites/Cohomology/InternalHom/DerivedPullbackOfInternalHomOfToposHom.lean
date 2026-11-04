module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived pullback and the internal hom, for a morphism of ringed topoi

Let `h : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi and let `K`, `L` be objects
of `D(O')`. **Stacks 08JF** asserts a canonical map

`Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)`

in `D(O)`. By the tensor–internal-Hom bijection of Stacks 08J8 such a map is the same thing as a
map `Lh^* RSheafHom(K, L) ⊗^L_O Lh^* K ⟶ Lh^* L`; the source of that arrow is
`Lh^*(RSheafHom(K, L) ⊗^L_{O'} K)` by Stacks 07A4, so it is `Lh^*` of the evaluation map
`RSheafHom(K, L) ⊗^L_{O'} K ⟶ L`, the arrow corresponding to the identity under Stacks 08J8.

Here `h` is a morphism of ringed topoi in the sense of Stacks 01D3, part (2): a morphism of the
underlying topoi together with the map of structure sheaves, with no functor between the
underlying sites and no hypothesis on it.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.derivedPullbackSheafHomPairing`: the map
  `Lh^* RSheafHom(K, L) ⊗^L_O Lh^* K ⟶ Lh^* L`.
* `AlgebraicGeometry.RingedToposHom.derivedPullbackSheafHomMap`: **Stacks 08JF**, the canonical
  map `Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)`.

## Implementation notes

The construction is the one of
`AlgebraicGeometry.RingedToposSiteHom.derivedPullbackSheafHomMap`, with the derived pullback of
Stacks 06YY and the comparison of Stacks 07A4 replaced by their versions for a morphism of
ringed topoi, `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback` and
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`. Neither takes a
morphism-of-sites hypothesis — the exactness of the inverse image is a field of the morphism of
topoi — so the map below takes none either.

Both ringed topoi are taken at `RingedTopos.{u, u, u}`: the derived tensor product of Stacks 06YU
and the bijection of Stacks 08J8 are available only at those universes. The derived internal
Hom of Stacks 0A97 is read off the presenting ringed sites
`AlgebraicGeometry.RingedTopos.toRingedSite`, which carry the same structure sheaf.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

namespace AlgebraicGeometry.RingedToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (h : RingedToposHom X Y)
  (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-- The map `Lh^* RSheafHom(K, L) ⊗^L_O Lh^* K ⟶ Lh^* L` of Stacks 08JF, for a morphism of
ringed topoi `h`: the derived pullback of the evaluation map `RSheafHom(K, L) ⊗^L_{O'} K ⟶ L`,
whose source is identified with the derived tensor product of the pullbacks by Stacks 07A4. -/
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
    ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso h).app
        ((((RingedSite.derivedSheafHomBifunctor
          (RingedTopos.toRingedSite Y)).obj (op K)).obj L), K)).inv ≫
      (derivedPullback h).map
        ((RingedSite.derivedTensorObjIso (RingedTopos.toRingedSite Y)
              (((RingedSite.derivedSheafHomBifunctor
                (RingedTopos.toRingedSite Y)).obj (op K)).obj L) K).inv ≫
          RingedSite.derivedSheafHomCounit (RingedTopos.toRingedSite Y) K L)

/-- **Stacks 08JF: the canonical map `Lh^* RSheafHom(K, L) ⟶ RSheafHom(Lh^* K, Lh^* L)`** in
`D(O)`, for a morphism of ringed topoi `h : (Sh(C), O) ⟶ (Sh(C'), O')` in the sense of
Stacks 01D3, part (2), and objects `K`, `L` of `D(O')`. It is the arrow corresponding to
`derivedPullbackSheafHomPairing` under the tensor–internal-Hom bijection of Stacks 08J8. -/
@[stacks 08JF "for a morphism of ringed topoi in the sense of Tag 01D3, part (2) -- a morphism
of the underlying topoi together with the map of structure sheaves, with no functor between the
underlying sites"]
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
    (derivedPullbackSheafHomPairing h K L)

end AlgebraicGeometry.RingedToposHom

end

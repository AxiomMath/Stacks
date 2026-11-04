module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedPullbackOfInternalHomOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the internal hom, for a commutative square of ringed topoi

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

in `D(O_{D'})`: the map adjoint, under `L(f')^* ⊣ R(f')_*`, to the composition of the
identification `L(f')^* Lg^* = Lh^* Lf^*` supplied by the square, `Lh^*` of the derived counit
`Lf^* Rf_* ⟶ id` at `RSheafHom(K, L)`, and the canonical map of Stacks 08JF.

The four arrows are morphisms of ringed topoi in the sense of Stacks 01D3, part (2) — a morphism
of the underlying topoi together with the map of structure sheaves — and the only hypothesis on
them is the commutativity of the square.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom.derivedBaseChangeSheafHomMap`:
  **Stacks 08JG**, the canonical base change map.

## Main results

* `Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom.derivedBaseChangeSheafHomMap_adjoint`:
  the adjoint characterization, which is how the source defines the map; since transposition
  along `L(f')^* ⊣ R(f')_*` is a bijection it determines the map.

## Implementation notes

The first two steps of the source are the derived base change map of Stacks 07A7 for the square,
`Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMap`, at `RSheafHom(K, L)`, whose
adjoint is the two identifications of iterated derived pullbacks followed by `Lh^*` of the counit.
The map below is that one followed by `R(f')_*` of the map of Stacks 08JF,
`AlgebraicGeometry.RingedToposHom.derivedPullbackSheafHomMap`; transposing a morphism of the
shape `a ≫ R(f')_* b` gives the transpose of `a` followed by `b`, which is the adjoint
characterization.

The two ringed topoi of the top row are taken at `RingedTopos.{u, u, u}`, where the derived
tensor product of Stacks 06YU and the derived internal Hom of Stacks 0A97 are available; the
universes of the two ringed topoi of the bottom row are free.

## References

* [Stacks Project, Tag 08JG](https://stacks.math.columbia.edu/tag/08JG)
* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom

namespace Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom

universe u vD' uD' wD' vD uD wD

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {C' C : RingedTopos.{u, u, u}}
  {D' : RingedTopos.{vD', uD', wD'}} {D : RingedTopos.{vD, uD, wD}}
  [C'.J.HasSheafCompose (forget RingCat.{u})] [C.J.HasSheafCompose (forget RingCat.{u})]
  [D'.J.HasSheafCompose (forget RingCat.{wD'})] [D.J.HasSheafCompose (forget RingCat.{wD})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify C'.J AddCommGrpCat.{u}] [C'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify C.J AddCommGrpCat.{u}] [C.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify D'.J AddCommGrpCat.{wD'}] [D'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify D.J AddCommGrpCat.{wD}] [D.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify C'.J (Type u)] [HasSheafify C.J (Type u)]
  [HasSheafify D'.J (Type wD')] [HasSheafify D.J (Type wD)]
  (f : RingedToposHom C D) (h : RingedToposHom C' C)
  (f' : RingedToposHom C' D') (g : RingedToposHom D' D)
  (sq : g.comp f' = f.comp h)
  (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf C.O)))

/-- **Stacks 08JG: the base change map for the internal hom in the derived category.**  For a
commutative square of morphisms of ringed topoi, with `h : (Sh(C'), O_{C'}) ⟶ (Sh(C), O_C)`
over `g : (Sh(D'), O_{D'}) ⟶ (Sh(D), O_D)`, and objects `K`, `L` of `D(O_C)`, the canonical map

`Lg^* Rf_* RSheafHom(K, L) ⟶ R(f')_* RSheafHom(Lh^* K, Lh^* L)`

in `D(O_{D'})`: the derived base change map of Stacks 07A7 at `RSheafHom(K, L)` followed by
`R(f')_*` of the canonical map of Stacks 08JF.  Its transpose is the three-step composition of
the source, `derivedBaseChangeSheafHomMap_adjoint`. -/
@[stacks 08JG "for a commutative square of morphisms of ringed topoi in the sense of Tag 01D3,
part (2), with no hypothesis beyond commutativity"]
def derivedBaseChangeSheafHomMap :
    (derivedPullback g).obj
        ((derivedPushforward f).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ⟶
      (derivedPushforward f').obj
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite C')).obj
            (op ((derivedPullback h).obj K))).obj ((derivedPullback h).obj L)) :=
  derivedBaseChangeMap f h f' g sq
      (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite C)).obj (op K)).obj L) ≫
    (derivedPushforward f').map (RingedToposHom.derivedPullbackSheafHomMap h K L)

/-- **Stacks 08JG, the adjoint characterization.**  Under the derived adjunction
`L(f')^* ⊣ R(f')_*` of Stacks 07A6, the base change map for the internal hom is the composition
the source prescribes: the identification `L(f')^* Lg^* = Lh^* Lf^*` of the iterated derived
pullbacks around the square (through the derived pullback along its common composite), then
`Lh^*` of the derived counit `Lf^* Rf_* ⟶ id` at `RSheafHom(K, L)`, then the canonical map of
Stacks 08JF.  Since transposition is a bijection this determines the map. -/
@[stacks 08JG "adjoint characterization, for a commutative square of morphisms of ringed topoi in
the sense of Tag 01D3, part (2)"]
theorem derivedBaseChangeSheafHomMap_adjoint :
    ((derivedAdjunction f').homEquiv
        ((derivedPullback g).obj ((derivedPushforward f).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite C)).obj (op K)).obj L)))
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite C')).obj
            (op ((derivedPullback h).obj K))).obj ((derivedPullback h).obj L))).symm
        (derivedBaseChangeSheafHomMap f h f' g sq K L) =
      (derivedPullbackCompIsoLeft f' g).hom.app
          ((derivedPushforward f).obj
            (((RingedSite.derivedSheafHomBifunctor
              (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫
        (derivedPullbackCompIsoRight f h f' g sq).inv.app
          ((derivedPushforward f).obj
            (((RingedSite.derivedSheafHomBifunctor
              (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫
        (derivedPullback h).map ((derivedAdjunction f).counit.app
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫
        RingedToposHom.derivedPullbackSheafHomMap h K L := by
  refine (Adjunction.homEquiv_naturality_right_symm _ _ _).trans ?_
  exact (congrArg (fun arrow => arrow ≫ RingedToposHom.derivedPullbackSheafHomMap h K L)
      (derivedBaseChangeMap_adjoint f h f' g sq
        (((RingedSite.derivedSheafHomBifunctor
          (RingedTopos.toRingedSite C)).obj (op K)).obj L))).trans
    ((Category.assoc _ _ _).trans
      (congrArg (fun arrow =>
        (derivedPullbackCompIsoLeft f' g).hom.app
          ((derivedPushforward f).obj
            (((RingedSite.derivedSheafHomBifunctor
              (RingedTopos.toRingedSite C)).obj (op K)).obj L)) ≫ arrow)
        (Category.assoc _ _ _)))

end Stacks.Cohomology.DerivedInternalHomBaseChangeOfToposHom

end

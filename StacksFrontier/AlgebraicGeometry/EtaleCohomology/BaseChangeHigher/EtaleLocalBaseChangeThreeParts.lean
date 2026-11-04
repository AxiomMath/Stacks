module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalDerivedBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalHigherBaseChange

/-!
# The three parts of the étale-local criterion for base change

Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S`
factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, and let

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

be the induced cartesian squares, where `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`.  Let `F` be a sheaf
of sets on the small étale site of `T`, let `𝓖` be an abelian sheaf on it and let `K` be an
object of its unbounded derived category, and write `F|ᵢ`, `𝓖|ᵢ`, `K|ᵢ` for their inverse images
along `Tᵢ ⟶ T`.  Stacks 0EZR asserts three implications: if the base change map of the `i`-th
local square is an isomorphism for every `i`, then so is the base change map of the outer square
— for a sheaf of sets, for an object of the unbounded derived category, and for the higher direct
images in each degree.

This file states all three at once, which is the content of the tag, and proves them from the
three parts carried out separately:

* part (1) is `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIso_local`;
* part (2) is
  `Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_of_isIso_local`;
* part (3) is `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_local`.

## Main results

* `Stacks.EtaleCohomology.etaleLocalBaseChange` — **Stacks 0EZR**, all three parts.

## Implementation notes

The geometry of the diagram is independent of the coefficients, while the three parts speak about
three different objects over it — a sheaf of sets, an abelian sheaf and an object of the derived
category of abelian sheaves.  `Stacks.EtaleCohomology.EtaleLocalBaseChangeData` carries the
diagram together with one sheaf, so the statement below takes the data at set-valued coefficients
(whose sheaf is the `F` of part (1)) together with the abelian sheaf of part (3) and the derived
object of part (2), and the two abelian parts are applied to the same diagram re-read at abelian
coefficients by `Stacks.EtaleCohomology.EtaleLocalBaseChangeData.withSheaf`.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe w t w' t' u v z

namespace Stacks.EtaleCohomology

/-- The data of Stacks 0EZR with its sheaf replaced by a sheaf with values in another coefficient
category.  The diagram, the covering, the factorizations and the induced cartesian squares are
geometric and do not involve the coefficients; only the last field of
`Stacks.EtaleCohomology.EtaleLocalBaseChangeData` does. -/
def EtaleLocalBaseChangeData.withSheaf {C : Type w} [Category.{t} C]
    (D : EtaleLocalBaseChangeData.{u, z, t, w} C) {C' : Type w'} [Category.{t'} C']
    (G : Sheaf D.T.smallEtaleTopology C') : EtaleLocalBaseChangeData.{u, z, t', w'} C' where
  X := D.X
  Y := D.Y
  S := D.S
  T := D.T
  f := D.f
  h := D.h
  e := D.e
  g := D.g
  cartesian := D.cartesian
  I := D.I
  U := D.U
  u := D.u
  cover := D.cover
  V := D.V
  v := D.v
  etale_v := D.etale_v
  f_i := D.f_i
  factorization := D.factorization
  Y_i := D.Y_i
  h_i := D.h_i
  toY_i := D.toY_i
  upper_cartesian := D.upper_cartesian
  T_i := D.T_i
  g_i := D.g_i
  toT_i := D.toT_i
  lower_cartesian := D.lower_cartesian
  e_i := D.e_i
  e_i_compatible := D.e_i_compatible
  local_cartesian := D.local_cartesian
  F := G

/-- **Stacks 0EZR.**  Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering of `X` such that each
composite `Uᵢ → X → S` factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, and let

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

be the induced cartesian squares, with `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`.  Let `F` be a sheaf
of sets on the small étale site of `T`, let `𝓖` be an abelian sheaf on it, let `K` be an object of
its unbounded derived category, and write `F|ᵢ`, `𝓖|ᵢ` and `K|ᵢ` for the inverse images along
`Tᵢ ⟶ T`.  Then:

1. if `fᵢ^{-1} g_{i,*} F|ᵢ ⟶ h_{i,*} eᵢ^{-1} F|ᵢ` is an isomorphism for every `i`, so is
   `f^{-1} g_* F ⟶ h_* e^{-1} F`;
2. if `fᵢ^{-1} Rg_{i,*} K|ᵢ ⟶ Rh_{i,*} eᵢ^{-1} K|ᵢ` is an isomorphism for every `i`, so is
   `f^{-1} Rg_* K ⟶ Rh_* e^{-1} K`;
3. for every degree `q`, if `fᵢ^{-1} R^q g_{i,*} 𝓖|ᵢ ⟶ R^q h_{i,*} eᵢ^{-1} 𝓖|ᵢ` is an
   isomorphism for every `i`, so is `f^{-1} R^q g_* 𝓖 ⟶ R^q h_* e^{-1} 𝓖`.

The hypotheses are exactly the source's: the square is cartesian, the family `{Uᵢ → X}` is an
étale covering, each `Uᵢ → S` factors through an étale `Vᵢ → S`, and the two families of induced
squares are cartesian.  Nothing is assumed of `f`, `g`, `h`, `e` beyond that, and the coefficients
are arbitrary sheaves of sets, arbitrary abelian sheaves and arbitrary objects of the unbounded
derived category.

The three parts are proved in
`Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_app_of_isIso_local`,
`Stacks.EtaleCohomology.isIso_etaleAbelianDerivedBaseChange_app_of_isIso_local` and
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_local`; each of them restricts
the base change map of the outer square to `Uᵢ`, compares it there with the base change map of
the `i`-th local square through the two decompositions of the rectangle `Uᵢ ⟶ X ⟶ S`, and
concludes by the locality of invertibility on the small étale site. -/
@[stacks 0EZR "parts (1), (2) and (3), as the conjunction of the three implications"]
theorem etaleLocalBaseChange
    (D : EtaleLocalBaseChangeData.{u, z, _, _} (Type (max (u + 1) v)))
    (𝓖 : Sheaf D.T.smallEtaleTopology Ab.{u + 1})
    (K : DerivedCategory (Sheaf D.T.smallEtaleTopology Ab.{u + 1})) :
    ((∀ i : D.I, IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i)
          (D.f_i i) (D.local_cartesian i).w.symm).app
            ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) →
        IsIso ((smallEtaleSetsBaseChange.{u, v} D.e D.h D.g D.f
          D.cartesian.w.symm).app D.F)) ∧
      ((∀ i : D.I, IsIso ((etaleAbelianDerivedBaseChange.{u, 0} (D.g_i i) (D.f_i i) (D.e_i i)
            (D.h_i i) (D.local_cartesian i).w.symm).app
              ((etaleAbelianDerivedInverseImage.{u, 0} (D.toT_i i)).obj K))) →
          IsIso ((etaleAbelianDerivedBaseChange.{u, 0} D.g D.f D.e D.h
            D.cartesian.w.symm).app K)) ∧
        ∀ q : ℕ, (∀ i : D.I, IsIso ((higherBaseChangeMapAb (D.f_i i) (D.g_i i) (D.h_i i)
            (D.e_i i) (D.local_cartesian i).w q).app
              ((smallEtalePullbackAb (D.toT_i i)).obj 𝓖))) →
          IsIso ((higherBaseChangeMapAb D.f D.g D.h D.e D.cartesian.w q).app 𝓖) :=
  ⟨isIso_smallEtaleSetsBaseChange_app_of_isIso_local D,
    isIso_etaleAbelianDerivedBaseChange_app_of_isIso_local (D.withSheaf 𝓖) K,
    fun q => isIso_higherBaseChangeMapAb_app_of_isIso_local (D.withSheaf 𝓖) q⟩

end Stacks.EtaleCohomology

end

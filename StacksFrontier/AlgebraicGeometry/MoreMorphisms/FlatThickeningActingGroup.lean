module

public import StacksFrontier.Algebra.Homology.HomBicomplexExt
public import StacksFrontier.AlgebraicGeometry.Conormal.SquareFlatIso
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationActionGlobal
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentExtZero

/-!
# The acting group of a flat first-order deformation, as derivations into the conormal sheaf

Let
```
X --i--→ X'
|        |
f        f'
↓        ↓
S --t--→ S'
```
be a cartesian square of schemes with `i` and `t` immersions and `f'` flat.  For `i` and `t`
first-order thickenings this is the situation of [Stacks Project, Tag 0D14]: `f : X ⟶ S` is a
morphism, `S ⊂ S'` a first order thickening and `f' : X' ⟶ S'` a flat deformation of `f` over
it.  The source states the two sets it computes there — the isomorphism classes of deformations
and the automorphisms of one of them — in terms of

`Ext^i_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'})`.

This file identifies the degree `0` group of that family with the group of derivations into the
conormal sheaf of `X` in `X'`,

`Ext⁰_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'}) = Hom_{𝒪_X}(Ω_{X/S}, 𝒞_{X/X'})`,

which is the form in which a difference of two lifts of a morphism across a first order
thickening is produced: two lifts over `S` differ by an `𝒪_S`-derivation with values in
`𝒞_{X/X'}`.

## Main definitions

* `Stacks.Thickenings.pullbackConormalModule`: `f^*𝒞_{S/S'}`, read as an object of
  `AlgebraicGeometry.Scheme.Modules X`.  Its companion `𝒞_{X/X'}` at the same spelling is
  `Stacks.Thickenings.conormalModules`.
* `Stacks.Thickenings.flatThickeningActingGroupAddEquiv`: the identification above, as an
  isomorphism of additive groups.

## Implementation notes

Two results are composed.  `Ext⁰` out of the naive cotangent complex is a homomorphism out
of `Ω_{X/S}`, which is `AlgebraicGeometry.Scheme.naiveCotangentExtZeroAddEquiv`; and the
canonical map `f^*𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] is invertible, which is the
flat base-change clause of [Stacks Project, Tag 0473],
`Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`.  The second is where the flatness of
`f'` and the base-change identity `X = S ×_{S'} X'` are used; the first needs no hypothesis at
all.

Nothing beyond a cartesian square of immersions with flat ambient map is assumed, which is less
than [Stacks Project, Tag 0D14] asks for: neither `i` nor `t` need be a *first order*
thickening, and `f` need not be flat.  Specialized to a morphism of first-order thickenings this
is the identification of the group that tag's two clauses are stated over; for that reading the
invertibility is `Stacks.Thickenings.isIso_firstOrderThickeningConormalSheafMap`, the
(1) ⟹ (2) half of [Stacks Project, Tag 063Y] for schemes, which is the same map by
`Stacks.Thickenings.firstOrderThickeningConormalSheafMap_eq`.

`Stacks.Thickenings.conormalModules` and `Stacks.Thickenings.pullbackConormalModule` exist to
fix the spelling of the category.  The conormal sheaf of an immersion of schemes is stated over
`RingedSpaceModuleAdjunction.structureSheafRing` of the underlying ringed space, while
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` is stated over
`AlgebraicGeometry.Scheme.Modules`, and only the latter has an `Abelian` instance that instance
search finds for a scheme; a group of homomorphisms written between the two spellings therefore
has no addition that can be synthesized, although the two categories are definitionally equal.
Naming the conormal sheaves at the `Scheme.Modules` spelling settles that once, with no
transport.

No `stacks` attribute is carried.  This is neither clause of [Stacks Project, Tag 0D14] — those
are the principal homogeneous space of deformation classes under `Ext¹` and the identification
of the automorphisms with `Ext⁰`, and neither is proved here or anywhere in this library — but
the identification of the group the two clauses are stated over, assembled from two tagged
results.

## References

* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473), flat base change of the
  conormal sheaf
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y), the ideal sheaf of `X`
  in `X'` is `f^*𝒞_{S/S'}` for a flat deformation
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J),
  `H⁰(NL_{X/S}) = Ω_{X/S}`
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

variable {X X' S S' : Scheme.{u}}

/-- The pullback `f^*𝒞_{S/S'}` of the conormal sheaf of an immersion along a morphism into its
source, read as an object of `AlgebraicGeometry.Scheme.Modules X`. -/
abbrev pullbackConormalModule (f : X ⟶ S) (t : S ⟶ S') [IsImmersion t] : X.Modules :=
  (modulePullback f.toLRSHom.toShHom).obj (Stacks.Conormal.conormalSheaf t)

/-- **The acting group of [Stacks Project, Tag 0D14], as derivations into the conormal sheaf.**
For a cartesian square of schemes with `i`, `t` immersions and the ambient map `f'` flat,

`Ext⁰_{𝒪_X}(NL_{X/S}, f^*𝒞_{S/S'}) = Hom_{𝒪_X}(Ω_{X/S}, 𝒞_{X/X'})`.

The left-hand group is the one the source states its two clauses over; the right-hand group is
the one a difference of two lifts of `f` across `X ⊂ X'` lives in.  The identification is the
composite of `Ext⁰` out of a complex in degrees `≤ 0` being a homomorphism out of its `H⁰`,
which is `Ω_{X/S}` by [Stacks Project, Tag 0D0J], with the invertibility of the canonical map
`f^*𝒞_{S/S'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 0473], which is where the flatness and the
base-change identity enter. -/
def flatThickeningActingGroupAddEquiv (i : X ⟶ X') (t : S ⟶ S') [IsImmersion i] [IsImmersion t]
    (f : X ⟶ S) (f' : X' ⟶ S') [Flat f'] (sq : IsPullback i f f' t) :
    AlgebraicGeometry.Scheme.naiveCotangentExt f (pullbackConormalModule f t) 0 ≃+
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentials f ⟶ conormalModules i) :=
  (AlgebraicGeometry.Scheme.naiveCotangentExtZeroAddEquiv f
      (pullbackConormalModule f t)).trans
    (CochainComplex.HomBicomplex.postcompAddEquiv
      (@asIso _ _ _ _ (Stacks.Immersion.immersionConormalSheafMap i t f f'
          (Stacks.Immersion.toShHom_square sq.w))
        (Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat i t f f' sq)))

end Stacks.Thickenings

end

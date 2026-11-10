module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf

/-!
# Transferring a conormal map across a comparison of module categories

Both conormal maps of this development are built in the same two steps.  At the level of
algebraic spaces, `AlgebraicGeometry.Space.conormalMap` (Stacks 04CP) is the comparison
isomorphism `f^*(i')^* ≅ i^*g^*` of `AlgebraicGeometry.Space.conormalPullbackCompIso`, evaluated
at the defining ideal sheaf of the lower closed subspace, followed by the inverse image along the
upper inclusion of the map `g^*𝓘' ⟶ 𝓘` of `AlgebraicGeometry.Space.idealSheafMap`.  At the level
of ringed spaces, `Stacks.ClosedImmersion.conormalSheafMap` (the map of Stacks 01R4 for closed
immersions) is the identical composite of
`Stacks.ClosedImmersion.pullbackCompIso` and `Stacks.ClosedImmersion.idealSheafMap`.

This file says that a comparison of the two categories of modules which is compatible with
inverse image carries the one map to the other **as soon as it does so on the defining ideals**.
That is the naturality in squares of closed subspaces which the comparison of the conormal
*objects* does not by itself provide, and it is item 3 of the carry note of the file
`ConormalShortExact.lean` under
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/PseudoCoherent/LocalCompleteIntersection/`.
The statement at the two concrete families of functors is in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleSchemeComparisonSquare.lean`.

## The shape of the transfer

Write `A?` for the four categories of modules on the space side of a square of closed subspaces
— on the ambient spaces `X`, `X'` and on the subspaces `Z`, `Z'` — and `B?` for the four on the
scheme side; write `ai, ai', ag, af` for the four inverse-image functors of the square on the one
side and `bi, bi', bg, bf` for those on the other.  A comparison is a quadruple of functors
`EX, EX', EZ, EZ'`, one per corner, together with a morphism comparing `E` after inverse image
with inverse image after `E`, one for each edge.  Given

* the comparison morphisms are natural at the map of ideals (`hpullback`),
* the comparison carries the map of defining ideals to the map of defining ideals (`hideal`),
* the two composition comparisons agree under the edge comparisons (`hpaste`),
* the composition comparison on the scheme side is natural (`hbL`),

the square of conormal maps commutes.  Nothing in the argument uses invertibility of any of
these morphisms, so they are taken as bare morphisms and not as isomorphisms: the two
identifications a consumer will have are isomorphisms, but an equality of composites is all that
is needed, and asking for less makes the statement apply to a comparison which is only known to
be a morphism in one direction.

## Main results

* `Stacks.ConormalComparison.comparison_square`: the transfer, for arbitrary functors between
  arbitrary categories.  This is the whole mathematical content of the naturality; the kernel has
  no inverse image to unfold here, which is why it is stated in this generality — the same device
  as `AlgebraicGeometry.Space.comp_app_of_paste`.
* The scheme-side input `hbL`, the naturality in the module of the composition comparison
  `Stacks.ClosedImmersion.pullbackCompIso`, is the base's
  `Stacks.ClosedImmersion.pullbackCompIso_naturality` of
  `StacksFrontier/AlgebraicGeometry/ProjectiveBundleConormal/BaseChange.lean`, which exhibits that
  comparison as the component of the natural isomorphism
  `Stacks.ClosedImmersion.pullbackCompNatIso`.
* `Stacks.ClosedImmersion.conormalSheafMap_eq_of_comm` and
  `Stacks.Thickenings.universalConormalSheafMap_eq`: the defining equations of the scheme-level
  conormal map and of its form at a morphism of universal first-order thickenings
  (Stacks 04F7).  These are what let a consumer pass between the folded spelling of those maps
  and the composite the transfer speaks about; the second of them is what makes the transfer
  apply to `Stacks.Thickenings.universalConormalSheaf`, which is the conormal sheaf of the
  inclusion of a universal first-order thickening.

## Implementation notes

**Why the composition comparison is repackaged as a natural isomorphism.**
`Stacks.ClosedImmersion.pullbackCompIso` is defined at one module at a time, as the composite of
the components at that module of three isomorphisms of functors.  Naturality is therefore not
available by name, and proving it by hand would mean chaining the three naturality squares across
two categories of sheaves of modules — goals of exactly the kind that neither `rw` nor `simp`
fires on.  `pullbackCompNatIso` composes the three isomorphisms as functors instead, so that
naturality is `CategoryTheory.NatTrans.naturality`, and
`pullbackCompNatIso_hom_app` identifies its components with `pullbackCompIso` by `rfl`:
projecting a composite of isomorphisms of functors at an object is an iota step, available at
every transparency.

## References

* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP), the map of conormal
  modules of a square of closed subspaces of algebraic spaces.
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4), the map of conormal
  sheaves of a square of closed immersions.
* [Stacks Project, Tag 04F7](https://stacks.math.columbia.edu/tag/04F7), its form at a morphism
  of universal first-order thickenings.
* [Stacks Project, Tag 06CB](https://stacks.math.columbia.edu/tag/06CB) and
  [Stacks Project, Tag 06CC](https://stacks.math.columbia.edu/tag/06CC), the two consumers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.ConormalComparison

variable {AX AX' AZ AZ' BX BX' BZ BZ' : Type*}
  [Category AX] [Category AX'] [Category AZ] [Category AZ']
  [Category BX] [Category BX'] [Category BZ] [Category BZ']
  (ai : AX ⥤ AZ) (ai' : AX' ⥤ AZ') (ag : AX' ⥤ AX) (af : AZ' ⥤ AZ)
  (bi : BX ⥤ BZ) (bi' : BX' ⥤ BZ') (bg : BX' ⥤ BX) (bf : BZ' ⥤ BZ)
  (EX : AX ⥤ BX) (EX' : AX' ⥤ BX') (EZ : AZ ⥤ BZ) (EZ' : AZ' ⥤ BZ')

/-- **A comparison of module categories compatible with inverse image carries one conormal map
to the other.**  The data are those of the module documentation of this file: two squares of
inverse-image functors, `ai, ai', ag, af` and `bi, bi', bg, bf`; a comparison functor `E` at each
of the four corners; a morphism `aL`, resp. `bL`, comparing the two ways around each square of
inverse images; a morphism `pI, pI', pG, pF` comparing `E` with inverse image along each of the
four edges; the two maps of ideals `m` and `n`; and the identification `eX`, `eX'` of the ideals
themselves at the two ambient corners.

The conclusion is that the square

```
  E(f^*𝒞') ----- E(conormal map) -----> E(𝒞)
     |                                    |
     v                                    v
  f^*𝒞'_scheme -- conormal map -------> 𝒞_scheme
```

commutes, its vertical arrows being the identifications of the conormal objects that `pI`, `pF`
and `eX`, `eX'` assemble.  Each conormal map is read as `aL I' ≫ ai.map m`, resp.
`bL J' ≫ bi.map n`, which is what the two definitions are.

The hypotheses are exactly the four facts listed in the module documentation, and no more: no
functor is assumed to be an equivalence, no comparison morphism to be invertible, and no
naturality is assumed of `aL`, of `pI'`, of `pG` or of `pF` beyond the single instance recorded
in `hpaste`. -/
theorem comparison_square
    (aL : ∀ M : AX', af.obj (ai'.obj M) ⟶ ai.obj (ag.obj M))
    (bL : ∀ N : BX', bf.obj (bi'.obj N) ⟶ bi.obj (bg.obj N))
    (pI : ∀ M : AX, EZ.obj (ai.obj M) ⟶ bi.obj (EX.obj M))
    (pI' : ∀ M : AX', EZ'.obj (ai'.obj M) ⟶ bi'.obj (EX'.obj M))
    (pG : ∀ M : AX', EX.obj (ag.obj M) ⟶ bg.obj (EX'.obj M))
    (pF : ∀ M : AZ', EZ.obj (af.obj M) ⟶ bf.obj (EZ'.obj M))
    {I' : AX'} {I : AX} (m : ag.obj I' ⟶ I)
    {J' : BX'} {J : BX} (n : bg.obj J' ⟶ J)
    (eX : EX.obj I ⟶ J) (eX' : EX'.obj I' ⟶ J')
    (hpullback : EZ.map (ai.map m) ≫ pI I = pI (ag.obj I') ≫ bi.map (EX.map m))
    (hideal : EX.map m ≫ eX = pG I' ≫ bg.map eX' ≫ n)
    (hpaste : EZ.map (aL I') ≫ pI (ag.obj I') ≫ bi.map (pG I')
      = pF (ai'.obj I') ≫ bf.map (pI' I') ≫ bL (EX'.obj I'))
    (hbL : bL (EX'.obj I') ≫ bi.map (bg.map eX') = bf.map (bi'.map eX') ≫ bL J') :
    EZ.map (aL I' ≫ ai.map m) ≫ pI I ≫ bi.map eX
      = (pF (ai'.obj I') ≫ bf.map (pI' I') ≫ bf.map (bi'.map eX')) ≫ bL J' ≫ bi.map n := by
  have h1 : EZ.map (ai.map m) ≫ pI I ≫ bi.map eX
      = pI (ag.obj I') ≫ bi.map (pG I') ≫ bi.map (bg.map eX') ≫ bi.map n := by
    rw [← Category.assoc (EZ.map (ai.map m)), hpullback, Category.assoc,
      ← Functor.map_comp bi (EX.map m) eX, hideal, Functor.map_comp, Functor.map_comp]
  have h2 : EZ.map (aL I') ≫ pI (ag.obj I') ≫ bi.map (pG I') ≫ bi.map (bg.map eX') ≫ bi.map n
      = pF (ai'.obj I') ≫ bf.map (pI' I')
          ≫ bL (EX'.obj I') ≫ bi.map (bg.map eX') ≫ bi.map n := by
    simpa only [Category.assoc] using
      congrArg (fun t : EZ.obj (af.obj (ai'.obj I')) ⟶ bi.obj (bg.obj (EX'.obj I')) =>
        t ≫ bi.map (bg.map eX') ≫ bi.map n) hpaste
  have h3 : bL (EX'.obj I') ≫ bi.map (bg.map eX') ≫ bi.map n
      = bf.map (bi'.map eX') ≫ bL J' ≫ bi.map n := by
    rw [← Category.assoc (bL (EX'.obj I')), hbL, Category.assoc]
  rw [Functor.map_comp, Category.assoc, h1, h2, h3, Category.assoc, Category.assoc]

end Stacks.ConormalComparison

namespace Stacks.ClosedImmersion

variable {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-- The components of `Stacks.ClosedImmersion.pullbackCompNatIso` are the isomorphisms
`Stacks.ClosedImmersion.pullbackCompIso`.  Both sides are the same composite of three
components, so this is `rfl`. -/
theorem pullbackCompNatIso_hom_app (comm : i ≫ k = f ≫ j)
    (M : SheafOfModules.{u} (structureSheafRing W')) :
    (pullbackCompNatIso comm).hom.app M = (pullbackCompIso comm M).hom := rfl

/-- **The defining equation of `Stacks.ClosedImmersion.conormalSheafMap`**: the map of conormal
sheaves of a commutative square is the composition comparison
`Stacks.ClosedImmersion.pullbackCompIso` at the ideal sheaf of `j`, followed by the inverse image
along `i` of the map of ideal sheaves `Stacks.ClosedImmersion.idealSheafMap`.

Stated so that a consumer may rewrite with it rather than unfold the definition, which is how
`Stacks.ConormalComparison.comparison_square` is brought to bear on the folded spelling. -/
theorem conormalSheafMap_eq_of_comm (comm : i ≫ k = f ≫ j) :
    conormalSheafMap comm =
      (pullbackCompIso comm (idealSheaf j)).hom ≫ (modulePullback i).map (idealSheafMap comm) :=
  rfl

end Stacks.ClosedImmersion

namespace Stacks.Thickenings

/-- **The map of conormal sheaves of a morphism of universal first-order thickenings is the map
of Stacks 01R4 at the square of inclusions.**  This is the defining equation of
`Stacks.Thickenings.universalConormalSheafMap`, the conormal half of Stacks 04F7, stated so that
a consumer may rewrite with it; the square is the one of
`Stacks.Thickenings.toShHom_universalFirstOrderThickeningMap_inclusion`.

Together with `Stacks.ClosedImmersion.conormalSheafMap_eq_of_comm` it brings
`Stacks.ConormalComparison.comparison_square` to bear on the conormal sheaf
`Stacks.Thickenings.universalConormalSheaf` of a formally unramified morphism of schemes, which
is the conormal sheaf of the inclusion of a universal first-order thickening. -/
theorem universalConormalSheafMap_eq {Z X W Y : Scheme.{u}} {h : Z ⟶ X} {h' : W ⟶ Y}
    (tZ : UniversalFirstOrderThickening h) (tW : UniversalFirstOrderThickening h')
    (p : Z ⟶ W) (q : X ⟶ Y) (comm : h ≫ q = p ≫ h') :
    universalConormalSheafMap tZ tW p q comm =
      Stacks.ClosedImmersion.conormalSheafMap
        (toShHom_universalFirstOrderThickeningMap_inclusion tZ tW p q comm) :=
  rfl

end Stacks.Thickenings

end

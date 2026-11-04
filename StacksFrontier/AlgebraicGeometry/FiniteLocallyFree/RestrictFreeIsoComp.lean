module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RestrictFreeIsoTautological
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart

/-!
# The free comparison of a restriction is pseudo-functorial

`Stacks.Modules.restrictFreeIso` identifies the restriction of a free module along an open
immersion with a free module.  For a composite of two open immersions there are therefore two
identifications of the restriction along the composite with the free module -- the one for the
composite, and the iterated one, read through
`AlgebraicGeometry.restrictCompIso`.  Every argument that trivialises a module over a cover and
then compares two members of the cover over their overlap needs these two to agree, because the
overlap is reached from each member by a further open immersion.

This file proves it, **reduced to the structure sheaf**.  A free module is a coproduct of copies
of the structure sheaf, so by `Stacks.Modules.hom_ext_free` the two identifications agree as soon
as they agree after every tautological inclusion, and there
`Stacks.Modules.ιFree_restrictFreeIso_inv` replaces each free comparison by the structure-sheaf
comparison `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.  What is left is the same statement
for `restrictUnitIso`, which is therefore taken as a hypothesis rather than proved:  it is a
statement about the structure sheaf alone, with no index type in it, and a consumer that has it
for its two open immersions gets the free statement for every index type at once.

This is the shape of `Stacks.SheafOfModules.free_comp_pullbackObjFreeIso_hom_of_unit` on the
pullback side, for the same reason.

## Implementation notes

**Everything is in term mode, through `congrArg`, and no step is a `rw` or a `simp`.**  The sheaf
of rings of a scheme is `AlgebraicGeometry.Scheme.ringCatSheaf`, whose type `TopCat.Sheaf` unfolds
to the `CategoryTheory.Sheaf` that `SheafOfModules` asks for only at default
transparency.  A goal mentioning a free module on a scheme is therefore not type-correct at the
transparency `rw` and `simp` build their motives at, and both fail on it -- with
`simp made no progress`, and a note that the target is not type-correct at the implicit
transparency level.  `congrArg` and `Eq.trans` check at default transparency and are unaffected.
For the same reason a `@[reassoc]` variant of
`Stacks.Modules.ιFree_restrictFreeIso_inv` is of no use -- it is generated, but `simp` will not
apply it either -- so no such attribute is declared and the associativity of composition is moved
by hand, one `CategoryTheory.Category.assoc` at a time.

## Main results

* `Stacks.Modules.restrictFreeIso_inv_comp_restrictCompIso_hom_of_unit`: **the free comparison of
  a restriction is pseudo-functorial as soon as the structure-sheaf comparison is**, for an
  arbitrary index type.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Modules

variable {T' T S : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S) [IsOpenImmersion h] [IsOpenImmersion g]
  {k : T' ⟶ S} (hk : h ≫ g = k) [IsOpenImmersion k] (I : Type u)

include hk in
/-- **The free comparison of a restriction is pseudo-functorial as soon as the structure-sheaf
comparison is.**  For open immersions `h : T' ⟶ T` and `g : T ⟶ S` composing to `k`, the
comparison of the restriction along `k` of the free `𝒪_S`-module on `I` with the free
`𝒪_{T'}`-module on `I` is the iterated comparison, read through
`AlgebraicGeometry.restrictCompIso`.

Both sides are morphisms *out of* the free `𝒪_{T'}`-module, so `Stacks.Modules.hom_ext_free`
reduces the statement to the tautological inclusions, and there
`Stacks.Modules.ιFree_restrictFreeIso_inv` turns each of the three free comparisons into the
structure-sheaf comparison with the inclusion carried along.  The naturality of
`AlgebraicGeometry.restrictCompIso` moves the inclusion past it, and what remains is the
hypothesis. -/
theorem restrictFreeIso_inv_comp_restrictCompIso_hom_of_unit
    (hunit : (Scheme.Modules.restrictUnitIso k).inv ≫
        (AlgebraicGeometry.restrictCompIso h g hk
          (SheafOfModules.unit S.ringCatSheaf)).hom =
      (Scheme.Modules.restrictUnitIso h).inv ≫
        (restrictFunctor h).map (Scheme.Modules.restrictUnitIso g).inv) :
    (restrictFreeIso k I).inv ≫
        (AlgebraicGeometry.restrictCompIso h g hk
          (SheafOfModules.free (R := S.ringCatSheaf) I)).hom =
      (restrictFreeIso h I).inv ≫
        (restrictFunctor h).map (restrictFreeIso g I).inv := by
  refine hom_ext_free I _ _ fun i => ?_
  have hk' := ιFree_restrictFreeIso_inv k I i
  have hh' := ιFree_restrictFreeIso_inv h I i
  have hg' := ιFree_restrictFreeIso_inv g I i
  have hnat := restrictCompIso_naturality h g hk (SheafOfModules.ιFree (R := S.ringCatSheaf) i)
  have t1 :=
    (Category.assoc (SheafOfModules.ιFree (R := T'.ringCatSheaf) i) (restrictFreeIso k I).inv
      (restrictCompIso h g hk (SheafOfModules.free (R := S.ringCatSheaf) I)).hom).symm
  have t2 :=
    t1.trans (congrArg
      (· ≫ (restrictCompIso h g hk (SheafOfModules.free (R := S.ringCatSheaf) I)).hom) hk')
  have t3 := t2.trans (Category.assoc _ _ _)
  have t4 := t3.trans (congrArg ((Scheme.Modules.restrictUnitIso k).inv ≫ ·) hnat)
  have t5 := t4.trans (Category.assoc _ _ _).symm
  have t6 :=
    t5.trans (congrArg
      (· ≫ (restrictFunctor h).map
        ((restrictFunctor g).map (SheafOfModules.ιFree (R := S.ringCatSheaf) i))) hunit)
  have t7 := t6.trans (Category.assoc _ _ _)
  have t8 :=
    t7.trans (congrArg ((Scheme.Modules.restrictUnitIso h).inv ≫ ·)
      ((restrictFunctor h).map_comp (Scheme.Modules.restrictUnitIso g).inv
        ((restrictFunctor g).map (SheafOfModules.ιFree (R := S.ringCatSheaf) i))).symm)
  have t9 :=
    t8.trans (congrArg
      (fun w => (Scheme.Modules.restrictUnitIso h).inv ≫ (restrictFunctor h).map w) hg'.symm)
  have t10 :=
    t9.trans (congrArg ((Scheme.Modules.restrictUnitIso h).inv ≫ ·)
      ((restrictFunctor h).map_comp (SheafOfModules.ιFree (R := T.ringCatSheaf) i)
        (restrictFreeIso g I).inv))
  have t11 := t10.trans (Category.assoc _ _ _).symm
  have t12 :=
    t11.trans (congrArg (· ≫ (restrictFunctor h).map (restrictFreeIso g I).inv) hh'.symm)
  exact t12.trans (Category.assoc _ _ _)

end Stacks.Modules

end

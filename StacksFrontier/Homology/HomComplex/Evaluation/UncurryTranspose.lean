module

public import StacksFrontier.Homology.HomComplex.Evaluation.TensorHom

/-!
# The inverse transpose of an uncurried chain map, followed by the K-injective comparison

For `L` K-flat, `I` K-injective and a chain map `f : K ⟶ RHom(L, I)`, the inverse [stacks 0A63]
transpose of the K-flat comparison followed by the localized uncurrying of `f`, followed by the
K-injective Hom comparison `homIso`, is the localization of `f`: this is
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry` transposed back.

The composite of three factors on the left is the shape in which the content factor of the
inverse component of [stacks 0E1W] is produced by
`Stacks.DerivedHom.BaseChange.modelRestrictScalarsNatIso_inv_app_tensorKFlat_changeOfRingsMap`,
for the chain map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap`; the statement itself
is about any chain map into a Hom complex of a K-flat source and a K-injective target.

## Main results

* `StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_symm_tensorIso_uncurry_comp_homIso`:
  the inverse transpose of the K-flat comparison followed by the localized uncurrying of a chain
  map, followed by the K-injective Hom comparison, is the localization of the chain map.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace StacksDraft.DerivedHom.DerivedInternalHom.Model

/-- **The inverse transpose of an uncurried chain map, followed by the K-injective comparison, is
the chain map.** For `L` K-flat, `I` K-injective and `f : K ⟶ RHom(L, I)`, the inverse transpose
of the K-flat comparison followed by `Q (uncurry f)`, followed by the K-injective Hom comparison,
is `Q f`. -/
@[reassoc]
public theorem homEquiv_symm_tensorIso_uncurry_comp_homIso
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L I : CochainComplex (ModuleCat.{u} R) ℤ) (hL : L.KFlat) [I.IsKInjective]
    (f : K ⟶ CochainComplex.HomComplexR R L I) :
    (homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
              (DerivedCategory.Q.obj I)).symm
            (((adjunction R).tensorIso K L hL).hom ≫
              DerivedCategory.Q.map (uncurry f)) ≫
        ((adjunction R).homIso L I).hom =
      DerivedCategory.Q.map f := by
  rw [← homEquiv_map_uncurry K L I hL f, AddEquiv.symm_apply_apply, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end StacksDraft.DerivedHom.DerivedInternalHom.Model

end

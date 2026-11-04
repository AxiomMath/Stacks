module

public import StacksFrontier.AlgebraicGeometry.Conormal.RestrictSquareMap

/-!
# The canonical map of conormal sheaves of a restriction square is an isomorphism

Let `i : Z ⟶ X` be an immersion of schemes and let `V' ≤ V` be opens of `X`. The square
```
i⁻¹V' --i∣_V'--→ V'
  |              |
  ρ             ρ_X
  ↓              ↓
i⁻¹V ---i∣_V---→ V
```
of restrictions is commutative, and [Stacks Project, Tag 01R4] attaches to it a canonical map
`ρ^* 𝒞_{i∣_V} ⟶ 𝒞_{i∣_V'}`. This file proves that map is an **isomorphism**, which is what
[Stacks Project, Tag 0473] predicts for a flat base change and what
`Stacks.ClosedImmersion.conormalSheafMap_restrictHom_comp_ofRestrict` says at the level of ringed
spaces for the restriction square of an immersion over an open.

The point of the statement is that it is the map of the square between *two restrictions* of one
immersion, not of the square between a restriction and the immersion itself; this is the map that
appears when the third condition of [Stacks Project, Tag 04FH] is carried from an open to a
smaller open, and its invertibility is what makes that condition local.

## Main results

* `Stacks.Immersion.isIso_immersionConormalSheafMap_ι`: the canonical map of the restriction
  square of `i` over an open `V` is an isomorphism.
* `Stacks.Immersion.isIso_immersionConormalSheafMap_homOfLE`: the canonical map of the restriction
  square between the restrictions of `i` over `V' ≤ V` is an isomorphism.

## Implementation notes

The first statement is
`Stacks.Immersion.modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso`, which exhibits
that map as a composite of three isomorphisms. Typeclass resolution cannot assemble the
`CategoryTheory.IsIso` of that composite on its own — the two sides of the composition are typed
at two definitionally equal but syntactically different spellings of the structure sheaf of rings
— so the composite isomorphism is written out with `CategoryTheory.Iso.trans` and its `hom` taken.

The second statement follows by stacking: by
`Stacks.Immersion.immersionConormalSheafMap_comp` the map of the restriction square of `i` over
`V'` factors as the pullback of the map over `V` composed with the map of the square between the
two restrictions, up to the comparison isomorphisms and the transport
`Stacks.Immersion.immersionConormalSheafMap_congr` along `ρ ≫ ι_{i⁻¹V} = ι_{i⁻¹V'}`. Every factor
but the last is an isomorphism, and so is the composite, so the last one is too.

## References

* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 04FH](https://stacks.math.columbia.edu/tag/04FH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.ClosedImmersion Stacks.Thickenings

universe u

namespace Stacks.Immersion

variable {Z X : Scheme.{u}}

/-- **The canonical map of the restriction square of an immersion is an isomorphism.** For an
immersion `i : Z ⟶ X` and an open `V` of `X`, the map `ι_{i⁻¹V}^* 𝒞_{Z/X} ⟶ 𝒞_{i∣_V}` of
[Stacks Project, Tag 01R4] induced by `(i ∣_ V) ≫ ι_V = ι_{i⁻¹V} ≫ i` is invertible. -/
theorem isIso_immersionConormalSheafMap_ι (i : Z ⟶ X) [IsImmersion i] (V : X.Opens) :
    IsIso (immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
      (toShHom_square (morphismRestrict_ι i V))) := by
  rw [← modulePullbackRestrictIso_comp_conormalSheafSelfRestrictIso i V]
  exact (asIso ((modulePullbackRestrictIso Z.toSheafedSpace (i ⁻¹ᵁ V)).hom.app
    (immersionConormalSheaf i)) ≪≫ conormalSheafSelfRestrictIso i V ≪≫
    conormalSheafSelfIso (i ∣_ V)).isIso_hom

/-- **The canonical map of the square between two restrictions of one immersion is an
isomorphism.** For an immersion `i : Z ⟶ X` and opens `V' ≤ V` of `X`, the map
`ρ^* 𝒞_{i∣_V} ⟶ 𝒞_{i∣_V'}` of [Stacks Project, Tag 01R4] induced by
`(i ∣_ V') ≫ ρ_X = ρ ≫ (i ∣_ V)` is invertible. -/
theorem isIso_immersionConormalSheafMap_homOfLE (i : Z ⟶ X) [IsImmersion i]
    {V V' : X.Opens} (hV : V' ≤ V) :
    IsIso (immersionConormalSheafMap (i ∣_ V') (i ∣_ V) (Z.homOfLE (i.preimage_mono hV))
      (X.homOfLE hV) (toShHom_square (morphismRestrict_homOfLE i V' V hV))) := by
  have h1 := isIso_immersionConormalSheafMap_ι i V'
  have h2 := isIso_immersionConormalSheafMap_ι i V
  have hmid := IsIso.of_isIso_fac_left (h := immersionConormalSheafMap (i ∣_ V') i
      (i ⁻¹ᵁ V').ι V'.ι (toShHom_square (morphismRestrict_ι i V')))
    (immersionConormalSheafMap_congr (i ∣_ V') i
      (Scheme.homOfLE_ι Z (i.preimage_mono hV)) (Scheme.homOfLE_ι X hV)
      (toShHom_square (square_comp (morphismRestrict_homOfLE i V' V hV)
        (morphismRestrict_ι i V)))
      (toShHom_square (morphismRestrict_ι i V'))).symm
  rw [immersionConormalSheafMap_comp (i ∣_ V') (i ∣_ V) i
    (Z.homOfLE (i.preimage_mono hV)) (X.homOfLE hV) (morphismRestrict_homOfLE i V' V hV)
    (i ⁻¹ᵁ V).ι V.ι (morphismRestrict_ι i V)] at hmid
  have hstep := @IsIso.of_isIso_comp_left _ _ _ _ _
    ((modulePullbackComp (Z.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom
      (i ⁻¹ᵁ V).ι.toLRSHom.toShHom).hom.app (immersionConormalSheaf i)) _ inferInstance hmid
  exact @IsIso.of_isIso_comp_left _ _ _ _ _
    ((modulePullback (Z.homOfLE (i.preimage_mono hV)).toLRSHom.toShHom).map
      (immersionConormalSheafMap (i ∣_ V) i (i ⁻¹ᵁ V).ι V.ι
        (toShHom_square (morphismRestrict_ι i V)))) _ inferInstance hstep

end Stacks.Immersion

end

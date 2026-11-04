module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-compactness is checked on an affine open covering of the target

A morphism of schemes `f : X ⟶ S` is quasi-compact if and only if the preimage of every affine
open of `S` is quasi-compact, if and only if there is a covering of `S` by affine opens whose
preimages are quasi-compact.

## Main results

* `AlgebraicGeometry.quasiCompact_tfae`: the three conditions above are equivalent.

## Implementation notes

The first equivalence is Mathlib's `AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen`. The
covering condition implies quasi-compactness because `QuasiCompact` has the affine property
`CompactSpace` of the source, so it is checked on any affine open covering of the target
(`AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`). Instance search does not find
`HasAffineProperty @QuasiCompact _` under the default `backward.isDefEq.respectTransparency`, so
Mathlib's instance is passed by name.

## References

* [Stacks Project, Tag 01K4](https://stacks.math.columbia.edu/tag/01K4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For a morphism of schemes `f : X ⟶ S` the following are equivalent:
1. `f` is quasi-compact;
2. the preimage of every affine open of `S` is quasi-compact;
3. there is a covering `S = ⋃ᵢ Uᵢ` by affine opens such that every `f⁻¹(Uᵢ)` is quasi-compact. -/
@[stacks 01K4]
theorem quasiCompact_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE [QuasiCompact f,
      ∀ U : S.Opens, IsAffineOpen U → IsCompact (f ⁻¹ᵁ U : Set X),
      ∃ (ι : Type u) (U : ι → S.Opens), (∀ i, IsAffineOpen (U i)) ∧ iSup U = ⊤ ∧
        ∀ i, IsCompact (f ⁻¹ᵁ U i : Set X)] := by
  tfae_have 1 ↔ 2 := quasiCompact_iff_forall_isAffineOpen
  tfae_have 2 → 3 := fun h ↦
    ⟨S.affineOpens, fun U ↦ U.1, fun U ↦ U.2, iSup_affineOpens_eq_top S, fun U ↦ h _ U.2⟩
  tfae_have 3 → 1 := by
    rintro ⟨ι, U, hU, hTop, hc⟩
    exact (@HasAffineProperty.iff_of_iSup_eq_top @QuasiCompact _
      instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat _ _ f _
      (fun i ↦ ⟨U i, hU i⟩) hTop).mpr fun i ↦ isCompact_iff_compactSpace.mp (hc i)
  tfae_finish

end AlgebraicGeometry

module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysAffineConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionSheaf

/-!
# The two spellings of the canonical connection of [Stacks, Tag 07J6] on `Cris(X/S)` agree

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], a crystal `F` in
`𝒪_{X/S}`-modules on the small crystalline site and an object `B = (U, T, δ)` of `Cris(X/S)`.  The
library has the canonical connection of [Stacks, Lemma 60.15.1, Tag 07J6] in two spellings:

* `...SmallSite.crystalConnection B hF`, a morphism of abelian sheaves
  `F_T ⟶ F_T ⊗_{𝒪_T} Ω_{T/S,δ}` on the ambient scheme `T`, whose value on a section over an
  open `W` is the recipe `p₁^* s - p₀^* s` read in `F_T ⊗ Ω` through the canonical morphism
  `...SmallSite.firstOrderTensorInclusion : F_T ⊗ Ω ⟶ p₀_* F_{T'}`;
* `...SmallSite.AffineConnection.connection he`, its value on global sections over an object with
  affine ambient scheme, `ℱ(B) ⟶ Γ(T, Ω_{T/S,δ}) ⊗_{Γ(T, 𝒪_T)} ℱ(B)`, the recipe
  `p₁^* s - p₀^* s` read in `Γ(T, Ω) ⊗ ℱ(B)` through the canonical map
  `...SmallSite.AffineConnection.diffAction`.  This is the connection whose extensions are the
  differentials of the de Rham complex of [Stacks, Tag 07LM]
  (`...SmallSite.crystalDeRhamSheafData`).

This module proves that they are **the same connection**: over the whole of `T`, both canonical
maps carry the two connections of a section `s` of `F` over `B` to the same section of `F` over
`(U, T', δ')`, namely `p₁^* s - p₀^* s`.

## Main results

* `firstOrderTensorInclusion_crystalConnection_top` — **the two connections agree**: the canonical
  map of the sheaf-level connection and the canonical map of the global-sections connection read
  both back to `p₁^* s - p₀^* s`.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}
  {B : CrystallineThickening S}

/-- The two restrictions to the whole of the ambient scheme commute with the projections of the
first-order thickening. -/
theorem crysSiteRestrict_restrictOpenMap_top (g : firstOrderThickeningCrysObject S B ⟶ B)
    (s : F.val.obj (op B)) :
    crysSiteRestrict F (CrystallineThickening.restrictOpenMap g ⊤)
        (crysSiteRestrict F (B.restrictOpenHom ⊤) s) =
      crysSiteRestrict F ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤)
        (crysSiteRestrict F g s) :=
  crysSiteRestrict_crysRestrictOpenMapTop F g s

/-- **The canonical connection of [Stacks, Tag 07J6] on the sheaf `F_T` and on the global sections
over `B` agree.**  For a crystal `F` and a section `s` of `F` over an object `B` of `Cris(X/S)`
whose base change along `p₀` is bijective (for instance a crystal in quasi-coherent modules over
an object with affine ambient scheme), the canonical morphism `F_T ⊗ Ω ⟶ p₀_* F_{T'}` carries the
sheaf-level connection of `s|_T`, over the whole of `T`, to the restriction to `T'` of the image of
the global-sections connection of `s` under the canonical map `Γ(T, Ω) ⊗ ℱ(B) ⟶ ℱ(U, T', δ')`:
both are `p₁^* s - p₀^* s`. -/
theorem firstOrderTensorInclusion_crystalConnection_top (hF : IsSheafCrystal F)
    (he : Function.Bijective (crysExtensionSectionsMap F B)) (s : F.val.obj (op B)) :
    (firstOrderTensorInclusion F B).val.app (op ⊤)
        ((crystalConnection B hF).hom.app (op ⊤) (crysSiteRestrict F (B.restrictOpenHom ⊤) s)) =
      crysSiteRestrict F ((firstOrderThickeningCrysObject S B).restrictOpenHom ⊤)
        (diffAction F B (connection he s)) := by
  refine (firstOrderTensorInclusion_crystalConnectionApp B hF ⊤
    (crysSiteRestrict F (B.restrictOpenHom ⊤) s)).trans ?_
  rw [crystalConnectionRaw_apply, diffAction_connection, connectionDifference_apply, restrict_sub]
  congr 1 <;> exact crysSiteRestrict_restrictOpenMap_top _ s

end Crystalline.GlobalCrystallineSituation.SmallSite.AffineConnection

end

end

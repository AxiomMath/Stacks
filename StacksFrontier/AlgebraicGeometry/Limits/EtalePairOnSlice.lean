module

public import StacksFrontier.AlgebraicGeometry.Limits.EtalePullbackMap

/-!
# The inverse image of a slice in a common étale neighbourhood

Let `U_i ⟶ S_i` be a scheme over `S_i` carrying two étale morphisms with trivial residue field
extension at a point `u_i`, one to `X ×_S S_i` and one to `Y ×_T S_i`, and let `i : V ⟶ S_i` be a
morphism through the image of `u_i` which is trivial on residue fields at its distinguished point
— for instance an immersion. Then the inverse image `W = U_i ×_{S_i} V` carries a point `w` over
`u_i` and `v`, and the two induced morphisms

```
W ⟶ X ×_S V        W ⟶ Y ×_T V
```

are étale with trivial residue field extension at `w`.

This is the final step of the proof of Stacks Tag 0GDX, "setting `W` equal to the scheme theoretic
inverse image of `V` in `U_i` we conclude", together with the residue field bookkeeping which
makes the two resulting étale neighbourhoods *elementary*.

## Main results

* `AlgebraicGeometry.exists_point_etale_pair_on_slice`: the point `w` and the two morphisms.

## Implementation notes

The structure morphism `pU` of `U_i` is a separate argument with the two triangles as hypotheses,
so that the fibre product `U_i ×_{S_i} V` is never transported along an equation of morphisms;
`AlgebraicGeometry.pullbackMapOver` is set up for exactly that. The identification
`(X ×_S S_i) ×_{S_i} V = X ×_S V` is Mathlib's
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, and the point `w` with its residue field comes
from `AlgebraicGeometry.Scheme.Pullback.exists_unique_point_of_isIso_residueFieldMap`.

Only triviality of the residue field extension of `i` at `v` is used, not that `i` is an
immersion; for an immersion it follows from
`AlgebraicGeometry.isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp` applied to
`i ≫ (S_i ⟶ S)`.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The inverse image of a slice in a common étale neighbourhood.** -/
public theorem exists_point_etale_pair_on_slice
    {S T X Y Dj U V : Scheme.{u}} (fX : X ⟶ S) (gY : Y ⟶ T)
    (pj : Dj ⟶ S) (tj : Dj ⟶ T) (pU : U ⟶ Dj)
    (a : U ⟶ pullback fX pj) (b : U ⟶ pullback gY tj)
    (ha : a ≫ pullback.snd fX pj = pU) (hb : b ≫ pullback.snd gY tj = pU)
    (hae : Etale a) (hbe : Etale b) (u : U)
    (hares : IsIso (a.residueFieldMap u)) (hbres : IsIso (b.residueFieldMap u))
    (i : V ⟶ Dj) (v : V) (hiv : i v = pU u) (hires : IsIso (i.residueFieldMap v)) :
    ∃ w : ↥(pullback pU i),
      pullback.fst pU i w = u ∧ pullback.snd pU i w = v ∧
      ∃ (FX : pullback pU i ⟶ pullback fX (i ≫ pj))
        (FY : pullback pU i ⟶ pullback gY (i ≫ tj)),
        Etale FX ∧ Etale FY ∧
          IsIso (FX.residueFieldMap w) ∧ IsIso (FY.residueFieldMap w) ∧
            FX ≫ pullback.snd fX (i ≫ pj) = pullback.snd pU i ∧
              FY ≫ pullback.snd gY (i ≫ tj) = pullback.snd pU i := by
  obtain ⟨w, ⟨hw₁, hw₂⟩, -⟩ :=
    Scheme.Pullback.exists_unique_point_of_isIso_residueFieldMap pU i u v hiv.symm hires
  have hX := etale_pullbackMapOver (pullback.snd fX pj) pU a ha i
  have hY := etale_pullbackMapOver (pullback.snd gY tj) pU b hb i
  have hXres := isIso_residueFieldMap_pullbackMapOver (pullback.snd fX pj) pU a ha i u w hw₁ hares
  have hYres := isIso_residueFieldMap_pullbackMapOver (pullback.snd gY tj) pU b hb i u w hw₁ hbres
  refine ⟨w, hw₁, hw₂,
    pullbackMapOver (pullback.snd fX pj) pU a ha i ≫ (pullbackLeftPullbackSndIso fX pj i).hom,
    pullbackMapOver (pullback.snd gY tj) pU b hb i ≫ (pullbackLeftPullbackSndIso gY tj i).hom,
    inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩ <;>
  first
    | (rw [Scheme.residueFieldMap_comp]
       exact IsIso.comp_isIso'
         (Scheme.instIsIsoCommRingCatResidueFieldMapOfIsOpenImmersion _ _) ‹_›)
    | rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullbackMapOver_snd]

end AlgebraicGeometry

end

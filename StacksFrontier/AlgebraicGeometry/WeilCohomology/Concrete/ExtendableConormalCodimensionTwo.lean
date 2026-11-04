module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExtendableConormalReduction

/-!
# The reduction of Tag 0FIR never meets codimension one

The reduction step of [Stacks, Tag 0FIR]
(`Stacks.WeilCohomology.WeilData.pushforward_unitTw_eq_cycleClass_of_extendable`) proves
`i_*1 = γ([Z])` for a closed immersion `i : Z ⟶ X` from the same equation for closed immersions
whose conormal class extends. It applies that hypothesis only twice:

* to `i` itself when `dim X ≤ dim Z`, which is codimension `0`; and
* to the embedding `h = (i, g) : Z ⟶ X × G(l, n)` with `0 < l < n` when `dim Z < dim X`. Its
  codimension is `(dim X - dim Z) + l(n - l) ≥ 1 + 1 = 2`.

So the hypothesis is needed only away from codimension one. This file states the reduction with
the hypothesis restricted to codimensions `c ≠ 1`. This is what the proof of Tag 0FIT under
(A1)–(A8) needs: there `j_*1 = γ([E])` for the exceptional divisor `E` holds when the centre has
codimension at least `2`, but not, a priori, in codimension `1`.

## Main results

* `Stacks.WeilCohomology.WeilData.pushforward_unitTw_eq_cycleClass_of_extendable_of_ne_one`

## References

* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 0FIT](https://stacks.math.columbia.edu/tag/0FIT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero
  Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

open SmoothProjectiveScheme in
/-- **The reduction step of Stacks 0FIR, away from codimension one.** Suppose `γ` commutes with
pushforward along the projections `X × G(l, n) ⟶ X`, `0 < l < n`. Suppose also that `j_*1 = γ([Z])`
holds for every closed immersion `j : Z ⟶ X` of nonempty equidimensional smooth projective
schemes that has codimension `c ≠ 1` and whose conormal class `[𝒞_{Z/X}] ∈ K₀(Z)` is pulled back
from `K₀(X)`. Then `i_*1 = γ([Z])` holds for every closed immersion `i` of nonempty
equidimensional smooth projective schemes. -/
theorem pushforward_unitTw_eq_cycleClass_of_extendable_of_ne_one (hA : W.PerfectPairing)
    (hG : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (l n : ℕ), 0 < l → l < n → ∀ (d d' : ℕ)
      (hX : IsNonemptyEquidimensional X d)
      (hP : IsNonemptyEquidimensional (prod X (SmoothProjectiveScheme.grassmannian k l n)) d')
      (p q : ℤ) (hq : q = p + d - d')
      (α : codimensionChowGroup k (prod X (SmoothProjectiveScheme.grassmannian k l n)).obj.hom p),
      W.cycleClass X q (equidimensionalPushforward (fst X _) d' d p q hq α) =
        W.pushforward hA (fst X _) hP hX (2 * p) p (2 * q) q (by omega) (by omega)
          (W.cycleClass _ p α))
    (hK : ∀ {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
      [IsClosedImmersion i.hom.left]
      {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d)
      (c : ℤ) (hc : c = d - e), c ≠ 1 →
      (∃ β : VectorBundleKZero X.obj.left, pullbackRingHom i.hom.left β =
        classOf Z.obj.left (Stacks.Conormal.conormalSheaf i.hom.left)) →
      W.pushforward hA i hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
        W.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c))
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {e d : ℕ}
    (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e) :
    W.pushforward hA i hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c) := by
  rcases le_or_gt d e with hde | hed
  · refine hK i hZ hX c hc (by omega) ?_
    obtain ⟨β, hβ⟩ := exists_pullbackRingHom_eq_classOf_conormalSheaf_of_le i
      hZ.relativeDimension hX.relativeDimension hde
    exact ⟨β, hβ⟩
  obtain ⟨l, n, hl, hln, h, hh, hhi, hβ⟩ :=
    exists_grassmannian_embedding i hZ.relativeDimension hX.relativeDimension hed
  subst hhi
  have hGne : Nonempty (SmoothProjectiveScheme.grassmannian k l n).obj.left :=
    ⟨(h ≫ snd X _).hom.left.base hZ.nonempty.some⟩
  have hP := isNonemptyEquidimensional_prod hX (isNonemptyEquidimensional_grassmannian l n hGne)
  have hpos : 0 < l * (n - l) := Nat.mul_pos hl (Nat.sub_pos_of_lt hln)
  have hh1 := hK h hZ hP ((d + l * (n - l) : ℕ) - e) rfl (by push_cast; omega) hβ
  exact W.pushforward_unitTw_comp_eq_cycleClass hA h (fst X _) hZ hP hX
    ((d + l * (n - l) : ℕ) - e) c rfl hc hh1
    (hG X l n hl hln d (d + l * (n - l)) hX hP _ c (by push_cast; omega) _)

end WeilData

end Stacks.WeilCohomology

end

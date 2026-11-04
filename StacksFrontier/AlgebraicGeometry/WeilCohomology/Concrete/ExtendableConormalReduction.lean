module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedSubschemeClassPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GrassmannianConormalEmbedding
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DiagonalDualBasis

/-!
# From closed immersions with extendable conormal class to all closed immersions

This file proves the reduction step of [Stacks, Tag 0FIR] for any data (D0)–(D3) with the perfect
pairing of axiom (A): let `i : Z ⟶ X` be a closed immersion of nonempty equidimensional smooth
projective schemes over `k`, of dimensions `e` and `d`. Suppose

* `γ` commutes with pushforward along every projection `p : X × G(l, n) ⟶ X`, `0 < l < n`
  (the conclusion of [Stacks, Tag 0FIQ]), and
* `j_*1 = γ([Z])` for every closed immersion `j` of nonempty equidimensional smooth projective
  schemes whose conormal class in `K₀(Z)` is the pullback of a class on the target.

Then `i_*1 = γ([Z])`. If `d ≤ e` the conormal sheaf of `i` is zero and the second hypothesis
applies to `i` itself. If `e < d`, embed `Z` into `X × G(l, n)` by `h = (i, g)` as in
`Stacks.WeilCohomology.SmoothProjectiveScheme.exists_grassmannian_embedding`; the second
hypothesis gives `h_*1 = γ([Z])`, and `i_*1 = p_* h_*1 = p_*γ([Z]) = γ(p_*[Z]) = γ([Z])`.

## Main results

* `Stacks.WeilCohomology.WeilData.pushforward_unitTw_eq_cycleClass_of_extendable`: under the two
  hypotheses above, `i_*1 = γ([Z])` for every closed immersion `i : Z ⟶ X`.

## References

* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero
  Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- `G(l, n)_k` is equidimensional of dimension `l(n - l)` once it is nonempty. -/
theorem isNonemptyEquidimensional_grassmannian (l n : ℕ)
    (h : Nonempty (SmoothProjectiveScheme.grassmannian k l n).obj.left) :
    IsNonemptyEquidimensional (SmoothProjectiveScheme.grassmannian k l n) (l * (n - l)) where
  nonempty := h
  relativeDimension := SmoothOfRelativeDimension.relativeDimension _ _

end SmoothProjectiveScheme

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

open SmoothProjectiveScheme in
/-- **The reduction step of Stacks 0FIR.** If `γ` commutes with pushforward along the projections
`X × G(l, n) ⟶ X`, `0 < l < n`, and `j_*1 = γ([Z])` holds for the closed immersions `j : Z ⟶ X`
of nonempty equidimensional smooth projective schemes whose conormal class `[𝒞_{Z/X}] ∈ K₀(Z)` is
pulled back from `K₀(X)`, then `i_*1 = γ([Z])` holds for every closed immersion `i` of nonempty
equidimensional smooth projective schemes. -/
theorem pushforward_unitTw_eq_cycleClass_of_extendable (hA : W.PerfectPairing)
    (hG : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (l n : ℕ), 0 < l → l < n → ∀ (d d' : ℕ)
      (hX : IsNonemptyEquidimensional X d)
      (hP : IsNonemptyEquidimensional (prod X (SmoothProjectiveScheme.grassmannian k l n)) d')
      (p q : ℤ) (hq : q = p + d - d')
      (α : codimensionChowGroup k (prod X (SmoothProjectiveScheme.grassmannian k l n)).obj.hom p),
      W.cycleClass X q (equidimensionalPushforward (fst X _) d' d p q hq α) =
        W.pushforward hA (fst X _) hP hX (2 * p) p (2 * q) q (by omega) (by omega)
          (W.cycleClass _ p α))
    (hK : ∀ {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
      [IsClosedImmersion i.hom.left] {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e)
      (hX : IsNonemptyEquidimensional X d) (c : ℤ) (hc : c = d - e),
      (∃ β : VectorBundleKZero X.obj.left, pullbackRingHom i.hom.left β =
        classOf Z.obj.left (Stacks.Conormal.conormalSheaf i.hom.left)) →
      W.pushforward hA i hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
        W.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c))
    {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X) [IsClosedImmersion i.hom.left]
    {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d) (c : ℤ)
    (hc : c = d - e) :
    W.pushforward hA i hZ hX 0 0 (2 * c) c (by omega) (by omega) (W.unitTw Z 0 0 rfl) =
      W.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c) := by
  rcases le_or_gt d e with hde | hed
  · exact hK i hZ hX c hc (exists_pullbackRingHom_eq_classOf_conormalSheaf_of_le i
      hZ.relativeDimension hX.relativeDimension hde)
  obtain ⟨l, n, hl, hln, h, hh, hhi, hβ⟩ :=
    exists_grassmannian_embedding i hZ.relativeDimension hX.relativeDimension hed
  subst hhi
  have hP := isNonemptyEquidimensional_prod hX (isNonemptyEquidimensional_grassmannian l n
    ⟨(h ≫ snd X _).hom.left.base hZ.nonempty.some⟩)
  exact W.pushforward_unitTw_comp_eq_cycleClass hA h (fst X _) hZ hP hX
    ((d + l * (n - l) : ℕ) - e) c rfl hc (hK h hZ hP ((d + l * (n - l) : ℕ) - e) rfl hβ)
    (hG X l n hl hln d (d + l * (n - l)) hX hP _ c (by push_cast; lia) _)

end WeilData

end Stacks.WeilCohomology

end

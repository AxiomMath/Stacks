module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardGrassmannian
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GrassmannianProjectionPushforward

/-!
# Lemma 0FIP: it suffices to check `i_*1 = γ([Z])` for closed immersions

Let data (D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), with
`γ` the cycle class map of Tag 0FIF and the pushforward on cohomology of Section 0FHA for the
data `WeilChernData.toWeilData` (Poincaré duality being Lemma 0FIJ). [Stacks, Tag 0FIP]: in order
to show that `γ` commutes with pushforward it suffices to show `i_*(1) = γ([Z])` for every closed
immersion `i : Z ⟶ X` of nonempty smooth projective equidimensional schemes over `k`.

The proof is `Stacks.WeilCohomology.WeilChernData.cycleClassPushforward_of_grassmannian`, with the
compatibility along the projections `X × G(l, n) ⟶ X` supplied by Lemma 0FIQ
(`Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_fst_grassmannian`). It replaces the
splitting principle, Bertini's theorem and the reduction to infinite fields of the source by
embeddings into Grassmannian bundles along which every class of `K₀` extends.

## Main results

* `Stacks.WeilCohomology.WeilChernData.cycleClassPushforward_of_closedImmersion`: Lemma 0FIP.

## References

* [Stacks Project, Tag 0FIP](https://stacks.math.columbia.edu/tag/0FIP)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **Stacks Project, Lemma 0FIP.** Assume given data (D0), (D1), (D2') satisfying axioms
(A1)–(A7). In order to show that `γ` commutes with pushforward (axiom (C)(b) of Section 0FHA for
the data `𝔚.toWeilData`) it suffices to show that `i_*(1) = γ([Z])` in `H^{2c}(X)(c)`,
`c = d - e`, whenever `i : Z ⟶ X` is a closed immersion of nonempty smooth projective
equidimensional schemes over `k`, of dimensions `e` and `d`. Here `[Z] ∈ CH^c(X)` is the class of
the closed subscheme `Z` and `i_*` the pushforward on cohomology defined by Poincaré duality. -/
@[stacks 0FIP "the whole lemma, under exactly (A1)-(A7) (WeilChernData): if i_*(1) = gamma([Z]) \
  for every closed immersion i : Z -> X of nonempty equidimensional smooth projective schemes over \
  k, then gamma commutes with pushforward (axiom (C)(b) for toWeilData); nothing assumed"]
theorem cycleClassPushforward_of_closedImmersion
    (hi : ∀ {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
      [IsClosedImmersion i.hom.left] {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e)
      (hX : IsNonemptyEquidimensional X d) (c : ℤ) (hc : c = d - e),
      𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * c) c (by omega) (by omega)
          (𝔚.toWeilData.unitTw Z 0 0 rfl) =
        𝔚.toWeilData.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c)) :
    𝔚.toWeilData.CycleClassPushforward 𝔚.perfectPairing :=
  cycleClassPushforward_of_grassmannian (𝔚 := 𝔚)
    (fun X _ _ _ hln d d' hX hP p q hq α =>
      𝔚.pushforwardCompatible_fst_grassmannian hln X d' d hP hX p q hq α) hi

end Stacks.WeilCohomology.WeilChernData

end

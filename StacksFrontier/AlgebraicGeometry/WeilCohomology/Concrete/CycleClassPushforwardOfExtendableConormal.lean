module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassPushforwardOfClosedImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ExtendableConormalReduction

/-!
# Lemma 0FIR: it suffices to check `i_*1 = γ([Z])` when the conormal class extends

Let data (D0), (D1), (D2') satisfy axioms (A1)–(A7) (`Stacks.WeilCohomology.WeilChernData`), with
`γ` the cycle class map of Tag 0FIF and the pushforward on cohomology of Section 0FHA for the
data `WeilChernData.toWeilData` (Poincaré duality being Lemma 0FIJ). [Stacks, Tag 0FIR]: in order
to show that `γ` commutes with pushforward it suffices to show `i_*(1) = γ([Z])` for every closed
immersion `i : Z ⟶ X` of nonempty smooth projective equidimensional schemes over `k` such that
the class of the conormal sheaf `𝒞_{Z/X}` in `K₀(Z)` is the pullback of a class in `K₀(X)`.

The proof is the source's. By Lemma 0FIP
(`Stacks.WeilCohomology.WeilChernData.cycleClassPushforward_of_closedImmersion`) it suffices to
treat every closed immersion `i`. If `Z` has codimension `0` the conormal sheaf is zero and the
hypothesis applies to `i`. Otherwise `i` factors as `Z ⟶ X × G(l, n) ⟶ X` with `0 < l < n`
through a closed immersion whose conormal class extends (Constructions, Section 089R and
Tag 067W), along whose second morphism `γ` commutes with pushforward by Lemma 0FIQ
(`Stacks.WeilCohomology.WeilChernData.pushforwardCompatible_fst_grassmannian`);
`Stacks.WeilCohomology.WeilData.pushforward_unitTw_eq_cycleClass_of_extendable` assembles this.

`K₀(Z)` is `K₀(Vect(Z))` (`AlgebraicGeometry.VectorBundleKZero`) with pullback
`AlgebraicGeometry.VectorBundleKZero.pullbackRingHom`; for smooth projective `Z` this is the
`K₀` of the source (Tags 0F87, 0FDJ).

## Main results

* `Stacks.WeilCohomology.WeilChernData.cycleClassPushforward_of_extendableConormal`:
  **Stacks 0FIR**.

## References

* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 0FIP](https://stacks.math.columbia.edu/tag/0FIP)
* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero Stacks.Chow

universe u w

namespace Stacks.WeilCohomology.WeilChernData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (𝔚 : WeilChernData k F)

/-- **Stacks Project, Lemma 0FIR.** Assume given data (D0), (D1), (D2') satisfying axioms
(A1)–(A7). In order to show that `γ` commutes with pushforward (axiom (C)(b) of Section 0FHA for
the data `𝔚.toWeilData`) it suffices to show that `i_*(1) = γ([Z])` in `H^{2c}(X)(c)`,
`c = d - e`, whenever `i : Z ⟶ X` is a closed immersion of nonempty smooth projective
equidimensional schemes over `k`, of dimensions `e` and `d`, such that the class of the conormal
sheaf `𝒞_{Z/X}` in `K₀(Z)` is the pullback of a class in `K₀(X)`. Here `[Z] ∈ CH^c(X)` is the
class of the closed subscheme `Z` and `i_*` the pushforward on cohomology defined by Poincaré
duality. -/
@[stacks 0FIR "the whole lemma, under exactly (A1)-(A7) (WeilChernData): if i_*(1) = gamma([Z]) \
  for every closed immersion i : Z -> X of nonempty equidimensional smooth projective schemes over \
  k whose conormal class in K_0(Z) is the pullback of a class in K_0(X), then gamma commutes with \
  pushforward (axiom (C)(b) for toWeilData); nothing assumed"]
theorem cycleClassPushforward_of_extendableConormal
    (hi : ∀ {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
      [IsClosedImmersion i.hom.left]
      {e d : ℕ} (hZ : IsNonemptyEquidimensional Z e) (hX : IsNonemptyEquidimensional X d)
      (c : ℤ) (hc : c = d - e),
      (∃ β : VectorBundleKZero X.obj.left, pullbackRingHom i.hom.left β =
        classOf Z.obj.left (Stacks.Conormal.conormalSheaf i.hom.left)) →
      𝔚.toWeilData.pushforward 𝔚.perfectPairing i hZ hX 0 0 (2 * c) c (by omega) (by omega)
          (𝔚.toWeilData.unitTw Z 0 0 rfl) =
        𝔚.toWeilData.cycleClass X c (closedSubschemeClass X.obj.hom i.hom.left c)) :
    𝔚.toWeilData.CycleClassPushforward 𝔚.perfectPairing :=
  𝔚.cycleClassPushforward_of_closedImmersion fun i _ _ _ hZ hX c hc =>
    𝔚.toWeilData.pushforward_unitTw_eq_cycleClass_of_extendable 𝔚.perfectPairing
      (fun X _ _ _ hln d d' hX hP p q hq α =>
        𝔚.pushforwardCompatible_fst_grassmannian hln X d' d hP hX p q hq α)
      hi i hZ hX c hc

end Stacks.WeilCohomology.WeilChernData

end

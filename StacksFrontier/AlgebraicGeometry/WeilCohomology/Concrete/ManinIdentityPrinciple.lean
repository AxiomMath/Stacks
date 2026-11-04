module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ChowGroupsOfMotives
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Rigid
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Motives.ManinIdentityPrinciple

/-!
# Manin's identity principle on the category of Chow motives

Let `k` be a field and let `c : M ⟶ N` be a morphism in the category `M_k` of Chow motives over
`k`. **Stacks 0FGN** (Manin): if for every smooth projective scheme `X` over `k` the morphism
`c ⊗ 1 : M ⊗ h(X) ⟶ N ⊗ h(X)` induces an isomorphism on Chow groups, then `c` is an isomorphism.

Everything is the concrete object of the source.

* `M_k` is `Stacks.WeilCohomology.ChowMotiveCat k`, the triples `(X, p, m)` of Section 0FG9 (Stacks
  0FGA), with the symmetric monoidal structure `(X, p, m) ⊗ (Y, q, n) = (X × Y, p ⊗ q, m + n)` of
  Stacks 0FGC (`Stacks.WeilCohomology.ChowMotiveCat.monoidalCategory`).
* `h(X) = (X, 1, 0)` is `(Stacks.WeilCohomology.ChowMotiveCat.h k).obj (op X)` for `X` a smooth
  projective scheme over `k`.
* `CH^i(M) = p(CH^{i+m}(X) ⊗ ℚ)` is `Stacks.WeilCohomology.ChowMotiveCat.chowGroup M i` of
  Definition 0FGL, and the map induced by `c` is the pushforward
  `Stacks.WeilCohomology.ChowMotiveCat.chowMap c i`, a `ℚ`-linear map. A `ℚ`-linear map is an
  isomorphism of `ℚ`-vector spaces exactly when it is bijective, which is how "induces an
  isomorphism on Chow groups" is stated, in every degree `i ∈ ℤ`.

## Proof

The source's proof is the formal argument of
`Stacks.WeilCohomology.isIso_of_bijective_chowMap_tensorUnitHom`, which is applied here to the
concrete inputs it needs, all of them theorems about `M_k`:

* Stacks 0FGM, `CH^i(M) = Hom(𝟏(-i), M)` functorially in `M`:
  `Stacks.WeilCohomology.ChowMotiveCat.chowGroupEquivHom` and
  `Stacks.WeilCohomology.ChowMotiveCat.chowGroupEquivHom_naturality`;
* `𝟏(-m)` is a right dual of `𝟏(m)`, by construction (proof of Stacks 0FGJ):
  `Stacks.WeilCohomology.ChowMotiveCat.tateExactPairing`;
* every motive `(X, p, m)` is a summand of `h(X)(m) = h(X) ⊗ 𝟏(m)` (proof of Stacks 0FGJ):
  `Stacks.WeilCohomology.ChowMotiveCat.retractHTensorTate`;
* Stacks 0FGJ, every object of `M_k` has a left dual:
  `Stacks.WeilCohomology.ChowMotiveCat.rightRigidCategory`;
* Stacks 0FFQ, `Hom(Z' ⊗ X, Z) = Hom(Z', Z ⊗ Y)` for `Y` a left dual of `X`, and the Yoneda lemma,
  Stacks 001P, used inside the formal argument.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.chowRepresentability`: the Chow groups of motives, the
  Tate motives, their duality and the representability of Stacks 0FGM, packaged in the shape
  the formal argument takes.
* `Stacks.WeilCohomology.ChowMotiveCat.isIso_of_bijective_chowMap_tensorHom_h`: **Stacks 0FGN**,
  Manin's identity principle.

## References

* [Stacks Project, Tag 0FGN](https://stacks.math.columbia.edu/tag/0FGN)
* [Stacks Project, Tag 0FGM](https://stacks.math.columbia.edu/tag/0FGM)
* [Stacks Project, Tag 0FGJ](https://stacks.math.columbia.edu/tag/0FGJ)
* [Stacks Project, Tag 0FFQ](https://stacks.math.columbia.edu/tag/0FFQ)
* [Stacks Project, Tag 001P](https://stacks.math.columbia.edu/tag/001P)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k]

/-- The Chow groups `CH^i(M)` of Chow motives (Definition 0FGL) with the pushforward
`c_* : CH^i(M) → CH^i(N)`, the Tate motives `𝟏(m)` with `𝟏(-m)` a right dual of `𝟏(m)`, and the
representability `CH^i(M) = Hom(𝟏(-i), M)` of Stacks 0FGM, natural in `M`. -/
def chowRepresentability : ChowRepresentability (ChowMotiveCat k) where
  unitTwist := tate k
  tateExactPairing := tateExactPairing
  chowGroup i M := chowGroup M i
  chowMap i c := chowMap c i
  chowEquiv i M := (chowGroupEquivHom M i).toEquiv
  chowEquiv_naturality i _ _ c x := chowGroupEquivHom_naturality c i x

/-- **Stacks Project, Tag 0FGN** (Manin's identity principle). Let `k` be a field and let
`c : M ⟶ N` be a morphism of Chow motives over `k`. If for every smooth projective scheme `X` over
`k` the morphism `c ⊗ 1 : M ⊗ h(X) ⟶ N ⊗ h(X)` induces an isomorphism
`CH^i(M ⊗ h(X)) → CH^i(N ⊗ h(X))` on Chow groups in every degree `i`, then `c` is an
isomorphism. -/
@[stacks 0FGN "Manin's identity principle, on the category M_k of Chow motives"]
theorem isIso_of_bijective_chowMap_tensorHom_h {M N : ChowMotiveCat k} (c : M ⟶ N)
    (hc : ∀ (X : (SmoothProjectiveScheme k).FullSubcategory) (i : ℤ),
      Function.Bijective (chowMap (c ⊗ₘ 𝟙 ((h k).obj (op X))) i)) :
    IsIso c := by
  refine isIso_of_bijective_chowMap_tensorUnitHom chowRepresentability (fun _ => inferInstance)
    (fun X : (SmoothProjectiveScheme k).FullSubcategory => (h k).obj (op X))
    (fun L => ⟨L.scheme, L.twist, ⟨retractHTensorTate L⟩⟩) c fun X i => ?_
  -- The formal argument reads `c ⊗ 1` through the monoidal structure's underlying
  -- `MonoidalCategoryStruct`; the statement elaborates it through the direct instance. The two
  -- are the same by definition, and rewriting first keeps the unifier from unfolding tensors.
  rw [show (MonoidalCategory.toMonoidalCategoryStruct : MonoidalCategoryStruct (ChowMotiveCat k)) =
    GradedCategory.TwistedKaroubi.monoidalCategoryStruct from rfl]
  exact hc X i

end Stacks.WeilCohomology.ChowMotiveCat

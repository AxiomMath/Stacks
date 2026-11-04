module

public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.TwistKZeroClass
public import StacksFrontier.AlgebraicGeometry.Conormal.SmoothKZeroClass
public import StacksFrontier.AlgebraicGeometry.Recovery27.UniversalQuotientClass

/-!
# The conormal class of a graph-type embedding into a Grassmannian bundle

This file assembles the `K₀` part of the proof of [Stacks, Tag 0FIR]. Let `i : Z ⟶ X` be a
closed immersion, `L` an ample invertible module on `X`, and suppose the conormal sheaf `𝒞_{Z/X}`
is finite locally free of constant rank `r`. The proof chooses a surjection
`𝒪_Z^{⊕ m} ⟶ 𝒞_{Z/X} ⊗ (i^*L)^{⊗ n}` and the morphism `g : Z ⟶ 𝐆(m - r, m)` it classifies, and
embeds `Z` into `X × 𝐆(m - r, m)` by `(i, g)`. Then the class of the conormal sheaf of the new
embedding is pulled back from `X × 𝐆(m - r, m)`.

The statement here makes no use of the product: for **every** smooth `p : P ⟶ X` with a
morphism `q : P ⟶ 𝐆(m - r, m)` and an immersion `h : Z ⟶ P` with `h ≫ p = i` and `h ≫ q = g`,
the class of `𝒞_{Z/P}` in `K₀(Vect(Z))` is `h^*` of a class in `K₀(Vect(P))`. The product
`X ×_k 𝐆(m - r, m)_k` with its two projections is one such `P`, with `p` smooth because the
Grassmannian is smooth over `k`.

The argument is the source's. Up to the twist, which is a class pulled back from `X`, the class of
`𝒞_{Z/X}` is that of the quotient `𝒪_Z^{⊕ m} ⟶ 𝒞_{Z/X} ⊗ (i^*L)^{⊗ n}`, which is `g^*` of the class
of the universal quotient; so `[𝒞_{Z/X}] = h^*(q^*[𝒬_univ] · p^*β)`. The conormal sequence
`0 ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/P} ⟶ h^*Ω_{P/X} ⟶ 0` of [Stacks, Tag 067W] then adds `h^*[Ω_{P/X}]`.

## Main results

* `Stacks.Conormal.exists_grassmannian_classOf_conormalSheaf`: the statement above.

## References

* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
* [Stacks Project, Tag 067W](https://stacks.math.columbia.edu/tag/067W)
* [Stacks Project, Tag 089T](https://stacks.math.columbia.edu/tag/089T)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero

universe u

namespace Stacks.Conormal

/-- **The conormal class of a graph-type embedding into a Grassmannian bundle**, the `K₀` part of
the proof of [Stacks, Tag 0FIR]. Let `i : Z ⟶ X` be a closed immersion, `L` an ample invertible
module on `X`, and suppose `𝒞_{Z/X}` is finite locally free of constant rank `r`. Then for every
`m₀` there are `m ≥ m₀` with `r ≤ m` and a morphism `g : Z ⟶ 𝐆(m - r, m)` such that, whenever
`p : P ⟶ X` is smooth, `q : P ⟶ 𝐆(m - r, m)` is a morphism and `h : Z ⟶ P` is an immersion with
`h ≫ p = i` and `h ≫ q = g`, the class of `𝒞_{Z/P}` in `K₀(Vect(Z))` is the pullback along `h`
of a class of `K₀(Vect(P))`. -/
theorem exists_grassmannian_classOf_conormalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hL : Stacks.Ample.IsAmple X L) (r : ℕ)
    [hC : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (conormalSheaf i : Z.Modules) r] (m₀ : ℕ) :
    ∃ m : ℕ, m₀ ≤ m ∧ r ≤ m ∧ ∃ g : Z ⟶ Grassmannian.scheme.{u} (m - r) m,
      ∀ (P : Scheme.{u}) (p : P ⟶ X) [Smooth p] (q : P ⟶ Grassmannian.scheme.{u} (m - r) m)
        (h : Z ⟶ P) [IsImmersion h], h ≫ p = i → h ≫ q = g →
          ∃ γ : VectorBundleKZero P,
            pullbackRingHom h γ = classOf Z (conormalSheaf h) := by
  obtain ⟨m, hm, Q, φ, hφ, hQ, β, hβ⟩ :=
    Stacks.Ample.exists_epi_free_classOf_eq_mul_pullbackRingHom L i hL
      (conormalSheaf i : Z.Modules) r (hC := hC) (max m₀ r)
  have hrm : r ≤ m := le_of_max_le_right hm
  have hQ' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q
      (m - (m - r)) := by
    rwa [Nat.sub_sub_self hrm]
  have := hφ
  have := hQ'
  obtain ⟨g, hg⟩ := Grassmannian.exists_pullbackRingHom_universalClass_eq_classOf
    (k := m - r) Q φ
  refine ⟨m, le_of_max_le_left hm, hrm, g, fun P p _ q h _ hp hq => ?_⟩
  have hCi : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf i : Z.Modules) :=
    @Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree Z (conormalSheaf i)
      (@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
        _ _ _ _ _ _ (conormalSheaf i : Z.Modules) r hC)
  refine exists_pullbackRingHom_eq_classOf_conormalSheaf_of_smooth h i p hp hCi
    ⟨pullbackRingHom q (Grassmannian.universalClass.{u} (m - r) m) * pullbackRingHom p β, ?_⟩
  rw [map_mul, ← pullbackRingHom_comp_apply, ← pullbackRingHom_comp_apply, hq, hp, hg, hβ]

end Stacks.Conormal

end

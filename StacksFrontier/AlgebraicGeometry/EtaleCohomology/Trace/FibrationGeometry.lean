module

public import StacksFrontier.RingTheory.NoetherNormalization.FibreDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Topology.KrullDimension

/-!
# Fibres of a projection over the rational points of a compactification of the base

Let `g : U ⟶ A` be a morphism of schemes whose fibres have dimension at most one and
`i : A ⟶ P` an open immersion. A fibre of `g ≫ i` over a rational point of `P` is either empty
or embeds, by a closed immersion, into a fibre of `g`, so it has dimension at most one as well.

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_of_isPullback_of_isOpenImmersion`: the fibre of
  `g ≫ i` over a rational point of `P` has dimension at most the bound on the fibres of `g`.
* `AlgebraicGeometry.exists_mvPolynomial_fibration`: Noether normalization with fibres of dimension
  at most one, for an affine scheme of finite type over a field.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- **The fibre over a rational point of a compactification of the base.** Let `g : U ⟶ A` be a
morphism of schemes all of whose fibres have dimension at most `d`, `i : A ⟶ P` an open immersion
and `y : Spec k ⟶ P` a section of a morphism `P ⟶ Spec k`. Then every scheme `Z` in a cartesian
square `Z ⟶ U`, `Z ⟶ Spec k` over `g ≫ i` and `y` has dimension at most `d`. -/
theorem topologicalKrullDim_le_of_isPullback_of_isOpenImmersion {k : Type u} [Field k]
    {U A P Z : Scheme.{u}} (g : U ⟶ A) (i : A ⟶ P) [IsOpenImmersion i] (fP : P ⟶ Spec (.of k))
    (y : Spec (.of k) ⟶ P) (hy : y ≫ fP = 𝟙 _) {d : WithBot ℕ∞}
    (hfib : ∀ a : A, topologicalKrullDim (g.base ⁻¹' {a}) ≤ d)
    (a : Z ⟶ U) (c : Z ⟶ Spec (.of k)) (h : IsPullback a c (g ≫ i) y) :
    topologicalKrullDim Z ≤ d := by
  have : IsClosedImmersion y := isClosedImmersion_of_comp_eq_id fP y hy
  have : IsClosedImmersion a := by
    rw [← h.isoPullback_hom_fst]
    infer_instance
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · have : IsEmpty (TopologicalSpace.IrreducibleCloseds Z) :=
      ⟨fun s => hZ.false s.isIrreducible.nonempty.some⟩
    change Order.krullDim (TopologicalSpace.IrreducibleCloseds Z) ≤ d
    exact Order.krullDim_eq_bot.trans_le bot_le
  obtain ⟨z₀⟩ := hZ
  have hmem (z : Z) : a.base z ∈ g.base ⁻¹' {g.base (a.base z₀)} := by
    have hw (t : Z) : i.base (g.base (a.base t)) = y.base (c.base t) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]
    exact i.isOpenEmbedding.injective ((hw z).trans
      ((congrArg y.base (Subsingleton.elim (c.base z) (c.base z₀))).trans (hw z₀).symm))
  exact (a.isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le.trans (hfib _)

/-- **A projection of an affine scheme of finite type to `𝔸ⁿ` with fibres of dimension at most
one.** For `Spec R` of finite type over a field `k` and of dimension at most `n + 1` there is a
morphism `g : Spec R ⟶ 𝔸ⁿ_k` over `k` all of whose fibres have dimension at most one. -/
theorem exists_mvPolynomial_fibration {k : Type u} [Field k] (R : CommRingCat.{u})
    (ψ : CommRingCat.of k ⟶ R) [LocallyOfFiniteType (Spec.map ψ)] (n : ℕ)
    (hdim : topologicalKrullDim (Spec R) ≤ n + 1) :
    ∃ g : Spec R ⟶ Spec (.of (MvPolynomial (Fin n) k)),
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin n) k))) = Spec.map ψ ∧
        ∀ a, topologicalKrullDim (g.base ⁻¹' {a}) ≤ 1 := by
  let : Algebra k R := ψ.hom.toAlgebra
  have : Algebra.FiniteType k R :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).1 inferInstance
  obtain ⟨φ, hφ⟩ :=
    Stacks.NoetherNormalization.exists_algHom_mvPolynomial_topologicalKrullDim_fibre_le_one_of_le
      k R n (by rwa [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim])
  refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_, fun a => hφ a⟩
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact φ.commutes x

end AlgebraicGeometry

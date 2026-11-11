module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.NoetherNormalization.Basic
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Noether normalization at a point, with the topological local dimension

Stacks tag 00OZ (Commutative Algebra, Lemma 10.115.5).

Let `k` be a field, `S` a finite type `k`-algebra, `X = Spec(S)`, `𝔮` a prime of `S` and
`x ∈ X` the corresponding point. Stacks uses the dimension `dim_x(X)` of 0055 (4), the minimum of
`dim(U)` over the open neighbourhoods `U` of `x`; in Lean this is
`topologicalKrullDimAt (PrimeSpectrum S) x`.

`noether_normalization_at_point` in `StacksFrontier.RingTheory.NoetherNormalization.Basic` states the
lemma with `localDimAtPrime k 𝔮`, the infimum of `dim(S_g)` over `g ∉ 𝔮`. Here we prove that the
two agree (`topologicalKrullDimAt_eq_localDimAtPrime`): the standard opens `D(g)`, `g ∉ 𝔮`, form a
basis of neighbourhoods of `x`, `dim` is monotone in the open set, and `D(g)` is homeomorphic to
`Spec(S_g)`, whose dimension is `dim(S_g)` (`topologicalKrullDim_basicOpen_eq_ringKrullDim`).

## Main results

* `topologicalKrullDim_basicOpen_eq_ringKrullDim`: `dim D(g) = dim(S_g)`.
* `topologicalKrullDimAt_eq_localDimAtPrime`: `dim_x(X) = min_{g ∉ 𝔮} dim(S_g)`.
* `noether_normalization_at_point_topologicalKrullDimAt`: Stacks 00OZ as stated, with
  `dim_x(X)` the topological local dimension of 0055 (4).
-/

@[expose] public section

/-- **The dimension of a standard open is that of the localization it carries.** The map
`Spec(R_g) → Spec(R)` is an open embedding with image `D(g)`, hence a homeomorphism onto `D(g)`,
and `dim Spec(R_g) = dim(R_g)`. -/
theorem PrimeSpectrum.topologicalKrullDim_basicOpen_eq_ringKrullDim {R : Type*} [CommRing R]
    (g : R) :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) =
      ringKrullDim (Localization.Away g) := by
  rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g,
    ← IsHomeomorph.topologicalKrullDim_eq _
      (PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g)
        g).isEmbedding.toHomeomorph.isHomeomorph,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]

/-- **The topological local dimension of `Spec(S)` at a point is `localDimAtPrime`.** For the point
`x` of `X = Spec(S)` corresponding to a prime `𝔮`, the dimension `dim_x(X)` of Stacks 0055 (4),
the minimum of `dim(U)` over open `U ∋ x`, equals the infimum of `dim(S_g)` over `g ∉ 𝔮`. The
standard opens `D(g)`, `g ∉ 𝔮`, are open neighbourhoods of `x` with `dim D(g) = dim(S_g)`, and
every open neighbourhood of `x` contains one of them, of no larger dimension. The field `k` only
enters through the definition of `localDimAtPrime`. -/
theorem topologicalKrullDimAt_eq_localDimAtPrime (k : Type*) {S : Type*} [Field k] [CommRing S]
    [Algebra k S] (x : PrimeSpectrum S) :
    topologicalKrullDimAt (PrimeSpectrum S) x = localDimAtPrime k x.asIdeal := by
  refine le_antisymm (le_iInf₂ fun g hg => ?_) (le_iInf fun U => ?_)
  · rw [← PrimeSpectrum.topologicalKrullDim_basicOpen_eq_ringKrullDim]
    exact (topologicalKrullDimAt_isLeast (PrimeSpectrum S) x).2
      ⟨_, hg, (PrimeSpectrum.basicOpen g).isOpen, rfl⟩
  · obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open U.2.1 U.2.2
    calc localDimAtPrime k x.asIdeal ≤ ringKrullDim (Localization.Away g) := iInf₂_le g hxg
      _ = topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) :=
        (PrimeSpectrum.topologicalKrullDim_basicOpen_eq_ringKrullDim g).symm
      _ ≤ topologicalKrullDim U.1 := topologicalKrullDim_le_of_subset hgU

/-- **Noether normalization at a point.** Let `k` be a field, `S` a finite type `k`-algebra,
`X = Spec(S)`, `𝔮` a prime of `S` and `x ∈ X` the corresponding point. There exist `g ∈ S`,
`g ∉ 𝔮`, such that `dim(S_g) = dim_x(X) =: d`, and a finite injective `k`-algebra map
`k[y_1, …, y_d] → S_g`, where `k[y_1, …, y_d] = MvPolynomial (Fin d) k` and `dim_x(X)` is the
Krull dimension of the topological space `X` at `x` (Stacks 0055 (4)),
`topologicalKrullDimAt (PrimeSpectrum S) x`. -/
@[stacks 00OZ "dim_x(X) is topologicalKrullDimAt of 0055 (4); finite is ψ.toRingHom.Finite"]
theorem noether_normalization_at_point_topologicalKrullDimAt
    {k S : Type*} [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (q : Ideal S) [q.IsPrime] :
    ∃ (g : S) (_ : g ∉ q) (d : ℕ)
      (ψ : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g),
      (d : WithBot ℕ∞) = ringKrullDim (Localization.Away g) ∧
      (d : WithBot ℕ∞) = topologicalKrullDimAt (PrimeSpectrum S) ⟨q, ‹_›⟩ ∧
      Function.Injective ψ ∧
      ψ.toRingHom.Finite := by
  obtain ⟨g, hg, d, ψ, hd, hloc, hinj, hfin⟩ := noether_normalization_at_point (k := k) q
  exact ⟨g, hg, d, ψ, hd,
    hloc.trans (topologicalKrullDimAt_eq_localDimAtPrime k ⟨q, ‹_›⟩).symm, hinj, hfin⟩

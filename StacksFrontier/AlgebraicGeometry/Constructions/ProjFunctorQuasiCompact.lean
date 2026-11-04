module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpen
public import StacksFrontier.AlgebraicGeometry.OrderedOpenCover

/-!
# Morphisms from a quasi-compact scheme into `Proj`

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and `X = Proj 𝒜`. The degree `d` opens
`U_d = ⋃_{f ∈ 𝒜 d} D₊(f)` of `AlgebraicGeometry.Proj.degreeOpen` grow along divisibility and
cover `X`, but neither `X` nor any `U_d` need be quasi-compact. Consequently a morphism
`φ : T ⟶ X` from an arbitrary scheme need not factor through a single `U_d`.

For a **quasi-compact** `T` it does: the opens `φ⁻¹(U_d)`, `d ≥ 1`, cover `T`, finitely many of
them already do, and the product of those finitely many degrees is a single degree dominating all
of them. The factorization through the open immersion `U_d ⟶ X` is then unique, and it is
constructed — not chosen out of an existence statement — by the universal property of open
immersions.

This is the first of the two verifications that the Stacks Project omits in its proof of Tag
01NC, that the functor `F` of Section 01N4 is representable by `Proj(S)`. The second one,
`Mor(T, X) = lim_{V ⊆ T quasi-compact open} Mor(V, X)`, is
`AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens`.

Neither verification is the statement of Tag 01NC, and neither carries its tag: a reduction step
is not the lemma it reduces. The statement itself is proved, and consumes both verifications. The
functor `F` is the colimit of the functors `F_d` of Tag 01N9 along the transition maps
`F_d ⟶ F_{d'}` for `d ∣ d'` —
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fcolim`, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorColimit.lean`, whose surjectivity half
runs on the factorization below — extended from quasi-compact schemes by the limit formula above:
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F` and the representing datum
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F.representableBy`, in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjFunctorRepresentable.lean`. The representing
inputs are `Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair` (Tag 01N8),
`Stacks.AlgebraicGeometry.ProjDegreeOpenRepresents.existsUnique_hom` (Tag 01N9), the functor at a
fixed weight `Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.functor` with both functor laws,
and the universal family
`Stacks.AlgebraicGeometry.ProjDegreeOpenUniversalTriple.universalVeroneseSections`.

**A note on universes.** A triple
carries an `𝒪_Y`-module, so `F_d` and `F` land in `Type (u + 1)` while `Y ⟶ X` is in `Type u`.
No `CategoryTheory.uliftFunctor` is interposed, and none is needed:
`CategoryTheory.Functor.RepresentableBy` is stated for `F : Cᵒᵖ ⥤ Type v` with `v` independent of
the universe of the `Hom` sets of `C`, and its field `homEquiv` is an `Equiv` between types that
may live in two different universes.

## Main definitions

* `AlgebraicGeometry.Proj.factorThroughDegreeOpen` — the factorization of a morphism
  `φ : T ⟶ Proj 𝒜` whose image lies in `U_d` through the open subscheme `U_d`.

## Main results

* `AlgebraicGeometry.Proj.sup_degreeOpen_le` — the degree opens of positive degree are directed:
  `U_d ∪ U_{d'} ⊆ U_{d d'}`.
* `AlgebraicGeometry.Proj.exists_pos_range_subset_degreeOpen` — a morphism from a quasi-compact
  scheme into `Proj 𝒜` has its image inside `U_d` for some `d ≥ 1`.
* `AlgebraicGeometry.Proj.factorThroughDegreeOpen_comp_ι` and
  `AlgebraicGeometry.Proj.eq_factorThroughDegreeOpen` — the factorization is a factorization, and
  it is the only one.
* `AlgebraicGeometry.Proj.exists_pos_existsUnique_factorization` — **the reduction step**: every
  morphism from a quasi-compact scheme into `Proj 𝒜` factors uniquely through some `U_d` with
  `d ≥ 1`.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u w

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The degree opens of positive degree are directed.** Both `U_d` and `U_{d'}` lie in
`U_{d d'}`, since `d` and `d'` both divide the positive number `d d'`. -/
theorem sup_degreeOpen_le {d d' : ℕ} (hd : 0 < d) (hd' : 0 < d') :
    degreeOpen 𝒜 d ⊔ degreeOpen 𝒜 d' ≤ degreeOpen 𝒜 (d * d') :=
  sup_le (degreeOpen_le_of_dvd 𝒜 (dvd_mul_right d d') (Nat.mul_pos hd hd'))
    (degreeOpen_le_of_dvd 𝒜 (dvd_mul_left d' d) (Nat.mul_pos hd hd'))

/-- **A quasi-compact scheme mapping into `Proj 𝒜` lands in a single `U_d`.** The opens
`φ⁻¹(U_{e+1})`, `e : ℕ`, cover `T` because the `U_d` with `d ≥ 1` cover `Proj 𝒜`; by
quasi-compactness finitely many of them do, and the product of the degrees involved is a positive
degree divisible by each of them, so its degree open contains all of them. -/
theorem exists_pos_range_subset_degreeOpen {T : Scheme.{u}} [CompactSpace T]
    (φ : T ⟶ Proj 𝒜) :
    ∃ d : ℕ, 0 < d ∧ Set.range φ.base ⊆ (degreeOpen 𝒜 d : Set (Proj 𝒜)) := by
  have hcov : (Set.univ : Set T) ⊆
      ⋃ e : ℕ, ((φ ⁻¹ᵁ degreeOpen 𝒜 (e + 1) : T.Opens) : Set T) := by
    intro t _
    have ht : φ.base t ∈ (⊤ : (Proj 𝒜).Opens) := trivial
    rw [← iSup_degreeOpen_eq_top 𝒜] at ht
    obtain ⟨d, hd⟩ := Opens.mem_iSup.mp ht
    obtain ⟨hd0, hmem⟩ := Opens.mem_iSup.mp hd
    exact Set.mem_iUnion.mpr ⟨d - 1, by simpa [Nat.sub_add_cancel hd0] using hmem⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun e : ℕ => ((φ ⁻¹ᵁ degreeOpen 𝒜 (e + 1) : T.Opens) : Set T))
    (fun e => (φ ⁻¹ᵁ degreeOpen 𝒜 (e + 1)).2) hcov
  have hpos : 0 < ∏ e ∈ s, (e + 1) := Finset.prod_pos fun e _ => e.succ_pos
  refine ⟨∏ e ∈ s, (e + 1), hpos, ?_⟩
  rintro _ ⟨t, rfl⟩
  obtain ⟨e, he, ht⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
  exact degreeOpen_le_of_dvd 𝒜 (Finset.dvd_prod_of_mem _ he) hpos ht

/-- **The factorization of a morphism into `Proj 𝒜` through a degree open containing its image.**
This is the universal property of the open immersion `U_d ⟶ Proj 𝒜`, so the factorization is
constructed rather than chosen. -/
def factorThroughDegreeOpen {T : Scheme.{u}} (φ : T ⟶ Proj 𝒜) (d : ℕ)
    (h : Set.range φ.base ⊆ (degreeOpen 𝒜 d : Set (Proj 𝒜))) :
    T ⟶ (degreeOpen 𝒜 d).toScheme :=
  IsOpenImmersion.lift (degreeOpen 𝒜 d).ι φ (by rw [Scheme.Opens.range_ι]; exact h)

/-- The factorization through `U_d` composed with the inclusion `U_d ⟶ Proj 𝒜` is the original
morphism. -/
@[simp]
theorem factorThroughDegreeOpen_comp_ι {T : Scheme.{u}} (φ : T ⟶ Proj 𝒜) (d : ℕ)
    (h : Set.range φ.base ⊆ (degreeOpen 𝒜 d : Set (Proj 𝒜))) :
    factorThroughDegreeOpen 𝒜 φ d h ≫ (degreeOpen 𝒜 d).ι = φ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization through `U_d` is the only morphism into `U_d` composing with the inclusion
to give `φ`. -/
theorem eq_factorThroughDegreeOpen {T : Scheme.{u}} (φ : T ⟶ Proj 𝒜) (d : ℕ)
    (h : Set.range φ.base ⊆ (degreeOpen 𝒜 d : Set (Proj 𝒜)))
    (l : T ⟶ (degreeOpen 𝒜 d).toScheme) (hl : l ≫ (degreeOpen 𝒜 d).ι = φ) :
    l = factorThroughDegreeOpen 𝒜 φ d h :=
  IsOpenImmersion.lift_uniq _ _ _ l hl

/-- **Every morphism from a quasi-compact scheme into `Proj 𝒜` factors uniquely through some
`U_d` with `d ≥ 1`.** This is the first of the two verifications the Stacks Project omits in its
proof of Tag 01NC: in the language of that proof, a point of `F(T)` for quasi-compact `T` comes
from a single `F_d(T)`, whose representing object is `U_d`.

It is a step in that proof and not the lemma, so it carries no tag; the lemma is
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.F.representableBy`, which consumes this through
`Stacks.AlgebraicGeometry.ProjTripleDegreeFunctor.Fd.exists_pos_classifyingMorphism_eq`. -/
theorem exists_pos_existsUnique_factorization {T : Scheme.{u}} [CompactSpace T]
    (φ : T ⟶ Proj 𝒜) :
    ∃ d : ℕ, 0 < d ∧ ∃! ψ : T ⟶ (degreeOpen 𝒜 d).toScheme,
      ψ ≫ (degreeOpen 𝒜 d).ι = φ := by
  obtain ⟨d, hd, hrange⟩ := exists_pos_range_subset_degreeOpen 𝒜 φ
  exact ⟨d, hd, factorThroughDegreeOpen 𝒜 φ d hrange,
    factorThroughDegreeOpen_comp_ι 𝒜 φ d hrange,
    fun l hl => eq_factorThroughDegreeOpen 𝒜 φ d hrange l hl⟩

end AlgebraicGeometry.Proj

end

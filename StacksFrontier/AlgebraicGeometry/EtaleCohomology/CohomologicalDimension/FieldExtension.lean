module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.DirectedLimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.IntegralMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.LimitPresentation
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField

/-!
# Cohomological dimension of a field extension (Stacks 0F0T)

Let `L/K` be a field extension. [Stacks, Tag 0F0T] says `cd(L) ≤ cd(K) + trdeg_K(L)`, where the
cohomological dimension of a field is that of its spectrum (Tag 0F0Q). The source's proof: if the
transcendence degree is infinite there is nothing to prove; otherwise a tower
`K = L_0 ⊂ L_1 ⊂ … ⊂ L_r = L` with each step of transcendence degree one reduces to the case
`trdeg_K(L) = 1`, and there `L` is the filtered colimit of its finite type `K`-subalgebras `A`,
so `cd(L) ≤ sup cd(A)` by Tag 0F0R and each `cd(A) ≤ 1 + cd(K)` by Tag 0F0S.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_iSup_adjoin`: `cd(L)` is at most
  the supremum of `cd(K[s])` over the finite subsets `s` of `L` (Tag 0F0R).
* `AlgebraicGeometry.Scheme.topologicalKrullDim_spec_adjoin_le_trdeg`: `dim K[s] ≤ trdeg_K(L)`
  (Tag 00P0).
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_of_isAlgebraic`: for an algebraic
  extension, `cd(L) ≤ cd(K)`. This is the case `r = 0` of the tower, which the source leaves to
  the reader: each `K[s]` is then a finite extension of `K`, so `Spec K[s] ⟶ Spec K` is integral.
* `Algebra.trdeg_adjoin_simple_le_one`: `trdeg_K K(x) ≤ 1`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_add_trdeg_of_le_one_add`: the
  reduction to transcendence degree at most one, by induction along the tower `K ⊂ K(x) ⊂ L`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_one_add_of_trdeg_le_one`: the case
  `trdeg_K(L) ≤ 1`.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_spec_le_add_trdeg`: **Tag 0F0T**.

## References

* [Stacks Project, Tag 0F0T](https://stacks.math.columbia.edu/tag/0F0T)
* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- **A simple field extension has transcendence degree at most one.** `K(x)` is algebraic over
`K[x]`, which is a quotient of the polynomial ring `K[X]` of transcendence degree one. -/
theorem Algebra.trdeg_adjoin_simple_le_one (K L : Type u) [Field K] [Field L] [Algebra K L]
    (x : L) : Algebra.trdeg K (IntermediateField.adjoin K {x}) ≤ 1 := by
  open scoped IntermediateField.algebraAdjoinAdjoin in
  have htower := trdeg_add_eq K (Algebra.adjoin K ({x} : Set L))
    (A := IntermediateField.adjoin K ({x} : Set L))
  rw [trdeg_eq_zero (R := Algebra.adjoin K ({x} : Set L)), add_zero] at htower
  rw [← htower, ← Polynomial.trdeg_of_isDomain (R := K)]
  let e := (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval K x)).symm
  exact trdeg_le_of_surjective (e.toAlgHom.comp (Polynomial.aeval x).rangeRestrict)
    (e.surjective.comp (AlgHom.rangeRestrict_surjective _))

namespace AlgebraicGeometry.Scheme

open Stacks.EtaleCohomology

/-- **A ring is the limit of its finitely generated subalgebras, for cohomological dimension.**
For a `K`-algebra `L`, `cd(Spec L)` is at most the supremum of `cd(Spec K[s])` over the finite
subsets `s` of `L`: `Spec L` is the directed limit of the affine schemes `Spec K[s]`
(`Stacks.EtaleCohomology.finsetSubalgebraIsColimit`), with affine transition morphisms, so this
is Tag 0F0R (`etaleCohomologicalDimension_le_iSup_of_isLimit_of_isDirected`). -/
theorem etaleCohomologicalDimension_spec_le_iSup_adjoin
    (K L : Type u) [CommRing K] [CommRing L] [Algebra K L] :
    etaleCohomologicalDimension (Spec (.of L)) ≤
      ⨆ s : (Finset L)ᵒᵖ,
        etaleCohomologicalDimension
          (Spec (.of (Algebra.adjoin K ((s.unop : Finset L) : Set L)))) := by
  classical
  have : ∀ {i j : (Finset L)ᵒᵖ} (a : i ⟶ j),
      IsAffineHom (((finsetSubalgebraDiagram K L).op ⋙ Scheme.Spec).map a) :=
    fun a => inferInstanceAs (IsAffineHom (Spec.map _))
  have : ∀ i : (Finset L)ᵒᵖ,
      CompactSpace (((finsetSubalgebraDiagram K L).op ⋙ Scheme.Spec).obj i) :=
    fun i => inferInstanceAs (CompactSpace (Spec _))
  have : ∀ i : (Finset L)ᵒᵖ,
      QuasiSeparatedSpace (((finsetSubalgebraDiagram K L).op ⋙ Scheme.Spec).obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Spec _))
  have : CompactSpace (Scheme.Spec.mapCone (finsetSubalgebraCocone K L).op).pt :=
    inferInstanceAs (CompactSpace (Spec (.of L)))
  have : QuasiSeparatedSpace (Scheme.Spec.mapCone (finsetSubalgebraCocone K L).op).pt :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of L)))
  exact etaleCohomologicalDimension_le_iSup_of_isLimit_of_isDirected
    ((finsetSubalgebraDiagram K L).op ⋙ Scheme.Spec)
    (c := Scheme.Spec.mapCone (finsetSubalgebraCocone K L).op)
    (isLimitOfPreserves Scheme.Spec (finsetSubalgebraIsColimit (A := K) (B := L)).op)

/-- **The finitely generated subalgebras of a field extension have dimension at most the
transcendence degree.** For `L/K` a field extension and `s` a finite subset of `L`, the domain
`K[s]` has Krull dimension the transcendence degree of its field of fractions (Tag 00P0), which
embeds in `L`. -/
theorem topologicalKrullDim_spec_adjoin_le_trdeg (K L : Type u) [Field K] [Field L]
    [Algebra K L] (s : Finset L) :
    topologicalKrullDim (Spec (.of (Algebra.adjoin K (s : Set L)))) ≤
      (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) := by
  let A := Algebra.adjoin K (s : Set L)
  have : Algebra.FiniteType K A := .adjoin_of_finite s.finite_toSet
  let F := FractionRing A
  have hdim := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, u} K A F).1
  rw [show topologicalKrullDim (Spec (.of A)) = ringKrullDim A from
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A, hdim]
  let φ : F →ₐ[K] L := IsFractionRing.liftAlgHom (K := F) (g := A.val) Subtype.val_injective
  exact_mod_cast Cardinal.toENat.monotone' (trdeg_le_of_injective φ φ.toRingHom.injective)

/-- **The case `trdeg_K(L) = 0` of Tag 0F0T: an algebraic extension does not raise the
cohomological dimension.** For `L/K` algebraic, every finitely generated subalgebra `K[s]` of `L`
is integral over `K`, so `Spec K[s] ⟶ Spec K` is integral and `cd(K[s]) ≤ cd(K)`
(`etaleCohomologicalDimension_le_of_isIntegralHom`); the limit over `s` is Tag 0F0R. -/
theorem etaleCohomologicalDimension_spec_le_of_isAlgebraic (K L : Type u) [Field K] [Field L]
    [Algebra K L] [Algebra.IsAlgebraic K L] :
    etaleCohomologicalDimension (Spec (.of L)) ≤ etaleCohomologicalDimension (Spec (.of K)) := by
  refine (etaleCohomologicalDimension_spec_le_iSup_adjoin K L).trans (iSup_le fun s => ?_)
  let A := Algebra.adjoin K ((s.unop : Finset L) : Set L)
  have : Algebra.IsAlgebraic K A := Algebra.IsAlgebraic.of_injective A.val Subtype.val_injective
  have : Algebra.IsIntegral K A := Algebra.IsAlgebraic.isIntegral
  have : IsIntegralHom (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  exact etaleCohomologicalDimension_le_of_isIntegralHom
    (Spec.map (CommRingCat.ofHom (algebraMap K A)))

/-- **Tag 0F0T reduced to transcendence degree at most one.** Suppose that for every field
extension `L/K` (in the universe `u`) with `trdeg_K(L) ≤ 1` one has `cd(L) ≤ 1 + cd(K)`. Then
`cd(L) ≤ cd(K) + trdeg_K(L)` for every field extension.

This is the source's tower argument. Infinite transcendence degree is clear. For finite
transcendence degree `n` induct on `n`: if `L/K` is algebraic this is
`etaleCohomologicalDimension_spec_le_of_isAlgebraic`; otherwise choose `x ∈ L` transcendental
over `K` and put `M = K(x)`. Then `trdeg_K(M) = 1` (`Algebra.trdeg_adjoin_simple_le_one` and the
transcendence of `x`), so `trdeg_M(L) = n - 1` by the tower law (Tag 030H), and
`cd(L) ≤ cd(M) + (n - 1) ≤ 1 + cd(K) + (n - 1)`. -/
theorem etaleCohomologicalDimension_spec_le_add_trdeg_of_le_one_add
    (h1 : ∀ (K L : Type u) [Field K] [Field L] [Algebra K L], Algebra.trdeg K L ≤ 1 →
      etaleCohomologicalDimension (Spec (.of L)) ≤
        1 + etaleCohomologicalDimension (Spec (.of K)))
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    etaleCohomologicalDimension (Spec (.of L)) ≤
      etaleCohomologicalDimension (Spec (.of K)) + (Algebra.trdeg K L).toENat := by
  suffices H : ∀ n : ℕ, ∀ (K L : Type u) [Field K] [Field L] [Algebra K L],
      (Algebra.trdeg K L).toENat ≤ n →
        etaleCohomologicalDimension (Spec (.of L)) ≤
          etaleCohomologicalDimension (Spec (.of K)) + n by
    induction h : (Algebra.trdeg K L).toENat using ENat.recTopCoe with
    | top => simp
    | coe n => exact H n K L h.le
  intro n
  induction n with
  | zero =>
    intro K L _ _ _ h
    have : Algebra.IsAlgebraic K L := trdeg_eq_zero_iff.mp (by simpa using h)
    simpa using etaleCohomologicalDimension_spec_le_of_isAlgebraic K L
  | succ n ih =>
    intro K L _ _ _ h
    by_cases halg : Algebra.IsAlgebraic K L
    · exact (etaleCohomologicalDimension_spec_le_of_isAlgebraic K L).trans le_self_add
    obtain ⟨x, hx⟩ := Algebra.transcendental_def.mp
      (Algebra.transcendental_iff_not_isAlgebraic.mpr halg)
    let M := IntermediateField.adjoin K ({x} : Set L)
    have hM1 : Algebra.trdeg K M ≤ 1 := Algebra.trdeg_adjoin_simple_le_one K L x
    have hM0 : 1 ≤ Algebra.trdeg K M :=
      Cardinal.one_le_iff_ne_zero.mpr (trdeg_ne_zero_iff.mpr (Algebra.transcendental_def.mpr
        ⟨IntermediateField.AdjoinSimple.gen K x,
          (transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective M L)).mp hx⟩))
    have hML : (Algebra.trdeg M L).toENat ≤ n := by
      have h' : (Algebra.trdeg K M).toENat + (Algebra.trdeg M L).toENat ≤ (n : ℕ∞) + 1 := by
        rw [← map_add, trdeg_add_eq K M (A := L)]
        exact_mod_cast h
      have hM1' : (Algebra.trdeg K M).toENat = 1 :=
        le_antisymm (by simpa using Cardinal.toENat.monotone' hM1)
          (by simpa using Cardinal.toENat.monotone' hM0)
      rw [hM1', add_comm] at h'
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'
    calc etaleCohomologicalDimension (Spec (.of L))
        ≤ etaleCohomologicalDimension (Spec (.of M)) + n := ih M L hML
      _ ≤ 1 + etaleCohomologicalDimension (Spec (.of K)) + n := by
        gcongr
        exact h1 K M hM1
      _ = etaleCohomologicalDimension (Spec (.of K)) + ((n + 1 : ℕ) : ℕ∞) := by
        push_cast
        ring

/-- **Tag 0F0T for transcendence degree at most one.** For a field extension `L/K` with
`trdeg_K(L) ≤ 1`, `cd(L) ≤ 1 + cd(K)`: by Tag 0F0R `cd(L) ≤ sup cd(K[s])`, and each `K[s]` is an
affine scheme of finite type over `K` of dimension at most `trdeg_K(L) ≤ 1` (Tag 00P0), so
`cd(K[s]) ≤ 1 + cd(K)` by Tag 0F0S (`etaleCohomologicalDimension_le_one_add`). -/
theorem etaleCohomologicalDimension_spec_le_one_add_of_trdeg_le_one
    {K L : Type u} [Field K] [Field L] [Algebra K L] (h : Algebra.trdeg K L ≤ 1) :
    etaleCohomologicalDimension (Spec (.of L)) ≤
      1 + etaleCohomologicalDimension (Spec (.of K)) := by
  refine (etaleCohomologicalDimension_spec_le_iSup_adjoin K L).trans (iSup_le fun s => ?_)
  let A := Algebra.adjoin K ((s.unop : Finset L) : Set L)
  have : Algebra.FiniteType K A := .adjoin_of_finite s.unop.finite_toSet
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hdim : topologicalKrullDim (Spec (.of A)) ≤ 1 := by
    refine (topologicalKrullDim_spec_adjoin_le_trdeg K L s.unop).trans ?_
    exact_mod_cast (show Cardinal.toENat (Algebra.trdeg K L) ≤ 1 by
      simpa using Cardinal.toENat.monotone' h)
  exact etaleCohomologicalDimension_le_one_add
    (Spec.map (CommRingCat.ofHom (algebraMap K A))) hdim

/-- **Stacks Project, Tag 0F0T** (Étale Cohomology, Lemma 59.95.4). Let `L/K` be a field
extension. Then `cd(L) ≤ cd(K) + trdeg_K(L)`.

The cohomological dimension of a field is that of its spectrum (Tag 0F0Q: "if `X = Spec(A)` we
sometimes call this the cohomological dimension of `A`"), `etaleCohomologicalDimension`, valued in
`ℕ∞`; the transcendence degree is the cardinal `Algebra.trdeg K L` read in `ℕ∞` by
`Cardinal.toENat`, so that an infinite transcendence degree is `⊤` and the inequality is then
clear, as in the source.

The proof is the source's: a tower of transcendence degree one steps
(`etaleCohomologicalDimension_spec_le_add_trdeg_of_le_one_add`, which also treats the algebraic
case `r = 0`) reduces to `trdeg_K(L) ≤ 1`, which is
`etaleCohomologicalDimension_spec_le_one_add_of_trdeg_le_one` (Tags 0F0R and 0F0S). -/
@[stacks 0F0T]
theorem etaleCohomologicalDimension_spec_le_add_trdeg
    (K L : Type u) [Field K] [Field L] [Algebra K L] :
    etaleCohomologicalDimension (Spec (.of L)) ≤
      etaleCohomologicalDimension (Spec (.of K)) + (Algebra.trdeg K L).toENat :=
  etaleCohomologicalDimension_spec_le_add_trdeg_of_le_one_add
    (fun _ _ _ _ _ h => etaleCohomologicalDimension_spec_le_one_add_of_trdeg_le_one h) K L

end AlgebraicGeometry.Scheme

end

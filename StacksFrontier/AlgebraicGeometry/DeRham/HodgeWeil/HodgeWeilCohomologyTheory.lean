module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Degeneration
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.AxiomsBasic
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.BaseChangeBijective
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.KunnethAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.Blowup
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorAxiom
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.TraceAxioms
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DeRhamWeilCohomologyTheory

/-!
# Hodge cohomology is a Weil cohomology theory (Remark 0FWE)

Let `k` be a field of characteristic zero. Remark 0FWE of the Stacks project makes two
mathematical assertions, and the rest of it is commentary.

1. **Hodge cohomology `X ↦ H^*_{Hodge}(X/k)` equipped with `c₁^{Hodge}` determines a Weil
   cohomology theory** (Definition 0FI2), "in exactly the same manner" as de Rham cohomology
   (Proposition 0FWD). This is `Stacks.HodgeWeil.exists_weilCohomologyTheory_hodge`, stated as
   `Stacks.WeilDeRham.exists_weilCohomologyTheory_deRham` is: the Hodge data (D0), (D1), (D2')
   `Stacks.HodgeWeil.hodgeFirstChernClassData k` satisfy (A1) – (A8) of Section 0FID, so they
   have a cohomological Chern character `ch` (Tag 0FIE) and Proposition 0FIU
   (`Stacks.WeilCohomology.WeilChernData.exists_weilCohomologyTheory`) makes the data
   `h.toWeilData …` of Section 0FHA a Weil cohomology theory. The axioms are
   * (A1) `Stacks.HodgeWeil.hodge_coproductAxiom`, (A2) `Stacks.HodgeWeil.hodge_pullbackAxiom`,
     (A8) `Stacks.HodgeWeil.hodge_globalSectionsAxiom`;
   * (A3) `Stacks.HodgeWeil.hodge_projectiveBundleAxiom`,
     (A4) `Stacks.HodgeWeil.hodge_divisorAxiom`;
   * (A5) `Stacks.HodgeWeil.hodge_kunnethAxiom`, (A7) `Stacks.HodgeWeil.hodge_blowupAxiom`;
   * (A6) `Stacks.HodgeWeil.hodge_traceAxiom`.
2. **The "amusing consequence"**: if the betti numbers of a Weil cohomology theory over `k` are
   independent of the chosen Weil cohomology theory, then the Hodge-to-de Rham spectral sequence
   degenerates at `E_1`. This is `Stacks.HodgeWeil.degeneratesAt_one_of_finrank_grade_eq`. The
   proof is the one the remark has in mind: applied to Hodge cohomology (part 1) and to de Rham
   cohomology (Proposition 0FWD), independence gives
   `∑_{p + q = n} dim_k H^q(X, Ω^p_{X/k}) = dim_k H^n_{Hodge}(X/k) = dim_k H^n_{dR}(X/k)`, the
   Hodge groups being finite dimensional, and this equality in every degree is equivalent to
   `E_1`-degeneration (`Stacks.HodgeWeil.degeneratesAt_one_iff_finrank_deRham_eq_sum_hodge`).

The remaining sentences of the remark are not mathematical assertions and are not formalized:
* "If we ever need this, we will precisely formulate and prove this here." (a promise);
* "Of course, the degeneration of the Hodge-to-de Rham spectral sequence is known (see for example
  [Deligne-Illusie] for a marvelous algebraic proof), but it is by no means an easy result!"
  (a citation and an appraisal; the degeneration itself is not claimed by the remark);
* "This suggests that proving the independence of betti numbers is a hard problem as well and as
  far as we know is still an open problem." (commentary on an open problem);
* "See Weil Cohomology Theories, Remark 0FI3 for a related question." (a cross-reference).

## Conventions

* A Weil cohomology theory over `k` with coefficients in `F` is
  `Stacks.WeilCohomology.WeilCohomologyTheory k F` (Definition 0FI2); the coefficient field `F`
  has characteristic zero, as in Definition 0FI2, and its `n`-th betti number at `X` is
  `dim_F H^n(X)`, `Module.finrank F (W.grade X n)`.
* The Hodge-to-de Rham spectral sequence of `X` is any brutal-truncation spectral sequence
  `E_1^{p, q} = H^q(X, Ω^p_{X/k}) ⟹ H^{p + q}_{dR}(X/k)` of the de Rham complex abutting to de Rham
  cohomology (`Stacks.Cohomology.FilteredComplex.StupidTruncationSpectralSequence` with
  `SpectralSequence.AbutsTo`); one exists by Tag 0FM7
  (`AlgebraicGeometry.SheafOfModules.exists_hodgeToDeRhamSpectralSequence`), and part 2 is stated
  for every one of them.

## Main results

* `Stacks.HodgeWeil.exists_weilCohomologyTheory_hodge`: **Remark 0FWE, part 1**.
* `Stacks.HodgeWeil.degeneratesAt_one_of_finrank_grade_eq`: **Remark 0FWE, part 2**.
* `Stacks.HodgeWeil.finiteDimensional_hodgeCohomologyComponent`: `H^q(X, Ω^p_{X/k})` is finite
  dimensional over `k` for `X` smooth projective over `k`.
* `Stacks.HodgeWeil.finrank_hodgeGradeOf`: `dim_k H^n_{Hodge}(X/k) = ∑_{p + q = n} h^{p, q}`.
* `Stacks.HodgeWeil.finrank_deRhamGrade`: the `n`-th betti number of the de Rham data is
  `dim_k H^n_{dR}(X/k)`.
* `Stacks.HodgeWeil.degeneratesAt_one_of_finrank_hodgeGradeOf_eq`: if the betti numbers of the
  Hodge and de Rham data of `X` agree, every Hodge-to-de Rham spectral sequence of `X`
  degenerates at `E_1`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Proposition 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Definition 0FI2](https://stacks.math.columbia.edu/tag/0FI2)
* [Stacks Project, Proposition 0FIU](https://stacks.math.columbia.edu/tag/0FIU)
* [Stacks Project, Tag 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamCohomology
  deRhamComplexInt deRhamDifferential baseRingedSpace)
open Stacks.Cohomology.FilteredComplex (StupidTruncationSpectralSequence)

universe u

namespace Stacks.HodgeWeil

variable {k : Type u} [Field k]

/-! ### Betti numbers of the Hodge and de Rham data -/

section Betti

variable (X : (SmoothProjectiveScheme k).FullSubcategory)

/-- **`H^q(X, Ω^p_{X/k})` is finite dimensional over `k`** for `X` smooth projective over `k`
([Stacks, Tag 02O6]: `Ω^p_{X/k}` is coherent and `X` is proper over `k`). -/
theorem finiteDimensional_hodgeCohomologyComponent (p : ℕ) (q : ℤ) :
    FiniteDimensional k (hodgeCohomologyComponent (formsAlgebras X.obj.hom) p q) := by
  have : IsProper X.obj.hom := (isProjective X).isProper
  have := finiteDimensional_pointCohomology_derivedFormsDirectImage X.obj.hom p q
  exact (hodgeLerayEquiv X p q).finiteDimensional

/-- The bidegrees `(p, q)` with `p + q = n`, as an integer, are the points of the antidiagonal
`Finset.HasAntidiagonal.antidiagonal n`. -/
def hodgeBidegreeIntEquivAntidiagonal (n : ℕ) :
    HodgeBidegreeInt (n : ℤ) ≃ (Finset.HasAntidiagonal.antidiagonal n) :=
  Equiv.subtypeEquivRight fun i => by
    rw [Finset.HasAntidiagonal.mem_antidiagonal, Nat.cast_inj]

/-- `H^n_{Hodge}(X/k) = ⨁_{p + q = n} H^q(X, Ω^p_{X/k})` as `k`-vector spaces, the sum being over
the antidiagonal. -/
def hodgePieceEquivAntidiagonal (n : ℕ) :
    letI := hodgePieceModule (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom) (n : ℤ)
    hodgePiece (formsAlgebras X.obj.hom) (n : ℤ) ≃ₗ[k]
      DirectSum (Finset.HasAntidiagonal.antidiagonal n) fun i =>
        (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u) :=
  let := hodgePieceModule (formsAlgebras X.obj.hom) (hodgeScalarsOverField X.obj.hom) (n : ℤ)
  ({ AddEquiv.refl _ with map_smul' := fun _ _ => DFinsupp.ext fun _ => rfl } :
      hodgePiece (formsAlgebras X.obj.hom) (n : ℤ) ≃ₗ[k]
        DirectSum (HodgeBidegreeInt (n : ℤ)) fun i =>
          (hodgeCohomologyComponent (formsAlgebras X.obj.hom) i.1.1 (i.1.2 : ℤ) : Type u)) ≪≫ₗ
    DirectSum.lequivCongrLeft k (hodgeBidegreeIntEquivAntidiagonal n)

/-- **The betti numbers of Hodge cohomology are sums of Hodge numbers**:
`dim_k H^n_{Hodge}(X/k) = ∑_{p + q = n} dim_k H^q(X, Ω^p_{X/k})`. -/
theorem finrank_hodgeGradeOf (n : ℕ) :
    Module.finrank k (hodgeGradeOf X n) =
      ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n,
        Module.finrank k (hodgeCohomologyComponent (formsAlgebras X.obj.hom) pq.1 (pq.2 : ℤ)) := by
  have := fun p q => finiteDimensional_hodgeCohomologyComponent X p q
  rw [(hodgeGradeEquiv X n).finrank_eq, (hodgePieceEquivAntidiagonal X n).finrank_eq,
    Module.finrank_directSum]
  exact Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n) fun pq =>
    Module.finrank k (hodgeCohomologyComponent (formsAlgebras X.obj.hom) pq.1 (pq.2 : ℤ))

/-- **The betti numbers of the de Rham data**: the degree-`n` part of `H^*_{dR}(X/k)` has
dimension `dim_k H^n_{dR}(X/k)`, `k` acting through `k ⟶ Γ(X, f⁻¹𝒪_{Spec k})`. -/
theorem finrank_deRhamGrade (n : ℤ) :
    Module.finrank k (Stacks.DeRhamWeil.grade X n) =
      Module.finrank k ((ModuleCat.restrictScalars.{u} (hodgeScalarsOverField X.obj.hom)).obj
        (deRhamCohomology (formsAlgebras X.obj.hom)
        (deRhamDifferential (formsAlgebras X.obj.hom)) n)) :=
  ((DirectSum.rangeGradingEquiv k (Stacks.DeRhamWeil.piece X) n).trans
    ({ AddEquiv.refl _ with map_smul' := fun _ _ => rfl } :
      Stacks.DeRhamWeil.piece X n ≃ₗ[k]
        ((ModuleCat.restrictScalars.{u} (hodgeScalarsOverField X.obj.hom)).obj
          (deRhamCohomology (formsAlgebras X.obj.hom)
        (deRhamDifferential (formsAlgebras X.obj.hom))
            n)))).finrank_eq

/-- **Equal betti numbers force `E_1`-degeneration** (the argument of Remark 0FWE): if for `X`
smooth projective over `k` the `n`-th betti numbers of Hodge and of de Rham cohomology agree for
every `n`, then every Hodge-to-de Rham spectral sequence of `X` (a brutal-truncation spectral
sequence of `Ω^•_{X/k}` abutting to `H^*_{dR}(X/k)`, Tag 0FM7) degenerates at `E_1`. -/
theorem degeneratesAt_one_of_finrank_hodgeGradeOf_eq
    (h : ∀ n : ℕ, Module.finrank k (hodgeGradeOf X n) =
      Module.finrank k (Stacks.DeRhamWeil.grade X n))
    (S : StupidTruncationSpectralSequence (baseRingedSpace _)
      (deRhamComplexInt (X := X.obj.left.toRingedSpace) (formsAlgebras X.obj.hom)
        (deRhamDifferential (formsAlgebras X.obj.hom))))
    (hS : SpectralSequence.AbutsTo S.spectralSequence
      (deRhamCohomology (X := X.obj.left.toRingedSpace) (formsAlgebras X.obj.hom)
        (deRhamDifferential (formsAlgebras X.obj.hom)))) :
    S.spectralSequence.DegeneratesAt 1 := by
  refine (degeneratesAt_one_iff_finrank_deRham_eq_sum_hodge _ _
    (hodgeScalarsOverField X.obj.hom) S hS
    fun p q => finiteDimensional_hodgeCohomologyComponent X p q).2 fun n => ?_
  rw [← finrank_deRhamGrade, ← h n, finrank_hodgeGradeOf]
  rfl

end Betti

/-! ### The Weil cohomology theory and the consequence -/

section Weil

/-- The betti numbers of a Weil cohomology theory are those of its data (D0) – (D3). -/
theorem finrank_grade_eq_of_toWeilData_eq {F : Type u} [Field F] {W : WeilCohomologyTheory k F}
    {D : WeilData k F} (hW : W.toWeilData = D) (X : (SmoothProjectiveScheme k).FullSubcategory)
    (n : ℤ) : Module.finrank F (W.grade X n) = Module.finrank F (D.grade X n) := by
  subst hW
  rfl

variable (k) in
/-- **Stacks Project, Remark 0FWE, part 1**: for a field `k` of characteristic zero, Hodge
cohomology `X ↦ H^*_{Hodge}(X/k) = ⨁_{p, q} H^q(X, Ω^p_{X/k})` on smooth projective schemes over
`k`, equipped with `c₁^{Hodge}`, determines a Weil cohomology theory over `k` with coefficients in
`k` (Definition 0FI2).

Formulation, as for de Rham cohomology (Proposition 0FWD,
`Stacks.WeilDeRham.exists_weilCohomologyTheory_deRham`): there is a Weil cohomology theory
`W : WeilCohomologyTheory k k` (data (D0) – (D3) satisfying (A), (B), (C) and condition (2) of
Lemma 0FI0) whose data are `h.toWeilData …` for a cohomological Chern character `h` (Tag 0FIE) of
the Hodge data `hodgeFirstChernClassData k`, so that
* (D0) `F(1)` is `k`;
* (D1) `H^*(X)` is `H^*_{Hodge}(X/k)` graded by total degree, with its cup product and pullbacks;
* (D2) the cycle class map `γ` is the one of Lemma 0FIF built from `c₁^{Hodge}` (the Chern
  character is determined by `c₁^{Hodge}`,
  `FirstChernClassData.existsUnique_isCohomologicalChernCharacter`);
* (D3) `∫_X` is the trace map `λ_X` of axiom (A6), normalised by `(1 ⊗ λ_X)γ([Δ]) = 1`.

The proof is the one of Proposition 0FWD: (A1) – (A8) for the Hodge data and Proposition 0FIU. -/
@[stacks 0FWE "part 1 (the first sentence): for k of characteristic zero, Hodge cohomology \
H^*_Hodge(-/k) with c_1^Hodge is a Weil cohomology theory (Definition 0FI2, coefficients k), \
with data (D0)-(D3) those of Hodge cohomology: F(1) = k, H^* = H^*_Hodge(-/k) with cup product \
and pullbacks, gamma from c_1^Hodge (0FIF), trace lambda of (A6). Part 2 (the consequence) is \
degeneratesAt_one_of_finrank_grade_eq"]
theorem exists_weilCohomologyTheory_hodge [CharZero k] :
    ∃ W : WeilCohomologyTheory k k, ∃ ch,
      ∃ h : (hodgeFirstChernClassData k).IsCohomologicalChernCharacter ch,
        W.toWeilData = h.toWeilData (hodge_coproductAxiom k) (hodge_projectiveBundleAxiom k)
          (hodge_kunnethAxiom k) (hodge_traceAxiom k h) := by
  have h := (hodgeFirstChernClassData k).isCohomologicalChernCharacter_chernCharacterOf
    (hodge_coproductAxiom k) (hodge_pullbackAxiom k) (hodge_projectiveBundleAxiom k)
    (hodge_divisorAxiom k)
  obtain ⟨W, hW⟩ := WeilChernData.exists_weilCohomologyTheory
    { toFirstChernClassData := hodgeFirstChernClassData k
      coproduct := hodge_coproductAxiom k
      pullback := hodge_pullbackAxiom k
      projectiveBundle := hodge_projectiveBundleAxiom k
      divisor := hodge_divisorAxiom k
      kunneth := hodge_kunnethAxiom k
      trace := hodge_traceAxiom k h
      blowup := hodge_blowupAxiom k } (hodge_globalSectionsAxiom k)
  exact ⟨W, _, h, hW⟩

/-- **Stacks Project, Remark 0FWE, part 2** (the "amusing consequence"): let `k` be a field of
characteristic zero. If the betti numbers of a Weil cohomology theory over `k` are independent of
the chosen Weil cohomology theory, then the Hodge-to-de Rham spectral sequence degenerates at
`E_1`.

Formulation: the hypothesis `hbetti` says that for any two Weil cohomology theories `W`, `W'` over
`k` (Definition 0FI2), with coefficients in fields `F`, `F'` of characteristic zero,
`dim_F H^n_W(X) = dim_{F'} H^n_{W'}(X)` for every smooth projective `X` over `k` and every `n`.
The conclusion is that for every smooth projective `X` over `k`, every Hodge-to-de Rham spectral
sequence `E_1^{p, q} = H^q(X, Ω^p_{X/k}) ⟹ H^{p + q}_{dR}(X/k)` of `X` (a brutal-truncation
spectral sequence of `Ω^•_{X/k}` abutting to `H^*_{dR}(X/k)`, which exists by Tag 0FM7)
degenerates at `E_1`.

The proof: by part 1 (`exists_weilCohomologyTheory_hodge`) and Proposition 0FWD
(`Stacks.WeilDeRham.exists_weilCohomologyTheory_deRham`), Hodge and de Rham cohomology are Weil
cohomology theories with coefficients in `k`, so `hbetti` gives
`dim_k H^n_{Hodge}(X/k) = dim_k H^n_{dR}(X/k)`; as the Hodge groups are finite dimensional this
is `E_1`-degeneration (`degeneratesAt_one_of_finrank_hodgeGradeOf_eq`). -/
@[stacks 0FWE "part 2 (the amusing consequence): over k of characteristic zero, if the betti \
numbers dim_F H^n(X) of Weil cohomology theories (any coefficient fields F of characteristic \
zero) do not depend on the theory, then for every smooth projective X over k the Hodge-to-de \
Rham spectral sequence (every brutal-truncation spectral sequence of the de Rham complex \
abutting to H^*_dR(X/k), 0FM7) degenerates at E_1. Part 1 is exists_weilCohomologyTheory_hodge"]
theorem degeneratesAt_one_of_finrank_grade_eq [CharZero k]
    (hbetti : ∀ (F F' : Type u) [Field F] [CharZero F] [Field F'] [CharZero F']
      (W : WeilCohomologyTheory k F) (W' : WeilCohomologyTheory k F')
      (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ),
      Module.finrank F (W.grade X n) = Module.finrank F' (W'.grade X n))
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (S : StupidTruncationSpectralSequence (baseRingedSpace _)
      (deRhamComplexInt (X := X.obj.left.toRingedSpace) (formsAlgebras X.obj.hom)
        (deRhamDifferential (formsAlgebras X.obj.hom))))
    (hS : SpectralSequence.AbutsTo S.spectralSequence
      (deRhamCohomology (X := X.obj.left.toRingedSpace) (formsAlgebras X.obj.hom)
        (deRhamDifferential (formsAlgebras X.obj.hom)))) :
    S.spectralSequence.DegeneratesAt 1 := by
  obtain ⟨WH, _, _, hWH⟩ := exists_weilCohomologyTheory_hodge k
  obtain ⟨WdR, _, _, hWdR⟩ := Stacks.WeilDeRham.exists_weilCohomologyTheory_deRham (k := k)
  refine degeneratesAt_one_of_finrank_hodgeGradeOf_eq X (fun n => ?_) S hS
  have h := hbetti k k WH WdR X n
  rw [finrank_grade_eq_of_toWeilData_eq hWH, finrank_grade_eq_of_toWeilData_eq hWdR] at h
  exact h

end Weil

end Stacks.HodgeWeil

end

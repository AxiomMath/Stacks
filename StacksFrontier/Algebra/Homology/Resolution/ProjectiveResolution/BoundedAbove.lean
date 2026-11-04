module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring.Basic
public import StacksFrontier.Algebra.Homology.Resolution.Defs.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution.EpiResData

/-!
# Projective resolutions of bounded-above complexes

Let `C` be an abelian category with enough projectives. Every cochain complex `K` with
`K^n = 0` for `n > a` admits a projective resolution `P → K`, bounded above by `a`, whose
components `P^n → K^n` are all epimorphisms ([Stacks, Tag 0646] (3)). Every cochain complex
whose cohomology vanishes in all sufficiently large degrees admits a bounded-above projective
resolution ([Stacks, Tag 0646] (2)).

## Main results

* `ProjectiveResolutionLemma.exists_epiResData`: a complex strictly bounded above by `a`
  admits an `EpiResData`.
* `ProjectiveResolutionLemma.epiResData_to_resolution`: an `EpiResData` yields a projective
  resolution with epimorphic components.
* `ProjectiveResolutionLemma.exists_epiResolution_of_strictlyLE`: a complex strictly bounded
  above by `a` has a projective resolution bounded above by `a` with epimorphic components.
* `ProjectiveResolutionLemma.exists_strictlyLE_quasiIso`: a complex with cohomology vanishing
  in large degrees is quasi-isomorphic to a strictly bounded-above complex.
* `ProjectiveResolutionLemma.statement2`: a complex with cohomology vanishing in large degrees
  has a bounded-above projective resolution.

## References

* [Stacks, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
-/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ProjectiveResolutionLemma

variable {C : Type*} [Category C] [Abelian C]

/-- **Existence of the resolution data** (Obligation 2+3, the descending recursion).

This is the heart of Stacks 0646(3): by descending induction on the degree, using
a projective cover of the relevant pullback at each step and maintaining the
"epimorphism onto cocycles" invariant, one builds an `EpiResData K a`. The two
genuinely mathematical facts (the induced cocycle map `β^m` is epi, §2.1) are
discharged inside `ExistsEpiResDataAux.step`; the assembly of the resulting tower
into the total ℤ-indexed family is handled by the `*_fun` lemmas. -/
theorem exists_epiResData [EnoughProjectives C] (a : ℤ)
    (K : CochainComplex C ℤ) (hK : K.IsStrictlyLE a) :
    Nonempty (EpiResData K a) :=
  ⟨{ X := ExistsEpiResDataAux.Xfun K a hK
     proj := fun n => (ExistsEpiResDataAux.tw K a hK n).hP
     zero := fun n hn => ExistsEpiResDataAux.tw_P_isZero K a hK n hn
     d := ExistsEpiResDataAux.dfun K a hK
     dd := ExistsEpiResDataAux.dd_fun K a hK
     α := ExistsEpiResDataAux.αfun K a hK
     comm := ExistsEpiResDataAux.comm_fun K a hK
     epiα := fun n => (ExistsEpiResDataAux.tw K a hK n).epiα
     ZP := ExistsEpiResDataAux.ZPfun K a hK
     jZP := ExistsEpiResDataAux.jZPfun K a hK
     hjZP := ExistsEpiResDataAux.hjZP_fun K a hK
     hjd := ExistsEpiResDataAux.hjd_fun K a hK
     ker := fun n => ExistsEpiResDataAux.ker_fun K a hK n
     αZ := ExistsEpiResDataAux.αZfun K a hK
     epiαZ := ExistsEpiResDataAux.epiαZ_fun K a hK
     hαZ := ExistsEpiResDataAux.hαZ_fun K a hK
     dbarP := ExistsEpiResDataAux.dbarPfun K a hK
     hdbarP := ExistsEpiResDataAux.hdbarP_fun K a hK
     hdbarP_sq := ExistsEpiResDataAux.hdbarP_sq_fun K a hK
     epiToPb := ExistsEpiResDataAux.epiToPb_fun K a hK }⟩

set_option maxHeartbeats 1600000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 800000 in
/-- **Assembly + quasi-isomorphism** (Obligations 2(c) + 4).

Given an `EpiResData K a`, assemble the family into a `ProjectiveResolutionComplex`
whose structure morphism is a quasi-isomorphism with epi components. The complex is
built with `CochainComplex.of` (using `dd` for `d ≫ d = 0`); the chain map from
`comm`; `projective`/`boundedAbove` from `proj`/`zero`; and the quasi-iso from the
cohomology-comparison argument (§4): each `homologyMap α n` is iso because
`homologyπ` is epi and the cocycle map is epi (epi half) and `ker β = coboundaries`
(mono half), via `quasiIsoAt_iff_isIso_homologyMap` and `quasiIso_iff`. -/
theorem epiResData_to_resolution [EnoughProjectives C] (a : ℤ)
    (K : CochainComplex C ℤ) (D : EpiResData K a) :
    ∃ P : ProjectiveResolutionComplex K a, ∀ n : ℤ, Epi (P.α.f n) := by
  -- DEPENDS ON: building `CochainComplex.of D.X D.d D.dd`, the `HomologicalComplex.Hom`
  -- from `D.comm`, and the degreewise quasi-iso `IsIso (homologyMap α n)` from §4.
  -- SANITY CHECK PASSED: the statement is TRUE. The conclusion is an *existence*
  -- statement about K; and `EpiResData K a` silently encodes `K.IsStrictlyLE a`
  -- (for n>a, αⁿ : 0 ↠ Kⁿ epi out of a zero object forces Kⁿ = 0). The assembled
  -- map α : (CochainComplex.of D.X D.d D.dd) → K from D.comm has epi components and
  -- IS a quasi-iso (Stacks 0646(3)); building P honestly from D is the real work.
  -- WARNING: do NOT close this by invoking exists_epiResolution_of_strictlyLE — that
  -- calls epiResData_to_resolution (circular). Build P from D's components directly.
  --
  -- ASSEMBLY (steps 1–5) is done honestly below. The remaining `quasiIso` field is,
  -- however, NOT PROVABLE from the bare `EpiResData` fields. See the BLOCKED note at
  -- the open goal for the quasiIso below for a precise counterexample.
  let P : CochainComplex C ℤ := CochainComplex.of D.X D.d D.dd
  have hPX : ∀ n, P.X n = D.X n := fun n => rfl
  have hPd : ∀ n, P.d n (n+1) = D.d n := fun n => by
    simp only [P, CochainComplex.of_d]
  let α : P ⟶ K :=
    { f := fun n => D.α n
      comm' := by
        intro i j hij
        simp only [ComplexShape.up_Rel] at hij
        subst hij
        rw [hPd i]
        exact D.comm i }
  have hboundP : P.IsStrictlyLE a := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [hPX i]
    exact D.zero i hi
  refine ⟨{ complex := P
            projective := fun n => by rw [hPX n]; exact D.proj n
            boundedAbove := hboundP
            α := α
            quasiIso := ?_ }, ?_⟩
  · -- `QuasiIso α`, via the cohomology comparison.
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    -- Re-index so the previous degree is on the nose: write `n = m + 1`.
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    -- `P.d (m+1) ((m+1)+1) = D.d (m+1)`.
    have hPdn : P.d (m + 1) (m + 1 + 1) = D.d (m + 1) := hPd (m + 1)
    have hαfn : α.f (m + 1) = D.α (m + 1) := rfl
    -- Build the iso `eZ : D.ZP (m+1) ≅ P.cycles (m+1)` (both ker of `P.d (m+1) (m+1+1) = D.d
    -- (m+1)`).
    have hjZP_d : D.jZP (m + 1) ≫ P.d (m + 1) (m + 1 + 1) = 0 := by rw [hPdn]; exact D.hjd (m + 1)
    let fwd : D.ZP (m + 1) ⟶ P.cycles (m + 1) :=
      P.liftCycles (D.jZP (m + 1)) (m + 1 + 1) (by simp) hjZP_d
    have hfwd_i : fwd ≫ P.iCycles (m + 1) = D.jZP (m + 1) := P.liftCycles_i _ _ _ _
    have hiCycles_d : P.iCycles (m + 1) ≫ D.d (m + 1) = 0 := by
      rw [← hPdn]; exact P.iCycles_d (m + 1) (m + 1 + 1)
    let bwd : P.cycles (m + 1) ⟶ D.ZP (m + 1) := (D.ker (m + 1) (P.iCycles (m + 1))
        hiCycles_d).choose
    have hbwd_j : bwd ≫ D.jZP (m + 1) = P.iCycles (m + 1) :=
      (D.ker (m + 1) (P.iCycles (m + 1)) hiCycles_d).choose_spec.1
    have : Mono (D.jZP (m + 1)) := D.hjZP (m + 1)
    have hfb : fwd ≫ bwd = 𝟙 _ := by
      rw [← cancel_mono (D.jZP (m + 1)), Category.assoc, hbwd_j, hfwd_i, Category.id_comp]
    have hbf : bwd ≫ fwd = 𝟙 _ := by
      rw [← cancel_mono (P.iCycles (m + 1)), Category.assoc, hfwd_i, hbwd_j, Category.id_comp]
    let eZ : D.ZP (m + 1) ≅ P.cycles (m + 1) := ⟨fwd, bwd, hfb, hbf⟩
    -- Identify `cyclesMap α (m+1)`: `eZ.hom ≫ cyclesMap α (m+1) = D.αZ (m+1)`.
    have hcm : eZ.hom ≫ HomologicalComplex.cyclesMap α (m + 1) = D.αZ (m + 1) := by
      rw [← cancel_mono (K.iCycles (m + 1)), Category.assoc, HomologicalComplex.cyclesMap_i,
        ← Category.assoc]
      show (fwd ≫ P.iCycles (m + 1)) ≫ α.f (m + 1) = _
      rw [hfwd_i, hαfn, D.hαZ (m + 1)]
    -- `Epi (cyclesMap α (m+1))` from `D.epiαZ`.
    have hepiCM : Epi (HomologicalComplex.cyclesMap α (m + 1)) :=
      have := D.epiαZ (m + 1)
      epi_of_epi_fac hcm
    have hnat := HomologicalComplex.homologyπ_naturality α (m + 1)
    -- EPI half (informal §2a): `homologyMap α (m+1)` is epi.
    have hepiHM : Epi (HomologicalComplex.homologyMap α (m + 1)) := epi_of_epi_fac hnat
    -- MONO half (informal §2b).
    have hmonoHM : Mono (HomologicalComplex.homologyMap α (m + 1)) := by
      apply CategoryTheory.Abelian.Pseudoelement.mono_of_zero_of_map_zero
      intro η hη
      -- Lift η along the epi `P.homologyπ (m+1)`.
      obtain ⟨w, hw⟩ := Pseudoelement.pseudo_surjective_of_epi (P.homologyπ (m + 1)) η
      -- `K.homologyπ (m+1)` kills `cyclesMap α (m+1)` applied to `w`.
      have hker : Pseudoelement.pseudoApply (K.homologyπ (m + 1))
          (Pseudoelement.pseudoApply (HomologicalComplex.cyclesMap α (m + 1)) w) = 0 := by
        rw [← Pseudoelement.comp_apply, ← hnat, Pseudoelement.comp_apply, hw, hη]
      -- Exactness `K.X m → K.cycles (m+1) → K.homology (m+1)`.
      have hexact : (ShortComplex.mk (K.toCycles m (m + 1)) (K.homologyπ (m + 1))
          (HomologicalComplex.toCycles_comp_homologyπ K m (m + 1))).Exact := by
        apply ShortComplex.exact_of_g_is_cokernel
        exact K.homologyIsCokernel m (m + 1) (by simp)
      obtain ⟨k₀, hk₀⟩ := Pseudoelement.pseudo_exact_of_exact hexact
        (Pseudoelement.pseudoApply (HomologicalComplex.cyclesMap α (m + 1)) w) hker
      -- Transport `w` to `D.ZP (m+1)` via `eZ.inv`.
      set wZ := Pseudoelement.pseudoApply eZ.inv w with hwZ
      have hαZwZ : Pseudoelement.pseudoApply (D.αZ (m + 1)) wZ
          = Pseudoelement.pseudoApply (HomologicalComplex.cyclesMap α (m + 1)) w := by
        rw [hwZ, ← Pseudoelement.comp_apply]
        have hinvαZ : eZ.inv ≫ D.αZ (m + 1) = HomologicalComplex.cyclesMap α (m + 1) := by
          rw [← hcm, ← Category.assoc, eZ.inv_hom_id, Category.id_comp]
        rw [hinvαZ]
      -- The pair `(wZ, k₀)` lifts into the pullback of `D.αZ (m+1)` and `K.toCycles m (m+1)`.
      have hpair : Pseudoelement.pseudoApply (D.αZ (m + 1)) wZ
          = Pseudoelement.pseudoApply (K.toCycles m (m + 1)) k₀ := by
        rw [hαZwZ]; exact hk₀.symm
      obtain ⟨s, hs₁, hs₂⟩ := Pseudoelement.pseudo_pullback hpair
      -- Lemma 1': lift `s` along the epi `epiToPb m` (no reindexing needed now).
      have hepiPb : Epi (pullback.lift (D.dbarP m) (D.α m) (D.hdbarP_sq m) :
          D.X m ⟶ pullback (D.αZ (m + 1)) (K.toCycles m (m + 1))) := D.epiToPb m
      obtain ⟨x, hx⟩ := Pseudoelement.pseudo_surjective_of_epi
        (pullback.lift (D.dbarP m) (D.α m) (D.hdbarP_sq m) :
          D.X m ⟶ pullback (D.αZ (m + 1)) (K.toCycles m (m + 1))) s
      -- `dbarP m` applied to `x` equals `wZ`.
      have hdbarx : Pseudoelement.pseudoApply (D.dbarP m) x = wZ := by
        have h1 : Pseudoelement.pseudoApply (pullback.fst (D.αZ (m + 1)) (K.toCycles m (m + 1)))
            (Pseudoelement.pseudoApply (pullback.lift (D.dbarP m) (D.α m) (D.hdbarP_sq m)) x)
            = Pseudoelement.pseudoApply (D.dbarP m) x := by
          rw [← Pseudoelement.comp_apply, pullback.lift_fst]
        rw [hx] at h1
        rw [← h1, hs₁]
      -- Key: `D.dbarP m ≫ eZ.hom = P.toCycles m (m+1)`, hence `w` is a coboundary.
      have hdbar_toCycles : D.dbarP m ≫ eZ.hom = P.toCycles m (m + 1) := by
        rw [← cancel_mono (P.iCycles (m + 1)), Category.assoc]
        show D.dbarP m ≫ fwd ≫ P.iCycles (m + 1) = _
        rw [hfwd_i, HomologicalComplex.toCycles_i, hPd m]
        exact (D.hdbarP m)
      -- Conclude `η = 0`: `pseudoApply (P.homologyπ (m+1)) w = 0`.
      have hzero : D.dbarP m ≫ eZ.hom ≫ P.homologyπ (m + 1) = 0 := by
        rw [← Category.assoc, hdbar_toCycles, HomologicalComplex.toCycles_comp_homologyπ]
      rw [← hw]
      calc Pseudoelement.pseudoApply (P.homologyπ (m + 1)) w
          = Pseudoelement.pseudoApply (eZ.inv ≫ eZ.hom ≫ P.homologyπ (m + 1)) w := by
            rw [Iso.inv_hom_id_assoc]
        _ = Pseudoelement.pseudoApply (eZ.hom ≫ P.homologyπ (m + 1))
              (Pseudoelement.pseudoApply eZ.inv w) := by rw [Pseudoelement.comp_apply]
        _ = Pseudoelement.pseudoApply (eZ.hom ≫ P.homologyπ (m + 1))
              (Pseudoelement.pseudoApply (D.dbarP m) x) := by rw [← hwZ, hdbarx]
        _ = Pseudoelement.pseudoApply (D.dbarP m ≫ eZ.hom ≫ P.homologyπ (m + 1)) x := by
            simp only [Pseudoelement.comp_apply]
        _ = 0 := by rw [hzero, Pseudoelement.zero_apply]
    exact isIso_of_mono_of_epi _
  · intro n
    show Epi (D.α n)
    exact D.epiα n

/-- **Statement 3, packaged** (the core descending-induction construction).

This is the full content of Statement 3 stated as a standalone lemma; `statement3`
is this lemma. The construction is by descending induction on the degree, using
`lift_to_pullback` at each step. It is now reduced to `exists_epiResData` (the
recursion producing the per-degree data) and `epiResData_to_resolution` (assembly
into a complex with the quasi-isomorphism). -/
@[sga "4½ Etat_0 3.1.9" "Part 1, special case"]
theorem exists_epiResolution_of_strictlyLE [EnoughProjectives C] (a : ℤ)
    (K : CochainComplex C ℤ) (hK : K.IsStrictlyLE a) :
    ∃ P : ProjectiveResolutionComplex K a, ∀ n : ℤ, Epi (P.α.f n) := by
  obtain ⟨D⟩ := exists_epiResData a K hK
  exact epiResData_to_resolution a K D

/-- **Statement 3.**
Assume `A` has enough projectives. Let `K^•` be a complex with `K^n = 0` for
`n > a`. Then there exists a projective resolution `α : P^• → K^•` (Definition 4)
bounded above by `a` such that, additionally, each component `α^n : P^n → K^n` is
an epimorphism. -/
@[stacks 0646 "(3)",
  sga "4½ Etat_0 3.1.9" "Part 1, special case",
  sga "4½ Etat_0 3.2.3" "partial",
  sga "4½ Etat_0 4.2.3.1" "Corollary 1"]
alias statement3 := ProjectiveResolutionLemma.exists_epiResolution_of_strictlyLE

/-- **Truncation lemma** (Stacks 13.19.2 / Tag 0645), reduction engine for
Statement 2.

If `H^n(K^•) = 0` for all `n ≥ M`, then there is a complex `L^•` strictly bounded
above by some `N` (here `N = M`) together with a quasi-isomorphism `t : L^• → K^•`.
Take `L^•` to be the *canonical truncation* `τ_{≤ M} K` (the "stupid/canonical
truncation in cohomological degree `M`"): `L^n = K^n` for `n < M`, `L^M = ker d_K^M`
(the cocycles `Z^M`), and `L^n = 0` for `n > M`, with the inclusion as `t`. Since
`H^n(K) = 0` for `n ≥ M`, the inclusion `t` is an isomorphism on `H^n` for `n < M`
and both sides vanish for `n > M`; at `n = M`, `H^M(L) = Z^M / B^M` while
`H^M(K) = 0`, and the truncation is arranged (using `H^M(K)=0`, i.e. `Z^M = B^M`)
so that `t` is still a quasi-iso — the standard canonical truncation is a
quasi-isomorphism precisely in the range where cohomology is concerned. -/
theorem exists_strictlyLE_quasiIso [EnoughProjectives C] (K : CochainComplex C ℤ)
    (hK : ∃ M : ℤ, ∀ n : ℤ, M ≤ n → IsZero (K.homology n)) :
    ∃ (N : ℤ) (L : CochainComplex C ℤ) (_ : L.IsStrictlyLE N) (t : L ⟶ K),
      QuasiIso t := by
  -- PROOF SKETCH (canonical truncation, Tag 0645):
  -- Obtain `M` from `hK` with `H^n(K) = 0` for `n ≥ M`. Build the canonical
  -- truncation `L := τ_{≤ M} K`: `L^n = K^n` (n < M), `L^M = cocycles Z^M(K)`
  -- (= `K.cycles M`, the kernel of `d_K^M`), `L^n = 0` (n > M); differentials are
  -- those of `K` for `n < M-1`, the corestriction of `d_K^{M-1}` to `Z^M` at
  -- `n = M-1`, and `0` above. The inclusion `t : L ⟶ K` is `id` below `M`,
  -- `K.iCycles M : Z^M ↪ K^M` at `M`, and `0` above.
  --   * `L.IsStrictlyLE M`: immediate from `L^n = 0` for `n > M`
  --     (`CochainComplex.isStrictlyLE_iff`), so take `N := M`.
  --   * `QuasiIso t`: degreewise (`quasiIso_iff`). For `n < M`, `t` is an iso on
  --     objects in a neighbourhood of `n`, hence `QuasiIsoAt`. At `n = M` and
  --     `n > M`, `H^n(K) = 0` (hypothesis) and `H^n(L) = 0` (since `L^M = Z^M` is
  --     the cocycles and `L^{>M} = 0`, the truncation is exact there), so the
  --     comparison is `0 → 0`, an iso. This is the standard fact that the
  --     canonical truncation map is a quasi-isomorphism.
  -- Mathlib: `K.cycles`, `K.iCycles`, `CochainComplex.of`, the
  -- `HomologicalComplex.Hom` constructor, `quasiIso_iff`,
  -- `exactAt_iff_isZero_homology`. The ℤ-indexed canonical-truncation functor is
  -- not pre-packaged in this snapshot, so `L` and `t` are built by hand.
  -- SANITY CHECK PASSED (TRUE: the canonical truncation `τ_{≤M} K → K` is a
  -- quasi-iso; at degree `M` it induces the identity `H^M(L) = Z^M/B^M = H^M(K)`
  -- regardless of vanishing, and the hypothesis `H^n(K)=0` for `n ≥ M` is even
  -- stronger than the `n > M` needed. Only an upper bound on `L` is asked, so
  -- nonzero homology in negative degrees is irrelevant).
  obtain ⟨M, hM⟩ := hK
  refine ⟨M, K.truncLE M, inferInstance, K.ιTruncLE M, ?_⟩
  rw [quasiIso_iff]
  intro q
  rcases le_or_gt q M with hq | hq
  · exact K.quasiIsoAt_ιTruncLE M q hq
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have hKzero : IsZero (K.homology q) := hM q (le_of_lt hq)
    have hLzero : IsZero ((K.truncLE M).homology q) := by
      have hX : IsZero ((K.truncLE M).X q) := CochainComplex.isZero_of_isStrictlyLE _ M q hq
      exact ShortComplex.isZero_homology_of_isZero_X₂ ((K.truncLE M).sc q) hX
    exact IsZero.isIso hLzero hKzero _

/-- **Statement 2.**
Assume `A` has enough projectives. Let `K^•` be a complex with `H^n(K^•) = 0`
for all `n ≫ 0`. Then `K^•` has a projective resolution in the sense of
Definition 4, i.e. there exists an upper bound `N` and a projective resolution
of `K^•` bounded above by `N`. -/
@[stacks 0646 "(2)", sga "4½ Etat_0 3.2.3" "partial", sga "4½ Etat_0 4.2.3.1" "Corollary 1"]
theorem statement2 [EnoughProjectives C] (K : CochainComplex C ℤ)
    (hK : ∃ M : ℤ, ∀ n : ℤ, M ≤ n → IsZero (K.homology n)) :
    ∃ N : ℤ, Nonempty (ProjectiveResolutionComplex K N) := by
  -- PROOF (reduction of Statement 2 to Statement 3 via the truncation lemma):
  -- Get a strictly-bounded-above `L` with quasi-iso `t : L ⟶ K` from
  -- `exists_strictlyLE_quasiIso`. Apply `statement3` to `L` to get a bounded-above
  -- projective resolution `P` of `L` (with `P.α : P.complex ⟶ L` a quasi-iso).
  -- Compose: `P.α ≫ t : P.complex ⟶ K` is a quasi-iso (QuasiIso closed under
  -- composition — instance inference, as in `statement1`), `P.complex` is bounded
  -- above by `N` and has projective components. Repackage as the required
  -- `ProjectiveResolutionComplex K N`.
  obtain ⟨N, L, hLstrict, t, htqi⟩ := exists_strictlyLE_quasiIso K hK
  obtain ⟨P, _⟩ := statement3 N L hLstrict
  refine ⟨N, ⟨?_⟩⟩
  refine
    { complex := P.complex
      projective := P.projective
      boundedAbove := P.boundedAbove
      α := P.α ≫ t
      quasiIso := ?_ }
  -- `QuasiIso (P.α ≫ t)` from `QuasiIso P.α` (`P.quasiIso`) and `QuasiIso t`.
  have := P.quasiIso
  have := htqi
  infer_instance

end ProjectiveResolutionLemma

end

end

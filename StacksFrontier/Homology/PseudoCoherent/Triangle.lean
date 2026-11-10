module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksFrontier.Algebra.Homology.PseudoCoherent
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

-- The brutal-truncation helpers in `truncGEaux` below (`ιcomp_comm`, `ιcomp_isIso`) rely on
-- `simp`/instance search seeing through the `extendXIso`/`restrictionXIso` composite, which
-- needs the pre-4.x defeq transparency behaviour. The pseudo-coherence substrate itself does
-- not need this option.
set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Let `R` be a ring and let `D(R)` denote the derived category of the
abelian category of `R`-modules. For an object `K` of `D(R)` and an integer `i`,
`H^i(K)` denotes the `i`-th cohomology `R`-module of `K`, and for a morphism
`α : E ⟶ K` in `D(R)`, `H^i(α)` denotes the induced map on `i`-th cohomology.

A complex `E` of `R`-modules is a *bounded complex of finite free `R`-modules*
if each term `E^i` is a finite free `R`-module and `E^i = 0` for all but finitely
many `i`.

Definition 1 (`m`-pseudo-coherence; Stacks 064Q (1)). Let `m ∈ ℤ`. An object `K`
of `D(R)` is `m`-pseudo-coherent if there exists a bounded complex `E` of finite
free `R`-modules and a morphism `α : E ⟶ K` in `D(R)` such that `H^i(α)` is an
isomorphism for all `i > m` and `H^m(α)` is surjective.

Definition 2 (Distinguished triangle in `D(R)`). A distinguished triangle in
`D(R)` is the data of objects `K, L, M` together with morphisms `f : K ⟶ L`,
`g : L ⟶ M`, `h : M ⟶ K[1]` forming a distinguished triangle for the triangulated
structure on `D(R)`.

# Main Statement(s) (Stacks 064R, Lemma 15.66.2)

Let `R` be a ring, let `m ∈ ℤ`, and let `(K, L, M, f, g, h)` be a distinguished
triangle in `D(R)`.

(1) If `K` is `(m+1)`-pseudo-coherent and `L` is `m`-pseudo-coherent, then `M` is
    `m`-pseudo-coherent.
(2) If `K` and `M` are both `m`-pseudo-coherent, then `L` is `m`-pseudo-coherent.
(3) If `L` is `(m+1)`-pseudo-coherent and `M` is `m`-pseudo-coherent, then `K` is
    `(m+1)`-pseudo-coherent.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u v

variable {R : Type u} [Ring R]

/-! ### Shared infrastructure

`m`-pseudo-coherence and its bookkeeping live in `StacksDraft.PseudoCoherence`,
which is universe-polymorphic in both the ring and the module universe; this file
uses them at `ModuleCat.{v} R` over a ring `R : Type u`, with independent universes.
From there we take `IsFiniteFree`,
`IsBoundedFiniteFree` and `IsBoundedFiniteFree.shift`; `IsPseudoCoherentFrom`
(Stacks 064Q (1)) with `IsPseudoCoherentFrom.shift` and
`IsPseudoCoherentFrom.ofIso`; and the functor-level bookkeeping
`epi_map_iff_of_natIso`, `homologyFunctorShiftIso`,
`isIso_homologyFunctor_map_shift_iff` and `epi_homologyFunctor_map_shift_iff`.
`H^i` on `D(R)` is `DerivedCategory.homologyFunctor (ModuleCat.{v} R) i`. -/

/-! ### Decomposition of Statement (1)

Statement (1) is the analytic core (Stacks 064R(1)). We follow the Stacks proof:
choose bounded-finite-free approximations `α : Q(P) ⟶ K` (iso on `H^i` for
`i > m+1`, epi on `H^{m+1}`) and `β : Q(E) ⟶ L` (iso on `H^i` for `i > m`, epi on
`H^m`). The proof breaks into three independent pieces:

* `exists_triangleMorphism_of_approx` — the **cone-of-finite-free construction**:
  build a morphism of distinguished triangles `S = (Q P, Q E, Q C) ⟶ T` extending
  `(α, β)`, where `C` is again a bounded complex of finite free modules. This is
  the genuine geometric content (lift the chain map `γ : P ⟶ E` over `f`, take its
  mapping cone, get a map of triangles).
* `isIso_homology_of_triangleMorphism` — the **five-lemma chase for iso** (Stacks
  05QB = `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`).
* `epi_homology_of_triangleMorphism` — the **five-lemma chase for epi** (Stacks
  05QA = `Abelian.epi_of_epi_of_epi_of_mono`).

The main theorem `isPseudoCoherent_of_distinguished_one` is then assembled below
from these three lemmas; the degree
bookkeeping (why `H^i(α)` is epi at `i = m+1` etc.) is discharged in that
assembly. -/

/-! #### CORRECTED decomposition of the cone construction (analytic kernel of (1))

⚠ The previous single sub-lemma `exists_triangleMorphism_of_approx` (which took
ARBITRARY `α, β` with no hypotheses) was **FALSE as stated** (it was
machine-checked to be false).
A triangle morphism `φ : S ⟶ T` must satisfy `comm₁`
(`S.mor₁ ≫ φ.hom₂ = φ.hom₁ ≫ T.mor₁`), which forces `α ≫ T.mor₁` to factor
through `β`; with arbitrary `β` (e.g. `β = 0` against the contractible triangle)
this is impossible. The connectivity hypotheses on `β` (and the projectivity of
`P`) are exactly what produce the chain-map lift making that square hold.

⚠⚠ SECOND CORRECTION: the first split's `exists_chainMap_lift` was
ALSO machine-checked FALSE because it dropped the SUPPORT constraint on `P`: with `P` allowed
in low degrees
the lift fails even though `β` is connective. The genuine Stacks 064R proof first
REPLACES the `(m+1)`-pseudo-coherence witness `(P, α)` of `K` by one whose complex
is concentrated in degrees `≥ m+1` (stupid/`truncGE` truncation; connectivity of
`α` is preserved).

We therefore use THREE sub-lemmas:
* `pseudoCoherent_witness_truncGE` (Sub-lemma C) — replace the `(m+1)`-pc witness
  `(P, α)` of `K` by `(P', α')` with `P'` bounded finite free concentrated in
  degrees `≥ m+1` (so `(Q P').IsGE (m+1)`), same connectivity. The step a naive
  argument omits.
* `exists_chainMap_lift` (Sub-lemmas A,B,D,E) — given the SUPPORT hypothesis
  `(Q P).IsGE (m+1)` + connectivity of `β` + K-projectivity of `P`, produce a
  genuine chain map `γ : P ⟶ E` with the D(R) square `Q γ ≫ β = α ≫ T.mor₁`.
* `exists_triangleMorphism_of_lift` (PROVEN) — given such a `γ` and the square,
  takes `C = cone γ` (bounded finite free), the cone triangle `S = (Q P, Q E, Q C)`
  (distinguished), and completes `(α, β)` to a triangle morphism `φ : S ⟶ T` (TR3).
The main theorem composes: truncate `(P,α) → (P',α')`, lift, then complete. -/

/-! ### Brutal (stupid) truncation helpers for Sub-lemma C

The stupid truncation `σ_{≥n}P` is realized as `(P.restriction e).extend e` for the
embedding `e = embeddingUpIntGE n : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)`,
together with the inclusion chain map `ιmap : σ_{≥n}P ⟶ P`. Its terms are `P.X i` for
`i ≥ n` and `0` below, so it stays bounded finite free and is strictly `GE n`. The
inclusion is iso on `H^i` for `i > n` (all three relevant terms agree) and epi on `H^n`
(cocycles surject onto homology). -/
namespace truncGEaux

/-- The brutal (stupid) truncation `σ_{≥n}P`. -/
@[ega "0 11.5.1" "special case", sga "4 XVII 1.1.16" "special case"]
noncomputable def Ptrunc (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{v} R) ℤ :=
  (P.restriction (ComplexShape.embeddingUpIntGE n)).extend (ComplexShape.embeddingUpIntGE n)

/-- For `n ≤ i`, the embedding `embeddingUpIntGE n` sends `(i - n).toNat` to `i`. -/
lemma emb_f_eq (n i : ℤ) (h : n ≤ i) :
    (ComplexShape.embeddingUpIntGE n).f (i - n).toNat = i := by
  rw [ComplexShape.embeddingUpIntGE_f]; omega

/-- Degreewise component of the inclusion `σ_{≥n}P ↪ P`. -/
noncomputable def ιcomp (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    (Ptrunc n P).X i ⟶ P.X i :=
  if h : n ≤ i then
    (HomologicalComplex.extendXIso (P.restriction (ComplexShape.embeddingUpIntGE n))
      (ComplexShape.embeddingUpIntGE n) (emb_f_eq n i h)).hom ≫
    (HomologicalComplex.restrictionXIso P (ComplexShape.embeddingUpIntGE n) (emb_f_eq n i h)).hom
  else 0

/-- Below degree `n`, the truncation `σ_{≥n}P` has zero terms. -/
private lemma isZero_Ptrunc_X (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ)
    (hi : i < n) : Limits.IsZero ((Ptrunc n P).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro k; rw [ComplexShape.embeddingUpIntGE_f]; omega

/-- The components `ιcomp n P` commute with the differentials of `σ_{≥n}P` and `P`. -/
lemma ιcomp_comm (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) :
    ιcomp n P i ≫ P.d i (i+1) = (Ptrunc n P).d i (i+1) ≫ ιcomp n P (i+1) := by
  by_cases hi : n ≤ i
  · have hi1 : n ≤ i + 1 := by omega
    rw [ιcomp, ιcomp, dite_eq_left hi, dite_eq_left hi1]
    change _ = ((P.restriction (ComplexShape.embeddingUpIntGE n)).extend
        (ComplexShape.embeddingUpIntGE n)).d i (i+1) ≫ _
    rw [HomologicalComplex.extend_d_eq _ (ComplexShape.embeddingUpIntGE n)
          (emb_f_eq n i hi) (emb_f_eq n (i+1) hi1),
        HomologicalComplex.restriction_d_eq _ (ComplexShape.embeddingUpIntGE n)
          (emb_f_eq n i hi) (emb_f_eq n (i+1) hi1)]
    simp
  · have : ιcomp n P i = 0 := by rw [ιcomp]; simp [hi]
    rw [this]
    rw [Limits.IsZero.eq_zero_of_src (isZero_Ptrunc_X n P i (by omega))
      ((Ptrunc n P).d i (i+1) ≫ ιcomp n P (i+1))]; simp

/-- The inclusion chain map `σ_{≥n}P ⟶ P`. -/
@[ega "0 11.5.1" "special case"]
noncomputable def ιmap (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) : Ptrunc n P ⟶ P where
  f i := ιcomp n P i
  comm' i j hij := by obtain rfl : i + 1 = j := hij; exact ιcomp_comm n P i

/-- For `n ≤ i`, the degree-`i` component of the inclusion `σ_{≥n}P ↪ P` is an isomorphism. -/
lemma ιcomp_isIso (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) (hi : n ≤ i) :
    IsIso (ιcomp n P i) := by rw [ιcomp, dite_eq_left hi]; infer_instance

/-- For `n ≤ i`, the truncation agrees with `P` in degree `i`. -/
@[ega "0 11.5.1" "partial", sga "4 XVII 1.1.16" "partial"]
noncomputable def PtruncXIso (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) (hi : n ≤ i) :
    (Ptrunc n P).X i ≅ P.X i :=
  (HomologicalComplex.extendXIso (P.restriction (ComplexShape.embeddingUpIntGE n))
    (ComplexShape.embeddingUpIntGE n) (emb_f_eq n i hi)) ≪≫
  (HomologicalComplex.restrictionXIso P (ComplexShape.embeddingUpIntGE n) (emb_f_eq n i hi))

/-- The truncation `σ_{≥n}P` is strictly concentrated in degrees `≥ n`. -/
@[sga "4 XVII 1.1.16" "partial"]
instance Ptrunc_strictlyGE (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    (Ptrunc n P).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply HomologicalComplex.isZero_extend_X
  intro k; rw [ComplexShape.embeddingUpIntGE_f]; omega

/-- If `P` is strictly concentrated in degrees `≤ b`, then so is `σ_{≥n}P`. -/
instance Ptrunc_strictlyLE (n b : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) [P.IsStrictlyLE b] :
    (Ptrunc n P).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hni : n ≤ i
  · exact (PtruncXIso n P i hni).isZero_iff.mpr (CochainComplex.isZero_of_isStrictlyLE P b i hi)
  · apply HomologicalComplex.isZero_extend_X
    intro k; rw [ComplexShape.embeddingUpIntGE_f]; omega

/-- If every term of `P` is finite free, then so is every term of `σ_{≥n}P`. -/
lemma Ptrunc_finiteFree (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hP : ∀ i, Module.Finite R (P.X i) ∧ Module.Free R (P.X i)) (i : ℤ) :
    Module.Finite R ((Ptrunc n P).X i) ∧ Module.Free R ((Ptrunc n P).X i) := by
  by_cases hi : n ≤ i
  · obtain ⟨hfin, hfree⟩ := hP i
    have el : (Ptrunc n P).X i ≃ₗ[R] (P.X i) := (PtruncXIso n P i hi).toLinearEquiv
    exact ⟨Module.Finite.equiv el.symm, Module.Free.of_equiv el.symm⟩
  · have hsub : Subsingleton ((Ptrunc n P).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (isZero_Ptrunc_X n P i (by omega))
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton R _⟩

/-- For `i > n`, the truncation inclusion is a quasi-isomorphism in degree `i`. -/
lemma isIso_homologyMap_ι (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) (hi : n < i) :
    IsIso (HomologicalComplex.homologyMap (ιmap n P) i) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff]
  have h1 : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).map (ιmap n P)).τ₁ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₁]
    change IsIso (ιcomp n P _)
    have he : (ComplexShape.up ℤ).prev i = i - 1 := by
      rw [ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (i-1) i by simp)]
    rw [he]; exact ιcomp_isIso n P (i-1) (by omega)
  have h2 : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).map (ιmap n P)).τ₂ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₂]
    exact ιcomp_isIso n P i (by omega)
  have h3 : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).map (ιmap n P)).τ₃ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₃]
    change IsIso (ιcomp n P _)
    have he : (ComplexShape.up ℤ).next i = i + 1 := by
      rw [ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel i (i+1) by simp)]
    rw [he]; exact ιcomp_isIso n P (i+1) (by omega)
  have : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) i).map (ιmap n P)) := ShortComplex.isIso_of_isIso _
  exact ShortComplex.quasiIso_of_isIso _

/-- At degree `n`, the truncation inclusion is epi on homology. -/
lemma epi_homologyMap_ι (n : ℤ) (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    Epi (HomologicalComplex.homologyMap (ιmap n P) n) := by
  change Epi (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) n).map (ιmap n P)))
  have h2 : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) n).map (ιmap n P)).τ₂ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₂]
    exact ιcomp_isIso n P n (by omega)
  have h3 : Mono ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) n).map (ιmap n P)).τ₃ := by
    rw [HomologicalComplex.shortComplexFunctor_map_τ₃]
    change Mono (ιcomp n P _)
    have he : (ComplexShape.up ℤ).next n = n + 1 := by
      rw [ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel n (n+1) by simp)]
    rw [he]
    have := ιcomp_isIso n P (n+1) (by omega)
    infer_instance
  have : IsIso (ShortComplex.cyclesMap ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} R)
      (ComplexShape.up ℤ) n).map (ιmap n P))) := ShortComplex.isIso_cyclesMap_of_isIso_of_mono _
  exact ShortComplex.epi_homologyMap_of_epi_cyclesMap _

/-- For `i > n`, the inclusion `σ_{≥n}P ⟶ P` induces an isomorphism on `H^i` in `D(R)`. -/
lemma isIso_cohomology_Qmap_ι [HasDerivedCategory (ModuleCat.{v} R)] (n : ℤ)
    (P : CochainComplex (ModuleCat.{v} R) ℤ) (i : ℤ) (hi : n < i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
      (DerivedCategory.Q.map (ιmap n P))) := by
  have e := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i
  have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (ιmap n P))
      = (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map (ιmap n P) :=
    rfl
  rw [h1, NatIso.isIso_map_iff e (ιmap n P), HomologicalComplex.homologyFunctor_map]
  exact isIso_homologyMap_ι n P i hi

/-- The inclusion `σ_{≥n}P ⟶ P` induces an epimorphism on `H^n` in `D(R)`. -/
lemma epi_cohomology_Qmap_ι [HasDerivedCategory (ModuleCat.{v} R)] (n : ℤ)
    (P : CochainComplex (ModuleCat.{v} R) ℤ) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
      (DerivedCategory.Q.map (ιmap n P))) := by
  have e := DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) n
  have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map
        (DerivedCategory.Q.map (ιmap n P))
      = (DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} R) n).map (ιmap n P) :=
    rfl
  rw [h1, epi_map_iff_of_natIso e (ιmap n P), HomologicalComplex.homologyFunctor_map]
  exact epi_homologyMap_ι n P

end truncGEaux

variable [HasDerivedCategory (ModuleCat.{v} R)]

/-- **Sub-lemma C (truncation/replacement of the witness for `K`; analogue of
Stacks 064T).** If `K` is `(m+1)`-pseudo-coherent — witnessed by a bounded-finite-
free `P` and `α : Q P ⟶ K` with `H^i(α)` iso for `i > m+1` and `H^{m+1}(α)` epi —
then there is ANOTHER bounded-finite-free witness `P'` (supported in degrees
`≥ m+1`, so `(Q P').IsGE (m+1)`) and `α' : Q P' ⟶ K` with the SAME connectivity.

INFORMAL ARGUMENT (Sub-lemma C). Take the stupid/brutal
truncation `P' := P.truncGE (m+1)` (kills terms in degrees `≤ m`, keeps `P^i` for
`i ≥ m+1`; bounded finite free since it only deletes terms). The inclusion-type
map `Q (P.truncGEπ …) : Q P ⟶ Q P'`… — more precisely, the canonical comparison
between `P` and its `truncGE` — induces `H^i` iso for `i > m+1` and epi at `m+1`
(its cone `≃ Q (σ^{≤m} P) ∈ D^{≤ m}`). Compose with `α` to get `α'` (in the right
direction) with `H^i(α')` iso for `i>m+1`, epi at `m+1`. And `P'` concentrated in
degrees `≥ m+1` ⇒ `(Q P').IsGE (m+1)` (`H^i(Q P') = 0` for `i ≤ m`).

⚠ DIRECTION CARE: `CochainComplex.truncGE` comes with `truncGEmap`/projection or
inclusion maps; check which direction Mathlib provides (`K ⟶ K.truncGE n` vs
`K.truncGE n ⟶ K`) and that it is a quasi-iso in degrees `> n` / `≥ n`. Probe
`#check` for `CochainComplex.truncGE`, its `π`/`ι`, `DerivedCategory` image, and
`isGE` of a `truncGE`. May instead use the `DerivedCategory` truncation
(`DerivedCategory.truncGE` / t-structure `truncation`) and its counit/unit, which
directly gives the `IsGE` object + a map with the homology behaviour.

FORMAL-PHASE HINTS: `CochainComplex.truncGE`, the SES `0 → σ^{≥n} → P → σ^{<n} → 0`
→ distinguished triangle, cohomology LES; `DerivedCategory.IsGE` / `isGE_iff`;
finite-freeness of `truncGE` (it deletes/keeps terms, so reuse `hP.finiteFree`,
`hP.lowerBound`, `hP.upperBound` with bounds clamped at `m+1`). Good place for a
further OR/AND decomposition (truncGE-is-BFF; truncGE-is-IsGE; truncGE-comparison-
connectivity). -/
theorem pseudoCoherent_witness_truncGE
    (m : ℤ) (K : DerivedCategory (ModuleCat.{v} R))
    {P : CochainComplex (ModuleCat.{v} R) ℤ} (hP : IsBoundedFiniteFree P)
    (α : (DerivedCategory.Q).obj P ⟶ K)
    (hαiso : ∀ i : ℤ, m + 1 < i →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α))
    (hαepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).map α)) :
    ∃ (P' : CochainComplex (ModuleCat.{v} R) ℤ) (_ : IsBoundedFiniteFree P')
      (_ : P'.IsStrictlyGE (m + 1))
      (α' : (DerivedCategory.Q).obj P' ⟶ K),
      (∀ i : ℤ, m + 1 < i →
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α')) ∧
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).map α') := by
  -- SANITY CHECK PASSED (Stacks 064R replacement step; explicit witness exists).
  -- ⚠ TOOLING CAVEAT FOUND BY SANITY CHECK: do NOT use Mathlib's
  -- `CochainComplex.truncGE` for P' — that is the CANONICAL/SMART truncation
  -- τ_{≥m+1}, whose degree-(m+1) term is `coker(d^m)`, finitely presented but
  -- generally NOT finite free, so it fails `IsBoundedFiniteFree P'`.
  -- USE THE STUPID/BRUTAL truncation: subcomplex σ_{≥m+1}P with P'.X i = P.X i for
  -- i ≥ m+1 and 0 below, inclusion ι : P' ↪ P (finite free terms preserved), then
  -- α' := Q(ι) ≫ α. H^i(ι) iso for i>m+1; epi at m+1 (H^{m+1}(P')=ker d^{m+1} ↠
  -- H^{m+1}(P)). P'.IsStrictlyGE (m+1) DEGREEWISE (the support the lift step needs).
  set P' := truncGEaux.Ptrunc (m + 1) P with hP'def
  obtain ⟨b, hb⟩ := hP.upperBound
  have : P.IsStrictlyLE b := hb
  have hP'bff : IsBoundedFiniteFree P' := by
    refine ⟨⟨m + 1, ?_⟩, ⟨b, ?_⟩, ?_⟩
    · exact truncGEaux.Ptrunc_strictlyGE (m + 1) P
    · exact truncGEaux.Ptrunc_strictlyLE (m + 1) b P
    · intro i
      exact truncGEaux.Ptrunc_finiteFree (m + 1) P (fun j => hP.finiteFree j) i
  have hP'GE : P'.IsStrictlyGE (m + 1) := truncGEaux.Ptrunc_strictlyGE (m + 1) P
  refine ⟨P', hP'bff, hP'GE, DerivedCategory.Q.map (truncGEaux.ιmap (m + 1) P) ≫ α, ?_, ?_⟩
  · intro i hi
    rw [Functor.map_comp]
    have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map
        (DerivedCategory.Q.map (truncGEaux.ιmap (m + 1) P))) :=
      truncGEaux.isIso_cohomology_Qmap_ι (m + 1) P i hi
    have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α) := hαiso i hi
    infer_instance
  · rw [Functor.map_comp]
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).map
        (DerivedCategory.Q.map (truncGEaux.ιmap (m + 1) P))) :=
      truncGEaux.epi_cohomology_Qmap_ι (m + 1) P
    have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (m + 1)).map α) := hαepi
    infer_instance

/-- Every morphism `Q P ⟶ Q Y` in `D(R)` from a K-projective `P` is `Q γ` for a chain map `γ`. -/
private theorem exists_chainMap_Q_map_eq {P Y : CochainComplex (ModuleCat.{v} R) ℤ}
    [P.IsKProjective] (g : (DerivedCategory.Q).obj P ⟶ (DerivedCategory.Q).obj Y) :
    ∃ γ : P ⟶ Y, (DerivedCategory.Q).map γ = g := by
  -- Transport the `Qh`-level bijection along `quotientCompQhIso : quotient ⋙ Qh ≅ Q`.
  have hbij := (Iso.homCongr
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app P)
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)).app Y)).bijective.comp
    (CochainComplex.IsKProjective.Qh_map_bijective P
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).obj Y))
  obtain ⟨φ, hφ⟩ := hbij.surjective g
  obtain ⟨γ, hγ'⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map_surjective φ
  refine ⟨γ, ?_⟩
  rw [← hφ, ← hγ']
  simp only [Function.comp_apply, Iso.homCongr_apply, Iso.app_hom, Iso.app_inv,
    DerivedCategory.quotientCompQhIso_hom_naturality, Iso.inv_hom_id_app_assoc]

/-- Hom-vanishing via STRICT support. For a K-projective complex `P` strictly
supported in degrees `≥ m+1` and any derived object `X` with `X.IsLE (m-1)`, every
morphism `f : Q P ⟶ X` in `D(R)` is zero. Proof: represent `X ≅ Q Y` with `Y`
strictly `LE (m-1)`; transport `f` to a chain map `γ : P ⟶ Y`; that chain map is
degreewise zero (each degree has a zero source `P.X i` or a zero target `Y.X i`),
hence null-homotopic, hence `Q γ = 0`. -/
theorem hom_eq_zero_of_isKProjective_isStrictlyGE_isLE
    (m : ℤ) {P : CochainComplex (ModuleCat.{v} R) ℤ}
    (hPkproj : P.IsKProjective)
    (hPstrictGE : P.IsStrictlyGE (m + 1))
    {X : DerivedCategory (ModuleCat.{v} R)} (hXLE : X.IsLE (m - 1))
    (f : (DerivedCategory.Q).obj P ⟶ X) :
    f = 0 := by
  have := hPstrictGE
  -- 1. Represent `X` by a strictly-LE(m-1) complex `Y`.
  obtain ⟨Y, hYLE, ⟨eX⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X (m - 1)
  have := hYLE
  -- Reduce to showing `f ≫ eX.hom = 0` (then cancel the iso).
  suffices hzero : f ≫ eX.hom = 0 by
    have := congrArg (· ≫ eX.inv) hzero
    simpa using this
  -- 2. `g := f ≫ eX.hom : Q P ⟶ Q Y` comes from a chain map `γ : P ⟶ Y`.
  set g : (DerivedCategory.Q).obj P ⟶ (DerivedCategory.Q).obj Y := f ≫ eX.hom with hg
  have hγ : ∃ γ : P ⟶ Y, (DerivedCategory.Q).map γ = g :=
    have := hPkproj
    exists_chainMap_Q_map_eq g
  obtain ⟨γ, hγ⟩ := hγ
  -- 3. `γ` is degreewise zero, hence null-homotopic, so `Q γ = 0`, so `g = 0`.
  have hγ0 : γ = 0 := by
    apply HomologicalComplex.hom_ext; intro i
    have hz : Limits.IsZero (Y.X i) ∨ Limits.IsZero (P.X i) := by
      rcases le_or_gt m i with h | h
      · left;  exact CochainComplex.isZero_of_isStrictlyLE Y (m - 1) i (by omega)
      · right; exact CochainComplex.isZero_of_isStrictlyGE P (m + 1) i (by omega)
    rcases hz with h | h
    · rw [h.eq_of_tgt (γ.f i) 0]; simp
    · rw [h.eq_of_src (γ.f i) 0]; simp
  -- `γ = 0` already gives this directly through `Q`; no `Qh` detour is needed.
  rw [← hγ, hγ0, Functor.map_zero]

/-- **Sub-lemma A0 (the chain-map lift).** Given a triangle `T`, bounded-finite-
free `P, E`, `α : Q P ⟶ T.obj₁`, `β : Q E ⟶ T.obj₂` with `β` "highly connective"
(iso on `H^i` for `i > m`, epi on `H^m`), AND — crucially — `P` STRICTLY supported
in degrees `≥ m+1` (`P.IsStrictlyGE (m+1)`, i.e. `P.X i = 0` for `i < m+1`), there
is a chain map `γ : P ⟶ E` with `Q γ ≫ β = α ≫ T.mor₁` in `D(R)`.

⚠ WHY `hPstrictGE` (STRICT, degreewise) AND NOT merely `(Q P).IsGE`.
The hypothesis-free form of this lemma was MACHINE-CHECKED FALSE
(`P = ℤ` in degree `-1`,
`m=0`, `β=0`, `T=contractibleTriangle`, `α=𝟙`). The HOMOLOGICAL
support `(Q P).IsGE (m+1)` alone is ALSO INSUFFICIENT: the obstruction lives in
`Hom_{D(R)}(Q P, Cone β)` with `Q P ∈ D^{≥m+1}`, `Cone β ∈ D^{≤m-1}` — the GE→LE
direction, which is genuinely `Ext^{≥2}` and NONzero for general source (e.g.
`R=k[x]/(x²)`); K-projectivity of `P` does NOT make this derived Hom vanish. The genuine
Stacks 064R proof first REPLACES the witness `P` by `σ_{≥m+1}P`, making `P^i = 0`
for `i < m+1` — i.e. STRICT support `P.IsStrictlyGE (m+1)`. That is supplied at the
call site by `pseudoCoherent_witness_truncGE`. Distinguishedness of `T` is NOT
needed for this lift step.

SANITY CHECK PASSED (strict-support version; no counterexample. Old cone2/cone3
witnesses excluded: P=ℤ@(-1) is NOT IsStrictlyGE 1; obstruction Hom(Q P,Cone β)
provably zero via degreewise-zero core. T-distinguishedness not needed.)

INFORMAL ARGUMENT (corrected):
(B) `Cone(β) ∈ D^{≤ m-1}`: β iso above `m`, epi at `m` ⇒ `H^i(Cone β) = 0` for
    `i ≥ m`, via the cohomology long exact sequence of the triangle of `β`.
(D) Lift through β: apply `Hom(Q P, -)` to the distinguished triangle
    `Q E --β--> L --ι--> Cone β --> (Q E)[1]`. The obstruction
    `(α ≫ T.mor₁) ≫ ι ∈ Hom(Q P, Cone β)` vanishes: represent `Cone β ≅ Q Y` with
    `Y.IsStrictlyLE (m-1)` (`exists_iso_Q_obj_of_isLE`); since `P` is K-projective,
    any `Q P ⟶ Q Y` is `Q γ'` for a chain map `γ' : P ⟶ Y`, and EVERY such chain map
    is DEGREEWISE ZERO (in each degree `i`, `P.X i = 0` for `i ≤ m` OR `Y.X i = 0`
    for `i ≥ m`), hence `Q γ' = 0`. So `α ≫ T.mor₁` lifts to `ψ : Q P ⟶ Q E`.
(E) Realize ψ by a chain map: `P` bounded finite free ⇒ K-projective ⇒
    `DerivedCategory.Q` bijective on `Hom(Q P, Q E)` so `ψ = Q γ`.

FORMAL-PHASE HINTS: cohomology LES (`DerivedCategory.HomologySequence`); the
distinguished triangle of `β` (`Pretriangulated.distinguished_cocone_triangle`);
the obstruction-vanishing via STRICT support — represent the LE object by a
strictly-LE complex (`DerivedCategory.exists_iso_Q_obj_of_isLE`), then every chain
map `P ⟶ Y` is `0` by `HomologicalComplex.hom_ext` + `isZero_of_isStrictlyGE P`/
`isZero_of_isStrictlyLE Y` (each degree has a zero source or zero target), so the
null-homotopy is `Homotopy.refl 0` — NO `Projective.factorThru`, NO comparison
theorem needed; `CochainComplex.isKProjective_of_projective` (needs
`[P.IsStrictlyLE d]` from `hP.upperBound`, `[∀ n, Projective (P.X n)]`),
`CochainComplex.IsKProjective.Qh_map_bijective` for the realization step. -/
theorem exists_chainMap_lift
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    {P E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : IsBoundedFiniteFree P)
    (hPstrictGE : P.IsStrictlyGE (m + 1))
    (α : (DerivedCategory.Q).obj P ⟶ T.obj₁)
    (β : (DerivedCategory.Q).obj E ⟶ T.obj₂)
    (hβiso : ∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map β))
    (hβepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map β)) :
    ∃ γ : P ⟶ E, (DerivedCategory.Q).map γ ≫ β = α ≫ T.mor₁ := by
  have := hPstrictGE
  -- `P` is K-projective (bounded complex of projective = free modules).
  have hPproj : ∀ n : ℤ, Projective (P.X n) := by
    intro n
    obtain ⟨_, hfree⟩ := hP.finiteFree n
    exact ModuleCat.projective_of_free (R := R) (M := P.X n) (Module.Free.chooseBasis R _)
  have hPkproj : P.IsKProjective := by
    obtain ⟨b, hb⟩ := hP.upperBound
    exact CochainComplex.isKProjective_of_projective P b
  -- Distinguished triangle of `β`:  `Q E --β--> L --ι--> Cone β --δ--> (Q E)[1]`.
  obtain ⟨Cβ, ι, δ, hdist⟩ := distinguished_cocone_triangle β
  -- (B) `Cone β` lies in `D^{≤ m-1}`.
  have hConeLE : Cβ.IsLE (m - 1) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    set Tr := Triangle.mk β ι δ with hTr
    have hβepi_i : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map β) := by
      rcases lt_or_eq_of_le (show m ≤ i by omega) with h | h
      · have := hβiso i h; infer_instance
      · rw [← h]; exact hβepi
    have hβmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map β) := by
      have := hβiso (i+1) (by omega); infer_instance
    have hιzero : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map ι = 0 := by
      have hcomp : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map β
          ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map ι = 0 := by
        rw [← Functor.map_comp,
          show β ≫ ι = Tr.mor₁ ≫ Tr.mor₂ from rfl, comp_distTriang_mor_zero₁₂ Tr hdist]
        simp
      exact (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map β)).mp
        (by rw [hcomp]; simp)
    have hδzero : DerivedCategory.HomologySequence.δ Tr i (i+1) rfl = 0 := by
      have hcomp : DerivedCategory.HomologySequence.δ Tr i (i+1) rfl
          ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map β = 0 :=
        (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceδ_comp Tr hdist i
            (i+1) rfl
      exact (cancel_mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map β)).mp
        (by rw [hcomp]; simp)
    exact (DerivedCategory.HomologySequence.exact₃ Tr hdist i (i+1) rfl).isZero_X₂ hιzero hδzero
  -- (A,D) The obstruction `(α ≫ T.mor₁) ≫ ι` vanishes via STRICT support.
  have hObstr : (α ≫ T.mor₁) ≫ ι = 0 := by
    rw [Category.assoc]
    exact hom_eq_zero_of_isKProjective_isStrictlyGE_isLE m hPkproj hPstrictGE hConeLE
      (α ≫ T.mor₁ ≫ ι)
  -- (D) Lift `α ≫ T.mor₁` through `β`.
  obtain ⟨ψ, hψ⟩ := Triangle.coyoneda_exact₂ _ hdist (α ≫ T.mor₁) hObstr
  -- (E) Realize `ψ : Q P ⟶ Q E` by a genuine chain map `γ : P ⟶ E`.
  have hψγ : ∃ γ : P ⟶ E, (DerivedCategory.Q).map γ = ψ :=
    have := hPkproj
    exists_chainMap_Q_map_eq ψ
  obtain ⟨γ, hγ⟩ := hψγ
  refine ⟨γ, ?_⟩
  rw [hγ]
  exact hψ.symm

/-- **Sub-lemma A (cone-of-finite-free construction, TR3 completion).** Given a
distinguished triangle `T`, bounded-finite-free `P, E`, `α : Q P ⟶ T.obj₁`,
`β : Q E ⟶ T.obj₂`, AND a chain map `γ : P ⟶ E` with the D(R) commuting square
`Q γ ≫ β = α ≫ T.mor₁`, there is a bounded-finite-free `C`, a distinguished
triangle `S = (Q P, Q E, Q C)`, and a triangle morphism `φ : S ⟶ T` with
`φ.hom₁ = α`, `φ.hom₂ = β` (up to the `eqToHom` identifications), `S.obj₃ = Q C`.

SANITY CHECK PASSED (with the commuting-square hypothesis the `comm₁` obstruction
that refuted the old hypothesis-free statement is satisfied by construction).

INFORMAL ARGUMENT. Take `C = cone(γ)`, the mapping cone of the chain map `γ`
(degree `i`: `P^{i+1} ⊕ E^i`). As a finite direct sum of finite free modules in
each degree and bounded (both `P`, `E` bounded), `C` is `IsBoundedFiniteFree`.
The cone triangle `P ⟶ E ⟶ C(γ) ⟶ P[1]` maps under `Q` to a distinguished
triangle `S = (Q P, Q E, Q C, Q γ, ·, ·)`. The pair `(α, β)` is a morphism of the
first two vertices commuting with the first map by the hypothesis `hsq`
(`S.mor₁ = Q γ`, so `S.mor₁ ≫ β = Q γ ≫ β = α ≫ T.mor₁`); by TR3
(`Pretriangulated.complete_distinguished_triangle_morphism`) it extends to a full
morphism of triangles `φ : S ⟶ T`.

FORMAL-PHASE HINTS: `CochainComplex.mappingCone γ` (needs
`[HomologicalComplex.HasHomotopyCofiber γ]`); the distinguished cone triangle of
`γ` in `D(R)` (search `CochainComplex.mappingConeCompTriangle`, mapping-cone
triangle is distinguished under `Q`, or `Triangle.mk` + `distinguished_cocone_triangle`);
`IsBoundedFiniteFree` of the cone from `hP, hE` (degreewise biproduct of finite
free; bounds shift by 1); TR3 `Pretriangulated.complete_distinguished_triangle_morphism`
to build `φ.hom₃`. This sub-lemma is a good place for a further OR-decomposition
(cone-is-BFF; cone-triangle-distinguished; TR3-completion). -/
theorem exists_triangleMorphism_of_lift
    (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    {P E : CochainComplex (ModuleCat.{v} R) ℤ}
    (hP : IsBoundedFiniteFree P) (hE : IsBoundedFiniteFree E)
    (α : (DerivedCategory.Q).obj P ⟶ T.obj₁)
    (β : (DerivedCategory.Q).obj E ⟶ T.obj₂)
    (γ : P ⟶ E)
    (hsq : (DerivedCategory.Q).map γ ≫ β = α ≫ T.mor₁) :
    ∃ (C : CochainComplex (ModuleCat.{v} R) ℤ) (_ : IsBoundedFiniteFree C)
      (S : Triangle (DerivedCategory (ModuleCat.{v} R))) (_ : S ∈ distinguishedTriangles)
      (φ : S ⟶ T) (hS1 : S.obj₁ = (DerivedCategory.Q).obj P)
      (hS2 : S.obj₂ = (DerivedCategory.Q).obj E),
      φ.hom₁ = (eqToHom hS1) ≫ α ∧ φ.hom₂ = (eqToHom hS2) ≫ β ∧
      S.obj₃ = (DerivedCategory.Q).obj C := by
  -- Take `C = mappingCone γ` and `S = Q.mapTriangle (mappingCone.triangle γ)`.
  refine ⟨CochainComplex.mappingCone γ, ?_, ?_⟩
  · -- `C` is a bounded complex of finite free modules.
    obtain ⟨a, ha⟩ := hP.lowerBound
    obtain ⟨b, hb⟩ := hE.lowerBound
    obtain ⟨a', ha'⟩ := hP.upperBound
    obtain ⟨b', hb'⟩ := hE.upperBound
    refine ⟨⟨min (a - 1) b, ?_⟩, ⟨max (a' - 1) b', ?_⟩, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨CochainComplex.isZero_of_isStrictlyGE P a (i + 1) (by omega),
        CochainComplex.isZero_of_isStrictlyGE E b i (by omega)⟩
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨CochainComplex.isZero_of_isStrictlyLE P a' (i + 1) (by omega),
        CochainComplex.isZero_of_isStrictlyLE E b' i (by omega)⟩
    · intro i
      obtain ⟨hPf, hPfr⟩ := hP.finiteFree (i + 1)
      obtain ⟨hEf, hEfr⟩ := hE.finiteFree i
      have e : (CochainComplex.mappingCone γ).X i ≅ (P.X (i + 1) ⊞ E.X i : ModuleCat R) :=
        HomologicalComplex.homotopyCofiber.XIsoBiprod γ i (i + 1) (by simp)
      have ebp : (P.X (i + 1) ⊞ E.X i : ModuleCat R) ≅
          ModuleCat.of R (↥(P.X (i + 1)) × ↥(E.X i)) := ModuleCat.biprodIsoProd _ _
      have el : (CochainComplex.mappingCone γ).X i ≃ₗ[R] (↥(P.X (i + 1)) × ↥(E.X i)) :=
        (e ≪≫ ebp).toLinearEquiv
      have hf : Module.Free R (↥(P.X (i + 1)) × ↥(E.X i)) := Module.Free.prod R _ _
      have hfin : Module.Finite R (↥(P.X (i + 1)) × ↥(E.X i)) := Module.Finite.prod
      exact ⟨Module.Finite.equiv el.symm, Module.Free.of_equiv el.symm⟩
  · -- The cone triangle, distinguished under `Q`, completed via TR3.
    set S : Triangle (DerivedCategory (ModuleCat.{v} R)) :=
      DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle γ) with hSdef
    have hS : S ∈ distinguishedTriangles :=
      DerivedCategory.mappingCone_triangle_distinguished γ
    have hS1 : S.obj₁ = (DerivedCategory.Q).obj P := rfl
    have hS2 : S.obj₂ = (DerivedCategory.Q).obj E := rfl
    have sq : S.mor₁ ≫ (eqToHom hS2 ≫ β) = (eqToHom hS1 ≫ α) ≫ T.mor₁ := by
      change (DerivedCategory.Q).map γ ≫ (𝟙 _ ≫ β) = (𝟙 _ ≫ α) ≫ T.mor₁
      rw [Category.id_comp, Category.id_comp]
      exact hsq
    obtain ⟨c, hc1, hc2⟩ := complete_distinguished_triangle_morphism S T hS hT
      (eqToHom hS1 ≫ α) (eqToHom hS2 ≫ β) sq
    exact ⟨S, hS, Triangle.homMk S T (eqToHom hS1 ≫ α) (eqToHom hS2 ≫ β) c sq hc1 hc2,
      hS1, hS2, rfl, rfl, rfl⟩

/-- **Sub-lemma B (five-lemma chase, iso; Stacks 05QB).** For a morphism of
distinguished triangles `φ : S ⟶ T`, if at degree `i` the map `H^i(φ.hom₁)` is
epi, `H^i(φ.hom₂)` is iso, `H^{i+1}(φ.hom₁)` is iso and `H^{i+1}(φ.hom₂)` is
mono, then `H^i(φ.hom₃)` is an isomorphism.

SANITY CHECK PASSED (this is the abstract five-lemma comparison; it is the
standard derived-category long-exact-sequence argument with the cited Mathlib
lemma, no counterexample).

INFORMAL ARGUMENT. The homology functor `H = H^0` on `D(R)` is a homological
functor for the triangulated structure (`DerivedCategory.homologyFunctor`); thus
each distinguished triangle yields a long exact cohomology sequence, and a
morphism of distinguished triangles yields a morphism (ladder) between the two
long exact sequences. Around degree `i` the ladder reads
`H^i(S₁) → H^i(S₂) → H^i(S₃) → H^{i+1}(S₁) → H^{i+1}(S₂)` over the corresponding
row for `T`, with vertical maps `H^i(φ₁), H^i(φ₂), H^i(φ₃), H^{i+1}(φ₁),
H^{i+1}(φ₂)`. Both rows are exact (homological functor + distinguished triangle).
Apply `CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono` (= 05QB) to
this 5-term ladder: with the outer maps epi / iso / iso / mono as in the
hypotheses, the middle map `H^i(φ₃) = H^i(φ.hom₃)` is an isomorphism.

FORMAL-PHASE HINTS: assemble the two `ComposableArrows _ 4` rows from the
homology long exact sequence of `S` and `T` (search Mathlib
`Triangulated`/`HomologySequence` / `homologyδ` API, e.g.
`DerivedCategory`'s `homologySequence_exact` analogues, or the general
`Pretriangulated` homological-functor long exact sequence), build the
`ComposableArrows` morphism from `φ` and naturality of `H`, then apply 05QB. -/
theorem isIso_homology_of_triangleMorphism
    {S T : Triangle (DerivedCategory (ModuleCat.{v} R))}
    (hS : S ∈ distinguishedTriangles) (hT : T ∈ distinguishedTriangles)
    (φ : S ⟶ T) (i : ℤ)
    (h1 : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₁))
    (h2 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂))
    (h1' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).map φ.hom₁))
    (h2' : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).map φ.hom₂)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃) := by
  -- Five lemma (05QB) on the morphism of long exact cohomology sequences.
  -- Build the two 5-term exact rows
  -- `H^i(·₁) → H^i(·₂) → H^i(·₃) → H^{i+1}(·₁) → H^{i+1}(·₂)` of `S` and `T` as
  -- `ComposableArrows _ 4`, the comparison morphism, then apply
  -- `Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`.
  let rowS : ComposableArrows (ModuleCat.{v} R) 4 :=
    ComposableArrows.mk₄
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map S.mor₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map S.mor₂)
      (DerivedCategory.HomologySequence.δ S i (i+1) rfl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map S.mor₁)
  let rowT : ComposableArrows (ModuleCat.{v} R) 4 :=
    ComposableArrows.mk₄
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T i (i+1) rfl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map T.mor₁)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₂ S hS i).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (DerivedCategory.HomologySequence.exact₃ S hS i (i+1) rfl).exact_toComposableArrows
        (DerivedCategory.HomologySequence.exact₁ S hS i (i+1) rfl).exact_toComposableArrows)
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₂ T hT i).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (DerivedCategory.HomologySequence.exact₃ T hT i (i+1) rfl).exact_toComposableArrows
        (DerivedCategory.HomologySequence.exact₁ T hT i (i+1) rfl).exact_toComposableArrows)
  let φ' : rowS ⟶ rowT :=
    ComposableArrows.homMk₄
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₂)
      (by
        change (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map S.mor₁
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₁
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
      (by
        change (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map S.mor₂
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
      (by
        change DerivedCategory.HomologySequence.δ S i (i+1) rfl
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₁
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃
            ≫ DerivedCategory.HomologySequence.δ T i (i+1) rfl
        exact (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceδ_naturality
          φ i (i+1) rfl |>.symm)
      (by
        change (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map S.mor₁
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₂
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₁
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono exS exT φ' h1 h2 h1' h2'

/-- **Sub-lemma C (five-lemma chase, epi; Stacks 05QA).** For a morphism of
distinguished triangles `φ : S ⟶ T`, if at degree `i` the map `H^i(φ.hom₂)` is
epi, `H^{i+1}(φ.hom₁)` is epi and `H^{i+1}(φ.hom₂)` is mono, then `H^i(φ.hom₃)`
is an epimorphism.

SANITY CHECK PASSED (abstract five-lemma comparison; standard, no counterexample).

INFORMAL ARGUMENT. As in Sub-lemma B, a morphism of distinguished triangles gives
a ladder between the two long exact cohomology sequences. Around degree `i` take
the 4-term exact piece
`H^i(S₂) → H^i(S₃) → H^{i+1}(S₁) → H^{i+1}(S₂)` over the corresponding row for
`T`, with vertical maps `H^i(φ₂), H^i(φ₃), H^{i+1}(φ₁), H^{i+1}(φ₂)`. Apply
`CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono` (= 05QA): with `H^i(φ₂)` epi,
`H^{i+1}(φ₁)` epi and `H^{i+1}(φ₂)` mono, the map `H^i(φ₃) = H^i(φ.hom₃)` is an
epimorphism.

FORMAL-PHASE HINTS: same long-exact-sequence machinery as Sub-lemma B; assemble
the two `ComposableArrows _ 3` rows and the comparison morphism, then apply 05QA. -/
theorem epi_homology_of_triangleMorphism
    {S T : Triangle (DerivedCategory (ModuleCat.{v} R))}
    (hS : S ∈ distinguishedTriangles) (hT : T ∈ distinguishedTriangles)
    (φ : S ⟶ T) (i : ℤ)
    (h2 : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂))
    (h1' : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).map φ.hom₁))
    (h2' : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i + 1)).map φ.hom₂)) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃) := by
  -- Five lemma (05QA) on the morphism of long exact cohomology sequences.
  -- Build the two 4-term exact rows `H^i(·₂) → H^i(·₃) → H^{i+1}(·₁) → H^{i+1}(·₂)`
  -- of `S` and `T` as `ComposableArrows _ 3`, the comparison morphism, then apply
  -- `Abelian.epi_of_epi_of_epi_of_mono`.
  let rowS : ComposableArrows (ModuleCat.{v} R) 3 :=
    ComposableArrows.mk₃
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map S.mor₂)
      (DerivedCategory.HomologySequence.δ S i (i+1) rfl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map S.mor₁)
  let rowT : ComposableArrows (ModuleCat.{v} R) 3 :=
    ComposableArrows.mk₃
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂)
      (DerivedCategory.HomologySequence.δ T i (i+1) rfl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map T.mor₁)
  have exS : rowS.Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₃ S hS i (i+1) rfl).exact_toComposableArrows
      (DerivedCategory.HomologySequence.exact₁ S hS i (i+1) rfl).exact_toComposableArrows
  have exT : rowT.Exact :=
    ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₃ T hT i (i+1) rfl).exact_toComposableArrows
      (DerivedCategory.HomologySequence.exact₁ T hT i (i+1) rfl).exact_toComposableArrows
  let φ' : rowS ⟶ rowT :=
    ComposableArrows.homMk₃
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₁)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₂)
      (by
        change (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map S.mor₂
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₂
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map T.mor₂
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
      (by
        change DerivedCategory.HomologySequence.δ S i (i+1) rfl
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₁
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃
            ≫ DerivedCategory.HomologySequence.δ T i (i+1) rfl
        exact (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).homologySequenceδ_naturality
          φ i (i+1) rfl |>.symm)
      (by
        change (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map S.mor₁
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₂
          = (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map φ.hom₁
            ≫ (DerivedCategory.homologyFunctor (ModuleCat.{v} R) (i+1)).map T.mor₁
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
  exact Abelian.epi_of_epi_of_epi_of_mono φ' exS exT h2 h1' h2'

omit [HasDerivedCategory (ModuleCat.{v} R)] in
/-- Helper: `Epi (f ≫ g)` when `f` is an isomorphism and `g` is an epimorphism.

This routes through the *clean* `IsIso.epi_of_iso`/`epi_comp` lemmas explicitly.
A bare `infer_instance` on such a goal instead synthesizes `Epi f` for the iso
factor `f` via the chain `Functor.map_epi`/`ExtremalEpi`/`EffectiveEpi`, which in
this environment can take a substantially less direct route. -/
theorem epi_isoComp_epi {X Y Z : ModuleCat.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsIso f] [Epi g] : Epi (f ≫ g) := by
  have : Epi f := IsIso.epi_of_iso f
  exact epi_comp f g

/-- **Statement (1).** If `K` is `(m+1)`-pseudo-coherent and `L` is
`m`-pseudo-coherent, and `(K, L, M, f, g, h)` is a distinguished triangle, then
`M` is `m`-pseudo-coherent.

Assembled from the three sub-lemmas above. The degree bookkeeping: with
`α : Q P ⟶ K` iso on `H^i` (`i > m+1`)/epi on `H^{m+1}` and `β : Q E ⟶ L` iso on
`H^i` (`i > m`)/epi on `H^m`, the cone `C` carries `μ = φ.hom₃ : Q C ⟶ M`. For
`i > m`: `H^i(α)` is epi (iso if `i > m+1`, epi if `i = m+1`), `H^i(β)` iso,
`H^{i+1}(α)` iso (since `i+1 > m+1`), `H^{i+1}(β)` mono (iso since `i+1 > m`), so
Sub-lemma B gives `H^i(μ)` iso. For `i = m`: `H^m(β)` epi, `H^{m+1}(α)` epi,
`H^{m+1}(β)` mono (iso since `m+1 > m`), so Sub-lemma C gives `H^m(μ)` epi. Hence
`(C, μ)` witnesses that `M` is `m`-pseudo-coherent. -/
@[stacks 064R "(1)", sga "6 I 2.6" "special case", sga "6 III 1.4" "special case"]
theorem isPseudoCoherent_of_distinguished_one
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    (hK : IsPseudoCoherentFrom T.obj₁ (m + 1))
    (hL : IsPseudoCoherentFrom T.obj₂ m) :
    IsPseudoCoherentFrom T.obj₃ m := by
  obtain ⟨P₀, hP₀, α₀, hα₀iso, hα₀epi⟩ := hK
  obtain ⟨E, hE, β, hβiso, hβepi⟩ := hL
  -- (C) Replace the (m+1)-pc witness (P₀, α₀) of K by (P, α) with P STRICTLY
  -- concentrated in degrees ≥ m+1 (P.IsStrictlyGE (m+1)); connectivity of α preserved.
  obtain ⟨P, hP, hPstrictGE, α, hαiso, hαepi⟩ :=
    pseudoCoherent_witness_truncGE m T.obj₁ hP₀ α₀ hα₀iso hα₀epi
  -- (A0) lift the chain map γ : P ⟶ E using STRICT support of P + connectivity of β
  obtain ⟨γ, hsq⟩ := exists_chainMap_lift m T hP hPstrictGE α β hβiso hβepi
  -- (A) cone of γ + TR3 completion to a triangle morphism φ : S ⟶ T
  obtain ⟨C, hC, S, hS, φ, hS1, hS2, hφ1, hφ2, hS3⟩ :=
    exists_triangleMorphism_of_lift T hT hP hE α β γ hsq
  -- The third component `μ = φ.hom₃ : Q C ⟶ M`, transported along `hS3`.
  refine ⟨C, hC, (eqToHom hS3.symm) ≫ φ.hom₃, ?_, ?_⟩
  · -- iso on `H^i` for `i > m`, via Sub-lemma B
    intro i hi
    rw [Functor.map_comp]
    have key : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map φ.hom₃) := by
      apply isIso_homology_of_triangleMorphism hS hT φ i
      · -- `H^i(α)` epi: iso if `i > m+1`, epi if `i = m+1`
        rw [hφ1, Functor.map_comp]
        rcases lt_or_eq_of_le (by omega : m + 1 ≤ i) with h | h
        · have := hαiso i (by omega)
          have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map α) :=
            IsIso.epi_of_iso _
          exact epi_isoComp_epi _ _
        · subst h; have := hαepi; exact epi_isoComp_epi _ _
      · rw [hφ2, Functor.map_comp]; have := hβiso i (by omega); infer_instance
      · rw [hφ1, Functor.map_comp]; have := hαiso (i+1) (by omega); infer_instance
      · rw [hφ2, Functor.map_comp]; have := hβiso (i+1) (by omega); infer_instance
    infer_instance
  · -- epi on `H^m`, via Sub-lemma C
    rw [Functor.map_comp]
    have key : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) m).map φ.hom₃) := by
      apply epi_homology_of_triangleMorphism hS hT φ m
      · rw [hφ2, Functor.map_comp]; have := hβepi; exact epi_isoComp_epi _ _
      · rw [hφ1, Functor.map_comp]; have := hαepi; exact epi_isoComp_epi _ _
      · rw [hφ2, Functor.map_comp]; have := hβiso (m+1) (by omega); infer_instance
    have := key
    exact epi_isoComp_epi _ _

/-- **Statement (2).** If `K` and `M` are both `m`-pseudo-coherent, and
`(K, L, M, f, g, h)` is a distinguished triangle, then `L` is
`m`-pseudo-coherent.

Reduction to (1): apply (1) to the (distinguished) inverse-rotated triangle
`(M⟦-1⟧, K, L)`, using that `M⟦-1⟧` is `(m+1)`-pseudo-coherent (shift of the
`m`-pseudo-coherent `M`) and `K` is `m`-pseudo-coherent. -/
@[stacks 064R "(2)",
  sga "6 I 2.5" "b), modules over a ring",
  sga "6 I 2.6" "special case",
  sga "6 III 1.4" "special case"]
theorem isPseudoCoherent_of_distinguished_two
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    (hK : IsPseudoCoherentFrom T.obj₁ m)
    (hM : IsPseudoCoherentFrom T.obj₃ m) :
    IsPseudoCoherentFrom T.obj₂ m := by
  -- `T.invRotate = (M⟦-1⟧, K, L)` is distinguished.
  have hrot := inv_rot_of_distTriang T hT
  -- `M⟦-1⟧` is `(m+1)`-pseudo-coherent.
  have hM' : IsPseudoCoherentFrom (T.obj₃⟦(-1 : ℤ)⟧) (m + 1) := by
    have := hM.shift (-1)
    simpa using this
  -- Apply (1).  Note `T.invRotate.obj₃ = T.obj₂ = L` definitionally.
  have := isPseudoCoherent_of_distinguished_one m T.invRotate hrot hM' hK
  simpa using this

/-- **Statement (3).** If `L` is `(m+1)`-pseudo-coherent and `M` is
`m`-pseudo-coherent, and `(K, L, M, f, g, h)` is a distinguished triangle, then
`K` is `(m+1)`-pseudo-coherent.

Reduction to (1): apply (1) to the (distinguished) rotated triangle
`(L, M, K⟦1⟧)`, concluding `K⟦1⟧` is `m`-pseudo-coherent; shifting back by `-1`
and transporting along the isomorphism `(K⟦1⟧)⟦-1⟧ ≅ K` yields that `K` is
`(m+1)`-pseudo-coherent. -/
@[stacks 064R "(3)", sga "6 I 2.6" "special case", sga "6 III 1.4" "special case"]
theorem isPseudoCoherent_of_distinguished_three
    (m : ℤ) (T : Triangle (DerivedCategory (ModuleCat.{v} R)))
    (hT : T ∈ distinguishedTriangles)
    (hL : IsPseudoCoherentFrom T.obj₂ (m + 1))
    (hM : IsPseudoCoherentFrom T.obj₃ m) :
    IsPseudoCoherentFrom T.obj₁ (m + 1) := by
  -- `T.rotate = (L, M, K⟦1⟧)` is distinguished.
  have hrot := rot_of_distTriang T hT
  -- Apply (1): obtain `K⟦1⟧` is `m`-pseudo-coherent.
  have hshift : IsPseudoCoherentFrom (T.obj₁⟦(1 : ℤ)⟧) m := by
    have := isPseudoCoherent_of_distinguished_one m T.rotate hrot hL hM
    simpa using this
  -- Shift back by `-1`: `(K⟦1⟧)⟦-1⟧` is `(m+1)`-pseudo-coherent.
  have hback : IsPseudoCoherentFrom ((T.obj₁⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧) (m + 1) := by
    have := hshift.shift (-1)
    simpa using this
  -- Transport along `(K⟦1⟧)⟦-1⟧ ≅ K`.
  exact hback.ofIso (shiftShiftNeg T.obj₁ 1)

end PseudoCoherence

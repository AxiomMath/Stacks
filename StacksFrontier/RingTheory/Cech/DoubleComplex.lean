module

public import StacksFrontier.RingTheory.Cech.Concatenation

/-!
# The Čech complex of a concatenated family as a total complex

Let `R` be a commutative ring, let `f : Fin r → R` and `g : Fin m → R` be two finite families of
elements of `R` and let `M` be an `R`-module. `StacksFrontier/RingTheory/Cech/Concatenation.lean`
identifies a single summand of the extended alternating Čech complex `C^•(f ++ g; M)` with a
summand of the iterated construction `C^•(f; C^•(g; M))`. This file assembles those summand
identifications into a degreewise identification indexed by *pairs* of index sets, and splits the
differential of `C^•(f ++ g; M)` into its two constituents under it.

In degree `n` the identification is

`C^n(f ++ g; M) ≅ ⨁_{#s + #t = n} (M_{∏_{j ∈ t} g j})_{∏_{i ∈ s} f i}`,

and the differential becomes `d_f + (-1)^{#s} d_g` on the summand indexed by `(s, t)`: the
Koszul differential of the total complex of the double complex `(p, q) ↦ C^p(f; C^q(g; M))`. The
two signs are the ones computed in `Cech.cechSign_castAdd` and `Cech.cechSign_natAdd`; nothing is
imposed here.

## Main definitions

* `Cech.splitIdx`, `Cech.joinIdx` — the two directions of `Cech.idxAppendEquiv`, spelled as
  reducible abbreviations.
* `Cech.pairModCongr` — the transport of an iterated summand along equalities of its two index
  sets.
* `Cech.pairTerm` — the degree-`n` term of the total complex, indexed by `Cech.PairIdx`.
* `Cech.pairTermEquiv` — the degreewise identification `C^n(f ++ g; M) ≅ Cech.pairTerm`.
* `Cech.pairIdxInsertLeft`, `Cech.pairIdxInsertRight` — inserting a new index into one of the two
  index sets of a pair.
* `Cech.pairDLeft`, `Cech.pairDRight`, `Cech.pairD` — the horizontal differential, the vertical
  differential with its Koszul sign, and their sum.
* `Cech.pairComplex` — the total complex itself, as a cochain complex of `R`-modules.
* `Cech.cechComplexAppendIso` — the identification of complexes
  `C^•(f ++ g; M) ≅ Cech.pairComplex`.

## Main results

* `Cech.compl_joinParts`, `Cech.sum_compl_joinParts` — the complement of an assembled index set is
  assembled from the two complements, so a sum over it splits into a sum over the first block plus
  a sum over the second. This is what turns the single sum over the complement in
  `Cech.cechD_lof` into a horizontal part plus a vertical part.
* `Cech.appendModEquiv_joinParts` — **the two spellings of a summand identification agree**: at
  `u = Cech.joinParts s t` the index-set-primary `Cech.appendModEquiv` is the pair-primary
  `Cech.pairModEquiv` followed by the transport `Cech.pairModCongr`.
* `Cech.pairTermEquiv_lof`, `Cech.pairTermEquiv_lof_join` — the degreewise identification acts
  summandwise, in the index-set-primary and in the pair-primary spelling.
* `Cech.pairTermEquiv_lof_insert_castAdd`, `Cech.pairTermEquiv_lof_insert_natAdd` — one summand of
  the image of a generator under the differential, in each of the two blocks.
* `Cech.pairTermEquiv_cechD_lof`, `Cech.pairTermEquiv_comp_cechD` — **the differential splits**:
  on the summand indexed by `(s, t)` the differential of `C^•(f ++ g; M)` is `d_f + (-1)^{#s} d_g`.
* `Cech.pairD_comp_pairD` — the differential of the total complex squares to zero, transported
  from `Cech.cechD_comp_cechD`.

## Implementation notes

The index type of the direct sum is kept as `Cech.PairIdx`, a subtype of pairs of index sets,
rather than being presented as `⨁_{p + q = n} ⨁_{#s = p} ⨁_{#t = q}`; the regrouping into a
bigraded object is a separate step.

`Cech.splitIdx` and `Cech.joinIdx` exist because `Cech.idxAppendEquiv` is a bundled `Equiv` and
`Equiv.symm` is semireducible, so `((Cech.idxAppendEquiv n).symm w).1` does not reduce to
`Cech.joinParts w.1.1 w.1.2` at the `implicit` transparency at which `rw` checks
type-correctness. Every term of a direct sum over `Cech.PairIdx` has a type depending on the
index, so a statement spelled with `Equiv.symm` is type-correct only at `default` transparency and
is rejected by `rw` — the same obstruction documented in
`StacksFrontier/RingTheory/Cech/Reindex.lean`, with the same remedy. The two abbreviations are the
components of `Cech.idxAppendEquiv`, which is recorded by
`Cech.idxAppendEquiv_apply` and `Cech.idxAppendEquiv_symm_apply_eq`.

The round-trip identities of `Cech.pairTermEquiv` are exactly where `DirectSum.lof` has to be
transported along a `Subtype.ext`, because splitting an index set is a bijection only
propositionally. Both transports are isolated in `Cech.lof_splitCongr` and
`Cech.lof_pairCongr`, each proved by substituting the equality of index sets, after which
`Cech.pairModCongr` is the identity by construction.

## References

* [Stacks Project, Tag 012Z](https://stacks.math.columbia.edu/tag/012Z), the total complex of a
  double complex and its sign convention.
* [Stacks Project, Tag 0ECP](https://stacks.math.columbia.edu/tag/0ECP), the subadditivity of
  cohomological dimension, for which this is the complex-level input.
-/

@[expose] public section

open Finset

namespace Cech

universe u v

variable {r m : ℕ}

/-! ### The complement of an assembled index set -/

/-- **The complement of an assembled index set is assembled from the two complements.** This is
what splits the sum over `uᶜ` in `Cech.cechD_lof` into a sum over the first block and a sum over
the second. -/
theorem compl_joinParts (s : Finset (Fin r)) (t : Finset (Fin m)) :
    (joinParts s t)ᶜ = joinParts sᶜ tᶜ := by
  ext x
  induction x using Fin.addCases with
  | left i => rw [Finset.mem_compl, mem_joinParts_castAdd, mem_joinParts_castAdd, Finset.mem_compl]
  | right j => rw [Finset.mem_compl, mem_joinParts_natAdd, mem_joinParts_natAdd, Finset.mem_compl]

/-! ### The two directions of the reindexing, reducibly -/

/-- The pair of index sets attached to an index set of the concatenated family. This is the
forward direction of `Cech.idxAppendEquiv`, as a reducible abbreviation. -/
abbrev splitIdx (n : ℕ) (u : ExtendedAlternatingCech.Idx (r + m) n) : PairIdx r m n :=
  ⟨(leftPart u.1, rightPart u.1), (card_leftPart_add_card_rightPart u.1).trans u.2⟩

/-- The index set of the concatenated family attached to a pair of index sets. This is the inverse
direction of `Cech.idxAppendEquiv`, as a reducible abbreviation. -/
abbrev joinIdx (n : ℕ) (w : PairIdx r m n) : ExtendedAlternatingCech.Idx (r + m) n :=
  ⟨joinParts w.1.1 w.1.2, (card_joinParts w.1.1 w.1.2).trans w.2⟩

/-- `Cech.splitIdx` is the forward direction of `Cech.idxAppendEquiv`. -/
theorem idxAppendEquiv_apply (n : ℕ) (u : ExtendedAlternatingCech.Idx (r + m) n) :
    idxAppendEquiv n u = splitIdx n u := rfl

/-- `Cech.joinIdx` is the inverse direction of `Cech.idxAppendEquiv`. -/
theorem idxAppendEquiv_symm_apply_eq (n : ℕ) (w : PairIdx r m n) :
    (idxAppendEquiv n).symm w = joinIdx n w := rfl

/-- Assembling the two parts of an index set recovers it. -/
theorem joinIdx_splitIdx (n : ℕ) (u : ExtendedAlternatingCech.Idx (r + m) n) :
    joinIdx n (splitIdx n u) = u :=
  Subtype.ext (joinParts_leftPart_rightPart u.1)

/-- Splitting an assembled index set recovers the pair. -/
theorem splitIdx_joinIdx (n : ℕ) (w : PairIdx r m n) : splitIdx n (joinIdx n w) = w :=
  Subtype.ext (Prod.ext (leftPart_joinParts w.1.1 w.1.2) (rightPart_joinParts w.1.1 w.1.2))

variable {R : Type u} [CommRing R]

variable (M : Type v) [AddCommGroup M] [Module R M]

/-! ### Transporting an iterated summand -/

/-- **The transport of an iterated summand along equalities of its two index sets.** The summand
`(M_{∏_t g})_{∏_s f}` depends on the two index sets `s` and `t`, so equal index sets give equal —
but not definitionally equal — summands; this is the resulting identification. -/
noncomputable def pairModCongr (f : Fin r → R) (g : Fin m → R) {s s' : Finset (Fin r)}
    (h : s = s') {t t' : Finset (Fin m)} (h' : t = t') :
    cechMod f (cechMod g M t) s ≃ₗ[R] cechMod f (cechMod g M t') s' := by
  subst h; subst h'; exact LinearEquiv.refl R _

/-- The transport of an iterated summand fixes the canonical generator. -/
@[simp] theorem pairModCongr_mk_mk_one (f : Fin r → R) (g : Fin m → R) {s s' : Finset (Fin r)}
    (h : s = s') {t t' : Finset (Fin m)} (h' : t = t') (x : M) :
    pairModCongr M f g h h' (LocalizedModule.mk (LocalizedModule.mk x 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk x 1) 1 := by
  subst h; subst h'; rfl

/-! ### The two transports of a summand of a direct sum -/

/-- **Transporting a summand indexed by an index set of the concatenated family.** Equal index
sets index the same summand of the iterated direct sum, and the identification of the two
summands is the transport `Cech.pairModCongr`. -/
theorem lof_splitCongr (f : Fin r → R) (g : Fin m → R) {p : ℕ}
    {U U' : Finset (Fin (r + m))} (hU : U = U') (hc : U.card = p) (hc' : U'.card = p)
    (z : cechMod f (cechMod g M (rightPart U)) (leftPart U)) :
    DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) p)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) ⟨U', hc'⟩
        (pairModCongr M f g (congrArg leftPart hU) (congrArg rightPart hU) z) =
      DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) p)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) ⟨U, hc⟩ z := by
  subst hU; rfl

/-- **Transporting a summand indexed by a pair of index sets.** -/
theorem lof_pairCongr (f : Fin r → R) (g : Fin m → R) {p : ℕ} {s s' : Finset (Fin r)}
    (h : s = s') {t t' : Finset (Fin m)} (h' : t = t')
    (hc : s.card + t.card = p) (hc' : s'.card + t'.card = p)
    (y : cechMod f (cechMod g M t) s) :
    DirectSum.lof R (PairIdx r m p) (fun w => cechMod f (cechMod g M w.1.2) w.1.1)
        ⟨(s', t'), hc'⟩ (pairModCongr M f g h h' y) =
      DirectSum.lof R (PairIdx r m p) (fun w => cechMod f (cechMod g M w.1.2) w.1.1)
        ⟨(s, t), hc⟩ y := by
  subst h; subst h'; rfl

/-! ### The two spellings of the summand identification agree -/

/-- **The index-set-primary and the pair-primary summand identifications agree.** At
`u = Cech.joinParts s t` the identification `Cech.appendModEquiv` is `Cech.pairModEquiv` followed
by the transport along `Cech.leftPart_joinParts` and `Cech.rightPart_joinParts`. Both sides are
maps out of a localization of `M`, and both send the canonical generator `x/1` to `(x/1)/1`. -/
theorem appendModEquiv_joinParts (f : Fin r → R) (g : Fin m → R) (s : Finset (Fin r))
    (t : Finset (Fin m)) (z : cechMod (Fin.append f g) M (joinParts s t)) :
    appendModEquiv M f g (joinParts s t) z =
      pairModCongr M f g (leftPart_joinParts s t).symm (rightPart_joinParts s t).symm
        (pairModEquiv M f g s t z) := by
  have key : (appendModEquiv M f g (joinParts s t)).toLinearMap =
      (pairModCongr M f g (leftPart_joinParts s t).symm
          (rightPart_joinParts s t).symm).toLinearMap.comp
        (pairModEquiv M f g s t).toLinearMap := by
    refine IsLocalizedModule.ext (cechSub (Fin.append f g) (joinParts s t))
      (LocalizedModule.mkLinearMap (cechSub (Fin.append f g) (joinParts s t)) M)
      (fun y => isUnit_algebraMap_pairMod_mem M f g
        (le_of_eq (leftPart_joinParts s t).symm) (le_of_eq (rightPart_joinParts s t).symm) y)
      (LinearMap.ext fun x => ?_)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LocalizedModule.mkLinearMap_apply,
      appendModEquiv_mk_one, pairModEquiv_mk_one, pairModCongr_mk_mk_one]
  exact LinearMap.congr_fun key z

/-! ### The pair-indexed degreewise identification -/

/-- The degree-`n` term of the total complex of the double complex
`(p, q) ↦ C^p(f; C^q(g; M))`, in the flat indexing by pairs of index sets of total cardinality
`n`. -/
abbrev pairTerm (f : Fin r → R) (g : Fin m → R) (n : ℕ) : Type _ :=
  DirectSum (PairIdx r m n) fun w => cechMod f (cechMod g M w.1.2) w.1.1

/-- The reindexing of the iterated direct sum from index sets of the concatenated family to pairs
of index sets. In this direction it is transport-free: the summand indexed by `u` is literally the
summand indexed by `Cech.splitIdx n u`. -/
noncomputable def pairReindex (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    DirectSum (ExtendedAlternatingCech.Idx (r + m) n)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) →ₗ[R]
      pairTerm M f g n :=
  DirectSum.toModule R _ _ fun u =>
    DirectSum.lof R (PairIdx r m n)
      (fun w => cechMod f (cechMod g M w.1.2) w.1.1) (splitIdx n u)

/-- The inverse reindexing, which transports each summand along `Cech.leftPart_joinParts` and
`Cech.rightPart_joinParts`. -/
noncomputable def pairUnreindex (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    pairTerm M f g n →ₗ[R]
      DirectSum (ExtendedAlternatingCech.Idx (r + m) n)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) :=
  DirectSum.toModule R _ _ fun w =>
    (DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) n)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1))
        (joinIdx n w)).comp
      (pairModCongr M f g (leftPart_joinParts w.1.1 w.1.2).symm
        (rightPart_joinParts w.1.1 w.1.2).symm).toLinearMap

/-- The reindexing acts summandwise. -/
@[simp] theorem pairReindex_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (u : ExtendedAlternatingCech.Idx (r + m) n)
    (z : cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) :
    pairReindex M f g n (DirectSum.lof R _
        (fun v => cechMod f (cechMod g M (rightPart v.1)) (leftPart v.1)) u z) =
      DirectSum.lof R (PairIdx r m n)
        (fun w => cechMod f (cechMod g M w.1.2) w.1.1) (splitIdx n u) z := by
  rw [pairReindex, DirectSum.toModule_lof]

/-- The inverse reindexing acts summandwise. -/
@[simp] theorem pairUnreindex_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ) (w : PairIdx r m n)
    (y : cechMod f (cechMod g M w.1.2) w.1.1) :
    pairUnreindex M f g n (DirectSum.lof R (PairIdx r m n)
        (fun w => cechMod f (cechMod g M w.1.2) w.1.1) w y) =
      DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) n)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) (joinIdx n w)
        (pairModCongr M f g (leftPart_joinParts w.1.1 w.1.2).symm
          (rightPart_joinParts w.1.1 w.1.2).symm y) := by
  rw [pairUnreindex, DirectSum.toModule_lof, LinearMap.comp_apply, LinearEquiv.coe_coe]

/-- The two reindexings are inverse to each other, in one direction. -/
theorem pairReindex_comp_pairUnreindex (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    (pairReindex M f g n).comp (pairUnreindex M f g n) = LinearMap.id := by
  refine DirectSum.linearMap_ext R fun w => LinearMap.ext fun y => ?_
  obtain ⟨⟨s, t⟩, hc⟩ := w
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_comp, pairUnreindex_lof,
    pairReindex_lof]
  exact lof_pairCongr M f g (leftPart_joinParts s t).symm (rightPart_joinParts s t).symm hc _ _

/-- The two reindexings are inverse to each other, in the other direction. -/
theorem pairUnreindex_comp_pairReindex (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    (pairUnreindex M f g n).comp (pairReindex M f g n) = LinearMap.id := by
  refine DirectSum.linearMap_ext R fun u => LinearMap.ext fun z => ?_
  obtain ⟨U, hc⟩ := u
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.id_comp, pairReindex_lof,
    pairUnreindex_lof]
  exact lof_splitCongr M f g (joinParts_leftPart_rightPart U).symm hc _ z

/-- The reindexing of the iterated direct sum, as an identification. -/
noncomputable def pairReindexEquiv (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    DirectSum (ExtendedAlternatingCech.Idx (r + m) n)
        (fun u => cechMod f (cechMod g M (rightPart u.1)) (leftPart u.1)) ≃ₗ[R]
      pairTerm M f g n :=
  LinearEquiv.ofLinearMap (pairReindex M f g n) (pairUnreindex M f g n)
    (pairReindex_comp_pairUnreindex M f g n) (pairUnreindex_comp_pairReindex M f g n)

/-- **The degree-`n` term of the Čech complex of a concatenated family is the degree-`n` term of
the total complex.** The summand indexed by an index set `u` of the concatenated family is the
summand indexed by the pair `(leftPart u, rightPart u)`, by `Cech.appendModEquiv`. -/
noncomputable def pairTermEquiv (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    cechTerm (Fin.append f g) M n ≃ₗ[R] pairTerm M f g n :=
  (appendTermEquiv M f g n).trans (pairReindexEquiv M f g n)

/-- **The degreewise identification acts summandwise**, in the index-set-primary spelling. -/
@[simp] theorem pairTermEquiv_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (u : ExtendedAlternatingCech.Idx (r + m) n) (z : cechMod (Fin.append f g) M u.1) :
    pairTermEquiv M f g n
        (DirectSum.lof R _ (fun v => cechMod (Fin.append f g) M v.1) u z) =
      DirectSum.lof R (PairIdx r m n) (fun w => cechMod f (cechMod g M w.1.2) w.1.1)
        (splitIdx n u) (appendModEquiv M f g u.1 z) := by
  rw [pairTermEquiv, LinearEquiv.trans_apply, appendTermEquiv_lof, pairReindexEquiv,
    LinearEquiv.coe_ofLinearMap, pairReindex_lof]

/-- **The degreewise identification acts summandwise**, in the pair-primary spelling: the summand
of `C^n(f ++ g; M)` indexed by `Cech.joinParts s t` is carried to the summand indexed by `(s, t)`
by `Cech.pairModEquiv`, with no transport. This is the form the differential split is stated
in. -/
theorem pairTermEquiv_lof_join (f : Fin r → R) (g : Fin m → R) (n : ℕ) (w : PairIdx r m n)
    (z : cechMod (Fin.append f g) M (joinParts w.1.1 w.1.2)) :
    pairTermEquiv M f g n
        (DirectSum.lof R _ (fun v => cechMod (Fin.append f g) M v.1) (joinIdx n w) z) =
      DirectSum.lof R (PairIdx r m n) (fun w => cechMod f (cechMod g M w.1.2) w.1.1) w
        (pairModEquiv M f g w.1.1 w.1.2 z) := by
  obtain ⟨⟨s, t⟩, hc⟩ := w
  rw [pairTermEquiv_lof, appendModEquiv_joinParts]
  exact lof_pairCongr M f g (leftPart_joinParts s t).symm (rightPart_joinParts s t).symm hc _ _

/-- The inverse of the degreewise identification acts summandwise. -/
theorem pairTermEquiv_symm_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ) (w : PairIdx r m n)
    (y : cechMod f (cechMod g M w.1.2) w.1.1) :
    (pairTermEquiv M f g n).symm
        (DirectSum.lof R (PairIdx r m n)
          (fun w => cechMod f (cechMod g M w.1.2) w.1.1) w y) =
      DirectSum.lof R _ (fun v => cechMod (Fin.append f g) M v.1) (joinIdx n w)
        ((pairModEquiv M f g w.1.1 w.1.2).symm y) := by
  rw [LinearEquiv.symm_apply_eq, pairTermEquiv_lof_join, LinearEquiv.apply_symm_apply]

/-- The degreewise identification on the canonical generator of a summand. -/
theorem pairTermEquiv_lof_join_mk_one (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (w : PairIdx r m n) (x : M) :
    pairTermEquiv M f g n
        (DirectSum.lof R _ (fun v => cechMod (Fin.append f g) M v.1) (joinIdx n w)
          (LocalizedModule.mk x 1)) =
      DirectSum.lof R (PairIdx r m n) (fun w => cechMod f (cechMod g M w.1.2) w.1.1) w
        (LocalizedModule.mk (LocalizedModule.mk x 1) 1) := by
  rw [pairTermEquiv_lof_join, pairModEquiv_mk_one]

/-! ### Splitting a sum over the complement of an index set -/

/-- **A sum over the complement of an assembled index set splits.** By
`Cech.compl_joinParts` the complement is assembled from the two complements, and the two blocks
of indices are disjoint. -/
theorem sum_compl_joinParts {T : Type*} [AddCommMonoid T] (s : Finset (Fin r))
    (t : Finset (Fin m)) (F : Fin (r + m) → T) :
    ∑ k ∈ (joinParts s t)ᶜ, F k =
      (∑ i ∈ sᶜ, F (Fin.castAdd m i)) + ∑ j ∈ tᶜ, F (Fin.natAdd r j) := by
  rw [compl_joinParts, joinParts, Finset.sum_union (disjoint_image_castAdd_natAdd _ _),
    Finset.sum_image (fun a _ b _ h => Fin.castAdd_injective _ _ h),
    Finset.sum_image (fun a _ b _ h => Fin.natAdd_injective _ _ h)]

/-! ### Inserting a new index into one of the two blocks -/

/-- Inserting a new index into the first index set raises the total cardinality by one. -/
theorem card_insert_left {n : ℕ} (w : PairIdx r m n) {i : Fin r} (hi : i ∉ w.1.1) :
    (insert i w.1.1).card + w.1.2.card = n + 1 := by
  have hw := w.2
  rw [Finset.card_insert_of_notMem hi]
  omega

/-- Inserting a new index into the second index set raises the total cardinality by one. -/
theorem card_insert_right {n : ℕ} (w : PairIdx r m n) {j : Fin m} (hj : j ∉ w.1.2) :
    w.1.1.card + (insert j w.1.2).card = n + 1 := by
  have hw := w.2
  rw [Finset.card_insert_of_notMem hj]
  omega

/-- Inserting a new index into the first index set of a pair, which raises the total cardinality
by one. -/
abbrev pairIdxInsertLeft {n : ℕ} (w : PairIdx r m n) {i : Fin r} (hi : i ∉ w.1.1) :
    PairIdx r m (n + 1) :=
  ⟨(insert i w.1.1, w.1.2), card_insert_left w hi⟩

/-- Inserting a new index into the second index set of a pair, which raises the total cardinality
by one. -/
abbrev pairIdxInsertRight {n : ℕ} (w : PairIdx r m n) {j : Fin m} (hj : j ∉ w.1.2) :
    PairIdx r m (n + 1) :=
  ⟨(w.1.1, insert j w.1.2), card_insert_right w hj⟩

/-! ### Rewriting the target index set of a transition map -/

/-- **Two spellings of the target index set give the same summand.** The transition map
`Cech.cechι` depends on the target index set only through a subset hypothesis, which is a
proposition, so equal target index sets give literally equal summands with no transport. This is
the device of `Cech.cechD_comp_cechD`. -/
theorem lof_cechι_congr {q p : ℕ} (h : Fin q → R) {u T T' : Finset (Fin q)}
    (hT : T.card = p) (hT' : T'.card = p) (huT : u ⊆ T) (huT' : u ⊆ T') (hTT' : T = T')
    (z : cechMod h M u) :
    DirectSum.lof R (ExtendedAlternatingCech.Idx q p) (fun v => cechMod h M v.1) ⟨T, hT⟩
        (cechι h M huT z) =
      DirectSum.lof R (ExtendedAlternatingCech.Idx q p) (fun v => cechMod h M v.1) ⟨T', hT'⟩
        (cechι h M huT' z) := by
  subst hTT'; rfl

/-! ### The two differentials of the total complex -/

/-- **The horizontal differential of the total complex.** On the summand indexed by `(s, t)` it
is the Čech differential of the first family with coefficients in the summand `M_{∏_t g}` of the
second: the sum over `i ∉ s` of the transition map into the summand indexed by
`(insert i s, t)`, weighted by `Cech.cechSign s i`. -/
noncomputable def pairDLeft (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    pairTerm M f g n →ₗ[R] pairTerm M f g (n + 1) :=
  DirectSum.toModule R _ _ fun w =>
    ∑ i ∈ w.1.1ᶜ.attach, cechSign w.1.1 i.1 •
      (DirectSum.lof R (PairIdx r m (n + 1))
        (fun v => cechMod f (cechMod g M v.1.2) v.1.1)
        (pairIdxInsertLeft w (by simpa using Finset.mem_compl.1 i.2))).comp
        (cechι f (cechMod g M w.1.2) (Finset.subset_insert i.1 w.1.1))

/-- **The vertical differential of the total complex, with its Koszul sign.** On the summand
indexed by `(s, t)` it is `(-1)^{#s}` times the Čech differential of the second family, localized
at the product over `s`: the sum over `j ∉ t` of the transition map into the summand indexed by
`(s, insert j t)`, weighted by `(-1)^{#s} · Cech.cechSign t j`. The sign is the one computed in
`Cech.cechSign_natAdd`, not an imposed convention. -/
noncomputable def pairDRight (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    pairTerm M f g n →ₗ[R] pairTerm M f g (n + 1) :=
  DirectSum.toModule R _ _ fun w =>
    ∑ j ∈ w.1.2ᶜ.attach, ((-1) ^ w.1.1.card * cechSign w.1.2 j.1) •
      (DirectSum.lof R (PairIdx r m (n + 1))
        (fun v => cechMod f (cechMod g M v.1.2) v.1.1)
        (pairIdxInsertRight w (by simpa using Finset.mem_compl.1 j.2))).comp
        (localizedCechι M f g w.1.1 (Finset.subset_insert j.1 w.1.2))

/-- The horizontal differential on a generator. -/
theorem pairDLeft_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ) (w : PairIdx r m n)
    (y : cechMod f (cechMod g M w.1.2) w.1.1) :
    pairDLeft M f g n
        (DirectSum.lof R (PairIdx r m n)
          (fun v => cechMod f (cechMod g M v.1.2) v.1.1) w y) =
      ∑ i ∈ w.1.1ᶜ.attach, cechSign w.1.1 i.1 •
        DirectSum.lof R (PairIdx r m (n + 1))
          (fun v => cechMod f (cechMod g M v.1.2) v.1.1)
          (pairIdxInsertLeft w (by simpa using Finset.mem_compl.1 i.2))
          (cechι f (cechMod g M w.1.2) (Finset.subset_insert i.1 w.1.1) y) := by
  rw [pairDLeft, DirectSum.toModule_lof]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

/-- The vertical differential on a generator. -/
theorem pairDRight_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ) (w : PairIdx r m n)
    (y : cechMod f (cechMod g M w.1.2) w.1.1) :
    pairDRight M f g n
        (DirectSum.lof R (PairIdx r m n)
          (fun v => cechMod f (cechMod g M v.1.2) v.1.1) w y) =
      ∑ j ∈ w.1.2ᶜ.attach, ((-1) ^ w.1.1.card * cechSign w.1.2 j.1) •
        DirectSum.lof R (PairIdx r m (n + 1))
          (fun v => cechMod f (cechMod g M v.1.2) v.1.1)
          (pairIdxInsertRight w (by simpa using Finset.mem_compl.1 j.2))
          (localizedCechι M f g w.1.1 (Finset.subset_insert j.1 w.1.2) y) := by
  rw [pairDRight, DirectSum.toModule_lof]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

/-! ### The differential splits -/

/-- A new index of the first block is outside an assembled index set when it is outside the first
of the two index sets. -/
theorem castAdd_notMem_joinParts {s : Finset (Fin r)} {t : Finset (Fin m)} {i : Fin r}
    (hi : i ∉ s) : Fin.castAdd m i ∉ joinParts s t := by
  rw [mem_joinParts_castAdd]; exact hi

/-- A new index of the second block is outside an assembled index set when it is outside the
second of the two index sets. -/
theorem natAdd_notMem_joinParts {s : Finset (Fin r)} {t : Finset (Fin m)} {j : Fin m}
    (hj : j ∉ t) : Fin.natAdd r j ∉ joinParts s t := by
  rw [mem_joinParts_natAdd]; exact hj

/-- Inserting a new index into an assembled index set raises its cardinality by one. -/
theorem card_insert_joinParts {n : ℕ} (w : PairIdx r m n) {k : Fin (r + m)}
    (hk : k ∉ joinParts w.1.1 w.1.2) :
    (insert k (joinParts w.1.1 w.1.2)).card = n + 1 := by
  have hw := w.2
  rw [Finset.card_insert_of_notMem hk, card_joinParts]
  omega

/-- Inserting a new index of the first block into an assembled index set raises its cardinality by
one. -/
theorem card_insert_castAdd {n : ℕ} (w : PairIdx r m n) {i : Fin r} (hi : i ∉ w.1.1) :
    (insert (Fin.castAdd m i) (joinParts w.1.1 w.1.2)).card = n + 1 :=
  card_insert_joinParts w (castAdd_notMem_joinParts hi)

/-- Inserting a new index of the second block into an assembled index set raises its cardinality
by one. -/
theorem card_insert_natAdd {n : ℕ} (w : PairIdx r m n) {j : Fin m} (hj : j ∉ w.1.2) :
    (insert (Fin.natAdd r j) (joinParts w.1.1 w.1.2)).card = n + 1 :=
  card_insert_joinParts w (natAdd_notMem_joinParts hj)

/-- **One horizontal summand of the differential.** Inserting an index of the first block into an
assembled index set produces, under the degreewise identification, the transition map of the Čech
complex of the first family into the summand indexed by the enlarged pair. -/
theorem pairTermEquiv_lof_insert_castAdd (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (w : PairIdx r m n) {i : Fin r} (hi : i ∉ w.1.1)
    (z : cechMod (Fin.append f g) M (joinParts w.1.1 w.1.2)) :
    pairTermEquiv M f g (n + 1)
        (DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) (n + 1))
          (fun v => cechMod (Fin.append f g) M v.1)
          ⟨insert (Fin.castAdd m i) (joinParts w.1.1 w.1.2), card_insert_castAdd w hi⟩
          (cechι (Fin.append f g) M
            (Finset.subset_insert (Fin.castAdd m i) (joinParts w.1.1 w.1.2)) z)) =
      DirectSum.lof R (PairIdx r m (n + 1)) (fun v => cechMod f (cechMod g M v.1.2) v.1.1)
        (pairIdxInsertLeft w hi)
        (cechι f (cechMod g M w.1.2) (Finset.subset_insert i w.1.1)
          (pairModEquiv M f g w.1.1 w.1.2 z)) := by
  rw [lof_cechι_congr (M := M) (Fin.append f g) (card_insert_castAdd w hi)
      ((card_joinParts (insert i w.1.1) w.1.2).trans (card_insert_left w hi))
      (Finset.subset_insert (Fin.castAdd m i) (joinParts w.1.1 w.1.2))
      (joinParts_subset_left (Finset.subset_insert i w.1.1) w.1.2)
      (joinParts_insert_left w.1.1 w.1.2 i).symm,
    pairTermEquiv_lof_join M f g (n + 1) (pairIdxInsertLeft w hi),
    pairModEquiv_cechι_left M f g (Finset.subset_insert i w.1.1) w.1.2 z]

/-- **One vertical summand of the differential.** Inserting an index of the second block produces,
under the degreewise identification, the transition map of the Čech complex of the second family
localized at the product over the first index set. -/
theorem pairTermEquiv_lof_insert_natAdd (f : Fin r → R) (g : Fin m → R) (n : ℕ)
    (w : PairIdx r m n) {j : Fin m} (hj : j ∉ w.1.2)
    (z : cechMod (Fin.append f g) M (joinParts w.1.1 w.1.2)) :
    pairTermEquiv M f g (n + 1)
        (DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) (n + 1))
          (fun v => cechMod (Fin.append f g) M v.1)
          ⟨insert (Fin.natAdd r j) (joinParts w.1.1 w.1.2), card_insert_natAdd w hj⟩
          (cechι (Fin.append f g) M
            (Finset.subset_insert (Fin.natAdd r j) (joinParts w.1.1 w.1.2)) z)) =
      DirectSum.lof R (PairIdx r m (n + 1)) (fun v => cechMod f (cechMod g M v.1.2) v.1.1)
        (pairIdxInsertRight w hj)
        (localizedCechι M f g w.1.1 (Finset.subset_insert j w.1.2)
          (pairModEquiv M f g w.1.1 w.1.2 z)) := by
  rw [lof_cechι_congr (M := M) (Fin.append f g) (card_insert_natAdd w hj)
      ((card_joinParts w.1.1 (insert j w.1.2)).trans (card_insert_right w hj))
      (Finset.subset_insert (Fin.natAdd r j) (joinParts w.1.1 w.1.2))
      (joinParts_subset_right w.1.1 (Finset.subset_insert j w.1.2))
      (joinParts_insert_right w.1.1 w.1.2 j).symm,
    pairTermEquiv_lof_join M f g (n + 1) (pairIdxInsertRight w hj),
    pairModEquiv_cechι_right M f g w.1.1 (Finset.subset_insert j w.1.2) z]

/-- **The differential of the Čech complex of a concatenated family splits into a horizontal and
a vertical part.** On the summand indexed by a pair `(s, t)` of index sets, the differential of
`C^•(f ++ g; M)` becomes `d_f + (-1)^{#s} d_g` under the degreewise identification: the Čech
differential of the first family with coefficients in `M_{∏_t g}`, plus `(-1)^{#s}` times the
Čech differential of the second family localized at `∏_s f`.

This is the Koszul differential of the total complex of the double complex
`(p, q) ↦ C^p(f; C^q(g; M))`. Neither sign is imposed: the first block contributes
`Cech.cechSign_castAdd`, which has no extra factor, and the second contributes
`Cech.cechSign_natAdd`, whose extra factor is `(-1)^{#s}`. -/
theorem pairTermEquiv_cechD_lof (f : Fin r → R) (g : Fin m → R) (n : ℕ) (w : PairIdx r m n)
    (z : cechMod (Fin.append f g) M (joinParts w.1.1 w.1.2)) :
    pairTermEquiv M f g (n + 1)
        (cechD (Fin.append f g) M n
          (DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) n)
            (fun v => cechMod (Fin.append f g) M v.1) (joinIdx n w) z)) =
      pairDLeft M f g n
          (DirectSum.lof R (PairIdx r m n) (fun v => cechMod f (cechMod g M v.1.2) v.1.1) w
            (pairModEquiv M f g w.1.1 w.1.2 z)) +
        pairDRight M f g n
          (DirectSum.lof R (PairIdx r m n) (fun v => cechMod f (cechMod g M v.1.2) v.1.1) w
            (pairModEquiv M f g w.1.1 w.1.2 z)) := by
  classical
  set G : Fin (r + m) → pairTerm M f g (n + 1) := fun k =>
    if hk : (insert k (joinParts w.1.1 w.1.2)).card = n + 1 then
      cechSign (joinParts w.1.1 w.1.2) k •
        pairTermEquiv M f g (n + 1)
          (DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) (n + 1))
            (fun v => cechMod (Fin.append f g) M v.1)
            ⟨insert k (joinParts w.1.1 w.1.2), hk⟩
            (cechι (Fin.append f g) M
              (Finset.subset_insert k (joinParts w.1.1 w.1.2)) z))
    else 0 with hG
  have hLHS : pairTermEquiv M f g (n + 1)
      (cechD (Fin.append f g) M n
        (DirectSum.lof R (ExtendedAlternatingCech.Idx (r + m) n)
          (fun v => cechMod (Fin.append f g) M v.1) (joinIdx n w) z)) =
      ∑ k ∈ (joinParts w.1.1 w.1.2)ᶜ, G k := by
    rw [cechD_lof, map_sum, ← Finset.sum_attach (joinParts w.1.1 w.1.2)ᶜ G]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := Finset.mem_compl.1 k.2
    rw [map_zsmul]
    simp only [hG, dite_eq_left (card_insert_joinParts w hk)]
  rw [hLHS, sum_compl_joinParts, pairDLeft_lof, pairDRight_lof,
    ← Finset.sum_attach w.1.1ᶜ (fun i => G (Fin.castAdd m i)),
    ← Finset.sum_attach w.1.2ᶜ (fun j => G (Fin.natAdd r j))]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi := Finset.mem_compl.1 i.2
    simp only [hG, dite_eq_left (card_insert_castAdd w hi)]
    rw [cechSign_castAdd, leftPart_joinParts,
      pairTermEquiv_lof_insert_castAdd M f g n w hi z]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj := Finset.mem_compl.1 j.2
    simp only [hG, dite_eq_left (card_insert_natAdd w hj)]
    rw [cechSign_natAdd, leftPart_joinParts, rightPart_joinParts,
      pairTermEquiv_lof_insert_natAdd M f g n w hj z]

/-- **The differential split, as an identity of linear maps.** Under the degreewise
identification the differential of `C^•(f ++ g; M)` is the sum of the horizontal and the vertical
differential of the total complex.

It suffices to check the identity on the generators of the form
`DirectSum.lof _ _ _ (Cech.joinIdx n w) z`, because those are the images under
`(Cech.pairTermEquiv M f g n).symm` of the generators of `Cech.pairTerm`, and the degreewise
identification is an isomorphism; an arbitrary generator of `C^n(f ++ g; M)` is indexed by an
index set that is only propositionally of the form `Cech.joinParts s t`. -/
theorem pairTermEquiv_comp_cechD (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    (pairTermEquiv M f g (n + 1)).toLinearMap.comp (cechD (Fin.append f g) M n) =
      (pairDLeft M f g n + pairDRight M f g n).comp
        (pairTermEquiv M f g n).toLinearMap := by
  have key : ((pairTermEquiv M f g (n + 1)).toLinearMap.comp
          (cechD (Fin.append f g) M n)).comp (pairTermEquiv M f g n).symm.toLinearMap =
      ((pairDLeft M f g n + pairDRight M f g n).comp
          (pairTermEquiv M f g n).toLinearMap).comp
        (pairTermEquiv M f g n).symm.toLinearMap := by
    refine DirectSum.linearMap_ext R fun w => LinearMap.ext fun y => ?_
    have h2 := pairTermEquiv_lof_join M f g n w ((pairModEquiv M f g w.1.1 w.1.2).symm y)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, pairTermEquiv_symm_lof,
      LinearMap.add_apply]
    rw [pairTermEquiv_cechD_lof M f g n w, h2]
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun key (pairTermEquiv M f g n x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

/-! ### The total complex -/

/-- **The differential of the total complex**: the horizontal differential plus the vertical one,
the latter weighted by the Koszul sign `(-1)^{#s}` on the summand indexed by `(s, t)`. -/
noncomputable def pairD (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    pairTerm M f g n →ₗ[R] pairTerm M f g (n + 1) :=
  pairDLeft M f g n + pairDRight M f g n

/-- **The differential of the total complex squares to zero.** This is transported from
`Cech.cechD_comp_cechD` along the degreewise identification, which is surjective; no cancellation
is recomputed. -/
theorem pairD_comp_pairD (f : Fin r → R) (g : Fin m → R) (n : ℕ) :
    (pairD M f g (n + 1)).comp (pairD M f g n) = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (pairTermEquiv M f g n).surjective x
  have h0 := LinearMap.congr_fun (pairTermEquiv_comp_cechD M f g n) y
  have h1 := LinearMap.congr_fun (pairTermEquiv_comp_cechD M f g (n + 1))
    (cechD (Fin.append f g) M n y)
  have h2 := LinearMap.congr_fun (cechD_comp_cechD (Fin.append f g) M n) y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at h0 h1 h2
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, pairD]
  rw [← h0, ← h1, h2, map_zero]

/-- **The total complex of the double complex `(p, q) ↦ C^p(f; C^q(g; M))`**, in the flat indexing
by pairs of index sets. -/
noncomputable def pairComplex (f : Fin r → R) (g : Fin m → R) :
    CochainComplex (ModuleCat.{max u v} R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (pairTerm M f g n))
    (fun n => ModuleCat.ofHom (pairD M f g n))
    (fun n => by
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
      exact pairD_comp_pairD M f g n)

/-- **The Čech complex of a concatenated family is the total complex of the double complex
`(p, q) ↦ C^p(f; C^q(g; M))`.** Degreewise this is `Cech.pairTermEquiv`, and the compatibility
with the differentials is `Cech.pairTermEquiv_comp_cechD`. -/
noncomputable def cechComplexAppendIso (f : Fin r → R) (g : Fin m → R) :
    cechComplex (Fin.append f g) M ≅ pairComplex M f g :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (pairTermEquiv M f g n).toModuleIso)
    (by
      intro i j hij
      obtain rfl : i + 1 = j := hij
      simp only [cechComplex, pairComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearEquiv.toModuleIso_hom]
      exact (pairTermEquiv_comp_cechD M f g i).symm)

end Cech

end

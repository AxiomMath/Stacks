module

public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.Algebra.Homology.StupidTruncationLE
public import StacksFrontier.Homology.KFlat.BifunctorBoundedBelow

@[expose] public noncomputable section

/-!
# The canonical truncation of a K-flat complex

The hypothesis `htrunc` of
`CochainComplex.KFlatBifunctor.exists_kFlat_resolution_isStrictlyGE_of_kFlat_truncGE` asks that
`CochainComplex.truncGE` at `m` take a K-flat complex `P` with `Hⁱ(P) = 0` for `i ≤ m` to a
K-flat complex.  This file supplies the two short exact sequences that split that question into
its parts, and proves the statement from the two inputs the parts need.

**Both inputs are necessary; neither is padding.**  The canonical truncation is assembled from
the *brutal* truncation `σ^{≥m+1}P` and the single complex on the bottom term
`(τ^{≥m}P)ᵐ = coker(dᵐ⁻¹)`, so the two inputs are:

* that the terms `Pᵖ` of `P` in degrees `p ≤ m`, each placed in its own degree, are K-flat —
  the brutal truncation of a K-flat complex is otherwise *not* K-flat.  Over `ℤ` the complex
  `P = (ℤ/2 →^{id} ℤ/2)` in degrees `0, 1` is contractible, hence K-flat, while
  `σ^{≥1}P = ℤ/2` placed in degree `1` is not: tensoring it with the acyclic complex `Z` with
  `Z^q = ℤ/4` and differential multiplication by `2` gives `ℤ/2` with zero differential in
  every degree.
* that the bottom term of the truncation is K-flat in its degree.  This is where the
  cohomological side condition enters: `Hᵐ(P) = 0` makes `coker(dᵐ⁻¹)` a *subobject* of
  `Pᵐ⁺¹`, which is `CochainComplex.mono_d_truncGE`, so the input becomes "a subobject of a
  flat object is flat" — true for abelian sheaves, where flat means torsion-free, and false in
  general.

Neither input can be read off K-flatness of `P` alone, and neither can be replaced by
degreewise flatness of `P` in all degrees: a bounded below complex of flat objects need not be
K-flat, as the module documentation of
`StacksFrontier/Homology/KFlat/BifunctorBoundedBelow.lean` records with a counterexample over `ℤ`.

## Main definitions

* `StacksDraft.StupidTruncation.stupidTruncGELEShortComplex`: the short complex
  `σ^{≥a}K ⟶ K ⟶ σ^{≤a-1}K`, the brutal truncation sequence that Mathlib and this library both
  lacked.  `StacksDraft.StupidTruncation.stupidTruncGELESplitting` is its degreewise splitting
  and `StacksDraft.StupidTruncation.stupidTruncGELEShortComplex_shortExact` its short
  exactness.
* `StacksDraft.StupidTruncation.truncGESingleShortComplex`: the short complex
  `σ^{≥m+1}K ⟶ τ^{≥m}K ⟶ (single m).obj ((τ^{≥m}K)ᵐ)`, which exhibits the canonical truncation
  as an extension of its bottom term by a brutal truncation, with degreewise splitting
  `StacksDraft.StupidTruncation.truncGESingleSplitting`.

## Main results

* `CochainComplex.mono_d_truncGE`: for `K` with `Hⁱ(K) = 0` for `i ≤ m`, the differential
  `(τ^{≥m}K)ᵐ ⟶ (τ^{≥m}K)ᵐ⁺¹` is a monomorphism.  This is the precise sense in which the
  bottom term of the truncation is a subobject of `Kᵐ⁺¹`.
* `CochainComplex.KFlatBifunctor.kFlat_single_of_isZero`: a zero object placed in any degree is
  K-flat.
* `CochainComplex.KFlatBifunctor.kFlat_stupidTruncGE`: **a brutal truncation `σ^{≥a}K` of a
  K-flat complex is K-flat as soon as the terms of `K` below `a` are**, from the brutal
  truncation sequence, two out of three in a degreewise split sequence, and
  `CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE` for the bounded above quotient.
* `CochainComplex.KFlatBifunctor.kFlat_truncGE_of_kFlat_terms`,
  `CochainComplex.KFlatBifunctor.kFlat_truncGE_of_isGE`: **the canonical truncation `τ^{≥m}K`
  of a K-flat complex is K-flat**, from the two inputs above; the second states the bottom
  input in the form "every subobject of `Kᵐ⁺¹`, placed in degree `m`, is K-flat", which is what
  the cohomological side condition buys.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex

namespace StacksDraft.StupidTruncation

/-! ### The brutal truncation sequence `0 ⟶ σ^{≥a}K ⟶ K ⟶ σ^{≤a-1}K ⟶ 0` -/

section BrutalSequence

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : CochainComplex C ℤ) (a : ℤ)

/-- The short complex `σ^{≥a}K ⟶ K ⟶ σ^{≤a-1}K` cut out by the two brutal truncations of `K` at
`a`: the inclusion of the subcomplex on the degrees `≥ a` followed by the projection onto the
quotient complex on the degrees `≤ a - 1`.  It is degreewise split, hence short exact; see
`stupidTruncGELESplitting` and `stupidTruncGELEShortComplex_shortExact`. -/
def stupidTruncGELEShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (ιStupidTrunc K (embeddingUpIntGE a))
    (K.πStupidTrunc (embeddingUpIntLE (a - 1)))
    (HomologicalComplex.hom_ext _ _ (fun n => by
      by_cases hn : a ≤ n
      · exact (CochainComplex.isZero_of_isStrictlyLE
          (K.stupidTrunc (embeddingUpIntLE (a - 1))) (a - 1) n (by omega)).eq_of_tgt _ _
      · exact (CochainComplex.isZero_of_isStrictlyGE
          (K.stupidTrunc (embeddingUpIntGE a)) a n (by omega)).eq_of_src _ _))

end BrutalSequence

section BrutalSequenceSplit

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  (K : CochainComplex C ℤ) (a : ℤ)

/-- **The brutal truncation sequence is degreewise split.**  In a degree `n ≥ a` the quotient
truncation vanishes and the inclusion is the identification of terms; in a degree `n < a` the
subcomplex vanishes and the projection is the identification of terms. -/
def stupidTruncGELESplitting (n : ℤ) :
    ((stupidTruncGELEShortComplex K a).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting := by
  by_cases hn : a ≤ n
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_
    · change IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f n)
      rw [ιStupidTruncGE_f K a n hn]
      infer_instance
    · exact CochainComplex.isZero_of_isStrictlyLE
        (K.stupidTrunc (embeddingUpIntLE (a - 1))) (a - 1) n (by omega)
  · refine ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_
    · exact CochainComplex.isZero_of_isStrictlyGE
        (K.stupidTrunc (embeddingUpIntGE a)) a n (by omega)
    · change IsIso ((K.πStupidTrunc (embeddingUpIntLE (a - 1))).f n)
      exact isIso_πStupidTruncLE_f K (a - 1) n (by omega)

end BrutalSequenceSplit

section BrutalSequenceExact

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ) (a : ℤ)

/-- **The sequence `0 ⟶ σ^{≥a}K ⟶ K ⟶ σ^{≤a-1}K ⟶ 0` is short exact**, being degreewise
split. -/
lemma stupidTruncGELEShortComplex_shortExact :
    (stupidTruncGELEShortComplex K a).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun n => (stupidTruncGELESplitting K a n).shortExact)

end BrutalSequenceExact

end StacksDraft.StupidTruncation

namespace CochainComplex

section TruncGEMono

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ) (m : ℤ)

/-- **The bottom term of the canonical truncation is a subobject of `Kᵐ⁺¹`**, for a complex
whose cohomology vanishes in degrees `≤ m`: the differential of `τ^{≥m}K` out of degree `m` is
a monomorphism.

The truncation vanishes in degree `m - 1`, so exactness of `τ^{≥m}K` at `m` is exactly that
statement; and `τ^{≥m}K` is exact at `m` because `K` is — the canonical projection
`K ⟶ τ^{≥m}K` is a quasi-isomorphism in degree `m`.  Composed with
`CochainComplex.truncGEXIso` this presents `(τ^{≥m}K)ᵐ` as a subobject of `Kᵐ⁺¹`, which is the
shape in which "a subobject of a flat object is flat" applies to it. -/
theorem mono_d_truncGE [K.IsGE (m + 1)] : Mono ((K.truncGE m).d m (m + 1)) := by
  have hex : (K.truncGE m).ExactAt m :=
    (exactAt_iff_of_quasiIsoAt (K.πTruncGE m) m).1
      (K.exactAt_of_isGE (m + 1) m (by omega))
  rw [HomologicalComplex.exactAt_iff' (K := K.truncGE m) (i := m - 1) (j := m) (k := m + 1)
    (CochainComplex.prev ℤ m) (CochainComplex.next ℤ m)] at hex
  have hf : ((K.truncGE m).sc' (m - 1) m (m + 1)).f = 0 :=
    ((K.truncGE m).isZero_of_isStrictlyGE m (m - 1) (by omega)).eq_of_src _ _
  exact (ShortComplex.exact_iff_mono _ hf).1 hex

end TruncGEMono

end CochainComplex

namespace StacksDraft.StupidTruncation

/-! ### The canonical truncation as an extension of its bottom term -/

section TruncGESequence

variable {C : Type*} [Category* C] [Abelian C] (K : CochainComplex C ℤ) (m : ℤ)

/-- The differential of `τ^{≥m}K` into degree `m` vanishes, the truncation being zero in
degree `m - 1`.  This is the hypothesis of `HomologicalComplex.mkHomToSingle` for the
projection of `τ^{≥m}K` onto its bottom term. -/
lemma truncGE_d_comp_id_eq_zero (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i m) :
    (K.truncGE m).d i m ≫ 𝟙 ((K.truncGE m).X m) = 0 :=
  (CochainComplex.isZero_of_isStrictlyGE (K.truncGE m) m i (by
    simp only [ComplexShape.up_Rel] at hi
    omega)).eq_of_src _ _

/-- The short complex `σ^{≥m+1}K ⟶ τ^{≥m}K ⟶ (single m).obj ((τ^{≥m}K)ᵐ)`.  The canonical
truncation agrees with `K` above `m` and has `coker(dᵐ⁻¹)` in degree `m`, so the brutal
truncation on the degrees `≥ m + 1` is a subcomplex of it with the bottom term as quotient.
The first map is the inclusion of the brutal truncation followed by the canonical projection;
the second is the projection onto the bottom term.  It is degreewise split; see
`truncGESingleSplitting`. -/
def truncGESingleShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (ιStupidTrunc K (embeddingUpIntGE (m + 1)) ≫ K.πTruncGE m)
    (HomologicalComplex.mkHomToSingle (𝟙 ((K.truncGE m).X m))
      (truncGE_d_comp_id_eq_zero K m))
    (by
      apply HomologicalComplex.to_single_hom_ext
      exact (CochainComplex.isZero_of_isStrictlyGE
        (K.stupidTrunc (embeddingUpIntGE (m + 1))) (m + 1) m (by omega)).eq_of_src _ _)

/-- **The sequence of `truncGESingleShortComplex` is degreewise split.**  In degree `m` the
brutal truncation vanishes and the projection onto the bottom term is an isomorphism; above `m`
the single complex vanishes and the first map is the composite of two isomorphisms; below `m`
all three terms vanish. -/
def truncGESingleSplitting (n : ℤ) :
    ((truncGESingleShortComplex K m).map
      (HomologicalComplex.eval C (ComplexShape.up ℤ) n)).Splitting := by
  by_cases hn : n = m
  · subst hn
    refine ShortComplex.Splitting.ofIsZeroOfIsIso _ ?_ ?_
    · exact CochainComplex.isZero_of_isStrictlyGE
        (K.stupidTrunc (embeddingUpIntGE (n + 1))) (n + 1) n (by omega)
    · change IsIso ((HomologicalComplex.mkHomToSingle (𝟙 ((K.truncGE n).X n))
        (truncGE_d_comp_id_eq_zero K n)).f n)
      rw [HomologicalComplex.mkHomToSingle_f]
      infer_instance
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ ?_
    · change IsIso ((ιStupidTrunc K (embeddingUpIntGE (m + 1)) ≫ K.πTruncGE m).f n)
      rw [HomologicalComplex.comp_f]
      rcases lt_or_gt_of_ne hn with h | h
      · exact IsZero.isIso
          (CochainComplex.isZero_of_isStrictlyGE
            (K.stupidTrunc (embeddingUpIntGE (m + 1))) (m + 1) n (by omega))
          (CochainComplex.isZero_of_isStrictlyGE (K.truncGE m) m n (by omega)) _
      · have h₁ : IsIso ((ιStupidTrunc K (embeddingUpIntGE (m + 1))).f n) := by
          rw [ιStupidTruncGE_f K (m + 1) n (by omega)]
          infer_instance
        have h₂ := K.isIso_πTruncGE_f_of_lt m n h
        infer_instance
    · exact isZero_single_obj_X (ComplexShape.up ℤ) m ((K.truncGE m).X m) n hn

end TruncGESequence

end StacksDraft.StupidTruncation

namespace CochainComplex.KFlatBifunctor

section Truncation

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [HasColimitsOfShape ℕ B] [HasColimitsOfShape ℕ D]

omit [HasColimitsOfShape ℕ B] [HasColimitsOfShape ℕ D] in
/-- A zero object placed in any degree gives a K-flat complex: the row complex `p ↦ F(Gᵖ, 0)` of
`CochainComplex.KFlatBifunctor.kFlat_single_of_exact` is degreewise zero, since `F(X, -)` is
additive, and a complex with zero terms is exact everywhere. -/
theorem kFlat_single_of_isZero (M : B) (hM : IsZero M) (q : ℤ) :
    KFlat F ((single B (ComplexShape.up ℤ) q).obj M) := by
  have h : ∀ X : A, IsZero ((F.obj X).obj M) := fun X => by
    rw [IsZero.iff_id_eq_zero, ← (F.obj X).map_id, hM.eq_of_src (𝟙 M) 0, Functor.map_zero]
  exact kFlat_single_of_exact F M q
    (fun G _ n => HomologicalComplex.ExactAt.of_isZero (h (G.X n)))

/-- **A brutal truncation `σ^{≥a}K` of a K-flat complex is K-flat as soon as the terms of `K` in
the degrees below `a`, each placed in its own degree, are.**

The brutal truncation sequence `0 ⟶ σ^{≥a}K ⟶ K ⟶ σ^{≤a-1}K ⟶ 0` of
`StacksDraft.StupidTruncation.stupidTruncGELEShortComplex` is degreewise split, so two out of
three applies: `σ^{≥a}K` is K-flat as soon as `K` and `σ^{≤a-1}K` are, and `σ^{≤a-1}K` is
strictly bounded above with the terms of `K` below `a` as its terms, which is
`CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE`.

The hypothesis on the terms cannot be dropped.  Over `ℤ` the contractible complex
`ℤ/2 →^{id} ℤ/2` in degrees `0, 1` is K-flat while its brutal truncation `σ^{≥1}` is `ℤ/2`
placed in degree `1`, which is not. -/
theorem kFlat_stupidTruncGE (K : CochainComplex B ℤ) (a : ℤ)
    (hF : ∀ X : A, PreservesColimitsOfShape ℕ (F.obj X))
    (hexact : ∀ (E : ℕ ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hK : KFlat F K)
    (hterm : ∀ q : ℤ, q < a → KFlat F ((single B (ComplexShape.up ℤ) q).obj (K.X q))) :
    KFlat F (K.stupidTrunc (embeddingUpIntGE a)) := by
  refine kFlat_X₁_of_degreewiseSplit F
    (StacksDraft.StupidTruncation.stupidTruncGELEShortComplex K a)
    (StacksDraft.StupidTruncation.stupidTruncGELESplitting K a) hK ?_
  refine kFlat_of_isStrictlyLE F (K.stupidTrunc (embeddingUpIntLE (a - 1))) (a - 1)
    hF hexact (fun q => ?_)
  by_cases hq : q ≤ a - 1
  · exact (hterm q (by omega)).of_iso F ((single B (ComplexShape.up ℤ) q).mapIso
      (StacksDraft.StupidTruncation.stupidTruncLEXIso K (a - 1) q hq).symm)
  · exact kFlat_single_of_isZero F _ (CochainComplex.isZero_of_isStrictlyLE
      (K.stupidTrunc (embeddingUpIntLE (a - 1))) (a - 1) q (by omega)) q

/-- **The canonical truncation `τ^{≥m}K` of a K-flat complex is K-flat**, given that the terms
of `K` in the degrees `≤ m` are K-flat in their own degree and that the bottom term
`(τ^{≥m}K)ᵐ = coker(dᵐ⁻¹)` is K-flat in degree `m`.

The sequence `0 ⟶ σ^{≥m+1}K ⟶ τ^{≥m}K ⟶ (single m).obj ((τ^{≥m}K)ᵐ) ⟶ 0` of
`StacksDraft.StupidTruncation.truncGESingleShortComplex` is degreewise split, so two out of
three gives the middle term from the two outer ones; the brutal truncation is K-flat by
`CochainComplex.KFlatBifunctor.kFlat_stupidTruncGE`.

For the form of the second hypothesis that the cohomological side condition `Hⁱ(K) = 0`,
`i ≤ m`, produces, see `CochainComplex.KFlatBifunctor.kFlat_truncGE_of_isGE`. -/
theorem kFlat_truncGE_of_kFlat_terms (K : CochainComplex B ℤ) (m : ℤ)
    (hF : ∀ X : A, PreservesColimitsOfShape ℕ (F.obj X))
    (hexact : ∀ (E : ℕ ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hK : KFlat F K)
    (hterm : ∀ q : ℤ, q ≤ m → KFlat F ((single B (ComplexShape.up ℤ) q).obj (K.X q)))
    (hbot : KFlat F ((single B (ComplexShape.up ℤ) m).obj ((K.truncGE m).X m))) :
    KFlat F (K.truncGE m) :=
  kFlat_X₂_of_degreewiseSplit F
    (StacksDraft.StupidTruncation.truncGESingleShortComplex K m)
    (StacksDraft.StupidTruncation.truncGESingleSplitting K m)
    (kFlat_stupidTruncGE F K (m + 1) hF hexact hK (fun q hq => hterm q (by omega))) hbot

/-- **The canonical truncation `τ^{≥m}K` of a K-flat complex whose cohomology vanishes in
degrees `≤ m` is K-flat**, given that the terms of `K` in the degrees `≤ m` are K-flat in their
own degree and that every subobject of `Kᵐ⁺¹`, placed in degree `m`, is K-flat.

This is `CochainComplex.KFlatBifunctor.kFlat_truncGE_of_kFlat_terms` with its second
hypothesis put in the form the side condition `K.IsGE (m + 1)` produces: that makes the
differential of
`τ^{≥m}K` out of degree `m` a monomorphism (`CochainComplex.mono_d_truncGE`), and composing it
with the identification `(τ^{≥m}K)ᵐ⁺¹ ≅ Kᵐ⁺¹` presents the bottom term as a subobject of
`Kᵐ⁺¹`.  So `hsub` is "a subobject of a flat object is flat" at the object `Kᵐ⁺¹`, which for
abelian sheaves is the statement that a subsheaf of a torsion-free abelian sheaf is
torsion-free. -/
theorem kFlat_truncGE_of_isGE (K : CochainComplex B ℤ) (m : ℤ)
    (hF : ∀ X : A, PreservesColimitsOfShape ℕ (F.obj X))
    (hexact : ∀ (E : ℕ ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hK : KFlat F K) (hGE : K.IsGE (m + 1))
    (hterm : ∀ q : ℤ, q ≤ m → KFlat F ((single B (ComplexShape.up ℤ) q).obj (K.X q)))
    (hsub : ∀ (M : B) (i : M ⟶ K.X (m + 1)), Mono i →
      KFlat F ((single B (ComplexShape.up ℤ) m).obj M)) :
    KFlat F (K.truncGE m) := by
  have := hGE
  refine kFlat_truncGE_of_kFlat_terms F K m hF hexact hK hterm
    (hsub _ ((K.truncGE m).d m (m + 1) ≫ (K.truncGEXIso m (m + 1) (by omega)).hom) ?_)
  have := CochainComplex.mono_d_truncGE K m
  infer_instance

end Truncation

end CochainComplex.KFlatBifunctor

end

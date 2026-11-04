module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.TermwiseSplit.GradedStrictness

/-!
# Strict exactness inputs of the termwise split lifting

The strictness and extension statements consumed by the construction of
`CochainComplex.exists_termwiseSplit_shortExact_of_filteredQuasiIso_of_injective_gr`: filtrations
with vanishing graded pieces, the strictness of the degreewise maps of a short exact sequence of
`Fil^f(𝒜)` and of a filtered quasi-isomorphism (`isStrictHom_evalFunctor_map_of_*`), the strict
exactness up to refinements and the extension step it yields (`exists_comp_eq_of_comp_eq_zero`),
and its two instances along a filtered resolution (`exists_comp_evalD_eq_of_*`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredTermwiseSplit

open CategoryTheory Limits Opposite CategoryTheory.FilteredObject

namespace CochainComplex.FilteredInjective.TermwiseSplit

open CochainComplex.FilteredInjective.Degreewise
open CochainComplex.FilteredInjective.Resolution (filtrationOfSteps homFromDegreeZero
  homFromDegreeZero_f_zero homFromDegreeZero_f_of_ne)

attribute [local simp] evalFil_ι_app homFromDegreeZero_f_zero homFromDegreeZero_f_of_ne

/-! ### Filtrations with vanishing graded pieces -/

/-- Downwards induction on `ℤ`: a property holding at all `q ≥ r` and passing from `q + 1` to `q`
holds everywhere. -/
private lemma forall_of_forall_ge_of_succ {P : ℤ → Prop} {r : ℤ} (hbase : ∀ q, r ≤ q → P q)
    (hstep : ∀ q, P (q + 1) → P q) (p : ℤ) : P p := by
  have hdown : ∀ k : ℕ, P (r - (k : ℤ)) := by
    intro k
    induction k with
    | zero => simpa using hbase r le_rfl
    | succ k ih =>
        refine hstep _ (by rwa [show r - (((k + 1 : ℕ)) : ℤ) + 1 = r - (k : ℤ) by push_cast; ring])
  by_cases hp : r ≤ p
  · exact hbase p hp
  · have h := hdown (r - p).toNat
    rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at h

/-- A step `F^{p + 1} X ⟶ F^p X` of a filtration with vanishing `p`-th graded piece is an
isomorphism: it is a monomorphism, being a morphism of subobjects of `X`, and its cokernel is the
graded piece. -/
private lemma isIso_diagram_map_of_isZero_gradedPiece {K : FilteredObject 𝒜 ℤᵒᵖ} {p : ℤ}
    (h : IsZero ((gr p).obj K)) :
    IsIso (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) := by
  have hmono : Mono (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) :=
    mono_of_mono_fac (Filtration.diagram_map_comp_ι_app K.filtration _)
  have hepi : Epi (K.filtration.diagram.map
      (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) :=
    (Preadditive.epi_iff_isZero_cokernel _).mpr h
  exact isIso_of_mono_of_epi _

/-- A filtration with vanishing graded pieces which vanishes at `q` vanishes at every `p ≤ q`. -/
private lemma isZero_obj_of_isZero_gradedPiece {K : FilteredObject 𝒜 ℤᵒᵖ}
    (h : ∀ p : ℤ, IsZero ((gr p).obj K)) {q : ℤ}
    (hq : IsZero (K.filtration.obj (op q))) {p : ℤ} (hpq : p ≤ q) :
    IsZero (K.filtration.obj (op p)) := by
  refine forall_of_forall_ge_of_succ (P := fun x => x ≤ q → IsZero (K.filtration.obj (op x)))
    (r := q + 1) (fun x hx hxq => absurd hxq (by omega)) (fun x hx hxq => ?_) p hpq
  rcases hxq.eq_or_lt with rfl | hlt
  · exact hq
  · have := isIso_diagram_map_of_isZero_gradedPiece (h x)
    exact (hx hlt).of_iso (asIso (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) :
      (x : ℤ) ⟶ x + 1).op)).symm

/-- A filtered object with finite filtration all of whose graded pieces vanish is zero: the
filtration is constant, and it both vanishes and is exhausted. -/
private lemma isZero_of_isFinite_of_forall_isZero_gradedPiece {K : FilteredObject 𝒜 ℤᵒᵖ}
    (hK : K.filtration.IsFinite) (h : ∀ p : ℤ, IsZero ((gr p).obj K)) :
    IsZero K.X := by
  obtain ⟨r, hr⟩ := hK.exists_isIso_ι
  obtain ⟨q, hq⟩ := hK.exists_isZero_obj
  have h1 : IsZero (K.filtration.obj (op (min r q))) :=
    isZero_obj_of_isZero_gradedPiece h hq (min_le_right r q)
  have h2 : IsIso (K.filtration.ι.app (op (min r q))) :=
    Filtration.isIso_ι_app_of_le K.filtration (min_le_left r q) hr
  exact h1.of_iso (asIso (K.filtration.ι.app (op (min r q)))).symm

/-! ### The three steps -/

/-- The graded pieces of a composite which vanishes on the underlying complexes compose to zero:
each `F^p C^• ⟶ C^•` is a monomorphism, so the composite already vanishes on the filtration
steps. -/
private lemma gradedPiece_map_comp_map_eq_zero
    {A B C : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : A ⟶ B) (β : B ⟶ C)
    (hcomp : α.hom ≫ β.hom = 0) (p : ℤ) :
    (gr p).map α ≫
      (gr p).map β = 0 := by
  have hz : ∀ q : ℤᵒᵖ, (α ≫ β).natTrans.app q = 0 := fun q =>
    zero_of_comp_mono (C.filtration.ι.app q) (by simp [hcomp])
  rw [← Functor.map_comp]
  apply coequalizer.hom_ext
  simp only [grMap_map, cokernel.π_desc, hz, zero_comp]
  exact comp_zero.symm

/-- The graded pieces of the middle term of a short exact sequence of `Fil^f(𝒜)` whose outer terms
are concentrated in degree `0` vanish outside degree `0`: `gr^p(B^n)` sits between `gr^p(A^n) = 0`
and `gr^p(C^n) = 0`. -/
private lemma isZero_gradedPiece_eval {A B C : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [A.X.IsStrictlyGE 0] [A.X.IsStrictlyLE 0] [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    (α : A ⟶ B) (β : B ⟶ C)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫
        (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (hcomp : α.hom ≫ β.hom = 0)
    (p n : ℤ) (hn : n ≠ 0) : IsZero ((gr p).obj (evalFil B n)) := by
  have hiso : ∀ K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ,
      ((gr p).obj K).X n ≅ (gr p).obj (evalFil K n) :=
    fun K => PreservesCokernel.iso (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      (K.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op)
  have hzeroX : ∀ K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ, IsZero (K.X.X n) →
      IsZero (((gr p).obj K).X n) := by
    intro K hK
    have hsub : IsZero ((evalFil K n).filtration.obj (op p)) :=
      IsZero.of_mono ((evalFil K n).filtration.ι.app (op p)) hK
    have hepi : Epi ((evalFil K n).filtration.diagram.map
        (homOfLE (Int.le_add_one le_rfl) : (p : ℤ) ⟶ p + 1).op) :=
      ⟨fun _ _ _ => hsub.eq_of_src _ _⟩
    exact IsZero.of_iso ((Preadditive.epi_iff_isZero_cokernel _).mp hepi) (hiso K)
  have hz0 := gradedPiece_map_comp_map_eq_zero α β hcomp p
  have h0 : ∀ (K : CochainComplex 𝒜 ℤ) [K.IsStrictlyGE 0] [K.IsStrictlyLE 0], IsZero (K.X n) := by
    intro K _ _
    rcases lt_or_gt_of_ne hn with h | h
    exacts [K.isZero_of_isStrictlyGE 0 n h, K.isZero_of_isStrictlyLE 0 n h]
  have hS := hgr p hz0
  have hex := (hS.map_of_exact (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).exact
  have hmono : Mono (((ShortComplex.mk _ _ hz0).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).g) :=
    hex.mono_g ((hzeroX A (h0 A.X)).eq_of_src _ _)
  exact IsZero.of_iso (IsZero.of_mono (((ShortComplex.mk _ _ hz0).map
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).g) (hzeroX C (h0 C.X))) (hiso B).symm

/-- The middle term of a short exact sequence of `Fil^f(𝒜)` whose outer terms are concentrated in
degree `0` is concentrated in degree `0`. -/
lemma isZero_X_of_ne_zero {A B C : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [A.X.IsStrictlyGE 0] [A.X.IsStrictlyLE 0] [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    (α : A ⟶ B) (β : B ⟶ C)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫
        (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (hB : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((B.filtration.ι.app (op p)).f n) ∧
      IsZero ((B.filtration.obj (op q)).X n))
    (hcomp : α.hom ≫ β.hom = 0)
    (n : ℤ) (hn : n ≠ 0) : IsZero (B.X.X n) :=
  isZero_of_isFinite_of_forall_isZero_gradedPiece (isFinite_eval hB n)
    (fun p => isZero_gradedPiece_eval α β hgr hcomp p n hn)

/-! ### The strict exactness inputs

The source's construction consumes, at each of its steps, the strictness of a morphism of filtered
objects and the extension property of a filtered injective object along it ([Stacks, Tag 05TR]).
Two of the inputs are strictness statements for the upper row: on `Fil^f(𝒜)` a morphism whose
graded pieces sit in short exact sequences is a strict monomorphism and the next one is a cokernel
(Homology, Lemma 05QH), and a filtered quasi-isomorphism out of an object concentrated in degree
`0` is a strict monomorphism in degree `0` (Homology, Lemma 05S1). The other two are the strict
exactness of the resolution `C[0] ⟶ J^•` in the form in which the induction consumes it: a morphism
out of `J^n` which kills the previous map extends along `d_J^n`, because it factors through
`Coim(d_J^n) = Im(d_J^n)` and `Im(d_J^n) ⟶ J^{n + 1}` is a strict monomorphism.
-/

/-- Two consecutive differentials of a filtered complex compose to zero. -/
private lemma evalD_comp_evalD_hom (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) :
    (evalD K n ≫ evalD K (n + 1)).hom = 0 := by
  show K.X.d n (n + 1) ≫ K.X.d (n + 1) (n + 1 + 1) = 0
  exact K.X.d_comp_d n (n + 1) (n + 1 + 1)

/-- A morphism into a filtered complex followed by two consecutive differentials vanishes. -/
lemma comp_evalD_comp_evalD_hom {X : FilteredObject 𝒜 ℤᵒᵖ}
    (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (n : ℤ) (f : X ⟶ evalFil K n) :
    (f ≫ evalD K n ≫ evalD K (n + 1)).hom = 0 := by
  show f.hom ≫ (evalD K n ≫ evalD K (n + 1)).hom = 0
  rw [evalD_comp_evalD_hom, comp_zero]

/-! ### The filtration steps of a short exact sequence of `Fil^f(𝒜)`

The source's construction consumes, in degree `n`, that `β` is a cokernel of `α` *in `Fil(𝒜)`*: a
morphism `B^n ⟶ X` of filtered objects killing `A^n` descends to `C^n`. Both the descent of the
underlying morphism and the descent of its components on the filtration steps come from the short
exactness of `0 → F^p A^n → F^p B^n → F^p C^n → 0`, which is [Stacks, Tag 05QH] (5). It is proved
here by descending induction on `p` from an index at which the filtrations vanish, along the
columns `0 → F^{p + 1} → F^p → gr^p → 0`, which are short exact by construction: the four lemma
(`CategoryTheory.ShortComplex.epi_τ₂_of_exact_of_epi`) propagates epimorphy from `F^{p + 1}` and
`gr^p` to `F^p`, and the nine lemma propagates exactness. `Mathlib` has the nine lemma for
`HomologicalComplex` (`CategoryTheory.ShortComplex.ShortExact.exactAt_X₂`) but not for
`ShortComplex`, and applying it here would mean presenting each row as three consecutive terms of a
complex; it is instead proved directly in the "up to refinements" form in which exactness of an
abelian category is available (`CategoryTheory.ShortComplex.exact_iff_exact_up_to_refinements`).
-/

/-- A step `F^{p + 1} K ⟶ F^p K` of a filtration is a monomorphism, being a morphism of subobjects
of `K`. -/
private lemma mono_fstep {C : Type u} [Category.{v} C] (K : FilteredObject C ℤᵒᵖ) (p : ℤ) :
    Mono (fstep K p) :=
  mono_of_mono_fac (fstep_comp_ι K p)

/-- The column `0 → F^{p + 1} K → F^p K → gr^p K → 0` of a filtration. -/
private noncomputable abbrev grSeq (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) : ShortComplex 𝒜 :=
  ShortComplex.mk (fstep K p) (cokernel.π (fstep K p)) (cokernel.condition _)

private lemma exact_grSeq (K : FilteredObject 𝒜 ℤᵒᵖ) (p : ℤ) : (grSeq K p).Exact :=
  ShortComplex.exact_cokernel (fstep K p)

/-- A morphism of filtered objects induces a morphism of the columns
`0 → F^{p + 1} K → F^p K → gr^p K → 0`. -/
private noncomputable def grSeqMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (p : ℤ) :
    grSeq K p ⟶ grSeq L p where
  τ₁ := f.natTrans.app (op (p + 1))
  τ₂ := f.natTrans.app (op p)
  τ₃ := grMap f p
  comm₁₂ := (f.natTrans.naturality _).symm
  comm₂₃ := (π_grMap f p).symm

/-- A filtration which vanishes at `p` vanishes at every `q ≥ p`. -/
private lemma isZero_obj_of_ge {K : FilteredObject 𝒜 ℤᵒᵖ} {p q : ℤ} (hpq : p ≤ q)
    (h : IsZero (K.filtration.obj (op p))) : IsZero (K.filtration.obj (op q)) := by
  have : Mono (K.filtration.diagram.map (homOfLE hpq).op) :=
    mono_of_mono_fac (Filtration.diagram_map_comp_ι_app K.filtration (homOfLE hpq).op)
  exact IsZero.of_mono (K.filtration.diagram.map (homOfLE hpq).op) h

/-- The components of a composite of morphisms of filtered objects on the filtration steps compose
to zero as soon as the underlying composite does: `F^p M ⟶ M` is a monomorphism. -/
private lemma natTrans_app_comp_app_eq_zero {K L M : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (g : L ⟶ M)
    (hfg : f.hom ≫ g.hom = 0) (i : ℤᵒᵖ) : f.natTrans.app i ≫ g.natTrans.app i = 0 :=
  zero_of_comp_mono (M.filtration.ι.app i) (by
    rw [Category.assoc, g.comm i, ← Category.assoc, f.comm i, Category.assoc, hfg, comp_zero])

private lemma grMap_comp_grMap_eq_zero {K L M : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L) (g : L ⟶ M)
    (hfg : f.hom ≫ g.hom = 0) (p : ℤ) : grMap f p ≫ grMap g p = 0 := by
  rw [← cancel_epi (cokernel.π (fstep K p)), comp_zero, ← Category.assoc, π_grMap, Category.assoc,
    π_grMap, ← Category.assoc, natTrans_app_comp_app_eq_zero f g hfg, zero_comp]

/-- If `a : W ⟶ F^p L` has the same image in `gr^p L` as a map through `gr^p f`, then up to an
epimorphism `a` differs from a map through `F^p f` by a map through `F^{p + 1} L`. -/
private lemma exists_refinement_sub_comp_natTrans_app {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L)
    (p : ℤ) {W : 𝒜} (a : W ⟶ L.filtration.obj (op p)) (u : W ⟶ cokernel (fstep K p))
    (h : a ≫ cokernel.π (fstep L p) = u ≫ grMap f p) :
    ∃ (W' : 𝒜) (e : W' ⟶ W) (_ : Epi e) (s : W' ⟶ L.filtration.obj (op (p + 1)))
      (t : W' ⟶ K.filtration.obj (op p)),
      s ≫ fstep L p = e ≫ a - t ≫ f.natTrans.app (op p) := by
  obtain ⟨W', e, he, t, ht⟩ := surjective_up_to_refinements_of_epi (cokernel.π (fstep K p)) u
  have hz : (e ≫ a - t ≫ f.natTrans.app (op p)) ≫ cokernel.π (fstep L p) = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, h, ← π_grMap, ← Category.assoc t,
      ← ht, Category.assoc, sub_self]
  exact ⟨W', e, he, _, t, (exact_grSeq L p).lift_f _ hz⟩

/-- **[Stacks, Tag 05QH] (5).** A morphism of filtered objects all of whose graded pieces are
epimorphisms is an epimorphism on every filtration step, provided the filtration of its target
vanishes somewhere: the four lemma propagates epimorphy downwards from the index where it does. -/
private lemma epi_natTrans_app_of_epi_grMap {K L : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L)
    (hgr : ∀ p : ℤ, Epi (grMap f p)) {r : ℤ} (hr : IsZero (L.filtration.obj (op r))) (p : ℤ) :
    Epi (f.natTrans.app (op p)) := by
  have hbase : ∀ q : ℤ, r ≤ q → Epi (f.natTrans.app (op q)) := fun q hq =>
    ⟨fun _ _ _ => (isZero_obj_of_ge hq hr).eq_of_src _ _⟩
  have hstep : ∀ q : ℤ, Epi (f.natTrans.app (op (q + 1))) → Epi (f.natTrans.app (op q)) := by
    intro q hq
    have h₁ : Epi (grSeqMap f q).τ₁ := hq
    have h₃ : Epi (grSeqMap f q).τ₃ := hgr q
    have hK : Epi (grSeq K q).g := inferInstanceAs (Epi (cokernel.π (fstep K q)))
    have hL : Epi (grSeq L q).g := inferInstanceAs (Epi (cokernel.π (fstep L q)))
    exact ShortComplex.epi_τ₂_of_exact_of_epi (grSeqMap f q) (exact_grSeq L q)
  exact forall_of_forall_ge_of_succ (P := fun q => Epi (f.natTrans.app (op q))) hbase hstep p

/-- **[Stacks, Tag 05QH] (5), the nine lemma.** If the graded pieces of `K → L → M` form exact
sequences and the filtration of `L` vanishes somewhere, then `F^p K → F^p L → F^p M` is exact for
every `p`. The induction is downwards from the index at which the filtration of `L` vanishes; the
step is the nine lemma for the columns `0 → F^{p + 1} → F^p → gr^p → 0`, in the "up to refinements"
form: a `x : W ⟶ F^p L` killed by `F^p L ⟶ F^p M` has its image in `gr^p L` coming from `gr^p K`,
and correcting `x` by a lift of that preimage to `F^p K` leaves a map through `F^{p + 1} L`, which
is killed by `F^{p + 1} L ⟶ F^{p + 1} M` and so comes from `F^{p + 1} K`. -/
private lemma exact_natTrans_app_of_exact_grMap {K L M : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L)
    (g : L ⟶ M) (hfg : f.hom ≫ g.hom = 0)
    (hgr : ∀ (p : ℤ) (w : grMap f p ≫ grMap g p = 0), (ShortComplex.mk _ _ w).Exact)
    {r : ℤ} (hr : IsZero (L.filtration.obj (op r))) (p : ℤ) :
    (ShortComplex.mk (f.natTrans.app (op p)) (g.natTrans.app (op p))
      (natTrans_app_comp_app_eq_zero f g hfg _)).Exact := by
  have hbase : ∀ q : ℤ, r ≤ q → (ShortComplex.mk (f.natTrans.app (op q)) (g.natTrans.app (op q))
      (natTrans_app_comp_app_eq_zero f g hfg _)).Exact := fun q hq =>
    ShortComplex.exact_of_isZero_X₂ _ (isZero_obj_of_ge hq hr)
  have hstep : ∀ q : ℤ, (ShortComplex.mk (f.natTrans.app (op (q + 1)))
        (g.natTrans.app (op (q + 1))) (natTrans_app_comp_app_eq_zero f g hfg _)).Exact →
      (ShortComplex.mk (f.natTrans.app (op q)) (g.natTrans.app (op q))
        (natTrans_app_comp_app_eq_zero f g hfg _)).Exact := by
    intro q hq
    rw [ShortComplex.exact_iff_exact_up_to_refinements]
    intro W x hx
    have hx' : x ≫ g.natTrans.app (op q) = 0 := hx
    have hπ : (x ≫ cokernel.π (fstep L q)) ≫ grMap g q = 0 := by
      rw [Category.assoc, π_grMap, ← Category.assoc, hx', zero_comp]
    obtain ⟨W₁, e₁, he₁, t₁, h₁⟩ :=
      (hgr q (grMap_comp_grMap_eq_zero f g hfg q)).exact_up_to_refinements _ hπ
    obtain ⟨W₂, e₂, he₂, s, t₂, hs⟩ :=
      exists_refinement_sub_comp_natTrans_app f q (e₁ ≫ x) t₁ (by rw [Category.assoc, h₁])
    have := he₁
    have := he₂
    have hgnat : fstep L q ≫ g.natTrans.app (op q)
        = g.natTrans.app (op (q + 1)) ≫ fstep M q := g.natTrans.naturality _
    have hsg : s ≫ g.natTrans.app (op (q + 1)) = 0 := by
      have := mono_fstep M q
      rw [← cancel_mono (fstep M q), zero_comp, Category.assoc, ← hgnat, ← Category.assoc, hs]
      simp [Preadditive.sub_comp, hx', natTrans_app_comp_app_eq_zero f g hfg]
    obtain ⟨W₃, e₃, he₃, u, h₃⟩ := hq.exact_up_to_refinements s hsg
    have := he₃
    refine ⟨W₃, e₃ ≫ e₂ ≫ e₁, inferInstance, u ≫ fstep K q + e₃ ≫ t₂, ?_⟩
    have hnat : fstep K q ≫ f.natTrans.app (op q)
        = f.natTrans.app (op (q + 1)) ≫ fstep L q := f.natTrans.naturality _
    simp only [Preadditive.add_comp, Category.assoc]
    rw [hnat, ← Category.assoc u, ← h₃, Category.assoc, hs, Preadditive.comp_sub]
    abel
  exact forall_of_forall_ge_of_succ (P := fun q => (ShortComplex.mk (f.natTrans.app (op q))
    (g.natTrans.app (op q)) (natTrans_app_comp_app_eq_zero f g hfg _)).Exact) hbase hstep p

/-- At an index where the filtrations exhaust the ambient objects, the exactness of the filtration
steps is the exactness of the ambient objects. -/
private lemma exact_hom_of_exact_natTrans_app {K L M : FilteredObject 𝒜 ℤᵒᵖ} (f : K ⟶ L)
    (g : L ⟶ M) (hfg : f.hom ≫ g.hom = 0) {p : ℤ}
    (hK : IsIso (K.filtration.ι.app (op p))) (hL : IsIso (L.filtration.ι.app (op p)))
    (hM : IsIso (M.filtration.ι.app (op p)))
    (h : (ShortComplex.mk (f.natTrans.app (op p)) (g.natTrans.app (op p))
      (natTrans_app_comp_app_eq_zero f g hfg _)).Exact) :
    (ShortComplex.mk f.hom g.hom hfg).Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (asIso (K.filtration.ι.app (op p)))
    (asIso (L.filtration.ι.app (op p))) (asIso (M.filtration.ι.app (op p))) ?_ ?_) h
  · simp
  · simp

omit [Abelian 𝒜] in
/-- At an index where the filtrations exhaust the ambient objects, epimorphy on the filtration
steps is epimorphy of the underlying morphism. -/
private lemma epi_hom_of_epi_natTrans_app {L M : FilteredObject 𝒜 ℤᵒᵖ} (g : L ⟶ M) {p : ℤ}
    (_hL : IsIso (L.filtration.ι.app (op p))) (hM : IsIso (M.filtration.ι.app (op p)))
    (h : Epi (g.natTrans.app (op p))) : Epi g.hom := by
  have hfac : Epi (L.filtration.ι.app (op p) ≫ g.hom) := by
    rw [← g.comm (op p)]
    have := h
    infer_instance
  exact epi_of_epi (L.filtration.ι.app (op p)) g.hom

/-- Monomorphy of `gr^p` in degree `n` is monomorphy of `gr^p` of the degree `n` term; here is the
same statement for epimorphy. -/
private lemma epi_grMap_evalFunctor_map {A B : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : A ⟶ B) (p n : ℤ) (h : Epi ((grMap α p).f n)) :
    Epi (grMap ((evalFunctor n).map α) p) := by
  have h₂ : Epi ((grMap α p).f n ≫ (grEvalIso B p n).hom) := by
    have := h; infer_instance
  have h₃ : Epi ((grEvalIso A p n).hom ≫ grMap ((evalFunctor n).map α) p) := by
    rw [grEvalIso_hom_comp_grMap]; exact h₂
  exact epi_of_epi (grEvalIso A p n).hom _

/-- Exactness of `gr^p` in degree `n` is exactness of `gr^p` of the degree `n` terms. -/
private lemma exact_grMap_evalFunctor_map {A B C : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : A ⟶ B) (β : B ⟶ C) (p n : ℤ)
    {w : (grMap α p).f n ≫ (grMap β p).f n = 0} (h : (ShortComplex.mk _ _ w).Exact)
    {w' : grMap ((evalFunctor n).map α) p ≫ grMap ((evalFunctor n).map β) p = 0} :
    (ShortComplex.mk _ _ w').Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (grEvalIso A p n) (grEvalIso B p n)
    (grEvalIso C p n) ?_ ?_) h
  · simpa using grEvalIso_hom_comp_grMap α p n
  · simpa using grEvalIso_hom_comp_grMap β p n

/-- **Homology, Lemma 05QH.** The first morphism of a short exact sequence of `Fil^f(𝒜)` is a
strict monomorphism, in each degree of the underlying complexes. -/
theorem isStrictHom_evalFunctor_map_of_shortExact_gradedPiece
    {A B C : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : A ⟶ B) (β : B ⟶ C)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫
        (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (hcomp : α.hom ≫ β.hom = 0)
    (hA : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((A.filtration.ι.app (op p)).f n) ∧
      IsZero ((A.filtration.obj (op q)).X n))
    (_hB : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((B.filtration.ι.app (op p)).f n) ∧
      IsZero ((B.filtration.obj (op q)).X n))
    (n : ℤ) : IsStrictHom ((evalFunctor n).map α) := by
  refine isStrictHom_of_mono_grMap _ (isFinite_eval hA n) fun p => ?_
  refine mono_grMap_evalFunctor_map α p n ?_
  exact ((hgr p (gradedPiece_map_comp_map_eq_zero α β hcomp p)).map_of_exact
    (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).mono_f

/-- **Homology, Lemma 05QH.** The second morphism of a short exact sequence of `Fil^f(𝒜)` is a
cokernel of the first in `Fil(𝒜)`, in each degree of the underlying complexes: a morphism out of
`B^n` killing `A^n` factors uniquely through `C^n`. -/
theorem existsUnique_comp_eq_of_shortExact_gradedPiece
    {A B C : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (α : A ⟶ B) (β : B ⟶ C)
    (hgr : ∀ (p : ℤ) (h : (gr p).map α ≫
        (gr p).map β = 0),
      (ShortComplex.mk _ _ h).ShortExact)
    (hcomp : α.hom ≫ β.hom = 0)
    (hA : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((A.filtration.ι.app (op p)).f n) ∧
      IsZero ((A.filtration.obj (op q)).X n))
    (hB : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((B.filtration.ι.app (op p)).f n) ∧
      IsZero ((B.filtration.obj (op q)).X n))
    (hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (n : ℤ) {X : FilteredObject 𝒜 ℤᵒᵖ} (g : evalFil B n ⟶ X)
    (hg : ((evalFunctor n).map α ≫ g).hom = 0) :
    ∃! h : evalFil C n ⟶ X, (evalFunctor n).map β ≫ h = g := by
  have hfg : ((evalFunctor n).map α).hom ≫ ((evalFunctor n).map β).hom = 0 := by
    show α.hom.f n ≫ β.hom.f n = 0
    rw [← HomologicalComplex.comp_f, hcomp]
    simp
  have hgrmap : ∀ (p : ℤ) (w : grMap ((evalFunctor n).map α) p ≫
      grMap ((evalFunctor n).map β) p = 0), (ShortComplex.mk _ _ w).Exact := fun p _ =>
    exact_grMap_evalFunctor_map α β p n
      ((hgr p (gradedPiece_map_comp_map_eq_zero α β hcomp p)).map_of_exact
        (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).exact
  have hgrepi : ∀ p : ℤ, Epi (grMap ((evalFunctor n).map β) p) := fun p =>
    epi_grMap_evalFunctor_map β p n
      ((hgr p (gradedPiece_map_comp_map_eq_zero α β hcomp p)).map_of_exact
        (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)).epi_g
  obtain ⟨pA, qA, hpA, hqA⟩ := hA n
  obtain ⟨pB, qB, hpB, hqB⟩ := hB n
  obtain ⟨pC, qC, hpC, hqC⟩ := hC n
  -- `β` is an epimorphism on every filtration step, by the four lemma
  have hepi : ∀ p : ℤ, Epi (((evalFunctor n).map β).natTrans.app (op p)) :=
    epi_natTrans_app_of_epi_grMap ((evalFunctor n).map β) hgrepi (r := qC) hqC
  -- and `0 → F^p A^n → F^p B^n → F^p C^n → 0` is exact, by the nine lemma
  have hexactp : ∀ p : ℤ, (ShortComplex.mk (((evalFunctor n).map α).natTrans.app (op p))
      (((evalFunctor n).map β).natTrans.app (op p))
      (natTrans_app_comp_app_eq_zero _ _ hfg _)).Exact :=
    exact_natTrans_app_of_exact_grMap _ _ hfg hgrmap (r := qB) hqB
  -- at an index where all three filtrations are exhausted, this is the ambient exactness
  have hiA : IsIso ((evalFil A n).filtration.ι.app (op (min pA (min pB pC)))) :=
    Filtration.isIso_ι_app_of_le (evalFil A n).filtration (min_le_left _ _) hpA
  have hiB : IsIso ((evalFil B n).filtration.ι.app (op (min pA (min pB pC)))) :=
    (evalFil B n).filtration.isIso_ι_app_of_le ((min_le_right _ _).trans (min_le_left _ _)) hpB
  have hiC : IsIso ((evalFil C n).filtration.ι.app (op (min pA (min pB pC)))) :=
    (evalFil C n).filtration.isIso_ι_app_of_le ((min_le_right _ _).trans (min_le_right _ _)) hpC
  have hexact : (ShortComplex.mk ((evalFunctor n).map α).hom
      ((evalFunctor n).map β).hom hfg).Exact :=
    exact_hom_of_exact_natTrans_app _ _ hfg hiA hiB hiC (hexactp _)
  have hepihom : Epi ((evalFunctor n).map β).hom :=
    epi_hom_of_epi_natTrans_app _ hiB hiC (hepi _)
  -- the descent of the underlying morphism
  obtain ⟨φ, hφ'⟩ := hexact.desc' g.hom hg
  have hφ : ((evalFunctor n).map β).hom ≫ φ = g.hom := hφ'
  -- and of its components on the filtration steps, using that `F^p β` is an epimorphism
  have hdesc : ∀ i : ℤᵒᵖ, ∃ ψ : (evalFil C n).filtration.obj i ⟶ X.filtration.obj i,
      ψ ≫ X.filtration.ι.app i = (evalFil C n).filtration.ι.app i ≫ φ := by
    intro i
    obtain ⟨p⟩ := i
    have hep := hepi p
    have hcomm : ((evalFunctor n).map β).natTrans.app (op p) ≫
        (evalFil C n).filtration.ι.app (op p)
        = (evalFil B n).filtration.ι.app (op p) ≫ ((evalFunctor n).map β).hom :=
      ((evalFunctor n).map β).comm (op p)
    have h1 : ((evalFunctor n).map β).natTrans.app (op p) ≫
        (evalFil C n).filtration.ι.app (op p) ≫ φ
        = g.natTrans.app (op p) ≫ X.filtration.ι.app (op p) := by
      rw [← Category.assoc, hcomm, Category.assoc, hφ, ← g.comm (op p)]
    have hker : ((evalFil C n).filtration.ι.app (op p) ≫ φ) ≫
        cokernel.π (X.filtration.ι.app (op p)) = 0 := by
      rw [← cancel_epi (((evalFunctor n).map β).natTrans.app (op p)), comp_zero,
        ← Category.assoc, h1, Category.assoc, cokernel.condition, comp_zero]
    exact ⟨_, (ShortComplex.exact_cokernel (X.filtration.ι.app (op p))).lift_f _ hker⟩
  refine ⟨FilteredObject.homMk φ (fun i => (hdesc i).choose) (fun i => (hdesc i).choose_spec),
    FilteredObject.hom_ext hφ, fun y hy => FilteredObject.hom_ext ?_⟩
  have hy' : ((evalFunctor n).map β).hom ≫ y.hom = g.hom :=
    congrArg FilteredObject.Hom.hom hy
  show y.hom = φ
  rw [← cancel_epi ((evalFunctor n).map β).hom, hy', hφ]

/-- **Homology, Lemma 05S1.** A filtered quasi-isomorphism from a filtered complex concentrated in
degree `0` into a filtered complex vanishing in negative degrees is, in degree `0`, a strict
monomorphism of filtered objects. -/
theorem isStrictHom_evalFunctor_map_of_filteredQuasiIso
    {C J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    [J.X.IsStrictlyGE 0] (c : C ⟶ J) (hc : CochainComplex.filteredQuasiIso 𝒜 c)
    (hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (_hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n)) :
    IsStrictHom ((evalFunctor 0).map c) := by
  refine isStrictHom_of_mono_grMap _ (isFinite_eval hC 0) fun p => ?_
  refine mono_grMap_evalFunctor_map c p 0 ?_
  have hqis : QuasiIso (grMap c p) := hc p
  exact mono_f_zero_of_quasiIso (grMap c p)
    (isZero_grObj_X (C.X.isZero_of_isStrictlyLE 0 1 (by norm_num)) p)
    (isZero_grObj_X (C.X.isZero_of_isStrictlyGE 0 (-1) (by norm_num)) p)
    (isZero_grObj_X (J.X.isZero_of_isStrictlyGE 0 (-1) (by norm_num)) p)

/-! ### Strict exactness up to refinements

Both remaining extension problems of the source's induction have the same shape: a morphism
`φ : Y ⟶ X` of filtered objects which kills the previous map `g : Z ⟶ Y` into `Y` is to be extended
along the next map `d : Y ⟶ Y'`, the input being the exactness of `gr Z → gr Y → gr Y'` and the
filtered injectivity of `X`. The two instances are `Z = C^0`, `g = c`, `Y = J^0`, `d = d_J^0` and
`Z = J^n`, `g = d_J^n`, `Y = J^{n + 1}`, `d = d_J^{n + 1}`.

The argument is the one of [Stacks, Tag 05TX]: `φ` is filtered for the *preimage* filtration
`d^{-1} F^• Y'` of `Y`, for which `d` is strict by construction, so that [Stacks, Tag 05TR]
extends it. That `φ` is filtered for the preimage filtration is the strict exactness
`d^{-1}(F^q Y') = F^q Y + g(Z)`, which is proved by induction on the number of steps of the
filtration between `q` and an index at which the filtration of `Y` is exhausted; each step is the
exactness of `gr^q Z → gr^q Y → gr^q Y'`, used in the "up to refinements" form
(`CategoryTheory.ShortComplex.Exact.exact_up_to_refinements`).
-/

/-- `x : W ⟶ Y` *refines into* the step `F^q Y` modulo `g : Z ⟶ Y` if, up to an epimorphism
`W' ↠ W`, it is the sum of a map through `F^q Y` and a map through `g`. This is membership of `x`
in `F^q Y + g(Z)`, in the form in which the exactness of an abelian category provides it, and it is
the invariant of the induction on the filtration below. -/
private def RefinesIntoMod {Z Y : FilteredObject 𝒜 ℤᵒᵖ} (g : Z ⟶ Y) (q : ℤ) {W : 𝒜}
    (x : W ⟶ Y.X) : Prop :=
  ∃ (W' : 𝒜) (e : W' ⟶ W) (_ : Epi e) (a : W' ⟶ Y.filtration.obj (op q)) (b : W' ⟶ Z.X),
    e ≫ x = (a ≫ Y.filtration.ι.app (op q) : W' ⟶ Y.X) + b ≫ g.hom

/-- **The strict exactness of an exact sequence `gr Z → gr Y → gr Y'` of `Fil^f(𝒜)`**, in the form
"up to refinements". If `x : W ⟶ Y` has `d ∘ x` factoring through `F^q Y'` then `x` lies in
`F^q Y + g(Z)`: the case of a `q` at which the filtration of `Y` is exhausted is trivial, and the
step from `q` to `q + 1` corrects `x` by an element of `g(Z)` produced by the exactness of
`gr^q Z → gr^q Y → gr^q Y'`, after which it lies in `F^{q + 1} Y + g(Z)`. -/
private lemma refinesIntoMod_filtration {Z Y Y' : FilteredObject 𝒜 ℤᵒᵖ} (g : Z ⟶ Y) (d : Y ⟶ Y')
    (hgd : (g ≫ d).hom = 0)
    (hex : ∀ (q : ℤ) (w : grMap g q ≫ grMap d q = 0), (ShortComplex.mk _ _ w).Exact)
    {r : ℤ} (hr : IsIso (Y.filtration.ι.app (op r))) (q : ℤ) {W : 𝒜}
    (x : W ⟶ Y.X) (y : W ⟶ Y'.filtration.obj (op q))
    (hxy : x ≫ d.hom = y ≫ Y'.filtration.ι.app (op q)) :
    RefinesIntoMod g q x := by
  have hgd' : g.hom ≫ d.hom = 0 := hgd
  suffices H : ∀ (k : ℕ) (q : ℤ), q ≤ r + k → ∀ {W : 𝒜} (x : W ⟶ Y.X)
      (y : W ⟶ Y'.filtration.obj (op q)),
      x ≫ d.hom = y ≫ Y'.filtration.ι.app (op q) → RefinesIntoMod g q x from
    H (q - r).toNat q (by omega) x y hxy
  intro k
  induction k with
  | zero =>
      intro q hq W x y _
      have hiso : IsIso (Y.filtration.ι.app (op q)) :=
        Filtration.isIso_ι_app_of_le Y.filtration (by simpa using hq) hr
      exact ⟨W, 𝟙 W, inferInstance, x ≫ inv (Y.filtration.ι.app (op q)), 0, by simp⟩
  | succ k ih =>
      intro q hq W x y hxy
      rcases le_or_gt q (r + k) with h | h
      · exact ih q h x y hxy
      · obtain rfl : q = r + k + 1 := by push_cast at hq ⊢; omega
        have hxy' : x ≫ d.hom
            = (y ≫ fstep Y' (r + k)) ≫ Y'.filtration.ι.app (op (r + k)) := by
          rw [Category.assoc, fstep_comp_ι, hxy]
        obtain ⟨W₁, e₁, he₁, a₀, b₀, h₁⟩ := ih (r + k) le_rfl x (y ≫ fstep Y' (r + k)) hxy'
        have := he₁
        have ha₀ : (a₀ ≫ Y.filtration.ι.app (op (r + k)) : W₁ ⟶ Y.X)
            = e₁ ≫ x - b₀ ≫ g.hom := by rw [h₁]; abel
        -- `a₀` is a cocycle of `gr^{r + k}`
        have hcoc : a₀ ≫ d.natTrans.app (op (r + k)) = e₁ ≫ y ≫ fstep Y' (r + k) := by
          rw [← cancel_mono (Y'.filtration.ι.app (op (r + k))), Category.assoc,
            d.comm (op (r + k)), ← Category.assoc, ha₀]
          simp [Preadditive.sub_comp, hxy', hgd']
        have hπ : (a₀ ≫ cokernel.π (fstep Y (r + k))) ≫ grMap d (r + k) = 0 := by
          rw [Category.assoc, π_grMap, ← Category.assoc, hcoc, Category.assoc, Category.assoc,
            cokernel.condition, comp_zero, comp_zero]
        -- the exactness of `gr^{r + k} Z → gr^{r + k} Y → gr^{r + k} Y'` corrects it
        obtain ⟨W₂, e₂, he₂, u, h₂⟩ :=
          (hex (r + k) (grMap_comp_grMap_eq_zero g d hgd' (r + k))).exact_up_to_refinements _ hπ
        have := he₂
        obtain ⟨W₃, e₃, he₃, L, u', hL⟩ := exists_refinement_sub_comp_natTrans_app g (r + k)
          (e₂ ≫ a₀) u (by rw [Category.assoc, h₂])
        have := he₃
        have hsum : e₃ ≫ e₂ ≫ a₀
            = L ≫ fstep Y (r + k) + u' ≫ g.natTrans.app (op (r + k)) := by rw [hL]; abel
        refine ⟨W₃, e₃ ≫ e₂ ≫ e₁, inferInstance, L,
          (u' ≫ Z.filtration.ι.app (op (r + k)) : W₃ ⟶ Z.X) + e₃ ≫ e₂ ≫ b₀, ?_⟩
        calc (e₃ ≫ e₂ ≫ e₁) ≫ x = (e₃ ≫ e₂) ≫ e₁ ≫ x := by simp
          _ = (e₃ ≫ e₂) ≫ ((a₀ ≫ Y.filtration.ι.app (op (r + k)) : W₁ ⟶ Y.X)
              + b₀ ≫ g.hom) := by rw [h₁]
          _ = ((e₃ ≫ e₂ ≫ a₀) ≫ Y.filtration.ι.app (op (r + k)) : W₃ ⟶ Y.X)
              + (e₃ ≫ e₂ ≫ b₀) ≫ g.hom := by simp [Preadditive.comp_add]
          _ = ((L ≫ fstep Y (r + k) + u' ≫ g.natTrans.app (op (r + k)))
              ≫ Y.filtration.ι.app (op (r + k)) : W₃ ⟶ Y.X)
              + (e₃ ≫ e₂ ≫ b₀) ≫ g.hom := by rw [hsum]
          _ = _ := by
              simp only [Preadditive.add_comp, Category.assoc, fstep_comp_ι, g.comm (op (r + k))]
              abel

/-- The filtered object `(Y, d^{-1} F^• Y')`, i.e. `Y` filtered by the preimages under `d` of the
steps of the filtration of `Y'`. The morphism `d` is a *strict* morphism out of it by construction
(`isStrictHom_preimageFilD`), which is what makes [Stacks, Tag 05TR] applicable. -/
private noncomputable def preimageFil {Y Y' : FilteredObject 𝒜 ℤᵒᵖ} (d : Y ⟶ Y') :
    FilteredObject 𝒜 ℤᵒᵖ where
  X := Y.X
  filtration := ⟨Y'.filtration.toMonoOver ⋙ MonoOver.pullback d.hom⟩

/-- The morphism `d`, read out of the preimage filtration of `Y`. -/
private noncomputable def preimageFilD {Y Y' : FilteredObject 𝒜 ℤᵒᵖ} (d : Y ⟶ Y') :
    preimageFil d ⟶ Y' :=
  FilteredObject.homMk d.hom (fun i => pullback.fst (Y'.filtration.ι.app i) d.hom)
    (fun _ => pullback.condition)

/-- `d` is strict for the preimage filtration: its filtration squares are pullbacks by
construction. -/
private lemma isStrictHom_preimageFilD {Y Y' : FilteredObject 𝒜 ℤᵒᵖ} (d : Y ⟶ Y') :
    IsStrictHom (preimageFilD d) :=
  ⟨fun i => IsPullback.of_hasPullback (Y'.filtration.ι.app i) d.hom⟩

/-- **The extension step.** A morphism `φ : Y ⟶ X` of filtered objects killing the previous map
`g : Z ⟶ Y` extends along `d : Y ⟶ Y'`, when `gr Z → gr Y → gr Y'` is exact, the filtration of `Y`
is exhausted somewhere, and `X` is filtered injective with finite filtration: `φ` is filtered for
the preimage filtration `d^{-1} F^• Y'` by the strict exactness above, `d` is strict for that
filtration by construction, and [Stacks, Tag 05TR] extends `φ` along it. -/
private theorem exists_comp_eq_of_comp_eq_zero {Z Y Y' X : FilteredObject 𝒜 ℤᵒᵖ} (g : Z ⟶ Y)
    (d : Y ⟶ Y') (hgd : (g ≫ d).hom = 0)
    (hex : ∀ (q : ℤ) (w : grMap g q ≫ grMap d q = 0), (ShortComplex.mk _ _ w).Exact)
    {r : ℤ} (hr : IsIso (Y.filtration.ι.app (op r))) (hXfin : X.filtration.IsFinite)
    (hXinj : ∀ p : ℤ, Injective ((gr p).obj X)) (φ : Y ⟶ X)
    (hφ : (g ≫ φ).hom = 0) : ∃ ψ : Y' ⟶ X, d ≫ ψ = φ := by
  have hφ' : g.hom ≫ φ.hom = 0 := hφ
  have hdesc : ∀ i : ℤᵒᵖ, ∃ t : (preimageFil d).filtration.obj i ⟶ X.filtration.obj i,
      t ≫ X.filtration.ι.app i = (preimageFil d).filtration.ι.app i ≫ φ.hom := by
    intro i
    obtain ⟨q⟩ := i
    obtain ⟨W', e, he, a, b, h⟩ := refinesIntoMod_filtration g d hgd hex hr q
      (pullback.snd (Y'.filtration.ι.app (op q)) d.hom)
      (pullback.fst (Y'.filtration.ι.app (op q)) d.hom) pullback.condition.symm
    have := he
    have hstep : Y.filtration.ι.app (op q) ≫ φ.hom
        = φ.natTrans.app (op q) ≫ X.filtration.ι.app (op q) := (φ.comm (op q)).symm
    have hstep2 : Y.filtration.ι.app (op q) ≫ φ.hom
        ≫ cokernel.π (X.filtration.ι.app (op q)) = 0 := by
      rw [← Category.assoc, hstep, Category.assoc, cokernel.condition, comp_zero]
    have hφ2 : g.hom ≫ φ.hom ≫ cokernel.π (X.filtration.ι.app (op q)) = 0 := by
      rw [← Category.assoc, hφ', zero_comp]
    have hker : (pullback.snd (Y'.filtration.ι.app (op q)) d.hom ≫ φ.hom)
        ≫ cokernel.π (X.filtration.ι.app (op q)) = 0 := by
      rw [← cancel_epi e, comp_zero]
      simp only [← Category.assoc]
      rw [h]
      simp only [Preadditive.add_comp, Category.assoc, hstep2, hφ2, comp_zero, add_zero,
        ]
    exact ⟨_, (ShortComplex.exact_cokernel (X.filtration.ι.app (op q))).lift_f _ hker⟩
  have := isStrictHom_preimageFilD d
  obtain ⟨ψ, hψ⟩ := factors_of_isFilteredInjective
    (FilteredObject.homMk (F := preimageFil d) (G := X) φ.hom (fun i => (hdesc i).choose)
      (fun i => (hdesc i).choose_spec)) (preimageFilD d) ⟨hXfin, hXinj⟩
  refine ⟨ψ, FilteredObject.hom_ext ?_⟩
  have hψ' : d.hom ≫ ψ.hom = φ.hom := congrArg FilteredObject.Hom.hom hψ
  exact hψ'

/-! ### The exactness inputs of the two extension steps -/

/-- Taking the `q`-th graded piece commutes with taking the term in degree `n`, for the
differentials. -/
private lemma grEvalIso_hom_comp_grMap_evalD (K : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ)
    (q n : ℤ) : (grEvalIso K q n).hom ≫ grMap (evalD K n) q
      = (grObj K q).d n (n + 1) ≫ (grEvalIso K q (n + 1)).hom := by
  have hd : (cokernel.π (fstep K q)).f n ≫ (grObj K q).d n (n + 1)
      = (K.filtration.obj (op q)).d n (n + 1) ≫ (cokernel.π (fstep K q)).f (n + 1) :=
    (cokernel.π (fstep K q)).comm n (n + 1)
  have step₁ : (cokernel.π (fstep K q)).f n ≫ (grEvalIso K q n).hom ≫ grMap (evalD K n) q
      = (K.filtration.obj (op q)).d n (n + 1) ≫ cokernel.π (fstep (evalFil K (n + 1)) q) := by
    rw [← Category.assoc, π_grEvalIso_hom]
    exact π_grMap (evalD K n) q
  have step₂ : (cokernel.π (fstep K q)).f n ≫ (grObj K q).d n (n + 1) ≫ (grEvalIso K q (n + 1)).hom
      = (K.filtration.obj (op q)).d n (n + 1) ≫ cokernel.π (fstep (evalFil K (n + 1)) q) := by
    rw [← Category.assoc, hd, Category.assoc, π_grEvalIso_hom]
  have := epi_π_f K q n
  exact (cancel_epi ((cokernel.π (fstep K q)).f n)).mp (step₁.trans step₂.symm)

/-- The exactness input of the extension step at `J^{n + 1}`: exactness of the graded pieces of
`J^n → J^{n + 1} → J^{n + 2}`, which is the exactness of `gr^q J^•` in degree `n + 1`. -/
private lemma exact_grMap_evalD_of_exactAt {J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} (q n : ℤ)
    (hex : (grObj J q).ExactAt (n + 1))
    {w : grMap (evalD J n) q ≫ grMap (evalD J (n + 1)) q = 0} :
    (ShortComplex.mk _ _ w).Exact := by
  refine ShortComplex.exact_of_iso (ShortComplex.isoMk (grEvalIso J q n) (grEvalIso J q (n + 1))
    (grEvalIso J q (n + 1 + 1)) ?_ ?_)
    (((grObj J q).exactAt_iff' n (n + 1) (n + 1 + 1)
      (ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl))
      (ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel (n + 1) (n + 1 + 1) from rfl))).1 hex)
  · exact grEvalIso_hom_comp_grMap_evalD J q n
  · exact grEvalIso_hom_comp_grMap_evalD J q (n + 1)

/-- **Homology, Lemma 05S1**, in the second form the source's construction uses it. A
quasi-isomorphism `ψ : Z^• ⟶ Y^•` from a complex concentrated in degree `0` into a complex
vanishing in degree `-1` presents `Z^0` as the cocycles of `Y^•` in degree `0`: the sequence
`Z^0 → Y^0 → Y^1` is exact. -/
private lemma exact_f_zero_d_of_quasiIso {Z Y : CochainComplex 𝒜 ℤ} (ψ : Z ⟶ Y) [QuasiIso ψ]
    (hZ1 : IsZero (Z.X (0 + 1))) (hZm : IsZero (Z.X (-1))) (hYm : IsZero (Y.X (-1)))
    {w : ψ.f 0 ≫ Y.d 0 (0 + 1) = 0} : (ShortComplex.mk _ _ w).Exact := by
  have h₁ : IsIso (Z.iCycles 0) := Z.isIso_iCycles 0 (0 + 1) (by simp) (hZ1.eq_of_tgt _ _)
  have h₂ : IsIso (Z.homologyπ 0) := Z.isIso_homologyπ (-1) 0 (by simp) (hZm.eq_of_src _ _)
  have h₃ : IsIso (Y.homologyπ 0) := Y.isIso_homologyπ (-1) 0 (by simp) (hYm.eq_of_src _ _)
  have h₄ : IsIso (HomologicalComplex.homologyMap ψ 0) := inferInstance
  have h₅ : IsIso (HomologicalComplex.cyclesMap ψ 0) := by
    have e : IsIso (HomologicalComplex.cyclesMap ψ 0 ≫ Y.homologyπ 0) := by
      rw [← HomologicalComplex.homologyπ_naturality]; infer_instance
    exact IsIso.of_isIso_comp_right (HomologicalComplex.cyclesMap ψ 0) (Y.homologyπ 0)
  have hker : (ShortComplex.mk (Y.iCycles 0) (Y.d 0 (0 + 1)) (Y.iCycles_d 0 (0 + 1))).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (Y.cyclesIsKernel 0 (0 + 1) (by simp))
  refine ShortComplex.exact_of_iso
    (S₁ := ShortComplex.mk (Y.iCycles 0) (Y.d 0 (0 + 1)) (Y.iCycles_d 0 (0 + 1)))
    (ShortComplex.isoMk ((asIso (HomologicalComplex.cyclesMap ψ 0)).symm.trans
      (asIso (Z.iCycles 0))) (Iso.refl _) (Iso.refl _) ?_ ?_) hker
  · simp
  · simp

/-- The exactness input of the extension step at `J^0`: the graded pieces of `C^0 → J^0 → J^1` are
exact, because `gr^q J^•` is a resolution of `gr^q C^0`. -/
private lemma exact_grMap_zero_of_filteredQuasiIso {C J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0] [J.X.IsStrictlyGE 0] (c : C ⟶ J)
    (hc : CochainComplex.filteredQuasiIso 𝒜 c) (q : ℤ)
    {w : grMap ((evalFunctor 0).map c) q ≫ grMap (evalD J 0) q = 0} :
    (ShortComplex.mk _ _ w).Exact := by
  have hqi : QuasiIso (grMap c q) := hc q
  have hZ1 : IsZero ((grObj C q).X (0 + 1)) :=
    isZero_grObj_X (C.X.isZero_of_isStrictlyLE 0 (0 + 1) (by norm_num)) q
  have hZm : IsZero ((grObj C q).X (-1)) :=
    isZero_grObj_X (C.X.isZero_of_isStrictlyGE 0 (-1) (by norm_num)) q
  have hYm : IsZero ((grObj J q).X (-1)) :=
    isZero_grObj_X (J.X.isZero_of_isStrictlyGE 0 (-1) (by norm_num)) q
  have hw0 : (grMap c q).f 0 ≫ (grObj J q).d 0 (0 + 1) = 0 := by
    rw [(grMap c q).comm 0 (0 + 1), hZ1.eq_of_tgt ((grObj C q).d 0 (0 + 1)) 0, zero_comp]
  have hsrc : (ShortComplex.mk ((grMap c q).f 0) ((grObj J q).d 0 (0 + 1)) hw0).Exact :=
    exact_f_zero_d_of_quasiIso (grMap c q) hZ1 hZm hYm
  exact ShortComplex.exact_of_iso
    (S₁ := ShortComplex.mk ((grMap c q).f 0) ((grObj J q).d 0 (0 + 1)) hw0)
    (ShortComplex.isoMk (grEvalIso C q 0) (grEvalIso J q 0) (grEvalIso J q (0 + 1))
      (grEvalIso_hom_comp_grMap c q 0) (grEvalIso_hom_comp_grMap_evalD J q 0)) hsrc

/-- The strict exactness of the filtered resolution `c : C[0] ⟶ J^•` at `J^0`, tested against a
filtered injective object `X` with finite filtration: a morphism `J^0 ⟶ X` killing `C` extends
along `d_J^0`, because it factors through `Coker(c) = Coim(d_J^0) = Im(d_J^0)` and
`Im(d_J^0) ⟶ J^1` is a strict monomorphism, along which [Stacks, Tag 05TR] extends it. -/
theorem exists_comp_evalD_eq_of_map_comp_eq_zero
    {C J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    [J.X.IsStrictlyGE 0] (c : C ⟶ J) (hc : CochainComplex.filteredQuasiIso 𝒜 c)
    (_hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n))
    {X : FilteredObject 𝒜 ℤᵒᵖ} (hXfin : X.filtration.IsFinite)
    (hXinj : ∀ p : ℤ, Injective ((gr p).obj X))
    (φ : evalFil J 0 ⟶ X) (hφ : ((evalFunctor 0).map c ≫ φ).hom = 0) :
    ∃ ψ : evalFil J ((0 : ℤ) + 1) ⟶ X, evalD J 0 ≫ ψ = φ := by
  obtain ⟨pJ, -, hpJ, -⟩ := hJfin 0
  refine exists_comp_eq_of_comp_eq_zero ((evalFunctor 0).map c) (evalD J 0) ?_
    (fun q _ => exact_grMap_zero_of_filteredQuasiIso c hc q) (r := pJ) hpJ hXfin hXinj φ hφ
  show c.hom.f 0 ≫ J.X.d 0 (0 + 1) = 0
  rw [c.hom.comm 0 (0 + 1),
    (C.X.isZero_of_isStrictlyLE 0 (0 + 1) (by norm_num)).eq_of_tgt (C.X.d 0 (0 + 1)) 0, zero_comp]

/-- The strict exactness of the filtered resolution `c : C[0] ⟶ J^•` at `J^{n + 1}` for `n ≥ 0`,
tested against a filtered injective object `X` with finite filtration: a morphism `J^{n + 1} ⟶ X`
killing the image of `d_J^n` extends along `d_J^{n + 1}`, because it factors through
`Coim(d_J^{n + 1}) = Im(d_J^{n + 1})` and `Im(d_J^{n + 1}) ⟶ J^{n + 2}` is a strict monomorphism,
along which [Stacks, Tag 05TR] extends it. -/
theorem exists_comp_evalD_eq_of_evalD_comp_eq_zero
    {C J : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ} [C.X.IsStrictlyGE 0] [C.X.IsStrictlyLE 0]
    [J.X.IsStrictlyGE 0] (c : C ⟶ J) (hc : CochainComplex.filteredQuasiIso 𝒜 c)
    (_hC : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((C.filtration.ι.app (op p)).f n) ∧
      IsZero ((C.filtration.obj (op q)).X n))
    (hJfin : ∀ n : ℤ, ∃ p q : ℤ, IsIso ((J.filtration.ι.app (op p)).f n) ∧
      IsZero ((J.filtration.obj (op q)).X n))
    {X : FilteredObject 𝒜 ℤᵒᵖ} (hXfin : X.filtration.IsFinite)
    (hXinj : ∀ p : ℤ, Injective ((gr p).obj X))
    (n : ℤ) (hn : 0 ≤ n) (φ : evalFil J (n + 1) ⟶ X) (hφ : (evalD J n ≫ φ).hom = 0) :
    ∃ ψ : evalFil J (n + 1 + 1) ⟶ X, evalD J (n + 1) ≫ ψ = φ := by
  obtain ⟨pJ, -, hpJ, -⟩ := hJfin (n + 1)
  refine exists_comp_eq_of_comp_eq_zero (evalD J n) (evalD J (n + 1))
    (evalD_comp_evalD_hom J n) (fun q _ => ?_) (r := pJ) hpJ hXfin hXinj φ hφ
  refine exact_grMap_evalD_of_exactAt q n ?_
  have hqi : QuasiIso (grMap c q) := hc q
  exact (_root_.exactAt_iff_of_quasiIsoAt (grMap c q) (n + 1)).1
    (HomologicalComplex.ExactAt.of_isZero
      (isZero_grObj_X (C.X.isZero_of_isStrictlyLE 0 (n + 1) (by omega)) q))

end CochainComplex.FilteredInjective.TermwiseSplit

end FilteredTermwiseSplit

end

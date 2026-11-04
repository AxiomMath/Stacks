module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc

@[expose] public section

/-!
# The inclusion of a brutal truncation, and the tower it generates

Mathlib's `HomologicalComplex.stupidTrunc K e` is the *brutal* (or *stupid*) truncation of a
complex `K` along an embedding of complex shapes `e`: it keeps the terms of `K` in the image of
`e` and replaces the others by zero. When `e` is a truncation embedding onto a final segment
(`e.IsTruncGE`), the terms that were discarded sit in degrees *below* the retained ones, so the
retained differentials assemble into an honest subcomplex and there is a canonical inclusion
`σ^{≥a}K ⟶ K`. Mathlib records that inclusion only as a TODO, so it is built here.

For cochain complexes indexed by `ℤ` the embeddings `ComplexShape.embeddingUpIntGE a` give the
truncations `σ^{≥a}K`, and the inclusions above organise them into an increasing tower whose
successive quotients are single complexes: for every `p` there is a short exact sequence

`0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ) ⟶ 0`.

That sequence is the induction step behind several arguments — the hyper-Ext spectral sequence
and the K-flatness of a bounded above complex of flat modules among them — so it lives in its
own module rather than being duplicated privately by each consumer.

## Main definitions

* `StacksDraft.StupidTruncation.ιStupidTrunc`: the inclusion `K.stupidTrunc e ⟶ K`.
* `StacksDraft.StupidTruncation.liftStupidTrunc`: the factorisation of a map out of a complex
  strictly supported on `e` through `K.stupidTrunc e`.
* `StacksDraft.StupidTruncation.stupidTruncTower`: the tower `i ↦ σ^{≥ -i}K`, a functor
  `ℤ ⥤ CochainComplex C ℤ`.
* `StacksDraft.StupidTruncation.stupidTruncGEShortComplex`: the short complex
  `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ)`.

## Main results

* `StacksDraft.StupidTruncation.mono_ιStupidTrunc`: the inclusion is a monomorphism.
* `StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact`: the short complex above
  is short exact, being degreewise split.
* `StacksDraft.StupidTruncation.isIso_homologyMap_of_isIso_f_prev_next`: a morphism of
  complexes invertible in the three degrees that compute the degree-`i` homology is invertible
  on it.
* `StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE`: the inclusion
  `σ^{≥a}K ⟶ K` is an isomorphism on cohomology in every degree above `a`.
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.StupidTruncation

universe u v

section Inclusion

open HomologicalComplex ComplexShape

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex A c') (e : c.Embedding c')

/-- The inclusion of a stupid truncation is a monomorphism: degreewise it is either an
isomorphism or a map out of a zero object. -/
theorem mono_ιStupidTrunc [e.IsTruncGE] : Mono (ιStupidTrunc K e) := by
  refine mono_of_mono_f _ fun i' => ?_
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [ιStupidTrunc_f K e hi]
    infer_instance
  · exact (K.isZero_stupidTrunc_X e i' (by simpa using hi')).mono _

attribute [local instance] mono_ιStupidTrunc

/-- A map from a complex strictly supported on `e` factors through the corresponding stupid
truncation. -/
noncomputable def liftStupidTrunc [e.IsRelIff]
    {L : HomologicalComplex A c'} [L.IsStrictlySupported e] (f : L ⟶ K) :
    L ⟶ K.stupidTrunc e :=
  e.liftExtend (restrictionMap f e) (fun _ hj i' hij' ↦
    (L.isZero_X_of_isStrictlySupported e i' (hj.notMem hij')).eq_of_src _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The factorisation `liftStupidTrunc` is one: composing it with the inclusion returns the
original map. Since the inclusion is a monomorphism, this characterises it. -/
lemma liftStupidTrunc_ι [e.IsTruncGE]
    {L : HomologicalComplex A c'} [L.IsStrictlySupported e] (f : L ⟶ K) :
    liftStupidTrunc K e f ≫ ιStupidTrunc K e = f := by
  ext i'
  show (liftStupidTrunc K e f).f i' ≫ (ιStupidTrunc K e).f i' = f.f i'
  by_cases hi' : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := hi'
    rw [ιStupidTrunc_f K e hi]
    dsimp only [liftStupidTrunc]
    rw [e.liftExtend_f _ _ hi]
    subst hi
    simp only [stupidTruncXIso, restrictionXIso, restrictionMap, Iso.trans_hom,
      Category.assoc, Iso.inv_hom_id_assoc]
    show (𝟙 (L.X (e.f i))) ≫ f.f (e.f i) ≫ 𝟙 (K.X (e.f i)) = f.f (e.f i)
    simp only [Category.id_comp, Category.comp_id]
  · exact (L.isZero_X_of_isStrictlySupported e i' (by simpa using hi')).eq_of_src _ _

end Inclusion

attribute [local instance] mono_ιStupidTrunc

section Tower

open HomologicalComplex ComplexShape

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : CochainComplex C ℤ)

/-- The comparison `σ^{≥b}K ⟶ σ^{≥a}K` for `a ≤ b`: the larger truncation is strictly supported
in degrees `≥ a`, so its inclusion into `K` factors through `σ^{≥a}K`. -/
noncomputable def stupidTruncGEMapLE {a b : ℤ} (h : a ≤ b) :
    K.stupidTrunc (embeddingUpIntGE b) ⟶ K.stupidTrunc (embeddingUpIntGE a) := by
  letI := CochainComplex.isStrictlyGE_of_ge (K.stupidTrunc (embeddingUpIntGE b)) a b h
  exact liftStupidTrunc K (embeddingUpIntGE a) (ιStupidTrunc K (embeddingUpIntGE b))

/-- The comparisons of the tower are compatible with the inclusions into `K`. -/
lemma stupidTruncGEMapLE_ι {a b : ℤ} (h : a ≤ b) :
    stupidTruncGEMapLE K h ≫ ιStupidTrunc K (embeddingUpIntGE a) =
      ιStupidTrunc K (embeddingUpIntGE b) := by
  have := CochainComplex.isStrictlyGE_of_ge (K.stupidTrunc (embeddingUpIntGE b)) a b h
  apply liftStupidTrunc_ι

/-- The increasing tower whose term at `i` retains degrees at least `-i`.

Functoriality is forced: the inclusions into `K` are monomorphisms and, by
`stupidTruncGEMapLE_ι`, every comparison is determined by them. -/
noncomputable def stupidTruncTower : ℤ ⥤ CochainComplex C ℤ where
  obj i := K.stupidTrunc (embeddingUpIntGE (-i))
  map f := stupidTruncGEMapLE K (neg_le_neg (leOfHom f))
  map_id i := by
    apply (cancel_mono (ιStupidTrunc K (embeddingUpIntGE (-i)))).1
    simp only [stupidTruncGEMapLE_ι, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (ιStupidTrunc K (embeddingUpIntGE _))).1
    simp only [Category.assoc, stupidTruncGEMapLE_ι]

/-- In a retained degree `n ≥ a`, the term `(σ^{≥a}K)ⁿ` is identified with `Kⁿ`. -/
noncomputable abbrev stupidTruncGEXIso (a n : ℤ) (h : a ≤ n) :
    (K.stupidTrunc (embeddingUpIntGE a)).X n ≅ K.X n :=
  K.stupidTruncXIso (embeddingUpIntGE a) (i := (n - a).toNat)
    (by change a + ((n - a).toNat : ℤ) = n; omega)

/-- In a retained degree, the inclusion `σ^{≥a}K ⟶ K` is the identification of terms; in
particular it is an isomorphism there. -/
lemma ιStupidTruncGE_f (a n : ℤ) (h : a ≤ n) :
    (ιStupidTrunc K (embeddingUpIntGE a)).f n = (stupidTruncGEXIso K a n h).hom :=
  ιStupidTrunc_f K _ _

/-- In a degree retained by both truncations, the comparison `σ^{≥b}K ⟶ σ^{≥a}K` is an
isomorphism, namely the composite of the two identifications with `Kⁿ`. -/
lemma stupidTruncGEMapLE_f {a b : ℤ} (h : a ≤ b) (n : ℤ) (hn : b ≤ n) :
    (stupidTruncGEMapLE K h).f n = (stupidTruncGEXIso K b n hn).hom ≫
      (stupidTruncGEXIso K a n (h.trans hn)).inv := by
  apply (cancel_mono (stupidTruncGEXIso K a n (h.trans hn)).hom).1
  have eq := congrArg (fun f => f.f n) (stupidTruncGEMapLE_ι K h)
  simpa only [HomologicalComplex.comp_f, ιStupidTruncGE_f K a n (h.trans hn),
    ιStupidTruncGE_f K b n hn, Category.assoc, Iso.inv_hom_id, Category.comp_id] using eq

/-- The terms of `σ^{≥a}K` below `a` are zero. -/
private theorem isZero_stupidTruncGE_X (a n : ℤ) (h : n < a) :
    IsZero ((K.stupidTrunc (embeddingUpIntGE a)).X n) :=
  CochainComplex.isZero_of_isStrictlyGE _ a n h

/-- The projection of `σ^{≥p}K` onto its bottom term, viewed as a map to the single complex
`(single p).obj (Kᵖ)`. -/
noncomputable def stupidTruncGEπ (p : ℤ) :
    K.stupidTrunc (embeddingUpIntGE p) ⟶ (single C (.up ℤ) p).obj (K.X p) :=
  mkHomToSingle (stupidTruncGEXIso K p p le_rfl).hom (fun i hi ↦
    (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE p)) p i
      (by change i + 1 = p at hi; omega)).eq_of_src _ _)

/-- The degree-`p` component of the projection to the single complex. -/
lemma stupidTruncGEπ_f (p : ℤ) :
    (stupidTruncGEπ K p).f p = (stupidTruncGEXIso K p p le_rfl).hom ≫
      (singleObjXSelf (.up ℤ) p (K.X p)).inv :=
  mkHomToSingle_f _ _

/-- The short complex `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ)` exhibiting the bottom term of
a brutal truncation as its quotient by the next truncation. It is short exact; see
`stupidTruncGEShortComplex_shortExact`. -/
noncomputable def stupidTruncGEShortComplex (p : ℤ) :
    ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (stupidTruncGEMapLE K (show p ≤ p + 1 by omega)) (stupidTruncGEπ K p)
    (by
      apply to_single_hom_ext
      exact (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE (p + 1)))
        (p + 1) p (by omega)).eq_of_src _ _)

end Tower

section ShortExact

open HomologicalComplex ComplexShape

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)

/-- The sequence `0 ⟶ σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ (single p).obj (Kᵖ) ⟶ 0` is short exact.

It is checked degreewise, and in each degree it is split: in degree `p` the first term vanishes
and the projection is an isomorphism, while in every other degree the first map is an
isomorphism and the single complex vanishes. -/
lemma stupidTruncGEShortComplex_shortExact (p : ℤ) :
    (stupidTruncGEShortComplex K p).ShortExact := by
  refine shortExact_of_degreewise_shortExact _ fun n => ?_
  let S := (stupidTruncGEShortComplex K p).map (eval C (.up ℤ) n)
  show S.ShortExact
  by_cases hn : n = p
  · subst n
    apply (ShortComplex.Splitting.ofIsZeroOfIsIso S ?_ ?_).shortExact
    · exact isZero_stupidTruncGE_X K (p + 1) p (by omega)
    · show IsIso ((stupidTruncGEπ K p).f p)
      rw [stupidTruncGEπ_f]
      infer_instance
  · apply (ShortComplex.Splitting.ofIsIsoOfIsZero S ?_ ?_).shortExact
    · show IsIso ((stupidTruncGEMapLE K (show p ≤ p + 1 by omega)).f n)
      by_cases hpn : p < n
      · rw [stupidTruncGEMapLE_f K _ n (by omega)]
        infer_instance
      · exact IsZero.isIso (isZero_stupidTruncGE_X K (p + 1) n (by omega))
          (isZero_stupidTruncGE_X K p n (by omega)) _
    · exact isZero_single_obj_X (.up ℤ) p (K.X p) n hn

end ShortExact

section Cohomology

open HomologicalComplex ComplexShape

/-- A morphism of homological complexes which is invertible in the three degrees `c.prev i`,
`i` and `c.next i` is invertible on the degree-`i` homology: that homology is by construction
the homology of the short complex cut out by those three terms, and a morphism of short
complexes invertible in each of its three degrees is invertible. -/
theorem isIso_homologyMap_of_isIso_f_prev_next {A : Type u} [Category.{v} A] [Abelian A]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex A c} (f : K ⟶ L) (i : ι)
    (h₁ : IsIso (f.f (c.prev i))) (h₂ : IsIso (f.f i)) (h₃ : IsIso (f.f (c.next i))) :
    IsIso (HomologicalComplex.homologyMap f i) := by
  have e₁ : IsIso ((HomologicalComplex.shortComplexFunctor A c i).map f).τ₁ := h₁
  have e₂ : IsIso ((HomologicalComplex.shortComplexFunctor A c i).map f).τ₂ := h₂
  have e₃ : IsIso ((HomologicalComplex.shortComplexFunctor A c i).map f).τ₃ := h₃
  have : IsIso ((HomologicalComplex.shortComplexFunctor A c i).map f) :=
    ShortComplex.isIso_of_isIso _
  exact inferInstanceAs
    (IsIso (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor A c i).map f)))

/-- In a degree `n ≥ a`, the inclusion `σ^{≥a}K ⟶ K` is an isomorphism. -/
private theorem isIso_ιStupidTruncGE_f {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
    [HasZeroObject A] (K : CochainComplex A ℤ) (a n : ℤ) (h : a ≤ n) :
    IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f n) := by
  rw [ιStupidTruncGE_f K a n h]
  infer_instance

/-- **The inclusion of a brutal truncation is an isomorphism on cohomology above the truncation
degree.** For `i > a` the complexes `σ^{≥a}K` and `K` agree in the three consecutive degrees
`i - 1`, `i` and `i + 1` which compute cohomology in degree `i`, so `Hⁱ(σ^{≥a}K) ⟶ Hⁱ(K)` is an
isomorphism.

This is what lets an approximation of a complex be replaced by its brutal truncation in degrees
`≥ a` without losing the comparison of cohomology above `a`: the composite
`σ^{≥a}P ⟶ P ⟶ G` is again an isomorphism on cohomology wherever `P ⟶ G` was, above `a`. -/
theorem isIso_homologyMap_ιStupidTruncGE {A : Type u} [Category.{v} A] [Abelian A]
    (K : CochainComplex A ℤ) (a i : ℤ) (hi : a < i) :
    IsIso (HomologicalComplex.homologyMap (ιStupidTrunc K (embeddingUpIntGE a)) i) := by
  refine isIso_homologyMap_of_isIso_f_prev_next _ i ?_ ?_ ?_
  · rw [CochainComplex.prev]
    exact isIso_ιStupidTruncGE_f K a _ (by omega)
  · exact isIso_ιStupidTruncGE_f K a _ (by omega)
  · rw [CochainComplex.next]
    exact isIso_ιStupidTruncGE_f K a _ (by omega)

end Cohomology

end StacksDraft.StupidTruncation

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Basic

/-!
# Strict monomorphisms out of a filtered injective object split

A strict monomorphism `u : I ⟶ A` of filtered objects whose source is filtered injective
(`FilteredObject.IsFilteredInjective`: its filtration is finite and all of its graded pieces
`gr^p I = F^p I / F^{p + 1} I` are injective objects of `𝒜`) admits a retraction in the category of
filtered objects.

The top piece of the filtration of `I` is split off and the argument descends on the length of that
filtration. The induction runs on the assertion `HasRetractionAt u q` that some morphism
`r : A ⟶ I` of filtered objects satisfies `F^q(u) ≫ F^q(r) = 𝟙 (F^q I)`. If `F^q I = 0` then
`HasRetractionAt u q` holds for the zero morphism, and it follows from `HasRetractionAt u (q + 1)`:
the defect `e = 𝟙 - F^q(u) ≫ F^q(r)` of `r` at `q` vanishes on `F^{q + 1} I` by the inductive
hypothesis, so it extends along the map `F^q I ⟶ A / F^{q + 1} A` induced by `u` to some
`σ : A / F^{q + 1} A ⟶ F^q I`, and the morphism of filtered objects attached to `σ` — supported in
degrees `≤ q` — corrects `r` at `q`. Since `F^n I = I` for `n` small and `F^m I = 0` for `m` large,
finitely many corrections give a morphism `r` with `F^n(u) ≫ F^n(r) = 𝟙`, and `F^n I ≅ I` turns
this into `u ≫ r = 𝟙 I`.

The extension of `e` (`exists_comp_eq_of_injective_gradedPiece`) is where the two hypotheses on `I`
meet, and it is the one statement the proof rests on. Vanishing on `F^{q + 1} I` makes `e` factor
through `gr^q I`. Strictness of `u` at `q + 1` makes `F^{q + 1} I` the kernel of
`F^q I ⟶ A / F^{q + 1} A` — the appeal to [Stacks, Tag 0127] — so that sequence is exact and the
induced map `gr^q I ⟶ A / F^{q + 1} A` is a monomorphism; injectivity of `gr^q I` retracts it, and
composing the retraction with the factorisation of `e` produces `σ`.

The zero morphism and the sum of two morphisms are those of the preadditive category of filtered
objects ([Stacks, Tag 0122]); only their level `q` components enter the proof.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]


section FilteredInjectiveSplitting

namespace CategoryTheory.FilteredObject.Splitting

open CategoryTheory Limits Opposite FilteredObject

section

variable {𝒜 : Type u} [Category.{v} 𝒜] {I A : FilteredObject 𝒜 ℤᵒᵖ}

/-- `HasRetractionAt u q` asserts that some morphism `r : A ⟶ I` of filtered objects retracts `u`
at `q`, i.e. satisfies `F^q(u) ≫ F^q(r) = 𝟙 (F^q I)`. This is the assertion the source's induction
on the length of the filtration of `I` runs on. -/
private abbrev HasRetractionAt (u : I ⟶ A) (q : ℤ) : Prop :=
  ∃ r : A ⟶ I, u.natTrans.app (op q) ≫ r.natTrans.app (op q) = 𝟙 _

/-- A morphism of filtered objects retracting `u` at an index `n` where the filtration of `I`
exhausts `I` is a retraction of `u`: the compatibilities of `u` and `r` with the epimorphism
`F^n I ⟶ I` turn `F^n(u) ≫ F^n(r) = 𝟙` into `u ≫ r = 𝟙 I`. -/
private lemma isSplitMono_of_hasRetractionAt (u : I ⟶ A) {n : ℤ}
    (hn : IsIso (I.filtration.ι.app (op n))) (h : HasRetractionAt u n) : IsSplitMono u := by
  obtain ⟨r, hr⟩ := h
  refine IsSplitMono.mk ⟨⟨r, hom_ext ?_⟩⟩
  rw [comp_hom, id_hom, ← cancel_epi (I.filtration.ι.app (op n)), ← Category.assoc, ← u.comm,
    Category.assoc, ← r.comm, ← Category.assoc, hr, Category.id_comp]
  simp

end

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] {I A : FilteredObject 𝒜 ℤᵒᵖ}

/-- The inclusion `F^{q + 1} X ⟶ F^q X` of consecutive steps of a filtration. The graded piece
`gr^q X` is by construction its cokernel, so `(gr q).obj X = cokernel (ιSucc X q)`
holds by definition. -/
private abbrev ιSucc (X : FilteredObject 𝒜 ℤᵒᵖ) (q : ℤ) :
    X.filtration.obj (op (q + 1)) ⟶ X.filtration.obj (op q) :=
  X.filtration.diagram.map (homOfLE (Int.le_add_one le_rfl) : (q : ℤ) ⟶ q + 1).op

/-- The map `F^q I ⟶ A / F^{q + 1} A` induced by a morphism `u : I ⟶ A` of filtered objects. Its
kernel is `F^{q + 1} I` as soon as `u` is strict, and it is the map along which the defect of a
partial retraction of `u` is extended. -/
private noncomputable abbrev toQuotient (u : I ⟶ A) (q : ℤ) :
    I.filtration.obj (op q) ⟶ cokernel (A.filtration.ι.app (op (q + 1))) :=
  I.filtration.ι.app (op q) ≫ u.hom ≫ cokernel.π _

/-- The map `F^q I ⟶ A / F^{q + 1} A` induced by `u` vanishes on `F^{q + 1} I`, since `u` carries
`F^{q + 1} I` into `F^{q + 1} A`. -/
private lemma ιSucc_comp_toQuotient (u : I ⟶ A) (q : ℤ) : ιSucc I q ≫ toQuotient u q = 0 := by
  rw [← Category.assoc, I.filtration.diagram_map_comp_ι_app _, ← Category.assoc, ← u.comm,
    Category.assoc, cokernel.condition, comp_zero]

/-- **Homology, Lemma 0127.** For a strict morphism `u : I ⟶ A` of filtered objects the sequence
`F^{q + 1} I ⟶ F^q I ⟶ A / F^{q + 1} A` is exact: a map to `F^q I` whose composite to
`A / F^{q + 1} A` vanishes lands in `F^{q + 1} A`, hence — by strictness of `u` at `q + 1`, which
makes `F^{q + 1} I` the pullback of `F^{q + 1} A` along `u` — in `F^{q + 1} I`. -/
private lemma exact_toQuotient (u : I ⟶ A) [IsStrictHom u] (q : ℤ) :
    (ShortComplex.mk (ιSucc I q) (toQuotient u q) (ιSucc_comp_toQuotient u q)).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun {W} k hk => ?_)
  have hk' : (k ≫ I.filtration.ι.app (op q) ≫ u.hom) ≫
      cokernel.π (A.filtration.ι.app (op (q + 1))) = 0 := by simpa using hk
  have hp := IsStrictHom.isPullback u (op (q + 1))
  refine ⟨hp.lift (Abelian.monoLift _ _ hk') (k ≫ I.filtration.ι.app (op q)) ?_, ?_⟩
  · rw [Category.assoc]
    exact Abelian.monoLift_comp _ _ hk'
  · rw [← cancel_mono (I.filtration.ι.app (op q)), Category.assoc,
      I.filtration.diagram_map_comp_ι_app _, hp.lift_snd]

/-- **The extension lemma.** Let `u : I ⟶ A` be a strict morphism of filtered objects whose graded
piece `gr^q I` is injective. Then every morphism `e : F^q I ⟶ T` vanishing on `F^{q + 1} I`
extends along `F^q I ⟶ A / F^{q + 1} A`, i.e. `e = toQuotient u q ≫ σ` for some
`σ : A / F^{q + 1} A ⟶ T`.

This is where the two hypotheses of Tag 05TQ meet: `e` descends to `gr^q I`, strictness makes
`gr^q I ⟶ A / F^{q + 1} A` a monomorphism, and injectivity of `gr^q I` retracts it. -/
private lemma exists_comp_eq_of_injective_gradedPiece (u : I ⟶ A) [IsStrictHom u] (q : ℤ)
    (hgr : Injective ((gr q).obj I)) {T : 𝒜} (e : I.filtration.obj (op q) ⟶ T)
    (he : ιSucc I q ≫ e = 0) :
    ∃ σ : cokernel (A.filtration.ι.app (op (q + 1))) ⟶ T, toQuotient u q ≫ σ = e := by
  -- `gr^q I` is by construction the cokernel of `ιSucc I q`.
  have : Injective (cokernel (ιSucc I q)) := hgr
  set m := cokernel.desc (ιSucc I q) (toQuotient u q) (ιSucc_comp_toQuotient u q)
  have : Mono m := (exact_toQuotient u q).mono_cokernelDesc
  refine ⟨Injective.factorThru (𝟙 _) m ≫ cokernel.desc (ιSucc I q) e he, ?_⟩
  have hπ : toQuotient u q = cokernel.π (ιSucc I q) ≫ m := (cokernel.π_desc _ _ _).symm
  rw [hπ, Category.assoc, ← Category.assoc m, Injective.comp_factorThru, Category.id_comp,
    cokernel.π_desc]

/-- The morphism of filtered objects `A ⟶ I` attached to a map `σ : A / F^{q + 1} A ⟶ F^q I`,
namely `A ⟶ A / F^{q + 1} A ⟶ F^q I ⟶ I`. Its levelwise components are the composites
`F^p A ⟶ A / F^{q + 1} A ⟶ F^q I ⟶ F^p I` for `p ≤ q` and zero for `p > q`, which is what makes
it a morphism of filtered objects: it is the source's `s' : A ⟶ I'` with `I'` the filtered object
supported in degrees `≤ q`. -/
private noncomputable def truncHom (q : ℤ)
    (σ : cokernel (A.filtration.ι.app (op (q + 1))) ⟶ I.filtration.obj (op q)) : A ⟶ I :=
  homMk (cokernel.π _ ≫ σ ≫ I.filtration.ι.app (op q))
    (fun i => if h : unop i ≤ q then
      A.filtration.ι.app i ≫ cokernel.π _ ≫ σ ≫ I.filtration.diagram.map (homOfLE h).op else 0)
    (by
      intro i
      obtain ⟨p⟩ := i
      by_cases h : p ≤ q
      · simp only [h, dite_true, Category.assoc, Filtration.diagram_map_comp_ι_app]
      · simp only [h, dite_false, zero_comp]
        rw [← A.filtration.diagram_map_comp_ι_app (homOfLE (show q + 1 ≤ p by omega)).op,
          Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero])

/-- The level `q` component of `truncHom q σ`, precomposed with `u`, is `toQuotient u q ≫ σ`. -/
private lemma comp_truncHom_natTrans_app (u : I ⟶ A) (q : ℤ)
    (σ : cokernel (A.filtration.ι.app (op (q + 1))) ⟶ I.filtration.obj (op q)) :
    u.natTrans.app (op q) ≫ (truncHom q σ).natTrans.app (op q) = toQuotient u q ≫ σ := by
  simp [truncHom]

/-- The defect at `q` of a morphism `r : A ⟶ I` retracting `u` at `q + 1` vanishes on
`F^{q + 1} I`: the defect is natural in the index, and at `q + 1` it is zero. -/
private lemma ιSucc_comp_defect (u : I ⟶ A) (r : A ⟶ I) {q : ℤ}
    (hr : u.natTrans.app (op (q + 1)) ≫ r.natTrans.app (op (q + 1)) = 𝟙 _) :
    ιSucc I q ≫ (𝟙 _ - u.natTrans.app (op q) ≫ r.natTrans.app (op q)) = 0 := by
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, u.natTrans.naturality,
    Category.assoc, r.natTrans.naturality, ← Category.assoc, hr, Category.id_comp, sub_self]

/-- Correcting `r` by `truncHom q σ` adds `toQuotient u q ≫ σ` to the level `q` component of
`F^q(u) ≫ F^q(r)`, so a `σ` extending the defect of `r` at `q` corrects `r` to a retraction of `u`
at `q`. -/
private lemma hasRetractionAt_of_comp_eq_defect (u : I ⟶ A) (r : A ⟶ I) (q : ℤ)
    (σ : cokernel (A.filtration.ι.app (op (q + 1))) ⟶ I.filtration.obj (op q))
    (hσ : toQuotient u q ≫ σ = 𝟙 _ - u.natTrans.app (op q) ≫ r.natTrans.app (op q)) :
    HasRetractionAt u q := by
  refine ⟨r + truncHom q σ, ?_⟩
  rw [add_natTrans_app, Preadditive.comp_add, comp_truncHom_natTrans_app, hσ]
  abel

/-- The inductive step of the source's induction: a morphism of filtered objects retracting `u` at
`q + 1` is corrected to one retracting `u` at `q`, by extending its defect
`e = 𝟙 - F^q(u) ≫ F^q(r)` — which vanishes on `F^{q + 1} I` — along `F^q I ⟶ A / F^{q + 1} A`. -/
private lemma hasRetractionAt_of_succ (u : I ⟶ A) [IsStrictHom u] {q : ℤ}
    (hgr : Injective ((gr q).obj I)) (h : HasRetractionAt u (q + 1)) :
    HasRetractionAt u q := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨σ, hσ⟩ := exists_comp_eq_of_injective_gradedPiece u q hgr _ (ιSucc_comp_defect u r hr)
  exact hasRetractionAt_of_comp_eq_defect u r q σ hσ

/-- The source's induction on the length `k` of the filtration of `I`: if `F^{q + k} I = 0` then
`u` admits a retraction at `q`. -/
private lemma hasRetractionAt_of_isZero (u : I ⟶ A) [IsStrictHom u]
    (hgr : ∀ p : ℤ, Injective ((gr p).obj I)) (k : ℕ) (q : ℤ)
    (hk : IsZero (I.filtration.obj (op (q + (k : ℤ))))) : HasRetractionAt u q := by
  induction k generalizing q with
  | zero => exact ⟨0, IsZero.eq_of_src (by simpa using hk) _ _⟩
  | succ k ih =>
    exact hasRetractionAt_of_succ u (hgr q)
      (ih (q + 1) (I.filtration.isZero_obj_of_le (by omega) hk))

end

end CategoryTheory.FilteredObject.Splitting

namespace CategoryTheory.FilteredObject

open Splitting in
/-- **Stacks 05TQ.** Let `𝒜` be an abelian category. A strict monomorphism `u : I ⟶ A` of
filtered objects of `𝒜` whose source `I` is a filtered injective object of `Fil^f(𝒜)` — its
filtration is finite and every graded piece `gr^p(I) = F^p I / F^{p + 1} I` is an injective object
of `𝒜` — is a split monomorphism: it admits a retraction in the category of filtered objects. -/
@[stacks 05TQ]
public theorem isSplitMono_of_isFilteredInjective {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {I A : FilteredObject 𝒜 ℤᵒᵖ} (u : I ⟶ A) [IsStrictHom u] (hI : I.IsFilteredInjective) :
    IsSplitMono u := by
  obtain ⟨n, hn⟩ := hI.isFinite.exists_isIso_ι
  obtain ⟨m, hm⟩ := hI.isFinite.exists_isZero_obj
  exact isSplitMono_of_hasRetractionAt u hn (hasRetractionAt_of_isZero u hI.injective_gr
    (m - n).toNat n (I.filtration.isZero_obj_of_le (by omega) hm))

end CategoryTheory.FilteredObject

end FilteredInjectiveSplitting

end

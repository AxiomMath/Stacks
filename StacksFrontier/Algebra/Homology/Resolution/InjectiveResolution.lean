module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.Resolution.Defs.InjectiveResolution
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Existence of injective resolutions, and morphisms into K-injective complexes

Let `A` be an abelian category. A cochain complex `K` of `A` is quasi-isomorphic to a complex
vanishing in the degrees `< n` exactly when its cohomology vanishes in those degrees, the
canonical truncation `τ_{≥ n} K` being the witness. If `A` has enough injectives, such a `K`
moreover has an injective resolution whose resolving complex again vanishes below `n`, with a
degreewise monomorphic resolution map as soon as `K` itself vanishes below `n`.

A morphism `γ : K ⟶ I` into a K-injective complex factors through any quasi-isomorphism
`α : K ⟶ L` up to homotopy: precomposition with `α` is a bijection
`Mor_{K(A)}(L, I) → Mor_{K(A)}(K, I)`, so the factorization is unique up to homotopy. When moreover
the terms of `I` are injective and `α` is a monomorphism in every degree, the factorization holds
on the nose.

Resolutions can be chosen compatibly along a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
bounded below complexes: given any injective resolution `I₁` of `X₁`, there are resolutions `I₂`
of `X₂` and `I₃` of `X₃` fitting into a short exact sequence `0 ⟶ I₁ ⟶ I₂ ⟶ I₃ ⟶ 0` of resolving
complexes with both squares commuting.

## Main results

* `CochainComplex.isGE_iff_exists_quasiIso_isStrictlyGE`: the cohomology of `K` vanishes in
  degrees `< n` if and only if `K` admits a quasi-isomorphism to a complex that is zero in
  degrees `< n`.
* `CochainComplex.exists_injectiveResolution_isStrictlyGE`: a complex whose cohomology vanishes
  in degrees `< a` over a category with enough injectives has an injective resolution which is
  zero in degrees `< a`, degreewise monomorphic if `K` is zero in degrees `< a`.
* `CochainComplex.bijective_precomp_quotient_map`: precomposition with a quasi-isomorphism is a
  bijection on morphisms of the homotopy category into a K-injective complex.
* `CochainComplex.IsKInjective.exists_factorization_of_quasiIso`: a morphism to a K-injective
  complex factors through a quasi-isomorphism, up to homotopy, and on the nose when the terms of
  the target are injective and the quasi-isomorphism is a monomorphism in every degree.
* `CochainComplex.IsKInjective.nonempty_homotopy_of_precomp_quasiIso`: that factorization is
  unique up to homotopy.
* `CategoryTheory.ShortComplex.ShortExact.exists_shortExact_injectiveResolution`: a short exact
  sequence of bounded below complexes, together with a given injective resolution of its first
  term, extends to a short exact sequence of injective resolutions, with the degree bound
  inherited by the two resolutions that are constructed.

## References

* [Stacks, Tag 013J](https://stacks.math.columbia.edu/tag/013J)
* [Stacks, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
* [Stacks, Tag 013P](https://stacks.math.columbia.edu/tag/013P)
* [Stacks, Tag 013R](https://stacks.math.columbia.edu/tag/013R)
* [Stacks, Tag 013S](https://stacks.math.columbia.edu/tag/013S)
* [Stacks, Tag 05T6](https://stacks.math.columbia.edu/tag/05T6)
* [Stacks, Tag 05TF](https://stacks.math.columbia.edu/tag/05TF)
* [Stacks, Tag 05TG](https://stacks.math.columbia.edu/tag/05TG)
* [Stacks, Tag 070I](https://stacks.math.columbia.edu/tag/070I)
-/

@[expose] public section

universe w v u

open CategoryTheory Limits

section Homotopy

variable {ι : Type*} {V : Type u} [Category.{v} V] [Preadditive V] {c : ComplexShape ι}
  {K L I : HomologicalComplex V c}

/-- A homotopy in a factorization through a degreewise monomorphism can be removed when the
target has injective terms: if `α` is a monomorphism in every degree, every term of `I` is an
injective object and `α ≫ β₀` is homotopic to `γ`, then `γ = α ≫ β` for some `β`. -/
private lemma Homotopy.exists_comp_eq [∀ n, Injective (I.X n)] {α : K ⟶ L} [∀ n, Mono (α.f n)]
    {β₀ : L ⟶ I} {γ : K ⟶ I} (h : Homotopy (α ≫ β₀) γ) :
    ∃ β : L ⟶ I, α ≫ β = γ :=
  ⟨β₀ - nullHomotopicMap fun i j ↦ Injective.factorThru (h.hom i j) (α.f i), by
    rw [Preadditive.comp_sub, comp_nullHomotopicMap,
      funext₂ fun i j ↦ Injective.comp_factorThru (h.hom i j) (α.f i),
      ← h.sub_eq_nullHomotopicMap, sub_sub_cancel]⟩

end Homotopy

namespace CochainComplex

/-- Let `C` be a category with zero morphisms, a zero object and homology for every short complex,
and let `K` be a cochain complex of `C`. The cohomology of `K` vanishes in all degrees `< n` if and
only if there is a quasi-isomorphism `f : K ⟶ L` with `L` zero in all degrees `< n`. -/
@[stacks 013J]
public theorem isGE_iff_exists_quasiIso_isStrictlyGE {C : Type*} [Category C]
    [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.IsGE n ↔ ∃ (L : CochainComplex C ℤ) (f : K ⟶ L) (_ : QuasiIso f), L.IsStrictlyGE n := by
  refine ⟨fun _ ↦ ⟨K.truncGE n, K.πTruncGE n, inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨L, f, _, _⟩
  exact (HomologicalComplex.isSupported_iff_of_quasiIso f
    (ComplexShape.embeddingUpIntGE n)).2 inferInstance

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Let `A` be an abelian category with enough injectives, let `a : ℤ` and let `K` be a cochain
complex of `A` with `H ^ n (K) = 0` for `n < a`. Then `K` has an injective resolution `R` whose
resolving complex satisfies `R.cocomplex.X n = 0` for `n < a`; and if moreover `K.X n = 0` for
`n < a`, then `R` can be chosen with all the components `R.ι.f n : K.X n ⟶ R.cocomplex.X n`
monomorphisms. -/
@[stacks 013K, sga "4½ Etat_0 3.2.3" "(4) existence", sga "4½ Etat_0 4.2.3.1" "Corollary 1"]
public theorem exists_injectiveResolution_isStrictlyGE [EnoughInjectives A] (a : ℤ)
    (K : CochainComplex A ℤ) [K.IsGE a] :
    ∃ (R : K.InjectiveResolution) (_ : K.IsStrictlyGE a → ∀ n, Mono (R.ι.f n)),
      R.cocomplex.IsStrictlyGE a := by
  obtain ⟨L, f, hf, hinj, hmono, hLGE⟩ :=
    exists_quasiIso_prop_isStrictlyGE (isInjective A)
      (fun X ↦ ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩) a K
  exact ⟨{ cocomplex := L
           boundedBelow := (plus_iff A L).2 ⟨a, hLGE⟩
           injective := hinj
           ι := f
           quasiIso := hf }, hmono, hLGE⟩

section KInjective

variable {K L I : CochainComplex A ℤ}

/-- If `I` is a K-injective cochain complex and `α : K ⟶ L` is a quasi-isomorphism, then
precomposition with the image of `α` in the homotopy category `K(A)` is a bijection
`Hom_{K(A)}(L, I) → Hom_{K(A)}(K, I)`. -/
@[stacks 05TF]
lemma bijective_precomp_quotient_map [I.IsKInjective] (α : K ⟶ L) [QuasiIso α] :
    Function.Bijective (fun β : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I =>
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map α ≫ β) := by
  have hI := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hI
  refine hI _ ?_
  rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    HomotopyCategory.quotient_map_mem_quasiIso_iff]
  exact ⟨inferInstance⟩

/-- A morphism `γ : K ⟶ I` to a K-injective complex factors, up to homotopy, through any
quasi-isomorphism `α : K ⟶ L`. -/
private lemma exists_nonempty_homotopy_comp [I.IsKInjective] (α : K ⟶ L) [QuasiIso α]
    (γ : K ⟶ I) : ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := by
  obtain ⟨β, hβ⟩ := (bijective_precomp_quotient_map α).2
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map γ)
  obtain ⟨β, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective β
  exact ⟨β, ⟨HomotopyCategory.homotopyOfEq _ _ (by rw [Functor.map_comp]; exact hβ)⟩⟩

/-- Let `A` be an abelian category, let `α : K ⟶ L` be a quasi-isomorphism of cochain complexes of
`A`, let `I` be a K-injective cochain complex of `A` and let `γ : K ⟶ I`. Then (1) there is a
morphism of complexes `β : L ⟶ I` such that `α ≫ β` is homotopic to `γ`, and (2) if every term of
`I` is an injective object and `α` is a monomorphism in every degree, then there is a `β` with
`α ≫ β = γ`. -/
@[stacks 013P "for a K-injective target, which by 013R covers the source's hypothesis that the \
  target be bounded below with injective terms; the extra hypotheses of part (2) are attached to \
  its own conjunct", sga "2 VIII 1.4" "existence of Cu"]
public theorem IsKInjective.exists_factorization_of_quasiIso [I.IsKInjective] (α : K ⟶ L)
    [QuasiIso α] (γ : K ⟶ I) :
    (∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ)) ∧
      (∀ [∀ n, Injective (I.X n)] [∀ n, Mono (α.f n)], ∃ β : L ⟶ I, α ≫ β = γ) := by
  refine ⟨exists_nonempty_homotopy_comp α γ, ?_⟩
  intro _ _
  obtain ⟨_, ⟨h⟩⟩ := exists_nonempty_homotopy_comp α γ
  exact h.exists_comp_eq

/-- Let `A` be an abelian category, let `α : K ⟶ L` be a quasi-isomorphism of cochain complexes of
`A` and let `I` be a K-injective cochain complex of `A`. Then two morphisms `β₁, β₂ : L ⟶ I` with
`α ≫ β₁` homotopic to `α ≫ β₂` are homotopic. -/
@[stacks 013S "for a K-injective target, which by Tag 013R covers the source's bounded below \
  complex of injective objects; the source's intermediary `γ : K ⟶ I` is eliminated by \
  transitivity of homotopy", sga "2 VIII 1.4" "uniqueness of Cu"]
public theorem IsKInjective.nonempty_homotopy_of_precomp_quasiIso [I.IsKInjective] (α : K ⟶ L)
    [QuasiIso α] {β₁ β₂ : L ⟶ I} (h : Homotopy (α ≫ β₁) (α ≫ β₂)) :
    Nonempty (Homotopy β₁ β₂) :=
  ⟨HomotopyCategory.homotopyOfEq _ _ <| (bijective_precomp_quotient_map α).injective <| by
    simpa only [← Functor.map_comp] using HomotopyCategory.eq_of_homotopy _ _ h⟩

end KInjective

end CochainComplex

add_to_stacks 05TG "the bijection `Mor_{K(A)}(K, I) → Mor_{D(A)}(K, I)` for a K-injective `I`"
  CochainComplex.IsKInjective.Qh_map_bijective
add_to_stacks 05TG "a complex strictly bounded below with injective terms is K-injective"
  CochainComplex.isKInjective_of_injective

section FiveLemma

variable {V : Type u} [Category.{v} V] [Abelian V] {ι : Type*} {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex V c)}

open HomologicalComplex HomologySequence ComposableArrows

/-- The exact sequence `H_i(X₃) ⟶ H_j(X₁) ⟶ H_j(X₂) ⟶ H_j(X₃) ⟶ H_k(X₁)` attached to a short
exact sequence `S` of homological complexes and to degrees `i`, `j`, `k` with `c.Rel i j` and
`c.Rel j k`. -/
private noncomputable def composableArrows₄ (hS : S₁.ShortExact) (i j k : ι) (hij : c.Rel i j)
    (hjk : c.Rel j k) : ComposableArrows V 4 :=
  mk₄ (hS.δ i j hij) (HomologicalComplex.homologyMap S₁.f j)
    (HomologicalComplex.homologyMap S₁.g j) (hS.δ j k hjk)

private lemma composableArrows₄_exact (hS : S₁.ShortExact) (i j k : ι) (hij : c.Rel i j)
    (hjk : c.Rel j k) : (composableArrows₄ hS i j k hij hjk).Exact :=
  exact_of_δ₀ (hS.homology_exact₁ i j hij).exact_toComposableArrows
    (exact_of_δ₀ (hS.homology_exact₂ j).exact_toComposableArrows
      (hS.homology_exact₃ j k hjk).exact_toComposableArrows)

/-- The morphism of exact sequences `composableArrows₄ hS₁ ⟶ composableArrows₄ hS₂` induced by a
morphism `φ : S₁ ⟶ S₂` of short exact sequences of homological complexes. -/
private noncomputable def mapComposableArrows₄ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact)
    (hS₂ : S₂.ShortExact) (i j k : ι) (hij : c.Rel i j) (hjk : c.Rel j k) :
    composableArrows₄ hS₁ i j k hij hjk ⟶ composableArrows₄ hS₂ i j k hij hjk :=
  homMk₄ (HomologicalComplex.homologyMap φ.τ₃ i) (HomologicalComplex.homologyMap φ.τ₁ j)
    (HomologicalComplex.homologyMap φ.τ₂ j) (HomologicalComplex.homologyMap φ.τ₃ j)
    (HomologicalComplex.homologyMap φ.τ₁ k)
    (δ_naturality φ hS₁ hS₂ i j hij)
    (naturality' (mapComposableArrows₂ φ j) 0 1)
    (naturality' (mapComposableArrows₂ φ j) 1 2)
    (δ_naturality φ hS₁ hS₂ j k hjk)

/-- The five lemma for the middle term: if `φ : S₁ ⟶ S₂` is a morphism of short exact sequences of
homological complexes whose degrees each have a predecessor and a successor, and if `φ.τ₁` and
`φ.τ₃` are quasi-isomorphisms, then so is `φ.τ₂`. -/
private lemma quasiIso_τ₂ (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (hprev : ∀ j, ∃ i, c.Rel i j) (hnext : ∀ j, ∃ k, c.Rel j k)
    (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) : QuasiIso φ.τ₂ := by
  have := h₁
  have := h₃
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨i, hij⟩ := hprev j
  obtain ⟨k, hjk⟩ := hnext j
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (composableArrows₄_exact hS₁ i j k hij hjk) (composableArrows₄_exact hS₂ i j k hij hjk)
    (mapComposableArrows₄ φ hS₁ hS₂ i j k hij hjk)
    (inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₃ i)))
    (inferInstanceAs (IsIso (HomologicalComplex.homologyMap φ.τ₁ j)))
    (inferInstanceAs (IsIso (HomologicalComplex.homologyMap φ.τ₃ j)))
    (inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₁ k)))

end FiveLemma

section Bounds

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

/-- A degreewise epimorphic image of a cochain complex vanishing in the degrees `< a` vanishes in
the degrees `< a`. -/
private lemma isStrictlyGE_of_epi {X Y : CochainComplex V ℤ} (g : X ⟶ Y) [∀ n, Epi (g.f n)] (a : ℤ)
    [X.IsStrictlyGE a] : Y.IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (g.f i)]
  simp [(X.isZero_of_isStrictlyGE a i hi).eq_of_src (g.f i) 0]

end Bounds

section Twist

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  {P Q : CochainComplex V ℤ}

private lemma twist_isStrictlyGE (δ : Q ⟶ P⟦(1 : ℤ)⟧) (b : ℤ) [P.IsStrictlyGE b]
    [Q.IsStrictlyGE b] : (CochainComplex.twist δ).IsStrictlyGE b := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.twist_X, biprod_isZero_iff]
  exact ⟨P.isZero_of_isStrictlyGE b i hi, Q.isZero_of_isStrictlyGE b i hi⟩

/-- The twisted direct sum of two bounded below complexes is bounded below. -/
private lemma twist_plus (δ : Q ⟶ P⟦(1 : ℤ)⟧) (hP : CochainComplex.plus V P)
    (hQ : CochainComplex.plus V Q) : CochainComplex.plus V (CochainComplex.twist δ) := by
  obtain ⟨b, _⟩ := (CochainComplex.plus_iff V P).1 hP
  obtain ⟨b', _⟩ := (CochainComplex.plus_iff V Q).1 hQ
  have := P.isStrictlyGE_of_ge (min b b') b (min_le_left b b')
  have := Q.isStrictlyGE_of_ge (min b b') b' (min_le_right b b')
  exact (CochainComplex.plus_iff V _).2 ⟨min b b', twist_isStrictlyGE δ (min b b')⟩

end Twist

section TwistLift

variable {V : Type u} [Category.{v} V] [Preadditive V] [HasBinaryBiproducts V]
  {P Q X Y : CochainComplex V ℤ} (δ : Q ⟶ P⟦(1 : ℤ)⟧) (p : ∀ n, X.X n ⟶ P.X n) (q : X ⟶ Q)

/-- A morphism into the twisted direct sum: the data of a morphism of complexes `q : X ⟶ Q` and a
degreewise family `p n : Xⁿ ⟶ Pⁿ` whose defect `d_X ≫ p - p ≫ d_P` against the differentials is
`q ≫ δ`. -/
private noncomputable def twistLift
    (h : ∀ n, X.d n (n + 1) ≫ p (n + 1) - p n ≫ P.d n (n + 1) = q.f n ≫ δ.f n) :
    X ⟶ CochainComplex.twist δ :=
  CochainComplex.ofHom (fun n => biprod.lift (p n) (q.f n)) (fun n => by
    rw [CochainComplex.twist_d]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
        Preadditive.comp_add]
      rw [← h n]
      abel
    · simp [q.comm])

private lemma twistLift_f
    (h : ∀ n, X.d n (n + 1) ≫ p (n + 1) - p n ≫ P.d n (n + 1) = q.f n ≫ δ.f n) (n : ℤ) :
    (twistLift δ p q h).f n = biprod.lift (p n) (q.f n) := rfl

/-- The twisted direct sum projects `twistLift δ p q h` back onto `q`. -/
private lemma twistLift_comp_twistSnd
    (h : ∀ n, X.d n (n + 1) ≫ p (n + 1) - p n ≫ P.d n (n + 1) = q.f n ≫ δ.f n) :
    twistLift δ p q h ≫ CochainComplex.twistπ δ = q := by
  ext n
  rw [HomologicalComplex.comp_f, twistLift_f, CochainComplex.twistπ_f]
  dsimp only [CochainComplex.twist_X]
  rw [biprod.lift_snd]

/-- On the part of `X` killed by `q`, the morphism `twistLift δ p q h` is `p` followed by the
inclusion of `P`: if `m : Y ⟶ X` satisfies `m ≫ q = 0` and `m` composed with `p` is `w`, then
`m ≫ twistLift δ p q h = w ≫ CochainComplex.twistι δ`. -/
private lemma comp_twistLift
    (h : ∀ n, X.d n (n + 1) ≫ p (n + 1) - p n ≫ P.d n (n + 1) = q.f n ≫ δ.f n)
    (m : Y ⟶ X) (w : Y ⟶ P) (hw : ∀ n, m.f n ≫ p n = w.f n)
    (hq : m ≫ q = 0) : m ≫ twistLift δ p q h = w ≫ CochainComplex.twistι δ := by
  ext n
  · simp only [HomologicalComplex.comp_f, twistLift_f, Category.assoc,
      biprod.lift_fst, biprod.inl_fst, Category.comp_id]
    exact hw n
  · simp only [HomologicalComplex.comp_f, twistLift_f, Category.assoc,
      biprod.lift_snd, biprod.inl_snd, Limits.comp_zero]
    rw [← HomologicalComplex.comp_f, hq, HomologicalComplex.zero_f]

end TwistLift

section TwistAbelian

variable {V : Type u} [Category.{v} V] [Abelian V] {P Q : CochainComplex V ℤ}

/-- The sequence `0 ⟶ P ⟶ CochainComplex.twist δ ⟶ Q ⟶ 0` is short exact, being split in every
degree. -/
private lemma twistShortComplex_shortExact (δ : Q ⟶ P⟦(1 : ℤ)⟧) :
    (CochainComplex.twistShortComplex δ).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact (CochainComplex.twistShortComplex δ)
    (fun _ =>
    ShortComplex.Splitting.shortExact
      { r := biprod.fst
        s := biprod.inr
        f_r := biprod.inl_fst
        s_g := biprod.inr_snd
        id := biprod.total })

end TwistAbelian

section Horseshoe

variable {A : Type u} [Category.{v} A] [Abelian A] {S : ShortComplex (CochainComplex A ℤ)}

/-- Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes, let `ι : X₁ ⟶ P`
be a morphism of complexes and let `u n : X₂ⁿ ⟶ Pⁿ` be a degreewise extension of `ι` along `S.f`,
which need not be a morphism of complexes. Then its defect `d_{X₂} ≫ u - u ≫ d_P` vanishes on `X₁`,
hence factors through `S.g`, and the factorization is a morphism of complexes `X₃ ⟶ P⟦1⟧`. -/
private lemma exists_shiftHom_defect (hS : S.ShortExact) {P : CochainComplex A ℤ} (ι : S.X₁ ⟶ P)
    (u : ∀ n, S.X₂.X n ⟶ P.X n) (hu : ∀ n, S.f.f n ≫ u n = ι.f n) :
    ∃ δ : S.X₃ ⟶ P⟦(1 : ℤ)⟧, ∀ n, S.g.f n ≫ δ.f n =
      S.X₂.d n (n + 1) ≫ u (n + 1) - u n ≫ P.d n (n + 1) := by
  have hSn : ∀ n, (S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hepi : ∀ n, Epi (S.g.f n) := fun n => (hSn n).epi_g
  have hepi' : ∀ n, Epi ((S.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).g) :=
    fun n => (hSn n).epi_g
  have key : ∀ n, S.f.f n ≫
      (S.X₂.d n (n + 1) ≫ u (n + 1) - u n ≫ P.d n (n + 1)) = 0 := fun n => by
    have h : S.f.f n ≫ S.X₂.d n (n + 1) ≫ u (n + 1) = S.X₁.d n (n + 1) ≫ ι.f (n + 1) := by
      rw [← Category.assoc, S.f.comm, Category.assoc, hu]
    rw [Preadditive.comp_sub, h, ← Category.assoc, hu, ι.comm, sub_self]
  obtain ⟨v, hv⟩ : ∃ v : ∀ n, S.X₃.X n ⟶ P.X (n + 1), ∀ n, S.g.f n ≫ v n =
      S.X₂.d n (n + 1) ≫ u (n + 1) - u n ≫ P.d n (n + 1) :=
    ⟨fun n => (hSn n).exact.desc _ (key n), fun n => (hSn n).exact.g_desc _ _⟩
  refine ⟨CochainComplex.ofHom v (fun n => ?_), hv⟩
  rw [← cancel_epi (S.g.f n), ← Category.assoc, hv, ← Category.assoc, S.g.comm,
    Category.assoc, hv, CochainComplex.shiftFunctor_obj_d',
    show ((1 : ℤ).negOnePow) = -1 from rfl, Units.neg_smul, one_smul]
  simp [Preadditive.sub_comp, Preadditive.comp_sub]

/-- Let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of cochain complexes, let `R₁` be an
injective resolution of `X₁` and let `R₃` be an injective resolution of `X₃` which is a
monomorphism in every degree. Then there is a morphism `δ : I₃ ⟶ I₁⟦1⟧` and a morphism
`X₂ ⟶ CochainComplex.twist δ` making both squares of
```
0 ⟶ X₁ ⟶ X₂        ⟶ X₃ ⟶ 0
     |     |           |
0 ⟶ I₁ ⟶ CochainComplex.twist δ ⟶ I₃ ⟶ 0
```
commute, the outer verticals being `R₁.ι` and `R₃.ι`. -/
private lemma exists_hom_twist (hS : S.ShortExact) (R₁ : S.X₁.InjectiveResolution)
    (R₃ : S.X₃.InjectiveResolution) [∀ n, Mono (R₃.ι.f n)] :
    ∃ (δ : R₃.cocomplex ⟶ R₁.cocomplex⟦(1 : ℤ)⟧) (ι₂ : S.X₂ ⟶ CochainComplex.twist δ),
      R₁.ι ≫ CochainComplex.twistι δ = S.f ≫ ι₂ ∧ ι₂ ≫ CochainComplex.twistπ δ = S.g ≫ R₃.ι := by
  have hmono : ∀ n, Mono (S.f.f n) := fun n =>
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n).mono_f
  obtain ⟨u, hu⟩ : ∃ u : ∀ n, S.X₂.X n ⟶ R₁.cocomplex.X n, ∀ n, S.f.f n ≫ u n = R₁.ι.f n :=
    ⟨fun n => Injective.factorThru (R₁.ι.f n) (S.f.f n), fun n => Injective.comp_factorThru _ _⟩
  obtain ⟨δbar, hδbar⟩ := exists_shiftHom_defect hS R₁.ι u hu
  have : R₁.cocomplex.IsKInjective := by
    obtain ⟨d, _⟩ := (CochainComplex.plus_iff A R₁.cocomplex).1 R₁.boundedBelow
    exact CochainComplex.isKInjective_of_injective R₁.cocomplex d
  have : ∀ n, Injective ((R₁.cocomplex⟦(1 : ℤ)⟧).X n) := fun n => R₁.injective (n + 1)
  obtain ⟨δ, hδ⟩ := (CochainComplex.IsKInjective.exists_factorization_of_quasiIso R₃.ι δbar).2
  have hdefect : ∀ n, S.X₂.d n (n + 1) ≫ u (n + 1) - u n ≫ R₁.cocomplex.d n (n + 1) =
      (S.g ≫ R₃.ι).f n ≫ δ.f n := by
    intro n
    rw [HomologicalComplex.comp_f, Category.assoc,
      show R₃.ι.f n ≫ δ.f n = δbar.f n by rw [← HomologicalComplex.comp_f, hδ]]
    exact (hδbar n).symm
  exact ⟨δ, twistLift δ u (S.g ≫ R₃.ι) hdefect,
    (comp_twistLift δ u _ hdefect S.f R₁.ι hu
      (by rw [← Category.assoc, S.zero, Limits.zero_comp])).symm,
    twistLift_comp_twistSnd δ u _ hdefect⟩

end Horseshoe

namespace CategoryTheory.ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Let `A` be an abelian category with enough injectives, let `S : 0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a
short exact sequence of cochain complexes of `A` with `X₂` (hence `X₁` and `X₃`) vanishing in the
degrees `< a`, and let `R₁` be any injective resolution of `X₁`. Then there are injective
resolutions `R₂` of `X₂` and `R₃` of `X₃` and a short exact sequence `0 ⟶ I₁ ⟶ I₂ ⟶ I₃ ⟶ 0` of the
resolving complexes making both squares commute; and if `I₁` also vanishes in the degrees `< a`,
then `I₂` and `I₃` may be chosen to do so as well. -/
@[stacks 013T "parts (1)–(3); the given resolution of the first term is a hypothesis and the \
  degree bound of parts (2) and (3) is an implication in the conclusion, so the source's plain \
  assertion follows by resolving the first term with 013K"]
public theorem exists_shortExact_injectiveResolution [EnoughInjectives A] (a : ℤ)
    {S : ShortComplex (CochainComplex A ℤ)} (hS : S.ShortExact) [S.X₂.IsStrictlyGE a]
    (R₁ : S.X₁.InjectiveResolution) :
    ∃ (R₂ : S.X₂.InjectiveResolution) (R₃ : S.X₃.InjectiveResolution)
      (f : R₁.cocomplex ⟶ R₂.cocomplex) (g : R₂.cocomplex ⟶ R₃.cocomplex)
      (w : f ≫ g = 0) (_ : (ShortComplex.mk f g w).ShortExact)
      (_ : R₁.cocomplex.IsStrictlyGE a →
        R₂.cocomplex.IsStrictlyGE a ∧ R₃.cocomplex.IsStrictlyGE a),
      R₁.ι ≫ f = S.f ≫ R₂.ι ∧ R₂.ι ≫ g = S.g ≫ R₃.ι := by
  have hepi : ∀ n, Epi (S.g.f n) := fun n =>
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n).epi_g
  have hX₃ : S.X₃.IsStrictlyGE a := isStrictlyGE_of_epi S.g a
  obtain ⟨R₃, hR₃mono, hR₃GE⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a S.X₃
  have := hR₃mono hX₃
  obtain ⟨δ, ι₂, hcomm₁₂, hcomm₂₃⟩ := exists_hom_twist hS R₁ R₃
  have : _root_.QuasiIso ι₂ :=
    quasiIso_τ₂ (S₁ := S) (S₂ := CochainComplex.twistShortComplex δ)
      { τ₁ := R₁.ι, τ₂ := ι₂, τ₃ := R₃.ι, comm₁₂ := hcomm₁₂, comm₂₃ := hcomm₂₃ }
      hS (twistShortComplex_shortExact δ) (fun j => ⟨j - 1, by simp⟩) (fun j => ⟨j + 1, rfl⟩)
      (inferInstanceAs (_root_.QuasiIso R₁.ι)) (inferInstanceAs (_root_.QuasiIso R₃.ι))
  exact ⟨{ cocomplex := CochainComplex.twist δ
           boundedBelow := twist_plus δ R₁.boundedBelow R₃.boundedBelow
           injective := fun n => by rw [CochainComplex.twist_X]; infer_instance
           ι := ι₂ }, R₃, CochainComplex.twistι δ, CochainComplex.twistπ δ,
    CochainComplex.twistι_comp_twistπ δ,
    twistShortComplex_shortExact δ, fun h => have := h; ⟨twist_isStrictlyGE δ a, hR₃GE⟩,
    hcomm₁₂, hcomm₂₃⟩

end CategoryTheory.ShortComplex.ShortExact

add_to_stacks 013R "the lemma's induction, with a supplied bound `d` for the boundedness below: \
  a complex which is strictly bounded below by `d` and whose terms are injective objects is \
  K-injective" CochainComplex.isKInjective_of_injective

add_to_stacks 013R "the conclusion at one morphism, the source's sentence: a morphism from an \
  acyclic complex to a K-injective complex is homotopic to zero"
  CochainComplex.IsKInjective.nonempty_homotopy_zero

add_to_stacks 013R "the conclusion in `K(A)`: a K-injective complex is right orthogonal to the \
  acyclic complexes, i.e. every morphism `K ⟶ I` of `K(A)` with `K` acyclic is zero"
  CochainComplex.IsKInjective.rightOrthogonal

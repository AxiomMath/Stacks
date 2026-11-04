module

public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.FirstQuadrantAbutment
import all StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.SpectralSequenceFunctor
import all StacksFrontier.Algebra.Homology.DerivedCategory.GrothendieckSpectralSequenceFunctorial.FirstQuadrantAbutment
-- `spectralSequence_iso` states the page-to-page isomorphism of the spectral sequence of a
-- spectral object with the autoparameter proofs of `spectralSequencePageXIso` written into
-- its right-hand side. Those proofs are lifted to private auxiliary declarations of the
-- Mathlib module, so without `import all` the statement mentions a constant this file cannot
-- resolve, and every tactic that has to typecheck it fails with `Unknown constant`.
import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The right-half-plane abutment of the functorial Grothendieck spectral sequence

Convergence of a right-half-plane spectral sequence of a single object, and the functorial
filtered abutment `plusAbutment` of the Grothendieck spectral sequence of a bounded below
complex to `H^n(R(G ∘ F))`, together with its transport along an isomorphism of the abutting
functors (`abutsToChangeAbutmentPlus`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.Grothendieck

open Stacks.Cohomology.HigherDirectImagePresheaf (derivedPlusToStandard)

attribute [local instance] HasDerivedCategory.standard

section Construction

open CategoryTheory.ComposableArrows

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section RightHalfPlane

open Opposite

/-! ### The right-half-plane abutment

The bounded below case differs from the first-quadrant case of `natAbutment` in exactly one
respect: the lower cohomological bound of an object of `DerivedCategory.Plus A` varies with
the object, so the page from which the spectral sequence of a single object has reached its
infinity term is not uniform. Everything below is arranged so that this is the *only*
`K`-dependent datum. The comparison `plusNu` from the whole-interval `E`-term to the `(p, q)`
spot of a page is a natural transformation of functors for every page `r > p`, and
`plusNu_edgeMonoSteps` says that these comparisons agree across pages; naturality of the
graded isomorphism then needs no `K`-dependent map at all.
-/

/-! #### Convergence of a right-half-plane spectral sequence of a single object

The five lemmas below are the objectwise ingredients, generic in the spectral sequence. They
are the right-half-plane analogues of the `CohomologicalSpectralSequenceNat.hasEdge…` lemmas
used by `spectralObjectFirstQuadrantAbutment`: the first-quadrant versions read the bounds off
the index type, whereas here the lower bound `a` is a parameter.
-/

/-- A right-half-plane spectral sequence whose second page vanishes below `a` has finite
support on every antidiagonal. -/
private lemma finite_pageTwo_support_of_rightHalfPlane
    {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (a : ℤ)
    (hLeft : ∀ p q : ℤ, p < 0 → IsZero ((E.page 2 (by omega)).X (p, q)))
    (hBottom : ∀ p q : ℤ, q < a → IsZero ((E.page 2 (by omega)).X (p, q)))
    (n : ℤ) : {p : ℤ | ¬ IsZero ((E.page 2 (by omega)).X (p, n - p))}.Finite := by
  apply (Set.finite_Icc 0 (n - a)).subset
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hpLower : 0 ≤ p := by
    by_contra h
    exact hp (hLeft p (n - p) (by omega))
  have hqLower : a ≤ n - p := by
    by_contra h
    exact hp (hBottom p (n - p) (by omega))
  exact ⟨hpLower, by omega⟩

/-- The relation of the shape `up' (r, 1 - r)` between two points of the plane. -/
private lemma up'_rel_iff {p q p' q' r : ℤ} :
    (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (p', q') (p, q) ↔
      p' = p - r ∧ q' = q + r - 1 := by
  simp only [ComplexShape.up', Prod.ext_iff, Prod.mk_add_mk]
  omega

/-- The differentials into `(p, q)` of the page `r` vanish if the source `(p - r, q + r - 1)`
vanishes on the second page. -/
private lemma hasEdgeMonoAt_of_isZero {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (p q r : ℤ) (hr : 2 ≤ r)
    (h : IsZero ((E.page 2 (by omega)).X (p - r, q + r - 1))) : E.HasEdgeMonoAt (p, q) r where
  le := hr
  zero pq' := by
    obtain ⟨p', q'⟩ := pq'
    by_cases hrel : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (p', q') (p, q)
    · obtain ⟨rfl, rfl⟩ := up'_rel_iff.1 hrel
      exact (isZero_page_of_isZero_initial E _ h r hr).eq_of_src _ _
    · exact (E.page r).shape _ _ hrel

/-- The differentials out of `(p, q)` of the page `r` vanish if the target `(p + r, q - r + 1)`
vanishes on the second page. -/
private lemma hasEdgeEpiAt_of_isZero {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (p q r : ℤ) (hr : 2 ≤ r)
    (h : IsZero ((E.page 2 (by omega)).X (p + r, q - r + 1))) : E.HasEdgeEpiAt (p, q) r where
  le := hr
  zero pq' := by
    obtain ⟨p', q'⟩ := pq'
    by_cases hrel : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel (p, q) (p', q')
    · obtain ⟨h₁, h₂⟩ := up'_rel_iff.1 hrel
      obtain rfl : p' = p + r := by omega
      obtain rfl : q' = q - r + 1 := by omega
      exact (isZero_page_of_isZero_initial E _ h r hr).eq_of_tgt _ _
    · exact (E.page r).shape _ _ hrel

/-- Finite support on the antidiagonals through `(p, q)` gives an infinity page there. -/
private lemma hasPageInfinityAt_of_finite_pageTwo
    {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A)
    (h : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 2 (by omega)).X (p, n - p))}.Finite)
    (p q : ℤ) : E.HasPageInfinityAt (p, q) := by
  obtain ⟨b₀, hb₀⟩ := (h (p + q - 1)).bddBelow
  obtain ⟨b₁, hb₁⟩ := (h (p + q + 1)).bddAbove
  refine ⟨⟨max 2 (p - b₀ + 1), by omega, fun r hr => ?_⟩,
    ⟨max 2 (b₁ - p + 1), by omega, fun r hr => ?_⟩⟩
  · refine hasEdgeMonoAt_of_isZero E p q r (by omega) ?_
    by_contra hn
    have hm : p - r ∈ {i : ℤ | ¬ IsZero ((E.page 2 (by omega)).X (i, p + q - 1 - i))} := by
      simpa only [Set.mem_ofPred_eq, show p + q - 1 - (p - r) = q + r - 1 by omega] using hn
    have := hb₀ hm
    omega
  · refine hasEdgeEpiAt_of_isZero E p q r (by omega) ?_
    by_contra hn
    have hm : p + r ∈ {i : ℤ | ¬ IsZero ((E.page 2 (by omega)).X (i, p + q + 1 - i))} := by
      simpa only [Set.mem_ofPred_eq, show p + q + 1 - (p + r) = q - r + 1 by omega] using hn
    have := hb₁ hm
    omega

/-- A right-half-plane spectral sequence bounded below by `a` has an infinity page. -/
private lemma hasPageInfinityAt_of_rightHalfPlane
    {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (a : ℤ)
    (hLeft : ∀ p q : ℤ, p < 0 → IsZero ((E.page 2 (by omega)).X (p, q)))
    (hBottom : ∀ p q : ℤ, q < a → IsZero ((E.page 2 (by omega)).X (p, q)))
    (p q : ℤ) : E.HasPageInfinityAt (p, q) :=
  hasPageInfinityAt_of_finite_pageTwo E
    (finite_pageTwo_support_of_rightHalfPlane E a hLeft hBottom) p q

/-- The differentials into `(p, q)` vanish from the page `max 2 (p + 1)` on. This bound uses
only the vanishing in the left half plane, so it is uniform in the object. -/
private lemma hasEdgeMonoAtFrom_of_rightHalfPlane
    {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (p q : ℤ) [E.HasPageInfinityAt (p, q)]
    (hLeft : ∀ p q : ℤ, p < 0 → IsZero ((E.page 2 (by omega)).X (p, q))) :
    E.HasEdgeMonoAtFrom (p, q) (max 2 (p + 1)) := by
  refine SpectralSequence.HasEdgeMonoAtFrom.mk'
    (E := E) (pq := (p, q)) (r := max 2 (p + 1)) ?_ (by omega)
  intro k
  exact hasEdgeMonoAt_of_isZero E p q _ (by omega) (hLeft _ _ (by omega))

/-- The differentials out of `(p, q)` vanish from the page `max 2 (q - a + 2)` on. This bound
depends on the lower bound `a`, hence on the object. -/
private lemma hasEdgeEpiAtFrom_of_rightHalfPlane
    {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (a p q : ℤ) [E.HasPageInfinityAt (p, q)]
    (hBottom : ∀ p q : ℤ, q < a → IsZero ((E.page 2 (by omega)).X (p, q))) :
    E.HasEdgeEpiAtFrom (p, q) (max 2 (q - a + 2)) := by
  refine SpectralSequence.HasEdgeEpiAtFrom.mk'
    (E := E) (pq := (p, q)) (r := max 2 (q - a + 2)) ?_ (by omega)
  intro k
  exact hasEdgeEpiAt_of_isZero E p q _ (by omega) (hBottom _ _ (by omega))

/-- Cancellation used to read `spectralSequence_iso` off the left homology data: the two
inverses in front of a threefold composite of isomorphisms leave the third factor. -/
private lemma iso_inv_inv_trans_hom_assoc {D : Type*} [Category D] {X Y Z W V : D}
    (e₁ : X ≅ Y) (e₂ : Y ≅ Z) (e₃ : Z ≅ W) (f : W ⟶ V) :
    e₂.inv ≫ e₁.inv ≫ (e₁ ≪≫ e₂ ≪≫ e₃).hom ≫ f = e₃.hom ≫ f := by
  simp

/-- A finite filtration whose graded pieces are the infinity terms witnesses convergence. -/
private theorem abutsTo_of_finiteFiltration {A : Type*} [Category A] [Abelian A]
    (E : E₂CohomologicalSpectralSequence A) (H : ℤ → A)
    (hInf : ∀ p q : ℤ, E.HasPageInfinityAt (p, q))
    (Fil : ℤ → FilteredObject A ℤᵒᵖ) (e : ∀ n, (Fil n).X ≅ H n)
    (hf : ∀ n, Filtration.IsFinite (Fil n).filtration)
    (hg : ∀ p q, E.pageInfinity (p, q) ≅ (FilteredObject.gr p).obj (Fil (p + q))) :
    E.AbutsTo H := by
  let Sub (n p : ℤ) := Subobject.mk ((Fil n).filtration.ι.app (op p) ≫ (e n).hom)
  have hS : ∀ n, Antitone (Sub n) := by
    intro n i j hij
    exact Subobject.mk_le_mk_of_comm ((Fil n).filtration.step (opHomOfLE hij))
      (by simp)
  refine ⟨hInf, Sub, hS, ?_, ?_⟩
  · intro n
    have := hf n
    obtain ⟨a, ha⟩ := Filtration.HasTopStep.exists_isIso (F := (Fil n).filtration)
    obtain ⟨b, hb⟩ := Filtration.HasBotStep.exists_isZero (Fil n).filtration
    refine ⟨min a.unop b.unop, b.unop, min_le_right _ _, ?_, ?_⟩
    · have := (Fil n).filtration.isIso_ι_app_of_le (min_le_left a.unop b.unop) ha
      exact (Subobject.isIso_iff_mk_eq_top _).1 inferInstance
    · exact (Subobject.mk_eq_bot_iff_nonempty_isInitial _).2 ⟨hb.isInitial⟩
  · intro p q
    refine ⟨hg p q ≪≫ cokernel.mapIso _ _
      (Subobject.underlyingIso
        ((Fil (p + q)).filtration.ι.app (op (p + 1)) ≫ (e (p + q)).hom)).symm
      (Subobject.underlyingIso
        ((Fil (p + q)).filtration.ι.app (op p) ≫ (e (p + q)).hom)).symm ?_⟩
    apply (cancel_mono (Sub (p + q) p).arrow).1
    simp only [Iso.symm_hom]
    simp [Sub, Subobject.underlyingIso_arrow]

/-! #### The Grothendieck spectral object over the bounded below derived category -/

section Plus

variable {A B C : Type*} [Category A] [Category B] [Category C]
  [Abelian A] [Abelian B] [Abelian C]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- The Grothendieck spectral object of `F` and `G`, read as a single spectral object of the
category of functors on the bounded below derived category of `A`. -/
private noncomputable abbrev plusSpectralObject :
    Abelian.SpectralObject (DerivedCategory.Plus A ⥤ C) EInt :=
  spectralObjectInFunctorCategory (derivedTruncationSpectralObjectFunctor F G)

/-- The upper vanishing holds in the functor category, uniformly in the object. -/
private theorem plusSpectralObject_isZero₂ (i j : EInt) (hij : i ≤ j) (n : ℤ) (hi : n < i) :
    IsZero (((plusSpectralObject F G).H n).obj (mk₁ (homOfLE hij))) :=
  (Functor.isZero_iff _).mpr fun K =>
    derivedTruncationSpectralObject_isZero₂ F G K i j hij n hi

/-- The second page vanishes in the left half plane, uniformly in the object. -/
private theorem plusPageTwo_isZero (p q : ℤ) (hp : p < 0) :
    IsZero ((((plusSpectralObject F G).E₂SpectralSequence).page 2).X (p, q)) :=
  (Functor.isZero_iff _).mpr fun K =>
    derivedTruncationSpectralSequenceFunctor_pageTwo_isZero F G K p q hp

/-- The differentials into `(p, q)` vanish on every page `r > p`, uniformly in the object:
their source lies in the left half plane. -/
private theorem plusSpectralSequence_hasEdgeMonoAt (p q r : ℤ) (hr : 2 ≤ r) (hpr : p < r) :
    ((plusSpectralObject F G).E₂SpectralSequence).HasEdgeMonoAt (p, q) r :=
  hasEdgeMonoAt_of_isZero _ p q r hr (plusPageTwo_isZero F G _ _ (by omega))

/-! The four `E`-terms that occur below all have the two middle indices `q ≤ q + 1`, and differ
only in the outer two. `plusE` names that family, `plusMapLower` and `plusMapUpper` the two
structural maps between its members, so that the three identities
`mapFourδ₁Toδ₀'_comp`, `mapFourδ₄Toδ₃'_comp` and `mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'` can be read
off. The `≤` proofs below are interchangeable by proof irrelevance; they are named only to
keep the terms short. -/

/-- `q ≤ q + 1` in `EInt`. -/
private lemma plusLe₁ (q : ℤ) : (q : EInt) ≤ ((q + 1 : ℤ) : EInt) :=
  WithBotTop.coe_le_coe.mpr (by omega)

/-- `q - r + 2 ≤ q` in `EInt`, the left end of the page-`r` interval. -/
private lemma plusLe₀ (q r : ℤ) (hr : 2 ≤ r) : ((q - r + 2 : ℤ) : EInt) ≤ (q : EInt) :=
  WithBotTop.coe_le_coe.mpr (by omega)

/-- `q + 1 ≤ q + r - 1` in `EInt`, the right end of the page-`r` interval. -/
private lemma plusLe₂ (q r : ℤ) (hr : 2 ≤ r) :
    ((q + 1 : ℤ) : EInt) ≤ ((q + r - 1 : ℤ) : EInt) :=
  WithBotTop.coe_le_coe.mpr (by omega)

/-- The right end of the page-`r` interval is above the total degree, for `r > p`. -/
private lemma plusLt (p q r : ℤ) (hpr : p < r) :
    ((p + q - 1 : ℤ) : EInt) < ((q + r - 1 : ℤ) : EInt) :=
  WithBotTop.coe_lt_coe.mpr (by omega)

/-- The `E`-term over `i ≤ q ≤ q + 1 ≤ j` in total degree `n`. -/
private noncomputable abbrev plusE (n q : ℤ) (i j : EInt) (hi : i ≤ (q : EInt))
    (hj : ((q + 1 : ℤ) : EInt) ≤ j) : DerivedCategory.Plus A ⥤ C :=
  (plusSpectralObject F G).E (homOfLE hi) (homOfLE (plusLe₁ q)) (homOfLE hj)
    (n - 1) n (n + 1) (by omega) (by omega)

/-- Shrinking the interval from the left. -/
private noncomputable abbrev plusMapLower (n q : ℤ) (i i' j : EInt) (hii' : i ≤ i')
    (hi' : i' ≤ (q : EInt)) (hj : ((q + 1 : ℤ) : EInt) ≤ j) :
    plusE F G n q i j (hii'.trans hi') hj ⟶ plusE F G n q i' j hi' hj :=
  (plusSpectralObject F G).mapFourδ₁Toδ₀' i i' (q : EInt) ((q + 1 : ℤ) : EInt) j
    hii' hi' (plusLe₁ q) hj (n - 1) n (n + 1)

/-- Enlarging the interval to the right. -/
private noncomputable abbrev plusMapUpper (n q : ℤ) (i j j' : EInt) (hi : i ≤ (q : EInt))
    (hj : ((q + 1 : ℤ) : EInt) ≤ j) (hjj' : j ≤ j') :
    plusE F G n q i j hi hj ⟶ plusE F G n q i j' hi (hj.trans hjj') :=
  (plusSpectralObject F G).mapFourδ₄Toδ₃' i (q : EInt) ((q + 1 : ℤ) : EInt) j j'
    hi (plusLe₁ q) hj hjj' (n - 1) n (n + 1)

/-- Enlarging the right end to `⊤` is an isomorphism as soon as the right end is above the
total degree: that is the upper vanishing, which is uniform in the object. -/
private noncomputable abbrev plusMapUpperTopIso (n q : ℤ) (i j : EInt) (hi : i ≤ (q : EInt))
    (hj : ((q + 1 : ℤ) : EInt) ≤ j) (hn : ((n - 1 : ℤ) : EInt) < j) :
    plusE F G n q i j hi hj ≅ plusE F G n q i ⊤ hi (hj.trans le_top) :=
  (plusSpectralObject F G).isoMapFourδ₄Toδ₃' i (q : EInt) ((q + 1 : ℤ) : EInt) j ⊤
    hi (plusLe₁ q) hj le_top (n - 1) n (n + 1)
    (plusSpectralObject_isZero₂ F G j ⊤ le_top (n - 1) hn)

/-- The `(p, q)` spot of the page `r` as the `E`-term over `q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1`. -/
private noncomputable abbrev plusPageIso (p q r : ℤ) (hr : 2 ≤ r) :
    (((plusSpectralObject F G).E₂SpectralSequence).page r hr).X (p, q) ≅
      plusE F G (p + q) q ((q - r + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
        (plusLe₀ q r hr) (plusLe₂ q r hr) :=
  (plusSpectralObject F G).spectralSequencePageXIso
    Abelian.SpectralObject.coreE₂Cohomological r hr (p, q)
    ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
    rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1) rfl

/-- The comparison from the whole-interval `E`-term to the `(p, q)` spot of the page `r`, for
any page `r > p`. It is a natural transformation of functors: its only input is the upper
vanishing, which is uniform in the object. At a given object it becomes an isomorphism once
`r` is large enough for that object; see `plusGradedIso`. -/
private noncomputable def plusNu (p q r : ℤ) (hr : 2 ≤ r) (hpr : p < r) :
    plusE F G (p + q) q ⊥ ⊤ bot_le le_top ⟶
      (((plusSpectralObject F G).E₂SpectralSequence).page r hr).X (p, q) :=
  (plusMapUpperTopIso F G (p + q) q ⊥ ((q + r - 1 : ℤ) : EInt) bot_le (plusLe₂ q r hr)
      (plusLt p q r hpr)).inv ≫
    plusMapLower F G (p + q) q ⊥ ((q - r + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      bot_le (plusLe₀ q r hr) (plusLe₂ q r hr) ≫
    (plusPageIso F G p q r hr).inv

/-- The comparisons `plusNu` at consecutive pages differ by the one-step edge monomorphism.

Clause (ii), `plusMapUpper_comp_edgeMonoStep`, is the compatibility of the edge monomorphism
with the left homology data that the spectral object supplies on each page, namely
`SpectralSequence.leftHomologyData_π_edgeMonoStep_compatibility` for
`spectralSequenceHomologyData`, whose `left.π` and `left.i` are the two structural maps. The
rest is the three structural identities of `mapFourδ`. -/
private theorem plusNu_step (p q r r' : ℤ) (hr : 2 ≤ r) (hpr : p < r) (hrr' : r + 1 = r')
    [((plusSpectralObject F G).E₂SpectralSequence).HasEdgeMonoAt (p, q) r] :
    plusNu F G p q r' (by omega) (by omega) ≫
        ((plusSpectralObject F G).E₂SpectralSequence).edgeMonoStep (p, q) r r' hrr' =
      plusNu F G p q r hr hpr := by
  have hr' : 2 ≤ r' := by omega
  have hpr' : p < r' := by omega
  -- Clause (ii): the edge monomorphism, read through the two page identifications, is the
  -- structural map which shrinks the left end from `q - r' + 2` to `q - r + 2`.
  have h3 : plusMapUpper F G (p + q) q ((q - r' + 2 : ℤ) : EInt)
          ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt) (plusLe₀ q r' hr')
          (plusLe₂ q r hr) (WithBotTop.coe_le_coe.mpr (by omega)) ≫
        (plusPageIso F G p q r' hr').inv ≫
          ((plusSpectralObject F G).E₂SpectralSequence).edgeMonoStep (p, q) r r' hrr' =
      plusMapLower F G (p + q) q ((q - r' + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt)
          ((q + r - 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.mpr (by omega)) (plusLe₀ q r hr)
          (plusLe₂ q r hr) ≫
        (plusPageIso F G p q r hr).inv := by
    let HD := (plusSpectralObject F G).spectralSequenceHomologyData
      Abelian.SpectralObject.coreE₂Cohomological r r' hrr' hr
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl
      ((q - r' + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt)
      rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1) rfl
    let hsc := (((plusSpectralObject F G).E₂SpectralSequence).page r hr).homologyIsoSc'
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl
    have key := SpectralSequence.leftHomologyData_π_edgeMonoStep_compatibility
      (E := (plusSpectralObject F G).E₂SpectralSequence) r r'
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl HD.left hrr'
    have hiso := (plusSpectralObject F G).spectralSequence_iso
      Abelian.SpectralObject.coreE₂Cohomological r r' hrr' hr
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
      ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl
      ((q - r' + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt)
      rfl rfl rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1) rfl
    -- The two inverses in front of `spectralSequence_iso` leave the page-`r'` identification.
    have hc : HD.left.homologyIso.inv ≫ hsc.inv ≫
          (((plusSpectralObject F G).E₂SpectralSequence).iso r r' (p, q) hrr' hr).hom ≫
            ((plusSpectralObject F G).E₂SpectralSequence).edgeMonoStep (p, q) r r' hrr' =
        (plusPageIso F G p q r' hr').inv ≫
          ((plusSpectralObject F G).E₂SpectralSequence).edgeMonoStep (p, q) r r' hrr' := by
      rw [hiso]
      exact iso_inv_inv_trans_hom_assoc hsc HD.left.homologyIso
        (plusPageIso F G p q r' hr').symm _
    have hπ : HD.left.π = plusMapUpper F G (p + q) q ((q - r' + 2 : ℤ) : EInt)
        ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt) (plusLe₀ q r' hr')
        (plusLe₂ q r hr) (WithBotTop.coe_le_coe.mpr (by omega)) := rfl
    have hi : HD.left.i = plusMapLower F G (p + q) q ((q - r' + 2 : ℤ) : EInt)
          ((q - r + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
          (WithBotTop.coe_le_coe.mpr (by omega)) (plusLe₀ q r hr) (plusLe₂ q r hr) ≫
        (plusPageIso F G p q r hr).inv :=
      Abelian.SpectralObject.spectralSequenceHomologyData_left_i ..
    rw [← hπ, ← hi, ← hc]
    exact key
  -- The three structural identities.
  have h1 : (plusMapUpperTopIso F G (p + q) q ⊥ ((q + r - 1 : ℤ) : EInt) bot_le
          (plusLe₂ q r hr) (plusLt p q r hpr)).hom ≫
        (plusMapUpperTopIso F G (p + q) q ⊥ ((q + r' - 1 : ℤ) : EInt) bot_le
          (plusLe₂ q r' hr') (plusLt p q r' hpr')).inv =
      plusMapUpper F G (p + q) q ⊥ ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt)
        bot_le (plusLe₂ q r hr) (WithBotTop.coe_le_coe.mpr (by omega)) := by
    refine (cancel_mono (plusMapUpperTopIso F G (p + q) q ⊥ ((q + r' - 1 : ℤ) : EInt) bot_le
      (plusLe₂ q r' hr') (plusLt p q r' hpr')).hom).1 ?_
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ((plusSpectralObject F G).mapFourδ₄Toδ₃'_comp ⊥ (q : EInt) ((q + 1 : ℤ) : EInt)
      ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt) ⊤ bot_le (plusLe₁ q)
      (plusLe₂ q r hr) (WithBotTop.coe_le_coe.mpr (by omega)) le_top
      (p + q - 1) (p + q) (p + q + 1)).symm
  have h2 : plusMapLower F G (p + q) q ⊥ ((q - r' + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
          bot_le (plusLe₀ q r' hr') (plusLe₂ q r hr) ≫
        plusMapUpper F G (p + q) q ((q - r' + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
          ((q + r' - 1 : ℤ) : EInt) (plusLe₀ q r' hr') (plusLe₂ q r hr)
          (WithBotTop.coe_le_coe.mpr (by omega)) =
      plusMapUpper F G (p + q) q ⊥ ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt)
          bot_le (plusLe₂ q r hr) (WithBotTop.coe_le_coe.mpr (by omega)) ≫
        plusMapLower F G (p + q) q ⊥ ((q - r' + 2 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt)
          bot_le (plusLe₀ q r' hr') (plusLe₂ q r' hr') :=
    (plusSpectralObject F G).mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' ⊥ ((q - r' + 2 : ℤ) : EInt)
      (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt) ((q + r' - 1 : ℤ) : EInt)
      bot_le (plusLe₀ q r' hr') (plusLe₁ q) (plusLe₂ q r hr)
      (WithBotTop.coe_le_coe.mpr (by omega)) (p + q - 1) (p + q) (p + q + 1)
  have h4 : plusMapLower F G (p + q) q ⊥ ((q - r' + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
          bot_le (plusLe₀ q r' hr') (plusLe₂ q r hr) ≫
        plusMapLower F G (p + q) q ((q - r' + 2 : ℤ) : EInt) ((q - r + 2 : ℤ) : EInt)
          ((q + r - 1 : ℤ) : EInt) (WithBotTop.coe_le_coe.mpr (by omega)) (plusLe₀ q r hr)
          (plusLe₂ q r hr) =
      plusMapLower F G (p + q) q ⊥ ((q - r + 2 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
        bot_le (plusLe₀ q r hr) (plusLe₂ q r hr) :=
    (plusSpectralObject F G).mapFourδ₁Toδ₀'_comp ⊥ ((q - r' + 2 : ℤ) : EInt)
      ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      bot_le (WithBotTop.coe_le_coe.mpr (by omega)) (plusLe₀ q r hr) (plusLe₁ q)
      (plusLe₂ q r hr) (p + q - 1) (p + q) (p + q + 1)
  rw [← cancel_epi (plusMapUpperTopIso F G (p + q) q ⊥ ((q + r - 1 : ℤ) : EInt) bot_le
    (plusLe₂ q r hr) (plusLt p q r hpr)).hom]
  dsimp only [plusNu]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h1, ← Category.assoc, ← h2, Category.assoc, h3, ← Category.assoc, h4]

/-! #### The spectral sequence of a single bounded below complex

Everything below compares the spectral sequence of a single object with the one in the functor
category, so it repeatedly crosses the identification
`((spectralSequenceEvaluate E K).page r hr).X pq = ((E.page r hr).X pq).obj K`. Without the
attribute below that identification holds only at semireducible transparency, and then even
*instance search* fails: `inv ((plusNu …).app K)` and the `IsIso` hypothesis about the same
morphism get the two different spellings of its source and are not seen to agree. -/

attribute [local implicit_reducible] spectralSequenceEvaluate spectralSequenceEvaluateMap
  spectralSequenceAsFunctor

/-- The spectral sequence of a single object of the bounded below derived category. -/
private noncomputable abbrev plusSeq (K : DerivedCategory.Plus A) :
    E₂CohomologicalSpectralSequence C :=
  spectralSequenceEvaluate (plusSpectralObject F G).E₂SpectralSequence K

/-- A lower cohomological bound for an object of the bounded below derived category. -/
private noncomputable def plusBound (K : DerivedCategory.Plus A) : ℤ :=
  Classical.choose K.property

omit [EnoughInjectives A] in
private theorem plusBound_isGE (K : DerivedCategory.Plus A) : K.IsGE (plusBound K) :=
  ⟨(Classical.choose_spec K.property).ge⟩

private theorem plusSeq_pageTwo_isZero_left (K : DerivedCategory.Plus A) (p q : ℤ) (hp : p < 0) :
    IsZero (((plusSeq F G K).page 2).X (p, q)) :=
  derivedTruncationSpectralSequenceFunctor_pageTwo_isZero F G K p q hp

private theorem plusSeq_pageTwo_isZero_bottom (K : DerivedCategory.Plus A) (p q : ℤ)
    (hq : q < plusBound K) : IsZero (((plusSeq F G K).page 2).X (p, q)) :=
  have := plusBound_isGE K
  derivedTruncationSpectralSequenceFunctor_pageTwo_isZero_of_lt F G K (plusBound K) p q hq

private theorem plusSeq_hasPageInfinityAt (K : DerivedCategory.Plus A) (p q : ℤ) :
    (plusSeq F G K).HasPageInfinityAt (p, q) :=
  hasPageInfinityAt_of_rightHalfPlane (plusSeq F G K) (plusBound K)
    (fun p' q' h => plusSeq_pageTwo_isZero_left F G K p' q' h)
    (fun p' q' h => plusSeq_pageTwo_isZero_bottom F G K p' q' h) p q

/-- The differentials into `(p, q)` vanish from any page `r > p` on. -/
private theorem plusSeq_hasEdgeMonoAtFrom (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r) [(plusSeq F G K).HasPageInfinityAt (p, q)] :
    (plusSeq F G K).HasEdgeMonoAtFrom (p, q) r :=
  have := hasEdgeMonoAtFrom_of_rightHalfPlane (plusSeq F G K) p q
    (fun p' q' h => plusSeq_pageTwo_isZero_left F G K p' q' h)
  (plusSeq F G K).hasEdgeMonoAtFrom_of_GE (p, q) (max 2 (p + 1)) r (by omega)

/-- The differentials out of `(p, q)` vanish from any page `r ≥ q - a + 2` on, where `a` is a
lower cohomological bound for the object. This bound is the one place where the page depends on
the object. -/
private theorem plusSeq_hasEdgeEpiAtFrom (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr2 : 2 ≤ r) (ha : q - plusBound K + 2 ≤ r)
    [(plusSeq F G K).HasPageInfinityAt (p, q)] :
    (plusSeq F G K).HasEdgeEpiAtFrom (p, q) r :=
  have := hasEdgeEpiAtFrom_of_rightHalfPlane (plusSeq F G K) (plusBound K) p q
    (fun p' q' h => plusSeq_pageTwo_isZero_bottom F G K p' q' h)
  (plusSeq F G K).hasEdgeEpiAtFrom_of_GE (p, q) (max 2 (q - plusBound K + 2)) r (by omega)

/-- The induced map of the spectral sequences of two objects. Not an `abbrev`: the point is
that the declared type names `plusSeq`, so that `mapPageInfinity_eq` instantiates its two
spectral sequences in the spelling the lemmas below use. -/
private noncomputable def plusSeqMap {K L : DerivedCategory.Plus A} (φ : K ⟶ L) :
    plusSeq F G K ⟶ plusSeq F G L :=
  (spectralSequenceAsFunctor (plusSpectralObject F G).E₂SpectralSequence).map φ

/-- The comparison `plusNu` at an object, with its target written as a spot on a page of that
object's spectral sequence. The body is `(plusNu …).app K`; the two types agree definitionally,
but only at default transparency, so *instance search* cannot see it. Every statement below
therefore uses this spelling, which is the one `pageInfinityIso` and `edgeMonoSteps` produce. -/
private noncomputable def plusNuApp (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r) :
    (plusE F G (p + q) q ⊥ ⊤ bot_le le_top).obj K ⟶ ((plusSeq F G K).page r hr2).X (p, q) :=
  (plusNu F G p q r hr2 hpr).app K

/-- The comparisons `plusNu` at two pages differ by the composite edge monomorphism. The
induction is over the number of steps; a single step is `plusNu_step`, transported to the
evaluated spectral sequence by `spectralSequenceEvaluate_edgeMonoStep`. -/
private theorem plusNu_edgeMonoSteps (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr : 2 ≤ r) (hpr : p < r)
    [(plusSeq F G K).HasPageInfinityAt (p, q)]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r] :
    ∀ (r' : ℤ) (hrr' : r ≤ r'),
      plusNuApp F G K p q r' (hr.trans hrr') (hpr.trans_le hrr') ≫
          (plusSeq F G K).edgeMonoSteps (p, q) r r' hrr' =
        plusNuApp F G K p q r hr hpr := by
  intro r' hrr'
  induction r', hrr' using Int.leInduction with
  | base =>
    rw [SpectralSequence.edgeMonoSteps_eq_id]
    exact Category.comp_id _
  | succ r' hrr' ih =>
    have : ((plusSpectralObject F G).E₂SpectralSequence).HasEdgeMonoAt (p, q) r' :=
      plusSpectralSequence_hasEdgeMonoAt F G p q r' (by omega) (by omega)
    have : (plusSeq F G K).HasEdgeMonoAt (p, q) r' :=
      spectralSequenceEvaluate_hasEdgeMonoAt _ K (p, q) r'
    have hstep : plusNuApp F G K p q (r' + 1) (by omega) (by omega) ≫
        (plusSeq F G K).edgeMonoStep (p, q) r' (r' + 1) rfl =
          plusNuApp F G K p q r' (by omega) (by omega) := by
      rw [spectralSequenceEvaluate_edgeMonoStep]
      exact congrArg (fun η : plusE F G (p + q) q ⊥ ⊤ bot_le le_top ⟶ _ => η.app K)
        (plusNu_step F G p q r' (r' + 1) (by omega) (by omega) rfl)
    rw [(plusSeq F G K).edgeMonoSteps_eq_edgeMonoStep_comp_edgeMonoSteps (p, q) r r' (r' + 1)
      hrr' rfl]
    exact ((Category.assoc _ _ _).symm.trans (congrArg
      (fun t => t ≫ (plusSeq F G K).edgeMonoSteps (p, q) r r' hrr') hstep)).trans ih

/-! #### The graded isomorphism -/

/-- `IsIso` of the evaluation of a `homologyMap` follows from `IsIso` of the `homologyMap` of
the evaluation: evaluation preserves homology, and the comparison is an isomorphism. -/
private lemma isIso_homologyMap_app {D A' : Type*} [Category D] [Category A'] [Abelian A']
    {T₁ T₂ : ShortComplex (D ⥤ A')} (φ : T₁ ⟶ T₂) (K : D)
    (h : IsIso (ShortComplex.homologyMap
      (((evaluation D A').obj K).mapShortComplex.map φ))) :
    IsIso ((ShortComplex.homologyMap φ).app K) := by
  have := h
  have heq := (Iso.inv_comp_eq (T₁.mapHomologyIso ((evaluation D A').obj K))).2
    (ShortComplex.mapHomologyIso_hom_naturality φ ((evaluation D A').obj K))
  have hiso : IsIso ((T₁.mapHomologyIso ((evaluation D A').obj K)).inv ≫
      ShortComplex.homologyMap (((evaluation D A').obj K).mapShortComplex.map φ) ≫
        (T₂.mapHomologyIso ((evaluation D A').obj K)).hom) := inferInstance
  have hev : IsIso (((evaluation D A').obj K).map (ShortComplex.homologyMap φ)) := heq ▸ hiso
  exact hev

/-- At an object `K` whose cohomology starts at or above `i'`, shrinking the left end of the
interval to `i'` is an isomorphism. The obstruction is the objectwise lower vanishing, which is
why this cannot be read off in the functor category. -/
private lemma isIso_plusMapLower_app (K : DerivedCategory.Plus A) (n q : ℤ) (i i' j : EInt)
    (hii' : i ≤ i') (hi' : i' ≤ (q : EInt)) (hj : ((q + 1 : ℤ) : EInt) ≤ j)
    (hz : IsZero ((((derivedTruncationSpectralObjectFunctor F G).obj K).H (n + 1)).obj
      (mk₁ (homOfLE hii')))) :
    IsIso ((plusMapLower F G n q i i' j hii' hi' hj).app K) :=
  isIso_homologyMap_app _ K
    (((derivedTruncationSpectralObjectFunctor F G).obj K).isIso_mapFourδ₁Toδ₀'
      i i' (q : EInt) ((q + 1 : ℤ) : EInt) j hii' hi' (plusLe₁ q) hj (n - 1) n (n + 1) hz)

/-- At an object with lower cohomological bound `a`, the comparison `plusNu` is an isomorphism
on every page `r ≥ q - a + 2`. -/
private lemma isIso_plusNu_app (K : DerivedCategory.Plus A) (p q r : ℤ) (hr2 : 2 ≤ r)
    (hpr : p < r) (ha : q - plusBound K + 2 ≤ r) :
    IsIso (plusNuApp F G K p q r hr2 hpr) := by
  have := plusBound_isGE K
  have := isIso_plusMapLower_app F G K (p + q) q ⊥ ((q - r + 2 : ℤ) : EInt)
    ((q + r - 1 : ℤ) : EInt) bot_le (plusLe₀ q r hr2) (plusLe₂ q r hr2)
    (derivedTruncationSpectralObject_isZero₁ F G K (plusBound K) ⊥ ((q - r + 2 : ℤ) : EInt)
      bot_le (WithBotTop.coe_le_coe.mpr (by omega)) (p + q + 1))
  have hc : plusNuApp F G K p q r hr2 hpr =
      (((plusMapUpperTopIso F G (p + q) q ⊥ ((q + r - 1 : ℤ) : EInt) bot_le (plusLe₂ q r hr2)
              (plusLt p q r hpr)).app K).symm ≪≫
          asIso ((plusMapLower F G (p + q) q ⊥ ((q - r + 2 : ℤ) : EInt)
            ((q + r - 1 : ℤ) : EInt) bot_le (plusLe₀ q r hr2) (plusLe₂ q r hr2)).app K) ≪≫
          ((plusPageIso F G p q r hr2).app K).symm).hom := rfl
  rw [hc]
  exact Iso.isIso_hom _

/-- The abutment filtration in total degree `n`, as a functor. -/
private noncomputable abbrev plusFiltration (n : ℤ) :
    DerivedCategory.Plus A ⥤ FilteredObject C ℤᵒᵖ :=
  filteredUncurry (spectralObjectFiltration (plusSpectralObject F G) n)

/-- The whole-interval `E`-term is the graded piece of the abutment filtration, naturally in
the object. -/
private noncomputable def plusGrIso (p q : ℤ) :
    plusE F G (p + q) q ⊥ ⊤ bot_le le_top ≅
      plusFiltration F G (p + q) ⋙ FilteredObject.gr p := by
  have hn : p + q - q = p := by omega
  simpa only [hn] using
    (spectralObjectFiltrationGrIso (plusSpectralObject F G) (p + q) q ≪≫
      filteredUncurryGrIso (spectralObjectFiltration (plusSpectralObject F G) (p + q))
        (p + q - q))

/-- The graded isomorphism, read at a given admissible page. -/
private noncomputable def plusGradedIsoAt (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r)
    [(plusSeq F G K).HasPageInfinityAt (p, q)]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r]
    [IsIso (plusNuApp F G K p q r hr2 hpr)] :
    (plusSeq F G K).pageInfinity (p, q) ≅
      (FilteredObject.gr p).obj ((plusFiltration F G (p + q)).obj K) :=
  (plusSeq F G K).pageInfinityIso (p, q) r ≪≫
    (asIso (plusNuApp F G K p q r hr2 hpr)).symm ≪≫ (plusGrIso F G p q).app K

private lemma plusGradedIsoAt_hom (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r)
    [(plusSeq F G K).HasPageInfinityAt (p, q)]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r]
    [IsIso (plusNuApp F G K p q r hr2 hpr)] :
    (plusGradedIsoAt F G K p q r hr2 hpr).hom =
      ((plusSeq F G K).pageInfinityIso (p, q) r).hom ≫
        inv (plusNuApp F G K p q r hr2 hpr) ≫ ((plusGrIso F G p q).app K).hom :=
  rfl

/-- The infinity-page identification does not depend on the admissible page: the two
comparisons agree because `pageInfinityIso` and `plusNu` are both compatible with the edge
monomorphisms. -/
private lemma plusPageInfinityIso_comp_inv_nu (K : DerivedCategory.Plus A) (p q r r' : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r) (hr'2 : 2 ≤ r') (hpr' : p < r') (hrr' : r ≤ r')
    [(plusSeq F G K).HasPageInfinityAt (p, q)]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r']
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r']
    [IsIso (plusNuApp F G K p q r hr2 hpr)]
    [IsIso (plusNuApp F G K p q r' hr'2 hpr')] :
    ((plusSeq F G K).pageInfinityIso (p, q) r).hom ≫ inv (plusNuApp F G K p q r hr2 hpr) =
      ((plusSeq F G K).pageInfinityIso (p, q) r').hom ≫
        inv (plusNuApp F G K p q r' hr'2 hpr') := by
  have hsteps := plusNu_edgeMonoSteps F G K p q r hr2 hpr r' hrr'
  have hinv : (plusSeq F G K).edgeMonoSteps (p, q) r r' hrr' ≫
      inv (plusNuApp F G K p q r hr2 hpr) =
        inv (plusNuApp F G K p q r' hr'2 hpr') := by
    refine (cancel_epi (plusNuApp F G K p q r' hr'2 hpr')).1 ?_
    rw [← Category.assoc, hsteps, IsIso.hom_inv_id, IsIso.hom_inv_id]
  rw [← (plusSeq F G K).pageInfinityIso_hom_edgeMonoSteps (p, q) r r' hrr', Category.assoc,
    hinv]

private lemma plusGradedIsoAt_hom_eq (K : DerivedCategory.Plus A) (p q r r' : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r) (hr'2 : 2 ≤ r') (hpr' : p < r') (hrr' : r ≤ r')
    [(plusSeq F G K).HasPageInfinityAt (p, q)]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r']
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r']
    [IsIso (plusNuApp F G K p q r hr2 hpr)]
    [IsIso (plusNuApp F G K p q r' hr'2 hpr')] :
    (plusGradedIsoAt F G K p q r hr2 hpr).hom =
      (plusGradedIsoAt F G K p q r' hr'2 hpr').hom := by
  rw [plusGradedIsoAt_hom, plusGradedIsoAt_hom, ← Category.assoc, ← Category.assoc,
    plusPageInfinityIso_comp_inv_nu F G K p q r r' hr2 hpr hr'2 hpr' hrr']

/-- The infinity term at `(p, q)` is the graded piece of the abutment filtration. -/
private noncomputable def plusGradedIso (K : DerivedCategory.Plus A) (p q : ℤ) :
    (plusSeq F G K).pageInfinity (p, q) ≅
      (FilteredObject.gr p).obj ((plusFiltration F G (p + q)).obj K) :=
  have h2 : (2 : ℤ) ≤ max (max 2 (p + 1)) (q - plusBound K + 2) := by omega
  have hp : p < max (max 2 (p + 1)) (q - plusBound K + 2) := by omega
  have ha : q - plusBound K + 2 ≤ max (max 2 (p + 1)) (q - plusBound K + 2) := by omega
  haveI := plusSeq_hasPageInfinityAt F G K p q
  haveI := plusSeq_hasEdgeMonoAtFrom F G K p q _ h2 hp
  haveI := plusSeq_hasEdgeEpiAtFrom F G K p q _ h2 ha
  haveI := isIso_plusNu_app F G K p q _ h2 hp ha
  plusGradedIsoAt F G K p q _ h2 hp

private lemma plusGradedIso_hom_eq (K : DerivedCategory.Plus A) (p q r : ℤ)
    (hr2 : 2 ≤ r) (hpr : p < r)
    (hrr : max (max 2 (p + 1)) (q - plusBound K + 2) ≤ r)
    [(plusSeq F G K).HasPageInfinityAt (p, q)]
    [(plusSeq F G K).HasEdgeMonoAtFrom (p, q) r]
    [(plusSeq F G K).HasEdgeEpiAtFrom (p, q) r]
    [IsIso (plusNuApp F G K p q r hr2 hpr)] :
    (plusGradedIso F G K p q).hom = (plusGradedIsoAt F G K p q r hr2 hpr).hom := by
  have h2 : (2 : ℤ) ≤ max (max 2 (p + 1)) (q - plusBound K + 2) := by omega
  have hp : p < max (max 2 (p + 1)) (q - plusBound K + 2) := by omega
  have ha' : q - plusBound K + 2 ≤ max (max 2 (p + 1)) (q - plusBound K + 2) := by omega
  have := plusSeq_hasEdgeMonoAtFrom F G K p q _ h2 hp
  have := plusSeq_hasEdgeEpiAtFrom F G K p q _ h2 ha'
  have := isIso_plusNu_app F G K p q _ h2 hp ha'
  exact plusGradedIsoAt_hom_eq F G K p q _ r h2 hp hr2 hpr hrr

/-- Naturality of the graded isomorphism. Because `plusNu` and `plusGrIso` are natural
transformations of functors and the comparisons at different pages agree, this is just their
naturality at a page admissible for both objects. -/
private lemma plusGradedIso_naturality {K L : DerivedCategory.Plus A} (φ : K ⟶ L) (p q : ℤ) :
    SpectralSequence.Hom.mapPageInfinity (plusSeqMap F G φ) (p, q) ≫
        (plusGradedIso F G L p q).hom =
      (plusGradedIso F G K p q).hom ≫
        (FilteredObject.gr p).map ((plusFiltration F G (p + q)).map φ) := by
  have := plusSeq_hasPageInfinityAt F G K p q
  have := plusSeq_hasPageInfinityAt F G L p q
  have hR2 : 2 ≤ max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2) := by
    omega
  have hpR : p < max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2) := by
    omega
  have haK : q - plusBound K + 2 ≤
      max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2) := by omega
  have haL : q - plusBound L + 2 ≤
      max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2) := by omega
  have hbK : max (max 2 (p + 1)) (q - plusBound K + 2) ≤
      max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2) := by omega
  have hbL : max (max 2 (p + 1)) (q - plusBound L + 2) ≤
      max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2) := by omega
  have := plusSeq_hasEdgeMonoAtFrom F G K p q _ hR2 hpR
  have := plusSeq_hasEdgeEpiAtFrom F G K p q _ hR2 haK
  have := plusSeq_hasEdgeMonoAtFrom F G L p q _ hR2 hpR
  have := plusSeq_hasEdgeEpiAtFrom F G L p q _ hR2 haL
  have := isIso_plusNu_app F G K p q _ hR2 hpR haK
  have := isIso_plusNu_app F G L p q _ hR2 hpR haL
  -- Naturality of `plusNu` at the common page, and of the graded identification.
  -- Stated with the page map in the `plusSeq` spelling: the `E₂SpectralSequence.page` spelling
  -- makes the composite below well-typed only across the `spectralSequenceEvaluate`
  -- identification, and then `rw` refuses to abstract it.
  have hnat : (plusE F G (p + q) q ⊥ ⊤ bot_le le_top).map φ ≫
        plusNuApp F G L p q _ hR2 hpR =
      plusNuApp F G K p q _ hR2 hpR ≫ ((plusSeqMap F G φ).hom _ hR2).f (p, q) :=
    (plusNu F G p q _ hR2 hpR).naturality φ
  have hβ : (plusE F G (p + q) q ⊥ ⊤ bot_le le_top).map φ ≫
        ((plusGrIso F G p q).app L).hom =
      ((plusGrIso F G p q).app K).hom ≫
        (FilteredObject.gr p).map ((plusFiltration F G (p + q)).map φ) :=
    (plusGrIso F G p q).hom.naturality φ
  rw [plusGradedIso_hom_eq F G K p q _ hR2 hpR hbK,
    plusGradedIso_hom_eq F G L p q _ hR2 hpR hbL,
    plusGradedIsoAt_hom, plusGradedIsoAt_hom,
    SpectralSequence.Hom.mapPageInfinity_eq (plusSeqMap F G φ) (p, q)
      (max (max (max 2 (p + 1)) (q - plusBound K + 2)) (q - plusBound L + 2)) hR2,
    Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, cancel_epi]
  refine (cancel_epi (plusNuApp F G K p q _ hR2 hpR)).1 ?_
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← hnat, Category.assoc,
    IsIso.hom_inv_id_assoc]
  exact hβ

/-! #### The abutment -/

/-- A step of the evaluated image filtration is zero at an object where the inclusion of the
`H`-term vanishes. The functor-category statement `filteredUncurry_isBot` does not apply: the
lower vanishing holds only at each object separately. -/
private lemma plusFiltration_isBot (K : DerivedCategory.Plus A) (n p : ℤ)
    (hz : IsZero ((((derivedTruncationSpectralObjectFunctor F G).obj K).H n).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((n - p + 1 : ℤ) : EInt) from bot_le))))) :
    ((plusFiltration F G n).obj K).filtration.subobject (op p) = ⊥ := by
  have hη : (spectralObjectInclusion (plusSpectralObject F G) n (n - p + 1)).app K = 0 :=
    hz.eq_of_src _ _
  show Subobject.mk ((imageSubobject
    (spectralObjectInclusion (plusSpectralObject F G) n (n - p + 1))).arrow.app K) = ⊥
  rw [Subobject.mk_eq_bot_iff_zero]
  have : Epi ((factorThruImageSubobject
      (spectralObjectInclusion (plusSpectralObject F G) n (n - p + 1))).app K) :=
    (NatTrans.epi_iff_epi_app _).1 inferInstance K
  refine zero_of_epi_comp ((factorThruImageSubobject
    (spectralObjectInclusion (plusSpectralObject F G) n (n - p + 1))).app K) ?_
  rw [← NatTrans.comp_app, imageSubobject_arrow_comp, hη]

private lemma plusFiltration_isTop (K : DerivedCategory.Plus A) (n : ℤ) :
    ((plusFiltration F G n).obj K).filtration.subobject (op 0) = ⊤ :=
  filteredUncurry_isTop _ K 0
    (spectralObjectFiltration_isTop (plusSpectralObject F G) n
      (plusSpectralObject_isZero₂ F G ((n + 1 : ℤ) : EInt) ⊤ le_top n
        (WithBotTop.coe_lt_coe.mpr (by omega))))

private lemma plusFiltration_isFinite (K : DerivedCategory.Plus A) (n : ℤ) :
    Filtration.IsFinite ((plusFiltration F G n).obj K).filtration := by
  have := plusBound_isGE K
  refine (Filtration.isFinite_iff_subobject _).mpr
    ⟨⟨op 0, plusFiltration_isTop F G K n⟩, ⟨op (n - plusBound K + 1), ?_⟩⟩
  exact plusFiltration_isBot F G K n (n - plusBound K + 1)
    (derivedTruncationSpectralObject_isZero₁ F G K (plusBound K) ⊥
      ((n - (n - plusBound K + 1) + 1 : ℤ) : EInt) bot_le
      (WithBotTop.coe_le_coe.mpr (by omega)) n)

/-- The abutment of the Grothendieck spectral sequence on the bounded below derived category is
the derived functor of the composite, by [Stacks, Tag 015M]. -/
private noncomputable def plusAbutmentIso
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (n : ℤ) :
    ((plusSpectralObject F G).H n).obj
        (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≅
      (F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C n := by
  change (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
    DerivedCategory.Plus.homologyFunctor C n ≅ _
  exact Functor.isoWhiskerRight (compDerivedIso F G hFG)
    (DerivedCategory.Plus.homologyFunctor C n)

/-- The functorial right-half-plane abutment of the Grothendieck spectral sequence for bounded
below complexes. -/
@[no_expose] noncomputable def plusAbutment
    (hFG : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) :
    Stacks.Cohomology.Leray.FunctorialRightHalfPlaneAbutsTo
      (derivedTruncationSpectralSequenceFunctor F G)
      (fun n : ℤ => (F ⋙ G).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor C n) where
  filtration n := plusFiltration F G n
  abutmentIso n := plusAbutmentIso F G hFG n
  isFinite K n := plusFiltration_isFinite F G K n
  isTop K n := plusFiltration_isTop F G K n
  abutsTo K := abutsTo_of_finiteFiltration (plusSeq F G K) _
    (fun p q => plusSeq_hasPageInfinityAt F G K p q)
    (fun n => (plusFiltration F G n).obj K) (fun n => (plusAbutmentIso F G hFG n).app K)
    (fun n => plusFiltration_isFinite F G K n) (fun p q => plusGradedIso F G K p q)
  gradedIso K p q := plusGradedIso F G K p q
  gradedIso_naturality φ p q := plusGradedIso_naturality F G φ p q

end Plus

/-! #### Transport along an isomorphism of the abutting functors -/

/-- Transport a functorial right-half-plane abutment along a natural isomorphism of the
abutting functors. -/
@[no_expose] noncomputable def abutsToChangeAbutmentPlus
    {D A : Type*} [Category D] [Category A] [Abelian A]
    {E : D ⥤ E₂CohomologicalSpectralSequence A} {H H' : ℤ → D ⥤ A}
    (ab : Stacks.Cohomology.Leray.FunctorialRightHalfPlaneAbutsTo E H) (e : ∀ n, H n ≅ H' n) :
    Stacks.Cohomology.Leray.FunctorialRightHalfPlaneAbutsTo E H' where
  filtration := ab.filtration
  abutmentIso n := ab.abutmentIso n ≪≫ e n
  isFinite := ab.isFinite
  isTop := ab.isTop
  abutsTo K := abutsTo_of_finiteFiltration (E.obj K) _
    (ab.abutsTo K).1 (fun n => (ab.filtration n).obj K)
    (fun n => (ab.abutmentIso n).app K ≪≫ (e n).app K) (ab.isFinite K) (ab.gradedIso K)
  gradedIso := ab.gradedIso
  gradedIso_naturality := ab.gradedIso_naturality

end RightHalfPlane

end Construction

end Stacks.Cohomology.Grothendieck

end

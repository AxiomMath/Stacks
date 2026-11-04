module

public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity

/-!
# Convergence of the spectral sequence of a bounded spectral object

Mathlib builds, from a spectral object `X : CategoryTheory.Abelian.SpectralObject C EInt`, an
`E₂`-cohomological spectral sequence `X.spectralSequence coreE₂Cohomological` whose page `r` at
`(p, q)` is `E^{p+q}(q - r + 2 ≤ q ≤ q + 1 ≤ q + r - 1)`, and stops there: it proves nothing
about the infinity page, and there is no notion of a *bounded* spectral object.

This file supplies both.  `IsBounded` says that in each cohomological degree `n` the objects
`H^n(i ≤ j)` vanish once the window `[i, j]` lies entirely below some integer or entirely above
some integer.  For such an `X`:

* the differentials into and out of each `(p, q)` vanish on every sufficiently late page, so the
  spectral sequence has an infinity page everywhere;
* the late pages at `(p, q)` are all `E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)`, the *full window* at `q`,
  because widening the two outer indices is an isomorphism once the outer `H`'s vanish;
* the images of `H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)` form a finite filtration of the abutment
  `H^n(⊥ ≤ ⊤)`, whose graded pieces are exactly those full windows.

Together these give `CategoryTheory.SpectralSequence.AbutsTo` for the spectral sequence of `X`,
for the family `n ↦ H^n(⊥ ≤ ⊤)`.

## Main definitions

* `CategoryTheory.Abelian.SpectralObject.IsBounded`: boundedness of a spectral object indexed
  by `EInt`.
* `CategoryTheory.Abelian.SpectralObject.EFull`: the full window `E^{p+q}(⊥ ≤ q ≤ q+1 ≤ ⊤)`.
* `CategoryTheory.Abelian.SpectralObject.abutment` and
  `CategoryTheory.Abelian.SpectralObject.abutmentFiltration`: the abutment `H^n(⊥ ≤ ⊤)` and its
  filtration by the images of `H^n(⊥ ≤ j)`.

## Main results

* `CategoryTheory.Abelian.SpectralObject.EIsoCokernelOfLE`: for any spectral object and any
  three composable arrows, `E^n(f₁, f₂, f₃)` is the quotient of the image of `H^n(f₁ ≫ f₂)` by
  the image of `H^n(f₁)` inside `H^n(f₁ ≫ f₂ ≫ f₃)`.
* `CategoryTheory.Abelian.SpectralObject.pageXIsoEFull`: identification of a late page with the
  full window.
* `CategoryTheory.Abelian.SpectralObject.pageInfinityIsoEFull`: identification of the infinity
  page with the full window.
* `CategoryTheory.Abelian.SpectralObject.abutsTo_spectralSequence`: the convergence theorem --
  the spectral sequence of a bounded spectral object abuts to `n ↦ H^n(⊥ ≤ ⊤)`.

## Implementation notes

* The graded-piece identification `EIsoCokernelOfLE` is Mathlib's
  `Abelian.SpectralObject.cokernelSequenceOpcyclesE_exact`, which presents `E^n(f₁, f₂, f₃)` as
  the cokernel of `H^n(f₁) ⟶ opZ^n(f₁ ≫ f₂, f₃)`, composed with
  `cokernelIsoCokernelOfLE`: the elementary fact that an epi-mono presentation of a map
  identifies a cokernel with a quotient of image subobjects.  No new homological algebra is
  needed, and in particular no comparison between two spectral sequences.
* The abutment filtration is a family of **images of honest morphisms**, not a greatest lower
  bound of a family of subobjects, so none of the subobject-functoriality obstructions of the
  filtered-complex route arise here.
* Boundedness is stated as two existentials rather than with named bounds, so that
  `IsFirstQuadrant` -- Mathlib's first quadrant condition, whose bounds depend on the degree --
  is an instance of it.
-/

@[expose] public section

universe v u

open CategoryTheory Category Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]

section ImageQuotient

variable {U V T O : C}

/-- **An epi-mono presentation identifies a cokernel with a quotient of image subobjects.**
If `b : V ⟶ T` factors as an epi `e : V ⟶ O` followed by a mono `m : O ⟶ T`, and `a : U ⟶ T`
factors through `m` as `f : U ⟶ O`, then `cokernel f` is the quotient of `imageSubobject b` by
`imageSubobject a`. -/
noncomputable def cokernelIsoCokernelOfLE (a : U ⟶ T) (b : V ⟶ T)
    (h : imageSubobject a ≤ imageSubobject b)
    (e : V ⟶ O) [Epi e] (m : O ⟶ T) [Mono m] (he : e ≫ m = b)
    (f : U ⟶ O) (hf : f ≫ m = a) :
    cokernel f ≅ cokernel (Subobject.ofLE (imageSubobject a) (imageSubobject b) h) := by
  have := strongEpi_of_epi e
  let i : O ≅ (imageSubobject b : C) :=
    image.isoStrongEpiMono e m he ≪≫ (imageSubobjectIso b).symm
  have hi : i.hom ≫ (imageSubobject b).arrow = m := by simp [i]
  have hfi : f ≫ i.hom = factorThruImageSubobject a ≫
      Subobject.ofLE (imageSubobject a) (imageSubobject b) h := by
    apply (cancel_mono (imageSubobject b).arrow).1
    simp only [Category.assoc, hi, hf, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
  exact cokernel.mapIso f _ (Iso.refl _) i (by simpa using hfi) ≪≫
    cokernelEpiComp (factorThruImageSubobject a) (Subobject.ofLE _ _ h)

/-- **Equal subobjects have the same quotient.**  A congruence lemma for
`cokernel (Subobject.ofLE _ _ _)` in its two subobject arguments; the inclusion proofs are
irrelevant. -/
noncomputable def cokernelOfLECongr {Z : C} {A B A' B' : Subobject Z} (hA : A = A') (hB : B = B')
    (h : A ≤ B) (h' : A' ≤ B') :
    cokernel (Subobject.ofLE A B h) ≅ cokernel (Subobject.ofLE A' B' h') := by
  subst hA hB
  exact Iso.refl _

/-- **Equal morphisms have equal image subobjects.**  Stated separately because `rw` cannot
rewrite under `imageSubobject`: the `HasImage` instance argument mentions the morphism. -/
lemma imageSubobject_congr {A B : C} {f g : A ⟶ B} (h : f = g) :
    imageSubobject f = imageSubobject g := by
  subst h
  rfl

end ImageQuotient

section GradedPiece

variable {ι : Type*} [Category* ι] (X : SpectralObject C ι)

/-- **`E^n(f₁, f₂, f₃)` is a graded piece of the image filtration of `H^n(f₁ ≫ f₂ ≫ f₃)`.**
The image of `H^n(f₁)` inside `H^n(f₁ ≫ f₂ ≫ f₃)` is contained in the image of
`H^n(f₁ ≫ f₂)`, and the quotient is `E^n(f₁, f₂, f₃)`.

This is the graded-piece statement for an arbitrary spectral object, with no boundedness: it is
Mathlib's presentation of `E` as the cokernel of `H^n(f₁) ⟶ opZ^n(f₁ ≫ f₂, f₃)` rewritten
through the epi-mono factorisation `opZ^n(f₁ ≫ f₂, f₃) ⟶ H^n(f₁ ≫ f₂ ≫ f₃)` of
`H^n(f₁ ≫ f₂) ⟶ H^n(f₁ ≫ f₂ ≫ f₃)`. -/
noncomputable def EIsoCokernelOfLE {i j k l : ι}
    (f₁ : i ⟶ j) (f₂ : j ⟶ k) (f₃ : k ⟶ l) (f₁₂ : i ⟶ k) (h₁₂ : f₁ ≫ f₂ = f₁₂)
    (f₁₂₃ : i ⟶ l) (h₁₂₃ : f₁₂ ≫ f₃ = f₁₂₃) (n : ℤ) :
    X.E f₁ f₂ f₃ (n - 1) n (n + 1) ≅
      cokernel (Subobject.ofLE
        (imageSubobject ((X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫
          (X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃)))
        (imageSubobject ((X.H n).map (twoδ₂Toδ₁ f₁₂ f₃ f₁₂₃ h₁₂₃)))
        (imageSubobject_comp_le _ _)) := by
  let S := X.cokernelSequenceOpcyclesE f₁ f₂ f₃ f₁₂ h₁₂ (n - 1) n (n + 1)
  have hS := X.cokernelSequenceOpcyclesE_exact f₁ f₂ f₃ f₁₂ h₁₂ (n - 1) n (n + 1)
  exact hS.gIsCokernel.coconePointUniqueUpToIso (cokernelIsCokernel S.f) ≪≫
    cokernelIsoCokernelOfLE _ _ _ (X.pOpcycles f₁₂ f₃ n)
      (X.fromOpcycles f₁₂ f₃ f₁₂₃ h₁₂₃ n) (X.p_fromOpcycles f₁₂ f₃ f₁₂₃ h₁₂₃ n)
      ((X.H n).map (twoδ₂Toδ₁ f₁ f₂ f₁₂ h₁₂) ≫ X.pOpcycles f₁₂ f₃ n)
      ((Category.assoc _ _ _).trans
        (congrArg _ (X.p_fromOpcycles f₁₂ f₃ f₁₂₃ h₁₂₃ n)))

end GradedPiece

section Bounded

/-- **A bounded spectral object indexed by `EInt`.**  In each cohomological degree `n`, the
objects `H^n(i ≤ j)` vanish once the window `[i, j]` lies entirely below some integer `a`
(`j ≤ a`) or entirely above some integer `b` (`b ≤ i`).

The bounds are allowed to depend on `n`, which is what makes `IsFirstQuadrant` an instance. -/
class IsBounded (X : SpectralObject C EInt) : Prop where
  /-- in each degree, `H^n` vanishes on windows lying below some integer -/
  exists_isZero_of_le (n : ℤ) : ∃ a : ℤ, ∀ (i j : EInt) (hij : i ≤ j), j ≤ (a : EInt) →
      IsZero ((X.H n).obj (mk₁ (homOfLE hij)))
  /-- in each degree, `H^n` vanishes on windows lying above some integer -/
  exists_isZero_of_ge (n : ℤ) : ∃ b : ℤ, ∀ (i j : EInt) (hij : i ≤ j), (b : EInt) ≤ i →
      IsZero ((X.H n).obj (mk₁ (homOfLE hij)))

/-- **A first quadrant spectral object is bounded.**  Mathlib's `IsFirstQuadrant` says that
`H^n(i ≤ j)` vanishes when `j ≤ 0` and when `n < i`; these are the two bounds, the second
depending on `n`. -/
instance (X : SpectralObject C EInt) [X.IsFirstQuadrant] : X.IsBounded where
  exists_isZero_of_le n := ⟨0, fun i j hij hj ↦ X.isZero₁_of_isFirstQuadrant i j hij hj n⟩
  exists_isZero_of_ge n := ⟨n + 1, fun i j hij hi ↦
    X.isZero₂_of_isFirstQuadrant i j hij n
      ((WithBotTop.coe_lt_coe.2 (by lia : n < n + 1)).trans_le hi)⟩

variable (X : SpectralObject C EInt)

/-- **The differentials into `(p, q)` vanish on the page `r`** as soon as `H^{p+q-1}` vanishes
on windows above `q + r - 1`: the source `E_r^{p-r, q+r-1}` of the only differential into
`(p, q)` is then zero. -/
lemma hasEdgeMonoAt (p q r b : ℤ) (hr : 2 ≤ r)
    (hb : ∀ (i j : EInt) (hij : i ≤ j), (b : EInt) ≤ i →
      IsZero ((X.H (p + q - 1)).obj (mk₁ (homOfLE hij))))
    (hrb : b ≤ q + r - 1) :
    (X.spectralSequence coreE₂Cohomological).HasEdgeMonoAt (p, q) r where
  le := hr
  zero pq' := by
    by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel pq' (p, q)
    · obtain ⟨p', q'⟩ := pq'
      have h : (p' + r, q' + (1 - r)) = (p, q) := hrel
      rw [Prod.mk.injEq] at h
      obtain rfl : p' = p - r := by lia
      obtain rfl : q' = q + r - 1 := by lia
      refine IsZero.eq_of_src ?_ _ _
      refine X.isZero_spectralSequence_page_X_of_isZero_H coreE₂Cohomological r hr _
        (p + q - 1) (by simp only [coreE₂Cohomological_deg]; lia)
        ((q + r - 1 : ℤ) : EInt) ((q + r : ℤ) : EInt) rfl (by norm_num) ?_
      exact hb _ _ _ (WithBotTop.coe_le_coe.2 hrb)
    · exact HomologicalComplex.shape _ _ _ hrel

/-- **The differentials out of `(p, q)` vanish on the page `r`** as soon as `H^{p+q+1}` vanishes
on windows below `q + 2 - r`: the target `E_r^{p+r, q+1-r}` of the only differential out of
`(p, q)` is then zero. -/
lemma hasEdgeEpiAt (p q r a : ℤ) (hr : 2 ≤ r)
    (ha : ∀ (i j : EInt) (hij : i ≤ j), j ≤ (a : EInt) →
      IsZero ((X.H (p + q + 1)).obj (mk₁ (homOfLE hij))))
    (hra : q + 2 - r ≤ a) :
    (X.spectralSequence coreE₂Cohomological).HasEdgeEpiAt (p, q) r where
  le := hr
  zero pq' := by
    by_cases hrel : (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).Rel (p, q) pq'
    · obtain ⟨p', q'⟩ := pq'
      have h : (p + r, q + (1 - r)) = (p', q') := hrel
      rw [Prod.mk.injEq] at h
      obtain rfl : p' = p + r := by lia
      obtain rfl : q' = q + 1 - r := by lia
      refine IsZero.eq_of_tgt ?_ _ _
      refine X.isZero_spectralSequence_page_X_of_isZero_H coreE₂Cohomological r hr _
        (p + q + 1) (by simp only [coreE₂Cohomological_deg]; lia)
        ((q + 1 - r : ℤ) : EInt) ((q + 2 - r : ℤ) : EInt) rfl (by norm_num; lia) ?_
      exact ha _ _ _ (WithBotTop.coe_le_coe.2 hra)
    · exact HomologicalComplex.shape _ _ _ hrel

/-- **The spectral sequence of a bounded spectral object has an infinity page everywhere.** -/
instance hasPageInfinityAt [X.IsBounded] (pq : ℤ × ℤ) :
    (X.spectralSequence coreE₂Cohomological).HasPageInfinityAt pq := by
  obtain ⟨p, q⟩ := pq
  obtain ⟨a, ha⟩ := IsBounded.exists_isZero_of_le (X := X) (p + q + 1)
  obtain ⟨b, hb⟩ := IsBounded.exists_isZero_of_ge (X := X) (p + q - 1)
  exact
    { nonempty_hasEdgeMonoSet := ⟨max 2 (b - q + 1), le_max_left _ _, fun r hr ↦
        X.hasEdgeMonoAt p q r b ((le_max_left _ _).trans hr) hb
          (by have := (le_max_right 2 (b - q + 1)).trans hr; lia)⟩
      nonempty_hasEdgeEpiSet := ⟨max 2 (q + 2 - a), le_max_left _ _, fun r hr ↦
        X.hasEdgeEpiAt p q r a ((le_max_left _ _).trans hr) ha
          (by have := (le_max_right 2 (q + 2 - a)).trans hr; lia)⟩ }

/-- **The full window at `q`:** `E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)`.  This is the value of every
sufficiently late page of `X.spectralSequence coreE₂Cohomological` at `(p, q)` when `X` is
bounded, hence of the infinity page. -/
noncomputable def EFull (p q : ℤ) : C :=
  X.E (homOfLE (bot_le : (⊥ : EInt) ≤ (q : EInt)))
    (homOfLE (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia)))
    (homOfLE (le_top : ((q + 1 : ℤ) : EInt) ≤ (⊤ : EInt)))
    (p + q - 1) (p + q) (p + q + 1)

/-- **A late page is the full window.**  Widening `i₀` from `q - r + 2` down to `⊥` and `i₃` from
`q + r - 1` up to `⊤` are isomorphisms once `H^{p+q+1}(⊥ ≤ q - r + 2)` and
`H^{p+q-1}(q + r - 1 ≤ ⊤)` vanish, which is Mathlib's `isoMapFourδ₁Toδ₀'` and
`isoMapFourδ₄Toδ₃'`. -/
noncomputable def pageXIsoEFull (p q r : ℤ) (hr : 2 ≤ r)
    (h₁ : IsZero ((X.H (p + q + 1)).obj
      (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q - r + 2 : ℤ) : EInt))))))
    (h₂ : IsZero ((X.H (p + q - 1)).obj
      (mk₁ (homOfLE (le_top : ((q + r - 1 : ℤ) : EInt) ≤ (⊤ : EInt)))))) :
    ((X.spectralSequence coreE₂Cohomological).page r hr).X (p, q) ≅ X.EFull p q :=
  X.spectralSequencePageXIso coreE₂Cohomological r hr (p, q)
      ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt)
      rfl rfl rfl rfl (p + q - 1) (p + q) (p + q + 1)
      (by simp only [coreE₂Cohomological_deg]) ≪≫
    (X.isoMapFourδ₁Toδ₀' ⊥ ((q - r + 2 : ℤ) : EInt) (q : EInt) ((q + 1 : ℤ) : EInt)
        ((q + r - 1 : ℤ) : EInt) bot_le
        (WithBotTop.coe_le_coe.2 (show q - r + 2 ≤ q by lia))
        (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia))
        (WithBotTop.coe_le_coe.2 (show q + 1 ≤ q + r - 1 by lia))
        (p + q - 1) (p + q) (p + q + 1) h₁).symm ≪≫
    X.isoMapFourδ₄Toδ₃' ⊥ (q : EInt) ((q + 1 : ℤ) : EInt) ((q + r - 1 : ℤ) : EInt) ⊤
      bot_le (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia))
      (WithBotTop.coe_le_coe.2 (show q + 1 ≤ q + r - 1 by lia)) le_top
      (p + q - 1) (p + q) (p + q + 1) h₂

/-- **The infinity page is the full window.**  For a bounded spectral object, the page `r` at
`(p, q)` is `X.EFull p q` for every `r` large enough that all the differentials into and out of
`(p, q)` have already vanished, so the infinity page is too. -/
lemma nonempty_pageInfinityIsoEFull [X.IsBounded] (p q : ℤ) :
    Nonempty ((X.spectralSequence coreE₂Cohomological).pageInfinity (p, q) ≅ X.EFull p q) := by
  obtain ⟨a, ha⟩ := IsBounded.exists_isZero_of_le (X := X) (p + q + 1)
  obtain ⟨b, hb⟩ := IsBounded.exists_isZero_of_ge (X := X) (p + q - 1)
  obtain ⟨r, hr₂, hrb, hra⟩ : ∃ r : ℤ, 2 ≤ r ∧ b - q + 1 ≤ r ∧ q + 2 - a ≤ r :=
    ⟨max 2 (max (b - q + 1) (q + 2 - a)), le_max_left _ _,
      (le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩
  have hmono : (X.spectralSequence coreE₂Cohomological).HasEdgeMonoAtFrom (p, q) r :=
    SpectralSequence.HasEdgeMonoAtFrom.mk' _ (p, q) r
      (fun k ↦ X.hasEdgeMonoAt p q (r + k) b (by lia) hb (by lia)) (by lia)
  have hepi : (X.spectralSequence coreE₂Cohomological).HasEdgeEpiAtFrom (p, q) r :=
    SpectralSequence.HasEdgeEpiAtFrom.mk' _ (p, q) r
      (fun k ↦ X.hasEdgeEpiAt p q (r + k) a (by lia) ha (by lia)) (by lia)
  exact ⟨SpectralSequence.pageInfinityIso _ (p, q) r ≪≫
    X.pageXIsoEFull p q r hr₂ (ha _ _ _ (WithBotTop.coe_le_coe.2 (by lia)))
      (hb _ _ _ (WithBotTop.coe_le_coe.2 (by lia)))⟩

/-- **The infinity page is the full window**, as data; see `nonempty_pageInfinityIsoEFull`. -/
noncomputable def pageInfinityIsoEFull [X.IsBounded] (p q : ℤ) :
    (X.spectralSequence coreE₂Cohomological).pageInfinity (p, q) ≅ X.EFull p q :=
  (X.nonempty_pageInfinityIsoEFull p q).some

/-- **The abutment of a spectral object in degree `n`:** `H^n(⊥ ≤ ⊤)`. -/
noncomputable def abutment (n : ℤ) : C :=
  (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (⊤ : EInt))))

/-- **The canonical map `H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)`**, induced by the inclusion of the window
`[⊥, j]` into `[⊥, ⊤]`. -/
noncomputable def toAbutment (n : ℤ) (j : EInt) :
    (X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ j))) ⟶ X.abutment n :=
  (X.H n).map (twoδ₂Toδ₁' (⊥ : EInt) j ⊤ bot_le le_top)

/-- **`toAbutment` factors through any intermediate window.** -/
lemma toAbutment_eq (n : ℤ) (j j' : EInt) (hjj' : j ≤ j') :
    X.toAbutment n j =
      (X.H n).map (twoδ₂Toδ₁' (⊥ : EInt) j j' bot_le hjj') ≫ X.toAbutment n j' :=
  (X.H n).map_comp _ _

/-- **The filtration of the abutment** by the images of the windows `[⊥, j]`. -/
noncomputable def abutmentFiltration (n : ℤ) (j : EInt) : Subobject (X.abutment n) :=
  imageSubobject (X.toAbutment n j)

/-- **The abutment filtration is increasing in the window.**  Immediate from `toAbutment_eq`
and `imageSubobject_comp_le`: the image of a composite is contained in the image of its second
factor. -/
lemma abutmentFiltration_monotone (n : ℤ) : Monotone (X.abutmentFiltration n) :=
  fun j j' hjj' ↦ (imageSubobject_congr (X.toAbutment_eq n j j' hjj')).le.trans
    (imageSubobject_comp_le _ _)

/-- A rewriting helper: the filtration at two equal integer windows agrees. -/
lemma abutmentFiltration_congr (n : ℤ) {j j' : ℤ} (h : j = j') :
    X.abutmentFiltration n (j : EInt) = X.abutmentFiltration n (j' : EInt) := by
  rw [h]

/-- **The filtration is `⊥` where the window has no cohomology.** -/
lemma abutmentFiltration_eq_bot (n : ℤ) (j : EInt)
    (h : IsZero ((X.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ j))))) :
    X.abutmentFiltration n j = ⊥ :=
  (imageSubobject_congr (h.eq_of_src (X.toAbutment n j) 0)).trans imageSubobject_zero

/-- **The filtration is `⊤` where the complementary window has no cohomology.**  The long exact
sequence of the triple `⊥ ≤ j ≤ ⊤` makes `toAbutment` an epimorphism as soon as `H^n(j ≤ ⊤)`
vanishes, and the image of an epimorphism is the whole object. -/
lemma abutmentFiltration_eq_top (n : ℤ) (j : EInt)
    (h : IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : j ≤ (⊤ : EInt)))))) :
    X.abutmentFiltration n j = ⊤ := by
  have hepi : Epi (X.toAbutment n j) :=
    (X.exact₂ (homOfLE (bot_le : (⊥ : EInt) ≤ j)) (homOfLE (le_top : j ≤ (⊤ : EInt))) _
      rfl n).epi_f (h.eq_of_tgt _ _)
  have := epi_of_epi_fac (imageSubobject_arrow_comp (X.toAbutment n j))
  have := isIso_of_mono_of_epi (imageSubobject (X.toAbutment n j)).arrow
  exact Subobject.eq_top_of_isIso_arrow (imageSubobject (X.toAbutment n j))

/-- **The graded pieces of the abutment filtration are the full windows.**  The step from `q` to
`q + 1` of the filtration of `H^{p+q}(⊥ ≤ ⊤)` has quotient `E^{p+q}(⊥ ≤ q ≤ q+1 ≤ ⊤)`.

This is `EIsoCokernelOfLE` for the four arrows `⊥ ≤ q ≤ q + 1 ≤ ⊤`; it holds with no
boundedness hypothesis. -/
noncomputable def EFullIsoCokernelOfLE (p q : ℤ) :
    X.EFull p q ≅ cokernel (Subobject.ofLE (X.abutmentFiltration (p + q) (q : EInt))
      (X.abutmentFiltration (p + q) ((q + 1 : ℤ) : EInt))
      (X.abutmentFiltration_monotone (p + q)
        (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia)))) :=
  X.EIsoCokernelOfLE _ _ _ (homOfLE (bot_le : (⊥ : EInt) ≤ ((q + 1 : ℤ) : EInt))) rfl
      (homOfLE (bot_le : (⊥ : EInt) ≤ (⊤ : EInt))) rfl (p + q) ≪≫
    cokernelOfLECongr
      (imageSubobject_congr (X.toAbutment_eq (p + q) (q : EInt) ((q + 1 : ℤ) : EInt)
        (WithBotTop.coe_le_coe.2 (show q ≤ q + 1 by lia))).symm) rfl _ _

/-- **Convergence of the spectral sequence of a bounded spectral object.**  For a bounded
spectral object `X` indexed by `EInt`, the `E₂`-cohomological spectral sequence
`X.spectralSequence coreE₂Cohomological` has an infinity page at every bidegree, and the images
of `H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤)` form a finite decreasing filtration of the abutment
`H^n(⊥ ≤ ⊤)` -- indexed by `p ↦ H^n(⊥ ≤ n - p + 1)` -- whose graded pieces are the terms
`E_∞^{p, n-p}`.

This is `CategoryTheory.SpectralSequence.AbutsTo` for the spectral sequence of `X` and the
abutment family `n ↦ H^n(⊥ ≤ ⊤)`, spelled out so that this file does not have to import the
definition. -/
theorem abutsTo_spectralSequence [X.IsBounded] :
    (∀ p q : ℤ, (X.spectralSequence coreE₂Cohomological).HasPageInfinityAt (p, q)) ∧
      ∃ (F : ∀ n : ℤ, ℤ → Subobject (X.abutment n)) (hF : ∀ n : ℤ, Antitone (F n)),
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ F n a = ⊤ ∧ F n b = ⊥) ∧
        ∀ p q : ℤ, Nonempty
          ((X.spectralSequence coreE₂Cohomological).pageInfinity (p, q) ≅
            cokernel (Subobject.ofLE (F (p + q) (p + 1)) (F (p + q) p)
              (hF (p + q) (by lia)))) := by
  refine ⟨fun p q ↦ inferInstance,
    fun n p ↦ X.abutmentFiltration n ((n - p + 1 : ℤ) : EInt),
    fun n p p' hpp' ↦ X.abutmentFiltration_monotone n
      (WithBotTop.coe_le_coe.2 (by lia)), fun n ↦ ?_, fun p q ↦ ?_⟩
  · obtain ⟨a, ha⟩ := IsBounded.exists_isZero_of_le (X := X) n
    obtain ⟨b, hb⟩ := IsBounded.exists_isZero_of_ge (X := X) n
    refine ⟨min (n + 1 - b) (n + 1 - a), max (n + 1 - b) (n + 1 - a),
      min_le_max, ?_, ?_⟩
    · exact X.abutmentFiltration_eq_top n _ (hb _ _ _ (WithBotTop.coe_le_coe.2
        (by have := min_le_left (n + 1 - b) (n + 1 - a); lia)))
    · exact X.abutmentFiltration_eq_bot n _ (ha _ _ _ (WithBotTop.coe_le_coe.2
        (by have := le_max_right (n + 1 - b) (n + 1 - a); lia)))
  · exact ⟨X.pageInfinityIsoEFull p q ≪≫ X.EFullIsoCokernelOfLE p q ≪≫
      cokernelOfLECongr (X.abutmentFiltration_congr (p + q) (show q = p + q - (p + 1) + 1 by lia))
        (X.abutmentFiltration_congr (p + q) (show q + 1 = p + q - p + 1 by lia)) _ _⟩

end Bounded

end CategoryTheory.Abelian.SpectralObject

end

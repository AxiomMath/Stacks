module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring.RingNF
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Homology.SpectralSequence.Boundedness
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Cycles
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic.InducedFiltration

/-!
# Spectral sequences of filtered complexes: the page complexes

Finite filtrations and weak Serre classes, filtrations of cohomology by cocycles, the subobjects
`F^p K^n`, `Z_r^{p, q}` and `D_r^{p, q}`, and the page complexes of the spectral sequence of a
filtered complex with the cokernel side of the page turn.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Preadditive Opposite

section Quotients

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A quotient by an equality is zero: the graded piece cut out by two equal subobjects. -/
private lemma isZero_cokernel_ofLE {B : A} {X Y : Subobject B} (h : X ≤ Y) (h' : Y ≤ X) :
    IsZero (cokernel (Subobject.ofLE X Y h)) := by
  have hfac : Subobject.ofLE Y X h' ≫ Subobject.ofLE X Y h = 𝟙 _ := by
    rw [← cancel_mono Y.arrow]; simp
  have : Epi (Subobject.ofLE X Y h) := epi_of_epi_fac hfac
  exact isZero_cokernel_of_epi _

/-- Equal pairs of nested subobjects have the same quotient, so a property of one is a property
of the other. -/
lemma prop_cokernel_ofLE_congr (P : ObjectProperty A) {B : A}
    {W V W' V' : Subobject B} (h : W ≤ V) (h' : W' ≤ V') (hW : W = W') (hV : V = V')
    (hP : P (cokernel (Subobject.ofLE W V h))) : P (cokernel (Subobject.ofLE W' V' h')) := by
  subst hW; subst hV; exact hP

/-- A morphism out of `V` vanishes on a join as soon as it vanishes on each of the two parts. -/
private lemma ofLE_sup_comp_eq_zero {B Q : A} {X Y V : Subobject B} (hX : X ≤ V) (hY : Y ≤ V)
    (g : (V : A) ⟶ Q) (h1 : Subobject.ofLE X V hX ≫ g = 0)
    (h2 : Subobject.ofLE Y V hY ≫ g = 0) :
    Subobject.ofLE (X ⊔ Y) V (sup_le hX hY) ≫ g = 0 := by
  obtain ⟨T', z, hz, β, γ, fac⟩ := Subobject.exists_refinement_of_factors_sup (X ⊔ Y).arrow
    (Subobject.factors_self _)
  refine zero_of_epi_comp z ?_
  rw [← Category.assoc, show z ≫ Subobject.ofLE (X ⊔ Y) V (sup_le hX hY)
      = β ≫ Subobject.ofLE X V hX + γ ≫ Subobject.ofLE Y V hY from by
    rw [← cancel_mono V.arrow, Preadditive.add_comp, Category.assoc, Category.assoc,
      Category.assoc, Subobject.ofLE_arrow, Subobject.ofLE_arrow, Subobject.ofLE_arrow, fac],
    Preadditive.add_comp, Category.assoc, Category.assoc, h1, h2, comp_zero, comp_zero, add_zero]

/-- **A quotient in the subobject lattice, computed by an epimorphism.** If `W ≤ V` are subobjects
of `B` and `g` is an epimorphism out of `V` which kills `W` and whose kernel is contained in `W`,
then the target of `g` is `V/W`. -/
private lemma nonempty_cokernel_ofLE_iso_of_epi {B Q : A} {W V : Subobject B} (h : W ≤ V)
    (g : (V : A) ⟶ Q) [Epi g] (h1 : Subobject.ofLE W V h ≫ g = 0)
    (h2 : ∀ {T : A} (t : T ⟶ (V : A)), t ≫ g = 0 → W.Factors (t ≫ V.arrow)) :
    Nonempty (cokernel (Subobject.ofLE W V h) ≅ Q) := by
  refine ⟨(Subobject.exists_iso_of_epi_of_kernel (cokernel.π (Subobject.ofLE W V h)) g ?_
    ?_).choose⟩
  · rw [← cokernel.π_desc _ g h1, ← Category.assoc, kernel.condition, zero_comp]
  · have hfac := h2 (kernel.ι g) (kernel.condition g)
    rw [show kernel.ι g = W.factorThru _ hfac ≫ Subobject.ofLE W V h from by
      rw [← cancel_mono V.arrow, Category.assoc, Subobject.ofLE_arrow,
        Subobject.factorThru_arrow], Category.assoc, cokernel.condition, comp_zero]

/-- **An object with a finite filtration whose graded pieces satisfy `P` satisfies `P`.** Here `P`
is a weak Serre class and the filtration is a decreasing family of subobjects of `X` which is `⊤`
at `a` and `⊥` at `b`. -/
public lemma prop_of_filtration {X : A} (P : ObjectProperty A) [P.IsWeakSerreClass]
    (G : ℤ → Subobject X) (hanti : ∀ p : ℤ, G (p + 1) ≤ G p) (a b : ℤ) (hab : a ≤ b)
    (htop : G a = ⊤) (hbot : G b = ⊥)
    (hgr : ∀ p : ℤ, P (cokernel (Subobject.ofLE (G (p + 1)) (G p) (hanti p)))) : P X := by
  have hstep : ∀ p : ℤ, P ((G (p + 1) : A)) → P ((G p : A)) := fun p h1 =>
    P.prop_X₂_of_shortExact
      (S := ShortComplex.mk (Subobject.ofLE _ _ (hanti p))
        (cokernel.π (Subobject.ofLE _ _ (hanti p))) (by simp))
      (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance)
      h1 (hgr p)
  have hbot' : P ((G b : A)) :=
    P.prop_of_isZero (IsZero.of_mono_eq_zero (G b).arrow (by
      rw [← Subobject.mk_eq_bot_iff_zero, Subobject.mk_arrow]; exact hbot))
  have key : ∀ k : ℕ, P ((G (b - (k : ℤ)) : A)) := fun k => by
    induction k with
    | zero => rwa [Nat.cast_zero, sub_zero]
    | succ k ih => exact hstep _ (by
        rwa [show b - ((k + 1 : ℕ) : ℤ) + 1 = b - (k : ℤ) from by push_cast; ring])
  have : IsIso (G a).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr htop
  exact P.prop_of_iso (asIso (G a).arrow)
    (by simpa only [show b - ((b - a).toNat : ℤ) = a from by omega] using key (b - a).toNat)

end Quotients

section CocycleFiltrations

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The homology of a complex whose terms satisfy a weak Serre class property satisfies it too. -/
private lemma prop_homology (P : ObjectProperty A) [P.IsWeakSerreClass] {ι : Type*}
    {c : ComplexShape ι} (L : HomologicalComplex A c) (j : ι) [L.HasHomology j]
    (hL : ∀ m, P (L.X m)) : P (L.homology j) :=
  P.prop_of_isColimit_cokernelCofork (L.homologyIsCokernel (c.prev j) j rfl) (hL _)
    (P.prop_of_isLimit_kernelFork (L.cyclesIsKernel j (c.next j) rfl) (hL j) (hL _))

/-- A weak Serre class containing one page of a spectral sequence contains every later page: the
pages that follow are iterated homology of it. -/
lemma prop_page_of_le {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}
    (E : SpectralSequence A c r₀) (P : ObjectProperty A) [P.IsWeakSerreClass] {r : ℤ}
    (hr : r₀ ≤ r) (hpage : ∀ pq : ι, P ((E.page r hr).X pq)) :
    ∀ r' : ℤ, r ≤ r' → ∀ (hr' : r₀ ≤ r') (pq : ι), P ((E.page r' hr').X pq) := by
  intro r' hle
  induction r', hle using Int.leInduction with
  | base => exact fun _ pq => hpage pq
  | succ m hm ih =>
    have hm0 : r₀ ≤ m := hr.trans hm
    exact fun _ pq => P.prop_of_iso (E.iso m (m + 1) pq rfl hm0)
      (prop_homology P (E.page m hm0) pq (fun x => ih hm0 x))

/-- A morphism of cochain complexes which is an isomorphism in the three degrees `n - 1, n, n + 1`
induces an isomorphism on `H^n`. -/
public lemma CochainComplex.isIso_homologyMap_of_isIso_f
    {L M : CochainComplex A ℤ} (φ : L ⟶ M) (n : ℤ)
    (h₁ : IsIso (φ.f (n - 1))) (h₂ : IsIso (φ.f n)) (h₃ : IsIso (φ.f (n + 1))) :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  have e₁ : IsIso (φ.f ((ComplexShape.up ℤ).prev n)) := by
    rwa [show (ComplexShape.up ℤ).prev n = n - 1 from by simp]
  have e₃ : IsIso (φ.f ((ComplexShape.up ℤ).next n)) := by
    rwa [show (ComplexShape.up ℤ).next n = n + 1 from by simp]
  set ψ := (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map φ with hψ
  have : IsIso ψ.τ₁ := e₁
  have : IsIso ψ.τ₂ := h₂
  have : IsIso ψ.τ₃ := e₃
  have : IsIso ψ := ShortComplex.isIso_of_isIso ψ
  exact inferInstanceAs (IsIso (ShortComplex.homologyMap ψ))

/-- A subobject of `L^n` contained in another one annihilated by `d^n` is itself annihilated
by `d^n`. -/
lemma arrow_comp_d_eq_zero_of_le {L : CochainComplex A ℤ} {n : ℤ}
    {U V : Subobject (L.X n)} (h : U ≤ V) (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    U.arrow ≫ L.d n (n + 1) = 0 := by
  rw [← Subobject.ofLE_arrow h, Category.assoc, hV, comp_zero]

/-- A subobject `V` of `L^n` annihilated by `d^n` lifts to the cocycles `Z^n(L)`. -/
private noncomputable def toCycles (L : CochainComplex A ℤ) (n : ℤ) {V : Subobject (L.X n)}
    (hV : V.arrow ≫ L.d n (n + 1) = 0) : (V : A) ⟶ L.cycles n :=
  L.liftCycles V.arrow (n + 1) (by simp) hV

private lemma toCycles_comp_iCycles (L : CochainComplex A ℤ) (n : ℤ) {V : Subobject (L.X n)}
    (hV : V.arrow ≫ L.d n (n + 1) = 0) : toCycles L n hV ≫ L.iCycles n = V.arrow := by
  unfold toCycles
  exact L.liftCycles_i _ _ _ _

/-- The cohomology class of a cocycle: the map `V ⟶ H^n(L)` attached to a subobject `V` of `L^n`
annihilated by `d^n`. Its image is the piece of the induced filtration cut out by `V`. -/
private noncomputable def toHomology (L : CochainComplex A ℤ) (n : ℤ) {V : Subobject (L.X n)}
    (hV : V.arrow ≫ L.d n (n + 1) = 0) : (V : A) ⟶ L.homology n :=
  toCycles L n hV ≫ L.homologyπ n

private lemma toCycles_comp_homologyπ (L : CochainComplex A ℤ) (n : ℤ) {V : Subobject (L.X n)}
    (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    toCycles L n hV ≫ L.homologyπ n = toHomology L n hV := by
  rw [toHomology]

private lemma ofLE_comp_toCycles (L : CochainComplex A ℤ) (n : ℤ) {U V : Subobject (L.X n)}
    (h : U ≤ V) (hU : U.arrow ≫ L.d n (n + 1) = 0) (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    Subobject.ofLE U V h ≫ toCycles L n hV = toCycles L n hU := by
  rw [← cancel_mono (L.iCycles n), Category.assoc, toCycles_comp_iCycles, toCycles_comp_iCycles,
    Subobject.ofLE_arrow]

private lemma ofLE_comp_toHomology (L : CochainComplex A ℤ) (n : ℤ) {U V : Subobject (L.X n)}
    (h : U ≤ V) (hU : U.arrow ≫ L.d n (n + 1) = 0) (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    Subobject.ofLE U V h ≫ toHomology L n hV = toHomology L n hU := by
  rw [← toCycles_comp_homologyπ, ← toCycles_comp_homologyπ, ← Category.assoc,
    ofLE_comp_toCycles L n h hU hV]

/-- Nested subobjects of cocycles have nested images in `H^n(L)`. -/
private lemma imageSubobject_toHomology_le_of_le (L : CochainComplex A ℤ) (n : ℤ)
    {U V : Subobject (L.X n)} (h : U ≤ V) (hU : U.arrow ≫ L.d n (n + 1) = 0)
    (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    imageSubobject (toHomology L n hU) ≤ imageSubobject (toHomology L n hV) := by
  rw [← ofLE_comp_toHomology L n h hU hV]
  exact imageSubobject_comp_le _ _

/-- The image of a subobject of cocycles, computed in `Z^n(L)` and pushed back to `L^n`, is the
subobject itself. -/
private lemma exists_iCycles_imageSubobject_toCycles (L : CochainComplex A ℤ) (n : ℤ)
    {V : Subobject (L.X n)} (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    (Subobject.«exists» (L.iCycles n)).obj (imageSubobject (toCycles L n hV)) = V := by
  rw [← Subobject.imageSubobject_comp_eq_exists, toCycles_comp_iCycles, imageSubobject_mono,
      Subobject.mk_arrow]

private lemma imageSubobject_toHomology (L : CochainComplex A ℤ) (n : ℤ)
    {V : Subobject (L.X n)} (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    imageSubobject (toHomology L n hV)
      = (Subobject.«exists» (L.homologyπ n)).obj (imageSubobject (toCycles L n hV)) := by
  rw [← Subobject.imageSubobject_comp_eq_exists, toCycles_comp_homologyπ]

/-- **A coboundary has zero cohomology class.** -/
private lemma toHomology_eq_zero (L : CochainComplex A ℤ) (n : ℤ) {V : Subobject (L.X n)}
    (hV : V.arrow ≫ L.d n (n + 1) = 0) (h : V ≤ imageSubobject (L.d (n - 1) n)) :
    toHomology L n hV = 0 := by
  rw [← toCycles_comp_homologyπ]
  refine (kernelSubobject_factors_iff (L.homologyπ n) _).1 ?_
  have hk : (kernelSubobject (L.homologyπ n) ⊔ kernelSubobject (L.iCycles n)).Factors
      (toCycles L n hV) := by
    refine factors_sup_kernelSubobject (L.iCycles n) _ _ ?_
    rw [exists_iCycles_kernelSubobject_homologyπ, toCycles_comp_iCycles]
    exact Subobject.factors_of_le _ h (Subobject.factors_self _)
  rwa [Subobject.kernelSubobject_eq_bot_of_mono (L.iCycles n), sup_bot_eq] at hk

/-- **The cocycles cover `H^n(L)`.** -/
private lemma imageSubobject_toHomology_eq_top (L : CochainComplex A ℤ) (n : ℤ)
    {V : Subobject (L.X n)} (hV : V.arrow ≫ L.d n (n + 1) = 0)
    (h : kernelSubobject (L.d n (n + 1)) ≤ V) : imageSubobject (toHomology L n hV) = ⊤ := by
  have hfac : V.Factors (L.iCycles n) := by
    rw [le_antisymm (Subobject.le_of_factors (kernelSubobject_factors _ _ hV)) h]
    exact kernelSubobject_factors _ _ (L.iCycles_d n (n + 1))
  have hsplit : V.factorThru (L.iCycles n) hfac ≫ toCycles L n hV = 𝟙 _ := by
    rw [← cancel_mono (L.iCycles n), Category.assoc, toCycles_comp_iCycles,
      Subobject.factorThru_arrow, Category.id_comp]
  have : IsSplitEpi (toCycles L n hV) := ⟨⟨_, hsplit⟩⟩
  have : Epi (toHomology L n hV) := by
    rw [← toCycles_comp_homologyπ]; exact epi_comp _ _
  exact Subobject.imageSubobject_eq_top_of_epi _

/-- **The graded pieces of the filtration that a filtration by cocycles induces on cohomology.**
Let `U ≤ V` be subobjects of `L^n` annihilated by `d^n`, and let `Im(U) ≤ Im(V)` be their images in
`H^n(L)`. Then `Im(V)/Im(U) ≅ V/(U ⊔ Im(d^{n-1}) ⊓ V)`: a cocycle of `V` has its class in `Im(U)`
exactly when it lies in `U` modulo a coboundary of `V`. -/
private lemma nonempty_cokernel_ofLE_iso_toHomology (L : CochainComplex A ℤ) (n : ℤ)
    {U V : Subobject (L.X n)} (h : U ≤ V) (hU : U.arrow ≫ L.d n (n + 1) = 0)
    (hV : V.arrow ≫ L.d n (n + 1) = 0) :
    Nonempty (cokernel (Subobject.ofLE _ _ (sup_le h inf_le_right :
        U ⊔ imageSubobject (L.d (n - 1) n) ⊓ V ≤ V)) ≅
      cokernel (Subobject.ofLE _ _ (imageSubobject_toHomology_le_of_le L n h hU hV))) := by
  have hIV : (imageSubobject (L.d (n - 1) n) ⊓ V).arrow ≫ L.d n (n + 1) = 0 :=
    arrow_comp_d_eq_zero_of_le inf_le_right hV
  set G := Subobject.ofLE _ _ (imageSubobject_toHomology_le_of_le L n h hU hV) with hG
  set g := factorThruImageSubobject (toHomology L n hV) ≫ cokernel.π G with hg
  have hepi : Epi g := epi_comp _ _
  have hsquare : Subobject.ofLE U V h ≫ factorThruImageSubobject (toHomology L n hV)
      = factorThruImageSubobject (toHomology L n hU) ≫ G := by
    rw [hG, ← cancel_mono (imageSubobject (toHomology L n hV)).arrow, Category.assoc,
      Category.assoc, imageSubobject_arrow_comp, Subobject.ofLE_arrow, imageSubobject_arrow_comp,
      ofLE_comp_toHomology L n h hU hV]
  refine nonempty_cokernel_ofLE_iso_of_epi _ g (ofLE_sup_comp_eq_zero h inf_le_right g ?_ ?_) ?_
  · rw [hg, ← Category.assoc, hsquare, Category.assoc, cokernel.condition, comp_zero]
  · have hzero : Subobject.ofLE _ V (inf_le_right : imageSubobject (L.d (n - 1) n) ⊓ V ≤ V)
        ≫ factorThruImageSubobject (toHomology L n hV) = 0 := by
      rw [← cancel_mono (imageSubobject (toHomology L n hV)).arrow, Category.assoc,
        imageSubobject_arrow_comp, zero_comp, ofLE_comp_toHomology L n _ hIV hV,
        toHomology_eq_zero L n hIV inf_le_left]
    rw [hg, ← Category.assoc, hzero, zero_comp]
  · intro T t ht
    have h1 := factors_of_comp_cokernel_π_ofLE_eq_zero
      (imageSubobject_toHomology_le_of_le L n h hU hV)
      (t ≫ factorThruImageSubobject (toHomology L n hV)) (by rw [Category.assoc]; exact ht)
    rw [Category.assoc, imageSubobject_arrow_comp, imageSubobject_toHomology L n hU] at h1
    have h2 := factors_sup_kernelSubobject (L.homologyπ n) (imageSubobject (toCycles L n hU))
      (t ≫ toCycles L n hV) (by rw [Category.assoc, toCycles_comp_homologyπ]; exact h1)
    have h3 := exists_factors (L.iCycles n) h2
    rw [(Subobject.existsPullbackAdj (L.iCycles n)).gc.l_sup,
      exists_iCycles_imageSubobject_toCycles L n hU, exists_iCycles_kernelSubobject_homologyπ,
      Category.assoc, toCycles_comp_iCycles] at h3
    exact Subobject.factors_of_le _ (sup_inf_le_assoc_of_le _ h)
      ((Subobject.inf_factors _).2 ⟨h3, Subobject.factors_comp_arrow _⟩)

/-- **An object of cohomology filtered by subobjects of cocycles.** Let `V` be a decreasing family
of subobjects of `L^n` annihilated by `d^n` which contains every cocycle at `a` and vanishes at
`b`, for some `a ≤ b`. If a weak Serre class `P` contains every
`V p / (V (p+1) ⊔ Im(d^{n-1}) ⊓ V p)`, then it contains `H^n(L)`: the images of the `V p` filter
`H^n(L)` finitely with those graded pieces. -/
lemma prop_homology_of_prop_gradedPiece (L : CochainComplex A ℤ) (n : ℤ)
    (P : ObjectProperty A) [P.IsWeakSerreClass] (V : ℤ → Subobject (L.X n))
    (hV : ∀ p, (V p).arrow ≫ L.d n (n + 1) = 0) (hanti : ∀ p, V (p + 1) ≤ V p)
    (a b : ℤ) (hab : a ≤ b) (ha : kernelSubobject (L.d n (n + 1)) ≤ V a) (hb : V b = ⊥)
    (hgr : ∀ p : ℤ, P (cokernel (Subobject.ofLE _ _ (sup_le (hanti p) inf_le_right :
      V (p + 1) ⊔ imageSubobject (L.d (n - 1) n) ⊓ V p ≤ V p)))) :
    P (L.homology n) := by
  refine prop_of_filtration P (fun p => imageSubobject (toHomology L n (hV p)))
    (fun p => imageSubobject_toHomology_le_of_le L n (hanti p) (hV (p + 1)) (hV p)) a b hab
    (imageSubobject_toHomology_eq_top L n (hV a) ha) ?_ fun p => ?_
  · rw [toHomology_eq_zero L n (hV b) (hb.le.trans bot_le), imageSubobject_zero]
  · obtain ⟨e⟩ := nonempty_cokernel_ofLE_iso_toHomology L n (hanti p) (hV (p + 1)) (hV p)
    exact P.prop_of_iso e (hgr p)

end CocycleFiltrations

section Filtration

variable {A : Type u} [Category.{v} A] [Abelian A]
  (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
  (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
  (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))

include hF in
/-- The filtration decreases: `F^{p'} K^n ≤ F^p K^n` for `p ≤ p'`. -/
lemma F_antitone {p p' : ℤ} (hp : p ≤ p') (n : ℤ) : F p' n ≤ F p n := by
  rw [hF p' n, hF p n]
  refine Subobject.mk_le_mk_of_comm ((K.filtration.diagram.map (homOfLE hp).op).f n) ?_
  rw [← HomologicalComplex.comp_f, K.filtration.diagram_map_comp_ι_app]

include hF in
/-- Each step of the filtration is a subcomplex: `d` carries `F^p K^n` into `F^p K^{n'}`. -/
private lemma factors_F_d (p n n' : ℤ) : (F p n').Factors ((F p n).arrow ≫ K.X.d n n') := by
  have hcomm : (K.filtration.ι.app (op p)).f n ≫ K.X.d n n' =
      (K.filtration.diagram.obj (op p)).d n n' ≫ (K.filtration.ι.app (op p)).f n' :=
    (K.filtration.ι.app (op p)).comm n n'
  rw [hF p n, hF p n']
  refine mk_factors_of_fac _ (t := (Subobject.underlyingIso _).hom ≫
    (K.filtration.diagram.obj (op p)).d n n') ?_
  rw [Category.assoc, ← hcomm, ← Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk]

include hF in
/-- `F^p K^n` is all of `K^n` exactly when its inclusion is an isomorphism. -/
lemma F_eq_top_iff (p n : ℤ) : F p n = ⊤ ↔ IsIso ((K.filtration.ι.app (op p)).f n) := by
  rw [hF p n]; exact (Subobject.isIso_iff_mk_eq_top _).symm

variable (hK : K.filtration.IsDegreewiseFinite)

include hF hK in
/-- Degreewise finiteness, exhaustion half: the filtration of `K^n` is everything far to the
left. -/
public lemma exists_F_eq_top (n : ℤ) : ∃ a : ℤ, ∀ p ≤ a, F p n = ⊤ := by
  obtain ⟨p₀, q₀, hiso, -⟩ := hK n
  refine ⟨p₀, fun p hp => top_le_iff.mp ?_⟩
  exact ((F_eq_top_iff K F hF p₀ n).mpr hiso).ge.trans (F_antitone K F hF hp n)

include hF hK in
/-- Degreewise finiteness, vanishing half: the filtration of `K^n` is zero far to the right. -/
public lemma exists_F_eq_bot (n : ℤ) : ∃ b : ℤ, ∀ p, b ≤ p → F p n = ⊥ := by
  obtain ⟨p₀, q₀, -, hzero⟩ := hK n
  refine ⟨q₀, fun p hp => le_bot_iff.mp ((F_antitone K F hF hp n).trans (le_of_eq ?_))⟩
  rw [hF q₀ n, Subobject.mk_eq_bot_iff_zero]
  exact hzero.eq_of_src _ _

section Spectral

variable (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
  (hZ : ∀ r p n : ℤ, Z r p n =
    F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
  (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
  (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
    (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1)))

include hF hZ in
/-- For `r ≤ 0` there is no condition at all: `Z_r^{p,q} = F^p K^n`, because the filtration is by
subcomplexes, so `d^n` already carries `F^p K^n` into `F^{p+r} K^{n+1}`. -/
lemma Z_eq_F {r : ℤ} (hr : r ≤ 0) (p n : ℤ) : Z r p n = F p n := by
  rw [hZ r p n, inf_eq_left]
  exact (Subobject.le_pullback_iff _ _ _).mpr (Subobject.factors_of_le _
    (F_antitone K F hF (by omega : p + r ≤ p) (n + 1)) (factors_F_d K F hF p n (n + 1)))

include hZ in
/-- `Z_r^{p,q}` vanishes where the filtration of `K^n` does. -/
lemma Z_eq_bot {r p n : ℤ} (h : F p n = ⊥) : Z r p n = ⊥ := by
  rw [hZ r p n, h, bot_inf_eq]

include hZ in
/-- Where the filtration of `K^{n+1}` has vanished, `Z_r^{p,q}` is the cocycles in `F^p K^n`. -/
lemma Z_eq_kernelSubobject_inf {r p n : ℤ} (h : F (p + r) (n + 1) = ⊥) :
    Z r p n = kernelSubobject (K.X.d n (n + 1)) ⊓ F p n := by
  rw [hZ r p n, h, Subobject.pullback_bot, inf_comm]

include hF hZ hD in
/-- `D_0^{p,q} = F^{p+1} K^n`: together with `Z_eq_F` this says that the `E_0`-page is the graded
object `gr^p K^n` of the filtration. -/
lemma D_zero_eq_F (p n : ℤ) : D 0 p n = F (p + 1) n := by
  rw [hD 0 p n, show p - (0 : ℤ) + 1 = p + 1 from by ring,
    Z_eq_F K F hF Z hZ (show (0 : ℤ) - 1 ≤ 0 by omega) (p + 1) n,
    Z_eq_F K F hF Z hZ (show (0 : ℤ) - 1 ≤ 0 by omega) (p + 1) (n - 1), sup_eq_left]
  exact (Subobject.exists_le_iff_le_pullback _ _ _).mpr ((Subobject.le_pullback_iff _ _ _).mpr
    (factors_F_d K F hF (p + 1) (n - 1) n))

include hZ hD in
/-- Where the filtration of `K^{n+1}` has vanished and that of `K^{n-1}` is everything,
`D_r^{p,q} = Ker(d^n) ⊓ F^{p+1}K^n ⊔ Im(d^{n-1}) ⊓ F^p K^n`. -/
lemma D_eq_sup {r p n : ℤ} (h₁ : F (p + r) (n + 1) = ⊥) (h₂ : F (p - r + 1) (n - 1) = ⊤) :
    D r p n = kernelSubobject (K.X.d n (n + 1)) ⊓ F (p + 1) n ⊔
      imageSubobject (K.X.d (n - 1) n) ⊓ F p n := by
  rw [hD r p n, hZ (r - 1) (p + 1) n, hZ (r - 1) (p - r + 1) (n - 1),
    show p + 1 + (r - 1) = p + r from by ring, show n - 1 + 1 = n from by ring,
    show p - r + 1 + (r - 1) = p from by ring, h₁, h₂, Subobject.pullback_bot, top_inf_eq,
    Abelian.Subobject.exists_pullback_eq_inf, inf_comm (F (p + 1) n),
    inf_comm (F p n)]

variable (E : CohomologicalSpectralSequence A 0)
  (hE : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
    cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))

namespace CochainComplex.Filtered

include hE in
/-- A term of the spectral sequence vanishes as soon as `D_r^{p,q}` is all of `Z_r^{p,q}`. -/
public lemma isZero_page (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q) (h : Z r p n ≤ D r p n) :
    IsZero ((E.page r hr).X (p, q)) :=
  IsZero.of_iso (isZero_cokernel_ofLE _ (le_inf h le_rfl)) (hE r p q n hr hn)

end CochainComplex.Filtered

end Spectral

end Filtration

namespace FilteredComplexSpectralSequence

-- `Subobject` is opened for the unqualified `comp_cokernel_π_eq_zero_iff`,
-- `factors_of_epi_comp`, `mk_le_of_factors`, ... of the subobject toolkit.
open Subobject

variable {A : Type u} [Category.{v} A] [Abelian A]

section Generic

variable (K : CochainComplex A ℤ) (F : ℤ → ∀ n : ℤ, Subobject (K.X n))

/-- **Two presentations of one subquotient.**  If the subobjects `V ≤ W` of `X` are cut out by
monomorphisms `s : S ⟶ X` and `t : T ⟶ X`, and `g : S ⟶ T` factors `s` through `t`, then
`W / V` and `T / S` are the same quotient: there is an isomorphism of the two cokernels
compatible with the projections out of `W`, whichever morphism `W ⟶ T` over `X` is used to
compare them (there is only one, `t` being a monomorphism). -/
lemma exists_iso_cokernel_ofLE_of_eq {X S T : A} {V W : Subobject X} (h : V ≤ W)
    (s : S ⟶ X) [Mono s] (t : T ⟶ X) [Mono t] (g : S ⟶ T) (hg : g ≫ t = s)
    (hV : V = Subobject.mk s) (hW : W = Subobject.mk t) :
    ∃ e : cokernel (Subobject.ofLE V W h) ≅ cokernel g,
      ∀ u : (W : A) ⟶ T, u ≫ t = W.arrow →
        cokernel.π (Subobject.ofLE V W h) ≫ e.hom = u ≫ cokernel.π g := by
  subst hV
  subst hW
  have w : Subobject.ofLE _ _ h ≫ (Subobject.underlyingIso t).hom
      = (Subobject.underlyingIso s).hom ≫ g := by
    rw [← cancel_mono t, Category.assoc, Category.assoc, hg,
      Subobject.underlyingIso_hom_comp_eq_mk, Subobject.underlyingIso_hom_comp_eq_mk,
      Subobject.ofLE_arrow]
  refine ⟨cokernel.mapIso _ g (Subobject.underlyingIso s) (Subobject.underlyingIso t) w,
    fun u hu => ?_⟩
  have hu' : u = (Subobject.underlyingIso t).hom := by
    rw [← cancel_mono t, hu, Subobject.underlyingIso_hom_comp_eq_mk]
  rw [hu']
  simp

/-- The denominator inclusion `D_r^{p, q} ⊓ Z_r^{p, q} ⟶ Z_r^{p, q}`. -/
noncomputable abbrev den (r p n : ℤ) :
    ((boundaries K F r p n ⊓ cycles K F r p n : Subobject (K.X n)) : A) ⟶
      ((cycles K F r p n : Subobject (K.X n)) : A) :=
  Subobject.ofLE _ _ inf_le_right

/-- The denominator inclusion composed with the inclusion of `Z_r^{p, q}` is the inclusion of
`D_r^{p, q} ⊓ Z_r^{p, q}`. -/
lemma den_arrow (r p n : ℤ) :
    den K F r p n ≫ (cycles K F r p n).arrow =
      (boundaries K F r p n ⊓ cycles K F r p n).arrow :=
  Subobject.ofLE_arrow _

/-- The page object `E_r^{p, q} = Z_r^{p, q} / (D_r^{p, q} ⊓ Z_r^{p, q})`. -/
noncomputable abbrev pageObj (r p n : ℤ) : A := cokernel (den K F r p n)

/-- The restriction of `d^n` to the cycle subobjects, `Z_r^{p, q} ⟶ Z_r^{p + r, q - r + 1}`. -/
noncomputable def deltaCycles (r p n : ℤ) :
    ((cycles K F r p n : Subobject (K.X n)) : A) ⟶
      ((cycles K F r (p + r) (n + 1) : Subobject (K.X (n + 1))) : A) :=
  Subobject.factorThru _ ((cycles K F r p n).arrow ≫ K.d n (n + 1))
    (Subobject.factors_arrow_comp_of_exists_le _ (exists_cycles_le K F r p n))

/-- `deltaCycles` followed by the inclusion of `Z_r^{p + r, q - r + 1}` is the inclusion of
`Z_r^{p, q}` followed by `d^n`. -/
lemma deltaCycles_arrow (r p n : ℤ) :
    deltaCycles K F r p n ≫ (cycles K F r (p + r) (n + 1)).arrow =
      (cycles K F r p n).arrow ≫ K.d n (n + 1) := by
  unfold deltaCycles
  exact Subobject.factorThru_arrow _ _ _

/-- Two consecutive restrictions `deltaCycles` of the differential compose to zero. -/
lemma deltaCycles_comp_deltaCycles (r p n : ℤ) :
    deltaCycles K F r p n ≫ deltaCycles K F r (p + r) (n + 1) = 0 := by
  rw [← cancel_mono (cycles K F r (p + r + r) (n + 1 + 1)).arrow, Category.assoc,
    deltaCycles_arrow, ← Category.assoc, deltaCycles_arrow, Category.assoc, K.d_comp_d,
    comp_zero, zero_comp]

/-- `deltaCycles` maps the denominator `D_r^{p, q} ⊓ Z_r^{p, q}` to zero in
`E_r^{p + r, q - r + 1}`. -/
lemma den_comp_deltaCycles_comp_π (r p n : ℤ) :
    den K F r p n ≫ deltaCycles K F r p n ≫ cokernel.π (den K F r (p + r) (n + 1)) = 0 := by
  rw [← Category.assoc, comp_cokernel_π_eq_zero_iff _ (den_arrow K F r (p + r) (n + 1)),
    Category.assoc, deltaCycles_arrow, ← Category.assoc, den_arrow]
  refine Subobject.factors_arrow_comp_of_exists_le _ (le_inf ?_ ?_)
  · exact ((Subobject.exists _).monotone inf_le_left).trans
      (exists_boundaries_le K F r p n)
  · exact ((Subobject.exists _).monotone inf_le_right).trans
      (exists_cycles_le K F r p n)

/-- The differential `E_r^{p, q} ⟶ E_r^{p + r, q - r + 1}`, induced by `d^n`. -/
noncomputable def pageMap (r p n : ℤ) :
    pageObj K F r p n ⟶ pageObj K F r (p + r) (n + 1) :=
  cokernel.desc _ (deltaCycles K F r p n ≫ cokernel.π (den K F r (p + r) (n + 1)))
    (den_comp_deltaCycles_comp_π K F r p n)

/-- On `Z_r^{p, q}`, the page differential `pageMap` is induced by `deltaCycles`. -/
lemma π_comp_pageMap (r p n : ℤ) :
    cokernel.π (den K F r p n) ≫ pageMap K F r p n =
      deltaCycles K F r p n ≫ cokernel.π (den K F r (p + r) (n + 1)) := by
  unfold pageMap
  exact cokernel.π_desc _ _ _

/-- Two consecutive page differentials compose to zero. -/
lemma pageMap_comp_pageMap (r p n : ℤ) :
    pageMap K F r p n ≫ pageMap K F r (p + r) (n + 1) = 0 := by
  refine zero_of_epi_comp (cokernel.π (den K F r p n)) ?_
  rw [← Category.assoc, π_comp_pageMap, Category.assoc, π_comp_pageMap,
    ← Category.assoc, deltaCycles_comp_deltaCycles, zero_comp]

/-- The differential with its indices given up to the arithmetic of the bidegree. -/
noncomputable def pageMap' (r p n p' n' : ℤ) (hp : p' = p + r) (hn : n' = n + 1) :
    pageObj K F r p n ⟶ pageObj K F r p' n' :=
  pageMap K F r p n ≫ eqToHom (by rw [hp, hn])

/-- The restriction of `d^n` to the cycles, with indices given up to the arithmetic of the
bidegree. -/
noncomputable def deltaCycles' (r p n p' n' : ℤ) (hp : p' = p + r) (hn : n' = n + 1) :
    ((cycles K F r p n : Subobject (K.X n)) : A) ⟶
      ((cycles K F r p' n' : Subobject (K.X n')) : A) :=
  deltaCycles K F r p n ≫ eqToHom (by rw [hp, hn])

/-- `deltaCycles'` followed by the inclusion of `Z_r^{p', n'}` is the inclusion of `Z_r^{p, n}`
followed by `d^n`. -/
lemma deltaCycles'_arrow (r p n p' n' : ℤ) (hp : p' = p + r) (hn : n' = n + 1) :
    deltaCycles' K F r p n p' n' hp hn ≫ (cycles K F r p' n').arrow =
      (cycles K F r p n).arrow ≫ K.d n n' := by
  subst hp; subst hn
  simpa [deltaCycles'] using deltaCycles_arrow K F r p n

/-- On `Z_r^{p, n}`, the page differential `pageMap'` is induced by `deltaCycles'`. -/
lemma π_comp_pageMap' (r p n p' n' : ℤ) (hp : p' = p + r) (hn : n' = n + 1) :
    cokernel.π (den K F r p n) ≫ pageMap' K F r p n p' n' hp hn =
      deltaCycles' K F r p n p' n' hp hn ≫ cokernel.π (den K F r p' n') := by
  subst hp; subst hn
  simpa [pageMap', deltaCycles'] using π_comp_pageMap K F r p n

/-- Two consecutive page differentials `pageMap'` compose to zero. -/
lemma pageMap'_comp_pageMap' (r p n p' n' p'' n'' : ℤ) (hp : p' = p + r)
    (hn : n' = n + 1) (hp' : p'' = p' + r) (hn' : n'' = n' + 1) :
    pageMap' K F r p n p' n' hp hn ≫ pageMap' K F r p' n' p'' n'' hp' hn' = 0 := by
  subst hp; subst hn; subst hp'; subst hn'
  simpa [pageMap'] using pageMap_comp_pageMap K F r p n

/-- The `r`-th page of the spectral sequence of a filtered complex. -/
noncomputable abbrev pageComplex (r : ℤ) :
    HomologicalComplex A (ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)) where
  X pq := pageObj K F r pq.1 (pq.1 + pq.2)
  d pq pq' := if h : pq + (r, 1 - r) = pq' then
      pageMap' K F r pq.1 (pq.1 + pq.2) pq'.1 (pq'.1 + pq'.2)
        (by rw [← h, Prod.fst_add])
        (by rw [← h, Prod.fst_add, Prod.snd_add]; dsimp only; ring)
    else 0
  shape pq pq' h := dite_eq_right (fun h' => h (ComplexShape.up'_mk _ _ _ h'))
  d_comp_d' pq pq' pq'' h h' := by
    rw [ComplexShape.up'_Rel] at h h'
    subst h h'
    rw [dite_eq_left rfl, dite_eq_left rfl]
    exact pageMap'_comp_pageMap' K F r _ _ _ _ _ _ _ _ _ _

/-- The differential of the `r`-th page from `pq` to `pq'`, for `pq' = pq + (r, 1 - r)`. -/
lemma pageComplex_d (r : ℤ) {pq pq' : ℤ × ℤ} (h : pq + (r, 1 - r) = pq') :
    (pageComplex K F r).d pq pq' = pageMap' K F r pq.1 (pq.1 + pq.2) pq'.1 (pq'.1 + pq'.2)
      (by rw [← h, Prod.fst_add]) (by rw [← h, Prod.fst_add, Prod.snd_add]; dsimp only; ring) :=
  dite_eq_left h

/-- The denominator of the `r`-th page lies in the kernel numerator. -/
lemma den_le_kernelNumerator (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r p n : ℤ) :
    boundaries K F r p n ⊓ cycles K F r p n
      ≤ kernelNumerator K F r p n :=
  _root_.le_sup_right.trans (le_kernelNumerator K F hanti r p n)

/-- The cycles object of the `r`-th page at `(p, n)`: the kernel numerator modulo the `r`-th
denominator. -/
noncomputable abbrev pageCycles (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r p n : ℤ) : A :=
  cokernel (Subobject.ofLE _ _ (den_le_kernelNumerator K F hanti r p n))

/-- The inclusion of the page cycles into the page, induced by `kernelNumerator ≤ Z_r`; it is a
monomorphism, the two quotients sharing the denominator `D_r ⊓ Z_r`. -/
noncomputable abbrev pageCyclesι (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r p n : ℤ) : pageCycles K F hanti r p n ⟶ pageObj K F r p n :=
  Subobject.quotientMap (den_le_kernelNumerator K F hanti r p n)
    (kernelNumerator_le_cycles K F r p n)

/-- On the kernel numerator, `pageCyclesι` is induced by the inclusion
`kernelNumerator ≤ Z_r^{p, q}`. -/
lemma π_comp_pageCyclesι (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r p n : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator K F hanti r p n))
        ≫ pageCyclesι K F hanti r p n
      = Subobject.ofLE _ _ (kernelNumerator_le_cycles K F r p n)
        ≫ cokernel.π (den K F r p n) :=
  Subobject.π_quotientMap _ _

/-- The page differential kills the page cycles. -/
lemma pageCyclesι_comp_pageMap (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)
    (r p n : ℤ) : pageCyclesι K F hanti r p n ≫ pageMap K F r p n = 0 := by
  refine zero_of_epi_comp (cokernel.π (Subobject.ofLE _ _
    (den_le_kernelNumerator K F hanti r p n))) ?_
  rw [← Category.assoc, π_comp_pageCyclesι, Category.assoc, π_comp_pageMap, ← Category.assoc]
  refine (comp_cokernel_π_eq_zero_iff _ (den_arrow K F r (p + r) (n + 1)) _).2 ?_
  rw [Category.assoc, deltaCycles_arrow, ← Category.assoc, Subobject.ofLE_arrow]
  -- the kernel numerator's differential lands in the target denominator, by definition
  have h : kernelNumerator K F r p n
      ≤ (Subobject.pullback (K.d n (n + 1))).obj
        (boundaries K F r (p + r) (n + 1) ⊓ cycles K F r (p + r) (n + 1)) := by
    rw [kernelNumerator]; exact _root_.inf_le_right
  exact (Subobject.le_pullback_iff _ _ _).1 h

/-- **Anything killed by the page differential comes from the kernel numerator.** Stated as a
`Factors`, so it may be proved up to a refinement: lift along the epimorphism `Z_r ⟶ E_r`, read off
that the lift's differential dies in the target denominator, and land in `kernelNumerator` by its
defining preimage condition. -/
lemma factors_pageCyclesι_of_comp_pageMap_eq_zero
    (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r p n : ℤ) {T : A}
    (g : T ⟶ pageObj K F r p n) (hg : g ≫ pageMap K F r p n = 0) :
    (Subobject.mk (pageCyclesι K F hanti r p n)).Factors g := by
  -- lift `g` along the epimorphism `Z_r ⟶ E_r`
  obtain ⟨T', w, hw, z, fac⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π (den K F r p n)) g
  refine factors_of_epi_comp w g ?_
  rw [fac]
  -- `z` lands in the kernel numerator
  have hzk : (kernelNumerator K F r p n).Factors
      (z ≫ (cycles K F r p n).arrow) := by
    rw [kernelNumerator]
    refine (Subobject.inf_factors _).2 ⟨Subobject.factors_comp_arrow z, ?_⟩
    rw [pullback_factors_iff, Category.assoc, ← deltaCycles_arrow, ← Category.assoc]
    refine (comp_cokernel_π_eq_zero_iff _ (den_arrow K F r (p + r) (n + 1)) _).1 ?_
    rw [Category.assoc, ← π_comp_pageMap, ← Category.assoc, ← fac, Category.assoc, hg,
      comp_zero]
  obtain ⟨t, ht⟩ : ∃ t : T' ⟶ (kernelNumerator K F r p n : A),
      t ≫ (kernelNumerator K F r p n).arrow = z ≫ (cycles K F r p n).arrow :=
    ⟨_, Subobject.factorThru_arrow _ _ hzk⟩
  have hzt : t ≫ Subobject.ofLE _ _ (kernelNumerator_le_cycles K F r p n) = z := by
    rw [← cancel_mono (cycles K F r p n).arrow, Category.assoc, Subobject.ofLE_arrow,
      ht]
  refine mk_factors_of_fac _ (t := t ≫ cokernel.π (Subobject.ofLE _ _
    (den_le_kernelNumerator K F hanti r p n))) ?_
  rw [Category.assoc, π_comp_pageCyclesι, ← Category.assoc, hzt]

/-- **`pageCyclesι` is the kernel of the page differential.** The lift of a morphism killed by
`pageMap` is built from `factors_pageCyclesι_of_comp_pageMap_eq_zero`; it is unique because
`pageCyclesι` is a monomorphism. -/
noncomputable def pageCyclesιIsKernel
    (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n) (r p n : ℤ) :
    IsLimit (KernelFork.ofι (pageCyclesι K F hanti r p n)
      (pageCyclesι_comp_pageMap K F hanti r p n)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} g hg => (Subobject.mk (pageCyclesι K F hanti r p n)).factorThru g
      (factors_pageCyclesι_of_comp_pageMap_eq_zero K F hanti r p n g hg)
      ≫ (Subobject.underlyingIso (pageCyclesι K F hanti r p n)).hom)
    (fun {_} g hg => by
      rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.factorThru_arrow])
    (fun {_} g hg m hm => by
      rw [← cancel_mono (pageCyclesι K F hanti r p n), hm, Category.assoc,
        Subobject.underlyingIso_hom_comp_eq_mk, Subobject.factorThru_arrow])

/-- Being killed by the outgoing page differential at `pq` is being killed by `pageMap`: the two
differ by the `eqToHom` reconciling the bidegree arithmetic, which is an isomorphism. -/
lemma comp_d_eq_zero_iff (r : ℤ) (pq : ℤ × ℤ) {T : A}
    (g : T ⟶ pageObj K F r pq.1 (pq.1 + pq.2)) :
    g ≫ (pageComplex K F r).d pq (pq + (r, 1 - r)) = 0
      ↔ g ≫ pageMap K F r pq.1 (pq.1 + pq.2) = 0 := by
  rw [pageComplex_d K F r rfl, pageMap', ← Category.assoc]
  exact ⟨fun h => zero_of_comp_mono _ h, fun h => by rw [h, zero_comp]⟩

/-- **The incoming page differential comes from `d` on the cycles.**  Any map `b` into the page at
`i` lifts, up to a refinement, along the epimorphism `Z_r^i ⟶ E_r^i`; `π_comp_pageMap'` then
computes `b ≫ d` as a map through `Z_r^{pq}`, whose arrow is `Z_r^i.arrow ≫ d` and therefore
factors through the image `d(Z_r^i)`.

Stated for an arbitrary source index `i` with `i + (r, 1 - r) = pq`, so that `pageComplex_d`
applies to the page differential and no `ComplexShape.prev` is ever unfolded. -/
lemma exists_refinement_comp_d (r : ℤ) (i pq : ℤ × ℤ) (hi : i + (r, 1 - r) = pq) {T : A}
    (b : T ⟶ pageObj K F r i.1 (i.1 + i.2)) :
    ∃ (T' : A) (u : T' ⟶ T) (_ : Epi u)
      (c : T' ⟶ ((cycles K F r pq.1 (pq.1 + pq.2) :
        Subobject (K.X (pq.1 + pq.2))) : A)),
      u ≫ b ≫ (pageComplex K F r).d i pq = c ≫ cokernel.π (den K F r pq.1 (pq.1 + pq.2)) ∧
      ((Subobject.exists (K.d (i.1 + i.2) (pq.1 + pq.2))).obj
          (cycles K F r i.1 (i.1 + i.2))).Factors
        (c ≫ (cycles K F r pq.1 (pq.1 + pq.2)).arrow) := by
  have hp : pq.1 = i.1 + r := by rw [← hi, Prod.fst_add]
  have hn : pq.1 + pq.2 = i.1 + i.2 + 1 := by
    rw [← hi, Prod.fst_add, Prod.snd_add]; dsimp only; ring
  obtain ⟨T', u, hu, z, fac⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π (den K F r i.1 (i.1 + i.2))) b
  refine ⟨T', u, hu, z ≫ deltaCycles' K F r i.1 (i.1 + i.2) pq.1 (pq.1 + pq.2) hp hn, ?_, ?_⟩
  · rw [pageComplex_d K F r hi, ← Category.assoc, fac, Category.assoc, π_comp_pageMap',
      Category.assoc]
  · rw [Category.assoc, deltaCycles'_arrow]
    exact Subobject.factors_of_factors_right _ (Subobject.factors_arrow_comp _ _)

/-- **The image of the incoming differential is `V = d(Z_r^{p-r,n-1})`.** The restricted
differential `deltaCycles` composed with the cycle inclusion is literally
`Z_r^{p-r,n-1}.arrow ≫ d`, whose image subobject is `V` by `Subobject.exists_eq_imageSubobject`. -/
lemma imageSubobject_deltaCycles (r p n : ℤ) :
    imageSubobject (deltaCycles K F r p n ≫ (cycles K F r (p + r) (n + 1)).arrow)
      = (Subobject.exists (K.d n (n + 1))).obj (cycles K F r p n) := by
  rw [deltaCycles_arrow, Subobject.exists_eq_imageSubobject]

/-- The page object the differential into `pq` comes from, at the explicitly indexed source
`pq - (r, 1 - r)`. -/
noncomputable abbrev prevPage (r : ℤ) (pq : ℤ × ℤ) : A :=
  pageObj K F r (pq - ((r, 1 - r) : ℤ × ℤ)).1
    ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2)

/-- The filtration index of the source of the differential into `pq`. -/
lemma prev_fst (r : ℤ) (pq : ℤ × ℤ) : (pq - ((r, 1 - r) : ℤ × ℤ)).1 = pq.1 - r :=
  Prod.fst_sub _ _

/-- The total degree of the source of the differential into `pq`. -/
lemma prev_fst_add_snd (r : ℤ) (pq : ℤ × ℤ) :
    (pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2 = pq.1 + pq.2 - 1 := by
  rw [Prod.fst_sub, Prod.snd_sub]
  ring

section CokernelSide

variable (hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n)

include hanti

/-- `V = d(Z_r^{p-r,n-1})` lies in the kernel numerator, being inside `Z_{r+1}`. -/
lemma V_le_kernelNumerator (r p n : ℤ) :
    (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1))
      ≤ kernelNumerator K F r p n :=
  (exists_cycles_le_cycles_succ K F r p n).trans
    (_root_.le_sup_left.trans (le_kernelNumerator K F hanti r p n))

/-- The enlarged denominator `(D_r ⊓ Z_r) ⊔ V` still lies in the kernel numerator. -/
lemma denV_le_kernelNumerator (r p n : ℤ) :
    (boundaries K F r p n ⊓ cycles K F r p n)
        ⊔ (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1))
      ≤ kernelNumerator K F r p n :=
  _root_.sup_le (den_le_kernelNumerator K F hanti r p n) (V_le_kernelNumerator K F hanti r p n)

/-- `Z_{r+1}` lies in the kernel numerator. -/
lemma cyclesSucc_le_kernelNumerator (r p n : ℤ) :
    cycles K F (r + 1) p n ≤ kernelNumerator K F r p n :=
  _root_.le_sup_left.trans (le_kernelNumerator K F hanti r p n)

/-- **The page turn, as an isomorphism of subquotients.**
`kernelNumerator / ((D_r ⊓ Z_r) ⊔ V) ≅ Z_{r+1} / (D_{r+1} ⊓ Z_{r+1}) = E_{r+1}`.
Both are quotients generated by `Z_{r+1}`, and their kernels agree by the companion identity
`boundaries_succ_inf_eq`; `exists_iso_cokernel_of_factors_iff` then identifies them. -/
lemma exists_pageTurn (r p n : ℤ) :
    ∃ e : cokernel (Subobject.ofLE _ _ (denV_le_kernelNumerator K F hanti r p n))
        ≅ pageObj K F (r + 1) p n,
      Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r p n)
          ≫ cokernel.π (Subobject.ofLE _ _ (denV_le_kernelNumerator K F hanti r p n)) ≫ e.hom
        = cokernel.π (den K F (r + 1) p n) := by
  have harrow : Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r p n)
      ≫ (kernelNumerator K F r p n).arrow
      = (cycles K F (r + 1) p n).arrow := Subobject.ofLE_arrow _
  have hepi : Epi (Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r p n)
      ≫ cokernel.π (Subobject.ofLE _ _ (denV_le_kernelNumerator K F hanti r p n))) :=
    Subobject.epi_ofLE_comp_cokernel_π _ (Subobject.ofLE_arrow _) _
      (cycles_succ_sup_eq_kernelNumerator K F hanti r p n).ge le_rfl
  obtain ⟨e, he⟩ := Subobject.exists_iso_cokernel_of_factors_iff
    (Subobject.ofLE _ _ (denV_le_kernelNumerator K F hanti r p n)) (Subobject.ofLE_arrow _)
    (den K F (r + 1) p n) (den_arrow K F (r + 1) p n)
    (Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K F hanti r p n)) (𝟙 _)
    (fun {T'} g => by
      simp only [harrow, Category.id_comp,
        ← boundaries_succ_inf_eq K F hanti r p n]
      exact ⟨fun h => (Subobject.inf_factors _).2
          ⟨Subobject.factors_of_factors_right _ (Subobject.factors_self _), h⟩,
        fun h => Subobject.factors_of_le _ _root_.inf_le_right h⟩)
  refine ⟨e, ?_⟩
  rw [he, Category.id_comp]

/-- The page projection `E_r`'s cycles onto `E_{r+1}`: quotient further by the image `V` of the
incoming differential, then turn the page. -/
noncomputable def pageπ (r p n : ℤ) :
    pageCycles K F hanti r p n ⟶ pageObj K F (r + 1) p n :=
  Subobject.enlargeDen _root_.le_sup_left (denV_le_kernelNumerator K F hanti r p n)
    ≫ (exists_pageTurn K F hanti r p n).choose.hom

/-- `pageπ` is an epimorphism. -/
instance epi_pageπ (r p n : ℤ) : Epi (pageπ K F hanti r p n) := by
  rw [pageπ]
  exact epi_comp _ _

/-- **The incoming page differential dies in `E_{r + 1}`.**  This is the `wπ` field of the left
homology datum, abstracted over the kernel-lift `L` and characterised only by
`L ≫ pageCyclesι = d`, so that the opaque `IsLimit.lift` term never has to be written out.

`pageπ` is `enlargeDen ≫ (page turn)` with the page turn an isomorphism, so it suffices that `L`
dies in `kernelNumerator / ((D_r ⊓ Z_r) ⊔ V)`.  By `comp_enlargeDen_eq_zero_of_factors` that is a
statement about refinement-lifts of `L` to `kernelNumerator`, and `exists_refinement_comp_d`
writes any such lift as a map through `V = d(Z_r^{p - r, n - 1})` modulo `D_r ⊓ Z_r`. -/
lemma wπ_aux (r : ℤ) (pq : ℤ × ℤ)
    (L : prevPage K F r pq ⟶ pageCycles K F hanti r pq.1 (pq.1 + pq.2))
    (hL : L ≫ pageCyclesι K F hanti r pq.1 (pq.1 + pq.2)
      = (pageComplex K F r).d (pq - (r, 1 - r)) pq) :
    L ≫ pageπ K F hanti r pq.1 (pq.1 + pq.2) = 0 := by
  have key : L ≫ Subobject.enlargeDen _root_.le_sup_left
      (denV_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2)) = 0 := by
    refine Subobject.comp_enlargeDen_eq_zero_of_factors _ _ L (fun {T'} t w _hw hfac => ?_)
    -- the class of `t` in `E_r` is the class of `w ≫ d`
    have h1 : w ≫ (pageComplex K F r).d (pq - (r, 1 - r)) pq
        = t ≫ Subobject.ofLE _ _
            (kernelNumerator_le_cycles K F r pq.1 (pq.1 + pq.2))
          ≫ cokernel.π (den K F r pq.1 (pq.1 + pq.2)) := by
      rw [← hL, ← Category.assoc, hfac, Category.assoc, π_comp_pageCyclesι]
    obtain ⟨T'', u, hu, c, hc, hcV⟩ :=
      exists_refinement_comp_d K F r (pq - (r, 1 - r)) pq (by abel) w
    rw [h1] at hc
    -- normalise the source indices of `V` to `(p - r, n - 1)`
    rw [prev_fst_add_snd, prev_fst] at hcV
    -- `u ≫ t` and `c` agree in `E_r`, so they differ by something in `D_r ⊓ Z_r`
    have hden : (boundaries K F r pq.1 (pq.1 + pq.2)
        ⊓ cycles K F r pq.1 (pq.1 + pq.2)).Factors
        ((u ≫ t ≫ Subobject.ofLE _ _
            (kernelNumerator_le_cycles K F r pq.1 (pq.1 + pq.2)) - c)
          ≫ (cycles K F r pq.1 (pq.1 + pq.2)).arrow) := by
      refine (comp_cokernel_π_eq_zero_iff _ (den_arrow K F r pq.1 (pq.1 + pq.2)) _).1 ?_
      rw [Preadditive.sub_comp, sub_eq_zero]
      simpa only [Category.assoc] using hc
    refine Subobject.factors_of_epi_comp u _ ?_
    have hsplit : u ≫ t ≫ (kernelNumerator K F r pq.1 (pq.1 + pq.2)).arrow
        = ((u ≫ t ≫ Subobject.ofLE _ _
              (kernelNumerator_le_cycles K F r pq.1 (pq.1 + pq.2)) - c)
            ≫ (cycles K F r pq.1 (pq.1 + pq.2)).arrow)
          + c ≫ (cycles K F r pq.1 (pq.1 + pq.2)).arrow := by
      rw [Preadditive.sub_comp]
      simp only [Category.assoc, Subobject.ofLE_arrow]
      abel
    rw [hsplit]
    exact Subobject.factors_add _ _ (Subobject.sup_factors_of_factors_left hden)
      (Subobject.sup_factors_of_factors_right hcV)
  rw [pageπ, ← Category.assoc, key, zero_comp]

/-- **`L` is the differential, read on classes.**  If `x` lifts `y ≫ Z_r^i.arrow ≫ d` to the kernel
numerator, its class in `kernelNumerator / (D_r ⊓ Z_r)` is `L` applied to the class of `y`.  Both
sides are compared after the monomorphism `pageCyclesι`, where `π_comp_pageMap'` computes the
differential; the comparison then reduces to two maps into `Z_r^{pq}` with equal arrows. -/
lemma class_eq_comp_L (r : ℤ) (pq : ℤ × ℤ)
    (L : prevPage K F r pq ⟶ pageCycles K F hanti r pq.1 (pq.1 + pq.2))
    (hL : L ≫ pageCyclesι K F hanti r pq.1 (pq.1 + pq.2)
      = (pageComplex K F r).d (pq - (r, 1 - r)) pq)
    {T : A} (x : T ⟶ ((kernelNumerator K F r pq.1 (pq.1 + pq.2) :
      Subobject (K.X (pq.1 + pq.2))) : A))
    (y : T ⟶ ((cycles K F r (pq - ((r, 1 - r) : ℤ × ℤ)).1
      ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2)) : A))
    (hxy : x ≫ (kernelNumerator K F r pq.1 (pq.1 + pq.2)).arrow
      = y ≫ (cycles K F r (pq - ((r, 1 - r) : ℤ × ℤ)).1
          ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2)).arrow
        ≫ K.d ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2) (pq.1 + pq.2)) :
    x ≫ cokernel.π (Subobject.ofLE _ _
        (den_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2)))
      = y ≫ cokernel.π (den K F r (pq - ((r, 1 - r) : ℤ × ℤ)).1
          ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2)) ≫ L := by
  refine (cancel_mono (pageCyclesι K F hanti r pq.1 (pq.1 + pq.2))).1 ?_
  rw [Category.assoc, π_comp_pageCyclesι, Category.assoc, Category.assoc, hL,
    pageComplex_d K F r (show pq - ((r, 1 - r) : ℤ × ℤ) + (r, 1 - r) = pq by abel),
    π_comp_pageMap', ← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono (cycles K F r pq.1 (pq.1 + pq.2)).arrow, Category.assoc,
    Category.assoc, Subobject.ofLE_arrow, deltaCycles'_arrow, hxy]

/-- **`pageπ` coequalises the incoming differential.**  Any `g'` killing `L` factors through
`pageπ`.  `pageπ` is `enlargeDen ≫ (page turn)` and `enlargeDen : N/W ⟶ N/W'` is the cokernel of
`W' ⟶ N/W`, so it is enough that `g'` kills that map; splitting `W' = W ⊔ V` as a join, the
`W`-part dies in `N/W` outright and the `V`-part is, after a refinement, `L` applied to a class —
which is where `L ≫ g' = 0` enters. -/
lemma exists_desc_pageπ (r : ℤ) (pq : ℤ × ℤ)
    (L : prevPage K F r pq ⟶ pageCycles K F hanti r pq.1 (pq.1 + pq.2))
    (hL : L ≫ pageCyclesι K F hanti r pq.1 (pq.1 + pq.2)
      = (pageComplex K F r).d (pq - (r, 1 - r)) pq)
    {Z' : A} (g' : pageCycles K F hanti r pq.1 (pq.1 + pq.2) ⟶ Z') (hg' : L ≫ g' = 0) :
    ∃ h : pageObj K F (r + 1) pq.1 (pq.1 + pq.2) ⟶ Z',
      pageπ K F hanti r pq.1 (pq.1 + pq.2) ≫ h = g' := by
  -- `g'` kills every class whose arrow factors through `V`, stated first with the source indices
  -- in `i = pq - (r, 1 - r)` form and then normalised to `(p - r, n - 1)`
  have hV : ∀ {T : A} (x : T ⟶ ((kernelNumerator K F r pq.1 (pq.1 + pq.2) :
        Subobject (K.X (pq.1 + pq.2))) : A)),
      ((Subobject.exists (K.d ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2)
          (pq.1 + pq.2))).obj (cycles K F r (pq - ((r, 1 - r) : ℤ × ℤ)).1
          ((pq - ((r, 1 - r) : ℤ × ℤ)).1 + (pq - ((r, 1 - r) : ℤ × ℤ)).2))).Factors
        (x ≫ (kernelNumerator K F r pq.1 (pq.1 + pq.2)).arrow) →
      x ≫ cokernel.π (Subobject.ofLE _ _
        (den_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2))) ≫ g' = 0 := by
    intro T x hx
    rw [Subobject.exists_eq_imageSubobject] at hx
    obtain ⟨T₃, z, hz, y, hzy⟩ := (Subobject.imageSubobject_factors_iff _ _).1 hx
    refine zero_of_epi_comp z ?_
    rw [← Category.assoc, ← Category.assoc,
      class_eq_comp_L K F hanti r pq L hL (z ≫ x) y (by rw [Category.assoc]; exact hzy),
      Category.assoc, Category.assoc, hg', comp_zero, comp_zero]
  rw [prev_fst_add_snd, prev_fst] at hV
  -- `g'` therefore kills `W' ⟶ N / W`
  have hker : Subobject.ofLE _ _ (denV_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2))
      ≫ cokernel.π (Subobject.ofLE _ _
        (den_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2))) ≫ g' = 0 := by
    refine ofLE_sup_comp_eq_zero (den_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2))
      (V_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2)) _ ?_ (hV _ ?_)
    · rw [← Category.assoc, cokernel.condition, zero_comp]
    · rw [Subobject.ofLE_arrow]
      exact Subobject.factors_self _
  -- descend along `enlargeDen`, then transport along the page turn
  refine ⟨(exists_pageTurn K F hanti r pq.1 (pq.1 + pq.2)).choose.inv
    ≫ cokernel.desc _ (cokernel.π (Subobject.ofLE _ _
      (den_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2))) ≫ g') hker, ?_⟩
  rw [pageπ, Category.assoc, Iso.hom_inv_id_assoc]
  refine (cancel_epi (cokernel.π (Subobject.ofLE _ _
    (den_le_kernelNumerator K F hanti r pq.1 (pq.1 + pq.2))))).1 ?_
  rw [Subobject.π_enlargeDen_assoc, cokernel.π_desc]

/-- **`hπ`: `pageπ` exhibits `E_{r + 1}` as the cokernel of the incoming page differential.**  The
descent is `exists_desc_pageπ`; uniqueness is free because `pageπ` is an epimorphism. -/
noncomputable def hπ_aux (r : ℤ) (pq : ℤ × ℤ)
    (L : prevPage K F r pq ⟶ pageCycles K F hanti r pq.1 (pq.1 + pq.2))
    (hL : L ≫ pageCyclesι K F hanti r pq.1 (pq.1 + pq.2)
      = (pageComplex K F r).d (pq - (r, 1 - r)) pq) :
    IsColimit (CokernelCofork.ofπ (pageπ K F hanti r pq.1 (pq.1 + pq.2))
      (wπ_aux K F hanti r pq L hL)) :=
  CokernelCofork.IsColimit.ofπ' _ _ fun {_} g' hg' =>
    ⟨(exists_desc_pageπ K F hanti r pq L hL g' hg').choose,
      (exists_desc_pageπ K F hanti r pq L hL g' hg').choose_spec⟩

end CokernelSide

end Generic

end FilteredComplexSpectralSequence

end

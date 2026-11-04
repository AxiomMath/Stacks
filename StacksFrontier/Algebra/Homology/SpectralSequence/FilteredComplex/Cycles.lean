module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Category.GaloisConnection
public import StacksCore.CategoryTheory.Subobject.Basic
public import StacksCore.CategoryTheory.Subobject.Limits
public import StacksFrontier.CategoryTheory.Subobject.Butterfly

/-!
# Cycles, boundaries and page kernels of a filtered complex

The subobject calculus behind the spectral sequence of a filtered complex (Stacks, Homological
Algebra, Section 12.24): the cycles `Z_r` and boundaries `D_r` of a filtered complex, and the
numerator of the kernel of the differential `d_r`.
-/

@[expose] public section

section

/-!
## Cycles and boundaries of a filtered complex

For a cochain complex `K` with a filtration `F p n` of each term by subobjects, the spectral
sequence of the filtration has pages built from the subobjects
```
Z r p n = F p n ⊓ (d^n)⁻¹ (F (p + r) (n + 1))
D r p n = Z (r - 1) (p + 1) n ⊔ d^{n-1} (Z (r - 1) (p - r + 1) (n - 1))
```
of `K.X n`. This file proves that the differential of `K` carries each of these families into the
next, which is what makes the differential descend to the quotients `Z / D` — the differentials of
the spectral sequence.

Both proofs run through the image/preimage Galois connection
(`CategoryTheory.Subobject.exists_le_iff_le_pullback`) and the fact that `d ≫ d = 0` makes the
relevant preimage the whole object. The filtered-complex notions live in the namespace
`FilteredComplexSpectralSequence`, that of the spectral sequence built from them.

## Main results

* `CategoryTheory.Subobject.pullback_zero_obj`: the preimage along a zero morphism is `⊤`.
* `FilteredComplexSpectralSequence.exists_cycles_le`: `d (Z r p n) ≤ Z r (p + r) (n + 1)`.
* `FilteredComplexSpectralSequence.exists_boundaries_le`: `d (D r p n) ≤ D r (p + r) (n + 1)`.
-/

universe v u

namespace CategoryTheory.Subobject

open Limits ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C]

section GaloisConnection

variable {X Y Z : C}

/-- The preimage of any subobject along a zero morphism is everything. -/
lemma pullback_zero_obj (Q : Subobject Y) : (Subobject.pullback (0 : X ⟶ Y)).obj Q = ⊤ := by
  have hsub : ∀ P : Subobject (0 : C), P = ⊤ := fun P =>
    top_le_iff.1 (Subobject.le_of_factors ((Subobject.factors_iff _ _).2
      ⟨0, (isZero_zero C).eq_of_tgt _ _⟩))
  have h : (0 : X ⟶ Y) = (0 : X ⟶ (0 : C)) ≫ (0 : (0 : C) ⟶ Y) := by simp
  rw [h, Subobject.pullback_comp, hsub ((Subobject.pullback (0 : (0 : C) ⟶ Y)).obj Q),
    Subobject.pullback_top]

/-- A subobject lies in the preimage of `Q` along `f` exactly when its arrow followed by `f`
factors through `Q`. -/
lemma le_pullback_iff (f : X ⟶ Y) (P : Subobject X) (Q : Subobject Y) :
    P ≤ (Subobject.pullback f).obj Q ↔ Q.Factors (P.arrow ≫ f) :=
  ⟨fun h => (pullback_factors_iff f Q _).mp
      (Subobject.factors_of_le _ h (Subobject.factors_self P)),
   fun h => Subobject.le_of_factors ((pullback_factors_iff f Q _).mpr h)⟩

/-- If the image of `P` along `f` lies in `Q`, then `Q` factors `P.arrow ≫ f`. -/
lemma factors_arrow_comp_of_exists_le (f : X ⟶ Y) {P : Subobject X} {Q : Subobject Y}
    (h : (Subobject.exists f).obj P ≤ Q) : Q.Factors (P.arrow ≫ f) :=
  (le_pullback_iff f P Q).1 ((Subobject.exists_le_iff_le_pullback f P Q).1 h)

/-- The image of `P` along `f` factors `P.arrow ≫ f`. -/
lemma factors_arrow_comp (f : X ⟶ Y) (P : Subobject X) :
    ((Subobject.exists f).obj P).Factors (P.arrow ≫ f) :=
  factors_arrow_comp_of_exists_le f le_rfl

/-- If `f ≫ g = 0` then the image along `f` lands in the preimage along `g` of anything. -/
lemma exists_le_pullback_of_comp_eq_zero {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0)
    (P : Subobject X) (Q : Subobject Z) :
    (Subobject.exists f).obj P ≤ (Subobject.pullback g).obj Q := by
  rw [Subobject.exists_le_iff_le_pullback, ← Subobject.pullback_comp, h, pullback_zero_obj]
  exact le_top

end GaloisConnection

end CategoryTheory.Subobject

namespace FilteredComplexSpectralSequence

open CategoryTheory Limits Subobject

variable {C : Type u} [Category.{v} C] [Abelian C]

section Cycles

variable (K : CochainComplex C ℤ) (F : ∀ (_p n : ℤ), Subobject (K.X n))

/-- The `r`-th cycle subobject of a filtered complex in degree `n` and filtration step `p`. -/
noncomputable def cycles (r p n : ℤ) : Subobject (K.X n) :=
  F p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj (F (p + r) (n + 1))

/-- The `r`-th boundary subobject of a filtered complex in degree `n` and filtration step `p`. -/
noncomputable def boundaries (r p n : ℤ) : Subobject (K.X n) :=
  cycles K F (r - 1) (p + 1) n ⊔
    (Subobject.exists (K.d (n - 1) n)).obj (cycles K F (r - 1) (p - r + 1) (n - 1))

/-- The introduction rule for the cycles: a subobject of `F p n` whose differential lands in
`F (p + r) (n + 1)` lies in `Z r p n`. -/
lemma le_cycles {r p n : ℤ} {P : Subobject (K.X n)} (h₁ : P ≤ F p n)
    (h₂ : P ≤ (Subobject.pullback (K.d n (n + 1))).obj (F (p + r) (n + 1))) :
    P ≤ cycles K F r p n := by
  rw [cycles]
  exact _root_.le_inf h₁ h₂

/-- **The differential carries cycles to cycles.** `d (Z r p n) ≤ Z r (p + r) (n + 1)`: the first
clause is the defining preimage condition read through the Galois connection, and the second holds
because `d ≫ d = 0` makes the preimage everything. -/
lemma exists_cycles_le (r p n : ℤ) :
    (Subobject.exists (K.d n (n + 1))).obj (cycles K F r p n)
      ≤ cycles K F r (p + r) (n + 1) := by
  simp only [cycles]
  refine _root_.le_inf ?_ ?_
  · rw [Subobject.exists_le_iff_le_pullback]
    exact _root_.inf_le_right
  · exact exists_le_pullback_of_comp_eq_zero (K.d_comp_d _ _ _) _ _

/-- **The differential carries boundaries to boundaries.** `d (D r p n) ≤ D r (p + r) (n + 1)`.
The first summand of `D r p n` is carried onto the second summand of the target exactly; the second
summand is killed, since it is already an image under `d`. -/
lemma exists_boundaries_le (r p n : ℤ) :
    (Subobject.exists (K.d n (n + 1))).obj (boundaries K F r p n)
      ≤ boundaries K F r (p + r) (n + 1) := by
  have e1 : n + 1 - 1 = n := by omega
  have e2 : p + r - r + 1 = p + 1 := by omega
  have hb : boundaries K F r (p + r) (n + 1) =
      cycles K F (r - 1) (p + r + 1) (n + 1) ⊔
        (Subobject.exists (K.d n (n + 1))).obj (cycles K F (r - 1) (p + 1) n) := by
    unfold boundaries
    rw [e1, e2]
  rw [hb]
  unfold boundaries
  rw [(Subobject.existsPullbackAdj (K.d n (n + 1))).gc.l_sup]
  refine _root_.sup_le _root_.le_sup_right ?_
  rw [Subobject.exists_le_iff_le_pullback]
  exact exists_le_pullback_of_comp_eq_zero (K.d_comp_d _ _ _) _ _

end Cycles

end FilteredComplexSpectralSequence

end

section

/-!
## The kernel of the spectral sequence differential

The `r`-th page of the spectral sequence of a filtered complex is `E_r^{p,q} = Z_r / (D_r ⊓ Z_r)`,
and its differential is induced by `d`. Turning the page means computing the homology of `E_r`,
and the numerator of the kernel of `d_r` at `(p, q)` is the subobject
```
Z_r^{p,n} ⊓ d⁻¹ (D_r^{p+r,n+1} ⊓ Z_r^{p+r,n+1})
```
of `K.X n`. The page-turning isomorphism rests on identifying that subobject with
`Z_{r+1}^{p,n} ⊔ (D_r^{p,n} ⊓ Z_r^{p,n})`, so that the kernel of `d_r` is
`Z_{r+1} / (D_r ⊓ Z_r)` and the butterfly lemma can be applied.

This file proves the containment `⊇` of that identity, together with the step it rests on: the
differential carries `Z_{r+1}` into the first summand `Z_{r-1}^{p+r+1,n+1}` of `D_r^{p+r,n+1}`,
because `z ∈ Z_{r+1}` has `dz ∈ F^{p+r+1}` by definition and `d(dz) = 0`.

## Main results

* `FilteredComplexSpectralSequence.exists_cycles_succ_le`:
  `d (Z_{r+1}^{p,n}) ≤ Z_{r-1}^{p+r+1,n+1}`.
* `FilteredComplexSpectralSequence.exists_cycles_succ_le_boundaries`:
  `d (Z_{r+1}^{p,n}) ≤ D_r^{p+r,n+1}`.
* `FilteredComplexSpectralSequence.le_kernelNumerator`: the `⊇` containment of the kernel identity.
-/

universe v u

namespace CategoryTheory.Subobject

open Limits Preadditive

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **Preimage recovery.** A morphism factoring through the image of `P` along `f` is, up to a
refinement, a morphism through `P` followed by `f`. This is what lets a decomposition obtained from
`exists_refinement_of_factors_sup` be turned back into an actual element of `P`. -/
theorem exists_factors_iff {X Y T : A} (f : X ⟶ Y) (P : Subobject X) (g : T ⟶ Y) :
    ((Subobject.exists f).obj P).Factors g ↔
      ∃ (T' : A) (z : T' ⟶ T) (_ : Epi z) (b : T' ⟶ (P : A)), z ≫ g = b ≫ (P.arrow ≫ f) := by
  rw [Subobject.exists_eq_imageSubobject]
  exact imageSubobject_factors_iff (P.arrow ≫ f) g

/-- An image under `f` is killed by any `g` with `f ≫ g = 0`. In particular a boundary is a
cycle: `d (Z)` composed with the next differential is zero. -/
theorem exists_arrow_comp_eq_zero {X Y Z : A} {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0)
    (P : Subobject X) : ((Subobject.exists f).obj P).arrow ≫ g = 0 :=
  (Subobject.bot_factors_iff_zero _).1
    ((le_pullback_iff g _ _).1 (exists_le_pullback_of_comp_eq_zero h P ⊥))

/-- Any morphism through an image under `f` is killed by a `g` with `f ≫ g = 0`. -/
theorem comp_eq_zero_of_factors_exists {X Y Z T : A} {f : X ⟶ Y} {g : Y ⟶ Z} (h : f ≫ g = 0)
    (P : Subobject X) (u : T ⟶ (((Subobject.exists f).obj P : Subobject Y) : A)) :
    u ≫ ((Subobject.exists f).obj P).arrow ≫ g = 0 := by
  rw [exists_arrow_comp_eq_zero h, comp_zero]

/-- A morphism through `P` followed by `P.arrow` factors through any larger subobject `Q`. -/
private theorem factors_comp_arrow_of_le {D : Type*} [Category D] {X T : D} {P Q : Subobject X}
    (h : P ≤ Q) (b : T ⟶ P) : Q.Factors (b ≫ P.arrow) :=
  Subobject.factors_of_le _ h (Subobject.factors_comp_arrow b)

/-- For `W ≤ N ≤ Z`, the composite `W ⟶ N ⟶ Z ⟶ Z / W` is zero. -/
theorem quotientMap_wellDef {X : A} {W N Z : Subobject X} (hWN : W ≤ N) (hNZ : N ≤ Z) :
    Subobject.ofLE W N hWN ≫ Subobject.ofLE N Z hNZ
        ≫ cokernel.π (Subobject.ofLE W Z (hWN.trans hNZ)) = 0 := by
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE, cokernel.condition]

/-- The map `N / W ⟶ Z / W` between quotients by a common denominator, induced by `N ≤ Z`. -/
noncomputable def quotientMap {X : A} {W N Z : Subobject X} (hWN : W ≤ N) (hNZ : N ≤ Z) :
    cokernel (Subobject.ofLE W N hWN) ⟶ cokernel (Subobject.ofLE W Z (hWN.trans hNZ)) :=
  cokernel.desc _ (Subobject.ofLE N Z hNZ ≫ cokernel.π _) (quotientMap_wellDef hWN hNZ)

/-- The projection onto `N / W` followed by `quotientMap` is the inclusion `N ≤ Z` followed by the
projection onto `Z / W`. -/
@[reassoc (attr := simp)]
theorem π_quotientMap {X : A} {W N Z : Subobject X} (hWN : W ≤ N) (hNZ : N ≤ Z) :
    cokernel.π (Subobject.ofLE W N hWN) ≫ quotientMap hWN hNZ =
      Subobject.ofLE N Z hNZ ≫ cokernel.π (Subobject.ofLE W Z (hWN.trans hNZ)) := by
  rw [quotientMap, cokernel.π_desc]

/-- The map between quotients by a common denominator induced by nested numerators is mono. -/
instance mono_quotientMap {X : A} {W N Z : Subobject X} (hWN : W ≤ N) (hNZ : N ≤ Z) :
    Mono (quotientMap hWN hNZ) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro R g hg
  obtain ⟨R', w, hw, t, fac⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π (Subobject.ofLE W N hWN)) g
  refine zero_of_epi_comp w ?_
  rw [fac]
  refine (comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow hWN) t).2 ?_
  have h2 : (t ≫ Subobject.ofLE N Z hNZ)
      ≫ cokernel.π (Subobject.ofLE W Z (hWN.trans hNZ)) = 0 := by
    rw [Category.assoc, ← π_quotientMap hWN hNZ, ← Category.assoc, ← fac, Category.assoc, hg,
      comp_zero]
  have h3 := (comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow (hWN.trans hNZ)) _).1 h2
  rwa [Category.assoc, Subobject.ofLE_arrow] at h3

/-- For `W ≤ W' ≤ N`, the composite `W ⟶ N ⟶ N / W'` is zero. -/
theorem enlargeDen_wellDef {X : A} {W W' N : Subobject X} (hWW' : W ≤ W') (hW'N : W' ≤ N) :
    Subobject.ofLE W N (hWW'.trans hW'N) ≫ cokernel.π (Subobject.ofLE W' N hW'N) = 0 := by
  rw [← Subobject.ofLE_comp_ofLE _ _ _ hWW' hW'N, Category.assoc, cokernel.condition, comp_zero]

/-- The induced map `N / W ⟶ N / W'` for `W ≤ W'`. -/
noncomputable def enlargeDen {X : A} {W W' N : Subobject X} (hWW' : W ≤ W') (hW'N : W' ≤ N) :
    cokernel (Subobject.ofLE W N (hWW'.trans hW'N)) ⟶ cokernel (Subobject.ofLE W' N hW'N) :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE W' N hW'N)) (enlargeDen_wellDef hWW' hW'N)

/-- The projection onto `N / W` followed by `enlargeDen` is the projection onto `N / W'`. -/
@[reassoc (attr := simp)]
theorem π_enlargeDen {X : A} {W W' N : Subobject X} (hWW' : W ≤ W') (hW'N : W' ≤ N) :
    cokernel.π (Subobject.ofLE W N (hWW'.trans hW'N)) ≫ enlargeDen hWW' hW'N =
      cokernel.π (Subobject.ofLE W' N hW'N) := by
  rw [enlargeDen, cokernel.π_desc]

/-- The map `enlargeDen` is an epimorphism. -/
instance epi_enlargeDen {X : A} {W W' N : Subobject X} (hWW' : W ≤ W') (hW'N : W' ≤ N) :
    Epi (enlargeDen hWW' hW'N) :=
  epi_of_epi_fac (π_enlargeDen hWW' hW'N)

/-- A morphism into `N / W` dies in `N / W'` exactly when each of its refinement-lifts to `N`
factors through `W'`. -/
theorem comp_enlargeDen_eq_zero_of_factors {X : A} {W W' N : Subobject X}
    (hWW' : W ≤ W') (hW'N : W' ≤ N) {T : A}
    (y : T ⟶ cokernel (Subobject.ofLE W N (hWW'.trans hW'N)))
    (h : ∀ {T' : A} (t : T' ⟶ (N : A)) (w : T' ⟶ T), Epi w →
      w ≫ y = t ≫ cokernel.π (Subobject.ofLE W N (hWW'.trans hW'N)) →
      W'.Factors (t ≫ N.arrow)) :
    y ≫ enlargeDen hWW' hW'N = 0 := by
  obtain ⟨T', w, hw, t, fac⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π (Subobject.ofLE W N (hWW'.trans hW'N))) y
  refine zero_of_epi_comp w ?_
  rw [← Category.assoc, fac, Category.assoc, π_enlargeDen]
  exact (comp_cokernel_π_eq_zero_iff _ (Subobject.ofLE_arrow hW'N) t).2 (h t w hw fac)

end CategoryTheory.Subobject

namespace FilteredComplexSpectralSequence

open CategoryTheory Limits Preadditive Subobject

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ)
  (F : ∀ (_p n : ℤ), Subobject (K.X n))


/-- The numerator of the kernel of the `r`-th differential at `(p, n)`: those cycles whose
differential already lies in the denominator of the target page. -/
noncomputable def kernelNumerator (r p n : ℤ) : Subobject (K.X n) :=
  cycles K F r p n ⊓
    (Subobject.pullback (K.d n (n + 1))).obj
      (boundaries K F r (p + r) (n + 1) ⊓ cycles K F r (p + r) (n + 1))

/-- The differential carries `Z_{r+1}^{p,n}` into `Z_{r-1}^{p+r+1,n+1}`: the filtration condition
is the defining one for `Z_{r+1}`, and the second condition is free because `d ≫ d = 0`. -/
lemma exists_cycles_succ_le (r p n : ℤ) :
    (Subobject.exists (K.d n (n + 1))).obj (cycles K F (r + 1) p n) ≤
      cycles K F (r - 1) (p + r + 1) (n + 1) := by
  have hix : p + (r + 1) = p + r + 1 := by omega
  refine le_cycles K F ?_ ?_
  · rw [Subobject.exists_le_iff_le_pullback, cycles, hix]
    exact _root_.inf_le_right
  · exact exists_le_pullback_of_comp_eq_zero (K.d_comp_d _ _ _) _ _

/-- The differential carries `Z_{r+1}^{p,n}` into the boundaries `D_r^{p+r,n+1}`, landing in its
first summand. -/
lemma exists_cycles_succ_le_boundaries (r p n : ℤ) :
    (Subobject.exists (K.d n (n + 1))).obj (cycles K F (r + 1) p n) ≤
      boundaries K F r (p + r) (n + 1) := by
  refine (exists_cycles_succ_le K F r p n).trans ?_
  unfold boundaries
  exact _root_.le_sup_left

/-- Monotonicity of the cycles in both indices. -/
private theorem cycles_le_cycles (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) {r r' p p' : ℤ}
    (n : ℤ) (hp : p ≤ p') (hpr : p + r ≤ p' + r') : cycles K F r' p' n ≤ cycles K F r p n := by
  simp only [cycles]
  exact
    _root_.le_inf (_root_.inf_le_left.trans (hanti _ _ _ hp))
      (_root_.inf_le_right.trans ((Subobject.pullback _).monotone (hanti _ _ _ hpr)))

/-- `Z_{r+1}` is contained in `Z_r`: the filtration is decreasing, so a stronger condition on the
differential is a stronger condition. -/
lemma cycles_succ_le (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    cycles K F (r + 1) p n ≤ cycles K F r p n :=
  cycles_le_cycles K F hanti n le_rfl (by omega)

/-- **The easy containment of the kernel identity.** Both `Z_{r+1}` and the denominator
`D_r ⊓ Z_r` lie in the kernel numerator: the first because its differential lands in
`D_r ⊓ Z_r` at the shifted index, the second because the differential preserves both families. -/
lemma le_kernelNumerator (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    cycles K F (r + 1) p n ⊔ (boundaries K F r p n ⊓ cycles K F r p n) ≤
      kernelNumerator K F r p n := by
  rw [kernelNumerator]
  refine
    _root_.sup_le (_root_.le_inf (cycles_succ_le K F hanti r p n) ?_)
      (_root_.le_inf _root_.inf_le_right ?_)
  · rw [← Subobject.exists_le_iff_le_pullback]
    exact
      _root_.le_inf (exists_cycles_succ_le_boundaries K F r p n)
        (((Subobject.exists _).monotone (cycles_succ_le K F hanti r p n)).trans
          (exists_cycles_le K F r p n))
  · rw [← Subobject.exists_le_iff_le_pullback]
    exact
      _root_.le_inf
        (((Subobject.exists _).monotone _root_.inf_le_left).trans (exists_boundaries_le K F r p n))
        (((Subobject.exists _).monotone _root_.inf_le_right).trans (exists_cycles_le K F r p n))

/-- A morphism `g` into `K.X n` factors through `Z r p n` when it factors through `F p n` and
`g ≫ d` factors through `F (p + r) (n + 1)`. -/
theorem cycles_factors {r p n : ℤ} {T : A} (g : T ⟶ K.X n) (h1 : (F p n).Factors g)
    (h2 : (F (p + r) (n + 1)).Factors (g ≫ K.d n (n + 1))) : (cycles K F r p n).Factors g := by
  rw [cycles]
  exact (Subobject.inf_factors _).2 ⟨h1, (pullback_factors_iff _ _ _).2 h2⟩

/-- The cycles `Z r p n` lie in the filtration step `F p n`. -/
theorem cycles_le_F (r p n : ℤ) : cycles K F r p n ≤ F p n := by
  rw [cycles]; exact _root_.inf_le_left

/-- For a decreasing filtration, `Z (r - 1) (p + 1) n ≤ Z r p n`. -/
theorem cycles_pred_succ_le (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    cycles K F (r - 1) (p + 1) n ≤ cycles K F r p n :=
  cycles_le_cycles K F hanti n (by omega) (by omega)

/-- The kernel numerator at `(p, n)` lies in the cycles `Z r p n`. -/
theorem kernelNumerator_le_cycles (r p n : ℤ) : kernelNumerator K F r p n ≤ cycles K F r p n := by
  rw [kernelNumerator]; exact _root_.inf_le_left

/-- For a decreasing filtration, the kernel numerator of `d_r` at `(p, n)` lies in
`Z_{r+1} ⊔ (D_r ⊓ Z_r)`. -/
theorem kernelNumerator_le (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    kernelNumerator K F r p n ≤
      cycles K F (r + 1) p n ⊔ (boundaries K F r p n ⊓ cycles K F r p n) := by
  refine Subobject.le_of_factors ?_
  set N := kernelNumerator K F r p n with hN
  have hfacD : (boundaries K F r (p + r) (n + 1)).Factors (N.arrow ≫ K.d n (n + 1)) := by
    have h1 :
      N ≤
        (Subobject.pullback (K.d n (n + 1))).obj
          (boundaries K F r (p + r) (n + 1) ⊓ cycles K F r (p + r) (n + 1)) := by
      rw [hN, kernelNumerator]; exact _root_.inf_le_right
    exact Subobject.factors_of_le _ _root_.inf_le_left ((le_pullback_iff _ _ _).1 h1)
  rw [boundaries, show n + 1 - 1 = n from by omega,
    show p + r - r + 1 = p + 1 from by omega] at hfacD
  obtain ⟨T', w, hw, β, γ, fac⟩ := exists_refinement_of_factors_sup _ hfacD
  obtain ⟨T'', u, hu, b, facb⟩ := (exists_factors_iff _ _ _).1 (Subobject.factors_comp_arrow γ)
  set b' : T'' ⟶ K.X n := b ≫ (cycles K F (r - 1) (p + 1) n).arrow with hb'
  have hNF : (F p n).Factors N.arrow :=
    Subobject.factors_of_le _ ((kernelNumerator_le_cycles K F r p n).trans (cycles_le_F K F r p n))
      (Subobject.factors_self N)
  have hb'F : (F p n).Factors b' := by
    exact factors_comp_arrow_of_le
      ((cycles_le_F K F (r - 1) (p + 1) n).trans (hanti _ _ _ (by omega))) b
  refine factors_of_epi_comp (u ≫ w) _ ?_
  rw [show (u ≫ w) ≫ N.arrow = ((u ≫ w) ≫ N.arrow - b') + b' from by abel]
  refine Subobject.factors_add _ _ ?_ ?_
  · refine Subobject.sup_factors_of_factors_left (cycles_factors K F _ ?_ ?_)
    · exact factors_sub _ _ (Subobject.factors_of_factors_right _ hNF) hb'F
    · rw [show p + (r + 1) = p + r + 1 from by omega, sub_comp]
      have key :
        ((u ≫ w) ≫ N.arrow) ≫ K.d n (n + 1) - b' ≫ K.d n (n + 1) =
          (u ≫ β) ≫ (cycles K F (r - 1) (p + r + 1) (n + 1)).arrow := by
        rw [hb', Category.assoc, Category.assoc, Category.assoc,
          show u ≫ w ≫ N.arrow ≫ K.d n (n + 1) = u ≫ (w ≫ N.arrow ≫ K.d n (n + 1)) from by
            simp only [],
          fac, comp_add, ← facb]
        simp only [Category.assoc]
        abel
      rw [key]
      exact factors_comp_arrow_of_le (cycles_le_F K F (r - 1) (p + r + 1) (n + 1)) _
  · refine Subobject.sup_factors_of_factors_right ((Subobject.inf_factors _).2 ⟨?_, ?_⟩)
    · rw [hb', boundaries]
      exact factors_comp_arrow_of_le _root_.le_sup_left b
    · rw [hb']
      exact factors_comp_arrow_of_le (cycles_pred_succ_le K F hanti r p n) b

/-- **The kernel identity.** The numerator of the kernel of `d_r` at `(p, n)` is exactly
`Z_{r+1} ⊔ (D_r ⊓ Z_r)`. This is what makes `ker d_r = Z_{r+1} / (D_r ⊓ Z_r)`, and hence what lets
the butterfly lemma identify the homology of the `r`-th page with the `(r+1)`-st page. -/
theorem kernelNumerator_eq (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    kernelNumerator K F r p n =
      cycles K F (r + 1) p n ⊔ (boundaries K F r p n ⊓ cycles K F r p n) :=
  le_antisymm (kernelNumerator_le K F hanti r p n) (le_kernelNumerator K F hanti r p n)

/-- The boundaries at `r + 1`, with the index arithmetic normalised:
`D_{r+1}^{p,n} = Z_r^{p+1,n} ⊔ d (Z_r^{p-r,n-1})`. This is the form the boundary side of the
page-turning isomorphism needs. -/
theorem boundaries_succ_eq (r p n : ℤ) :
    boundaries K F (r + 1) p n =
      cycles K F r (p + 1) n ⊔
        (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1)) := by
  rw [boundaries, show r + 1 - 1 = r from by omega, show p - (r + 1) + 1 = p - r from by omega]

/-- **Monotonicity of the cycles in both indices.** `Z_{r'}^{p',n} ≤ Z_r^{p,n}` as soon as
`p ≤ p'` and `p + r ≤ p' + r'`: the first condition compares the filtration steps, the second
compares the conditions on the differential. Subsumes `cycles_succ_le` and
`cycles_pred_succ_le`. -/
theorem cycles_mono (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) {r r' p p' : ℤ} (n : ℤ)
    (hp : p ≤ p') (hpr : p + r ≤ p' + r') : cycles K F r' p' n ≤ cycles K F r p n :=
  cycles_le_cycles K F hanti n hp hpr

/-- The easy half of the companion (boundary-side) identity: the denominator of the `(r+1)`-st page
lies in the numerator of the image of `d_r` together with the `r`-th denominator. -/
theorem boundaries_succ_inf_le (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    boundaries K F (r + 1) p n ⊓ cycles K F (r + 1) p n ≤
      (boundaries K F r p n ⊓ cycles K F r p n) ⊔
        (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1)) := by
  rw [boundaries_succ_eq]
  refine _root_.inf_le_left.trans (_root_.sup_le ?_ _root_.le_sup_right)
  refine _root_.le_sup_of_le_left (_root_.le_inf ?_ ?_)
  · rw [boundaries]
    exact _root_.le_sup_of_le_left (cycles_mono K F hanti n (by omega) (by omega))
  · exact cycles_mono K F hanti n (by omega) (by omega)

/-- Inside `Z_{r+1}^{p,n}`, the join of `D_r^{p,n} ⊓ Z_r^{p,n}` with `d (Z_r^{p-r,n-1})` lies in
`D_{r+1}^{p,n}`. -/
theorem le_boundaries_succ (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    cycles K F (r + 1) p n ⊓
        ((boundaries K F r p n ⊓ cycles K F r p n) ⊔
          (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1))) ≤
      boundaries K F (r + 1) p n := by
  rw [boundaries_succ_eq]
  refine Subobject.le_of_factors ?_
  set V := (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1)) with hV
  set W := cycles K F (r + 1) p n ⊓ ((boundaries K F r p n ⊓ cycles K F r p n) ⊔ V) with hW
  obtain ⟨T₁, w₁, hw₁, x, v, fac₁⟩ :=
    exists_refinement_of_factors_sup (x := boundaries K F r p n ⊓ cycles K F r p n) (y := V)
      W.arrow (Subobject.factors_of_le _ _root_.inf_le_right (Subobject.factors_self W))
  have hxD :
    (cycles K F (r - 1) (p + 1) n ⊔
          (Subobject.exists (K.d (n - 1) n)).obj (cycles K F (r - 1) (p - r + 1) (n - 1))).Factors
      (x ≫ (boundaries K F r p n ⊓ cycles K F r p n).arrow) :=
    factors_comp_arrow_of_le _root_.inf_le_left x
  obtain ⟨T₂, w₂, hw₂, a, db, fac₂⟩ := exists_refinement_of_factors_sup _ hxD
  refine factors_of_epi_comp (w₂ ≫ w₁) _ ?_
  have hsplit :
    (w₂ ≫ w₁) ≫ W.arrow =
      a ≫ (cycles K F (r - 1) (p + 1) n).arrow +
        (db ≫
            ((Subobject.exists (K.d (n - 1) n)).obj
                (cycles K F (r - 1) (p - r + 1) (n - 1))).arrow +
          w₂ ≫ v ≫ V.arrow) := by
    calc
      (w₂ ≫ w₁) ≫ W.arrow = w₂ ≫ (w₁ ≫ W.arrow) := by rw [Category.assoc]
      _ = w₂ ≫ (x ≫ (boundaries K F r p n ⊓ cycles K F r p n).arrow + v ≫ V.arrow) := by rw [fac₁]
      _ = w₂ ≫ (x ≫ (boundaries K F r p n ⊓ cycles K F r p n).arrow) + w₂ ≫ (v ≫ V.arrow) := by
        rw [comp_add]
      _ =
          (a ≫ (cycles K F (r - 1) (p + 1) n).arrow +
              db ≫
                ((Subobject.exists (K.d (n - 1) n)).obj
                    (cycles K F (r - 1) (p - r + 1) (n - 1))).arrow) +
            w₂ ≫ (v ≫ V.arrow) :=
        by rw [fac₂]
      _ = _ := by abel
  rw [hsplit]
  refine Subobject.factors_add _ _ ?_ (Subobject.factors_add _ _ ?_ ?_)
  · refine Subobject.sup_factors_of_factors_left (cycles_factors K F _ ?_ ?_)
    · exact factors_comp_arrow_of_le (cycles_le_F K F (r - 1) (p + 1) n) a
    · have hkill1 :
        (db ≫
              ((Subobject.exists (K.d (n - 1) n)).obj
                  (cycles K F (r - 1) (p - r + 1) (n - 1))).arrow) ≫
            K.d n (n + 1) =
          0 := by
        rw [Category.assoc]
        exact comp_eq_zero_of_factors_exists (K.d_comp_d _ _ _) _ db
      have hkill2 : (w₂ ≫ v ≫ V.arrow) ≫ K.d n (n + 1) = 0 := by
        have h :=
          comp_eq_zero_of_factors_exists (f := K.d (n - 1) n) (g := K.d n (n + 1))
            (K.d_comp_d _ _ _) (cycles K F r (p - r) (n - 1)) (w₂ ≫ v)
        simpa only [Category.assoc] using h
      have hda :
        (a ≫ (cycles K F (r - 1) (p + 1) n).arrow) ≫ K.d n (n + 1) =
          ((w₂ ≫ w₁) ≫ W.arrow) ≫ K.d n (n + 1) := by
        rw [hsplit, add_comp, add_comp, hkill1, hkill2, add_zero, add_zero]
      rw [hda, show p + 1 + r = p + r + 1 from by omega, Category.assoc]
      refine Subobject.factors_of_factors_right _ ?_
      have hWZ : W ≤ cycles K F (r + 1) p n := by
        rw [hW]; exact _root_.inf_le_left
      exact factors_arrow_comp_of_exists_le _ ((((Subobject.exists _).monotone hWZ).trans
        (exists_cycles_succ_le K F r p n)).trans (cycles_le_F K F (r - 1) (p + r + 1) (n + 1)))
  · refine Subobject.sup_factors_of_factors_right ?_
    exact factors_comp_arrow_of_le
      ((Subobject.exists _).monotone (cycles_mono K F hanti (n - 1) (by omega) (by omega))) db
  · exact
      Subobject.sup_factors_of_factors_right
        (Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow v))

/-- **The companion (boundary-side) identity.** Inside `Z_{r+1}`, the numerator of the image of
`d_r` together with the `r`-th denominator cuts out exactly the `(r+1)`-st denominator:
```
Z_{r+1} ⊓ ((D_r ⊓ Z_r) ⊔ d (Z_r^{p-r,n-1})) = D_{r+1} ⊓ Z_{r+1}
```
With `kernelNumerator_eq` this is the second of the two identities the page-turning isomorphism
needs, after which `exists_iso_cokernel_of_factors_iff` identifies the two presentations of the
subquotient. -/
theorem boundaries_succ_inf_eq (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m) (r p n : ℤ) :
    cycles K F (r + 1) p n ⊓
        ((boundaries K F r p n ⊓ cycles K F r p n) ⊔
          (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1))) =
      boundaries K F (r + 1) p n ⊓ cycles K F (r + 1) p n :=
  le_antisymm (_root_.le_inf (le_boundaries_succ K F hanti r p n) _root_.inf_le_left)
    (_root_.le_inf _root_.inf_le_right (boundaries_succ_inf_le K F hanti r p n))

/-- `exists_cycles_le` with the target degree given up to arithmetic. -/
theorem exists_cycles_le' (r p n n' : ℤ) (h : n' = n + 1) :
    (Subobject.exists (K.d n n')).obj (cycles K F r p n) ≤ cycles K F r (p + r) n' := by
  subst h; exact exists_cycles_le K F r p n

/-- `V = d(Z_r^{p-r,n-1})` lies in `Z_{r+1}^{p,n}`: it lies in `Z_r^{p,n}` hence in `F^p`, and its
differential is zero, so the `F^{p+r+1}` condition is free. -/
theorem exists_cycles_le_cycles_succ (r p n : ℤ) :
    (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1))
      ≤ cycles K F (r + 1) p n := by
  refine le_cycles K F ?_ ?_
  · have h := exists_cycles_le' K F r (p - r) (n - 1) n (by omega)
    rw [show p - r + r = p by omega] at h
    exact h.trans (cycles_le_F K F r p n)
  · rw [le_pullback_iff, exists_arrow_comp_eq_zero (K.d_comp_d _ _ _)]
    exact Subobject.factors_zero

/-- **The butterfly's numerator is the kernel numerator.** Adjoining the image of the incoming
differential to `Z_{r+1} ⊔ (D_r ⊓ Z_r)` changes nothing, because that image already lies in
`Z_{r+1}`. So the subquotient `pageCycles / image` has numerator `kernelNumerator`. -/
theorem cycles_succ_sup_eq_kernelNumerator (hanti : ∀ p p' m : ℤ, p ≤ p' → F p' m ≤ F p m)
    (r p n : ℤ) :
    cycles K F (r + 1) p n
        ⊔ ((boundaries K F r p n ⊓ cycles K F r p n)
          ⊔ (Subobject.exists (K.d (n - 1) n)).obj (cycles K F r (p - r) (n - 1)))
      = kernelNumerator K F r p n := by
  rw [kernelNumerator_eq K F hanti r p n, ← _root_.sup_assoc]
  exact _root_.sup_eq_left.2
    ((exists_cycles_le_cycles_succ K F r p n).trans _root_.le_sup_left)

end FilteredComplexSpectralSequence

end

module

public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
import Mathlib.Tactic.Ring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Functoriality of the spectral sequence of a filtered complex

A morphism `φ : K ⟶ L` of complexes which carries each step `F^p K^n` of a filtration of `K`
into the step `F^p L^n` of a filtration of `L` carries the cycles `Z_r^{p,q}` and boundaries
`D_r^{p,q}` of `K` into those of `L`, hence induces maps `E_r^{p,q}(K) ⟶ E_r^{p,q}(L)` on the
pages of the spectral sequences. These commute with the differentials `d_r` and with the
identifications `E_{r+1} = H(E_r)`, so they form a morphism of spectral sequences
([Stacks, Tag 012O]); the construction is functorial in `φ`. Two such morphisms which are
homotopic through a homotopy compatible with the filtrations induce the same maps on the pages
`E_r` for `r ≥ 1`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite Subobject

namespace FilteredComplexSpectralSequence

variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : CochainComplex A ℤ} {FK : ℤ → ∀ n : ℤ, Subobject (K.X n)}
  {FL : ℤ → ∀ n : ℤ, Subobject (L.X n)}

/-- If `P ≤ R` and `f` carries `R` into `Q`, then `P.arrow ≫ f` factors through `Q`. -/
private lemma factors_arrow_comp_of_le {X Y : A} {P R : Subobject X} {Q : Subobject Y} (f : X ⟶ Y)
    (hP : P ≤ R) (hf : («exists» f).obj R ≤ Q) : Q.Factors (P.arrow ≫ f) :=
  factors_arrow_comp_of_exists_le _ (((Subobject.exists _).monotone hP).trans hf)

section Map

variable (φ : K ⟶ L) (hφ : ∀ p n : ℤ, («exists» (φ.f n)).obj (FK p n) ≤ FL p n)

include hφ

/-- The image under `φ` of `Z_r^{p,q}(K)` is contained in `Z_r^{p,q}(L)`. -/
lemma exists_cycles_le_cycles_map (r p n : ℤ) :
    («exists» (φ.f n)).obj (cycles K FK r p n) ≤ cycles L FL r p n := by
  rw [exists_le_iff_le_pullback, le_pullback_iff]
  refine cycles_factors L FL _ (factors_arrow_comp_of_le _ (cycles_le_F K FK r p n) (hφ p n)) ?_
  rw [Category.assoc, φ.comm, ← Category.assoc, ← deltaCycles_arrow K FK r p n, Category.assoc]
  exact factors_of_factors_right _
    (factors_arrow_comp_of_le _ (cycles_le_F K FK r (p + r) (n + 1)) (hφ (p + r) (n + 1)))

/-- The image under `φ` of `D_r^{p,q}(K)` is contained in `D_r^{p,q}(L)`. -/
lemma exists_boundaries_le_boundaries_map (r p n : ℤ) :
    («exists» (φ.f n)).obj (boundaries K FK r p n) ≤ boundaries L FL r p n := by
  rw [exists_le_iff_le_pullback, boundaries]
  refine sup_le ?_ ?_
  · rw [← exists_le_iff_le_pullback, boundaries]
    exact (exists_cycles_le_cycles_map φ hφ _ _ _).trans le_sup_left
  · rw [← exists_le_iff_le_pullback, ← Subobject.exists_comp, ← φ.comm, Subobject.exists_comp,
      boundaries]
    exact ((Subobject.exists _).monotone (exists_cycles_le_cycles_map φ hφ _ _ _)).trans
      le_sup_right

/-- The image under `φ` of `D_r^{p,q}(K) ⊓ Z_r^{p,q}(K)` is contained in
`D_r^{p,q}(L) ⊓ Z_r^{p,q}(L)`. -/
lemma exists_den_le_den_map (r p n : ℤ) :
    («exists» (φ.f n)).obj (boundaries K FK r p n ⊓ cycles K FK r p n) ≤
      boundaries L FL r p n ⊓ cycles L FL r p n :=
  le_inf (((Subobject.exists _).monotone inf_le_left).trans
      (exists_boundaries_le_boundaries_map φ hφ r p n))
    (((Subobject.exists _).monotone inf_le_right).trans (exists_cycles_le_cycles_map φ hφ r p n))

/-- The map `Z_r^{p,q}(K) ⟶ Z_r^{p,q}(L)` induced by `φ`. -/
noncomputable def cyclesMap (r p n : ℤ) :
    ((cycles K FK r p n : Subobject (K.X n)) : A) ⟶ ((cycles L FL r p n : Subobject (L.X n)) : A) :=
  factorThru _ ((cycles K FK r p n).arrow ≫ φ.f n)
    (factors_arrow_comp_of_exists_le _ (exists_cycles_le_cycles_map φ hφ r p n))

/-- The map `cyclesMap φ hφ r p n` is the restriction of `φ.f n` to `Z_r^{p,q}`. -/
@[reassoc (attr := simp)]
lemma cyclesMap_arrow (r p n : ℤ) :
    cyclesMap φ hφ r p n ≫ (cycles L FL r p n).arrow = (cycles K FK r p n).arrow ≫ φ.f n :=
  factorThru_arrow _ _ _

/-- The map `E_r^{p,q}(K) ⟶ E_r^{p,q}(L)` induced by `φ`. -/
noncomputable def pageObjMap (r p n : ℤ) : pageObj K FK r p n ⟶ pageObj L FL r p n :=
  cokernel.desc _ (cyclesMap φ hφ r p n ≫ cokernel.π (den L FL r p n)) (by
    rw [← Category.assoc, comp_cokernel_π_eq_zero_iff _ (den_arrow L FL r p n), Category.assoc,
      cyclesMap_arrow, ← Category.assoc, den_arrow]
    exact factors_arrow_comp_of_exists_le _ (exists_den_le_den_map φ hφ r p n))

/-- The map `pageObjMap φ hφ r p n` is induced by `cyclesMap φ hφ r p n` on cokernels. -/
@[reassoc (attr := simp)]
lemma π_pageObjMap (r p n : ℤ) :
    cokernel.π (den K FK r p n) ≫ pageObjMap φ hφ r p n =
      cyclesMap φ hφ r p n ≫ cokernel.π (den L FL r p n) :=
  cokernel.π_desc _ _ _

/-- The maps `cyclesMap φ hφ` commute with the maps `deltaCycles : Z_r^{p,q} ⟶ Z_r^{p+r,q-r+1}`
induced by the differentials. -/
@[reassoc]
lemma cyclesMap_deltaCycles (r p n : ℤ) :
    cyclesMap φ hφ r p n ≫ deltaCycles L FL r p n =
      deltaCycles K FK r p n ≫ cyclesMap φ hφ r (p + r) (n + 1) := by
  rw [← cancel_mono (cycles L FL r (p + r) (n + 1)).arrow, Category.assoc, deltaCycles_arrow,
    cyclesMap_arrow_assoc, Category.assoc, cyclesMap_arrow,
    reassoc_of% deltaCycles_arrow K FK r p n,
    φ.comm]

/-- The maps `pageObjMap φ hφ` commute with the differentials `d_r` of the `r`-th pages. -/
@[reassoc]
lemma pageObjMap_pageMap (r p n : ℤ) :
    pageObjMap φ hφ r p n ≫ pageMap L FL r p n =
      pageMap K FK r p n ≫ pageObjMap φ hφ r (p + r) (n + 1) := by
  rw [← cancel_epi (cokernel.π (den K FK r p n)), π_pageObjMap_assoc, π_comp_pageMap,
    reassoc_of% π_comp_pageMap K FK r p n, π_pageObjMap, cyclesMap_deltaCycles_assoc]

/-- The maps `pageObjMap φ hφ` commute with the identifications `E_r^{p,n} = E_r^{p',n'}` for
`p = p'` and `n = n'`. -/
@[reassoc]
lemma pageObjMap_eqToHom (r p p' n n' : ℤ) (hp : p = p') (hn : n = n') :
    pageObjMap φ hφ r p n ≫ eqToHom (by rw [hp, hn]) =
      eqToHom (by rw [hp, hn]) ≫ pageObjMap φ hφ r p' n' := by
  subst hp hn
  simp

/-- The morphism `E_r(K) ⟶ E_r(L)` of `r`-th pages induced by `φ`. -/
@[ega "0 13.6.5" "special case"]
noncomputable def pageHom (r : ℤ) : pageComplex K FK r ⟶ pageComplex L FL r where
  f pq := pageObjMap φ hφ r pq.1 (pq.1 + pq.2)
  comm' pq pq' h := by
    rw [ComplexShape.up'_Rel] at h
    rw [pageComplex_d K FK r h, pageComplex_d L FL r h, pageMap', pageMap',
      pageObjMap_pageMap_assoc, Category.assoc, pageObjMap_eqToHom]
    · rw [← h, Prod.fst_add]
    · rw [← h, Prod.fst_add, Prod.snd_add]; dsimp only; ring

/-- The component of `pageHom φ hφ r` at `(p, q)` is `pageObjMap φ hφ r p (p + q)`. -/
@[simp]
lemma pageHom_f (r : ℤ) (pq : ℤ × ℤ) :
    (pageHom φ hφ r).f pq = pageObjMap φ hφ r pq.1 (pq.1 + pq.2) := rfl

variable (hantiK : ∀ p p' n : ℤ, p ≤ p' → FK p' n ≤ FK p n)
  (hantiL : ∀ p p' n : ℤ, p ≤ p' → FL p' n ≤ FL p n)

/-- The cycle of the `r`-th page represented by an element of `Z_{r+1}`. -/
noncomputable def liftSucc (r : ℤ) (pq : ℤ × ℤ) :
    ((cycles K FK (r + 1) pq.1 (pq.1 + pq.2) : Subobject _) : A) ⟶
      (pageComplex K FK r).cycles pq :=
  (pageComplex K FK r).liftCycles
    (Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K FK hantiK r pq.1 _) ≫
      cokernel.π (Subobject.ofLE _ _ (den_le_kernelNumerator K FK hantiK r pq.1 _)) ≫
        pageCyclesι K FK hantiK r pq.1 (pq.1 + pq.2))
    (pq + (r, 1 - r)) ((ComplexShape.up' ((r, 1 - r) : ℤ × ℤ)).next_eq'
      (by rw [ComplexShape.up'_Rel]))
    (by
      rw [comp_d_eq_zero_iff, Category.assoc, Category.assoc, pageCyclesι_comp_pageMap,
        comp_zero, comp_zero])

omit hφ in
/-- The class in `H(E_r)` of the cycle `liftSucc hantiK r pq`, transported along
`pageHomologyIso`, is the class in `E_{r+1}` of the corresponding element of `Z_{r+1}`. -/
lemma liftSucc_homologyπ_pageHomologyIso (r : ℤ) (pq : ℤ × ℤ) :
    liftSucc hantiK r pq ≫ (pageComplex K FK r).homologyπ pq ≫
        (pageHomologyIso K FK hantiK r pq).hom =
      cokernel.π (den K FK (r + 1) pq.1 (pq.1 + pq.2)) := by
  have := homologyπ_comp_pageHomologyIso_hom K FK hantiK r pq (liftSucc hantiK r pq) (𝟙 _)
    (Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K FK hantiK r pq.1 _) ≫
      Subobject.ofLE _ _ (kernelNumerator_le_cycles K FK r pq.1 _))
    (by simp) (by rw [liftSucc, HomologicalComplex.liftCycles_i, Category.assoc,
      π_comp_pageCyclesι, ← Category.assoc])
  rwa [Category.id_comp] at this

/-- Under the identifications `H(E_r) = E_{r+1}` given by `pageHomologyIso`, the map induced by
`pageHom φ hφ r` on homology is `pageObjMap φ hφ (r + 1)`. -/
lemma homologyMap_pageHom_comp_pageHomologyIso (r : ℤ) (pq : ℤ × ℤ) :
    HomologicalComplex.homologyMap (pageHom φ hφ r) pq ≫
        (pageHomologyIso L FL hantiL r pq).hom =
      (pageHomologyIso K FK hantiK r pq).hom ≫ pageObjMap φ hφ (r + 1) pq.1 (pq.1 + pq.2) := by
  rw [← cancel_epi (pageHomologyIso K FK hantiK r pq).inv, Iso.inv_hom_id_assoc,
    ← cancel_epi (cokernel.π (den K FK (r + 1) pq.1 (pq.1 + pq.2))), π_pageObjMap,
    ← liftSucc_homologyπ_pageHomologyIso hantiK r pq]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  have := homologyπ_comp_pageHomologyIso_hom L FL hantiL r pq
    (liftSucc hantiK r pq ≫ HomologicalComplex.cyclesMap (pageHom φ hφ r) pq)
    (cyclesMap φ hφ (r + 1) pq.1 (pq.1 + pq.2))
    ((Subobject.ofLE _ _ (cyclesSucc_le_kernelNumerator K FK hantiK r pq.1 _) ≫
      Subobject.ofLE _ _ (kernelNumerator_le_cycles K FK r pq.1 _)) ≫
        cyclesMap φ hφ r pq.1 (pq.1 + pq.2))
    (by simp)
    (by
      rw [Category.assoc, HomologicalComplex.cyclesMap_i, liftSucc,
        HomologicalComplex.liftCycles_i_assoc, pageHom_f, Category.assoc, Category.assoc,
        reassoc_of% π_comp_pageCyclesι K FK hantiK r pq.1 (pq.1 + pq.2), Category.assoc,
        Category.assoc, π_pageObjMap])
  simpa only [Category.assoc] using this

/-- A morphism `φ : K ⟶ L` of filtered complexes, i.e. carrying each `F^p K^n` into `F^p L^n`,
induces a morphism of spectral sequences `E_r(K) ⟶ E_r(L)`: on the `r`-th pages it is the map
`Z_r^{p,q}(K)/D_r^{p,q}(K) ⟶ Z_r^{p,q}(L)/D_r^{p,q}(L)` induced by `φ`, and these maps commute
with the differentials `d_r` and the identifications `H(E_r) = E_{r+1}`. -/
@[stacks 012O, ega "0 11.2.3" "existence of E(u)", ega "0 11.2.2" "functoriality"]
noncomputable def spectralSequenceMap :
    spectralSequence K FK hantiK ⟶ spectralSequence L FL hantiL where
  hom r _ := pageHom φ hφ r
  comm r r' pq hrr' hr := by
    subst hrr'
    exact homologyMap_pageHom_comp_pageHomologyIso φ hφ hantiK hantiL r pq

/-- The map of `spectralSequenceMap φ hφ hantiK hantiL` on the `r`-th pages is
`pageHom φ hφ r`. -/
@[simp]
lemma spectralSequenceMap_hom (r : ℤ) (hr : 0 ≤ r) :
    (spectralSequenceMap φ hφ hantiK hantiL).hom r hr = pageHom φ hφ r := rfl

end Map


section Laws

/-- The image of a subobject `P` of `X` under `𝟙 X` is contained in `P`. -/
lemma exists_id_le (X : A) (P : Subobject X) : («exists» (𝟙 X)).obj P ≤ P := by
  rw [exists_le_iff_le_pullback, pullback_id]

/-- The identity of `K` carries each `F^p K^n` into itself. -/
lemma exists_id_f_le (p n : ℤ) : («exists» ((𝟙 K : K ⟶ K).f n)).obj (FK p n) ≤ FK p n := by
  rw [HomologicalComplex.id_f]
  exact exists_id_le _ _

/-- The map on `Z_r^{p,q}` induced by the identity is the identity. -/
@[simp]
lemma cyclesMap_id (r p n : ℤ) :
    cyclesMap (FK := FK) (FL := FK) (𝟙 K) exists_id_f_le r p n = 𝟙 _ := by
  rw [← cancel_mono (cycles K FK r p n).arrow, cyclesMap_arrow, HomologicalComplex.id_f,
    Category.comp_id, Category.id_comp]

/-- The map on `Z_r^{p,q}` induced by a composite is the composite of the induced maps. -/
lemma cyclesMap_comp {M : CochainComplex A ℤ} {FM : ℤ → ∀ n : ℤ, Subobject (M.X n)}
    (φ : K ⟶ L) (hφ : ∀ p n : ℤ, («exists» (φ.f n)).obj (FK p n) ≤ FL p n)
    (ψ : L ⟶ M) (hψ : ∀ p n : ℤ, («exists» (ψ.f n)).obj (FL p n) ≤ FM p n)
    (hφψ : ∀ p n : ℤ, («exists» ((φ ≫ ψ).f n)).obj (FK p n) ≤ FM p n) (r p n : ℤ) :
    cyclesMap (φ ≫ ψ) hφψ r p n = cyclesMap φ hφ r p n ≫ cyclesMap ψ hψ r p n := by
  rw [← cancel_mono (cycles M FM r p n).arrow, cyclesMap_arrow, Category.assoc, cyclesMap_arrow,
    cyclesMap_arrow_assoc, HomologicalComplex.comp_f]

variable (hantiK : ∀ p p' n : ℤ, p ≤ p' → FK p' n ≤ FK p n)
  (hantiL : ∀ p p' n : ℤ, p ≤ p' → FL p' n ≤ FL p n)

/-- The morphism of spectral sequences induced by the identity is the identity. -/
lemma spectralSequenceMap_id :
    spectralSequenceMap (𝟙 K) exists_id_f_le hantiK hantiK =
      𝟙 (spectralSequence K FK hantiK) := by
  ext r hr pq : 3
  change cokernel.π _ ≫ pageObjMap _ _ r pq.1 (pq.1 + pq.2) = cokernel.π _ ≫ 𝟙 _
  rw [π_pageObjMap, cyclesMap_id, Category.id_comp, Category.comp_id]

/-- The morphism of spectral sequences induced by a composite is the composite. -/
lemma spectralSequenceMap_comp {M : CochainComplex A ℤ} {FM : ℤ → ∀ n : ℤ, Subobject (M.X n)}
    (hantiM : ∀ p p' n : ℤ, p ≤ p' → FM p' n ≤ FM p n)
    (φ : K ⟶ L) (hφ : ∀ p n : ℤ, («exists» (φ.f n)).obj (FK p n) ≤ FL p n)
    (ψ : L ⟶ M) (hψ : ∀ p n : ℤ, («exists» (ψ.f n)).obj (FL p n) ≤ FM p n)
    (hφψ : ∀ p n : ℤ, («exists» ((φ ≫ ψ).f n)).obj (FK p n) ≤ FM p n) :
    spectralSequenceMap (φ ≫ ψ) hφψ hantiK hantiM =
      spectralSequenceMap φ hφ hantiK hantiL ≫ spectralSequenceMap ψ hψ hantiL hantiM := by
  ext r hr pq : 3
  change cokernel.π _ ≫ pageObjMap _ _ r pq.1 (pq.1 + pq.2) =
    cokernel.π _ ≫ (pageObjMap φ hφ r pq.1 (pq.1 + pq.2) ≫ pageObjMap ψ hψ r pq.1 (pq.1 + pq.2))
  rw [π_pageObjMap, π_pageObjMap_assoc, π_pageObjMap, cyclesMap_comp φ hφ ψ hψ hφψ,
    Category.assoc]

end Laws

section Homotopy

private lemma factors_sub' {X Y : A} {P : Subobject Y} (f g : X ⟶ Y) (hf : P.Factors f)
    (hg : P.Factors g) : P.Factors (f - g) := by
  rw [← factorThru_arrow P f hf, ← factorThru_arrow P g hg, ← Preadditive.sub_comp]
  exact factors_comp_arrow _

private lemma cycles_factors_of_eq {r p n p' n' : ℤ} (hp : p + r = p') (hn : n + 1 = n') {T : A}
    (g : T ⟶ L.X n) (h1 : (FL p n).Factors g) (h2 : (FL p' n').Factors (g ≫ L.d n n')) :
    (cycles L FL r p n).Factors g := by
  subst hp hn
  exact cycles_factors L FL g h1 h2

private lemma factors_FL_of_le (hantiL : ∀ p p' n : ℤ, p ≤ p' → FL p' n ≤ FL p n) {m j : ℤ}
    {P : Subobject (K.X m)} {p p' : ℤ} (hP : P ≤ FK p m) (hpp' : p' ≤ p) (u : K.X m ⟶ L.X j)
    (hu : ∀ q, («exists» u).obj (FK q m) ≤ FL q j) :
    (FL p' j).Factors (P.arrow ≫ u) :=
  factors_arrow_comp_of_le _ hP ((hu p).trans (hantiL _ _ _ hpp'))

private lemma homotopy_sub {φ ψ : K ⟶ L} (h : Homotopy φ ψ) (n : ℤ) :
    φ.f n - ψ.f n = K.d n (n + 1) ≫ h.hom (n + 1) n + h.hom n (n - 1) ≫ L.d (n - 1) n := by
  rw [h.comm n, dNext_eq _ (show (ComplexShape.up ℤ).Rel n (n + 1) from rfl),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (n - 1) n by simp)]
  abel

private lemma hom_comp_d_eq {φ ψ : K ⟶ L} (h : Homotopy φ ψ) {i j : ℤ} (hij : j + 1 = i) :
    h.hom i j ≫ L.d j i = (φ.f i - ψ.f i) - K.d i (i + 1) ≫ h.hom (i + 1) i := by
  subst hij
  rw [homotopy_sub h (j + 1), show j + 1 - 1 = j by ring]
  abel

variable (hantiL : ∀ p p' n : ℤ, p ≤ p' → FL p' n ≤ FL p n)
  {φ ψ : K ⟶ L} (hφ : ∀ p n : ℤ, («exists» (φ.f n)).obj (FK p n) ≤ FL p n)
  (hψ : ∀ p n : ℤ, («exists» (ψ.f n)).obj (FK p n) ≤ FL p n)
  (h : Homotopy φ ψ) (hh : ∀ p i j : ℤ, («exists» (h.hom i j)).obj (FK p i) ≤ FL p j)

include hantiL hh

/-- **Homotopy invariance.** Morphisms of filtered complexes which are homotopic through a
homotopy compatible with the filtrations induce the same maps on the pages `E_r`, `r ≥ 1`. -/
@[ega "0 11.2.3" "special case"]
lemma pageObjMap_eq_of_homotopy {r : ℤ} (hr : 1 ≤ r) (p n : ℤ) :
    pageObjMap φ hφ r p n = pageObjMap ψ hψ r p n := by
  rw [← cancel_epi (cokernel.π (den K FK r p n)), π_pageObjMap, π_pageObjMap, ← sub_eq_zero,
    ← Preadditive.sub_comp, comp_cokernel_π_eq_zero_iff _ (den_arrow L FL r p n),
    Preadditive.sub_comp, cyclesMap_arrow, cyclesMap_arrow, ← Preadditive.comp_sub]
  set Z := cycles K FK r p n
  have hZ : Z ≤ FK p n := cycles_le_F K FK r p n
  have hdiff : ∀ m q (P : Subobject (K.X m)), P ≤ FK q m →
      (FL q m).Factors (P.arrow ≫ (φ.f m - ψ.f m)) := fun m q P hP => by
    rw [Preadditive.comp_sub]
    exact factors_sub' _ _ (factors_arrow_comp_of_le _ hP (hφ q m))
      (factors_arrow_comp_of_le _ hP (hψ q m))
  have hd : ∀ {Y : A} (g : K.X (n + 1) ⟶ Y) (P : Subobject Y),
      P.Factors ((cycles K FK r (p + r) (n + 1)).arrow ≫ g) →
        P.Factors (Z.arrow ≫ K.d n (n + 1) ≫ g) :=
    fun g P hg => by
      rw [← Category.assoc, ← deltaCycles_arrow K FK r p n, Category.assoc]
      exact factors_of_factors_right _ hg
  have hδ : ∀ p', p' ≤ p + r → (FL p' n).Factors (Z.arrow ≫ K.d n (n + 1) ≫ h.hom (n + 1) n) :=
    fun p' hp' => hd _ _ (factors_FL_of_le hantiL (cycles_le_F K FK r (p + r) (n + 1)) hp' _
      (hh · (n + 1) n))
  have h₁ : (cycles L FL (r - 1) (p + 1) n).Factors
      (Z.arrow ≫ K.d n (n + 1) ≫ h.hom (n + 1) n) := by
    refine cycles_factors_of_eq (p' := p + r) (n' := n + 1) (by ring) rfl _ (hδ _ (by omega)) ?_
    have hz : Z.arrow ≫ K.d n (n + 1) ≫ K.d (n + 1) (n + 1 + 1) ≫
        h.hom (n + 1 + 1) (n + 1) = 0 := by
      rw [HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]
    simp only [Category.assoc]
    rw [hom_comp_d_eq h rfl, Preadditive.comp_sub, Preadditive.comp_sub, hz, sub_zero]
    exact hd _ _ (hdiff _ _ _ (cycles_le_F K FK r (p + r) (n + 1)))
  have h₂ : Subobject.Factors
      ((«exists» (L.d (n - 1) n)).obj (cycles L FL (r - 1) (p - r + 1) (n - 1)))
      (Z.arrow ≫ h.hom n (n - 1) ≫ L.d (n - 1) n) := by
    have hg : (cycles L FL (r - 1) (p - r + 1) (n - 1)).Factors (Z.arrow ≫ h.hom n (n - 1)) := by
      refine cycles_factors_of_eq (p' := p) (n' := n) (by ring) (by ring) _
        (factors_FL_of_le hantiL hZ (by omega) _ (hh · n (n - 1))) ?_
      rw [Category.assoc, hom_comp_d_eq h (by ring), Preadditive.comp_sub]
      exact factors_sub' _ _ (hdiff _ _ _ hZ) (hδ p (by omega))
    rw [← Category.assoc, ← factorThru_arrow _ _ hg, Category.assoc]
    exact factors_of_factors_right _ (factors_arrow_comp _ _)
  refine (inf_factors _).2 ⟨?_, ?_⟩
  · rw [homotopy_sub h n, Preadditive.comp_add, boundaries]
    exact factors_add _ _ (sup_factors_of_factors_left h₁) (sup_factors_of_factors_right h₂)
  · rw [Preadditive.comp_sub, ← cyclesMap_arrow φ hφ, ← cyclesMap_arrow ψ hψ,
      ← Preadditive.sub_comp]
    exact factors_comp_arrow _

/-- **Homotopy invariance for the morphism of spectral sequences.** -/
@[ega "0 11.2.3" "special case"]
lemma spectralSequenceMap_hom_eq_of_homotopy
    (hantiK : ∀ p p' n : ℤ, p ≤ p' → FK p' n ≤ FK p n) {r : ℤ} (hr : 1 ≤ r) :
    (spectralSequenceMap φ hφ hantiK hantiL).hom r (by omega) =
      (spectralSequenceMap ψ hψ hantiK hantiL).hom r (by omega) := by
  ext pq : 1
  exact pageObjMap_eq_of_homotopy hantiL hφ hψ h hh hr _ _

end Homotopy

end FilteredComplexSpectralSequence

namespace CochainComplex

open FilteredComplexSpectralSequence Subobject

/-- The filtration `F^p K^n = Im(F^p K^• ⟶ K^•)` of a filtered complex decreases in `p`. -/
lemma antitone_of_eq {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n)) :
    ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n :=
  fun _ _ n hp => F_antitone K F hF hp n

/-- The spectral sequence of a filtered complex, for a presentation `F` of its filtration. -/
noncomputable abbrev spectralSequenceOf {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n)) :
    CohomologicalSpectralSequence A 0 :=
  spectralSequence K.X F (antitone_of_eq K F hF)

/-- **[Stacks, Tag 012M] for the spectral sequence of a filtered complex as constructed.** The
spectral sequence `spectralSequence K^• F` of a filtered complex has pages
`Z_r^{p,q}/D_r^{p,q}`, differentials induced by `d`, zeroth page `gr^p K^•` and first page
`H^n(gr^p K^•)`. -/
theorem exists_iso_spectralSequence_page
    {A : Type u} [Category.{v} A] [Abelian A]
    (K : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ)
    (F : ∀ (_p n : ℤ), Subobject (K.X.X n))
    (hF : ∀ p n : ℤ, F p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
    (Z : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hZ : ∀ r p n : ℤ, Z r p n =
      F p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (F (p + r) (n + 1)))
    (D : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
    (hD : ∀ r p n : ℤ, D r p n = Z (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Z (r - 1) (p - r + 1) (n - 1))) :
    ∃ (e : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q),
        ((spectralSequenceOf K F hF).page r hr).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)))
      (α : ∀ (p q n : ℤ), n = p + q → (((spectralSequenceOf K F hF).page 0 le_rfl).X (p, q) ≅
        ((FilteredObject.gr p).obj K).X n)),
      (∀ (r p q n : ℤ) (hr : 0 ≤ r) (hn : n = p + q),
        ∃ δ : (Z r p n : A) ⟶ (Z r (p + r) (n + 1) : A),
          δ ≫ (Z r (p + r) (n + 1)).arrow = (Z r p n).arrow ≫ K.X.d n (n + 1) ∧
          cokernel.π (Subobject.ofLE _ _ (inf_le_right : D r p n ⊓ Z r p n ≤ Z r p n)) ≫
              (e r p q n hr hn).inv ≫
                  ((spectralSequenceOf K F hF).page r hr).d (p, q) (p + r, q - r + 1) =
            δ ≫ cokernel.π (Subobject.ofLE _ _ (inf_le_right :
                D r (p + r) (n + 1) ⊓ Z r (p + r) (n + 1) ≤ Z r (p + r) (n + 1))) ≫
              (e r (p + r) (q - r + 1) (n + 1) hr (by omega)).inv) ∧
      (∀ (p q n : ℤ) (hn : n = p + q) (u : (Z 0 p n : A) ⟶ (K.filtration.obj (op p)).X n),
        u ≫ (K.filtration.ι.app (op p)).f n = (Z 0 p n).arrow →
        cokernel.π (Subobject.ofLE _ _ (inf_le_right : D 0 p n ⊓ Z 0 p n ≤ Z 0 p n)) ≫
            (e 0 p q n le_rfl hn).inv ≫ (α p q n hn).hom =
          u ≫ (FilteredObject.grMapπ (FilteredObject.succHom p) K).f n) ∧
      (∀ (p q n : ℤ) (hn : n = p + q),
        ((spectralSequenceOf K F hF).page 0 le_rfl).d (p, q) (p, q + 1) ≫
            (α p (q + 1) (n + 1) (by omega)).hom =
          (α p q n hn).hom ≫
            ((FilteredObject.gr p).obj K).d n (n + 1)) ∧
      (∀ p q n : ℤ, n = p + q → Nonempty (((spectralSequenceOf K F hF).page 1).X (p, q) ≅
        ((FilteredObject.gr p).obj K).homology n)) := by
  have hZ' : Z = FilteredComplexSpectralSequence.cycles K.X F := by
    funext r p n; rw [hZ, FilteredComplexSpectralSequence.cycles]
  subst hZ'
  have hD' : D = FilteredComplexSpectralSequence.boundaries K.X F := by
    funext r p n; rw [hD, FilteredComplexSpectralSequence.boundaries]
  subst hD'
  have hanti : ∀ p p' n : ℤ, p ≤ p' → F p' n ≤ F p n := fun _ _ n hp => F_antitone K F hF hp n
  obtain ⟨α, h2, h3, h4⟩ := exists_iso_gradedPiece_zeroPage K F hF hanti
  refine ⟨eIso K.X F hanti, α, ?_, h2, h3, h4⟩
  intro r p q n hr hn
  refine ⟨deltaCycles K.X F r p n, deltaCycles_arrow K.X F r p n, ?_⟩
  subst hn
  rw [spectralSequence_d, eIso_inv_rfl, Category.id_comp, ← Category.assoc, π_comp_pageMap,
    Category.assoc]

section FilteredMaps

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The subobject `F^p K^n ⊆ K^n` of a filtered complex. -/
noncomputable abbrev filtrationSubobject (M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) (p n : ℤ) :
    Subobject (M.X.X n) :=
  Subobject.mk ((M.filtration.ι.app (op p)).f n)

/-- The subobjects `F^p K^n` of a filtered complex decrease in `p`. -/
lemma filtrationSubobject_antitone (M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :
    ∀ p p' n : ℤ, p ≤ p' → filtrationSubobject M p' n ≤ filtrationSubobject M p n :=
  fun _ _ n hp => F_antitone M _ (fun _ _ => rfl) hp n

/-- The spectral sequence `(E_r, d_r)_{r ≥ 0}` of a filtered complex ([Stacks, Tag 012M]). -/
noncomputable abbrev filteredSpectralSequence (M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :
    CohomologicalSpectralSequence A 0 :=
  spectralSequence M.X (filtrationSubobject M) (filtrationSubobject_antitone M)

/-- If `g ≫ f` factors through the monomorphism `g'`, then the image under `f` of the subobject
`Subobject.mk g` is contained in `Subobject.mk g'`. -/
lemma exists_mk_le_mk {X Y S S' : A} (f : X ⟶ Y) (g : S ⟶ X) [Mono g] (g' : S' ⟶ Y) [Mono g']
    (t : S ⟶ S') (h : t ≫ g' = g ≫ f) :
    («exists» f).obj (Subobject.mk g) ≤ Subobject.mk g' :=
  exists_le_of_comm f ((Subobject.underlyingIso g).hom ≫ t ≫ (Subobject.underlyingIso g').inv)
    (by rw [← Subobject.underlyingIso_hom_comp_eq_mk g', ← Subobject.underlyingIso_hom_comp_eq_mk g,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, h, Category.assoc])

/-- A morphism `φ : M ⟶ N` of filtered complexes carries each `F^p M^n` into `F^p N^n`. -/
lemma exists_filtrationSubobject_le {M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (φ : M ⟶ N)
    (p n : ℤ) :
    («exists» (φ.hom.f n)).obj (filtrationSubobject M p n) ≤ filtrationSubobject N p n :=
  exists_mk_le_mk _ _ _ ((φ.natTrans.app (op p)).f n)
    (HomologicalComplex.congr_hom (φ.comm (op p)) n)

/-- **[Stacks, Tag 012O] for filtered complexes.** The morphism of spectral sequences induced by
a morphism of filtered complexes. -/
noncomputable abbrev filteredSpectralSequenceMap {M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (φ : M ⟶ N) : filteredSpectralSequence M ⟶ filteredSpectralSequence N :=
  spectralSequenceMap φ.hom (exists_filtrationSubobject_le φ) _ _

/-- The morphism of spectral sequences induced by the identity of a filtered complex is the
identity. -/
lemma filteredSpectralSequenceMap_id (M : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ) :
    filteredSpectralSequenceMap (𝟙 M) = 𝟙 _ :=
  spectralSequenceMap_id _

/-- The morphism of spectral sequences induced by a composite of morphisms of filtered complexes
is the composite of the induced morphisms. -/
lemma filteredSpectralSequenceMap_comp {M N P : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    filteredSpectralSequenceMap (φ ≫ ψ) =
      filteredSpectralSequenceMap φ ≫ filteredSpectralSequenceMap ψ :=
  spectralSequenceMap_comp _ _ _ _ _ _ _ _

/-- Two morphisms of filtered complexes are *filtered homotopic* if they are homotopic through a
homotopy `h` each of whose components `h^{i,j}` carries `F^p K^i` into `F^p L^j`. -/
def FilteredHomotopic {M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} (φ ψ : M ⟶ N) : Prop :=
  ∃ h : Homotopy φ.hom ψ.hom, ∀ i j p : ℤ,
    ∃ hp : (M.filtration.obj (op p)).X i ⟶ (N.filtration.obj (op p)).X j,
      hp ≫ (N.filtration.ι.app (op p)).f j = (M.filtration.ι.app (op p)).f i ≫ h.hom i j

/-- **Homotopy invariance.** Filtered homotopic morphisms of filtered complexes induce the same
maps on the pages `E_r`, `r ≥ 1`. -/
@[ega "0 11.2.3" "special case"]
lemma filteredSpectralSequenceMap_hom_eq_of_filteredHomotopic
    {M N : FilteredObject (CochainComplex A ℤ) ℤᵒᵖ} {φ ψ : M ⟶ N} (h : FilteredHomotopic φ ψ)
    {r : ℤ} (hr : 1 ≤ r) :
    (filteredSpectralSequenceMap φ).hom r (by omega) =
      (filteredSpectralSequenceMap ψ).hom r (by omega) := by
  obtain ⟨h, hh⟩ := h
  exact spectralSequenceMap_hom_eq_of_homotopy _ _ _ h (fun p i j =>
    exists_mk_le_mk _ _ _ (hh i j p).choose (hh i j p).choose_spec) _ hr

end FilteredMaps

end CochainComplex

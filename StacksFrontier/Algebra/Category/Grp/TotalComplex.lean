module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.GroupTheory.FreeAbelianGroup
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksFrontier.Algebra.Homology.AbelianGroupComplexResolutions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolutions of complexes of abelian groups by double complexes

Stacks, Homological Algebra, Section 12.26: for a complex of abelian groups `M^•`, an exact
resolution `0 → M^• → A_0^• → A_1^• → …` induces a quasi-isomorphism `M^• → Tot(A^{•,•})` (0E1Q); a
good resolution gives a quasi-isomorphism from the total complex to `M^•` (09IZ); and a left
resolution `… → A_1^• → A_0^• → M^• → 0` induces a quasi-isomorphism `Tot_π(A^{•,•}) → M^•` (0E1R).
-/

@[expose] public section

section

/-!
## Coordinates on the total complex of a double complex of abelian groups

The total complex is an abstract coproduct. Its map to the direct sum of a diagonal supplies
finite support, and the projections onto the terms of a diagonal let the proofs below argue
term by term without choosing an implementation of that coproduct.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

local notation "𝕀" => ComplexShape.up ℤ

/-- The `n`-th diagonal `{(p, q) | p + q = n}`. -/
public abbrev diagonal (n : ℤ) := {pq : ℤ × ℤ // pq.1 + pq.2 = n}

/-- The coordinates of a cochain of a total complex: the direct sum, over the diagonal, of the
constituent objects of the bicomplex. -/
noncomputable def totalCoordinates
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀] (n : ℤ) :
    (A.total 𝕀).X n ⟶ AddCommGrpCat.of
      (DirectSum (diagonal n) (fun i => (A.X i.1.1).X i.1.2)) :=
  A.totalDesc (fun p q hpq => AddCommGrpCat.ofHom
    (DirectSum.of (fun i : diagonal n => (A.X i.1.1).X i.1.2) ⟨(p, q), hpq⟩))

/-- Assembling a family of coordinates on the diagonal back into a cochain of the total
complex. -/
noncomputable def totalSumDiag
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀] (n : ℤ) :
    AddCommGrpCat.of (DirectSum (diagonal n) (fun i => (A.X i.1.1).X i.1.2)) ⟶
      (A.total 𝕀).X n :=
  AddCommGrpCat.ofHom (DirectSum.toAddMonoid (fun i : diagonal n =>
    (A.ιTotal 𝕀 i.1.1 i.1.2 n i.2).hom))

/-- Assembling a single coordinate is the inclusion of the corresponding summand. -/
lemma totalSumDiag_of
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀] (n : ℤ) (i : diagonal n)
    (x : (A.X i.1.1).X i.1.2) :
    totalSumDiag A n (DirectSum.of (fun i : diagonal n => (A.X i.1.1).X i.1.2) i x) =
      A.ιTotal 𝕀 i.1.1 i.1.2 n i.2 x :=
  DirectSum.toAddMonoid_of _ _ _

/-- A cochain of a total complex is the sum of its coordinates. -/
lemma coordinates_sum
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀] (n : ℤ) :
    totalCoordinates A n ≫ totalSumDiag A n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext 𝕀
  intro p q hpq
  rw [← Category.assoc, totalCoordinates, HomologicalComplex₂.ι_totalDesc]
  ext x
  rw [ConcreteCategory.comp_apply, AddCommGrpCat.ofHom_apply, totalSumDiag_of, Category.comp_id]

/-- The projection of a total complex onto the constituent object in one bidegree. -/
noncomputable def totalProjectionDiag
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q n : ℤ) (hpq : p + q = n) : (A.total 𝕀).X n ⟶ (A.X p).X q :=
  totalCoordinates A n ≫ AddCommGrpCat.ofHom
    (DFinsupp.evalAddMonoidHom (β := fun i : diagonal n => ↥((A.X i.1.1).X i.1.2)) ⟨(p,q), hpq⟩)

/-- The projection onto a bidegree reads off the corresponding coordinate. -/
lemma totalProjectionDiag_apply
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q n : ℤ) (hpq : p + q = n) (x : (A.total 𝕀).X n) :
    totalProjectionDiag A p q n hpq x = totalCoordinates A n x ⟨(p, q), hpq⟩ :=
  rfl

/-- The projection is a retraction of the inclusion of the summand it names. -/
@[reassoc (attr := simp)]
lemma inclusion_projection_self
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q n : ℤ) (hpq : p + q = n) :
    A.ιTotal 𝕀 p q n hpq ≫ totalProjectionDiag A p q n hpq = 𝟙 _ := by
  rw [totalProjectionDiag, ← Category.assoc, totalCoordinates, HomologicalComplex₂.ι_totalDesc]
  ext x
  exact DirectSum.of_eq_same _ _

/-- The projection kills every summand in a different column. -/
@[reassoc (attr := simp)]
lemma inclusion_projection_ne
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q r s n : ℤ) (hpq : p + q = n) (hrs : r + s = n) (hpr : p ≠ r) :
    A.ιTotal 𝕀 p q n hpq ≫ totalProjectionDiag A r s n hrs = 0 := by
  rw [totalProjectionDiag, ← Category.assoc, totalCoordinates, HomologicalComplex₂.ι_totalDesc]
  ext x
  apply DirectSum.of_eq_of_ne
  intro he
  exact hpr (congrArg (fun i : diagonal n => i.1.1) he).symm

/-- Two cochains of a total complex with the same coordinates agree. -/
lemma total_ext_elements
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀] (n : ℤ)
    (x y : (A.total 𝕀).X n)
    (h : ∀ p q (hpq : p + q = n), totalProjectionDiag A p q n hpq x =
      totalProjectionDiag A p q n hpq y) : x = y := by
  have he : totalCoordinates A n x = totalCoordinates A n y :=
    DFinsupp.ext fun ⟨⟨p, q⟩, hpq⟩ => h p q hpq
  simpa only [← ConcreteCategory.comp_apply, coordinates_sum, ConcreteCategory.id_apply] using
    congrArg (totalSumDiag A n) he

/-- The differential of a total complex on one summand: the differential of the bicomplex in
the first degree, plus the one in the second degree with the sign of the first degree. -/
lemma inclusion_differential
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q p' q' n n' : ℤ) (hpq : p + q = n)
    (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n') :
    A.ιTotal 𝕀 p q n hpq ≫ (A.total 𝕀).d n n' =
      (A.d p p').f q ≫ A.ιTotal 𝕀 p' q n' (by simp only [ComplexShape.π_def]; omega) +
      p.negOnePow • ((A.X p).d q q' ≫
        A.ιTotal 𝕀 p q' n' (by simp only [ComplexShape.π_def]; omega)) := by
  subst p' q' n'
  exact HomologicalComplex₂.ιTotal_d_up_ℤ A p q n hpq

/-- One coordinate of the differential of a cochain of a total complex, as a morphism: it is
determined by the two coordinates of the cochain adjacent to the given bidegree. -/
lemma differential_projection
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q p₀ q₀ n : ℤ) (hp : p₀ + 1 = p) (hq : q₀ + 1 = q)
    (hpq : p + q = n + 1) :
    (A.total 𝕀).d n (n + 1) ≫ totalProjectionDiag A p q (n + 1) hpq =
      totalProjectionDiag A p₀ q n (by omega) ≫ (A.d p₀ p).f q +
      p.negOnePow • (totalProjectionDiag A p q₀ n (by omega) ≫ (A.X p).d q₀ q) := by
  subst hp hq
  apply HomologicalComplex₂.total.hom_ext 𝕀
  intro r s hrs
  simp only [ComplexShape.π_def] at hrs
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ A r s n hrs, Preadditive.add_comp,
    Linear.units_smul_comp, Preadditive.comp_add, Linear.comp_units_smul]
  simp only [Category.assoc]
  simp only [← Category.assoc (A.ιTotal 𝕀 r s n hrs)]
  by_cases hr : r = p₀ + 1
  · subst r
    have hs : s = q₀ := by omega
    subst s
    simp [inclusion_projection_self, inclusion_projection_ne]
  · by_cases hr' : r = p₀
    · subst r
      have hs : s = q₀ + 1 := by omega
      subst s
      simp [inclusion_projection_self, inclusion_projection_ne, hr]
    · simp [inclusion_projection_ne, hr, hr', show r + 1 ≠ p₀ + 1 by omega]

private lemma total_has_lower_bound
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (n : ℤ) (x : (A.total 𝕀).X n) :
    ∃ k : ℕ, ∀ p q (hpq : p + q = n), p < -(k : ℤ) →
      totalProjectionDiag A p q n hpq x = 0 := by
  classical
  have hb : ∀ s : Finset (diagonal n), ∃ a : ℤ, ∀ i ∈ s, a ≤ i.1.1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨min i.1.1 a, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ha j hj)
  obtain ⟨a, ha⟩ := hb (totalCoordinates A n x).support
  obtain ⟨k, hk⟩ := exists_nat_ge (-a)
  refine ⟨k, fun p q hpq hp => ?_⟩
  rw [totalProjectionDiag_apply]
  apply DFinsupp.notMem_support_iff.mp
  intro hi
  have := ha ⟨(p, q), hpq⟩ hi
  dsimp at this
  omega

/-- The projection recovers the summand it names, on elements. -/
lemma projection_inclusion_self
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q n : ℤ) (hpq : p + q = n) (x : (A.X p).X q) :
    totalProjectionDiag A p q n hpq (A.ιTotal 𝕀 p q n hpq x) = x := by
  rw [← ConcreteCategory.comp_apply, inclusion_projection_self, ConcreteCategory.id_apply]

/-- The projection kills a summand in a different column, on elements. -/
lemma projection_inclusion_ne
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q r s n : ℤ) (hpq : p + q = n) (hrs : r + s = n) (hpr : p ≠ r)
    (x : (A.X p).X q) :
    totalProjectionDiag A r s n hrs (A.ιTotal 𝕀 p q n hpq x) = 0 := by
  rw [← ConcreteCategory.comp_apply, inclusion_projection_ne A p q r s n hpq hrs hpr]
  rfl

/-- The differential of a total complex on one summand, on elements. -/
lemma differential_inclusion_apply
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q p' q' n n' : ℤ) (hpq : p + q = n)
    (hp : p + 1 = p') (hq : q + 1 = q') (hn : n + 1 = n') (x : (A.X p).X q) :
    (A.total 𝕀).d n n' (A.ιTotal 𝕀 p q n hpq x) =
      A.ιTotal 𝕀 p' q n' (by simp only [ComplexShape.π_def]; omega) ((A.d p p').f q x) +
      p.negOnePow • A.ιTotal 𝕀 p q' n' (by simp only [ComplexShape.π_def]; omega)
        ((A.X p).d q q' x) := by
  have he := ConcreteCategory.congr_hom (inclusion_differential A p q p' q' n n' hpq hp hq hn) x
  simpa [Units.smul_def] using he

private lemma projection_differential_apply
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q p₀ q₀ n : ℤ) (hp : p₀ + 1 = p) (hq : q₀ + 1 = q)
    (hpq : p + q = n + 1) (x : (A.total 𝕀).X n) :
    totalProjectionDiag A p q (n + 1) hpq ((A.total 𝕀).d n (n + 1) x) =
      (A.d p₀ p).f q (totalProjectionDiag A p₀ q n (by omega) x) +
      p.negOnePow • (A.X p).d q₀ q (totalProjectionDiag A p q₀ n (by omega) x) := by
  have he := ConcreteCategory.congr_hom (differential_projection A p q p₀ q₀ n hp hq hpq) x
  simpa [Units.smul_def] using he



/-- A cochain of a total complex occupies only finitely many columns, so its coordinates vanish
in all large enough first degrees. -/
lemma total_has_upper_bound
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀)
    [A.HasTotal 𝕀] (n : ℤ) (x : (A.total 𝕀).X n) :
    ∃ k : ℕ, ∀ p q (hpq : p + q = n), (k : ℤ) < p → totalProjectionDiag A p q n hpq x = 0 := by
  classical
  refine ⟨(totalCoordinates A n x).support.sup (fun i => i.1.1.toNat), fun p q hpq hp => ?_⟩
  rw [totalProjectionDiag_apply]
  by_contra hn
  have hm := Finset.le_sup (f := fun i : diagonal n => i.1.1.toNat)
    (DFinsupp.mem_support_iff.mpr hn)
  have he : p ≤ (p.toNat : ℤ) := Int.self_le_toNat p
  dsimp at hm
  omega


end

section

/-!
## Stacks tag 0E1Q

Let `M^•` be a cochain complex of abelian groups and let
`0 → M^• → A_0^• → A_1^• → A_2^• → …` be an exact complex of complexes of
abelian groups. Then the induced map `M^• → Tot(A^{•,•})` is a
quasi-isomorphism.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex

local notation "𝕀" => ComplexShape.up ℤ

/-- For a double complex `A` indexed on `ℤ × ℤ`, the augmented column at
cohomological degree `q` and horizontal position `p`. -/
noncomputable def augmentedColumn
    (M : CochainComplex AddCommGrpCat ℤ)
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀)
    (f : M ⟶ A.X 0) (q : ℤ) (p : ℤ)
    (h : f.f q ≫ (A.d 0 1).f q = 0) : ShortComplex AddCommGrpCat :=
  if p = 0 then
    ShortComplex.mk (f.f q) ((A.d 0 1).f q) h
  else
    ShortComplex.mk ((A.d (p-1) p).f q) ((A.d p (p+1)).f q) (by
      simp [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d])

/-- `g : M ⟶ A.total 𝕀` is induced by `f : M ⟶ A.X 0` via the canonical
inclusion of the `0`-th column. -/
abbrev InducedFromColumnZero
    {M : CochainComplex AddCommGrpCat ℤ}
    {A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀} [A.HasTotal 𝕀]
    (f : M ⟶ A.X 0) (g : M ⟶ A.total 𝕀) : Prop :=
  ∀ q : ℤ, g.f q = f.f q ≫ A.ιTotal 𝕀 0 q q (zero_add q)

/-- The "right resolution" exactness hypothesis. -/
abbrev IsRightResolution
    (M : CochainComplex AddCommGrpCat ℤ)
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀)
    (f : M ⟶ A.X 0) : Prop :=
  (∀ q : ℤ, Mono (f.f q)) ∧
  ∃ h : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0,
    ∀ q : ℤ, ∀ p : ℤ, 0 ≤ p → (augmentedColumn M A f q p (h q)).Exact

/-- A morphism with acyclic mapping cone is a quasi-isomorphism. -/
@[sga "6 I 1.4.2" "(i) ⇒ (ii), special case"]
lemma quasiIso_of_mappingCone_acyclic
    {F G : CochainComplex AddCommGrpCat ℤ} (φ : F ⟶ G)
    (h : ∀ n : ℤ, (CochainComplex.mappingCone φ).ExactAt n) :
    QuasiIso φ := by
  rw [← mem_quasiIso_iff, ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  refine ((HomotopyCategory.subcategoryAcyclic AddCommGrpCat).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished φ)).2 ?_
  simp only [Functor.mapTriangle_obj, CochainComplex.mappingCone.triangle_obj₃,
    Pretriangulated.Triangle.mk_obj₃]
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_exactAt _).2 h

/-- Elementwise content of augmented-column exactness at `p = 0`. -/
lemma column_zero_exists_preimage_M
    (M : CochainComplex AddCommGrpCat ℤ)
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀)
    (f : M ⟶ A.X 0) (hExact : IsRightResolution M A f) (q : ℤ)
    (x : (A.X 0).X q)
    (hx : (ConcreteCategory.hom ((A.d 0 1).f q)) x = 0) :
    ∃ u : M.X q, (ConcreteCategory.hom (f.f q)) u = x := by
  obtain ⟨_, h, he⟩ := hExact
  have e := he q 0 (le_refl 0)
  simp only [augmentedColumn] at e
  exact (ShortComplex.ab_exact_iff _).1 e x hx

/-- Elementwise content of augmented-column exactness at `p ≥ 1`. -/
lemma column_pos_exists_preimage_prev
    (M : CochainComplex AddCommGrpCat ℤ)
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀)
    (f : M ⟶ A.X 0) (hExact : IsRightResolution M A f) (q p : ℤ) (hp : 1 ≤ p)
    (x : (A.X p).X q)
    (hx : (ConcreteCategory.hom ((A.d p (p + 1)).f q)) x = 0) :
    ∃ y : (A.X (p-1)).X q,
        (ConcreteCategory.hom ((A.d (p-1) p).f q)) y = x := by
  obtain ⟨_, h, he⟩ := hExact
  have e := he q p (by omega)
  simp only [augmentedColumn, ite_eq_right (show p ≠ 0 by omega)] at e
  exact (ShortComplex.ab_exact_iff _).1 e x hx

/-- The inclusion of a zero column into the totalization is zero. -/
private lemma ιTotal_eq_zero_of_isZero
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (p q n : ℤ) (hpq : p + q = n) (hp : IsZero (A.X p)) :
    A.ιTotal 𝕀 p q n hpq = 0 :=
  ((eval AddCommGrpCat 𝕀 q).map_isZero hp).eq_of_src _ _

/-- The inclusion from negative outer index into the totalization is zero. -/
lemma ιTotal_eq_zero_of_neg
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (hA_vanish : ∀ p : ℤ, p < 0 → IsZero (A.X p))
    (p q n : ℤ) (hpq : p + q = n) (hp : p < 0) :
    A.ιTotal 𝕀 p q n hpq = 0 :=
  ιTotal_eq_zero_of_isZero A p q n hpq (hA_vanish p hp)

section

noncomputable section

variable (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]

/-- An upper bound for the horizontal support of a total-complex element. -/
private abbrev bounded (n k : ℤ) (z : (A.total 𝕀).X n) : Prop :=
  ∀ p q (h : p + q = n), k < p → totalProjectionDiag A p q n h z = 0

variable (M : CochainComplex AddCommGrpCat ℤ) (f : M ⟶ A.X 0)
    (g : M ⟶ A.total 𝕀) (hg : InducedFromColumnZero f g)

include hg in
private lemma g_proj_zero (p q n : ℤ) (h : p + q = n) (hp : p ≠ 0) :
    g.f n ≫ totalProjectionDiag A p q n h = 0 := by
  rw [hg n, Category.assoc, inclusion_projection_ne A 0 n p q n (by omega) h (Ne.symm hp)]
  simp

include hg in
private lemma top_closed (n p q : ℤ) (h : p + q = n) (hp : 0 ≤ p)
    (z : (A.total 𝕀).X n) (u : M.X (n + 1))
    (hz : (A.total 𝕀).d n (n + 1) z = g.f (n + 1) u) (hb : bounded A n p z) :
    (A.d p (p + 1)).f q (totalProjectionDiag A p q n h z) = 0 := by
  have e := congrArg (totalProjectionDiag A (p + 1) q (n + 1) (by omega)) hz
  rw [← ConcreteCategory.comp_apply,
    differential_projection A (p + 1) q p (q - 1) n rfl (by omega) (by omega),
    ← ConcreteCategory.comp_apply,
    g_proj_zero A M f g hg (p + 1) q (n + 1) (by omega) (by omega)] at e
  simpa [Units.smul_def, AddCommGrpCat.hom_comp, ConcreteCategory.comp_apply,
    hb (p + 1) (q - 1) (by omega) (by omega)] using e

private lemma proj_eq_zero_of_isZero (p q n : ℤ) (h : p + q = n) (hp : IsZero (A.X p))
    (z : (A.total 𝕀).X n) : totalProjectionDiag A p q n h z = 0 := by
  have he : totalProjectionDiag A p q n h = 0 :=
    ((eval AddCommGrpCat 𝕀 q).map_isZero hp).eq_of_tgt _ _
  rw [he]
  rfl
include hg in
/-- Remove the highest column by a boundary and induct on its index. -/
private lemma boundary_mod_column (hA : ∀ p : ℤ, p < 0 → IsZero (A.X p))
    (hExact : IsRightResolution M A f) (n : ℤ) (k : ℕ)
    (z : (A.total 𝕀).X n) (u : M.X (n + 1))
    (hz : (A.total 𝕀).d n (n + 1) z = g.f (n + 1) u) (hb : bounded A n k z) :
    ∃ (v : M.X n) (t : (A.total 𝕀).X (n - 1)), z = g.f n v + (A.total 𝕀).d (n - 1) n t := by
  induction k generalizing z with
  | zero =>
    have hc := top_closed A M f g hg n 0 n (by omega) (by omega) z u hz hb
    obtain ⟨v, hv⟩ := column_zero_exists_preimage_M M A f hExact n _ hc
    refine ⟨v, 0, ?_⟩
    simp only [map_zero, add_zero]
    apply total_ext_elements A n
    intro p q hpq
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by omega
      subst q
      rw [hg n, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        inclusion_projection_self]
      simpa using hv.symm
    · rw [← ConcreteCategory.comp_apply, g_proj_zero A M f g hg p q n hpq hp]
      simp only [AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
      by_cases hn : p < 0
      · exact proj_eq_zero_of_isZero A p q n hpq (hA p hn) z
      · exact hb p q hpq (by omega)
  | succ k ih =>
    let p : ℤ := (k : ℤ) + 1
    let q : ℤ := n - p
    have hpq : p + q = n := by dsimp [q]; omega
    have hc := top_closed A M f g hg n p q hpq (by dsimp [p]; omega) z u hz hb
    obtain ⟨y, hy⟩ := column_pos_exists_preimage_prev M A f hExact q p
      (by dsimp [p]; omega) _ hc
    let t₀ : (A.total 𝕀).X (n - 1) := A.ιTotal 𝕀 (p - 1) q (n - 1) (by dsimp; omega) y
    let z' := z - (A.total 𝕀).d (n - 1) n t₀
    have hd : (A.total 𝕀).d n (n + 1) z' = g.f (n + 1) u := by
      dsimp [z']
      rw [map_sub, ← ConcreteCategory.comp_apply, d_comp_d]
      simpa using hz
    have hb' : bounded A n k z' := by
      intro a b hab ha
      dsimp [z', t₀]
      rw [map_sub, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Category.assoc,
        inclusion_differential A (p - 1) q p (q + 1) (n - 1) n (by omega) (by omega) rfl (by omega)]
      by_cases hap : a = p
      · subst a
        have hq : b = q := by omega
        subst b
        have hm : p - 1 ≠ p := by omega
        simp [Preadditive.add_comp, Category.assoc, inclusion_projection_ne, hm, hy]
      · have hkp : p < a := by dsimp [p] at *; omega
        rw [hb a b hab hkp]
        simp [Preadditive.add_comp, Category.assoc, inclusion_projection_ne,
          show p ≠ a by omega, show p - 1 ≠ a by omega]
    obtain ⟨v, t, ht⟩ := ih z' hd hb'
    refine ⟨v, t + t₀, ?_⟩
    dsimp [z'] at ht
    rw [map_add]
    exact (sub_eq_iff_eq_add.mp ht).trans (by abel)

include hg in
private lemma g_injective (hExact : IsRightResolution M A f) (n : ℤ) :
    Function.Injective (g.f n) := by
  intro x y hxy
  refine ((AddCommGrpCat.mono_iff_injective (f.f n)).mp (hExact.1 n)).eq_iff.mp ?_
  have e := congrArg (totalProjectionDiag A 0 n n (zero_add n)) hxy
  have he : g.f n ≫ totalProjectionDiag A 0 n n (zero_add n) = f.f n := by
    rw [hg n, Category.assoc, inclusion_projection_self, Category.comp_id]
  simpa only [← ConcreteCategory.comp_apply, he] using e

open CochainComplex HomComplex

private lemma cone_ext {F G : CochainComplex AddCommGrpCat ℤ} (φ : F ⟶ G)
    (n : ℤ) (x y : (mappingCone φ).X n)
    (h₁ : (mappingCone.fst φ).1.v n (n + 1) rfl x =
      (mappingCone.fst φ).1.v n (n + 1) rfl y)
    (h₂ : (mappingCone.snd φ).v n n (add_zero n) x =
      (mappingCone.snd φ).v n n (add_zero n) y) : x = y := by
  have e₁ := ConcreteCategory.congr_hom (mappingCone.id_X φ n (n + 1) rfl) x
  have e₂ := ConcreteCategory.congr_hom (mappingCone.id_X φ n (n + 1) rfl) y
  simp only [AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at e₁ e₂
  rw [← e₁, ← e₂, h₁, h₂]

/-- Elementwise exactness of a cochain complex of abelian groups at `n`: every cycle is a
boundary. The refinement is the free abelian group on the source. -/
private lemma exactAt_of_ab (K : CochainComplex AddCommGrpCat ℤ) (n : ℤ)
    (h : ∀ x : K.X n, K.d n (n + 1) x = 0 → ∃ y : K.X (n - 1), K.d (n - 1) n y = x) :
    K.ExactAt n := by
  rw [exactAt_iff_exact_up_to_refinements K (n - 1) n (n + 1) (by simp) (by simp)]
  intro B x₂ hx₂
  have hy (b : B) : ∃ y : K.X (n - 1), K.d (n - 1) n y = x₂ b :=
    h _ (by simpa using ConcreteCategory.congr_hom hx₂ b)
  refine ⟨AddCommGrpCat.of (FreeAbelianGroup B), AddCommGrpCat.ofHom (FreeAbelianGroup.lift id),
    ?_, AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun b => (hy b).choose), ?_⟩
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro b
    exact ⟨FreeAbelianGroup.of b, by simp⟩
  · ext1
    apply FreeAbelianGroup.lift_ext
    intro b
    simp [(hy b).choose_spec]

/-- Heart of the proof: the mapping cone of `g` is exact at every degree. -/
lemma mappingCone_g_exactAt
    (M : CochainComplex AddCommGrpCat ℤ)
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (f : M ⟶ A.X 0)
    (hA_vanish : ∀ p : ℤ, p < 0 → IsZero (A.X p))
    (hExact : IsRightResolution M A f)
    (g : M ⟶ A.total 𝕀) (hg : InducedFromColumnZero f g)
    (n : ℤ) :
    (CochainComplex.mappingCone g).ExactAt n := by
  refine exactAt_of_ab _ n fun x hx => ?_
  let u := (mappingCone.fst g).1.v n (n + 1) rfl x
  let z := (mappingCone.snd g).v n n (add_zero n) x
  have hz : (A.total 𝕀).d n (n + 1) z = g.f (n + 1) (-u) := by
    have e := congrArg ((mappingCone.snd g).v (n + 1) (n + 1) (add_zero _)) hx
    rw [← ConcreteCategory.comp_apply, mappingCone.d_snd_v g n (n + 1) rfl] at e
    simp only [map_zero, AddCommGrpCat.hom_add_apply, ConcreteCategory.comp_apply] at e
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right e
  obtain ⟨k, hk⟩ := total_has_upper_bound A n z
  obtain ⟨v, t, ht⟩ := boundary_mod_column A M f g hg hA_vanish hExact n k z (-u) hz hk
  have hv : -(M.d n (n + 1) v) = u := by
    refine (g_injective A M f g hg hExact (n + 1)).eq_iff.mp ?_
    have e := congrArg ((A.total 𝕀).d n (n + 1)) ht
    rw [hz, map_add] at e
    simp only [← ConcreteCategory.comp_apply, d_comp_d] at e
    rw [g.comm n (n + 1)] at e
    simpa using congrArg Neg.neg e.symm
  refine ⟨(mappingCone.inl g).v n (n - 1) (by omega) v + (mappingCone.inr g).f (n - 1) t, ?_⟩
  apply cone_ext g n
  · rw [← ConcreteCategory.comp_apply, mappingCone.d_fst_v' g n (n + 1) rfl]
    simp [← ConcreteCategory.comp_apply,
      mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v, hv, u]
  · rw [← ConcreteCategory.comp_apply, mappingCone.d_snd_v' g n]
    simpa [ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v,
      mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v] using ht.symm

end

end

/-- Let `M^•` be a cochain complex of abelian groups and let
`0 → M^• → A_0^• → A_1^• → …` be an exact complex of complexes of abelian
groups (encoded as a half-plane double complex with augmentation `f`). Then
the induced map `g : M^• → Tot(A^{•,•})` is a quasi-isomorphism. -/
@[stacks 0E1Q]
theorem quasiIso_of_isRightResolution
    (M : CochainComplex AddCommGrpCat ℤ)
    (A : HomologicalComplex₂ AddCommGrpCat 𝕀 𝕀) [A.HasTotal 𝕀]
    (f : M ⟶ A.X 0)
    (hA_vanish : ∀ p : ℤ, p < 0 → IsZero (A.X p))
    (hExact : IsRightResolution M A f)
    (g : M ⟶ A.total 𝕀) (hg : InducedFromColumnZero f g) :
    QuasiIso g :=
  quasiIso_of_mappingCone_acyclic g
    (mappingCone_g_exactAt M A f hA_vanish hExact g hg)

end

section

/-!
## Stacks tag 09IZ

A "good resolution" of a complex of abelian groups gives a quasi-isomorphism
from the total complex of the resolution to the original complex.
-/

open CategoryTheory

/-- Shorthand: the cochain complex shape on `ℤ`. -/
abbrev shZ : ComplexShape ℤ := ComplexShape.up ℤ

/-- The underlying function on elements of a morphism in `Ab`. -/
noncomputable abbrev fnOf {X Y : Ab} (φ : X ⟶ Y) : X → Y := φ.hom

/-- A "good resolution" of `M` by `A` via augmentation `f`. The columns of `A`
vanish for `p > 0`, the augmented complex is row-wise exact, and the
vertical-kernel rows are also exact. -/
structure GoodResolution
    (M : HomologicalComplex Ab shZ)
    (A : HomologicalComplex₂ Ab shZ shZ)
    (f : A.X 0 ⟶ M) : Prop where
  vanishing_pos :
    ∀ p : ℤ, 0 < p → Limits.IsZero (A.X p)
  aug_comp_zero :
    A.d (-1) 0 ≫ f = 0
  /-- In every degree `q`, the augmentation `f` is surjective. -/
  aug_surj :
    ∀ q : ℤ, Function.Surjective (fnOf (f.f q))
  row_exact_at_zero :
    ∀ (q : ℤ) (x : (A.X 0).X q), fnOf (f.f q) x = 0 →
      ∃ y : (A.X (-1)).X q, fnOf ((A.d (-1) 0).f q) y = x
  row_exact_neg :
    ∀ (p q : ℤ), p < 0 →
      ∀ (x : (A.X p).X q), fnOf ((A.d p (p + 1)).f q) x = 0 →
        ∃ y : (A.X (p - 1)).X q, fnOf ((A.d (p - 1) p).f q) y = x
  ker_aug_surj :
    ∀ (q : ℤ) (m : M.X q), fnOf (M.d q (q + 1)) m = 0 →
      ∃ x : (A.X 0).X q,
        fnOf ((A.X 0).d q (q + 1)) x = 0 ∧ fnOf (f.f q) x = m
  ker_row_exact_at_zero :
    ∀ (q : ℤ) (x : (A.X 0).X q),
      fnOf ((A.X 0).d q (q + 1)) x = 0 → fnOf (f.f q) x = 0 →
        ∃ y : (A.X (-1)).X q,
          fnOf ((A.X (-1)).d q (q + 1)) y = 0 ∧
            fnOf ((A.d (-1) 0).f q) y = x
  ker_row_exact_neg :
    ∀ (p q : ℤ), p < 0 →
      ∀ (x : (A.X p).X q),
        fnOf ((A.X p).d q (q + 1)) x = 0 →
        fnOf ((A.d p (p + 1)).f q) x = 0 →
          ∃ y : (A.X (p - 1)).X q,
            fnOf ((A.X (p - 1)).d q (q + 1)) y = 0 ∧
              fnOf ((A.d (p - 1) p).f q) y = x

/-- The canonical per-degree component of the induced map `A.total shZ ⟶ M`. -/
noncomputable def canonicalMapF
    (M : HomologicalComplex Ab shZ)
    (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ]
    (f : A.X 0 ⟶ M) (n : ℤ) :
    (A.total shZ).X n ⟶ M.X n :=
  A.totalDesc (fun p q hpq => by
    by_cases hp : p = 0
    · subst hp
      have hqn : q = n := by simpa using hpq
      exact f.f q ≫ (M.XIsoOfEq hqn).hom
    · exact 0)

/-- Construction of the canonical chain map from a good resolution. -/
lemma canonical_chain_map_exists
    (M : HomologicalComplex Ab shZ)
    (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ]
    (f : A.X 0 ⟶ M)
    (h : GoodResolution M A f) :
    ∃ φ : A.total shZ ⟶ M, ∀ n : ℤ, φ.f n = canonicalMapF M A f n := by
  refine ⟨{ f := canonicalMapF M A f, comm' := ?_ }, fun _ => rfl⟩
  intro n n' hn
  obtain rfl : n + 1 = n' := hn
  apply HomologicalComplex₂.total.hom_ext shZ
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  rw [← Category.assoc, ← Category.assoc, HomologicalComplex₂.ιTotal_d_up_ℤ A p q n hpq,
    Preadditive.add_comp, Linear.units_smul_comp]
  simp only [Category.assoc, canonicalMapF, HomologicalComplex₂.ι_totalDesc]
  by_cases hp : p = 0
  · subst p
    have hq : q = n := by omega
    subst q
    simp
  · by_cases hp' : p + 1 = 0
    · have he : p = -1 := by omega
      subst p
      have hq : q = n + 1 := by omega
      subst q
      have hz := congrArg (fun g : A.X (-1) ⟶ M => g.f (n + 1)) h.aug_comp_zero
      simpa using hz.symm
    · simp [hp, hp']

private lemma canonical_projection
    (M : HomologicalComplex Ab shZ) (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ] (f : A.X 0 ⟶ M) (n : ℤ) :
    canonicalMapF M A f n = totalProjectionDiag A 0 n n (by omega) ≫ f.f n := by
  apply HomologicalComplex₂.total.hom_ext shZ
  intro p q hpq
  simp only [ComplexShape.π_def] at hpq
  rw [canonicalMapF, HomologicalComplex₂.ι_totalDesc, ← Category.assoc]
  by_cases hp : p = 0
  · subst p
    have hq : q = n := by omega
    subst q
    simp [inclusion_projection_self]
  · simp [hp, inclusion_projection_ne]

private lemma top_horizontal_cycle
    (A : HomologicalComplex₂ Ab shZ shZ) [A.HasTotal shZ]
    (n b q : ℤ) (hbq : b + q = n) (x : (A.total shZ).X n)
    (hx : (A.total shZ).d n (n + 1) x = 0)
    (hu : ∀ p s (hps : p + s = n), b < p → totalProjectionDiag A p s n hps x = 0) :
    (A.d b (b + 1)).f q (totalProjectionDiag A b q n hbq x) = 0 := by
  have he := projection_differential_apply A (b + 1) q b (q - 1) n rfl (by omega) (by omega) x
  rw [hx, map_zero, hu (b + 1) (q - 1) (by omega) (by omega), map_zero,
    smul_zero, add_zero] at he
  simpa only [add_sub_cancel_right] using he.symm

private lemma bottom_vertical_cycle
    (A : HomologicalComplex₂ Ab shZ shZ) [A.HasTotal shZ]
    (n b q : ℤ) (hbq : b + q = n) (x : (A.total shZ).X n)
    (hx : (A.total shZ).d n (n + 1) x = 0)
    (hl : ∀ p s (hps : p + s = n), p < b → totalProjectionDiag A p s n hps x = 0) :
    (A.X b).d q (q + 1) (totalProjectionDiag A b q n hbq x) = 0 := by
  have he := projection_differential_apply A b (q + 1) (b - 1) q n (by omega) rfl (by omega) x
  rw [hx, map_zero, hl (b - 1) (q + 1) (by omega) (by omega), map_zero,
    zero_add] at he
  have hh : b.negOnePow • (A.X b).d q (q + 1) (totalProjectionDiag A b q n hbq x) = 0 := by
    simpa only [add_sub_cancel_right] using he.symm
  exact (smul_eq_zero_iff_eq b.negOnePow).mp hh

private lemma top_augmentation_zero
    (M : HomologicalComplex Ab shZ) (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ] (f : A.X 0 ⟶ M)
    (φ : A.total shZ ⟶ M) (hφ : ∀ n, φ.f n = canonicalMapF M A f n)
    (n : ℤ) (x : (A.total shZ).X n) (hx : φ.f n x = 0) :
    f.f n (totalProjectionDiag A 0 n n (by omega) x) = 0 := by
  simpa only [hφ, canonical_projection, ConcreteCategory.comp_apply] using hx

private lemma canonical_inclusion_zero
    (M : HomologicalComplex Ab shZ) (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ] (f : A.X 0 ⟶ M)
    (φ : A.total shZ ⟶ M) (hφ : ∀ n, φ.f n = canonicalMapF M A f n)
    (p q n : ℤ) (hpq : p + q = n) (hp : p ≠ 0) (x : (A.X p).X q) :
    φ.f n (A.ιTotal shZ p q n hpq x) = 0 := by
  rw [hφ, canonical_projection, ConcreteCategory.comp_apply,
    projection_inclusion_ne A p q 0 n n hpq (by omega) hp, map_zero]

/-- Subtracting a boundary from a cycle leaves a cycle. -/
private lemma d_sub_d_eq_zero {K : HomologicalComplex Ab shZ} {n : ℤ} {x : K.X n}
    (hx : K.d n (n + 1) x = 0) (t : K.X (n - 1)) : K.d n (n + 1) (x - K.d (n - 1) n t) = 0 := by
  rw [map_sub, hx, ← ConcreteCategory.comp_apply, HomologicalComplex.d_comp_d]
  simp

/-- A chain map applied to `x - d t`. -/
private lemma map_sub_d_eq_sub {K L : HomologicalComplex Ab shZ} (φ : K ⟶ L) {n : ℤ}
    (x : K.X n) (t : K.X (n - 1)) :
    φ.f n (x - K.d (n - 1) n t) = φ.f n x - L.d (n - 1) n (φ.f (n - 1) t) := by
  rw [map_sub, ← ConcreteCategory.comp_apply, ← φ.comm (n - 1) n, ConcreteCategory.comp_apply]

/-- A cycle in the augmentation kernel supported in `[b-k,b]`, with `b ≤ 0`,
is a boundary. Row exactness removes column `b`. When only one column remains,
exactness on vertical kernels gives a closed preimage, so removal introduces
no further component. -/
private lemma cycle_boundary_of_bounds
    (M : HomologicalComplex Ab shZ) (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ] (f : A.X 0 ⟶ M) (h : GoodResolution M A f)
    (φ : A.total shZ ⟶ M) (hφ : ∀ n, φ.f n = canonicalMapF M A f n) (k : ℕ) :
    ∀ (n b q : ℤ) (_hbq : b + q = n), b ≤ 0 → ∀ x : (A.total shZ).X n,
      (A.total shZ).d n (n + 1) x = 0 → φ.f n x = 0 →
      (∀ p s (hps : p + s = n), p < b - (k : ℤ) ∨ b < p →
        totalProjectionDiag A p s n hps x = 0) →
      ∃ y : (A.total shZ).X (n - 1), (A.total shZ).d (n - 1) n y = x := by
  induction k with
  | zero =>
    intro n b q hbq hb x hx hfx hs
    have hv := bottom_vertical_cycle A n b q hbq x hx
      (fun p s hps hp => hs p s hps (Or.inl (by simpa using hp)))
    have hy : ∃ y : (A.X (b - 1)).X q,
        (A.X (b - 1)).d q (q + 1) y = 0 ∧
          (A.d (b - 1) b).f q y = totalProjectionDiag A b q n hbq x := by
      by_cases hb0 : b = 0
      · subst b
        have hn : n = q := by omega
        cases hn
        exact h.ker_row_exact_at_zero n _ hv (top_augmentation_zero M A f φ hφ n x hfx)
      · exact h.ker_row_exact_neg b q (by omega) _ hv
          (top_horizontal_cycle A n b q hbq x hx
            (fun p s hps hp => hs p s hps (Or.inr hp)))
    obtain ⟨y, hyv, hy⟩ := hy
    refine ⟨A.ιTotal shZ (b - 1) q (n - 1) (by simp only [ComplexShape.π_def]; omega) y, ?_⟩
    rw [differential_inclusion_apply A (b - 1) q b (q + 1) (n - 1) n
      (by omega) (by omega) rfl (by omega), hyv, map_zero, smul_zero, add_zero, hy]
    apply total_ext_elements A n
    intro p s hps
    by_cases hp : p = b
    · subst p
      have hq : s = q := by omega
      subst s
      exact projection_inclusion_self A b q n hbq _
    · rw [projection_inclusion_ne A b q p s n hbq hps (Ne.symm hp),
        hs p s hps (by simp only [Nat.cast_zero, sub_zero]; omega)]
  | succ k ih =>
    intro n b q hbq hb x hx hfx hs
    have hy : ∃ y : (A.X (b - 1)).X q,
        (A.d (b - 1) b).f q y = totalProjectionDiag A b q n hbq x := by
      by_cases hb0 : b = 0
      · subst b
        have hn : n = q := by omega
        cases hn
        exact h.row_exact_at_zero n _ (top_augmentation_zero M A f φ hφ n x hfx)
      · exact h.row_exact_neg b q (by omega) _
          (top_horizontal_cycle A n b q hbq x hx
            (fun p s hps hp => hs p s hps (Or.inr hp)))
    obtain ⟨y, hy⟩ := hy
    let t := A.ιTotal shZ (b - 1) q (n - 1) (by simp only [ComplexShape.π_def]; omega) y
    have hdt : (A.total shZ).d (n - 1) n t =
        A.ιTotal shZ b q n hbq (totalProjectionDiag A b q n hbq x) +
          (b - 1).negOnePow • A.ιTotal shZ (b - 1) (q + 1) n
            (by simp only [ComplexShape.π_def]; omega) ((A.X (b - 1)).d q (q + 1) y) := by
      dsimp [t]
      rw [differential_inclusion_apply A (b - 1) q b (q + 1) (n - 1) n
        (by omega) (by omega) rfl (by omega), hy]
    have htφ : φ.f (n - 1) t = 0 :=
      canonical_inclusion_zero M A f φ hφ (b - 1) q (n - 1) (by omega) (by omega) y
    have hcycle := d_sub_d_eq_zero hx t
    have haug := map_sub_d_eq_sub φ x t
    rw [hfx, htφ, map_zero, sub_self] at haug
    have hsupport : ∀ p s (hps : p + s = n), p < (b - 1) - (k : ℤ) ∨ b - 1 < p →
        totalProjectionDiag A p s n hps (x - (A.total shZ).d (n - 1) n t) = 0 := by
      intro p s hps hp
      rw [map_sub, hdt, map_add]
      simp only [Units.smul_def, map_zsmul]
      by_cases hpb : p = b
      · subst p
        have hsq : s = q := by omega
        subst s
        rw [projection_inclusion_self, projection_inclusion_ne A (b - 1) (q + 1) b q n
          (by omega) hbq (by omega)]
        simp
      · rw [projection_inclusion_ne A b q p s n hbq hps (Ne.symm hpb),
          projection_inclusion_ne A (b - 1) (q + 1) p s n (by omega) hps (by omega),
          hs p s hps (by push_cast; omega)]
        simp
    obtain ⟨z, hz⟩ := ih n (b - 1) (q + 1) (by omega) (by omega)
      (x - (A.total shZ).d (n - 1) n t) hcycle haug hsupport
    refine ⟨z + t, ?_⟩
    rw [map_add, hz, sub_add_cancel]

private lemma cycle_boundary
    (M : HomologicalComplex Ab shZ) (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ] (f : A.X 0 ⟶ M) (h : GoodResolution M A f)
    (φ : A.total shZ ⟶ M) (hφ : ∀ n, φ.f n = canonicalMapF M A f n)
    (n : ℤ) (x : (A.total shZ).X n)
    (hx : (A.total shZ).d n (n + 1) x = 0) (hfx : φ.f n x = 0) :
    ∃ y : (A.total shZ).X (n - 1), (A.total shZ).d (n - 1) n y = x := by
  obtain ⟨k, hk⟩ := total_has_lower_bound A n x
  apply cycle_boundary_of_bounds M A f h φ hφ k n 0 n (by omega) le_rfl x hx hfx
  intro p q hpq hp
  rcases hp with hp | hp
  · exact hk p q hpq (by simpa using hp)
  · exact proj_eq_zero_of_isZero A p q n hpq (h.vanishing_pos p hp) x

private lemma cycle_lift
    (M : HomologicalComplex Ab shZ) (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ] (f : A.X 0 ⟶ M) (h : GoodResolution M A f)
    (φ : A.total shZ ⟶ M) (hφ : ∀ n, φ.f n = canonicalMapF M A f n)
    (n : ℤ) (m : M.X n) (hm : M.d n (n + 1) m = 0) :
    ∃ x : (A.total shZ).X n, (A.total shZ).d n (n + 1) x = 0 ∧ φ.f n x = m := by
  obtain ⟨x, hx, hfx⟩ := h.ker_aug_surj n m hm
  dsimp only [fnOf] at hx
  refine ⟨A.ιTotal shZ 0 n n (by simp only [ComplexShape.π_def]; omega) x, ?_, ?_⟩
  · rw [differential_inclusion_apply A 0 n 1 (n + 1) n (n + 1)
      (by omega) (by omega) rfl rfl, hx, map_zero, smul_zero, add_zero]
    rw [ιTotal_eq_zero_of_isZero A 1 n (n + 1) _ (h.vanishing_pos 1 (by omega))]
    rfl
  · rw [hφ, canonical_projection, ConcreteCategory.comp_apply, projection_inclusion_self]
    exact hfx

private lemma cycles_lift {c : ComplexShape ℤ} (X : HomologicalComplex Ab c) (j k : ℤ)
    (hk : c.next j = k) (x : X.X j) (hx : X.d j k x = 0) :
    ∃ z : X.cycles j, X.iCycles j z = x :=
  (ShortComplex.mk (X.iCycles j) (X.d j k) (X.iCycles_d j k)).ab_exact_iff.mp
    (ShortComplex.exact_of_f_is_kernel _ (X.cyclesIsKernel j k hk)) x hx

private lemma cycles_boundary {c : ComplexShape ℤ} (X : HomologicalComplex Ab c) (i j : ℤ)
    (hi : c.prev j = i) (z : X.cycles j) (hz : X.homologyπ j z = 0) :
    ∃ y : X.X i, X.toCycles i j y = z :=
  (ShortComplex.mk (X.toCycles i j) (X.homologyπ j) (X.toCycles_comp_homologyπ i j)).ab_exact_iff.mp
    (ShortComplex.exact_of_g_is_cokernel _ (X.homologyIsCokernel i j hi)) z hz

private lemma quasiIsoAt_of_elements {c : ComplexShape ℤ} {K L : HomologicalComplex Ab c}
    (φ : K ⟶ L) (i j k : ℤ) (hi : c.prev j = i) (hk : c.next j = k)
    (hs : ∀ t : L.X j, L.d j k t = 0 → ∃ s : K.X j, K.d j k s = 0 ∧ φ.f j s = t)
    (hb : ∀ s : K.X j, K.d j k s = 0 → (∃ t : L.X i, L.d i j t = φ.f j s) →
      ∃ y : K.X i, K.d i j y = s) : QuasiIsoAt φ j := by
  have hepi : Function.Surjective (HomologicalComplex.cyclesMap φ j) := by
    intro t
    have ht : L.d j k (L.iCycles j t) = 0 := by
      rw [← ConcreteCategory.comp_apply, L.iCycles_d, AddCommGrpCat.zero_apply]
    obtain ⟨s, hs, hst⟩ := hs (L.iCycles j t) ht
    obtain ⟨z, hz⟩ := cycles_lift K j k hk s hs
    refine ⟨z, (AddCommGrpCat.mono_iff_injective (L.iCycles j)).mp inferInstance ?_⟩
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, hz, hst]
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap φ j) := by
    intro a
    obtain ⟨t, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (L.homologyπ j)).mp inferInstance a
    obtain ⟨z, rfl⟩ := hepi t
    refine ⟨K.homologyπ j z, ?_⟩
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
      ConcreteCategory.comp_apply]
  have hinj : Function.Injective (HomologicalComplex.homologyMap φ j) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ j)).mp inferInstance a
    have hz : L.homologyπ j (HomologicalComplex.cyclesMap φ j z) = 0 := by
      rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyπ_naturality,
        ConcreteCategory.comp_apply, ha]
    obtain ⟨t, ht⟩ := cycles_boundary L i j hi _ hz
    have hst : L.d i j t = φ.f j (K.iCycles j z) := by
      rw [← L.toCycles_i, ConcreteCategory.comp_apply, ht, ← ConcreteCategory.comp_apply,
        HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply]
    have hsz : K.d j k (K.iCycles j z) = 0 := by
      rw [← ConcreteCategory.comp_apply, K.iCycles_d, AddCommGrpCat.zero_apply]
    obtain ⟨y, hy⟩ := hb (K.iCycles j z) hsz ⟨t, hst⟩
    have hyz : K.toCycles i j y = z := by
      apply (AddCommGrpCat.mono_iff_injective (K.iCycles j)).mp inferInstance
      rw [← ConcreteCategory.comp_apply, K.toCycles_i, hy]
    rw [← hyz, ← ConcreteCategory.comp_apply, K.toCycles_comp_homologyπ,
      AddCommGrpCat.zero_apply]
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap φ j) :=
    (AddCommGrpCat.mono_iff_injective _).mpr hinj
  have : Epi (HomologicalComplex.homologyMap φ j) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
  exact isIso_of_mono_of_epi _

/-- Any chain map with the canonical components is a quasi-isomorphism. -/
lemma canonical_chain_map_quasiIso
    (M : HomologicalComplex Ab shZ)
    (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ]
    (f : A.X 0 ⟶ M)
    (h : GoodResolution M A f)
    (φ : A.total shZ ⟶ M)
    (hφ : ∀ n : ℤ, φ.f n = canonicalMapF M A f n) :
    QuasiIso φ := by
  refine ⟨fun n => quasiIsoAt_of_elements φ (n - 1) n (n + 1) (by simp) (by simp)
    (cycle_lift M A f h φ hφ n) ?_⟩
  intro x hx ⟨m, hm⟩
  obtain ⟨a, ha⟩ := h.aug_surj (n - 1) m
  let t := A.ιTotal shZ 0 (n - 1) (n - 1) (by simp only [ComplexShape.π_def]; omega) a
  have ht : φ.f (n - 1) t = m := by
    dsimp [t]
    rw [hφ, canonical_projection, ConcreteCategory.comp_apply, projection_inclusion_self]
    exact ha
  have hcycle := d_sub_d_eq_zero hx t
  have haug := map_sub_d_eq_sub φ x t
  rw [ht, hm, sub_self] at haug
  obtain ⟨z, hz⟩ := cycle_boundary M A f h φ hφ n _ hcycle haug
  exact ⟨z + t, by rw [map_add, hz, sub_add_cancel]⟩

/-- A good resolution `A → M` yields a chain map `A.total shZ ⟶ M` whose
per-degree components agree with `canonicalMapF`, and this chain map is a
quasi-isomorphism. -/
@[stacks 09IZ]
theorem quasiIso_of_goodResolution
    (M : HomologicalComplex Ab shZ)
    (A : HomologicalComplex₂ Ab shZ shZ)
    [A.HasTotal shZ]
    (f : A.X 0 ⟶ M)
    (_h : GoodResolution M A f) :
    ∃ φ : A.total shZ ⟶ M,
      (∀ n : ℤ, φ.f n = canonicalMapF M A f n) ∧ QuasiIso φ := by
  obtain ⟨φ, hφ⟩ := canonical_chain_map_exists M A f _h
  exact ⟨φ, hφ, canonical_chain_map_quasiIso M A f _h φ hφ⟩

end

section

/-!
## Stacks tag 0E1R

Let `M^•` be a cochain complex of abelian groups and let
`… → A_2^• → A_1^• → A_0^• → M^• → 0` be an exact complex of complexes of
abelian groups. Then the induced map `Tot_π(A^{•,•}) → M^•` is a
quasi-isomorphism.
-/

open CategoryTheory CategoryTheory.Limits

/-- A "left resolution by complexes" of a cochain complex `M` of abelian groups. -/
@[ega "0 11.4.1" "special case"]
structure LeftComplexResolution (M : CochainComplex Ab.{0} ℤ) where
  /-- The complex `A_n^•` in position `n`. -/
  A : ℕ → CochainComplex Ab.{0} ℤ
  /-- The differential `A_{n+1}^• → A_n^•`. -/
  d : ∀ n, A (n + 1) ⟶ A n
  /-- The augmentation `A_0^• → M^•`. -/
  ε : A 0 ⟶ M
  d_comp_d : ∀ n, d (n + 1) ≫ d n = 0
  d_comp_ε : d 0 ≫ ε = 0
  /-- In every degree `q`, the sequence `A_{n+2}^q → A_{n+1}^q → A_n^q` is exact. -/
  exact_at_A : ∀ (n : ℕ) (q : ℤ),
    (ShortComplex.mk ((d (n + 1)).f q) ((d n).f q) (by
      have h := d_comp_d n
      have := congrArg (fun (φ : A (n + 1 + 1) ⟶ A n) => φ.f q) h
      simpa using this)).Exact
  /-- In every degree `q`, the sequence `A_1^q → A_0^q → M^q` is exact. -/
  exact_at_A0 : ∀ (q : ℤ),
    (ShortComplex.mk ((d 0).f q) (ε.f q) (by
      have h := d_comp_ε
      have := congrArg (fun (φ : A 1 ⟶ M) => φ.f q) h
      simpa using this)).Exact
  /-- In every degree `q`, the augmentation `A_0^q → M^q` is an epimorphism. -/
  epi_ε : ∀ (q : ℤ), Epi (ε.f q)

namespace LeftComplexResolution

variable {M : CochainComplex Ab.{0} ℤ} (R : LeftComplexResolution M)

/-- The degree-`n` part of the product total complex. -/
@[sga "4 XVII 1.1.4" "partial"]
noncomputable abbrev productTotalX (n : ℤ) : Ab.{0} :=
  ∏ᶜ (fun k : ℕ => (R.A k).X (n + (k : ℤ)))

/-- Projection onto the `(p, q) = (-k, n+k)` factor. -/
noncomputable def productTotalProj (n : ℤ) (k : ℕ) :
    R.productTotalX n ⟶ (R.A k).X (n + (k : ℤ)) :=
  Pi.π _ k

/-- Auxiliary shift equality. -/
lemma shift_eq (n : ℤ) (k : ℕ) :
    (R.A (k + 1)).X (n + 1 + (k : ℤ)) = (R.A (k + 1)).X (n + ((k + 1 : ℕ) : ℤ)) := by
  congr 1
  push_cast
  ring

/-- The differential of the product total complex. -/
@[sga "4 XVII 1.1.4" "partial"]
noncomputable def productTotalD (n : ℤ) :
    R.productTotalX n ⟶ R.productTotalX (n + 1) :=
  Pi.lift (fun k =>
    (-1)^k • (R.productTotalProj n k ≫ (R.A k).d (n + k) (n + 1 + k)) +
    (R.productTotalProj n (k + 1) ≫ eqToHom (R.shift_eq n k).symm ≫
      ((R.d k).f (n + 1 + k))))

private lemma productTotal_hom_ext {n : ℤ} {Z : Ab.{0}} {f g : Z ⟶ R.productTotalX n}
    (h : ∀ k, f ≫ R.productTotalProj n k = g ≫ R.productTotalProj n k) : f = g :=
  Pi.hom_ext _ _ fun k => by simpa only [productTotalProj] using h k

private lemma eqToHom_eq_XIsoOfEq_hom (K : CochainComplex Ab.{0} ℤ) {a b : ℤ} (e : a = b)
    (h : K.X a = K.X b) : eqToHom h = (K.XIsoOfEq e).hom := by
  subst e
  simp

private abbrev verticalMap (n : ℤ) (k : ℕ) :=
  (R.A k).d (n + k) (n + 1 + k)

private lemma horizontal_degree (n : ℤ) (k : ℕ) : n + (k + 1 : ℕ) = n + 1 + k := by
  push_cast; ring

private noncomputable def horizontalMap (n : ℤ) (k : ℕ) :
    (R.A (k + 1)).X (n + (k + 1 : ℕ)) ⟶ (R.A k).X (n + 1 + k) :=
  ((R.A (k + 1)).XIsoOfEq (horizontal_degree n k)).hom ≫ (R.d k).f (n + 1 + k)

private lemma verticalMap_comp_verticalMap (n : ℤ) (k : ℕ) :
    R.verticalMap n k ≫ R.verticalMap (n + 1) k = 0 :=
  (R.A k).d_comp_d _ _ _

private lemma horizontalMap_comp_verticalMap (n : ℤ) (k : ℕ) :
    R.horizontalMap n k ≫ R.verticalMap (n + 1) k =
      R.verticalMap n (k + 1) ≫ R.horizontalMap (n + 1) k := by
  rw [horizontalMap, horizontalMap, Category.assoc, HomologicalComplex.Hom.comm,
    ← Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d, ← Category.assoc,
    HomologicalComplex.d_comp_XIsoOfEq_hom]

private lemma horizontalMap_comp_horizontalMap (n : ℤ) (k : ℕ) :
    R.horizontalMap n (k + 1) ≫ R.horizontalMap (n + 1) k = 0 := by
  rw [horizontalMap, horizontalMap, Category.assoc, ← Category.assoc ((R.d (k + 1)).f _),
    HomologicalComplex.XIsoOfEq_hom_naturality, Category.assoc]
  have h := congrArg (fun f => HomologicalComplex.Hom.f f (n + 1 + 1 + k))
    (R.d_comp_d k)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
  rw [h, comp_zero, comp_zero]

private lemma productTotalD_proj (n : ℤ) (k : ℕ) :
    R.productTotalD n ≫ R.productTotalProj (n + 1) k =
      (-1 : ℤ)^k • (R.productTotalProj n k ≫ R.verticalMap n k) +
        R.productTotalProj n (k + 1) ≫ R.horizontalMap n k := by
  simp [productTotalD, productTotalProj, horizontalMap,
    eqToHom_eq_XIsoOfEq_hom (R.A (k + 1)) (horizontal_degree n k)]

/-- The product total differential squares to zero. -/
lemma productTotalD_sq_zero_aux {M : CochainComplex Ab.{0} ℤ}
    (R : LeftComplexResolution M) (n : ℤ) :
    R.productTotalD n ≫ R.productTotalD (n + 1) = 0 := by
  refine R.productTotal_hom_ext fun k => ?_
  rw [Category.assoc, productTotalD_proj, Preadditive.comp_add, Preadditive.comp_zsmul,
    ← Category.assoc, ← Category.assoc, productTotalD_proj, productTotalD_proj]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
    verticalMap_comp_verticalMap, horizontalMap_comp_horizontalMap, comp_zero, zero_comp,
    smul_zero, zero_add, add_zero]
  rw [horizontalMap_comp_verticalMap, pow_succ, mul_neg_one, neg_smul, add_neg_cancel]

/-- The differential of the product total complex squares to zero. -/
theorem productTotalD_comp_productTotalD (n : ℤ) :
    R.productTotalD n ≫ R.productTotalD (n + 1) = 0 :=
  productTotalD_sq_zero_aux R n

/-- The product total complex of the double complex coming from a left complex
resolution. -/
@[sga "4 XVII 1.1.4" "special case"]
noncomputable abbrev productTotal : CochainComplex Ab.{0} ℤ :=
  CochainComplex.of (fun n => R.productTotalX n) (fun n => R.productTotalD n)
    R.productTotalD_comp_productTotalD

private lemma productTotal_d (n : ℤ) : R.productTotal.d n (n + 1) = R.productTotalD n :=
  CochainComplex.of_d _ _ n

/-- Auxiliary degree shift used by the augmentation. -/
lemma augF_degree_eq (n : ℤ) :
    (R.A 0).X (n + ((0 : ℕ) : ℤ)) = (R.A 0).X n := by
  congr 1
  push_cast
  ring

/-- The component of the augmentation in degree `n`. -/
noncomputable def productTotalAugF (n : ℤ) : R.productTotalX n ⟶ M.X n :=
  R.productTotalProj n 0 ≫ eqToHom (R.augF_degree_eq n) ≫ R.ε.f n

private lemma aug_degree (n : ℤ) : n + ((0 : ℕ) : ℤ) = n := by
  simp

private noncomputable def augmentationMap (n : ℤ) : (R.A 0).X (n + (0 : ℕ)) ⟶ M.X n :=
  ((R.A 0).XIsoOfEq (aug_degree n)).hom ≫ R.ε.f n

private lemma productTotalAugF_eq (n : ℤ) :
    R.productTotalAugF n = R.productTotalProj n 0 ≫ R.augmentationMap n := by
  rw [productTotalAugF, augmentationMap, eqToHom_eq_XIsoOfEq_hom _ (aug_degree n)]

private lemma verticalMap_comp_augmentationMap (n : ℤ) :
    R.verticalMap n 0 ≫ R.augmentationMap (n + 1) =
      R.augmentationMap n ≫ M.d n (n + 1) := by
  rw [augmentationMap, augmentationMap, Category.assoc, R.ε.comm, ← Category.assoc,
    HomologicalComplex.d_comp_XIsoOfEq_hom, ← Category.assoc ((R.A 0).XIsoOfEq _).hom,
    HomologicalComplex.XIsoOfEq_hom_comp_d]

private lemma horizontalMap_comp_augmentationMap (n : ℤ) :
    R.horizontalMap n 0 ≫ R.augmentationMap (n + 1) = 0 := by
  rw [horizontalMap, augmentationMap, Category.assoc, ← Category.assoc ((R.d 0).f _),
    HomologicalComplex.XIsoOfEq_hom_naturality, Category.assoc]
  have h := congrArg (fun f => HomologicalComplex.Hom.f f (n + 1)) R.d_comp_ε
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at h
  rw [h, comp_zero, comp_zero]

/-- The augmentation commutes with the differentials. -/
lemma productTotalAugF_comm_aux {M : CochainComplex Ab.{0} ℤ}
    (R : LeftComplexResolution M) (n : ℤ) :
    R.productTotalD n ≫ R.productTotalAugF (n + 1) =
      R.productTotalAugF n ≫ M.d n (n + 1) := by
  rw [productTotalAugF_eq, productTotalAugF_eq, ← Category.assoc, productTotalD_proj]
  simp [Preadditive.add_comp, verticalMap_comp_augmentationMap,
    horizontalMap_comp_augmentationMap]

/-- Compatibility of the augmentation with the differentials of the product
total complex and of `M`. -/
theorem productTotalAugF_comm (n : ℤ) :
    R.productTotalD n ≫ R.productTotalAugF (n + 1) =
      R.productTotalAugF n ≫ M.d n (n + 1) :=
  productTotalAugF_comm_aux R n

/-- The augmentation chain map from the product total complex to `M`. -/
noncomputable def productTotalAug : R.productTotal ⟶ M where
  f n := R.productTotalAugF n
  comm' i j hij := by
    rw [ComplexShape.up_Rel] at hij
    subst hij
    rw [productTotal_d]
    exact (R.productTotalAugF_comm i).symm

private lemma productTotalAug_f (n : ℤ) : R.productTotalAug.f n = R.productTotalAugF n :=
  rfl

private lemma augmentationMap_surjective (n : ℤ) : Function.Surjective (R.augmentationMap n) := by
  have := R.epi_ε n
  have : Epi (R.augmentationMap n) := by
    rw [augmentationMap]
    infer_instance
  exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance

private lemma horizontalMap_exact (n : ℤ) (k : ℕ)
    (x : (R.A (k + 1)).X (n + 1 + (k + 1 : ℕ)))
    (hx : R.horizontalMap (n + 1) k x = 0) :
    ∃ y, R.horizontalMap n (k + 1) y = x := by
  let e := (R.A k).XIsoOfEq (horizontal_degree (n + 1) k)
  have he : R.horizontalMap (n + 1) k = (R.d k).f _ ≫ e.hom := by
    rw [horizontalMap, HomologicalComplex.XIsoOfEq_hom_naturality]
  have hx' : (R.d k).f _ x = 0 := by
    refine ((AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance).eq_iff.mp ?_
    simpa only [he, ConcreteCategory.comp_apply, map_zero] using hx
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (R.exact_at_A k _) x hx'
  let e' := (R.A (k + 1 + 1)).XIsoOfEq (horizontal_degree n (k + 1))
  refine ⟨e'.inv y, ?_⟩
  rw [horizontalMap, ← ConcreteCategory.comp_apply, Iso.inv_hom_id_assoc]
  exact hy

private lemma horizontalMap_exact_zero (n : ℤ) (x : (R.A 0).X (n + 1 + (0 : ℕ)))
    (hx : R.augmentationMap (n + 1) x = 0) : ∃ y, R.horizontalMap n 0 y = x := by
  let e := (R.A 0).XIsoOfEq (aug_degree (n + 1))
  have hx' : R.ε.f (n + 1) (e.hom x) = 0 := by
    rwa [augmentationMap, ConcreteCategory.comp_apply] at hx
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (R.exact_at_A0 (n + 1)) (e.hom x) hx'
  let e' := (R.A 1).XIsoOfEq (show n + (0 + 1 : ℕ) = n + 1 by simp)
  refine ⟨e'.inv y, ?_⟩
  refine ((AddCommGrpCat.mono_iff_injective e.hom).mp inferInstance).eq_iff.mp ?_
  rw [← ConcreteCategory.comp_apply]
  have he : R.horizontalMap n 0 ≫ e.hom = e'.hom ≫ (R.d 0).f (n + 1) := by
    rw [horizontalMap, Category.assoc, HomologicalComplex.XIsoOfEq_hom_naturality,
      HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
  rw [he, ← ConcreteCategory.comp_apply, Iso.inv_hom_id_assoc]
  exact hy

private lemma productTotalProj_d_apply (n : ℤ) (k : ℕ) (x : R.productTotalX n) :
    R.productTotalProj (n + 1) k (R.productTotalD n x) =
      (-1 : ℤ)^k • R.verticalMap n k (R.productTotalProj n k x) +
        R.horizontalMap n k (R.productTotalProj n (k + 1) x) := by
  simpa [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (R.productTotalD_proj n k) x

private lemma productTotal_ext (n : ℤ) (x y : R.productTotalX n)
    (h : ∀ k, R.productTotalProj n k x = R.productTotalProj n k y) : x = y := by
  refine (Concrete.productEquiv (fun k => (R.A k).X (n + k))).apply_eq_iff_eq.mp ?_
  funext k
  simpa only [Concrete.productEquiv_apply_apply, productTotalProj] using h k

-- The recursive lifting property for the augmentation. At each step, exactness
-- of the next row supplies the next component of the product.
private lemma lift_differential (n : ℤ) (x : R.productTotalX (n + 1))
    (hx : R.productTotalD (n + 1) x = 0) (y : M.X n)
    (hy : R.productTotalAugF (n + 1) x = M.d n (n + 1) y) :
    ∃ z : R.productTotalX n, R.productTotalD n z = x ∧ R.productTotalAugF n z = y := by
  classical
  obtain ⟨z₀, hz₀⟩ := R.augmentationMap_surjective n y
  obtain ⟨z, hz_zero, hz_succ⟩ : ∃ z : ∀ k : ℕ, (R.A k).X (n + k), z 0 = z₀ ∧
      ∀ k, z (k + 1) = Function.invFun (R.horizontalMap n k)
        (R.productTotalProj (n + 1) k x - (-1 : ℤ)^k • R.verticalMap n k (z k)) :=
    ⟨fun k => Nat.rec z₀ (fun k z => Function.invFun (R.horizontalMap n k)
      (R.productTotalProj (n + 1) k x - (-1 : ℤ)^k • R.verticalMap n k z)) k,
      rfl, fun _ => rfl⟩
  have hz (k : ℕ) : R.horizontalMap n k (z (k + 1)) =
      R.productTotalProj (n + 1) k x - (-1 : ℤ)^k • R.verticalMap n k (z k) := by
    induction k with
    | zero =>
      rw [hz_succ 0]
      apply Function.invFun_eq
      apply R.horizontalMap_exact_zero
      have he := ConcreteCategory.congr_hom (R.verticalMap_comp_augmentationMap n) z₀
      simp only [ConcreteCategory.comp_apply] at he
      rw [productTotalAugF_eq, ConcreteCategory.comp_apply] at hy
      rw [pow_zero, one_smul, map_sub, hz_zero, he, hz₀]
      exact sub_eq_zero.mpr hy
    | succ k ih =>
      rw [hz_succ (k + 1)]
      apply Function.invFun_eq
      apply R.horizontalMap_exact
      simp only [map_sub, map_zsmul]
      have hc := R.productTotalProj_d_apply (n + 1) k x
      rw [hx, map_zero] at hc
      have hv := ConcreteCategory.congr_hom (R.horizontalMap_comp_verticalMap n k) (z (k + 1))
      have hvv := ConcreteCategory.congr_hom (R.verticalMap_comp_verticalMap n k) (z k)
      simp only [ConcreteCategory.comp_apply, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply] at hv hvv
      rw [← hv, ih, map_sub, map_zsmul, hvv, smul_zero, sub_zero, pow_succ, mul_neg_one,
        neg_smul, sub_neg_eq_add]
      exact (add_comm _ _).trans hc.symm
  let z' : R.productTotalX n := (Concrete.productEquiv (fun k => (R.A k).X (n + k))).symm z
  have hp (k : ℕ) : R.productTotalProj n k z' = z k := by
    simpa only [productTotalProj] using Concrete.productEquiv_symm_apply_π _ z k
  refine ⟨z', ?_, ?_⟩
  · apply R.productTotal_ext
    intro k
    rw [R.productTotalProj_d_apply, hp, hp, hz, add_sub_cancel]
  · rw [productTotalAugF_eq, ConcreteCategory.comp_apply, hp, hz_zero]
    exact hz₀

end LeftComplexResolution

/-- Quasi-isomorphism of the augmentation, packaged as a helper. -/
lemma quasiIso_productTotalAug_aux {M : CochainComplex Ab.{0} ℤ} (R : LeftComplexResolution M) :
    QuasiIso R.productTotalAug := by
  rw [quasiIso_iff]
  intro i
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, n + 1 = i := ⟨i - 1, by omega⟩
  apply HomologicalComplex₂.quasiIsoAt_of_elements
  · intro y hy
    obtain ⟨z, hz, he⟩ := R.lift_differential (n + 1) 0 (map_zero _) y
      (by simpa only [map_zero] using hy.symm)
    refine ⟨z, ?_, 0, ?_⟩
    · rw [R.productTotal_d]
      exact hz
    · rw [R.productTotalAug_f, map_zero, add_zero]
      exact he.symm
  · intro x hx y hy
    rw [R.productTotal_d] at hx
    rw [R.productTotalAug_f] at hy
    obtain ⟨z, hz, _⟩ := R.lift_differential n x hx y hy
    refine ⟨z, ?_⟩
    rw [R.productTotal_d]
    exact hz

/-- The natural map from the product total complex of an exact left resolution
by complexes to `M` is a quasi-isomorphism. -/
@[stacks 0E1R]
alias quasiIso_productTotalAug := quasiIso_productTotalAug_aux

end

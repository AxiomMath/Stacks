module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Matress

/-!
# Dual matresses

The dual of a matress of finite-dimensional vector spaces, with the two indices reversed and
negated, is again a matress.

## Main results

* `Stacks.DerivedEquivalence.exists_dual_matress` constructs the dual double complex and its
  matress structure.

## Implementation notes

The constructed double complex has terms `Hom(K^{-q,-p}, k)`.  Heterogeneous equalities specify
its horizontal and vertical differentials as the duals of the vertical and the horizontal
differentials of `K` respectively; they avoid choosing noncanonical integer-index casts.  The
matress structure includes the exact rows and columns, the compatible three-periodicity and the
diagonal filling condition.

## References

* [Stacks Project, Tag 0H8C](https://stacks.math.columbia.edu/tag/0H8C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex₂ (Matress reindexIso)

universe u v

namespace Stacks.DerivedEquivalence

/-- The first differential of a double complex, composed with the identification of its target with
a reindexed entry. -/
private abbrev horizontal {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' : ℤ) (hp : p + 1 = p') (hq : q = q') : K.X p q ⟶ K.X p' q' :=
  K.d₁ p q ≫ (reindexIso K hp hq).hom

/-- The second differential of a double complex, composed with the identification of its target
with a reindexed entry. -/
private abbrev vertical {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' : ℤ) (hp : p = p') (hq : q + 1 = q') : K.X p q ⟶ K.X p' q' :=
  K.d₂ p q ≫ (reindexIso K hp hq).hom

/-- Two consecutive reindexed first differentials compose to zero. -/
private lemma horizontal_comp_horizontal {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' p'' q'' : ℤ) (hp : p + 1 = p') (hq : q = q')
    (hp' : p' + 1 = p'') (hq' : q' = q'') :
    horizontal K p q p' q' hp hq ≫ horizontal K p' q' p'' q'' hp' hq' = 0 := by
  subst p' q' p'' q''
  simpa [horizontal, reindexIso] using K.d₁_comp_d₁ p q

/-- Two consecutive reindexed second differentials compose to zero. -/
private lemma vertical_comp_vertical {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' p'' q'' : ℤ) (hp : p = p') (hq : q + 1 = q')
    (hp' : p' = p'') (hq' : q' + 1 = q'') :
    vertical K p q p' q' hp hq ≫ vertical K p' q' p'' q'' hp' hq' = 0 := by
  subst p' q' p'' q''
  simpa [vertical, reindexIso] using K.d₂_comp_d₂ p q

/-- The reindexed first and second differentials commute. -/
private lemma horizontal_vertical {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q a b c d e f : ℤ) (ha : p + 1 = a) (hb : q = b)
    (hc : p = c) (hd : q + 1 = d) (he : a = e) (hf : b + 1 = f)
    (he' : c + 1 = e) (hf' : d = f) :
    horizontal K p q a b ha hb ≫ vertical K a b e f he hf =
      vertical K p q c d hc hd ≫ horizontal K c d e f he' hf' := by
  subst a b c d e f
  simpa [horizontal, vertical, reindexIso] using (K.comm p q).symm

/-- The first differential of the dual double complex: the dual of a reindexed second differential.
-/
private abbrev dualD₁ {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)) (p q : ℤ) :
    ModuleCat.of k (Module.Dual k (K.X (-q) (-p))) ⟶
      ModuleCat.of k (Module.Dual k (K.X (-q) (-(p + 1)))) :=
  ModuleCat.ofHom (vertical K (-q) (-(p + 1)) (-q) (-p) rfl (by omega)).hom.dualMap

/-- The second differential of the dual double complex: the dual of a reindexed first differential.
-/
private abbrev dualD₂ {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)) (p q : ℤ) :
    ModuleCat.of k (Module.Dual k (K.X (-q) (-p))) ⟶
      ModuleCat.of k (Module.Dual k (K.X (-(q + 1)) (-p))) :=
  ModuleCat.ofHom (horizontal K (-(q + 1)) (-p) (-q) (-p) (by omega) rfl).hom.dualMap

/-- Dualizing reverses a composition that vanishes, and the result again vanishes. -/
private lemma dual_comp_zero {k : Type u} [Field k] {A B C : ModuleCat.{max u v} k}
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) :
    ModuleCat.ofHom g.hom.dualMap ≫ ModuleCat.ofHom f.hom.dualMap = 0 := by
  apply ModuleCat.hom_ext
  change f.hom.dualMap ∘ₗ g.hom.dualMap = 0
  rw [LinearMap.dualMap_comp_dualMap, show g.hom ∘ₗ f.hom = 0 from congrArg ModuleCat.Hom.hom h]
  ext φ x
  exact map_zero φ

/-- Dualizing a commuting square gives a commuting square with the two sides exchanged. -/
private lemma dual_comp_eq {k : Type u} [Field k] {A B C D : ModuleCat.{max u v} k}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (i : C ⟶ D) (w : f ≫ g = h ≫ i) :
    ModuleCat.ofHom g.hom.dualMap ≫ ModuleCat.ofHom f.hom.dualMap =
      ModuleCat.ofHom i.hom.dualMap ≫ ModuleCat.ofHom h.hom.dualMap := by
  apply ModuleCat.hom_ext
  change f.hom.dualMap ∘ₗ g.hom.dualMap = h.hom.dualMap ∘ₗ i.hom.dualMap
  simp only [LinearMap.dualMap_comp_dualMap]
  exact congrArg LinearMap.dualMap (congrArg ModuleCat.Hom.hom w)

/-- The dual double complex, with terms `Hom(K^{-q,-p}, k)` and the dual differentials. -/
private def dualComplex {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)) :
    HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k) where
  X p q := ModuleCat.of k (Module.Dual k (K.X (-q) (-p)))
  d₁ := dualD₁ K
  d₂ := dualD₂ K
  d₁_comp_d₁ _ _ := dual_comp_zero _ _ (vertical_comp_vertical K _ _ _ _ _ _ _ _ _ _)
  d₂_comp_d₂ _ _ := dual_comp_zero _ _ (horizontal_comp_horizontal K _ _ _ _ _ _ _ _ _ _)
  comm _ _ := dual_comp_eq _ _ _ _ (horizontal_vertical K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).symm

/-- Dualizing an exact pair of linear maps over a field gives an exact pair in the reverse order.
-/
@[sga "2 IV 5.2" "partial"]
private lemma exact_dual {k : Type u} [Field k]
    {V W Z : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup Z]
    [Module k V] [Module k W] [Module k Z]
    (f : V →ₗ[k] W) (g : W →ₗ[k] Z) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by
  rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, h.linearMap_ker_eq]

/-- The dual of a reindexed second differential is the dual of the second differential itself. -/
private lemma dual_vertical_heq {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' r s : ℤ) (hp : p = p') (hq : q + 1 = q')
    (hr : p = r) (hs : q = s) :
    HEq (ModuleCat.ofHom (R := k) (vertical K p q p' q' hp hq).hom.dualMap)
      (ModuleCat.ofHom (R := k) (K.d₂ r s).hom.dualMap) := by
  subst p' q' r s
  simp [vertical, reindexIso]

/-- The dual of a reindexed first differential is the dual of the first differential itself. -/
private lemma dual_horizontal_heq {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' r s : ℤ) (hp : p + 1 = p') (hq : q = q')
    (hr : p = r) (hs : q = s) :
    HEq (ModuleCat.ofHom (R := k) (horizontal K p q p' q' hp hq).hom.dualMap)
      (ModuleCat.ofHom (R := k) (K.d₁ r s).hom.dualMap) := by
  subst p' q' r s
  simp [horizontal, reindexIso]

/-- The rows of a matress are exact, in the reindexed form. -/
private lemma horizontal_exact {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q p' q' p'' q'' : ℤ) (hp : p + 1 = p') (hq : q = q')
    (hp' : p' + 1 = p'') (hq' : q' = q'') :
    Function.Exact (horizontal K p q p' q' hp hq).hom
      (horizontal K p' q' p'' q'' hp' hq').hom := by
  subst p' q' p'' q''
  simpa [horizontal, reindexIso] using hK.row_exact p q

/-- The columns of a matress are exact, in the reindexed form. -/
private lemma vertical_exact {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q p' q' p'' q'' : ℤ) (hp : p = p') (hq : q + 1 = q')
    (hp' : p' = p'') (hq' : q' + 1 = q'') :
    Function.Exact (vertical K p q p' q' hp hq).hom
      (vertical K p' q' p'' q'' hp' hq').hom := by
  subst p' q' p'' q''
  simpa [vertical, reindexIso] using hK.column_exact p q

/-- The three-periodicity of a matress, composed with a reindexing of its target. -/
private abbrev periodicTo {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q p' q' : ℤ) (hp : p + 3 = p') (hq : q - 3 = q') : K.X p q ≅ K.X p' q' :=
  hK.periodic p q ≪≫ reindexIso K hp hq

/-- The reindexing isomorphism is the `eqToHom` of the equality of entries it comes from. -/
private lemma reindexIso_hom {C : Type*} [Category C] [HasZeroMorphisms C]
    (K : HomologicalComplex₂.DoubleComplex C) {p q p' q' : ℤ}
    (hp : p = p') (hq : q = q') :
    (reindexIso K hp hq).hom = eqToHom (congrArg₂ K.X hp hq) := by
  subst p' q'
  rfl

/-- The reindexed three-periodicity commutes with the reindexed first differential. -/
private lemma horizontal_periodic {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q a b c d e f : ℤ) (ha : p + 1 = a) (hb : q = b)
    (hc : p + 3 = c) (hd : q - 3 = d) (he : a + 3 = e) (hf : b - 3 = f)
    (he' : c + 1 = e) (hf' : d = f) :
    horizontal K p q a b ha hb ≫ (periodicTo hK a b e f he hf).hom =
      (periodicTo hK p q c d hc hd).hom ≫ horizontal K c d e f he' hf' := by
  subst a b c d e f
  have hh := hK.periodic_d₁ p q
  simp only [reindexIso_hom, Category.assoc] at hh ⊢
  apply (cancel_mono (eqToHom (congrArg (fun i => K.X i (q - 3))
    (show (p + 1) + 3 = p + 4 by omega)))).1
  simpa [horizontal, periodicTo, reindexIso_hom, Category.assoc] using hh

/-- The reindexed three-periodicity commutes with the reindexed second differential. -/
private lemma vertical_periodic {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q a b c d e f : ℤ) (ha : p = a) (hb : q + 1 = b)
    (hc : p + 3 = c) (hd : q - 3 = d) (he : a + 3 = e) (hf : b - 3 = f)
    (he' : c = e) (hf' : d + 1 = f) :
    vertical K p q a b ha hb ≫ (periodicTo hK a b e f he hf).hom =
      (periodicTo hK p q c d hc hd).hom ≫ vertical K c d e f he' hf' := by
  subst a b c d e f
  have hh := hK.periodic_d₂ p q
  apply (cancel_mono (eqToHom (congrArg (fun j => K.X (p + 3) j)
    (show (q + 1) - 3 = q - 2 by omega)))).1
  simpa [vertical, periodicTo, reindexIso_hom, Category.assoc] using hh

/-- The dual of an isomorphism of modules, composed with negation; this is the sign convention
under which the periodic identifications of the dual complex commute with its differentials. -/
private def negativeDualIso {k : Type u} [Field k] {A B : ModuleCat.{max u v} k}
    (e : A ≅ B) : ModuleCat.of k (Module.Dual k A) ≅ ModuleCat.of k (Module.Dual k B) :=
  LinearEquiv.toModuleIso (e.symm.toLinearEquiv.dualMap.trans (LinearEquiv.neg k))

/-- The value of the sign-twisted dual isomorphism on a functional. -/
private lemma negativeDualIso_apply {k : Type u} [Field k] {A B : ModuleCat.{max u v} k}
    (e : A ≅ B) (φ : Module.Dual k A) (x : B) :
    (negativeDualIso e).hom φ x = -φ (e.inv x) := rfl

/-- A commuting square of modules dualizes, after the sign twist, to a commuting square of duals.
-/
private lemma negative_dual_square {k : Type u} [Field k]
    {A B C D : ModuleCat.{max u v} k} (f : A ⟶ B) (g : C ⟶ D)
    (i : A ≅ C) (j : B ≅ D) (w : f ≫ j.hom = i.hom ≫ g) :
    ModuleCat.ofHom f.hom.dualMap ≫ (negativeDualIso i).hom =
      (negativeDualIso j).hom ≫ ModuleCat.ofHom g.hom.dualMap := by
  have h : i.inv ≫ f = g ≫ j.inv := by
    apply (cancel_mono j.hom).1
    simp [Category.assoc, w]
  ext φ x
  change -φ (f (i.inv x)) = -φ (j.inv (g x))
  rw [show f (i.inv x) = j.inv (g x) from
    congrArg (fun t : C ⟶ B => t x) h]

/-- The three-periodicity of the dual complex, composed with a reindexing of its target. -/
private abbrev dualPeriodTo {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q p' q' : ℤ) (hp : p + 3 = p') (hq : q - 3 = q') :
    (dualComplex K).X p q ≅ (dualComplex K).X p' q' :=
  negativeDualIso (periodicTo hK (-q) (-p) (-q') (-p') (by omega) (by omega))

/-- The three-periodicity of the dual complex. -/
private def dualPeriodic {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q : ℤ) := dualPeriodTo hK p q (p + 3) (q - 3) rfl rfl

/-- The first differential of the dual complex is the dual of a reindexed second differential. -/
private lemma dual_horizontal {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' : ℤ) (hp : p + 1 = p') (hq : q = q') :
    horizontal (dualComplex K) p q p' q' hp hq =
      ModuleCat.ofHom (vertical K (-q') (-p') (-q) (-p) (by omega) (by omega)).hom.dualMap := by
  subst p' q'
  simp [horizontal, reindexIso, dualComplex]
  rfl

/-- The second differential of the dual complex is the dual of a reindexed first differential. -/
private lemma dual_vertical {k : Type u} [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    (p q p' q' : ℤ) (hp : p = p') (hq : q + 1 = q') :
    vertical (dualComplex K) p q p' q' hp hq =
      ModuleCat.ofHom (horizontal K (-q') (-p') (-q) (-p) (by omega) (by omega)).hom.dualMap := by
  subst p' q'
  simp [vertical, reindexIso, dualComplex]
  rfl

/-- The reindexed periodicity of the dual complex factors through its periodicity. -/
private lemma dualPeriodTo_eq {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q p' q' : ℤ) (hp : p + 3 = p') (hq : q - 3 = q') :
    (dualPeriodTo hK p q p' q' hp hq).hom =
      (dualPeriodic hK p q).hom ≫ (reindexIso (dualComplex K) hp hq).hom := by
  subst p' q'
  simp [reindexIso]
  rfl

/-- The periodicity of the dual complex commutes with its first differential. -/
private lemma dual_horizontal_periodic {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q a b c d e f : ℤ) (ha : p + 1 = a) (hb : q = b)
    (hc : p + 3 = c) (hd : q - 3 = d) (he : a + 3 = e) (hf : b - 3 = f)
    (he' : c + 1 = e) (hf' : d = f) :
    horizontal (dualComplex K) p q a b ha hb ≫ (dualPeriodTo hK a b e f he hf).hom =
      (dualPeriodTo hK p q c d hc hd).hom ≫ horizontal (dualComplex K) c d e f he' hf' := by
  simp only [dual_horizontal]
  exact negative_dual_square _ _ _ _ (vertical_periodic hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- The periodicity of the dual complex commutes with its second differential. -/
private lemma dual_vertical_periodic {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q a b c d e f : ℤ) (ha : p = a) (hb : q + 1 = b)
    (hc : p + 3 = c) (hd : q - 3 = d) (he : a + 3 = e) (hf : b - 3 = f)
    (he' : c = e) (hf' : d + 1 = f) :
    vertical (dualComplex K) p q a b ha hb ≫ (dualPeriodTo hK a b e f he hf).hom =
      (dualPeriodTo hK p q c d hc hd).hom ≫ vertical (dualComplex K) c d e f he' hf' := by
  simp only [dual_vertical]
  exact negative_dual_square _ _ _ _ (horizontal_periodic hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- Two functionals agreeing on the fibre product of two maps into a module extend to a single
functional on that module. -/
private lemma exists_common_extension {k : Type u} [Field k]
    {A B D : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module k A] [Module k B] [Module k D]
    (a : A →ₗ[k] D) (b : B →ₗ[k] D) (t : Module.Dual k A) (u : Module.Dual k B)
    (h : ∀ x y, a x = b y → t x = u y) :
    ∃ χ : Module.Dual k D, χ.comp a = t ∧ χ.comp b = u := by
  let f := a.coprod (-b)
  let ψ := t.coprod (-u)
  have hm : ψ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    rintro ⟨x, y⟩ hxy
    have he : a x = b y := by
      simpa [f, LinearMap.mem_ker, sub_eq_zero, ← sub_eq_add_neg] using hxy
    simpa [ψ, ← sub_eq_add_neg] using sub_eq_zero.mpr (h x y he)
  obtain ⟨χ, hχ⟩ := hm
  refine ⟨χ, ?_, ?_⟩
  · ext x
    simpa [f, ψ] using congrArg (fun z : Module.Dual k (A × B) => z (x, 0)) hχ
  · ext y
    simpa [f, ψ] using congrArg (fun z : Module.Dual k (A × B) => z (0, y)) hχ

/-- The filling condition of a matress, in the reindexed form. -/
private lemma fill_reindexed {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q bx bq cx cy dx dy ex ey fx fy gx gy : ℤ)
    (hbx : p - 1 = bx) (hby : q + 1 = bq)
    (hcx : p - 2 = cx) (hcy : q + 2 = cy)
    (hdx : p = dx) (hdy : q + 1 = dy)
    (hex : p - 1 = ex) (hey : q + 2 = ey)
    (hfx : p - 2 = fx) (hfy : q + 3 = fy)
    (hgx : p + 1 = gx) (hgy : q = gy)
    (α : K.X p q) (β : K.X bx bq)
    (h : vertical K p q dx dy (by omega) (by omega) α =
      horizontal K bx bq dx dy (by omega) (by omega) β) :
    ∃ γ : K.X cx cy,
      horizontal K cx cy ex ey (by omega) (by omega) γ =
        vertical K bx bq ex ey (by omega) (by omega) β ∧
      (periodicTo hK fx fy gx gy (by omega) (by omega)).hom
        (vertical K cx cy fx fy (by omega) (by omega) γ) =
          (p + q).negOnePow • horizontal K p q gx gy (by omega) (by omega) α := by
  subst bx bq cx cy dx dy ex ey fx fy gx gy
  simpa [horizontal, vertical, periodicTo, reindexIso_hom, ModuleCat.comp_apply] using
    hK.fill p q α β (by simpa [horizontal, vertical, reindexIso_hom, ModuleCat.comp_apply] using h)

/-- The dual complex of a matress satisfies the filling condition. -/
private lemma dual_fill {k : Type u} [Field k]
    {K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k)} (hK : Matress K)
    (p q : ℤ) (α : (dualComplex K).X p q) (β : (dualComplex K).X (p - 1) (q + 1))
    (h : vertical (dualComplex K) p q p (q + 1) rfl rfl α =
      horizontal (dualComplex K) (p - 1) (q + 1) p (q + 1) (by omega) rfl β) :
    ∃ γ : (dualComplex K).X (p - 2) (q + 2),
      horizontal (dualComplex K) (p - 2) (q + 2) (p - 1) (q + 2) (by omega) rfl γ =
        vertical (dualComplex K) (p - 1) (q + 1) (p - 1) (q + 2) rfl (by omega) β ∧
      (dualPeriodTo hK (p - 2) (q + 3) (p + 1) q (by omega) (by omega)).hom
        (vertical (dualComplex K) (p - 2) (q + 2) (p - 2) (q + 3) rfl (by omega) γ) =
          (p + q).negOnePow • horizontal (dualComplex K) p q (p + 1) q rfl rfl α := by
  change Module.Dual k (K.X (-q) (-p)) at α
  change Module.Dual k (K.X (-(q + 1)) (-(p - 1))) at β
  let r : ℤ := -q + 1
  let s : ℤ := -p - 2
  let n := (r + s).negOnePow
  let a := vertical K r s r (-(p + 1)) rfl (by dsimp [s]; omega)
  let b := horizontal K (-q) (-(p + 1)) r (-(p + 1)) rfl rfl
  let c := horizontal K (-(q + 1)) (-p) (-q) (-p) (by omega) rfl
  let d := vertical K (-q) (-(p + 1)) (-q) (-p) rfl (by omega)
  let e := vertical K (-(q + 1)) (-p) (-(q + 1)) (-(p - 1)) rfl (by omega)
  let f := horizontal K r s (r + 1) s rfl rfl
  let P := periodicTo hK (-(q + 1)) (-(p - 1)) (r + 1) s
    (by dsimp [r]; omega) (by dsimp [s]; omega)
  let A := periodicTo hK (-(q + 2)) (-(p - 1)) r s
    (by dsimp [r]; omega) (by dsimp [s]; omega)
  let D := periodicTo hK (-(q + 2)) (-(p - 2)) r (-(p + 1))
    (by dsimp [r]; omega) (by omega)
  let B := periodicTo hK (-(q + 3)) (-(p - 2)) (-q) (-(p + 1)) (by omega) (by omega)
  let a' := vertical K (-(q + 2)) (-(p - 1)) (-(q + 2)) (-(p - 2)) rfl (by omega)
  let b' := horizontal K (-(q + 3)) (-(p - 2)) (-(q + 2)) (-(p - 2)) (by omega) rfl
  let f' := horizontal K (-(q + 2)) (-(p - 1)) (-(q + 1)) (-(p - 1)) (by omega) rfl
  have hce : ∀ z, α (c z) = β (e z) := fun z => by
    have hh := congrArg (fun l : Module.Dual k (K.X (-(q + 1)) (-p)) => l z) h
    simp only [dual_vertical, dual_horizontal] at hh
    exact hh
  obtain ⟨χ, hχa, hχb⟩ := exists_common_extension a.hom b.hom
    (n • (β.comp (P.inv.hom.comp f.hom))) (α.comp d.hom) (by
      intro x y hxy
      obtain ⟨z, hz₁, hz₂⟩ := fill_reindexed hK r s
        (-q) (-(p + 1)) (-(q + 1)) (-p) r (-(p + 1)) (-q) (-p)
        (-(q + 1)) (-(p - 1)) (r + 1) s
        (by dsimp [r]; omega) (by dsimp [s]; omega)
        (by dsimp [r]; omega) (by dsimp [s]; omega)
        rfl (by dsimp [s]; omega) (by dsimp [r]; omega) (by dsimp [s]; omega)
        (by dsimp [r]; omega) (by dsimp [s]; omega) rfl rfl x y hxy
      change c z = d y at hz₁
      change P.hom (e z) = n • f x at hz₂
      have he : β (e z) = n • β (P.inv (f x)) := by
        simpa [Units.smul_def] using congrArg (fun z => β (P.inv z)) hz₂
      change n • β (P.inv (f x)) = α (d y)
      rw [← he, ← hce z, hz₁])
  have ha : a' ≫ D.hom = A.hom ≫ a :=
    vertical_periodic hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hf : f' ≫ P.hom = A.hom ≫ f :=
    horizontal_periodic hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hb : b' ≫ D.hom = B.hom ≫ b :=
    horizontal_periodic hK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨n • χ.comp D.hom.hom, ?_, ?_⟩ <;> simp only [dual_horizontal, dual_vertical] <;>
    refine LinearMap.ext fun x => ?_
  · change n • χ (D.hom (a' x)) = β (f' x)
    rw [show D.hom (a' x) = a (A.hom x) from ConcreteCategory.congr_hom ha x]
    have hχ := congrArg (fun t : Module.Dual k (K.X r s) => t (A.hom x)) hχa
    change χ (a (A.hom x)) = n • β (P.inv (f (A.hom x))) at hχ
    rw [hχ, smul_smul, Int.units_mul_self, one_smul,
      ← show P.hom (f' x) = f (A.hom x) from ConcreteCategory.congr_hom hf x]
    simp
  · change -(n • χ (D.hom (b' (B.inv x)))) = (p + q).negOnePow • α (d x)
    rw [show D.hom (b' (B.inv x)) = b x by simpa using ConcreteCategory.congr_hom hb (B.inv x)]
    have hχ := congrArg (fun t : Module.Dual k (K.X (-q) (-(p + 1))) => t x) hχb
    change χ (b x) = α (d x) at hχ
    rw [hχ]
    have hn : n = -(p + q).negOnePow := by
      change (r + s).negOnePow = _
      rw [show r + s = -(p + q) - 1 by dsimp [r, s]; omega,
        Int.negOnePow_sub, Int.negOnePow_neg]
      simp
    rw [hn]
    simp [Units.smul_def]

/-- **Stacks 0H8C.** The dual of a finite-dimensional matress is a matress. -/
@[stacks 0H8C]
public theorem exists_dual_matress (k : Type u) [Field k]
    (K : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k))
    [∀ p q : ℤ, FiniteDimensional k (K.X p q)]
    (hK : HomologicalComplex₂.Matress K) :
    ∃ L : HomologicalComplex₂.DoubleComplex (ModuleCat.{max u v} k),
      (∀ p q : ℤ, L.X p q = ModuleCat.of k (Module.Dual k (K.X (-q) (-p)))) ∧
      (∀ p q : ℤ,
        HEq (L.d₁ p q)
          (ModuleCat.ofHom (K.d₂ (-q) (-p - 1)).hom.dualMap)) ∧
      (∀ p q : ℤ,
        HEq (L.d₂ p q)
          (ModuleCat.ofHom (K.d₁ (-q - 1) (-p)).hom.dualMap)) ∧
      Nonempty (HomologicalComplex₂.Matress L) := by
  let L := dualComplex K
  refine ⟨L, fun _ _ => rfl, ?_, ?_, ?_⟩
  · intro p q
    exact dual_vertical_heq K _ _ _ _ _ _ _ _ rfl (by omega)
  · intro p q
    exact dual_horizontal_heq K _ _ _ _ _ _ _ _ (by omega) rfl
  · refine ⟨{ row_exact := ?_
              column_exact := ?_
              periodic := dualPeriodic hK
              periodic_d₁ := ?_
              periodic_d₂ := ?_
              fill := ?_ }⟩
    · intro p q
      exact exact_dual _ _ (vertical_exact hK _ _ _ _ _ _ _ _ _ _)
    · intro p q
      exact exact_dual _ _ (horizontal_exact hK _ _ _ _ _ _ _ _ _ _)
    · intro p q
      have hh := dual_horizontal_periodic hK p q (p + 1) q (p + 3) (q - 3) (p + 4) (q - 3)
          rfl rfl rfl rfl (by omega) rfl (by omega) rfl
      rw [dualPeriodTo_eq hK (p + 1) q (p + 4) (q - 3),
        dualPeriodTo_eq hK p q (p + 3) (q - 3)] at hh
      simpa [L, horizontal, reindexIso_hom, Category.assoc] using hh
    · intro p q
      have hh := dual_vertical_periodic hK p q p (q + 1) (p + 3) (q - 3) (p + 3) (q - 2)
          rfl rfl rfl rfl rfl (by omega) rfl (by omega)
      rw [dualPeriodTo_eq hK p (q + 1) (p + 3) (q - 2),
        dualPeriodTo_eq hK p q (p + 3) (q - 3)] at hh
      simpa [L, vertical, reindexIso_hom, Category.assoc] using hh
    · intro p q α β h
      have hh := dual_fill (k := k) (K := K) hK p q α β (by
        change (L.d₂ p q) α =
          (reindexIso L (p := (p - 1) + 1) (q := q + 1)
            (p' := p) (q' := q + 1) (by omega) rfl).hom ((L.d₁ (p - 1) (q + 1)) β)
        exact h)
      rw [dualPeriodTo_eq hK (p - 2) (q + 3) (p + 1) q] at hh
      simpa [L, horizontal, vertical, reindexIso_hom, ModuleCat.comp_apply] using hh

end Stacks.DerivedEquivalence

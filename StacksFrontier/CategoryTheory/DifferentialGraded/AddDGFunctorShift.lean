module

public import StacksFrontier.CategoryTheory.DifferentialGraded.AddDGFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaShiftIso

/-!
# Every additive functor of differential graded categories commutes with the shift

Let `A` and `B` be differential graded categories satisfying axiom (B) and let `F : A ⟶ B` be an
additive functor of differential graded categories. Axiom (B) identifies a degree-`(k + n)`
morphism `x ⟶ y` with a degree-`k` morphism `x ⟶ y[n]`; in particular the identity of `x[n]`
is a canonical morphism `ε : x[n] ⟶ x` of degree `n` with an inverse `x ⟶ x[n]` of degree `-n`.
Applying `F` to `ε` and reading the result through axiom (B) for `B` gives a closed isomorphism
`F(x[n]) ≅ F(x)[n]` of degree zero, natural in `x` and compatible with both identifications. So
*every* such functor satisfies the hypothesis `DGCategory.AddDGFunctor.CommShiftBIso` of Tag 0FQF.

## Main definitions

* `DGCategory.ShiftAxiomB.unit` and `DGCategory.ShiftAxiomB.counit`: the canonical morphisms
  `x[n] ⟶ x` and `x ⟶ x[n]`, of degrees `n` and `-n`.
* `DGCategory.AddDGFunctor.commShiftBIso`: the closed isomorphism `F(x[n]) ≅ F(x)[n]`, as a
  `DGCategory.AddDGFunctor.CommShiftBIso`.
* `DGCategory.AddDGFunctor.commShift`: the induced commutation of `F` with the translations of the
  homotopy categories.

## Main results

* `DGCategory.AddDGFunctor.isTriangulated`: the induced functor on homotopy categories is
  triangulated.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u v u' v' w w'

/-! ### Heterogeneous equalities of homogeneous morphisms -/

section Heq

variable {R : Type w} [CommRing R] {C : DGCategory.{v, u} R}

/-- Composition respects heterogeneous equality of its arguments, across equal objects and
degrees. -/
theorem comp_heq_congr {x y z x' y' z' : C.Obj} {m n k m' n' k' : ℤ}
    (h : m + n = k) (h' : m' + n' = k') (hx : x = x') (hy : y = y') (hz : z = z')
    (hm : m = m') (hn : n = n')
    {g : C.Hom y z m} {g' : C.Hom y' z' m'} {f : C.Hom x y n} {f' : C.Hom x' y' n'}
    (hg : HEq g g') (hf : HEq f f') : HEq (C.comp h g f) (C.comp h' g' f') := by
  subst hx hy hz hm hn
  obtain rfl : k = k' := by omega
  cases hg; cases hf; rfl

/-- Composition only depends on the proof of the degree equation, up to heterogeneous equality. -/
private theorem comp_heq_degree {x y z : C.Obj} {m n k k' : ℤ} (h : m + n = k) (h' : m + n = k')
    {g : C.Hom y z m} {f : C.Hom x y n} : HEq (C.comp h g f) (C.comp h' g f) := by
  subst h h'; rfl

/-- The differential `d'` with a prescribed target degree vanishes iff `d` does. -/
private theorem d'_eq_zero_iff {x y : C.Obj} {m n : ℤ} (e : m + 1 = n) (f : C.Hom x y m) :
    C.d' e f = 0 ↔ C.d f = 0 := by
  subst e; rfl

/-- Composing with an identity on the left gives a morphism heterogeneously equal to the
original. -/
theorem id_comp_heq {x y : C.Obj} {n k : ℤ} (h : 0 + n = k) (f : C.Hom x y n) :
    HEq (C.comp h (C.id y) f) f := by
  obtain rfl : k = n := by omega
  exact heq_of_eq (C.id_comp f)

/-- Composing with an identity on the right gives a morphism heterogeneously equal to the
original. -/
theorem comp_id_heq {x y : C.Obj} {n k : ℤ} (h : n + 0 = k) (f : C.Hom x y n) :
    HEq (C.comp h f (C.id x)) f := by
  obtain rfl : k = n := by omega
  exact heq_of_eq (C.comp_id f)

/-- Associativity of composition as a heterogeneous equality, with independent degree equations. -/
theorem assoc_heq {w x y z : C.Obj} {l m n p q p' q' : ℤ} (h₁ : l + m = p) (h₂ : p + n = q)
    (h₃ : m + n = p') (h₄ : l + p' = q') (e : C.Hom y z l) (g : C.Hom x y m)
    (f : C.Hom w x n) :
    HEq (C.comp h₂ (C.comp h₁ e g) f) (C.comp h₄ e (C.comp h₃ g f)) := by
  obtain rfl : q' = q := by omega
  exact heq_of_eq (C.assoc h₃ h₄ h₁ h₂ e g f).symm

/-- Identities of equal objects are heterogeneously equal. -/
theorem id_heq {x x' : C.Obj} (h : x = x') : HEq (C.id x) (C.id x') := by
  subst h; rfl

/-- The differential respects heterogeneous equality. -/
theorem d_heq {x y x' y' : C.Obj} {n n' : ℤ} (hx : x = x') (hy : y = y') (hn : n = n')
    {f : C.Hom x y n} {f' : C.Hom x' y' n'} (hf : HEq f f') : HEq (C.d f) (C.d f') := by
  subst hx hy hn; cases hf; rfl

/-- The differential `d'` with a prescribed target degree is heterogeneously equal to `d`. -/
theorem d'_heq {x y : C.Obj} {m n : ℤ} (e : m + 1 = n) (f : C.Hom x y m) :
    HEq (C.d' e f) (C.d f) := by
  subst e; rfl

/-- Heterogeneously equal morphisms of the same Hom module are equal. -/
theorem eq_of_heq_hom {x y : C.Obj} {n : ℤ} {f g : C.Hom x y n} (h : HEq f g) : f = g :=
  eq_of_heq h

/-- Scalar multiplication by `(-1)^m` respects heterogeneous equality. -/
theorem neg_one_pow_smul_heq {x y x' y' : C.Obj} {n n' : ℤ} (hx : x = x') (hy : y = y')
    (hn : n = n') (m : ℕ) {f : C.Hom x y n} {f' : C.Hom x' y' n'} (hf : HEq f f') :
    HEq ((-1 : R) ^ m • f) ((-1 : R) ^ m • f') := by
  subst hx hy hn; cases hf; rfl

end Heq

/-! ### The canonical morphisms `x[n] ⟶ x` and `x ⟶ x[n]` -/

namespace ShiftAxiomB

variable {R : Type w} [CommRing R] {A : DGCategory.{v, u} R} (S : ShiftAxiomB A)

/-- The identification of axiom (B) respects heterogeneous equality. -/
theorem toShift_heq {n : ℤ} {x y x' y' : A.Obj} {k k' : ℤ} (hx : x = x') (hy : y = y')
    (hk : k = k') {f : A.Hom x y (k + n)} {f' : A.Hom x' y' (k' + n)} (hf : HEq f f') :
    HEq (S.toShift n x y k f) (S.toShift n x' y' k' f') := by
  subst hx hy hk; cases hf; rfl

/-- The inverse of the identification of axiom (B) respects heterogeneous equality. -/
theorem toShift_symm_heq {n : ℤ} {x y x' y' : A.Obj} {k k' : ℤ} (hx : x = x') (hy : y = y')
    (hk : k = k') {f : A.Hom x ((S.shiftFunctor n).obj y) k}
    {f' : A.Hom x' ((S.shiftFunctor n).obj y') k'} (hf : HEq f f') :
    HEq ((S.toShift n x y k).symm f) ((S.toShift n x' y' k').symm f') := by
  subst hx hy hk; cases hf; rfl

/-- The canonical morphism `x[n] ⟶ x` of degree `n`: the identity of `x[n]`, read through the
identification of axiom (B). -/
def unit (n : ℤ) (x : A.Obj) : A.Hom ((S.shiftFunctor n).obj x) x (0 + n) :=
  (S.toShift n _ x 0).symm (A.id _)

/-- The canonical morphism `x ⟶ x[n]` of degree `-n`: the identity of `x`, read through the
identification of axiom (B). -/
def counit (n : ℤ) (x : A.Obj) : A.Hom x ((S.shiftFunctor n).obj x) (-n) :=
  S.toShift n x x (-n) ((neg_add_cancel n).symm ▸ A.id x)

omit S in
/-- The transported identity of `x` defining `counit` is heterogeneously equal to the identity. -/
theorem counit_heq (n : ℤ) (x : A.Obj) :
    HEq ((neg_add_cancel n).symm ▸ A.id x : A.Hom x x (-n + n)) (A.id x) := by
  generalize (neg_add_cancel n).symm = h
  revert h
  generalize -n + n = m
  intro h; subst h; rfl

/-- The identification of axiom (B) sends `unit n x` to the identity of `x[n]`. -/
theorem toShift_unit (n : ℤ) (x : A.Obj) : S.toShift n _ x 0 (S.unit n x) = A.id _ :=
  LinearEquiv.apply_symm_apply _ _

/-- **Composing with the canonical morphism undoes the identification of axiom (B).** -/
theorem unit_comp_toShift (n : ℤ) {w y : A.Obj} {k p : ℤ} (h : (0 + n) + k = p)
    (g : A.Hom w y (k + n)) :
    HEq (A.comp h (S.unit n y) (S.toShift n w y k g)) g := by
  have e := S.toShiftAxiomBIso.symm_toShift_comp_right n (show 0 + k = k by omega)
    (A.id ((S.shiftFunctor n).obj y)) (S.toShift n w y k g)
  rw [A.id_comp, LinearEquiv.symm_apply_apply] at e
  exact (comp_heq_degree _ _).trans (heq_of_eq e.symm)

/-- The identification of axiom (B) applied to a composite with the canonical morphism. -/
theorem toShift_comp_unit (n : ℤ) {w y : A.Obj} {k p : ℤ} (h : (0 + n) + k = p)
    (a : A.Hom w ((S.shiftFunctor n).obj y) k) :
    HEq (A.comp h (S.unit n y) a) ((S.toShift n w y k).symm a) := by
  have e := S.unit_comp_toShift n h ((S.toShift n w y k).symm a)
  rwa [LinearEquiv.apply_symm_apply] at e

/-- `ε ∘ η = 1`: the canonical morphisms compose to the identity of `x`. -/
theorem unit_comp_counit (n : ℤ) (x : A.Obj) (h : (0 + n) + -n = 0) :
    A.comp h (S.unit n x) (S.counit n x) = A.id x :=
  eq_of_heq ((S.unit_comp_toShift n h _).trans (counit_heq n x))

/-- `η ∘ ε = 1`: the canonical morphisms compose to the identity of `x[n]`. -/
theorem counit_comp_unit (n : ℤ) (x : A.Obj) (h : -n + (0 + n) = 0) :
    A.comp h (S.counit n x) (S.unit n x) = A.id _ := by
  have e := S.toShiftAxiomBIso.toShift_comp_right n
    ((neg_add_cancel n).symm ▸ A.id x : A.Hom x x (-n + n)) (S.unit n x)
  refine eq_of_heq ((comp_heq_degree h _).trans ((heq_of_eq e).symm.trans ?_))
  refine HEq.trans ?_ (heq_of_eq (S.toShift_unit n x))
  refine S.toShift_heq rfl rfl (by omega) ?_
  exact (comp_heq_congr _ (show 0 + (0 + n) = 0 + n by omega) rfl rfl rfl (by omega) rfl
    (counit_heq n x) HEq.rfl).trans (id_comp_heq _ _)

/-- The identification of axiom (B) sends closed morphisms to closed morphisms. -/
private theorem d_toShift_eq_zero_of_d {S : ShiftAxiomB A} (n : ℤ) {x y : A.Obj} {k : ℤ}
    (f : A.Hom x y (k + n)) (hf : A.d f = 0) : A.d (S.toShift n x y k f) = 0 := by
  have e := S.toShift_d n x y k f
  rw [(d'_eq_zero_iff _ f).mpr hf, map_zero] at e
  rcases neg_one_pow_eq_or R n.natAbs with h1 | h1 <;> rw [h1] at e <;> simpa using e.symm

/-- The canonical morphism `x[n] ⟶ x` is closed. -/
theorem d_unit (n : ℤ) (x : A.Obj) : A.d (S.unit n x) = 0 := by
  have e := S.toShift_d n _ x 0 (S.unit n x)
  rw [S.toShift_unit, A.d_id, smul_zero] at e
  exact (d'_eq_zero_iff _ _).mp ((LinearEquiv.map_eq_zero_iff _).mp e)

/-- The canonical morphism `x ⟶ x[n]` is closed. -/
theorem d_counit (n : ℤ) (x : A.Obj) : A.d (S.counit n x) = 0 :=
  d_toShift_eq_zero_of_d n _ (by
    have key : ∀ (m : ℤ) (h : 0 = m), A.d (h ▸ A.id x : A.Hom x x m) = 0 := by
      rintro m rfl; exact A.d_id x
    exact key _ _)

/-- **The canonical morphisms are natural**, up to the Koszul sign of the shift of a morphism:
`ε_y ∘ f[n] = (-1)^{nk} f ∘ ε_x`. -/
theorem unit_comp_shiftMap (n : ℤ) {x y : A.Obj} {k p : ℤ} (f : A.Hom x y k)
    (h : (0 + n) + k = p) (h' : k + (0 + n) = p) :
    A.comp h (S.unit n y) ((S.shiftFunctor n).map f) =
      (-1 : R) ^ (n * k).natAbs • A.comp h' f (S.unit n x) := by
  have e₁ := S.toShiftAxiomBIso.symm_toShift_comp_right n (show 0 + k = k by omega)
    (A.id ((S.shiftFunctor n).obj y)) ((S.shiftFunctor n).map f)
  have e₂ := S.toShiftAxiomBIso.symm_toShift_comp_left n (show k + 0 = k by omega) f
    (A.id ((S.shiftFunctor n).obj x))
  rw [A.id_comp] at e₁
  rw [A.comp_id] at e₂
  rw [e₂] at e₁
  have e₃ := heq_of_eq e₁
  refine eq_of_heq ((comp_heq_degree _ _).trans
    (e₃.symm.trans ?_))
  exact neg_one_pow_smul_heq rfl rfl (by omega) _
    (comp_heq_degree _ _)

end ShiftAxiomB

/-! ### The comparison `F(x[n]) ≅ F(x)[n]` -/

namespace AddDGFunctor

variable {R₁ : Type w} [CommRing R₁] {R₂ : Type w'} [CommRing R₂]
  {A : DGCategory.{v, u} R₁} {B : DGCategory.{v', u'} R₂} (F : AddDGFunctor A B)

/-- An additive functor of differential graded categories respects heterogeneous equality. -/
theorem map_heq {x y x' y' : A.Obj} {n n' : ℤ} (hx : x = x') (hy : y = y') (hn : n = n')
    {f : A.Hom x y n} {f' : A.Hom x' y' n'} (hf : HEq f f') : HEq (F.map f) (F.map f') := by
  subst hx hy hn; cases hf; rfl

/-- An additive functor of differential graded categories preserves negation. -/
theorem map_neg {x y : A.Obj} {n : ℤ} (f : A.Hom x y n) : F.map (-f) = -F.map f :=
  eq_neg_of_add_eq_zero_left (by rw [← F.map_add, neg_add_cancel, F.map_zero])

/-- An additive functor of differential graded categories commutes with scalar
multiplication by `(-1)^m`. -/
theorem map_neg_one_pow_smul {x y : A.Obj} {n : ℤ} (m : ℕ) (f : A.Hom x y n) :
    F.map ((-1 : R₁) ^ m • f) = (-1 : R₂) ^ m • F.map f := by
  rcases Nat.even_or_odd m with hm | hm
  · rw [hm.neg_one_pow, hm.neg_one_pow, one_smul, one_smul]
  · rw [hm.neg_one_pow, hm.neg_one_pow, neg_one_smul, neg_one_smul, F.map_neg]

variable (SA : ShiftAxiomB A) (SB : ShiftAxiomB B)

/-- The identification of axiom (B) sends closed morphisms to closed morphisms. -/
theorem _root_.DGCategory.ShiftAxiomB.d_toShift_eq_zero (S : ShiftAxiomB B) (n : ℤ)
    {x y : B.Obj} {k : ℤ} (f : B.Hom x y (k + n)) (hf : B.d f = 0) :
    B.d (S.toShift n x y k f) = 0 :=
  ShiftAxiomB.d_toShift_eq_zero_of_d n f hf

/-- The comparison `F(x[n]) ⟶ F(x)[n]`: `F` of the canonical morphism `x[n] ⟶ x`, read through
the identification of axiom (B) for `B`. -/
def shiftHom (n : ℤ) (x : A.Obj) :
    B.Cocycle (F.obj ((SA.shiftFunctor n).obj x)) ((SB.shiftFunctor n).obj (F.obj x)) :=
  ⟨SB.toShift n _ _ 0 (F.map (SA.unit n x)), SB.d_toShift_eq_zero n _
    (by rw [← F.map_d, SA.d_unit, F.map_zero])⟩

/-- The inverse comparison `F(x)[n] ⟶ F(x[n])`: `F` of the canonical morphism `x ⟶ x[n]`
composed with the canonical morphism `F(x)[n] ⟶ F(x)`. -/
def shiftInv (n : ℤ) (x : A.Obj) :
    B.Cocycle ((SB.shiftFunctor n).obj (F.obj x)) (F.obj ((SA.shiftFunctor n).obj x)) :=
  ⟨B.comp (show -n + (0 + n) = 0 by omega) (F.map (SA.counit n x)) (SB.unit n (F.obj x)), by
    rw [B.leibniz, ← F.map_d, SA.d_counit, F.map_zero, SB.d_unit, B.comp_zero_left,
      B.comp_zero_right, smul_zero, add_zero]⟩

/-- The comparison `shiftHom` followed by `shiftInv` is the identity of `F(x[n])`. -/
theorem shiftInv_comp_shiftHom (n : ℤ) (x : A.Obj) :
    B.compCocycle (F.shiftInv SA SB n x) (F.shiftHom SA SB n x) =
      ⟨B.id (F.obj ((SA.shiftFunctor n).obj x)), B.d_id _⟩ := by
  refine Subtype.ext (eq_of_heq ?_)
  change HEq (B.comp _ (B.comp _ (F.map (SA.counit n x)) (SB.unit n (F.obj x)))
    (SB.toShift n _ _ 0 (F.map (SA.unit n x)))) _
  refine (assoc_heq _ _ (show (0 + n) + 0 = 0 + n by omega) (show -n + (0 + n) = 0 by omega)
    _ _ _).trans ?_
  refine (comp_heq_congr _ (show -n + (0 + n) = 0 by omega) rfl rfl rfl rfl rfl HEq.rfl
    (SB.unit_comp_toShift n _ _)).trans ?_
  rw [← F.map_comp, SA.counit_comp_unit, F.map_id]

/-- The comparison `shiftInv` followed by `shiftHom` is the identity of `F(x)[n]`. -/
theorem shiftHom_comp_shiftInv (n : ℤ) (x : A.Obj) :
    B.compCocycle (F.shiftHom SA SB n x) (F.shiftInv SA SB n x) =
      ⟨B.id ((SB.shiftFunctor n).obj (F.obj x)), B.d_id _⟩ := by
  refine Subtype.ext (eq_of_heq ?_)
  change HEq (B.comp _ (SB.toShift n _ _ 0 (F.map (SA.unit n x)))
    (B.comp _ (F.map (SA.counit n x)) (SB.unit n (F.obj x)))) _
  refine (assoc_heq (show 0 + -n = 0 + -n from rfl) (show (0 + -n) + (0 + n) = 0 by omega)
    _ _ _ _ _).symm.trans ?_
  have e := SB.toShiftAxiomBIso.toShift_comp_right n (F.map (SA.unit n x))
    (F.map (SA.counit n x))
  rw [← F.map_comp] at e
  have hu : HEq (A.comp (show (0 + n) + -n = (0 + -n) + n by omega) (SA.unit n x)
      (SA.counit n x)) (A.id x) :=
    (comp_heq_congr _ (show (0 + n) + -n = 0 by omega) rfl rfl rfl rfl rfl HEq.rfl
      HEq.rfl).trans (heq_of_eq (SA.unit_comp_counit n x _))
  have e₂ : HEq (B.comp (show 0 + -n = 0 + -n from rfl)
      (SB.toShift n _ _ 0 (F.map (SA.unit n x))) (F.map (SA.counit n x)))
      (SB.counit n (F.obj x)) :=
    (heq_of_eq e.symm).trans (SB.toShift_heq rfl rfl (by omega)
      ((F.map_heq rfl rfl (by omega) hu).trans
        ((heq_of_eq (F.map_id x)).trans (ShiftAxiomB.counit_heq n (F.obj x)).symm)))
  refine (comp_heq_congr _ (show -n + (0 + n) = 0 by omega) rfl rfl rfl (by omega) rfl e₂
    HEq.rfl).trans ?_
  rw [SB.counit_comp_unit]

/-- The comparison `shiftHom` is natural. -/
theorem shiftHom_naturality (n : ℤ) {x y : A.Obj} {k : ℤ} (f : A.Hom x y k) :
    B.comp (zero_add k) (F.shiftHom SA SB n y).1 (F.map ((SA.shiftFunctor n).map f)) =
      B.comp (add_zero k) ((SB.shiftFunctor n).map (F.map f)) (F.shiftHom SA SB n x).1 := by
  change B.comp _ (SB.toShift n _ _ 0 (F.map (SA.unit n y))) _ =
    B.comp _ _ (SB.toShift n _ _ 0 (F.map (SA.unit n x)))
  have e₁ := SB.toShiftAxiomBIso.toShift_comp_right n (F.map (SA.unit n y))
    (F.map ((SA.shiftFunctor n).map f))
  have e₂ := SB.toShiftAxiomBIso.toShift_comp_left n (F.map f) (F.map (SA.unit n x))
  have e₃ : B.comp (show (0 + n) + k = (0 + k) + n by omega) (F.map (SA.unit n y))
      (F.map ((SA.shiftFunctor n).map f)) =
      (-1 : R₂) ^ (n * k).natAbs • B.comp (show k + (0 + n) = (0 + k) + n by omega)
        (F.map f) (F.map (SA.unit n x)) := by
    rw [← F.map_comp, ← F.map_comp, ← F.map_neg_one_pow_smul,
      SA.unit_comp_shiftMap n f _ (show k + (0 + n) = (0 + k) + n by omega)]
  rw [e₃, _root_.map_smul] at e₁
  have hm : HEq (SB.toShift n (F.obj ((SA.shiftFunctor n).obj x)) (F.obj y) (0 + k)
      (B.comp (show k + (0 + n) = (0 + k) + n by omega) (F.map f) (F.map (SA.unit n x))))
      (SB.toShift n (F.obj ((SA.shiftFunctor n).obj x)) (F.obj y) (k + 0)
      (B.comp (show k + (0 + n) = (k + 0) + n by omega) (F.map f) (F.map (SA.unit n x)))) :=
    SB.toShift_heq rfl rfl (by omega) (comp_heq_degree _ _)
  refine eq_of_heq ((comp_heq_degree _ _).trans
    ((heq_of_eq e₁).symm.trans ?_))
  refine (neg_one_pow_smul_heq rfl rfl (by omega) _ (hm.trans (heq_of_eq e₂))).trans ?_
  rw [smul_smul, RightModule.neg_one_pow_natAbs_mul_self, one_smul]
  exact comp_heq_degree _ _

/-- The comparison `shiftHom` carries the identification of axiom (B) of `A` to that of `B`. -/
theorem shiftHom_toShift (n : ℤ) (x y : A.Obj) (k : ℤ) (f : A.Hom x y (k + n)) :
    B.comp (zero_add k) (F.shiftHom SA SB n y).1 (F.map (SA.toShift n x y k f)) =
      SB.toShift n (F.obj x) (F.obj y) k (F.map f) := by
  change B.comp _ (SB.toShift n _ _ 0 (F.map (SA.unit n y))) _ = _
  have e := SB.toShiftAxiomBIso.toShift_comp_right n (F.map (SA.unit n y))
    (F.map (SA.toShift n x y k f))
  rw [← F.map_comp] at e
  refine eq_of_heq ((comp_heq_degree _ _).trans
    ((heq_of_eq e).symm.trans ?_))
  exact SB.toShift_heq rfl rfl (by omega)
    (F.map_heq rfl rfl (by omega) (SA.unit_comp_toShift n _ f))

/-- **Every additive functor of differential graded categories commutes with the shift up to a
closed isomorphism**, in the form `DGCategory.AddDGFunctor.CommShiftBIso` of Tag 0FQF. -/
def commShiftBIso : F.CommShiftBIso SA.toShiftAxiomBIso SB.toShiftAxiomBIso where
  hom n x := F.shiftHom SA SB n x
  inv n x := F.shiftInv SA SB n x
  hom_inv_id n x := F.shiftInv_comp_shiftHom SA SB n x
  inv_hom_id n x := F.shiftHom_comp_shiftInv SA SB n x
  map n _ _ _ f := F.shiftHom_naturality SA SB n f
  toShift n x y k f := F.shiftHom_toShift SA SB n x y k f

/-! ### Coherence of the comparison -/

/-- The canonical morphisms `x[n] ⟶ x` of axiom (B) are *coherent*: the one for the shift by `0`
is the identity, and the one for `a + b` is the composite of those for `a` and for `b`. This is a
property of the identifications of axiom (B) — which axiom (B) itself does not pin down — and it
is what makes the comparisons `F(x[n]) ≅ F(x)[n]` compatible with the coherence isomorphisms of
the translations. -/
structure _root_.DGCategory.ShiftAxiomB.UnitCoherent {C : DGCategory.{v, u} R₁}
    (S : ShiftAxiomB C) : Prop where
  /-- The canonical morphism for the shift by `0` is the identity. -/
  zero : ∀ x : C.Obj, HEq (S.unit 0 x) (C.id x)
  /-- The canonical morphism for `a + b` is the composite of those for `a` and for `b`. -/
  add : ∀ (a b : ℤ) (x : C.Obj), HEq (S.unit (a + b) x)
    (C.comp (show (0 + a) + (0 + b) = 0 + (a + b) by omega) (S.unit a x)
      (S.unit b ((S.shiftFunctor a).obj x)))

/-- Two degree-zero morphisms into `y[n]` are heterogeneously equal when their composites with
the canonical morphism `y[n] ⟶ y` are. -/
theorem _root_.DGCategory.ShiftAxiomB.heq_of_unit_comp_heq {C : DGCategory.{v, u} R₁}
    (S : ShiftAxiomB C) (n : ℤ) {W W' y T : C.Obj} (hT : (S.shiftFunctor n).obj y = T)
    (g₁ : C.Hom W ((S.shiftFunctor n).obj y) 0) (g₂ : C.Hom W' T 0) (hW : W = W')
    (u' : C.Hom T y (0 + n)) (hu : HEq (S.unit n y) u') (h₁ : (0 + n) + 0 = 0 + n)
    (h : HEq (C.comp h₁ (S.unit n y) g₁) (C.comp h₁ u' g₂)) : HEq g₁ g₂ := by
  subst hT hW
  obtain rfl := eq_of_heq hu
  have e₁ := S.toShift_comp_unit n h₁ g₁
  have e₂ := S.toShift_comp_unit n h₁ g₂
  exact heq_of_eq ((S.toShift n W y 0).symm.injective (eq_of_heq (e₁.symm.trans (h.trans e₂))))

variable {SA SB}

/-- For coherent canonical morphisms, the comparison for the shift by `0` is the identity. -/
theorem shiftHom_zero_heq (hA : SA.UnitCoherent) (hB : SB.UnitCoherent) (x : A.Obj) :
    HEq (F.shiftHom SA SB 0 x).1 (B.id (F.obj x)) := by
  change HEq (SB.toShift 0 _ _ 0 (F.map (SA.unit 0 x))) _
  have h₁ : HEq (F.map (SA.unit 0 x)) (SB.unit 0 (F.obj x)) :=
    ((F.map_heq (SA.zero_obj x) rfl (by omega) (hA.zero x)).trans
      (heq_of_eq (F.map_id x))).trans (hB.zero (F.obj x)).symm
  refine (SB.toShift_heq ((congrArg F.obj (SA.zero_obj x)).trans (SB.zero_obj _).symm) rfl rfl
    h₁).trans ?_
  rw [SB.toShift_unit]
  exact id_heq (SB.zero_obj _)

/-- For coherent canonical morphisms, the comparison for `a + b` is the composite of the
comparisons for `a` and for `b`. -/
theorem shiftHom_add_heq (hA : SA.UnitCoherent) (hB : SB.UnitCoherent) (a b : ℤ) (x : A.Obj) :
    HEq (F.shiftHom SA SB (a + b) x).1
      (B.comp (show (0 : ℤ) + 0 = 0 from rfl) ((SB.shiftFunctor b).map (F.shiftHom SA SB a x).1)
        (F.shiftHom SA SB b ((SA.shiftFunctor a).obj x)).1) := by
  have hT : (SB.shiftFunctor (a + b)).obj (F.obj x) =
      (SB.shiftFunctor b).obj ((SB.shiftFunctor a).obj (F.obj x)) := by
    rw [add_comm a b]; exact SB.add_obj b a _
  have hW : F.obj ((SA.shiftFunctor (a + b)).obj x) =
      F.obj ((SA.shiftFunctor b).obj ((SA.shiftFunctor a).obj x)) := by
    rw [add_comm a b]; exact congrArg F.obj (SA.add_obj b a x)
  refine SB.heq_of_unit_comp_heq (a + b) hT _ _ hW _ (hB.add a b (F.obj x))
    (show (0 + (a + b)) + 0 = 0 + (a + b) by omega) ?_
  refine (SB.unit_comp_toShift (a + b) _ _).trans ?_
  set sa := (F.shiftHom SA SB a x).1
  set sb := (F.shiftHom SA SB b ((SA.shiftFunctor a).obj x)).1
  have e₁ : HEq (B.comp (show (0 + b) + 0 = 0 + b by omega)
      (SB.unit b ((SB.shiftFunctor a).obj (F.obj x)))
      (B.comp (show (0 : ℤ) + 0 = 0 from rfl) ((SB.shiftFunctor b).map sa) sb))
      (B.comp (show 0 + (0 + b) = 0 + b by omega) sa
        (F.map (SA.unit b ((SA.shiftFunctor a).obj x)))) := by
    refine (assoc_heq (show (0 + b) + 0 = 0 + b by omega) (show (0 + b) + 0 = 0 + b by omega)
      _ _ _ _ _).symm.trans ?_
    rw [SB.unit_comp_shiftMap b sa (show (0 + b) + 0 = 0 + b by omega)
      (show 0 + (0 + b) = 0 + b by omega)]
    simp only [mul_zero, Int.natAbs_zero, pow_zero, one_smul]
    refine (assoc_heq _ _ (show (0 + b) + 0 = 0 + b by omega)
      (show 0 + (0 + b) = 0 + b by omega) _ _ _).trans ?_
    exact comp_heq_congr _ _ rfl rfl rfl rfl rfl HEq.rfl (SB.unit_comp_toShift b _ _)
  have e₂ : HEq (B.comp (show (0 + a) + (0 + b) = 0 + (a + b) by omega)
      (SB.unit a (F.obj x)) (B.comp (show 0 + (0 + b) = 0 + b by omega) sa
        (F.map (SA.unit b ((SA.shiftFunctor a).obj x)))))
      (F.map (SA.unit (a + b) x)) := by
    refine (assoc_heq (show (0 + a) + 0 = 0 + a by omega)
      (show (0 + a) + (0 + b) = 0 + (a + b) by omega) _ _ _ _ _).symm.trans ?_
    refine (comp_heq_congr _ (show (0 + a) + (0 + b) = 0 + (a + b) by omega) rfl rfl rfl
      rfl rfl (SB.unit_comp_toShift a _ _) HEq.rfl).trans ?_
    rw [← F.map_comp]
    have hX : (SA.shiftFunctor b).obj ((SA.shiftFunctor a).obj x) =
        (SA.shiftFunctor (a + b)).obj x := by
      rw [add_comm a b]; exact (SA.add_obj b a x).symm
    exact F.map_heq hX rfl (by omega) (hA.add a b x).symm
  refine HEq.trans ?_ ((assoc_heq (show (0 + a) + (0 + b) = 0 + (a + b) by omega)
    (show (0 + (a + b)) + 0 = 0 + (a + b) by omega) (show (0 + b) + 0 = 0 + b by omega)
    (show (0 + a) + (0 + b) = 0 + (a + b) by omega) _ _ _).symm)
  refine HEq.trans ?_ (comp_heq_congr (show (0 + a) + (0 + b) = 0 + (a + b) by omega)
    (show (0 + a) + (0 + b) = 0 + (a + b) by omega) rfl rfl rfl rfl rfl
    (HEq.refl (SB.unit a (F.obj x))) e₁).symm
  exact e₂.symm

/-- The comparison `kHom` at equal objects, conjugated by the identifying `eqToHom`s. -/
theorem kHom_congr (hF : F.CommShiftBIso SA.toShiftAxiomBIso SB.toShiftAxiomBIso) (n : ℤ)
    {x₁ x₂ : A.K} (h : x₁ = x₂) :
    hF.kHom n x₁ = eqToHom (by rw [h]) ≫ hF.kHom n x₂ ≫ eqToHom (by rw [h]) := by
  subst h; simp

variable (SA SB)

/-- **The comparison in degree `0` is the canonical one**, for strict translations and coherent
canonical morphisms. -/
theorem kIso_zero (hA : SA.IsStrictKShift) (hB : SB.IsStrictKShift)
    (hcA : SA.UnitCoherent) (hcB : SB.UnitCoherent) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    (F.commShiftBIso SA SB).kIso 0 = Functor.CommShift.isoZero F.onK ℤ := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  obtain ⟨hA0, hAeq⟩ := hA.1
  obtain ⟨hB0, hBeq⟩ := hB.1
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  have h : F.onK.obj ((SA.shiftFunctor 0).onK.obj x) = F.onK.obj x :=
    congrArg F.obj (SA.zero_obj x)
  have h' : (SB.shiftFunctor 0).onK.obj (F.onK.obj x) = F.onK.obj x := SB.zero_obj _
  have hk := (conj_eqToHom_iff_heq ((F.commShiftBIso SA SB).kHom 0 x) (𝟙 (F.onK.obj x))
    h h').mpr (homotopyClass_heq _ h h' (F.shiftHom_zero_heq hcA hcB x))
  rw [CommShiftBIso.kIso_hom_app, Functor.CommShift.isoZero_hom_app, hAeq, hBeq, hk]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, Category.id_comp,
    eqToHom_trans]

/-- **The comparisons are additive in the degree**, for strict translations and coherent
canonical morphisms. -/
theorem kIso_add (hA : SA.IsStrictKShift) (hB : SB.IsStrictKShift)
    (hcA : SA.UnitCoherent) (hcB : SB.UnitCoherent) (a b : ℤ) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    (F.commShiftBIso SA SB).kIso (a + b) =
      Functor.CommShift.isoAdd ((F.commShiftBIso SA SB).kIso a)
        ((F.commShiftBIso SA SB).kIso b) := by
  let : HasShift A.K ℤ := SA.kShift
  let : HasShift B.K ℤ := SB.kShift
  obtain ⟨hAab, hAeq⟩ := hA.2 a b
  obtain ⟨hBab, hBeq⟩ := hB.2 a b
  set hF := F.commShiftBIso SA SB
  refine Iso.ext (NatTrans.ext (funext fun x => ?_))
  have hx : (shiftFunctor A.K a).obj x = (SA.shiftFunctor a).onK.obj x :=
    Functor.congr_obj (SA.kShift_functor a) x
  have h : F.onK.obj ((SA.shiftFunctor (a + b)).onK.obj x) =
      F.onK.obj ((SA.shiftFunctor b).onK.obj ((SA.shiftFunctor a).onK.obj x)) := by
    change F.obj ((SA.shiftFunctor (a + b)).obj x) =
      F.obj ((SA.shiftFunctor b).obj ((SA.shiftFunctor a).obj x))
    rw [add_comm a b]; exact congrArg F.obj (SA.add_obj b a x)
  have h' : (SB.shiftFunctor (a + b)).onK.obj (F.onK.obj x) =
      (SB.shiftFunctor b).onK.obj ((SB.shiftFunctor a).onK.obj (F.onK.obj x)) := by
    change (SB.shiftFunctor (a + b)).obj (F.obj x) =
      (SB.shiftFunctor b).obj ((SB.shiftFunctor a).obj (F.obj x))
    rw [add_comm a b]; exact SB.add_obj b a _
  have hk := (conj_eqToHom_iff_heq (hF.kHom (a + b) x)
    (hF.kHom b ((SA.shiftFunctor a).onK.obj x) ≫ (SB.shiftFunctor b).onK.map (hF.kHom a x))
    h h').mpr (homotopyClass_heq _ h h' (F.shiftHom_add_heq hcA hcB a b x))
  rw [CommShiftBIso.kIso_hom_app, Functor.CommShift.isoAdd_hom_app, hAeq, hBeq,
    CommShiftBIso.kIso_hom_app, CommShiftBIso.kIso_hom_app,
    Functor.congr_hom (SB.kShift_functor b), hk, kHom_congr F hF b hx]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, Functor.map_comp,
    Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rw [eqToHom_refl, Category.id_comp]

/-- **An additive functor of differential graded categories commutes with the translations of
the homotopy categories**, for strict translations and coherent canonical morphisms of axiom (B),
the comparison isomorphisms being those of `DGCategory.AddDGFunctor.commShiftBIso`. -/
@[instance_reducible]
noncomputable def commShift (hA : SA.IsStrictKShift) (hB : SB.IsStrictKShift)
    (hcA : SA.UnitCoherent) (hcB : SB.UnitCoherent) :
    letI : HasShift A.K ℤ := SA.kShift
    letI : HasShift B.K ℤ := SB.kShift
    F.onK.CommShift ℤ :=
  letI : HasShift A.K ℤ := SA.kShift
  letI : HasShift B.K ℤ := SB.kShift
  { commShiftIso := (F.commShiftBIso SA SB).kIso
    commShiftIso_zero := F.kIso_zero SA SB hA hB hcA hcB
    commShiftIso_add := F.kIso_add SA SB hA hB hcA hcB }

/-- **Tag 0FQF for an additive functor of differential graded categories.** Let `A` and `B` be
differential graded categories satisfying axioms (A), (B) and (C), over two possibly different
rings, with strict translations and coherent canonical morphisms of axiom (B). Then every
additive functor `F : A ⟶ B` of differential graded categories induces an exact functor
`K(A) ⥤ K(B)` of triangulated categories. -/
theorem isTriangulated (CA : ConeSituation A) (CB : ConeSituation B)
    (hA : CA.shift.IsStrictKShift) (hB : CB.shift.IsStrictKShift)
    (hcA : CA.shift.UnitCoherent) (hcB : CB.shift.UnitCoherent) :
    letI : Preadditive A.K := homotopyPreadditive A
    letI : Limits.HasZeroObject A.K := homotopyHasZeroObject A CA
    letI : HasShift A.K ℤ := CA.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor A.K n).Additive := fun n => homotopyShiftAdditive A CA n
    letI : Pretriangulated A.K := homotopyPretriangulated A CA
    letI : Preadditive B.K := homotopyPreadditive B
    letI : Limits.HasZeroObject B.K := homotopyHasZeroObject B CB
    letI : HasShift B.K ℤ := CB.shift.kShift
    letI : ∀ n : ℤ, (shiftFunctor B.K n).Additive := fun n => homotopyShiftAdditive B CB n
    letI : Pretriangulated B.K := homotopyPretriangulated B CB
    letI : F.onK.CommShift ℤ := F.commShift CA.shift CB.shift hA hB hcA hcB
    F.onK.IsTriangulated :=
  CommShiftBIso.onK_isTriangulated CA CB (F.commShiftBIso CA.shift CB.shift)
    (F.commShift CA.shift CB.shift hA hB hcA hcB) rfl

end AddDGFunctor

end DGCategory

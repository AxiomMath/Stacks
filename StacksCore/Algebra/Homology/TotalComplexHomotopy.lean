module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # The total complex of homotopic maps of double complexes

Stacks 0G6A and 0G6B, second points: if two maps `f, g : A → B` of double complexes are
homotopic when the double complexes are regarded as complexes of complexes, then
`Tot(f), Tot(g) : Tot(A) → Tot(B)` are homotopic. In 0G6B the double complexes are complexes of
columns, which is Mathlib's `HomologicalComplex₂ C c₁ c₂`, and a homotopy is a `Homotopy f g`
there; the induced homotopy on the total complexes is `h^{p, q}` on the summand `A^{p, q}`. In
0G6A they are complexes of rows, which is the `flip`, a homotopy is a `Homotopy` between the
flipped maps, and the induced homotopy is `(-1)^p h^{p, q}`.

Mathlib has these statements only for the double complexes `F(K₁, K₂)` built from a bifunctor
(`HomologicalComplex.mapBifunctorMapHomotopy₁` and `₂`). Here they are proved for an arbitrary
bicomplex over any complex shapes with a `TotalComplexShape`:

* `totalMapHomotopy₁ h : Homotopy (total.map f c₁₂) (total.map g c₁₂)` from `h : Homotopy f g`;
  on the summand `(i₁, i₂)` it is `ε₁ (c₁.prev i₁, i₂) • h.hom i₁ (c₁.prev i₁)`, which for
  `ℤ`-cochain shapes is Stacks' unsigned `h^{p, q}` (`ιTotal_totalMapHomotopy₁_hom`);
* `totalMapHomotopy₂ h` from a homotopy `h` between the flipped maps, obtained from the first
  by transport along `totalFlipIso`, exactly as Mathlib derives `mapBifunctorMapHomotopy₂`; the
  transported sign is `ε₂ (i₁, c₂.prev i₂)`, Stacks' `(-1)^p`.

The proofs follow Mathlib's `Mathlib.Algebra.Homology.BifunctorHomotopy` with the bifunctor
stripped out. The other points of the two remarks remain open here: point 1, the compatibility
with shifts, is Mathlib's `totalShift₁Iso`/`totalShift₂Iso` (attributed in
`StacksCore.Algebra.Homology.TotalComplexShift`); point 3, that `h ↦ h'` is compatible with the
identification of self-homotopies with maps to the shift; and point 4, the comparison of the
connecting morphisms of a termwise split short exact sequence of double complexes and of its
total complexes.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] {I₁ I₂ I₁₂ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  {K L : HomologicalComplex₂ C c₁ c₂} {f g : K ⟶ L}

section first

variable (h : Homotopy f g)
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]
  [K.HasTotal c₁₂] [L.HasTotal c₁₂]

namespace totalMapHomotopy

/-- Auxiliary definition for `totalMapHomotopy₁`: the homotopy on the total complexes, given on
the summand `(i₁, i₂)` by `ε₁ (c₁.prev i₁, i₂) • h.hom i₁ (c₁.prev i₁)` into the summand
`(c₁.prev i₁, i₂)`. -/
noncomputable def hom₁ (j j' : I₁₂) : (K.total c₁₂).X j ⟶ (L.total c₁₂).X j' :=
  K.totalDesc (fun i₁ i₂ _ => ComplexShape.ε₁ c₁ c₂ c₁₂ (c₁.prev i₁, i₂) •
    (h.hom i₁ (c₁.prev i₁)).f i₂ ≫ L.ιTotalOrZero c₁₂ (c₁.prev i₁) i₂ j')

@[reassoc]
lemma ιTotal_hom₁ (i₁ i₁' : I₁) (i₂ : I₂) (j j' : I₁₂)
    (hj : ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂) = j) (h' : c₁.prev i₁' = i₁) :
    K.ιTotal c₁₂ i₁' i₂ j hj ≫ hom₁ h c₁₂ j j' =
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) • (h.hom i₁' i₁).f i₂ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ j' := by
  subst h'
  simp [hom₁]

lemma zero₁ (j j' : I₁₂) (hj : ¬ c₁₂.Rel j' j) : hom₁ h c₁₂ j j' = 0 := by
  ext i₁ i₂ h'
  dsimp [hom₁]
  rw [comp_zero, ι_totalDesc]
  by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
  · rw [ιTotalOrZero_eq_zero, comp_zero, smul_zero]
    intro h₄
    apply hj
    rw [← h', ← h₄]
    exact ComplexShape.rel_π₁ c₂ c₁₂ h₃ i₂
  · rw [h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma comm₁_aux {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁') {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') (j : I₁₂)
    (hj : ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂) = j) :
    ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) • (h.hom i₁' i₁).f i₂ ≫ L.d₂ c₁₂ i₁ i₂ j =
      -K.d₂ c₁₂ i₁' i₂ (c₁₂.next j) ≫ hom₁ h c₁₂ (c₁₂.next j) j := by
  have hj' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ = j := by
    rw [← hj, ← ComplexShape.next_π₂ c₁ c₁₂ i₁ hi₂, ComplexShape.next_π₁ c₂ c₁₂ hi₁ i₂]
  rw [L.d₂_eq _ _ hi₂ _ hj',
    K.d₂_eq _ _ hi₂ _ (by rw [← c₁₂.next_eq' (ComplexShape.rel_π₂ c₁ c₁₂ i₁' hi₂), hj]),
    Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ιTotal_hom₁ _ _ _ _ _ _ _ _ (c₁.prev_eq' hi₁), ιTotalOrZero_eq _ _ _ _ _ hj',
    Linear.comp_units_smul, smul_smul, smul_smul, ComplexShape.ε₁_ε₂ c₁₂ hi₁ hi₂, neg_mul,
    Units.neg_smul, neg_inj, smul_left_cancel_iff, ← Category.assoc, ← Category.assoc,
    (h.hom i₁' i₁).comm]

lemma comm₁ (j : I₁₂) :
    (total.map f c₁₂).f j =
      (K.total c₁₂).d j (c₁₂.next j) ≫ hom₁ h c₁₂ (c₁₂.next j) j +
        hom₁ h c₁₂ j (c₁₂.prev j) ≫ (L.total c₁₂).d (c₁₂.prev j) j + (total.map g c₁₂).f j := by
  ext i₁ i₂ hij
  simp only [ιTotal_map, h.comm i₁, dNext_eq_dFrom_fromNext, HomologicalComplex.dFrom, fromNext,
    AddMonoidHom.mk'_apply, prevD_eq_toPrev_dTo, toPrev, HomologicalComplex.dTo,
    HomologicalComplex.add_f_apply,
    HomologicalComplex.comp_f, Preadditive.add_comp, Category.assoc, total_d,
    Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc, add_left_inj]
  have : ∀ {X Y : C} (a b c d e f : X ⟶ Y), a = c → b = e → f = -d →
      a + b = c + d + (e + f) := by rintro X Y a b _ d _ _ rfl rfl rfl; abel
  apply this
  · by_cases h₃ : c₁.Rel i₁ (c₁.next i₁)
    · rw [K.d₁_eq _ h₃ _ _ (by rw [← hij, ComplexShape.next_π₁ c₂ c₁₂ h₃]),
        Linear.units_smul_comp, Category.assoc, ιTotal_hom₁ _ _ i₁ _ _ _ _ _ (c₁.prev_eq' h₃),
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
        ιTotalOrZero_eq _ _ _ _ _ hij]
    · rw [K.shape _ _ h₃, HomologicalComplex.zero_f, zero_comp, K.d₁_eq_zero _ _ _ _ h₃,
        zero_comp]
  · rw [ιTotal_hom₁_assoc _ _ _ _ _ _ _ _ rfl]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [ιTotalOrZero_eq _ _ _ _ _ (by rw [← ComplexShape.prev_π₁ c₂ c₁₂ h₃, hij]),
        Linear.units_smul_comp, Category.assoc, ι_D₁, L.d₁_eq _ h₃ _ _ hij,
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
    · rw [h.zero _ _ h₃]
      simp only [HomologicalComplex.zero_f, zero_comp, smul_zero]
  · rw [ιTotal_hom₁_assoc _ _ _ _ _ _ _ _ rfl]
    by_cases h₃ : c₁.Rel (c₁.prev i₁) i₁
    · rw [Linear.units_smul_comp, Category.assoc,
        ιTotalOrZero_eq _ _ _ _ _ (by rw [← ComplexShape.prev_π₁ c₂ c₁₂ h₃, hij]), ι_D₂]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · exact comm₁_aux h c₁₂ h₃ h₄ j hij
      · rw [L.d₂_eq_zero _ _ _ _ h₄, comp_zero, smul_zero, K.d₂_eq_zero _ _ _ _ h₄, zero_comp,
          neg_zero]
    · rw [h.zero _ _ h₃]
      simp only [HomologicalComplex.zero_f, zero_comp, smul_zero, zero_eq_neg]
      by_cases h₄ : c₂.Rel i₂ (c₂.next i₂)
      · by_cases h₅ : c₁₂.Rel j (c₁₂.next j)
        · rw [K.d₂_eq _ _ h₄ _ (by rw [← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₄, hij]),
            Linear.units_smul_comp, Category.assoc, ιTotal_hom₁ _ _ _ _ _ _ _ _ rfl,
            h.zero _ _ h₃, HomologicalComplex.zero_f, zero_comp, smul_zero, comp_zero, smul_zero]
        · rw [zero₁ _ _ _ _ h₅, comp_zero]
      · rw [K.d₂_eq_zero _ _ _ _ h₄, zero_comp]

end totalMapHomotopy

open totalMapHomotopy in
/-- **Stacks 0G6B**, second point: a homotopy `h` between maps `f, g` of bicomplexes, regarded as
complexes of columns, induces a homotopy between `Tot(f)` and `Tot(g)`; on the summand
`(i₁, i₂)` it is `ε₁ (c₁.prev i₁, i₂) • h.hom i₁ (c₁.prev i₁)`, which for `ℤ`-cochain shapes is
the tag's `h^{p, q}` on `A^{p, q}`. -/
@[implicit_reducible, stacks 0G6B "point 2: `Tot` of homotopic maps of double complexes are
  homotopic; any shapes"]
noncomputable def totalMapHomotopy₁ : Homotopy (total.map f c₁₂) (total.map g c₁₂) where
  hom := hom₁ h c₁₂
  zero := zero₁ h c₁₂
  comm := comm₁ h c₁₂

/-- The homotopy `totalMapHomotopy₁ h` on the summand `(i₁', i₂)`: it is `h.hom i₁' i₁` into the
summand `(i₁, i₂)`, `i₁ = c₁.prev i₁'`, up to the sign `ε₁ (i₁, i₂)`; for `ℤ`-cochain shapes this
is Stacks 0G6B's `h'`, given by `h^{p, q}` on `A^{p, q}`. -/
@[reassoc, stacks 0G6B "the tag's `h'`: `h^{p, q}` on the summand `A^{p, q}`, times `ε₁`"]
lemma ιTotal_totalMapHomotopy₁_hom (i₁ i₁' : I₁) (i₂ : I₂) (j j' : I₁₂)
    (hj : ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂) = j) (h' : c₁.prev i₁' = i₁) :
    K.ιTotal c₁₂ i₁' i₂ j hj ≫ (totalMapHomotopy₁ h c₁₂).hom j j' =
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂) • (h.hom i₁' i₁).f i₂ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ j' :=
  totalMapHomotopy.ιTotal_hom₁ h c₁₂ i₁ i₁' i₂ j j' hj h'

end first

section second

variable (h₂ : Homotopy ((flipFunctor C c₁ c₂).map f) ((flipFunctor C c₁ c₂).map g))
  (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]
  [K.HasTotal c₁₂] [L.HasTotal c₁₂]

namespace totalMapHomotopy

/-- The components of a homotopy between the flipped maps `f, g : K ⟶ L`, i.e. of a homotopy of
maps of complexes of rows, retyped as morphisms between the terms of `K` and `L`. -/
def rowHom (i₂ i₂' : I₂) (i₁ : I₁) : (K.X i₁).X i₂ ⟶ (L.X i₁).X i₂' := (h₂.hom i₂ i₂').f i₁

attribute [local implicit_reducible] HomologicalComplex₂.flipFunctor HomologicalComplex₂.flip

lemma rowHom_zero (i₂ i₂' : I₂) (i₁ : I₁) (hi : ¬ c₂.Rel i₂' i₂) : rowHom h₂ i₂ i₂' i₁ = 0 := by
  dsimp only [rowHom]
  rw [h₂.zero _ _ hi, HomologicalComplex.zero_f]

@[reassoc]
lemma rowHom_comm (i₂ i₂' : I₂) (i₁ i₁' : I₁) :
    rowHom h₂ i₂ i₂' i₁ ≫ (L.d i₁ i₁').f i₂' = (K.d i₁ i₁').f i₂ ≫ rowHom h₂ i₂ i₂' i₁' :=
  (h₂.hom i₂ i₂').comm i₁ i₁'

lemma rowHom_comm' (i₁ : I₁) (i₂ : I₂) :
    (f.f i₁).f i₂ = (K.X i₁).d i₂ (c₂.next i₂) ≫ rowHom h₂ (c₂.next i₂) i₂ i₁ +
      rowHom h₂ i₂ (c₂.prev i₂) i₁ ≫ (L.X i₁).d (c₂.prev i₂) i₂ + (g.f i₁).f i₂ :=
  congrArg (fun ψ => ψ.f i₁) (h₂.comm i₂)

/-- Auxiliary definition for `totalMapHomotopy₂`: the homotopy on the total complexes, given on
the summand `(i₁, i₂)` by `ε₂ (i₁, c₂.prev i₂) • rowHom h₂ i₂ (c₂.prev i₂) i₁` into the summand
`(i₁, c₂.prev i₂)`. -/
noncomputable def hom₂ (j j' : I₁₂) : (K.total c₁₂).X j ⟶ (L.total c₁₂).X j' :=
  K.totalDesc (fun i₁ i₂ _ => ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, c₂.prev i₂) •
    rowHom h₂ i₂ (c₂.prev i₂) i₁ ≫ L.ιTotalOrZero c₁₂ i₁ (c₂.prev i₂) j')

@[reassoc]
lemma ιTotal_hom₂ (i₁ : I₁) (i₂ i₂' : I₂) (j j' : I₁₂)
    (hj : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂') = j) (h' : c₂.prev i₂' = i₂) :
    K.ιTotal c₁₂ i₁ i₂' j hj ≫ hom₂ h₂ c₁₂ j j' =
      ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) • rowHom h₂ i₂' i₂ i₁ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ j' := by
  subst h'
  simp [hom₂]

lemma zero₂ (j j' : I₁₂) (hj : ¬ c₁₂.Rel j' j) : hom₂ h₂ c₁₂ j j' = 0 := by
  ext i₁ i₂ h'
  dsimp [hom₂]
  rw [comp_zero, ι_totalDesc]
  by_cases h₃ : c₂.Rel (c₂.prev i₂) i₂
  · rw [ιTotalOrZero_eq_zero, comp_zero, smul_zero]
    intro h₄
    apply hj
    rw [← h', ← h₄]
    exact ComplexShape.rel_π₂ _ _ _ h₃
  · rw [rowHom_zero _ _ _ _ h₃, zero_comp, smul_zero]

lemma comm₂_aux {i₂ i₂' : I₂} (hi₂ : c₂.Rel i₂ i₂') {i₁ i₁' : I₁} (hi₁ : c₁.Rel i₁ i₁') (j : I₁₂)
    (hj : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂') = j) :
    ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) • rowHom h₂ i₂' i₂ i₁ ≫ L.d₁ c₁₂ i₁ i₂ j =
      -K.d₁ c₁₂ i₁ i₂' (c₁₂.next j) ≫ hom₂ h₂ c₁₂ (c₁₂.next j) j := by
  have hj' : ComplexShape.π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ = j := by
    rw [← hj, ← ComplexShape.next_π₁ c₂ c₁₂ hi₁ i₂, ComplexShape.next_π₂ c₁ c₁₂ i₁ hi₂]
  rw [L.d₁_eq _ hi₁ _ _ hj', K.d₁_eq _ hi₁ _ _ (by
    rw [← c₁₂.next_eq' (ComplexShape.rel_π₁ c₂ c₁₂ hi₁ i₂'), hj]),
    Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ιTotal_hom₂ _ _ _ _ _ _ _ _ (c₂.prev_eq' hi₂), ιTotalOrZero_eq _ _ _ _ _ hj',
    Linear.comp_units_smul, smul_smul, smul_smul, mul_comm (ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)),
    ComplexShape.ε₁_ε₂ c₁₂ hi₁ hi₂, neg_mul, mul_comm, Units.neg_smul, neg_inj,
    smul_left_cancel_iff, ← Category.assoc, ← Category.assoc, rowHom_comm]


lemma comm₂ (j : I₁₂) :
    (total.map f c₁₂).f j =
      (K.total c₁₂).d j (c₁₂.next j) ≫ hom₂ h₂ c₁₂ (c₁₂.next j) j +
        hom₂ h₂ c₁₂ j (c₁₂.prev j) ≫ (L.total c₁₂).d (c₁₂.prev j) j + (total.map g c₁₂).f j := by
  ext i₁ i₂ hij
  simp only [ιTotal_map, rowHom_comm' h₂ i₁ i₂, Preadditive.add_comp, Category.assoc, total_d,
    Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc, add_left_inj]
  have : ∀ {X Y : C} (a b c d e f : X ⟶ Y), a = d → b = f → e = -c →
      a + b = c + d + (e + f) := by rintro X Y a b c _ _ _ rfl rfl rfl; abel
  apply this
  · by_cases h₃ : c₂.Rel i₂ (c₂.next i₂)
    · rw [K.d₂_eq _ _ h₃ _ (by rw [← hij, ComplexShape.next_π₂ c₁ c₁₂ i₁ h₃]),
        Linear.units_smul_comp, Category.assoc, ιTotal_hom₂ _ _ _ i₂ _ _ _ _ (c₂.prev_eq' h₃),
        Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul,
        ιTotalOrZero_eq _ _ _ _ _ hij]
    · rw [(K.X i₁).shape _ _ h₃, zero_comp, K.d₂_eq_zero _ _ _ _ h₃, zero_comp]
  · rw [ιTotal_hom₂_assoc _ _ _ _ _ _ _ _ rfl]
    by_cases h₃ : c₂.Rel (c₂.prev i₂) i₂
    · simp [ιTotalOrZero_eq _ _ _ _ _ (by rw [← ComplexShape.prev_π₂ c₁ c₁₂ i₁ h₃, hij]),
        L.d₂_eq _ _ h₃ _ hij, smul_smul]
    · simp [rowHom_zero _ _ _ _ h₃]
  · rw [ιTotal_hom₂_assoc _ _ _ _ _ _ _ _ rfl]
    by_cases h₃ : c₂.Rel (c₂.prev i₂) i₂
    · rw [Linear.units_smul_comp, Category.assoc,
        ιTotalOrZero_eq _ _ _ _ _ (by rw [← ComplexShape.prev_π₂ c₁ c₁₂ i₁ h₃, hij]), ι_D₁]
      by_cases h₄ : c₁.Rel i₁ (c₁.next i₁)
      · exact comm₂_aux h₂ c₁₂ h₃ h₄ j hij
      · simp [L.d₁_eq_zero _ _ _ _ h₄, K.d₁_eq_zero _ _ _ _ h₄]
    · rw [rowHom_zero _ _ _ _ h₃]
      simp only [zero_comp, smul_zero, zero_eq_neg]
      by_cases h₄ : c₁.Rel i₁ (c₁.next i₁)
      · by_cases h₅ : c₁₂.Rel j (c₁₂.next j)
        · simp [K.d₁_eq _ h₄ _ _ (by rw [← ComplexShape.next_π₁ c₂ c₁₂ h₄ i₂, hij]),
            Linear.units_smul_comp, Category.assoc, ιTotal_hom₂ _ _ _ _ _ _ _ _ rfl,
            rowHom_zero _ _ _ _ h₃, zero_comp, smul_zero, comp_zero, smul_zero]
        · rw [zero₂ _ _ _ _ h₅, comp_zero]
      · simp_all [K.d₁_eq_zero]

end totalMapHomotopy

open totalMapHomotopy in
/-- **Stacks 0G6A**, second point: a homotopy between maps `f, g` of bicomplexes regarded as
complexes of rows, i.e. between the flipped maps, induces a homotopy between `Tot(f)` and `Tot(g)`;
on the summand `(i₁, i₂)` it is `ε₂ (i₁, c₂.prev i₂) • h.hom i₂ (c₂.prev i₂)`, which for
`ℤ`-cochain shapes is the tag's `(-1)^p h^{p, q}` on `A^{p, q}`. -/
@[implicit_reducible, stacks 0G6A "point 2: `Tot` of maps homotopic as complexes of rows are
  homotopic; any shapes"]
noncomputable def totalMapHomotopy₂ : Homotopy (total.map f c₁₂) (total.map g c₁₂) where
  hom := hom₂ h₂ c₁₂
  zero := zero₂ h₂ c₁₂
  comm := comm₂ h₂ c₁₂

/-- The homotopy `totalMapHomotopy₂ h₂` on the summand `(i₁, i₂')`: it is the component at `i₁`
of `h₂.hom i₂' i₂` into the summand `(i₁, i₂)`, `i₂ = c₂.prev i₂'`, up to the sign `ε₂ (i₁, i₂)`;
for `ℤ`-cochain shapes this is Stacks 0G6A's `h'`, given by `(-1)^p h^{p, q}` on `A^{p, q}`. -/
@[reassoc, stacks 0G6A "the tag's `h'`: `(-1)^p h^{p, q}` on the summand `A^{p, q}`, as `ε₂`"]
lemma ιTotal_totalMapHomotopy₂_hom (i₁ : I₁) (i₂ i₂' : I₂) (j j' : I₁₂)
    (hj : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂') = j) (h' : c₂.prev i₂' = i₂) :
    K.ιTotal c₁₂ i₁ i₂' j hj ≫ (totalMapHomotopy₂ h₂ c₁₂).hom j j' =
      ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂) • (h₂.hom i₂' i₂).f i₁ ≫ L.ιTotalOrZero c₁₂ i₁ i₂ j' :=
  totalMapHomotopy.ιTotal_hom₂ h₂ c₁₂ i₁ i₂ i₂' j j' hj h'

end second

end HomologicalComplex₂

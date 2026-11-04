module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.SegmentTriangle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.HomDoubleComplex
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.ExactRowsColumns
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Matress
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hom double complex of two distinguished triangles is a matress

The double complex of morphism groups between the three-periodic sequences of two distinguished
triangles satisfies the filling condition of axiom TR3: a commuting square extends one step
further along the diagonal, where it closes up with the diagonal periodicity. Together with the
exactness of its rows and columns and the compatibility of the periodicity with both
differentials, this makes it a matress.

## Main results

* `AlgebraicGeometry.HomDoubleComplexSetup.exists_fill` is the filling property: a commuting
  square between two three-periodic sequences extends one step further along the diagonal.
* `AlgebraicGeometry.HomDoubleComplexSetup.exists_fill'` is the same statement with the three
  degrees of the first sequence supplied separately, so that it can be read off at the degrees
  the matress structure uses.
* `AlgebraicGeometry.HomDoubleComplexSetup.homDoubleComplexMatress` is the matress structure.

## Implementation notes

The filling property is axiom TR3 applied to the two triangles of three consecutive steps, so
the proof is the transposition of the third commuting square of the resulting morphism of
triangles into the `[-1]`-shifted form in which the diagonal periodicity is stated. The matress
structure then only has to be read off at the degrees its fields use, which is what the primed
form of the filling property and the lemmas describing the differentials, the reindexing
isomorphism and the periodicity as functions are for.

## References

* [Stacks Project, Tag 0H8B](https://stacks.math.columbia.edu/tag/0H8B)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.HomDoubleComplexSetup

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Stacks 0H8B.** The filling property of the Hom double complex: a commuting square between
two three-periodic sequences of distinguished triangles extends one step further along the
diagonal, where it closes up with the periodicity identification. This is axiom TR3. -/
@[stacks 0H8B "the filling property of the Hom double complex, i.e. axiom TR3 in the form the \
remark states it"]
theorem exists_fill (K : HomDoubleComplexSetup (C := C)) (a q : ℤ)
    (α : triangleObject K.X a ⟶ triangleObject K.Y q)
    (β : triangleObject K.X (a + 1) ⟶ triangleObject K.Y (q + 1))
    (hαβ : triangleMap K.X a ≫ β = α ≫ triangleMap K.Y q) :
    ∃ γ : triangleObject K.X (a + 2) ⟶ triangleObject K.Y (q + 2),
      (triangleMap K.X (a + 1) ≫
          eqToHom (congrArg (triangleObject K.X) (show a + 1 + 1 = a + 2 by omega))) ≫ γ =
        β ≫ triangleMap K.Y (q + 1) ≫
          eqToHom (congrArg (triangleObject K.Y) (show q + 1 + 1 = q + 2 by omega)) ∧
      (triangleObjectPeriodicityIso K.X (a + 2)).hom ≫
          (γ ≫ triangleMap K.Y (q + 2) ≫
            eqToHom (congrArg (triangleObject K.Y)
              (show q + 2 + 1 = q + 3 by omega)))⟦(-1 : ℤ)⟧' ≫
          (triangleObjectPeriodicityIso K.Y (q + 3)).inv =
        -(triangleMap K.X (a + 2 - 3) ≫
          eqToHom (congrArg (triangleObject K.X) (show a + 2 - 3 + 1 = a by omega)) ≫ α ≫
          eqToHom (congrArg (triangleObject K.Y) (show q = q + 3 - 3 by omega))) := by
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : triangleObject K.X (a + 2) ⟶ triangleObject K.Y (q + 2),
      (triangleMap K.X (a + 1) ≫
          eqToHom (congrArg (triangleObject K.X) (show a + 1 + 1 = a + 2 by omega))) ≫ γ =
        β ≫ triangleMap K.Y (q + 1) ≫
          eqToHom (congrArg (triangleObject K.Y) (show q + 1 + 1 = q + 2 by omega)) ∧
      (triangleMap K.X (a + 2) ≫
          eqToHom (congrArg (triangleObject K.X) (show a + 2 + 1 = a + 3 by omega)) ≫
          (triangleObjectShiftIso K.X a).hom) ≫ α⟦(1 : ℤ)⟧' =
        γ ≫ triangleMap K.Y (q + 2) ≫
          eqToHom (congrArg (triangleObject K.Y) (show q + 2 + 1 = q + 3 by omega)) ≫
          (triangleObjectShiftIso K.Y q).hom :=
    complete_distinguished_triangle_morphism (segmentTriangle K.X a) (segmentTriangle K.Y q)
      (segmentTriangle_distinguished K.X K.X_distinguished a)
      (segmentTriangle_distinguished K.Y K.Y_distinguished q) α β hαβ
  refine ⟨γ, hγ₁, ?_⟩
  have hnat : (α⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app (triangleObject K.Y q) =
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app (triangleObject K.X a) ≫ α := by
    simpa using (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.naturality α
  have h2 := congrArg (fun k => k⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app (triangleObject K.Y q)) hγ₂
  simp only [Functor.map_comp, Category.assoc, eqToHom_map] at h2
  rw [hnat, reassoc_of% triangleObjectShiftIso_hom_shift,
    triangleObjectShiftIso_hom_shift] at h2
  have hper : (triangleObjectPeriodicityIso K.X (a + 2)).hom ≫
      (triangleMap K.X (a + 2))⟦(-1 : ℤ)⟧' =
      -(triangleMap K.X (a + 2 - 3) ≫
        eqToHom (congrArg (triangleObject K.X) (show a + 2 - 3 + 1 = a + 2 + 1 - 3 by omega)) ≫
        (triangleObjectPeriodicityIso K.X (a + 2 + 1)).hom) := by
    rw [triangleMap_comp_triangleObjectPeriodicityIso_hom K.X (a + 2)]
    simp
  have hc := triangleObjectPeriodicityIso_congr K.X (show a + 2 + 1 = a + 3 by omega)
  simp only [eqToHom_map] at hc
  apply (cancel_mono (eqToHom (congrArg (triangleObject K.Y)
    (show q + 3 - 3 = q by omega)))).1
  simp only [Functor.map_comp, Category.assoc, eqToHom_map]
  rw [← h2, reassoc_of% hper]
  simp only [Preadditive.neg_comp, Category.assoc]
  rw [reassoc_of% hc]
  simp

/-- The reindexing isomorphism of the Hom double complex conjugates a morphism by the
identifications of its source and target. -/
private lemma reindexIso_hom_fun (K : HomDoubleComplexSetup (C := C)) {p q p' q' : ℤ}
    (hp : p = p') (hq : q = q') :
    ⇑(ConcreteCategory.hom (HomologicalComplex₂.reindexIso (homDoubleComplex K) hp hq).hom) =
      fun x => eqToHom (congrArg (triangleObject K.X) (show -p' = -p by omega)) ≫ x ≫
        eqToHom (congrArg (triangleObject K.Y) hq) := by
  subst p'
  subst q'
  funext x
  simp only [HomologicalComplex₂.reindexIso, Iso.refl_hom, AddCommGrpCat.hom_id,
    AddMonoidHom.id_apply, eqToHom_refl, Category.id_comp]
  exact (Category.comp_id x).symm

/-- Transporting a term of the Hom double complex along an equality of its first index. -/
private lemma cast_term_left (K : HomDoubleComplexSetup (C := C)) {p p' q : ℤ} (hp : p = p')
    (x : K.term p q) :
    cast (congrArg (fun i => K.term i q) hp) x =
      eqToHom (congrArg (triangleObject K.X) (show -p' = -p by omega)) ≫ x := by
  subst p'
  simp

/-- Transporting a term of the Hom double complex along an equality of its second index. -/
private lemma cast_term_right (K : HomDoubleComplexSetup (C := C)) {p q q' : ℤ} (hq : q = q')
    (x : K.term p q) :
    cast (congrArg (K.term p) hq) x = x ≫ eqToHom (congrArg (triangleObject K.Y) hq) := by
  subst q'
  simp

/-- The horizontal differential of the Hom double complex, as a function. -/
private lemma homDoubleComplex_d₁_fun (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    ⇑(ConcreteCategory.hom ((homDoubleComplex K).d₁ p q)) =
      fun x => (triangleMap K.X (-(p + 1)) ≫
        eqToHom (congrArg (triangleObject K.X) (show -(p + 1) + 1 = -p by omega))) ≫ x := rfl

/-- The vertical differential of the Hom double complex, as a function. -/
private lemma homDoubleComplex_d₂_fun (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    ⇑(ConcreteCategory.hom ((homDoubleComplex K).d₂ p q)) =
      fun x => x ≫ triangleMap K.Y q := rfl

/-- The three-periodicity identification of the Hom double complex, as a function. -/
private lemma periodic_hom_fun (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    ⇑(ConcreteCategory.hom (AddEquiv.toAddCommGrpIso
        (X := (homDoubleComplex K).X p q) (Y := (homDoubleComplex K).X (p + 3) (q - 3))
        (diagonalPeriodicityEquiv K p q)).hom) = ⇑(diagonalPeriodicityEquiv K p q) := rfl

/-- The filling property, with the three degrees of the first sequence supplied separately. -/
theorem exists_fill' (K : HomDoubleComplexSetup (C := C)) (a a₁ a₂ a₃ q : ℤ)
    (ha₁ : a + 1 = a₁) (ha₂ : a + 2 = a₂) (ha₃ : a + 2 - 3 = a₃)
    (α : triangleObject K.X a ⟶ triangleObject K.Y q)
    (β : triangleObject K.X a₁ ⟶ triangleObject K.Y (q + 1))
    (hαβ : triangleMap K.X a ≫ eqToHom (congrArg (triangleObject K.X) ha₁) ≫ β =
      α ≫ triangleMap K.Y q) :
    ∃ γ : triangleObject K.X a₂ ⟶ triangleObject K.Y (q + 2),
      (triangleMap K.X a₁ ≫
          eqToHom (congrArg (triangleObject K.X) (show a₁ + 1 = a₂ by omega))) ≫ γ =
        β ≫ triangleMap K.Y (q + 1) ≫
          eqToHom (congrArg (triangleObject K.Y) (show q + 1 + 1 = q + 2 by omega)) ∧
      (triangleObjectPeriodicityIso K.X a₂).hom ≫
          (γ ≫ triangleMap K.Y (q + 2) ≫
            eqToHom (congrArg (triangleObject K.Y)
              (show q + 2 + 1 = q + 3 by omega)))⟦(-1 : ℤ)⟧' ≫
          (triangleObjectPeriodicityIso K.Y (q + 3)).inv =
        -(eqToHom (congrArg (triangleObject K.X) (show a₂ - 3 = a₃ by omega)) ≫
          triangleMap K.X a₃ ≫
          eqToHom (congrArg (triangleObject K.X) (show a₃ + 1 = a by omega)) ≫ α ≫
          eqToHom (congrArg (triangleObject K.Y) (show q = q + 3 - 3 by omega))) := by
  subst ha₁
  subst ha₂
  subst ha₃
  obtain ⟨γ, h₁, h₂⟩ := exists_fill K a q α β (by simpa using hαβ)
  exact ⟨γ, h₁, by simpa using h₂⟩

/-- **Stacks 0H8B.** The double complex of morphism groups between the three-periodic sequences
of two distinguished triangles is a matress: its rows and columns are exact, it is three-periodic
compatibly with both differentials, and it satisfies the filling condition. -/
@[stacks 0H8B "the whole remark for the Hom double complex of two distinguished triangles: the \
matress structure, so exact rows and columns, three-periodicity compatible with both \
differentials, and the TR3 filling condition"]
noncomputable def homDoubleComplexMatress (K : HomDoubleComplexSetup (C := C)) :
    HomologicalComplex₂.Matress (homDoubleComplex K) where
  row_exact p q := K.d₁_exact p q
  column_exact p q := K.d₂_exact p q
  periodic p q := AddEquiv.toAddCommGrpIso (diagonalPeriodicityEquiv K p q)
  periodic_d₁ p q := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    have h := diagonalPeriodicityEquiv_d₁ K p q x
    rw [cast_term_left K (show p + 1 + 3 = p + 3 + 1 by omega)] at h
    simp only [ConcreteCategory.comp_apply, reindexIso_hom_fun]
    change eqToHom (congrArg (triangleObject K.X) (show -(p + 4) = -(p + 1 + 3) by omega)) ≫
        (diagonalPeriodicityEquiv K (p + 1) q (K.d₁ p q x)) ≫
        eqToHom (congrArg (triangleObject K.Y) (show q - 3 = q - 3 from rfl)) =
      eqToHom (congrArg (triangleObject K.X) (show -(p + 4) = -(p + 3 + 1) by omega)) ≫
        (K.d₁ (p + 3) (q - 3) (diagonalPeriodicityEquiv K p q x)) ≫
        eqToHom (congrArg (triangleObject K.Y) (show q - 3 = q - 3 from rfl))
    rw [← h]
    simp
  periodic_d₂ p q := by
    refine ConcreteCategory.hom_ext _ _ fun x => ?_
    have h := diagonalPeriodicityEquiv_d₂ K p q x
    rw [cast_term_right K (show q + 1 - 3 = q - 3 + 1 by omega)] at h
    simp only [ConcreteCategory.comp_apply, reindexIso_hom_fun]
    change eqToHom (congrArg (triangleObject K.X) (show -(p + 3) = -(p + 3) from rfl)) ≫
        (diagonalPeriodicityEquiv K p (q + 1) (K.d₂ p q x)) ≫
        eqToHom (congrArg (triangleObject K.Y) (show q + 1 - 3 = q - 2 by omega)) =
      eqToHom (congrArg (triangleObject K.X) (show -(p + 3) = -(p + 3) from rfl)) ≫
        (K.d₂ (p + 3) (q - 3) (diagonalPeriodicityEquiv K p q x)) ≫
        eqToHom (congrArg (triangleObject K.Y) (show q - 3 + 1 = q - 2 by omega))
    rw [← h]
    simp
  fill p q alpha beta h := by
    obtain ⟨a', ha'⟩ : ∃ a' : triangleObject K.X (-p) ⟶ triangleObject K.Y q, alpha = a' :=
      ⟨alpha, rfl⟩
    obtain ⟨b', hb'⟩ : ∃ b' : triangleObject K.X (-(p - 1)) ⟶ triangleObject K.Y (q + 1),
        beta = b' := ⟨beta, rfl⟩
    rw [ha', hb'] at h ⊢
    simp only [reindexIso_hom_fun, homDoubleComplex_d₁_fun, homDoubleComplex_d₂_fun] at h
    have hαβ : triangleMap K.X (-p) ≫
        eqToHom (congrArg (triangleObject K.X) (show -p + 1 = -(p - 1) by omega)) ≫ b' =
        a' ≫ triangleMap K.Y q := by
      have hm := triangleMap_eqToHom K.X (show -p = -(p - 1 + 1) by omega)
        (show -(p - 1 + 1) + 1 = -(p - 1) by omega)
      rw [h, ← Category.assoc, hm]
      simp
    obtain ⟨γ, hγ₁, hγ₂⟩ := exists_fill' K (-p) (-(p - 1)) (-(p - 2)) (-(p + 1)) q
      (by omega) (by omega) (by omega) a' b' hαβ
    refine ⟨γ, ?_, ?_⟩
    · simp only [reindexIso_hom_fun, homDoubleComplex_d₁_fun, homDoubleComplex_d₂_fun]
      have hm := triangleMap_eqToHom K.X (show -(p - 1) = -(p - 2 + 1) by omega)
        (show -(p - 2 + 1) + 1 = -(p - 2) by omega)
      simp only [Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [← reassoc_of% hm]
      exact (Category.assoc _ _ _).symm.trans hγ₁
    · simp only [reindexIso_hom_fun, homDoubleComplex_d₁_fun, homDoubleComplex_d₂_fun,
        periodic_hom_fun, diagonalPeriodicityEquiv_apply]
      have hsign : (p - 2 + (q + 3)).negOnePow = -(p + q).negOnePow := by
        rw [show p - 2 + (q + 3) = p + q + 1 by omega, Int.negOnePow_add]
        simp
      simp only [xObjectPeriodicityIso, yObjectPeriodicityIso, Iso.trans_hom, eqToIso.hom,
        Category.assoc, eqToHom_refl, Category.id_comp, hsign,
        Units.neg_smul, Linear.units_smul_comp, Linear.comp_units_smul,
        Preadditive.comp_neg, Preadditive.neg_comp]
      rw [reassoc_of% hγ₂]
      simp
      rfl

end AlgebraicGeometry.HomDoubleComplexSetup

end

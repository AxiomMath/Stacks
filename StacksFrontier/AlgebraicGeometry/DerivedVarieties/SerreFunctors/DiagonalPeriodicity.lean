module

public import Mathlib.CategoryTheory.HomCongr
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.HomDoubleComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Diagonal periodicity of the Hom double complex

The Hom double complex attached to two distinguished triangles is invariant under translation of
its bidegree by `(3, -3)`: both periodic sequences are three-periodic up to the shift `[-1]`, so
the morphism group in bidegree `(p, q)` is identified with the one in bidegree `(p+3, q-3)`.
These identifications commute with both differentials.

## Main definitions

* `AlgebraicGeometry.triangleObjectPeriodicityIso` identifies the object three steps back in a
  periodic sequence with the `[-1]`-shift of the current one.
* `AlgebraicGeometry.xObjectPeriodicityIso` and `AlgebraicGeometry.yObjectPeriodicityIso` are
  the resulting identifications for the two triangles.
* `AlgebraicGeometry.diagonalPeriodicityEquiv` is the additive equivalence between diagonally
  translated terms.

## Main results

* `AlgebraicGeometry.diagonalPeriodicityEquiv_apply` describes the identification as shifting a
  morphism and composing with the object identifications.
* `AlgebraicGeometry.diagonalPeriodicityEquiv_d₁` and
  `AlgebraicGeometry.diagonalPeriodicityEquiv_d₂` are its compatibility with the two
  differentials.

## Implementation notes

The identification shifts morphisms by `[-1]`. Since `CategoryTheory.Pretriangulated.Triangle`'s
shift functor carries the sign `(-1)^n` on all three maps, the identification also multiplies by
`(-1)^(p+q)`, which is what makes it commute with both differentials. The object isomorphisms
and the application formula are public so that triangle morphisms can be transported through
this identification.

## References

* [Stacks Project, Tag 0H8B](https://stacks.math.columbia.edu/tag/0H8B)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Decreasing the degree of the extended triangle by three shifts its object by `[-1]`.
The identification is the canonical associativity isomorphism for shifts. -/
noncomputable def triangleObjectPeriodicityIso (T : Triangle C) (p : ℤ) :
    HomDoubleComplexSetup.triangleObject T (p - 3) ≅
      (HomDoubleComplexSetup.triangleObject T p)⟦(-1 : ℤ)⟧ := by
  have hr : (p - 3) % 3 = p % 3 := by omega
  dsimp only [HomDoubleComplexSetup.triangleObject]
  rw [hr]
  split_ifs <;>
    exact (shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).app _

/-- The source-object identification for diagonal periodicity. -/
noncomputable def xObjectPeriodicityIso
    (K : HomDoubleComplexSetup (C := C)) (p : ℤ) :
    K.XObject (-(p + 3)) ≅ (K.XObject (-p))⟦(-1 : ℤ)⟧ :=
  eqToIso (congrArg (HomDoubleComplexSetup.triangleObject K.X) (by omega)) ≪≫
    triangleObjectPeriodicityIso K.X (-p)

/-- The target-object identification for diagonal periodicity. -/
noncomputable def yObjectPeriodicityIso
    (K : HomDoubleComplexSetup (C := C)) (q : ℤ) :
    K.YObject (q - 3) ≅ (K.YObject q)⟦(-1 : ℤ)⟧ :=
  triangleObjectPeriodicityIso K.Y q

/-- The diagonal three-periodicity identification in the Hom double-complex of two
distinguished triangles. -/
@[stacks 0H8B "diagonal_periodicity"]
noncomputable def diagonalPeriodicityEquiv
    (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    K.term p q ≃+ K.term (p + 3) (q - 3) :=
  let e : K.term p q ≃+ K.term (p + 3) (q - 3) :=
    { toEquiv :=
        (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C (-1 : ℤ))).homEquiv.trans
          (Iso.homCongr (xObjectPeriodicityIso K p).symm
            (yObjectPeriodicityIso K q).symm)
      map_add' := by
        intro f g
        simp [Preadditive.comp_add, Preadditive.add_comp] }
  e.trans (DistribMulAction.toAddEquiv _ (p + q).negOnePow)

/-- Diagonal periodicity shifts a morphism by `[-1]`, transports its source and
target through the canonical shift isomorphisms, and inserts the sign required by
the signed triangle maps. -/
@[simp]
lemma diagonalPeriodicityEquiv_apply
    (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) (f : K.term p q) :
    diagonalPeriodicityEquiv K p q f =
      (p + q).negOnePow •
        ((xObjectPeriodicityIso K p).hom ≫ f⟦(-1 : ℤ)⟧' ≫
          (yObjectPeriodicityIso K q).inv) := rfl

section

omit [HasZeroObject C] [Pretriangulated C]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
omit [Preadditive C] [HasShift C ℤ] in
private lemma iso_hom_heq {X Y X' Y' : C} (e : X ≅ Y) (e' : X' ≅ Y')
    (hX : X = X') (hY : Y = Y') (h : HEq e e') : HEq e.hom e'.hom := by
  subst X'
  subst Y'
  cases h
  rfl

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
private lemma periodicity_hom_heq (T : Triangle C) (p n m : ℤ) (X : C)
    (hX : (p % 3 = 0 ∧ X = T.obj₁) ∨ (p % 3 = 1 ∧ X = T.obj₂) ∨ (p % 3 = 2 ∧ X = T.obj₃))
    (hn : p / 3 = n) (hm : (p - 3) / 3 = m) :
    HEq (triangleObjectPeriodicityIso T p).hom
      ((shiftFunctorAdd' C n (-1) m (by omega)).hom.app X) := by
  subst n
  subst m
  have hp3 : (p - 3) % 3 = p % 3 := by omega
  rcases hX with ⟨hp, rfl⟩ | ⟨hp, rfl⟩ | ⟨hp, rfl⟩ <;>
  · apply iso_hom_heq _ ((shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).app _)
    · simp [HomDoubleComplexSetup.triangleObject, hp3, hp]
    · simp [HomDoubleComplexSetup.triangleObject, hp]
    · simp only [Int.reduceNeg, triangleObjectPeriodicityIso, hp,
        one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ↓reduceDIte,
        eq_mpr_eq_cast, cast_cast, id_eq, Functor.comp_obj, cast_heq_iff_heq]
      apply cast_heq

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
private lemma triangleMap_heq_zero (T : Triangle C) (p n : ℤ)
    (hp : p % 3 = 0) (hn : p / 3 = n) :
    HEq (HomDoubleComplexSetup.triangleMap T p)
      (((Triangle.shiftFunctor C n).obj T).mor₁) := by
  subst n
  simp [HomDoubleComplexSetup.triangleMap, hp, ← Category.assoc]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
private lemma triangleMap_heq_one (T : Triangle C) (p n : ℤ)
    (hp : p % 3 = 1) (hn : p / 3 = n) :
    HEq (HomDoubleComplexSetup.triangleMap T p)
      (((Triangle.shiftFunctor C n).obj T).mor₂) := by
  subst n
  simp [HomDoubleComplexSetup.triangleMap, hp, ← Category.assoc]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
private lemma triangleMap_heq_two (T : Triangle C) (p n : ℤ)
    (hp : p % 3 = 2) (hn : p / 3 = n) :
    HEq (HomDoubleComplexSetup.triangleMap T p)
      (n.negOnePow • (T.mor₃⟦n⟧' ≫
        (shiftFunctorAdd' C 1 n (n + 1) (by omega)).inv.app T.obj₁)) := by
  subst n
  apply HEq.trans (b := ((Triangle.shiftFunctor C (p / 3)).obj T).mor₃ ≫
    (shiftFunctorAdd' C (p / 3) 1 (p / 3 + 1) rfl).inv.app T.obj₁)
  · simp only [HomDoubleComplexSetup.triangleMap, hp, show (2 : ℤ) ≠ 0 by decide,
      show (2 : ℤ) ≠ 1 by decide, ↓reduceDIte, eqToHom_comp_heq_iff]
    exact HEq.trans (heq_of_eq (Category.assoc _ _ _).symm)
      (comp_eqToHom_heq (C := C) _ _)
  · apply heq_of_eq
    simp [Triangle.shiftFunctor, shiftFunctorComm_eq C 1 (p / 3) (p / 3 + 1) (by omega),
      Linear.units_smul_comp, Category.assoc]

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
private lemma signed_square_of_heq {A B A' B' X Y X' Y' : C}
    (a : A ⟶ B) (a' : A' ⟶ B') (s : A' ⟶ A⟦(-1 : ℤ)⟧)
    (t : B' ⟶ B⟦(-1 : ℤ)⟧)
    (b : X ⟶ Y) (b' : X' ⟶ Y') (u : X' ⟶ X⟦(-1 : ℤ)⟧)
    (v : Y' ⟶ Y⟦(-1 : ℤ)⟧)
    (hA : A = X) (hB : B = Y) (hA' : A' = X') (hB' : B' = Y')
    (ha : HEq a b) (ha' : HEq a' b') (hs : HEq s u) (ht : HEq t v)
    (h : b' ≫ v = -(u ≫ b⟦(-1 : ℤ)⟧')) :
    a' ≫ t = -(s ≫ a⟦(-1 : ℤ)⟧') := by
  subst X Y X' Y'
  cases ha
  cases ha'
  cases hs
  cases ht
  exact h

private lemma shifted_signed_square {A B : C} (f : A ⟶ B) (n m : ℤ)
    (h : n + (-1) = m) :
    (m.negOnePow • f⟦m⟧') ≫ (shiftFunctorAdd' C n (-1) m h).hom.app B =
      -((shiftFunctorAdd' C n (-1) m h).hom.app A ≫
        (n.negOnePow • f⟦n⟧')⟦(-1 : ℤ)⟧') := by
  subst m
  simp only [Linear.units_smul_comp, NatTrans.naturality, Functor.comp_map,
    Functor.map_units_smul, Linear.comp_units_smul, Int.negOnePow_add,
    Int.negOnePow_neg, Int.negOnePow_one, mul_smul]
  simp

private lemma shifted_third_signed_square {A B : C} (f : A ⟶ B⟦(1 : ℤ)⟧)
    (n m : ℤ) (h : n + (-1) = m) :
    (m.negOnePow • (f⟦m⟧' ≫
      (shiftFunctorAdd' C 1 m (m + 1) (by omega)).inv.app B)) ≫
        (shiftFunctorAdd' C (n + 1) (-1) (m + 1) (by omega)).hom.app B =
    -((shiftFunctorAdd' C n (-1) m h).hom.app A ≫
      (n.negOnePow • (f⟦n⟧' ≫
        (shiftFunctorAdd' C 1 n (n + 1) (by omega)).inv.app B))⟦(-1 : ℤ)⟧') := by
  have hc : (shiftFunctorAdd' C 1 m (m + 1) (by omega)).inv.app B ≫
        (shiftFunctorAdd' C (n + 1) (-1) (m + 1) (by omega)).hom.app B =
      (shiftFunctorAdd' C n (-1) m h).hom.app (B⟦(1 : ℤ)⟧) ≫
        ((shiftFunctorAdd' C 1 n (n + 1) (by omega)).inv.app B)⟦(-1 : ℤ)⟧' := by
    apply (cancel_epi ((shiftFunctorAdd' C 1 m (m + 1) (by omega)).hom.app B)).1
    apply (cancel_mono (((shiftFunctorAdd' C 1 n (n + 1) (by omega)).hom.app B)⟦(-1 : ℤ)⟧')).1
    simpa [Category.assoc, ← Functor.map_comp] using
      (shiftFunctorAdd'_assoc_hom_app (C := C) 1 n (-1) (n + 1) m (m + 1)
        (by omega) h (by omega) B)
  simp only [Linear.units_smul_comp, Category.assoc, hc]
  simpa [Functor.map_units_smul, Functor.map_comp, Linear.comp_units_smul,
    Linear.units_smul_comp, Category.assoc] using
    congrArg (fun k => k ≫
      ((shiftFunctorAdd' C 1 n (n + 1) (by omega)).inv.app B)⟦(-1 : ℤ)⟧')
      (shifted_signed_square f n m h)

private lemma triangleMap_periodicity_zero (T : Triangle C) (p : ℤ) (hp : p % 3 = 0) :
    HomDoubleComplexSetup.triangleMap T (p - 3) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p - 3 + 1 = p + 1 - 3 by omega)) ≫
      (triangleObjectPeriodicityIso T (p + 1)).hom =
    -((triangleObjectPeriodicityIso T p).hom ≫
      (HomDoubleComplexSetup.triangleMap T p)⟦(-1 : ℤ)⟧') := by
  have hp' : (p + 1) % 3 = 1 := by omega
  have hmp : (p - 3) % 3 = 0 := by omega
  have hmp' : (p + 1 - 3) % 3 = 1 := by omega
  have hn : (p + 1) / 3 = p / 3 := by omega
  have hm : (p + 1 - 3) / 3 = (p - 3) / 3 := by omega
  rw [← Category.assoc]
  refine signed_square_of_heq _ _ _ _
    ((Triangle.shiftFunctor C (p / 3)).obj T).mor₁
    ((Triangle.shiftFunctor C ((p - 3) / 3)).obj T).mor₁
    ((shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).hom.app T.obj₁)
    ((shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).hom.app T.obj₂)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [HomDoubleComplexSetup.triangleObject, hp]
  · simp [HomDoubleComplexSetup.triangleObject, hp', hn]
  · simp [HomDoubleComplexSetup.triangleObject, hmp]
  · simp [HomDoubleComplexSetup.triangleObject, hmp', hm]
  · exact triangleMap_heq_zero T p _ hp rfl
  · exact (comp_eqToHom_heq (C := C) _ _).trans
      (triangleMap_heq_zero T (p - 3) _ hmp rfl)
  · exact periodicity_hom_heq T p _ _ _ (.inl ⟨hp, rfl⟩) rfl rfl
  · exact periodicity_hom_heq T (p + 1) _ _ _ (.inr (.inl ⟨hp', rfl⟩)) hn hm
  · exact shifted_signed_square T.mor₁ _ _ (by omega)

private lemma triangleMap_periodicity_one (T : Triangle C) (p : ℤ) (hp : p % 3 = 1) :
    HomDoubleComplexSetup.triangleMap T (p - 3) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p - 3 + 1 = p + 1 - 3 by omega)) ≫
      (triangleObjectPeriodicityIso T (p + 1)).hom =
    -((triangleObjectPeriodicityIso T p).hom ≫
      (HomDoubleComplexSetup.triangleMap T p)⟦(-1 : ℤ)⟧') := by
  have hp' : (p + 1) % 3 = 2 := by omega
  have hmp : (p - 3) % 3 = 1 := by omega
  have hmp' : (p + 1 - 3) % 3 = 2 := by omega
  have hn : (p + 1) / 3 = p / 3 := by omega
  have hm : (p + 1 - 3) / 3 = (p - 3) / 3 := by omega
  rw [← Category.assoc]
  refine signed_square_of_heq _ _ _ _
    ((Triangle.shiftFunctor C (p / 3)).obj T).mor₂
    ((Triangle.shiftFunctor C ((p - 3) / 3)).obj T).mor₂
    ((shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).hom.app T.obj₂)
    ((shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).hom.app T.obj₃)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [HomDoubleComplexSetup.triangleObject, hp]
  · simp [HomDoubleComplexSetup.triangleObject, hp', hn]
  · simp [HomDoubleComplexSetup.triangleObject, hmp]
  · simp [HomDoubleComplexSetup.triangleObject, hmp', hm]
  · exact triangleMap_heq_one T p _ hp rfl
  · exact (comp_eqToHom_heq (C := C) _ _).trans
      (triangleMap_heq_one T (p - 3) _ hmp rfl)
  · exact periodicity_hom_heq T p _ _ _ (.inr (.inl ⟨hp, rfl⟩)) rfl rfl
  · exact periodicity_hom_heq T (p + 1) _ _ _ (.inr (.inr ⟨hp', rfl⟩)) hn hm
  · exact shifted_signed_square T.mor₂ _ _ (by omega)

private lemma triangleMap_periodicity_two (T : Triangle C) (p : ℤ) (hp : p % 3 = 2) :
    HomDoubleComplexSetup.triangleMap T (p - 3) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p - 3 + 1 = p + 1 - 3 by omega)) ≫
      (triangleObjectPeriodicityIso T (p + 1)).hom =
    -((triangleObjectPeriodicityIso T p).hom ≫
      (HomDoubleComplexSetup.triangleMap T p)⟦(-1 : ℤ)⟧') := by
  have hp' : (p + 1) % 3 = 0 := by omega
  have hmp : (p - 3) % 3 = 2 := by omega
  have hmp' : (p + 1 - 3) % 3 = 0 := by omega
  have hn : (p + 1) / 3 = p / 3 + 1 := by omega
  have hm : (p + 1 - 3) / 3 = (p - 3) / 3 + 1 := by omega
  rw [← Category.assoc]
  refine signed_square_of_heq _ _ _ _
    ((p / 3).negOnePow • (T.mor₃⟦p / 3⟧' ≫
      (shiftFunctorAdd' C 1 (p / 3) (p / 3 + 1) (by omega)).inv.app T.obj₁))
    (((p - 3) / 3).negOnePow • (T.mor₃⟦(p - 3) / 3⟧' ≫
      (shiftFunctorAdd' C 1 ((p - 3) / 3) ((p - 3) / 3 + 1) (by omega)).inv.app T.obj₁))
    ((shiftFunctorAdd' C (p / 3) (-1) ((p - 3) / 3) (by omega)).hom.app T.obj₃)
    ((shiftFunctorAdd' C (p / 3 + 1) (-1) ((p - 3) / 3 + 1) (by omega)).hom.app T.obj₁)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [HomDoubleComplexSetup.triangleObject, hp]
  · simp [HomDoubleComplexSetup.triangleObject, hp', hn]
  · simp [HomDoubleComplexSetup.triangleObject, hmp]
  · simp [HomDoubleComplexSetup.triangleObject, hmp', hm]
  · exact triangleMap_heq_two T p _ hp rfl
  · exact (comp_eqToHom_heq (C := C) _ _).trans
      (triangleMap_heq_two T (p - 3) _ hmp rfl)
  · exact periodicity_hom_heq T p _ _ _ (.inr (.inr ⟨hp, rfl⟩)) rfl rfl
  · exact periodicity_hom_heq T (p + 1) _ _ _ (.inl ⟨hp', rfl⟩) hn hm
  · exact shifted_third_signed_square T.mor₃ _ _ (by omega)

private lemma triangleMap_periodicity (T : Triangle C) (p : ℤ) :
    HomDoubleComplexSetup.triangleMap T (p - 3) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p - 3 + 1 = p + 1 - 3 by omega)) ≫
      (triangleObjectPeriodicityIso T (p + 1)).hom =
    -((triangleObjectPeriodicityIso T p).hom ≫
      (HomDoubleComplexSetup.triangleMap T p)⟦(-1 : ℤ)⟧') := by
  rcases (show p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 by omega) with h | h | h
  · exact triangleMap_periodicity_zero T p h
  · exact triangleMap_periodicity_one T p h
  · exact triangleMap_periodicity_two T p h

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
/-- In a degree divisible by three, the periodicity identification of a three-periodic sequence
is the canonical shift identification of the first object of the triangle. -/
lemma triangleObjectPeriodicityIso_hom_heq_of_emod_eq_zero (T : Triangle C) (p n m : ℤ)
    (hp : p % 3 = 0) (hn : p / 3 = n) (hm : (p - 3) / 3 = m) :
    HEq (triangleObjectPeriodicityIso T p).hom
      ((shiftFunctorAdd' C n (-1) m (by omega)).hom.app T.obj₁) :=
  periodicity_hom_heq T p n m _ (.inl ⟨hp, rfl⟩) hn hm

/-- The periodicity identifications of a three-periodic sequence anticommute with its transition
maps. -/
lemma triangleMap_comp_triangleObjectPeriodicityIso_hom (T : Triangle C) (p : ℤ) :
    HomDoubleComplexSetup.triangleMap T (p - 3) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p - 3 + 1 = p + 1 - 3 by omega)) ≫
      (triangleObjectPeriodicityIso T (p + 1)).hom =
    -((triangleObjectPeriodicityIso T p).hom ≫
      (HomDoubleComplexSetup.triangleMap T p)⟦(-1 : ℤ)⟧') :=
  triangleMap_periodicity T p

private lemma triangleMap_periodicity_reindex (T : Triangle C) (p q r s : ℤ)
    (h : p + 1 = q) (hr : r = p - 3) (hs : s = q - 3) :
    HomDoubleComplexSetup.triangleMap T r ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show r + 1 = s by omega)) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T) hs) ≫
      (triangleObjectPeriodicityIso T q).hom =
    -(eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T) hr) ≫
      (triangleObjectPeriodicityIso T p).hom ≫
      (HomDoubleComplexSetup.triangleMap T p ≫
        eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T) h))⟦(-1 : ℤ)⟧') := by
  subst r s q
  simpa using triangleMap_periodicity T p

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
omit [Preadditive C] [HasShift C ℤ] in
private lemma cast_hom_right {ι : Sort*} (X : C) (Y : ι → C) {i j : ι}
    (h : i = j) (f : X ⟶ Y i) :
    cast (congrArg (fun k => X ⟶ Y k) h) f = f ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

omit [∀ n : ℤ, (shiftFunctor C n).Additive] in
omit [Preadditive C] [HasShift C ℤ] in
private lemma cast_hom_left {ι : Sort*} (X : ι → C) (Y : C) {i j : ι}
    (h : i = j) (f : X i ⟶ Y) :
    cast (congrArg (fun k => X k ⟶ Y) h) f = eqToHom (congrArg X h.symm) ≫ f := by
  subst j
  simp

end

/-- The diagonal periodicity identification commutes with the first differential. -/
@[stacks 0H8B "diagonal_periodicity"]
lemma diagonalPeriodicityEquiv_d₁
    (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) (f : K.term p q) :
    cast (congrArg (fun i => K.term i (q - 3)) (by omega))
        (diagonalPeriodicityEquiv K (p + 1) q (K.d₁ p q f)) =
      K.d₁ (p + 3) (q - 3) (diagonalPeriodicityEquiv K p q f) := by
  simp only [diagonalPeriodicityEquiv_apply]
  show cast (congrArg (fun i => K.term i (q - 3))
    (show p + 1 + 3 = p + 3 + 1 by omega))
    ((p + 1 + q).negOnePow • ((xObjectPeriodicityIso K (p + 1)).hom ≫
      ((HomDoubleComplexSetup.triangleMap K.X (-(p + 1)) ≫
        eqToHom (congrArg (HomDoubleComplexSetup.triangleObject K.X)
          (show -(p + 1) + 1 = -p by omega))) ≫ f)⟦(-1 : ℤ)⟧' ≫
      (yObjectPeriodicityIso K q).inv)) =
    (HomDoubleComplexSetup.triangleMap K.X (-(p + 3 + 1)) ≫
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject K.X)
        (show -(p + 3 + 1) + 1 = -(p + 3) by omega))) ≫
    ((p + q).negOnePow • ((xObjectPeriodicityIso K p).hom ≫ f⟦(-1 : ℤ)⟧' ≫
      (yObjectPeriodicityIso K q).inv))
  rw [cast_hom_left (X := fun i => K.XObject (-i))
    (h := show p + 1 + 3 = p + 3 + 1 by omega)]
  have hsign : (p + 1 + q).negOnePow = -(p + q).negOnePow := by
    rw [add_right_comm, Int.negOnePow_succ]
  simp only [hsign, Units.neg_smul, Linear.comp_units_smul, Preadditive.comp_neg,
    ← smul_neg]
  congr 1
  have h := triangleMap_periodicity_reindex K.X (-(p + 1)) (-p)
    (-(p + 3 + 1)) (-(p + 3)) (by omega) (by omega) (by omega)
  simpa [xObjectPeriodicityIso, Functor.map_comp, Category.assoc] using
    (congrArg (fun k => k ≫ f⟦(-1 : ℤ)⟧' ≫ (yObjectPeriodicityIso K q).inv) h).symm

/-- The diagonal periodicity identification commutes with the second differential. -/
@[stacks 0H8B "diagonal_periodicity"]
lemma diagonalPeriodicityEquiv_d₂
    (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) (f : K.term p q) :
    cast (congrArg (K.term (p + 3)) (by omega))
        (diagonalPeriodicityEquiv K p (q + 1) (K.d₂ p q f)) =
      K.d₂ (p + 3) (q - 3) (diagonalPeriodicityEquiv K p q f) := by
  simp only [diagonalPeriodicityEquiv_apply]
  show cast (congrArg (K.term (p + 3)) (show q + 1 - 3 = q - 3 + 1 by omega))
    ((p + (q + 1)).negOnePow •
      ((xObjectPeriodicityIso K p).hom ≫
        (f ≫ HomDoubleComplexSetup.triangleMap K.Y q)⟦(-1 : ℤ)⟧' ≫
        (yObjectPeriodicityIso K (q + 1)).inv)) =
    ((p + q).negOnePow • ((xObjectPeriodicityIso K p).hom ≫ f⟦(-1 : ℤ)⟧' ≫
      (yObjectPeriodicityIso K q).inv)) ≫ HomDoubleComplexSetup.triangleMap K.Y (q - 3)
  rw [cast_hom_right (Y := K.YObject) (h := show q + 1 - 3 = q - 3 + 1 by omega)]
  have hsign : (p + (q + 1)).negOnePow = -(p + q).negOnePow := by
    rw [← add_assoc, Int.negOnePow_succ]
  simp only [hsign, Units.neg_smul, Linear.units_smul_comp, Preadditive.neg_comp, ← smul_neg]
  congr 1
  apply (cancel_mono (eqToHom (congrArg (HomDoubleComplexSetup.triangleObject K.Y)
      (show q - 3 + 1 = q + 1 - 3 by omega)) ≫
    (triangleObjectPeriodicityIso K.Y (q + 1)).hom)).1
  simp only [Functor.map_comp, Category.assoc, Preadditive.neg_comp,
    yObjectPeriodicityIso, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id_assoc, triangleMap_periodicity, Preadditive.comp_neg]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry

module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.DiagonalPeriodicity
public import StacksCore.Tactic.StacksAttribute

/-!
# The distinguished triangle cut out of a three-periodic sequence

Three consecutive steps `X^p ⟶ X^{p+1} ⟶ X^{p+2}` of the bi-infinite three-periodic sequence of
a distinguished triangle, together with the identification `X^{p+3} ≅ (X^p)⟦1⟧` supplied by
diagonal periodicity, form a distinguished triangle again. This is the triangle to which the
TR3 axiom is applied in the Hom double complex of two distinguished triangles.

## Main definitions

* `AlgebraicGeometry.shiftIsoOfNegShiftIso` turns an identification `A ≅ B⟦-1⟧` into the
  identification `B ≅ A⟦1⟧` it determines.
* `AlgebraicGeometry.triangleObjectShiftIso` is the resulting identification
  `X^{p+3} ≅ (X^p)⟦1⟧` of the three-periodic sequence.
* `AlgebraicGeometry.segmentTriangle` is the triangle of three consecutive steps.

## Main results

* `AlgebraicGeometry.segmentTriangle_distinguished`: the segment of a distinguished triangle is
  distinguished.

## Implementation notes

Only one degree is computed by hand. The segment in degree `p + 1` is the rotation of the segment
in degree `p`, because the periodicity identifications anticommute with the transition maps, and
rotation preserves distinguished triangles in both directions; so the general case follows from
degree zero by induction on `ℤ`. The transposition of a periodicity identification into a shift
identification, and of the squares they sit in, is isolated in `shiftIsoOfNegShiftIso` and its
lemmas, which know nothing about triangles.

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

section NegShift

omit [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The identification `B ≅ A⟦1⟧` determined by an identification `A ≅ B⟦-1⟧`. -/
noncomputable def shiftIsoOfNegShiftIso {A B : C} (e : A ≅ B⟦(-1 : ℤ)⟧) : B ≅ A⟦(1 : ℤ)⟧ :=
  ((shiftFunctorCompIsoId C (-1) 1 (by omega)).app B).symm ≪≫
    (shiftFunctor C (1 : ℤ)).mapIso e.symm

/-- The forward map of `shiftIsoOfNegShiftIso`. -/
lemma shiftIsoOfNegShiftIso_hom {A B : C} (e : A ≅ B⟦(-1 : ℤ)⟧) :
    (shiftIsoOfNegShiftIso e).hom =
      (shiftFunctorCompIsoId C (-1) 1 (by omega)).inv.app B ≫ e.inv⟦(1 : ℤ)⟧' := rfl

/-- A square of `⟦-1⟧`-identifications transposes into a square of the `⟦1⟧`-identifications
they determine. -/
lemma shiftIsoOfNegShiftIso_square {A A' B B' : C} (e : A ≅ B⟦(-1 : ℤ)⟧)
    (e' : A' ≅ B'⟦(-1 : ℤ)⟧) (f : A ⟶ A') (g : B ⟶ B')
    (h : e.hom ≫ g⟦(-1 : ℤ)⟧' = f ≫ e'.hom) :
    g ≫ (shiftIsoOfNegShiftIso e').hom = (shiftIsoOfNegShiftIso e).hom ≫ f⟦(1 : ℤ)⟧' := by
  have h' : g⟦(-1 : ℤ)⟧' ≫ e'.inv = e.inv ≫ f := by
    simpa [Category.assoc] using congrArg (fun k => e.inv ≫ k ≫ e'.inv) h
  have hnat : g ≫ (shiftFunctorCompIsoId C (-1) 1 (by omega)).inv.app B' =
      (shiftFunctorCompIsoId C (-1) 1 (by omega)).inv.app B ≫ (g⟦(-1 : ℤ)⟧')⟦(1 : ℤ)⟧' := by
    simpa using (shiftFunctorCompIsoId C (-1) 1 (by omega)).inv.naturality g
  rw [shiftIsoOfNegShiftIso_hom, shiftIsoOfNegShiftIso_hom, reassoc_of% hnat,
    ← Functor.map_comp, h', Functor.map_comp, Category.assoc]

/-- Shifting the identification determined by `e` back by `[-1]` recovers `e`. -/
lemma shiftIsoOfNegShiftIso_hom_shift {A B : C} (e : A ≅ B⟦(-1 : ℤ)⟧) :
    (shiftIsoOfNegShiftIso e).hom⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app A = e.inv := by
  have hnat : ((e.inv⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧') ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app A =
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app (B⟦(-1 : ℤ)⟧) ≫ e.inv := by
    simpa using (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.naturality e.inv
  have hcancel : ((shiftFunctorCompIsoId C (-1) 1 (by omega)).inv.app B)⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app (B⟦(-1 : ℤ)⟧) = 𝟙 _ := by
    rw [shift_shiftFunctorCompIsoId_inv_app]
    simp
  rw [shiftIsoOfNegShiftIso_hom, Functor.map_comp, Category.assoc, hnat, ← Category.assoc,
    hcancel]
  simp

/-- On the canonical shift identifications, `shiftIsoOfNegShiftIso` is again a canonical shift
identification. -/
lemma shiftIsoOfNegShiftIso_shiftFunctorAdd' (Z : C) (n m : ℤ) (h : n + 1 = m) :
    (shiftIsoOfNegShiftIso ((shiftFunctorAdd' C m (-1) n (by omega)).app Z)).hom =
      (shiftFunctorAdd' C n 1 m h).hom.app Z := by
  have key : (shiftFunctorAdd' C n 1 m h).hom.app Z ≫
      ((shiftFunctorAdd' C m (-1) n (by omega)).hom.app Z)⟦(1 : ℤ)⟧' =
      (shiftFunctorCompIsoId C (-1) 1 (by omega)).inv.app (Z⟦m⟧) := by
    rw [shiftFunctorAdd'_assoc_hom_app (C := C) m (-1) 1 n 0 m (by omega) (by omega) (by omega) Z]
    simp [shiftFunctorCompIsoId, shiftFunctorAdd'_add_zero_hom_app]
  rw [shiftIsoOfNegShiftIso_hom, ← key, Category.assoc, ← Functor.map_comp]
  simp

omit [HasShift C ℤ] in
/-- A morphism equal to another one up to equalities of its source and target. -/
lemma iso_hom_eq_of_heq {A B A' B' : C} (e : A ≅ B) (e' : A' ≅ B')
    (hA : A = A') (hB : B = B') (h : HEq e.hom e'.hom) :
    e.hom = eqToHom hA ≫ e'.hom ≫ eqToHom hB.symm := by
  subst hA hB
  simp [eq_of_heq h]

/-- Transporting `shiftIsoOfNegShiftIso` along equalities of the two objects involved. -/
lemma shiftIsoOfNegShiftIso_eqToHom {A A' B B' : C} (e : A ≅ B⟦(-1 : ℤ)⟧)
    (e' : A' ≅ B'⟦(-1 : ℤ)⟧) (hA : A = A') (hB : B = B')
    (he : e.hom = eqToHom hA ≫ e'.hom ≫
      eqToHom (congrArg (fun Z : C => Z⟦(-1 : ℤ)⟧) hB.symm)) :
    (shiftIsoOfNegShiftIso e).hom =
      eqToHom hB ≫ (shiftIsoOfNegShiftIso e').hom ≫ (eqToHom hA.symm)⟦(1 : ℤ)⟧' := by
  subst hA hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at he ⊢
  simp [show e = e' from Iso.ext he]

end NegShift

/-- The identification `X^{p+3} ≅ (X^p)⟦1⟧` of the three-periodic sequence of a triangle. -/
noncomputable def triangleObjectShiftIso (T : Triangle C) (p : ℤ) :
    HomDoubleComplexSetup.triangleObject T (p + 3) ≅
      (HomDoubleComplexSetup.triangleObject T p)⟦(1 : ℤ)⟧ :=
  shiftIsoOfNegShiftIso
    (eqToIso (congrArg (HomDoubleComplexSetup.triangleObject T) (show p = p + 3 - 3 by omega)) ≪≫
      triangleObjectPeriodicityIso T (p + 3))

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Shifting the shift identification back by `[-1]` recovers the periodicity identification. -/
lemma triangleObjectShiftIso_hom_shift (T : Triangle C) (p : ℤ) :
    (triangleObjectShiftIso T p).hom⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app
          (HomDoubleComplexSetup.triangleObject T p) =
      (triangleObjectPeriodicityIso T (p + 3)).inv ≫
        eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
          (show p + 3 - 3 = p by omega)) := by
  rw [triangleObjectShiftIso, shiftIsoOfNegShiftIso_hom_shift]
  simp

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- Reindexing a periodicity identification along an equality of degrees. -/
lemma triangleObjectPeriodicityIso_congr (T : Triangle C) {r r' : ℤ} (h : r = r') :
    (triangleObjectPeriodicityIso T r).hom ≫
        (eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T) h))⟦(-1 : ℤ)⟧' =
      eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show r - 3 = r' - 3 by omega)) ≫ (triangleObjectPeriodicityIso T r').hom := by
  cases h
  simp

omit [HasZeroObject C] [Pretriangulated C] in
/-- The shift identifications of a three-periodic sequence anticommute with its transition
maps. -/
lemma triangleMap_comp_triangleObjectShiftIso (T : Triangle C) (p : ℤ) :
    (HomDoubleComplexSetup.triangleMap T (p + 3) ≫
        eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
          (show p + 3 + 1 = p + 1 + 3 by omega))) ≫
        (triangleObjectShiftIso T (p + 1)).hom =
      (triangleObjectShiftIso T p).hom ≫
        (-HomDoubleComplexSetup.triangleMap T p)⟦(1 : ℤ)⟧' := by
  simp only [triangleObjectShiftIso]
  refine shiftIsoOfNegShiftIso_square _ _ _ _ ?_
  have hper : (triangleObjectPeriodicityIso T (p + 3)).hom ≫
      (HomDoubleComplexSetup.triangleMap T (p + 3))⟦(-1 : ℤ)⟧' =
      -(HomDoubleComplexSetup.triangleMap T (p + 3 - 3) ≫
        eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
          (show p + 3 - 3 + 1 = p + 3 + 1 - 3 by omega)) ≫
        (triangleObjectPeriodicityIso T (p + 3 + 1)).hom) := by
    rw [triangleMap_comp_triangleObjectPeriodicityIso_hom T (p + 3)]
    simp
  have hm := HomDoubleComplexSetup.triangleMap_eqToHom T
    (show p = p + 3 - 3 by omega) (show p + 3 - 3 + 1 = p + 3 + 1 - 3 by omega)
  have hc := triangleObjectPeriodicityIso_congr T (show p + 3 + 1 = p + 1 + 3 by omega)
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, Functor.map_comp,
    Preadditive.neg_comp, eqToHom_map] at hm hc ⊢
  rw [reassoc_of% hper]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
  rw [hc, ← reassoc_of% hm]
  simp

/-- The triangle of three consecutive steps of the three-periodic sequence of a triangle. -/
noncomputable def segmentTriangle (T : Triangle C) (p : ℤ) : Triangle C where
  obj₁ := HomDoubleComplexSetup.triangleObject T p
  obj₂ := HomDoubleComplexSetup.triangleObject T (p + 1)
  obj₃ := HomDoubleComplexSetup.triangleObject T (p + 2)
  mor₁ := HomDoubleComplexSetup.triangleMap T p
  mor₂ := HomDoubleComplexSetup.triangleMap T (p + 1) ≫
    eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T) (show p + 1 + 1 = p + 2 by omega))
  mor₃ := HomDoubleComplexSetup.triangleMap T (p + 2) ≫
    eqToHom (congrArg (HomDoubleComplexSetup.triangleObject T)
      (show p + 2 + 1 = p + 3 by omega)) ≫ (triangleObjectShiftIso T p).hom

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- In a degree divisible by three, the shift identification of the three-periodic sequence is
the canonical shift identification of the first object of the triangle. -/
lemma triangleObjectShiftIso_hom_mod_zero (T : Triangle C) (p n : ℤ) (h : p = 3 * n)
    (hA : HomDoubleComplexSetup.triangleObject T p = T.obj₁⟦n⟧)
    (hB : HomDoubleComplexSetup.triangleObject T (p + 3) = T.obj₁⟦n + 1⟧) :
    (triangleObjectShiftIso T p).hom =
      eqToHom hB ≫ (shiftFunctorAdd' C n 1 (n + 1) rfl).hom.app T.obj₁ ≫
        (eqToHom hA.symm)⟦(1 : ℤ)⟧' := by
  have he : (eqToIso (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p = p + 3 - 3 by omega)) ≪≫ triangleObjectPeriodicityIso T (p + 3)).hom =
      eqToHom hA ≫ ((shiftFunctorAdd' C (n + 1) (-1) n (by omega)).app T.obj₁).hom ≫
        eqToHom (congrArg (fun Z : C => Z⟦(-1 : ℤ)⟧) hB.symm) := by
    have hheq := triangleObjectPeriodicityIso_hom_heq_of_emod_eq_zero T (p + 3) (n + 1) n
      (by omega) (by omega) (by omega)
    have hA2 : HomDoubleComplexSetup.triangleObject T (p + 3 - 3) = T.obj₁⟦n⟧ := by
      rwa [show p + 3 - 3 = p by omega]
    have hB2 : (HomDoubleComplexSetup.triangleObject T (p + 3))⟦(-1 : ℤ)⟧ =
        (T.obj₁⟦n + 1⟧)⟦(-1 : ℤ)⟧ := congrArg (fun Z : C => Z⟦(-1 : ℤ)⟧) hB
    rw [Iso.trans_hom, eqToIso.hom,
      iso_hom_eq_of_heq (triangleObjectPeriodicityIso T (p + 3))
        ((shiftFunctorAdd' C (n + 1) (-1) n (by omega)).app T.obj₁) hA2 hB2 hheq]
    simp
  rw [triangleObjectShiftIso, shiftIsoOfNegShiftIso_eqToHom _
    ((shiftFunctorAdd' C (n + 1) (-1) n (by omega)).app T.obj₁) hA hB he,
    shiftIsoOfNegShiftIso_shiftFunctorAdd' T.obj₁ n (n + 1) rfl]

/-- The segment in degree `p + 1` is the rotation of the segment in degree `p`. -/
noncomputable def segmentTriangleRotateIso (T : Triangle C) (p : ℤ) :
    segmentTriangle T (p + 1) ≅ (segmentTriangle T p).rotate :=
  Triangle.isoMk _ _ (Iso.refl _)
    (eqToIso (congrArg (HomDoubleComplexSetup.triangleObject T) (show p + 1 + 1 = p + 2 by omega)))
    (eqToIso (congrArg (HomDoubleComplexSetup.triangleObject T)
        (show p + 1 + 2 = p + 3 by omega)) ≪≫ triangleObjectShiftIso T p)
    (by simp [segmentTriangle, Triangle.rotate])
    (by
      have hm := HomDoubleComplexSetup.triangleMap_eqToHom T
        (show p + 1 + 1 = p + 2 by omega) (show p + 2 + 1 = p + 3 by omega)
      dsimp [segmentTriangle, Triangle.rotate]
      simp only [Category.assoc, eqToHom_trans_assoc]
      rw [reassoc_of% hm])
    (by
      have hm := HomDoubleComplexSetup.triangleMap_eqToHom T
        (show p + 1 + 2 = p + 3 by omega) (show p + 3 + 1 = p + 1 + 3 by omega)
      have hk := triangleMap_comp_triangleObjectShiftIso T p
      simp only [Category.assoc] at hk
      dsimp [segmentTriangle, Triangle.rotate]
      simp only [Category.assoc]
      rw [reassoc_of% hm, reassoc_of% hk]
      simp [Functor.map_neg])

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The transition map in a degree divisible by three, with the objects of the shifted triangle
written out. -/
private lemma triangleMap_mod_zero' (T : Triangle C) (p n : ℤ) (h : p = 3 * n)
    (hA : HomDoubleComplexSetup.triangleObject T p = T.obj₁⟦n⟧)
    (hB : HomDoubleComplexSetup.triangleObject T (p + 1) = T.obj₂⟦n⟧) :
    HomDoubleComplexSetup.triangleMap T p =
      eqToHom hA ≫ (n.negOnePow • T.mor₁⟦n⟧') ≫ eqToHom hB.symm := by
  rw [HomDoubleComplexSetup.triangleMap_of_eq_three_mul T p n h]
  rfl

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The transition map in a degree congruent to one modulo three, with the objects of the shifted
triangle written out. -/
private lemma triangleMap_mod_one' (T : Triangle C) (p n : ℤ) (h : p = 3 * n + 1)
    (hA : HomDoubleComplexSetup.triangleObject T p = T.obj₂⟦n⟧)
    (hB : HomDoubleComplexSetup.triangleObject T (p + 1) = T.obj₃⟦n⟧) :
    HomDoubleComplexSetup.triangleMap T p =
      eqToHom hA ≫ (n.negOnePow • T.mor₂⟦n⟧') ≫ eqToHom hB.symm := by
  rw [HomDoubleComplexSetup.triangleMap_of_eq_three_mul_add_one T p n h]
  rfl

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The transition map in a degree congruent to two modulo three, with the objects of the shifted
triangle written out. -/
private lemma triangleMap_mod_two' (T : Triangle C) (p n : ℤ) (h : p = 3 * n + 2)
    (hA : HomDoubleComplexSetup.triangleObject T p = T.obj₃⟦n⟧)
    (hB : HomDoubleComplexSetup.triangleObject T (p + 1) = T.obj₁⟦n + 1⟧) :
    HomDoubleComplexSetup.triangleMap T p =
      eqToHom hA ≫ (n.negOnePow • (T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁)) ≫
        (shiftFunctorAdd' C n 1 (n + 1) rfl).inv.app T.obj₁ ≫ eqToHom hB.symm := by
  rw [HomDoubleComplexSetup.triangleMap_of_eq_three_mul_add_two T p n h]
  rfl

/-- The segment in a degree divisible by three is the shifted triangle itself. -/
lemma segmentTriangle_distinguished_three_mul (T : Triangle C) (hT : T ∈ distTriang C) (n : ℤ) :
    segmentTriangle T (3 * n) ∈ distTriang C := by
  have hA : HomDoubleComplexSetup.triangleObject T (3 * n) = T.obj₁⟦n⟧ := by
    simp [HomDoubleComplexSetup.triangleObject, show 3 * n / 3 = n by omega,
      show 3 * n % 3 = 0 by omega]
  have hB : HomDoubleComplexSetup.triangleObject T (3 * n + 1) = T.obj₂⟦n⟧ := by
    simp [HomDoubleComplexSetup.triangleObject, show (3 * n + 1) / 3 = n by omega,
      show (3 * n + 1) % 3 = 1 by omega]
  have hC : HomDoubleComplexSetup.triangleObject T (3 * n + 2) = T.obj₃⟦n⟧ := by
    simp [HomDoubleComplexSetup.triangleObject, show (3 * n + 2) / 3 = n by omega,
      show (3 * n + 2) % 3 = 2 by omega]
  have hD : HomDoubleComplexSetup.triangleObject T (3 * n + 3) = T.obj₁⟦n + 1⟧ := by
    simp [HomDoubleComplexSetup.triangleObject, show (3 * n + 3) / 3 = n + 1 by omega,
      show (3 * n + 3) % 3 = 0 by omega]
  have hB' : HomDoubleComplexSetup.triangleObject T (3 * n + 1 + 1) = T.obj₃⟦n⟧ := by
    simp [HomDoubleComplexSetup.triangleObject, show (3 * n + 1 + 1) / 3 = n by omega,
      show (3 * n + 1 + 1) % 3 = 2 by omega]
  have hD' : HomDoubleComplexSetup.triangleObject T (3 * n + 2 + 1) = T.obj₁⟦n + 1⟧ := by
    simp [HomDoubleComplexSetup.triangleObject, show (3 * n + 2 + 1) / 3 = n + 1 by omega,
      show (3 * n + 2 + 1) % 3 = 0 by omega]
  refine isomorphic_distinguished _ (Triangle.shift_distinguished T hT n) _
    (Triangle.isoMk _ _ (eqToIso hA) (eqToIso hB) (eqToIso hC) ?_ ?_ ?_)
  · dsimp [segmentTriangle]
    rw [triangleMap_mod_zero' T (3 * n) n rfl hA hB]
    simp [Triangle.shiftFunctor]
  · dsimp [segmentTriangle]
    rw [triangleMap_mod_one' T (3 * n + 1) n rfl hB hB']
    simp [Triangle.shiftFunctor]
  · dsimp [segmentTriangle]
    rw [triangleMap_mod_two' T (3 * n + 2) n rfl hC hD',
      triangleObjectShiftIso_hom_mod_zero T (3 * n) n rfl hA hD]
    simp [Triangle.shiftFunctor, eqToHom_map]

/-- **Stacks 0H8B.** Three consecutive steps of the three-periodic sequence of a distinguished
triangle form a distinguished triangle. -/
@[stacks 0H8B "the shifting the remark appeals to: three consecutive steps of a three-periodic \
sequence form a distinguished triangle, so TR3 applies in every degree"]
theorem segmentTriangle_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (p : ℤ) :
    segmentTriangle T p ∈ distTriang C := by
  have step : ∀ r : ℤ, segmentTriangle T r ∈ distTriang C ↔
      segmentTriangle T (r + 1) ∈ distTriang C := fun r =>
    (rotate_distinguished_triangle (segmentTriangle T r)).trans
      (distinguished_iff_of_iso (segmentTriangleRotateIso T r)).symm
  induction p with
  | zero => simpa using segmentTriangle_distinguished_three_mul T hT 0
  | succ i ih => exact (step i).mp ih
  | pred i ih =>
      refine (step (-(i : ℤ) - 1)).mpr ?_
      rwa [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by omega]

end AlgebraicGeometry

end

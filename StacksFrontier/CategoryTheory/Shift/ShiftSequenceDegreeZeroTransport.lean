module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# Transporting a degree-zero transformation along two shift sequences

Let `U` and `V` be functors out of a category `C` with a shift by `ℤ`, each equipped with a
`CategoryTheory.Functor.ShiftSequence`, so that each has "degree-`n`" functors `U.shift n` and
`V.shift n` together with identifications `U.shift a (X⟦n⟧) ≅ U.shift (n + a) X`.  A natural
transformation `θ : U.shift 0 ⟶ V.shift 0` between the degree-zero functors determines one in
every degree, by evaluating `θ` at shifted objects:

`U.shift n X ≅ U.shift 0 (X⟦n⟧) ⟶ V.shift 0 (X⟦n⟧) ≅ V.shift n X`.

The transformations so obtained are compatible with the connecting morphisms
`CategoryTheory.Functor.homologySequenceδ` of every triangle of `C`: a connecting morphism is the
degree-zero functor applied to a shift of the third morphism of the triangle, conjugated by the
identifications of the shift sequence, so no compatibility of `θ` with the shift is required.

## Main definitions

* `CategoryTheory.Functor.shiftSequenceTransport`: the degree-`n` transformation determined by
  `θ`.
* `CategoryTheory.Functor.shiftSequenceTransportIso`: the same for a natural isomorphism.
* `CategoryTheory.Functor.ShiftSequence.rightComp`: the shift sequence of `F ⋙ G` obtained by
  post-composing the one of `F` with an arbitrary functor `G`.

## Main results

* `CategoryTheory.Functor.homologySequenceδ_eq_shiftIso`: a connecting morphism is the
  degree-zero functor applied to `T.mor₃⟦n₀⟧'`, conjugated by the shift sequence.
* `CategoryTheory.Functor.shiftSequenceTransport_app_comp_homologySequenceδ`: **the transported
  transformations commute with the connecting morphisms of every triangle.**
* `CategoryTheory.Functor.ShiftSequence.rightComp_homologySequenceδ`: connecting morphisms of a
  post-composite are the images of the connecting morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Category Pretriangulated

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A] [HasShift C ℤ]

section Delta

variable (F : C ⥤ A) [F.ShiftSequence ℤ]

/-- **A connecting morphism through the degree-zero functor.**  For a triangle `T` and
`n₀ + 1 = n₁`, the connecting morphism `F.shift n₀ T.obj₃ ⟶ F.shift n₁ T.obj₁` is the
degree-zero functor applied to `T.mor₃⟦n₀⟧'` followed by the identification
`T.obj₁⟦1⟧⟦n₀⟧ ≅ T.obj₁⟦n₁⟧`, conjugated by the identifications `F.shift n X ≅ F.shift 0 (X⟦n⟧)`
of the shift sequence. -/
theorem homologySequenceδ_eq_shiftIso (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    F.homologySequenceδ T n₀ n₁ h =
      (F.shiftIso n₀ 0 n₀ (add_zero n₀)).inv.app T.obj₃ ≫
        (F.shift 0).map (T.mor₃⟦n₀⟧' ≫
          (shiftFunctorAdd' C 1 n₀ n₁ (by rw [add_comm 1, h])).inv.app T.obj₁) ≫
        (F.shiftIso n₁ 0 n₁ (add_zero n₁)).hom.app T.obj₁ := by
  have key := F.shiftIso_hom_app_comp_shiftMap T.mor₃ n₀ n₁ (by rw [add_comm 1, h]) 0 n₀ n₁
    (add_zero n₀) (by rw [add_comm 1, h])
  rw [← cancel_epi ((F.shiftIso n₀ 0 n₀ (add_zero n₀)).hom.app T.obj₃),
    Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  exact key

end Delta

section Transport

variable (U V : C ⥤ A) [U.ShiftSequence ℤ] [V.ShiftSequence ℤ]

/-- **The degree-`n` transformation determined by a degree-zero one.**  At `X` it is
`U.shift n X ≅ U.shift 0 (X⟦n⟧) ⟶ V.shift 0 (X⟦n⟧) ≅ V.shift n X`, the middle arrow being `θ` at
the shifted object. -/
def shiftSequenceTransport (θ : U.shift (0 : ℤ) ⟶ V.shift (0 : ℤ)) (n : ℤ) :
    U.shift n ⟶ V.shift n :=
  (U.shiftIso n 0 n (add_zero n)).inv ≫ whiskerLeft (shiftFunctor C n) θ ≫
    (V.shiftIso n 0 n (add_zero n)).hom

/-- The component of `shiftSequenceTransport U V θ n` at `X` is
`(U.shiftIso n 0 n _).inv.app X ≫ θ.app (X⟦n⟧) ≫ (V.shiftIso n 0 n _).hom.app X`. -/
@[simp]
theorem shiftSequenceTransport_app (θ : U.shift (0 : ℤ) ⟶ V.shift (0 : ℤ)) (n : ℤ) (X : C) :
    (shiftSequenceTransport U V θ n).app X =
      (U.shiftIso n 0 n (add_zero n)).inv.app X ≫ θ.app (X⟦n⟧) ≫
        (V.shiftIso n 0 n (add_zero n)).hom.app X :=
  rfl

/-- **The transported transformations commute with the connecting morphisms.**  For every
triangle `T` of `C` (distinguished or not) and `n₀ + 1 = n₁`, the square formed by the
degree-`n₀` and degree-`n₁` transformations and the connecting morphisms of `U` and `V`
commutes. -/
@[reassoc]
theorem shiftSequenceTransport_app_comp_homologySequenceδ
    (θ : U.shift (0 : ℤ) ⟶ V.shift (0 : ℤ)) (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (shiftSequenceTransport U V θ n₀).app T.obj₃ ≫ V.homologySequenceδ T n₀ n₁ h =
      U.homologySequenceδ T n₀ n₁ h ≫ (shiftSequenceTransport U V θ n₁).app T.obj₁ := by
  rw [homologySequenceδ_eq_shiftIso V, homologySequenceδ_eq_shiftIso U,
    shiftSequenceTransport_app, shiftSequenceTransport_app]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← θ.naturality_assoc]

/-- The degree-`n` isomorphism determined by a degree-zero natural isomorphism. -/
def shiftSequenceTransportIso (θ : U.shift (0 : ℤ) ≅ V.shift (0 : ℤ)) (n : ℤ) :
    U.shift n ≅ V.shift n :=
  (U.shiftIso n 0 n (add_zero n)).symm ≪≫ isoWhiskerLeft (shiftFunctor C n) θ ≪≫
    V.shiftIso n 0 n (add_zero n)

/-- The forward morphism of `shiftSequenceTransportIso U V θ n` is
`shiftSequenceTransport U V θ.hom n`. -/
@[simp]
theorem shiftSequenceTransportIso_hom (θ : U.shift (0 : ℤ) ≅ V.shift (0 : ℤ)) (n : ℤ) :
    (shiftSequenceTransportIso U V θ n).hom = shiftSequenceTransport U V θ.hom n :=
  rfl

end Transport

namespace ShiftSequence

variable {B : Type u₃} [Category.{v₃} B]

/-- The shift sequence of `F ⋙ G` obtained from one of `F` by post-composing every functor and
every identification with `G`. -/
@[implicit_reducible]
def rightComp (F : C ⥤ A) [F.ShiftSequence ℤ] (G : A ⥤ B) : (F ⋙ G).ShiftSequence ℤ where
  sequence n := F.shift n ⋙ G
  isoZero := isoWhiskerRight (F.isoShiftZero ℤ) G
  shiftIso n a a' ha' :=
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    simp [F.shiftIso_zero_hom_app]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    simp [F.shiftIso_add_hom_app n m a a' a'' ha' ha'']

/-- For the shift sequence `rightComp F G`, the degree-`n` functor of `F ⋙ G` is
`F.shift n ⋙ G`. -/
theorem rightComp_shift (F : C ⥤ A) [F.ShiftSequence ℤ] (G : A ⥤ B) (n : ℤ) :
    letI := rightComp F G
    (F ⋙ G).shift n = F.shift n ⋙ G :=
  rfl

/-- For the shift sequence `rightComp F G`, the identification `(F ⋙ G).shiftIso n a a' ha'` at
`X` is the image under `G` of `(F.shiftIso n a a' ha').hom.app X`. -/
theorem rightComp_shiftIso_hom_app (F : C ⥤ A) [F.ShiftSequence ℤ] (G : A ⥤ B)
    (n a a' : ℤ) (ha' : n + a = a') (X : C) :
    letI := rightComp F G
    ((F ⋙ G).shiftIso n a a' ha').hom.app X = G.map ((F.shiftIso n a a' ha').hom.app X) := by
  let := rightComp F G
  change 𝟙 _ ≫ G.map _ = _
  rw [Category.id_comp]

/-- **Connecting morphisms of a post-composite** are the images of the connecting morphisms. -/
theorem rightComp_homologySequenceδ (F : C ⥤ A) [F.ShiftSequence ℤ] (G : A ⥤ B)
    (T : Triangle C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    letI := rightComp F G
    (F ⋙ G).homologySequenceδ T n₀ n₁ h = G.map (F.homologySequenceδ T n₀ n₁ h) := by
  let := rightComp F G
  simp only [homologySequenceδ, shiftMap, rightComp_shiftIso_hom_app, G.map_comp]
  rfl

end ShiftSequence

end CategoryTheory.Functor

end

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjunctionUnitTruncations

/-!
# Counits of adjunctions between derived categories, detected on cohomology objects

Let `F : D(A) ⥤ D(B)` and `G : D(B) ⥤ D(A)` be triangulated functors between derived categories
of abelian categories with `F ⊣ G`, and let `P` be a property of objects of `B`. Suppose the
counit `ε : G ⋙ F ⟶ 𝟭` is an isomorphism at `M[n]` for every `M` satisfying `P` and every `n`.
Then `ε` is an isomorphism at every bounded object all of whose cohomology objects satisfy `P`.

If moreover `F` carries a morphism invertible on `H^q` to one, `G` keeps `D^{≥ n}`, and `G`
carries an object of `D^{≤ c}` whose cohomology objects satisfy `P` into `D^{≤ c}`, then `ε` is
an isomorphism at every object whose cohomology objects satisfy `P`, bounded or not: in degree
`q` it is compared with `ε` at `τ_{≤ q+1} τ_{≥ q-1} X`.

This is the counit half of the formal argument of Stacks 09J1, in the form used for Stacks 06Z0:
there `F = Lp^*`, `G = Rp_*` for the morphism to the ringed point of global sections of an
affine algebraic space, and `P` is quasi-coherence.

## Main results

* `Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_counit_app_of_isGE_of_isLE`: the
  bounded case, by induction on the length of the cohomological interval.
* `Stacks.DerivedCategory.AdjunctionUnitTruncations.isIso_counit_app_of_homologyIn`: the
  unbounded case.

## Implementation notes

Only the long exact cohomology sequences of the truncation triangles and the naturality of `ε`
are used, exactly as for the unit in
`StacksFrontier/Algebra/Homology/DerivedCategory/AdjunctionUnitTruncations.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated

namespace Stacks.DerivedCategory.AdjunctionUnitTruncations

section Counit

/-- If `s ≫ e = e' ≫ t` with `s`, `e'`, `t` invertible, then `e` is invertible. -/
private theorem isIso_of_comp_eq_comp_left {C : Type*} [Category* C] {a b c d : C} {s : a ⟶ b}
    {e : b ⟶ d} {e' : a ⟶ c} {t : c ⟶ d} (h : s ≫ e = e' ≫ t) [IsIso s] [IsIso e'] [IsIso t] :
    IsIso e := by
  have : IsIso (s ≫ e) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_left s e

/-- If `e ≫ t = s ≫ e'` with `t`, `s`, `e'` invertible, then `e` is invertible. -/
private theorem isIso_of_comp_eq_comp_right {C : Type*} [Category* C] {a b c d : C} {e : a ⟶ b}
    {t : b ⟶ d} {s : a ⟶ c} {e' : c ⟶ d} (h : e ≫ t = s ≫ e') [IsIso t] [IsIso s] [IsIso e'] :
    IsIso e := by
  have : IsIso (e ≫ t) := by rw [h]; infer_instance
  exact IsIso.of_isIso_comp_right e t

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  {F : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
  {G : _root_.DerivedCategory B ⥤ _root_.DerivedCategory A}
  (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  (P : ObjectProperty B) [P.IsClosedUnderIsomorphisms]
  (hε : ∀ M : B, P M → ∀ n : ℤ,
    IsIso (adj.counit.app ((DerivedCategory.singleFunctor B n).obj M)))

local notation "H" q => DerivedCategory.homologyFunctor B q

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- The counit is an isomorphism at a zero object. -/
theorem isIso_counit_app_of_isZero [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    {X : _root_.DerivedCategory B} (hX : IsZero X) : IsIso (adj.counit.app X) :=
  ⟨⟨0, ((G ⋙ F).map_isZero hX).eq_of_src _ _, hX.eq_of_src _ _⟩⟩

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- The counit is an isomorphism at an object isomorphic to one where it is. -/
theorem isIso_counit_app_of_iso {X Y : _root_.DerivedCategory B} (e : X ≅ Y)
    [IsIso (adj.counit.app Y)] : IsIso (adj.counit.app X) :=
  (NatTrans.isIso_app_iff_of_iso _ e).2 inferInstance

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- `isIso_counit_app_of_iso` with the invertibility at `Y` as an explicit hypothesis. -/
theorem isIso_counit_app_of_iso_of_isIso {X Y : _root_.DerivedCategory B} (e : X ≅ Y)
    (h : IsIso (adj.counit.app Y)) : IsIso (adj.counit.app X) :=
  (NatTrans.isIso_app_iff_of_iso _ e).2 h

omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- If the counit is an isomorphism at `Y`, then `H^q(Y)` and `H^q(F G Y)` agree. -/
theorem isZero_homology_obj_of_isIso_counit {Y : _root_.DerivedCategory B}
    [IsIso (adj.counit.app Y)] (q : ℤ) (hY : IsZero ((H q).obj Y)) :
    IsZero ((H q).obj ((G ⋙ F).obj Y)) :=
  hY.of_iso ((H q).mapIso (asIso (adj.counit.app Y)))

include hε in
omit [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] in
/-- The counit is an isomorphism at an object concentrated in one degree whose cohomology there
satisfies `P` or is zero. -/
theorem isIso_counit_app_of_isGE_of_isLE_self [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (X : _root_.DerivedCategory B) (a : ℤ) [X.IsGE a] [X.IsLE a]
    (hX : HomologyIn P X) : IsIso (adj.counit.app X) := by
  rcases hX a with hP | hZ
  · obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero X a
      fun i hi ↦ hi.lt_or_gt.elim (fun h ↦ DerivedCategory.isZero_of_isGE X a i h)
        (fun h ↦ DerivedCategory.isZero_of_isLE X a i h)
    exact isIso_counit_app_of_iso_of_isIso adj e (hε _ hP a)
  · refine isIso_counit_app_of_isZero adj ?_
    have : X.IsGE (a + 1) := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      rcases lt_or_eq_of_le (show i ≤ a by omega) with h | rfl
      · exact DerivedCategory.isZero_of_isGE X a i h
      · exact hZ
    exact DerivedCategory.TStructure.t.isZero X a (a + 1) (by omega)

include hε in
/-- **The bounded case.** The counit is an isomorphism at every object of `D^{[a, a + k]}` all
of whose cohomology objects satisfy `P` or are zero, by induction on `k`. -/
theorem isIso_counit_app_of_isGE_of_isLE (k : ℕ) :
    ∀ (X : _root_.DerivedCategory B) (a : ℤ), X.IsGE a → X.IsLE (a + k) → HomologyIn P X →
      IsIso (adj.counit.app X) := by
  induction k with
  | zero =>
    intro X a hGE hLE hX
    have : X.IsLE a := by simpa using hLE
    exact isIso_counit_app_of_isGE_of_isLE_self adj P hε X a hX
  | succ k ih =>
    intro X a hGE hLE hX
    let T := truncTriangle X (a + k)
    have hT : (G ⋙ F).mapTriangle.obj T ∈ distTriang _ :=
      (G ⋙ F).map_distinguished T (truncTriangle_distinguished X (a + k))
    have : T.obj₁.IsGE a := by
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact (DerivedCategory.isZero_of_isGE X a i hi).of_iso (@asIso _ _ _ _ ((H i).map T.mor₁)
        (isIso_homologyMap_truncTriangle_mor₁ X (a + k) i (by omega)))
    have hY : IsIso (adj.counit.app T.obj₁) :=
      ih T.obj₁ a inferInstance (by dsimp [T]; infer_instance) (hX.truncTriangle_obj₁ _)
    have : T.obj₃.IsLE (a + k + 1) := by
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact (DerivedCategory.isZero_of_isLE X (a + ((k + 1 : ℕ) : ℤ)) i
        (by push_cast; omega)).of_iso (@asIso _ _ _ _ ((H i).map T.mor₂)
          (isIso_homologyMap_truncTriangle_mor₂ X (a + k) i (by omega))).symm
    have : T.obj₃.IsGE (a + k + 1) := by dsimp [T]; infer_instance
    have hZ : IsIso (adj.counit.app T.obj₃) :=
      isIso_counit_app_of_isGE_of_isLE_self adj P hε T.obj₃ (a + k + 1)
        (hX.truncTriangle_obj₃ _)
    change IsIso (adj.counit.app T.obj₂)
    rw [DerivedCategory.isIso_iff]
    intro q
    by_cases hq : q ≤ a + k
    · have h₁ := isIso_homologyMap_truncTriangle_mor₁ X (a + k) q hq
      have h₂ : IsIso ((H q).map ((G ⋙ F).mapTriangle.obj T).mor₁) :=
        isIso_homologyMap_mor₁_of_isZero _ hT q
          (isZero_homology_obj_of_isIso_counit adj (q - 1)
            (DerivedCategory.isZero_of_isGE T.obj₃ (a + k + 1) (q - 1) (by omega)))
          (isZero_homology_obj_of_isIso_counit adj q
            (DerivedCategory.isZero_of_isGE T.obj₃ (a + k + 1) q (by omega)))
      have hnat := (H q).congr_map (adj.counit.naturality T.mor₁)
      simp only [Functor.map_comp, Functor.id_map] at hnat
      have : IsIso ((H q).map ((G ⋙ F).map T.mor₁)) := h₂
      exact isIso_of_comp_eq_comp_left hnat
    · have h₁ := isIso_homologyMap_truncTriangle_mor₂ X (a + k) q (by omega)
      have h₂ : IsIso ((H q).map ((G ⋙ F).mapTriangle.obj T).mor₂) :=
        isIso_homologyMap_mor₂_of_isZero _ hT q
          (isZero_homology_obj_of_isIso_counit adj q
            (DerivedCategory.isZero_of_isLE T.obj₁ (a + k) q (by omega)))
          (isZero_homology_obj_of_isIso_counit adj (q + 1)
            (DerivedCategory.isZero_of_isLE T.obj₁ (a + k) (q + 1) (by omega)))
      have hnat := (H q).congr_map (adj.counit.naturality T.mor₂)
      simp only [Functor.map_comp, Functor.id_map] at hnat
      have : IsIso ((H q).map ((G ⋙ F).map T.mor₂)) := h₂
      exact isIso_of_comp_eq_comp_right hnat.symm

include hε in
/-- **The unbounded case.** Suppose `F` carries morphisms invertible on `H^q` to morphisms
invertible on `H^q`, `G` keeps `D^{≥ n}`, and `G` carries an object of `D^{≤ c}` whose cohomology
objects satisfy `P` or vanish into `D^{≤ c}`. Then the counit is an isomorphism at every object
whose cohomology objects satisfy `P` or vanish: in degree `q` it agrees with the counit at the
bounded object `τ_{≤ q+1} τ_{≥ q-1} X`. -/
theorem isIso_counit_app_of_homologyIn
    (hF : ∀ {Y Y' : _root_.DerivedCategory A} (g : Y ⟶ Y') (q : ℤ),
      IsIso ((DerivedCategory.homologyFunctor A q).map g) → IsIso ((H q).map (F.map g)))
    (hGGE : ∀ (Y : _root_.DerivedCategory B) (n : ℤ), Y.IsGE n → (G.obj Y).IsGE n)
    (hGLE : ∀ (Y : _root_.DerivedCategory B), HomologyIn P Y → ∀ c : ℤ, Y.IsLE c →
      (G.obj Y).IsLE c)
    (X : _root_.DerivedCategory B) (hX : HomologyIn P X) : IsIso (adj.counit.app X) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  -- the truncation `X ⟶ X₁ = τ_{≥ q-1} X`, with first vertex `τ_{≤ q-2} X`
  let T₁ := truncTriangle X (q - 2)
  have hT₁ : G.mapTriangle.obj T₁ ∈ distTriang _ :=
    G.map_distinguished T₁ (truncTriangle_distinguished X (q - 2))
  -- the truncation `X₂ = τ_{≤ q+1} X₁ ⟶ X₁`
  let T₂ := truncTriangle T₁.obj₃ (q + 1)
  have hT₂ : G.mapTriangle.obj T₂ ∈ distTriang _ :=
    G.map_distinguished T₂ (truncTriangle_distinguished T₁.obj₃ (q + 1))
  have hX₂ : HomologyIn P T₂.obj₁ := (hX.truncTriangle_obj₃ _).truncTriangle_obj₁ _
  -- the counit at the bounded `X₂`
  have : T₁.obj₃.IsGE (q - 2 + 1) := inferInstance
  have : T₂.obj₁.IsGE (q - 2 + 1) := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    by_cases hi' : i ≤ q + 1
    · exact (DerivedCategory.isZero_of_isGE T₁.obj₃ (q - 2 + 1) i hi).of_iso
        (@asIso _ _ _ _ ((H i).map T₂.mor₁)
          (isIso_homologyMap_truncTriangle_mor₁ _ (q + 1) i hi'))
    · exact DerivedCategory.isZero_of_isLE _ (q + 1) i (by omega)
  have : T₂.obj₁.IsLE (q + 1) := inferInstance
  have hε₂ : IsIso (adj.counit.app T₂.obj₁) :=
    isIso_counit_app_of_isGE_of_isLE adj P hε 3 T₂.obj₁ (q - 2 + 1)
      inferInstance (DerivedCategory.TStructure.t.isLE_of_le _ (q + 1) _ (by omega)) hX₂
  -- `H^q` of the two truncation maps, before and after `G`
  have hm₁ : IsIso ((H q).map T₁.mor₂) :=
    isIso_homologyMap_truncTriangle_mor₂ X (q - 2) q (by omega)
  have hm₂ : IsIso ((H q).map T₂.mor₁) :=
    isIso_homologyMap_truncTriangle_mor₁ T₁.obj₃ (q + 1) q (by omega)
  have hG₁ : (G.obj T₁.obj₁).IsLE (q - 2) :=
    hGLE _ (hX.truncTriangle_obj₁ _) (q - 2) inferInstance
  have hG₂ : (G.obj T₂.obj₃).IsGE (q + 1 + 1) := hGGE _ _ inferInstance
  have hGm₁ : IsIso ((DerivedCategory.homologyFunctor A q).map (G.map T₁.mor₂)) :=
    isIso_homologyMap_mor₂_of_isZero _ hT₁ q
      (DerivedCategory.isZero_of_isLE (G.obj T₁.obj₁) (q - 2) q (by omega))
      (DerivedCategory.isZero_of_isLE (G.obj T₁.obj₁) (q - 2) (q + 1) (by omega))
  have hGm₂ : IsIso ((DerivedCategory.homologyFunctor A q).map (G.map T₂.mor₁)) :=
    isIso_homologyMap_mor₁_of_isZero _ hT₂ q
      (DerivedCategory.isZero_of_isGE (G.obj T₂.obj₃) (q + 1 + 1) (q - 1) (by omega))
      (DerivedCategory.isZero_of_isGE (G.obj T₂.obj₃) (q + 1 + 1) q (by omega))
  have hFm₁ := hF _ q hGm₁
  have hFm₂ := hF _ q hGm₂
  -- naturality of the counit along the two maps
  have hn₁ := (H q).congr_map (adj.counit.naturality T₁.mor₂)
  have hn₂ := (H q).congr_map (adj.counit.naturality T₂.mor₁)
  simp only [Functor.map_comp, Functor.id_map, Functor.comp_map] at hn₁ hn₂
  have h₂ : IsIso ((H q).map (adj.counit.app T₂.obj₂)) := isIso_of_comp_eq_comp_left hn₂
  have h₂' : IsIso ((H q).map (adj.counit.app T₁.obj₃)) := h₂
  change IsIso ((H q).map (adj.counit.app T₁.obj₂))
  exact isIso_of_comp_eq_comp_right hn₁.symm

end Counit

end Stacks.DerivedCategory.AdjunctionUnitTruncations

end

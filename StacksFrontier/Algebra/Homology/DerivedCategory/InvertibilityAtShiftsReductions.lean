module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.StupidTruncationLE
public import StacksFrontier.Homology.KFlat.BifunctorTruncationGE
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility

/-!
# Invertibility of a natural transformation from its values on single objects

Let `η : H₁ ⟶ H₂` be a natural transformation between two exact functors `D(C) ⥤ D(D)` of derived
categories. Nothing is assumed about the compatibility of `η` with the shifts. This file proves
the two reductions with which the proofs of the Künneth section of the étale cohomology chapter
pass from complexes to single objects ([Stacks, Tag 0F1J], first two paragraphs of the proof):

* **canonical truncations, for bounded below objects.** If both functors carry `D^{≥m}` into
  `D^{≥m+c}` for a fixed `c`, and `η` is invertible at every object of `C` placed in any single
  degree, then `η` is invertible at every bounded below object.
* **stupid truncations, for bounded below complexes.** If `K` is a complex vanishing below some
  degree, `η` is invertible at every term of `K` placed in any single degree, and both functors
  carry the stupid truncations `σ^{≥N}K` into `D^{≥N+c}` for a fixed `c`, then `η` is invertible at
  `K`. This is the source's argument: `σ^{≥N}K ⟶ K ⟶ σ^{≤N-1}K` is a distinguished triangle whose
  first vertex does not reach the degrees below `N + c` after applying `H₁` or `H₂`, and
  `σ^{≤N-1}K` is built from its finitely many terms by distinguished triangles.

## The invertibility locus at all shifts

Without a compatibility of `η` with the shift, the objects at which `η` is invertible need not be
stable under the shift. The objects `K` such that `η` is invertible at *every* shift of `K` are,
and they pass from two vertices of a distinguished triangle to the third by the five lemma
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts`. That is the
strictly full triangulated subcategory both arguments run in
(`CategoryTheory.NatTrans.isoLocusAtShifts`). The hypothesis "invertible at an object placed in
any single degree" is the same as "invertible at every shift of it placed in degree zero",
because `M` placed in degree `k` is `M` placed in degree zero shifted by `-k`.

## Main definitions

* `CategoryTheory.NatTrans.isoLocusAtShifts`: the objects at every shift of which `η` is
  invertible.

## Main results

* `CategoryTheory.NatTrans.isIso_app_of_isGE_of_isIso_app_singleFunctor`: the reduction along
  canonical truncations.
* `CategoryTheory.NatTrans.isIso_app_Q_obj_of_isIso_app_singleFunctor_X`: the reduction along
  stupid truncations.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u v' u'

namespace CategoryTheory.NatTrans

open DerivedCategory ObjectProperty

section Locus

variable {A B : Type*} [Category* A] [Category* B]
  [HasShift A ℤ] [HasShift B ℤ] [Preadditive A] [Preadditive B]
  [HasZeroObject A] [HasZeroObject B]
  [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
  [Pretriangulated A] [Pretriangulated B]
  {H₁ H₂ : A ⥤ B} (η : H₁ ⟶ H₂)

/-- **The objects at every shift of which `η` is invertible.** Unlike the objects at which `η` is
invertible, these are stable under the shift for every `η`, compatible with the shift or not. -/
def isoLocusAtShifts : ObjectProperty A := fun K => ∀ n : ℤ, IsIso (η.app (K⟦n⟧))

/-- The invertibility locus of `η` at all shifts is closed under isomorphisms. -/
instance isoLocusAtShifts_isClosedUnderIsomorphisms :
    (isoLocusAtShifts η).IsClosedUnderIsomorphisms where
  of_iso e hK n := (η.isIso_app_iff_of_iso ((shiftFunctor A n).mapIso e)).1 (hK n)

/-- The invertibility locus of `η` at all shifts is stable under every shift. -/
instance isoLocusAtShifts_isStableUnderShift : (isoLocusAtShifts η).IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun K hK n =>
    (η.isIso_app_iff_of_iso ((shiftFunctorAdd A a n).app K)).1 (hK (a + n))⟩

/-- For triangulated functors `H₁` and `H₂`, the invertibility locus of `η` at all shifts contains
the middle vertex of a distinguished triangle whose other two vertices lie in it. -/
instance isoLocusAtShifts_isTriangulatedClosed₂ [H₁.CommShift ℤ] [H₂.CommShift ℤ]
    [H₁.IsTriangulated] [H₂.IsTriangulated] :
    (isoLocusAtShifts η).IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _
    (Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_middle_of_all_shifts
      H₁ H₂ η T hT h₁ h₃)

omit [HasShift B ℤ] [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
  [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
  [Pretriangulated A] [Pretriangulated B] in
/-- An object of the locus is a point of invertibility. -/
theorem isIso_app_of_isoLocusAtShifts {K : A} (hK : isoLocusAtShifts η K) : IsIso (η.app K) :=
  (η.isIso_app_iff_of_iso ((shiftFunctorZero A ℤ).app K)).1 (hK 0)

end Locus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory D]
  {H₁ H₂ : DerivedCategory C ⥤ DerivedCategory D}
  [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated]
  (η : H₁ ⟶ H₂)

omit [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated] in
/-- An object `M` of `C` placed in degree zero lies in the invertibility locus at all shifts as
soon as `η` is invertible at `M` placed in every single degree. -/
theorem isoLocusAtShifts_singleFunctor_obj {M : C}
    (hM : ∀ k : ℤ, IsIso (η.app ((singleFunctor C k).obj M))) (k : ℤ) :
    isoLocusAtShifts η ((singleFunctor C k).obj M) := fun n =>
  (η.isIso_app_iff_of_iso (((singleFunctors C).shiftIso n (k - n) k (by omega)).app M)).2
    (hM (k - n))

/-- The naturality square of `η` at `g` on `H^q`. -/
private theorem homologyMap_map_comp_app {H₁ H₂ : DerivedCategory C ⥤ DerivedCategory D}
    (η : H₁ ⟶ H₂) {X Y : DerivedCategory C} (g : X ⟶ Y) (q : ℤ) :
    (homologyFunctor D q).map (H₁.map g) ≫ (homologyFunctor D q).map (η.app Y) =
      (homologyFunctor D q).map (η.app X) ≫ (homologyFunctor D q).map (H₂.map g) := by
  simp only [← Functor.map_comp, η.naturality]

omit [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated] in
/-- The naturality square of `η` at `g : A ⟶ B` on `H^q`, read from the target: if `H₁ g` and
`H₂ g` are invertible on `H^q` and `η` is invertible on `H^q` at `B`, it is so at `A`. -/
theorem isIso_homologyMap_app_of_isIso_target {X Y : DerivedCategory C} (g : X ⟶ Y) (q : ℤ)
    (h₁ : IsIso ((homologyFunctor D q).map (H₁.map g)))
    (h₂ : IsIso ((homologyFunctor D q).map (H₂.map g)))
    (hY : IsIso ((homologyFunctor D q).map (η.app Y))) :
    IsIso ((homologyFunctor D q).map (η.app X)) := by
  have : IsIso ((homologyFunctor D q).map (η.app X) ≫ (homologyFunctor D q).map (H₂.map g)) := by
    rw [← homologyMap_map_comp_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((homologyFunctor D q).map (H₂.map g))

omit [H₁.CommShift ℤ] [H₂.CommShift ℤ] [H₁.IsTriangulated] [H₂.IsTriangulated] in
/-- The naturality square of `η` at `g : A ⟶ B` on `H^q`, read from the source: if `H₁ g` and
`H₂ g` are invertible on `H^q` and `η` is invertible on `H^q` at `A`, it is so at `B`. -/
theorem isIso_homologyMap_app_of_isIso_source {X Y : DerivedCategory C} (g : X ⟶ Y) (q : ℤ)
    (h₁ : IsIso ((homologyFunctor D q).map (H₁.map g)))
    (h₂ : IsIso ((homologyFunctor D q).map (H₂.map g)))
    (hX : IsIso ((homologyFunctor D q).map (η.app X))) :
    IsIso ((homologyFunctor D q).map (η.app Y)) := by
  have : IsIso ((homologyFunctor D q).map (H₁.map g) ≫ (homologyFunctor D q).map (η.app Y)) := by
    rw [homologyMap_map_comp_app]
    infer_instance
  exact IsIso.of_isIso_comp_left ((homologyFunctor D q).map (H₁.map g)) _

/-- **Invertibility on bounded below objects, from invertibility on single objects** — the
reduction along canonical truncations of [Stacks, Tag 0F1J], for a natural transformation with no
assumed compatibility with the shift. Let `H₁` and `H₂` be exact functors `D(C) ⥤ D(D)` carrying
`D^{≥m}` into `D^{≥m+c}` for a fixed `c`, and let `η : H₁ ⟶ H₂` be invertible at every object of
`C` placed in any single degree. Then `η` is invertible at every bounded below object.

Fix a degree `q` and truncate `K ∈ D^{≥a}` at `t ≥ q + 1 - c`: the truncation `τ^{<t}K` has
cohomology in the window `[a, t - 1]`, so it lies in the invertibility locus at all shifts
(`CategoryTheory.ObjectProperty.prop_of_isGE_of_isLE`), while `τ^{≥t}K` is carried into
`D^{≥q+1}` by both functors, so that both are invertible on `H^q` along `τ^{<t}K ⟶ K`. -/
theorem isIso_app_of_isGE_of_isIso_app_singleFunctor (c : ℤ)
    (hH₁ : ∀ (L : DerivedCategory C) (m : ℤ), L.IsGE m → (H₁.obj L).IsGE (m + c))
    (hH₂ : ∀ (L : DerivedCategory C) (m : ℤ), L.IsGE m → (H₂.obj L).IsGE (m + c))
    (hsingle : ∀ (M : C) (k : ℤ), IsIso (η.app ((singleFunctor C k).obj M)))
    (K : DerivedCategory C) (a : ℤ) (hK : K.IsGE a) : IsIso (η.app K) := by
  have := hK
  rw [isIso_iff]
  intro q
  let t : ℤ := max (q + 1 - c) (a + 1)
  have hT := TStructure.t.triangleLTGE_distinguished t K
  have hU : isoLocusAtShifts η ((TStructure.t.truncLT t).obj K) := by
    refine (isoLocusAtShifts η).prop_of_isGE_of_isLE a (t - 1 - a).toNat _ inferInstance ?_
      fun p hp₁ hp₂ ↦ isoLocusAtShifts_singleFunctor_obj η (hsingle _) 0
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ t - 1 - a)]
    exact TStructure.t.isLE_truncLT_obj K t (a + (t - 1 - a)) (by omega)
  have hV : ((TStructure.t.truncGE t).obj K).IsGE t := inferInstance
  have h₁ : IsIso ((homologyFunctor D q).map (H₁.map ((TStructure.t.truncLTι t).app K))) :=
    isIso_homologyMap_mor₁_of_isGE₃ _ (H₁.map_distinguished _ hT) q (t + c)
      (hH₁ _ t hV) (by omega)
  have h₂ : IsIso ((homologyFunctor D q).map (H₂.map ((TStructure.t.truncLTι t).app K))) :=
    isIso_homologyMap_mor₁_of_isGE₃ _ (H₂.map_distinguished _ hT) q (t + c)
      (hH₂ _ t hV) (by omega)
  have : IsIso (η.app ((TStructure.t.truncLT t).obj K)) := isIso_app_of_isoLocusAtShifts η hU
  exact isIso_homologyMap_app_of_isIso_source η ((TStructure.t.truncLTι t).app K) q h₁ h₂
    inferInstance

open StacksDraft.StupidTruncation HomologicalComplex ComplexShape in
/-- The stupid truncations `σ^{≤M}K` of a complex `K` vanishing below `a` lie in the
invertibility locus at all shifts of `η`, as soon as every term of `K` placed in any single degree
does: `σ^{≤a-1}K` is zero, and `σ^{≤p}K` is an extension of `σ^{≤p-1}K` by `Kᵖ` placed in degree
`p`. -/
theorem isoLocusAtShifts_stupidTruncLE (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hsingle : ∀ p k : ℤ, IsIso (η.app ((singleFunctor C k).obj (K.X p)))) :
    ∀ n : ℕ, isoLocusAtShifts η (Q.obj (K.stupidTrunc (embeddingUpIntLE (a - 1 + n)))) := by
  intro n
  induction n with
  | zero =>
    intro m
    have hZ : IsZero ((Q.obj (K.stupidTrunc (embeddingUpIntLE (a - 1 + ((0 : ℕ) : ℤ)))))⟦m⟧) := by
      refine Functor.map_isZero _ (Functor.map_isZero _ ?_)
      rw [HomologicalComplex.isZero_stupidTrunc_iff]
      exact ⟨fun i => CochainComplex.isZero_of_isStrictlyGE K a _ (by
        show a - 1 + ((0 : ℕ) : ℤ) - (i : ℤ) < a
        omega)⟩
    exact IsZero.isIso (Functor.map_isZero _ hZ) (Functor.map_isZero _ hZ) _
  | succ n ih =>
    have hp : (a - 1 + (n : ℤ)) + 1 = a - 1 + ((n + 1 : ℕ) : ℤ) := by omega
    have hS := stupidTruncLEShortComplex_shortExact K (a - 1 + ((n + 1 : ℕ) : ℤ))
      (a - 1 + (n : ℤ)) hp
    exact (isoLocusAtShifts η).ext_of_isTriangulatedClosed₂ _
      (triangleOfSES_distinguished hS) (isoLocusAtShifts_singleFunctor_obj η (hsingle _) _) ih

open StacksDraft.StupidTruncation HomologicalComplex ComplexShape in
/-- **Invertibility on a bounded below complex, from invertibility on its terms** — the reduction
along stupid truncations of [Stacks, Tag 0F1J], for a natural transformation with no assumed
compatibility with the shift. Let `K` be a complex vanishing below `a`, let `η` be invertible at
every term of `K` placed in any single degree, and suppose that for a fixed `c` both functors
carry every stupid truncation `σ^{≥N}K` into `D^{≥N+c}`. Then `η` is invertible at `K`.

Fix a degree `q` and take `N` with `N + c > q + 1`. In the distinguished triangle of the short
exact sequence `0 ⟶ σ^{≥N}K ⟶ K ⟶ σ^{≤N-1}K ⟶ 0`, carried by `H₁` and `H₂`, the first vertex lies
in `D^{≥N+c}`, so both functors of the projection `K ⟶ σ^{≤N-1}K` are invertible on `H^q`; and
`η` is invertible at the bounded complex `σ^{≤N-1}K` (`isoLocusAtShifts_stupidTruncLE`). -/
theorem isIso_app_Q_obj_of_isIso_app_singleFunctor_X (K : CochainComplex C ℤ) (a c : ℤ)
    [K.IsStrictlyGE a]
    (hsingle : ∀ p k : ℤ, IsIso (η.app ((singleFunctor C k).obj (K.X p))))
    (hbound₁ : ∀ N : ℤ, (H₁.obj (Q.obj (K.stupidTrunc (embeddingUpIntGE N)))).IsGE (N + c))
    (hbound₂ : ∀ N : ℤ, (H₂.obj (Q.obj (K.stupidTrunc (embeddingUpIntGE N)))).IsGE (N + c)) :
    IsIso (η.app (Q.obj K)) := by
  rw [isIso_iff]
  intro q
  let N : ℤ := max (q + 2 - c) a
  have hT := triangleOfSES_distinguished (stupidTruncGELEShortComplex_shortExact K N)
  have h₁ : IsIso ((homologyFunctor D q).map (H₁.map
      (Q.map (K.πStupidTrunc (embeddingUpIntLE (N - 1)))))) :=
    isIso_homologyMap_mor₂_of_isGE₁ _ (H₁.map_distinguished _ hT) q (N + c) (hbound₁ N)
      (by omega)
  have h₂ : IsIso ((homologyFunctor D q).map (H₂.map
      (Q.map (K.πStupidTrunc (embeddingUpIntLE (N - 1)))))) :=
    isIso_homologyMap_mor₂_of_isGE₁ _ (H₂.map_distinguished _ hT) q (N + c) (hbound₂ N)
      (by omega)
  have hloc := isoLocusAtShifts_stupidTruncLE η K a hsingle (N - a).toNat
  have hNa : a - 1 + (((N - a).toNat : ℕ) : ℤ) = N - 1 := by omega
  rw [hNa] at hloc
  have : IsIso (η.app (Q.obj (K.stupidTrunc (embeddingUpIntLE (N - 1))))) :=
    isIso_app_of_isoLocusAtShifts η hloc
  exact isIso_homologyMap_app_of_isIso_target η
    (Q.map (K.πStupidTrunc (embeddingUpIntLE (N - 1)))) q h₁ h₂ inferInstance

end CategoryTheory.NatTrans

end

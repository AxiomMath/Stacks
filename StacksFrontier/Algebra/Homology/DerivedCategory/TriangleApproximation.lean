module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Cohomological approximation and the third vertex of a distinguished triangle

Let `A` be an abelian category and `T` a distinguished triangle of `D(A)`. Call `T.mor₁` an
*approximation in degree `m`* when it is an isomorphism on cohomology in every degree `> m`
and a surjection on cohomology in degree `m`. This file records that this happens exactly
when the third vertex of `T` lies in `D^{≤ m - 1}(A)`: the long exact cohomology sequence
turns each condition into the other.

Both directions are used to transport an approximation along an exact functor of triangulated
categories: the functor is applied to the triangle, the third vertex is bounded above by a
right t-exactness statement about the functor, and the dictionary is read back. That transport
is `DerivedCategory.approximation_of_isLE_functor`, and the two remaining lemmas are the
bookkeeping its consumers need around it: an approximation in degree `s` is a surjection on
cohomology in every degree above `s`, and an object approximated above `s` by a complex with no
terms above `c` lies in `D^{≤ max s c}`.

## Main results

* `DerivedCategory.triangle_obj₃_isLE_of_approximation`: an approximation in degree `m` has
  third vertex in `D^{≤ m - 1}(A)`.
* `DerivedCategory.approximation_of_triangle_isLE`: conversely, a triangle with third vertex
  in `D^{≤ m - 1}(A)` has first map an approximation in degree `m`.
* `DerivedCategory.approximation_of_isLE_functor`: an exact functor which shifts the upper
  bound by `e` shifts an approximation by `e`.
* `DerivedCategory.epi_homologyMap_of_le`: an approximation in degree `s` is a surjection on
  cohomology in every degree `≥ s`.
* `DerivedCategory.isLE_Q_obj_of_approximation` and
  `DerivedCategory.isLE_Q_obj_of_homologyMap_approximation`: an object approximated above `s`
  by a complex with no terms above `c` lies in `D^{≤ max s c}`, for an approximation given in
  the derived category resp. by a morphism of complexes.

## Implementation notes

This is the dual of Stacks 05TC read in the derived category rather than at the level of
complexes, which is why it is stated about an arbitrary distinguished triangle rather than
about a mapping cone: the consumers obtain their triangles from
`CategoryTheory.Pretriangulated.distinguished_cocone_triangle` and from the image of a
triangle under an exact functor, neither of which is a mapping cone on the nose.

## References

* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- An approximation in degree `s` is a surjection on cohomology in every degree `t ≥ s`. -/
private theorem epi_homologyMap_of_approximation {Y Z : DerivedCategory A} (φ : Y ⟶ Z) (s t : ℤ)
    (hst : s ≤ t) (hiso : ∀ i : ℤ, s < i → IsIso ((homologyFunctor A i).map φ))
    (hepi : Epi ((homologyFunctor A s).map φ)) : Epi ((homologyFunctor A t).map φ) := by
  rcases eq_or_lt_of_le hst with rfl | h
  · exact hepi
  · have := hiso t h
    infer_instance

/-- **One half of the dual of Stacks 05TC.** If the first map of a distinguished triangle of
the derived category is an isomorphism on cohomology in degrees `> m` and a surjection in
degree `m`, then its third vertex is `≤ m - 1`: the long exact cohomology sequence forces
every cohomology object of `T.obj₃` in degree `≥ m` to sit between a zero map out of it and a
zero connecting map into it. -/
theorem triangle_obj₃_isLE_of_approximation
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (m : ℤ)
    (hiso : ∀ i : ℤ, m < i → IsIso ((homologyFunctor A i).map T.mor₁))
    (hepi : Epi ((homologyFunctor A m).map T.mor₁)) :
    T.obj₃.IsLE (m - 1) := by
  rw [isLE_iff]
  intro i hi
  have hi' : m ≤ i := by omega
  have hαepi := epi_homologyMap_of_approximation T.mor₁ m i hi' hiso hepi
  have hβ : (homologyFunctor A i).map T.mor₂ = 0 :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).1 hαepi
  have hδα : HomologySequence.δ T i (i + 1) rfl = 0 := by
    apply (HomologySequence.mono_homologyMap_mor₁_iff T hT i (i + 1) rfl).1
    exact @IsIso.mono_of_iso _ _ _ _ _ (hiso (i + 1) (by omega))
  exact (HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_zeros hβ hδα

/-- **The other half of the dual of Stacks 05TC.** If the third vertex of a distinguished
triangle of the derived category is `≤ m - 1`, then its first map is an isomorphism on
cohomology in degrees `> m` and a surjection in degree `m`. -/
theorem approximation_of_triangle_isLE
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang _) (m : ℤ)
    (hLE : T.obj₃.IsLE (m - 1)) :
    (∀ i : ℤ, m < i → IsIso ((homologyFunctor A i).map T.mor₁)) ∧
      Epi ((homologyFunctor A m).map T.mor₁) := by
  have := hLE
  have hepi : ∀ i : ℤ, m ≤ i → Epi ((homologyFunctor A i).map T.mor₁) := fun i hi ↦ by
    rw [HomologySequence.epi_homologyMap_mor₁_iff T hT i]
    exact (isZero_of_isLE T.obj₃ (m - 1) i (by omega)).eq_of_tgt _ _
  refine ⟨fun i hi ↦ ?_, hepi m le_rfl⟩
  · have := hepi i hi.le
    have : Mono ((homologyFunctor A i).map T.mor₁) := by
      rw [HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)]
      exact (isZero_of_isLE T.obj₃ (m - 1) (i - 1) (by omega)).eq_of_src _ _
    exact isIso_of_mono_of_epi _

/-- **An exact functor which shifts the upper bound by `e` shifts a cohomological approximation
by `e`.** If `F` takes `D^{≤ c}(A)` into `D^{≤ c + e}(A)` for every `c` and `φ` is an
approximation in degree `s`, then `F.map φ` is an approximation in degree `s + e`: the third
vertex of a cocone triangle of `φ` is `≤ s - 1`, so its image under `F` is `≤ s + e - 1`, and
the dictionary above is read backwards on the image triangle. -/
theorem approximation_of_isLE_functor
    (F : DerivedCategory A ⥤ DerivedCategory A) [F.CommShift ℤ] [F.IsTriangulated] (e : ℤ)
    (hF : ∀ (Z : DerivedCategory A) (c : ℤ), Z.IsLE c → (F.obj Z).IsLE (c + e))
    {Y Z : DerivedCategory A} (φ : Y ⟶ Z) (s : ℤ)
    (hiso : ∀ i : ℤ, s < i → IsIso ((homologyFunctor A i).map φ))
    (hepi : Epi ((homologyFunctor A s).map φ)) :
    (∀ i : ℤ, s + e < i → IsIso ((homologyFunctor A i).map (F.map φ))) ∧
      Epi ((homologyFunctor A (s + e)).map (F.map φ)) := by
  obtain ⟨Cn, g, h, hT⟩ := distinguished_cocone_triangle φ
  have hC : Cn.IsLE (s - 1) := triangle_obj₃_isLE_of_approximation _ hT s hiso hepi
  have hFC₀ := hF Cn (s - 1) hC
  have hFC : (F.obj Cn).IsLE (s + e - 1) :=
    TStructure.t.isLE_of_le _ (s - 1 + e) (s + e - 1) (by omega)
  exact approximation_of_triangle_isLE _ (F.map_distinguished _ hT) (s + e) hFC

/-- An approximation in degree `s` is in particular a surjection on cohomology in every
degree `t ≥ s`. -/
theorem epi_homologyMap_of_le {Y Z : DerivedCategory A} (φ : Y ⟶ Z) (s t : ℤ) (hst : s ≤ t)
    (hiso : ∀ i : ℤ, s < i → IsIso ((homologyFunctor A i).map φ))
    (hepi : Epi ((homologyFunctor A s).map φ)) :
    Epi ((homologyFunctor A t).map φ) :=
  epi_homologyMap_of_approximation φ s t hst hiso hepi

/-- **An object whose cohomology agrees above `s` with that of a complex having no terms above
`c` lies in `D^{≤ max s c}`.** Above `max s c` the cohomology of the complex vanishes for
degree reasons and the comparison map is an isomorphism there. -/
theorem isLE_Q_obj_of_approximation {P K : CochainComplex A ℤ} (s c : ℤ)
    (hPz : ∀ j : ℤ, c < j → IsZero (P.X j)) (α : Q.obj P ⟶ Q.obj K)
    (hiso : ∀ j : ℤ, s < j → IsIso ((homologyFunctor A j).map α)) :
    (Q.obj K).IsLE (max s c) := by
  have hPs : P.IsStrictlyLE c := (CochainComplex.isStrictlyLE_iff P c).2 hPz
  have := hPs
  rw [isLE_iff]
  intro j hj
  have h3 : IsIso ((homologyFunctor A j).map α) := hiso j (by omega)
  exact (isZero_of_isLE (Q.obj P) c j (by omega)).of_iso
    (asIso ((homologyFunctor A j).map α)).symm

/-- `DerivedCategory.isLE_Q_obj_of_approximation` for an approximation given by a morphism of
complexes: if `α : P ⟶ K` is invertible on homology above `s` and `P` has no terms above `c`,
then the class of `K` lies in `D^{≤ max s c}`. -/
theorem isLE_Q_obj_of_homologyMap_approximation {P K : CochainComplex A ℤ} (s c : ℤ)
    (hPz : ∀ j : ℤ, c < j → IsZero (P.X j)) (α : P ⟶ K)
    (hiso : ∀ j : ℤ, s < j → IsIso (HomologicalComplex.homologyMap α j)) :
    (Q.obj K).IsLE (max s c) :=
  isLE_Q_obj_of_approximation s c hPz (Q.map α) fun j hj =>
    (NatIso.isIso_map_iff (homologyFunctorFactors A j) α).mpr (hiso j hj)

end DerivedCategory

end

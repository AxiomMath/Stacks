module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# A triangulated functor applied to a short exact sequence, in positive degrees

Let `F : D(𝒜) ⥤ D(ℬ)` be a triangulated functor between derived categories of abelian
categories and let `0 ⟶ K ⟶ M ⟶ N ⟶ 0` be a short exact sequence in `𝒜`, read in degree `0`.
The distinguished triangle `K ⟶ M ⟶ N ⟶ K[1]` goes to a distinguished triangle, whose long exact
cohomology sequence relates the maps `H^q(F(M)) ⟶ H^q(F(N))` to the objects `H^q(F(K))`:

* if `H^q(F(K)) = 0` for every `q ≥ 1`, then `H^q(F(M)) ⟶ H^q(F(N))` is an isomorphism for every
  `q ≥ 1`;
* conversely, if `H^q(F(M)) ⟶ H^q(F(N))` is an isomorphism for every `q ≥ 1` and an epimorphism
  for `q = 0`, then `H^q(F(K)) = 0` for every `q ≥ 1`.

This is the form in which a statement "`F(M) ⟶ F(N)` is an isomorphism on cohomology in degrees
`≥ 1`" about a surjection `M ⟶ N` becomes a vanishing statement about its kernel; for
`F = Rf_*` it is the long exact sequence of higher direct images.

## Main results

* `CategoryTheory.ShortComplex.ShortExact.isIso_homologyFunctor_map_g_of_isZero`
* `CategoryTheory.ShortComplex.ShortExact.isZero_homologyFunctor_obj_X₁_of_isIso`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' v v' u u'

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ] [F.IsTriangulated]
  {S : ShortComplex C} (hS : S.ShortExact)

/-- The image under a triangulated functor of the triangle of a short exact sequence placed in
degree `0` is distinguished. -/
theorem mapTriangle_singleTriangle_distinguished :
    F.mapTriangle.obj hS.singleTriangle ∈ distTriang (DerivedCategory D) :=
  F.map_distinguished _ hS.singleTriangle_distinguished

include hS in
/-- **Vanishing on the kernel gives isomorphisms in positive degrees.** If `H^q(F(K)) = 0` for
every `q ≥ 1`, then `H^q(F(M)) ⟶ H^q(F(N))` is an isomorphism for every `q ≥ 1`. -/
theorem isIso_homologyFunctor_map_g_of_isZero
    (hK : ∀ q : ℤ, 1 ≤ q → IsZero ((DerivedCategory.homologyFunctor D q).obj
      (F.obj ((DerivedCategory.singleFunctor C 0).obj S.X₁))))
    (q : ℤ) (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor D q).map
      (F.map ((DerivedCategory.singleFunctor C 0).map S.g))) := by
  have hT := mapTriangle_singleTriangle_distinguished F hS
  have hmono : Mono ((DerivedCategory.homologyFunctor D q).map
      (F.mapTriangle.obj hS.singleTriangle).mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hT q).2
      ((hK q hq).eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor D q).map
      (F.mapTriangle.obj hS.singleTriangle).mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT q (q + 1)).2
      ((hK (q + 1) (by omega)).eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

include hS in
/-- **Isomorphisms in positive degrees give vanishing on the kernel.** If
`H^q(F(M)) ⟶ H^q(F(N))` is an isomorphism for every `q ≥ 1` and an epimorphism for `q = 0`,
then `H^q(F(K)) = 0` for every `q ≥ 1`. -/
theorem isZero_homologyFunctor_obj_X₁_of_isIso
    (h : ∀ q : ℤ, 1 ≤ q → IsIso ((DerivedCategory.homologyFunctor D q).map
      (F.map ((DerivedCategory.singleFunctor C 0).map S.g))))
    (h₀ : Epi ((DerivedCategory.homologyFunctor D 0).map
      (F.map ((DerivedCategory.singleFunctor C 0).map S.g))))
    (q : ℤ) (hq : 1 ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor D q).obj
      (F.obj ((DerivedCategory.singleFunctor C 0).obj S.X₁))) := by
  have hT := mapTriangle_singleTriangle_distinguished F hS
  have hepi : Epi ((DerivedCategory.homologyFunctor D (q - 1)).map
      (F.mapTriangle.obj hS.singleTriangle).mor₂) := by
    rcases eq_or_lt_of_le hq with hq1 | hq1
    · subst hq1
      exact h₀
    · have := h (q - 1) (by omega)
      change Epi ((DerivedCategory.homologyFunctor D (q - 1)).map
        (F.map ((DerivedCategory.singleFunctor C 0).map S.g)))
      infer_instance
  have hmono : Mono ((DerivedCategory.homologyFunctor D q).map
      (F.mapTriangle.obj hS.singleTriangle).mor₂) := by
    have := h q hq
    change Mono ((DerivedCategory.homologyFunctor D q).map
      (F.map ((DerivedCategory.singleFunctor C 0).map S.g)))
    infer_instance
  have hδ := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT (q - 1) q
    (by omega)).1 hepi
  have hmor₁ := (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hT q).1 hmono
  exact (DerivedCategory.HomologySequence.exact₁ _ hT (q - 1) q (by omega)).isZero_of_both_zeros
    hδ hmor₁

end CategoryTheory.ShortComplex.ShortExact

end

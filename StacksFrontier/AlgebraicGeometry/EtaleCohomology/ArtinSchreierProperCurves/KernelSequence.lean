module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The cohomology of a triangulated image of a short exact sequence as a kernel

Let `0 ⟶ A ⟶ B ⟶ C ⟶ 0` be a short exact sequence in an abelian category and let `R` be a
triangulated functor between derived categories. If `Hᵠ⁻¹(R(B)) ⟶ Hᵠ⁻¹(R(C))` is an
epimorphism, the long exact cohomology sequence of the distinguished triangle
`R(A) ⟶ R(B) ⟶ R(C) ⟶` identifies `Hᵠ(R(A))` with the kernel of `Hᵠ(R(B)) ⟶ Hᵠ(R(C))`.

This is the step of the Artin–Schreier argument of [Stacks, Tag 0GKV], case (b), which reads
`R¹f_*(𝐙/p𝐙)` as the kernel of `F - 1` on `R¹f_*𝒪_X` and shows that `Rᵠf_*(𝐙/p𝐙)` vanishes
for `q ≥ 2`.

## Main results

* `DerivedCategory.isIso_kernelLift_homologyMap_of_shortExact`: the comparison of `Hᵠ(R(A))` with
  the kernel is an isomorphism.
* `DerivedCategory.isZero_homology_of_shortExact`: `Hᵠ(R(A))` vanishes when `Hᵠ(R(B))` does and
  `Hᵠ⁻¹(R(B)) ⟶ Hᵠ⁻¹(R(C))` is an epimorphism.

## References

* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated

namespace DerivedCategory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (R : DerivedCategory C ⥤ DerivedCategory D) [R.CommShift ℤ] [R.IsTriangulated]
  {S : ShortComplex C} (hS : S.ShortExact) (q₀ q : ℤ) (hq : q₀ + 1 = q)

/-- If `Hᵠ⁻¹(R(B)) ⟶ Hᵠ⁻¹(R(C))` is an epimorphism, then `Hᵠ(R(A)) ⟶ Hᵠ(R(B))` is a
monomorphism. -/
private theorem mono_homologyMap_map_f_of_epi (hS : S.ShortExact) (hq : q₀ + 1 = q)
    (h : Epi ((homologyFunctor D q₀).map (R.map ((singleFunctor C 0).map S.g)))) :
    Mono ((homologyFunctor D q).map (R.map ((singleFunctor C 0).map S.f))) :=
  let T := R.mapTriangle.obj hS.singleTriangle
  let hT : T ∈ distTriang _ := R.map_distinguished _ hS.singleTriangle_distinguished
  (HomologySequence.mono_homologyMap_mor₁_iff T hT q₀ q hq).2
    ((HomologySequence.epi_homologyMap_mor₂_iff T hT q₀ q hq).1 h)

include hS hq in
/-- **The kernel step of a long exact cohomology sequence.** For a short exact sequence
`0 ⟶ A ⟶ B ⟶ C ⟶ 0` and a triangulated functor `R`, if `Hᵠ⁻¹(R(B)) ⟶ Hᵠ⁻¹(R(C))` is an
epimorphism then `Hᵠ(R(A)) ⟶ Hᵠ(R(B))` is a kernel of `Hᵠ(R(B)) ⟶ Hᵠ(R(C))`: the comparison
`kernel.lift` is an isomorphism. -/
theorem isIso_kernelLift_homologyMap_of_shortExact
    (h : Epi ((homologyFunctor D q₀).map (R.map ((singleFunctor C 0).map S.g)))) :
    IsIso (kernel.lift ((homologyFunctor D q).map (R.map ((singleFunctor C 0).map S.g)))
      ((homologyFunctor D q).map (R.map ((singleFunctor C 0).map S.f)))
      (by rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, S.zero,
        Functor.map_zero, Functor.map_zero, Functor.map_zero])) := by
  have hT := R.map_distinguished _ hS.singleTriangle_distinguished
  have : Mono ((homologyFunctor D q).map (R.mapTriangle.obj hS.singleTriangle).mor₁) :=
    mono_homologyMap_map_f_of_epi R q₀ q hS hq h
  exact (IsLimit.conePointUniqueUpToIso (HomologySequence.exact₂ _ hT q).fIsKernel
    (kernelIsKernel _)).isIso_hom

include hS hq in
/-- **Vanishing from the long exact cohomology sequence.** If `Hᵠ(R(B)) = 0` and
`Hᵠ⁻¹(R(B)) ⟶ Hᵠ⁻¹(R(C))` is an epimorphism, then `Hᵠ(R(A)) = 0`. -/
theorem isZero_homology_of_shortExact
    (h : Epi ((homologyFunctor D q₀).map (R.map ((singleFunctor C 0).map S.g))))
    (hB : Limits.IsZero ((homologyFunctor D q).obj (R.obj ((singleFunctor C 0).obj S.X₂)))) :
    Limits.IsZero ((homologyFunctor D q).obj (R.obj ((singleFunctor C 0).obj S.X₁))) := by
  have := mono_homologyMap_map_f_of_epi R q₀ q hS hq h
  exact @Limits.IsZero.of_mono _ _ _ _ _ _ this hB

end DerivedCategory

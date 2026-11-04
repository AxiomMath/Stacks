module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ZeroDimensionalAgreement
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.TwistOfFixing
import StacksCore.Tactic.StacksAttribute

/-!
# Countably many families of relative equivalences

Let `K` be an algebraically closed field. There is a countable set `I` of families
`(Sᵢ/K, Xᵢ ⟶ Sᵢ, Yᵢ ⟶ Sᵢ, Mᵢ)` with `Sᵢ` of finite type over `K`, `Xᵢ`, `Yᵢ` proper smooth over
`Sᵢ` and `Mᵢ` the perfect Fourier-Mukai kernel of a relative equivalence from `Xᵢ` to `Yᵢ`
over `Sᵢ`, such that every pair of smooth proper `K`-schemes with `K`-linearly and exactly
equivalent perfect derived categories occurs as a pair of fibres `(Xᵢ)ₛ`, `(Yᵢ)ₛ` at a
`K`-point `s` of some `Sᵢ`. This is [Stacks, Tag 0G0Y].

`AlgebraicGeometry.exists_countable_relativeEquivalenceKernels_of_parts` derives the statement
from the two halves of the object-wise Orlov theorem: part A, the construction of
[Stacks, Section 0G07] (`AlgebraicGeometry.fourierMukaiAgreesOnZeroDimensional`), and part B,
[Stacks, Tag 0G27] over an algebraically closed field
(`Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.twistOfFixingZeroDimensional`). Both are
proved, so the statement holds unconditionally.

## Main results

* `AlgebraicGeometry.exists_countable_relativeEquivalenceKernels`: [Stacks, Tag 0G0Y].

## References

* [Stacks Project, Tag 0G0Y](https://stacks.math.columbia.edu/tag/0G0Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **Stacks Project, Tag 0G0Y.** Let `K` be an algebraically closed field. There is a countable
set `I` and for each `i ∈ I` a system `(Sᵢ/K, Xᵢ ⟶ Sᵢ, Yᵢ ⟶ Sᵢ, Mᵢ)` with
1. `Sᵢ` of finite type over `K`,
2. `Xᵢ ⟶ Sᵢ` and `Yᵢ ⟶ Sᵢ` proper and smooth,
3. `Mᵢ ∈ D_perf(𝒪_{Xᵢ ×_{Sᵢ} Yᵢ})` the Fourier-Mukai kernel of a relative equivalence from `Xᵢ`
   to `Yᵢ` over `Sᵢ`,
4. for all smooth proper `K`-schemes `X`, `Y` with a `K`-linear exact equivalence
   `D_perf(𝒪_X) ⟶ D_perf(𝒪_Y)` there are `i ∈ I` and `s ∈ Sᵢ(K)` with `X ≅ (Xᵢ)ₛ` and
   `Y ≅ (Yᵢ)ₛ`. -/
@[stacks 0G0Y]
theorem exists_countable_relativeEquivalenceKernels (K : Type u) [Field K] [IsAlgClosed K] :
    ∃ (I : Type (u + 1)) (_ : Countable I)
      (S : I → Over (Spec (.of K)))
      (X Y : (i : I) → Over (S i).left)
      (M : (i : I) → DerivedCategory (pullback (X i).hom (Y i).hom).Modules)
      (_ : ∀ i, LocallyOfFiniteType (S i).hom ∧ QuasiCompact (S i).hom)
      (_ : ∀ i, Smooth (X i).hom ∧ IsProper (X i).hom)
      (_ : ∀ i, Smooth (Y i).hom ∧ IsProper (Y i).hom)
      (_ : ∀ i, IsRelativeEquivalenceKernel (X i).hom (Y i).hom (M i)),
      ∀ (A B : Over (Spec (.of K))),
        Smooth A.hom → IsProper A.hom → Smooth B.hom → IsProper B.hom →
          (letI : Linear K A.left.Modules := modulesLinear K A
           letI : Linear K B.left.Modules := modulesLinear K B
           ∃ e : PerfectDerivedCategory A.left ≌ PerfectDerivedCategory B.left,
             e.functor.Linear K ∧
               ∃ h : e.functor.CommShift ℤ,
                 letI := h
                 e.functor.IsTriangulated) →
            ∃ (i : I) (s : Over.mk (𝟙 (Spec (.of K))) ⟶ S i),
              Nonempty (A ≅ (Over.pullback s.left).obj (X i)) ∧
                Nonempty (B ≅ (Over.pullback s.left).obj (Y i)) :=
  exists_countable_relativeEquivalenceKernels_of_parts K (fourierMukaiAgreesOnZeroDimensional K)
    (Stacks.AlgebraicGeometry.DerivedVarieties.Orlov.twistOfFixingZeroDimensional K)

end AlgebraicGeometry

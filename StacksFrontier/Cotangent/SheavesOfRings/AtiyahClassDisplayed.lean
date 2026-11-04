module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedProjectionConstantCoefficient
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahDifferentialsLowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The Atiyah triangle and the Atiyah class at the objects the source displays

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it,
let `ℱ` be a sheaf of `ℬ`-modules and let `P_• ⟶ ℬ` be the standard resolution of `ℬ` over `𝒜`.
[Stacks, Tag 09DH] displays the Atiyah triangle with its outer terms replaced by

`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ[1]`,

and [Stacks, Tag 09DI] *names* the last arrow of that display the **Atiyah class** of `ℱ`. This
file states both at those objects, given an identification `e₁` of the first term of
`CategoryTheory.Sheaf.resolutionAtiyahTriangle` with `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` and an identification `e₃`
of its third term with `ℱ[0]`. The third term is the `Lπ_!` of [Stacks, Tag 09D3] — derived
extension of scalars `Lε^*` along the augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` followed by the `Lπ_!` of
[Stacks, Tag 09CY] — applied to `ε_*(π^{-1}ℱ)`, and the first term is its value on the first term
of the short exact sequence of [Stacks, Tag 09DG]. The cotangent complex `L_{ℬ/𝒜}` is that of
[Stacks, Tag 08SS], and the identifications rest on [Stacks, Tag 09D2].

## Main definitions

* `CategoryTheory.Sheaf.resolutionAtiyahTriangleThirdTermIso`: the third-term identification `e₃`,
  given [Stacks, Tag 09D2] at the coefficient module.
* `CategoryTheory.Sheaf.resolutionAtiyahClass`: the Atiyah class of Tag 09DI as a morphism
  `ℱ[0] ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)[1]` in `D(ℬ)`.

## Main results

* `CategoryTheory.Sheaf.resolutionAtiyahClass_mem_distinguished`: the triangle of Tag 09DH as the
  source displays it is distinguished, with the Atiyah class as its last arrow.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the displayed triangle,
  and [Tag 09DI](https://stacks.math.columbia.edu/tag/09DI), the Atiyah class, which is its last
  arrow.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), the lemma that removes the
  derived base change along the augmentation.
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor `Lπ_!` of the
  triangle, and [Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), its second factor.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex of a
  homomorphism of sheaves of rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.SimplicialModules (projection projectionTopology projectionRing
  derivedProjectionLowerShriek derivedProjectionLowerShriekRestrictionIso)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **The third term of the Atiyah triangle is `ℱ`, given [Stacks, Tag 09D2] at the coefficient
module.** The third term of `CategoryTheory.Sheaf.resolutionAtiyahTriangle` is the functor `Lπ_!`
of Remark 09D3 — derived extension of scalars along the augmentation `ε : 𝒫 ⟶ π^{-1}ℬ`, then the
`Lπ_!` of Remark 09CY — applied to the coefficient module `ε_*(π^{-1}ℱ)`. Given an isomorphism `h`
dropping the derived base change, which is Tag 09D2 at that sheaf, the remaining computation
`Lπ_!(π^{-1}ℱ[0]) ≅ ℱ[0]` is `Stacks.SimplicialModules.derivedProjectionLowerShriekRestrictionIso`,
the Moore complex of a constant simplicial module being a resolution of its value. -/
def resolutionAtiyahTriangleThirdTermIso (F : SheafOfModules.{u} (targetRing J (B := B)))
    (h : (resolutionAtiyahTriangle J f F).obj₃ ≅
      (derivedProjectionLowerShriek C J (targetRing J (B := B))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
            (ComplexShape.up ℤ) 0).obj (projectionCoefficients J (B := B) F)))) :
    (resolutionAtiyahTriangle J f F).obj₃ ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F) :=
  h ≪≫ derivedProjectionLowerShriekRestrictionIso C J (targetRing J (B := B)) F

/-- **The Atiyah class of a sheaf of `ℬ`-modules**, as [Stacks, Tag 09DI] names it: the last arrow

`ℱ ⟶ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ[1]`

of the triangle of [Stacks, Tag 09DH] as the source displays it. Both endpoints are the source's
own objects; what is assumed is the two identifications the source performs, `e₁` of the first term
with `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` and `e₃` of the third with `ℱ`. -/
def resolutionAtiyahClass (F : SheafOfModules.{u} (targetRing J (B := B)))
    (e₁ : (resolutionAtiyahTriangle J f F).obj₁ ≅
      ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)))
    (e₃ : (resolutionAtiyahTriangle J f F).obj₃ ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F)) :
    DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F) ⟶
      (((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)))⟦(1 : ℤ)⟧ :=
  e₃.inv ≫ (resolutionAtiyahTriangle J f F).mor₃ ≫
    (shiftFunctor (DerivedCategory (SheafOfModules.{u} (targetRing J (B := B)))) (1 : ℤ)).map
      e₁.hom

/-- **The triangle of [Stacks, Tag 09DH] as the source displays it is distinguished, and its last
arrow is the Atiyah class of [Stacks, Tag 09DI]:**

`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ[1]`

is a distinguished triangle in `D(ℬ)`. It is the Atiyah triangle
(`CategoryTheory.Sheaf.resolutionAtiyahTriangle_distinguished`) transported along the two
identifications of its outer terms. -/
theorem resolutionAtiyahClass_mem_distinguished (F : SheafOfModules.{u} (targetRing J (B := B)))
    (e₁ : (resolutionAtiyahTriangle J f F).obj₁ ≅
      ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)))
    (e₃ : (resolutionAtiyahTriangle J f F).obj₃ ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F)) :
    Triangle.mk (e₁.inv ≫ (resolutionAtiyahTriangle J f F).mor₁)
        ((resolutionAtiyahTriangle J f F).mor₂ ≫ e₃.hom)
        (resolutionAtiyahClass J f F e₁ e₃) ∈ distinguishedTriangles :=
  isomorphic_distinguished _ (resolutionAtiyahTriangle_distinguished J f F) _
    (Triangle.isoMk _ _ e₁.symm (Iso.refl _) e₃.symm (by simp) (by simp)
      (by simp [resolutionAtiyahClass]))

end CategoryTheory.Sheaf

end

module

public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorGradedPiece
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedComparisonGlobal

/-!
# The comparison of Section 0FMK, at the pullback of the forms of the target

Let `f : X ⟶ Y` be a morphism of schemes over a base `S`, with `g : Y ⟶ S` the structure
morphism of the target. The splitting-free comparison
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison` maps onto the graded
piece of the filtration of `Ω^n_{X/S}` by the forms pulled back from `Y`,

`⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`,  `n = k + 1 + m`,

whose source is written with the exterior power of a pullback. This file identifies its first
factor with the pullback `f^*Ω^k_{Y/S}` of the exterior power `Ω^k_{Y/S} = ⋀^kΩ_{Y/S}`, and reads
the comparison at that source:

`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`.

That `⋀^k` and `f^*` commute is [Stacks, Tag 01CI], here
`AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackExteriorIso`: the source of the
  comparison, with its first factor read as `f^*Ω^k_{Y/S}`.
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison`: the comparison
  of Section 0FMK at that source, `f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`.

## Main results

* `Stacks.CategoryTheory.epi_isoHom_comp`, `Stacks.CategoryTheory.isIso_isoHom_comp`: an
  epimorphism, resp. isomorphism, precomposed with an isomorphism is one.
* `AlgebraicGeometry.Scheme.Hom.epi_relativeDifferentialsPullbackGradedComparison`: the
  comparison is an epimorphism, for `f` smooth.
* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsPullbackGradedComparison`: the
  comparison is an isomorphism, for `f` smooth.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.CategoryTheory

/-- **An epimorphism precomposed with an isomorphism is an epimorphism.** -/
theorem epi_isoHom_comp {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {P Q R : C₁}
    (e : P ≅ Q) (c : Q ⟶ R) (hc : Epi c) : Epi (e.hom ≫ c) :=
  have := hc
  epi_comp _ _

/-- **An isomorphism precomposed with an isomorphism is an isomorphism.** -/
theorem isIso_isoHom_comp {C₁ : Type*} [_root_.CategoryTheory.Category C₁] {P Q R : C₁}
    (e : P ≅ Q) (c : Q ⟶ R) (hc : IsIso c) : IsIso (e.hom ≫ c) :=
  have := hc
  IsIso.comp_isIso

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The source of the comparison of [Stacks, Section 0FMK], read with its first factor the
pullback `f^*Ω^k_{Y/S}` of the sheaf of relative `k`-forms of the target**:

`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ≅ ⋀^k(f^*Ω_{Y/S}) ⊗_{𝒪_X} Ω^{m+1}_{X/Y}`.

The two first factors are identified by [Stacks, Tag 01CI]
(`AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso`), applied in the first slot of the
tensor bifunctor with the identity in the second. -/
def relativeDifferentialsPullbackExteriorIso (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
        ((Scheme.Modules.pullback f).obj (relativeDifferentialForms g (k : ℤ)),
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₃).exterior.piece ((m + 1 : ℕ) : ℤ)) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).obj
          ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₁).exteriorPower k)).obj
        ((_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
          (relativeDifferentialsShortComplex f g).X₃).exterior.piece ((m + 1 : ℕ) : ℤ)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.toRingedSpace.sheaf).mapIso
    (Scheme.Modules.exteriorPowerPullbackIso f (relativeDifferentials g) (k : ℤ))).app _

/-- **The comparison of [Stacks, Section 0FMK], at the pullback source**: for
`f : X ⟶ Y` smooth over a base `S` and `n = k + 1 + m`,

`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`.

It is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison` precomposed
with the identification of Tag 01CI. -/
def relativeDifferentialsPullbackGradedComparison [Smooth f] (k m : ℕ) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf)).obj
        ((Scheme.Modules.pullback f).obj (relativeDifferentialForms g (k : ℤ)),
          (_root_.SheafOfModules.ringedSpaceAlgebras X.toRingedSpace
            (relativeDifferentialsShortComplex f g).X₃).exterior.piece ((m + 1 : ℕ) : ℤ)) ⟶
      relativeDifferentialsExteriorGraded f g k m :=
  (relativeDifferentialsPullbackExteriorIso f g k m).hom ≫
    relativeDifferentialsExteriorGradedComparison f g k m

/-- **The comparison at the pullback source is an epimorphism**, for `f` smooth. -/
theorem epi_relativeDifferentialsPullbackGradedComparison [Smooth f] (k m : ℕ) :
    Epi (relativeDifferentialsPullbackGradedComparison f g k m) :=
  Stacks.CategoryTheory.epi_isoHom_comp _ _
    (epi_relativeDifferentialsExteriorGradedComparison f g k m)

/-- **[Stacks, Section 0FMK] at the pullback source: the comparison

`f^*Ω^k_{Y/S} ⊗_{𝒪_X} Ω^{m+1}_{X/Y} ⟶ gr^kΩ^n_{X/S}`

is an isomorphism**, for every smooth `f` and `n = k + 1 + m`. -/
theorem isIso_relativeDifferentialsPullbackGradedComparison [Smooth f] (k m : ℕ) :
    IsIso (relativeDifferentialsPullbackGradedComparison f g k m) :=
  Stacks.CategoryTheory.isIso_isoHom_comp _ _
    (isIso_relativeDifferentialsExteriorGradedComparison f g k m)

end AlgebraicGeometry.Scheme.Hom

end

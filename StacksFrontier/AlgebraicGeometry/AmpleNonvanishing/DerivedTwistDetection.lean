module

public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistedSectionChart
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryB.FiniteFreeSummandsOnASpace
public import StacksFrontier.Homology.DerivedCategory.HomFromSingleNonzero
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksCore.Tactic.StacksAttribute

/-!
# The negative tensor powers of an ample module detect the bounded-below part of `D_QCoh(𝒪_X)`

Let `X` be a scheme carrying an ample invertible `𝒪_X`-module `L`. This file proves that the
family `L ^⊗ (-p)`, `p ≥ 0`, detects the zero object among the objects of `D_QCoh(𝒪_X)` that are
**bounded below**: if every morphism `L ^⊗ (-p)[-j] ⟶ K` out of a shift of a negative tensor
power vanishes, and the cohomology sheaves of `K` are quasi-coherent and vanish below some
degree, then `K = 0`.

For bounded-below `K` no representation of `K` by a complex of quasi-coherent modules is needed:
`DerivedCategory.exists_hom_singleFunctor_ne_zero_of_isGE` produces a nonzero morphism out of the
lowest nonvanishing cohomology sheaf directly. The statement for all of `D_QCoh(𝒪_X)`, on a scheme
with affine diagonal, is
`Stacks.AmpleNonvanishingChart.isZero_of_forall_hom_tensorPowModule_neg_eq_zero`
(`StacksFrontier/AlgebraicGeometry/AmpleNonvanishing/DerivedQCohDetection.lean`).

## Main results

* `Stacks.AmpleNonvanishingChart.exists_hom_monoidalUnit_ne_zero` — a module with a nonzero
  global section receives a nonzero morphism from the monoidal unit `𝒪_X`.
* `Stacks.AmpleNonvanishingChart.homTensorPowModuleNegOfUnitHom` and
  `Stacks.AmpleNonvanishingChart.homTensorPowModuleNegOfUnitHom_ne_zero` — the untwisting of a
  morphism `𝒪_X ⟶ F ⊗ L ^⊗ p` into a morphism `L ^⊗ (-p) ⟶ F`, and its nonvanishing.
* `Stacks.AmpleNonvanishingChart.exists_hom_tensorPowModule_neg_ne_zero_of_isAmple` —
  **[Stacks, Tag 0BQR] at a module, in `Hom` shape**: a nonzero quasi-coherent `F` receives a
  nonzero morphism from some `L ^⊗ (-p)`.
* `Stacks.AmpleNonvanishingChart.isZero_of_isGE_of_forall_hom_tensorPowModule_neg_eq_zero` —
  the detection statement displayed above.

## Implementation notes

The global sections of a sheaf of modules are a compatible family over all opens, while
[Stacks, Tag 0BQR]'s witness is a section over `⊤`. The bijection between the two is
`AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv`. The
passage from a nonzero section to a nonzero morphism is made through `Nontrivial` rather than
through additivity of the bijections, none of which is recorded.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category TopologicalSpace Opposite
open MonoidalCategory AlgebraicGeometry
open Stacks.Ample

universe u

namespace Stacks.AmpleNonvanishingChart

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

/-! ### From a nonzero global section to a nonzero morphism out of `𝒪_X` -/

/-- **A module with a nonzero global section receives a nonzero morphism from `𝒪_X`.**

The morphisms `𝒪_X ⟶ F` out of the monoidal unit are the global sections of `F`
(`Stacks.SectionProduct.monoidalUnitHomEquiv`), and the global sections are the sections over
`⊤` (`AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv`). A nonzero section makes `Γ(F, ⊤)`
nontrivial, hence
makes the morphism type nontrivial, hence produces a morphism that is not zero. The argument
goes through `Nontrivial` because neither bijection is recorded as additive. -/
theorem exists_hom_monoidalUnit_ne_zero {X : Scheme.{u}} (F : X.Modules) (τ : Γ(F, ⊤))
    (hτ : τ ≠ 0) : ∃ g : 𝟙_ X.Modules ⟶ F, g ≠ 0 := by
  have hnt : Nontrivial Γ(F, ⊤) := ⟨⟨τ, 0, hτ⟩⟩
  have : Nontrivial (𝟙_ X.Modules ⟶ F) :=
    ((Stacks.SectionProduct.monoidalUnitHomEquiv F).trans
      (AlgebraicGeometry.Scheme.Modules.sectionsTopEquiv F).symm).symm.injective.nontrivial
  exact exists_ne 0

/-! ### Untwisting a morphism out of `𝒪_X` -/

section Untwist

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L] (F : X.Modules) (p : ℤ)

/-- **The untwisting of a morphism `𝒪_X ⟶ F ⊗ L ^⊗ p` into a morphism `L ^⊗ (-p) ⟶ F`.** Tensor
the morphism on the right with `L ^⊗ (-p)` and cancel the twist by
`Stacks.AmpleGlobalGeneration.twistCancelIso`. -/
def homTensorPowModuleNegOfUnitHom (g : 𝟙_ X.Modules ⟶ F ⊗ tensorPowModule X L p) :
    tensorPowModule X L (-p) ⟶ F :=
  (λ_ (tensorPowModule X L (-p))).inv ≫
    (MonoidalCategory.tensorRight (tensorPowModule X L (-p))).map g ≫
    (Stacks.AmpleGlobalGeneration.twistCancelIso L F p).hom

/-- **The untwisting of a nonzero morphism is nonzero.** Tensoring on the right with the
invertible module `L ^⊗ (-p)` is an equivalence, hence faithful, and the two outer factors of
the untwisting are isomorphisms. -/
theorem homTensorPowModuleNegOfUnitHom_ne_zero
    (g : 𝟙_ X.Modules ⟶ F ⊗ tensorPowModule X L p) (hg : g ≠ 0) :
    homTensorPowModuleNegOfUnitHom L F p g ≠ 0 := by
  intro h
  have := Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight L (-p)
  refine hg ((MonoidalCategory.tensorRight (tensorPowModule X L (-p))).map_injective ?_)
  rw [Functor.map_zero, homTensorPowModuleNegOfUnitHom] at *
  simpa using h

end Untwist

/-! ### Stacks Tag 0BQR at a module, in Hom shape -/

/-- **[Stacks, Tag 0BQR] at a quasi-coherent module, in `Hom` shape.** For `L` an ample
invertible `𝒪_X`-module, a nonzero quasi-coherent `𝒪_X`-module `F` receives a nonzero morphism
from some negative tensor power `L ^⊗ (-p)`, `p ≥ 0`.

`Stacks.AmpleNonvanishingChart.exists_twistedSection_restrict_eq_tensorSection` produces the
exponent `p` and a nonzero global section of `F ⊗ L ^⊗ p`;
`Stacks.AmpleNonvanishingChart.exists_hom_monoidalUnit_ne_zero` turns that into a nonzero
morphism `𝒪_X ⟶ F ⊗ L ^⊗ p`, and
`Stacks.AmpleNonvanishingChart.homTensorPowModuleNegOfUnitHom` untwists it. -/
theorem exists_hom_tensorPowModule_neg_ne_zero_of_isAmple {X : Scheme.{u}} (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
    (hF : ¬ IsZero F) :
    ∃ (p : ℕ) (ψ : tensorPowModule X L (-(p : ℤ)) ⟶ F), ψ ≠ 0 := by
  obtain ⟨p, σ, U, τ, t, -, -, -, hτ, -⟩ :=
    exists_twistedSection_restrict_eq_tensorSection L hL F hF
  obtain ⟨g, hg⟩ := exists_hom_monoidalUnit_ne_zero _ τ hτ
  exact ⟨p, homTensorPowModuleNegOfUnitHom L F (p : ℤ) g,
    homTensorPowModuleNegOfUnitHom_ne_zero L F (p : ℤ) g hg⟩

/-! ### The detection statement -/

/-- **The negative tensor powers of an ample invertible module detect the zero object among the
bounded-below objects of `D_QCoh(𝒪_X)`.**

Let `X` be a scheme, `L` an ample invertible `𝒪_X`-module and `K` an object of the derived
category of `𝒪_X`-modules whose cohomology sheaves are quasi-coherent and vanish in all degrees
below `j₀`. If every morphism `L ^⊗ (-p)[-j] ⟶ K`, `p ≥ 0`, `j : ℤ`, is zero, then `K` is a zero
object.

The two inputs are
`Stacks.AmpleNonvanishingChart.exists_hom_tensorPowModule_neg_ne_zero_of_isAmple` — the
module-level [Stacks, Tag 0BQR] in `Hom` shape — and
`DerivedCategory.isZero_of_isGE_of_forall_hom_singleFunctor_eq_zero`, which assembles a family
detecting the nonzero quasi-coherent sheaves into one detecting the zero object of the
bounded-below part of `D_QCoh(𝒪_X)`. -/
theorem isZero_of_isGE_of_forall_hom_tensorPowModule_neg_eq_zero {X : Scheme.{u}}
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (K : DerivedCategory X.Modules) (j₀ : ℤ) (hKge : K.IsGE j₀)
    (hKQ : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (hvan : ∀ (p : ℕ) (j : ℤ) (φ : (DerivedCategory.singleFunctor X.Modules j).obj
      (tensorPowModule X L (-(p : ℤ))) ⟶ K), φ = 0) :
    IsZero K := by
  refine DerivedCategory.isZero_of_isGE_of_forall_hom_singleFunctor_eq_zero
    (fun F : X.Modules => F.IsQuasicoherent)
    (fun M : X.Modules => ∃ p : ℕ, M = tensorPowModule X L (-(p : ℤ))) K j₀ hKge hKQ ?_ ?_
  · intro F hFQ hF
    have : F.IsQuasicoherent := hFQ
    obtain ⟨p, ψ, hψ⟩ := exists_hom_tensorPowModule_neg_ne_zero_of_isAmple L hL F hF
    exact ⟨tensorPowModule X L (-(p : ℤ)), ⟨p, rfl⟩, ψ, hψ⟩
  · rintro M ⟨p, rfl⟩ j φ
    exact hvan p j φ

end Stacks.AmpleNonvanishingChart

end

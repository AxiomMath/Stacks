module

public import StacksFrontier.AlgebraicGeometry.TensorSectionNonvanishing.ProjTwistDegreeZeroNormalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison morphism for twisted global sections on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring, `X = Proj 𝒮`, let `ℱ` be a sheaf of `𝒪_X`-modules and
let `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be the integer-graded `S`-module of twisted global sections, with
its canonical graded-module structure `twistedGlobalSectionsModule`. There is a unique morphism
`M̃ ⟶ ℱ` with the prescribed restriction to each positive-degree standard open; it commutes with
every morphism of sheaves out of `ℱ`, and it sends the global section of `M̃` attached to a
degree-zero element `t ∈ M₀ = Γ(X, ℱ(0)) = Γ(X, ℱ)` back to `t`.

## Main results

* `comparison_existsUnique_functorial_degreeZeroId`: the comparison morphism `M̃ ⟶ ℱ` is unique
  with its prescribed local form, natural in `ℱ`, and the identity in degree zero.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTrivialization (projRingSheaf)
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistedGlobalSectionsGrading
  twistedSectionsComponent twistedGlobalSectionsAssociatedSheaf twistedGlobalSectionsModule)
open Stacks.AlgebraicGeometry.ProjTwistComparison (PositiveElem positiveBasicOpen
  twistedGlobalSectionsAssociatedSheafMap)
open Stacks.AlgebraicGeometry.ProjTwistIntegerComparison (localComparison integerComparison
  existsUnique_comparison integerComparison_naturality)
open Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization (twistZeroCancelIso
  integerComparison_degreeZeroToGlobalSections_id)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections)

namespace Stacks.AlgebraicGeometry.ProjTwistIntegerComparisonStatement

universe u w

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Let `S` be a graded ring, `X = Proj S`, let `ℱ` be a sheaf of `𝒪_X`-modules and let
`M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` be the graded `S`-module of twisted global sections, taken with its
canonical graded-module structure
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule`. Then there is a
canonical `𝒪_X`-module map `M̃ ⟶ ℱ`, functorial in `ℱ`, whose induced map `M₀ → Γ(X, ℱ)` is the
identity.

The three conjuncts are, in order:

1. **Existence and canonicity.** There is exactly one morphism `M̃ ⟶ ℱ` whose restriction to the
  standard open `D₊(f)` of each positive-degree homogeneous element is the chart comparison
  `m / f ^ k ↦ m|_{D₊(f)} ⊗ f ^ (-k)`. The morphism it names is
  `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.integerComparison`.
2. **Functoriality in `ℱ`.** For every sheaf `𝒢` and every morphism `ψ : ℱ ⟶ 𝒢`, the comparison
  morphisms of `ℱ` and of `𝒢` form a commuting square with `ψ` and with the morphism of
  associated sheaves that `ψ` induces on the graded modules of twisted global sections.
3. **The degree-zero map is the identity.** A global section `t` of `ℱ` is a degree-zero element
  of `M` through the identification `ℱ(0) ≅ ℱ` of
  `Stacks.AlgebraicGeometry.ProjTwistDegreeZeroNormalization.twistZeroCancelIso`; the global
  section of `M̃` attached to it is sent by the comparison morphism back to `t`. -/
@[stacks 0B5I "the tag's three assertions in one statement, for the canonical graded-module
structure on `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`: the comparison morphism `M̃ ⟶ ℱ` exists and is the
unique morphism restricting on each positive-degree standard open to `m / f ^ k ↦ m|_{D₊(f)} ⊗
f ^ (-k)`, it commutes with every morphism of sheaves of modules out of `ℱ`, and it returns each
global section of `ℱ` to itself through the identification `ℱ(0) ≅ ℱ`",
  ega "II 2.6.4" "more general"]
theorem comparison_existsUnique_functorial_degreeZeroId
    (F : SheafOfModules.{u} (projRingSheaf 𝒮)) :
    (∃! φ : twistedGlobalSectionsAssociatedSheaf 𝒮 F (twistedGlobalSectionsModule 𝒮 F) ⟶ F,
        ∀ p : PositiveElem 𝒮,
          φ.val.app (op (positiveBasicOpen 𝒮 p)) =
            localComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F) p) ∧
      (∀ (G : SheafOfModules.{u} (projRingSheaf 𝒮)) (ψ : F ⟶ G),
          twistedGlobalSectionsAssociatedSheafMap 𝒮 (twistedGlobalSectionsModule 𝒮 F)
                (twistedGlobalSectionsModule 𝒮 G) ψ ≫
              integerComparison 𝒮 G (twistedGlobalSectionsModule 𝒮 G) =
            integerComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F) ≫ ψ) ∧
      (letI := (twistedGlobalSectionsModule 𝒮 F).moduleInst
       letI := (twistedGlobalSectionsModule 𝒮 F).gradedSMul
       ∀ t : F.val.obj (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))),
        (integerComparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F)).val.app
            (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮)))
            (degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F)
              ⟨DirectSum.of (fun k : ℤ => twistedSectionsComponent 𝒮 F k) 0
                  ((twistZeroCancelIso 𝒮 F (rfl : (0 : ℤ) = 0)).inv.val.app
                    (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) t),
                (DirectSum.mem_rangeGrading ℤ (fun k : ℤ => twistedSectionsComponent 𝒮 F k) 0
                  _).mpr ⟨_, rfl⟩⟩) = t) :=
  ⟨existsUnique_comparison 𝒮 F (twistedGlobalSectionsModule 𝒮 F),
    fun G ψ => integerComparison_naturality 𝒮 (twistedGlobalSectionsModule 𝒮 F)
      (twistedGlobalSectionsModule 𝒮 G) ψ,
    fun t => integerComparison_degreeZeroToGlobalSections_id 𝒮 F
      (twistedGlobalSectionsModule 𝒮 F) t⟩

end Stacks.AlgebraicGeometry.ProjTwistIntegerComparisonStatement

end

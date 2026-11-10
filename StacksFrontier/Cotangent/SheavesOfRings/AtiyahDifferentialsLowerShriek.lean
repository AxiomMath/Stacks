module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.DerivedProjectionMooreComplexModules
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentDifferentialsBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!(Ω_{P_•/𝒜} ⊗_{P_•} ℱ) = L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a morphism of sheaves of commutative rings on it,
let `ℱ` be a sheaf of `ℬ`-modules and let `P_•` be the standard resolution of `ℬ` over `𝒜`. The
first term of the Atiyah triangle of [Stacks, Tag 09DH] is displayed there as
`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`. This file proves that it is: the derived lower shriek of Remark 09CY,

`Lπ_! : D(π^{-1}ℬ) ⥤ D(ℬ)`,

carries the simplicial sheaf of `ℬ`-modules `Ω_{P_•/𝒜} ⊗_{P_•} ℱ` to `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`.

## Main definitions

* `CategoryTheory.Sheaf.simplicialDifferentialsCoefficients`: `Ω_{P_•/𝒜} ⊗_{P_•} ℱ` read as a
  sheaf of `π^{-1}ℬ`-modules on `Δ × C`, by the uncurrying of
  `Stacks.SimplicialModules.simplicialModuleEquivalence`.

## Main results

* `CategoryTheory.Sheaf.derivedLowerShriekSimplicialDifferentialsIso`:
  **`Lπ_!(Ω_{P_•/𝒜} ⊗_{P_•} ℱ) ≅ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` in `D(ℬ)`.**

## Implementation notes

The proof is the composite of the two halves the source's display rests on, both of which are now
available:

* `Stacks.SimplicialModules.derivedProjectionLowerShriekIsoMooreComplexModules`, the
  module-coefficient form of the untagged paragraph of Cohomology on Sites, Section 09D0:
  `Lπ_!` of a sheaf of `π^{-1}ℬ`-modules is the associated chain complex of the simplicial sheaf
  of `ℬ`-modules it is. Its fibrewise reading of an uncurried simplicial module is that module
  back again (`Stacks.SimplicialModules.uncurryModFibrewiseIso`), so at
  `Ω_{P_•/𝒜} ⊗_{P_•} ℱ` the answer is the associated chain complex of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`.
* `CategoryTheory.Sheaf.cotangentComplexDerivedTensorSimplicialIso`, which says that this
  complex is `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`.

**The two complexes are the same complex, on the nose.** The Moore complex of Section 09D0 is
taken over the site `Δ` with the tautological cosimplicial object `𝟭 Δ`, and so is
`Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)`; the complex defining
the cotangent complex of [Stacks, Tag 08SS] is
`AlgebraicTopology.alternatingFaceMapCochainComplex`. The first is the second precomposed with
restriction along `(𝟭 Δ).op`, which is the identity, so
`CategoryTheory.Sheaf.mooreCochainComplex_eq_alternatingFaceMapCochainComplex` is `rfl` and no
comparison is needed.

**What this is not.** It is not Tag 09DH, and it is not the first term of
`CategoryTheory.Sheaf.resolutionAtiyahTriangle` either. That term is
`Lπ_!` *of Remark 09D3* — derived base change along the augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` followed
by the `Lπ_!` above — applied to `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ` on `Δ × C`. Two things separate the two
statements, and both are identified precisely in the module docstring of
`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangle.lean`:

* that `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ε_*(π^{-1}ℱ)` is `ε_*` of the uncurrying of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`,
  which is what identifies it with the simplicial module used here. That is now proved, **on
  `Δ × C` and not degreewise**, by `CategoryTheory.Sheaf.simplicialPrincipalPartsX₁Iso`
  (`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangleFirstTerm.lean`), out of the unconditional
  tensor/restriction transitivity, the corepresentation of
  `Der_{π^{-1}𝒜}(𝒫, ε_*(-))` by both `ε^*Ω_{𝒫/π^{-1}𝒜}` and the uncurrying
  (`CategoryTheory.Sheaf.extendAugmentationDifferentialsUncurryIso`) and the commutation of
  uncurrying with tensoring by an inverse-image module
  (`Stacks.SimplicialModules.TensorUncurry.tensorUncurryIso`). The degreewise statement
  `CategoryTheory.Sheaf.fibrePrincipalPartsX₁DegreeIso`
  (`StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentialsDegree.lean`) is the same mathematics
  over `P_n`, and is not used: nothing in the chain is assembled out of fibrewise comparisons, so
  nothing about the naturality of
  `Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso` in the functor of
  sites is needed; and
* that the derived base change along `ε` may be dropped, which is Lemma 21.41.2 — [Stacks,
  Tag 09D2] — at module coefficients. It cannot be dropped for free: the augmentation
  `𝒫 ⟶ π^{-1}ℬ` is a surjection of sheaves of rings with nonzero `Tor`, so
  `ε^*` is not exact on `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ` and the higher terms are only killed after `Lπ_!`.

Both are now theorems — see
`CategoryTheory.Sheaf.nonempty_resolutionAtiyahTriangleFirstTermIso`
(`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangleFirstTerm.lean`), and the registrations
of Tags 09DH and 09DI are in `StacksFrontier/Cotangent/SheavesOfRings/AtiyahClassDefinite.lean`
— but neither is claimed here, and no `@[stacks]` attribute is taken.

Nor is this [Stacks, Tag 08PU]. That lemma opens "Let `A → B` be a ring map" and computes
`L_{B/A}` as `Lπ_!(Ω_{𝒪/A} ⊗_𝒪 \underline{B})` for the point morphism `π` of the chaotic
polynomial site `C_{B/A}` of [Stacks, Tag 08PR]; it is a statement about a ring map and a
different site, and Section 92.19 does not cite it.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle,
  whose first term this is.
* [Stacks Project, Tag 09D0](https://stacks.math.columbia.edu/tag/09D0), `Lπ_!` of a simplicial
  module as its associated chain complex.
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), the functor `Lπ_!` used
  here, and [Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor of Tag 09DH, which
  is this one precomposed with derived base change along the augmentation.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), which is what would
  remove that precomposition.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex of
  a morphism of sheaves of rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.SimplicialModules (projection projectionTopology projectionRing fibrewiseMod
  uncurryMod uncurryModFibrewiseIso derivedProjectionLowerShriek
  derivedProjectionLowerShriekIsoMooreComplexModules)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **The Moore complex of Section 09D0 at the tautological cosimplicial object is the reindexed
alternating-face-map complex.** The Moore complex of Stacks 09D0 is formed over the site `Δ` with
the cosimplicial object `𝟭 Δ`, so the restriction along `(𝟭 Δ).op` that it precomposes with is
the identity and the two complexes are the same. -/
theorem mooreCochainComplex_eq_alternatingFaceMapCochainComplex
    (M : Type*) [Category* M] [Abelian M] :
    Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory) M =
      alternatingFaceMapCochainComplex M :=
  rfl

/-- **`Ω_{P_•/𝒜} ⊗_{P_•} ℱ` as a sheaf of `π^{-1}ℬ`-modules on `Δ × C`**, which is the shape in
which the computation of `Lπ_!` of Stacks 09D0 consumes a simplicial sheaf of `ℬ`-modules. -/
def simplicialDifferentialsCoefficients (F : SheafOfModules.{u} (targetRing J (B := B))) :
    SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))) :=
  (uncurryMod C J (targetRing J (B := B))).obj (cotangentSimplicialModuleTensor J f F)

omit [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- The sections of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ` on `Δ × C` over `(n, U)` are the sections over `U` of
its degree-`n` term: the passage to `Δ × C` changes nothing but the indexing. -/
theorem simplicialDifferentialsCoefficients_sections
    (F : SheafOfModules.{u} (targetRing J (B := B))) (n : SimplexCategory) (U : Cᵒᵖ) :
    ((simplicialDifferentialsCoefficients J f F).val.obj (op (n, U.unop)) : Type u) =
      (((cotangentSimplicialModuleTensor J f F).obj (op n)).val.obj U : Type u) :=
  rfl

/-- **`Lπ_!(Ω_{P_•/𝒜} ⊗_{P_•} ℱ) ≅ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` in `D(ℬ)`.** The derived lower shriek of
Remark 09CY carries the simplicial sheaf of `ℬ`-modules `Ω_{P_•/𝒜} ⊗_{P_•} ℱ` to the first term
of the Atiyah triangle of [Stacks, Tag 09DH] as that term is displayed there.

The left-hand side is computed by the module-coefficient form of Section 09D0, which gives the
associated chain complex of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`; the right-hand side is that same complex by
`CategoryTheory.Sheaf.cotangentComplexDerivedTensorSimplicialIso`, the cotangent complex being
K-flat. -/
def derivedLowerShriekSimplicialDifferentialsIso
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (derivedProjectionLowerShriek C J (targetRing J (B := B))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
            (ComplexShape.up ℤ) 0).obj (simplicialDifferentialsCoefficients J f F))) ≅
      ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F)) :=
  derivedProjectionLowerShriekIsoMooreComplexModules C J (targetRing J (B := B))
      (simplicialDifferentialsCoefficients J f F) ≪≫
    DerivedCategory.Q.mapIso
      ((Stacks.ChaoticSite.GeneralValued.mooreCochainComplex (𝟭 SimplexCategory)
        (SheafOfModules.{u} (targetRing J (B := B)))).mapIso
        ((uncurryModFibrewiseIso C J (targetRing J (B := B))).app
          (cotangentSimplicialModuleTensor J f F))) ≪≫
    (cotangentComplexDerivedTensorSimplicialIso J f F).symm

end CategoryTheory.Sheaf

end

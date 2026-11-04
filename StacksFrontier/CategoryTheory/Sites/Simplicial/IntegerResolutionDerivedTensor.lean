module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionPostnikov
public import StacksFrontier.CategoryTheory.Sites.Simplicial.VanishingCohomology

/-!
# The Postnikov system and the derived colimit of `- ⊗^L_ℤ K` on a simplicial site

Let `S` be a simplicial-site situation (Stacks 09WE) and let `K` be an object of the unbounded
derived category `D(𝒞_total)` of abelian sheaves on its total site. Put

`Xₙ = g_{n!}ℤ ⊗^L_ℤ K` and `Yₙ = (g_{n!}ℤ → … → g_{0!}ℤ)[-n] ⊗^L_ℤ K`,

the derived tensor product over `ℤ` of `K` with the integral resolution of Stacks 09WI and with
its brutal truncations. Stacks 0D9I asserts that the triangles
`Yₙ ⟶ Xₙ ⟶ Yₙ₋₁ ⟶ Yₙ[1]` form a Postnikov system for the inverse system
`… ⟶ X₂ ⟶ X₁ ⟶ X₀`, and that `K = hocolim Yₙ[n]`.

`StacksFrontier/CategoryTheory/Sites/Simplicial/IntegerResolutionPostnikov.lean` proves both
statements for an arbitrary exact functor `T` of `D(𝒞_total)` commuting with countable direct
sums. This file instantiates them at `T = - ⊗^L_ℤ K`, which is legitimate because the three
facts that instantiation needs are available: `- ⊗^L_ℤ K` is exact
(`Stacks.DerivedTensor.AbelianSheaves.isTriangulated_derivedTensorFlipObj`), it commutes with
countable direct sums
(`Stacks.DerivedTensor.AbelianSheaves.preservesCountableCoproducts_derivedTensorFlipObj`), and
the constant sheaf `ℤ` in degree zero is a unit for it
(`Stacks.DerivedTensor.AbelianSheaves.constantSheafLeftUnitIso`).

The unit is what turns the abstract conclusion `T(ℤ) = hocolim T(Yₙ[n])` into the source's
`K = hocolim Yₙ[n]`: the integral resolution represents the constant sheaf `ℤ`, so
`ℤ ⊗^L_ℤ K ≅ K`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.integerResolutionAugmentation`: the augmentation of
  the integral resolution onto the constant integer sheaf in degree zero, on the cochain complex
  of `IntegerResolutionPostnikov`.
* `CategoryTheory.SimplicialSiteSituation.integerResolutionDerivedIso`: **the integral
  resolution represents the constant sheaf `ℤ`** in `D(𝒞_total)`.
* `CategoryTheory.SimplicialSiteSituation.integerDerivedTensorRight`: the functor `- ⊗^L_ℤ K`.
* `CategoryTheory.SimplicialSiteSituation.derivedTensorIntegerResolutionPostnikovSystem`:
  **Stacks 0D9I(1)** for `- ⊗^L_ℤ K`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedTensorIntegerResolutionTermIso`: the `n`-th
  term of the Postnikov system is `g_{n!}ℤ ⊗^L_ℤ K`.
* `CategoryTheory.SimplicialSiteSituation.derivedTensorIntegerResolutionIso`:
  `ℤ ⊗^L_ℤ K ≅ K`, with `ℤ` presented by the integral resolution.
* `CategoryTheory.SimplicialSiteSituation.isHomotopyColimit_derivedTensorIntegerResolutionSystem`
  and its refinement `…isHomotopyColimitWith_derivedTensorIntegerResolutionSystem`:
  **Stacks 0D9I(2)** for `- ⊗^L_ℤ K`, namely `K = hocolim Yₙ[n]`, without and with the
  coprojections recorded.

## Implementation notes

The derived tensor product of abelian sheaves is built on the standard model of the derived
category, so that model is activated here as a local instance; the statements of
`IntegerResolutionPostnikov` are universe-polymorphic in the model and specialise to it.

The quasi-isomorphism of the augmentation is the one of
`CategoryTheory.SimplicialSiteSituation.quasiIso_integerChainAugmentation`, re-extended along
`ComplexShape.embeddingUpIntLE 0` rather than along `ComplexShape.embeddingDownNat`, which is
the embedding `IntegerResolutionPostnikov` places the resolution in; the two embeddings agree but
not by `rfl`, and extending the chain-level map again is shorter than transporting the cochain
one.

## References

* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open Stacks.DerivedTensor.AbelianSheaves
open StacksDraft.BrutalPostnikov
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u})

/-! ### The integral resolution represents the constant sheaf `ℤ` -/

/-- The augmentation of the integral resolution of Stacks 09WI onto the constant integer sheaf
placed in degree zero, read on the cochain complex `integerResolutionComplex` — which is, by
definition, the resolution extended along `ComplexShape.embeddingUpIntLE 0`, the spelling used
here so that the source of the morphism is the one instance search sees. -/
def integerResolutionAugmentation :
    S.simplicialIntegerComplex.extend (ComplexShape.embeddingUpIntLE 0) ⟶
      (CochainComplex.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj S.totalIntegerSheaf :=
  HomologicalComplex.extendMap S.integerChainAugmentation
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0)
      S.totalIntegerSheaf 0 0 (by simp)).hom

/-- **The integral resolution of Stacks 09WI is a resolution**: its augmentation onto the
constant integer sheaf in degree zero is a quasi-isomorphism. -/
instance quasiIso_integerResolutionAugmentation :
    QuasiIso (integerResolutionAugmentation S) := by
  dsimp only [integerResolutionAugmentation]
  infer_instance

section Derived

/-- **The integral resolution represents the constant sheaf `ℤ`**: in `D(𝒞_total)` the object
of the resolution `… → g_{1!}ℤ → g_{0!}ℤ` is the constant integer sheaf placed in degree
zero. -/
def integerResolutionDerivedIso :
    DerivedCategory.Q.obj (integerResolutionComplex S) ≅
      (DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj S.totalIntegerSheaf :=
  @asIso _ _ _ _ (DerivedCategory.Q.map (integerResolutionAugmentation S))
      ((DerivedCategory.isIso_Q_map_iff_quasiIso ..).2
        (quasiIso_integerResolutionAugmentation S)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (Sheaf S.totalTopology Ab.{u}) 0).app
      S.totalIntegerSheaf).symm

/-! ### Stacks 0D9I for `- ⊗^L_ℤ K` -/

variable (K : DerivedCategory (Sheaf S.totalTopology Ab.{u}))

/-- The functor `- ⊗^L_ℤ K` on `D(𝒞_total)`: the derived tensor product of abelian sheaves with
its second variable fixed at `K`. -/
abbrev integerDerivedTensorRight :
    DerivedCategory (Sheaf S.totalTopology Ab.{u}) ⥤
      DerivedCategory (Sheaf S.totalTopology Ab.{u}) :=
  (derivedTensor S.totalTopology).flip.obj K

/-- **Stacks 0D9I(1) for `- ⊗^L_ℤ K`.** For each length `N`, the images under `- ⊗^L_ℤ K` of
the brutal-truncation triangles `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁[1]` of the integral resolution are a
Postnikov system (Derived Categories, Definition 0D7Z) for `X_N ⟶ ⋯ ⟶ X₁ ⟶ X₀`, where
`Xₙ = g_{n!}ℤ ⊗^L_ℤ K` by `derivedTensorIntegerResolutionTermIso`. -/
@[stacks 0D9I]
def derivedTensorIntegerResolutionPostnikovSystem (N : ℕ) :
    Triangulated.PostnikovSystem
      (fun i : Fin (N + 1) =>
        (integerDerivedTensorRight S K).obj (integerResolutionTerm S (i : ℕ)))
      (fun i : Fin N =>
        (integerDerivedTensorRight S K).map
          (termDiff (integerResolutionComplex S) (i : ℕ))) :=
  map_integerResolutionPostnikovSystem S (integerDerivedTensorRight S K) N

/-- The terms of the Postnikov system of `- ⊗^L_ℤ K` are the objects `Xₙ = g_{n!}ℤ ⊗^L_ℤ K` of
the source. -/
def derivedTensorIntegerResolutionTermIso (n : ℕ) :
    (integerDerivedTensorRight S K).obj (integerResolutionTerm S n) ≅
      ((derivedTensor S.totalTopology).obj
        ((DerivedCategory.singleFunctor (Sheaf S.totalTopology Ab.{u}) 0).obj
          (componentIntegerSheaf S ⦋n⦌))).obj K :=
  (integerDerivedTensorRight S K).mapIso (integerResolutionTermIso S n)

/-- **`ℤ ⊗^L_ℤ K ≅ K`**, with the constant sheaf `ℤ` presented by the integral resolution: the
derived tensor product of `K` with the object of `D(𝒞_total)` represented by
`… → g_{1!}ℤ → g_{0!}ℤ` is `K`. -/
def derivedTensorIntegerResolutionIso :
    (integerDerivedTensorRight S K).obj
        (DerivedCategory.Q.obj (integerResolutionComplex S)) ≅ K :=
  (integerDerivedTensorRight S K).mapIso (integerResolutionDerivedIso S) ≪≫
    constantSheafLeftUnitIso S.totalTopology K

/-- **Stacks 0D9I(2) for `- ⊗^L_ℤ K`.** The object `K` is the derived colimit of the system
`Yₙ[n] = (g_{n!}ℤ → … → g_{0!}ℤ) ⊗^L_ℤ K`, **with the coprojections recorded**: the `n`-th one is
the image under `- ⊗^L_ℤ K` of the inclusion of the `n`-th brutal truncation of the integral
resolution, followed by the identification `ℤ ⊗^L_ℤ K ≅ K`. -/
theorem isHomotopyColimitWith_derivedTensorIntegerResolutionSystem :
    IsHomotopyColimitWith (integerResolutionSystem S ⋙ integerDerivedTensorRight S K) K
      (fun n ↦ (integerDerivedTensorRight S K).map
        (DerivedCategory.Q.map (HomologicalComplex.ιStupidTrunc
          (integerResolutionComplex S) (ComplexShape.embeddingUpIntGE (-(n : ℤ))))) ≫
        (derivedTensorIntegerResolutionIso S K).hom) :=
  have := preservesCountableCoproducts_derivedTensorFlipObj S.totalTopology K ℕ
  (isHomotopyColimitWith_map_integerResolutionSystem S
    (integerDerivedTensorRight S K)).of_iso (derivedTensorIntegerResolutionIso S K)

/-- **Stacks 0D9I(2) for `- ⊗^L_ℤ K`.** The object `K` is the derived colimit of the system
`Yₙ[n] = (g_{n!}ℤ → … → g_{0!}ℤ) ⊗^L_ℤ K`. -/
@[stacks 0D9I]
theorem isHomotopyColimit_derivedTensorIntegerResolutionSystem :
    IsHomotopyColimit (integerResolutionSystem S ⋙ integerDerivedTensorRight S K) K :=
  (isHomotopyColimitWith_derivedTensorIntegerResolutionSystem S K).isHomotopyColimit

end Derived

end CategoryTheory.SimplicialSiteSituation

end

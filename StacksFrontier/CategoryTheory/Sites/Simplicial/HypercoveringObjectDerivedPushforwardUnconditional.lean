module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionFreeYonedaQuasiIso
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedPushforwardFreeYonedaChain
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringUnit
import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects

/-!
# `Ra_*`-acyclicity of `a^{-1}` of a K-injective complex, for a hypercovering of an object

For a hypercovering `K` of an object `X` of a site `C`, the extension by zero `a_!` carries the
augmentation of the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism, for every
object `V` of `C/X`. By the criterion of Stacks 0D88 the inverse image `a^{-1}` of a K-injective
complex of abelian sheaves then computes `Ra_*`
(`CategoryTheory.SimplicialSiteSituation.Augmentation.InverseImageComputesDerivedPushforward`),
and Stacks 0D8L, Stacks 0D8N and Stacks 0D8G hold with no hypothesis beyond the hypercovering
conditions.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.quasiIso_map_resolutionChainAugmentation_freeYoneda_over`: **`a_!` carries the augmentation of
  the resolution of Stacks 0D78 of `a^{-1}ℤ_V^♯` to a quasi-isomorphism**, for a hypercovering of
  an object `X` and every object `V` of `C/X`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageComputesDerivedPushforward_over_of_isHypercovering`: **the second input of
  Stacks 0D8L holds for a hypercovering of an object**, with no hypothesis beyond the hypercovering
  conditions.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`: the same over the site
  itself rather than a slice, for a hypercovering of the terminal presheaf.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.isIso_derivedAugmentationUnitOver_app_of_isHypercovering_unconditional`,
  `.isIso_derivedAugmentationUnitAugmented_app_unconditional` and
  `.isIso_derivedAugmentationUnit_app_of_hypercovering_unconditional`: the canonical map
  `E ⟶ Ra_* a⁻¹ E` is an isomorphism (Stacks 0D8L, Stacks 0D8N, Stacks 0D8G).

## Implementation notes

* The three tagged theorems restate forms lower in the import order which take the
  `Ra_*`-acyclicity of `a⁻¹` of a K-injective complex as an explicit input.
* In `quasiIso_map_resolutionChainAugmentation_freeYoneda_over` the objects `V` are quantified
  inside the statement, because the sheaf categories it mentions depend on the topology of `C/X`.

## References

* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8N](https://stacks.math.columbia.edu/tag/0D8N)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation
open Stacks.Cohomology.CohomologyPresheaf

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable Stacks.CategoryTheory.Hypercovering

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

section Terminal

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} P)

/-- **The second input of Stacks 0D8L holds for a hypercovering of the site itself**: for a site
`C` with equalizers and fibre products and a hypercovering `K` of its terminal presheaf, the
inverse image `a^{-1}` of a K-injective complex of abelian sheaves on `C` computes `Ra_*` along
the augmentation `a` of Stacks 0D8B. -/
theorem inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal :
    Augmentation.InverseImageComputesDerivedPushforward
      (situation P.toGrothendieck H.toSimplicialObject) (Cat.of C) P.toGrothendieck
      (situationAugmentation P.toGrothendieck H.toSimplicialObject) :=
  inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda_chain
    P.toGrothendieck H.toSimplicialObject
    (quasiIso_map_resolutionChainAugmentation_freeYoneda P H)

end Terminal

section Over

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X))) (hK : IsHypercovering P K)

include hK in
/-- **The extension by zero `a_!` carries the augmentation of the resolution of Stacks 0D78 of
`a^{-1}ℤ_V^♯` to a quasi-isomorphism, for a hypercovering of an object `X`** and every object `V`
of the slice site `C/X`. -/
theorem quasiIso_map_resolutionChainAugmentation_freeYoneda_over :
    ∀ V : Over X, QuasiIso
      (((augmentationAbelianLowerShriek (P.toGrothendieck.over X) K).mapHomologicalComplex
          (ComplexShape.down ℕ)).map
        (Augmentation.resolutionChainAugmentation (situation (P.toGrothendieck.over X) K)
          (Cat.of (Over X)) (P.toGrothendieck.over X)
          (situationAugmentation (P.toGrothendieck.over X) K)
          (freeYonedaSheaf (P.toGrothendieck.over X) V))) := by
  have : HasFiniteLimits (Over X) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  obtain ⟨H, hH⟩ := exists_hypercoveringOfTerminal_over_of_isHypercovering P K hK
  have hQ : ((P.toGrothendieck.over X).toPretopology).toGrothendieck =
      P.toGrothendieck.over X := (Pretopology.gi (C := Over X)).l_u_eq _
  rw [← hQ, ← hH]
  exact quasiIso_map_resolutionChainAugmentation_freeYoneda _ H

include hK in
/-- **The second input of Stacks 0D8L holds for a hypercovering of an object**: for a site `C`
with fibre products, an object `X` of `C` and a hypercovering `K` of `X`, the inverse image
`a^{-1}` of a K-injective complex of abelian sheaves on `C/X` computes `Ra_*` along the
augmentation of Stacks 0D8B read over `C/X`. -/
theorem inverseImageComputesDerivedPushforward_over_of_isHypercovering :
    Augmentation.InverseImageComputesDerivedPushforward
      (situation (P.toGrothendieck.over X) K) (Cat.of (Over X)) (P.toGrothendieck.over X)
      (situationAugmentation (P.toGrothendieck.over X) K) :=
  inverseImageComputesDerivedPushforward_of_quasiIso_freeYoneda_chain
    (P.toGrothendieck.over X) K
    (quasiIso_map_resolutionChainAugmentation_freeYoneda_over P K hK)

end Over

/-! ### Stacks 0D8L, 0D8N and 0D8G with no hypothesis beyond the hypercovering conditions -/

section Downstream

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C]

/-- For a hypercovering `K` of an object `X` of a site `C` with fibre products, the canonical map
`E ⟶ Ra_* a⁻¹ E` is invertible at every object `E` of the unbounded derived category of abelian
sheaves on `C/X`. -/
@[stacks 0D8L "for a hypercovering K of X, the map E → Ra_*a⁻¹E is an isomorphism for every
E in D(C/X)"]
theorem isIso_derivedAugmentationUnitOver_app_of_isHypercovering_unconditional
    (P : Pretopology C) {X : C} (K : SimplicialObject (FormalCoproduct.{u} (Over X)))
    (hK : IsHypercovering P K)
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitOver P.toGrothendieck X K).app E) :=
  isIso_derivedAugmentationUnitOver_app_of_isHypercovering_of_quasiIso_freeYoneda_chain P K hK
    (quasiIso_map_resolutionChainAugmentation_freeYoneda_over P K hK) E

/-- For a site `C` with fibre products given by a pretopology `P`, an object `X` of `C` and a
hypercovering `a : U ⟶ X` of `X` in `C` by a simplicial object `U` of `C`, in the sense of
Stacks 09X8, the canonical map `E ⟶ Ra_* a⁻¹ E` is invertible at every object `E` of the
unbounded derived category `D(C/X)` of abelian sheaves on `C/X`.

As in the source, this is Stacks 0D8L for the associated simplicial semi-representable object
`n ↦ {U_n ⟶ X}` over `X`. -/
@[stacks 0D8N]
theorem isIso_derivedAugmentationUnitAugmented_app_unconditional (P : Pretopology C) {X : C}
    (U : SimplicialObject C) (a : U ⟶ (SimplicialObject.const C).obj X)
    (h : IsHypercoveringAugmentation P U a)
    (E : DerivedCategory (AbelianSheavesOver P.toGrothendieck X)) :
    IsIso ((derivedAugmentationUnitAugmented P U a).app E) :=
  isIso_derivedAugmentationUnitAugmented_app' P U a h
    (fun I hI => isIso_derivedAbelianTotalPushforwardOverUnit_app_inverseImage P.toGrothendieck X
      (associatedSimplicialObject.{u} U a)
      (inverseImageComputesDerivedPushforward_over_of_isHypercovering P
        (associatedSimplicialObject.{u} U a) (h.isHypercovering P U a)) I hI) E

end Downstream

section DownstreamTerminal

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u} P)

/-- For a site `C` with equalizers and fibre products, a hypercovering `K` of it and the
augmentation `a : Sh((C/K)_total) ⟶ Sh(C)` of Stacks 0D8B, the canonical map `E ⟶ Ra_* a⁻¹ E` is
an isomorphism at every object `E` of the unbounded derived category of abelian sheaves on `C`.

No boundedness is assumed on `E`, as in the source. The untagged forms
`Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering'` and
`Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering` take the
`Ra_*`-acyclicity of `a⁻¹` of a K-injective complex (and, for the latter, Stacks 0D8E) as
hypotheses; here the acyclicity is
`inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal`. -/
@[stacks 0D8G]
theorem isIso_derivedAugmentationUnit_app_of_hypercovering_unconditional
    (E : DerivedCategory (Sheaf P.toGrothendieck AddCommGrpCat.{u})) :
    IsIso ((Augmentation.derivedAugmentationUnit (hypercoveringSituation P H) (Cat.of C)
      P.toGrothendieck (hypercoveringAugmentation P H)).app E) :=
  Stacks.CategoryTheory.Hypercovering.isIso_derivedAugmentationUnit_app_of_hypercovering' P H
    (inverseImageComputesDerivedPushforward_of_hypercoveringOfTerminal P H) E

end DownstreamTerminal

end CategoryTheory.SimplicialSemiRepresentable

end

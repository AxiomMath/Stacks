module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic

/-!
# The identity law for pullback is monoidal

Let `Z` be a ringed space. Pullback of sheaves of modules along the identity is the identity
functor — the isomorphism is `Stacks.PullbackPseudofunctor.modulePullbackIdIso`, obtained from the
uniqueness of left adjoints. This file proves that this isomorphism is **monoidal** for the
monoidal structure of `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, whose
tensorator is the comparison of [Stacks, Tag 01CD], and for the canonical monoidal structure on
the identity functor.

It is the unitality counterpart of
`Stacks.PullbackTensorCoherence.isMonoidal_pullbackCompIso_hom`, which does the same for the
composition law `f^* g^* ≅ (f ≫ g)^*`. Together the two say that `X ↦ Mod(𝒪_X)` with the
comparison of Tag 01CD is pseudofunctorial *through monoidal functors*, which is what a consumer
needs in order to pull a sheaf of **algebras** back along an identity and recognise the result:
`CategoryTheory.Functor.mapMonNatIso` turns a monoidal natural isomorphism of lax monoidal
functors into an isomorphism of the induced functors on monoid objects, so with this file
`(𝟙 Z)^* A ≅ A` as sheaves of algebras and not merely as sheaves of modules.

## Why there is no new comparison here

`pullbackIdIso` below is **not** a new construction. The repository already contains the
isomorphism `(𝟙 Z)^* ≅ 𝟭`, in several places: `Stacks.PullbackPseudofunctor.modulePullbackIdIso`
(from `CategoryTheory.Adjunction.leftAdjointUniq`, with its three adjoint equations),
`Stacks.RingedSpace.modulePullbackId` of
`StacksFrontier/AlgebraicGeometry/ModulePullbackPseudofunctor/Basic.lean` (from Mathlib's
`SheafOfModules.pullbackId`), and three further copies under `StacksFrontier/Topology/Sheaves/`.
`pullbackIdIso` names the first of them at this namespace's spelling, exactly as
`Stacks.PullbackTensorCoherence.pullbackCompIso` names
`Stacks.DerivedPullback.Composition.modulePullbackComp`. What was missing — and all that is new
here — is the **monoidality**, together with the section formula it is proved from: no
`CategoryTheory.NatTrans.IsMonoidal` statement existed for any of those five comparisons.

## Main definitions

* `Stacks.PullbackTensorCoherence.pullbackIdIso`: the identity law `(𝟙 Z)^* ≅ 𝟭`, named at this
  namespace's spelling.

## Main results

* `Stacks.PullbackTensorCoherence.pullbackIdIso_hom_app_pullbackUnit`: **the identity law carries
  a pullback-unit image to the section itself.** This is the adjoint equation
  `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackIdIso_hom_app` read at a local
  section, and it is the only computation the rest of the file needs.
* `Stacks.PullbackTensorCoherence.sharp_id`: the structure morphism of an identity is the
  identity on local sections.
* `Stacks.PullbackTensorCoherence.pullbackUnitComparison_id` and
  `pullbackTensorComparison_id`: **the structure-sheaf comparison and the tensor comparison of
  Tag 01CD are compatible with the identity law.**
* `Stacks.PullbackTensorCoherence.isMonoidal_pullbackIdIso_hom`: **the identity law for pullback
  is a monoidal natural isomorphism** for the monoidal structure whose tensorator is the
  comparison of Tag 01CD.

## Implementation notes

Both compatibility statements are equalities of morphisms out of a pullback, so
`Stacks.PullbackTensorCoherence.pullback_hom_ext` and `pullback_tensor_hom_ext` reduce them to
the pullback-unit images of the local sections, where every morphism involved has a section
formula already: `pullbackIdIso_hom_app_pullbackUnit` for the identity law,
`pullbackUnitComparison_pullbackUnit` and `pullbackTensorComparison_pullbackUnit` for the two
comparisons, and `tensorHom_tmul` for the monoidal product of two morphisms. No coherence is
discharged by automation that is not already proved.

`sharp_id` and the reduction of `opensMap (𝟙 Z)` to the identity functor on opens are both `rfl`:
a morphism of ringed spaces has `structureSheafHom (𝟙 Z) = 𝟙 (structureSheafRing Z)` and
`opensMap (𝟙 Z) = 𝟭 (Opens Z.carrier)` definitionally, which is the same computation that makes
`Stacks.PullbackPseudofunctor.modulePushforward_id` an equality rather than an isomorphism.

As in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparisonComp.lean`, the
result is for `pullbackComparisonMonoidal` and not for
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`: those are two monoidal structures on the
same functor which are not known to be equal, and the proof is available only for the first,
because it is the one whose tensorator has a section formula.

**No `@[stacks]` attribute.** Tag 01CD is carried by `Stacks.RingedSpace.comparisonIso` and the
identity law is a property of the pullback adjunction, not a result of the Stacks project; this
is plumbing, and tagging it would register a result that is not there.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097) — pullback is
  multiplicative.
-/

@[expose] public section

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace PresheafOfModules

open scoped TensorProduct

universe u

noncomputable section

namespace Stacks.PullbackTensorCoherence

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable (Z : RingedSpace.{u, u})

/-- **The identity law for pullback of sheaves of modules**, `(𝟙 Z)^* ≅ 𝟭`, named at the spelling
of this namespace. This is `Stacks.PullbackPseudofunctor.modulePullbackIdIso`; see the module
docstring for the other four copies of it in the repository. -/
noncomputable abbrev pullbackIdIso :
    pullbackFunctor (𝟙 Z) ≅ 𝟭 (SheafOfModules.{u} (structureRingSheaf Z)) :=
  Stacks.PullbackPseudofunctor.modulePullbackIdIso Z

/-- **The identity law carries the pullback-unit image of a local section to that section.** This
is `Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackIdIso_hom_app` read at a local
section: pushforward along an identity is the identity functor and the unit of the identity
adjunction is the identity, so both passages are `rfl`. -/
theorem pullbackIdIso_hom_app_pullbackUnit
    (M : SheafOfModules.{u} (structureRingSheaf Z)) (U : (Opens Z.carrier)ᵒᵖ)
    (x : M.val.obj U) :
    ((pullbackIdIso Z).hom.app M).val.app ((opensMap (𝟙 Z)).op.obj U)
        (pullbackUnit (𝟙 Z) M U x) = x := by
  have h := Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackIdIso_hom_app Z M
  exact congrArg
    (fun k : M ⟶ (modulePushforward (𝟙 Z)).obj M => k.val.app U x) h

/-- The structure morphism of an identity morphism of ringed spaces is the identity on local
sections. -/
theorem sharp_id (U : (Opens Z.carrier)ᵒᵖ) (r : (structureRingSheaf Z).obj.obj U) :
    sharp (𝟙 Z) U r = r :=
  rfl

/-- **The structure-sheaf comparison of Stacks 01CD is compatible with the identity law.** Both
sides are morphisms out of the pullback `(𝟙 Z)^* 𝒪_Z`, hence determined by their values on the
pullback-unit images of the local sections, where both carry the pullback-unit image of `r` to
`r`. -/
theorem pullbackUnitComparison_id :
    (pullbackIdIso Z).hom.app (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) =
      pullbackUnitComparison (𝟙 Z) :=
  pullback_hom_ext (𝟙 Z) fun U r ↦
    (pullbackIdIso_hom_app_pullbackUnit Z
        (𝟙_ (SheafOfModules.{u} (structureRingSheaf Z))) U r).trans
      ((sharp_id Z U r).symm.trans
        (pullbackUnitComparison_pullbackUnit (𝟙 Z) U r).symm)

variable {Z}

/-- **The comparison of Stacks 01CD is compatible with the identity law.** Both sides are
morphisms out of the pullback `(𝟙 Z)^*(A ⊗ B)`, hence determined by their values on the
pullback-unit images of the local pure tensors, where the section formulas for the comparison,
for the identity law and for the monoidal product of two morphisms compute them to the same
local pure tensor. -/
theorem pullbackTensorComparison_id (A B : SheafOfModules.{u} (structureRingSheaf Z)) :
    (pullbackIdIso Z).hom.app (A ⊗ B) =
      pullbackTensorComparison (𝟙 Z) A B ≫
        ((pullbackIdIso Z).hom.app A ⊗ₘ (pullbackIdIso Z).hom.app B) :=
  pullback_tensor_hom_ext (𝟙 Z) fun U a b ↦ by
    rw [pullbackIdIso_hom_app_pullbackUnit, SheafOfModules.comp_val_app_apply,
      pullbackTensorComparison_pullbackUnit, tensorHom_tmul,
      pullbackIdIso_hom_app_pullbackUnit, pullbackIdIso_hom_app_pullbackUnit]
    exact rfl

variable (Z)

/-- **The identity law for pullback is a monoidal natural isomorphism** for the monoidal
structure whose tensorator is the comparison of Stacks 01CD, the identity functor carrying its
canonical one. This is what makes the identity law act on sheaves of algebras, and it is the
unitality counterpart of `isMonoidal_pullbackCompIso_hom`. -/
theorem isMonoidal_pullbackIdIso_hom :
    letI := pullbackComparisonMonoidal (𝟙 Z)
    NatTrans.IsMonoidal (pullbackIdIso Z).hom :=
  let := pullbackComparisonMonoidal (𝟙 Z)
  { unit := by
      rw [pullbackComparisonMonoidal_epsilon, pullbackUnitComparison_id, IsIso.inv_hom_id]
      rfl
    tensor := fun M N ↦ by
      rw [pullbackComparisonMonoidal_mu, pullbackTensorComparison_id, IsIso.inv_hom_id_assoc]
      rfl }

end Stacks.PullbackTensorCoherence

end

end

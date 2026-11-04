module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Cokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Product
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Restriction of coherent adic systems is exact on the right, and is jointly faithful

Let `X` be a locally Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf on `X` and `f : Y ⟶ X`
an open immersion. Restriction `Coh(X, ℐ) ⥤ Coh(Y, ℐ|_Y)` commutes with the formation of
cokernels, and more generally preserves all finite colimits. This is the local half of
[Stacks, Tag 087X] (2): the cokernel of a morphism of coherent adic systems may be computed on
the members of an open covering.

The reason is that both categories compute cokernels levelwise. The inclusion of `Coh(X, ℐ)`
into `ℕᵒᵖ ⥤ X.Modules` creates, hence preserves, the cokernel of a morphism
(`Stacks.Coherent.preservesColimitParallelPairι`); termwise restriction preserves it because
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a left adjoint and a colimit in a functor
category is computed pointwise; and the inclusion of `Coh(Y, ℐ|_Y)` is fully faithful, so it
reflects what the composite preserves.

The companion statement of [Stacks, Tag 087X] (3) is that this computation determines a morphism:
a morphism of coherent adic systems whose restriction to each member of an open covering vanishes
is itself zero, because an equality of morphisms of sheaves of modules is a local condition.

## Main results

* `Stacks.Coherent.restrictFunctor_preservesColimitParallelPair` — **restriction preserves the
  cokernel of a morphism of coherent adic systems.**
* `Stacks.Coherent.restrictFunctor_preservesFiniteColimits` — restriction preserves all finite
  colimits of coherent adic systems.
* `Stacks.Coherent.hom_eq_zero_of_restrictFunctor_map_eq_zero` — a morphism of sheaves of modules
  on a scheme vanishing on every member of an open covering vanishes.
* `Stacks.Coherent.hom_eq_zero_of_restrictFunctor_map_eq_zero_system` — **the same for a morphism
  of coherent adic systems.**

## Implementation notes

The covering family of `Stacks.Coherent.hom_eq_zero_of_restrictFunctor_map_eq_zero` and of
`Stacks.Coherent.hom_eq_zero_of_restrictFunctor_map_eq_zero_system` is indexed by a type in an
unrelated universe: the statements are applied to coverings by affine opens, whose index type is
a subtype of the opens of `X` and so lives one universe up.

Passing from the preservation of cokernels to the preservation of all finite colimits is
`CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels`, whose hypotheses on
`Coh(X, ℐ)` are supplied from `Stacks.Coherent.hasFiniteProducts` and
`Stacks.Coherent.hasCokernels_coherentAdicSystems`: a preadditive category with finite products
has finite biproducts, hence finite coproducts and a zero object, and one with cokernels has
coequalizers.

## References

* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace Stacks.Coherent

/-! ### Restriction preserves cokernels -/

/-- **Restriction along an open immersion preserves the cokernel of a morphism of coherent adic
systems.** Equivalently, the cokernel in `Coh(X, ℐ)` may be computed after restricting to an open
subscheme.

Cokernels are levelwise on both sides: the inclusion of `Coh(X, ℐ)` into `ℕᵒᵖ ⥤ X.Modules`
preserves this cokernel, termwise restriction preserves it because
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` is a left adjoint and colimits in a functor
category are pointwise, and the inclusion of `Coh(Y, ℐ|_Y)` is fully faithful, hence reflects
colimits. -/
public instance restrictFunctor_preservesColimitParallelPair {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] {F G : CoherentAdicSystems I} (α : F ⟶ G) :
    PreservesColimit (parallelPair α 0) (Stacks.Coherent.restrictFunctor I f) :=
  have : PreservesColimit (parallelPair α 0)
      (restrictFunctor I f ⋙ ObjectProperty.ι (IsCoherentAdicSystem (I.comap f))) :=
    preservesColimit_of_natIso _ (restrictFunctorCompιIso I f).symm
  preservesColimit_of_reflects_of_preserves (restrictFunctor I f)
    (ObjectProperty.ι (IsCoherentAdicSystem (I.comap f)))

/-- **Restriction along an open immersion preserves finite colimits of coherent adic systems.**

`Coh(X, ℐ)` is preadditive with finite products and cokernels, so it has finite coproducts, a
zero object and coequalizers; a functor out of such a category which preserves cokernels
preserves every finite colimit. -/
public instance restrictFunctor_preservesFiniteColimits {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] :
    PreservesFiniteColimits (Stacks.Coherent.restrictFunctor I f) :=
  have : HasFiniteBiproducts (CoherentAdicSystems I) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteBiproducts (CoherentAdicSystems (I.comap f)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts (CoherentAdicSystems I) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : HasCoequalizers (CoherentAdicSystems I) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels (restrictFunctor I f)

/-! ### A morphism vanishing on an open covering vanishes -/

/-- **Vanishing of a morphism of sheaves of modules is a local condition.** A morphism of sheaves
of modules on a scheme whose restriction to every member of an open covering is zero is zero.

Only the separatedness half of the sheaf condition is used. -/
public theorem hom_eq_zero_of_restrictFunctor_map_eq_zero {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    (hg : ∀ j, (Scheme.Modules.restrictFunctor (U j).ι).map g = 0) : g = 0 :=
  Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover U
    (fun x => Opens.mem_iSup.1 (hU ▸ Opens.mem_top x))
    fun j => (hg j).trans ((Scheme.Modules.restrictFunctor (U j).ι).map_zero M N).symm

/-- **Vanishing of a morphism of coherent adic systems is a local condition.** A morphism of
coherent adic systems whose restriction to every member of an open covering is zero is zero.

This is the uniqueness clause of [Stacks, Tag 087X] (3): morphisms in `Coh(X, ℐ)` are natural
transformations of the underlying inverse systems, so the statement is
`Stacks.Coherent.hom_eq_zero_of_restrictFunctor_map_eq_zero` applied level by level. -/
public theorem hom_eq_zero_of_restrictFunctor_map_eq_zero_system {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (α : F ⟶ G)
    {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    (hα : ∀ j, (Stacks.Coherent.restrictFunctor I (U j).ι).map α = 0) : α = 0 := by
  refine ObjectProperty.hom_ext (IsCoherentAdicSystem I) (NatTrans.ext (funext fun n => ?_))
  refine hom_eq_zero_of_restrictFunctor_map_eq_zero (α.hom.app n) U hU fun j => ?_
  exact congrArg (fun β => β.hom.app n) (hα j)

end Stacks.Coherent

end

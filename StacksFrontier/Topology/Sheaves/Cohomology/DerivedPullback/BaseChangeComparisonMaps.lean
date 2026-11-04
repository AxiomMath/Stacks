module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap

/-!
# The base-change comparison maps for a derived tensor product and a derived internal hom

Let `h : (X', 𝒪_{X'}) ⟶ (X, 𝒪_X)` be a morphism of ringed spaces, let `K ∈ D(𝒪_X)`, let
`K' ∈ D(𝒪_{X'})` and let `φ : Lh^*K ⟶ K'`.  Such a datum `(K, K', φ)` propagates to a derived
tensor product and to a derived internal hom: for `E ∈ D(𝒪_X)` there are canonical maps

`Lh^*(E ⊗^L_{𝒪_X} K) ⟶ Lh^*E ⊗^L_{𝒪_{X'}} K'`

and

`Lh^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(Lh^*E, K')`,

each obtained by composing the canonical map for `K` itself — the monoidality of derived
pullback (Tag 079U) in the first case, the map of Tag 08I3 in the second — with the map
induced by `φ` in the second argument.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison`: the map
  `Lh^*(E ⊗^L_{𝒪_X} K) ⟶ Lh^*E ⊗^L_{𝒪_{X'}} K'`.
* `Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison`: the map
  `Lh^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(Lh^*E, K')`.

## Main results

* `Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeTensorComparison_comp` and
  `Stacks.Cohomology.DerivedBaseChangeComparison.baseChangeSheafHomComparison_comp`: both maps
  are natural in the target of `φ`, so a datum `(K, K', φ)` and a morphism `ψ : K' ⟶ K''`
  propagate as the datum `(K, K'', φ ≫ ψ)`.

## Implementation notes

*No hypotheses beyond the morphism.*  Derived pullback exists for every morphism of ringed
spaces (Tag 079W), the derived tensor product and the derived internal hom for every ringed
space (Tags 06YU, 08DI), and the two canonical maps for every morphism (Tags 079U, 08I3); so
the only data are `h`, `E`, `K`, `K'` and `φ`.  Nothing is required of `φ`, and neither map is
an isomorphism in general.

*Naturality in the target of `φ`.*  Both maps are a composite whose first factor — the
monoidality isomorphism, respectively the map of Tag 08I3 — does not involve `φ` at all, so
replacing `φ` by `φ ≫ ψ` only composes the comparison with the map induced by `ψ`.  That is the
content of the two lemmas below, and it is what identifies the pointwise base-change map of
Stacks 0DJ7 on either comparison in
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorAndSheafHomBaseChange`.  Each
is proved as a term — `Functor.map_comp` carried through the unchanged first factor by
`congrArg`, then reassociated — and not by `rw`: because both statements mix the two spellings
of the category of module sheaves, their goals are not type-correct at `implicit` transparency,
and there `rw` refuses the `F.map (f ≫ g)` pattern they visibly contain.

*One spelling for the category of module sheaves.*  The derived pullback of Tag 079W is
declared over `SheafOfModules (structureSheafRing X)`, the derived tensor
product and the derived internal hom over
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)`.  The two are the same sheaf
of rings by `rfl`, and both statements below mix them; the first is a `def` and so is made
reducible at `implicit` transparency for this file, which is what makes the two types
recognised as equal.

## References

* [Stacks Project, Tag 0DJA](https://stacks.math.columbia.edu/tag/0DJA)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.Cohomology.DerivedBaseChangeComparison

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback of Tag 079W names the structure sheaf of a ringed space by
-- `structureSheafRing`, the derived tensor product and the derived internal hom by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`.  The two are the same sheaf of rings by `rfl`, and
-- the statements below mix them; `structureSheafRing` is `@[instance_reducible]`, so it already
-- unfolds at `implicit` transparency, but its reduct stops at an explicit-constructor
-- projection and `Tensor.ringSheaf X.sheaf` reduces to `(sheafCompose _ _).obj X.sheaf`, so
-- closing the gap needs these two Mathlib definitions unfoldable there as well.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

noncomputable section

variable {X' X : RingedSpace.{u, u}} (h : X' ⟶ X)
  (E K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
  (K' K'' : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X'))
  (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj K ⟶ K')

/-- **The base-change comparison for a derived tensor product.**  For a morphism of ringed
spaces `h : X' ⟶ X`, objects `E, K` of `D(𝒪_X)`, an object `K'` of `D(𝒪_{X'})` and a morphism
`φ : Lh^*K ⟶ K'`, the canonical map

`Lh^*(E ⊗^L_{𝒪_X} K) ⟶ Lh^*E ⊗^L_{𝒪_{X'}} K'`

in `D(𝒪_{X'})`.  It is the monoidality isomorphism of Tag 079U at the pair `(E, K)` followed
by `Lh^*E ⊗^L_{𝒪_{X'}} φ`. -/
def baseChangeTensorComparison :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E).obj K) ⟶
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj E)).obj K' :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso h).hom.app (E, K) ≫
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj E)).map φ

/-- **The base-change comparison for a derived internal hom.**  For a morphism of ringed spaces
`h : X' ⟶ X`, objects `E, K` of `D(𝒪_X)`, an object `K'` of `D(𝒪_{X'})` and a morphism
`φ : Lh^*K ⟶ K'`, the canonical map

`Lh^*R𝓗om_{𝒪_X}(E, K) ⟶ R𝓗om_{𝒪_{X'}}(Lh^*E, K')`

in `D(𝒪_{X'})`.  It is the canonical map of Tag 08I3 followed by
`R𝓗om_{𝒪_{X'}}(Lh^*E, φ)`. -/
def baseChangeSheafHomComparison :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op E)).obj K) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj
            E))).obj K' :=
  Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap h E K ≫
    ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
      (op ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj E))).map φ

/-- Precomposing with `F.map (φ ≫ ψ)` is precomposing with `F.map φ` and then `F.map ψ`. -/
private theorem comp_map_comp {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {A : D}
    {X Y Z : C} (f : A ⟶ F.obj X) (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    f ≫ F.map (φ ≫ ψ) = (f ≫ F.map φ) ≫ F.map ψ :=
  (congrArg (f ≫ ·) (F.map_comp φ ψ)).trans (Category.assoc _ _ _).symm

/-- The base-change comparison for a derived tensor product is natural in the target of `φ`:
composing `φ` with `ψ : K' ⟶ K''` composes the comparison with `Lh^*E ⊗^L_{𝒪_{X'}} ψ`. -/
theorem baseChangeTensorComparison_comp (ψ : K' ⟶ K'') :
    baseChangeTensorComparison h E K K'' (φ ≫ ψ) =
      baseChangeTensorComparison h E K K' φ ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X'.sheaf).obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj E)).map ψ :=
  by unfold baseChangeTensorComparison; exact comp_map_comp _ _ φ ψ

/-- The base-change comparison for a derived internal hom is natural in the target of `φ`:
composing `φ` with `ψ : K' ⟶ K''` composes the comparison with
`R𝓗om_{𝒪_{X'}}(Lh^*E, ψ)`. -/
theorem baseChangeSheafHomComparison_comp (ψ : K' ⟶ K'') :
    baseChangeSheafHomComparison h E K K'' (φ ≫ ψ) =
      baseChangeSheafHomComparison h E K K' φ ≫
        ((Stacks.SheafOfModules.derivedSheafHom X'.sheaf).obj
          (op ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).obj
            E))).map ψ :=
  by unfold baseChangeSheafHomComparison; exact comp_map_comp _ _ φ ψ

end

end Stacks.Cohomology.DerivedBaseChangeComparison

end

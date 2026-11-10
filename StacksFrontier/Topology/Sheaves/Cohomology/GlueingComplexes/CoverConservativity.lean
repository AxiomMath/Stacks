module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# A cover by two open immersions detects isomorphisms of unbounded derived modules

Let `X` be a ringed space and let `jU : U ⟶ X` and `jV : V ⟶ X` be open immersions whose images
cover `X`.  A morphism of `D(𝒪_X)` whose derived restrictions along `jU` and along `jV` are
invertible is invertible.

This is the conservativity that distinguishes a *cover* by two opens from an arbitrary pair of
opens, and it is the one input of [Stacks, Tag 08DG] that the first clause of that tag does not
need: the glued object exists for any two opens, and a cover is what pins it down.

## Main results

* `Stacks.Cohomology.GlueingComplexes.isIso_derivedPullback_map_of_comp`: invertibility of a
  derived restriction passes to a smaller open.
* `Stacks.Cohomology.GlueingComplexes.isIso_jStar_mapDerivedCategory_map_of_isIso`: the crossing
  from the derived pullback along an abstract open immersion to the derived restriction to its
  image, which is the spelling the stalkwise criterion is stated in.
* `Stacks.Cohomology.GlueingComplexes.isIso_of_isIso_derivedPullback_of_cover`: the
  conservativity itself.

## Implementation notes

The stalkwise criterion
`PushforwardRestriction.isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar` is stated
for two opens of the underlying space and for `ExtensionByZeroModules.jStar`, the
restriction functor whose derived functor is `CategoryTheory.Functor.mapDerivedCategory`.  The
glueing material is stated for abstract open immersions of ringed spaces and for the derived
pullback of [Stacks, Tag 079W].  The two are crossed in two steps, neither of which is new
here: an open immersion factors through the inclusion of its image by an isomorphism of ringed
spaces (`Stacks.Cohomology.RelativeMayerVietoris.openImmersionImageIso`), and derived pullback
along the inclusion of an open subspace is derived restriction
(`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso`).

The isomorphism of ringed spaces is crossed in the direction that needs no reflection: rather
than factor `Lj_U^*` as `Lj^* ⋙ Le_{hom}^*` and reflect invertibility along the equivalence
`Le_{hom}^*`, the inverse factorisation `e^{-1} ≫ j_U = j` is used, so that `Lj^*` is
`Lj_U^* ⋙ Le_{inv}^*` and a functor carrying an isomorphism to an isomorphism is all that is
needed.

No statement below writes `derivedPullback` of a *composite or concrete* morphism of ringed
spaces: the existence instance
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`
carries two free derived-category universes that instance search does not solve against a
morphism that is not a local variable, so every such functor is reached by instantiating a
lemma whose own statement names only variables.

## References

* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.RelativeMayerVietoris
open Stacks.Cohomology.HigherDirectImage

namespace Stacks.Cohomology.GlueingComplexes

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_jStar preservesFiniteColimits_jStar

/-- The inverse of `Stacks.Cohomology.RelativeMayerVietoris.openImmersionImageIso` factors the
inclusion of the image of an open immersion through the open immersion itself. -/
theorem openImmersionImageIso_inv_comp {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j] :
    (openImmersionImageIso j).inv ≫ j = openSubspaceInclusion X (immImage j) := by
  have h := openImmersionImageIso_hom_comp j
  calc (openImmersionImageIso j).inv ≫ j
      = (openImmersionImageIso j).inv ≫ (openImmersionImageIso j).hom ≫
          openSubspaceInclusion X (immImage j) := by rw [h]
    _ = openSubspaceInclusion X (immImage j) := by rw [Iso.inv_hom_id_assoc]

/-- **Invertibility of a derived restriction passes to a smaller open.**  If `Lj^*φ` is
invertible then so is `L(i ≫ j)^*φ`, by the composition isomorphism of [Stacks, Tag 0D5S]. -/
theorem isIso_derivedPullback_map_of_comp {X U W : RingedSpace.{u, u}} (j : U ⟶ X) (i : W ⟶ U)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L)
    (hj : IsIso ((derivedPullback j).map φ)) :
    IsIso ((derivedPullback (i ≫ j)).map φ) := by
  have hcomp : IsIso ((derivedPullback j ⋙ derivedPullback i).map φ) := by
    have := hj
    change IsIso ((derivedPullback i).map ((derivedPullback j).map φ))
    infer_instance
  exact (NatIso.isIso_map_iff
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical i j) φ).mp hcomp

/-- **The crossing of the two spellings of restriction to an open.**  If the derived pullback
along an open immersion `j` carries `φ` to an isomorphism, then so does the derived restriction
to the image of `j`, in the `ExtensionByZeroModules.jStar` spelling in which isomorphisms are
detected on stalks. -/
theorem isIso_jStar_mapDerivedCategory_map_of_isIso {X U : RingedSpace.{u, u}} (j : U ⟶ X)
    [SheafedSpace.IsOpenImmersion j]
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L)
    (hj : IsIso ((derivedPullback j).map φ)) :
    IsIso ((jStar (immImage j) (structureSheafRing X)).mapDerivedCategory.map φ) :=
  (NatIso.isIso_map_iff
      (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso X
        (immImage j)) φ).mp
    ((NatIso.isIso_map_iff
        (eqToIso (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullback_eq_of_eq
          (openImmersionImageIso_inv_comp j))) φ).mp
      (isIso_derivedPullback_map_of_comp j (openImmersionImageIso j).inv φ hj))

/-- **A cover by two open immersions detects isomorphisms of unbounded derived modules.**  Let
`jU : U ⟶ X` and `jV : V ⟶ X` be open immersions of ringed spaces whose images cover `X`.  A
morphism of `D(𝒪_X)` whose derived restrictions to `U` and to `V` are invertible is
invertible. -/
theorem isIso_of_isIso_derivedPullback_of_cover {X U V : RingedSpace.{u, u}} (jU : U ⟶ X)
    (jV : V ⟶ X) [SheafedSpace.IsOpenImmersion jU] [SheafedSpace.IsOpenImmersion jV]
    (hcover : Set.range jU.hom.base ∪ Set.range jV.hom.base = Set.univ)
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L)
    (hU : IsIso ((derivedPullback jU).map φ)) (hV : IsIso ((derivedPullback jV).map φ)) :
    IsIso φ := by
  refine PushforwardRestriction.isIso_derived_of_isIso_restrictions_on_cover_of_exact_jStar
    (structureSheafRing X) (immImage jU) (immImage jV) (fun x => ?_) φ
    (isIso_jStar_mapDerivedCategory_map_of_isIso jU φ hU)
    (isIso_jStar_mapDerivedCategory_map_of_isIso jV φ hV)
  have hx : x ∈ Set.range jU.hom.base ∪ Set.range jV.hom.base := by
    rw [hcover]
    exact Set.mem_univ x
  exact hx

end Stacks.Cohomology.GlueingComplexes

end

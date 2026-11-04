module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaComplexes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product on a scheme, and the projection formula at a closed immersion

For a scheme `Z` the derived tensor product of `Z`-modules is the one the ringed site of `Z`
carries, `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf`. This file
records the two elementary facts about it that a dévissage over a resolution needs — it adds
cohomological bounds, and tensoring on the left with the structure sheaf in degree zero is the
identity — and the projection formula `Ri_*Li^*G ≅ Ri_*𝒪_U ⊗^𝐋_{𝒪_Z} G` at a closed immersion
of schemes. It also records that the comparison functor `ModuleCat Γ(Z, ⊤) ⥤ Z.Modules` of an
affine scheme is exact.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isLE_derivedTensorProduct`: the derived tensor product of an
  object of `D^{≤ a}(𝒪_Z)` with an object of `D^{≤ b}(𝒪_Z)` lies in `D^{≤ a + b}(𝒪_Z)`.
* `AlgebraicGeometry.Scheme.Modules.derivedTensorUnitLeftIso`: `𝒪_Z ⊗^𝐋_{𝒪_Z} G ≅ G`, the
  structure sheaf being placed in degree zero and tensored on the left.
* `Stacks.ClosedImmersion.nonempty_derivedPushforwardDerivedPullbackIsoTensor`: for a closed
  immersion of schemes `i : U ⟶ Z` and any `G` in `D(𝒪_Z)`, `Ri_*Li^*G` is the derived tensor
  product of `Ri_*𝒪_U` with `G`.
* `Stacks.AlgebraicGeometry.AffineTilde.additive_tildeOf`,
  `preservesFiniteLimits_tildeOf`, `preservesFiniteColimits_tildeOf` and
  `isTriangulated_mapDerivedCategory_tildeOf`: the comparison functor of an affine scheme is
  additive and exact, hence induces a triangulated functor on derived categories.

## Implementation notes

**The two spellings of the category of modules.** The derived tensor product is indexed by
`Stacks.DerivedTensor.RingedSite.Modules Z.sheaf`, which is
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)`, while a client of relative
pseudo-coherence works in `AlgebraicGeometry.Scheme.Modules`, which is
`SheafOfModules Z.ringCatSheaf`. The two are equal at default transparency but not at the
reducible transparency instance search uses, since the two sheaves of rings unfold to each other
only through `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`. A statement
whose *type* mentions both elaborates without help, but an `IsLE` hypothesis stated at one
spelling is not found by instance search at the other. That is why
`AlgebraicGeometry.Scheme.Modules.isLE_derivedTensorProduct` takes its two boundedness
hypotheses as explicit arguments and discharges them through an auxiliary statement quantified at
the derived-tensor spelling, rather than restating
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct` directly.

**The left unit law, not the right one.** The projection formula produces `Ri_*𝒪_U` in the *left*
slot of the tensor product, so a dévissage over a resolution of `Ri_*𝒪_U` meets the unit in the
left slot too. The library's unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso` is the right one and is stated for the
`AlgebraicGeometry.RingedSite`-indexed flavour of the derived tensor product, not for the
`Z.sheaf`-indexed one used here. The left law below is therefore built from the one-sided K-flat
comparison `comparisonLeft` at the K-flat complex `𝒪_Z[0]`
(`Stacks.SheafOfModules.isKFlat_single_unit`), followed by the Koszul symmetry
`Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` and the right law on complexes
`Stacks.SheafOfModules.tensorComplexUnitIso`.

**Exactness of the affine comparison functor** is stated here rather than where
`Stacks.AlgebraicGeometry.AffineTilde.tildeOf` is defined, because the triangulatedness of the
induced functor on derived categories is stated at the derived categories supplied by
`CategoryTheory.HasDerivedCategory.standard`, which is made a local instance; there is no global
instance, so a user of these results makes the same declaration. The three exactness facts are
`AlgebraicGeometry.tilde.functor`'s, transported along pullback by
`AlgebraicGeometry.Scheme.isoSpec`, which is an equivalence of the categories of modules.

## References

* [The Stacks Project, Lemma 20.47.6 (0B55)](https://stacks.math.columbia.edu/tag/0B55)
* [The Stacks Project, Section 20.26 (06YU)](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Lemma 20.26.17 (06YQ)](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open Stacks.DerivedTensor.RingedSite (canonicalDerivedTensorProduct)

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of the affine comparison functor -/

namespace Stacks.AlgebraicGeometry.AffineTilde

open _root_.AlgebraicGeometry

/-- The comparison functor of an affine scheme is additive. -/
public instance additive_tildeOf (Z : Scheme.{u}) [IsAffine Z] : (tildeOf Z).Additive := by
  unfold tildeOf; infer_instance

/-- The comparison functor of an affine scheme is left exact: `~` is, and pullback along
`AlgebraicGeometry.Scheme.isoSpec` is an equivalence. -/
public instance preservesFiniteLimits_tildeOf (Z : Scheme.{u}) [IsAffine Z] :
    PreservesFiniteLimits (tildeOf Z) := by
  unfold tildeOf; infer_instance

/-- The comparison functor of an affine scheme is right exact. -/
public instance preservesFiniteColimits_tildeOf (Z : Scheme.{u}) [IsAffine Z] :
    PreservesFiniteColimits (tildeOf Z) := by
  unfold tildeOf; infer_instance

/-- An exact additive functor induces a triangulated functor on derived categories, so the
comparison functor of an affine scheme does. -/
public instance isTriangulated_mapDerivedCategory_tildeOf (Z : Scheme.{u}) [IsAffine Z] :
    (tildeOf Z).mapDerivedCategory.IsTriangulated :=
  inferInstance

end Stacks.AlgebraicGeometry.AffineTilde

namespace AlgebraicGeometry

attribute [local implicit_reducible] Scheme.Modules

/-! ### The derived tensor product on a scheme -/

namespace Scheme.Modules

/-- **The derived tensor product adds cohomological bounds.** This is
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct` with its two boundedness hypotheses
taken explicitly, so that it applies to objects presented at the
`AlgebraicGeometry.Scheme.Modules` spelling of the category of modules. -/
public theorem isLE_derivedTensorProduct (Z : Scheme.{u}) (K G : DerivedCategory Z.Modules)
    (a b : ℤ) (hK : K.IsLE a) (hG : G.IsLE b) :
    (((canonicalDerivedTensorProduct Z.sheaf).tensor.obj K).obj G).IsLE (a + b) := by
  have h : ∀ K' G' : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf,
      K'.IsLE a → G'.IsLE b →
      (((canonicalDerivedTensorProduct Z.sheaf).tensor.obj K').obj G').IsLE (a + b) := by
    intro K' G' h1 h2
    let := h1
    let := h2
    exact Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct Z.sheaf _ K' G' a b
  exact h K G hK hG

/-- **Tensoring on the left with the structure sheaf in degree zero is the identity.**
`𝒪_Z[0]` is a K-flat complex, so the one-sided comparison computes the derived tensor product
with it as the total tensor complex; the Koszul symmetry moves it to the right factor, where the
unit law on complexes removes it. -/
public def derivedTensorUnitLeftIso (Z : Scheme.{u}) (G : DerivedCategory Z.Modules) :
    ((canonicalDerivedTensorProduct Z.sheaf).tensor.obj
        ((DerivedCategory.singleFunctor Z.Modules 0).obj
          (SheafOfModules.unit Z.ringCatSheaf))).obj G ≅ G :=
  letI R := Z.sheaf
  letI T := canonicalDerivedTensorProduct R
  letI N := DerivedCategory.Q.objPreimage G
  letI W := (HomologicalComplex.single
    (Stacks.DerivedTensor.RingedSite.Modules R) (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))
  (T.tensor.mapIso ((DerivedCategory.singleFunctorIsoCompQ
      (Stacks.DerivedTensor.RingedSite.Modules R) 0).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)))).app G ≪≫
    (T.tensor.obj (DerivedCategory.Q.obj W)).mapIso
      (DerivedCategory.Q.objObjPreimageIso G).symm ≪≫
    T.comparisonLeft W N (Stacks.SheafOfModules.isKFlat_single_unit R) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso R W N ≪≫
        Stacks.SheafOfModules.tensorComplexUnitIso R N) ≪≫
    DerivedCategory.Q.objObjPreimageIso G

end Scheme.Modules

end AlgebraicGeometry

/-! ### The projection formula at a closed immersion of schemes -/

namespace Stacks.ClosedImmersion

open _root_.AlgebraicGeometry

/-- **The projection formula at the structure sheaf, for a closed immersion of schemes.** For
`i : U ⟶ Z` a closed immersion and `G` an arbitrary object of `D(𝒪_Z)`, the object `Ri_*Li^*G`
is the derived tensor product of `Ri_*𝒪_U` with `G`.

This is
`ClosedEmbeddingProjectionFormulaComplexes.nonempty_derivedPushforwardDerivedPullbackIsoTensor`
(in the namespace `Stacks.Cohomology`) at the underlying morphism of ringed spaces, whose base
map is a closed embedding and whose module pushforward is right exact. It is a statement about an
existing isomorphism and not about the morphism of [Stacks, Tag 0B53], so it is not that tag. -/
@[sga "6 IX 1.8" "more general"]
public theorem nonempty_derivedPushforwardDerivedPullbackIsoTensor {U Z : Scheme.{u}} (i : U ⟶ Z)
    [IsClosedImmersion i] (G : DerivedCategory Z.Modules) :
    Nonempty ((derivedPushforward i.toLRSHom.toShHom).obj
        ((derivedPullback i.toLRSHom.toShHom).obj G) ≅
      ((canonicalDerivedTensorProduct Z.sheaf).tensor.obj
          ((derivedPushforward i.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor U.Modules 0).obj
              (SheafOfModules.unit U.ringCatSheaf)))).obj G) :=
  open Stacks.Cohomology in
  ClosedEmbeddingProjectionFormulaComplexes.nonempty_derivedPushforwardDerivedPullbackIsoTensor
    i.toLRSHom.toShHom (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i) G

end Stacks.ClosedImmersion

end

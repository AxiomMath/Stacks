module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtSheaves
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality and composition for the Ext sheaves of a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of `D(O_X)`. The *Ext sheaves*

`Ext^n_{O_X}(K, L) = H^n(RSheafHom_{O_X}(K, L))`

are the cohomology sheaves of the derived internal Hom; they are
`Stacks.SheafOfModules.derivedSheafExt` of Stacks 0BQP. They are sheaves of `O_X`-modules, not
merely abelian groups: taking cohomology of an object of `D(O_X)` lands back in `Mod(O_X)`.

Composition of derived internal Homs induces, for every `n`, a map from the `n`-th cohomology
sheaf of `RSheafHom(L, M) ⊗^L_{O_X} RSheafHom(K, L)` to `Ext^n_{O_X}(K, M)`. Together with a
Künneth map out of `Ext^a(L, M) ⊗_{O_X} Ext^b(K, L)` this is what produces the multiplication
on Ext sheaves; the map recorded here is the second half of that composite, the half that comes
from derived composition.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafExtMap`: the map of Ext sheaves induced by a morphism of the
  source, contravariantly, and of the target, covariantly.
* `Stacks.SheafOfModules.derivedSheafExtComposition`: the map on `n`-th cohomology sheaves
  induced by the derived composition morphism of Stacks 0A8V.

## Main results

* `Stacks.SheafOfModules.derivedSheafExtMap_id` and
  `Stacks.SheafOfModules.derivedSheafExtMap_comp`: the Ext sheaves are functorial,
  contravariantly in the source and covariantly in the target.
* `Stacks.SheafOfModules.derivedSheafExtComposition_natural_source`,
  `Stacks.SheafOfModules.derivedSheafExtComposition_natural_target` and
  `Stacks.SheafOfModules.derivedSheafExtComposition_dinatural_middle`: the induced map on
  cohomology sheaves inherits the three variances of derived composition.

## Implementation notes

The cohomology functor is `DerivedCategory.homologyFunctor` at the standard model of the derived
category, the model fixed by `HasDerivedCategory.standard` throughout the derived internal Hom
development, and the indexing is cohomological: `Ext^n` is `H^n` and not `H^{-n}`.

The Ext sheaves themselves are not defined here: they are
`Stacks.SheafOfModules.derivedSheafExt`, which carries the tag 0BQP, and which takes the degree
as its last argument. Everything below is stated at that definition.

The name distinguishes these Ext sheaves from `Stacks.Duality.sheafExt`, which is the right
derived functor of the internal Hom in its second variable. The two agree on sheaves placed in
degree zero, but only `derivedSheafExt` accepts arbitrary objects of `D(O_X)`, and only it
receives the derived composition morphism of Stacks 0A8V; no comparison between them is
available here.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The map of Ext sheaves `Ext^n_{O_X}(K, L) ⟶ Ext^n_{O_X}(K', L')` induced contravariantly by
`k : K' ⟶ K` and covariantly by `l : L ⟶ L'`. -/
def derivedSheafExtMap (n : ℤ) {K K' L L' : DerivedCategory (StructureSheafModules Rc)}
    (k : K' ⟶ K) (l : L ⟶ L') :
    derivedSheafExt Rc K L n ⟶ derivedSheafExt Rc K' L' n :=
  (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
    (derivedSheafHomMap Rc k l)

/-- Two identities induce the identity on an Ext sheaf. -/
@[simp]
theorem derivedSheafExtMap_id (n : ℤ) (K L : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafExtMap Rc n (𝟙 K) (𝟙 L) = 𝟙 (derivedSheafExt Rc K L n) := by
  dsimp only [derivedSheafExtMap]
  refine Eq.trans (congrArg
    (fun f => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map f)
    (RingedSite.derivedSheafHomMap_id (ringedSite Rc) (derivedInternalHom Rc) K L)) ?_
  exact CategoryTheory.Functor.map_id _ _

/-- The maps induced on Ext sheaves compose, contravariantly in the source and covariantly in
the target. -/
theorem derivedSheafExtMap_comp (n : ℤ)
    {K K' K'' L L' L'' : DerivedCategory (StructureSheafModules Rc)}
    (k : K' ⟶ K) (l : L ⟶ L') (k' : K'' ⟶ K') (l' : L' ⟶ L'') :
    derivedSheafExtMap Rc n k l ≫ derivedSheafExtMap Rc n k' l' =
      derivedSheafExtMap Rc n (k' ≫ k) (l ≫ l') := by
  dsimp only [derivedSheafExtMap]
  rw [← CategoryTheory.Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map f)
    (RingedSite.derivedSheafHomMap_comp (ringedSite Rc) (derivedInternalHom Rc) k l k' l')

variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The map on `n`-th cohomology sheaves induced by the derived composition morphism of
Stacks 0A8V,

`H^n(RSheafHom(L, M) ⊗^L_{O_X} RSheafHom(K, L)) ⟶ Ext^n_{O_X}(K, M)`.

Precomposing it with a Künneth map out of `Ext^a(L, M) ⊗_{O_X} Ext^b(K, L)`, for `a + b = n`,
gives the multiplication of Ext sheaves. -/
def derivedSheafExtComposition (K L M : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).obj
        (((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj
          (((derivedSheafHom Rc).obj (op K)).obj L)) ⟶
      derivedSheafExt Rc K M n :=
  (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
    (derivedSheafHomComposition Rc K L M)

/-- Composition of Ext sheaves is contravariant in the source object. -/
theorem derivedSheafExtComposition_natural_source (n : ℤ)
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K)
    (L M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafExtComposition Rc K L M n ≫ derivedSheafExtMap Rc n k (𝟙 M) =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op L)).obj M))
            (derivedSheafHomMap Rc k (𝟙 L))) ≫
        derivedSheafExtComposition Rc K' L M n := by
  dsimp only [derivedSheafExtComposition, derivedSheafExtMap]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map f)
    (derivedSheafHomComposition_natural_source Rc k L M)

/-- Composition of Ext sheaves is covariant in the target object. -/
theorem derivedSheafExtComposition_natural_target (n : ℤ)
    (K L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M') :
    derivedSheafExtComposition Rc K L M n ≫ derivedSheafExtMap Rc n (𝟙 K) m =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (derivedTensorMap Rc (derivedSheafHomMap Rc (𝟙 L) m)
            (𝟙 (((derivedSheafHom Rc).obj (op K)).obj L))) ≫
        derivedSheafExtComposition Rc K L M' n := by
  dsimp only [derivedSheafExtComposition, derivedSheafExtMap]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map f)
    (derivedSheafHomComposition_natural_target Rc K L m)

/-- Composition of Ext sheaves is dinatural in the intermediate object: a morphism `L ⟶ L'` may
be absorbed covariantly into the left tensor factor or contravariantly into the right one, with
the same result. -/
theorem derivedSheafExtComposition_dinatural_middle (n : ℤ)
    (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)} (l : L ⟶ L')
    (M : DerivedCategory (StructureSheafModules Rc)) :
    (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op L')).obj M))
            (derivedSheafHomMap Rc (𝟙 K) l)) ≫
        derivedSheafExtComposition Rc K L' M n =
      (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map
          (derivedTensorMap Rc (derivedSheafHomMap Rc l (𝟙 M))
            (𝟙 (((derivedSheafHom Rc).obj (op K)).obj L))) ≫
        derivedSheafExtComposition Rc K L M n := by
  dsimp only [derivedSheafExtComposition]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg
    (fun f => (DerivedCategory.homologyFunctor (StructureSheafModules Rc) n).map f)
    (derivedSheafHomComposition_dinatural_middle Rc K l M)

end Stacks.SheafOfModules

end

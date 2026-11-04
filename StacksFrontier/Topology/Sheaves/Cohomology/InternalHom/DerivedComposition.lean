module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction
public import StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.TensorTotalComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Composition for the derived internal hom on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`. Composing a map
`L ⟶ M` with a map `K ⟶ L` gives a canonical morphism

`RSheafHom(L, M) ⊗^L_{O_X} RSheafHom(K, L) ⟶ RSheafHom(K, M)`

in `D(O_X)`, functorial in all three objects. This is Stacks 0A8V.

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so the ringed-site derived composition of Stacks 0A98
applies verbatim. The declarations below read it off along `Stacks.SheafOfModules.ringedSite`,
for the derived internal hom of `Stacks.SheafOfModules.derivedInternalHom`.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHomComposition` (Stacks 0A8V): the canonical composition
  morphism.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomComposition_natural_source`,
  `Stacks.SheafOfModules.derivedSheafHomComposition_natural_target` and
  `Stacks.SheafOfModules.derivedSheafHomComposition_dinatural_middle` (Stacks 0A8V): composition
  is contravariant in the source, covariant in the target, and dinatural in the intermediate
  object.
* `Stacks.SheafOfModules.derivedSheafHomComposition_kFlatModel` (Stacks 0A8V): on K-injective
  representatives of `L` and `M` and a K-flat model of the second internal Hom complex,
  composition is the class of the composition morphism of internal Hom complexes.

## Implementation notes

Variance in the intermediate object `L` is dinaturality rather than naturality: `L` occurs
covariantly in the left tensor factor `RSheafHom(L, M)` and contravariantly in the right one
`RSheafHom(K, L)`, so a morphism `L ⟶ L'` may be absorbed into either factor, and the two
absorptions agree after composing.

The K-flat model computation needs no quasi-isomorphism hypothesis on the map
`H ⟶ SheafHom^•(K, L)`: the identity holds for every such map, and K-flatness of `H` enters only
to make the source comparison an isomorphism. The complex-level composition morphism appearing
there is `AlgebraicGeometry.RingedSite.compositionMap`, which is the declaration carrying
Stacks 0A91 and 0A8N.

`CategoryTheory.sheafCompose` is made `implicit_reducible` for this file, as in
`StacksFrontier.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection.InternalHomComplexQuasiIso`
where `ringedSite` is defined. `_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)` is
`SheafOfModules (Tensor.ringSheaf.{u, u, u} Rc)`, i.e. modules over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, whereas
`SheafOfModules (Tensor.ringSheaf.{u, u, u} Rc)` — the category the ringed-site declarations are
stated over — is modules over `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which pairs the
composite presheaf with the sheaf condition directly. The two sheaves of rings are equal, but only
after unfolding `sheafCompose`, so without this the K-injectivity hypotheses of
`derivedSheafHomComposition_kFlatModel` are carried at the first spelling and are not found at the
second.

## References

* [Stacks Project, Tag 0A8V](https://stacks.math.columbia.edu/tag/0A8V)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

/-- For objects `K`, `L`, `M` of `D(O_X)` on a ringed space, the canonical composition morphism

`RSheafHom(L, M) ⊗^L_{O_X} RSheafHom(K, L) ⟶ RSheafHom(K, M)`

in `D(O_X)`, obtained from the composition morphism of internal Hom complexes after passing to
K-injective representatives of `L` and `M` and a K-flat model of the internal Hom complex into
the representative of `L`. -/
@[stacks 0A8V "the canonical composition morphism"]
def derivedSheafHomComposition
    (K L M : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj
        (((derivedSheafHom Rc).obj (op K)).obj L) ⟶
      ((derivedSheafHom Rc).obj (op K)).obj M :=
  RingedSite.derivedSheafHomComposition (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K L M

/-- Derived composition is contravariant in the source object. -/
@[stacks 0A8V "functoriality in the source"]
theorem derivedSheafHomComposition_natural_source
    {K K' : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))}
    (k : K' ⟶ K)
    (L M : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    derivedSheafHomComposition Rc K L M ≫ derivedSheafHomMap Rc k (𝟙 M) =
      derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op L)).obj M))
          (derivedSheafHomMap Rc k (𝟙 L)) ≫
        derivedSheafHomComposition Rc K' L M :=
  RingedSite.derivedSheafHomComposition_natural_source (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) k L M

/-- Derived composition is covariant in the target object. -/
@[stacks 0A8V "functoriality in the target"]
theorem derivedSheafHomComposition_natural_target
    (K L : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))
    {M M' : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))}
    (m : M ⟶ M') :
    derivedSheafHomComposition Rc K L M ≫ derivedSheafHomMap Rc (𝟙 K) m =
      derivedTensorMap Rc (derivedSheafHomMap Rc (𝟙 L) m)
          (𝟙 (((derivedSheafHom Rc).obj (op K)).obj L)) ≫
        derivedSheafHomComposition Rc K L M' :=
  RingedSite.derivedSheafHomComposition_natural_target (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K L m

/-- Derived composition is dinatural in the intermediate object: a morphism `L ⟶ L'` may be
absorbed covariantly into the left tensor factor or contravariantly into the right one, with the
same result. -/
@[stacks 0A8V "functoriality in the intermediate object"]
theorem derivedSheafHomComposition_dinatural_middle
    (K : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))
    {L L' : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))}
    (l : L ⟶ L')
    (M : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))) :
    derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op L')).obj M))
          (derivedSheafHomMap Rc (𝟙 K) l) ≫
        derivedSheafHomComposition Rc K L' M =
      derivedTensorMap Rc (derivedSheafHomMap Rc l (𝟙 M))
          (𝟙 (((derivedSheafHom Rc).obj (op K)).obj L)) ≫
        derivedSheafHomComposition Rc K L M :=
  RingedSite.derivedSheafHomComposition_dinatural_middle (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K l M

/-- On K-injective representatives `J` of `L` and `I` of `M` and any map `f` from a K-flat
complex `H` to the internal Hom complex `SheafHom^•(K, J)`, derived composition is the class of
the composition morphism of internal Hom complexes
`Tot(SheafHom^•(J, I) ⊗_{O_X} SheafHom^•(K, J)) ⟶ SheafHom^•(K, I)`. -/
@[stacks 0A8V "comparison with composition of complexes"]
theorem derivedSheafHomComposition_kFlatModel
    (K J I H : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)
    [hJ : J.IsKInjective] [hI : I.IsKInjective] (hH : IsKFlat Rc H)
    (f : H ⟶ (sheafHomComplex Rc K J).obj) :
    ((derivedTensor Rc).obj
            (((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj J))).obj
              (DerivedCategory.Q.obj I))).map
          (DerivedCategory.Q.map f ≫
            (@RingedSite.derivedSheafHomComparison (ringedSite Rc) _ K J hJ).inv) ≫
        derivedSheafHomComposition Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj J)
          (DerivedCategory.Q.obj I) ≫
        (@RingedSite.derivedSheafHomComparison (ringedSite Rc) _ K I hI).hom =
      (RingedSite.derivedEvaluationSourceComparison (ringedSite Rc)
            (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc)
            H J I hH).hom ≫
        DerivedCategory.Q.map (tensorTotalMap Rc (𝟙 (sheafHomComplex Rc J I).obj) f) ≫
        DerivedCategory.Q.map (RingedSite.compositionMap (ringedSite Rc) K J I) :=
  RingedSite.derivedSheafHomComposition_kFlatModel (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K J I H hH f

end Stacks.SheafOfModules

end

module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.GlobalInvertible
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreTensorInstance
public import StacksFrontier.Homology.KFlat.ScalarEquivalenceDerivedTensor
public import StacksFrontier.Homology.Tor.CanonicalTensorDerivedBifunctor
public import StacksFrontier.Homology.Tor.DerivedTensorDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# The derived form of Tag 01CB on a fibre product of schemes

`AlgebraicGeometry.FibreTensorComparisons f g` bundles the comparisons for the derived tensor
product on `D(𝒪_{X ×_S Y})` that the reflection step of [Stacks, Tag 0FZ9] consumes, and
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/FibreTensorInstance.lean` builds all of it
except the field `stalk`, the derived form of [Stacks, Tag 01CB]:

`(E ⊗^𝐋_{𝒪_{X ×_S Y}} F)_z ≅ E_z ⊗^𝐋_{𝒪_{X ×_S Y, z}} F_z`.

This file supplies that field, so that the bundle is **unconditional** for a fibre product of
schemes.

## Main definitions

* `AlgebraicGeometry.derivedStalkFibreTensorIso` — the derived form of [Stacks, Tag 01CB] at the
  spellings `AlgebraicGeometry.fourierMukaiTensor` and `AlgebraicGeometry.fibreRingTensor` that
  `AlgebraicGeometry.FibreTensorComparisons` is stated in.
* `AlgebraicGeometry.fibreTensorComparisonsOfPullback` — the bundle itself, with no datum
  carried.

## Implementation notes

*Why there is anything to do.* The derived comparison with the stalk functor is in the library
twice, and neither copy is at the spelling the bundle asks for.
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoGeneral` is the right statement —
both tensor factors arbitrary, the ringed-site derived tensor product of [Stacks, Tag 06YU]
upstairs and the canonical derived tensor product of [Stacks, Tag 0BYI] downstairs — but it is
stated over the `RingCat`-valued stalk
`TopCat.Presheaf.stalk (C := RingCat) (Stacks.SheafOfModules.Tensor.ringSheaf R).obj z` of the
sheaf of rings, whereas `AlgebraicGeometry.FibreTensorComparisons.ringTensor` is a derived tensor
product over the local ring `𝒪_{X ×_S Y, z}`, which is the `CommRingCat`-valued stalk. The two
differ by `AlgebraicGeometry.ringCatStalkRingEquiv`.

Three statements cross that ring isomorphism:

* `AlgebraicGeometry.derivedStalkSpellingFunctorIsoAnyModel` factors the derived stalk functor
  over the local ring as the derived stalk functor over the `RingCat`-valued stalk followed by
  restriction of scalars along `ringCatStalkRingEquiv`;
* `CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorObjIso` carries the derived tensor
  product across restriction of scalars along a ring isomorphism;
* `CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso` identifies the K-flat descent
  of [Stacks, Tag 06YU] over a ring, which the previous item is phrased in, with the canonical
  derived tensor product of [Stacks, Tag 0BYI], which the bundle is phrased in.

*The braiding.*  `AlgebraicGeometry.fourierMukaiTensor f g E` is `- ⊗^𝐋 E`, so
`(fourierMukaiTensor f g E).obj F` is `F ⊗^𝐋 E` with `F` in the first slot, while the bundle's
field asks for `E_z ⊗^𝐋 F_z` with `E` first.  One commutativity isomorphism is therefore needed,
and it is taken downstairs, over the stalk ring, where
`CochainComplex.DerivedTensor.derivedTensorProductCommIso` provides it for the canonical derived
tensor product.

*No naturality is claimed.*  The field is a family of isomorphisms quantified over the point and
over both arguments, with no coherence condition, which is exactly what the chain below produces;
every link is in fact natural, but that is not recorded.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- The canonical derived tensor product of [Stacks, Tag 0BYI] on the derived category of
modules over the local ring of a scheme at a point. -/
abbrev localRingDerivedTensor (W : Scheme.{u}) (z : ↥W) :
    CochainComplex.DerivedTensor.DerivedTensorProduct (W.presheaf.stalk z) :=
  CochainComplex.DerivedTensor.canonicalDerivedTensorProduct _

/-- **The derived form of [Stacks, Tag 01CB] over the local ring of a scheme**: the derived
stalk at `z` of `E ⊗^𝐋_{𝒪_W} F` is `E_z ⊗^𝐋_{𝒪_{W,z}} F_z`, for arbitrary objects of
`D(𝒪_W)`.

This is `Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoGeneral` transported
from the `RingCat`-valued stalk of the sheaf of rings to the local ring along
`AlgebraicGeometry.ringCatStalkRingEquiv`. -/
def derivedStalkTensorIso (W : Scheme.{u}) (z : ↥W)
    (E F : DerivedCategory W.Modules) :
    (derivedStalkFunctor z).obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.sheaf).tensor.obj
          E).obj F) ≅
      ((localRingDerivedTensor W z).tensor.obj ((derivedStalkFunctor z).obj E)).obj
        ((derivedStalkFunctor z).obj F) :=
  let _stalkCommRing := StacksDraft.StalkTensor.commRing_stalk_ringSheaf W.sheaf z
  let sp := AlgebraicGeometry.derivedStalkSpellingFunctorIsoAnyModel z
  let e := AlgebraicGeometry.ringCatStalkRingEquiv z
  sp.app _ ≪≫
    (ModuleCat.restrictScalars e.symm.toRingHom).mapDerivedCategory.mapIso
      ((Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIsoGeneral
          W.sheaf z E F).symm ≪≫
        (((CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso _).app _).app _).symm) ≪≫
    CochainComplex.KFlatBifunctor.restrictScalarsDerivedTensorObjIso e.symm _ _ ≪≫
    ((CochainComplex.DerivedTensor.derivedBifunctorCanonicalTensorIso _).app _).app _ ≪≫
    ((localRingDerivedTensor W z).tensor.mapIso (sp.app E).symm).app _ ≪≫
    ((localRingDerivedTensor W z).tensor.obj _).mapIso (sp.app F).symm

/-- **The stalk of the degree-zero cohomology of the derived tensor product of two modules
placed in degree zero is the ordinary tensor product of the stalks**:

`H⁰(ℳ[0] ⊗^𝐋_{𝒪_W} 𝒩[0])_z ≅ ℳ_z ⊗_{𝒪_{W,z}} 𝒩_z`.

The derived form of [Stacks, Tag 01CB] takes the stalk inside the derived tensor product, and
the degree-zero cohomology of a derived tensor product of two modules in degree zero over a
*ring* is their ordinary tensor product
(`Stacks.DerivedTensor.homologyZeroIsoTensorProduct`). -/
def homologyZeroStalkTensorIso (W : Scheme.{u}) (z : ↥W) (M N : W.Modules) :
    (Stacks.ModuleSkyscraper.modulesStalkFunctor W z).obj
        ((DerivedCategory.homologyFunctor W.Modules 0).obj
          (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct W.sheaf).tensor.obj
                ((DerivedCategory.singleFunctor W.Modules 0).obj M)).obj
            ((DerivedCategory.singleFunctor W.Modules 0).obj N))) ≅
      ModuleCat.of (W.presheaf.stalk z)
        (TensorProduct (W.presheaf.stalk z)
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).obj M)
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).obj N)) :=
  (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapDerivedCategoryHomologyIso 0).app
      _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (W.presheaf.stalk z)) 0).mapIso
      (derivedStalkTensorIso W z _ _ ≪≫
        (((localRingDerivedTensor W z).tensor.mapIso
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapDerivedCategorySingleFunctor
              0).app M)).app _ ≪≫
          ((localRingDerivedTensor W z).tensor.obj _).mapIso
            (((Stacks.ModuleSkyscraper.modulesStalkFunctor W z).mapDerivedCategorySingleFunctor
              0).app N))) ≪≫
    Stacks.DerivedTensor.homologyZeroIsoTensorProduct (W.presheaf.stalk z) _ _

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The derived form of [Stacks, Tag 01CB] on `X ×_S Y`**, at the spellings
`AlgebraicGeometry.fourierMukaiTensor` and `AlgebraicGeometry.fibreRingTensor`: the stalk at `z`
of `F ⊗^𝐋_{𝒪_{X ×_S Y}} E` is `E_z ⊗^𝐋_{𝒪_{X ×_S Y, z}} F_z`.

This is `AlgebraicGeometry.derivedStalkTensorIso` braided: `fourierMukaiTensor f g E` is
`- ⊗^𝐋 E`, so it puts `F` in the first slot upstairs while the field of
`AlgebraicGeometry.FibreTensorComparisons` asks for `E_z` in the first slot downstairs. -/
def derivedStalkFibreTensorIso (z : ↥(Limits.pullback f g))
    (E F : DerivedCategory (Limits.pullback f g).Modules) :
    (derivedStalkFunctor z).obj ((fourierMukaiTensor f g E).obj F) ≅
      ((fibreRingTensor f g z).tensor.obj ((derivedStalkFunctor z).obj E)).obj
        ((derivedStalkFunctor z).obj F) :=
  derivedStalkTensorIso (Limits.pullback f g) z F E ≪≫
    CochainComplex.DerivedTensor.derivedTensorProductCommIso _ _

/-- **The comparisons of [Stacks, Tag 0FZ9] for a fibre product of schemes, with no datum
carried.**  `AlgebraicGeometry.fibreTensorComparisons` reduces the bundle to the derived form of
[Stacks, Tag 01CB], which `AlgebraicGeometry.derivedStalkFibreTensorIso` supplies. -/
def fibreTensorComparisonsOfPullback : FibreTensorComparisons f g :=
  fibreTensorComparisons f g (derivedStalkFibreTensorIso f g)

end AlgebraicGeometry

end

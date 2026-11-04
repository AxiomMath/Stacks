module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSiteDerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitude
public import StacksFrontier.CategoryTheory.Adjunction.CompositeTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality

/-!
# The tensor–Hom adjunction at `Ri_* 𝒪_Z`, as the composite of the two adjunctions of `i`

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces. On `D(𝒪_X)` there are two
adjunctions attached to `i`,

* `Li^* ⊣ i_*`, which is [Stacks, Tag 079W], as
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`, and
* `i_* ⊣ R ℰom(𝒪_Z, -)`, which is [Stacks, Tag 0A76], as
  `ClosedQuotientMorphismOfRingedSpaces.derivedModulePushforwardSheafHomExactSupportAdjunction`,

and composing them gives an adjunction between endofunctors of `D(𝒪_X)`:

`i_* Li^*(-) ⊣ i_* R ℰom(𝒪_Z, -)`.

The right adjoint is the derived internal Hom of the ringed site of opens of `X` out of
`Ri_* 𝒪_Z` by [Stacks, Tag 0A77], and the left adjoint is `(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} -` by the
projection formula of [Stacks, Tag 0B53] at the structure sheaf, which is invertible for a closed
embedding by [Stacks, Tag 0B55]. Transporting the composite along these two identifications gives
the derived tensor–Hom adjunction at `Ri_* 𝒪_Z`,

`(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} - ⊣ RSheafHom(Ri_* 𝒪_Z, -)`.

## Main definitions

* `Stacks.Duality.TensorHomTorAmplitude.tensorPushforwardStructureSheafNatIso`:
  `(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} - ≅ i_* Li^*(-)`, as an isomorphism of functors on `D(𝒪_X)`.
* `Stacks.Duality.TensorHomTorAmplitude.derivedPullbackModulePushforwardAdjunction`:
  [Stacks, Tag 079W] with the pushforward read in the model of [Stacks, Tag 0A76], that is
  `Li^* ⊣ i_*` with `i_*` the functor induced on derived categories by the exact `i_*`.
* `Stacks.Duality.TensorHomTorAmplitude.pullbackPushforwardSheafHomSiteAdjunction`: the
  composite adjunction `i_* Li^*(-) ⊣ RSheafHom(Ri_* 𝒪_Z, -)`.
* `Stacks.Duality.TensorHomTorAmplitude.tensorSheafHomAdjunctionAtPushforwardStructureSheaf`:
  the same adjunction with its left adjoint read as the derived tensor product with
  `Ri_* 𝒪_Z`.

## Main results

* `Stacks.Duality.TensorHomTorAmplitude.isIso_projectionFormulaStructureSheafNatTrans`: the
  projection-formula map of [Stacks, Tag 0B53] at `𝒪_Z` is invertible as a morphism of functors
  in the ambient variable.
* `tensorSheafHomAdjunctionAtPushforwardStructureSheaf_homEquiv`: the hom-bijection of the
  tensor–Hom adjunction above is the hom-bijection of [Stacks, Tag 0A76] followed by that of
  [Stacks, Tag 079W], conjugated by the two identifications.

## Implementation notes

*Why the projection formula is packaged as a morphism of functors by hand.* The components of
`projectionFormulaStructureSheafNatTrans` are `projectionFormulaMap`, and its naturality is
`projectionFormulaMap_natural_right` verbatim — the target functor is written so that the
naturality square *is* that lemma, with no reassociation. That is not cosmetic: in this context
the ringed-space structure sheaf `S.X.sheaf` has type `TopCat.Sheaf CommRingCat _` where
`AlgebraicGeometry.RingedSite.O` asks for `Sheaf (Opens.grothendieckTopology _) CommRingCat`,
and the two are definitionally but not reducibly equal, so a goal mentioning both
`derivedTensorProductFunctor S.X.sheaf` and
`DerivedCategory (SheafOfModules (structureSheafRing S.X))` is not type-correct at `implicit`
transparency and `rw` with `Category.assoc` fails on it. Every proof below is therefore a term or
a single `exact`, and the pasting law is
`CategoryTheory.Adjunction.homEquiv_ofNatIsoLeft_ofNatIsoRight_comp`, proved in a bare
category-theoretic context.

*The two models of pushforward.* The projection formula is stated for the total right derived
functor `Ri_*` and [Stacks, Tag 0A76] for the functor induced by the exact `i_*`; the comparison
is [Stacks, Tag 0E2K], `derivedPushforwardComparison`, and the transports below pass through it
once on the tensor factor and once on the ambient functor.

## References

* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.DerivedTensor.RingedSite
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.TensorHomTorAmplitude

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-! ### `Ri_* Li^*` is the derived tensor product with `Ri_* 𝒪_Z` -/

/-- The structure sheaf of `Z` in degree zero, at the ringed site of opens of `Z`. -/
abbrev derivedStructureSheafZ :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)

/-- **[Stacks, Tag 0FPT], the unit constraint on the left on `Z`, as an isomorphism of
functors**: `𝒪_Z[0] ⊗^𝐋_{𝒪_Z} - ≅ 𝟭 D(𝒪_Z)`. This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitNatIso` for the canonical derived
tensor product of [Stacks, Tag 06YU], read at the ringed site of opens of `Z`. -/
abbrev structureSheafLeftUnitNatIso :
    (derivedTensorProductFunctor S.Z.sheaf).obj (derivedStructureSheafZ S) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z))) :=
  DerivedTensorProduct.leftUnitNatIso (Stacks.RingedSpace.toRingedSite S.Z)
    (canonicalDerivedTensorProduct S.Z.sheaf)

/-- **The projection-formula map of [Stacks, Tag 0B53] at the structure sheaf of `Z`, as a
morphism of functors in the ambient variable**:

`(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} - ⟶ Ri_*(𝒪_Z ⊗^𝐋_{𝒪_Z} Li^*(-))`.

Its components are `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap` and its
naturality is `projectionFormulaMap_natural_right`. -/
def projectionFormulaStructureSheafNatTrans :
    (derivedTensorProductFunctor S.X.sheaf).obj
        ((derivedPushforward S.i).obj (derivedStructureSheafZ S)) ⟶
      derivedPullback S.i ⋙
        (derivedTensorProductFunctor S.Z.sheaf).obj (derivedStructureSheafZ S) ⋙
          derivedPushforward S.i where
  app K := projectionFormulaMap S.i (derivedStructureSheafZ S) K
  naturality _ _ k := projectionFormulaMap_natural_right S.i _ k

/-- **[Stacks, Tag 0B55] at the structure sheaf of `Z`, as invertibility of a morphism of
functors.** The projection-formula map at `𝒪_Z` is invertible in every ambient variable, by
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding` at
the closed embedding `ClosedQuotientMorphismOfRingedSpaces.isClosedEmbedding`, hence invertible
as a morphism of functors. No boundedness, flatness or quasi-coherence hypothesis enters. -/
theorem isIso_projectionFormulaStructureSheafNatTrans :
    IsIso (projectionFormulaStructureSheafNatTrans S) := by
  have : ∀ K, IsIso ((projectionFormulaStructureSheafNatTrans S).app K) := fun K =>
    isIso_projectionFormulaMap_of_isClosedEmbedding S.i S.isClosedEmbedding
      (derivedStructureSheafZ S) K
  exact NatIso.isIso_of_isIso_app _

/-- **The derived pushforward of the derived pullback is the derived tensor product with
`Ri_* 𝒪_Z`**: `(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} - ≅ Ri_* Li^*(-)`, with `Ri_*` the total right derived
pushforward.

It is the projection-formula isomorphism of [Stacks, Tag 0B55] at `𝒪_Z`, followed by cancelling
the unit constraint of [Stacks, Tag 0FPT] inside `Ri_*`. -/
def derivedPushforwardPullbackTensorNatIso :
    (derivedTensorProductFunctor S.X.sheaf).obj
        ((derivedPushforward S.i).obj (derivedStructureSheafZ S)) ≅
      derivedPullback S.i ⋙ derivedPushforward S.i :=
  haveI := isIso_projectionFormulaStructureSheafNatTrans S
  asIso (projectionFormulaStructureSheafNatTrans S) ≪≫
    Functor.isoWhiskerLeft (derivedPullback S.i)
      (Functor.isoWhiskerRight (structureSheafLeftUnitNatIso S) (derivedPushforward S.i) ≪≫
        Functor.leftUnitor (derivedPushforward S.i))

/-- The isomorphism `derivedPushforwardPullbackTensorNatIso` is the projection-formula morphism
of [Stacks, Tag 0B53] followed by the left unit constraint inside `Ri_*`. -/
theorem derivedPushforwardPullbackTensorNatIso_hom :
    (derivedPushforwardPullbackTensorNatIso S).hom =
      projectionFormulaStructureSheafNatTrans S ≫
        Functor.whiskerLeft (derivedPullback S.i)
          (Functor.whiskerRight (structureSheafLeftUnitNatIso S).hom (derivedPushforward S.i) ≫
            (Functor.leftUnitor (derivedPushforward S.i)).hom) :=
  rfl

/-- `Ri_* 𝒪_Z`, with the pushforward in the model of [Stacks, Tag 0A76]: the functor induced on
derived categories by the exact functor `i_*`. -/
abbrev pushforwardDerivedStructureSheaf :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  (modulePushforward S.i).mapDerivedCategory.obj (derivedStructureSheafZ S)

/-- **`i_* Li^*` is the derived tensor product with `Ri_* 𝒪_Z`**, with both pushforwards read in
the model of [Stacks, Tag 0A76]: `(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} - ≅ i_* Li^*(-)`. This is
`derivedPushforwardPullbackTensorNatIso` conjugated by the comparison of the two models of
pushforward, [Stacks, Tag 0E2K]. -/
def tensorPushforwardStructureSheafNatIso :
    (derivedTensorProductFunctor S.X.sheaf).obj (pushforwardDerivedStructureSheaf S) ≅
      derivedPullback S.i ⋙ (modulePushforward S.i).mapDerivedCategory :=
  (derivedTensorProductFunctor S.X.sheaf).mapIso
      (S.derivedPushforwardComparison.app (derivedStructureSheafZ S)) ≪≫
    derivedPushforwardPullbackTensorNatIso S ≪≫
      Functor.isoWhiskerLeft (derivedPullback S.i) S.derivedPushforwardComparison.symm

/-! ### The composite adjunction -/

/-- **[Stacks, Tag 079W] with the pushforward in the model of [Stacks, Tag 0A76]**:
`Li^* ⊣ i_*`, where `i_*` is the functor induced on derived categories by the exact functor
`i_*` rather than the total right derived functor. This is
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction`, which is unconditional,
transported along [Stacks, Tag 0E2K]. -/
def derivedPullbackModulePushforwardAdjunction :
    derivedPullback S.i ⊣ (modulePushforward S.i).mapDerivedCategory :=
  Adjunction.ofNatIsoRight (derivedAdjunction S.i) S.derivedPushforwardComparison.symm

/-- **The composite of the two adjunctions of `i`**, with the right adjoint identified by
[Stacks, Tag 0A77]:

`i_* Li^*(-) ⊣ RSheafHom(Ri_* 𝒪_Z, -)`.

The composite of `Li^* ⊣ i_*` and `i_* ⊣ R ℰom(𝒪_Z, -)` has right adjoint
`R ℰom(𝒪_Z, -)` followed by `i_*`, which is the left-hand side of [Stacks, Tag 0A77] in the
form `ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportPushforwardNatIso`. -/
def pullbackPushforwardSheafHomSiteAdjunction :
    derivedPullback S.i ⋙ (modulePushforward S.i).mapDerivedCategory ⊣
      (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op (pushforwardDerivedStructureSheaf S)) :=
  Adjunction.ofNatIsoRight
    ((derivedPullbackModulePushforwardAdjunction S).comp
      S.derivedModulePushforwardSheafHomExactSupportAdjunction)
    S.derivedSheafHomExactSupportPushforwardNatIso

/-- **The derived tensor–Hom adjunction at `Ri_* 𝒪_Z` on `D(𝒪_X)`**:

`(Ri_* 𝒪_Z) ⊗^𝐋_{𝒪_X} - ⊣ RSheafHom(Ri_* 𝒪_Z, -)`.

This is `pullbackPushforwardSheafHomSiteAdjunction` with its left adjoint read through
`tensorPushforwardStructureSheafNatIso`. The tensor product is the one of [Stacks, Tag 06YU] at
the ringed site of opens of `X` and the internal Hom is the derived internal Hom bifunctor of that
site. -/
def tensorSheafHomAdjunctionAtPushforwardStructureSheaf :
    (derivedTensorProductFunctor S.X.sheaf).obj (pushforwardDerivedStructureSheaf S) ⊣
      (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op (pushforwardDerivedStructureSheaf S)) :=
  Adjunction.ofNatIsoLeft (pullbackPushforwardSheafHomSiteAdjunction S)
    (tensorPushforwardStructureSheafNatIso S).symm

/-- **The pasting law for the tensor–Hom adjunction at `Ri_* 𝒪_Z`.** Its hom-bijection is the
hom-bijection of [Stacks, Tag 0A76] followed by that of [Stacks, Tag 079W], conjugated by the
identification of the left adjoint with the derived tensor product and by [Stacks, Tag 0A77]. -/
theorem tensorSheafHomAdjunctionAtPushforwardStructureSheaf_homEquiv
    (A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (f : ((derivedTensorProductFunctor S.X.sheaf).obj
      (pushforwardDerivedStructureSheaf S)).obj A ⟶ B) :
    (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).homEquiv A B f =
      (derivedPullbackModulePushforwardAdjunction S).homEquiv _ _
          (S.derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _
            ((tensorPushforwardStructureSheafNatIso S).inv.app A ≫ f)) ≫
        S.derivedSheafHomExactSupportPushforwardNatIso.hom.app B :=
  Adjunction.homEquiv_ofNatIsoLeft_ofNatIsoRight_comp
    (derivedPullbackModulePushforwardAdjunction S)
    S.derivedModulePushforwardSheafHomExactSupportAdjunction
    (tensorPushforwardStructureSheafNatIso S).symm
    S.derivedSheafHomExactSupportPushforwardNatIso A B f

end Stacks.Duality.TensorHomTorAmplitude

end

module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfect
public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPerfectTensorFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalPseudoCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# Moving a derived tensor factor inside a derived internal Hom on an algebraic space

Let `X` be an algebraic space over a scheme `S` and let `K`, `L`, `M` be objects of `D(𝒪_X)`.
**Stacks 0E4Q** asserts that the canonical morphism of Stacks 0BYU

`K ⊗^L_{𝒪_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{𝒪_X} L)`

is an isomorphism when (1) `M` is perfect, (2) `K` is perfect, or (3) `M` is pseudo-coherent,
`L` is cohomologically bounded below and `K` has finite Tor dimension.

All three cases are proved here with no hypothesis on the remaining objects beyond the ones
the source states, by specialising the ringed-site statements of Stacks 0ATN.

## Main definitions

* `AlgebraicGeometry.RingedSite.PseudoCoherentTensorHomDiagonal`: the content of Stacks 0ATN
  part (3) at a ringed site, as a property of that site.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedTensorHomDiagonal_of_isPerfect`: **Stacks 0E4Q case
  (1)**, the internal-Hom source perfect.
* `AlgebraicGeometry.Space.isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor`:
  **Stacks 0E4Q case (2)**, the tensor factor perfect.
* `AlgebraicGeometry.Space.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent`: **Stacks 0E4Q
  case (3)**, the internal-Hom source pseudo-coherent, its target cohomologically bounded below
  and the tensor factor of finite Tor dimension.

## Implementation notes

The statements are made on `AlgebraicGeometry.Space.smallEtaleModelRingedSite`, the
equi-universe model of the small étale ringed site of `X`, and not on
`AlgebraicGeometry.Space.smallEtaleRingedSite` itself. The reason is that the morphism of
Stacks 0BYU, hence the statement of Stacks 0E4Q, does not exist at the universes of the small
étale site: it is built from `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, which is
pinned to a ringed site whose objects, morphisms and sections lie in one universe — the
internal Hom complex of Stacks 0A8Z raises the module universe of a site with objects in
`Type (u + 1)`, so an iterated internal Hom forces the three site universes together, as the
implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom` record — whereas
the small étale ringed site of an algebraic space is an
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`. The model is the device the development already
uses for exactly this gap, its `𝒪_X`-modules being those of `X` by
`AlgebraicGeometry.Space.modulesEquivModelModules`, and this is the pattern of
`AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_isFinitePresentation_model`.

The three objects range over all of `D(𝒪_X)` rather than over `D_QCoh(𝒪_X)`: none of the three
cases uses quasi-coherence, so the objects of
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` named by the source are covered by the
statements below through the inclusion of that full subcategory.

The instances in the variable block are setup and not hypotheses: sheafification on the model
site and on its slices, and additivity and totalisability of the tensor product of sheaves of
modules, are what it takes for the derived tensor product, the derived internal Hom and the
restrictions to slices appearing in perfection and pseudo-coherence to exist at all. This is
the variable block in which Stacks 0ATN is stated, read at the model site.

## References

* [Stacks Project, Lemma 75.13.11 (Tag 0E4Q)](https://stacks.math.columbia.edu/tag/0E4Q)
* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 21.35.7 (Tag 0BYU)](https://stacks.math.columbia.edu/tag/0BYU)
* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Definition 20.47.1 (Tag 08FT)](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Definition 20.48.2 (Tag 08FZ)](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **Stacks 0ATN part (3) as a property of a ringed site.** The diagonal of Stacks 0BYS

`K ⊗^L_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_O L)`

is an isomorphism whenever `M` is pseudo-coherent, `L` is cohomologically bounded below and
`K` has finite Tor dimension for the canonical derived tensor product. -/
def PseudoCoherentTensorHomDiagonal : Prop :=
  ∀ K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
    X.IsPseudoCoherent M → DerivedCategoryB.IsBoundedBelow L →
      Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) K →
        IsIso (derivedTensorHomDiagonal X K L M)

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] RingedSite.ringSheafSectionsCommRing
  RingedSite.presheafOfModulesMonoidalCategory
  RingedSite.curriedTensorPreservesZeroMorphisms
  RingedSite.curriedTensorObjPreservesZeroMorphisms

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  [HasSheafify (smallEtaleModelRingedSite B S hS F hF).J AddCommGrpCat.{u}]
  [(smallEtaleModelRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
    HasSheafify ((smallEtaleModelRingedSite B S hS F hF).J.over V) AddCommGrpCat.{u}]
  [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
    ((smallEtaleModelRingedSite B S hS F hF).J.over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
    ((smallEtaleModelRingedSite B S hS F hF).J.over V).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
    ((smallEtaleModelRingedSite B S hS F hF).J.over V).HasSheafCompose
      (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} (smallEtaleModelRingedSite B S hS F hF).O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} (smallEtaleModelRingedSite B S hS F hF).O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
        (smallEtaleModelRingedSite B S hS F hF).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (sheafTensor (smallEtaleModelRingedSite B S hS F hF).O) (ComplexShape.up ℤ)]

omit [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
  ((smallEtaleModelRingedSite B S hS F hF).J.over V).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 0E4Q case (1).** For objects `K`, `L`, `M` of `D(𝒪_X)` on an algebraic space `X`
with `M` perfect, the canonical morphism of Stacks 0BYU

`K ⊗^L_{𝒪_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{𝒪_X} L)`

is an isomorphism. Nothing is assumed of `K` or `L`; in particular quasi-coherence of the
cohomology sheaves is not used. -/
@[stacks 0E4Q "case (1): M perfect"]
theorem isIso_derivedTensorHomDiagonal_of_isPerfect
    (K L M : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)))
    (hM : (smallEtaleModelRingedSite B S hS F hF).IsPerfect M) :
    IsIso (RingedSite.derivedTensorHomDiagonal
      (smallEtaleModelRingedSite B S hS F hF) K L M) :=
  RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect
    (smallEtaleModelRingedSite B S hS F hF) K L M hM

omit [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
  ((smallEtaleModelRingedSite B S hS F hF).J.over V).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 0E4Q case (2).** For objects `K`, `L`, `M` of `D(𝒪_X)` on an algebraic space `X`
with the tensor factor `K` perfect, the canonical morphism of Stacks 0BYU

`K ⊗^L_{𝒪_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{𝒪_X} L)`

is an isomorphism. Nothing is assumed of `L` or `M`; neither side need have quasi-coherent
cohomology. -/
@[stacks 0E4Q "case (2): K perfect"]
theorem isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor
    (K L M : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)))
    (hK : (smallEtaleModelRingedSite B S hS F hF).IsPerfect K) :
    IsIso (RingedSite.derivedTensorHomDiagonal
      (smallEtaleModelRingedSite B S hS F hF) K L M) :=
  RingedSite.isIso_derivedTensorHomDiagonal_of_isPerfect_tensorFactor
    (smallEtaleModelRingedSite B S hS F hF) K L M hK

omit [∀ V : (smallEtaleModelRingedSite B S hS F hF).C,
  ((smallEtaleModelRingedSite B S hS F hF).J.over V).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- **Stacks 0E4Q case (3).** For objects `K`, `L`, `M` of `D(𝒪_X)` on an algebraic space `X`
with `M` pseudo-coherent, `L` cohomologically bounded below and `K` of finite Tor dimension,
the canonical morphism of Stacks 0BYU

`K ⊗^L_{𝒪_X} RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^L_{𝒪_X} L)`

is an isomorphism.

Nothing is assumed beyond the three conditions the source states; in particular
quasi-coherence of the cohomology sheaves is not used. Like the two cases above, this
specialises the corresponding part of Stacks 0ATN for an arbitrary ringed site —
`AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent` — to the
model of the small étale ringed site of `X`. -/
@[stacks 0E4Q "case (3): M pseudo-coherent, L bounded below, K of finite Tor dimension"]
theorem isIso_derivedTensorHomDiagonal_of_isPseudoCoherent
    (K L M : DerivedCategory
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)))
    (hM : (smallEtaleModelRingedSite B S hS F hF).IsPseudoCoherent M)
    (hL : DerivedCategoryB.IsBoundedBelow L)
    (hK : Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS F hF)) K) :
    IsIso (RingedSite.derivedTensorHomDiagonal
      (smallEtaleModelRingedSite B S hS F hF) K L M) :=
  RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent
    (smallEtaleModelRingedSite B S hS F hF) K L M hM hL hK

end AlgebraicGeometry.Space

end

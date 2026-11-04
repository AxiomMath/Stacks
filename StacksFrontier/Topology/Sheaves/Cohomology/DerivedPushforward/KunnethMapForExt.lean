module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# The Künneth formula for Ext

Let `a : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `b : (Y, 𝒪_Y) ⟶ (S, 𝒪_S)` be morphisms of ringed spaces and
let `p : (W, 𝒪_W) ⟶ X`, `q : W ⟶ Y` be morphisms with `p ≫ a = f = q ≫ b`.  For `K ∈ D(𝒪_X)`
and `M ∈ D(𝒪_Y)` the exterior product is

`K ⊠ M = Lp^*K ⊗^L_{𝒪_W} Lq^*M`,

and for `K, K' ∈ D(𝒪_X)` and `M, M' ∈ D(𝒪_Y)` there is a canonical morphism

`Ra_*R SheafHom(K, K') ⊗^L_{𝒪_S} Rb_*R SheafHom(M, M') ⟶ Rf_*(R SheafHom(K ⊠ M, K' ⊠ M'))`,

Equation 36.25.0.1 of the Stacks project.  It is the relative Künneth morphism of Stacks 0FLP
at the two derived internal homs, followed by the pushforward of the comparison of a tensor
product of derived internal homs with the derived internal hom of the exterior products.

The Stacks project takes `W = X ×_S Y` with its two projections; as in Stacks 0FLP the fibre
product is not used, so the two projections and the two factorizations of `f` are taken as
data here, which specializes to the statement of the source.

## Main definitions

* `Stacks.Cohomology.DerivedKunnethExt.sheafHomEval`: the evaluation morphism
  `R SheafHom(A, B) ⊗^L_{𝒪_Z} A ⟶ B`.
* `Stacks.Cohomology.DerivedKunnethExt.middleFour`: the flip of the middle two factors
  `(H ⊗^L G) ⊗^L (A ⊗^L B) ⟶ (H ⊗^L A) ⊗^L (G ⊗^L B)`.
* `Stacks.Cohomology.DerivedKunnethExt.sheafHomTensorMap`: the canonical morphism
  `R SheafHom(A, A') ⊗^L R SheafHom(B, B') ⟶ R SheafHom(A ⊗^L B, A' ⊗^L B')` of Stacks 0FXP.
* `Stacks.Cohomology.DerivedKunnethExt.pullbackSheafHomMap`: the canonical morphism
  `Lh^*R SheafHom(A, B) ⟶ R SheafHom(Lh^*A, Lh^*B)` of Stacks 08I3.
* `Stacks.Cohomology.DerivedKunnethExt.boxProd`: the exterior product `K ⊠ M`.
* `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`: the comparison
  `Lp^*R SheafHom(K, K') ⊗^L Lq^*R SheafHom(M, M') ⟶ R SheafHom(K ⊠ M, K' ⊠ M')`.
* `Stacks.Cohomology.DerivedKunnethExt.kunnethExtMap`: the Künneth morphism for Ext.

## Main results

* `Stacks.Cohomology.DerivedKunnethExt.kunnethExtMap_eq`: the Künneth morphism for Ext is the
  relative Künneth morphism of Stacks 0FLP at the two derived internal homs, followed by the
  pushforward of `Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`.

## Implementation notes

*Two derived tensor products meet here.*  The derived internal hom and its tensor–internal-hom
bijection of Stacks 08DI are stated over
`Stacks.SheafOfModules.derivedTensorProductFunctor`, while the relative Künneth morphism, the
derived pullback–tensor comparison of Stacks 079U and the symmetric monoidal structure on
`D(𝒪_Z)` are stated over `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`.  Every
statement below uses the latter, and `Stacks.Cohomology.DerivedKunnethExt.tensorBridge` is the
comparison of the two, which is where each use of the bijection of Stacks 08DI passes between
them.

*The flip of the middle two factors* that Stacks 0FXP calls for is
`Stacks.Cohomology.DerivedKunnethExt.middleFour`, built from the associator and the braiding
of `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal`, whose tensor product
*is* the derived tensor product of Stacks 06YU, so no transport appears in it.

*Module categories are spelled* `Stacks.SheafOfModules.DerivedMonoidal.Mod Z.sheaf` throughout,
and `Stacks.Cohomology.DerivedKunnethExt.derivedPullbackFunctor` and
`derivedPushforwardFunctor` are the derived pullback and pushforward re-typed to that spelling,
equal to the originals by `rfl`.  The alternative spelling
`SheafOfModules (structureSheafRing Z)` is equal to it by `rfl` as well, but
only through a non-reducible definition, and both the monoidal structure and the additive
structure on the morphism groups are found by instance search, which does not unfold one.

## References

* [Stacks Project, Tag 0FXY](https://stacks.math.columbia.edu/tag/0FXY)
* [Stacks Project, Tag 0FXP](https://stacks.math.columbia.edu/tag/0FXP)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.DerivedKunnethExt

attribute [local instance] HasDerivedCategory.standard

-- The objects below live over `Mod Z.sheaf = SheafOfModules (Tensor.ringSheaf Z.sheaf)`, which
-- pairs `Z.sheaf.obj ⋙ forget₂ CommRingCat RingCat` with the sheaf condition directly, while the
-- bijection of Stacks 08DI is stated over
-- `StructureSheafModules Z.sheaf = SheafOfModules (structureSheaf Z.sheaf)`, i.e. over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Z.sheaf`. The two sheaves of rings are the
-- same sheaf, but seeing it needs `CategoryTheory.sheafCompose` unfolded, which instance search
-- does not do at reducible transparency: without this attribute the morphism groups of the
-- bijection have no `Add` instance at the spelling the objects here are written in, so
-- `Stacks.Cohomology.DerivedKunnethExt.sheafHomTensorMap` cannot invert it. Same attribute, on
-- the same declaration, for the same reason as in
-- `StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom`, which states the
-- bijection.
attribute [local implicit_reducible] CategoryTheory.sheafCompose

/-! ### Derived tensor product and derived internal hom on one ringed space -/

section OneSpace

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `A ⊗^L_{𝒪_Z} B`, the derived tensor product of Stacks 06YU. -/
abbrev tensorObj (A B : DerivedCategory (Mod Z.sheaf)) : DerivedCategory (Mod Z.sheaf) :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj A).obj B

/-- `R SheafHom_{𝒪_Z}(A, B)`, the derived internal hom of Stacks 08DI. -/
abbrev sheafHomObj (A B : DerivedCategory (Mod Z.sheaf)) : DerivedCategory (Mod Z.sheaf) :=
  ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op A)).obj B

/-- The comparison of the derived tensor product the derived internal hom of Stacks 08DI is
stated over with the derived tensor product of Stacks 06YU. -/
abbrev tensorBridge :
    Stacks.SheafOfModules.derivedTensorProductFunctor (Stacks.SheafOfModules.ringedSite Z.sheaf) ≅
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf :=
  interfaceTensorCanonicalIso (Stacks.SheafOfModules.ringedSite Z.sheaf)

/-- The map `A ⊗^L_{𝒪_Z} B ⟶ A' ⊗^L_{𝒪_Z} B'` induced by `x : A ⟶ A'` and `y : B ⟶ B'`. -/
def tensorMap {A A' B B' : DerivedCategory (Mod Z.sheaf)} (x : A ⟶ A') (y : B ⟶ B') :
    tensorObj Z A B ⟶ tensorObj Z A' B' :=
  ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).map x).app B ≫
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj A').map y

/-- **The evaluation morphism** `R SheafHom(A, B) ⊗^L_{𝒪_Z} A ⟶ B`: the morphism corresponding
to the identity of `R SheafHom(A, B)` under the tensor–internal-hom bijection of Stacks 08DI. -/
def sheafHomEval (A B : DerivedCategory (Mod Z.sheaf)) :
    tensorObj Z (sheafHomObj Z A B) A ⟶ B :=
  ((tensorBridge Z).inv.app (sheafHomObj Z A B)).app A ≫
    AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf)
      (sheafHomObj Z A B) A B (𝟙 _)

/-- The flip of the middle two factors `(H ⊗^L G) ⊗^L (A ⊗^L B) ⟶ (H ⊗^L A) ⊗^L (G ⊗^L B)`,
given by the associator and the braiding of the symmetric monoidal structure on `D(𝒪_Z)` whose
tensor product is the derived tensor product. -/
def middleFour (H G A B : DerivedCategory (Mod Z.sheaf)) :
    tensorObj Z (tensorObj Z H G) (tensorObj Z A B) ⟶
      tensorObj Z (tensorObj Z H A) (tensorObj Z G B) :=
  letI := canonicalDerivedMonoidal Z.sheaf
  letI := canonicalDerivedSymmetric Z.sheaf
  (α_ H G (A ⊗ B)).hom ≫ (H ◁ (α_ G A B).inv) ≫ (H ◁ ((β_ G A).hom ▷ B)) ≫
    (H ◁ (α_ A G B).hom) ≫ (α_ H A (G ⊗ B)).inv

/-- **Stacks 0FXP.** For `A, A', B, B'` in `D(𝒪_Z)` there is a canonical morphism

`R SheafHom(A, A') ⊗^L_{𝒪_Z} R SheafHom(B, B') ⟶ R SheafHom(A ⊗^L_{𝒪_Z} B, A' ⊗^L_{𝒪_Z} B')`,

adjoint under the bijection of Stacks 08DI to the flip of the middle two factors followed by
the tensor product of the two evaluation morphisms. -/
def sheafHomTensorMap (A A' B B' : DerivedCategory (Mod Z.sheaf)) :
    tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B') ⟶
      sheafHomObj Z (tensorObj Z A B) (tensorObj Z A' B') :=
  (AlgebraicGeometry.RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf)
      (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B'))
      (tensorObj Z A B) (tensorObj Z A' B')).toEquiv.symm
    (((tensorBridge Z).hom.app (tensorObj Z (sheafHomObj Z A A') (sheafHomObj Z B B'))).app
        (tensorObj Z A B) ≫
      middleFour Z (sheafHomObj Z A A') (sheafHomObj Z B B') A B ≫
      tensorMap Z (sheafHomEval Z A A') (sheafHomEval Z B B'))

end OneSpace

/-! ### Pulling back a derived internal hom -/

section Pullback

variable {Z W : RingedSpace.{u, u}} (h : W ⟶ Z)
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `Lh^*`, the derived pullback of Stacks 06YJ. -/
def derivedPullbackFunctor : DerivedCategory (Mod Z.sheaf) ⥤ DerivedCategory (Mod W.sheaf) :=
  derivedPullback h

/-- `Rh_*`, the derived pushforward of Stacks 079W. -/
def derivedPushforwardFunctor : DerivedCategory (Mod W.sheaf) ⥤ DerivedCategory (Mod Z.sheaf) :=
  derivedPushforward h

/-- The derived pullback is the derived pullback of Stacks 06YJ. -/
theorem derivedPullbackFunctor_eq : derivedPullbackFunctor h = derivedPullback h := rfl

/-- The derived pushforward is the derived pushforward of Stacks 079W. -/
theorem derivedPushforwardFunctor_eq : derivedPushforwardFunctor h = derivedPushforward h := rfl

/-- The canonical morphism `Lh^*R SheafHom(A, B) ⟶ R SheafHom(Lh^*A, Lh^*B)` of Stacks 08I3, at
the module-category spelling this file works in.  It is
`Stacks.Cohomology.DerivedInternalHomPullback.derivedPullbackSheafHomMap`, which carries the
characterization and the invertibility theory; the tag is registered there. -/
def pullbackSheafHomMap (A B : DerivedCategory (Mod Z.sheaf)) :
    (derivedPullbackFunctor h).obj (sheafHomObj Z A B) ⟶
      sheafHomObj W ((derivedPullbackFunctor h).obj A) ((derivedPullbackFunctor h).obj B) :=
  DerivedInternalHomPullback.derivedPullbackSheafHomMap h A B

end Pullback

/-! ### The Künneth morphism for Ext -/

section Kunneth

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)
  [HasSheafify (Opens.grothendieckTopology S.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The exterior product `K ⊠ M = Lp^*K ⊗^L_{𝒪_W} Lq^*M` of `K ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)`. -/
abbrev boxProd (K : DerivedCategory (Mod X.sheaf)) (M : DerivedCategory (Mod Y.sheaf)) :
    DerivedCategory (Mod W.sheaf) :=
  tensorObj W ((derivedPullbackFunctor p).obj K) ((derivedPullbackFunctor q).obj M)

/-- The comparison
`Lp^*R SheafHom(K, K') ⊗^L_{𝒪_W} Lq^*R SheafHom(M, M') ⟶ R SheafHom(K ⊠ M, K' ⊠ M')`: the
tensor product of the two pullback comparisons of Stacks 08I3, followed by the morphism of
Stacks 0FXP on `W`. -/
def boxSheafHomMap (K K' : DerivedCategory (Mod X.sheaf))
    (M M' : DerivedCategory (Mod Y.sheaf)) :
    tensorObj W ((derivedPullbackFunctor p).obj (sheafHomObj X K K'))
        ((derivedPullbackFunctor q).obj (sheafHomObj Y M M')) ⟶
      sheafHomObj W (boxProd p q K M) (boxProd p q K' M') :=
  tensorMap W (pullbackSheafHomMap p K K') (pullbackSheafHomMap q M M') ≫
    sheafHomTensorMap W ((derivedPullbackFunctor p).obj K) ((derivedPullbackFunctor p).obj K')
      ((derivedPullbackFunctor q).obj M) ((derivedPullbackFunctor q).obj M')

/-- **The Künneth morphism for Ext**
`Ra_*R SheafHom(K, K') ⊗^L_{𝒪_S} Rb_*R SheafHom(M, M') ⟶ Rf_*(R SheafHom(K ⊠ M, K' ⊠ M'))`,
Equation 36.25.0.1: the relative Künneth morphism of Stacks 0FLP at the two derived internal
homs, followed by the pushforward of
`Stacks.Cohomology.DerivedKunnethExt.boxSheafHomMap`.  It is defined for arbitrary
`K, K' ∈ D(𝒪_X)` and `M, M' ∈ D(𝒪_Y)`. -/
@[stacks 0FXY]
def kunnethExtMap (K K' : DerivedCategory (Mod X.sheaf))
    (M M' : DerivedCategory (Mod Y.sheaf)) :
    tensorObj S ((derivedPushforwardFunctor a).obj (sheafHomObj X K K'))
        ((derivedPushforwardFunctor b).obj (sheafHomObj Y M M')) ⟶
      (derivedPushforwardFunctor f).obj
        (sheafHomObj W (boxProd p q K M) (boxProd p q K' M')) :=
  Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
      (sheafHomObj X K K') (sheafHomObj Y M M') ≫
    (derivedPushforwardFunctor f).map (boxSheafHomMap p q K K' M M')

/-- The Künneth morphism for Ext is the relative Künneth morphism of Stacks 0FLP at the two
derived internal homs, followed by the pushforward of the comparison of a tensor product of
derived internal homs with the derived internal hom of the exterior products. -/
theorem kunnethExtMap_eq (K K' : DerivedCategory (Mod X.sheaf))
    (M M' : DerivedCategory (Mod Y.sheaf)) :
    kunnethExtMap a b p q f hp hq K K' M M' =
      Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq
          (sheafHomObj X K K') (sheafHomObj Y M M') ≫
        (derivedPushforwardFunctor f).map (boxSheafHomMap p q K K' M M') :=
  rfl

end Kunneth

end Stacks.Cohomology.DerivedKunnethExt

end

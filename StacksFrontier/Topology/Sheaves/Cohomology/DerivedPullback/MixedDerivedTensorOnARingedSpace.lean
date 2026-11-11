module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.DerivedMixedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.LinearMixedDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.LinearDerivedMixedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.TopoiBridge.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# The mixed derived tensor product on a ringed space

Let `f : (X, O_X) ⟶ (Y, O_Y)` be a morphism of ringed spaces.  **Stacks 08DE** asserts a
canonical bifunctorial isomorphism

`F ⊗^L_{O_X} Lf^*G ≅ F ⊗^L_{f⁻¹O_Y} f⁻¹G`

for `F` in `D(O_X)` and `G` in `D(O_Y)`.  A ringed space is a ringed topos — the site of its
opens with its structure sheaf — and a morphism of ringed spaces is a morphism of ringed topoi
presented by the continuous functor `V ↦ f⁻¹V`, so the tag is the ringed-topos statement
**Stacks 08I6** read at that presentation.  This file supplies the presentation and reads the
statement at it.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.ringedToposSiteHom`: the morphism of
  ringed topoi presented by a morphism of ringed spaces, in the
  `AlgebraicGeometry.RingedToposSiteHom` form that the ringed-topos derived pullback consumes.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceDerivedTensorPullback`: the
  left-hand bifunctor `(F, G) ↦ (F ⊗^L_{O_X} Lf^*G)|_{f⁻¹O_Y}` of the tag, written with the
  *ringed-space* derived pullback `Lf^*` of Tag 06YJ.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.derivedMixedTensorIso`: the comparison of
  Stacks 08DE after restriction of scalars along `f⁻¹O_Y ⟶ O_X`.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceLinearDerivedTensorPullback`: the
  left-hand bifunctor `(F, G) ↦ F ⊗^L_{O_X} Lf^*G` of the tag, read in `D(O_X)`.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceLinearDerivedMixedTensor`: the
  bifunctor `(F, G) ↦ F ⊗^L_{O_X} Lh^*(f⁻¹G)` into `D(O_X)`, where `h` is extension of scalars
  along `f⁻¹O_Y ⟶ O_X`.  It is not the derived mixed tensor product of the tag.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceDerivedLinearMixedTensorIso`:
  `F ⊗^L_{O_X} Lf^*G ≅ F ⊗^L_{O_X} Lh^*(f⁻¹G)`, the whiskering of Stacks 0G6R.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceDerivedMixedTensorInverseImage`: the
  right-hand bifunctor `(F, G) ↦ F ⊗^L_{f⁻¹O_Y} f⁻¹G`, valued in `D(O_X)`, as the derived
  bifunctor of the sectionwise mixed tensor product
  (`Stacks.Cohomology.MixedDerivedTensor.mixedDerivedTensor`) computed by one-sided K-flat
  resolutions.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.derivedLinearMixedTensorIso`:
  **Stacks 08DE** in `D(O_X)` between `spaceLinearDerivedTensorPullback` and that bifunctor.

## Main results

* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.pullbackTopos_eq` and
  `derivedPullback_eq`: the ringed-space pullback and derived pullback of sheaves of modules
  *are* the ringed-topos ones along `ringedToposSiteHom f`.  Without these the tag would be
  Stacks 08I6 restated at a special topology, asserting nothing about the `Lf^*` that the
  ringed-space development (Tags 06YJ, 079U, 0FP0, 0D5S) uses.
* `Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceDerivedTensorPullback_eq_restrict`:
  the left-hand bifunctor read in `D(f⁻¹O_Y)` is the restriction of scalars of the `O_X`-valued
  one.

## Implementation notes

**Why the identification is `rfl`.**  The two derived pullbacks are independently constructed
left derived functors, but of one and the same degreewise functor.  `modulePullback f` is
`CategoryTheory.SheafOfModules.pullback (structureSheafHom f)`, and
`(ringedToposSiteHom f).pullbackTopos` is `SheafOfModules.pullback` of `fSharpRing`;
the two maps of sheaves of rings are both `ObjectProperty.homMk` of `f^♯` whiskered with
`forget₂ CommRingCat RingCat`, so they are equal, and the `IsRightAdjoint` instance arguments
by which `SheafOfModules.pullback` chooses its left adjoint are `Prop`s, hence equal by proof
irrelevance.  Degreewise pullback, `pullbackOnHomotopy`, and the total left derived functor are
then the same term on each side, so `derivedPullback_eq` is `rfl`.  The same holds for the
sheaves of rings themselves: `structureSheafRing X`,
`(ToposBridge.ringedTopos X).ringSheaf` and `Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf` are
one `sheafCompose` term, differing only in where the `HasSheafCompose` instance comes from, and
that class is a `Prop`.

**The `O_X`-linear statement, in two constructions.**  Both sides of Stacks 08DE are genuinely
`O_X`-modules — `F ⊗_{f⁻¹O_Y} f⁻¹G` inherits the `O_X`-action from `F`, the tensor product being
taken over the smaller sheaf of rings `f⁻¹O_Y ⟶ O_X` — and the source states the tag for `F` in
`D(O_X)` and `G` in `D(O_Y)`.  The registered declaration `derivedLinearMixedTensorIso` is that
statement in `D(O_X)`.

`spaceDerivedLinearMixedTensorIso` is an intermediate comparison and is not the tag: its
right-hand side `spaceLinearDerivedMixedTensor` is `F ⊗^L_{O_X} Lh^*(f⁻¹G)`, the derived tensor
product over `O_X` with the derived extension of scalars of `f⁻¹G`, and the comparison is the
whiskering of Stacks 0G6R — `Lf^* ≅ Lg^* ⋙ Lh^*` — into the second variable.  No identification
of that bifunctor with the derived mixed tensor product over `f⁻¹O_Y` is proved here.

`derivedLinearMixedTensorIso` builds the right-hand side as the derived bifunctor of the
sectionwise mixed tensor product `(H, N) ↦ (H ⊗_{f⁻¹O_Y} N)^#`, computed by K-flat resolutions with flat terms of `N`; the
isomorphism is, on a K-flat complex `G` with flat terms, the underived identity
`F ⊗_{O_X} f^*G ≅ F ⊗_{f⁻¹O_Y} f⁻¹G` of sheaves of `O_X`-modules in each bidegree, as in the
source's proof.

`derivedMixedTensorIso` is the image of the comparison under restriction of scalars along
`f⁻¹O_Y ⟶ O_X`, with both bifunctors landing in `D(f⁻¹O_Y)`: Stacks 08I6 as formalized in this
repository, read at the presentation of `f`.

**The hypotheses.**  `hmos` is discharged here, not assumed: `V ↦ f⁻¹V` is a morphism of sites
between the small Zariski sites by `StacksZariskiSite.isMorphismOfSites_opensMap`, which is what
makes the continuous functor present a morphism of topoi.  The two
`HasLeftDerivedFunctor` instance arguments of Stacks 08I6 are discharged by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy` from
`hmos`.  So the statement below carries no residual hypothesis on `f`.

## References

* [The Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.Cohomology.MixedDerivedTensor StacksPullbackFactorization

namespace Stacks.Cohomology.MixedDerivedTensorOnARingedSpace

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : RingedSpace.{u, u}}

/-- **The morphism of ringed topoi presented by a morphism of ringed spaces**, in the form that
the ringed-topos derived pullback consumes: the continuous functor is `V ↦ f⁻¹V` on opens and
the structure map is `f^♯`.

`Stacks.ToposBridge.ringedToposHom` is the same morphism in the `AlgebraicGeometry.RingedToposHom`
form, whose geometric datum is a morphism of topoi rather than a continuous functor between the
sites; the derived pullback of Tag 06YY is stated for the latter. -/
def ringedToposSiteHom (f : X ⟶ Y) :
    RingedToposSiteHom (ToposBridge.ringedTopos X) (ToposBridge.ringedTopos Y) where
  u := Opens.map f.hom.base
  isContinuous := RingedSpaceModuleAdjunction.opensMap_isContinuous f
  fSharp := Stacks.ToposBridge.commRingStructureHom f

/-- **`V ↦ f⁻¹V` is a morphism of sites.**  This is the hypothesis under which the ringed-topos
derived pullback exists, and it holds for every morphism of ringed spaces. -/
theorem isMorphismOfSites (f : X ⟶ Y) :
    (ringedToposSiteHom f).u.IsMorphismOfSites (ToposBridge.ringedTopos Y).J
      (ToposBridge.ringedTopos X).J :=
  StacksZariskiSite.isMorphismOfSites_opensMap f.hom.base

/-! ### The instance plumbing of Stacks 08I6 at the site of opens

Every instance argument of Stacks 08I6 is discharged here, so the statement of Stacks 08DE below
carries no hypothesis beyond `f` itself. -/

/-- Sheafification of presheaves of abelian groups on the site of opens of a space. -/
local instance hasSheafifyRingedTopos (X : RingedSpace.{u, u}) :
    HasSheafify (ToposBridge.ringedTopos X).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})

/-- The weak equivalences of presheaves of abelian groups on the site of opens of a space are
the locally bijective maps. -/
local instance wEqualsLocallyBijectiveRingedTopos (X : RingedSpace.{u, u}) :
    (ToposBridge.ringedTopos X).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u})

/-- Forgetting commutativity preserves sheaves on the site of opens of a space. -/
local instance hasSheafComposeRingedTopos (X : RingedSpace.{u, u}) :
    (ToposBridge.ringedTopos X).J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
  inferInstanceAs ((Opens.grothendieckTopology X.carrier).HasSheafCompose
    (forget₂ CommRingCat.{u} RingCat.{u}))

/-- `⊗_{f⁻¹O_Y}` is additive in its first variable. -/
local instance sheafTensorInvRingAdditive (f : X ⟶ Y) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (invRing (ringedToposSiteHom f))).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u}
    (J := Opens.grothendieckTopology X.carrier) _

/-- `F ⊗_{f⁻¹O_Y} -` is additive. -/
local instance sheafTensorInvRingObjAdditive (f : X ⟶ Y)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (invRing (ringedToposSiteHom f)))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (invRing (ringedToposSiteHom f))).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (J := Opens.grothendieckTopology X.carrier) _ M

/-- The total complexes `Tot(K ⊗_{f⁻¹O_Y} L)` exist. -/
local instance hasMapBifunctorSheafTensorInvRing (f : X ⟶ Y)
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (invRing (ringedToposSiteHom f)))) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing (ringedToposSiteHom f)))
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := Opens.grothendieckTopology X.carrier) _ K L

/-- The ringed-topos derived pullback along `f` exists. -/
local instance hasLeftDerivedFunctorPullbackOnHomotopy (f : X ⟶ Y) :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
        (ringedToposSiteHom f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ToposBridge.ringedTopos Y).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (ringedToposSiteHom f) (isMorphismOfSites f)

/-- The derived inverse image `Lf⁻¹ : D(O_Y) ⥤ D(f⁻¹O_Y)` exists: it is the derived pullback
along the geometric half of the factorization of `f` through the auxiliary ringed topos
`(X, f⁻¹O_Y)`, whose underlying continuous functor is that of `f`. -/
local instance hasLeftDerivedFunctorPullbackOnHomotopyAux (f : X ⟶ Y) :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
        (auxHomG (ringedToposSiteHom f))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ToposBridge.ringedTopos Y).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (auxHomG (ringedToposSiteHom f)) (isMorphismOfSites f)

/-- The derived extension of scalars `Lh^* : D(f⁻¹O_Y) ⥤ D(O_X)` exists. -/
local instance hasLeftDerivedFunctorPullbackOnHomotopyAuxH (f : X ⟶ Y) :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.pullbackOnHomotopy
        (auxHomH (ringedToposSiteHom f))).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos (ringedToposSiteHom f)).O))
        (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (auxHomH (ringedToposSiteHom f))
    (Stacks.Cohomology.MixedDerivedTensor.isMorphismOfSites_auxHomH (ringedToposSiteHom f))

/-! ### The identification of the two derived pullbacks -/

variable (f : X ⟶ Y)

/-- The structure map of `ringedToposSiteHom f`, read on sheaves of not necessarily commutative
rings, *is* the datum `f^♯` that the ringed-space pullback of sheaves of modules is defined
from. -/
theorem fSharpRing_eq :
    (ringedToposSiteHom f).fSharpRing = RingedSpaceModuleAdjunction.structureSheafHom f :=
  rfl

/-- **The ringed-space pullback of sheaves of modules is the ringed-topos one.**  Both are
`CategoryTheory.SheafOfModules.pullback` of the same map of sheaves of rings. -/
theorem pullbackTopos_eq :
    (ringedToposSiteHom f).pullbackTopos = RingedSpaceModuleAdjunction.modulePullback f :=
  rfl

/-- **The ringed-space derived pullback is the ringed-topos one.**  This is what makes the
statement below a statement about the `Lf^*` of Tag 06YJ rather than about a second, unrelated
left derived functor of the same degreewise functor. -/
theorem derivedPullback_eq :
    Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback
        (ringedToposSiteHom f) =
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f :=
  rfl

/-! ### Stacks 08DE -/

/-- **The left-hand bifunctor of Stacks 08DE**: `(F, G) ↦ (F ⊗^L_{O_X} Lf^*G)|_{f⁻¹O_Y}`,
written with the *ringed-space* derived pullback of Tag 06YJ and the derived tensor product of
Tag 06YU over `O_X`. -/
def spaceDerivedTensorPullback :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ×
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (invRing (ringedToposSiteHom f)))) :=
  (𝟭 _).prod (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf) ⋙
      derivedRestrictTensor (ringedToposSiteHom f)

/-- The left-hand bifunctor of Stacks 08DE *is* the left-hand bifunctor of Stacks 08I6 at the
presentation of `f` as a morphism of ringed topoi. -/
theorem spaceDerivedTensorPullback_eq :
    spaceDerivedTensorPullback f = mixedDerivedTensorPullback (ringedToposSiteHom f) :=
  rfl

/-- **The right-hand bifunctor of Stacks 08DE**: `(F, G) ↦ F|_{f⁻¹O_Y} ⊗^L_{f⁻¹O_Y} f⁻¹G`. -/
def spaceDerivedTensorInverseImage :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ×
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (invRing (ringedToposSiteHom f)))) :=
  mixedDerivedTensorInverseImage (ringedToposSiteHom f)

/-- **The comparison of Stacks 08DE after restriction of scalars along `f⁻¹O_Y ⟶ O_X`.**  The
canonical bifunctorial isomorphism

`(F ⊗^L_{O_X} Lf^*G)|_{f⁻¹O_Y} ≅ F|_{f⁻¹O_Y} ⊗^L_{f⁻¹O_Y} f⁻¹G`

in `D(f⁻¹O_Y)`, for a morphism `f : (X, O_X) ⟶ (Y, O_Y)` of ringed spaces, `F` in `D(O_X)` and
`G` in `D(O_Y)`.  It is stated between the two uncurried bifunctors on `D(O_X) × D(O_Y)`, so that
bifunctoriality is part of its type, and the left-hand one is written with the ringed-space
derived pullback of Tag 06YJ.  The isomorphism of the tag in `D(O_X)` is
`spaceDerivedLinearMixedTensorIso` below. -/
def derivedMixedTensorIso :
    spaceDerivedTensorPullback f ≅ spaceDerivedTensorInverseImage f :=
  Stacks.Cohomology.MixedDerivedTensor.derivedMixedTensorIso (ringedToposSiteHom f)
    (isMorphismOfSites f)

/-! ### Stacks 08DE, `O_X`-linearly -/

/-- **The mixed tensor product over `f⁻¹O_Y`, as an endofunctor of `O_X`-modules**:
`F ↦ F ⊗_{f⁻¹O_Y} N`, with the `O_X`-action coming from `F` and sections
`F(U) ⊗_{f⁻¹O_Y(U)} N(U)`. -/
noncomputable def spaceLinearMixedTensorRight
    (N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos (ringedToposSiteHom f)).O)) :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ToposBridge.ringedTopos X).O) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (ToposBridge.ringedTopos X).O) :=
  Stacks.Cohomology.MixedDerivedTensor.linearMixedTensorRight.{u} (ringedToposSiteHom f) N

/-- **The underived identity of Stacks 08DE as sheaves of `O_X`-modules**:
`F ⊗_{O_X} f^*G ≅ F ⊗_{f⁻¹O_Y} f⁻¹G`, naturally in `F`. -/
noncomputable def spaceUnderivedLinearMixedTensorIso
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        (ToposBridge.ringedTopos X).O).flip.obj ((ringedToposSiteHom f).pullbackTopos.obj G)) ≅
      spaceLinearMixedTensorRight f ((auxHomG (ringedToposSiteHom f)).pullbackTopos.obj G) :=
  Stacks.Cohomology.MixedDerivedTensor.underivedLinearTensorInverseImageIso.{u}
    (ringedToposSiteHom f) G

/-- **The left-hand bifunctor of Stacks 08DE, `O_X`-linearly**: `(F, G) ↦ F ⊗^L_{O_X} Lf^*G`
read in `D(O_X)`, written with the *ringed-space* derived pullback of Tag 06YJ and the derived
tensor product of Tag 06YU over `O_X`. -/
def spaceLinearDerivedTensorPullback :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ×
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  (𝟭 _).prod (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf)

/-- The left-hand bifunctor of Stacks 08DE *is* the left-hand bifunctor of Stacks 08I6 at the
presentation of `f` as a morphism of ringed topoi, `O_X`-linearly as well. -/
theorem spaceLinearDerivedTensorPullback_eq :
    spaceLinearDerivedTensorPullback f =
      linearDerivedTensorPullback.{u} (ringedToposSiteHom f) :=
  rfl

/-- **The left-hand bifunctor of Stacks 08DE read in `D(f⁻¹O_Y)` is the restriction of scalars
of the `O_X`-linear one**, `spaceLinearDerivedTensorPullback`. -/
theorem spaceDerivedTensorPullback_eq_restrict :
    spaceDerivedTensorPullback f =
      spaceLinearDerivedTensorPullback f ⋙ derivedRestrictTensor (ringedToposSiteHom f) :=
  rfl

/-- **The bifunctor `(F, G) ↦ F ⊗^L_{O_X} Lh^*(f⁻¹G)`** into `D(O_X)`, where `f⁻¹G` is the
inverse image of `G` as a complex of `f⁻¹O_Y`-modules and `Lh^*` is the derived extension of
scalars along `f⁻¹O_Y ⟶ O_X`.  This is not the derived mixed tensor product
`F ⊗^L_{f⁻¹O_Y} f⁻¹G` of Stacks 08DE, which is `spaceDerivedMixedTensorInverseImage` below. -/
def spaceLinearDerivedMixedTensor :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ×
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  linearDerivedMixedTensor.{u} (ringedToposSiteHom f)

/-- **`F ⊗^L_{O_X} Lf^*G ≅ F ⊗^L_{O_X} Lh^*(f⁻¹G)`**, bifunctorially in `F` in `D(O_X)` and `G`
in `D(O_Y)`, for a morphism `f : (X, O_X) ⟶ (Y, O_Y)` of ringed spaces, where `h` is extension
of scalars along `f⁻¹O_Y ⟶ O_X`.  It is the whiskering of Stacks 0G6R, `Lf^* ≅ Lg^* ⋙ Lh^*`,
into the second variable.  Its right-hand side is not the derived mixed tensor product of
Stacks 08DE; the isomorphism of that tag is `derivedLinearMixedTensorIso` below. -/
def spaceDerivedLinearMixedTensorIso :
    spaceLinearDerivedTensorPullback f ≅ spaceLinearDerivedMixedTensor f :=
  Stacks.Cohomology.MixedDerivedTensor.derivedLinearMixedTensorIso.{u} (ringedToposSiteHom f)
    (isMorphismOfSites f)

/-! ### Stacks 08DE through the mixed tensor bifunctor -/

/-- **The right-hand bifunctor of Stacks 08DE**: `(F, G) ↦ F ⊗^L_{f⁻¹O_Y} f⁻¹G`, valued in
`D(O_X)`: the derived tensor product over `f⁻¹O_Y` of `F` with the derived inverse image of
`G`, an `O_X`-module through `F`. -/
def spaceDerivedMixedTensorInverseImage :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) ×
        DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf)) :=
  linearMixedDerivedTensorInverseImage (X := ToposBridge.ringedTopos X)
    (Y := ToposBridge.ringedTopos Y) (ringedToposSiteHom f)

/-- **Stacks 08DE, through the one-sided K-flat descent of the mixed tensor product.**  The
canonical bifunctorial isomorphism

`F ⊗^L_{O_X} Lf^*G ≅ F ⊗^L_{f⁻¹O_Y} f⁻¹G`

in `D(O_X)`, for a morphism `f : (X, O_X) ⟶ (Y, O_Y)` of ringed spaces, `F` in `D(O_X)` and
`G` in `D(O_Y)`.  The right-hand side is the derived tensor product over `f⁻¹O_Y` of `F` and
`f⁻¹G`, an object of `D(O_X)` through `F`.  It is stated between the two uncurried bifunctors on
`D(O_X) × D(O_Y)`, so that bifunctoriality is part of its type, and the left-hand one is written
with the ringed-space derived pullback of Tag 06YJ. -/
@[stacks 08DE "the canonical bifunctorial isomorphism, in D(O_X)"]
def derivedLinearMixedTensorIso :
    spaceLinearDerivedTensorPullback f ≅ spaceDerivedMixedTensorInverseImage f :=
  Stacks.Cohomology.MixedDerivedTensor.linearDerivedMixedTensorIso
    (X := ToposBridge.ringedTopos X) (Y := ToposBridge.ringedTopos Y) (ringedToposSiteHom f)
    (isMorphismOfSites f)

end Stacks.Cohomology.MixedDerivedTensorOnARingedSpace

end

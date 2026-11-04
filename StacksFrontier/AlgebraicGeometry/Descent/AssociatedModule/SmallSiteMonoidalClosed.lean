module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonUlift
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# `Mod(𝒪)` is monoidal closed at the module universe of the structure sheaf

Let `X` be a ringed site whose objects lie one universe above its morphisms and the sections of
its structure sheaf — `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, the shape of the small
Zariski and the small étale site of a scheme, and of the small étale site of an algebraic space
— and let `X` be essentially `u`-small.  This file equips the `𝒪`-modules with sections in `u`
with a **monoidal closed** structure whose internal Hom is
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, the internal Hom of Stacks 03EM descended
to the module universe `u`.

The monoidal structure is `Stacks.SheafOfModules.monoidalCategory` and the adjunction is
`AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction`, Stacks 03EO at the
module universe `u`.  Nothing new is proved about either; what is supplied here is the glue that
turns that adjunction into `CategoryTheory.MonoidalClosed`, namely the identification of
Mathlib's `MonoidalCategory.tensorRight` for the localized monoidal structure with the functor
`AlgebraicGeometry.RingedSite.tensorRightModules` that the adjunction is stated for, and the
passage from `tensorRight` to `tensorLeft` through the braiding.

## Main definitions

* `AlgebraicGeometry.RingedSite.modulesMonoidal`, `modulesBraided` and `modulesSymmetric`: the
  tensor product of `𝒪`-modules with sections in `u`, its braiding and the symmetry of that
  braiding, read off `Stacks.SheafOfModules.monoidalCategory` at the structure sheaf of `X`.
* `AlgebraicGeometry.RingedSite.closedSmall`: for each `𝒪`-module `M`, the object `M` is closed
  — `M ⊗ -` has a right adjoint, namely `internalHomSheafSmall X M -`.
* `AlgebraicGeometry.RingedSite.modulesMonoidalClosed`: **the `𝒪`-modules with sections in `u`
  are monoidal closed.**
* `AlgebraicGeometry.RingedSite.dualEvaluationSmall`: the evaluation `𝓗om_𝒪(M, N) ⊗ M ⟶ N`,
  which at `N = 𝒪` is the evaluation of Stacks 0FNY.
* `AlgebraicGeometry.Space.modulesMonoidalClosed`: the same for the small étale site of an
  algebraic space, at `AlgebraicGeometry.Space.modulesMonoidalCategory`.
* `AlgebraicGeometry.Space.smallEtaleDualEvaluation`: **the evaluation morphism
  `𝓗om(M, 𝒪_F) ⊗ M ⟶ 𝒪_F` of Stacks 0FNY, at the module universe of the schemes.**

## Main results

* `AlgebraicGeometry.RingedSite.tensorRightIso`: Mathlib's `tensorRight M` for the localized
  monoidal structure is `AlgebraicGeometry.RingedSite.tensorRightModules X M`, as functors.
* `AlgebraicGeometry.RingedSite.internalHom_obj_eq_internalHomSheafSmall` and
  `AlgebraicGeometry.Space.internalHom_obj_eq_smallEtaleInternalHomSmall`: the internal Hom of
  the monoidal closed structure is `internalHomSheafSmall`, on the nose, so a statement about
  one is a statement about the other.
* `AlgebraicGeometry.Space.modulesMonoidal_eq_modulesMonoidalCategory`: on the small étale
  ringed site of an algebraic space the monoidal structure closed here is
  `AlgebraicGeometry.Space.modulesMonoidalCategory` itself, not a second one.

## Implementation notes

**What this does and does not give.**  On such a site the dual *object* of an `𝒪`-module and the
*evaluation* out of it are now available at the module universe `u` of the structure sheaf.  The
**coevaluation** `𝒪 ⟶ M ⊗ 𝓗om(M, 𝒪)` is not, and neither is the left-dual pairing of
Stacks 0FNY, for a reason that is not a missing adjunction: the pairing cluster of Tag 0FNY in
this tree — `Stacks.SheafOfModules.dualSheaf`, `tensorDualToEndomorphism`,
`isIso_tensorDualToEndomorphism`, `coevaluation`, `exactPairingDualSheafOfRetract` and
`exactPairingDualSheafOfLocallyFreeData` — is stated for a structure sheaf
`𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}`, with the module universe equal to that *ring* universe.  On a
site of this shape `max u v = u + 1` while the structure sheaf has its sections in `u`, so the
cluster does not apply at module universe `u` and does not apply at `u + 1` either: the
obstruction is the ring universe, which is a property of the site and cannot be raised by
lifting the modules.  See the implementation notes of
`AlgebraicGeometry.RingedSite.modulesMonoidalClosed` for why there is also nothing to transport
down from `u + 1`.

**Why `tensorRight` and not `tensorLeft`.**
`AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction` is stated with
`- ⊗ M` on the left, because the internal Hom of Stacks 03EM has its source in the first
argument; Mathlib's `CategoryTheory.Closed` wants `M ⊗ -`.  The two are interchanged by
`CategoryTheory.BraidedCategory.tensorLeftIsoTensorRight`, which is why the braided structure
appears in the construction of a structure that does not mention it.

**The two spellings of the ring sheaf.**  `Stacks.SheafOfModules.Tensor.ringSheaf X.O`, which the
descended internal Hom is indexed by, and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf`, which the monoidal structure is
indexed by, are equal by `rfl`: both forget the commutativity of `X.O` and carry a proof of the
sheaf condition, which is a proposition.  That is
`AlgebraicGeometry.RingedSite.structureSheaf_eq_ringSheaf`, and it is what lets the monoidal
structure be stated for the same category the adjunction is stated for, with no transport.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u + 1, u, u})

/-- The underlying presheaf of rings of the structure sheaf of a ringed site is a sheaf, in the
spelling the tensor product of Stacks 05NA is indexed by.  It is the sheaf condition already
carried by `AlgebraicGeometry.RingedSite.ringSheaf`. -/
theorem structureRingPresheaf_isSheaf :
    Presheaf.IsSheaf X.J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.O.obj) :=
  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property

/-- The two spellings of the sheaf of rings `𝒪` agree.  Both forget the commutativity of the
structure sheaf and carry a proof of the sheaf condition, which is a proposition. -/
theorem structureSheaf_eq_ringSheaf :
    Stacks.SheafOfModules.TensorSheafification.structureSheaf X.O.obj
        (structureRingPresheaf_isSheaf X) =
      Stacks.SheafOfModules.Tensor.ringSheaf X.O :=
  rfl

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The tensor product of the `𝒪`-modules with sections in `u`** on a ringed site whose
objects lie one universe above its morphisms and its structure rings.  This is
`Stacks.SheafOfModules.monoidalCategory` at the structure sheaf of `X`; the module universe is
the universe of the structure sheaf, which is the only one at which Mathlib's monoidal structure
on presheaves of modules exists. -/
@[instance_reducible]
def modulesMonoidal :
    MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.monoidalCategory X.O.obj (structureRingPresheaf_isSheaf X)

attribute [local instance] modulesMonoidal

/-- The braiding of `AlgebraicGeometry.RingedSite.modulesMonoidal`. -/
@[instance_reducible]
def modulesBraided :
    BraidedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.braidedCategory X.O.obj (structureRingPresheaf_isSheaf X)

attribute [local instance] modulesBraided

/-- The braiding of `AlgebraicGeometry.RingedSite.modulesMonoidal` is a symmetry. -/
@[instance_reducible]
def modulesSymmetric :
    SymmetricCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  Stacks.SheafOfModules.symmetricCategory X.O.obj (structureRingPresheaf_isSheaf X)

/-- **Mathlib's `tensorRight M` is `AlgebraicGeometry.RingedSite.tensorRightModules X M`.**
Tensoring on the right by `M` in the localized monoidal structure is the functor the
tensor--internal-Hom adjunction of Stacks 03EO is stated for.

On objects the two agree on the nose, and on morphisms the comparison is
`Stacks.SheafOfModules.sheafifyWhiskerRight_eq_comparison`: the whiskering of the sheaf tensor
product is the localized whiskering conjugated by
`Stacks.SheafOfModules.tensorObjIso`. -/
def tensorRightIso (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tensorRight M ≅ tensorRightModules X M :=
  NatIso.ofComponents
    (fun N => Stacks.SheafOfModules.tensorObjIso X.O.obj (structureRingPresheaf_isSheaf X) N M)
    (fun {N _N'} f =>
      ((congrArg
          (fun z => (Stacks.SheafOfModules.tensorObjIso X.O.obj
            (structureRingPresheaf_isSheaf X) N M).hom ≫ z)
          (Stacks.SheafOfModules.sheafifyWhiskerRight_eq_comparison X.O.obj
            (structureRingPresheaf_isSheaf X) f M)).trans
        (Iso.hom_inv_id_assoc _ _)).symm)

variable [HasWeakSheafify X.J AddCommGrpCat.{u + 1}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] [EssentiallySmall.{u} X.C]

/-- **Each `𝒪`-module is closed**: `M ⊗ -` has a right adjoint, the descended internal Hom
`AlgebraicGeometry.RingedSite.internalHomSheafSmall X M -`.

This is `AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction`, Stacks 03EO at
the module universe of the structure sheaf, transported from `- ⊗ M` to `M ⊗ -` along
`AlgebraicGeometry.RingedSite.tensorRightIso` and the braiding. -/
@[instance_reducible]
def closedSmall (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Closed M where
  rightAdj := internalHomSheafSmallFunctor.{u} X M
  adj :=
    ((sheafTensorRightInternalHomSmallAdjunction X M).ofNatIsoLeft
        (tensorRightIso X M).symm).ofNatIsoLeft
      (BraidedCategory.tensorLeftIsoTensorRight M).symm

/-- **The `𝒪`-modules with sections in `u` are monoidal closed**, on a ringed site which is
essentially `u`-small and whose objects lie one universe above its morphisms and the sections of
its structure sheaf.  The internal Hom is
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`, the internal Hom of Stacks 03EM descended
to the module universe of the structure sheaf.

**This is not the monoidal closed structure of
`SheafOfModules.monoidalClosed`**, which is stated for a ring sheaf in
`CommRingCat.{max u v w}` with modules in the same universe and therefore does not apply here:
on a site of this shape `max u v = u + 1` while the structure sheaf has its sections in `u`.
That constraint is not an artefact of this tree.  Mathlib's
`PresheafOfModules.monoidalCategory`, which every monoidal structure on sheaves of modules here
is localized from, pins the module universe to the ring universe.  So of the `𝒪`-modules of such
a site only those with sections in `u` carry a tensor product at all here: no monoidal structure
on the `u + 1`-modules is available, and hence there is nothing monoidal at `u + 1` to transport
down to `u` along the sectionwise universe lift of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteSheafHomComparisonUlift`.  What
does descend to `u` is the *adjunction*, and that descent is what this structure is built
from. -/
@[instance_reducible]
def modulesMonoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) where
  closed := closedSmall X

attribute [local instance] modulesMonoidalClosed

/-- The internal Hom of `AlgebraicGeometry.RingedSite.modulesMonoidalClosed` is the descended
internal Hom of Stacks 03EM, on the nose: a statement about
`CategoryTheory.MonoidalClosed.internalHom` on such a site is a statement about
`AlgebraicGeometry.RingedSite.internalHomSheafSmall`. -/
theorem internalHom_obj_eq_internalHomSheafSmall
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (MonoidalClosed.internalHom.obj (Opposite.op M)).obj N = internalHomSheafSmall.{u} X M N :=
  rfl

/-- **The evaluation morphism `𝓗om_𝒪(M, N) ⊗ M ⟶ N`** at the module universe of the structure
sheaf: the counit of `AlgebraicGeometry.RingedSite.sheafTensorRightInternalHomSmallAdjunction`,
read in the localized monoidal structure along
`AlgebraicGeometry.RingedSite.tensorRightIso`.

At `N = 𝒪` this is the evaluation `ε` of Stacks 0FNY.  No `@[stacks 0FNY]` attribute is claimed
here or below: that tag asserts that `𝓗om(M, 𝒪)` together with this evaluation *and a
coevaluation* is a left dual of `M`, and the coevaluation is not available at this universe —
see the implementation notes of this file. -/
def dualEvaluationSmall
    (M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    internalHomSheafSmall.{u} X M N ⊗ M ⟶ N :=
  (tensorRightIso X M).hom.app (internalHomSheafSmall.{u} X M N) ≫
    (sheafTensorRightInternalHomSmallAdjunction X M).counit.app N

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

/-- The tensor product that `AlgebraicGeometry.RingedSite.modulesMonoidal` gives the small étale
ringed site of an algebraic space **is** `AlgebraicGeometry.Space.modulesMonoidalCategory`, on the
nose.  This is what makes the monoidal closed structure below a structure on the monoidal
category the consumers of `AlgebraicGeometry.Space.Modules` already use, rather than on a second
one. -/
theorem modulesMonoidal_eq_modulesMonoidalCategory :
    RingedSite.modulesMonoidal (smallEtaleRingedSite B S hS F hF) =
      modulesMonoidalCategory B S hS F hF :=
  rfl

/-- **The `𝒪_F`-modules on an algebraic space are monoidal closed**, with internal Hom
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall`.  This is
`AlgebraicGeometry.RingedSite.modulesMonoidalClosed` at the small étale ringed site of `F`,
whose monoidal structure is `AlgebraicGeometry.Space.modulesMonoidalCategory` by `rfl`. -/
@[instance_reducible]
def modulesMonoidalClosed : MonoidalClosed (Modules.{u, u} B S hS F hF) :=
  RingedSite.modulesMonoidalClosed (smallEtaleRingedSite B S hS F hF)

attribute [local instance] modulesMonoidalClosed

/-- The internal Hom of `AlgebraicGeometry.Space.modulesMonoidalClosed` is
`AlgebraicGeometry.Space.smallEtaleInternalHomSmall`, on the nose. -/
theorem internalHom_obj_eq_smallEtaleInternalHomSmall (M N : Modules.{u, u} B S hS F hF) :
    (MonoidalClosed.internalHom.obj (Opposite.op M)).obj N =
      smallEtaleInternalHomSmall B S hS F hF M N :=
  rfl

/-- **The evaluation morphism `𝓗om_{𝒪_F}(M, 𝒪_F) ⊗ M ⟶ 𝒪_F` of Stacks 0FNY**, at the module
universe of the schemes.

This is the half of Tag 0FNY's data that the closed structure supplies,
`AlgebraicGeometry.RingedSite.dualEvaluationSmall` at the tensor unit of the small étale ringed
site of `F`.  No `@[stacks 0FNY]` attribute is claimed: that tag asserts that `𝓗om(M, 𝒪_F)`
together with this evaluation *and a coevaluation* is a left dual of `M`, and the coevaluation is
not available at this universe. -/
def smallEtaleDualEvaluation (M : Modules.{u, u} B S hS F hF) :
    smallEtaleInternalHomSmall B S hS F hF M (𝟙_ (Modules.{u, u} B S hS F hF)) ⊗ M ⟶
      𝟙_ (Modules.{u, u} B S hS F hF) :=
  RingedSite.dualEvaluationSmall (smallEtaleRingedSite B S hS F hF) M
    (𝟙_ (Modules.{u, u} B S hS F hF))

end AlgebraicGeometry.Space

end

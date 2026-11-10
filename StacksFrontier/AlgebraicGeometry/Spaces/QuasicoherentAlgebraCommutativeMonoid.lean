module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafCommutativeMonoid
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesMonoidal

/-!
# A quasi-coherent algebra sheaf is a commutative monoid object in the quasi-coherent sheaves

Let `F` be an algebraic space.  An algebra sheaf on `F` is a commutative monoid object in
`AlgebraicGeometry.Space.Modules` by
`AlgebraicGeometry.Space.AlgebraSheaf.commMon`, and `AlgebraicGeometry.Space.QuasicoherentSheaves`
is a symmetric monoidal subcategory of `AlgebraicGeometry.Space.Modules` by
`AlgebraicGeometry.Space.quasicoherentSheavesMonoidalCategory`.  This file puts the two together:
**a quasi-coherent sheaf of commutative `𝒪_F`-algebras is a commutative monoid object in
`QCoh(𝒪_F)`.**

## Main definitions

* `CategoryTheory.ObjectProperty.monObjFullSubcategory` and
  `CategoryTheory.ObjectProperty.isCommMonObjFullSubcategory`: a (commutative) monoid object whose
  underlying object satisfies a monoidal property of objects is a (commutative) monoid object of
  the full subcategory that property cuts out.
* `AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentObj` is the quasi-coherent sheaf underlying a
  quasi-coherent algebra sheaf.
* `AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentMonObj`,
  `AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentIsCommMonObj` and
  `AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentCommMon` are **the commutative monoid object
  structure in `QCoh(𝒪_F)` on the quasi-coherent sheaf underlying a quasi-coherent algebra
  sheaf.**

## Main results

* `CategoryTheory.ObjectProperty.monObjFullSubcategory_one` and
  `CategoryTheory.ObjectProperty.monObjFullSubcategory_mul`: the unit and the multiplication of
  the lifted monoid object are those of the original one, on the nose.
* `AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentCommMon_X_obj`: the underlying `𝒪_F`-module
  of the commutative monoid object is the `𝒪_F`-module underlying the algebra sheaf, on the nose.

## Implementation notes

The lift is immediate because the monoidal structure of
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory` is the ambient one on the nose: the
tensor product of two objects of the subcategory is the ambient tensor product of their
underlying objects, the unit is the ambient unit, and the associator, the unitors and the
braiding are the ambient ones wrapped by `CategoryTheory.ObjectProperty.homMk`.  So the unit and
the multiplication of the ambient monoid object are already morphisms of the subcategory, and
each law is the ambient law after `CategoryTheory.ObjectProperty.hom_ext`.  Mathlib carries no
monoidal version of `CategoryTheory.ObjectProperty.lift` — that is an explicit TODO of
`Mathlib/CategoryTheory/Monoidal/Subcategory.lean` — so the two lifts are given here, in the same
place and for the same reason as `CategoryTheory.IsCommMonObj.ofIso` of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafCommutativeMonoid.lean`.

**What is not here.** No clause of Stacks 081V, and no equivalence.  The `equivalence` field of
`AlgebraicGeometry.Space.AffineAlgebraAntiEquivalence`
(`StacksFrontier/AlgebraicGeometry/Spaces/AffineAlgebraAntiEquivalence.lean:238`) is an
anti-equivalence between the algebraic spaces affine over `X` and
`AlgebraicGeometry.Space.QuasicoherentAlgebra`, the full subcategory of the algebra sheaves cut
out by quasi-coherence; it is *not* a statement about `CategoryTheory.CommMon` of anything, and
nothing below produces a functor out of `AlgebraicGeometry.Space.AffineOver`.  What the
commutative monoid object buys is that a quasi-coherent algebra is a structure in the symmetric
monoidal category `QCoh(𝒪_F)`, hence transportable along any braided monoidal equivalence of
quasi-coherent sheaves.  The converse direction — reading a commutative monoid object in
`QCoh(𝒪_F)` back as an `AlgebraicGeometry.Space.AlgebraSheaf` — is absent for the reason recorded
in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/AlgebraSheafCommutativeMonoid.lean`: it needs the
multiplication's sections, and a section of a tensor product sheaf is only locally a pure tensor.

**Why the equivalence of Stacks 03M3 cannot yet be applied to this structure.**  The
equivalence `AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase` has
`AlgebraicGeometry.Space.QuasicoherentModule` as its codomain, and
`CategoryTheory.Equivalence.mapCommMon` asks for a braided monoidal structure on both sides.
There is no `CategoryTheory.MonoidalCategory` on
`AlgebraicGeometry.Space.QuasicoherentModule` at all, so a
`CategoryTheory.Functor.LaxBraided` instance for
`AlgebraicGeometry.Space.quasicoherentFromSpaceBase` cannot even be *stated*.  Building that
monoidal structure means tensoring the transition morphisms: the transition of `M.F ⊗ N.F` is
`M.alpha ⊗ N.alpha` conjugated by the comparison
`AlgebraicGeometry.Space.modulePullbackTensorIso` of Stacks 03EL on each side, and the
`cocycle` and `unit` fields of the result then need that comparison to be compatible with
`AlgebraicGeometry.Space.modulePullbackCompIso` and with
`AlgebraicGeometry.Space.pullbackTransport`.  The comparison exists only as a bare isomorphism
with no coherence, so the declaration that unlocks the step is
`CategoryTheory.Functor.Monoidal (AlgebraicGeometry.Space.modulePullback B S hS f)`, which does
not exist; the analogous structure for a morphism of ringed *spaces* is
`Stacks.PullbackSheafTensor.monoidal` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackSheafTensorMonoidal.lean`, over a
different inverse-image functor.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]

/-- **A monoid object whose underlying object satisfies a monoidal property of objects is a
monoid object of the full subcategory that property cuts out.**

The unit and the multiplication are the ambient ones, read as morphisms of the full subcategory;
each law is the ambient law, the structural morphisms of
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory` being the ambient ones wrapped by
`CategoryTheory.ObjectProperty.homMk`. -/
@[instance_reducible]
def monObjFullSubcategory {X : C} [MonObj X] (hX : P X) :
    MonObj (⟨X, hX⟩ : P.FullSubcategory) where
  one := homMk η[X]
  mul := homMk μ[X]
  one_mul := hom_ext _ (by simp)
  mul_one := hom_ext _ (by simp)
  mul_assoc := hom_ext _ (by simp)

/-- The unit of `CategoryTheory.ObjectProperty.monObjFullSubcategory` is the ambient unit. -/
theorem monObjFullSubcategory_one {X : C} [MonObj X] (hX : P X) :
    letI := monObjFullSubcategory P hX
    (η[(⟨X, hX⟩ : P.FullSubcategory)]).hom = η[X] :=
  rfl

/-- The multiplication of `CategoryTheory.ObjectProperty.monObjFullSubcategory` is the ambient
multiplication. -/
theorem monObjFullSubcategory_mul {X : C} [MonObj X] (hX : P X) :
    letI := monObjFullSubcategory P hX
    (μ[(⟨X, hX⟩ : P.FullSubcategory)]).hom = μ[X] :=
  rfl

/-- **A commutative monoid object whose underlying object satisfies a monoidal property of
objects is a commutative monoid object of the full subcategory that property cuts out.**  The
braiding of `CategoryTheory.ObjectProperty.fullBraidedSubcategory` is the ambient braiding, so
commutativity is the ambient commutativity. -/
theorem isCommMonObjFullSubcategory [BraidedCategory C] {X : C} [MonObj X] [IsCommMonObj X]
    (hX : P X) :
    letI := monObjFullSubcategory P hX
    IsCommMonObj (⟨X, hX⟩ : P.FullSubcategory) := by
  let := monObjFullSubcategory P hX
  exact ⟨hom_ext _ (IsCommMonObj.mul_comm X)⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.Space.AlgebraSheaf

attribute [local instance] modulesMonoidalCategory modulesBraidedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (A : AlgebraSheaf.{u, u} B S hS F hF) (hA : A.IsQuasicoherent)

/-- The quasi-coherent sheaf underlying a quasi-coherent algebra sheaf: the `𝒪_F`-module
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` together with its quasi-coherence, which
is what `AlgebraicGeometry.Space.AlgebraSheaf.IsQuasicoherent` asserts. -/
noncomputable def quasicoherentObj : QuasicoherentSheaves.{u, u} B S hS F hF :=
  ⟨A.underlyingModule, hA⟩

/-- The underlying `𝒪_F`-module of
`AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentObj` is the `𝒪_F`-module underlying the
algebra sheaf. -/
@[simp]
theorem quasicoherentObj_obj : (A.quasicoherentObj hA).obj = A.underlyingModule :=
  rfl

/-- **The quasi-coherent sheaf underlying a quasi-coherent algebra sheaf is a monoid object** in
`QCoh(𝒪_F)`, for the tensor product of
`AlgebraicGeometry.Space.quasicoherentSheavesMonoidalCategory`: the monoid object of
`AlgebraicGeometry.Space.AlgebraSheaf.monObj`, read in the monoidal full subcategory. -/
@[instance_reducible]
noncomputable def quasicoherentMonObj :
    @MonObj (QuasicoherentSheaves.{u, u} B S hS F hF) _
      (quasicoherentSheavesMonoidalCategory B S hS F hF) (A.quasicoherentObj hA) :=
  let := A.monObj
  ObjectProperty.monObjFullSubcategory
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) hA

/-- The monoid object of `AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentMonObj` is
commutative. -/
theorem quasicoherentIsCommMonObj :
    @IsCommMonObj (QuasicoherentSheaves.{u, u} B S hS F hF) _
      (quasicoherentSheavesMonoidalCategory B S hS F hF)
      (quasicoherentSheavesBraidedCategory B S hS F hF) (A.quasicoherentObj hA)
      (A.quasicoherentMonObj hA) :=
  let := A.monObj
  let := A.isCommMonObj
  ObjectProperty.isCommMonObjFullSubcategory
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) hA

/-- **A quasi-coherent sheaf of commutative `𝒪_F`-algebras on an algebraic space is a commutative
monoid object in the quasi-coherent sheaves.**  The commutative monoid object in
`QCoh(𝒪_F)`, for the tensor product of
`AlgebraicGeometry.Space.quasicoherentSheavesMonoidalCategory`, whose underlying object is the
quasi-coherent sheaf underlying the algebra sheaf. -/
noncomputable def quasicoherentCommMon :
    @CommMon (QuasicoherentSheaves.{u, u} B S hS F hF) _
      (quasicoherentSheavesMonoidalCategory B S hS F hF)
      (quasicoherentSheavesBraidedCategory B S hS F hF) :=
  @CommMon.mk (QuasicoherentSheaves.{u, u} B S hS F hF) _
    (quasicoherentSheavesMonoidalCategory B S hS F hF)
    (quasicoherentSheavesBraidedCategory B S hS F hF) (A.quasicoherentObj hA)
    (A.quasicoherentMonObj hA) (A.quasicoherentIsCommMonObj hA)

/-- The underlying `𝒪_F`-module of
`AlgebraicGeometry.Space.AlgebraSheaf.quasicoherentCommMon` is the `𝒪_F`-module underlying the
algebra sheaf, on the nose. -/
theorem quasicoherentCommMon_X_obj :
    (@CommMon.X (QuasicoherentSheaves.{u, u} B S hS F hF) _
        (quasicoherentSheavesMonoidalCategory B S hS F hF)
        (quasicoherentSheavesBraidedCategory B S hS F hF) (A.quasicoherentCommMon hA)).obj =
      A.underlyingModule :=
  rfl

end AlgebraicGeometry.Space.AlgebraSheaf

end

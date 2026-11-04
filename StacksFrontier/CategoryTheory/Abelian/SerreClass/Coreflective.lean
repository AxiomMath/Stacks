module

public import Mathlib.CategoryTheory.Abelian.Opposite
public import Mathlib.CategoryTheory.Abelian.SerreClass.Bousfield
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Serre quotients through a right exact coreflector

Let `D` be an abelian category and `i : C ⥤ D` a fully faithful functor out of a preadditive
category with a right adjoint `Q : D ⥤ C` which is right exact.  Then:

* `C` is abelian (`CategoryTheory.abelianOfCoreflection`), the dual of
  `CategoryTheory.abelianOfAdjunction`;
* the kernel of `Q`, i.e. the objects `Q` sends to zero, is a Serre class of `D`;
* `Q` inverts exactly the morphisms whose kernel and cokernel lie in that Serre class;
* `Q` is a localization functor for that class, so `C` is the Serre quotient of `D` by the kernel
  of `Q` (`CategoryTheory.Abelian.isLocalization_isoModSerre_kernel_of_rightAdjoint`).

This is the dual of `CategoryTheory.Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint`,
where the localization functor is the *left* adjoint of a fully faithful functor.  Here it is the
right adjoint, and the point is that `C` need not be known to be abelian in advance: it is
abelian because `Q` is right exact.

## Main definitions

* `CategoryTheory.abelianOfCoreflection`: the abelian structure on `C`.

## Main results

* `CategoryTheory.Abelian.isSerreClass_kernel_of_rightAdjoint`: the kernel of `Q` is a Serre
  class.
* `CategoryTheory.Abelian.isoModSerre_kernel_eq_inverseImage_isomorphisms_of_rightAdjoint`: the
  morphisms inverted by `Q` are those with kernel and cokernel in the kernel of `Q`.
* `CategoryTheory.Abelian.isLocalization_isoModSerre_kernel_of_rightAdjoint`: `Q` is a
  localization functor for those morphisms.

## Implementation notes

The abelian structure on `C` is a `def`, not an instance, and the three results only use it
inside their proofs: their statements involve kernels and cokernels in `D` alone, so they hold
whatever abelian structure `C` is later given.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe vC uC vD uD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {i : C ⥤ D} {Q : D ⥤ C} (adj : i ⊣ Q) [i.Full] [i.Faithful] [PreservesFiniteColimits Q]

omit [Preadditive C] in
include adj in
/-- A right exact coreflector makes the coreflective subcategory finitely cocomplete: the
coreflector carries a colimit of `K ⋙ i` in `D` to a colimit of `K ⋙ i ⋙ Q ≅ K`. -/
theorem hasFiniteColimits_of_coreflection : HasFiniteColimits C where
  out _J _ _ := ⟨fun K =>
    have : HasColimit (K ⋙ i ⋙ Q) :=
      ⟨⟨⟨_, isColimitOfPreserves Q (colimit.isColimit (K ⋙ i))⟩⟩⟩
    hasColimit_of_iso (K.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft K (asIso adj.unit))⟩

/-- **A coreflective subcategory of an abelian category with a right exact coreflector is
abelian.**  This is `CategoryTheory.abelianOfAdjunction` applied to the opposite categories,
where `Q.op` is a left exact reflector onto `Cᵒᵖ`. -/
@[instance_reducible]
def abelianOfCoreflection : Abelian C :=
  haveI := hasFiniteColimits_of_coreflection adj
  haveI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
  haveI := adj.op.isLeftAdjoint
  haveI : PreservesFiniteLimits Q.op := preservesFiniteLimits_op Q
  haveI : Abelian Cᵒᵖ := abelianOfAdjunction i.op Q.op
    (NatIso.op (asIso adj.unit)) adj.op
  abelianOfEquivalence (opOp C)

namespace Abelian

variable {P : ObjectProperty D}

/-- A property of objects of `D` which holds exactly for the objects `Q` sends to zero is the
kernel of `Q`, for some abelian structure on `C` making `Q` a right adjoint. -/
private theorem exists_abelian_eq_kernel (adj : i ⊣ Q)
    (hP : ∀ X, P X ↔ IsZero (Q.obj X)) :
    ∃ (_ : Abelian C) (_ : Q.IsRightAdjoint), P = Q.kernel :=
  ⟨abelianOfCoreflection adj, adj.isRightAdjoint, funext fun X => propext (hP X)⟩

include adj in
/-- **The kernel of a right exact coreflector is a Serre class.**  It is stated for any
property `P` of objects of `D` which holds exactly for the objects `Q` sends to zero. -/
theorem isSerreClass_of_rightAdjoint (hP : ∀ X, P X ↔ IsZero (Q.obj X)) : P.IsSerreClass := by
  obtain ⟨_, _, rfl⟩ := exists_abelian_eq_kernel adj hP
  infer_instance

include adj in
/-- **A right exact coreflector inverts exactly the morphisms whose kernel and cokernel lie in
its kernel.**  It is stated for any Serre class `P` of `D` which holds exactly for the objects
`Q` sends to zero. -/
theorem isoModSerre_eq_inverseImage_isomorphisms_of_rightAdjoint [P.IsSerreClass]
    (hP : ∀ X, P X ↔ IsZero (Q.obj X)) :
    P.isoModSerre = (MorphismProperty.isomorphisms C).inverseImage Q := by
  obtain ⟨_, _, rfl⟩ := exists_abelian_eq_kernel adj hP
  exact isoModSerre_kernel_eq_inverseImage_isomorphisms Q

include adj in
/-- **A right exact coreflector is the Serre quotient by its kernel**: `Q` is a localization
functor for the morphisms whose kernel and cokernel lie in any Serre class `P` of `D` which
holds exactly for the objects `Q` sends to zero.  This is the dual of
`CategoryTheory.Abelian.isLocalization_isoModSerre_kernel_of_leftAdjoint`. -/
theorem isLocalization_isoModSerre_of_rightAdjoint [P.IsSerreClass]
    (hP : ∀ X, P X ↔ IsZero (Q.obj X)) : Q.IsLocalization P.isoModSerre := by
  rw [isoModSerre_eq_inverseImage_isomorphisms_of_rightAdjoint adj hP]
  exact adj.isLocalization'

end Abelian

end CategoryTheory

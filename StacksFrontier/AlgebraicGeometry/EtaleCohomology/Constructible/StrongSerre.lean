module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-!
# The strong Serre property for constructible abelian sheaves

Stacks 09BH (2) says that on a Noetherian scheme the constructible abelian sheaves on the small
étale site form a *strong* Serre subcategory of all abelian sheaves: besides kernels, cokernels and
extensions, they are closed under **subobjects** and **quotients**. That is strictly more than the
weak Serre property of 03RZ (2), which gives kernels, cokernels and extensions of maps *between*
constructible sheaves and says nothing about a subsheaf of a constructible sheaf. The difference is
what Stacks 0A5C needs: for the middle term of `0 → ℱ₁ → ℱ → ℱ₂ → 0` one has to deduce that
`ℱ₁` and `ℱ₂` are constructible *from* `ℱ` being constructible, which is exactly sub- and
quotient-closure.

This file does two things. It records the target statement of 09BH (2) in the form the library's
constructibility predicate takes, and it proves the categorical half of it: **given the weak Serre
property, closure under subobjects already implies the whole strong Serre property.** So the one
mathematical statement 09BH (2) still asks for is sub-closure.

## Main results

* `CategoryTheory.ObjectProperty.isClosedUnderQuotients_of_isClosedUnderSubobjects`: in an abelian
  category, a weak Serre class closed under subobjects is closed under quotients.
* `CategoryTheory.ObjectProperty.isSerreClass_of_isClosedUnderSubobjects` and
  `.isSerreClass_iff_isClosedUnderSubobjects`: hence such a class is a Serre class, and for a weak
  Serre class being a Serre class *is* closure under subobjects.
* `AlgebraicGeometry.isConstructibleAbelianSheafProperty`: constructibility of an abelian sheaf on
  the small étale site, as a property of objects of that abelian category — the subject of
  09BH (2).
* `AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects`: 09BH (2)
  follows from 03RZ (2) together with sub-closure. 03RZ (2) is proved in the library, so the form
  of this reduction to use is
  `AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects'`, which
  carries sub-closure alone.

## Implementation notes

**No `@[stacks 09BH]` attribute appears in this file**, because what is proved here is the
categorical reduction and not the proposition. The tag is carried, for parts (1) and (2), by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreSets` and
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian`. The latter
discharges the sub-closure hypothesis of the final theorem below from part (1) for sheaves of
sets, using that finite local constancy of an abelian sheaf is a property of its underlying sheaf
of sets; so the reduction here is not the only route to 09BH (2).

Of the two inputs of the final theorem, 03RZ (2) is available unconditionally —
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleAbelianSheaf`, at the coefficient
universe `AddCommGrpCat.{max (u + 1) w}` in which 093U (2) is available on this site, and
`AlgebraicGeometry.constructibleAbelianSheaf_isWeakSerreClass` at `AddCommGrpCat.{u + 1}`. So the
primed form of the final theorem below carries sub-closure alone.

The source's own route to sub-closure is Noetherian induction (the induction scheme is
`AlgebraicGeometry.exists_constructibleStratification_of_noetherianSpace`) reducing to a
neighbourhood of the generic point of an irreducible component; replacing the scheme by a
neighbourhood of a geometric point of that generic point, which needs constructibility to be
local, Stacks 095E, available as `AlgebraicGeometry.isConstructibleFiniteSheaf_tfae`,
`AlgebraicGeometry.isConstructibleModuleSheaf_tfae` and
`AlgebraicGeometry.isStratifiedSheaf_tfae`; descending a section of the subsheaf along
`U ×_X U ⇉ U` by the sheaf condition; and Stacks 09BG, that a sheaf squeezed between two constant
sheaves on an irreducible scheme whose generic geometric stalk is the subgroup equals the smaller
constant sheaf, which is available as
`AlgebraicGeometry.constantSetSubsheaf_eq_of_genericStalk`,
`AlgebraicGeometry.constantAbelianSubsheaf_eq_of_genericStalk` and
`AlgebraicGeometry.constantModuleSubsheaf_eq_of_genericStalk`. The descent of sections is the one
step of that route with no Lean declaration, and it is what part (3), for sheaves of modules over
a Noetherian ring, still needs: the underlying-sets route of `StrongSerreAbelian` does not reach
it, because a finite-type locally constant sheaf of modules has no finiteness on underlying sets.

The quotient half of the categorical reduction is the abelian substitute for the source's argument
for sheaves of sets, which forms `ℱ ×_𝒬 ℱ ⊆ ℱ × ℱ` and appeals to 03RZ. In an abelian category one
instead writes an epimorphism `f` as the cokernel of its own kernel: the kernel is a subobject, so
sub-closure puts it in the class, and cokernel-closure then puts the target in the class.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 09BG](https://stacks.math.columbia.edu/tag/09BG)
* [Stacks Project, Tag 0A5C](https://stacks.math.columbia.edu/tag/0A5C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w v

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- A weak Serre class closed under subobjects is closed under quotients.

An epimorphism is the cokernel of its own kernel. The kernel is a subobject of the source, so it
belongs to the class, and a weak Serre class is closed under cokernels of morphisms between its
members. -/
public theorem isClosedUnderQuotients_of_isClosedUnderSubobjects [P.IsWeakSerreClass]
    [P.IsClosedUnderSubobjects] : P.IsClosedUnderQuotients where
  prop_of_epi f _ hX :=
    P.prop_of_isColimit_cokernelCofork
      ((ShortComplex.mk (kernel.ι f) f (kernel.condition f)).exact_of_f_is_kernel
        (kernelIsKernel f)).gIsCokernel
      (P.prop_of_mono (kernel.ι f) hX) hX

/-- **A weak Serre class closed under subobjects is a Serre class.** The two conditions of
`CategoryTheory.ObjectProperty.IsSerreClass` which a weak Serre class does not already have are
closure under subobjects and under quotients, and the first implies the second. -/
public theorem isSerreClass_of_isClosedUnderSubobjects [P.IsWeakSerreClass]
    [P.IsClosedUnderSubobjects] : P.IsSerreClass :=
  have := P.isClosedUnderQuotients_of_isClosedUnderSubobjects
  { }

/-- For a weak Serre class, being a Serre class is exactly closure under subobjects.

This is the precise sense in which the content of Stacks 09BH (2) over Stacks 03RZ (2) is the
single assertion that a subsheaf of a constructible abelian sheaf is constructible. -/
public theorem isSerreClass_iff_isClosedUnderSubobjects [P.IsWeakSerreClass] :
    P.IsSerreClass ↔ P.IsClosedUnderSubobjects :=
  ⟨fun _ => inferInstance, fun _ => P.isSerreClass_of_isClosedUnderSubobjects⟩

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{w}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{w}]
  [HasSheafify (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}]

/-- Constructibility of an abelian sheaf on the small étale site of `X`, as a property of objects
of the abelian category of all such sheaves. This is the subject of Stacks 09BH (2). -/
public def isConstructibleAbelianSheafProperty :
    ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{w}) :=
  fun F => IsConstructibleAbelianSheaf B X F

/-- **Stacks 09BH (2) from Stacks 03RZ (2) and sub-closure.** If the constructible abelian sheaves
on the small étale site of `X` form a weak Serre subcategory and a subsheaf of a constructible
abelian sheaf is constructible, then they form a strong Serre subcategory.

The first hypothesis is Stacks 03RZ (2) and is available: at the coefficient universe of 093U (2)
on this site it is
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleAbelianSheaf`, and
`AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects'` is this
statement with it discharged. The second is the geometric content of Stacks 09BH;
`AlgebraicGeometry.isClosedUnderSubobjects_isConstructibleAbelianSheaf` supplies it at
`AddCommGrpCat.{u + 1}`. The Noetherian hypothesis on `X` that 09BH carries is not needed for this
reduction; it is needed for that input. -/
public theorem isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects
    [(isConstructibleAbelianSheafProperty B X).IsWeakSerreClass]
    [(isConstructibleAbelianSheafProperty B X).IsClosedUnderSubobjects] :
    (isConstructibleAbelianSheafProperty B X).IsSerreClass :=
  (isConstructibleAbelianSheafProperty B X).isSerreClass_of_isClosedUnderSubobjects

end AlgebraicGeometry

end

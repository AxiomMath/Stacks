module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedHomOfAHomotopyColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectStructureSheafWitness

/-!
# A non-degenerate system of perfect objects

Stacks 0DJI, and the statements around it, do not bind a single perfect object: they bind a
*system* `F : ℕ ⥤ D(O)` together with the hypothesis `∀ n, IsPerfect (F.obj n)`. Such a
hypothesis is inhabited by the constant system on any single perfect object, so
`AlgebraicGeometry.RingedSite.isPerfect_derivedStructureSheaf` already settles it in principle;
what is recorded here is the system itself, because the term-level passage is not one a proof
search finds — `((Functor.const ℕ).obj K).obj n` and `K` are definitionally but not syntactically
equal, and `exact?` on the system-shaped goal fails while the same call on the object-shaped goal
succeeds.

The system is the constant one on the structure sheaf in degree zero. Every one of its terms is
a perfect object, and every one of them fails to be a zero object as soon as `O` is not a zero
module, so the hypothesis is inhabited *non-degenerately*: not by the system all of whose terms
are zero, which `AlgebraicGeometry.RingedSite.isPerfect_of_isZero` supplies and which makes every
conclusion drawn from it empty.

**Nothing here is a clause of a Stacks tag and nothing here is tagged.** These are inhabitants of
the hypotheses of tagged statements, not part of any assertion.

## Main definitions

* `AlgebraicGeometry.RingedSite.constDerivedStructureSheafSystem`: the constant system
  `n ↦ O[0]` of objects of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_constDerivedStructureSheafSystem`: every term of that
  system is a perfect object in the sense of Stacks 08G5.
* `AlgebraicGeometry.RingedSite.not_isZero_constDerivedStructureSheafSystem`: no term of it is a
  zero object, once `O` is not a zero module.
* `Stacks.SheafOfModules.OnSpace.isPerfect_constDerivedStructureSheafSystem_specULiftInt` and
  `Stacks.SheafOfModules.OnSpace.not_isZero_constDerivedStructureSheafSystem_specULiftInt`: the
  two together at a named base, `Spec ℤ`, with no hypothesis of any kind.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08G5)](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 0DJI](https://stacks.math.columbia.edu/tag/0DJI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The constant system `n ↦ O[0]`** of objects of `D(O)`, with identity transition maps. -/
abbrev constDerivedStructureSheafSystem :
    ℕ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (Functor.const ℕ).obj (derivedStructureSheaf X)

/-- **Every term of the constant system is a perfect object**, so the hypothesis
`∀ n, IsPerfect (F.obj n)` carried by the statements about systems of perfect objects — Stacks
0DJI among them — is inhabited. -/
theorem isPerfect_constDerivedStructureSheafSystem (n : ℕ) :
    X.IsPerfect ((constDerivedStructureSheafSystem X).obj n) :=
  isPerfect_derivedStructureSheaf X

omit [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **No term of the constant system is a zero object**, once `O` is not a zero module. Together
with the previous theorem this is what makes the perfectness hypothesis of a statement about a
system non-degenerately inhabited: the system all of whose terms vanish also satisfies it, and
every conclusion drawn at that system is empty. -/
theorem not_isZero_constDerivedStructureSheafSystem
    (h : ¬ IsZero (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ) :
    ¬ IsZero ((constDerivedStructureSheafSystem X).obj n) :=
  not_isZero_derivedStructureSheaf X h

end AlgebraicGeometry.RingedSite

namespace Stacks.SheafOfModules.OnSpace

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A named base at which the system is non-degenerate.** On `Spec ℤ` every term of the
constant system on the structure sheaf is a perfect object of `D(O)`, with no hypothesis of any
kind. -/
theorem isPerfect_constDerivedStructureSheafSystem_specULiftInt (n : ℕ) :
    (Stacks.SheafOfModules.ringedSite (specULiftIntRingedSpace.{u}).sheaf).IsPerfect
      ((AlgebraicGeometry.RingedSite.constDerivedStructureSheafSystem
        (Stacks.SheafOfModules.ringedSite (specULiftIntRingedSpace.{u}).sheaf)).obj n) :=
  isPerfect_derivedStructureSheaf_specULiftInt

/-- **And no term of it is a zero object there**, unconditionally: `1 ≠ 0` in the ring of global
sections of `Spec ℤ`. -/
theorem not_isZero_constDerivedStructureSheafSystem_specULiftInt (n : ℕ) :
    ¬ IsZero ((AlgebraicGeometry.RingedSite.constDerivedStructureSheafSystem
      (Stacks.SheafOfModules.ringedSite (specULiftIntRingedSpace.{u}).sheaf)).obj n) :=
  not_isZero_derivedStructureSheaf_specULiftInt

end Stacks.SheafOfModules.OnSpace

end

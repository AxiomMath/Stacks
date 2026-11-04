module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Evaluation
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf

/-!
# Invertible quotients exist, and the base-change comparisons fire on them

`Stacks.Divisors.InvertibleQuotient X E` packages a surjection from `E` onto an invertible
`𝒪_X`-module. Tag 0B3V's two base-change comparisons —
`Stacks.Divisors.quotientKernelBaseChange` and `Stacks.Divisors.inverseQuotientBaseChange` —
and everything else in `StacksDraft/AlgebraicGeometry/F3b/InvertibleQuotient/` is quantified
over that structure. Before this file the only declaration *concluding* it was
`Stacks.RelativeProj.TautologicalDatum.pullbackQuotient`, which takes a tautological datum and
a **section of `𝐏(E) → X`** as inputs; nothing in either tree exhibits such a section, so the
structure had no inhabitant and every statement about it was true and empty.

This file inhabits it unconditionally and then fires both comparisons on the inhabitants, so
the comparisons are known to be about something.

## Main definitions

* `Stacks.Divisors.InvertibleQuotient.ofInvertible`: an invertible module is an invertible
  quotient of itself, by the identity.
* `Stacks.Divisors.unitInvertibleQuotient`: **the structure sheaf of any scheme carries one,
  with no hypothesis.**
* `Stacks.Divisors.biprodInvertibleQuotient`: the first projection `L ⊞ L ⟶ L`. Its kernel is
  `L` rather than the zero object, so it exercises the kernel clause; the identity quotient
  does not.
* `Stacks.Divisors.InvertibleQuotient.baseChange`: the pullback of an invertible quotient along
  an arbitrary morphism of schemes, again an invertible quotient.

## Main results

* `Stacks.Divisors.kernel_biprodInvertibleQuotient_iso`: the kernel of the biproduct quotient is
  `L`. This is what makes that witness non-degenerate, and
  `Stacks.Divisors.exists_invertibleQuotient_kernel_iso_unit` is the unconditional consequence:
  every scheme carries an invertible quotient whose kernel is the structure sheaf.
* `Stacks.Divisors.exists_baseChange_data`: **the three comparison hypotheses that both of Tag
  0B3V's base-change comparisons take — `hE`, `hL` and the compatibility `hq` — are jointly
  satisfiable**, for every morphism of schemes and every invertible quotient, with both
  comparison isomorphisms the identity.
* `Stacks.Divisors.quotientKernelBaseChange_baseChange` and
  `Stacks.Divisors.inverseQuotientBaseChange_baseChange`: the two comparisons applied to that
  data. Each is a term of the comparison's own type with every hypothesis discharged, so
  neither comparison is a theorem about an empty hypothesis set.

## Implementation notes

**The invertibility of a pullback crosses the two Tag 01CS classes once.**
`Stacks.Modules.isInvertible_pullback` concludes `Stacks.SheafOfModules.IsInvertible`, while
`Stacks.Divisors.InvertibleQuotient.invertible` is
`AlgebraicGeometry.SheafOfModules.IsInvertible`. The crossing is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, used twice in
`Stacks.Divisors.isInvertible_pullbackObj_of_isInvertible` and nowhere else here. This is the
same crossing `Stacks.RelativeProj.TautologicalDatum.ofInvertible` already makes.

**The invertibility argument is explicit, not an instance binder.** The library instance for the
structure sheaf, `AlgebraicGeometry.Scheme.Modules.isInvertible_unit`, concludes at the
`X.toRingedSpace.presheaf` / `structureSheafRing
  X.toRingedSpace` spelling while
`InvertibleQuotient` records the class at `X.presheaf` / `X.ringCatSheaf.2`; instance search
does not cross that gap, and the term is accepted against the declared type.

**Why `𝟙` is not a sufficient witness on its own.** `InvertibleQuotient.ofInvertible` has
`kernel q = 0`, so the quotient-kernel comparison at it compares two zero objects and exercises
nothing. `biprodInvertibleQuotient` is supplied for that reason. What no witness here reaches
is a quotient of a module that is *not* a direct sum of invertibles — in particular nothing
here exercises `𝐏(E)` for `E` of rank `≥ 2`, and no section of a projective bundle is
produced.

**The biproduct of the structure sheaf with itself cannot be written in a declared return
type.** `HasBinaryBiproducts X.Modules` is `inferInstance` and
`HasBinaryBiproduct (SheafOfModules.unit X.ringCatSheaf : X.Modules) _` is found with the
ascription, yet the *term* `(SheafOfModules.unit X.ringCatSheaf : X.Modules) ⊞ _` is
`synthInstanceFailed` — the `⊞` notation re-elaborates its operands without the ascription, and
`SheafOfModules.unit X.ringCatSheaf` then presents at the `SheafOfModules X.ringCatSheaf`
spelling, which the instance at the `def`-wrapped `X.Modules` does not reach. Nothing is needed
at an *application* of `Stacks.Divisors.biprodInvertibleQuotient`, whose instance is resolved
once at its own definition site with the module a variable; so the unconditional statement is
an existential with the module bound at `X.Modules` rather than a `def` with `⊞` in its type.

**No tag is attached.** Tag 0B3V's content is the bijection, the conormal identification and
their base-change compatibilities; this file states none of them. It supplies the data their
quantifiers range over.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X X' : Scheme.{u}}

/-- **The pullback of an invertible module sheaf is invertible**, at the `X.presheaf` /
`X.ringCatSheaf.2` spelling of the class that `Stacks.Divisors.InvertibleQuotient` records.
This is `Stacks.Modules.isInvertible_pullback` read across the two Tag 01CS classes by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`. -/
theorem isInvertible_pullbackObj_of_isInvertible (g : X' ⟶ X) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ g L
      ((Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL))

/-- **An invertible module sheaf is an invertible quotient of itself**, by the identity. -/
def InvertibleQuotient.ofInvertible (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    InvertibleQuotient X L where
  L := L
  invertible := hL
  q := 𝟙 L
  epi := inferInstance

/-- The invertible module of `InvertibleQuotient.ofInvertible X L hL` is `L`. -/
@[simp] theorem InvertibleQuotient.ofInvertible_L (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    (InvertibleQuotient.ofInvertible X L hL).L = L := rfl

/-- The quotient map of `InvertibleQuotient.ofInvertible X L hL` is the identity of `L`. -/
@[simp] theorem InvertibleQuotient.ofInvertible_q (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    (InvertibleQuotient.ofInvertible X L hL).q = 𝟙 L := rfl

/-- **Every scheme carries an invertible quotient, with no hypothesis**: the structure sheaf is
invertible (Tag 01CT) and is a quotient of itself. -/
def unitInvertibleQuotient (X : Scheme.{u}) :
    InvertibleQuotient X (SheafOfModules.unit X.ringCatSheaf) :=
  InvertibleQuotient.ofInvertible X _ (AlgebraicGeometry.Scheme.Modules.isInvertible_unit X)

/-- **An invertible quotient whose kernel is not the zero object**: the first projection
`L ⊞ L ⟶ L`, a split epimorphism with kernel `L`. -/
def biprodInvertibleQuotient (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    InvertibleQuotient X (L ⊞ L) where
  L := L
  invertible := hL
  q := biprod.fst
  epi := inferInstance

/-- The quotient map of `biprodInvertibleQuotient X L hL` is the first projection `L ⊞ L ⟶ L`. -/
@[simp] theorem biprodInvertibleQuotient_q (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    (biprodInvertibleQuotient X L hL).q = (biprod.fst : L ⊞ L ⟶ L) := rfl

/-- **The kernel of the biproduct quotient is `L`, not the zero object.** So the quotient-kernel
base-change comparison at this witness compares two copies of `g^*L` rather than two zero
objects, which is what the identity quotient of `Stacks.Divisors.InvertibleQuotient.ofInvertible`
would give. -/
def kernel_biprodInvertibleQuotient_iso (X : Scheme.{u}) (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    kernel (biprodInvertibleQuotient X L hL).q ≅ L :=
  kernelBiprodFstIso

/-- **Every scheme carries an invertible quotient whose kernel is the structure sheaf rather
than the zero object, with no hypothesis.** This is the biproduct witness at the structure
sheaf, which is invertible by Tag 01CT. -/
theorem exists_invertibleQuotient_kernel_iso_unit (X : Scheme.{u}) :
    ∃ (E : X.Modules) (Q : InvertibleQuotient X E),
      Nonempty (kernel Q.q ≅ SheafOfModules.unit X.ringCatSheaf) :=
  ⟨_, biprodInvertibleQuotient X (SheafOfModules.unit X.ringCatSheaf)
      (AlgebraicGeometry.Scheme.Modules.isInvertible_unit X),
    ⟨kernel_biprodInvertibleQuotient_iso X _ _⟩⟩

/-- **The pullback of an invertible quotient along an arbitrary morphism of schemes.** Pullback
is a left adjoint, so it preserves the epimorphism, and it preserves invertibility. -/
def InvertibleQuotient.baseChange (g : X' ⟶ X) {E : X.Modules} (Q : InvertibleQuotient X E) :
    InvertibleQuotient X' ((Scheme.Modules.pullback g).obj E) where
  L := (Scheme.Modules.pullback g).obj Q.L
  invertible := isInvertible_pullbackObj_of_isInvertible g Q.L Q.invertible
  q := (Scheme.Modules.pullback g).map Q.q
  epi := by have := Q.epi; infer_instance

/-- The invertible module of `Q.baseChange g` is the pullback `g^*Q.L`. -/
@[simp] theorem InvertibleQuotient.baseChange_L (g : X' ⟶ X) {E : X.Modules}
    (Q : InvertibleQuotient X E) :
    (Q.baseChange g).L = (Scheme.Modules.pullback g).obj Q.L := rfl

/-- The quotient map of `Q.baseChange g` is the pullback of the quotient map of `Q`. -/
@[simp] theorem InvertibleQuotient.baseChange_q (g : X' ⟶ X) {E : X.Modules}
    (Q : InvertibleQuotient X E) :
    (Q.baseChange g).q = (Scheme.Modules.pullback g).map Q.q := rfl

/-- **The hypothesis set of both of Tag 0B3V's base-change comparisons is jointly satisfiable**,
for every morphism of schemes and every invertible quotient: take the pulled-back quotient, with
both comparison isomorphisms the identity. The compatibility `hq` is then the unit laws. -/
theorem exists_baseChange_data (g : X' ⟶ X) (E : X.Modules) (Q : InvertibleQuotient X E) :
    ∃ (E' : X'.Modules) (Q' : InvertibleQuotient X' E')
      (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
      (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L),
      Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q :=
  ⟨_, Q.baseChange g, Iso.refl _, Iso.refl _, by simp⟩

/-- **Tag 0B3V's quotient-kernel base-change comparison, fired.** Every hypothesis is
discharged, so the comparison is not a statement about an empty hypothesis set. -/
def quotientKernelBaseChange_baseChange (g : X' ⟶ X) (E : X.Modules)
    (Q : InvertibleQuotient X E) :
    { e : (Scheme.Modules.pullback g).obj (kernel Q.q) ≅ kernel (Q.baseChange g).q //
      e.hom ≫ kernel.ι (Q.baseChange g).q =
        (Scheme.Modules.pullback g).map (kernel.ι Q.q) ≫ (Iso.refl _).inv } :=
  quotientKernelBaseChange g E _ (Iso.refl _) Q (Q.baseChange g) (Iso.refl _) (by simp)

/-- **Tag 0B3V's inverse-line base-change comparison, fired.** The only hypothesis is the
identification of the quotient lines, which is the identity here. -/
def inverseQuotientBaseChange_baseChange (g : X' ⟶ X) (E : X.Modules)
    (Q : InvertibleQuotient X E) :
    (Scheme.Modules.pullback g).obj
        (letI := Q.invertible
         Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 Q.L (-1)) ≅
      (letI := (Q.baseChange g).invertible
       Stacks.SheafOfModules.Invertible.tensorPower X'.presheaf X'.ringCatSheaf.2
         (Q.baseChange g).L (-1)) :=
  inverseQuotientBaseChange g E _ Q (Q.baseChange g) (Iso.refl _)

end Stacks.Divisors

end

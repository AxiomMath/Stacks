module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.Basic

/-!
# Base change of invertible quotients, at the `Scheme.Modules.pullback` spelling

Tag 0B3V describes the sections of the projective bundle `P(E) ⟶ X` by the surjections from `E`
onto an invertible module, taken up to isomorphism of the target. The vocabulary of that
right-hand side -- `Stacks.Divisors.InvertibleQuotient`, the equivalence relation on it, the
setoid and the type of isomorphism classes, together with the comparison of kernels that the
tag's conormal clause compares across a base change -- is
`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/Basic.lean`, and this file uses it rather
than restating it.

What is added here is a spelling gap that blocks every statement of this shape, see
`Stacks.ProjectiveBundleQuotients.pullbackIso`, and the base change of a quotient in the form
Tag 0B3V's clauses are written in.

## Main definitions

* `Stacks.ProjectiveBundleQuotients.pullbackIso`: the pullback functor on module sheaves of a
  morphism of schemes agrees with the pullback functor of its underlying morphism of ringed
  spaces.
* `Stacks.ProjectiveBundleQuotients.InvertibleQuotient.baseChange` and `baseChangeClass`: the
  pullback of a `Stacks.Divisors.InvertibleQuotient` along a morphism of schemes, and the induced
  map on `Stacks.Divisors.InvertibleQuotientClass`.

## Main results

* `Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj`: **the pullback of an invertible
  module sheaf along a morphism of schemes is invertible, at the `Scheme.Modules.pullback`
  spelling.** Registered as an instance.
* `Stacks.ProjectiveBundleQuotients.baseChange_isEquivalent`: base change respects the
  equivalence of quotients, which is what makes `baseChangeClass` well defined.

## Implementation notes

**The spelling gap, and why it has to be closed here.** Tag 0B8L -- the pullback of an invertible
module is invertible -- is formalized twice, as
`Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf` and
`Stacks.InvertiblePullback.isInvertibleModule_pullback`, and *both* conclude about
`RingedSpaceModuleAdjunction.modulePullback f.toLRSHom.toShHom`, the pullback of the underlying
morphism of ringed spaces. The statements of Tag 0B3V, and of Tag 01O4 before it, are written
with `AlgebraicGeometry.Scheme.Modules.pullback` instead -- the spelling Mathlib's adjunction,
`Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackId` are stated in. Instance
search does **not** cross between the two, so `Stacks.SheafOfModules.IsInvertible X.presheaf
X.ringCatSheaf.2 ((Scheme.Modules.pullback g).obj L)` fails to synthesize outright. `pullbackIso`
closes the gap, and `isInvertible_pullback_obj` is Tag 0B8L at the spelling the tagged statements
use.

The bridge is the uniqueness of a left adjoint: both functors are left adjoint to the *same*
pushforward functor, so `CategoryTheory.Adjunction.leftAdjointUniq` applies with nothing to
check. No transport of the base sheaf of rings is needed on either side.

**`baseChange` carries the comparison `hE : E' ≅ (Scheme.Modules.pullback g).obj E` rather than
fixing `E'` to be the pullback**, which is the form Tag 0B3V's base-change clauses are stated in:
the module on the new base is given independently and only compared with the pullback. It is
therefore not an instance of `Stacks.Divisors.InvertibleQuotient.baseChange`, which fixes the
target module to the pullback itself; neither is written in terms of the other.

**`Stacks.Divisors.InvertibleQuotient.invertible` and `.epi` are not global instances**, so the
corresponding two fields of a base-changed quotient name them explicitly through `letI` and
`haveI`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)

## Not done here

**No assertion of Tag 0B3V is proved and no tag of it is attached.** Of its nine labelled
assertions, one -- `closed immersion` -- is proved and tagged in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SectionClosedImmersion`. The other eight
all need one of
three objects that this repository does not construct at this pin, and nothing here supplies any
of them: a `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` for the relative Proj of
`Sym(E)` (Tag 01NR, the relative `O(1)`, hence the tautological quotient), a
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Representation` (Tag 01O4, the existence assertion),
or a base-change comparison for the relative Proj of a quasi-coherent graded algebra along an
arbitrary morphism of bases.

**Nothing is said about the compatibility of `baseChange` with composition or with the identity.**
Those need `Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackId` threaded through the
comparison `hE`, and no statement below consumes them.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open RingedSpaceModuleAdjunction

namespace Stacks.ProjectiveBundleQuotients

universe u

/-! ### The two spellings of the pullback of module sheaves -/

/-- **The pullback functor on module sheaves of a morphism of schemes is the pullback functor of
its underlying morphism of ringed spaces.**

`AlgebraicGeometry.Scheme.Modules.pullback g` and
`RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom` are left adjoint to the same
pushforward functor, so the uniqueness of a left adjoint identifies them. This is the bridge that
carries Tag 0B8L from the spelling it is proved in to the spelling the tagged statements use. -/
public def pullbackIso {X X' : Scheme.{u}} (g : X' ⟶ X) :
    Scheme.Modules.pullback g ≅ modulePullback g.toLRSHom.toShHom :=
  (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjointUniq
    (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom)

/-- **Stacks Tag 0B8L at the `Scheme.Modules.pullback` spelling**: the pullback of an invertible
module sheaf along a morphism of schemes is invertible.

`Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf` is the same statement for
`RingedSpaceModuleAdjunction.modulePullback`, and instance search does not cross between the two
spellings; this instance is that one transported along `Stacks.ProjectiveBundleQuotients.`
`pullbackIso`. -/
public instance isInvertible_pullback_obj {X X' : Scheme.{u}} (g : X' ⟶ X) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    Stacks.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj L) :=
  Stacks.SheafOfModules.isInvertible_of_iso _ _ ((pullbackIso g).app L).symm

/-! ### Base change -/

variable {X : Scheme.{u}} {E : X.Modules}
variable {X' : Scheme.{u}} (g : X' ⟶ X) {E' : X'.Modules}

/-- **The base change of an invertible quotient.** Given a comparison of `E'` with the pullback of
`E`, an invertible quotient of `E` gives one of `E'`: the pullback of the quotient map, precomposed
with the comparison. Invertibility of the target is Tag 0B8L and surjectivity is preservation of
epimorphisms by a left adjoint. -/
public def InvertibleQuotient.baseChange (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : Stacks.Divisors.InvertibleQuotient X E) :
    Stacks.Divisors.InvertibleQuotient X' E' where
  L := (Scheme.Modules.pullback g).obj Q.L
  invertible :=
    letI := Q.invertible
    isInvertible_pullback_obj g Q.L
  q := hE.hom ≫ (Scheme.Modules.pullback g).map Q.q
  epi :=
    haveI := Q.epi
    epi_comp _ _

/-- The quotient map of a base-changed invertible quotient is the comparison `hE` followed by the
pullback of the original quotient map. -/
@[simp]
public theorem InvertibleQuotient.baseChange_q (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : Stacks.Divisors.InvertibleQuotient X E) :
    (InvertibleQuotient.baseChange g hE Q).q =
      hE.hom ≫ (Scheme.Modules.pullback g).map Q.q := rfl

/-- **Base change respects the equivalence of invertible quotients**: an isomorphism of targets
over `E` pulls back to one over `E'`. -/
public theorem baseChange_isEquivalent (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    {Q R : Stacks.Divisors.InvertibleQuotient X E} (h : Q.IsEquivalent R) :
    (InvertibleQuotient.baseChange g hE Q).IsEquivalent
      (InvertibleQuotient.baseChange g hE R) := by
  obtain ⟨α, hα⟩ := h
  refine ⟨(Scheme.Modules.pullback g).mapIso α, ?_⟩
  dsimp only [InvertibleQuotient.baseChange, Functor.mapIso_hom]
  rw [Category.assoc, ← Functor.map_comp, hα]

/-- **The base-change map on isomorphism classes of invertible quotients.** -/
public def baseChangeClass (hE : E' ≅ (Scheme.Modules.pullback g).obj E) :
    Stacks.Divisors.InvertibleQuotientClass X E →
      Stacks.Divisors.InvertibleQuotientClass X' E' :=
  Quotient.map (fun Q => InvertibleQuotient.baseChange g hE Q) fun _ _ h =>
    baseChange_isEquivalent g hE h

/-- `baseChangeClass` sends the class of an invertible quotient to the class of its base change. -/
@[simp]
public theorem baseChangeClass_mk (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
    (Q : Stacks.Divisors.InvertibleQuotient X E) :
    baseChangeClass g hE (Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid X E) Q) =
      Quotient.mk (Stacks.Divisors.invertibleQuotientSetoid X' E')
        (InvertibleQuotient.baseChange g hE Q) := rfl

end Stacks.ProjectiveBundleQuotients

end

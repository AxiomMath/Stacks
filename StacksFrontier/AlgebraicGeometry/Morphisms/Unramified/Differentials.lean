module

public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unramified morphisms and the vanishing of the relative differentials

A morphism of schemes is formally unramified exactly when its sheaf of relative differentials is
a zero object. It is unramified exactly when, in addition, it is locally of finite type, and
G-unramified exactly when it is locally of finite presentation.

## Main results

* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_of_isZero_relativeDifferentials`: vanishing
  of the sheaf of relative differentials makes a morphism formally unramified.
* `AlgebraicGeometry.Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials`: a morphism
  is formally unramified if and only if its sheaf of relative differentials is a zero object.
* `AlgebraicGeometry.unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials`: a
  morphism is unramified if and only if it is locally of finite type and its sheaf of relative
  differentials is zero.
* `AlgebraicGeometry.gUnramified_iff_locallyOfFinitePresentation_and_isZero_relativeDifferentials`:
  a morphism is G-unramified if and only if it is locally of finite presentation and its sheaf of
  relative differentials is zero.
* `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials_of_mono`: the sheaf of relative
  differentials of a monomorphism is zero; the special case of an immersion is
  `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentials_of_isImmersion`.

## References

* [Stacks Project, Tag 02H9](https://stacks.math.columbia.edu/tag/02H9)
* [Stacks Project, Tag 02G5](https://stacks.math.columbia.edu/tag/02G5)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01UY](https://stacks.math.columbia.edu/tag/01UY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.AffineDifferentialsIso

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- A morphism of schemes whose sheaf of relative differentials is a zero object is formally
unramified. -/
@[ega "IV 17.4.2" "c) ⇒ a)"]
theorem formallyUnramified_of_isZero_relativeDifferentials (f : X ⟶ S)
    (hz : IsZero (relativeDifferentials f)) : FormallyUnramified f := by
  refine ⟨fun {V} hV {U} hU hUV ↦ ?_⟩
  obtain ⟨e, -, -⟩ := existsUnique_affineDifferentialsIso f hU hUV hV
  have hsec : IsZero ((relativeDifferentials f).val.obj (.op U)) :=
    Functor.map_isZero (PresheafOfModules.evaluation X.ringCatSheaf.obj (.op U))
      (Functor.map_isZero (Scheme.Modules.toPresheafOfModules X) hz)
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  rw [show (f.appLE V U hUV).hom = algebraMap Γ(S, V) Γ(X, U) from rfl,
    RingHom.formallyUnramified_algebraMap, Algebra.formallyUnramified_iff]
  exact ModuleCat.isZero_iff_subsingleton.mp (hsec.of_iso e.symm)

/-- A morphism of schemes is formally unramified if and only if its sheaf of relative
differentials is a zero object. -/
@[stacks 02H9, ega "IV 17.2.1", ega "IV 17.2.2" "case Z = Y", ega "IV 17.4.2" "a) ⇔ c)"]
theorem formallyUnramified_iff_isZero_relativeDifferentials (f : X ⟶ S) :
    FormallyUnramified f ↔ IsZero (relativeDifferentials f) :=
  ⟨fun _ ↦ isZero_relativeDifferentials_of_formallyUnramified f,
    formallyUnramified_of_isZero_relativeDifferentials f⟩

/-- The sheaf of relative differentials of a monomorphism of schemes is a zero object. -/
@[stacks 01UY]
theorem isZero_relativeDifferentials_of_mono (f : X ⟶ S) [Mono f] :
    IsZero (relativeDifferentials f) :=
  (formallyUnramified_iff_isZero_relativeDifferentials f).mp inferInstance

/-- The sheaf of relative differentials of an immersion of schemes is a zero object. -/
@[stacks 01UY "the immersion case named in the first clause of the statement"]
theorem isZero_relativeDifferentials_of_isImmersion (f : X ⟶ S) [IsImmersion f] :
    IsZero (relativeDifferentials f) :=
  isZero_relativeDifferentials_of_mono f

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A morphism of schemes is unramified if and only if it is locally of finite type and its
sheaf of relative differentials is zero. -/
@[stacks 02G5 "part (1)",
  stacks 02GD "first sentence: an unramified morphism is locally of finite type",
  ega "IV 17.4.1.2" "Omega = 0 criterion", sga "1 II 4.1" "S=Y, unramified clause"]
theorem unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials (f : X ⟶ S) :
    Unramified f ↔
      (LocallyOfFiniteType f ∧ IsZero (Scheme.Hom.relativeDifferentials f)) := by
  rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified,
    Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials]

/-- A morphism of schemes is G-unramified if and only if it is locally of finite presentation
and its sheaf of relative differentials is zero. -/
@[stacks 02G5 "part (2)",
  stacks 02GD "first sentence: an unramified morphism is locally of finite type"]
theorem gUnramified_iff_locallyOfFinitePresentation_and_isZero_relativeDifferentials
    (f : X ⟶ S) :
    GUnramified f ↔
      (LocallyOfFinitePresentation f ∧ IsZero (Scheme.Hom.relativeDifferentials f)) := by
  rw [gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified,
    Scheme.Hom.formallyUnramified_iff_isZero_relativeDifferentials]

end AlgebraicGeometry

end

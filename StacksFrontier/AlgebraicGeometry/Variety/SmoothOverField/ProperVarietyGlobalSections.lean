module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Connected
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.RingTheory.GeometricallyIrreducible.Tower

/-!
# Global functions on a proper variety

The ring of global functions on a proper variety over a field is a field finite over that field.
It is separable over the base field when the variety is geometrically reduced, purely inseparable
when it is geometrically irreducible, and equal to the base field when it is geometrically
integral.

## Main results

* `AlgebraicGeometry.isSeparable_globalSections_of_isProperVariety`: for a geometrically reduced
  proper variety the field of global functions is separable over the base field.
* `AlgebraicGeometry.isPurelyInseparable_globalSections_of_isProperVariety`: for a
  geometrically irreducible proper variety the field of global functions is purely inseparable
  over the base field.

## Implementation notes

The `k`-algebra structure on the global sections is the canonical one induced by the structure
morphism. That the global sections form a field finite over `k` is
`AlgebraicGeometry.isField_of_universallyClosed` together with
`AlgebraicGeometry.finite_appTop_of_universallyClosed`, both of which apply because a proper
variety is integral, universally closed and locally of finite type; those two statements are the
first part of the source, and are tagged here.

Separability is read off geometric reducedness of a stalk: the global sections are a field, so the
germ map at any point is injective, and geometric reducedness passes to a subalgebra. Pure
inseparability is read off geometric irreducibility of the global sections, which holds because a
geometrically irreducible morphism is geometrically connected: the separable closure of `k` inside
a geometrically irreducible extension is `k` itself, and for an algebraic extension that is
exactly pure inseparability. The last part — that a geometrically integral proper scheme has only
constant global functions — holds without the variety hypothesis and is stated that way.

## References

* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.ProperSectionsGeom

universe u

namespace AlgebraicGeometry

add_to_stacks 04L2 "part (1), field" AlgebraicGeometry.isField_of_universallyClosed
add_to_stacks 04L2 "part (1), finite extension"
  AlgebraicGeometry.finite_appTop_of_universallyClosed

/-- The global sections of a proper variety over `k` form a finite `k`-module. -/
private theorem finite_globalSections_of_isProperVariety
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProperVariety k f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Module.Finite k Γ(X, ⊤) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  rw [← RingHom.finite_algebraMap]
  exact (finite_appTop_of_universallyClosed k f).comp
    (RingHom.Finite.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom fun x =>
      ⟨(Scheme.ΓSpecIso (.of k)).hom.hom x, by simp⟩)

/-- **Stacks Project, Tag 04L2, part (2).** For a geometrically reduced proper variety over a
field `k`, the field of global functions is separable over `k`. -/
@[stacks 04L2 "part (2)"]
theorem isSeparable_globalSections_of_isProperVariety
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] [GeometricallyReduced f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    Algebra.IsSeparable k Γ(X, ⊤) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed k f).toField
  let : Module.Finite k Γ(X, ⊤) := finite_globalSections_of_isProperVariety k f
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : Algebra.IsSeparableExtension k Γ(X, ⊤) :=
    ((Algebra.isSeparableExtension_tfae k Γ(X, ⊤) (ringExpChar k)).out 4 1).mp
      (isGeometricallyReduced_globalSections_of_injective_germ k f x
        (X.presheaf.germ ⊤ x trivial).hom.injective)
  exact isSeparable_of_isSeparableExtension k Γ(X, ⊤)

/-- **Stacks Project, Tag 04L2, part (3).** For a geometrically irreducible proper variety over a
field `k`, the field of global functions is purely inseparable over `k`. -/
@[stacks 04L2 "part (3)"]
theorem isPurelyInseparable_globalSections_of_isProperVariety
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProperVariety k f] [GeometricallyIrreducible f] :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    IsPurelyInseparable k Γ(X, ⊤) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Field Γ(X, ⊤) := (isField_of_universallyClosed k f).toField
  let : Module.Finite k Γ(X, ⊤) := finite_globalSections_of_isProperVariety k f
  have : GeometricallyConnected f := ⟨fun _ _ y Z fst snd h ↦
    (GeometricallyIrreducible.geometrically_irreducibleSpace y fst snd h).connectedSpace⟩
  exact (separableClosure.eq_bot_iff (F := k) (E := Γ(X, ⊤))).1
    ((separableClosure.eq_bot_iff_geometricallyIrreducible k Γ(X, ⊤)).2
      (isGeometricallyIrreducible_globalSections_of_isProper k f))

add_to_stacks 04L2 "part (4)" AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral

end AlgebraicGeometry

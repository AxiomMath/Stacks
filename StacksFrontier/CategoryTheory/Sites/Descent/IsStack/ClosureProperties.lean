module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.IsoOverId

/-!
# Closure of a subcategory under strongly cartesian morphisms and under descent

For a functor `p : 𝒳 ⥤ 𝒮` and a property `P` of objects of `𝒳`, two closure conditions: the
source of a strongly cartesian morphism into an object with property `P` is isomorphic to an
object with property `P`, and an object whose pullbacks along a covering family are all isomorphic
to objects with property `P` is itself isomorphic to one. Each comes in two forms, reading
"isomorphic" as isomorphic over the identity (`CategoryTheory.Functor.IsoOverId`) or plainly
(`P.isoClosure`), and the two forms agree when `P` is closed under isomorphisms.

## Main definitions

* `CategoryTheory.Functor.ClosedUnderStronglyCartesian` and
  `CategoryTheory.Functor.ClosedUnderStronglyCartesianUpToIso`, closure under strongly cartesian
  morphisms;
* `CategoryTheory.Functor.LocallyClosed` and
  `CategoryTheory.Functor.LocallyClosedUpToIso`, closure under descent along coverings.

## Main results

* `CategoryTheory.Functor.closedUnderStronglyCartesian_iff_upToIso` and
  `CategoryTheory.Functor.locallyClosed_iff_upToIso`, that the two forms of each agree.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- If `φ : y ⟶ x` is strongly cartesian and `x` has property `P`, then `y` is isomorphic over
the identity to an object with property `P`. -/
@[implicit_reducible]
def ClosedUnderStronglyCartesian (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) : Prop :=
  ∀ {V U : 𝒮} {y x : 𝒳} (f : V ⟶ U) (φ : y ⟶ x), p.IsStronglyCartesian f φ →
    P x → IsoOverId p P y

/-- If `φ : y ⟶ x` is strongly cartesian and `x` has property `P`, then `y` is isomorphic to an
object with property `P`. -/
def ClosedUnderStronglyCartesianUpToIso (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳) : Prop :=
  ∀ {V U : 𝒮} {y x : 𝒳} (f : V ⟶ U) (φ : y ⟶ x), p.IsStronglyCartesian f φ →
    P x → P.isoClosure y

/-- `ClosedUnderStronglyCartesian` implies `ClosedUnderStronglyCartesianUpToIso`. -/
lemma ClosedUnderStronglyCartesian.upToIso {p : 𝒳 ⥤ 𝒮} {P : ObjectProperty 𝒳}
    (h : ClosedUnderStronglyCartesian p P) : ClosedUnderStronglyCartesianUpToIso p P :=
  fun f φ hφ hx => isoClosure_of_isoOverId (h f φ hφ hx)

/-- For `P` closed under isomorphisms, `ClosedUnderStronglyCartesian` and
`ClosedUnderStronglyCartesianUpToIso` agree. -/
lemma closedUnderStronglyCartesian_iff_upToIso (p : 𝒳 ⥤ 𝒮) (P : ObjectProperty 𝒳)
    [P.IsClosedUnderIsomorphisms] :
    ClosedUnderStronglyCartesian p P ↔ ClosedUnderStronglyCartesianUpToIso p P :=
  ⟨fun h => h.upToIso, fun h _ _ _ _ f φ hφ hx =>
    (isoOverId_iff_isoClosure p P _).2 (h f φ hφ hx)⟩

/-- If `{fᵢ : Uᵢ ⟶ U}` is a covering and every pullback `fᵢ^* x` is isomorphic over the identity
to an object with property `P`, then so is `x`. -/
def LocallyClosed (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered]
    (P : ObjectProperty 𝒳) (J : GrothendieckTopology 𝒮) : Prop :=
  ∀ {U : 𝒮} {ι : Type (max u₁ v₁)} (Uᵢ : ι → 𝒮) (fᵢ : (i : ι) → Uᵢ i ⟶ U),
    Sieve.generate (Presieve.ofArrows Uᵢ fᵢ) ∈ J U →
    ∀ x : p.Fiber U, (∀ i, IsoOverId p P (pullbackFiber p x (fᵢ i)).1) →
      IsoOverId p P x.1

/-- If `{fᵢ : Uᵢ ⟶ U}` is a covering and every pullback `fᵢ^* x` is isomorphic to an object with
property `P`, then so is `x`. -/
def LocallyClosedUpToIso (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered]
    (P : ObjectProperty 𝒳) (J : GrothendieckTopology 𝒮) : Prop :=
  ∀ {U : 𝒮} {ι : Type (max u₁ v₁)} (Uᵢ : ι → 𝒮) (fᵢ : (i : ι) → Uᵢ i ⟶ U),
    Sieve.generate (Presieve.ofArrows Uᵢ fᵢ) ∈ J U →
    ∀ x : p.Fiber U, (∀ i, P.isoClosure (pullbackFiber p x (fᵢ i)).1) →
      P.isoClosure x.1

/-- For `P` closed under isomorphisms, `LocallyClosed` and `LocallyClosedUpToIso` agree. -/
lemma locallyClosed_iff_upToIso (p : 𝒳 ⥤ 𝒮) [p.IsPreFibered] (P : ObjectProperty 𝒳)
    [P.IsClosedUnderIsomorphisms] (J : GrothendieckTopology 𝒮) :
    LocallyClosed p P J ↔ LocallyClosedUpToIso p P J :=
  ⟨fun h _ _ Uᵢ fᵢ hcov x hx => isoClosure_of_isoOverId
      (h Uᵢ fᵢ hcov x fun i => (isoOverId_iff_isoClosure p P _).2 (hx i)),
    fun h _ _ Uᵢ fᵢ hcov x hx => (isoOverId_iff_isoClosure p P x.1).2
      (h Uᵢ fᵢ hcov x fun i => isoClosure_of_isoOverId (hx i))⟩

end Functor

end CategoryTheory

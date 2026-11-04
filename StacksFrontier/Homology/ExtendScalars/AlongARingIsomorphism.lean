module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Extension of scalars along a ring isomorphism

Let `e : R ≃+* S` be an isomorphism of commutative rings. Restriction of scalars along `e` is
an equivalence `Mod(S) ⥤ Mod(R)`, so its left adjoint — extension of scalars along `e` — is
an inverse of it, namely restriction of scalars along `e⁻¹`. In particular restricting and
then extending scalars along `e` is the identity functor of `Mod(S)`.

A consequence is that a composite `restrictScalars ρ ⋙ extendScalars ψ`, for two ring maps
`ρ : S →+* T` and `ψ : S →+* A` out of a common source, is unchanged when both are
precomposed with one and the same ring isomorphism `α : R ≃+* S`:

`restrictScalars (ρ ∘ α) ⋙ extendScalars (ψ ∘ α) ≅ restrictScalars ρ ⋙ extendScalars ψ.`

That reconciliation is what identifies a chain of restrictions of scalars along isomorphisms
of rings, followed by one extension of scalars, with a single extension of scalars along a
ring map between the two rings one started from.

## Main results

* `ModuleCat.extendScalarsIsoRestrictScalarsSymm`: extension of scalars along a ring
  isomorphism is restriction of scalars along the inverse isomorphism.
* `ModuleCat.restrictExtendScalarsSelfIso`: restriction of scalars along a ring isomorphism
  followed by extension of scalars along it is the identity functor.
* `ModuleCat.restrictExtendScalarsCompIso`: precomposing a restriction and an extension of
  scalars with one and the same ring isomorphism does not change their composite.

## Implementation notes

`ModuleCat.extendScalarsRestrictScalarsIso` is the object-level form of
`ModuleCat.restrictExtendScalarsSelfIso`, written as an explicit linear equivalence for rings
in independent universes. The natural isomorphism here is obtained instead from uniqueness of
left adjoints, which avoids checking naturality of that explicit map. It is stated for rings in
a single universe, which is the generality of `ModuleCat.extendScalarsComp`, the other
ingredient of `ModuleCat.restrictExtendScalarsCompIso`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- **Extension of scalars along a ring isomorphism is restriction of scalars along the
inverse isomorphism.** Restriction of scalars along `e` is an equivalence, so its left
adjoint is an inverse of it. -/
def extendScalarsIsoRestrictScalarsSymm (e : R ≃+* S) :
    extendScalars.{u, u, u} e.toRingHom ≅ restrictScalars.{u} e.symm.toRingHom :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdj.{u, u, u} e.toRingHom)
    (restrictScalarsEquivalenceOfRingEquiv.{u, u, u} e).symm.toAdjunction

/-- **Along a ring isomorphism, extension of scalars undoes restriction of scalars.** -/
def restrictExtendScalarsSelfIso (e : R ≃+* S) :
    restrictScalars.{u} e.toRingHom ⋙ extendScalars.{u, u, u} e.toRingHom ≅
      𝟭 (ModuleCat.{u} S) :=
  Functor.isoWhiskerLeft _ (extendScalarsIsoRestrictScalarsSymm e) ≪≫
    (restrictScalarsEquivalenceOfRingEquiv.{u, u, u} e).unitIso.symm

variable {T A : Type u} [Ring T] [CommRing A]

/-- **Precomposing a restriction and an extension of scalars with one and the same ring
isomorphism does not change their composite.** -/
def restrictExtendScalarsCompIso (ρ : S →+* T) (ψ : S →+* A) (α : R ≃+* S) :
    restrictScalars.{u} (ρ.comp α.toRingHom) ⋙ extendScalars.{u, u, u} (ψ.comp α.toRingHom) ≅
      restrictScalars.{u} ρ ⋙ extendScalars.{u, u, u} ψ :=
  Functor.isoWhiskerRight (restrictScalarsComp.{u} α.toRingHom ρ)
      (extendScalars.{u, u, u} (ψ.comp α.toRingHom)) ≪≫
    Functor.isoWhiskerLeft (restrictScalars.{u} ρ ⋙ restrictScalars.{u} α.toRingHom)
      (extendScalarsComp α.toRingHom ψ) ≪≫
    Functor.isoWhiskerLeft (restrictScalars.{u} ρ)
      (Functor.isoWhiskerRight (restrictExtendScalarsSelfIso α) (extendScalars.{u, u, u} ψ))

end ModuleCat

end

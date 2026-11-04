module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc

/-!
# The comparison of direct images of modules as a transported comparison

For a composable pair `f : X ⟶ Y`, `g : Y ⟶ Z` of morphisms of algebraic spaces, Stacks 03LU
provides the comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images of `𝒪`-modules,
`AlgebraicGeometry.Space.modulePushforwardCompIso`.  One level down,
`AlgebraicGeometry.Space.pushforwardModulesCompAt` is the same comparison at the morphisms of
ringed topoi of Stacks 03G8, and there the associativity cocycle law is available as
`AlgebraicGeometry.Space.pushforwardModulesCompAt_assoc`.

The two comparisons differ by transports along
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward`, an equality of functors.
This file identifies them, and isolates the general fact that a cocycle law survives such a
transport.

## Main definitions

* `CategoryTheory.Functor.compIsoCongr` transports a composition comparison `p ⋙ q ≅ pq` along
  equalities `p = p'`, `q = q'`, `pq = pq'` of functors.

## Main results

* `CategoryTheory.Functor.compIsoCongr_cocycle`: transporting a composition comparison along
  equalities of functors preserves the associativity cocycle law.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_eq_compIsoCongr`: **the comparison of
  direct images of modules of Stacks 03LU is the comparison at the morphisms of ringed topoi,
  so transported.**  This is the identification that the implementation notes of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` record as missing,
  and the reason it was missing is worth stating, since it dictates the proof: `eqToHom` is
  `Eq.mpr`-based, so reducing `(eqToHom p).app F` means deciding `p`, and here `p` is an
  equality of functors between categories of sheaves of modules — deciding it unfolds
  `AlgebraicGeometry.Space.modulePushforward`,
  `AlgebraicGeometry.RingedToposHom.pushforwardModules` and `SheafOfModules.restrictScalars`
  at those types, which does not terminate.  Every spelling that puts the transports into a
  *composition of morphisms* therefore diverges.  What does work is to stay at the level of
  isomorphisms and never project: the two sides differ by one application of
  `CategoryTheory.Iso.trans_assoc`, and `congrArg` of it is the whole proof.

## Implementation notes

Associativity of composition in `AlgebraicGeometry.AlgebraicSpaces` holds by definitional
unfolding, so no transport along `CategoryTheory.Category.assoc` appears below.

## What is not done

The associativity cocycle law is **not** carried across from
`AlgebraicGeometry.Space.pushforwardModulesCompAt` to
`AlgebraicGeometry.Space.modulePushforwardCompIso`, and so not to
`AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`.  The two ingredients are both here —
`CategoryTheory.Functor.compIsoCongr_cocycle` is the transport law and
`modulePushforwardCompIso_eq_compIsoCongr` rewrites the four comparisons into the transported
form — and the elaborator accepts their composition once
`CategoryTheory.Functor.compIsoCongr` is kept from unfolding.  The *kernel* does not: it
ignores reducibility, and checking the instantiated transport law against the cocycle
statement sends it into the `eqToHom` reduction described above.  The obstruction is isolated:
the cocycle statement's own type is kernel-checkable at these types, and so is each half of
it, so what remains is only the final defeq between the instantiated conclusion and that type.
Removing the `eqToHom`s is what the remaining step needs — that is,
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` becoming a componentwise
natural isomorphism rather than an equality of functors, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean` already propose.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

variable {A₀ : Type u₀} {A₁ : Type u₁} {A₂ : Type u₂} {A₃ : Type u₃}
  [Category.{v₀} A₀] [Category.{v₁} A₁] [Category.{v₂} A₂] [Category.{v₃} A₃]

/-- A composition comparison `p ⋙ q ≅ pq` transported along equalities `p = p'`, `q = q'` and
`pq = pq'` of functors. -/
def compIsoCongr {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂} (hp : p = p')
    (hq : q = q') (hpq : pq = pq') (P : p ⋙ q ≅ pq) : p' ⋙ q' ≅ pq' :=
  eqToIso (congrArg₂ (fun (a : A₀ ⥤ A₁) (b : A₁ ⥤ A₂) ↦ a ⋙ b) hp.symm hq.symm) ≪≫ P ≪≫
    eqToIso hpq

/-- `CategoryTheory.Functor.compIsoCongr` written out. -/
theorem compIsoCongr_eq {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂} (hp : p = p')
    (hq : q = q') (hpq : pq = pq') (P : p ⋙ q ≅ pq) :
    compIsoCongr hp hq hpq P =
      eqToIso (congrArg₂ (fun (a : A₀ ⥤ A₁) (b : A₁ ⥤ A₂) ↦ a ⋙ b) hp.symm hq.symm) ≪≫ P ≪≫
        eqToIso hpq :=
  rfl

/-- **Transporting a composition comparison along equalities of functors preserves the
associativity cocycle law.**  Written at a single object, which is the form the underlying
cocycle law is available in. -/
theorem compIsoCongr_cocycle {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {r r' : A₂ ⥤ A₃}
    {pq pq' : A₀ ⥤ A₂} {qr qr' : A₁ ⥤ A₃} {pqr pqr' : A₀ ⥤ A₃} (hp : p = p') (hq : q = q')
    (hr : r = r') (hpq : pq = pq') (hqr : qr = qr') (hpqr : pqr = pqr') (P : p ⋙ q ≅ pq)
    (Q : q ⋙ r ≅ qr) (PQ : pq ⋙ r ≅ pqr) (QR : p ⋙ qr ≅ pqr)
    (hcoc : ∀ N, r.map (P.hom.app N) ≫ PQ.hom.app N = Q.hom.app (p.obj N) ≫ QR.hom.app N)
    (N : A₀) :
    r'.map ((compIsoCongr hp hq hpq P).hom.app N) ≫
        (compIsoCongr hpq hr hpqr PQ).hom.app N =
      (compIsoCongr hq hr hqr Q).hom.app (p'.obj N) ≫
        (compIsoCongr hp hqr hpqr QR).hom.app N := by
  subst hp
  subst hq
  subst hr
  subst hpq
  subst hqr
  subst hpqr
  simpa [compIsoCongr] using hcoc N

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS}

/-- **The comparison of direct images of modules of Stacks 03LU is the comparison at the level
of the morphisms of ringed topoi of Stacks 03G8**, transported along the identifications
`AlgebraicGeometry.Space.pushforwardModules_eq_modulePushforward` of the two direct images.

The two sides differ by one reassociation of the four factors, and nothing is projected to the
level of morphisms, which is what keeps the transports from being reduced. -/
theorem modulePushforwardCompIso_eq_compIsoCongr (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforwardCompIso B S hS f g =
      Functor.compIsoCongr (pushforwardModules_eq_modulePushforward B S hS f)
        (pushforwardModules_eq_modulePushforward B S hS g)
        (pushforwardModules_eq_modulePushforward B S hS (f ≫ g))
        (pushforwardModulesCompAt B S hS f g) :=
  congrArg (fun t ↦ eqToIso (modulePushforward_comp_eq B S hS f g) ≪≫ t)
    (Iso.trans_assoc
      (RingedToposHom.pushforwardModulesCompIso (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS g)).symm
      (pushforwardModulesCompTransport B S hS f g)
      (eqToIso (pushforwardModules_eq_modulePushforward B S hS (f ≫ g)))).symm

end AlgebraicGeometry.Space

end

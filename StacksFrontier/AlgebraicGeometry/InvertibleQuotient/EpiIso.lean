module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.KernelBaseChange

/-!
# A surjection between invertible sheaves of modules is an isomorphism

Let `X` be a ringed space and `q : E ⟶ L` a surjection of sheaves of `𝒪_X`-modules with `E` and
`L` both invertible. Then `q` is an isomorphism, with no further hypothesis.

The argument is the stalkwise one of
`StacksFrontier/AlgebraicGeometry/InvertibleQuotient/KernelBaseChange.lean`, taken one step
further. Monomorphisms of sheaves of modules are detected on stalks; the stalk of an invertible
sheaf of modules is an invertible module over the local ring
(`Stacks.SheafOfModules.module_invertible_grpStalk_of_isInvertible`); and Mathlib's
`Module.Invertible.bijective_of_surjective` says a surjection between two invertible modules over
a commutative ring is bijective. So `q` is a monomorphism, and sheaves of modules form a balanced
category, so a morphism that is both a monomorphism and an epimorphism is invertible.

No local triviality of either module, no cover and no gluing is used; only the stalk pairing.

## Main results

* `Stacks.SheafOfModules.isIso_of_epi_of_isInvertible`: the statement above, on a ringed space.
* `Stacks.Divisors.isIso_q_of_isInvertible`: **an invertible quotient of an invertible module on a
  scheme is an isomorphism.** This is the form Tag 0B3V's bijection consumes: it says the
  invertible quotients of an invertible `E` form a single isomorphism class, the one of `𝟙 E`.
* `Stacks.Divisors.subsingleton_invertibleQuotientClass_of_isInvertible`: that consequence,
  stated as the isomorphism classes of invertible quotients of an invertible module being a
  subsingleton.

## Implementation notes

**The two invertibility predicates, crossed once in each direction and no further.**
`Stacks.Divisors.InvertibleQuotient.invertible` records
`AlgebraicGeometry.SheafOfModules.IsInvertible`, while the stalk API consumes
`Stacks.SheafOfModules.IsInvertible`; the crossing is
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, used twice in one proof and
restating nothing. Inside `namespace Stacks.SheafOfModules` the bare name `IsInvertible` resolves
silently to the enclosing namespace's constant, so both binders below are written out in full
(as `set_option pp.fullNames true` confirms).

**Why the scheme-level statement applies the ringed-space one with `@`.**
`AlgebraicGeometry.Scheme.Modules` is a plain `def` carrying its own `Category` instance, so
`Epi Q.q` and the two invertibility hypotheses are not found by synthesis at the
`SheafOfModules (structureSheafRing X.toRingedSpace)` spelling even with proofs
of them in context; supplied explicitly they are accepted, the two spellings being definitionally
equal. This is the pattern `Stacks.Divisors.mono_pullback_map_kernel_ι` already uses.

**No tag is attached.** Tag 0B3V states a bijection between sections of `𝐏(E) ⟶ X` and invertible
quotients of `E`; this is a lemma about invertible quotients used in measuring that bijection at
rank one, and it is not a clause of any tag.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

/-- **A surjection between two invertible sheaves of modules on a ringed space is an
isomorphism.** At every stalk it is a surjection between invertible modules over the local ring,
hence bijective by `Module.Invertible.bijective_of_surjective`; monomorphisms are detected on
stalks, and the category of sheaves of modules is balanced. -/
theorem isIso_of_epi_of_isInvertible (X : AlgebraicGeometry.RingedSpace.{u, u})
    {E L : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (q : E ⟶ L) [Epi q]
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property E]
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property L] :
    IsIso q := by
  have hmono : Mono q := by
    apply AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono
    intro x
    let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X E.val x
    let := Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X L.val x
    have hE := module_invertible_grpStalk_of_isInvertible X E x
    have hL := module_invertible_grpStalk_of_isInvertible X L x
    have hepi : Epi ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing X) x).map q) :=
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (structureSheafRing X) x).map_epi q
    have hsurj : Function.Surjective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL X E.val
      L.val q.val x) :=
      (ModuleCat.epi_iff_surjective _).mp hepi
    have hbij := Module.Invertible.bijective_of_surjective hsurj
    exact (ModuleCat.mono_iff_injective _).mpr hbij.injective
  exact isIso_of_mono_of_epi q

end Stacks.SheafOfModules

namespace Stacks.Divisors

/-- **An invertible quotient of an invertible module on a scheme is an isomorphism.** So an
invertible module has exactly one invertible quotient up to isomorphism over it, the identity. -/
theorem isIso_q_of_isInvertible {X : Scheme.{u}} {E : X.Modules}
    (hE : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E)
    (Q : InvertibleQuotient X E) : IsIso Q.q := by
  have hq : Epi Q.q := Q.epi
  have hEs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hE
  have hLs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 Q.L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr Q.invertible
  exact @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible X.toRingedSpace E Q.L Q.q hq hEs hLs

/-- **The invertible quotients of an invertible module form a single isomorphism class.** Each
quotient map is an isomorphism, so each quotient is equivalent over `E` to the identity one. -/
theorem subsingleton_invertibleQuotientClass_of_isInvertible {X : Scheme.{u}} {E : X.Modules}
    (hE : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 E) :
    Subsingleton (InvertibleQuotientClass X E) := by
  refine ⟨Quotient.ind₂ fun Q R => Quotient.sound ?_⟩
  have hQ := isIso_q_of_isInvertible hE Q
  have hR := isIso_q_of_isInvertible hE R
  exact ⟨(asIso Q.q).symm ≪≫ asIso R.q, Iso.hom_inv_id_assoc (asIso Q.q) R.q⟩

end Stacks.Divisors

end

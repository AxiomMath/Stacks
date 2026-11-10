module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompositionGeneral
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatBaseChangeUnconditional
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof

/-!
# Composing algebraic upper shriek along two finite-type homomorphisms

Let `a : R →+* A` and `b : A →+* B` be homomorphisms of finite type with `R` Noetherian.
`StacksFrontier.RingTheory.Dualizing.UpperShriek.CompositionGeneral` builds the transformation

`b^! ∘ a^! ⟶ (b ∘ a)^!`

of [Stacks, Tag 0BZT] at a presentation `p` of `a`, a presentation `q` of `b` and the induced
presentation `p.comp q` of `b ∘ a`, with no hypothesis at all, and reduces its invertibility at
`K` to a single instance of the base-change comparison of [Stacks, Tag 0E29]: the one at the
square `P, A, P[y_1, …, y_m], A ⊗_P P[y_1, …, y_m]` of the presentation `p` with the `m`
variables of `q` adjoined, read at `K ⊗_R^L P`.

This file discharges that instance from the flat case of [Stacks, Tag 0BZM] and so proves
[Stacks, Tag 0BZT] — the transformation of functors together with its being an isomorphism on
`D⁺(R)` — at arbitrary presentations of `a`, of `b` and of `b ∘ a`.

## Main results

* `Dualizing.PolynomialPresentation.isIso_polynomialDerivedHomBaseChange_app` — the instance of
  [Stacks, Tag 0BZM] that the composition needs: the base-change morphism of
  `Dualizing.polynomialDerivedHomBaseChange` is invertible at every bounded-below object of
  `D(P)`.
* `Dualizing.PolynomialPresentation.exists_upperShriekComp_isIso_of_isBoundedBelow` — Tag 0BZT
  at the induced presentation `p.comp q` of the composite.
* `Dualizing.PolynomialPresentation.exists_upperShriekComp_of_finiteType` — **[Stacks, Tag 0BZT]**:
  both maps of finite type, at arbitrary presentations of all three.

## Implementation notes

### What the Noetherian hypothesis is for

The flat case of [Stacks, Tag 0BZM] asks that `A` be pseudo-coherent as a `P`-module.  It holds
because `A` is a finite `P`-module, `p.toRingHom` being surjective, and `P = R[x_1, …, x_n]` is
Noetherian when `R` is.  That is the only use of `IsNoetherianRing R`, and the source asks for
it too — Tag 0BZT is stated there for finite-type homomorphisms of Noetherian rings.  The other
hypotheses are free: `P[y_1, …, y_m]` is flat over `P`, so the square is Tor independent, and
`K ⊗_R^L P` is bounded below with `K` by
`Dualizing.PolynomialPresentation.derivedExtension_isBoundedBelow`.

The flat case of Tag 0BZM used is
`Dualizing.isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge`, which is proved on cohomology
and needs no compatibility of projection formulas.

### Why the surjective case is not subsumed

`Dualizing.upperShriekFunctor_comp_of_surjective` gives, for a surjective second map, an
isomorphism on all of `D(R)` and not merely on `D⁺(R)`, with no Noetherian hypothesis: a
surjection has no polynomial variables to move past the first `RHom`, so no base-change
comparison enters its proof.

### Form of the statement

The transformation is produced as the witness of an existential rather than named, matching
`Dualizing.PolynomialPresentation.exists_upperShriekComp`: it is built from derived Hom
adjunctions and shift compatibilities that are themselves only known to exist, so no particular
transformation is canonical.  Boundedness below is `Dualizing.DerivedCategoryB.IsBoundedBelow`,
the form `Dualizing.PolynomialPresentation.derivedExtension_isBoundedBelow` takes.

The three rings live in one universe `u` and the modules in an arbitrary universe `max v u`, as
in `Dualizing.PolynomialPresentation.upperShriekFunctor`.

## References

* [Stacks Project, Tag 0BZT](https://stacks.math.columbia.edu/tag/0BZT)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

attribute [local instance 2000] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

namespace PolynomialPresentation

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

/-- **The instance of [Stacks, Tag 0BZM] that the composition of upper shriek needs.**  Let `p`
present `a : R →+* A` with polynomial algebra `P`, let `m : ℕ`, and let `R` be Noetherian.  Then
the base-change morphism of [Stacks, Tag 0E29] at the square
`P, A, P[y_1, …, y_m], A ⊗_P P[y_1, …, y_m]`, namely
`Dualizing.polynomialDerivedHomBaseChange`, is invertible at every `M` in `D(P)` bounded below.

This is the flat case of [Stacks, Tag 0BZM]: the polynomial algebra `P[y_1, …, y_m]` is flat over
`P`, hence Tor independent from `A` over `P`, and `A` is pseudo-coherent over `P` because it is a
finite `P`-module over a Noetherian ring. -/
theorem isIso_polynomialDerivedHomBaseChange_app [IsNoetherianRing R] {a : R →+* A}
    (p : PolynomialPresentation a) (m : ℕ)
    {K : DerivedCategory (ModuleCat.{max v u} R)} (hK : DerivedCategoryB.IsBoundedBelow K) :
    IsIso ((polynomialDerivedHomBaseChange.{u, v} p m).app (p.derivedExtension.{u, v}.obj K)) := by
  let : Algebra p.Poly A := p.toRingHom.toAlgebra
  have hT : (algebraMap p.Poly (MvPolynomial (Fin m) p.Poly)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hA : (algebraMap A (TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly))).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have hTor : RingTheory.TorIndependence.TorIndependent p.Poly A
      (MvPolynomial (Fin m) p.Poly) :=
    torIndependent_of_flat_right (R := p.Poly) (A := A) (B := MvPolynomial (Fin m) p.Poly)
  have hFin : Module.Finite p.Poly A := p.finite_toRingHom
  have hPC : StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := p.Poly) A :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (R := p.Poly) ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
        (ModuleCat.of p.Poly p.Poly)) 0 A).2.2).2 hFin
  have key : polynomialDerivedHomBaseChange.{u, v} p m =
      derivedHomBaseChange.{u, u, u, v} hTor
        (flatDerivedExtensionLarge.{u, v} (algebraMap p.Poly (MvPolynomial (Fin m) p.Poly)) hT)
        (flatDerivedExtensionLargeFactors.{u, v} (algebraMap p.Poly (MvPolynomial (Fin m) p.Poly))
          hT)
        (flatDerivedExtensionLarge_isLeftDerived.{u, v}
          (algebraMap p.Poly (MvPolynomial (Fin m) p.Poly)) hT)
        (flatDerivedExtensionLarge.{u, v}
          (algebraMap A (TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly))) hA)
        (flatDerivedExtensionLargeFactors.{u, v}
          (algebraMap A (TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly))) hA)
        (flatDerivedExtensionLarge_isLeftDerived.{u, v}
          (algebraMap A (TensorProduct p.Poly A (MvPolynomial (Fin m) p.Poly))) hA) := rfl
  rw [key]
  obtain ⟨c, hc⟩ := p.derivedExtension_isBoundedBelow.{u, v} hK
  exact isIso_derivedHomBaseChange_app_of_flat_flatModelsLarge.{u, v} hTor hT hA
    (isPseudoCoherent_singleULiftAlgebra.{u, u, v} hPC) _ c ((DerivedCategory.isGE_iff _ c).2 hc)

/-- **[Stacks, Tag 0BZT] at the induced presentation of the composite.**  Let `a : R →+* A` and
`b : A →+* B` be of finite type with `R` Noetherian, presented by `p` and by `q`.  Then there is a
transformation

`b^!(a^!(K)) ⟶ (b ∘ a)^!(K)`

of functors `D(R) ⥤ D(B)`, upper shriek being read at `p`, at `q` and at the induced presentation
`p.comp q`, and it is an isomorphism at every bounded-below `K`.

The transformation is the one of `Dualizing.PolynomialPresentation.exists_upperShriekComp`, built
with no hypothesis; what is added here is its invertibility, whose single antecedent there is
discharged by `Dualizing.PolynomialPresentation.isIso_polynomialDerivedHomBaseChange_app`. -/
theorem exists_upperShriekComp_isIso_of_isBoundedBelow [IsNoetherianRing R] {a : R →+* A}
    {b : A →+* B} (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) :
    ∃ τ : p.upperShriekFunctor.{u, v} ⋙ q.upperShriekFunctor.{u, v} ⟶
        (p.comp q).upperShriekFunctor.{u, v},
      ∀ K : DerivedCategory (ModuleCat.{max v u} R), DerivedCategoryB.IsBoundedBelow K →
        IsIso (τ.app K) := by
  obtain ⟨τ, hτ⟩ := p.exists_upperShriekComp q
  exact ⟨τ, fun K hK =>
    hτ K (isIso_polynomialDerivedHomBaseChange_app p q.variableCount hK)⟩

/-- **Stacks Project, Tag 0BZT.**  Let `a : R →+* A` and `b : A →+* B` be homomorphisms of finite
type with `R` Noetherian, let `p` be any polynomial presentation of `a`, `q` any polynomial
presentation of `b` and `r` any polynomial presentation of `b ∘ a`.  Then there is a
transformation of functors

`b^! ∘ a^! ⟶ (b ∘ a)^!`

upper shriek being read at `p`, at `q` and at `r` and modules taken in any universe `max v u`,
which is an isomorphism at every object of `D⁺(R)`.  The Noetherian hypothesis is needed on `R`
only; it passes to the polynomial algebras, which is all the proof uses.

It is `Dualizing.PolynomialPresentation.exists_upperShriekComp_isIso_of_isBoundedBelow`, which
states it at the induced presentation `p.comp q` of the composite, transported to an arbitrary `r`
along the independence of the presentation, [Stacks, Tag 0BZJ],
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`. -/
@[stacks 0BZT]
theorem exists_upperShriekComp_of_finiteType [IsNoetherianRing R] {a : R →+* A} {b : A →+* B}
    (p : PolynomialPresentation a)
    (q : PolynomialPresentation b) (r : PolynomialPresentation (b.comp a)) :
    ∃ τ : p.upperShriekFunctor.{u, v} ⋙ q.upperShriekFunctor.{u, v} ⟶
        r.upperShriekFunctor.{u, v},
      ∀ K : DerivedCategory (ModuleCat.{max v u} R), DerivedCategoryB.IsBoundedBelow K →
        IsIso (τ.app K) := by
  obtain ⟨τ, hτ⟩ := exists_upperShriekComp_isIso_of_isBoundedBelow p q
  obtain ⟨e⟩ := nonempty_upperShriekFunctor_iso.{u, v} (b.comp a) (p.comp q) r
  refine ⟨τ ≫ e.hom, fun K hK => ?_⟩
  have hτK : IsIso (τ.app K) := hτ K hK
  change IsIso (τ.app K ≫ e.hom.app K)
  exact IsIso.comp_isIso' hτK inferInstance

end PolynomialPresentation

end

end Dualizing

end

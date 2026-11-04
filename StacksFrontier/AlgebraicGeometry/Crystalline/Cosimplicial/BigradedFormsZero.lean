module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamDegreeZero
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeForms

/-!
# The exterior degree zero slice of the bigraded family `Ω^a_{D(b)}`

The double complex `K^{a,b}` of [Stacks, Proposition 60.21.3, Tag 07LG] is read on two edges, and
one of them is the column `a = 0`.  This module records what that column of the *forms* is:
**in exterior degree zero the bigraded family is the cosimplicial ring `D(*)` itself**, transition
maps included.

The degree-zero statement for a single divided power ring is
`Crystalline.completedDividedPowerFormsZeroEquiv` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamDegreeZero.lean`; what is added here is
that the identification is compatible with the transition maps of a
`Crystalline.CosimplicialDPAlgebra`, hence of the actual cosimplicial envelope `D(*)` of
[Stacks, Equation 60.17.3, Tag 07JF].  Compatibility is stated on the `p`-adically dense image of
the uncompleted forms, which is where the transition maps of both sides are computed from the
uncompleted ones — `Crystalline.completedMapDifferentialForms_of` on the one side and
`Crystalline.adicCompletionRingMap_of` on the other.

## Main definitions

* `Crystalline.CosimplicialDPAlgebra.formsZeroEquiv` — **`Ω^0_{D(b)} ≅ D(b)`** for a cosimplicial
  family of divided power algebras.
* `Crystalline.envelopeFormsZeroEquiv` — the same for the actual cosimplicial envelope.

## Main results

* `Crystalline.CosimplicialDPAlgebra.formsZeroEquiv_formsMap_of` and
  `Crystalline.envelopeFormsZeroEquiv_formsMap_of` — **the transition maps of the forms in
  exterior degree zero are the transition maps of the ring**, on the dense image of the
  uncompleted forms.

No tag attribute is placed: this is a step inside the proof of [Stacks, Tag 07LG] and is not the
statement of a tag.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
-/

@[expose] public section

open CategoryTheory DividedPowers

universe u v w

namespace Crystalline

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **`Ω^0_{D(b)} ≅ D(b)`**: in exterior degree zero the bigraded family of a cosimplicial family
of divided power algebras is the cosimplicial ring. -/
public noncomputable def formsZeroEquiv (b : ℕ) :
    E.forms p 0 b ≃ₗ[completedDividedPowerRing p (B := E.carrier b)]
      completedDividedPowerRing p (B := E.carrier b) :=
  completedDividedPowerFormsZeroEquiv p A (E.dividedPowers b)

/-- **In exterior degree zero the transition maps of the forms are the transition maps of the
ring**, on the `p`-adically dense image of the uncompleted forms.  So the slice `a = 0` of the
bigraded family `Ω^a_{D(b)}` is the cosimplicial ring `D(*)` and nothing else. -/
public theorem formsZeroEquiv_formsMap_of {m n : SimplexCategory} (phi : m ⟶ n)
    (omega : dividedPowerDifferentialForms (A := A) (E.dividedPowers m.len) 0) :
    E.formsZeroEquiv p n.len (E.formsMap p phi 0
        (AdicCompletion.of (pAdicIdeal (A := E.carrier m.len) p) _ omega)) =
      AdicCompletion.of (pAdicIdeal (A := E.carrier n.len) p) _
        (E.map phi (exteriorPower.zeroEquiv (E.carrier m.len)
          (dividedPowerDifferentials (A := A) (E.dividedPowers m.len)) omega)) :=
  completedDividedPowerFormsZeroEquiv_completedMap_of p A (E.dividedPowers m.len)
    (E.dividedPowers n.len) (E.map phi) (E.map_isDPMorphism phi) omega

end CosimplicialDPAlgebra

/-! ### The cosimplicial envelope -/

section Envelope

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **`Ω^0_{D(b)} ≅ D(b)` for the actual cosimplicial envelope** of a polynomial presentation. -/
public noncomputable def envelopeFormsZeroEquiv (b : ℕ) :
    envelopeForms s f 0 b ≃ₗ[completedDividedPowerRing s.p
        (B := (envelopeDPAlgebra s f).carrier b)]
      completedDividedPowerRing s.p (B := (envelopeDPAlgebra s f).carrier b) :=
  (envelopeDPAlgebra s f).formsZeroEquiv s.p b

/-- **The transition maps of `Ω^0_{D(*)}` are the transition maps of `D(*)`**, for the actual
cosimplicial envelope. -/
public theorem envelopeFormsZeroEquiv_formsMap_of {m n : SimplexCategory} (phi : m ⟶ n)
    (omega : dividedPowerDifferentialForms (A := (s.A : Type u))
      ((envelopeDPAlgebra s f).dividedPowers m.len) 0) :
    envelopeFormsZeroEquiv s f n.len (envelopeFormsMap s f phi 0
        (AdicCompletion.of
          (pAdicIdeal (A := (envelopeDPAlgebra s f).carrier m.len) s.p) _ omega)) =
      AdicCompletion.of (pAdicIdeal (A := (envelopeDPAlgebra s f).carrier n.len) s.p) _
        ((envelopeDPAlgebra s f).map phi
          (exteriorPower.zeroEquiv ((envelopeDPAlgebra s f).carrier m.len)
            (dividedPowerDifferentials (A := (s.A : Type u))
              ((envelopeDPAlgebra s f).dividedPowers m.len)) omega)) :=
  (envelopeDPAlgebra s f).formsZeroEquiv_formsMap_of s.p phi omega

end Envelope

end Crystalline

end

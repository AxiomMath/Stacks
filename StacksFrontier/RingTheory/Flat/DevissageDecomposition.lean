module

public import StacksFrontier.RingTheory.Flat.DevissageFlatTfae
public import StacksFrontier.RingTheory.Flat.DevissageTail
public import StacksFrontier.RingTheory.Flat.GeometricallyIrreducibleFibreLocus
public import StacksFrontier.RingTheory.Module.Kaplansky
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# The conclusions of Stacks 05I4 for a complete dévissage at a prime

Stacks 05I4 says that a finite module `N` over a finitely presented algebra `S` of a local ring
`R`, flat at a prime `q` over the closed point and carrying a complete dévissage at `q`, is

* finitely presented over `S`,
* free as an `R`-module, and
* isomorphic as an `R`-module to `⨁ᵢ Bᵢ^(⊕ rᵢ)`, the `Bᵢ` being the smooth lower algebras of
  the dévissage.

`StacksFrontier.RingTheory.Flat.DevissageTail` proves the first and third conclusions for a
`Module.CompleteDevissage`, that is for a dévissage *over* a prime of the base, taking as
hypotheses the injectivity of the maps `alphaᵢ` and the `R`-projectivity of the `Bᵢ`. This file

* transports all three conclusions to a `Module.CompleteDevissageAt`, a dévissage *at* a prime of
  `S`, which is the form Stacks 05I4 is stated in and which also allows the empty dévissage of
  the zero module, and
* discharges both of those hypotheses as far as the library currently allows: the projectivity
  from Stacks 05FT and Stacks 056T, and the injectivity from Stacks 05I3 applied at every stage.

## Main results

* `Module.CompleteDevissageAt.nonempty_linearEquiv_directSum` is the decomposition.
* `Module.CompleteDevissageAt.finitePresentation` is finite presentation over `S`.
* `Module.CompleteDevissageAt.free` is freeness over a local base.
* `Module.CompleteDevissage.projective_lowerAlgebra` discharges the projectivity hypothesis of
  those three.
* `Module.CompleteDevissage.injective_alpha` and
  `Module.NonemptyCompleteDevissageAt.injective_alpha` reduce the injectivity hypothesis to
  flatness over `R` of the localization of every stage module at its stage prime.

## Implementation notes

The empty dévissage has no stages, so its direct sum is indexed by `Fin 0` and both sides of the
decomposition are subsingletons; the zero module is free and finitely presented, so all three
conclusions are immediate there. For a nonempty dévissage the stage data, the number of stages,
the lower algebras and the multiplicities of `Module.CompleteDevissageAt` are by definition those
of the underlying `Module.CompleteDevissage`, so the three results of
`StacksFrontier.RingTheory.Flat.DevissageTail` apply with no transport.

The injectivity hypothesis concerns the maps `alphaᵢ`, which are carried by the underlying
`Module.CompleteDevissage` and not exposed on `Module.CompleteDevissageAt`; it is therefore
phrased for the stage data of the nonempty constructor and is vacuous for the empty one.

### What the two hypotheses now rest on

Projectivity of the `Bᵢ` is Stacks 05FT applied to the smooth lower algebras, and
`Module.CompleteDevissage.projective_lowerAlgebra` carries that application out with nothing
left over. Its two inputs are both theorems of the library:

* constructibility of the geometrically *reduced* fibre locus over a Noetherian base, the affine
  case of Stacks 0579, is
  `Algebra.isConstructible_geometricallyReducedFibreLocus'`, and together with the
  geometrically *irreducible* half — the affine case of the level set `n = 1` of Stacks 055B —
  it gives `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_finiteType`, and
* Stacks 056T, that a smooth morphism of schemes has geometrically reduced fibres, is
  `AlgebraicGeometry.geometricallyReduced_of_smooth`; it is what upgrades the geometrically
  *irreducible* fibres recorded by a dévissage to geometrically *integral* ones.

Injectivity of the `alphaᵢ` is the implication (1) ⟹ (3) of Stacks 05I3 at stage `i`, available
in the universes a dévissage needs it in as
`Module.injective_of_flat_localizedModule_of_projective_finsupp`. Its remaining input is
flatness over `R` of `(Mᵢ)_{𝔮ᵢ}`, which Stacks 05I4 obtains by a downward recursion on the
stages: flatness of `N_𝔮` gives it at stage zero, and Stacks 05I3 then hands flatness of the
localized cokernel, which is the next stage module, to the following step. That recursion is not
formalized here, so stagewise flatness appears as the hypothesis `hflat`.

## References

* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 055B](https://stacks.math.columbia.edu/tag/055B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat
open scoped DirectSum

universe u v w

namespace Module

namespace CompleteDevissage

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {r : Ideal R} [r.IsPrime]

/-- **The projectivity hypothesis of Stacks 05I4, discharged.** Every lower algebra of a complete
dévissage is projective over the base.

The lower algebras are smooth over the base, hence flat and of finite presentation, and their
fibres are geometrically irreducible by definition of a dévissage; Stacks 056T
(`AlgebraicGeometry.geometricallyReduced_of_smooth`) upgrades that to geometrically integral
fibres, which is the hypothesis of Stacks 05FT. Stacks 05FT itself needs constructibility of the
geometrically integral fibre locus over a Noetherian base, whose reduced half is the affine case
of Stacks 0579 (`Algebra.isConstructible_geometricallyReducedFibreLocus'`) and whose
irreducible half is the affine case of the level set `n = 1` of Stacks 055B
(`Algebra.isConstructible_geometricallyIrreducibleFibreLocus_of_finiteType`). -/
public theorem projective_lowerAlgebra
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Module.Projective R (D.B i) := by
  have hsmooth : Smooth (Spec.map (ofHom (algebraMap R (D.B i)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 inferInstance)
  have : GeometricallyReduced (Spec.map (ofHom (algebraMap R (D.B i)))) :=
    geometricallyReduced_of_smooth _
  have : GeometricallyIntegral (Spec.map (ofHom (algebraMap R (D.B i)))) :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  exact Algebra.projective_of_flat_of_geometricallyIntegral_of_isConstructible
    (fun R₀ S₀ _ _ _ _ _ _ =>
      Algebra.isConstructible_geometricallyIntegralFibreLocus_of_finiteType R₀ S₀)

/-- **The injectivity hypothesis of Stacks 05I4, reduced to stagewise flatness.** Let `R` be a
local ring and let `D` be a complete dévissage over its maximal ideal. Fix a prime `p i` of every
lower algebra lying over the maximal ideal. If every lower algebra is projective over `R` and
every stage module becomes `R`-flat after localizing at the prime of its stage, then every map
`alpha i` of the dévissage is injective.

This is the implication (1) ⟹ (3) of Stacks 05I3 applied at each stage, in the form
`Module.injective_of_flat_localizedModule_of_projective_finsupp`. The ideal `𝔪 Bᵢ` is prime
because a dévissage records it as such, and the stage modules are finite over the lower algebras
because they are finite over the upper ones and `Bᵢ → Aᵢ` is finite. -/
public theorem injective_alpha [IsLocalRing R]
    (D : CompleteDevissage R S N r) (hr : r = IsLocalRing.maximalIdeal R)
    (hproj : ∀ i, Module.Projective R (D.B i))
    (p : ∀ i, Ideal (D.B i)) (hp : ∀ i, (p i).IsPrime)
    (hp_under : ∀ i, (p i).comap (algebraMap R (D.B i)) = IsLocalRing.maximalIdeal R)
    (hflat : ∀ i,
      letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
      letI : Module R (D.M i) := Module.compHom (D.M i) (algebraMap R (D.A i))
      letI : IsScalarTower R (D.B i) (D.M i) :=
        Module.isScalarTower_compHom R (D.B i) (D.A i) (D.M i) (D.toLeft i)
      Module.Flat R (LocalizedModule (p i).primeCompl (D.M i)))
    (i : Fin (D.stepCount + 1)) :
    letI : Module (D.B i) (D.M i) := Module.compHom (D.M i) (D.toLeft i).toRingHom
    Function.Injective (D.alpha i) := by
  subst hr
  let : ∀ j, Module (D.B j) (D.M j) := fun j =>
    Module.compHom (D.M j) (D.toLeft j).toRingHom
  let : ∀ j, Module R (D.M j) := fun j =>
    Module.compHom (D.M j) (algebraMap R (D.A j))
  let : ∀ j, IsScalarTower R (D.B j) (D.M j) := fun j =>
    Module.isScalarTower_compHom R (D.B j) (D.A j) (D.M j) (D.toLeft j)
  let : ∀ j, Algebra (D.B j) (D.A j) := fun j => (D.toLeft j).toRingHom.toAlgebra
  let : ∀ j, IsScalarTower (D.B j) (D.A j) (D.M j) := fun j =>
    ⟨fun b a m => by change (D.toLeft j b * a) • m = D.toLeft j b • (a • m); rw [mul_smul]⟩
  let : ∀ j, Module.Finite (D.B j) (D.A j) := fun j =>
    RingHom.finite_algebraMap.mp (D.left_finite j)
  let : ∀ j, Module.Finite (D.B j) (D.M j) := fun j => Module.Finite.trans (D.A j) (D.M j)
  let : ∀ j, Module.Projective R (D.B j) := hproj
  let : (p i).IsPrime := hp i
  let : (Algebra.closedFiberIdeal R (D.B i)).IsPrime := D.map_isPrime i
  exact Module.injective_of_flat_localizedModule_of_projective_finsupp R (D.B i) (p i)
    (hp_under i) (D.M i) (D.multiplicity i) (D.alpha i) (D.fiber_bijective i) (hflat i)

end CompleteDevissage

namespace NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- **The injectivity hypothesis of Stacks 05I4, reduced to stagewise flatness**, for a nonempty
complete dévissage at a prime `q` of `S` over the closed point of a local base. The stage primes
are the ones the dévissage records, and they lie over the maximal ideal because they lie over the
prime below `q`. -/
public theorem injective_alpha [IsLocalRing R] (E : NonemptyCompleteDevissageAt R S N q)
    (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hproj : ∀ i, Module.Projective R (E.toCompleteDevissage.B i))
    (hflat : ∀ i,
      letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
        Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
      letI : Module R (E.toCompleteDevissage.M i) :=
        Module.compHom (E.toCompleteDevissage.M i)
          (algebraMap R (E.toCompleteDevissage.A i))
      letI : IsScalarTower R (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
        Module.isScalarTower_compHom R (E.toCompleteDevissage.B i)
          (E.toCompleteDevissage.A i) (E.toCompleteDevissage.M i)
          (E.toCompleteDevissage.toLeft i)
      Module.Flat R
        (LocalizedModule (E.lowerPrime i).primeCompl (E.toCompleteDevissage.M i)))
    (i : Fin (E.toCompleteDevissage.stepCount + 1)) :
    letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
      Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
    Function.Injective (E.toCompleteDevissage.alpha i) :=
  CompleteDevissage.injective_alpha E.toCompleteDevissage hq hproj E.lowerPrime
    E.lowerPrime_isPrime (fun j => ((E.lowerPrime_liesOver j).over).symm.trans hq) hflat i

end NonemptyCompleteDevissageAt

namespace CompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- **Stacks Project, Tag 05I4, the decomposition**, for a complete dévissage at a prime, with
the injectivity of the maps `alpha i` and the projectivity of the lower algebras as hypotheses
rather than consequences of Stacks 05I3 and Stacks 05FT.

A complete dévissage at `q` whose maps `alpha i` are injective and whose lower algebras are
projective over the base decomposes the original module into the finite free modules
`lowerAlgebra i ^ (⊕ multiplicity i)`. The empty dévissage decomposes the zero module as the
empty direct sum. -/
public theorem nonempty_linearEquiv_directSum [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q)
    (hinj : ∀ E : NonemptyCompleteDevissageAt R S N q, D = .nonempty E → ∀ i,
      letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
        Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
      Function.Injective (E.toCompleteDevissage.alpha i))
    (hproj : ∀ i, Module.Projective R (D.lowerAlgebra i)) :
    Nonempty (N ≃ₗ[R] ⨁ i : Fin D.length, (Fin (D.multiplicity i) →₀ D.lowerAlgebra i)) := by
  cases D with
  | empty hN =>
    have := hN
    let : IsEmpty (Fin (CompleteDevissageAt.empty (R := R) (S := S) (N := N) (q := q) hN).length) :=
      show IsEmpty (Fin 0) from inferInstance
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  | nonempty E =>
    exact CompleteDevissage.nonempty_linearEquiv_directSum E.toCompleteDevissage
      (hinj E rfl) hproj

/-- **Stacks Project, Tag 05I4, finite presentation**, for a complete dévissage at a prime, with
the injectivity of the maps `alpha i` as a hypothesis rather than a consequence of Stacks 05I3.

A finite module over a finitely presented algebra carrying a complete dévissage at a prime
whose maps `alpha i` are injective is finitely presented. The empty dévissage presents the zero
module. -/
public theorem finitePresentation [Algebra.FinitePresentation R S]
    (D : CompleteDevissageAt R S N q)
    (hinj : ∀ E : NonemptyCompleteDevissageAt R S N q, D = .nonempty E → ∀ i,
      letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
        Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
      Function.Injective (E.toCompleteDevissage.alpha i)) :
    Module.FinitePresentation S N := by
  cases D with
  | empty hN =>
    have := hN
    exact (LinearEquiv.finitePresentation_iff
      (LinearEquiv.ofSubsingleton (Fin 0 → S) N)).mp inferInstance
  | nonempty E =>
    exact CompleteDevissage.finitePresentation_of_injective_alpha E.toCompleteDevissage
      (hinj E rfl)

/-- **Stacks Project, Tag 05I4, freeness over the base**, for a complete dévissage at a prime,
with the injectivity of the maps `alpha i` and the projectivity of the lower algebras as
hypotheses rather than consequences of Stacks 05I3 and Stacks 05FT.

Over a local base the lower algebras are then free, hence so is the direct sum the module
decomposes into. -/
public theorem free [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q)
    (hinj : ∀ E : NonemptyCompleteDevissageAt R S N q, D = .nonempty E → ∀ i,
      letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
        Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
      Function.Injective (E.toCompleteDevissage.alpha i))
    (hproj : ∀ i, Module.Projective R (D.lowerAlgebra i)) :
    Module.Free R N := by
  obtain ⟨e⟩ := nonempty_linearEquiv_directSum D hinj hproj
  let : ∀ i, Module.Projective R (D.lowerAlgebra i) := hproj
  let : ∀ i, Module.Free R (D.lowerAlgebra i) := fun _ =>
    Module.free_of_projective_of_isLocalRing
  exact Module.Free.of_equiv e.symm

end CompleteDevissageAt

end Module

end

module

public import StacksFrontier.RingTheory.Flat.DevissageProjectiveStages

/-!
# Stacks 05I4 over a Noetherian base, with no external input

`StacksFrontier.RingTheory.Flat.DevissageProjectiveStages` proves the three conclusions of
Stacks 05I4 — finite presentation over `S`, freeness over `R`, and the decomposition
`N ≅ ⨁ᵢ Bᵢ^(⊕ rᵢ)` — for a complete dévissage at a prime `q` of `S` over the closed point of a
local ring `R`, granted one hypothesis: constructibility of the geometrically integral fibre
locus of a flat finite type algebra over a Noetherian ring. That hypothesis is the single
remaining argument of Stacks 05FT, and it is used only to obtain projectivity over `R` of the
smooth lower algebras `Bᵢ`.

**Over a Noetherian base that hypothesis is not needed**, because the Noetherian case of
Stacks 05FT is Stacks 05FS, which is proved:
`Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres`. A lower algebra of a
dévissage is smooth over `R`, hence flat and of finite presentation, and its fibres are
geometrically irreducible by definition of a dévissage and geometrically reduced by Stacks 056T
(`AlgebraicGeometry.geometricallyReduced_of_smooth`), hence geometrically integral. So Stacks 05FS
applies directly and all three conclusions of Stacks 05I4 become unconditional for
`[IsNoetherianRing R]`.

## Main results

* `Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing` and
  `Module.CompleteDevissageAt.projective_lowerAlgebra_of_isNoetherianRing`: every lower algebra of
  a complete dévissage over a Noetherian base is projective over that base, with no hypothesis
  beyond the dévissage.
* `Module.NonemptyCompleteDevissageAt.injective_alpha_of_flat_of_isNoetherianRing`: every map
  `alphaᵢ` is injective, from flatness at `q` alone.
* `Module.CompleteDevissageAt.nonempty_linearEquiv_directSum_of_flat_of_isNoetherianRing`,
  `Module.CompleteDevissageAt.finitePresentation_of_flat_of_isNoetherianRing` and
  `Module.CompleteDevissageAt.free_of_flat_of_isNoetherianRing`: the three conclusions of
  Stacks 05I4 over a Noetherian local base, each with no hypothesis beyond flatness at `q`, the
  dévissage, and `q` lying over the closed point.
* `Module.CompleteDevissageAt.subsingleton_of_length_eq_zero` and
  `Module.CompleteDevissageAt.length_ne_zero_of_not_subsingleton`: the decomposition is degenerate
  only for the zero module.

## Implementation notes

The statements below are *not* tagged `@[stacks 05I4]`. Stacks 05I4 assumes nothing about the base
beyond locality, and tagging a statement that adds `[IsNoetherianRing R]` with the tag of one that
does not would misreport what is proved; the conditional forms in
`StacksFrontier.RingTheory.Flat.DevissageProjectiveStages` are untagged for the same reason, there
because of the hypothesis `hConstr`. Either the general Stacks 05FT or the affine cases of
Stacks 0579 and Stacks 055B turns those into Stacks 05I4; nothing below is needed for that, and
nothing below shrinks that gap. What it does is give the Noetherian case of all three conclusions
with no hypothesis at all beyond the dévissage and flatness at `q`.

### Why the decomposition is not degenerate

The decomposition is stated for a *given* dévissage `D`, and its index set `Fin D.length`, its
multiplicities `D.multiplicity` and its summands `D.lowerAlgebra` are projections of `D`
(`Module.CompleteDevissageAt.length`, `.multiplicity`, `.lowerAlgebra`), each defined by a match
on the constructor of `D` and not by a choice with a fallback. So no degenerate decomposition can
be substituted for the one `D` describes: there is nothing to choose. The one degenerate shape
reachable at all is the empty index set, and `subsingleton_of_length_eq_zero` shows it occurs only
for the empty dévissage, which exists only for the zero module. Equivalently, by
`length_ne_zero_of_not_subsingleton`, a nonzero module has at least one stage, so the conclusion
is an isomorphism onto a nonempty direct sum and the content of the nonempty branch is not
avoidable.

## References

* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
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

/-- **The projectivity hypothesis of Stacks 05I4, discharged over a Noetherian base.** Every
lower algebra of a complete dévissage over a Noetherian base is projective as a module over that
base, with no further hypothesis.

A lower algebra is smooth over `R`, hence flat and of finite presentation, and the morphism it
defines has geometrically irreducible fibres by definition of a dévissage; Stacks 056T makes those
fibres geometrically reduced, hence geometrically integral. Stacks 05FS, the Noetherian case of
Stacks 05FT, then gives projectivity. This is
`Module.CompleteDevissage.projective_lowerAlgebra` with both of its external inputs removed: the
hypothesis `hReduced` by `AlgebraicGeometry.geometricallyReduced_of_smooth`, and the hypothesis
`hConstr` by the Noetherian assumption, which is exactly what `hConstr` was there to supply after
a Noetherian approximation. -/
public theorem projective_lowerAlgebra_of_isNoetherianRing [IsNoetherianRing R]
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Module.Projective R (D.B i) := by
  have hsmooth : Smooth (Spec.map (ofHom (algebraMap R (D.B i)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 (RingHom.smooth_algebraMap.2 inferInstance)
  have : GeometricallyReduced (Spec.map (ofHom (algebraMap R (D.B i)))) :=
    @AlgebraicGeometry.geometricallyReduced_of_smooth _ _ _ hsmooth
  have : GeometricallyIntegral (Spec.map (ofHom (algebraMap R (D.B i)))) :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  exact Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres
    (geometricallyIntegral_algebraMap_iff_residueField.mp ‹_›)

end CompleteDevissage

namespace NonemptyCompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- **The injectivity hypothesis of Stacks 05I4, discharged over a Noetherian local base.** Every
map `alpha i` of a nonempty complete dévissage at `q` is injective as soon as `N_𝔮` is flat
over `R`.

This is `Module.NonemptyCompleteDevissageAt.injective_alpha_of_flat` with its projectivity
hypothesis supplied by
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing`. -/
public theorem injective_alpha_of_flat_of_isNoetherianRing [IsNoetherianRing R] [IsLocalRing R]
    [Module R N] [IsScalarTower R S N]
    (E : NonemptyCompleteDevissageAt R S N q)
    (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N))
    (i : Fin (E.toCompleteDevissage.stepCount + 1)) :
    letI : Module (E.toCompleteDevissage.B i) (E.toCompleteDevissage.M i) :=
      Module.compHom (E.toCompleteDevissage.M i) (E.toCompleteDevissage.toLeft i).toRingHom
    Function.Injective (E.toCompleteDevissage.alpha i) :=
  E.injective_alpha_of_flat hq
    (fun j => CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing
      E.toCompleteDevissage j) hflat i

end NonemptyCompleteDevissageAt

namespace CompleteDevissageAt

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]
  {q : Ideal S} [q.IsPrime]

/-- Every lower algebra of a complete dévissage at a prime over a Noetherian base is projective
over that base, with no further hypothesis. This is
`Module.CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing` transported to a dévissage
*at* a prime; the empty dévissage has no stages. -/
public theorem projective_lowerAlgebra_of_isNoetherianRing [IsNoetherianRing R]
    (D : CompleteDevissageAt R S N q) (i : Fin D.length) :
    Module.Projective R (D.lowerAlgebra i) := by
  cases D with
  | empty hN => exact Fin.elim0 i
  | nonempty E =>
    exact CompleteDevissage.projective_lowerAlgebra_of_isNoetherianRing E.toCompleteDevissage i

/-- **Stacks Project, Tag 05I4, the decomposition, over a Noetherian local base.** A finite module
over a finite type algebra of a Noetherian local ring which is flat over the base at a prime `q`
lying over the closed point and which carries a complete dévissage at `q` decomposes as an
`R`-module into the finite free modules `lowerAlgebra i ^ (⊕ multiplicity i)` of that dévissage.

This is `Module.CompleteDevissageAt.nonempty_linearEquiv_directSum_of_flat` with its hypothesis
`hConstr` removed. -/
public theorem nonempty_linearEquiv_directSum_of_flat_of_isNoetherianRing [IsNoetherianRing R]
    [IsLocalRing R] [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Nonempty (N ≃ₗ[R] ⨁ i : Fin D.length, (Fin (D.multiplicity i) →₀ D.lowerAlgebra i)) :=
  D.nonempty_linearEquiv_directSum
    (fun E _ i => E.injective_alpha_of_flat_of_isNoetherianRing hq hflat i)
    (fun i => D.projective_lowerAlgebra_of_isNoetherianRing i)

/-- **Stacks Project, Tag 05I4, finite presentation, over a Noetherian local base.** This is
`Module.CompleteDevissageAt.finitePresentation_of_flat` with its hypothesis `hConstr` removed. -/
public theorem finitePresentation_of_flat_of_isNoetherianRing [IsNoetherianRing R] [IsLocalRing R]
    [Module R N] [IsScalarTower R S N] [Algebra.FinitePresentation R S]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.FinitePresentation S N :=
  D.finitePresentation (fun E _ i => E.injective_alpha_of_flat_of_isNoetherianRing hq hflat i)

/-- **Stacks Project, Tag 05I4, freeness over the base, over a Noetherian local base.** This is
`Module.CompleteDevissageAt.free_of_flat` with its hypothesis `hConstr` removed. -/
public theorem free_of_flat_of_isNoetherianRing [IsNoetherianRing R] [IsLocalRing R]
    [Module R N] [IsScalarTower R S N]
    (D : CompleteDevissageAt R S N q) (hq : q.under R = IsLocalRing.maximalIdeal R)
    (hflat : Module.Flat R (LocalizedModule q.primeCompl N)) :
    Module.Free R N :=
  D.free (fun E _ i => E.injective_alpha_of_flat_of_isNoetherianRing hq hflat i)
    (fun i => D.projective_lowerAlgebra_of_isNoetherianRing i)

/-- **The decomposition of Stacks 05I4 is degenerate only for the zero module.** A complete
dévissage at a prime with no stages is the empty dévissage, which exists only for a module with
one element.

The direct sum of the decomposition is indexed by `Fin D.length`, so this says that the only way
the conclusion of Stacks 05I4 can be an isomorphism onto an empty direct sum is for `N` to be
zero. -/
public theorem subsingleton_of_length_eq_zero (D : CompleteDevissageAt R S N q)
    (h : D.length = 0) : Subsingleton N := by
  cases D with
  | empty hN => exact hN
  | nonempty E => exact absurd h (Nat.succ_ne_zero _)

/-- **A nonzero module has at least one dévissage stage**, the contrapositive of
`Module.CompleteDevissageAt.subsingleton_of_length_eq_zero`. -/
public theorem length_ne_zero_of_not_subsingleton (D : CompleteDevissageAt R S N q)
    (h : ¬ Subsingleton N) : D.length ≠ 0 :=
  fun hlen => h (D.subsingleton_of_length_eq_zero hlen)

end CompleteDevissageAt

end Module

end

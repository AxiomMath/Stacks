module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksFrontier.RingTheory.Flat.EtaleNeighborhoodProjectiveSections
public import StacksFrontier.RingTheory.Smooth.GeometricallyIrreducibleFibres
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Localizing the base of a complete dévissage at the prime it sits over

Let `B` be an algebra over `R`, let `P` be a submonoid of `R` (typically `r.primeCompl` for a
prime `r`), and let `R'` and `B'` be localizations of `R` at `P` and of `B` at the image of `P`,
with the two scalar towers relating them. Then `B'` is the base change `R' ⊗[R] B`, and
smoothness, finiteness, finite presentation and geometric irreducibility of the fibres pass from
`B/R` to `B'/R'`. For smooth `B` with geometrically irreducible fibres, `B'` is projective over
`R'` and the maximal ideal of `R'` extends to a prime of `B'`. These statements are specialized to
the lower algebras of a complete dévissage.

## Main results

* `Algebra.smooth_of_isLocalization`: smoothness survives.
* `Algebra.finitePresentation_of_isLocalization` and `Module.finite_of_isLocalization`: the two
  finiteness conditions survive.
* `AlgebraicGeometry.geometricallyIrreducible_spec_of_isLocalization`: geometric irreducibility
  of the fibres survives.
* `Module.projective_of_isLocalization_of_smooth`: the localized algebra is projective over the
  localized base.
* `Ideal.map_maximalIdeal_eq_map_map_of_isLocalization` and
  `Ideal.isPrime_map_maximalIdeal_of_isLocalization`: the generic point of the closed fibre of
  the localized algebra is the extension of the generic point `rB` of the fibre over `r`, and it
  is prime.
* `Module.faithfullyFlat_of_geometricallyIrreducible` and
  `Ideal.comap_map_of_geometricallyIrreducible`: a flat algebra with geometrically irreducible
  fibres is faithfully flat, and therefore `rB` contracts to `r`.
* `Algebra.algebraMapSubmonoid_le_primeCompl_map`: the localizing submonoid misses `rB`, so the
  localized algebra is a localization of `B` away from `rB`.
* `Module.CompleteDevissage.smooth_localizedLowerAlgebra`,
  `Module.CompleteDevissage.geometricallyIrreducible_localizedLowerAlgebra`,
  `Module.CompleteDevissage.projective_localizedLowerAlgebra`,
  `Module.CompleteDevissage.map_maximalIdeal_localizedLowerAlgebra`,
  `Module.CompleteDevissage.isPrime_map_maximalIdeal_localizedLowerAlgebra` and
  `Module.CompleteDevissage.algebraMapSubmonoid_le_primeCompl_localizedLowerAlgebra`: the same
  statements for the lower algebra at a stage of a complete dévissage.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 05IB](https://stacks.math.columbia.edu/tag/05IB)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u v w

/-- The square relating an algebra, a localization of its base and the matching localization of
the algebra is a pushout of rings: the localized algebra is the base change. -/
public theorem Algebra.isPushout_of_isLocalization_submonoid (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] (P : Submonoid R) (R' B' : Type u) [CommRing R'] [CommRing B']
    [Algebra R R'] [Algebra B B'] [IsLocalization P R']
    [IsLocalization (Algebra.algebraMapSubmonoid B P) B'] [Algebra R' B'] [Algebra R B']
    [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    Algebra.IsPushout R B R' B' :=
  Algebra.isPushout_of_isLocalization P R' B B'

/-- **Smoothness survives localizing the base.** If `B` is smooth over `R` then the localization
of `B` at the image of a submonoid `P` of `R` is smooth over the localization of `R` at `P`. -/
public theorem Algebra.smooth_of_isLocalization (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.Smooth R B] (P : Submonoid R) (R' B' : Type u) [CommRing R']
    [CommRing B'] [Algebra R R'] [Algebra B B'] [IsLocalization P R']
    [IsLocalization (Algebra.algebraMapSubmonoid B P) B'] [Algebra R' B'] [Algebra R B']
    [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    Algebra.Smooth R' B' :=
  have := Algebra.isPushout_of_isLocalization_submonoid R B P R' B'
  RingHom.smooth_algebraMap.1 (RingHom.Smooth.isStableUnderBaseChange R B R' B'
    (RingHom.smooth_algebraMap.2 inferInstance))

/-- **Finite presentation survives localizing the base.** -/
public theorem Algebra.finitePresentation_of_isLocalization (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B] (P : Submonoid R)
    (R' B' : Type u) [CommRing R'] [CommRing B'] [Algebra R R'] [Algebra B B']
    [IsLocalization P R'] [IsLocalization (Algebra.algebraMapSubmonoid B P) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    Algebra.FinitePresentation R' B' :=
  have := Algebra.isPushout_of_isLocalization_submonoid R B P R' B'
  RingHom.finitePresentation_algebraMap.1
    (RingHom.finitePresentation_isStableUnderBaseChange R B R' B'
      (RingHom.finitePresentation_algebraMap.2 inferInstance))

/-- **Module finiteness survives localizing the base.** -/
public theorem Module.finite_of_isLocalization (R B : Type u) [CommRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] (P : Submonoid R) (R' B' : Type u) [CommRing R']
    [CommRing B'] [Algebra R R'] [Algebra B B'] [IsLocalization P R']
    [IsLocalization (Algebra.algebraMapSubmonoid B P) B'] [Algebra R' B'] [Algebra R B']
    [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    Module.Finite R' B' :=
  have := Algebra.isPushout_of_isLocalization_submonoid R B P R' B'
  RingHom.finite_algebraMap.1 (RingHom.finite_isStableUnderBaseChange R B R' B'
    (RingHom.finite_algebraMap.2 inferInstance))

/-- **Geometrically irreducible fibres survive localizing the base.** If `Spec B → Spec R` has
geometrically irreducible fibres, then so does `Spec B' → Spec R'`. -/
public theorem AlgebraicGeometry.geometricallyIrreducible_spec_of_isLocalization (R B : Type u)
    [CommRing R] [CommRing B] [Algebra R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] (P : Submonoid R)
    (R' B' : Type u) [CommRing R'] [CommRing B'] [Algebra R R'] [Algebra B B']
    [IsLocalization P R'] [IsLocalization (Algebra.algebraMapSubmonoid B P) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap R' B'))) := by
  have hcomm : (algebraMap R' B').comp (algebraMap R R') =
      (algebraMap B B').comp (algebraMap R B) := by
    ext x
    simp [← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Submonoid.map (algebraMap R B) P) B' := ‹_›
  exact MorphismProperty.of_isPullback (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap R B) (algebraMap R' B') hcomm P)) ‹_›

/-- A localization of `R` at the complement of a prime is a local ring. -/
public theorem IsLocalRing.of_isLocalization_primeCompl (R : Type u) [CommRing R] (r : Ideal R)
    [r.IsPrime] (R' : Type u) [CommRing R'] [Algebra R R'] [IsLocalization r.primeCompl R'] :
    IsLocalRing R' :=
  IsLocalization.AtPrime.isLocalRing R' r

/-- **The closed fibre of the localized algebra is the fibre over `r`.** The ideal generated by
the maximal ideal of `R_r` in a localization of `B` at the image of `r.primeCompl` is the
extension to that localization of the ideal `rB`. -/
public theorem Ideal.map_maximalIdeal_eq_map_map_of_isLocalization (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] (r : Ideal R) [r.IsPrime] (R' B' : Type u) [CommRing R']
    [CommRing B'] [IsLocalRing R'] [Algebra R R'] [Algebra B B']
    [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid B r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    Ideal.map (algebraMap R' B') (IsLocalRing.maximalIdeal R') =
      Ideal.map (algebraMap B B') (Ideal.map (algebraMap R B) r) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal r R', Ideal.map_map, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- **The localized algebra is projective over the localized base.** If `B` is smooth over `R`
with geometrically irreducible fibres, then `B'` is a projective `R'`-module. -/
public theorem Module.projective_of_isLocalization_of_smooth (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] (P : Submonoid R)
    (R' B' : Type u) [CommRing R'] [CommRing B'] [Algebra R R'] [Algebra B B']
    [IsLocalization P R'] [IsLocalization (Algebra.algebraMapSubmonoid B P) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    Module.Projective R' B' :=
  have := Algebra.smooth_of_isLocalization R B P R' B'
  have := AlgebraicGeometry.geometricallyIrreducible_spec_of_isLocalization R B P R' B'
  Algebra.projective_of_smooth_of_geometricallyIrreducible R' B'

/-- **The generic point of the closed fibre survives localizing the base.** For a smooth algebra
with geometrically irreducible fibres, the ideal generated in the localized algebra by the
maximal ideal of `R_r` is prime. -/
public theorem Ideal.isPrime_map_maximalIdeal_of_isLocalization (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] (r : Ideal R) [r.IsPrime]
    (R' B' : Type u) [CommRing R'] [CommRing B'] [IsLocalRing R'] [Algebra R R'] [Algebra B B']
    [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid B r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R B B'] :
    (Ideal.map (algebraMap R' B') (IsLocalRing.maximalIdeal R')).IsPrime :=
  have := Algebra.smooth_of_isLocalization R B r.primeCompl R' B'
  have := AlgebraicGeometry.geometricallyIrreducible_spec_of_isLocalization R B r.primeCompl R' B'
  Ideal.isPrime_map_of_smooth_of_geometricallyIrreducible R' B' (IsLocalRing.maximalIdeal R')

/-- **A flat algebra with geometrically irreducible fibres is faithfully flat.** -/
public theorem Module.faithfullyFlat_of_geometricallyIrreducible (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] [Module.Flat R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] :
    Module.FaithfullyFlat R B :=
  have hs : Surjective (Spec.map (ofHom (algebraMap R B))) := inferInstance
  Module.FaithfullyFlat.of_comap_surjective hs.1

/-- **The generic point of the fibre over `r` lies over `r`.** For a flat algebra with
geometrically irreducible fibres the ideal `rB` contracts to `r`. -/
@[ega "0 22.4.8" "special case"]
public theorem Ideal.comap_map_of_geometricallyIrreducible (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] [Module.Flat R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] (r : Ideal R) :
    (Ideal.map (algebraMap R B) r).comap (algebraMap R B) = r :=
  have := Module.faithfullyFlat_of_geometricallyIrreducible R B
  Ideal.comap_map_eq_self_of_faithfullyFlat r

/-- **The localizing submonoid misses the generic point of the fibre.** The image of
`r.primeCompl` in `B` lies in the complement of `rB`, for a flat algebra `B` with geometrically
irreducible fibres. -/
public theorem Algebra.algebraMapSubmonoid_le_primeCompl_map (R B : Type u) [CommRing R]
    [CommRing B] [Algebra R B] [Module.Flat R B]
    [GeometricallyIrreducible (Spec.map (ofHom (algebraMap R B)))] (r : Ideal R) [r.IsPrime]
    [(Ideal.map (algebraMap R B) r).IsPrime] :
    Algebra.algebraMapSubmonoid B r.primeCompl ≤ (Ideal.map (algebraMap R B) r).primeCompl := by
  rintro x ⟨y, hy, rfl⟩ hmem
  exact hy (Ideal.comap_map_of_geometricallyIrreducible R B r ▸ hmem)

namespace Module.CompleteDevissage

/-- The lower algebra of a stage of a complete dévissage stays smooth after localizing the base
at `r`. -/
public theorem smooth_localizedLowerAlgebra {R : Type u} {S : Type v} {N : Type w} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N] [Module S N]
    [Module.Finite S N] {r : Ideal R} [r.IsPrime] (D : CompleteDevissage R S N r)
    (i : Fin (D.stepCount + 1)) (R' B' : Type u) [CommRing R'] [CommRing B'] [Algebra R R']
    [Algebra (D.B i) B'] [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R (D.B i) B'] :
    Algebra.Smooth R' B' :=
  Algebra.smooth_of_isLocalization R (D.B i) r.primeCompl R' B'

/-- The lower algebra of a stage of a complete dévissage keeps its geometrically irreducible
fibres after localizing the base at `r`. -/
public theorem geometricallyIrreducible_localizedLowerAlgebra {R : Type u} {S : Type v}
    {N : Type w} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) (R' B' : Type u) [CommRing R']
    [CommRing B'] [Algebra R R'] [Algebra (D.B i) B'] [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R (D.B i) B'] :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap R' B'))) :=
  AlgebraicGeometry.geometricallyIrreducible_spec_of_isLocalization R (D.B i) r.primeCompl R' B'

/-- The localized lower algebra of a stage of a complete dévissage is projective over the
localization of the base at `r`. -/
public theorem projective_localizedLowerAlgebra {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N]
    [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime] (D : CompleteDevissage R S N r)
    (i : Fin (D.stepCount + 1)) (R' B' : Type u) [CommRing R'] [CommRing B'] [Algebra R R']
    [Algebra (D.B i) B'] [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R (D.B i) B'] :
    Module.Projective R' B' :=
  Module.projective_of_isLocalization_of_smooth R (D.B i) r.primeCompl R' B'

/-- The ideal generated by the maximal ideal of `R_r` in the localized lower algebra of a stage
is the extension of the generic point `rBᵢ` of the fibre over `r`. -/
public theorem map_maximalIdeal_localizedLowerAlgebra {R : Type u} {S : Type v} {N : Type w}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] [AddCommGroup N]
    [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime] (D : CompleteDevissage R S N r)
    (i : Fin (D.stepCount + 1)) (R' B' : Type u) [CommRing R'] [CommRing B'] [IsLocalRing R']
    [Algebra R R'] [Algebra (D.B i) B'] [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R (D.B i) B'] :
    Ideal.map (algebraMap R' B') (IsLocalRing.maximalIdeal R') =
      Ideal.map (algebraMap (D.B i) B') (Ideal.map (algebraMap R (D.B i)) r) :=
  Ideal.map_maximalIdeal_eq_map_map_of_isLocalization R (D.B i) r R' B'

/-- The ideal generated by the maximal ideal of `R_r` in the localized lower algebra of a stage
is prime: it is the generic point of the closed fibre of the localized stage. -/
public theorem isPrime_map_maximalIdeal_localizedLowerAlgebra {R : Type u} {S : Type v}
    {N : Type w} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) (R' B' : Type u) [CommRing R']
    [CommRing B'] [IsLocalRing R'] [Algebra R R'] [Algebra (D.B i) B']
    [IsLocalization r.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid (D.B i) r.primeCompl) B'] [Algebra R' B']
    [Algebra R B'] [IsScalarTower R R' B'] [IsScalarTower R (D.B i) B'] :
    (Ideal.map (algebraMap R' B') (IsLocalRing.maximalIdeal R')).IsPrime :=
  Ideal.isPrime_map_maximalIdeal_of_isLocalization R (D.B i) r R' B'

/-- The image of `r.primeCompl` in the lower algebra of a stage misses the generic point `rBᵢ`
of the fibre over `r`, so the localized lower algebra is a localization of `Bᵢ` away from
`rBᵢ`. -/
public theorem algebraMapSubmonoid_le_primeCompl_localizedLowerAlgebra {R : Type u} {S : Type v}
    {N : Type w} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
    [AddCommGroup N] [Module S N] [Module.Finite S N] {r : Ideal R} [r.IsPrime]
    (D : CompleteDevissage R S N r) (i : Fin (D.stepCount + 1)) :
    Algebra.algebraMapSubmonoid (D.B i) r.primeCompl ≤
      (Ideal.map (algebraMap R (D.B i)) r).primeCompl :=
  Algebra.algebraMapSubmonoid_le_primeCompl_map R (D.B i) r

end Module.CompleteDevissage

end

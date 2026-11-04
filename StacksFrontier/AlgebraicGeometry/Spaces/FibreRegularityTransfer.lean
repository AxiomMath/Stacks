module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.FlatPullbackStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartFibreResidueFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.RingTheory.Sequence.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Transferring regularity from the étale local ring of a fibre to a chart of the fibre

Let `X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `Spec k ⟶ Y` be a point of
the target and let `F = X ×_Y Spec k` be the fibre, an algebraic space.  A sequence of global
regular functions is tested for regularity in the étale local ring `𝒪_{F, z̄}` at a geometric
point `z` of `F`, whereas the scheme-level slicing lemma Stacks 06LI consumes regularity in the
ordinary (Zariski) local ring `𝒪_{U_v, u}` of a scheme chart of the fibre.  This file moves
regularity from the former to the latter, and back.

Two flat local comparisons separate the two rings, and regularity is insensitive to both because
a flat local homomorphism of local rings is faithfully flat and Algebra Stacks 00LM descends and
ascends regular sequences along a faithfully flat base change.

* `𝒪_{U, u} ⟶ 𝒪_{F, z̄}` for `U` a scheme chart of `F` through `z`: the étale local ring is the
  strict henselization of the local ring of the chart (Stacks 04KF), and a strict henselization
  is faithfully flat over the ring it henselizes.  This is Stacks 05VP in the form
  `AlgebraicGeometry.Space.faithfullyFlat_chartLocalRingToEtaleLocalRing`.
* `𝒪_{U_v, u} ⟶ 𝒪_{U, u}` for any *flat* morphism of schemes `U ⟶ U_v`.  In the slicing argument
  the chart of `F` is the base change `U_v ×_{κ(v)} Spec k` of the fibre chart `U_v` along the
  residue field enlargement that makes `z` a section, and that projection is flat because `k` is
  a vector space over `κ(v)`: this is
  `AlgebraicGeometry.Scheme.Hom.flat_fst_fiber_extendResidueField`, equivalently
  `AlgebraicGeometry.flat_SpecMap_of_residueField` together with stability of flatness under
  base change.

## Main results

* `RingTheory.Sequence.isRegular_map_iff_of_faithfullyFlat`: Algebra Stacks 00LM read for a
  faithfully flat ring homomorphism rather than for a prescribed base change of modules.
* `AlgebraicGeometry.isRegular_map_stalkMap_iff`: along a flat morphism of schemes, regularity
  of a sequence in the local ring of the target is equivalent to regularity of its image in the
  local ring of the source.
* `AlgebraicGeometry.Space.isRegular_map_chartLocalRingToEtaleLocalRing_iff`: a sequence in the
  local ring of a scheme chart of an algebraic space is regular exactly when its image in the
  étale local ring at the geometric point is regular.
* `AlgebraicGeometry.Space.isRegular_map_etaleLocalRing_iff_of_flat`: **the regularity
  transfer.**  For a flat morphism `U ⟶ U_v` out of the scheme chart of a small étale
  neighbourhood of `z`, a sequence in `𝒪_{U_v, u}` is regular exactly when its image in
  `𝒪_{F, z̄}` is.
* `AlgebraicGeometry.Space.isRegular_map_etaleLocalRing_iff_fiber_extendResidueField`: the same
  with the flat morphism specialized to the one the residue field enlargement produces, namely
  the projection `U_v ×_{κ(v)} Spec K ⟶ U_v`, composed with an identification of the chart of
  `F` with that base change.

## Implementation notes

The transfer is stated for an arbitrary flat morphism `q : U ⟶ U_v` from the scheme underlying a
small étale neighbourhood of `z`, with the sequence living in `𝒪_{U_v, q u}`.  That is exactly
the shape in which the source uses it — *"since `𝒪_{U_v, u}` maps flatly into it, they form a
regular sequence in `𝒪_{U_v, u}` too"* — and it keeps the identification of the chart of `F`
with the base-changed fibre chart out of the statement.  The specialized form puts the
identification back, as a flat morphism `j` from the chart to
`U_v ×_{κ(v)} Spec K`; an isomorphism is flat, so taking `j` to be an identification is a legal
instantiation, but no isomorphism is demanded and nothing in the proof needs one.

Nothing here asserts flatness of anything over `Y`: the only flatness hypotheses are on the two
comparisons of local rings, both of which are supplied, and the only flatness conclusions are
about those same comparisons.  The three rings live in two universes — the two Zariski local
rings in `u` and the étale local ring, a colimit over the small étale neighbourhoods, in `u + 1`
— so the two comparisons are bare `RingHom`s and are composed as such rather than through a
universe-monomorphic composition law for faithfully flat ring maps.

The ring-level statement `RingTheory.Sequence.isRegular_map_iff_of_faithfullyFlat` is stated
here, and not in the `RingTheory` tree, because it is the only consumer: Algebra Stacks 00LM is
already in the library as
`RingTheory.Sequence.isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange`, and this is
only that lemma read along `RingHom.toAlgebra` for a bare ring homomorphism, which is the form
both comparisons above come in.  Faithful flatness of the homomorphism of local rings of a flat
morphism of schemes is `AlgebraicGeometry.faithfullyFlat_stalkMap`, which the library already
has.

## References

* [Stacks Project, Tag 00LM](https://stacks.math.columbia.edu/tag/00LM)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 05VL](https://stacks.math.columbia.edu/tag/05VL)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace RingTheory.Sequence

/-- **Algebra Stacks 00LM for a faithfully flat ring homomorphism.**  A sequence in `R` is
regular exactly when its image under a faithfully flat homomorphism `ψ : R ⟶ T` is regular in
`T`: the target is the base change of the source along `ψ`, so
`RingTheory.Sequence.isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange` applies with
the module taken to be the ring itself. -/
@[ega "0 15.1.13" "special case",
  ega "0 15.1.14" "special case",
  ega "0 15.1.21" "a)⇒b)",
  ega "0 15.2.5" "special case",
  ega "IV 19.7.5" "more general", sga "3 VIIB 5.5.2" "special case"]
theorem isRegular_map_iff_of_faithfullyFlat {R T : Type*} [CommRing R] [CommRing T]
    {ψ : R →+* T} (hψ : ψ.FaithfullyFlat) (rs : List R) :
    IsRegular T (rs.map ψ) ↔ IsRegular R rs := by
  let _ : Algebra R T := ψ.toAlgebra
  have : Module.FaithfullyFlat R T := hψ
  exact isRegular_map_algebraMap_iff_of_faithfullyFlat_of_isBaseChange
    (IsBaseChange.linearMap R T) rs

end RingTheory.Sequence

namespace AlgebraicGeometry

/-- **Regularity of a sequence is unchanged by the local rings of a flat morphism of schemes.**
A sequence in the local ring of the target at the image of a point is regular exactly when its
image in the local ring of the source at that point is regular. -/
theorem isRegular_map_stalkMap_iff {W T : Scheme.{u}} (p : W ⟶ T) [Flat p] (w : W)
    (rs : List (T.presheaf.stalk (p w))) :
    RingTheory.Sequence.IsRegular (W.presheaf.stalk w) (rs.map (p.stalkMap w).hom) ↔
      RingTheory.Sequence.IsRegular (T.presheaf.stalk (p w)) rs :=
  RingTheory.Sequence.isRegular_map_iff_of_faithfullyFlat (faithfullyFlat_stalkMap p w) rs

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Regularity in the local ring of a scheme chart is regularity in the étale local ring.**
The canonical map `𝒪_{U, u} ⟶ 𝒪_{F, z̄}` of Stacks 05VP is faithfully flat, the étale local ring
being the strict henselization of the chart's local ring, so Algebra Stacks 00LM identifies the
two regularity conditions. -/
theorem isRegular_map_chartLocalRingToEtaleLocalRing_iff {z : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood z) (rs : List ↥(chartLocalRing B S hS F N)) :
    RingTheory.Sequence.IsRegular ↥(etaleLocalRing B S hS F z)
        (rs.map (chartLocalRingToEtaleLocalRing B S hS F hF N)) ↔
      RingTheory.Sequence.IsRegular ↥(chartLocalRing B S hS F N) rs :=
  RingTheory.Sequence.isRegular_map_iff_of_faithfullyFlat
    (faithfullyFlat_chartLocalRingToEtaleLocalRing B S hS F hF N) rs

/-- **The regularity transfer.**  Let `F` be an algebraic space, let `z` be a geometric point of
`F`, let `U` be the scheme underlying a small étale neighbourhood of `z` with `u` the point of
`U` under `z`, and let `q : U ⟶ U_v` be a *flat* morphism of schemes.  Then a sequence in the
ordinary local ring `𝒪_{U_v, q u}` is regular exactly when its image in the étale local ring
`𝒪_{F, z̄}` is regular.

The image is taken along the composite of the homomorphism of local rings of `q` with the
canonical map `𝒪_{U, u} ⟶ 𝒪_{F, z̄}` of Stacks 05VP.  Both are faithfully flat — the first by
flatness of `q` and locality of a stalk map, the second because `𝒪_{F, z̄}` is the strict
henselization of `𝒪_{U, u}` — so Algebra Stacks 00LM applies to each in turn.

This is the step the proof of Stacks 06LW performs after enlarging the residue field: having
identified a chart of the fibre with the base change `U_v ×_{κ(v)} Spec k`, whose projection to
`U_v` is flat, it reads the regular sequence in `𝒪_{F, z̄}` as a regular sequence in
`𝒪_{U_v, u}`, which is what the scheme-level slicing lemma Stacks 06LI consumes. -/
theorem isRegular_map_etaleLocalRing_iff_of_flat {z : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood z) {Uv : Scheme.{u}} (q : chartScheme N.chart ⟶ Uv) [Flat q]
    (rs : List (Uv.presheaf.stalk (q (chartPoint B S hS F N)))) :
    RingTheory.Sequence.IsRegular ↥(etaleLocalRing B S hS F z)
        (rs.map ((chartLocalRingToEtaleLocalRing B S hS F hF N).comp
          (q.stalkMap (chartPoint B S hS F N)).hom)) ↔
      RingTheory.Sequence.IsRegular (Uv.presheaf.stalk (q (chartPoint B S hS F N))) rs := by
  have hsplit : rs.map ((chartLocalRingToEtaleLocalRing B S hS F hF N).comp
        (q.stalkMap (chartPoint B S hS F N)).hom) =
      (rs.map (q.stalkMap (chartPoint B S hS F N)).hom).map
        (chartLocalRingToEtaleLocalRing B S hS F hF N) := by
    rw [List.map_map]
    rfl
  rw [hsplit, isRegular_map_chartLocalRingToEtaleLocalRing_iff B S hS F hF N,
    isRegular_map_stalkMap_iff q (chartPoint B S hS F N) rs]

/-- **The regularity transfer along the residue field enlargement.**  Let `g : U ⟶ V` be a
morphism of schemes, let `v` be a point of `V` and let `φ : κ(v) ⟶ K` be an extension of its
residue field, so that `U ×_V Spec K = U_v ×_{κ(v)} Spec K` is the base change of the fibre
`U_v = g^{-1}(v)` along `φ`.  Let `F` be an algebraic space with a geometric point `z`, and let
`j` be a flat morphism from the scheme underlying a small étale neighbourhood of `z` to that base
change — an identification of the chart of `F` with the base-changed fibre chart is one such `j`,
being an isomorphism.  Then a sequence in `𝒪_{U_v, u}` is regular exactly when its image in the
étale local ring `𝒪_{F, z̄}` is regular.

Flatness of the projection `U_v ×_{κ(v)} Spec K ⟶ U_v`, which is what the enlargement of the
residue field costs, is `AlgebraicGeometry.flat_SpecMap_of_residueField`: a module over a field
is free.  The rest is
`AlgebraicGeometry.Space.isRegular_map_etaleLocalRing_iff_of_flat` applied to the composite of
`j` with that projection. -/
theorem isRegular_map_etaleLocalRing_iff_fiber_extendResidueField {z : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood z) {U V : Scheme.{u}} (g : U ⟶ V) (v : V) {K : Type u} [Field K]
    (φ : V.residueField v ⟶ CommRingCat.of K)
    (j : chartScheme N.chart ⟶ pullback (g.fiberToSpecResidueField v) (Spec.map φ)) [Flat j]
    (rs : List ((g.fiber v).presheaf.stalk
      ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
        (chartPoint B S hS F N)))) :
    RingTheory.Sequence.IsRegular ↥(etaleLocalRing B S hS F z)
        (rs.map ((chartLocalRingToEtaleLocalRing B S hS F hF N).comp
          ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ)).stalkMap
            (chartPoint B S hS F N)).hom)) ↔
      RingTheory.Sequence.IsRegular ((g.fiber v).presheaf.stalk
        ((j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ))
          (chartPoint B S hS F N))) rs :=
  have : Flat (Spec.map φ) := flat_SpecMap_of_residueField φ
  isRegular_map_etaleLocalRing_iff_of_flat B S hS F hF N
    (j ≫ pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ)) rs

end Space

end AlgebraicGeometry

end

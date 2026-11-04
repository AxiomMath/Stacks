module

public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.RingTheory.Smooth.GeometricallyIrreducibleFibres

/-!
# The extension of a prime is the generic point of its fibre

Let `R → B` be a smooth ring map whose spectrum has geometrically irreducible fibres and let `r`
be a prime of `R`. `Ideal.isPrime_map_of_smooth_of_geometricallyIrreducible` shows that the
extension `rB` is prime. This file proves that the point of `Spec B` it defines is the **generic
point of the fibre of `Spec B → Spec R` over `r`**: it lies in that fibre, every point of the
fibre lies in its closure, and it is the only point of the fibre with that property.

The fibre is the subspace `comap (algebraMap R B) ⁻¹' {r}` of `Spec B`, which is the form
`Algebra.relativeDimensionAt` uses.

## Main results

* `Ideal.map_le_of_comap_eq`: a prime of `B` contracting to `r` contains `rB`. No hypothesis on
  the ring map.
* `Ideal.comap_map_eq_self_of_exists_comap_eq`: if some prime of `B` contracts to `r` then so
  does `rB`.
* `Ideal.comap_map_eq_self_of_smooth_of_geometricallyIrreducible`: under the hypotheses of
  Stacks 05HX the extension `rB` contracts to `r`, because the morphism of spectra is
  surjective.
* `Ideal.isGenericPoint_map_of_smooth_of_geometricallyIrreducible`: **`rB` is a generic point of
  the fibre over `r`.**
* `Ideal.eq_map_of_mem_fiber_of_fiber_le`: a point of the fibre over `r` below every point of
  that fibre — in particular its generic point — has ideal `rB`. This is the form in which the
  identification is consumed: a generic point is produced by a topological argument and has to
  be recognised as `rB`.

## Implementation notes

Only one of the two hypotheses of Stacks 05HX is used, and only through one consequence:
geometric irreducibility of the fibres makes the morphism of spectra surjective
(`AlgebraicGeometry.instSurjectiveOfGeometricallyIrreducible`), so the fibre over `r` is
nonempty, and a prime of `B` over `r` sandwiches the contraction of `rB` between `r` and
itself. Smoothness enters only through
`Ideal.isPrime_map_of_smooth_of_geometricallyIrreducible`, which is what makes `rB` a point of
`Spec B` at all.

Genericity is stated in the subspace, as `IsGenericPoint _ Set.univ` for the fibre regarded as
a type, because the closure of `rB` in the whole of `Spec B` is strictly larger than the fibre:
it contains every prime containing `rB`, including those contracting to primes strictly above
`r`. `closure_subtype` is what reduces the subspace statement to the containment of ideals.

## References

* [Stacks Project, Tag 05HX](https://stacks.math.columbia.edu/tag/05HX)
* [Stacks Project, Tag 00QD](https://stacks.math.columbia.edu/tag/00QD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Ideal

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A prime of `B` contracting to `r` contains the extension `rB`. -/
public theorem map_le_of_comap_eq (r : Ideal R) (q : Ideal B)
    (hq : q.comap (algebraMap R B) = r) : r.map (algebraMap R B) ≤ q :=
  Ideal.map_le_iff_le_comap.2 (hq ▸ le_rfl)

/-- If some ideal of `B` contracts to `r`, then the extension `rB` contracts to `r` as well. -/
public theorem comap_map_eq_self_of_exists_comap_eq (r : Ideal R)
    (h : ∃ q : Ideal B, q.comap (algebraMap R B) = r) :
    (r.map (algebraMap R B)).comap (algebraMap R B) = r := by
  obtain ⟨q, hq⟩ := h
  refine le_antisymm ?_ Ideal.le_comap_map
  calc (r.map (algebraMap R B)).comap (algebraMap R B)
      ≤ q.comap (algebraMap R B) := Ideal.comap_mono (map_le_of_comap_eq r q hq)
    _ = r := hq

variable (R B) in
/-- **The extension `rB` contracts to `r`**, for `R → B` smooth with geometrically irreducible
fibres: such a morphism of spectra is surjective, so the fibre over `r` is nonempty. -/
public theorem comap_map_eq_self_of_smooth_of_geometricallyIrreducible [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B)))] (r : Ideal R)
    [r.IsPrime] : (r.map (algebraMap R B)).comap (algebraMap R B) = r := by
  have hs : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B))) := inferInstance
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R B)) := hs.surj
  obtain ⟨q, hq⟩ := hsurj ⟨r, ‹_›⟩
  exact comap_map_eq_self_of_exists_comap_eq r ⟨q.asIdeal, congrArg PrimeSpectrum.asIdeal hq⟩

variable (R B) in
/-- The point of `Spec B` defined by the extension `rB` lies in the fibre over `r`. -/
public theorem comap_mk_map_eq [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B)))] (r : Ideal R)
    [r.IsPrime] :
    PrimeSpectrum.comap (algebraMap R B)
        ⟨r.map (algebraMap R B), isPrime_map_of_smooth_of_geometricallyIrreducible R B r⟩ =
      ⟨r, ‹_›⟩ :=
  PrimeSpectrum.ext (comap_map_eq_self_of_smooth_of_geometricallyIrreducible R B r)

variable (R B) in
/-- **A point of the fibre over `r` that is below every point of that fibre has ideal `rB`.**
In particular the generic point of the fibre, which exists because the fibre is irreducible, is
the point defined by `rB`. -/
public theorem eq_map_of_mem_fiber_of_fiber_le [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B)))] (r : Ideal R)
    [r.IsPrime] (q : PrimeSpectrum B)
    (hq : PrimeSpectrum.comap (algebraMap R B) q = ⟨r, ‹_›⟩)
    (hle : ∀ q' : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap R B) q' = ⟨r, ‹_›⟩ →
      q.asIdeal ≤ q'.asIdeal) :
    q.asIdeal = r.map (algebraMap R B) :=
  le_antisymm
    (hle ⟨r.map (algebraMap R B), isPrime_map_of_smooth_of_geometricallyIrreducible R B r⟩
      (comap_mk_map_eq R B r))
    (map_le_of_comap_eq r q.asIdeal (congrArg PrimeSpectrum.asIdeal hq))

variable (R B) in
/-- **The extension `rB` is a generic point of the fibre of `Spec B → Spec R` over `r`**, for
`R → B` smooth with geometrically irreducible fibres. -/
public theorem isGenericPoint_map_of_smooth_of_geometricallyIrreducible [Algebra.Smooth R B]
    [GeometricallyIrreducible (Spec.map (CommRingCat.ofHom (algebraMap R B)))] (r : Ideal R)
    [r.IsPrime] :
    IsGenericPoint
      (⟨⟨r.map (algebraMap R B), isPrime_map_of_smooth_of_geometricallyIrreducible R B r⟩,
        comap_mk_map_eq R B r⟩ :
        ↥(PrimeSpectrum.comap (algebraMap R B) ⁻¹' {(⟨r, ‹_›⟩ : PrimeSpectrum R)}))
      Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  rw [closure_subtype, Set.image_singleton, PrimeSpectrum.closure_singleton]
  exact map_le_of_comap_eq r q.1.asIdeal (congrArg PrimeSpectrum.asIdeal q.2)

end Ideal

end

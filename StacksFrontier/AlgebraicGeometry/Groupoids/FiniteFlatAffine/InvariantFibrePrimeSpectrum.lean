module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.AffineQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.InvariantFibreBijection
public import StacksFrontier.AlgebraicGeometry.Scheme.CarrierPrimeSpectrum
public import StacksFrontier.RingTheory.Spectrum.Prime.QuotientFibre

/-!
# The fibres over the invariant spectrum, as spectra of quotient rings

The map of fibres `U'_{p'} → U_p` of the "Claim" of [Stacks Project, Tag 0DT9]
(`invariantFibreMap`) is a map between subtypes of the points of the two object schemes. For
affine object schemes, this file describes the same fibres as sets of primes of the rings of
global functions, and, over closed points, as the spectra of two quotient rings, one for each
fibre.

For an affine object scheme the two steps are:

* the points of `U` are the primes of `A = Γ(U, ⊤)`, and the morphism `U ⟶ M` to the invariant
  spectrum is, on points, contraction along the inclusion `invariantRing G ⊆ A`
  (`objectsToInvariantSpectrum_base`, which holds by `rfl`); so the fibre over `p` is
  `{x : Spec A // x ∩ invariantRing G = p}`, and the map of fibres becomes contraction along
  `A → A' = Γ(U', ⊤)`;
* when `p` is a *closed* point of `M`, that set of primes is the zero locus of `√(p A)`, because
  a prime of `A` contracts to the maximal ideal `p` exactly when it contains the extension `p A`
  (`PrimeSpectrum.comap_eq_iff_radical_map_le`). So the fibre is `Spec (A ⧸ √(p A))`, a quotient
  by a radical ideal.

The resulting ideal is `invariantFibreIdeal`, and the ideal of the fibre over `p'` upstairs
contains the extension of the ideal of the fibre over `p` downstairs
(`invariantFibreIdeal_le_comap`). It is *not* an equality: `√(p A) · A'` cuts out the preimage of
the whole of `U_p`, the union of the fibres `U'_{p''}` over all points `p''` of `M'` above `p`,
whereas `invariantFibreIdeal G' p'` cuts out `U'_{p'}` alone. Already for `G' = G ⨿ G` the two
differ.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.invariantFibrePrimeMap`: the map of fibres of
  `invariantFibreMap`, read on prime ideals.
* `AlgebraicGeometry.GroupoidScheme.invariantFibreIdeal`: the radical ideal cutting out the fibre
  over a point of the invariant spectrum.

## Main results

* `AlgebraicGeometry.GroupoidScheme.bijective_invariantFibrePrimeMap`: the bijection of fibres,
  read on prime ideals.
* `AlgebraicGeometry.GroupoidScheme.bijective_comapRestrict_invariantFibreIdeal`: the bijection
  of fibres over closed points as a bijection between the primes above the two fibre ideals.

## References

* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry

namespace GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- **The fibre of `U ⟶ M` over a point of `M`, read on prime ideals of `Γ(U, ⊤)`.** The two
descriptions agree because the morphism to the invariant spectrum is, on points, contraction
along the inclusion of the invariant ring. -/
def invariantFibreEquivPrimeSpectrum (G : GroupoidScheme S) [IsAffine G.objects.left]
    (p : Spec (.of (invariantRing G))) :
    {u : G.objects.left // (objectsToInvariantSpectrum G).base u = p} ≃
      {x : PrimeSpectrum Γ(G.objects.left, ⊤) //
        PrimeSpectrum.comap (invariantRing G).subtype x = p} :=
  Equiv.subtypeEquiv G.objects.left.carrierEquivPrimeSpectrum fun _ => Iff.rfl

/-- The inclusion of the invariant ring commutes with pullback of global functions along the map
of object schemes. This is `invariantRingMap_comp_subtype` in the `appTop` spelling of that
pullback. -/
theorem invariantRingMap_comp_subtype_appTop :
    (invariantRing G').subtype.comp (invariantRingMap F) =
      F.mapObjects.left.appTop.hom.comp (invariantRing G).subtype := by
  rw [← Scheme.Γ_map_op]
  exact invariantRingMap_comp_subtype F

/-- **The map of fibres of `invariantFibreMap`, read on prime ideals**: contraction along the map
`Γ(U, ⊤) → Γ(U', ⊤)` of rings of global functions. -/
def invariantFibrePrimeMap (p' : Spec (.of (invariantRing G'))) :
    {x' : PrimeSpectrum Γ(G'.objects.left, ⊤) //
        PrimeSpectrum.comap (invariantRing G').subtype x' = p'} →
      {x : PrimeSpectrum Γ(G.objects.left, ⊤) //
        PrimeSpectrum.comap (invariantRing G).subtype x =
          PrimeSpectrum.comap (invariantRingMap F) p'} :=
  fun x' => ⟨PrimeSpectrum.comap F.mapObjects.left.appTop.hom x'.1, by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (invariantRing G).subtype
        (Ideal.comap F.mapObjects.left.appTop.hom x'.1.asIdeal) =
      Ideal.comap (invariantRingMap F) p'.asIdeal
    rw [Ideal.comap_comap, ← invariantRingMap_comp_subtype_appTop, ← Ideal.comap_comap]
    exact congrArg (Ideal.comap (invariantRingMap F)) (congrArg PrimeSpectrum.asIdeal x'.2)⟩

/-- The prime underlying the image of `x'` under `invariantFibrePrimeMap` is the contraction of
`x'` along the map `Γ(U, ⊤) → Γ(U', ⊤)`. -/
@[simp]
theorem invariantFibrePrimeMap_coe (p' : Spec (.of (invariantRing G')))
    (x' : {x' : PrimeSpectrum Γ(G'.objects.left, ⊤) //
      PrimeSpectrum.comap (invariantRing G').subtype x' = p'}) :
    (invariantFibrePrimeMap F p' x').1 =
      PrimeSpectrum.comap F.mapObjects.left.appTop.hom x'.1 :=
  rfl

/-- **The bijection of fibres of the "Claim" of [Stacks Project, Tag 0DT9], read on prime
ideals.** This is `bijective_invariantFibreMap` transported along
`invariantFibreEquivPrimeSpectrum`: the same bijection, between the primes of `Γ(U', ⊤)` over `p'`
and the primes of `Γ(U, ⊤)` over the image of `p'`. -/
theorem bijective_invariantFibrePrimeMap [IsAffine G.objects.left] [IsAffine G'.objects.left]
    (p' : Spec (.of (invariantRing G')))
    (hbij : Function.Bijective (invariantFibreMap F p')) :
    Function.Bijective (invariantFibrePrimeMap F p') := by
  have hcomm : invariantFibrePrimeMap F p' =
      (invariantFibreEquivPrimeSpectrum G
          ((Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p')) ∘
        (invariantFibreMap F p') ∘ (invariantFibreEquivPrimeSpectrum G' p').symm := by
    refine funext fun x' => ?_
    obtain ⟨u', rfl⟩ := (invariantFibreEquivPrimeSpectrum G' p').surjective x'
    refine Subtype.ext ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply, invariantFibrePrimeMap_coe]
    exact (Scheme.carrierEquivPrimeSpectrum_naturality F.mapObjects.left u'.1).symm
  rw [hcomm]
  exact (Equiv.comp_bijective _ _).2 ((Equiv.bijective_comp _ _).2 hbij)

/-- **The radical ideal cutting out the fibre of `U ⟶ M` over a point `p` of `M`.** It is the
radical of the extension of `p` to the ring of global functions; its zero locus is the fibre
exactly when `p` is a closed point of `M`, which is
`PrimeSpectrum.comap_eq_iff_radical_map_le`. -/
def invariantFibreIdeal (G : GroupoidScheme S) (p : Spec (.of (invariantRing G))) :
    Ideal Γ(G.objects.left, ⊤) :=
  (p.asIdeal.map (invariantRing G).subtype).radical

/-- The fibre ideal `invariantFibreIdeal G p` is a radical ideal. -/
theorem invariantFibreIdeal_isRadical (G : GroupoidScheme S)
    (p : Spec (.of (invariantRing G))) : (invariantFibreIdeal G p).IsRadical :=
  Ideal.radical_isRadical _

/-- **The fibre ideal upstairs contains the extension of the fibre ideal downstairs**: the fibre
`U'_{p'}` lies inside the preimage of the fibre `U_p`.

The containment is in general strict, since the preimage of `U_p` is the union of the fibres
`U'_{p''}` over all the points `p''` of `M'` above `p`. -/
theorem invariantFibreIdeal_le_comap (p' : Spec (.of (invariantRing G'))) :
    invariantFibreIdeal G (PrimeSpectrum.comap (invariantRingMap F) p') ≤
      (invariantFibreIdeal G' p').comap F.mapObjects.left.appTop.hom := by
  have hrad : ((invariantFibreIdeal G' p').comap
      F.mapObjects.left.appTop.hom).IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := hx
    rw [Ideal.mem_comap] at hn ⊢
    exact invariantFibreIdeal_isRadical G' p' ⟨n, by rw [← map_pow]; exact hn⟩
  refine (hrad.radical_le_iff).mpr ?_
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← invariantRingMap_comp_subtype_appTop,
    ← Ideal.comap_comap]
  exact Ideal.comap_mono (Ideal.map_le_iff_le_comap.mp Ideal.le_radical)

/-- **The bijection of fibres of the "Claim" of [Stacks Project, Tag 0DT9] as a bijection between
the primes above the two fibre ideals.** Both points are required to be closed, which makes each
fibre the zero locus of its fibre ideal. -/
theorem bijective_comapRestrict_invariantFibreIdeal [IsAffine G.objects.left]
    [IsAffine G'.objects.left] (p' : Spec (.of (invariantRing G')))
    (hp' : p'.asIdeal.IsMaximal)
    (hp : (PrimeSpectrum.comap (invariantRingMap F) p').asIdeal.IsMaximal)
    (hbij : Function.Bijective (invariantFibreMap F p')) :
    Function.Bijective (PrimeSpectrum.comapRestrict
      F.mapObjects.left.appTop.hom (invariantFibreIdeal_le_comap F p')) := by
  have e : ∀ x : PrimeSpectrum Γ(G.objects.left, ⊤),
      PrimeSpectrum.comap (invariantRing G).subtype x =
          PrimeSpectrum.comap (invariantRingMap F) p' ↔
        invariantFibreIdeal G (PrimeSpectrum.comap (invariantRingMap F) p') ≤ x.asIdeal :=
    fun x => PrimeSpectrum.comap_eq_iff_radical_map_le _ hp x
  have e' : ∀ x' : PrimeSpectrum Γ(G'.objects.left, ⊤),
      PrimeSpectrum.comap (invariantRing G').subtype x' = p' ↔
        invariantFibreIdeal G' p' ≤ x'.asIdeal :=
    fun x' => PrimeSpectrum.comap_eq_iff_radical_map_le _ hp' x'
  have hcomm : PrimeSpectrum.comapRestrict
      F.mapObjects.left.appTop.hom (invariantFibreIdeal_le_comap F p') =
      (Equiv.subtypeEquivRight e) ∘ ((invariantFibrePrimeMap F p') ∘
        (Equiv.subtypeEquivRight e').symm) :=
    funext fun _ => Subtype.ext rfl
  rw [hcomm]
  exact (Equiv.comp_bijective _ _).2
    ((Equiv.bijective_comp _ _).2 (bijective_invariantFibrePrimeMap F p' hbij))

end GroupoidScheme

end AlgebraicGeometry

end

end

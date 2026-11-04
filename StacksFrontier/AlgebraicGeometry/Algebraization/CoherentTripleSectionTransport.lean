module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit

/-!
# The section-multiplication compatibility, as a morphism of coherent triples out of the unit

`Stacks.Algebraization.CoherentTriple.mulSectionTwistZ` asks for two global sections `σ`, `σ₀` of
the members of an invertible triple `L`, together with a hypothesis `hcompat` identifying their
inverse images along the two routes around the square of `L` after cancelling the two
`Scheme.Modules.pullbackUnitIso` identifications of the inverse image of the unit module with the
unit module. That hypothesis is exactly the compatibility making `(σ, σ₀)` a morphism of coherent
triples `Stacks.Algebraization.CoherentTriple.unit A f h ⟶ L`, once the latter's own `alpha` --
itself built from the same two `pullbackUnitIso` identifications -- is unfolded. This file records
that equivalence, so that supplying a `CoherentTriple.Hom (CoherentTriple.unit A f h) L` is enough
to supply `hcompat`.

## Main results

* `Stacks.Algebraization.hcompat_iff_hom_compatible`: `hcompat` is equivalent, for the same `σ`
  and `σ₀`, to the compatibility square of a morphism of coherent triples out of
  `CoherentTriple.unit A f h`.
* `Stacks.Algebraization.hcompat_of_hom`: the hypothesis `hcompat` needed by
  `CoherentTriple.mulSectionTwistZ`, read off directly from a morphism of coherent triples
  `CoherentTriple.unit A f h ⟶ L`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- **`hcompat` unfolds to the compatibility square of a morphism of coherent triples out of the
unit triple.** The isomorphism `Scheme.Modules.pullbackUnitIso` on the punctured-spectrum side of
the square is exactly the one cancelled on both sides of `hcompat`, and
`CoherentTriple.unit A f h` is built from the same two `pullbackUnitIso` identifications; so
cancelling that isomorphism identifies the two statements. -/
public theorem hcompat_iff_hom_compatible {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A}
    (h : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    {L : CoherentTriple A f}
    (σ : Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme ⟶ L.F)
    (σ₀ : Stacks.Ample.unitModule (closedFibre A f) ⟶ L.F₀) :
    (((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀) ↔
      (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map σ ≫ L.alpha.hom =
        (CoherentTriple.unit A f h).alpha.hom ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map σ₀ := by
  have halpha : (CoherentTriple.unit A f h).alpha.hom =
      (Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).hom ≫
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv := rfl
  rw [halpha]
  simp only [Category.assoc]
  exact Iso.inv_comp_eq _

/-- **`hcompat`, read off from a morphism of coherent triples out of the unit.** Given
`φ : CoherentTriple.unit A f h ⟶ L`, its own `onPunctured` and `onClosedFibre` satisfy the
hypothesis `hcompat` of `CoherentTriple.mulSectionTwistZ`. -/
public theorem hcompat_of_hom {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A}
    (h : IsFTorsionFree A f
      (Stacks.Ample.unitModule (Stacks.Divisors.puncturedSpectrum A).toScheme))
    {L : CoherentTriple A f} (φ : (CoherentTriple.unit A f h).Hom L) :
    ((Scheme.Modules.pullbackUnitIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).inv ≫
          (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map φ.onPunctured) ≫ L.alpha.hom =
        (Scheme.Modules.pullbackUnitIso (puncturedClosedFibre A f).ι).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map φ.onClosedFibre :=
  (hcompat_iff_hom_compatible h φ.onPunctured φ.onClosedFibre).2 φ.compatible

end Stacks.Algebraization

end

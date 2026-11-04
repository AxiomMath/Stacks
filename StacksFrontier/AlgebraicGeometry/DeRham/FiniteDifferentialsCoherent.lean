module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.CoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle

/-!
# Coherence of the relative differentials of a finite morphism's composite

Let `f : Y ⟶ X` be a finite morphism of schemes and let `q : X ⟶ S` be arbitrary, with `X`
locally Noetherian.  If `Ω_{X/S}` is coherent then so is `Ω_{Y/S}`, and so is every sheaf
`Ω^n_{Y/S}` of relative differential `n`-forms.

This is the first step of the proof of [Stacks, Tag 0AX6], where the conclusion is used to form
the reflexive hull and to apply [Stacks, Tag 0AY7]: nothing about `q` is needed beyond coherence
of `Ω_{X/S}`, which is exactly the hypothesis the source assumes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isCoherent_relativeDifferentials_comp_of_isFinite`: `Ω_{Y/S}` is
  coherent.
* `AlgebraicGeometry.Scheme.Hom.isCoherent_relativeDifferentialForms_comp_of_isFinite`: so is
  `Ω^n_{Y/S}`, in every degree.

## Implementation notes

The source's argument is the exact sequence `f^*Ω_{X/S} ⟶ Ω_{Y/S} ⟶ Ω_{Y/X} ⟶ 0` of
[Stacks, Tag 01UX], available as `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_exact`
together with `AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials_epi`.  Its outer terms are
coherent: the pullback of a coherent module along a morphism with locally Noetherian source is
coherent by `AlgebraicGeometry.isCoherent_pullback`, and `Ω_{Y/X}` is coherent because a finite
morphism is locally of finite type.  Coherent modules are a weak Serre subcategory, so the
middle term is coherent once the sequence has been cut into a short exact one.

Cutting it is the only step with any content.  The sequence is exact at `Ω_{Y/S}` and the right
map is an epimorphism, but the left map is not a monomorphism, so
`AlgebraicGeometry.CoherentAbelian.isCoherent_X₂_of_shortExact` does not apply to it directly.
Replacing the left term by `ker` of the right map gives a short exact sequence, and exactness at
the middle term says precisely that the comparison `f^*Ω_{X/S} ⟶ ker` is an epimorphism —
`CategoryTheory.ShortComplex.exact_iff_epi_toCycles` composed with
`CategoryTheory.ShortComplex.cyclesIsoKernel`.  A quotient of a coherent module that is known to
be quasi-coherent is coherent, which is what
`Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi` says, and the kernel is
quasi-coherent because `Ω` always is.

`Y` is locally Noetherian rather than assumed so: a finite morphism has locally Noetherian source
over a locally Noetherian target, by `AlgebraicGeometry.isLocallyNoetherian_of_isFinite`.

## References

* [Stacks Project, Tag 01UX](https://stacks.math.columbia.edu/tag/01UX)
* [Stacks Project, Tag 0AX6](https://stacks.math.columbia.edu/tag/0AX6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {S X Y : Scheme.{u}}

/-- **The relative differentials of `Y ⟶ S` are coherent when those of `X ⟶ S` are and
`Y ⟶ X` is finite.**  This is the first step of the proof of [Stacks, Tag 0AX6]: the exact
sequence `f^*Ω_{X/S} ⟶ Ω_{Y/S} ⟶ Ω_{Y/X} ⟶ 0` has coherent outer terms, and coherent modules are
closed under extensions. -/
theorem isCoherent_relativeDifferentials_comp_of_isFinite (q : X ⟶ S) (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsFinite f] [(relativeDifferentials q).IsCoherent] :
    (relativeDifferentials (f ≫ q)).IsCoherent := by
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isFinite f
  have : ((Scheme.Modules.pullback f).obj (relativeDifferentials q)).IsCoherent :=
    isCoherent_pullback f _
  have : (relativeDifferentials f).IsCoherent := isCoherent_relativeDifferentials f
  have hepi : Epi (f.toRelativeDifferentials q) := toRelativeDifferentials_epi f q
  obtain ⟨hzero, hexact⟩ := toRelativeDifferentials_exact f q
  have : (kernel (f.toRelativeDifferentials q)).IsCoherent := by
    let c := ShortComplex.mk _ _ hzero
    have : Epi c.toCycles := (ShortComplex.exact_iff_epi_toCycles _).mp hexact
    exact Stacks.AlgebraicGeometry.CoherentSubquotients.isCoherent_of_epi
      (c.toCycles ≫ c.cyclesIsoKernel.hom)
  exact CoherentAbelian.isCoherent_X₂_of_shortExact
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (f.toRelativeDifferentials q))
      (show Mono (kernel.ι (f.toRelativeDifferentials q)) from inferInstance) hepi)
    ‹_› ‹_›

/-- **The sheaf `Ω^n_{Y/S}` of relative differential `n`-forms is coherent when `Ω_{X/S}` is and
`Y ⟶ X` is finite**, in every degree: it is the `n`-th exterior power of the coherent module
`Ω_{Y/S}` on the locally Noetherian scheme `Y`. -/
theorem isCoherent_relativeDifferentialForms_comp_of_isFinite (q : X ⟶ S) (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsFinite f] [(relativeDifferentials q).IsCoherent] (n : ℕ) :
    (relativeDifferentialForms (f ≫ q) (n : ℤ)).IsCoherent :=
  have : IsLocallyNoetherian Y := isLocallyNoetherian_of_isFinite f
  have : (relativeDifferentials (f ≫ q)).IsCoherent :=
    isCoherent_relativeDifferentials_comp_of_isFinite q f
  Scheme.Modules.isCoherent_exteriorPower (relativeDifferentials (f ≫ q)) n

end AlgebraicGeometry.Scheme.Hom

end

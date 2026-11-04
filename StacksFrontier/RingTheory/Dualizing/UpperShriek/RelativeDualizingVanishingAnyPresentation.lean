module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingVanishing

/-!
# The vanishing of the relative dualizing complex of a surjection, at any presentation

Let `φ : R →+* A` be a surjective homomorphism of Noetherian rings.  Clause (1) of
[Stacks, Tag 0E9R] — the vanishing `H^i(ω^•_{A/R})_𝔭 = 0` for `i < -r` — holds for such a `φ`
with `r = 0`, the sharp value of the tag's hypothesis (2), and with its hypothesis (1) unused;
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingVanishing` proves it at the
presentation of `φ` by the polynomial algebra in no variables, where `n = 0` makes the bound
`-n` of `Dualizing.PolynomialPresentation.isZero_homology_relativeDualizingComplex` the sharp
one.

At a presentation with `n` variables that bound is only `i < -n`, which is weaker.  This file
restores the sharp bound at an *arbitrary* presentation, by the independence of the presentation
of [Stacks, Tag 0BZJ] — `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso`,
unconditional in this library.  It is the same passage that
`StacksFrontier.RingTheory.Dualizing.UpperShriek.SurjectiveAnyPresentation` makes for
[Stacks, Tag 0C0G], [Stacks, Tag 0BZT] and [Stacks, Tag 0E9L].

## Main results

* `Dualizing.isZero_homology_relativeDualizingComplex_of_surjective` — the vanishing clause of
  [Stacks, Tag 0E9R] for a surjective `φ`, at an arbitrary polynomial presentation.
* `Dualizing.subsingleton_localizedModule_homology_relativeDualizingComplex_of_surjective` — the
  same after localization, the shape in which the source states the clause.

## Implementation notes

These are special cases of [Stacks, Tag 0E9R], which is proved in full for a general finite type
`φ` in `StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingCohenMacaulay`
(`Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex` and
`Dualizing.propertySkModule_localizedModule_homology_relativeDualizingComplex`); they carry no
Tag 0E9R attribute.  The surjective case needs neither hypothesis (1) nor a dualizing complex.

This is a separate module from
`StacksFrontier.RingTheory.Dualizing.UpperShriek.SurjectiveAnyPresentation` because the two cannot
be imported together and use instance search for `HasDerivedCategory`: Tag 0E9L's statement
mentions `Dualizing.IsDualizingComplex`, whose derived-category instance has to be pinned by
hand once the global locally small instances of
`StacksFrontier.Homology.DerivedCategory.LocallySmall` are in scope, as they are through Tag 0BZJ.
Nothing here mentions a dualizing complex, so nothing here needs that pinning.

## References

* [Stacks Project, Tag 0E9R](https://stacks.math.columbia.edu/tag/0E9R)
* [Stacks Project, Tag 0BZJ](https://stacks.math.columbia.edu/tag/0BZJ)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

noncomputable section

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **The vanishing of [Stacks, Tag 0E9R] for a surjective `φ` at an arbitrary
presentation.**  For a surjective `φ : R →+* A` the sharp value of hypothesis (2) of the source
is `r = 0`, because `A` is a quotient of `R` and so `κ(𝔮) = κ(R ∩ 𝔮)` at every prime `𝔮` of `A`;
hypothesis (1) is not needed.  The conclusion `H^i(ω^•_{A/R}) = 0` for `i < 0` is therefore
exactly the vanishing the tag asserts, and it holds at *every* polynomial presentation of `φ`,
not only at the one with no variables.

`Dualizing.isZero_homology_relativeDualizingComplex_ofSurjective` is the case of the
presentation with no variables, where the bound comes for free from
`Dualizing.PolynomialPresentation.isZero_homology_relativeDualizingComplex` at `n = 0`.  At a
presentation with `n` variables that lemma only gives `i < -n`, which is weaker; the sharp bound
at an arbitrary presentation is the independence of the presentation,
[Stacks, Tag 0BZJ], read through
`Dualizing.upperShriekFunctor_iso_derivedHom_of_surjective`. -/
theorem isZero_homology_relativeDualizingComplex_of_surjective
    (f : R →+* A) (hf : Function.Surjective f) (p : PolynomialPresentation f)
    (i : ℤ) (hi : i < 0) :
    Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) := by
  obtain ⟨eInd⟩ := PolynomialPresentation.nonempty_upperShriekFunctor_iso.{u, v} f p
    (PolynomialPresentation.ofSurjective f hf)
  exact Limits.IsZero.of_iso
    (isZero_homology_relativeDualizingComplex_ofSurjective.{u, v} f hf i hi)
    ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).mapIso (eInd.app _))

/-- **The vanishing of [Stacks, Tag 0E9R], localized, for a surjective `φ` at an arbitrary
presentation.**  The localized form of
`Dualizing.isZero_homology_relativeDualizingComplex_of_surjective`, which is the shape in which
the source states the clause. -/
theorem subsingleton_localizedModule_homology_relativeDualizingComplex_of_surjective
    (f : R →+* A) (hf : Function.Surjective f) (p : PolynomialPresentation f)
    (S : Submonoid A) (i : ℤ) (hi : i < 0) :
    Subsingleton (LocalizedModule S
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        (p.upperShriekFunctor.{u, v}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
            (ModuleCat.of R (ULift.{v} R)))))) := by
  have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      (p.upperShriekFunctor.{u, v}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
          (ModuleCat.of R (ULift.{v} R))))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (isZero_homology_relativeDualizingComplex_of_surjective.{u, v} f hf p i hi)
  infer_instance


end

end Dualizing

end

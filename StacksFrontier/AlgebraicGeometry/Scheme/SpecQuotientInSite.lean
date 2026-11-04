module

public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughClosedSubspace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The spectrum of a quotient as an object of a big fppf site, and factorisations through it

Let `R` be a commutative ring whose spectrum belongs to a big fppf site, and let `I ⊆ R` be an
ideal.  Then `\Spec(R/I)` belongs to the same site, and a morphism of schemes to `\Spec R` whose
kernel on global functions contains the kernel of `\Spec(R/I) ⟶ \Spec R` factors through
`\Spec(R/I)`.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_specQuotient`: `\Spec(R/I)` satisfies the size cutoff
  of a big fppf site containing `\Spec R`.
* `AlgebraicGeometry.exists_comp_eq_specQuotientMk`: the factorisation of a morphism to
  `\Spec R` through `\Spec(R/I)`.
* `AlgebraicGeometry.locallyOfFinitePresentation_specQuotientMk`: for `I` finitely generated the
  closed immersion is locally of finite presentation.

## Implementation notes

`\Spec(R/I) ⟶ \Spec R` is a closed immersion, hence a quasi-compact monomorphism, so
`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact` (Stacks 04VA) bounds the size of the
source by that of the target and the cutoff is not crossed.

The factorisation is Mathlib's `AlgebraicGeometry.IsClosedImmersion.lift`, whose hypothesis is an
inclusion of kernel ideal sheaves; over the affine target that inclusion is the inclusion of the
kernels on global functions, which is `AlgebraicGeometry.Scheme.ker_le_ker_iff_of_isAffine`. The
hypothesis is stated as that inclusion of kernels on global functions rather than as `I ≤ \ker`
of the composite with `AlgebraicGeometry.Scheme.ΓSpecIso`, so that nothing has to be transported
across the identification of `R` with `Γ(\Spec R, ⊤)`.

## References

* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The closed immersion `\Spec(R/I) ⟶ \Spec R` cut out by an ideal of `R`. -/
noncomputable abbrev specQuotientMk {R : CommRingCat.{u}} (I : Ideal R) :
    Spec (.of (R ⧸ I)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The morphism `\Spec(R/I) ⟶ \Spec R` induced by the quotient map is a closed immersion. -/
instance isClosedImmersion_specQuotientMk {R : CommRingCat.{u}} (I : Ideal R) :
    IsClosedImmersion (specQuotientMk I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- **The spectrum of a quotient of a ring whose spectrum lies in a big fppf site lies in that
site.** -/
theorem BigFppfSite.contains_specQuotient (B : BigFppfSite.{u}) {R : CommRingCat.{u}}
    (hR : B.Contains (Spec R)) (I : Ideal R) :
    B.Contains (Spec (.of (R ⧸ I))) :=
  lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact (specQuotientMk I)) hR

/-- **A morphism to `\Spec R` factors through `\Spec(R/I)` as soon as its kernel on global
functions contains the kernel of `\Spec(R/I) ⟶ \Spec R`.** -/
theorem exists_comp_eq_specQuotientMk {R : CommRingCat.{u}} (I : Ideal R) {T : Scheme.{u}}
    (h : T ⟶ Spec R)
    (hle : RingHom.ker (specQuotientMk I).appTop.hom ≤ RingHom.ker h.appTop.hom) :
    ∃ g : T ⟶ Spec (.of (R ⧸ I)), g ≫ specQuotientMk I = h :=
  ⟨IsClosedImmersion.lift (specQuotientMk I) h
      ((Scheme.ker_le_ker_iff_of_isAffine (specQuotientMk I) h).2 hle),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- **The closed immersion cut out by a finitely generated ideal is locally of finite
presentation.** -/
@[sga "3 XI 6.4" "Affine case"]
theorem locallyOfFinitePresentation_specQuotientMk {R : CommRingCat.{u}} {I : Ideal R}
    (hI : I.FG) : LocallyOfFinitePresentation (specQuotientMk I) := by
  refine (LocallyOfFinitePresentation.SpecMap_iff
    (CommRingCat.ofHom (Ideal.Quotient.mk I))).mpr ?_
  refine RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_
  simpa only [CommRingCat.hom_ofHom, Ideal.mk_ker] using hI

end AlgebraicGeometry

end

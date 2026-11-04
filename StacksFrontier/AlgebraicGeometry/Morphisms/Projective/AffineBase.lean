module

public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjectiveOfHQuasiProjective
public import StacksFrontier.AlgebraicGeometry.LocallyProjectiveHProjective.Sym

/-!
# Projectivity and quasi-projectivity over an affine base

Over an affine base the projective-bundle condition of [Stacks, Tag 01W8] and the embedding
condition of [Stacks, Tag 01VW] collapse onto their `ℙⁿ` forms: a morphism `f : X ⟶ S` with `S`
affine is projective exactly when it is H-projective, and quasi-projective exactly when it is
H-quasi-projective.

This is the content of [Stacks, Tag 01WB] and [Stacks, Tag 01VZ] at a base needing no covering:
both tags reduce the global statement to affine opens of the base, and over an affine base the
whole base is such an open. The reduction itself is already available —
`Stacks.LocallyProjectiveHProjective.isProjectiveMorphism_morphismRestrict_of_isProjective` and
`Stacks.HProjective.isHQuasiProjective_morphismRestrict_of_isQuasiProjective` — so all that is
done here is to take the affine open to be `⊤` and transport the conclusion along
`AlgebraicGeometry.Scheme.topIso`.

## Main results

* `AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine`: over an affine base,
  projective and H-projective agree.
* `AlgebraicGeometry.isQuasiProjective_iff_isHQuasiProjective_of_isAffine`: over an affine base,
  quasi-projective and H-quasi-projective agree.

## References

* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 01VZ](https://stacks.math.columbia.edu/tag/01VZ)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 01VY](https://stacks.math.columbia.edu/tag/01VY)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The restriction of `f` over the whole base is `f` itself, read as a commuting square whose
vertical maps are the canonical isomorphisms of `⊤` with the ambient scheme. -/
theorem topIso_hom_comp_eq_morphismRestrict_top :
    X.topIso.hom ≫ f = f ∣_ ⊤ ≫ S.topIso.hom :=
  (morphismRestrict_ι f ⊤).symm

/-- A projective morphism `f : X ⟶ S` with `S` affine is H-projective. -/
theorem isProjectiveMorphism_of_isProjective_of_isAffine [IsAffine S] (hf : IsProjective f) :
    IsProjectiveMorphism f :=
  (Stacks.LocallyProjectiveHProjective.isProjectiveMorphism_morphismRestrict_of_isProjective hf
    (isAffineOpen_top S)).of_iso X.topIso S.topIso
    (topIso_hom_comp_eq_morphismRestrict_top f)

/-- **Stacks Project, Tag 01WB over an affine base.** A morphism to an affine scheme is
projective if and only if it is H-projective, that is, if and only if its source is a closed
subscheme of `ℙⁿ` over the base for some `n`. -/
theorem isProjective_iff_isProjectiveMorphism_of_isAffine [IsAffine S] :
    IsProjective f ↔ IsProjectiveMorphism f :=
  ⟨isProjectiveMorphism_of_isProjective_of_isAffine f,
    fun hf => hf.isProjective⟩

/-- A quasi-projective morphism `f : X ⟶ S` with `S` affine is H-quasi-projective. -/
theorem isHQuasiProjective_of_isQuasiProjective_of_isAffineBase [IsAffine S]
    (hf : IsQuasiProjective f) : IsHQuasiProjective f :=
  Stacks.HProjective.isHQuasiProjective_of_iso X.topIso S.topIso
    (topIso_hom_comp_eq_morphismRestrict_top f)
    (Stacks.HProjective.isHQuasiProjective_morphismRestrict_of_isQuasiProjective f hf ⊤
      (isAffineOpen_top S))

/-- **Stacks Project, Tag 01VZ over an affine base.** A morphism to an affine scheme is
quasi-projective if and only if it is H-quasi-projective, that is, if and only if its source is
a locally closed subscheme of `ℙⁿ` over the base for some `n` — a quasi-compact immersion. -/
theorem isQuasiProjective_iff_isHQuasiProjective_of_isAffine [IsAffine S] :
    IsQuasiProjective f ↔ IsHQuasiProjective f :=
  ⟨isHQuasiProjective_of_isQuasiProjective_of_isAffineBase f,
    Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f⟩

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Projective and quasi-projective varieties

Let `k` be a field. A *projective variety* over `k` is a variety over `k` whose structure
morphism to the spectrum of `k` is projective, and a *quasi-projective variety* is one whose
structure morphism is quasi-projective. Since `Spec k` is affine the first condition is the same
as H-projectivity — a closed immersion into a projective space over `Spec k`, that is, an
isomorphism onto a closed subscheme of `ℙⁿ_k` — and the second is the same as
H-quasi-projectivity, a quasi-compact immersion into `ℙⁿ_k`, that is, an isomorphism onto a
locally closed subscheme of `ℙⁿ_k`. These are the identifications [Stacks, Tag 04L1] records by
citing Tags 01WB and 01VZ; over an affine base both come from
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase`.

## Main definitions

* `AlgebraicGeometry.IsProjectiveVariety`: the property of a structure morphism to the spectrum
  of a field that makes its source a projective variety.
* `AlgebraicGeometry.IsQuasiProjectiveVariety`: the same for quasi-projective varieties.

## Main results

* `AlgebraicGeometry.isProjectiveVariety_iff` and
  `AlgebraicGeometry.isProjectiveVariety_iff_isProjectiveMorphism`: characterizations of the
  class as a variety together with projectivity of its structure morphism.
* `AlgebraicGeometry.isProjectiveVariety_iff_isProjective'` and
  `AlgebraicGeometry.isProjectiveVariety_iff_isProjective`: the same with projectivity spelled
  as the projective-bundle condition of clause (1) of Definition 01W8, which is the form in
  which Tag 04L1 states the definition.
* `AlgebraicGeometry.isQuasiProjectiveVariety_iff`,
  `AlgebraicGeometry.isQuasiProjectiveVariety_iff_isQuasiProjective` and
  `AlgebraicGeometry.isQuasiProjectiveVariety_iff_isHQuasiProjective`: the corresponding
  characterizations for quasi-projective varieties, the last one by a quasi-compact immersion
  into `ℙⁿ_k`.

## Implementation notes

The structure morphism is an explicit argument, as for `AlgebraicGeometry.IsVariety`. For
`AlgebraicGeometry.IsProjectiveVariety` projectivity is `AlgebraicGeometry.IsProjectiveMorphism`,
the H-projective clause (2) of Definition 01W8, and for
`AlgebraicGeometry.IsQuasiProjectiveVariety` quasi-projectivity is
`AlgebraicGeometry.IsQuasiProjective`, the first condition of Definition 01VW. Neither is a
class, so in both cases the morphism property is a field rather than a parent, and
`IsProjectiveVariety.isProjective` and `IsQuasiProjectiveVariety.isQuasiProjective` are the
accessors downstream statements use where `IsProperVariety` and `IsSmoothVariety` offer a parent
projection.

The two spellings of each notion are interchangeable over `Spec k` by the two equivalences of
`StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase`, so the choice of field is
immaterial; both spellings are offered as characterizations.

`AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety` is a theorem and not an
instance on purpose. As an instance it adds a second route from a projective variety to
`AlgebraicGeometry.IsVariety` and through it to the integrality and irreducibility of `X`, which
pushes the synthesis of `IrreducibleSpace X` in
`StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel` past the default heartbeat
limit. The corresponding statement for proper varieties is an instance because it is the one
the curve files already rely on.

## References

* [Stacks Project, Tag 04L1](https://stacks.math.columbia.edu/tag/04L1)
* [Stacks Project, Tag 01WB](https://stacks.math.columbia.edu/tag/01WB)
* [Stacks Project, Tag 01VZ](https://stacks.math.columbia.edu/tag/01VZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04L1.** A variety over a field is projective when its structure
morphism to the spectrum of the field is H-projective, equivalently projective. -/
@[stacks 04L1 "projective_variety"]
class IsProjectiveVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop extends IsVariety k f where
  /-- The structure morphism of a projective variety is H-projective. -/
  isProjective : IsProjectiveMorphism f

/-- A projective variety is exactly a variety whose structure morphism is H-projective. -/
theorem isProjectiveVariety_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    IsProjectiveVariety k f ↔ IsVariety k f ∧ IsProjectiveMorphism f :=
  ⟨fun h => ⟨h.toIsVariety, h.isProjective⟩,
    fun ⟨hv, hp⟩ => { toIsVariety := hv, isProjective := hp }⟩

/-- **Stacks Project, Tag 04L1, clause (2), the form cited to [Stacks, Tag 01WB].** For a
variety, being a projective variety is equivalent to H-projectivity of its structure morphism,
that is, to `X` being isomorphic over `k` to a closed subscheme of `ℙⁿ_k` for some `n`. -/
@[simp, stacks 04L1 "projective_variety_closed_subscheme"]
theorem isProjectiveVariety_iff_isProjectiveMorphism (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    IsProjectiveVariety k f ↔ IsProjectiveMorphism f := by
  rw [isProjectiveVariety_iff]; exact and_iff_right inferInstance

/-- **Stacks Project, Tag 04L1, clause (2).** A projective variety is exactly a variety whose
structure morphism to the spectrum of the field is projective.

The source defines the notion by projectivity of the structure morphism and observes, citing
[Stacks, Tag 01WB], that it amounts to `X` being isomorphic to a closed subscheme of `ℙⁿ_k` for
some `n`, which is the H-projectivity carried by the class. The two agree over the affine base
`Spec k` by `AlgebraicGeometry.isProjective_iff_isProjectiveMorphism_of_isAffine`. -/
@[stacks 04L1 "projective_variety_2"]
theorem isProjectiveVariety_iff_isProjective' (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    IsProjectiveVariety k f ↔ IsVariety k f ∧ IsProjective f := by
  rw [isProjectiveVariety_iff, isProjective_iff_isProjectiveMorphism_of_isAffine]

/-- For a variety, being a projective variety is equivalent to projectivity of its structure
morphism. -/
theorem isProjectiveVariety_iff_isProjective (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    IsProjectiveVariety k f ↔ IsProjective f := by
  rw [isProjectiveVariety_iff_isProjective']; exact and_iff_right inferInstance

/-- A projective variety is proper, since an H-projective morphism is proper. -/
instance (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [h : IsProjectiveVariety k f] : IsProperVariety k f := by
  have := h.toIsVariety
  have := isProper_of_isProjectiveMorphism f h.isProjective
  exact IsProperVariety.mk

/-- **Stacks Project, Tag 04L1.** A variety over a field is quasi-projective when its structure
morphism to the spectrum of the field is quasi-projective. -/
@[stacks 04L1 "quasi_projective_variety"]
class IsQuasiProjectiveVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop extends IsVariety k f where
  /-- The structure morphism of a quasi-projective variety is quasi-projective. -/
  isQuasiProjective : IsQuasiProjective f

/-- A quasi-projective variety is exactly a variety whose structure morphism is
quasi-projective. -/
theorem isQuasiProjectiveVariety_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    IsQuasiProjectiveVariety k f ↔ IsVariety k f ∧ IsQuasiProjective f :=
  ⟨fun h => ⟨h.toIsVariety, h.isQuasiProjective⟩,
    fun ⟨hv, hq⟩ => { toIsVariety := hv, isQuasiProjective := hq }⟩

/-- For a variety, being a quasi-projective variety is equivalent to quasi-projectivity of its
structure morphism. -/
@[simp]
theorem isQuasiProjectiveVariety_iff_isQuasiProjective (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] :
    IsQuasiProjectiveVariety k f ↔ IsQuasiProjective f := by
  rw [isQuasiProjectiveVariety_iff]; exact and_iff_right inferInstance

/-- **Stacks Project, Tag 04L1, clause (3).** A quasi-projective variety is exactly a variety
whose structure morphism is H-quasi-projective, that is, admits a quasi-compact immersion into
`ℙⁿ_k` over `k` for some `n`, which realizes `X` as a locally closed subscheme of `ℙⁿ_k`.

This is the identification the source records by citing [Stacks, Tag 01VZ]; over the affine base
`Spec k` it is `AlgebraicGeometry.isQuasiProjective_iff_isHQuasiProjective_of_isAffine`. -/
@[stacks 04L1 "quasi_projective_variety_locally_closed_subscheme"]
theorem isQuasiProjectiveVariety_iff_isHQuasiProjective (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    IsQuasiProjectiveVariety k f ↔ IsVariety k f ∧ IsHQuasiProjective f := by
  rw [isQuasiProjectiveVariety_iff, isQuasiProjective_iff_isHQuasiProjective_of_isAffine]

/-- A projective variety is quasi-projective: a closed immersion into `ℙⁿ_k` is in particular a
quasi-compact immersion into `ℙⁿ_k`.

This is deliberately not an instance; see the implementation notes. -/
theorem IsProjectiveVariety.isQuasiProjectiveVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [h : IsProjectiveVariety k f] : IsQuasiProjectiveVariety k f where
  __ := h.toIsVariety
  isQuasiProjective := Stacks.HProjective.isQuasiProjective_of_isHQuasiProjective f
    h.isProjective.isHQuasiProjective

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DifferentialSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale

/-!
# The étale localization isomorphism of relative differentials

Let `p : X ⟶ S` be a morphism of schemes and let `h : T ⟶ X` be étale. For any `q : T ⟶ S` with
`h ≫ p = q`, the canonical map `h^*Ω_{X/S} ⟶ Ω_{T/S}` of the square with horizontal edges `h` and
`𝟙 S` is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.etaleRelativeDifferentialsIso`: the isomorphism
  `h^*Ω_{X/S} ≅ Ω_{T/S}` for an étale `h` and any `q : T ⟶ S` with `h ≫ p = q`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_etale_eq`: for an étale `h` and
  any `q` with `h ≫ p = q`, the canonical map `h^*Ω_{X/S} ⟶ Ω_{T/S}` is an isomorphism.
* `AlgebraicGeometry.Scheme.Hom.isRelativeDifferentialsMap_etaleRelativeDifferentialsIso`: the
  forward map of the isomorphism carries the pulled-back universal differential of a local section
  to the universal differential of its pullback.

## Implementation notes

Naturality of the family in `T` is given by the identity and composition laws of the canonical
maps, `AlgebraicGeometry.relativeDifferentialsMap_id_overBase` and
`AlgebraicGeometry.relativeDifferentialsMap_comp_overBase`, stated for morphisms of `Over S`.

## References

* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX), the étale localization
  of relative differentials.
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV), the canonical map of a
  commutative square and its uniqueness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T X S : Scheme.{u}}

/-- For an étale `h : T ⟶ X` and a `q : T ⟶ S` with `h ≫ p = q`, the canonical map
`h^*Ω_{X/S} ⟶ Ω_{T/S}` is an isomorphism. -/
theorem isIso_relativeDifferentialsMap_of_etale_eq (h : T ⟶ X) (p : X ⟶ S) (q : T ⟶ S)
    (hq : h ≫ p = q) [Etale h] :
    IsIso (relativeDifferentialsMap h p q (𝟙 S) (hq.trans (Category.comp_id q).symm)) := by
  subst hq
  exact isIso_relativeDifferentialsMap_of_comp h p

/-- The étale localization isomorphism `h^*Ω_{X/S} ≅ Ω_{T/S}` for an étale `h : T ⟶ X` and any
`q : T ⟶ S` with `h ≫ p = q`, whose forward map is the canonical map `relativeDifferentialsMap`. -/
noncomputable def etaleRelativeDifferentialsIso (h : T ⟶ X) (p : X ⟶ S) (q : T ⟶ S)
    (hq : h ≫ p = q) [Etale h] :
    (Scheme.Modules.pullback h).obj (relativeDifferentials p) ≅ relativeDifferentials q :=
  @asIso _ _ _ _ _ (isIso_relativeDifferentialsMap_of_etale_eq h p q hq)

/-- The forward map of `etaleRelativeDifferentialsIso h p q hq` is the canonical map
`h^*Ω_{X/S} ⟶ Ω_{T/S}`. -/
@[simp]
theorem etaleRelativeDifferentialsIso_hom (h : T ⟶ X) (p : X ⟶ S) (q : T ⟶ S)
    (hq : h ≫ p = q) [Etale h] :
    (etaleRelativeDifferentialsIso h p q hq).hom =
      relativeDifferentialsMap h p q (𝟙 S) (hq.trans (Category.comp_id q).symm) :=
  rfl

/-- The forward map of `etaleRelativeDifferentialsIso h p q hq` carries the pulled-back universal
differential of a local section to the universal differential of its pullback. -/
theorem isRelativeDifferentialsMap_etaleRelativeDifferentialsIso (h : T ⟶ X) (p : X ⟶ S)
    (q : T ⟶ S) (hq : h ≫ p = q) [Etale h] :
    IsRelativeDifferentialsMap h p q (etaleRelativeDifferentialsIso h p q hq).hom :=
  (isRelativeDifferentialsMap_iff_eq h p q (𝟙 S) (hq.trans (Category.comp_id q).symm) _).mpr rfl

end AlgebraicGeometry.Scheme.Hom

end

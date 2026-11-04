module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsFibre
public import StacksFrontier.Deformation.Examples.Geometric.SpacesRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme

/-!
# The special fibre of a deformation of an algebraic space over the dual numbers

Let `X` be an algebraic space over the field `k` and let `xε` be a point of its deformation
category over an object `Aε` of `𝒞_Λ` carrying a dual-number coordinate, so that the family of
`xε` is an algebraic space `X'` flat over `Spec Aε` together with a cartesian arrow to `(k, X)`.
This file sets up the first order thickening `X ⊂ X'` in the shape the deformation theory of
maps of algebraic spaces ([Stacks Project, Tag 0617]) is stated in:

* `Spec k ⊂ Spec Aε` is a first order thickening of algebraic spaces, the closed subspace
  `K` being the range of the closed immersion `Spec k ⟶ Spec Aε` induced by the residue map;
* its inverse image `G ⊆ X'` is a first order thickening of `X'` ([Stacks Project, Tag 09ZX]).

## Main definitions

* `Deformation.Examples.spaceTotalSpace`: the total space of a point, as an algebraic space.
* `Deformation.Examples.spaceBaseSpecialSubspace`: the closed subspace `Spec k ⊂ Spec A`.
* `Deformation.Examples.spaceSpecialSubspace`: its inverse image `G ⊆ X'`.

## Main results

* `Deformation.Examples.ker_eq_maximalIdeal_of_hom_residueFieldBase`,
  `surjective_of_hom_residueFieldBase`: a morphism of `𝒞_Λ` to the residue field is surjective
  with kernel the maximal ideal.
* `Deformation.Examples.maximalIdeal_sq_eq_bot_of_isCanonicalDualNumberPair`: the maximal ideal
  of an object with a dual-number coordinate has square zero.
* `Deformation.Examples.isFirstOrderThickening_spaceSpecialSubspace`.

## References

* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Ring theory of the base -/

/-- A morphism of `𝒞_Λ` to the residue field has kernel the maximal ideal: it is a local
homomorphism to a field. -/
theorem ker_eq_maximalIdeal_of_hom_residueFieldBase {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) :
    RingHom.ker f.hom.toRingHom = IsLocalRing.maximalIdeal A := by
  have := f.isLocal
  ext a
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h ha
    have := ha.map f.hom.toRingHom
    rw [h] at this
    exact not_isUnit_zero this
  · intro h
    by_contra hne
    exact h (isUnit_of_map_unit f.hom.toRingHom a (Ne.isUnit (G₀ := k) hne))

/-- A morphism of `𝒞_Λ` to the residue field is surjective: it is compatible with the
identifications of the residue fields with `k`. -/
theorem surjective_of_hom_residueFieldBase {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) : Function.Surjective f.hom := by
  intro c
  obtain ⟨r, hr⟩ := A.residueEquiv.surjective c
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  refine ⟨a, ?_⟩
  have h := f.residue_comm a
  rw [residueFieldBase_residueEquiv_residue] at h
  exact h.trans hr

/-- The maximal ideal of an object of `𝒞_Λ` with a dual-number coordinate has square zero. -/
theorem maximalIdeal_sq_eq_bot_of_isCanonicalDualNumberPair
    {A₀ Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {g : A₀ ⟶ Aε} {e : Aε ⟶ A₀} (hpair : IsCanonicalDualNumberPair g e) :
    IsLocalRing.maximalIdeal Aε ^ 2 = ⊥ := by
  obtain ⟨-, iε, -, -, -⟩ := hpair
  have hm : ∀ x ∈ IsLocalRing.maximalIdeal Aε, TrivSqZeroExt.fst (iε x) = 0 := by
    intro x hx
    have hx' : iε x ∈ IsLocalRing.maximalIdeal (DualNumber k) :=
      (IsLocalRing.mem_maximalIdeal _).2 fun hu =>
        ((IsLocalRing.mem_maximalIdeal _).1 hx) ((isUnit_map_iff iε.toRingEquiv x).1 hu)
    by_contra hne
    exact ((IsLocalRing.mem_maximalIdeal _).1 hx') ((TrivSqZeroExt.isUnit_iff_isUnit_fst).2
      (Ne.isUnit hne))
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [Ideal.mem_bot]
  apply iε.injective
  rw [map_mul, map_zero]
  ext
  · simp [hm x hx]
  · simp [TrivSqZeroExt.snd_mul, hm x hx, hm y hy]

variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))

/-- **`Spec k ⊂ Spec A` is a square-zero closed immersion** for an object `A` of `𝒞_Λ` whose
maximal ideal has square zero. -/
theorem isSquareZeroClosedImmersion_spaceBaseOverMap {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) (hA : IsLocalRing.maximalIdeal A ^ 2 = ⊥) :
    IsSquareZeroClosedImmersion B (Spec (.of Λ)) hΛ (spaceBaseOverMap B hΛ hSpec f) := by
  rw [IsSquareZeroClosedImmersion, toScheme_map_spaceBaseOverMap]
  exact Stacks.Smooth.isFirstOrderThickening_specMap (CommRingCat.ofHom f.hom.toRingHom)
    (surjective_of_hom_residueFieldBase f)
    (by rw [CommRingCat.hom_ofHom, ker_eq_maximalIdeal_of_hom_residueFieldBase]; exact hA)

/-- **The closed subspace `Spec k ⊂ Spec A`**: the range of the closed immersion induced by a
morphism `A ⟶ k` of `𝒞_Λ`. -/
def spaceBaseSpecialSubspace {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) :
    ClosedSubspaces B (Spec (.of Λ)) hΛ (schemeSpace
      (spaceBaseOver B hΛ hSpec A)).1 :=
  ⟨Subfunctor.range (yoneda.map (spaceBaseOverMap B hΛ hSpec f)),
    isClosedSubspace_range_yoneda_map B (Spec (.of Λ)) hΛ _ (by
      rw [toScheme_map_spaceBaseOverMap]
      exact IsClosedImmersion.spec_of_surjective _ (surjective_of_hom_residueFieldBase f))⟩

/-- **`Spec k ⊂ Spec A` is a first order thickening** when the maximal ideal of `A` has square
zero. -/
theorem isFirstOrderThickening_spaceBaseSpecialSubspace {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : A ⟶ residueFieldBase Λ k) (hA : IsLocalRing.maximalIdeal A ^ 2 = ⊥) :
    IsFirstOrderThickening B (Spec (.of Λ)) hΛ
      (schemeSpace (spaceBaseOver B hΛ hSpec A))
      (spaceBaseSpecialSubspace B hΛ hSpec f).1 :=
  isFirstOrderThickening_range_yoneda_map B (Spec (.of Λ)) hΛ _
    (isSquareZeroClosedImmersion_spaceBaseOverMap B hΛ hSpec f hA)

/-! ### The special fibre of a family -/

/-- The total space of a flat family of algebraic spaces, as an algebraic space. -/
abbrev spaceTotalSpace (P : FlatAlgebraicSpaceFamily B hΛ hSpec) :
    AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
  ⟨P.space, P.algebraic⟩

/-- The structure morphism of a flat family, as a morphism of algebraic spaces. -/
abbrev spaceTotalToBase (P : FlatAlgebraicSpaceFamily B hΛ hSpec) :
    spaceTotalSpace B hΛ hSpec P ⟶ schemeSpace (spaceBaseOver B hΛ hSpec P.base) :=
  ObjectProperty.homMk P.toBase

/-- **The special fibre `G ⊆ X'` of a flat family over `A`**, for a morphism `A ⟶ k`: the
inverse image of `Spec k ⊂ Spec A`. -/
abbrev spaceSpecialSubspace (P : FlatAlgebraicSpaceFamily B hΛ hSpec)
    (f : P.base ⟶ residueFieldBase Λ k) :
    ClosedSubspaces B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P).1 :=
  preimageSubspace B (Spec (.of Λ)) hΛ (spaceTotalToBase B hΛ hSpec P)
    (spaceBaseSpecialSubspace B hΛ hSpec f)

/-- **The special fibre of a family over an object with square-zero maximal ideal is a first
order thickening of its total space** ([Stacks Project, Tag 09ZX]). -/
theorem isFirstOrderThickening_spaceSpecialSubspace (P : FlatAlgebraicSpaceFamily B hΛ hSpec)
    (f : P.base ⟶ residueFieldBase Λ k) (hA : IsLocalRing.maximalIdeal P.base ^ 2 = ⊥) :
    IsFirstOrderThickening B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec P)
      (spaceSpecialSubspace B hΛ hSpec P f).1 :=
  isFirstOrderThickening_preimage B (Spec (.of Λ)) hΛ _ (spaceTotalToBase B hΛ hSpec P)
    (isFirstOrderThickening_spaceBaseSpecialSubspace B hΛ hSpec f hA)

end Deformation.Examples

end

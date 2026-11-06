module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.HenselianLocalRingStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty

/-!
# The henselian local ring along an isomorphism of algebraic spaces

Let `e : F ⟶ G` be an isomorphism of decent algebraic spaces over `S` and let `x` be a point of
`F`. An elementary étale neighborhood `(U, u)` of `x` becomes one of `e(x)` by composing its
structure morphism with `e`, with the same scheme and the same point; so the henselian local
rings `𝒪^h_{F, x}` and `𝒪^h_{G, e(x)}` are both henselizations of the one local ring `𝒪_{U, u}`
(Stacks 0EMY), and the universal property of the henselization (Stacks 04GS) identifies them.

## Main definitions

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.compIso`: an elementary étale
  neighborhood of `x` read as one of `e(x)`.
* `AlgebraicGeometry.Space.henselianLocalRingEquivOfIsIso`: the ring isomorphism
  `𝒪^h_{G, y} ≃ 𝒪^h_{F, x}` for `y = e(x)`.

## References

* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 0BGU](https://stacks.math.columbia.edu/tag/0BGU)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)

/-- An elementary étale neighborhood of a point `x` of `F`, read as an elementary étale
neighborhood of `e(x)` for an isomorphism `e : F ⟶ G`: the same scheme and the same point, with
the structure morphism composed with `e`. -/
def ElementaryEtaleNeighborhood.compIso {x : points B S hS F}
    (E : ElementaryEtaleNeighborhood B S hS F hF x) (e : F ⟶ G) [IsIso e] :
    ElementaryEtaleNeighborhood B S hS G hG (pointsMap B S hS F e x) where
  scheme := E.scheme
  point := E.point
  residueField_contained := E.residueField_contained
  toSpace := E.toSpace ≫ e
  etale_toSpace := isEtale_comp B S hS E.etale_toSpace (isEtale_of_isIso B S hS e)
  map_point := by
    rw [pointsMap_comp, Function.comp_apply, E.map_point]
  mono_residueField := by
    have := E.mono_residueField
    rw [← Category.assoc]
    exact mono_comp' this (IsIso.mono_of_iso e)

variable (hFdec : IsDecentSpace B S hS F) (hGdec : IsDecentSpace B S hS G)

/-- **The henselian local ring is invariant under isomorphism.** For an isomorphism `e : F ⟶ G`
of decent algebraic spaces and a point `x` of `F` with image `y = e(x)`, the henselian local
rings `𝒪^h_{G, y}` and `𝒪^h_{F, x}` are isomorphic: for an elementary étale neighborhood
`(U, u)` of `x`, both are henselizations of `𝒪_{U, u}` (Stacks 0EMY), and the two local
`𝒪_{U, u}`-algebra maps of Stacks 04GS between them compose to the identity on either side by
the uniqueness clause of Stacks 04GS. -/
def henselianLocalRingEquivOfIsIso (e : F ⟶ G) [IsIso e] (x : points B S hS F)
    (y : points B S hS G) (hy : pointsMap B S hS F e x = y) :
    (henselianLocalRing B S hS G hG y hGdec : Type (u + 1)) ≃+*
      (henselianLocalRing B S hS F hF x hFdec : Type (u + 1)) := by
  subst hy
  let E := (exists_affine_elementaryEtaleNeighborhood' B S hS hF hFdec x).choose
  let E' := E.compIso B S hS hF hG e
  let A := E.scheme.left.1.presheaf.stalk E.point
  letI := henselianLocalRing_isLocalRing B S hS F hF x hFdec
  letI := henselianLocalRing_isLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec
  letI : Algebra A (henselianLocalRing B S hS F hF x hFdec : Type (u + 1)) :=
    stalkAlgebra B S hS F hF x hFdec E
  letI : Algebra A (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec :
      Type (u + 1)) :=
    stalkAlgebra B S hS G hG (pointsMap B S hS F e x) hGdec E'
  haveI hhF := henselianLocalRing_isHenselization B S hS F hF x hFdec E
  haveI hhG : IsHenselization A (ResidueField A)
      (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec : Type (u + 1)) :=
    henselianLocalRing_isHenselization B S hS G hG (pointsMap B S hS F e x) hGdec E'
  haveI : IsLocalHom (algebraMap A (henselianLocalRing B S hS F hF x hFdec : Type (u + 1))) :=
    IsHenselization.isLocalHom (R := A) (L := ResidueField A)
  haveI : IsLocalHom (algebraMap A (henselianLocalRing B S hS G hG (pointsMap B S hS F e x)
      hGdec : Type (u + 1))) :=
    IsHenselization.isLocalHom (R := A) (L := ResidueField A)
  haveI : HenselianLocalRing (henselianLocalRing B S hS F hF x hFdec : Type (u + 1)) :=
    IsHenselization.henselian A (ResidueField A)
  haveI : HenselianLocalRing (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec :
      Type (u + 1)) :=
    IsHenselization.henselian A (ResidueField A)
  have hiF := IsHenselization.ind_etale (R := A) (L := ResidueField A)
    (Rh := (henselianLocalRing B S hS F hF x hFdec : Type (u + 1)))
  have hiG := IsHenselization.ind_etale (R := A) (L := ResidueField A)
    (Rh := (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec : Type (u + 1)))
  have hsF := (IsHenselization.residueField_map_bijective (R := A)
    (Rh := (henselianLocalRing B S hS F hF x hFdec : Type (u + 1)))).2
  have hsG := (IsHenselization.residueField_map_bijective (R := A)
    (Rh := (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec :
      Type (u + 1)))).2
  let φ := HenselianLocalRing.indEtaleAlgHom
    (Sh := (henselianLocalRing B S hS F hF x hFdec : Type (u + 1))) hiG hsG
  let ψ := HenselianLocalRing.indEtaleAlgHom
    (Sh := (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec : Type (u + 1)))
    hiF hsF
  haveI := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := (henselianLocalRing B S hS F hF x hFdec : Type (u + 1))) hiG hsG
  haveI := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := (henselianLocalRing B S hS G hG (pointsMap B S hS F e x) hGdec : Type (u + 1)))
    hiF hsF
  refine AlgEquiv.toRingEquiv (AlgEquiv.ofAlgHom φ ψ ?_ ?_)
  · exact (HenselianLocalRing.indEtaleAlgHom_unique hiF hsF (φ.comp ψ)
      ⟨fun a ha => isUnit_of_map_unit ψ a (isUnit_of_map_unit φ _ ha)⟩).trans
      (HenselianLocalRing.indEtaleAlgHom_unique hiF hsF (AlgHom.id A _)
        ⟨fun _ ha => ha⟩).symm
  · exact (HenselianLocalRing.indEtaleAlgHom_unique hiG hsG (ψ.comp φ)
      ⟨fun a ha => isUnit_of_map_unit φ a (isUnit_of_map_unit ψ _ ha)⟩).trans
      (HenselianLocalRing.indEtaleAlgHom_unique hiG hsG (AlgHom.id A _)
        ⟨fun _ ha => ha⟩).symm

end AlgebraicGeometry.Space

end

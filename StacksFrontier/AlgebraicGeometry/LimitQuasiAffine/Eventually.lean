module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Quasi-affineness of a limit holds at every late enough stage

Let `D : I ⥤ Scheme` be a cofiltered diagram of quasi-compact quasi-separated schemes with affine
transition morphisms, and let `c` be a limit cone. Mathlib's
`AlgebraicGeometry.Scheme.exists_isQuasiAffine_of_isLimit` shows that if `c.pt` is quasi-affine
then some `D.obj i` is quasi-affine. Since a scheme admitting an affine morphism to a quasi-affine
scheme is quasi-affine (`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`), every stage
`D.obj j` with a morphism `j ⟶ i` is then quasi-affine as well. This is the statement of
Stacks Tag 01Z5.

## Main results

* `AlgebraicGeometry.Scheme.exists_forall_isQuasiAffine_of_isLimit`: if the limit is
  quasi-affine, there is `i₀` such that `D.obj i` is quasi-affine for every `i ⟶ i₀`.

## References

* [Stacks Project, Tag 01Z5](https://stacks.math.columbia.edu/tag/01Z5)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)

include hc in
/-- Suppose `{ Xᵢ }` is a cofiltered inverse system of quasi-compact quasi-separated schemes with
affine transition maps. If `lim Xᵢ` is quasi-affine, then there is an index `i₀` such that `Xᵢ`
is quasi-affine for every `i ⟶ i₀`. -/
@[stacks 01Z5 "Stated for a cofiltered index category; `i ⟶ i₀` plays the role of
`i ≥ i₀`."]
lemma Scheme.exists_forall_isQuasiAffine_of_isLimit [IsCofiltered I]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ (i : I), CompactSpace (D.obj i)]
    [∀ (i : I), QuasiSeparatedSpace (D.obj i)]
    [IsQuasiAffine c.pt] :
    ∃ i₀, ∀ i (_ : i ⟶ i₀), IsQuasiAffine (D.obj i) := by
  obtain ⟨i₀, hi₀⟩ := Scheme.exists_isQuasiAffine_of_isLimit D c hc
  exact ⟨i₀, fun _ f ↦ IsQuasiAffine.of_isAffineHom (D.map f)⟩

end AlgebraicGeometry

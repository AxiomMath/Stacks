module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.WeierstrassEquation
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCoordinateChange
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicIso

/-!
# Every elliptic curve over a field has a Weierstrass equation

An elliptic curve `(E, f, 0)` over a field `k` — a pointed proper family, smooth of relative
dimension one, with `dim_k H⁰(E, 𝒪_E) = 1` and genus one — is isomorphic as a pointed family to
the plane cubic of a Weierstrass equation with invertible discriminant, with its point
`(0 : 1 : 0)` at infinity. Read at the fibres of a family, this is the input of the proof of
[Stacks, Tag 072T] that the Weierstrass family `W ⟶ 𝓜₁,₁` is surjective: for an elliptic curve
`E'` over a scheme `S'` and a point `s'` of `S'`, the fibre of `E'` at `s'` is the restriction of
the Weierstrass family along a point of `W` with values in the residue field of `s'`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_familyIso_familyOf`: an elliptic
  curve over a field is isomorphic to the plane cubic of a Weierstrass equation.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.exists_comparison_fromSpecResidueField`:
  the fibre of an elliptic curve at a point is a triple `(a, a', α)` over the residue field whose
  morphism `a'` is the canonical one.

## Implementation notes

The plane cubic of a Weierstrass curve `C` over `k` is the pointed family `familyOf C`; when the
discriminant of `C` is invertible, `C` is the base change of the generic equation along the point
`baseRingHom C` of `W`, and `familyOfMapIso` identifies the restriction of the Weierstrass family
along that point with `familyOf C`. The field case itself is
`AlgebraicGeometry.GenusOne.exists_weierstrassCurve_iso`.

## References

* [Stacks Project, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

/-- **An elliptic curve over a field has a Weierstrass equation**: a pointed family over a field
`k` which is proper and smooth of relative dimension one, with one-dimensional `H⁰` and genus one,
is isomorphic to the plane cubic of a Weierstrass curve over `k` with invertible discriminant, its
section going to the point at infinity. -/
theorem exists_familyIso_familyOf {k : Type u} [Field k] (E : PointedFamily (Spec (.of k)))
    [IsProper E.map] [SmoothOfRelativeDimension 1 E.map]
    (h0 : Module.finrank k (structureSheafCohomology E.map 0) = 1) (hg : genus E.map = 1) :
    ∃ (C : WeierstrassCurve k) (_ : C.IsElliptic), Nonempty (FamilyIso (familyOf C) E) := by
  obtain ⟨C, hC, e, hover, hzero⟩ :=
    AlgebraicGeometry.GenusOne.exists_weierstrassCurve_iso E.map h0 hg E.zero E.zero_map
  refine ⟨C, hC, ⟨⟨e.symm, ?_, ?_⟩⟩⟩
  · change e.inv ≫ E.map = projectionOf C
    rw [← hover, Iso.inv_hom_id_assoc]
  · change zeroOf C ≫ e.inv = E.zero
    rw [← hzero, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The fibre of an elliptic curve at a point has a Weierstrass equation**, as a triple
`(a, a', α)` over the residue field: for an elliptic curve `(E', f', 0')` over `S'` and a point
`s'` of `S'`, there is a triple over `Spec κ(s')` whose morphism to `S'` is the canonical one. -/
theorem exists_comparison_fromSpecResidueField {S' : Scheme.{u}} (E' : PointedFamily S')
    (hE' : E'.IsElliptic) (s' : S') :
    ∃ x : Comparison family.{u} E' (Spec (S'.residueField s')),
      x.snd = S'.fromSpecResidueField s' := by
  obtain ⟨hprop, hsmooth, hfib⟩ := hE'
  have hprop' : IsProper (pullback.snd E'.map (S'.fromSpecResidueField s')) := inferInstance
  have hsmooth' : SmoothOfRelativeDimension 1 (pullback.snd E'.map (S'.fromSpecResidueField s')) :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback E'.map _) hsmooth
  obtain ⟨C, hC, ⟨φ⟩⟩ := @exists_familyIso_familyOf _ _ (E'.pullback (S'.fromSpecResidueField s'))
    hprop' hsmooth' (hfib s').1 (hfib s').2
  have hcurve : FamilyIso (familyOf (curve.{u}.map (baseRingHom C))) (familyOf C) := by
    rw [curve_map_baseRingHom C]
    exact FamilyIso.refl _
  exact ⟨Comparison.ofFamilyIso (Spec.map (CommRingCat.ofHom (baseRingHom C)))
    (S'.fromSpecResidueField s')
    (((familyOfMapIso curve.{u} (baseRingHom C)).trans hcurve).trans φ), rfl⟩

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end

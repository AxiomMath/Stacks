module

public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicIso
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyFibres
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilySmooth

/-!
# The Weierstrass family is an elliptic curve

This file proves the assertion of [Stacks, Tag 072S] that the Weierstrass family
`(E_W, f_W, 0_W)` over `W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])` is an elliptic curve in the sense of
[Stacks, Tag 072J], and more generally that the plane cubic of any Weierstrass equation over a
ring `R` whose discriminant is a unit, with its section `(0 : 1 : 0)`, is an elliptic curve over
`Spec R`.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.residueMapOf`: the ring map `R → κ(s)` to
  the residue field at a point `s` of `Spec R`.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isPullback_fromSpecResidueField`: the
  fibre of the plane cubic of `C` at `s` is the plane cubic of `C` read over `κ(s)`.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isElliptic_familyOf`: the plane cubic of a
  Weierstrass equation with invertible discriminant is an elliptic curve.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isElliptic_family`: **Tag 072S**, the
  Weierstrass family over `W` is an elliptic curve.

## Implementation notes

The three clauses of `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsElliptic` are
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isProper_projectionOf`,
`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.smoothOfRelativeDimension_projectionOf` and
the computation of `H⁰` and of the genus of a plane cubic over a field in
`StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamilyFibres`. The fibre at `s` is the
pullback along `Spec κ(s) ⟶ Spec R`, which is `Spec` of `residueMapOf s`; the plane cubic commutes
with base change (`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isPullback_mapMap`), so the
fibre is isomorphic over `Spec κ(s)` to the plane cubic of `C.map (residueMapOf s)`, and the
dimensions of the cohomology groups of the structure sheaf do not see the isomorphism
(`AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.finrank_structureSheafCohomology_iso_comp`).
The fibres are plane cubics over a field, for which no hypothesis on the discriminant is needed.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 072J](https://stacks.math.columbia.edu/tag/072J)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

variable {R : Type u} [CommRing R] (C : WeierstrassCurve R)

/-- The ring map `R → κ(s)` to the residue field at a point `s` of `Spec R`, whose spectrum is the
inclusion of that point. -/
def residueMapOf (s : Spec (CommRingCat.of R)) :
    R →+* (Spec (CommRingCat.of R)).residueField s :=
  (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom

/-- `Spec` of `residueMapOf s` is the inclusion `Spec κ(s) ⟶ Spec R` of the point `s`. -/
theorem SpecMap_residueMapOf (s : Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (residueMapOf s)) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s := by
  rw [residueMapOf, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The image of `a ∈ R` in the residue field at `x` is a unit exactly when `a ∉ x`. -/
theorem isUnit_residueMapOf_iff (x : Spec (CommRingCat.of R)) (a : R) :
    IsUnit (residueMapOf x a) ↔ a ∉ x.asIdeal := by
  have hx : x.asIdeal = RingHom.ker (residueMapOf x) := by
    obtain ⟨pt⟩ : Nonempty (Spec ((Spec (CommRingCat.of R)).residueField x)) := inferInstance
    have h := Scheme.fromSpecResidueField_apply (X := Spec (CommRingCat.of R)) x pt
    rw [← SpecMap_residueMapOf, Spec.map_base] at h
    have h2 : x.asIdeal = Ideal.comap (residueMapOf x) pt.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal h).symm
    rw [h2, (Ideal.eq_bot_or_top pt.asIdeal).resolve_right pt.isPrime.ne_top]
    rfl
  rw [hx, RingHom.mem_ker, isUnit_iff_ne_zero]

/-- **The fibre of the plane cubic at a point is the plane cubic of the residue equation.** The
square formed by `mapMap C (residueMapOf s)`, the two projections and
`Spec κ(s) ⟶ Spec R` is cartesian. -/
theorem isPullback_fromSpecResidueField (s : Spec (CommRingCat.of R)) :
    IsPullback (mapMap C (residueMapOf s)) (projectionOf (C.map (residueMapOf s)))
      (projectionOf C) ((Spec (CommRingCat.of R)).fromSpecResidueField s) := by
  have h := isPullback_mapMap C (residueMapOf s)
  rwa [SpecMap_residueMapOf] at h

/-- The dimension of `Hⁿ` of the structure sheaf of the fibre of the plane cubic at `s` is that of
the plane cubic of `C.map (residueMapOf s)` over `κ(s)`. -/
theorem finrank_structureSheafCohomology_fiberToSpecResidueField (s : Spec (CommRingCat.of R))
    (n : ℕ) :
    Module.finrank ((Spec (CommRingCat.of R)).residueField s)
        (structureSheafCohomology (R := (Spec (CommRingCat.of R)).residueField s)
          ((projectionOf C).fiberToSpecResidueField s) n) =
      Module.finrank ((Spec (CommRingCat.of R)).residueField s)
        (structureSheafCohomology (projectionOf (C.map (residueMapOf s))) n) := by
  have h := isPullback_fromSpecResidueField C s
  have e : (projectionOf C).fiberToSpecResidueField s =
      h.isoPullback.symm.hom ≫ projectionOf (C.map (residueMapOf s)) :=
    (h.isoPullback_inv_snd).symm
  rw [e]
  exact finrank_structureSheafCohomology_iso_comp _ _ _ n

/-- **Stacks Project, Tag 072S.** The plane cubic of a Weierstrass equation with invertible
discriminant, with its section at infinity, is an elliptic curve over `Spec R`. -/
@[stacks 072S "E_W over a ring with Δ invertible is an elliptic curve"]
theorem isElliptic_familyOf [C.IsElliptic] : (familyOf C).IsElliptic := by
  refine ⟨isProper_projectionOf C, smoothOfRelativeDimension_projectionOf C C.isUnit_Δ,
    fun s => ⟨?_, ?_⟩⟩
  · exact (finrank_structureSheafCohomology_fiberToSpecResidueField C s 0).trans
      (finrank_structureSheafCohomology_projectionOf_zero _)
  · exact (finrank_structureSheafCohomology_fiberToSpecResidueField C s 1).trans
      (genus_projectionOf _)

/-- **Stacks Project, Tag 072S.** The Weierstrass family `(E_W, f_W, 0_W)` over
`W = Spec(ℤ[a₁, a₂, a₃, a₄, a₆, 1/Δ])` is an elliptic curve. -/
@[stacks 072S "(E_W, f_W, 0_W) is an elliptic curve"]
theorem isElliptic_family : family.{u}.IsElliptic := isElliptic_familyOf curve

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

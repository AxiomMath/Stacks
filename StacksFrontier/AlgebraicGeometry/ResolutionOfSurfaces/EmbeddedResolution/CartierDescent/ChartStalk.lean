module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.AffineIdealSheaf

/-!
# The stalk dictionary at a point of an affine chart of a blowup

Let `S` be a scheme, `ℐ` a quasi-coherent sheaf of ideals on `S`, `U` an affine open of `S` and
`a ∈ ℐ(U)`. The chart `Stacks.Blowup.blowUpAffineChart ℐ U ha` is an open immersion of
`Spec Γ(S, U)[ℐ(U)/a]` into the blowup of `S` in `ℐ`; these charts cover the preimage of `U` by
the second assertion of [Stacks, Tag 0804].

This file is the dictionary that turns a computation with ideals of the chart algebra
`Bx = Γ(S, U)[ℐ(U)/a]` into a computation with stalks of an ideal sheaf on the blowup. For a
quasi-coherent ideal sheaf `K` on the blowup and a point `w` of the chart there is a ring
isomorphism from the local ring of the blowup at the image of `w` to the localisation of `Bx` at
the prime `w.asIdeal`, and it carries the stalk of `K` to the extension of the chart ideal of `K`.
The two invariants of `K` which the colength bookkeeping of [Stacks, Tag 0AGT] consumes — the
colength of the stalk, and membership of the support — are therefore read off the chart algebra
alone.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.isIso_stalkMap_blowUpAffineChart`: a chart of a
  blowup induces an isomorphism on every local ring.
* `Stacks.ResolutionOfSurfaces.CartierDescent.nonempty_ringEquiv_stalk_chart`: there is a ring
  isomorphism from the stalk of the blowup at a chart point to the localisation of the chart
  algebra at the corresponding prime, carrying the stalk of `K` to the extension of the chart
  ideal of `K`.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_chart_eq`: the colength of the
  stalk of `K` at a chart point is the colength of the localised chart ideal.
* `Stacks.ResolutionOfSurfaces.CartierDescent.mem_support_chart_iff`: the image of a chart point
  lies in the support of `K` exactly when the chart ideal of `K` is contained in the prime.

## Implementation notes

A point of the chart is spelled as an element of
`PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) a))`, as the affine sibling
`CartierDescent.AffineIdealSheaf` spells a point of `Spec R`; that type is definitionally equal
to the carrier of the chart, so the chart
morphism applies to such a `w` with no coercion, and the prime attached to `w` is simply
`w.asIdeal` — no `IsAffineOpen.primeIdealOf` and no `Scheme.isoSpec` appear. The chart ideal of
`K` is correspondingly the image of `(K.comap c).ideal ⟨⊤, _⟩` under `(Scheme.ΓSpecIso _).hom`,
which is the ideal of the chart algebra that the affine sibling's statements are about.

All three results are the composite of two steps. The chart is an open immersion, hence an
isomorphism on local rings (`AlgebraicGeometry.IsOpenImmersion.iff_isIso_stalkMap`), so the
question transports to the affine scheme `Spec Bx` and the ideal sheaf `K.comap c`: for the stalk
ideal by `AlgebraicGeometry.IdealSheafData.stalk_comap`, for the colength by
`Stacks.ResolutionOfSurfaces.CartierDescent.length_stalk_quotient_comap_eq_of_isOpenImmersion`,
and for the support by `AlgebraicGeometry.Scheme.IdealSheafData.support_comap`. The affine
sibling then supplies the rest, as `map_stalkIso_stalk`, `length_stalk_quotient_eq` and
`mem_support_iff_le`.

The isomorphism of `nonempty_ringEquiv_stalk_chart` is returned inside an existential rather than
bundled as a definition: consumers use it only to transport a length or a membership, never its
value, and the two transports they want are already the other two results of this file.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Stacks.ResolutionOfSurfaces.CartierDescent

variable {S : Scheme.{u}} {ℐ : S.IdealSheafData} {U : S.affineOpens} {a : Γ(S, U.1)}
  (ha : a ∈ ℐ.ideal U)

/-- **An affine chart of a blowup induces an isomorphism on every local ring**, being an open
immersion. -/
public theorem isIso_stalkMap_blowUpAffineChart
    (w : PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) a))) :
    IsIso ((Stacks.Blowup.blowUpAffineChart ℐ U ha).stalkMap w) :=
  (IsOpenImmersion.iff_isIso_stalkMap.mp
    (inferInstance : IsOpenImmersion (Stacks.Blowup.blowUpAffineChart ℐ U ha))).2 w

/-- **The stalk of the blowup at a point of an affine chart is the localisation of the chart
algebra, and it carries the stalk of an ideal sheaf to the localised chart ideal.** For a
quasi-coherent ideal sheaf `K` on the blowup of `S` in `ℐ` and a prime `w` of the chart algebra
`Γ(S, U)[ℐ(U)/a]` there is a ring isomorphism from `𝒪_{X', c w}` to `Localization.AtPrime
w.asIdeal` under which the stalk of `K` becomes the extension of the ideal of `K.comap c` on the
chart.

This is the dictionary by which an ideal computation in the affine blowup algebra becomes a
statement about stalks on the blowup, as the colength bookkeeping of [Stacks, Tag 0AGT] requires;
the chart itself is the second assertion of [Stacks, Tag 0804]. -/
public theorem nonempty_ringEquiv_stalk_chart (K : (Stacks.Blowup.blowUp ℐ).IdealSheafData)
    (w : PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) a))) :
    ∃ e : (Stacks.Blowup.blowUp ℐ).presheaf.stalk
          ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w) ≃+*
        Localization.AtPrime w.asIdeal,
      Ideal.map e.toRingHom (AlgebraicGeometry.IdealSheafData.stalk K
          ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w)) =
        Ideal.map (algebraMap _ (Localization.AtPrime w.asIdeal))
          (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a))).hom.hom
            ((K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)).ideal
              ⟨⊤, isAffineOpen_top _⟩)) := by
  have hiso := isIso_stalkMap_blowUpAffineChart ha w
  have h1 : Ideal.map (asIso ((Stacks.Blowup.blowUpAffineChart ℐ U ha).stalkMap
          w)).commRingCatIsoToRingEquiv.toRingHom
        (AlgebraicGeometry.IdealSheafData.stalk K
          ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w)) =
      AlgebraicGeometry.IdealSheafData.stalk
        (K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)) w :=
    (AlgebraicGeometry.IdealSheafData.stalk_comap K
      (Stacks.Blowup.blowUpAffineChart ℐ U ha) w).symm
  have h2 := Ideal.map_map
    (asIso ((Stacks.Blowup.blowUpAffineChart ℐ U ha).stalkMap
      w)).commRingCatIsoToRingEquiv.toRingHom
    (Spec.stalkIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a))
      w).commRingCatIsoToRingEquiv.toRingHom
    (I := AlgebraicGeometry.IdealSheafData.stalk K
      ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w))
  refine ⟨(asIso ((Stacks.Blowup.blowUpAffineChart ℐ U ha).stalkMap
      w)).commRingCatIsoToRingEquiv.trans
    (Spec.stalkIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a)) w).commRingCatIsoToRingEquiv, ?_⟩
  rw [RingEquiv.toRingHom_trans']
  exact h2.symm.trans ((congrArg (Ideal.map
      (Spec.stalkIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a))
        w).commRingCatIsoToRingEquiv.toRingHom) h1).trans
    (map_stalkIso_stalk (K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)) w))

/-- **The colength of the stalk of an ideal sheaf at a point of an affine chart of a blowup is
the colength of the localised chart ideal.** The chart is an open immersion, so the local ring of
the blowup at `c w` is the local ring of `Spec Γ(S, U)[ℐ(U)/a]` at `w`, that is the localisation
of the chart algebra at `w.asIdeal`, and under that identification the stalk of `K` becomes the
extension of the chart ideal.

This is the form in which the colength drop of [Stacks, Tag 0AGT] is computed. -/
public theorem length_stalk_quotient_chart_eq (K : (Stacks.Blowup.blowUp ℐ).IdealSheafData)
    (w : PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) a))) :
    Module.length
        ((Stacks.Blowup.blowUp ℐ).presheaf.stalk
          ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w))
        ((Stacks.Blowup.blowUp ℐ).presheaf.stalk
            ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w) ⧸
          AlgebraicGeometry.IdealSheafData.stalk K
            ((Stacks.Blowup.blowUpAffineChart ℐ U ha).base w)) =
      Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap _ (Localization.AtPrime w.asIdeal))
            (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a))).hom.hom
              ((K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)).ideal
                ⟨⊤, isAffineOpen_top _⟩))) :=
  (length_stalk_quotient_comap_eq_of_isOpenImmersion
      (Stacks.Blowup.blowUpAffineChart ℐ U ha) K w).symm.trans
    (length_stalk_quotient_eq (K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)) w)

/-- **A point of an affine chart of a blowup lies over the support of an ideal sheaf exactly when
the chart ideal is contained in the corresponding prime.** The support of the inverse image of `K`
on the chart is the preimage of the support of `K`, and on the affine chart that support is the
zero locus of the chart ideal. -/
public theorem mem_support_chart_iff (K : (Stacks.Blowup.blowUp ℐ).IdealSheafData)
    (w : PrimeSpectrum (CommRingCat.of (affineBlowup (ℐ.ideal U) a))) :
    (Stacks.Blowup.blowUpAffineChart ℐ U ha).base w ∈ K.support ↔
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (affineBlowup (ℐ.ideal U) a))).hom.hom
          ((K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)).ideal ⟨⊤, isAffineOpen_top _⟩) ≤
        w.asIdeal := by
  have h := mem_support_iff_le (K.comap (Stacks.Blowup.blowUpAffineChart ℐ U ha)) w
  rw [Scheme.IdealSheafData.support_comap] at h
  exact h

end Stacks.ResolutionOfSurfaces.CartierDescent

end

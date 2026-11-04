module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectCompactQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectRetract
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SupportedClassicalGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.CategoryTheory.Triangulated.LocallySmallCompactEnvelope
import StacksCore.Tactic.StacksAttribute

/-!
# Compact objects of `D_{QCoh,T}(𝒪_X)` are the perfect ones

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let
`T ⊆ |X|` be a closed subset such that `|X| ∖ T` is quasi-compact. Stacks 0AED says that an
object of `D_{QCoh,T}(𝒪_X)` is compact in `D_{QCoh,T}(𝒪_X)` if and only if it is perfect as an
object of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.Space.isCompactObject_iff_isPerfect_of_supported`: **Stacks 0AED**.

## The proof

This is the source's proof. `D_{QCoh,T}(𝒪_X)`
(`AlgebraicGeometry.Space.quasicoherentDerivedSupportedOn`) is a triangulated subcategory of
`D_QCoh(𝒪_X)` closed under direct sums
(`AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn`, the
remark preceding the lemma in the source). A perfect object is compact in `D_QCoh(𝒪_X)`
(Stacks 09M8), hence in the subcategory, whose direct sums are those of `D_QCoh(𝒪_X)`.
Conversely, the perfect generator `P` of Stacks 0AEC is a compact weak generator of
`D_{QCoh,T}(𝒪_X)`
(`AlgebraicGeometry.Space.isWeakTriangulatedGenerator_singleton_quasicoherentDerivedSupportedOn`),
so by Stacks 09SR every compact object lies in the triangulated envelope of `P`
(`CategoryTheory.Pretriangulated.triangEnvelope_eq_isCompactObject_of_locallySmall`). The objects
of `D_{QCoh,T}(𝒪_X)` that are perfect in `D(𝒪_X)` form a triangulated subcategory (perfect objects
are stable under shifts and two-out-of-three in distinguished triangles, Stacks 08G9) stable under
direct summands (`AlgebraicGeometry.Space.isPerfect_of_retract`), which contains `P` and hence
that envelope: this is the source's "each of these operations preserves the property of being
perfect".

## References

* [Stacks Project, Tag 0AED](https://stacks.math.columbia.edu/tag/0AED)
* [Stacks Project, Tag 0AEC](https://stacks.math.columbia.edu/tag/0AEC)
* [Stacks Project, Tag 09M8](https://stacks.math.columbia.edu/tag/09M8)
* [Stacks Project, Tag 09SR](https://stacks.math.columbia.edu/tag/09SR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated ZeroObject

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0AED.** Let `S` be a scheme, `X` a quasi-compact and quasi-separated algebraic space
over `S`, and `T ⊆ |X|` a closed subset such that `|X| ∖ T` is quasi-compact. An object of
`D_{QCoh,T}(𝒪_X)` is compact (in `D_{QCoh,T}(𝒪_X)`) if and only if it is perfect as an object of
`D(𝒪_X)`.

`D_{QCoh,T}(𝒪_X)` is the full subcategory of `D_QCoh(𝒪_X)` of the objects whose cohomology
sheaves are supported on `T` (`AlgebraicGeometry.Space.quasicoherentDerivedSupportedOn`, with
support as in Stacks 08GF); compactness is `CategoryTheory.IsCompactObject` (Stacks 07LS) in that
category, for direct sums indexed by the universe `u` of the site. -/
@[stacks 0AED]
theorem isCompactObject_iff_isPerfect_of_supported (X : AlgebraicSpaces B S hS)
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X.1)
    (T : Set (points B S hS X.1)) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (E : (quasicoherentDerivedSupportedOn X T).FullSubcategory) :
    IsCompactObject.{u} E ↔ (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E.obj.obj := by
  have := isGrothendieckAbelian_modules_ringUniverse B S hS X.1 X.2
  have := enoughInjectives_modules_ringUniverse B S hS X.1 X.2
  have := hasCoproducts_quasicoherentDerivedCategory_ringUniverse B S hS X.1 X.2
  have := fun J : Type u =>
    isClosedUnderColimitsOfShape_quasicoherentDerivedSupportedOn X T hT J
  have hcomp : ∀ F : (quasicoherentDerivedSupportedOn X T).FullSubcategory,
      (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect F.obj.obj → IsCompactObject.{u} F :=
    fun F hF => isCompactObject_of_fullyFaithful (ObjectProperty.ι _) F
      (isCompactObject_of_isPerfect X hXqc hXqs F.obj hF)
  refine ⟨fun hE => ?_, hcomp E⟩
  obtain ⟨P, hP, hPq, hPs, hdet⟩ :=
    exists_isPerfect_generator_of_supported B S hS X hXqc hXqs T hT hTc
  let P' : (quasicoherentDerivedSupportedOn X T).FullSubcategory := ⟨⟨P, hPq⟩, hPs⟩
  have hgen : (ObjectProperty.singleton P').IsWeakTriangulatedGenerator :=
    isWeakTriangulatedGenerator_singleton_quasicoherentDerivedSupportedOn X T P'
      fun E hEs h => (hdet E hEs).2 h
  have h := CategoryTheory.Pretriangulated.triangEnvelope_eq_isCompactObject_of_locallySmall P'
    (hcomp P' hP) hgen
  -- The objects of `D_{QCoh,T}(𝒪_X)` that are perfect in `D(𝒪_X)` form a triangulated
  -- subcategory stable under direct summands.
  let Φ : ObjectProperty (quasicoherentDerivedSupportedOn X T).FullSubcategory :=
    fun F => (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect F.obj.obj
  have : Φ.IsTriangulated :=
    { exists_zero := ⟨0, isZero_zero _, isPerfect_of_iso' B S hS
        ((isZero_zero _).iso ((quasicoherentDerivedSupportedOnι X T).map_isZero (isZero_zero _)))
        (RingedSite.isPerfect_obj₃_of_distinguished_general (smallEtaleRingedSite B S hS X.1 X.2)
          _ (contractible_distinguished P) hP hP)⟩
      isStableUnderShiftBy := fun n => ⟨fun F hF => isPerfect_of_iso' B S hS
        (((quasicoherentDerivedSupportedOnι X T).commShiftIso n).app F).symm
        (RingedSite.isPerfect_shift_general (smallEtaleRingedSite B S hS X.1 X.2) hF n)⟩
      ext₂' := fun Tri hTri h₁ h₃ => ObjectProperty.le_isoClosure _ _
        (RingedSite.isPerfect_obj₂_of_distinguished_general (smallEtaleRingedSite B S hS X.1 X.2)
          ((ObjectProperty.ι _).mapTriangle.obj
            ((ObjectProperty.ι (quasicoherentDerivedSupportedOn X T)).mapTriangle.obj Tri))
          ((ObjectProperty.ι _).map_distinguished _
            ((ObjectProperty.ι (quasicoherentDerivedSupportedOn X T)).map_distinguished Tri hTri))
          h₁ h₃) }
  have : Φ.IsStableUnderRetracts :=
    ⟨fun r hF => isPerfect_of_retract X ((quasicoherentDerivedSupportedOnι X T).map r.i)
      ((quasicoherentDerivedSupportedOnι X T).map r.r)
      (((quasicoherentDerivedSupportedOnι X T).map_comp r.i r.r).symm.trans
        ((congrArg (quasicoherentDerivedSupportedOnι X T).map r.retract).trans
          ((quasicoherentDerivedSupportedOnι X T).map_id _))) hF⟩
  have hle : (ObjectProperty.singleton P').triangEnvelope ≤ Φ := by
    rw [ObjectProperty.triangEnvelope_le_iff, ObjectProperty.singleton_le_iff]
    exact hP
  exact hle _ (h ▸ hE)

end AlgebraicGeometry.Space

end

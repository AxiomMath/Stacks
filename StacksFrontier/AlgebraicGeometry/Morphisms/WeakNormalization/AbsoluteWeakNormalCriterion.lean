module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.SeminormalLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AbsoluteWeakNormalAffine

/-!
# When the absolute weak normalization maps isomorphically to a universal homeomorphism

Let `X` be a scheme whose category of universal homeomorphisms has an initial object compatible
with restriction to open subschemes. For a universal homeomorphism `Y ⟶ X` the canonical
morphism from the absolute weak normalization of `X` to `Y` is an isomorphism exactly when `Y`
is absolutely weakly normal.

Both sides of the equivalence are local on `X`: being an isomorphism is Zariski-local at the
target, and absolute weak normality is a local property of rings. So it suffices to treat the
preimage of an affine open of `X`, where the restricted initial object is still initial and the
statement is the affine one.

## Main definitions

* `AlgebraicGeometry.UniversalHomeomorphismOver.restrict` restricts a universal homeomorphism
  over `X` to an open subscheme of `X`.
* `AlgebraicGeometry.UniversalHomeomorphismOver.restrictHom` restricts a morphism of universal
  homeomorphisms over `X`.
* `AlgebraicGeometry.UniversalHomeomorphismOver.restrictIsoPullback` compares that restriction
  with the fibre product along the open immersion.

## Main results

* `AlgebraicGeometry.isInitial_restrict_initial`: the restriction of the initial universal
  homeomorphism to an open subscheme is initial.
* `AlgebraicGeometry.isIso_resLE_iff`: being an isomorphism does not depend on the chosen
  description of the source open of a restriction.
* `AlgebraicGeometry.isIso_initialTo_iff_isAbsolutelyWeaklyNormal` is the characterization
  itself.

## Implementation notes

Restriction is taken along `AlgebraicGeometry.morphismRestrict` rather than as a fibre product,
so that the ring of sections of a restricted object is literally the sections of the original
object over the preimage open. The comparison with the fibre product, which is the shape in
which initiality of the restricted initial object is available, is `pullbackSymmetry` followed
by `AlgebraicGeometry.pullbackRestrictIsoRestrict`.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- An affine scheme is absolutely weakly normal exactly when its ring of global sections is. -/
private theorem isAbsolutelyWeaklyNormal_iff_sections {Z : Scheme.{u}} [IsAffine Z] :
    IsAbsolutelyWeaklyNormal Z ↔ IsAbsolutelyWeaklyNormalRing Γ(Z, ⊤) :=
  ⟨fun h => h.forall_affineOpens isAbsolutelyWeaklyNormalRing_propertyIsLocal
      ⟨⊤, isAffineOpen_top Z⟩,
    fun h => (isLocally_iff_exists_affineOpenCover _ Z).mpr
      ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top Z⟩,
        by simp [TopologicalSpace.IsOpenCover], fun _ => h⟩⟩

/-- The restriction of a universal homeomorphism over `X` to an open subscheme of `X`. -/
abbrev UniversalHomeomorphismOver.restrict (Z : UniversalHomeomorphismOver X) (U : X.Opens) :
    UniversalHomeomorphismOver U.toScheme :=
  ⟨Over.mk (Z.obj.hom ∣_ U), by
    have hZ := Z.property
    rw [universalHomeomorphism_iff] at hZ ⊢
    exact MorphismProperty.of_isPullback (isPullback_morphismRestrict Z.obj.hom U).flip hZ⟩

/-- The restriction of a morphism of universal homeomorphisms over `X` to an open subscheme. -/
def UniversalHomeomorphismOver.restrictHom {Z W : UniversalHomeomorphismOver X} (m : Z ⟶ W)
    (U : X.Opens) : Z.restrict U ⟶ W.restrict U :=
  ObjectProperty.homMk (Over.homMk
    (m.hom.left.resLE (W.obj.hom ⁻¹ᵁ U) (Z.obj.hom ⁻¹ᵁ U)
      (le_of_eq (by rw [← Scheme.Hom.comp_preimage, m.hom.w])))
    (by
      rw [← cancel_mono U.ι]
      simp only [Over.mk_left, Over.mk_hom, Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, m.hom.w]))

/-- The comparison of the restriction of a universal homeomorphism over `X` with its fibre
product along the inclusion of the open subscheme. -/
def UniversalHomeomorphismOver.restrictIsoPullback (Z : UniversalHomeomorphismOver X)
    (U : X.Opens) : UniversalHomeomorphismOver.pullback U.ι Z ≅ Z.restrict U :=
  ObjectProperty.isoMk _ (Over.isoMk
    (pullbackSymmetry U.ι Z.obj.hom ≪≫ pullbackRestrictIsoRestrict Z.obj.hom U) (by
      change (pullbackSymmetry U.ι Z.obj.hom ≪≫ pullbackRestrictIsoRestrict Z.obj.hom U).hom ≫
        (Z.obj.hom ∣_ U) = pullback.fst U.ι Z.obj.hom
      simp))

/-- The restriction of the initial universal homeomorphism to an open subscheme is initial. -/
def isInitial_restrict_initial [HasLocallyInitialUniversalHomeomorphismOver X] (U : X.Opens) :
    IsInitial ((initial (UniversalHomeomorphismOver X)).restrict U) :=
  IsInitial.ofIso (isInitial_pullback_initial U.ι)
    (UniversalHomeomorphismOver.restrictIsoPullback _ U)

/-- Restricting the canonical morphism out of the initial universal homeomorphism to an open
subscheme gives the canonical morphism out of the restricted initial object. -/
private theorem isInitial_restrict_initial_to
    [HasLocallyInitialUniversalHomeomorphismOver X] (U : X.Opens)
    (Y : UniversalHomeomorphismOver X) :
    ((isInitial_restrict_initial U).to (Y.restrict U)).hom.left =
      ((initial.to Y).hom.left).resLE (Y.obj.hom ⁻¹ᵁ U)
        ((initial (UniversalHomeomorphismOver X)).obj.hom ⁻¹ᵁ U)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, (initial.to Y).hom.w])) := by
  rw [(isInitial_restrict_initial U).hom_ext ((isInitial_restrict_initial U).to (Y.restrict U))
    (UniversalHomeomorphismOver.restrictHom (initial.to Y) U)]
  rfl

/-- Being an isomorphism does not depend on the chosen description of the source open. -/
theorem isIso_resLE_iff {A B : Scheme.{u}} (f : A ⟶ B) {U : B.Opens} {V : A.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (he : V = f ⁻¹ᵁ U) : IsIso (f.resLE U V e) ↔ IsIso (f ∣_ U) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  exact Scheme.Hom.resLE_congr (f := f) (e := e) rfl he (MorphismProperty.isomorphisms Scheme)

/-- **Stacks Project, Tag 0EUS.** The canonical morphism from the absolute weak normalization of
`X` to a universal homeomorphism `Y ⟶ X` is an isomorphism if and only if `Y` is absolutely
weakly normal. -/
@[stacks 0EUS "absolute_weak_normalization_iso_iff"]
theorem isIso_initialTo_iff_isAbsolutelyWeaklyNormal (X : Scheme.{u})
    [HasLocallyInitialUniversalHomeomorphismOver X] (Y : UniversalHomeomorphismOver X) :
    IsIso ((initial.to Y).hom.left) ↔ IsAbsolutelyWeaklyNormal Y.obj.left := by
  have hlocal : ∀ U : X.affineOpens,
      IsIso (((initial.to Y).hom.left) ∣_ (Y.obj.hom ⁻¹ᵁ U.1)) ↔
        IsAbsolutelyWeaklyNormal (Y.obj.hom ⁻¹ᵁ U.1).toScheme := by
    intro U
    have hUaff : IsAffine U.1.toScheme := U.2
    have hYaff : IsAffine (Y.obj.hom ⁻¹ᵁ U.1).toScheme :=
      isAffine_of_universalHomeomorphism (Y.obj.hom ∣_ U.1) (Y.restrict U.1).property
    set hA := isInitial_restrict_initial (X := X) U.1 with hAdef
    have hstep : IsIso (((initial.to Y).hom.left) ∣_ (Y.obj.hom ⁻¹ᵁ U.1)) ↔
        IsIso ((hA.to (Y.restrict U.1)).hom.left) := by
      rw [hAdef, isInitial_restrict_initial_to U.1 Y]
      exact (isIso_resLE_iff _ _ (by rw [← Scheme.Hom.comp_preimage, (initial.to Y).hom.w])).symm
    rw [hstep, isAbsolutelyWeaklyNormal_iff_sections]
    refine ⟨fun h => ?_, fun h => isIso_of_isInitial_universalHomeomorphismOver hA _ h⟩
    exact isAbsolutelyWeaklyNormalRing_propertyIsLocal.of_ringEquiv
      (Scheme.Γ.mapIso
        (asIso ((hA.to (Y.restrict U.1)).hom.left)).op).symm.commRingCatIsoToRingEquiv
      (isAbsolutelyWeaklyNormalRing_of_isInitial_universalHomeomorphismOver hA)
  have hsup : ⨆ U : X.affineOpens, Y.obj.hom ⁻¹ᵁ U.1 = ⊤ :=
    Scheme.Hom.iSup_preimage_eq_top _ (iSup_affineOpens_eq_top X)
  refine ⟨fun h => (isLocally_iff_exists_openCover isAbsolutelyWeaklyNormalRing_propertyIsLocal
      Y.obj.left).mpr ⟨X.affineOpens, fun U => Y.obj.hom ⁻¹ᵁ U.1,
        TopologicalSpace.IsOpenCover.mk hsup, fun U => (hlocal U).mp
          (IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme) h _)⟩,
    fun h => IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun U : X.affineOpens => Y.obj.hom ⁻¹ᵁ U.1) hsup fun U => (hlocal U).mpr
        (isLocally_open isAbsolutelyWeaklyNormalRing_propertyIsLocal Y.obj.left h _)⟩

end AlgebraicGeometry

end

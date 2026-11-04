module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AbsoluteWeakNormalCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalAffine
public import StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.Basic

/-!
# When the seminormalization maps isomorphically to a seminormalization candidate

Let `X` be a scheme whose category of seminormalization candidates — universal homeomorphisms
onto `X` inducing isomorphisms on all residue fields — has an initial object compatible with
restriction to open subschemes. For a candidate `Y ⟶ X` the canonical morphism from the
seminormalization of `X` to `Y` is an isomorphism exactly when `Y` is seminormal.

Both sides of the equivalence are local on `X`: being an isomorphism is Zariski-local at the
target, and seminormality is a local property of rings. So it suffices to treat the preimage of
an affine open of `X`, where the restricted initial object is still initial and the statement is
the affine one.

## Main definitions

* `AlgebraicGeometry.HasLocallyInitialSeminormalizationCategory` records that the initial
  seminormalization candidate over `X` exists and stays initial after restriction to an open
  subscheme, which is what the affine gluing construction of Stacks Tag 0EUS supplies.
* `AlgebraicGeometry.SeminormalizationCategory.restrictOpen` restricts a seminormalization
  candidate over `X` to an open subscheme of `X`.
* `AlgebraicGeometry.SeminormalizationCategory.restrictOpenHom` restricts a morphism of
  seminormalization candidates over `X`.
* `AlgebraicGeometry.SeminormalizationCategory.restrictOpenIsoPullback` compares that
  restriction with the fibre product along the open immersion.

## Main results

* `AlgebraicGeometry.isInitial_restrictOpen_initial`: the restriction of the initial
  seminormalization candidate to an open subscheme is initial.
* `AlgebraicGeometry.isInitial_restrictOpen_initial_to`: restricting the canonical morphism out
  of the initial candidate gives the canonical morphism out of the restricted initial object.
* `AlgebraicGeometry.isSeminormal_iff_sections`: an affine scheme is seminormal exactly when its
  ring of global sections is.

The characterization itself, `AlgebraicGeometry.isIso_initialTo_iff_isSeminormal`, is proved
without the locality hypothesis of this file in
`StacksFrontier.AlgebraicGeometry.SeminormalizationGluing.Basic`, which constructs the initial
seminormalization candidate of an arbitrary scheme, and is re-exported here.

## Implementation notes

Restriction is taken along `AlgebraicGeometry.morphismRestrict` rather than as a fibre product,
so that the ring of sections of a restricted candidate is literally the sections of the original
candidate over the preimage open. The comparison with the fibre product, which is the shape in
which initiality of the restricted initial object is available, is `pullbackSymmetry` followed
by `AlgebraicGeometry.pullbackRestrictIsoRestrict`. Everything here mirrors
`StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AbsoluteWeakNormalCriterion`, with
the residue field condition carried along: that a restriction of a candidate is again a
candidate uses `AlgebraicGeometry.morphismRestrict_ι` to compare its residue field maps with
those of the candidate itself, both inclusions of opens being open immersions.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- An affine scheme is seminormal exactly when its ring of global sections is. -/
theorem isSeminormal_iff_sections {Z : Scheme.{u}} [IsAffine Z] :
    IsSeminormal Z ↔ IsSeminormalRing Γ(Z, ⊤) :=
  ⟨fun h => h.forall_affineOpens isSeminormalRing_propertyIsLocal ⟨⊤, isAffineOpen_top Z⟩,
    fun h => (isLocally_iff_exists_affineOpenCover _ Z).mpr
      ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top Z⟩,
        by simp [TopologicalSpace.IsOpenCover], fun _ => h⟩⟩

/-- A morphism inducing isomorphisms on all residue fields still does so after restriction to an
open subscheme of the target. -/
private theorem isIso_residueFieldMap_morphismRestrict {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (hres : ∀ y : Y, IsIso (f.residueFieldMap y)) (U : Z.Opens)
    (y : (f ⁻¹ᵁ U).toScheme) : IsIso ((f ∣_ U).residueFieldMap y) := by
  have hι : ∀ w : U.toScheme, IsIso (U.ι.residueFieldMap w) := fun w => inferInstance
  have hpre : ∀ w : (f ⁻¹ᵁ U).toScheme, IsIso ((f ⁻¹ᵁ U).ι.residueFieldMap w) :=
    fun w => inferInstance
  have hcomp : IsIso (((f ⁻¹ᵁ U).ι ≫ f).residueFieldMap y) := by
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (hres _) (hpre y)
  rw [← morphismRestrict_ι, Scheme.residueFieldMap_comp] at hcomp
  have := hι ((f ∣_ U) y)
  exact (isIso_comp_left_iff (U.ι.residueFieldMap ((f ∣_ U) y))
    ((f ∣_ U).residueFieldMap y)).mp hcomp

variable {X : Scheme.{u}}

namespace SeminormalizationCategory

/-- The restriction of a seminormalization candidate over `X` to an open subscheme of `X`. -/
abbrev restrictOpen (Z : SeminormalizationCategory X) (U : X.Opens) :
    SeminormalizationCategory U.toScheme :=
  ⟨Over.mk (Z.obj.hom ∣_ U), by
    refine (isSeminormalizationCandidate_iff (Over.mk (Z.obj.hom ∣_ U))).mpr ⟨?_, fun y => ?_⟩
    · have hZ := IsSeminormalizationCandidate.universalHomeomorphism Z.property
      rw [universalHomeomorphism_iff] at hZ ⊢
      exact MorphismProperty.of_isPullback (isPullback_morphismRestrict Z.obj.hom U).flip hZ
    · exact isIso_residueFieldMap_morphismRestrict Z.obj.hom
        (IsSeminormalizationCandidate.isIso_residueFieldMap Z.property) U y⟩

/-- The restriction of a morphism of seminormalization candidates over `X` to an open
subscheme. -/
def restrictOpenHom {Z W : SeminormalizationCategory X} (m : Z ⟶ W) (U : X.Opens) :
    Z.restrictOpen U ⟶ W.restrictOpen U :=
  ObjectProperty.homMk (Over.homMk
    (m.hom.left.resLE (W.obj.hom ⁻¹ᵁ U) (Z.obj.hom ⁻¹ᵁ U)
      (le_of_eq (by rw [← Scheme.Hom.comp_preimage, m.hom.w])))
    (by
      rw [← cancel_mono U.ι]
      simp only [Over.mk_left, Over.mk_hom, Category.assoc, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, m.hom.w]))

/-- The comparison of the restriction of a seminormalization candidate over `X` with its fibre
product along the inclusion of the open subscheme. -/
def restrictOpenIsoPullback (Z : SeminormalizationCategory X) (U : X.Opens) :
    SeminormalizationCategory.restrict U.ι Z ≅ Z.restrictOpen U :=
  ObjectProperty.isoMk _ (Over.isoMk
    (pullbackSymmetry U.ι Z.obj.hom ≪≫ pullbackRestrictIsoRestrict Z.obj.hom U) (by
      change (pullbackSymmetry U.ι Z.obj.hom ≪≫ pullbackRestrictIsoRestrict Z.obj.hom U).hom ≫
        (Z.obj.hom ∣_ U) = pullback.fst U.ι Z.obj.hom
      simp))

end SeminormalizationCategory

/-- The initial seminormalization candidate exists and remains initial after restriction to any
open subscheme, as in the affine gluing construction of Stacks Tag 0EUS. -/
class HasLocallyInitialSeminormalizationCategory (X : Scheme.{u}) : Prop
    extends HasInitial (SeminormalizationCategory X) where
  /-- Restricting the chosen initial seminormalization candidate along an open immersion gives
  an initial seminormalization candidate over the open subscheme. -/
  nonempty_isInitial_restrict (U : Scheme.{u}) (f : U ⟶ X) [IsOpenImmersion f] :
    Nonempty (IsInitial (SeminormalizationCategory.restrict f
      (initial (SeminormalizationCategory X))))

/-- The base change of the chosen seminormalization along an open immersion is initial among
seminormalization candidates over the open subscheme. -/
def isInitial_pullback_initial_seminormalization {X U : Scheme.{u}}
    [HasLocallyInitialSeminormalizationCategory X] (f : U ⟶ X) [IsOpenImmersion f] :
    IsInitial (SeminormalizationCategory.restrict f (initial (SeminormalizationCategory X))) :=
  Classical.choice
    (HasLocallyInitialSeminormalizationCategory.nonempty_isInitial_restrict U f)

/-- The restriction of the initial seminormalization candidate to an open subscheme is
initial. -/
def isInitial_restrictOpen_initial [HasLocallyInitialSeminormalizationCategory X] (U : X.Opens) :
    IsInitial ((initial (SeminormalizationCategory X)).restrictOpen U) :=
  IsInitial.ofIso (isInitial_pullback_initial_seminormalization U.ι)
    (SeminormalizationCategory.restrictOpenIsoPullback _ U)

/-- Restricting the canonical morphism out of the initial seminormalization candidate to an open
subscheme gives the canonical morphism out of the restricted initial object. -/
theorem isInitial_restrictOpen_initial_to
    [HasLocallyInitialSeminormalizationCategory X] (U : X.Opens)
    (Y : SeminormalizationCategory X) :
    ((isInitial_restrictOpen_initial U).to (Y.restrictOpen U)).hom.left =
      ((initial.to Y).hom.left).resLE (Y.obj.hom ⁻¹ᵁ U)
        ((initial (SeminormalizationCategory X)).obj.hom ⁻¹ᵁ U)
        (le_of_eq (by rw [← Scheme.Hom.comp_preimage, (initial.to Y).hom.w])) := by
  rw [(isInitial_restrictOpen_initial U).hom_ext
    ((isInitial_restrictOpen_initial U).to (Y.restrictOpen U))
    (SeminormalizationCategory.restrictOpenHom (initial.to Y) U)]
  rfl

end AlgebraicGeometry

end

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Nagata
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine

/-!
# Normalization of a Japanese scheme

The normalization of an integral Japanese scheme is finite over it.

Being finite is Zariski-local on the target, so it is enough to check it over the affine opens
witnessing the Japanese condition. Over such an affine open `Spec A`, the normalization is the
spectrum of the integral closure of `A` in its fraction field, and the Japanese condition on
`A` says exactly that this integral closure is a finite `A`-module.

## Main results

* `AlgebraicGeometry.normalization_isFinite`: the normalization morphism of an integral
  Japanese scheme is finite.

## Implementation notes

An integral scheme is irreducible, so every quasi-compact open has at most one irreducible
component. This supplies the finiteness hypothesis required to form the normalization, so the
statement does not carry it; it is instead produced inside the statement by a `let`, which
also makes the normalization morphism it names unambiguous.

`finiteProp` packages finiteness as a `MorphismProperty Scheme`. Naming the property at that
type, rather than letting `IsFinite` be read as one at the point of use, is what lets the
affine-locality and Zariski-locality interfaces apply to it, and keeps the two transports
below — along an isomorphism of arrows, and along an open cover — ordinary instance
resolution.

## References

* [Stacks Project, Tag 035R](https://stacks.math.columbia.edu/tag/035R)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Finiteness of a morphism of schemes, packaged as a morphism property. -/
def finiteProp : MorphismProperty Scheme.{u} := @IsFinite

/-- A morphism is finite exactly when, over every affine open of its target, its source is
affine and its map of sections is a finite ring map. -/
local instance hasAffineProperty_finiteProp :
    HasAffineProperty finiteProp.{u} (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  intro X Y f
  simp [finiteProp, isFinite_iff]

/-- The Japanese condition on a domain says that the integral closure in its fraction field is
a finite module over it. -/
private theorem japanese_fractionField_integralClosure_finite
    (A : Type u) [CommRing A] [IsDomain A] (hA : IsJapaneseRing A) :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  hA.finite (FractionRing A)

/-- Over an affine open whose ring of sections is Japanese, the normalization morphism is
finite: it is the spectrum map of the inclusion of that ring into its integral closure. -/
private theorem normalization_restrict_isFinite_of_isJapanese
    (X : Scheme.{u}) [IsIntegral X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.affineOpens) [Nonempty U.val]
    (hU : IsJapaneseRing Γ(X, U.val)) :
    IsFinite (Scheme.normalization X hfinite ∣_ U.val) := by
  let A := Γ(X, U.val)
  let B := integralClosure A (FractionRing A)
  let e : Spec (.of A) ≅ U.val.toScheme := U.2.isoSpec.symm
  have : IsAffine U.val.toScheme := U.2
  let νU := preimageNormalizationIsoSpecIntegralClosure hfinite U.val e
  have hB : Module.Finite A B := japanese_fractionField_integralClosure_finite A hU
  have hSpec : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hB)
  have hcomm :=
    preimageNormalizationIsoSpecIntegralClosure_hom_comp
      (X := X) (hX := hfinite) (U := U.val) (e := e)
  let arrowIso :
      CategoryTheory.Arrow.mk (Scheme.normalization X hfinite ∣_ U.val) ≅
        CategoryTheory.Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    CategoryTheory.Arrow.isoMk νU e.symm (by simpa [νU, A, B] using hcomm)
  exact (MorphismProperty.arrow_mk_iso_iff finiteProp.{u} arrowIso).mpr hSpec

/-- **Stacks Project, Tag 035R.** The normalization morphism of an integral Japanese scheme is
finite. -/
@[stacks 035R]
theorem normalization_isFinite (X : Scheme.{u}) [IsIntegral X]
    (hX : IsJapaneseScheme X) :
    let hfinite : ∀ U : X.Opens,
        IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
      intro U _
      cases isEmpty_or_nonempty U with
      | inl hU =>
          rw [Set.finite_def]
          let : IsEmpty U := hU
          exact ⟨⟨∅, fun C ↦ isEmptyElim (C.2.1.nonempty.some)⟩⟩
      | inr hU =>
          let : Nonempty U := hU
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
    IsFinite (Scheme.normalization X hfinite) := by
  intro hfinite
  let U : X → X.affineOpens := fun x => (hX x).choose
  have hcontains (x : X) : x ∈ (U x : X.Opens) := (hX x).choose_spec.choose
  have hJapanese (x : X) :
      let : Nonempty (U x).val := ⟨⟨x, hcontains x⟩⟩
      IsJapaneseRing Γ(X, (U x).val) :=
    (hX x).choose_spec.choose_spec
  have hcover : (⨆ x : X, (U x : X.Opens)) = ⊤ :=
    top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hcontains x⟩
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := finiteProp.{u})
    (fun x : X => (U x : X.Opens)) hcover).mpr fun x => ?_
  have : Nonempty (U x).val := ⟨⟨x, hcontains x⟩⟩
  exact normalization_restrict_isFinite_of_isJapanese X hfinite (U x) (hJapanese x)

end AlgebraicGeometry

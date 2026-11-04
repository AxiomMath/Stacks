module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Noetherian.TensorProduct

/-!
# Locally Noetherian schemes after extending the base field

For a finitely generated extension of fields, a scheme over the smaller field is locally
Noetherian if and only if its base change to the larger field is locally Noetherian.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_baseChange_iff` characterizes when base change along a
  finitely generated field extension is locally Noetherian.

## Implementation notes

The base change is represented by the categorical pullback of the structure morphism along the
morphism of spectra induced by the field extension. A finitely generated field extension is
expressed by Mathlib's `Algebra.EssFiniteType` class.

## References

* [Stacks Project, Tag 038R](https://stacks.math.columbia.edu/tag/038R)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

/-- The global sections of a base change of an affine scheme along a field extension, as a
tensor product. -/
private noncomputable def pullback_sections_ringEquiv
    (k U k' : Type u) [Field k] [CommRing U] [Field k'] [Algebra k U] [Algebra k k'] :
    Γ(pullback (Spec.map (ofHom (algebraMap k U)))
      (Spec.map (ofHom (algebraMap k k'))), ⊤) ≃+* k' ⊗[k] U :=
  (Scheme.Γ.mapIso (pullbackSpecIso k U k').symm.op).commRingCatIsoToRingEquiv.trans
    ((Scheme.ΓSpecIso (CommRingCat.of (U ⊗[k] k'))).commRingCatIsoToRingEquiv.trans
      (Algebra.TensorProduct.comm k U k').toRingEquiv)

/-- For `Spec U` over `Spec k`, the ring `U` is Noetherian if and only if the global sections of
its base change along a finitely generated field extension are. -/
private theorem isNoetherianRing_iff_isNoetherianRing_sections_pullback
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k']
    (U : CommRingCat.{u}) (fi : Spec U ⟶ Spec (.of k)) :
    IsNoetherianRing U ↔
      IsNoetherianRing Γ(pullback fi (Spec.map (ofHom (algebraMap k k'))), ⊤) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective fi
  algebraize [φ.hom]
  have e := pullback_sections_ringEquiv k U k'
  refine ⟨fun _ => ?_, fun h => ?_⟩
  · have : IsNoetherianRing (k' ⊗[k] U) :=
      tensorProduct_isNoetherianRing_of_finitelyGenerated_fieldExtension
        k U k' (IntermediateField.fg_top k k')
    exact isNoetherianRing_of_ringEquiv (k' ⊗[k] U) e.symm
  · have : IsNoetherianRing (k' ⊗[k] U) := isNoetherianRing_of_ringEquiv _ e
    let : Algebra U (k' ⊗[k] U) :=
      (Algebra.TensorProduct.includeRight (R := k) (A := k') (B := U)).toRingHom.toAlgebra
    let eU : (U ⊗[k] k') ≃ₐ[U] (k' ⊗[k] U) :=
      AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm k U k').toRingEquiv)
        fun _ => rfl
    have : Module.FaithfullyFlat U (k' ⊗[k] U) :=
      Module.FaithfullyFlat.of_linearEquiv U _ eU.symm.toLinearEquiv
    exact descent_noetherian (algebraMap U (k' ⊗[k] U))
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) inferInstance

/-- Extending the base field by a finitely generated field extension preserves and reflects
the property that a scheme is locally Noetherian. -/
@[stacks 038R, ega "IV 4.7.3" "(i)", ega "IV 6.7.1" "k'/k finitely generated"]
public theorem isLocallyNoetherian_baseChange_iff
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [Algebra.EssFiniteType k k']
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    IsLocallyNoetherian X ↔
      IsLocallyNoetherian
        (pullback f (Spec.map (ofHom (algebraMap k k')))) := by
  have hA : ∀ i, IsAffine ((X.affineOpenCover.openCover.pullbackCoverOfLeft f
      (Spec.map (ofHom (algebraMap k k')))).X i) := fun i => by
    change IsAffine (pullback
      (X.affineOpenCover.openCover.f i ≫ f)
      (Spec.map (ofHom (algebraMap k k'))))
    have : IsAffine (X.affineOpenCover.openCover.X i) := Scheme.isAffine_affineCover X i
    have : IsAffineHom (X.affineOpenCover.openCover.f i ≫ f) := isAffineHom_of_isAffine _
    infer_instance
  constructor
  · intro h
    rw [isLocallyNoetherian_iff_of_affine_openCover
      (X.affineOpenCover.openCover.pullbackCoverOfLeft f
        (Spec.map (ofHom (algebraMap k k'))))]
    intro i
    change IsNoetherianRing Γ(pullback (X.affineOpenCover.openCover.f i ≫ f)
      (Spec.map (ofHom (algebraMap k k'))), ⊤)
    refine (isNoetherianRing_iff_isNoetherianRing_sections_pullback k k'
      (X.affineOpenCover.X i) (X.affineOpenCover.openCover.f i ≫ f)).mp ?_
    have : IsOpenImmersion (X.affineOpenCover.openCover.f i) := X.affineOpenCover.map_prop i
    have : IsAffine (X.affineOpenCover.openCover.X i) := Scheme.isAffine_affineCover X i
    refine @isNoetherianRing_of_ringEquiv
      (Γ(X, (X.affineOpenCover.openCover.f i).opensRange)) _ _ _ ?_ ?_
    · exact (IsOpenImmersion.ΓIsoTop
        (X.affineOpenCover.openCover.f i)).commRingCatIsoToRingEquiv.symm.trans
        (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv
    · exact h.component_noetherian ⟨_, isAffineOpen_opensRange _⟩
  · intro h
    rw [isLocallyNoetherian_iff_openCover
      (X.affineOpenCover.openCover.pullbackCoverOfLeft f
        (Spec.map (ofHom (algebraMap k k'))))] at h
    have : ∀ i, IsAffine (X.affineOpenCover.openCover.X i) := Scheme.isAffine_affineCover X
    rw [isLocallyNoetherian_iff_of_affine_openCover X.affineOpenCover.openCover]
    intro i
    have := hA i
    have := (isNoetherianRing_iff_isNoetherianRing_sections_pullback k k'
      (X.affineOpenCover.X i) (X.affineOpenCover.openCover.f i ≫ f)).mpr
      ((h i).component_noetherian ⟨⊤, isAffineOpen_top _⟩)
    exact isNoetherianRing_of_ringEquiv (X.affineOpenCover.X i)
      (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv

end AlgebraicGeometry

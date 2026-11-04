module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineLocal

/-!
# Quasi-affineness after a change of base field

A scheme over a field is quasi-affine as soon as it becomes quasi-affine after extending the
base field.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.isQuasiAffine_of_isQuasiAffine_baseChange`: quasi-affineness descends
  along an extension of the base field.

## Implementation notes

The base change is the pullback of the structure morphism along the morphism of spectra
induced by the field extension. That morphism is faithfully flat and quasi-compact, so it is
a one-element fpqc covering, and quasi-affineness of morphisms is local on the target for the
fpqc topology (Tag 02L7). Over the affine base `Spec K`, quasi-affineness of the projection is
exactly quasi-affineness of the base-changed scheme.

## References

* [Stacks Project, Tag 0BDD](https://stacks.math.columbia.edu/tag/0BDD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0BDD.** Quasi-affineness descends along an extension of the base
field: if the base change of `X` to `K` is quasi-affine, then so is `X`. -/
@[stacks 0BDD]
theorem isQuasiAffine_of_isQuasiAffine_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (h : Scheme.IsQuasiAffine
      (pullback f (Spec.map (ofHom (algebraMap k K))))) :
    Scheme.IsQuasiAffine X := by
  let s : Spec (.of K) ⟶ Spec (.of k) := Spec.map (ofHom (algebraMap k K))
  obtain ⟨_, _⟩ : Flat s ∧ Surjective s :=
    (flat_and_surjective_SpecMap_iff (ofHom (algebraMap k K))).2
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Scheme.IsQuasiAffine (⊤ : X.Opens).toScheme :=
    (MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := @IsQuasiAffineHom) (f := f)
      (Scheme.Hom.singleton_mem_fpqcPrecoverage s)
      (by rintro U g inst ⟨⟩
          exact (isQuasiAffineHom_iff_isQuasiAffine _).mpr h)).isQuasiAffine_preimage
      ⊤ (isAffineOpen_top _)
  have : CompactSpace X := (TopCat.homeoOfIso (asIso X.topIso.hom.base)).compactSpace
  exact Scheme.IsQuasiAffine.of_isImmersion X.topIso.inv

end AlgebraicGeometry

end

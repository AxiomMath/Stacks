module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.FaithfullyFlatDescent

/-!
# Geometric normality under extension of the base field

Geometric normality of a scheme over a field is unchanged by an arbitrary extension of that
field.

## Main results

* `AlgebraicGeometry.isNormal_of_iso`: normality of schemes transports along an isomorphism.
* `AlgebraicGeometry.isNormal_of_flat_surjective`: normality of schemes descends along a flat
  surjective morphism.
* `AlgebraicGeometry.isGeometricallyNormal_iff_baseChange`: geometric normality is invariant
  under extension of the ground field.

## Implementation notes

Base change is the categorical pullback of the structure morphism along the morphism of spectra
induced by the field extension, and the base-changed scheme is viewed over the larger field by
the second projection.

Geometric normality is used through the equivalence of items (1) and (2) of Tag 038O: a scheme
over `k` is geometrically normal exactly when every one of its base changes to a field extension
of `k` is a normal scheme. In that formulation the two directions of the statement are a
comparison of iterated base changes, which is `AlgebraicGeometry.iteratedBaseChangeIso`, plus —
for the harder direction — the observation that two extensions `K` and `L` of `k` admit a common
extension `M`, so that normality of the base change to `L` follows by descending normality of
the base change to `M` along the flat surjective projection.

Descent of normality is stalkwise: the map of local rings induced by a flat morphism is a
faithfully flat local homomorphism, and normality of rings descends along such maps by
Tag 033G.

## References

* [Stacks Project, Tag 038P](https://stacks.math.columbia.edu/tag/038P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- Normality of schemes descends along a flat surjective morphism. -/
public theorem isNormal_of_flat_surjective {X Y : Scheme.{u}} (r : X ⟶ Y)
    [Flat r] [Surjective r] [IsNormal X] : IsNormal Y := by
  refine (isNormal_iff_stalk_isNormalRing Y).2 fun y => ?_
  obtain ⟨x, rfl⟩ := r.surjective y
  let _ : Algebra (Y.presheaf.stalk (r x)) (X.presheaf.stalk x) := (r.stalkMap x).hom.toAlgebra
  have _ : Module.Flat (Y.presheaf.stalk (r x)) (X.presheaf.stalk x) := Flat.stalkMap r x
  have _ : IsLocalHom (algebraMap (Y.presheaf.stalk (r x)) (X.presheaf.stalk x)) :=
    r.toLRSHom.prop x
  have _ : Module.FaithfullyFlat (Y.presheaf.stalk (r x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isDomain_and_isIntegrallyClosed_atPrime_of_faithfullyFlat
    ((isNormal_iff_stalk_isNormalRing X).mp ‹_› x)

/-- For a tower `k ⊆ K ⊆ L` of fields, base changing to `K` and then to `L` gives a normal
scheme exactly when base changing to `L` in one step does. -/
private theorem isNormal_baseChange_tower_iff (k K L : Type u) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    IsNormal (pullback (pullback.snd f (Spec.map (ofHom (algebraMap k K))))
        (Spec.map (ofHom (algebraMap K L)))) ↔
      IsNormal (pullback f (Spec.map (ofHom (algebraMap k L)))) := by
  have e := iteratedBaseChangeIso f (Spec.map (ofHom (algebraMap k K)))
    (Spec.map (ofHom (algebraMap K L))) (Spec.map (ofHom (algebraMap k L)))
    (specMap_algebraMap_comp k K L)
  exact ⟨fun _ => isNormal_of_iso e.symm, fun _ => isNormal_of_iso e⟩

/-- The morphism of spectra induced by an extension of fields is flat and surjective. -/
private theorem flat_and_surjective_specMap_algebraMap (K L : Type u) [Field K] [Field L]
    [Algebra K L] :
    Flat (Spec.map (ofHom (algebraMap K L))) ∧
      Surjective (Spec.map (ofHom (algebraMap K L))) :=
  (flat_and_surjective_SpecMap_iff (ofHom (algebraMap K L))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)

/-- **Stacks Project, Tag 038P.** Geometric normality of a scheme over a field is invariant
under extension of the ground field. -/
@[stacks 038P "global equivalence", ega "IV 6.7.8" "(vi) global"]
public theorem isGeometricallyNormal_iff_baseChange (k K : Type u) [Field k] [Field K]
    [Algebra k K] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    IsGeometricallyNormal f ↔
      IsGeometricallyNormal (pullback.snd f (Spec.map (ofHom (algebraMap k K)))) := by
  have hf := (geometricallyNormal_tfae k X f).out 1 2
  have hfK := (geometricallyNormal_tfae K (pullback f (Spec.map (ofHom (algebraMap k K))))
    (pullback.snd f (Spec.map (ofHom (algebraMap k K))))).out 1 2
  rw [hf, hfK]
  refine ⟨fun h M _ _ => ?_, fun h L _ _ => ?_⟩
  · let _ : Algebra k M := ((algebraMap K M).comp (algebraMap k K)).toAlgebra
    have _ : IsScalarTower k K M :=
      IsScalarTower.of_algebraMap_eq' (RingHom.algebraMap_toAlgebra _)
    exact (isNormal_baseChange_tower_iff k K M f).mpr (h M)
  · obtain ⟨M, _, _, _, _, _, _⟩ := exists_common_extension k K L
    have _ : IsNormal (pullback f (Spec.map (ofHom (algebraMap k M)))) :=
      (isNormal_baseChange_tower_iff k K M f).mp (h M)
    have _ : IsNormal (pullback (pullback.snd f (Spec.map (ofHom (algebraMap k L))))
        (Spec.map (ofHom (algebraMap L M)))) :=
      (isNormal_baseChange_tower_iff k L M f).mpr inferInstance
    obtain ⟨_, _⟩ := flat_and_surjective_specMap_algebraMap L M
    exact isNormal_of_flat_surjective
      (pullback.fst (pullback.snd f (Spec.map (ofHom (algebraMap k L))))
        (Spec.map (ofHom (algebraMap L M))))

end AlgebraicGeometry

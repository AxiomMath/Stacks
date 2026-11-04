module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Nagata
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Smooth.RegularRing

/-!
# Regularity is local in the smooth topology

A scheme is regular if and only if the members of a jointly surjective family of smooth
morphisms onto it are regular. Since an étale morphism is smooth, the same holds for étale
coverings.

## Main results

* `AlgebraicGeometry.isRegular_isLocal_smooth` states that regularity is local in the smooth
  topology.
* `AlgebraicGeometry.isRegular_isLocal_etale` states that it is local in the étale topology.

## Implementation notes

Regularity of a scheme is locally satisfying the ring property `IsRegularRing`, so Zariski
locality is the general statement for a local property of rings. Ascent is regularity of a
smooth algebra over a regular ring and descent is regularity along a faithfully flat ring
map; both are applied to the global sections of the affine schemes involved.

Étale locality is read off the smooth statement through
`CategoryTheory.ObjectProperty.IsLocal.of_le`; locality for a coarser precoverage is the
stronger statement, so nothing beyond the inclusion of étale in smooth morphisms is needed.

## References

* [Stacks Project, Tag 036D](https://stacks.math.columbia.edu/tag/036D)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The ring of global sections of an affine regular scheme is a regular ring. -/
private theorem isRegularRing_of_isRegular {X : Scheme.{u}} [IsAffine X] (h : IsRegular X) :
    IsRegularRing Γ(X, ⊤) :=
  (isLocally_iff_forall_affineOpens CommRing.isRegularRing_propertyIsLocal X).mp h
    ⟨⊤, isAffineOpen_top X⟩

/-- An affine scheme whose ring of global sections is regular is regular. -/
private theorem isRegular_of_isRegularRing {X : Scheme.{u}} [IsAffine X]
    (h : IsRegularRing Γ(X, ⊤)) : IsRegular X := fun _ =>
  ⟨⟨⊤, isAffineOpen_top X⟩, trivial, h⟩

/-- **Stacks Project, Tag 036D.** Regularity of schemes is local for the smooth
precoverage. -/
@[stacks 036D]
instance isRegular_isLocal_smooth :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsRegular X)
      (Scheme.precoverage @Smooth) := by
  have : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsRegular X)
      Scheme.zariskiPrecoverage :=
    isLocally_isLocal_zariski CommRing.isRegularRing_propertyIsLocal
  refine isLocal_smoothPrecoverage_of_affine (fun X : Scheme.{u} => IsRegular X) ?_ ?_
  · intro X S hX hS f hsm hSreg
    let : IsAffine X := hX
    let : IsAffine S := hS
    have hmap : (f.appTop).hom.Smooth := by
      simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
        hsm.smooth_appLE (isAffineOpen_top S) (isAffineOpen_top X) le_rfl
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    let : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) := RingHom.smooth_algebraMap.mp hmap
    let : IsRegularRing Γ(S, ⊤) := isRegularRing_of_isRegular hSreg
    exact isRegular_of_isRegularRing (Algebra.isRegularRing_of_smooth Γ(S, ⊤) Γ(X, ⊤))
  · intro X S hX hS f hsm hsurj hXreg
    let : IsAffine X := hX
    let : IsAffine S := hS
    let : Smooth f := hsm
    have hff : (f.appTop).hom.FaithfullyFlat :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, hsurj⟩
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    let : Module.FaithfullyFlat Γ(S, ⊤) Γ(X, ⊤) := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      simpa [RingHom.algebraMap_toAlgebra] using hff
    let : IsRegularRing Γ(X, ⊤) := isRegularRing_of_isRegular hXreg
    exact isRegular_of_isRegularRing (IsRegularRing.of_faithfullyFlat Γ(X, ⊤))

/-- Every étale morphism of schemes is smooth. -/
private theorem etale_le_smooth : (@Etale.{u} : MorphismProperty Scheme.{u}) ≤ @Smooth :=
  fun _ _ f hf => by let : Etale f := hf; infer_instance

/-- Regularity of schemes is local for the étale precoverage: a scheme is regular if and only
if the members of an étale covering family are. Locality for a coarser precoverage is the
stronger statement, so this follows from the smooth case. -/
instance isRegular_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsRegular X) Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le (Scheme.precoverage_mono etale_le_smooth)

end AlgebraicGeometry

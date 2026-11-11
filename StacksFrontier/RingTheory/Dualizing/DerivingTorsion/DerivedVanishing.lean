module

public import StacksFrontier.RingTheory.Dualizing.DerivedTorsionCounit
public import StacksFrontier.RingTheory.Dualizing.DerivingTorsion.Vanishing

/-!
# Vanishing of `RΓ_I` on complexes where an element of `I` is inverted

Let `I` be a finitely generated ideal of a commutative ring `A`, and let `RΓ_I` be the total
right derived functor of the `I`-power-torsion functor `H^0_I`, valued in the derived category
of `I`-power-torsion modules. If some `f ∈ I` acts invertibly on an object `K` of `D(A)` (for
instance, `K` is a complex of `A_f`-modules), then `RΓ_I(K) = 0`.

## Main results

* `Dualizing.derivedPowerTorsion_isZero_of_isIso_smul` — Stacks 0A6M.

## Implementation notes

The hypothesis is invertibility of the scalar endomorphism `f • 𝟙 K` in `D(A)`. Being right
adjoint to the `A`-linear derived inclusion, `RΓ_I` sends `f • 𝟙 K` to `f • 𝟙 (RΓ_I K)`, so `f`
acts invertibly on every cohomology object of `RΓ_I K`; these are `I`-power torsion, hence zero,
exactly as in the proof in the source.

## References

* [Stacks Project, Tag 0A6M](https://stacks.math.columbia.edu/tag/0A6M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The property of an `A`-module of being `I`-power torsion, as a reducible name for the
predicate used in the construction of `Dualizing.derivedPowerTorsion`. -/
private abbrev torsionProperty (A : Type u) [CommRing A] (I : Ideal A) :
    ObjectProperty (ModuleCat.{max u v} A) :=
  fun M ↦ IsIPowerTorsion A M I

/-- A right adjoint of an `R`-linear functor between `R`-linear categories sends the scalar
endomorphism `r • 𝟙 K` to `r • 𝟙` of its value. -/
private lemma map_smul_id_of_adjunction {R : Type*} [CommRing R] {C D : Type*} [Category C]
    [Category D] [Preadditive C] [Preadditive D] [Linear R C] [Linear R D] {L : D ⥤ C}
    {G : C ⥤ D} [L.Linear R] (adj : L ⊣ G) (K : C) (r : R) :
    G.map (r • 𝟙 K) = r • 𝟙 (G.obj K) := by
  apply (adj.homEquiv _ K).symm.injective
  rw [adj.homEquiv_counit, adj.homEquiv_counit]
  have h := adj.counit.naturality (r • 𝟙 K)
  simp only [Functor.comp_map, Functor.id_map, Linear.comp_smul] at h
  rw [h]
  simp

/-- **Stacks 0A6M.** Let `I` be a finitely generated ideal of `A` and let `K ∈ D(A)` be such that
multiplication by some `f ∈ I` is an isomorphism of `K` (e.g. `K` is a complex of
`A_f`-modules). Then `RΓ_I(K) = 0`, where `RΓ_I` is the derived functor of `H^0_I` with values
in the derived category of `I`-power-torsion modules. -/
@[stacks 0A6M]
theorem derivedPowerTorsion_isZero_of_isIso_smul
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (f : A) (hf : f ∈ I) (hiso : IsIso (f • 𝟙 K)) :
    IsZero ((derivedPowerTorsion.{u, v} A I hI).obj K) := by
  letI : (torsionProperty.{u, v} A I).IsSerreClass := isSerreClass_isIPowerTorsion I hI
  letI : PreservesFiniteLimits (torsionProperty.{u, v} A I).ι :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass (torsionProperty.{u, v} A I)
  letI : PreservesFiniteColimits (torsionProperty.{u, v} A I).ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass (torsionProperty.{u, v} A I)
  let R := derivedPowerTorsion.{u, v} A I hI
  let X := R.obj K
  have hmap : R.map (f • 𝟙 K) = f • 𝟙 X :=
    map_smul_id_of_adjunction (derivedPowerTorsionAdjunction.{u, v} A I hI) K f
  have hX : IsIso (f • 𝟙 X) := by
    rw [← hmap]
    infer_instance
  let P := torsionProperty.{u, v} A I
  change IsZero X
  rw [Coreflection.isZero_iff_zero_isIso, DerivedCategory.isIso_iff]
  intro n
  let H := DerivedCategory.homologyFunctor P.FullSubcategory n
  letI : H.Linear A := DerivedCategory.homologyFunctor_linear (C := P.FullSubcategory) A n
  rw [H.map_zero, ← Coreflection.isZero_iff_zero_isIso]
  have hH : IsIso (f • 𝟙 (H.obj X)) := by
    simpa using H.map_isIso (f • 𝟙 X)
  have hM : IsIso (f • 𝟙 (P.ι.obj (H.obj X))) := by
    have e : P.ι.map (f • 𝟙 (H.obj X)) = f • 𝟙 (P.ι.obj (H.obj X)) := by
      rw [Functor.map_smul]
      rfl
    rw [← e]
    infer_instance
  have hsub :=
    isIPowerTorsion_subsingleton_of_isIso_smul A I hf (P.ι.obj (H.obj X)) (H.obj X).property hM
  exact IsZero.of_full_of_faithful_of_isZero P.ι _
    (ModuleCat.isZero_iff_subsingleton.mpr hsub)

end Dualizing

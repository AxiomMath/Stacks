module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.RingTheory.Dualizing.UbiquityStability
public import StacksFrontier.RingTheory.Dualizing.UbiquityCompleteLocal
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.Regular.AscentAlongRegularRingHom
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularLocusFinite
public import StacksFrontier.AlgebraicGeometry.SchemeJTwoLocal.JTwoTFAE
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.RationalSingularPointsResolution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local rings of schemes of finite type over an excellent local ring

The proofs of [Stacks, Tags 0BGM and 0BGN] use, without further mention, that every local ring
met along the way is essentially of finite type over a Noetherian complete local ring, hence
excellent, Nagata, with a dualizing complex, and with normal completion when it is normal. This
file records those facts for the local rings of a scheme locally of finite type over the
spectrum of an excellent ring.

## Main results

* `AlgebraicGeometry.essFiniteType_stalkStructureMap`: the structure map `C ⟶ 𝒪_{Y, y}` of a
  scheme over `Spec C` (the localization `C ⟶ 𝒪_{Spec C, f(y)}` followed by the stalk map of
  `f`) is essentially of finite type when `Y ⟶ Spec C` is locally of finite type.
* `AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType`: the local rings are excellent
  (that they have dualizing complexes when `C` has one is the library's
  `AlgebraicGeometry.exists_isDualizingComplex_stalk_of_locallyOfFiniteType`).
* `AlgebraicGeometry.isNormalRing_adicCompletion_of_isExcellent_of_isNormalRing`: an excellent
  normal Noetherian local ring has normal completion.
* `AlgebraicGeometry.finite_singularLocus_of_locallyOfFiniteType_of_isExcellent`: a normal
  Noetherian scheme of dimension at most two locally of finite type over an excellent ring has
  finitely many singular points.

## References

* [Stacks Project, Tag 07QU](https://stacks.math.columbia.edu/tag/07QU)
* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 0C23](https://stacks.math.columbia.edu/tag/0C23)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- A ring map essentially of finite type in Mathlib's sense is essentially of finite type in
the Stacks sense of [Stacks, Tag 00QM]: the target is a localization of the finitely generated
subalgebra recorded by `Algebra.EssFiniteType.subalgebra`. -/
theorem isEssentiallyOfFiniteType_of_essFiniteType {R S : Type u} [CommRing R] [CommRing S]
    {f : R →+* S} (hf : f.EssFiniteType) : IsEssentiallyOfFiniteType R S f := by
  let := f.toAlgebra
  have : Algebra.EssFiniteType R S := hf
  exact ⟨Algebra.EssFiniteType.subalgebra R S, inferInstance, inferInstance, inferInstance,
    Algebra.EssFiniteType.submonoid R S, inferInstance, inferInstance,
    Algebra.EssFiniteType.isLocalization R S⟩

/-- The structure map `C ⟶ 𝒪_{Y, y}` of a scheme `Y` locally of finite type over `Spec C` (the
localization `C ⟶ 𝒪_{Spec C, f(y)}` followed by the stalk map of `f`) is essentially of finite
type: a localization followed by a stalk map of a morphism locally of finite type. -/
theorem essFiniteType_stalkStructureMap {C : Type u} [CommRing C] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of C)) [LocallyOfFiniteType f] (y : Y) :
    ((f.stalkMap y).hom.comp ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom).EssFiniteType := by
  have := (f.base y).isPrime
  have h0 : (algebraMap C (Localization.AtPrime (f.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (f.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of C) (f.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of C) (f.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of C)).inv ≫
      (Spec (.of C)).presheaf.germ ⊤ (f.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of C) (x := f.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  exact h1.comp (LocallyOfFiniteType.stalkMap f y)

/-- Excellence along a ring map essentially of finite type ([Stacks, Tag 07QU]). -/
@[ega "IV 7.8.3" "more general"]
theorem isExcellent_of_essFiniteType {R S : Type u} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.EssFiniteType) (hR : IsExcellent R) : IsExcellent S := by
  let := f.toAlgebra
  have : Algebra.EssFiniteType R S := hf
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType.{u, u}).2 hR

/-- The local rings of a scheme locally of finite type over the spectrum of an excellent ring
are excellent. -/
@[ega "IV 7.8.3" "(ii), special case"]
theorem isExcellent_stalk_of_locallyOfFiniteType {C : Type u} [CommRing C] (hC : IsExcellent C)
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of C)) [LocallyOfFiniteType f] (y : Y) :
    IsExcellent (Y.presheaf.stalk y) :=
  isExcellent_of_essFiniteType (essFiniteType_stalkStructureMap f y) hC

/-- **The completion of an excellent normal Noetherian local ring is normal.** An excellent ring
is a G-ring, so the map to the completion is regular, and normality ascends along a regular
map. -/
@[ega "IV 7.8.3" "(v), special case"]
theorem isNormalRing_adicCompletion_of_isExcellent_of_isNormalRing (R : Type u) [CommRing R]
    [IsLocalRing R] (hExcellent : IsExcellent R) (hR : IsNormalRing R) :
    IsNormalRing (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing R := hExcellent.1.1
  have hreg : IsRegularRingHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    isRegularRingHom_algebraMap_adicCompletion hExcellent.1.2.1 (maximalIdeal R)
  rw [isRegularRingHom_iff_of_eq_algebraMap _ rfl] at hreg
  exact isNormalRing_of_flat_of_isGeometricallyRegular_fiber R
    (AdicCompletion (maximalIdeal R) R) hR fun q _ => (hreg.2 q).2

/-- **A normal Noetherian scheme of dimension at most two locally of finite type over an
excellent ring has finitely many singular points.** An excellent ring is J-2. -/
theorem finite_singularLocus_of_locallyOfFiniteType_of_isExcellent {C : Type u} [CommRing C]
    (hC : IsExcellent C) {X : Scheme.{u}} [IsNoetherian X] [IsNormal X]
    (f : X ⟶ Spec (.of C)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X ≤ 2) :
    (singularLocus X).Finite := by
  have : IsNoetherianRing C := hC.1.1
  have : IsLocallyNoetherian (Spec (.of C)) := isLocallyNoetherian_Spec.mpr inferInstance
  exact finite_singularLocus_of_isJ2 X hdim
    (Scheme.isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian
      ((Scheme.isJ2_Spec_iff C).mpr hC.1.2.2) f)

end AlgebraicGeometry

end

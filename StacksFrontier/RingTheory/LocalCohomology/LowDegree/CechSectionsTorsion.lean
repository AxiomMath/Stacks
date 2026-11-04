module

public import StacksFrontier.RingTheory.LocalCohomology.ArtinianLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison

/-!
# Torsion of the outer terms of the low-degree sequence

Let `I` be a finitely generated ideal of a commutative ring `A`, let `U = Spec A \ V(I)` and let
`M` be an `A`-module. The four-term exact sequence of Stacks 0BK0 identifies the kernel of the
restriction map `M ⟶ Γ(U, F)` with a quotient of `H⁰_I(M)` and its cokernel with `H¹_I(M)`;
local cohomology with support in `V(I)` is `I`-power torsion, so both are `I`-power torsion.

## Main results

* `Stacks.LocalCohomology.isIPowerTorsion_ker_restrictionToComplement` — the kernel of
  `M ⟶ Γ(U, F)` is `I`-power torsion.
* `Stacks.LocalCohomology.isIPowerTorsion_quotient_range_restrictionToComplement` — its cokernel
  is `I`-power torsion.
* `Stacks.LocalCohomology.isIPowerTorsion_lowDegreeComparison` — both, for the localization
  triangle data that `Stacks.LocalCohomology.localizationTriangleData` produces unconditionally.

## Implementation notes

No `@[stacks 0BK0]` attribute is placed here. Tag 0BK0 asserts the exactness of the four-term
sequence and identifies the outer terms as `H⁰_I(M)` and `H¹_I(M)`; that those two modules are
`I`-power torsion is a property of local cohomology with support in `V(I)`, recorded by
`Stacks.LocalCohomology.isIPowerTorsion_localCohomologyModule` and coming from Stacks 0A6Q.

## References

* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

section General

variable {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}

/-- **The kernel of `M ⟶ Γ(U, F)` is `I`-power torsion.** It is the image of `H⁰_I(M)`, and
local cohomology with support in `V(I)` is `I`-power torsion. -/
theorem isIPowerTorsion_ker_restrictionToComplement
    (D : LocalizationTriangleData.{u, v} A I hI) (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    IsIPowerTorsion A (LinearMap.ker (restrictionToComplement D M F e)) I := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := (exact_localCohomologyZeroToModule_restrictionToComplement D M F e x).1
    (LinearMap.mem_ker.1 hx)
  obtain ⟨n, hn, hkill⟩ := isIPowerTorsion_localCohomologyModule A I hI M 0 y
  refine ⟨n, hn, fun a ha => Subtype.ext ?_⟩
  have h : a • (localCohomologyZeroToModule A I hI M).hom y =
      (localCohomologyZeroToModule A I hI M).hom (a • y) := (map_smul _ a y).symm
  show a • (localCohomologyZeroToModule A I hI M).hom y = (0 : M)
  rw [h, hkill a ha, map_zero]

/-- **The cokernel of `M ⟶ Γ(U, F)` is `I`-power torsion.** The connecting map identifies it
with `H¹_I(M)`, and local cohomology with support in `V(I)` is `I`-power torsion. -/
theorem isIPowerTorsion_quotient_range_restrictionToComplement
    (D : LocalizationTriangleData.{u, v} A I hI) (M : ModuleCat.{v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    IsIPowerTorsion A
      (complementGlobalSections A I F ⧸
        LinearMap.range (restrictionToComplement D M F e)) I := by
  intro z
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨n, hn, hkill⟩ :=
    isIPowerTorsion_localCohomologyModule A I hI M 1 (localizationBoundary D M F e s)
  refine ⟨n, hn, fun a ha => ?_⟩
  have hs : localizationBoundary D M F e (a • s) = 0 := by
    rw [map_smul, hkill a ha]
  rw [← Submodule.Quotient.mk_smul]
  exact (Submodule.Quotient.mk_eq_zero _).2
    (LinearMap.mem_range.2
      ((exact_restrictionToComplement_localizationBoundary D M F e (a • s)).1 hs))

end General

section Existence

variable (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **The 0BK0 comparison modulo torsion.** For a finitely generated ideal `I` of a commutative
ring `A` and `U = Spec A \ V(I)`, the kernel and the cokernel of the restriction map
`M ⟶ Γ(U, F)` are both `I`-power torsion. -/
theorem isIPowerTorsion_lowDegreeComparison (M : ModuleCat.{max u v} A)
    (F : SheafOfModules.{max u v} (complementZeroLocus A I : Scheme).ringCatSheaf)
    (e : F ≅ complementTilde A I M) :
    IsIPowerTorsion A
        (LinearMap.ker
          (restrictionToComplement (localizationTriangleData.{v} A I hI) M F e)) I ∧
      IsIPowerTorsion A
        (complementGlobalSections A I F ⧸
          LinearMap.range
            (restrictionToComplement (localizationTriangleData.{v} A I hI) M F e)) I :=
  ⟨isIPowerTorsion_ker_restrictionToComplement _ M F e,
    isIPowerTorsion_quotient_range_restrictionToComplement _ M F e⟩

end Existence

end Stacks.LocalCohomology

end

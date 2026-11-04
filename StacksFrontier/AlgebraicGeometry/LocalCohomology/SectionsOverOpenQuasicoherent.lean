module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SectionsOverOpenCoherent
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk

/-!
# Sections away from `V(I)` as homomorphisms out of an ideal power, for a quasi-coherent module

Let `X` be a Noetherian scheme, `I` a quasi-coherent sheaf of ideals whose first power `I • 𝒪_X`
is of finite type, and `F` a quasi-coherent `𝒪_X`-module. Writing `U` for the open complement
`X ∖ V(I)`, the canonical map `colim_n Hom(I ^ n • 𝒪_X, F) ⟶ Γ(F, U)` of
`Stacks.LocalCohomology.canonicalMapToSections` is a bijection.

## Main results

* `Stacks.LocalCohomology.isCompact_idealComplement`: the complement of `V(I)` in a Noetherian
  scheme is quasi-compact.
* `Stacks.LocalCohomology.canonicalMapToSections_surjective_of_isQuasicoherent`: for `F`
  quasi-coherent, every section of `F` over `X ∖ V(I)` is the value of a morphism
  `I ^ n • 𝒪_X ⟶ F`.
* `Stacks.LocalCohomology.canonicalMapToSections_bijective_of_isQuasicoherent`: for `F`
  quasi-coherent, the canonical map `colim_n Hom(I ^ n • 𝒪_X, F) ⟶ Γ(F, X ∖ V(I))` is a
  bijection.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.LocalCohomology

open Stacks.Ample (unitModule)

variable {X : Scheme.{u}}

/-- On a Noetherian scheme, for a sheaf of ideals `I` whose first power is of finite type and a
quasi-coherent `𝒪_X`-module `F`, every section of `F` over `X ∖ V(I)` is the value on the unit
section of a morphism `I ^ n • 𝒪_X ⟶ F`. -/
theorem canonicalMapToSections_surjective_of_isQuasicoherent [IsNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] :
    Function.Surjective (canonicalMapToSections I F).1 := by
  rw [canonicalMapToSections_surjective_iff]
  intro s
  obtain ⟨G, hGqc, hGft, t, ht⟩ := AlgebraicGeometry.exists_finiteTypeQuasicoherentSubobject_section
    F (idealComplement I) (TopologicalSpace.NoetherianSpace.isCompact _) s
  have : (G : X.Modules).IsQuasicoherent := hGqc
  have : (G : X.Modules).IsFiniteType := hGft
  have : (G : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
      (G : X.Modules)
  obtain ⟨n, φ, hφ⟩ := (canonicalMapToSections_surjective_iff I (G : X.Modules)).1
    (canonicalMapToSections_surjective_of_isCoherent I (G : X.Modules)) t
  refine ⟨n, φ ≫ G.arrow, ?_⟩
  have hcomp : ((φ ≫ G.arrow).val.app (op (idealComplement I))).hom
      (complementUnitLift I n (idealComplement I) le_rfl) =
      (G.arrow.val.app (op (idealComplement I))).hom
        ((φ.val.app (op (idealComplement I))).hom
          (complementUnitLift I n (idealComplement I) le_rfl)) := rfl
  rw [hcomp, hφ]
  exact ht

/-- On a Noetherian scheme, for a sheaf of ideals `I` whose first power is of finite type and a
quasi-coherent `𝒪_X`-module `F`, the canonical map `colim_n Hom(I ^ n • 𝒪_X, F) → Γ(F, X ∖ V(I))`
is a bijection. -/
theorem canonicalMapToSections_bijective_of_isQuasicoherent [IsNoetherian X]
    (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] :
    Function.Bijective (canonicalMapToSections I F).1 :=
  ⟨canonicalMapToSections_injective I F,
    canonicalMapToSections_surjective_of_isQuasicoherent I F⟩

end Stacks.LocalCohomology

end

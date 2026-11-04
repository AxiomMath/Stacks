module

public import StacksFrontier.AlgebraicGeometry.Blowup.CentreNormalizeChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjBridge
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal

/-!
# A submodule of a Rees piece, read as a centre inside a power of the ideal

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on it. The degree-`d` piece of the Rees
algebra `⨁ Iⁿ` is `I ^ d`, presented as the kernel of `𝒪_X ⟶ ι_* 𝒪_{V(I ^ d)}`. A quasi-coherent
submodule `ℱ` of that piece — the object [Stacks, Tag 0803] produces — is therefore a
quasi-coherent subsheaf of `𝒪_X` contained in `I ^ d`, that is, a centre on `X`.

This file writes that reading down: the inclusion of the piece into the structure sheaf, the
centre `J` attached to `ℱ` as the image ideal sheaf of the composite `ℱ ⟶ 𝒜_d ⟶ 𝒪_X`, and the
two properties of `J` that the proof of [Stacks, Tag 080B] uses: it is contained in `I ^ d`, and
it is of finite type as soon as `ℱ` is.

## Main definitions

* `Stacks.Blowup.reesPieceι`: the inclusion of the degree-`n` piece of the Rees algebra into the
  structure sheaf.
* `Stacks.Blowup.reesSubmoduleHom`: the composite `ℱ ⟶ 𝒜_d ⟶ 𝒪_X` of that inclusion with the
  inclusion of a submodule of the piece.
* `Stacks.Blowup.reesCentre`: the centre on `X` attached to `ℱ`, as the image ideal sheaf.

## Main results

* `Stacks.Blowup.structureAppₗ_reesPieceι`: a local section of the piece has the same image in
  `Γ(X, U)` under the inclusion as the one `Stacks.Blowup.reesPieceAmbient` gives it.
* `Stacks.Blowup.reesCentre_le_pow`: **the centre lies inside `I ^ d`.**
* `Stacks.Blowup.isFiniteType_reesCentre`: **the centre is of finite type** when `ℱ` is.
* `Stacks.Blowup.mem_ideal_reesCentre_iff`: a section of `Γ(X, U)` lies in the centre exactly
  when it is the image of a local section of `ℱ`.

## Implementation notes

The degree-`n` piece is `Stacks.Blowup.reesPiece`, which in nonnegative degrees is
`Stacks.Blowup.idealPowerKernel` — the categorical kernel of
`Stacks.ClosedSubscheme.structureSheafProjection (I ^ n)`, the two being the same term. The
inclusion is therefore `kernel.ι` of that projection, and the image of a local section under it
is `Stacks.Blowup.idealPowerKernelAmbient` by definition; the containment in `I ^ d` is then
`Stacks.Blowup.reesPieceAmbient_mem_affine`, the affine-local description of the piece.

The image ideal sheaf is `AlgebraicGeometry.idealSheafDataOfHom`, whose ideal over an affine open
is the range of the map on sections, so `Stacks.Blowup.mem_ideal_reesCentre_iff` holds by
definition and the two properties are read off the sections.

## References

* [Stacks Project, Tag 0803](https://stacks.math.columbia.edu/tag/0803)
* [Stacks Project, Tag 080B](https://stacks.math.columbia.edu/tag/080B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.IdealPowerColimit
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.Blowup

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The inclusion of a Rees piece into the structure sheaf.** The degree-`n` piece of the Rees
algebra of `I` is the kernel of `𝒪_X ⟶ ι_* 𝒪_{V(Iⁿ)}`, so it comes with a monomorphism into
`𝒪_X`: this one. -/
public def reesPieceι (n : ℕ) :
    ((reesSheafGradedAlgebra I).piece (n : ℤ) : X.Modules) ⟶ structureModule X :=
  kernel.ι (C := X.Modules) (Stacks.ClosedSubscheme.structureSheafProjection (I ^ n))

/-- The image in `Γ(X, U)` of a local section of the degree-`n` piece under the inclusion into
the structure sheaf is the one `Stacks.Blowup.reesPieceAmbient` gives it. -/
public theorem structureAppₗ_reesPieceι (n : ℕ) (U : X.Opens)
    (x : Γ((reesSheafGradedAlgebra I).piece (n : ℤ), U)) :
    structureAppₗ (reesPieceι I n) U x = reesPieceAmbient I (n : ℤ) U x := rfl

variable {d : ℕ} (ℱ : ((reesSheafGradedAlgebra I).piece (d : ℤ)).Submodule)

/-- The inclusion of a submodule of the degree-`d` Rees piece, at the `AlgebraicGeometry.Scheme`
spelling of the category of modules. The two spellings are the same category, but field notation
and `rw` do not cross between them. -/
public def reesSubmoduleι :
    (ℱ.toSheafOfModules : X.Modules) ⟶ ((reesSheafGradedAlgebra I).piece (d : ℤ) : X.Modules) :=
  ℱ.ι

/-- The composite `ℱ ⟶ 𝒜_d ⟶ 𝒪_X` of the inclusion of a submodule of the degree-`d` Rees piece
with the inclusion of that piece into the structure sheaf. -/
public def reesSubmoduleHom : (ℱ.toSheafOfModules : X.Modules) ⟶ structureModule X :=
  reesSubmoduleι I ℱ ≫ reesPieceι I d

/-- **The centre on `X` attached to a submodule of the degree-`d` Rees piece**: the image ideal
sheaf of `ℱ ⟶ 𝒜_d ⟶ 𝒪_X`. This is the ideal sheaf `𝒥` of the proof of [Stacks, Tag 080B]. -/
public def reesCentre [(ℱ.toSheafOfModules : X.Modules).IsQuasicoherent] : X.IdealSheafData :=
  idealSheafDataOfHom (ℱ.toSheafOfModules : X.Modules) (reesSubmoduleHom I ℱ)

/-- A section of `Γ(X, U)` lies in the centre attached to `ℱ` exactly when it is the image of a
local section of `ℱ`. -/
public theorem mem_ideal_reesCentre_iff [(ℱ.toSheafOfModules : X.Modules).IsQuasicoherent]
    (U : X.affineOpens) (y : Γ(X, U.1)) :
    y ∈ (reesCentre I ℱ).ideal U ↔
      ∃ x : Γ(ℱ.toSheafOfModules, U.1), structureAppₗ (reesSubmoduleHom I ℱ) U.1 x = y :=
  Iff.rfl

/-- **The centre attached to `ℱ` lies inside `I ^ d`.** A local section of `ℱ` is a local section
of the degree-`d` Rees piece, whose image in `Γ(X, U)` lies in `I(U) ^ d` over an affine open. -/
public theorem reesCentre_le_pow [(ℱ.toSheafOfModules : X.Modules).IsQuasicoherent] :
    reesCentre I ℱ ≤ I ^ d := by
  intro U y hy
  obtain ⟨x, rfl⟩ := (mem_ideal_reesCentre_iff I ℱ U y).1 hy
  rw [Scheme.IdealSheafData.ideal_pow]
  have hx : structureAppₗ (reesSubmoduleHom I ℱ) U.1 x =
      reesPieceAmbient I (d : ℤ) U.1
        (Scheme.Modules.Hom.app (reesSubmoduleι I ℱ) U.1 x) := rfl
  rw [hx]
  exact reesPieceAmbient_mem_affine I (d : ℤ) (Int.natCast_nonneg d) U _

/-- **The centre attached to `ℱ` is of finite type** when `ℱ` is of finite type: the image of a
morphism out of a module of finite type is generated by the images of the generators. -/
public theorem isFiniteType_reesCentre [(ℱ.toSheafOfModules : X.Modules).IsQuasicoherent]
    [(ℱ.toSheafOfModules : X.Modules).IsFiniteType] : (reesCentre I ℱ).IsFiniteType :=
  isFiniteType_idealSheafDataOfHom _ (reesSubmoduleHom I ℱ)

/-- **The factorization of the centre attached to `ℱ`, read on the charts of the blowup.** The
inverse image of `Stacks.Blowup.reesCentre` on the blowup of `X` in `I` is `E ^ d` times a given
second centre `Z'` exactly when, on every standard affine chart `Γ(X, U)[I/a]`, that second
centre is generated by the fractions `x / aᵈ` for `x` a local section of `ℱ` over `U`.

This is `Stacks.BlowUpChartCover.comap_idealSheafDataOfHom_eq_exceptionalIdeal_pow_mul_iff` at
the centre of `Stacks.Blowup.reesCentre`, whose containment in `I ^ d` is
`Stacks.Blowup.reesCentre_le_pow` rather than an assumption. -/
public theorem comap_reesCentre_eq_exceptionalIdeal_pow_mul_iff
    [(ℱ.toSheafOfModules : X.Modules).IsQuasicoherent]
    (Z' : (AlgebraicGeometry.blowUp I).IdealSheafData) :
    (reesCentre I ℱ).comap (AlgebraicGeometry.blowUpToBase I) =
        AlgebraicGeometry.exceptionalIdeal I ^ d * Z' ↔
      ∀ (U : X.affineOpens) (a : I.ideal U),
        Ideal.map (Stacks.BlowUpChartCover.chartΓIso I U a).hom.hom
            (Z'.ideal (Stacks.BlowUpChartCover.chartOpen I U a)) =
          Ideal.span (Set.range fun x : Γ(ℱ.toSheafOfModules, U.1) ↦
            affineBlowupAlgebra.fraction (S := Localization.Away (a : Γ(X, U.1)))
              (I.ideal U) (a : Γ(X, U.1)) d
              ⟨structureAppₗ (reesSubmoduleHom I ℱ) U.1 x,
                Stacks.BlowUpChartCover.ideal_le_ideal_pow I (reesCentre_le_pow I ℱ) U
                  (Stacks.BlowUpChartCover.structureAppₗ_mem_idealSheafDataOfHom
                    (reesSubmoduleHom I ℱ) U x)⟩) :=
  Stacks.BlowUpChartCover.comap_idealSheafDataOfHom_eq_exceptionalIdeal_pow_mul_iff I
    (reesSubmoduleHom I ℱ) d (reesCentre_le_pow I ℱ) Z'

end Stacks.Blowup

end

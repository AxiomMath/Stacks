module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality
public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.IdealSheafSections.Basic

/-!
# Closed immersions of finite presentation

A closed immersion of schemes is of finite presentation exactly when its ideal sheaf — the
kernel of `𝒪_X ⟶ i_* 𝒪_Z`, read as a sheaf of `𝒪_X`-modules — is of finite type. So closed
immersions of finite presentation correspond to quasi-coherent sheaves of ideals of finite type.

## Main results

* `AlgebraicGeometry.finitePresentation_iff_isFiniteType_idealSheaf`: the characterization of
  finite presentation of a closed immersion by finite type of its ideal sheaf.

## Implementation notes

Both sides are tested on affine opens of the target, and they meet at the ideal of sections
killed by the comorphism.

On the finite-presentation side a closed immersion is an affine morphism, quasi-compact and
quasi-separated, so finite presentation reduces to local finite presentation, which for an
affine morphism is finite presentation of the map on sections over every affine open
(`Stacks.Flatness.locallyOfFinitePresentation_iff_app`); that map is surjective, so it is of
finite presentation exactly when its kernel is finitely generated.

On the finite-type side the ideal sheaf is quasi-coherent
(`Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf`), and for a
quasi-coherent module finite type is finiteness of the module of sections over every affine
open: `isFiniteType_iff_forall_moduleFinite_sections`, which is
`Stacks.AlgebraicGeometry.CoherentFinite.finite_sections` in one direction and condition (4) of
[Stacks, Tag 01XZ] in the other.

The two sides are joined by the inclusion of the ideal sheaf into the structure sheaf read on
sections, which is injective (`Stacks.Conormal.Locality.idealSheaf_section_injective`) with image
the sections killed by the comorphism
(`Stacks.ClosedImmersion.exists_idealSheaf_section`): so the module of sections of the ideal
sheaf over an open is the kernel ideal there, and finiteness of the one is finite generation of
the other.

The ideal sheaf is built over `structureSheafRing` of the underlying ringed
space rather than over `AlgebraicGeometry.Scheme.ringCatSheaf`. The two agree, but not to the
transparency instance search uses, so the proof names the ideal sheaf once as a term of
`AlgebraicGeometry.Scheme.Modules` and works with that name throughout.

## References

* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.CoherentFinite Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace AlgebraicGeometry

/-- A quasi-coherent `𝒪_X`-module is of finite type exactly when its module of sections over
every affine open is finite. -/
private lemma isFiniteType_iff_forall_moduleFinite_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] :
    SheafOfModules.IsFiniteType.{u, u, u} F ↔
      ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(F, U.1) := by
  refine ⟨fun _ U => finite_sections F U.2, fun h => ?_⟩
  refine (isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F
    (exists_affineOpenCover_isFiniteTildeOn F fun U hU => ?_)).2
  have := h ⟨U, hU⟩
  exact isFiniteTildeOn_of_finite_specModule F U hU
    (Module.Finite.equiv (specSectionsEquiv F hU).symm)

/-- A closed immersion is of finite presentation if and only if its ideal sheaf is of finite type
as a module over the structure sheaf of the target.

This is the module-theoretic encoding of **Stacks 01TV**. The tag is registered on
`AlgebraicGeometry.finitePresentation_iff_fg_ker`, which states the same equivalence with the
kernel ideal finitely generated on each affine open; the two are one node in two encodings, so
only one of them carries the tag. -/
@[ega "IV 1.4.5" "closed immersion case"]
public theorem finitePresentation_iff_isFiniteType_idealSheaf {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    FinitePresentation i ↔
      (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsFiniteType := by
  let α := SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toLRSHom.toShHom)
  let F : X.Modules := kernel α
  have hqc : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.ClosedImmersionTFAE.isQuasicoherent_idealSheaf i
  have hcond : ∀ (U : X.Opens) (t : Γ(F, U)),
      (i.app U).hom (((kernel.ι α).val.app (Opposite.op U)).hom t) = 0 := by
    intro U t
    have h0 : (kernel.ι α ≫ α).val.app (Opposite.op U) = 0 := by
      rw [kernel.condition]
      rfl
    exact congrArg (fun φ : _ ⟶ _ => ModuleCat.Hom.hom φ t) h0
  have key : ∀ U : X.affineOpens,
      Module.Finite Γ(X, U.1) Γ(F, U.1) ↔ (RingHom.ker (i.app U.1).hom).FG := by
    intro U
    let κ : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) :=
      { toFun := fun t => ((kernel.ι α).val.app (Opposite.op (U.1 : X.Opens))).hom t
        map_add' := fun a b => map_add _ a b
        map_smul' := fun r t =>
          ((kernel.ι α).val.app (Opposite.op (U.1 : X.Opens))).hom.map_smul r t }
    have hinj : Function.Injective κ :=
      Stacks.Conormal.Locality.idealSheaf_section_injective i U.1
    have hrange : LinearMap.range κ = RingHom.ker (i.app U.1).hom := by
      refine le_antisymm ?_ fun s hs => ?_
      · rintro s ⟨t, rfl⟩
        exact hcond U.1 t
      · exact Stacks.ClosedImmersion.exists_idealSheaf_section i U.1 s hs
    rw [← hrange]
    exact ⟨fun _ => Module.Finite.iff_fg.mp (.equiv (LinearEquiv.ofInjective κ hinj)),
      fun h => have := Module.Finite.iff_fg.mpr h; .equiv (LinearEquiv.ofInjective κ hinj).symm⟩
  refine Iff.trans ?_ (Iff.rfl : SheafOfModules.IsFiniteType.{u, u, u} F ↔
    (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).IsFiniteType)
  rw [isFiniteType_iff_forall_moduleFinite_sections F,
    show FinitePresentation i ↔ LocallyOfFinitePresentation i from
      ⟨fun h => h.1, fun h => ⟨h, inferInstance, inferInstance⟩⟩,
    Stacks.Flatness.locallyOfFinitePresentation_iff_app]
  exact ⟨fun h U => (key U).mpr
      (Stacks.Flatness.fg_ker_of_finitePresentation (h U.1 U.2) (i.app_surjective U.1 U.2)),
    fun h U hU => RingHom.FinitePresentation.of_surjective _ (i.app_surjective U hU)
      ((key ⟨U, hU⟩).mp (h ⟨U, hU⟩))⟩

end AlgebraicGeometry

end

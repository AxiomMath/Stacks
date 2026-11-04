module

public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.AffineSections
public import StacksFrontier.AlgebraicGeometry.RelativeSpecQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.RelativeSpec

/-!
# Finite type transports across [Stacks, Tag 01SB]

Let `A` be a quasi-coherent sheaf of commutative `𝒪_X`-algebras on a scheme `X`, with relative
spectrum `π : X' = Spec_X A ⟶ X`, and let `G` be a quasi-coherent `𝒪_{X'}`-module.  This file
proves that `G` is **of finite type** as soon as its direct image `π_* G` is of finite type as an
`A`-module.

This is the transport the proof of [Stacks, Tag 0897] needs: there `ℱ'` is produced from
`ℱ = ⨁ₙ ℱₙ` by the equivalence `Stacks.AffineAlgebraEquivalence.relativeSpecQcohEquivalence`,
and what has to be known about `ℱ'` is coherence, i.e. quasi-coherence (which the equivalence
gives) together with finite type.

Nothing in the library transported `SheafOfModules.IsFiniteType` in this direction:
`Stacks.SheafOfModules.Site.isFiniteType_pushforward` needs the site functor to be an
equivalence, and the scheme-level results
(`AlgebraicGeometry.isFiniteType_iff_pushforward_isFiniteType`,
`AlgebraicGeometry.Scheme.Modules.isFiniteType_pushforward_iff`) need `π` *finite* rather than
merely affine — and for merely affine `π` the statement over `𝒪_X` is false
(`Stacks.NodalCurve.not_isFiniteType_pushforward_unit`), so it has to stay over `A`.

## Main results

* `Stacks.AffineAlgebraEquivalence.module_finite_sections_preimage`: finiteness of the sections
  transports: if `Γ(π_* G, U)` is a finite `A(U)`-module then `Γ(G, π⁻¹U)` is a finite
  `Γ(X', π⁻¹U)`-module.
* `Stacks.AffineAlgebraEquivalence.isFiniteType_of_isFiniteType_pushforward`: **`G` is of finite
  type when `π_* G` is.**
* `Stacks.AffineAlgebraEquivalence.isFiniteType_inverse_obj`: the same read on the inverse of the
  equivalence, which is the form [Stacks, Tag 0897] uses.

## Implementation notes

`G` is taken as an object of `X'.Modules` rather than of the quasi-coherent full subcategory,
because `AlgebraicGeometry.Scheme.Modules` is a semireducible definition: with `G` spelled
`F'.obj` for `F'` in the full subcategory, instance search cannot see `Γ(G, V)` as the sections
of a module on a scheme and the `Module Γ(X', V) Γ(G, V)` instance is not found.  `qcohObj`
packages `G` back up for the equivalence.

The three identifications the argument needs all hold by `rfl`, so no transport intervenes:
`Γ(π_* G, U) = Γ(G, π⁻¹U)` (`sections_preimage_eq`); the `A(U)`-action on those sections is the
`Γ(X', π⁻¹U)`-action composed with the ring map of [Stacks, Tag 01LX](3) at `U`, which is what
makes `algebraSectionsPreimage` a scalar tower by `rfl`; and the sections of `A` over `U` are the
sections of `AlgebraSheaf.ringSheaf A` over `U`.  With that, `Module.Finite` descends along the
restriction of scalars by `Module.Finite.of_restrictScalars_finite`, and the affine opens whose
preimages carry finite sections cover `X'` because `π⁻¹U` is affine for affine `U`
(`isAffineOpen_preimage_relativeSpecToBase`), so
`Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections_affineOpens`
concludes.

The `A`-side input — finiteness of `Γ(π_* G, U)` over `A(U)` on an affine open cover — is
`Stacks.AlgebraicGeometry.QcohOverAlgebra.exists_affineCover_module_finite`, the `A`-analogue of
[Stacks, Tag 01PB].

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AffineAlgebraEquivalence

noncomputable section

variable {X : Scheme.{u}} (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A]

/-- The `A(U)`-algebra structure on the sections of the relative spectrum over `π⁻¹U`, along
the identification `π_* 𝒪 ≅ A` of [Stacks, Tag 01LX](3). -/
@[instance_reducible]
def algebraSectionsPreimage (U : X.Opens) :
    Algebra ↥(AlgebraSheaf.sections A U) Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U) :=
  ((pushforwardRingIso A).inv.hom.app (op U)).hom.toAlgebra

variable (G : (relativeSpec A).Modules) [G.IsQuasicoherent]

/-- `G` as a quasi-coherent module on the relative spectrum, in the form the equivalence of
[Stacks, Tag 01SB] consumes. -/
def qcohObj : (SheafOfModules.isQuasicoherent (relativeSpec A).ringCatSheaf).FullSubcategory :=
  ⟨G, ‹G.IsQuasicoherent›⟩

/-- **The direct image of `G` has the same sections**: `Γ(π_* G, U) = Γ(G, π⁻¹U)`. -/
theorem sections_preimage_eq (U : X.Opens) :
    Γ(Stacks.AlgebraicGeometry.QcohOverAlgebra.baseModule A
        ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj, U)
      = Γ(G, relativeSpecToBase A ⁻¹ᵁ U) := rfl

/-- **Finiteness of the sections transports across [Stacks, Tag 01SB].**  The `A(U)`-action on
`Γ(G, π⁻¹U)` is the `Γ(X', π⁻¹U)`-action along the ring isomorphism of [Stacks, Tag 01LX](3),
so the two finiteness statements differ only by a restriction of scalars along an
isomorphism. -/
theorem module_finite_sections_preimage (U : X.Opens)
    (h : letI := Stacks.AlgebraicGeometry.QcohOverAlgebra.moduleSections A
          ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj U
        Module.Finite ↥(AlgebraSheaf.sections A U)
          Γ(Stacks.AlgebraicGeometry.QcohOverAlgebra.baseModule A
            ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj, U)) :
    Module.Finite Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U)
      Γ(G, relativeSpecToBase A ⁻¹ᵁ U) := by
  let := algebraSectionsPreimage A U
  let : Module ↥(AlgebraSheaf.sections A U) Γ(G, relativeSpecToBase A ⁻¹ᵁ U) :=
    Stacks.AlgebraicGeometry.QcohOverAlgebra.moduleSections A
      ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj U
  have : Module.Finite ↥(AlgebraSheaf.sections A U)
      Γ(G, relativeSpecToBase A ⁻¹ᵁ U) := h
  have : IsScalarTower ↥(AlgebraSheaf.sections A U)
      Γ(relativeSpec A, relativeSpecToBase A ⁻¹ᵁ U)
      Γ(G, relativeSpecToBase A ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.of_restrictScalars_finite ↥(AlgebraSheaf.sections A U) _ _

/-- **The transport of finite type across [Stacks, Tag 01SB]**: a quasi-coherent module on the
relative spectrum of `A` is of finite type as soon as its direct image is of finite type as an
`A`-module. -/
theorem isFiniteType_of_isFiniteType_pushforward
    (hft : ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj.IsFiniteType) :
    G.IsFiniteType := by
  have := hft
  have : (((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj).IsQuasicoherent :=
    ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).property
  obtain ⟨κ, W, hcov, hWaff, hfin⟩ :=
    Stacks.AlgebraicGeometry.QcohOverAlgebra.exists_affineCover_module_finite A
      ((relativeSpecQcohEquivalence A).functor.obj (qcohObj A G)).obj
  exact Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_of_finite_sections_affineOpens
    G (fun j => relativeSpecToBase A ⁻¹ᵁ W j)
    (hcov.comap (relativeSpecToBase A).base.hom)
    (fun j => isAffineOpen_preimage_relativeSpecToBase A ⟨W j, hWaff j⟩)
    fun j => module_finite_sections_preimage A G (W j) (hfin j)

/-- **The module of [Stacks, Tag 01SB] attached to an `A`-module of finite type is of finite
type.**  This is the form the proof of [Stacks, Tag 0897] uses: `ℱ'` is produced as the inverse
image of `ℱ = ⨁ₙ ℱₙ` under the equivalence, and its finite type is what coherence needs. -/
theorem isFiniteType_inverse_obj
    (N : (SheafOfModules.isQuasicoherent (AlgebraSheaf.ringSheaf A)).FullSubcategory)
    (hft : N.obj.IsFiniteType) :
    (((relativeSpecQcohEquivalence A).inverse.obj N).obj).IsFiniteType := by
  have : (((relativeSpecQcohEquivalence A).inverse.obj N).obj).IsQuasicoherent :=
    ((relativeSpecQcohEquivalence A).inverse.obj N).property
  have := hft
  refine isFiniteType_of_isFiniteType_pushforward A
    ((relativeSpecQcohEquivalence A).inverse.obj N).obj ?_
  have e : N.obj ≅ ((relativeSpecQcohEquivalence A).functor.obj
      ((relativeSpecQcohEquivalence A).inverse.obj N)).obj :=
    ((SheafOfModules.isQuasicoherent (AlgebraSheaf.ringSheaf A)).ι.mapIso
      ((relativeSpecQcohEquivalence A).counitIso.app N)).symm
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u} e

end

end Stacks.AffineAlgebraEquivalence

end

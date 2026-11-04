module

public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators

/-!
# The conormal map of a morphism of first-order thickenings is the ambient comorphism

Let `i₁ : T₁ ⟶ T₁'` and `i₂ : T₂ ⟶ T₂'` be first-order thickenings and let
`(h, h') : (T₂ ⊂ T₂') ⟶ (T₁ ⊂ T₁')` be a morphism of thickenings, that is `i₂ ≫ h' = h ≫ i₁`.
[Stacks Project, Tag 01R4] produces a map of conormal sheaves `h^* 𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}`,
namely `Stacks.Immersion.immersionConormalSheafMap`. For a first-order thickening the conormal
sheaf sits inside the ambient structure sheaf by
`Stacks.Thickenings.firstOrderImmersionConormalSheafι`, and read there the map of
[Stacks Project, Tag 01R4] is nothing but the ambient comorphism `(h')^♯`.

This is the sheaf-level form of `Stacks.Thickenings.conormalTransport_apply`, which says the same
thing on global sections over affine ambient schemes.

## Main definitions

* `Stacks.Thickenings.conormalTransportSheaf`: the map of [Stacks Project, Tag 01R4] for the
  square `i₂ ≫ h' = h ≫ i₁`, transposed along `h^* ⊣ h_*`, pushed forward to `T₁'` and composed
  with the inclusion of `𝒞_{T₂/T₂'}` into `𝒪_{T₂'}`, i.e. a morphism
  `i₁_* 𝒞_{T₁/T₁'} ⟶ h'_* 𝒪_{T₂'}`.

## Main results

* `Stacks.Thickenings.conormalTransportSheaf_eq`: that morphism is the inclusion
  `i₁_* 𝒞_{T₁/T₁'} ⟶ 𝒪_{T₁'}` followed by the structure-sheaf map `(h')^♯`.
* `Stacks.Thickenings.conormalTransportSheaf_apply`: the same on sections.

## Implementation notes

For a first-order thickening the conormal quotient map `ℐ ⟶ i_* 𝒞_{T/T'}` of
[Stacks Project, Tag 01R3] is an isomorphism
(`Stacks.Thickenings.isIso_canonicalConormalQuotientMap`), so it suffices to compare the two
morphisms after precomposing with it.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 04BY](https://stacks.math.columbia.edu/tag/04BY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion Stacks.Immersion

universe u

namespace Stacks.Thickenings

variable {T₁ T₁' T₂ T₂' : Scheme.{u}} {i₁ : T₁ ⟶ T₁'} {i₂ : T₂ ⟶ T₂'}
  {h : T₂ ⟶ T₁} {h' : T₂' ⟶ T₁'}
  [AlgebraicGeometry.IsClosedImmersion i₁] [AlgebraicGeometry.IsClosedImmersion i₂]

/-- The map of [Stacks Project, Tag 01R4] of a morphism of first-order thickenings, read inside
the ambient structure sheaves. For `i₂ ≫ h' = h ≫ i₁` it is
`Stacks.Immersion.immersionConormalSheafMap` transposed along `h^* ⊣ h_*`, pushed forward along
`i₁`, carried across the square by `RingedSpaceModuleAdjunction.modulePushforwardSquareIso` and
followed by `Stacks.Thickenings.firstOrderImmersionConormalSheafι` for `i₂`:
```
i₁_* 𝒞_{T₁/T₁'} ⟶ i₁_* h_* 𝒞_{T₂/T₂'} ≅ h'_* i₂_* 𝒞_{T₂/T₂'} ⟶ h'_* 𝒪_{T₂'}.
```
By `Stacks.Thickenings.conormalTransportSheaf_eq` it is the inclusion of `𝒞_{T₁/T₁'}` into
`𝒪_{T₁'}` followed by `(h')^♯`. -/
def conormalTransportSheaf (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (cT : i₂ ≫ h' = h ≫ i₁) :
    (modulePushforward i₁.toLRSHom.toShHom).obj (immersionConormalSheaf i₁) ⟶
      (modulePushforward h'.toLRSHom.toShHom).obj
        (SheafOfModules.unit (structureSheafRing T₂'.toLocallyRingedSpace.toRingedSpace)) :=
  (modulePushforward i₁.toLRSHom.toShHom).map
      ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
        (immersionConormalSheafMap i₂ i₁ h h' (toShHom_square cT))) ≫
    (modulePushforwardSquareIso h.toLRSHom.toShHom h'.toLRSHom.toShHom i₂.toLRSHom.toShHom
          i₁.toLRSHom.toShHom (toShHom_square cT)).inv.app (immersionConormalSheaf i₂) ≫
      (modulePushforward h'.toLRSHom.toShHom).map (firstOrderImmersionConormalSheafι i₂ hi₂)

/-- The map of [Stacks Project, Tag 01R4] of a morphism of first-order thickenings is the ambient
comorphism. Read through the inclusions
`Stacks.Thickenings.firstOrderImmersionConormalSheafι` of the two conormal sheaves into the
ambient structure sheaves, the canonical map `h^* 𝒞_{T₁/T₁'} ⟶ 𝒞_{T₂/T₂'}` is the
structure-sheaf map `(h')^♯` of the ambient morphism. -/
theorem conormalTransportSheaf_eq (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (cT : i₂ ≫ h' = h ≫ i₁) :
    conormalTransportSheaf hi₁ hi₂ cT =
      firstOrderImmersionConormalSheafι i₁ hi₁ ≫ structureSheafModuleHom h'.toLRSHom.toShHom := by
  have hiso := isIso_canonicalConormalQuotientMap i₁ hi₁
  refine (cancel_epi (canonicalConormalQuotientMap i₁)).mp ?_
  rw [conormalTransportSheaf, ← Category.assoc,
    canonicalConormalQuotientMap_comp_pushforward_homEquiv i₂ i₁ h h' (toShHom_square cT)]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
    canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι, ← Functor.map_comp,
    idealSheafMap_comp_ι, Functor.map_comp, ← Category.assoc, Adjunction.unit_naturality,
    Category.assoc, unit_app_unit_comp_modulePushforward_map, ← Category.assoc,
    canonicalConormalQuotientMap_comp_firstOrderImmersionConormalSheafι]

/-- The map of [Stacks Project, Tag 01R4] of a morphism of first-order thickenings, on sections.
Over an open `V` of `T₁'`, a conormal section is carried to the image under `(h')^♯`
of its image in `𝒪_{T₁'}`. -/
theorem conormalTransportSheaf_apply (hi₁ : i₁.ker ^ 2 = ⊥) (hi₂ : i₂.ker ^ 2 = ⊥)
    (cT : i₂ ≫ h' = h ≫ i₁) (V : T₁'.Opens)
    (m : ((modulePushforward i₁.toLRSHom.toShHom).obj (immersionConormalSheaf i₁)).val.obj
      (op V)) :
    (conormalTransportSheaf hi₁ hi₂ cT).val.app (op V) m =
      (h'.app V).hom ((firstOrderImmersionConormalSheafι i₁ hi₁).val.app (op V) m) :=
  congrArg (fun φ ↦ φ.val.app (op V) m) (conormalTransportSheaf_eq hi₁ hi₂ cT)

end Stacks.Thickenings

end

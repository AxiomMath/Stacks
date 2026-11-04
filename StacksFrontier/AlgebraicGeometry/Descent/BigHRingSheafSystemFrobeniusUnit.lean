module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemOpens
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitOpenPullback

/-!
# The Frobenius system of sheaves of rings has the restriction property

`AlgebraicGeometry.BigHOver.RingSheafSystem.UnitBijective` asks of a system of sheaves of rings on
the big h category over `S` that, along the inclusion of every open `V` of every object, the unit
`M ⟶ ι_* ι^* M` of extension of scalars is bijective on the sections over every open contained in
`V`. This file proves it for the system of the Frobenius colimits `colim_F 𝒪_U` of Stacks Tag
0EXE, `AlgebraicGeometry.frobeniusRingSheafSystem`.

## Main results

* `AlgebraicGeometry.bijective_frobeniusColimit_unit_app`: for a scheme `X` in characteristic `p`,
  an open `V` and a sheaf of `colim_F 𝒪_X`-modules `M`, the unit of the adjunction between
  extension of scalars along `V.ι` and pushforward is bijective on the sections over every open
  `T ≤ V`.
* `AlgebraicGeometry.frobeniusRingSheafSystem_unitBijective`: **the Frobenius system has the
  restriction property.**

## Implementation notes

Extension of scalars along `V.ι` has a second left adjoint to the same pushforward,
`AlgebraicGeometry.frobeniusColimitSiteRestrictAdjunction` (restriction to the open subscheme,
as pushforward along the open-image functor), whose unit at `M` is on sections over `T` the
restriction map of `M` along the counit `V.ι ''ᵁ (V.ι ⁻¹ᵁ T) ⟶ T` of the open-image adjunction —
an equality of opens when `T ≤ V`. Mathlib's
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` writes the unit of the first adjunction as
the unit of the second followed by the pushforward of an isomorphism, and both factors are
bijective on sections.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

/-- **The unit of extension of scalars along the inclusion of an open is bijective on the
sections over every smaller open**, for the Frobenius colimit `colim_F 𝒪_X` of a scheme in
characteristic `p`. -/
theorem bijective_frobeniusColimit_unit_app (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (V : X.Opens) (hV : IsInCharacteristic V.toScheme p)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) (T : X.Opens)
    (hT : T ≤ V) :
    Function.Bijective
      (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
        (frobeniusColimitStructureSheafHom p V.ι hV hX)).unit.app M).val.app (op T)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (frobeniusColimitSiteRestrictAdjunction X p hX V hV)
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (frobeniusColimitStructureSheafHom p V.ι hV hX)) M
  rw [← h, BigHOver.RingSheafSystem.coe_app_comp]
  refine Function.Bijective.comp (BigHOver.RingSheafSystem.bijective_app_of_isIso _ _) ?_
  -- the unit of the restriction adjunction is a restriction map of `M`
  have hT' : (Scheme.Hom.isOpenEmbedding V.ι).isOpenMap.functor.obj
      ((Opens.map V.ι.base).obj T) = T := by
    refine le_antisymm ((Scheme.Hom.isOpenEmbedding V.ι).isOpenMap.adjunction.counit.app T).le ?_
    intro x hx
    refine ⟨⟨x, hT hx⟩, hx, rfl⟩
  have hb := BigHOver.RingSheafSystem.bijective_map_of_eq M.val
    ((Scheme.Hom.isOpenEmbedding V.ι).isOpenMap.adjunction.counit.app T).op
    (congrArg op hT').symm
  exact hb

/-- **The Frobenius system of sheaves of rings of Stacks Tag 0EXE has the restriction
property**: along the inclusion of every open `V` of every object of the big h category over `S`,
the unit of extension of scalars is bijective on the sections over the opens contained in `V`. -/
theorem frobeniusRingSheafSystem_unitBijective (B : BigHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (p : ℕ) [Fact p.Prime] (hpS : IsInCharacteristic S p) :
    (frobeniusRingSheafSystem B S hS p hpS).UnitBijective := by
  intro U V M T hT
  exact bijective_frobeniusColimit_unit_app ((BigHOver.toScheme B S hS).obj U) p
    (isInCharacteristic_bigHOver B S hS p hpS U) V
    (isInCharacteristic_bigHOver B S hS p hpS (BigHOver.opensObj B S hS V)) M T hT

end AlgebraicGeometry

end

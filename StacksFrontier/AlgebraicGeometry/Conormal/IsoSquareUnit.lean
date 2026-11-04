module

public import StacksFrontier.AlgebraicGeometry.Conormal.AffineSections

/-!
# The transport across an isomorphism square, read on the conormal quotient map

`StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare` transports the ideal sheaf and the conormal
sheaf across a commuting square
```
Z₁ --j₁--→ X₁
|          |
a          b
↓          ↓
Z₂ --j₂--→ X₂
```
of ringed spaces in which `a` and `b` are isomorphisms. [Stacks Project, Tag 01R3] part (1)
attaches to a morphism `j` a *quotient map* `ℐ_j ⟶ j_* 𝒞_j`, the unit of `j^* ⊣ j_*` at the
ideal sheaf.

This file proves that the transports are compatible with this unit on the **ideal-sheaf side**:

`Π ≫ η_{j₁ ≫ b, ℐ_{j₂}} ≫ (j₁ ≫ b)_*(c) = b_*(η_{j₁, ℐ_{j₁}}) ≫ b_*((j₁)_*((j₁)^* Q))`

where `Π` is `Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare`, `Q` is
`Stacks.ClosedImmersion.idealSheafIsoOfSquare` and `c` is the pullback composition isomorphism at
`ℐ_{j₂}`. It also records the three transports along the square's commutativity, and an expansion
of `Stacks.ClosedImmersion.conormalSheafIsoOfSquare`.

## Main results

* `Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare_comp_unit` is the statement above.
* `Stacks.ClosedImmersion.conormalSheafIsoOfSquare_hom_eq` writes
  `Stacks.ClosedImmersion.conormalSheafIsoOfSquare` out as `(j₁)^*` of
  `Stacks.ClosedImmersion.idealSheafIsoOfSquare` followed by the two pullback composition
  isomorphisms and the transport along the square's commutativity.
* `RingedSpaceModuleAdjunction.unit_app_eq_comp_eqToHom`,
  `RingedSpaceModuleAdjunction.modulePullbackCongr_hom_app` and
  `RingedSpaceModuleAdjunction.eqToHom_comp_modulePushforward_map` read the unit, the
  pullback and the pushforward along an equality of morphisms of ringed spaces.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 
open AlgebraicGeometry AlgebraicGeometry.RingedSpace

universe u

namespace RingedSpaceModuleAdjunction

variable {Z X : RingedSpace.{u, u}}

/-- **The unit of `p^* ⊣ p_*` along an equality of morphisms of ringed spaces.** For `p = q` the
unit of `q^* ⊣ q_*` is the unit of `p^* ⊣ p_*` followed by the transport of its target. -/
theorem unit_app_eq_comp_eqToHom {p q : Z ⟶ X} (h : p = q)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackPushforwardAdjunction q).unit.app M =
      (modulePullbackPushforwardAdjunction p).unit.app M ≫
        eqToHom (congrArg (fun r : Z ⟶ X =>
          (modulePushforward r).obj ((modulePullback r).obj M)) h) := by
  subst h
  exact (Category.comp_id _).symm

/-- The components of `RingedSpaceModuleAdjunction.modulePullbackCongr` are the transports
of the objects along the equality of morphisms. -/
theorem modulePullbackCongr_hom_app {p q : Z ⟶ X} (h : p = q)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackCongr h).hom.app M =
      eqToHom (congrArg (fun r : Z ⟶ X => (modulePullback r).obj M) h) := by
  subst h
  rfl

/-- **The transport of a pushforward along an equality of morphisms is natural.** For `p = q` and
a morphism `ψ` from a sheaf of modules on `Z` to `p^* M`, pushing `ψ` forward along `p` and then
transporting is the same as transporting first and pushing forward along `q` the composite of `ψ`
with the transport of `p^* M`. -/
theorem eqToHom_comp_modulePushforward_map {p q : Z ⟶ X} (h : p = q)
    (M : SheafOfModules.{u} (structureSheafRing X)) (N : SheafOfModules.{u} (structureSheafRing Z))
    (ψ : N ⟶ (modulePullback p).obj M) :
    eqToHom (congrArg (fun r : Z ⟶ X => (modulePushforward r).obj N) h) ≫
        (modulePushforward q).map (ψ ≫
          eqToHom (congrArg (fun r : Z ⟶ X => (modulePullback r).obj M) h)) =
      (modulePushforward p).map ψ ≫
        eqToHom (congrArg (fun r : Z ⟶ X =>
          (modulePushforward r).obj ((modulePullback r).obj M)) h) := by
  subst h
  simp

end RingedSpaceModuleAdjunction

namespace Stacks.ClosedImmersion

variable {Z₁ Z₂ X₁ X₂ : RingedSpace.{u, u}} (a : Z₁ ≅ Z₂) (b : X₁ ≅ X₂) (j₁ : Z₁ ⟶ X₁)
  (j₂ : Z₂ ⟶ X₂)

/-- **`Stacks.ClosedImmersion.conormalSheafIsoOfSquare` written out.** It is `(j₁)^*` of
`Stacks.ClosedImmersion.idealSheafIsoOfSquare`, followed by the inverse of the pullback
composition isomorphism at `(j₁, b)`, the transport along the square's commutativity, and the
pullback composition isomorphism at `(a, j₂)`. -/
theorem conormalSheafIsoOfSquare_hom_eq (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (conormalSheafIsoOfSquare a b j₁ j₂ comm).hom =
      (modulePullback j₁).map (idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackComp j₁ b.hom).inv.app (idealSheaf j₂) ≫
          eqToHom (congrArg (fun r : Z₁ ⟶ X₂ =>
            (modulePullback r).obj (idealSheaf j₂)) comm) ≫
            (modulePullbackComp a.hom j₂).hom.app (idealSheaf j₂) := by
  rw [conormalSheafIsoOfSquare, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    modulePullbackIsoOfSquare, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Iso.symm_hom, modulePullbackCongr_hom_app]

/-- **The ideal-sheaf transport across an isomorphism square carries the unit at `ℐ_{j₂}` to the
unit at `ℐ_{j₁}`.** Precisely: `Stacks.ClosedImmersion.pushforwardIdealSheafIsoOfSquare` followed
by the unit of `(j₁ ≫ b)^* ⊣ (j₁ ≫ b)_*` at `ℐ_{j₂}` and by the pullback composition isomorphism
is `b_*` of the unit of `(j₁)^* ⊣ (j₁)_*` at `ℐ_{j₁}`, twisted by `(j₁)^*` of
`Stacks.ClosedImmersion.idealSheafIsoOfSquare`. -/
theorem pushforwardIdealSheafIsoOfSquare_comp_unit (comm : j₁ ≫ b.hom = a.hom ≫ j₂) :
    (pushforwardIdealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
        (modulePullbackPushforwardAdjunction (j₁ ≫ b.hom)).unit.app (idealSheaf j₂) ≫
          (modulePushforward (j₁ ≫ b.hom)).map
            ((modulePullbackComp j₁ b.hom).hom.app (idealSheaf j₂)) =
      (modulePushforward b.hom).map
          ((modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁)) ≫
        (modulePushforward b.hom).map ((modulePushforward j₁).map
          ((modulePullback j₁).map (idealSheafIsoOfSquare a b j₁ j₂ comm).hom)) := by
  have hnat : (idealSheafIsoOfSquare a b j₁ j₂ comm).hom ≫
      (modulePullbackPushforwardAdjunction j₁).unit.app
        ((modulePullback b.hom).obj (idealSheaf j₂)) =
      (modulePullbackPushforwardAdjunction j₁).unit.app (idealSheaf j₁) ≫
        (modulePushforward j₁).map ((modulePullback j₁).map
          (idealSheafIsoOfSquare a b j₁ j₂ comm).hom) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (modulePullbackPushforwardAdjunction j₁).unit.naturality
        (idealSheafIsoOfSquare a b j₁ j₂ comm).hom
  rw [← unit_modulePullbackComp j₁ b.hom (idealSheaf j₂)]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (modulePushforward b.hom).map
          ((modulePullbackPushforwardAdjunction j₁).unit.app
            ((modulePullback b.hom).obj (idealSheaf j₂))))
        (pushforwardIdealSheafIsoOfSquare_hom_comp_unit a b j₁ j₂ comm)).trans
      (((modulePushforward b.hom).map_comp _ _).symm.trans
        ((congrArg (modulePushforward b.hom).map hnat).trans
          ((modulePushforward b.hom).map_comp _ _))))

end Stacks.ClosedImmersion

end

module

public import StacksFrontier.AlgebraicGeometry.Thickenings.LiftBaseIdentification
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalGenerators
public import StacksFrontier.AlgebraicGeometry.Thickenings.FirstOrderConormalInclusion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealLift
public import StacksFrontier.AlgebraicGeometry.Conormal.AffineGenerators

/-!
# Equal conormal sheaf maps make the difference of two lifts kill the defining ideal

Let `i : X ⟶ X'` be a first-order thickening — a closed immersion with square-zero defining
ideal, surjective on points — and let `a' b' : X' ⟶ Y'` be two lifts of one and the same
`a : X ⟶ Y` along `j : Y ⟶ Y'`. Their difference over an **arbitrary** open `V` of `Y'` is
`Stacks.Thickenings.mapDifferenceApp` of
`StacksFrontier/AlgebraicGeometry/Thickenings/LiftBaseIdentification.lean`. This file proves that
this difference vanishes on every section of the defining ideal of `j` over `V`, provided the two
induced maps of conormal sheaves agree.

Together with the vanishing on sections pulled back from the base and the bundling of the
difference as a derivation, this is the hypothesis under which the difference descends: the
conclusion proved here is literally the `hD` hypothesis of
`Stacks.Sites.Conormal.existsUnique_derivation_of_vanishing_on_kernel` of
`StacksFrontier/CategoryTheory/Sites/Modules/DerivationKernelDescent.lean`.

## Main results

* `Stacks.Thickenings.mapDifferenceApp_eq_zero_of_conormalSheafMap_eq`: if the two conormal sheaf
  maps induced by the squares `i ≫ a' = a ≫ j` and `i ≫ b' = a ≫ j` are equal, then
  `Stacks.Thickenings.mapDifferenceApp` kills every section of `Γ(Y', V)` annihilated by
  `j.app V`.

## Implementation notes

The affine form of this statement is
`Stacks.Thickenings.mapDifference_eq_zero_of_mem_ker` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivation.lean`, which carries
`[IsAffine X']` and `[IsAffine Y']` and compares the two lifts only on **global** sections, where
the two preimages `a' ⁻¹ᵁ ⊤` and `b' ⁻¹ᵁ ⊤` are both `⊤` and the conormal **modules** may be
compared directly. Nothing of that kind is available here: no affineness is assumed, the
hypothesis is on the conormal **sheaf** maps of
`Stacks.ClosedImmersion.conormalSheafMap`, and the open `V` is arbitrary, so the two opens
`a' ⁻¹ᵁ V` and `b' ⁻¹ᵁ V` of `X'` have to be identified by
`Stacks.Thickenings.preimage_eq_of_comm_of_surjective` before the two sides can be subtracted.

The proof runs in five steps.

1. The hypothesis `hC`, transposed across
   `RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` by
   `Stacks.ClosedImmersion.unit_comp_pushforward_homEquiv_conormalSheafMap`, puts the two squares
   in a single hom-set, so the two transposed maps agree.
2. That equality of sheaf morphisms is read on sections over `V`. Both sides are the image of one
   section `y` of the ideal sheaf of `j`, pushed into the ideal sheaf of `i` over `a' ⁻¹ᵁ V` and
   over `b' ⁻¹ᵁ V` respectively; those two sections are named `Ea` and `Eb`.
3. The unit of the adjunction is an isomorphism on the ideal sheaf of a first-order thickening,
   by `Stacks.Thickenings.isIso_unit_app_idealSheaf` — this is the only place the square-zero
   hypothesis `hsq` is used — so it may be cancelled, giving `Ea = Eb` after restriction along
   `a' ⁻¹ᵁ V ≤ b' ⁻¹ᵁ V`.
4. Pushing `Ea` and `Eb` forward along the inclusion of the ideal sheaf into the structure sheaf
   identifies them with `a'.app V x` and `b'.app V x`.
5. Since restriction along `a' ⁻¹ᵁ V ≤ b' ⁻¹ᵁ V` is restriction along an equality of opens, the
   two comorphisms agree on `x`, which is the vanishing of the difference.

The inequality of opens in step 3 is an equality by
`Stacks.Thickenings.preimage_eq_of_comm_of_surjective`, but it is carried as `homOfLE` throughout
rather than
as an `eqToHom`: the restriction maps of the sheaves involved are indexed by `≤`, and
`AlgebraicGeometry.RingedSpace.val_map_eq_of_subsingleton` absorbs the discrepancy between the
two proofs of the same inequality.

## References

* [Stacks Project, Tag 04FG](https://stacks.math.columbia.edu/tag/04FG)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.ClosedImmersion
open AlgebraicGeometry.RingedSpace

universe u

namespace Stacks.Thickenings

variable {X X' Y Y' : Scheme.{u}}
variable {i : X ⟶ X'} {j : Y ⟶ Y'} {a : X ⟶ Y} {a' b' : X' ⟶ Y'}

/-- **Equal conormal sheaf maps make the difference of two lifts kill the defining ideal of `j`,
over an arbitrary open.** If the two maps of conormal sheaves induced by the squares
`i ≫ a' = a ≫ j` and `i ≫ b' = a ≫ j` agree — the sheaf form of the hypothesis that the two maps
`a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 01R4] are equal — then
`Stacks.Thickenings.mapDifferenceApp` vanishes on every section of `Γ(Y', V)` killed by
`j.app V`, for every open `V` of `Y'`.

This is the unrestricted form of
`Stacks.Thickenings.mapDifference_eq_zero_of_mem_ker` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/MapDifferenceDerivation.lean`: no affineness is
assumed of `X'` or `Y'`, and `V` is an arbitrary open rather than `⊤`. -/
theorem mapDifferenceApp_eq_zero_of_conormalSheafMap_eq
    [AlgebraicGeometry.IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)
    (hi : Function.Surjective i.base)
    (comm_a : i ≫ a' = a ≫ j) (comm_b : i ≫ b' = a ≫ j)
    (hC : Stacks.ClosedImmersion.conormalSheafMap (Stacks.Immersion.toShHom_square comm_a) =
          Stacks.ClosedImmersion.conormalSheafMap (Stacks.Immersion.toShHom_square comm_b))
    (V : Y'.Opens) {x : Γ(Y', V)} (hx : (j.app V).hom x = 0) :
    mapDifferenceApp hi comm_a comm_b V x = 0 := by
  -- Step 5: lift `x` to a section of the ideal sheaf of `j`.
  obtain ⟨y, hy⟩ := exists_idealSheaf_section_of_app_eq_zero j.toLRSHom.toShHom V x
    ((Stacks.Immersion.structureSheafModuleHom_val_app j V x).trans hx)
  -- Step 1: the hypothesis on conormal sheaf maps, transposed, lands both squares in one
  -- hom-set, so the two right-hand sides agree.
  have h1 := unit_comp_pushforward_homEquiv_conormalSheafMap
    (Stacks.Immersion.toShHom_square comm_a)
  have h2 := unit_comp_pushforward_homEquiv_conormalSheafMap
    (Stacks.Immersion.toShHom_square comm_b)
  rw [hC] at h1
  -- Step 2: read that equality on sections over `V`.
  have key := congr($(h1.symm.trans h2).val.app (op V) y)
  simp only [AlgebraicGeometry.RingedSpace.comp_val_app_apply,
    Stacks.Immersion.modulePushforward_map_val_app_preimage] at key
  obtain ⟨Ea, hEa⟩ : ∃ E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (a' ⁻¹ᵁ V)),
      ((modulePushforward a'.toLRSHom.toShHom).map
          (idealSheafMap (Stacks.Immersion.toShHom_square comm_a))).val.app (op V)
        (((modulePullbackPushforwardAdjunction a'.toLRSHom.toShHom).unit.app
          (idealSheaf j.toLRSHom.toShHom)).val.app (op V) y) = E := ⟨_, rfl⟩
  obtain ⟨Eb, hEb⟩ : ∃ E : (idealSheaf i.toLRSHom.toShHom).val.obj (op (b' ⁻¹ᵁ V)),
      ((modulePushforward b'.toLRSHom.toShHom).map
          (idealSheafMap (Stacks.Immersion.toShHom_square comm_b))).val.app (op V)
        (((modulePullbackPushforwardAdjunction b'.toLRSHom.toShHom).unit.app
          (idealSheaf j.toLRSHom.toShHom)).val.app (op V) y) = E := ⟨_, rfl⟩
  rw [hEa, hEb] at key
  -- The three opens of `X` in play are all equal.
  have hab' : a' ⁻¹ᵁ V ≤ b' ⁻¹ᵁ V := le_of_eq (preimage_eq_of_comm_of_surjective hi comm_a comm_b V)
  have hab : i ⁻¹ᵁ a' ⁻¹ᵁ V ≤ i ⁻¹ᵁ b' ⁻¹ᵁ V := i.preimage_mono hab'
  have hga : i ⁻¹ᵁ a' ⁻¹ᵁ V ≤ a ⁻¹ᵁ j ⁻¹ᵁ V := by
    have h : (i ≫ a') ⁻¹ᵁ V = (a ≫ j) ⁻¹ᵁ V := by rw [comm_a]
    exact le_of_eq h
  have hra := modulePushforwardSquareIso_hom_val_app_restrict a.toLRSHom.toShHom
    a'.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom
    (Stacks.Immersion.toShHom_square comm_a)
    (conormalSheaf i.toLRSHom.toShHom) V (homOfLE hga) (homOfLE (le_refl (i ⁻¹ᵁ a' ⁻¹ᵁ V)))
    (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)).val.app (op (a' ⁻¹ᵁ V)) Ea)
  have hrb := modulePushforwardSquareIso_hom_val_app_restrict a.toLRSHom.toShHom
    b'.toLRSHom.toShHom i.toLRSHom.toShHom j.toLRSHom.toShHom
    (Stacks.Immersion.toShHom_square comm_b)
    (conormalSheaf i.toLRSHom.toShHom) V (homOfLE hga) (homOfLE hab)
    (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)).val.app (op (b' ⁻¹ᵁ V)) Eb)
  have key2 := hra.symm.trans ((val_map_congr (homOfLE hga) key).trans hrb)
  have hid := congr($((conormalSheaf i.toLRSHom.toShHom).val.map_id (op (i ⁻¹ᵁ a' ⁻¹ᵁ V)))
    (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)).val.app (op (a' ⁻¹ᵁ V)) Ea))
  have hnat := val_app_naturality
    ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)) (homOfLE hab') Eb
  have hpf := modulePushforward_obj_val_map i.toLRSHom.toShHom
    (conormalSheaf i.toLRSHom.toShHom) (homOfLE hab')
    (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)).val.app (op (b' ⁻¹ᵁ V)) Eb)
  have hsub := val_map_eq_of_subsingleton (conormalSheaf i.toLRSHom.toShHom)
    ((Opens.map i.toLRSHom.toShHom.hom.base).map (homOfLE hab')) (homOfLE hab)
    (((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)).val.app (op (b' ⁻¹ᵁ V)) Eb)
  -- Step 3: cancel the unit, which is an isomorphism for a first-order thickening.
  have := isIso_unit_app_idealSheaf i hsq
  have : Mono ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
      (idealSheaf i.toLRSHom.toShHom)) := IsIso.mono_of_iso _
  have hE : Ea = (idealSheaf i.toLRSHom.toShHom).val.map (homOfLE hab').op Eb :=
    Stacks.SheafOfModules.injective_val_app_of_mono_evaluation
      ((modulePullbackPushforwardAdjunction i.toLRSHom.toShHom).unit.app
        (idealSheaf i.toLRSHom.toShHom)) (op (a' ⁻¹ᵁ V))
      (hid.symm.trans (key2.trans (hsub.symm.trans (hpf.symm.trans hnat.symm))))
  -- Step 4: push into `𝒪_{X'}`.
  have hι : ∀ {c : X' ⟶ Y'} (comm : i ≫ c = a ≫ j),
      (idealSheafι i.toLRSHom.toShHom).val.app (op (c ⁻¹ᵁ V))
        (((modulePushforward c.toLRSHom.toShHom).map
          (idealSheafMap (Stacks.Immersion.toShHom_square comm))).val.app (op V)
        (((modulePullbackPushforwardAdjunction c.toLRSHom.toShHom).unit.app
          (idealSheaf j.toLRSHom.toShHom)).val.app (op V) y)) = (c.app V).hom x := by
    intro c comm
    have h := congr($(unit_comp_pushforward_idealSheafMap_comp_ι
      (Stacks.Immersion.toShHom_square comm)).val.app (op V) y)
    simp only [Functor.map_comp, AlgebraicGeometry.RingedSpace.comp_val_app_apply,
      Stacks.Immersion.modulePushforward_map_val_app_preimage] at h
    exact h.trans ((congrArg
        (fun z => (structureSheafModuleHom c.toLRSHom.toShHom).val.app (op V) z) hy).trans
      (Stacks.Immersion.structureSheafModuleHom_val_app c V x))
  have ha'x := hι comm_a
  have hb'x := hι comm_b
  rw [hEa] at ha'x
  rw [hEb] at hb'x
  have hfin : (a'.app V).hom x =
      (SheafOfModules.unit (structureSheafRing X'.toLocallyRingedSpace.toRingedSpace)).val.map
        (homOfLE hab').op ((b'.app V).hom x) := by
    rw [← ha'x, ← hb'x, hE]
    exact val_app_naturality (idealSheafι i.toLRSHom.toShHom) (homOfLE hab') Eb
  refine Subtype.ext ?_
  rw [mapDifferenceApp_coe, ZeroMemClass.coe_zero, sub_eq_zero, secondLiftAppLE,
    Scheme.Hom.appLE_eq_app, Stacks.Immersion.appLE_apply]
  exact hfin

end Stacks.Thickenings

end

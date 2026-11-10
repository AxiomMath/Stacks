module

public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.AlgebraicGeometry.TateMap.Basic

/-!
# Morphisms of the category of Section 0FKB are chart base changes on affine charts

Let `b/a : Y'/X' → Y/X` be a morphism of the category of Stacks, Section 0FKB: a commutative
square identifying `Y'` with an open subscheme of `X' ×_X Y`. Around every point of `Y'` there
are affine opens `U ⊆ X`, `V ⊆ Y`, `U' ⊆ X'`, `V' ⊆ Y'` compatible with the four maps for which
`Γ(Y', V')` is a principal localization of `Γ(X', U') ⊗_{Γ(X, U)} Γ(Y, V)`: the square is, on
those charts, a chart base change. So the compatibility with base change required of the Tate
map, read on charts, applies around every point of every morphism of the category.

## Main definitions

* `Stacks.TateMap.ChartBaseChange.ofIsPushout`: a principal localization of a pushout is a chart
  base change.

## Main results

* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.exists_chartBaseChange`: the affine charts
  around a point of `Y'`.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.TateMap.ChartBaseChange

variable {A B A' B' C : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing C]
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B']
  [Algebra A C] [Algebra A' C] [Algebra B C] [IsScalarTower A A' C] [IsScalarTower A B C]
  [Algebra.IsPushout A A' B C] [Algebra C B'] [IsScalarTower A' C B'] [IsScalarTower B C B']

/-- **A principal localization of a pushout is a chart base change.** If `C = A' ⊗_A B` (as a
pushout) and `B'` is the localization of `C` away from an element, compatibly with the maps from
`A'` and `B`, then `B'` is a chart base change of `A → B` along `A → A'`. -/
def ofIsPushout (c : C) [IsLocalization.Away c B'] : ChartBaseChange A B A' B' :=
  let ε := Algebra.IsPushout.equiv A A' B C
  { algebra := ((algebraMap C B').comp ε.toRingHom).toAlgebra
    base_left := fun y ↦ by
      change algebraMap C B' (ε (y ⊗ₜ 1)) = _
      rw [Algebra.IsPushout.equiv_tmul, map_one, mul_one, ← IsScalarTower.algebraMap_apply]
    base_right := fun x ↦ by
      change algebraMap C B' (ε (1 ⊗ₜ x)) = _
      rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul, ← IsScalarTower.algebraMap_apply]
    elt := ε.symm c
    isLocalization := by
      have h := IsLocalization.isLocalization_of_base_ringEquiv (S := B') (Submonoid.powers c)
        ε.symm.toRingEquiv
      rw [Submonoid.map_powers] at h
      exact h }

end Stacks.TateMap.ChartBaseChange

namespace AlgebraicGeometry.TateMap.OpenBaseChangeSquare

/-- **A morphism of the category of Section 0FKB is a chart base change around every point.**
For a morphism `b/a : Y'/X' → Y/X` (with `a = sq.base`, `b = sq.cover`) and a point `y'` of `Y'`
there are affine opens `U ⊆ X`, `V ⊆ Y`, `U' ⊆ X'`, `V' ⊆ Y'` with `y' ∈ V'`, compatible with the
four maps, such that `Γ(Y', V')` is a chart base change of `Γ(X, U) → Γ(Y, V)` along
`Γ(X, U) → Γ(X', U')`, for the algebra structures given by the maps on sections. -/
theorem exists_chartBaseChange {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
    (sq : OpenBaseChangeSquare f f') (y' : Y') :
    ∃ (U : X.affineOpens) (V : Y.affineOpens) (U' : X'.affineOpens) (V' : Y'.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
      (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1), y' ∈ V'.1 ∧
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
      letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
      letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
      Nonempty (Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1)) := by
  have := sq.isOpenImmersion
  set ι := pullback.lift f' sq.cover sq.w.symm with hι
  have H : IsPullback (pullback.snd sq.base f) (pullback.fst sq.base f) f sq.base :=
    (IsPullback.of_hasPullback sq.base f).flip
  -- the charts of the base and of the source
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (sq.cover y'))) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show sq.cover y' ∈ f ⁻¹ᵁ U from hyU)
      (f ⁻¹ᵁ U).isOpen
  replace hVU : V ≤ f ⁻¹ᵁ U := hVU
  have hx' : f' y' ∈ sq.base ⁻¹ᵁ U := by
    change sq.base (f' y') ∈ U
    rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]
    exact hVU hyV
  obtain ⟨-, ⟨U', hU', rfl⟩, hyU', hU'U⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hx' (sq.base ⁻¹ᵁ U).isOpen
  replace hU'U : U' ≤ sq.base ⁻¹ᵁ U := hU'U
  have appLE_eq : ∀ {S T : Scheme.{u}} {φ ψ : S ⟶ T} (_ : φ = ψ) {O : T.Opens} {O' : S.Opens}
      (e : O' ≤ φ ⁻¹ᵁ O) (e' : O' ≤ ψ ⁻¹ᵁ O), φ.appLE O O' e = ψ.appLE O O' e' := by
    intro S T φ ψ h O O' e e'; subst h; rfl
  -- the affine open of the fibre product
  set W : (pullback sq.base f).Opens :=
    pullback.snd sq.base f ⁻¹ᵁ V ⊓ pullback.fst sq.base f ⁻¹ᵁ U' with hWdef
  have hW : IsAffineOpen W := IsAffineOpen.inf_preimage_of_isPullback H hU hV hVU hU' hU'U rfl
  have hιfst : ∀ z, pullback.fst sq.base f (ι z) = f' z := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, hι, pullback.lift_fst]
  have hιsnd : ∀ z, pullback.snd sq.base f (ι z) = sq.cover z := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, hι, pullback.lift_snd]
  have hyW : ι y' ∈ W := ⟨by change _ ∈ V; rw [hιsnd]; exact hyV,
    by change _ ∈ U'; rw [hιfst]; exact hyU'⟩
  obtain ⟨g, hgle, hyg⟩ := hW.exists_basicOpen_le (V := W ⊓ ι.opensRange)
    ⟨ι y', hyW, y', rfl⟩ hyW
  set D := (pullback sq.base f).basicOpen g with hD
  have hDW : D ≤ W := fun z hz ↦ (hgle hz).1
  have hDι : D ≤ ι.opensRange := fun z hz ↦ (hgle hz).2
  set V' := ι ⁻¹ᵁ D with hV'def
  have hV' : IsAffineOpen V' := (hW.basicOpen g).preimage_of_isOpenImmersion ι hDι
  have hyV' : y' ∈ V' := hyg
  have hV'W : V' ≤ ι ⁻¹ᵁ W := fun z hz ↦ hDW hz
  have hV'U' : V' ≤ f' ⁻¹ᵁ U' := fun z hz ↦ by
    have := (hV'W hz).2
    change f' z ∈ U'
    rw [← hιfst]; exact this
  have hV'V : V' ≤ sq.cover ⁻¹ᵁ V := fun z hz ↦ by
    have := (hV'W hz).1
    change sq.cover z ∈ V
    rw [← hιsnd]; exact this
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, ⟨U', hU'⟩, ⟨V', hV'⟩, hVU, hU'U, hV'U', hV'V, hyV', ?_⟩
  let : Algebra Γ(X, U) Γ(Y, V) := (f.appLE U V hVU).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', U') := (sq.base.appLE U U' hU'U).hom.toAlgebra
  let : Algebra Γ(X', U') Γ(Y', V') := (f'.appLE U' V' hV'U').hom.toAlgebra
  let : Algebra Γ(Y, V) Γ(Y', V') := (sq.cover.appLE V V' hV'V).hom.toAlgebra
  -- the pushout `Γ(P, W) = Γ(X', U') ⊗_{Γ(X, U)} Γ(Y, V)`
  let : Algebra Γ(Y, V) Γ(pullback sq.base f, W) :=
    ((pullback.snd sq.base f).appLE V W inf_le_left).hom.toAlgebra
  let : Algebra Γ(X', U') Γ(pullback sq.base f, W) :=
    ((pullback.fst sq.base f).appLE U' W inf_le_right).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(pullback sq.base f, W) :=
    ((algebraMap Γ(Y, V) Γ(pullback sq.base f, W)).comp (algebraMap Γ(X, U) Γ(Y, V))).toAlgebra
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ(pullback sq.base f, W) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower Γ(X, U) Γ(X', U') Γ(pullback sq.base f, W) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change ((f.appLE U V hVU) ≫ (pullback.snd sq.base f).appLE V W inf_le_left) a =
        ((sq.base.appLE U U' hU'U) ≫ (pullback.fst sq.base f).appLE U' W inf_le_right) a
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_eq H.w]
  have : Algebra.IsPushout Γ(X, U) Γ(X', U') Γ(Y, V) Γ(pullback sq.base f, W) :=
    algebra_isPushout_appLE_of_isPullback H hU hV hVU hU' hU'U rfl
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  -- `Γ(Y', V')` is the localization of `Γ(P, W)` away from `g`
  let : Algebra Γ(pullback sq.base f, W) Γ(Y', V') := (ι.appLE W V' hV'W).hom.toAlgebra
  have : IsScalarTower Γ(X', U') Γ(pullback sq.base f, W) Γ(Y', V') :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change (f'.appLE U' V' hV'U') a =
        ((pullback.fst sq.base f).appLE U' W inf_le_right ≫ ι.appLE W V' hV'W) a
      rw [Scheme.Hom.appLE_comp_appLE, appLE_eq (pullback.lift_fst _ _ _)]
  have : IsScalarTower Γ(Y, V) Γ(pullback sq.base f, W) Γ(Y', V') :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change (sq.cover.appLE V V' hV'V) a =
        ((pullback.snd sq.base f).appLE V W inf_le_left ≫ ι.appLE W V' hV'W) a
      rw [Scheme.Hom.appLE_comp_appLE, appLE_eq (pullback.lift_snd _ _ _)]
  have hlocD := hW.isLocalization_of_eq_basicOpen g (homOfLE hDW) rfl
  let := ((pullback sq.base f).presheaf.map (homOfLE hDW).op).hom.toAlgebra
  have : IsIso (ι.app D) := ι.isIso_app D hDι
  let e : Γ(pullback sq.base f, D) ≃+* Γ(Y', V') := (asIso (ι.app D)).commRingCatIsoToRingEquiv
  have he : ∀ c, e (algebraMap Γ(pullback sq.base f, W) Γ(pullback sq.base f, D) c) =
      algebraMap Γ(pullback sq.base f, W) Γ(Y', V') c := fun c ↦ by
    change ((pullback sq.base f).presheaf.map (homOfLE hDW).op ≫ ι.app D) c =
      (ι.appLE W V' hV'W) c
    rw [ι.app_eq_appLE, Scheme.Hom.map_appLE]
  have : IsLocalization.Away g Γ(Y', V') :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g)
      (AlgEquiv.ofRingEquiv (f := e) he)
  exact ⟨Stacks.TateMap.ChartBaseChange.ofIsPushout g⟩

end AlgebraicGeometry.TateMap.OpenBaseChangeSquare

module

public import StacksFrontier.AlgebraicGeometry.TateMap.BaseChangeCharts

/-!
# Chart base changes of a morphism of Section 0FKB inside prescribed charts

Let `b/a : Y'/X' → Y/X` be a morphism of the category of Stacks, Section 0FKB. For prescribed
affine opens `U ⊆ X`, `V ⊆ Y` with `f(V) ⊆ U`, every point `y'` of `Y'` mapping into `V` and every
open neighbourhood `O'` of `y'` there are affine opens `U' ⊆ X'`, `V' ⊆ O'` with `y' ∈ V'` on which
the square is a chart base change. In particular these `V'` form a basis of the topology of the
preimage of `V`.

## Main results

* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.exists_chartBaseChange_of_le`.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TateMap.OpenBaseChangeSquare

/-- **Chart base changes inside prescribed charts.** For affine opens `U ⊆ X`, `V ⊆ Y` with
`f(V) ⊆ U`, a point `y'` of `Y'` with `b(y') ∈ V` and an open neighbourhood `O'` of `y'`, there are
affine opens `U' ⊆ a⁻¹(U)` and `V' ⊆ O'` containing `y'`, compatible with the four maps, on which
the square is a chart base change. -/
theorem exists_chartBaseChange_of_le {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
    (sq : OpenBaseChangeSquare f f') (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (y' : Y') (hyV : sq.cover y' ∈ V.1) (O' : Y'.Opens)
    (hyO : y' ∈ O') :
    ∃ (U' : X'.affineOpens) (V' : Y'.affineOpens)
      (hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1) (hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1)
      (hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1), y' ∈ V'.1 ∧ V'.1 ≤ O' ∧
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
      letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
      letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
      Nonempty (Stacks.TateMap.ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1)) := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨V, hV⟩ := V
  change V ≤ f ⁻¹ᵁ U at hVU
  change sq.cover y' ∈ V at hyV
  have := sq.isOpenImmersion
  set ι := pullback.lift f' sq.cover sq.w.symm with hι
  have H : IsPullback (pullback.snd sq.base f) (pullback.fst sq.base f) f sq.base :=
    (IsPullback.of_hasPullback sq.base f).flip
  have hx' : f' y' ∈ sq.base ⁻¹ᵁ U := by
    show sq.base (f' y') ∈ U
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
  have hmem : ∀ z, ι z ∈ W ↔ sq.cover z ∈ V ∧ f' z ∈ U' := fun z ↦ by
    change pullback.snd sq.base f (ι z) ∈ V ∧ pullback.fst sq.base f (ι z) ∈ U' ↔ _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hι, pullback.lift_fst, pullback.lift_snd]
  have hyW : ι y' ∈ W := (hmem y').2 ⟨hyV, hyU'⟩
  have hyO' : ι y' ∈ ι ''ᵁ O' := ⟨y', hyO, rfl⟩
  obtain ⟨g, hgle, hyg⟩ := hW.exists_basicOpen_le (V := W ⊓ ι ''ᵁ O') ⟨ι y', hyW, hyO'⟩ hyW
  set D := (pullback sq.base f).basicOpen g with hD
  have hDW : D ≤ W := fun z hz ↦ (hgle hz).1
  have hDO : D ≤ ι ''ᵁ O' := fun z hz ↦ (hgle hz).2
  have hDι : D ≤ ι.opensRange := hDO.trans (ι.image_le_opensRange O')
  set V' := ι ⁻¹ᵁ D with hV'def
  have hV' : IsAffineOpen V' := (hW.basicOpen g).preimage_of_isOpenImmersion ι hDι
  have hyV' : y' ∈ V' := hyg
  have hV'W : V' ≤ ι ⁻¹ᵁ W := fun z hz ↦ hDW hz
  have hV'U' : V' ≤ f' ⁻¹ᵁ U' := fun z hz ↦ ((hmem z).1 (hV'W hz)).2
  have hV'V : V' ≤ sq.cover ⁻¹ᵁ V := fun z hz ↦ ((hmem z).1 (hV'W hz)).1
  have hV'O : V' ≤ O' := by
    rw [hV'def, ← ι.preimage_image_eq O']
    exact ι.preimage_mono hDO
  refine ⟨⟨U', hU'⟩, ⟨V', hV'⟩, hU'U, hV'U', hV'V, hyV', hV'O, ?_⟩
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
      show ((f.appLE U V hVU) ≫ (pullback.snd sq.base f).appLE V W inf_le_left) a =
        ((sq.base.appLE U U' hU'U) ≫ (pullback.fst sq.base f).appLE U' W inf_le_right) a
      rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_eq H.w]
  have : Algebra.IsPushout Γ(X, U) Γ(X', U') Γ(Y, V) Γ(pullback sq.base f, W) :=
    algebra_isPushout_appLE_of_isPullback H hU hV hVU hU' hU'U rfl
      (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  -- `Γ(Y', V')` is the localization of `Γ(P, W)` away from `g`
  let : Algebra Γ(pullback sq.base f, W) Γ(Y', V') := (ι.appLE W V' hV'W).hom.toAlgebra
  have : IsScalarTower Γ(X', U') Γ(pullback sq.base f, W) Γ(Y', V') :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      show (f'.appLE U' V' hV'U') a =
        ((pullback.fst sq.base f).appLE U' W inf_le_right ≫ ι.appLE W V' hV'W) a
      rw [Scheme.Hom.appLE_comp_appLE, appLE_eq (pullback.lift_fst _ _ _)]
  have : IsScalarTower Γ(Y, V) Γ(pullback sq.base f, W) Γ(Y', V') :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      show (sq.cover.appLE V V' hV'V) a =
        ((pullback.snd sq.base f).appLE V W inf_le_left ≫ ι.appLE W V' hV'W) a
      rw [Scheme.Hom.appLE_comp_appLE, appLE_eq (pullback.lift_snd _ _ _)]
  have hlocD := hW.isLocalization_of_eq_basicOpen g (homOfLE hDW) rfl
  let := ((pullback sq.base f).presheaf.map (homOfLE hDW).op).hom.toAlgebra
  have : IsIso (ι.app D) := ι.isIso_app D hDι
  let e : Γ(pullback sq.base f, D) ≃+* Γ(Y', V') := (asIso (ι.app D)).commRingCatIsoToRingEquiv
  have he : ∀ c, e (algebraMap Γ(pullback sq.base f, W) Γ(pullback sq.base f, D) c) =
      algebraMap Γ(pullback sq.base f, W) Γ(Y', V') c := fun c ↦ by
    show ((pullback sq.base f).presheaf.map (homOfLE hDW).op ≫ ι.app D) c =
      (ι.appLE W V' hV'W) c
    rw [ι.app_eq_appLE, Scheme.Hom.map_appLE]
  have : IsLocalization.Away g Γ(Y', V') :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers g)
      (AlgEquiv.ofRingEquiv (f := e) he)
  exact ⟨Stacks.TateMap.ChartBaseChange.ofIsPushout g⟩

end AlgebraicGeometry.TateMap.OpenBaseChangeSquare

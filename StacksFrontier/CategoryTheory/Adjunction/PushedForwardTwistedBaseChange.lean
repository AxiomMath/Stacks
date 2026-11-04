module

public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardBaseChange
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableSquare

/-!
# The pushed-forward base change map of right adjoints of pushforward

In the situation of `Stacks.CategoryTheory.BaseChange.pushforwardSquare`, suppose moreover that
the two pushforwards have right adjoints, `Rf ⊣ a` and `Rf' ⊣ a'`. The comparison
`σ : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg` of the composite pushforwards has a mate `ξ : a' ⋙ Rg' ⟶ Rg ⋙ a`, and
when `ξ` is invertible the base change map `β : a ⋙ Lg' ⟶ Lg ⋙ a'` of the right adjoints is the
mate of `ξ⁻¹`. This file identifies `Rg'(β_K)`, followed by `ξ`, with the two-variable comparison
`B(a K, Lf J) ⟶ a(A(K, J))` of `a` at `J = Rg 𝟙'`: the source of [Stacks, Tag 0AA8].

## Main definitions

* `Stacks.CategoryTheory.BaseChange.composedPushforwardSquare` — `σ`.
* `Stacks.CategoryTheory.BaseChange.rightAdjointSquare` — `ξ`.
* `Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange` — `β`.
* `Stacks.CategoryTheory.BaseChange.rightAdjointTensorComparison` — the two-variable comparison.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_rightAdjointBaseChange_comp_counit` — the adjunct of `β`
  under `Rf' ⊣ a'` is the inverse base change map followed by `Lg` of the counit.
* `Stacks.CategoryTheory.BaseChange.isIso_rightAdjointSquare` — `ξ` is invertible when the base
  change map of pushforward along pullback is.
* `Stacks.CategoryTheory.BaseChange.unitProjection_comp_map_rightAdjointBaseChange_comp` — the
  identification of `Rg'(β_K)` with the two-variable comparison of `a`.
* `Stacks.CategoryTheory.BaseChange.isIso_map_rightAdjointBaseChange` — hence `Rg'(β_K)` is
  invertible when the comparison is.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped CategoryTheory.Prod

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {S : Type*} {T : Type*} {S' : Type*} {T' : Type*}
  [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'}
  {Lg : S ⥤ S'} {Rg : S' ⥤ S} {Lg' : T ⥤ T'} {Rg' : T' ⥤ T} {Lc : S ⥤ T'}
  (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  {a : S ⥤ T} {a' : S' ⥤ T'} (adja : Rf ⊣ a) (adja' : Rf' ⊣ a')

/-- **The comparison of the composite pushforwards**, `σ : Rg' ⋙ Rf ⟶ Rf' ⋙ Rg`, the conjugate
of the identification `Lg ⋙ Lf' ⟶ Lf ⋙ Lg'` of the composite pullbacks. -/
def composedPushforwardSquare : TwoSquare Rg' Rf' Rf Rg :=
  conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') (squareCompositeIso eg ef).hom

/-- The comparison `σ` of the composite pushforwards is an isomorphism. -/
instance : IsIso (composedPushforwardSquare adjf adjf' adjg adjg' eg ef).natTrans := by
  unfold composedPushforwardSquare; infer_instance

/-- `σ` is the inverse of the comparison `ψ = pushforwardSquare`. -/
theorem pushforwardSquare_comp_composedPushforwardSquare :
    pushforwardSquare adjf adjf' adjg adjg' eg ef ≫
      (composedPushforwardSquare adjf adjf' adjg adjg' eg ef).natTrans = 𝟙 _ :=
  conjugateEquiv_comm _ _ (Iso.hom_inv_id _)

/-- The base change map of pushforward along pullback is the inverse mate of `σ`. -/
theorem mateEquiv_symm_composedPushforwardSquare :
    (mateEquiv adjg' adjg).symm (composedPushforwardSquare adjf adjf' adjg adjg' eg ef) =
      twoSquare adjf adjf' eg ef := by
  apply (mateEquiv adjg' adjg).injective
  rw [Equiv.apply_symm_apply]
  ext1
  rw [twoSquare, iterated_mateEquiv_conjugateEquiv]
  rfl

/-- **The mate `ξ : a' ⋙ Rg' ⟶ Rg ⋙ a`** of `σ` under `Rf' ⊣ a'` and `Rf ⊣ a`. -/
def rightAdjointSquare : TwoSquare a' Rg Rg' a :=
  mateEquiv adja' adja (composedPushforwardSquare adjf adjf' adjg adjg' eg ef)

/-- `σ` is the mate of the base change map of pushforward along pullback. -/
theorem composedPushforwardSquare_eq_mateEquiv :
    composedPushforwardSquare adjf adjf' adjg adjg' eg ef =
      mateEquiv adjg' adjg (twoSquare adjf adjf' eg ef) := by
  rw [← mateEquiv_symm_composedPushforwardSquare, Equiv.apply_symm_apply]

/-- **`ξ` is the conjugate of the base change map** of pushforward along pullback, under the
composite adjunctions `Lg' ⋙ Rf' ⊣ a' ⋙ Rg'` and `Rf ⋙ Lg ⊣ Rg ⋙ a`. -/
theorem rightAdjointSquare_natTrans_eq :
    (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans =
      conjugateEquiv (adjg'.comp adja') (adja.comp adjg) (twoSquare adjf adjf' eg ef).natTrans := by
  rw [rightAdjointSquare, composedPushforwardSquare_eq_mateEquiv,
    ← iterated_mateEquiv_conjugateEquiv]

/-- `ξ` is invertible as soon as the base change map of pushforward along pullback is. -/
theorem isIso_rightAdjointSquare [IsIso (twoSquare adjf adjf' eg ef).natTrans] :
    IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans := by
  rw [rightAdjointSquare_natTrans_eq]; infer_instance

variable [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans]

/-- **The base change map `β : a ⋙ Lg' ⟶ Lg ⋙ a'`** of the right adjoints, the inverse mate of
`ξ⁻¹` under `Lg ⊣ Rg` and `Lg' ⊣ Rg'`. -/
def rightAdjointBaseChange : TwoSquare a Lg Lg' a' :=
  (mateEquiv adjg adjg').symm
    (TwoSquare.mk _ _ _ _
      (inv (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans))

/-- **`β` is the mate of the inverse base change map of pushforward along pullback**, under
`Rf ⊣ a` and `Rf' ⊣ a'`. -/
theorem rightAdjointBaseChange_eq [IsIso (twoSquare adjf adjf' eg ef).natTrans] :
    rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja' =
      mateEquiv adja adja' (TwoSquare.mk _ _ _ _ (inv (twoSquare adjf adjf' eg ef).natTrans)) := by
  apply (mateEquiv adjg adjg').injective
  rw [rightAdjointBaseChange, Equiv.apply_symm_apply]
  refine Eq.trans ?_ (iterated_mateEquiv_conjugateEquiv adja adja' adjg' adjg _).symm
  show inv (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans =
    conjugateEquiv (adja.comp adjg) (adjg'.comp adja') (inv (twoSquare adjf adjf' eg ef).natTrans)
  rw [← cancel_epi (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans,
    IsIso.hom_inv_id, rightAdjointSquare_natTrans_eq]
  exact (conjugateEquiv_comm _ _ (IsIso.inv_hom_id _)).symm

/-- **The adjunct of `β` under `Rf' ⊣ a'`** is the inverse base change map of pushforward along
pullback at `a K`, followed by `Lg` of the counit of `Rf ⊣ a`. -/
theorem map_rightAdjointBaseChange_comp_counit [IsIso (twoSquare adjf adjf' eg ef).natTrans]
    (K : S) :
    Rf'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K) ≫
        adja'.counit.app (Lg.obj K) =
      (inv (twoSquare adjf adjf' eg ef).natTrans).app (a.obj K) ≫ Lg.map (adja.counit.app K) := by
  rw [rightAdjointBaseChange_eq, mateEquiv_counit]

section Tensor

variable (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')
  (o' : S') (ρ' : Functor.prod' (𝟭 S') ((Functor.const S').obj o') ⋙ A' ⟶ 𝟭 S')
  (o'' : T') (ρ'' : Functor.prod' (𝟭 T') ((Functor.const T').obj o'') ⋙ B' ⟶ 𝟭 T')
  (u : Lf'.obj o' ⟶ o'')

/-- **The two-variable comparison of the right adjoint `a`**, `B(a K, Lf H) ⟶ a(A(K, H))`: the
adjunct under `Rf ⊣ a` of the inverse projection-formula map followed by the counit of `Rf ⊣ a`
in the first factor. -/
def rightAdjointTensorComparison (K H : S)
    [IsIso (adjunctionTensorMap adjf A B αf (a.obj K) H)] :
    B.obj (a.obj K, Lf.obj H) ⟶ a.obj (A.obj (K, H)) :=
  adja.homEquiv _ _ (inv (adjunctionTensorMap adjf A B αf (a.obj K) H) ≫
    A.map (adja.counit.app K ×ₘ 𝟙 H))

omit [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans] in
/-- **The pushed-forward base change map of right adjoints, through the two-variable
comparison.** `Φ'`, then `Rg'` of `β_K`, then `ξ`, is the inverse of `τ` in the second factor,
then the two-variable comparison of `a` at `(K, J)`, then `a` of `Φ`. -/
theorem unitProjection_comp_map_rightAdjointBaseChange_comp (K : S)
    [IsIso (twoSquare adjf adjf' eg ef).natTrans]
    [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans]
    [IsIso (adjunctionTensorMap adjf A B αf (a.obj K) (Rg.obj o'))]
    [IsIso (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)]
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj (a.obj K))
      (Rg.obj o'))
    (hunit : ∀ X : S', αf'.app (X, o') ≫ B'.map (𝟙 (Lf'.obj X) ×ₘ u) ≫ ρ''.app (Lf'.obj X) =
      Lf'.map (ρ'.app X)) :
    unitProjection adjg' B' B αg' o'' ρ'' (a.obj K) ≫
        Rg'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K) ≫
          (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans.app (Lg.obj K) =
      B.map (𝟙 (a.obj K) ×ₘ inv (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)) ≫
        rightAdjointTensorComparison adjf adja A B αf K (Rg.obj o') ≫
          a.map (unitProjection adjg A' A αg o' ρ' K) := by
  apply (adja.homEquiv _ _).symm.injective
  have hξ := mateEquiv_counit adja' adja (composedPushforwardSquare adjf adjf' adjg adjg' eg ef)
    (Lg.obj K)
  have hβ := map_rightAdjointBaseChange_comp_counit adjf adjf' adjg adjg' eg ef adja adja' K
  have hσ := (composedPushforwardSquare adjf adjf' adjg adjg' eg ef).natTrans.naturality
    ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K)
  have hIB := unitProjection_comp_map_comp_pushforwardSquare adjf adjf' adjg adjg' eg ef A A' B B'
    αf αf' αg αg' o' ρ' o'' ρ'' u (a.obj K) hsq hunit
  have hψσ := congrArg (fun t => t.app (Lg'.obj (a.obj K)))
    (pushforwardSquare_comp_composedPushforwardSquare adjf adjf' adjg adjg' eg ef)
  simp only [NatTrans.comp_app, NatTrans.id_app] at hψσ
  have hΦ : A.map (adja.counit.app K ×ₘ 𝟙 (Rg.obj o')) ≫ unitProjection adjg A' A αg o' ρ' K =
      unitProjection adjg A' A αg o' ρ' (Rf.obj (a.obj K)) ≫ Rg.map (Lg.map (adja.counit.app K)) :=
    unitProjection_naturality adjg A' A αg o' ρ' (adja.counit.app K)
  have hC : Rf.map (rightAdjointTensorComparison adjf adja A B αf K (Rg.obj o')) ≫
      adja.counit.app (A.obj (K, Rg.obj o')) =
      inv (adjunctionTensorMap adjf A B αf (a.obj K) (Rg.obj o')) ≫
        A.map (adja.counit.app K ×ₘ 𝟙 (Rg.obj o')) := by
    rw [rightAdjointTensorComparison]
    exact (adja.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)
  have hτ : B.map (𝟙 (a.obj K) ×ₘ inv (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)) ≫
      B.map (𝟙 (a.obj K) ×ₘ transposedUnitBaseChange adjg adjg' eg ef o' o'' u) = 𝟙 _ := by
    rw [← B.map_comp, prod_comp, Category.id_comp, IsIso.inv_hom_id, ← CategoryTheory.prod_id,
      B.map_id]
  have key : Rf.map (unitProjection adjg' B' B αg' o'' ρ'' (a.obj K)) =
      Rf.map (B.map (𝟙 (a.obj K) ×ₘ inv (transposedUnitBaseChange adjg adjg' eg ef o' o'' u))) ≫
        inv (adjunctionTensorMap adjf A B αf (a.obj K) (Rg.obj o')) ≫
        unitProjection adjg A' A αg o' ρ' (Rf.obj (a.obj K)) ≫
        Rg.map (map adjf adjf' eg ef (a.obj K)) ≫
        (pushforwardSquare adjf adjf' adjg adjg' eg ef).app (Lg'.obj (a.obj K)) := by
    rw [hIB, IsIso.inv_hom_id_assoc, CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp_assoc, hτ, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hbc : map adjf adjf' eg ef (a.obj K) ≫
      (inv (twoSquare adjf adjf' eg ef).natTrans).app (a.obj K) = 𝟙 _ := by
    rw [NatIso.isIso_inv_app]
    exact IsIso.hom_inv_id ((twoSquare adjf adjf' eg ef).natTrans.app _)
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  calc _ = Rf.map (unitProjection adjg' B' B αg' o'' ρ'' (a.obj K)) ≫
        (Rg' ⋙ Rf).map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K) ≫
        (composedPushforwardSquare adjf adjf' adjg adjg' eg ef).natTrans.app ((Lg ⋙ a').obj K) ≫
        Rg.map (adja'.counit.app (Lg.obj K)) := by
        simp only [Functor.map_comp, Category.assoc, Functor.comp_map]
        rw [rightAdjointSquare] at *
        rw [hξ]
        rfl
    _ = Rf.map (unitProjection adjg' B' B αg' o'' ρ'' (a.obj K)) ≫
        (composedPushforwardSquare adjf adjf' adjg adjg' eg ef).natTrans.app ((a ⋙ Lg').obj K) ≫
        Rg.map ((inv (twoSquare adjf adjf' eg ef).natTrans).app (a.obj K) ≫
          Lg.map (adja.counit.app K)) := by
        rw [← Category.assoc ((Rg' ⋙ Rf).map _), hσ, Category.assoc, Functor.comp_map Rf' Rg,
          ← Rg.map_comp, hβ]
    _ = _ := by
        rw [key]
        simp only [Category.assoc, Functor.comp_obj]
        rw [reassoc_of% hψσ, Functor.map_comp, ← Rg.map_comp_assoc, hbc, Rg.map_id,
          Category.id_comp, ← hΦ, Functor.map_comp, Functor.map_comp, Category.assoc,
          Category.assoc, ← Functor.comp_map a Rf, adja.counit.naturality, Functor.id_map,
          reassoc_of% hC]

omit [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans] in
/-- **The pushed-forward base change map of right adjoints is invertible** as soon as `Φ'` at
`a K`, `Φ` at `K`, the two-variable comparison of `a` at `(K, J)` and `τ` are. -/
theorem isIso_map_rightAdjointBaseChange (K : S)
    [IsIso (twoSquare adjf adjf' eg ef).natTrans]
    [IsIso (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans]
    [IsIso (adjunctionTensorMap adjf A B αf (a.obj K) (Rg.obj o'))]
    [IsIso (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)]
    [IsIso (unitProjection adjg' B' B αg' o'' ρ'' (a.obj K))]
    [IsIso (unitProjection adjg A' A αg o' ρ' K)]
    [IsIso (rightAdjointTensorComparison adjf adja A B αf K (Rg.obj o'))]
    (hsq : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' (Rf.obj (a.obj K))
      (Rg.obj o'))
    (hunit : ∀ X : S', αf'.app (X, o') ≫ B'.map (𝟙 (Lf'.obj X) ×ₘ u) ≫ ρ''.app (Lf'.obj X) =
      Lf'.map (ρ'.app X)) :
    IsIso (Rg'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K)) := by
  have h := unitProjection_comp_map_rightAdjointBaseChange_comp adjf adjf' adjg adjg' eg ef adja
    adja' A A' B B' αf αf' αg αg' o' ρ' o'' ρ'' u K hsq hunit
  have : IsIso (B.map (𝟙 (a.obj K) ×ₘ inv (transposedUnitBaseChange adjg adjg' eg ef o' o'' u))) :=
    have : IsIso (𝟙 (a.obj K) ×ₘ inv (transposedUnitBaseChange adjg adjg' eg ef o' o'' u)) :=
      (isIso_prod_iff (C := T) (D := T)).2 ⟨inferInstance, inferInstance⟩
    inferInstance
  have h1 : IsIso (unitProjection adjg' B' B αg' o'' ρ'' (a.obj K) ≫
      Rg'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K) ≫
        (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans.app (Lg.obj K)) := by
    rw [h]; infer_instance
  have h2 : IsIso (Rg'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').app K) ≫
      (rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans.app (Lg.obj K)) :=
    IsIso.of_isIso_comp_left (unitProjection adjg' B' B αg' o'' ρ'' (a.obj K)) _
  exact IsIso.of_isIso_comp_right _
    ((rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja').natTrans.app (Lg.obj K))

end Tensor

end Stacks.CategoryTheory.BaseChange

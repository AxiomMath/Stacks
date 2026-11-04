module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LevelCoinvariantsLimit

/-!
# Kőnig's lemma for the levels, with a family of endomorphisms

`Stacks.EtaleCohomology.exists_iso_padicQuotientTower_of_levels` makes level isomorphisms between
a tower `S` and the quotient tower of a finite `ℤ_ℓ`-module `M` compatible, when they intertwine
one endomorphism. This file does the same for a family of endomorphisms `σ i` of `S` and `ψ i` of
`M`: the sets of level isomorphisms intertwining all of them are finite, nonempty by hypothesis,
and stable under reduction. It also records that the identification
`ℚ_ℓ ⊗ lim S ≅ (ℚ_ℓ^r)_H` of
`Stacks.EtaleCohomology.exists_extendScalars_limit_linearEquiv_coinvariants` carries the limit of
any endomorphism of `S` lying over an endomorphism of `(ℤ_ℓ^r)_H` to its rationalization.

## Main results

* `Stacks.EtaleCohomology.exists_iso_padicQuotientTower_of_levels_family`: a tower whose levels
  are isomorphic to those of the quotient tower of `M` compatibly with a family of endomorphisms
  is isomorphic to that quotient tower compatibly with the family.
* `Stacks.EtaleCohomology.exists_extendScalars_limit_linearEquiv_coinvariants_natural`: the
  identification `ℚ_ℓ ⊗ lim S ≅ (ℚ_ℓ^r)_H` carries the limit of an endomorphism of `S` lying over
  an endomorphism of `(ℤ_ℓ^r)_H` to its rationalization.
-/

@[expose] public noncomputable section

open Representation Matrix CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ) {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : Γ →* GL (Fin r) ℤ_[ℓ])

section Koenig

universe v

variable {M : ModuleCat.{v} ℤ_[ℓ]}

variable (M) in
/-- The isomorphisms of a level of `S` with a level of the quotient tower intertwining a family
of endomorphisms. -/
abbrev levelIsoSetFamily {ι : Type*} (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (σ : ι → (S ⟶ S))
    (ψ : ι → (M ⟶ M)) (n : ℕ) : Type v :=
  {e : S.obj (Opposite.op n) ≃ₗ[ℤ_[ℓ]] (padicQuotientTower M).obj (Opposite.op n) //
    ∀ i x, e (((σ i).app (Opposite.op n)).hom x) =
      ((padicQuotientTowerMap (ψ i)).app (Opposite.op n)).hom (e x)}

/-- The levels of a tower `S` admitting an isomorphism with the quotient tower of a finite
`ℤ_ℓ`-module intertwining a family of endomorphisms have finitely many such isomorphisms. -/
theorem finite_levelIsoSetFamily [Module.Finite ℤ_[ℓ] M] {ι : Type*}
    (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (σ : ι → (S ⟶ S)) (ψ : ι → (M ⟶ M)) (n : ℕ)
    (h : Nonempty (levelIsoSetFamily M S σ ψ n)) : Finite (levelIsoSetFamily M S σ ψ n) := by
  have := finite_padicQuotientTower_obj (M := M) n
  obtain ⟨e₀⟩ := h
  have : Finite (S.obj (Opposite.op n)) := Finite.of_equiv _ e₀.1.symm.toEquiv
  exact Finite.of_injective (fun e : levelIsoSetFamily M S σ ψ n => ⇑e.1)
    fun a b h => Subtype.ext (LinearEquiv.coe_injective h)

/-- A linear equivalence preserves the submodule `I • ⊤`. -/
private theorem linearEquiv_mem_smul_top_iff {R N P : Type*} [CommRing R] [AddCommGroup N]
    [AddCommGroup P] [Module R N] [Module R P] (I : Ideal R) (e : N ≃ₗ[R] P) (x : N) :
    e x ∈ I • (⊤ : Submodule R P) ↔ x ∈ I • (⊤ : Submodule R N) :=
  ⟨fun h => by simpa using Submodule.smul_top_le_comap_smul_top I e.symm.toLinearMap h,
    fun h => Submodule.smul_top_le_comap_smul_top I e.toLinearMap h⟩

/-- The transition of the quotient tower is its map along `n ≤ n + 1`. -/
private theorem padicQuotientTower_map_homOfLE (n : ℕ) :
    (padicQuotientTower M).map (homOfLE (Nat.le_add_right n 1)).op =
      padicQuotientTransition M n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- Naturality of a map of towers, on elements, for the transition `n + 1 → n`. -/
private theorem map_app_apply_homOfLE {S T : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]} (η : S ⟶ T) (n : ℕ)
    (x : S.obj (Opposite.op (n + 1))) :
    (T.map (homOfLE (Nat.le_add_right n 1)).op).hom ((η.app (Opposite.op (n + 1))).hom x) =
      (η.app (Opposite.op n)).hom ((S.map (homOfLE (Nat.le_add_right n 1)).op).hom x) :=
  congrArg (fun t => t.hom x) (η.naturality (homOfLE (Nat.le_add_right n 1)).op).symm

open Pointwise in
/-- An isomorphism of level `n + 1` of a tower `S`, whose transition to level `n` is surjective
with kernel `ℓ^{n+1}`, with the quotient tower of `M` reduces to an isomorphism of level `n`. -/
theorem exists_linearEquiv_padicQuotientTower_reduction (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (n : ℕ)
    (hsurj : Function.Surjective (S.map (homOfLE (Nat.le_add_right n 1)).op).hom)
    (hker : LinearMap.ker (S.map (homOfLE (Nat.le_add_right n 1)).op).hom =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (S.obj (Opposite.op (n + 1)))))
    (e : S.obj (Opposite.op (n + 1)) ≃ₗ[ℤ_[ℓ]] (padicQuotientTower M).obj (Opposite.op (n + 1))) :
    ∃ e' : S.obj (Opposite.op n) ≃ₗ[ℤ_[ℓ]] (padicQuotientTower M).obj (Opposite.op n),
      ∀ x, e' ((S.map (homOfLE (Nat.le_add_right n 1)).op).hom x) =
        (padicQuotientTransition M n).hom (e x) := by
  let tS := (S.map (homOfLE (Nat.le_add_right n 1)).op).hom
  let tQ := (padicQuotientTransition M n).hom
  have hkerQ : ∀ y : (padicQuotientTower M).obj (Opposite.op (n + 1)),
      tQ y = 0 ↔ y ∈ padicIdeal ℓ ^ (n + 1) •
        (⊤ : Submodule ℤ_[ℓ] ((padicQuotientTower M).obj (Opposite.op (n + 1)))) :=
    SetLike.ext_iff.1 (ker_padicQuotientTransition (M := M) n)
  have hsurjQ : Function.Surjective tQ := fun x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  let g : S.obj (Opposite.op (n + 1)) →ₗ[ℤ_[ℓ]] (padicQuotientTower M).obj (Opposite.op n) :=
    tQ ∘ₗ e.toLinearMap
  have hker' : LinearMap.ker tS ≤ LinearMap.ker g := by
    intro x hx
    rw [hker] at hx
    rw [LinearMap.mem_ker]
    exact (hkerQ _).2 ((linearEquiv_mem_smul_top_iff _ e _).2 hx)
  let q := (LinearMap.quotKerEquivOfSurjective tS hsurj).symm.toLinearMap
  let g' := (LinearMap.ker tS).liftQ g hker' ∘ₗ q
  have hg' : ∀ x, g' (tS x) = tQ (e x) := fun x => by
    change (LinearMap.ker tS).liftQ g hker'
      ((LinearMap.quotKerEquivOfSurjective tS hsurj).symm (tS x)) = _
    have : (LinearMap.quotKerEquivOfSurjective tS hsurj).symm (tS x) =
        Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  have hbij : Function.Bijective g' := by
    refine ⟨?_, fun z => ?_⟩
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      rw [LinearMap.mem_ker, hg'] at hy
      have hx' := (linearEquiv_mem_smul_top_iff _ e _).1 ((hkerQ _).1 hy)
      rw [← hker] at hx'
      exact (Submodule.mem_bot _).2 (LinearMap.mem_ker.1 hx')
    · obtain ⟨w, rfl⟩ := hsurjQ z
      obtain ⟨x, rfl⟩ := e.surjective w
      exact ⟨tS x, hg' x⟩
  exact ⟨LinearEquiv.ofBijective g' hbij, hg'⟩

open Pointwise in
/-- Reduction of a level isomorphism intertwining a family of endomorphisms: it reduces to a level
isomorphism one level down which still intertwines the family. -/
theorem exists_levelIsoSetFamily_reduction {ι : Type*} (ψ : ι → (M ⟶ M))
    (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (σ : ι → (S ⟶ S)) (n : ℕ)
    (hsurj : Function.Surjective (S.map (homOfLE (Nat.le_add_right n 1)).op).hom)
    (hker : LinearMap.ker (S.map (homOfLE (Nat.le_add_right n 1)).op).hom =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (S.obj (Opposite.op (n + 1)))))
    (e : levelIsoSetFamily M S σ ψ (n + 1)) :
    ∃ e' : levelIsoSetFamily M S σ ψ n,
      ∀ x, e'.1 ((S.map (homOfLE (Nat.le_add_right n 1)).op).hom x) =
        (padicQuotientTransition M n).hom (e.1 x) := by
  obtain ⟨e', he'⟩ := exists_linearEquiv_padicQuotientTower_reduction S n hsurj hker e.1
  refine ⟨⟨e', fun i y => ?_⟩, he'⟩
  obtain ⟨x, rfl⟩ := hsurj y
  have hψ := map_app_apply_homOfLE (padicQuotientTowerMap (ψ i)) n
  rw [padicQuotientTower_map_homOfLE] at hψ
  rw [← map_app_apply_homOfLE (σ i), he', he', e.2]
  exact hψ _

open Pointwise in
/-- **Kőnig's lemma for the levels, with a family of endomorphisms**: a tower `S` whose
transitions are surjective with kernel `ℓ^{n+1}`, with endomorphisms `σ i`, all of whose levels are
isomorphic to those of the quotient tower of a finite `ℤ_ℓ`-module `M` compatibly with every `σ i`
and `ψ i`, is isomorphic to that quotient tower compatibly with every `σ i` and `ψ i`. -/
theorem exists_iso_padicQuotientTower_of_levels_family [Module.Finite ℤ_[ℓ] M] {ι : Type*}
    (ψ : ι → (M ⟶ M)) (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (σ : ι → (S ⟶ S))
    (hsurj : ∀ n, Function.Surjective (S.map (homOfLE (Nat.le_add_right n 1)).op).hom)
    (hker : ∀ n, LinearMap.ker (S.map (homOfLE (Nat.le_add_right n 1)).op).hom =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (S.obj (Opposite.op (n + 1)))))
    (hlev : ∀ n, Nonempty (levelIsoSetFamily M S σ ψ n)) :
    ∃ E : S ≅ padicQuotientTower M, ∀ i, σ i ≫ E.hom = E.hom ≫ padicQuotientTowerMap (ψ i) := by
  classical
  let tS := fun n => (S.map (homOfLE (Nat.le_add_right n 1)).op).hom
  let tQ := fun n => (padicQuotientTransition M n).hom
  choose res hres using fun n => exists_levelIsoSetFamily_reduction ψ S σ n (hsurj n) (hker n)
  let F : ℕᵒᵖ ⥤ Type v := Functor.ofOpSequence (C := Type v)
    (X := fun n => levelIsoSetFamily M S σ ψ n) (fun n => TypeCat.ofHom (res n))
  have : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j =>
    finite_levelIsoSetFamily S σ ψ j.unop (hlev j.unop)
  have : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => hlev j.unop
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  have hcompat : ∀ n x, (sec (Opposite.op n)).1 (tS n x) =
      tQ n ((sec (Opposite.op (n + 1))).1 x) := fun n x => by
    have hF : F.map (homOfLE (Nat.le_add_right n 1)).op = TypeCat.ofHom (res n) :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [← hsec (homOfLE (Nat.le_add_right n 1)).op, hF]
    exact hres n _ x
  let Ehom : S ⟶ padicQuotientTower M := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom (sec (Opposite.op n)).1.toLinearMap) fun n => by
      ext x
      rw [padicQuotientTower_map_homOfLE]
      exact hcompat n x
  have : ∀ n, IsIso (Ehom.app n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (sec n).1.bijective
  have : IsIso Ehom := NatIso.isIso_of_isIso_app _
  refine ⟨asIso Ehom, fun i => ?_⟩
  ext n x
  exact (sec n).2 i x

end Koenig

section AssemblyNatural

universe w

open scoped ChangeOfRings

variable [H.Normal] (φ : Γ) (τ : Γ →* GL (Fin r) ℚ_[ℓ]) (P : GL (Fin r) ℚ_[ℓ])
  (hP : ∀ g, rationalGL ρ g = P⁻¹ * τ g * P) (c : ℤ_[ℓ])

include hP in
/-- **Assembly, naturally**: the identification `ℚ_ℓ ⊗ lim S ≅ (ℚ_ℓ^r)_H` of
`Stacks.EtaleCohomology.exists_extendScalars_limit_linearEquiv_coinvariants` also carries the limit
of every endomorphism `σ'` of `S` lying over an endomorphism `ψ'` of `(ℤ_ℓ^r)_H` to the
endomorphism of `(ℚ_ℓ^r)_H` which `ψ'` rationalizes to. -/
theorem exists_extendScalars_limit_linearEquiv_coinvariants_natural (S : ℕᵒᵖ ⥤ ModuleCat.{w} ℤ_[ℓ])
    (E : S ≅ padicQuotientTower (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]))
    (σ : S ⟶ S)
    (hσ : σ ≫ E.hom = E.hom ≫ padicQuotientTowerMap (integralCoinvariantsModuleEnd H ρ φ c)) :
    ∃ e : (ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj (limit S) ≃ₗ[ℚ_[ℓ]]
        Coinvariants ((matrixRepresentation τ).comp H.subtype),
      (∀ x, e (((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (limMap σ)).hom x) =
        algebraMap ℤ_[ℓ] ℚ_[ℓ] c • coinvariantsFrobenius H τ φ (e x)) ∧
      ∀ (σ' : S ⟶ S) (ψ' : (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) ⟶
          integralCoinvariantsModule H ρ)
        (Ψ' : Coinvariants ((matrixRepresentation τ).comp H.subtype) →ₗ[ℚ_[ℓ]]
          Coinvariants ((matrixRepresentation τ).comp H.subtype)),
        σ' ≫ E.hom = E.hom ≫ padicQuotientTowerMap ψ' →
        (∀ x : integralCoinvariants H ρ, rationalCoinvariantsConjEquiv H τ P hP
            (integralCoinvariantsRationalization H ρ (ψ'.hom (ULift.up x)).down) =
          Ψ' (rationalCoinvariantsConjEquiv H τ P hP (integralCoinvariantsRationalization H ρ x))) →
        ∀ x, e (((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (limMap σ')).hom x) = Ψ' (e x) := by
  have : IsAdicComplete (padicIdeal ℓ) (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) :=
    isAdicComplete_integralCoinvariantsModule H ρ
  let M : ModuleCat.{w} ℤ_[ℓ] := integralCoinvariantsModule H ρ
  let I := limitIsoOfIsoPadicQuotientTower M S E
  let f := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  let X := (ModuleCat.restrictScalars f).obj (ModuleCat.of ℚ_[ℓ] ℚ_[ℓ])
  have : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₂ : ((ModuleCat.extendScalars f).obj M : Type w) ≃ₗ[ℚ_[ℓ]]
      TensorProduct ℤ_[ℓ] ℚ_[ℓ] (integralCoinvariants H ρ) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ_[ℓ] ℚ_[ℓ]) ULift.moduleEquiv
  let e₃ := (isBaseChange_integralCoinvariantsRationalization H ρ).equiv
  let e₄ := rationalCoinvariantsConjEquiv H τ P hP
  let e := ((ModuleCat.extendScalars f).mapIso I).toLinearEquiv ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄
  have he : ∀ m : ((limit S : ModuleCat.{w} ℤ_[ℓ]) : Type w), e ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] m) =
      e₄ (integralCoinvariantsRationalization H ρ (ULift.down (I.hom.hom m))) := fun m => by
    change e₄ (e₃ (e₂ ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] I.hom.hom m))) = _
    congr 1
    change e₃ ((1 : ℚ_[ℓ]) ⊗ₜ ULift.down (I.hom.hom m)) = _
    rw [IsBaseChange.equiv_tmul, one_smul]
  refine ⟨e, (and_iff_right_of_imp fun hnat => ?_).2 ?_⟩
  · refine hnat σ (integralCoinvariantsModuleEnd H ρ φ c) (f c • coinvariantsFrobenius H τ φ) hσ
      fun x => ?_
    rw [LinearMap.smul_apply, integralCoinvariantsModuleEnd_apply, map_smul,
      integralCoinvariantsRationalization_coinvariantsFrobenius, ← algebraMap_smul ℚ_[ℓ] c,
      map_smul, rationalCoinvariantsConjEquiv_coinvariantsFrobenius]
  · intro σ' ψ' Ψ' hσ' hΨ' x
    have hI' : ∀ m : ((limit S : ModuleCat.{w} ℤ_[ℓ]) : Type w), I.hom.hom ((limMap σ').hom m) =
        ψ'.hom (I.hom.hom m) := fun m =>
      congrArg (fun t => t.hom m) (limMap_comp_limitIsoOfIsoPadicQuotientTower_hom M S E σ' _ hσ')
    let α' : (ModuleCat.extendScalars f).obj (limit S) ⟶
        ModuleCat.of ℚ_[ℓ] (ULift.{w} (Coinvariants ((matrixRepresentation τ).comp H.subtype))) :=
      (ModuleCat.extendScalars f).map (limMap σ') ≫
        ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ e.toLinearMap)
    let β' : (ModuleCat.extendScalars f).obj (limit S) ⟶
        ModuleCat.of ℚ_[ℓ] (ULift.{w} (Coinvariants ((matrixRepresentation τ).comp H.subtype))) :=
      ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ Ψ' ∘ₗ e.toLinearMap)
    have hαβ' : α' = β' := by
      refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
      change ULift.up (e (((ModuleCat.extendScalars f).map (limMap σ')).hom
          ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] m))) =
        ULift.up (Ψ' (e ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] m)))
      congr 1
      refine (he ((limMap σ').hom m)).trans ?_
      rw [he m, hI']
      exact hΨ' (I.hom.hom m).down
    exact congrArg (fun t => ULift.down (t.hom x)) hαβ'

end AssemblyNatural

end Stacks.EtaleCohomology

end

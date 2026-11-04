module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem

/-!
# The coherent adic system of a decreasing sequence of ideal sheaves

Let `X` be a scheme, `𝓘` a quasi-coherent ideal sheaf and `(Jₙ)` a decreasing sequence of
quasi-coherent ideal sheaves with `𝓘 ^ (n + 1) ⊆ Jₙ` and `Jₙ = 𝓘 ^ (n + 1) + J_{n+1}`. Then the
structure sheaves of the closed subschemes they cut out form an inverse system
`n ↦ 𝒪_X / Jₙ` which is a coherent adic system along `𝓘`, in the sense of
`Stacks.Coherent.IsCoherentAdicSystem`, as soon as `X` is locally Noetherian. This is the
algebraic shadow of a formal closed subscheme of the formal completion of `X` along `𝓘`.

## Main definitions

* `Stacks.Algebraization.idealQuotientMap` — the map `𝒪_X / J ⟶ 𝒪_X / J'` for `J ≤ J'`.
* `Stacks.Algebraization.idealQuotientSystem` — the inverse system `n ↦ 𝒪_X / Jₙ`, its
  transition maps being the induced maps of quotients.

## Main results

* `Stacks.Algebraization.isCoherentAdicSystem_idealQuotientSystem` — it is a coherent adic
  system along `𝓘`.

## Implementation notes

`𝒪_X / J` is written `idealPowerQuotient J 1 𝒪_X`, the ideal-power quotient at exponent one, so
that the descent and annihilation lemmas for ideal-power quotients, such as
`Stacks.Algebraization.idealPowerQuotientDesc`, apply to it. The comparison
`(𝒪_X / J_{n+1}) / 𝓘 ^ (n + 1) ≅ 𝒪_X / Jₙ` is built, as
`Stacks.Algebraization.idealPowerQuotientSupIso` is, from two epimorphisms out of `𝒪_X` each
factoring through the other (`Stacks.Algebraization.isoOfEpiFac`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- The map `𝒪_X / J ⟶ 𝒪_X / J'` induced by an inclusion `J ≤ J'` of ideal sheaves. -/
public def idealQuotientMap {J J' : X.IdealSheafData} (h : J ≤ J') :
    idealPowerQuotient J 1 (SheafOfModules.unit X.ringCatSheaf) ⟶
      idealPowerQuotient J' 1 (SheafOfModules.unit X.ringCatSheaf) :=
  idealPowerQuotientMap J J' 1 1 (by rw [pow_one, pow_one]; exact h) (𝟙 _)

/-- The induced map of quotients commutes with the projections from `𝒪_X`. -/
@[reassoc]
public theorem idealQuotientMap_π {J J' : X.IdealSheafData} (h : J ≤ J') :
    cokernel.π (C := X.Modules)
        (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)).ι ≫ idealQuotientMap h =
      cokernel.π (C := X.Modules)
        (idealPowerMultiple J' 1 (SheafOfModules.unit X.ringCatSheaf)).ι :=
  (idealPowerQuotientMap_π J J' 1 1 _ (𝟙 _)).trans (Category.id_comp _)

/-- The projection `𝒪_X ⟶ 𝒪_X / J` is an epimorphism. -/
public instance epi_idealQuotientπ (J : X.IdealSheafData) :
    Epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)).ι) :=
  epi_cokernel_π_submodule_ι (X := X) (M := SheafOfModules.unit X.ringCatSheaf) _

/-- The induced map of quotients for `J ≤ J` is the identity. -/
public theorem idealQuotientMap_refl (J : X.IdealSheafData) :
    idealQuotientMap (le_refl J) = 𝟙 _ := by
  refine (cancel_epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)).ι)).1
    ((idealQuotientMap_π _).trans (Category.comp_id _).symm)

/-- The induced maps of quotients compose. -/
public theorem idealQuotientMap_trans {J J' J'' : X.IdealSheafData} (h : J ≤ J') (h' : J' ≤ J'') :
    idealQuotientMap (h.trans h') = idealQuotientMap h ≫ idealQuotientMap h' := by
  refine (cancel_epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple J 1 (SheafOfModules.unit X.ringCatSheaf)).ι)).1
    ((idealQuotientMap_π _).trans ((idealQuotientMap_π h').symm.trans
      ((congrArg (· ≫ idealQuotientMap h') (idealQuotientMap_π h).symm).trans
        (Category.assoc _ _ _))))

/-- The inverse system `n ↦ 𝒪_X / Jₙ` attached to a decreasing sequence of ideal sheaves, with the
induced maps of quotients as transition maps. -/
public def idealQuotientSystem (J : ℕ → X.IdealSheafData) (hJ : Antitone J) :
    ℕᵒᵖ ⥤ X.Modules where
  obj n := idealPowerQuotient (J n.unop) 1 (SheafOfModules.unit X.ringCatSheaf)
  map {m n} h := idealQuotientMap (J := J m.unop) (J' := J n.unop) (hJ (leOfHom h.unop))
  map_id n := idealQuotientMap_refl (J n.unop)
  map_comp {_ _ _} g h := idealQuotientMap_trans (hJ (leOfHom g.unop)) (hJ (leOfHom h.unop))

/-- The transition maps of `idealQuotientSystem` commute with the projections from `𝒪_X`. -/
@[reassoc]
public theorem idealQuotientSystem_map_π (J : ℕ → X.IdealSheafData) (hJ : Antitone J)
    {m n : ℕᵒᵖ} (h : m ⟶ n) :
    cokernel.π (C := X.Modules)
        (idealPowerMultiple (J m.unop) 1 (SheafOfModules.unit X.ringCatSheaf)).ι ≫
      (idealQuotientSystem J hJ).map h =
    cokernel.π (C := X.Modules)
        (idealPowerMultiple (J n.unop) 1 (SheafOfModules.unit X.ringCatSheaf)).ι :=
  idealQuotientMap_π (hJ (leOfHom h.unop))

/-- **The structure sheaves of a decreasing sequence of closed subschemes form a coherent adic
system.** If `𝓘 ^ (n + 1) ⊆ Jₙ` and `Jₙ = 𝓘 ^ (n + 1) ⊔ J_{n+1}` for every `n`, then on a locally
Noetherian scheme `n ↦ 𝒪_X / Jₙ` is a coherent adic system along `𝓘`. -/
public theorem isCoherentAdicSystem_idealQuotientSystem [IsLocallyNoetherian X]
    [(SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent]
    [(SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent]
    (𝓘 : X.IdealSheafData) (J : ℕ → X.IdealSheafData) (hJ : Antitone J)
    (hle : ∀ n, 𝓘 ^ (n + 1) ≤ J n) (hsup : ∀ n, J n = 𝓘 ^ (n + 1) ⊔ J (n + 1)) :
    Stacks.Coherent.IsCoherentAdicSystem 𝓘 (idealQuotientSystem J hJ) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hann (n : ℕ) : idealPowerMultiple 𝓘 (n + 1) (idealPowerQuotient (J n) 1 O) = ⊥ :=
    idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le (by rw [pow_one]; exact hle n) O
  refine ⟨fun n => isCoherent_idealPowerQuotient (J n) 1 O, hann, fun n => ?_⟩
  let F := idealQuotientSystem J hJ
  let tr := F.map (homOfLE (Nat.le_succ n)).op
  let d : idealPowerQuotient 𝓘 (n + 1) (idealPowerQuotient (J (n + 1)) 1 O) ⟶
      idealPowerQuotient (J n) 1 O := idealPowerQuotientDesc 𝓘 (n + 1) tr (hann n)
  have hann' : idealPowerMultiple (J n) 1
      (idealPowerQuotient 𝓘 (n + 1) (idealPowerQuotient (J (n + 1)) 1 O)) = ⊥ := by
    have h := idealPowerMultiple_sup_eq_bot
      (idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_outer 𝓘 (J (n + 1)) (n + 1) 1 O)
      (idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_inner 𝓘 (J (n + 1)) (n + 1) 1 O)
    rwa [pow_one, ← hsup n] at h
  let d' : idealPowerQuotient (J n) 1 O ⟶
      idealPowerQuotient 𝓘 (n + 1) (idealPowerQuotient (J (n + 1)) 1 O) :=
    idealPowerQuotientDesc (J n) 1
      (doubleIdealPowerQuotientProjection 𝓘 (J (n + 1)) (n + 1) 1 O) hann'
  have hd : doubleIdealPowerQuotientProjection 𝓘 (J (n + 1)) (n + 1) 1 O ≫ d =
      cokernel.π (C := X.Modules) (idealPowerMultiple (J n) 1 O).ι :=
    (Category.assoc _ _ _).trans ((congrArg (cokernel.π (C := X.Modules)
      (idealPowerMultiple (J (n + 1)) 1 O).ι ≫ ·) (idealPowerQuotientDesc_π 𝓘 (n + 1) tr
        (hann n))).trans (idealQuotientSystem_map_π J hJ (homOfLE (Nat.le_succ n)).op))
  have hd' : cokernel.π (C := X.Modules) (idealPowerMultiple (J n) 1 O).ι ≫ d' =
      doubleIdealPowerQuotientProjection 𝓘 (J (n + 1)) (n + 1) 1 O :=
    idealPowerQuotientDesc_π _ _ _ _
  refine ⟨isoOfEpiFac (epi_doubleIdealPowerQuotientProjection 𝓘 (J (n + 1)) (n + 1) 1 O)
    (epi_cokernel_π_submodule_ι _) d d' hd hd', ?_⟩
  exact idealPowerQuotientDesc_π 𝓘 (n + 1) tr (hann n)

end Stacks.Algebraization

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.UnitSheafRestrictScalarsExt
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompactSupportFiniteness
public import StacksFrontier.Algebra.Homology.DerivedCategory.TraceMapPairingCriterion

/-!
# Sheaves of `ℤ/ℓ`-modules over a separably closed field are detected by `ℤ/ℓ`

Let `k` be a separably closed field and `ℓ` a prime. Global sections identify sheaves of
`ℤ/ℓ`-modules on `(Spec k)_ét` with `ℤ/ℓ`-vector spaces
(`Stacks.EtaleCohomology.isEquivalence_etaleModuleGlobalSections_of_isSepClosed`), so every such
sheaf is projective and injective, and for every sheaf `M` the map
`Hom(M, Λ) → Hom_ℤ(Hom(Λ, M), End(Λ))`, `ψ ↦ (x ↦ ψ ∘ x)`, is bijective, `Λ = ℤ/ℓ`
(`Stacks.EtaleCohomology.bijective_homCompPairing_unitSheaf_of_isSepClosed`): it is
`Hom_{ℤ/ℓ}(V, ℤ/ℓ) = Hom_ℤ(V, ℤ/ℓ)` for `V = Γ(M)`.

Consequently morphisms `K ⟶ Λ[c]` of `D((Spec k)_ét, Λ)` are detected by the classes
`Λ ⟶ K[-c]` (`Stacks.RelativeDuality.bijective_shiftedHom_comp_of_projective_of_injective`), the
form in which a fibre of a smooth projective curve enters relative Poincaré duality, in the proof
of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.projective_etaleModule_of_isSepClosed`.
* `Stacks.EtaleCohomology.injective_etaleModule_of_isSepClosed`.
* `Stacks.EtaleCohomology.bijective_homCompPairing_unitSheaf_of_isSepClosed`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

open ExtensionTorsor

variable (k : Type u) [Field k] [IsSepClosed k] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Every sheaf of `ℤ/ℓ`-modules on `(Spec k)_ét` is projective**, `k` separably closed. -/
theorem projective_etaleModule_of_isSepClosed
    (M : EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) : Projective M := by
  have := isEquivalence_etaleModuleGlobalSections_of_isSepClosed (ZMod ℓ) k
  let e := (etaleModuleGlobalSections.{u, 0} (ZMod ℓ) (Spec (.of k))).asEquivalence
  exact (e.map_projective_iff M).1
    (ModuleCat.projective_of_free (Module.Basis.ofVectorSpace (ZMod ℓ) (e.functor.obj M)))

/-- **Every sheaf of `ℤ/ℓ`-modules on `(Spec k)_ét` is injective**, `k` separably closed. -/
theorem injective_etaleModule_of_isSepClosed
    (M : EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) : Injective M := by
  have := isEquivalence_etaleModuleGlobalSections_of_isSepClosed (ZMod ℓ) k
  let e := (etaleModuleGlobalSections.{u, 0} (ZMod ℓ) (Spec (.of k))).asEquivalence
  let : Module.Injective (ZMod ℓ) (e.functor.obj M) :=
    Module.injective_of_isSemisimpleRing (ZMod ℓ) _
  have : Injective (e.functor.obj M) :=
    Module.injective_object_of_injective_module (ZMod ℓ) (e.functor.obj M)
  exact Injective.of_iso (e.unitIso.app M).symm
    (Injective.injective_of_adjoint e.toAdjunction (e.functor.obj M))

variable {k ℓ}

/-- Maps out of `Λ` are global sections, additively. -/
theorem homUnitSheafEquiv_add {Y : Scheme.{u}} (M : EtaleModules.{u, 0} (ZMod ℓ) Y)
    (x₁ x₂ : unitSheaf (X := Y) ℓ ⟶ M) :
    homUnitSheafEquiv ℓ M (x₁ + x₂) = homUnitSheafEquiv ℓ M x₁ + homUnitSheafEquiv ℓ M x₂ := by
  simp only [homUnitSheafEquiv, Equiv.trans_apply, Adjunction.homEquiv_unit, Functor.map_add,
    Preadditive.comp_add, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_add]

/-- Maps out of `Λ` are global sections, naturally in the target. -/
theorem homUnitSheafEquiv_comp {Y : Scheme.{u}} {M M' : EtaleModules.{u, 0} (ZMod ℓ) Y}
    (x : unitSheaf (X := Y) ℓ ⟶ M) (ψ : M ⟶ M') :
    homUnitSheafEquiv ℓ M' (x ≫ ψ) =
      ψ.hom.app (op (etaleSiteTerminal Y)) (homUnitSheafEquiv ℓ M x) := by
  rw [homUnitSheafEquiv_eq_app, homUnitSheafEquiv_eq_app ℓ M]
  rfl

variable (k ℓ)

/-- **`Hom(M, Λ) = Hom_ℤ(Hom(Λ, M), End(Λ))` over a separably closed field**: for every sheaf `M`
of `ℤ/ℓ`-modules on `(Spec k)_ét`, `ψ ↦ (x ↦ ψ ∘ x)` is bijective, `Λ = ℤ/ℓ`. -/
theorem bijective_homCompPairing_unitSheaf_of_isSepClosed
    (M : EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) :
    Function.Bijective (Stacks.RelativeDuality.homCompPairing (unitSheaf (X := Spec (.of k)) ℓ)
      (unitSheaf (X := Spec (.of k)) ℓ) M) := by
  have := isEquivalence_etaleModuleGlobalSections_of_isSepClosed (ZMod ℓ) k
  let T := etaleSiteTerminal (Spec (.of k))
  let ev :=
    (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj (op T)
  have hev : ev.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful
      (etaleModuleGlobalSections.{u, 0} (ZMod ℓ) (Spec (.of k)))).ofIso
      (Sheaf.ΓNatIsoSheafSections _ _ (etaleSiteTerminalIsTerminal (Spec (.of k))))
  let hM := homUnitSheafEquiv ℓ M
  let hΛ := homUnitSheafEquiv ℓ (unitSheaf (X := Spec (.of k)) ℓ)
  constructor
  · intro ψ₁ ψ₂ hψ
    apply hev.map_injective
    ext s
    have h := DFunLike.congr_fun hψ (hM.symm s)
    change hM.symm s ≫ ψ₁ = hM.symm s ≫ ψ₂ at h
    have h' := congrArg hΛ h
    rwa [homUnitSheafEquiv_comp, homUnitSheafEquiv_comp, Equiv.apply_symm_apply] at h'
  · intro φ
    let g : M.obj.obj (op T) →+ (unitSheaf (X := Spec (.of k)) ℓ).obj.obj (op T) :=
      AddMonoidHom.mk' (fun s => hΛ (φ (hM.symm s))) (fun s₁ s₂ => by
        have : hM.symm (s₁ + s₂) = hM.symm s₁ + hM.symm s₂ := by
          apply hM.injective
          rw [Equiv.apply_symm_apply, homUnitSheafEquiv_add, Equiv.apply_symm_apply,
            Equiv.apply_symm_apply]
        rw [this, map_add, homUnitSheafEquiv_add])
    refine ⟨hev.preimage (ModuleCat.ofHom (g.toZModLinearMap ℓ)), AddMonoidHom.ext fun x => ?_⟩
    apply hΛ.injective
    show hΛ (x ≫ hev.preimage _) = hΛ (φ x)
    rw [homUnitSheafEquiv_comp]
    refine (congrArg (fun f => f (hM x))
      (hev.map_preimage (ModuleCat.ofHom (g.toZModLinearMap ℓ)))).trans ?_
    simp [g, hM]

end Stacks.EtaleCohomology

end

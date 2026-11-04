module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveDualityPlusBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.ProperCurveFibreDuality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.SepClosedPointUnitDetection
public import StacksFrontier.Homology.DerivedCategory.HomFromSingleProjectiveDetection

/-!
# The duality map of a smooth proper curve over an algebraically closed field is invertible

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `f : X ⟶ Spec k` a
smooth proper curve. For every invertible multiplication `w : E ⊗^L E ⟶ E` of `E = f⁻¹Λ[0]` and
every top-degree trace `t : Rf_* E ⟶ Λ[-2]`, the duality map
`D_{w,t} : Rf_* E ⟶ RHom(Rf_* E, Λ[-2])` (`Stacks.EtaleCohomology.curveDualityMap`) is an
isomorphism (`Stacks.EtaleCohomology.isIso_curveDualityMap_fibre`).

The proof: changing `w` by an automorphism of `E` changes the trace by one, so `w` may be taken to
be the canonical multiplication `Stacks.EtaleCohomology.curveDualityMultiplication`. Relative
duality over `Spec k` (`Stacks.EtaleCohomology.isBijectiveAt_properCurveFibre`, on `D⁺`, for every
top-degree trace) passes to the unbounded derived category
(`Stacks.EtaleCohomology.isBijectiveAt_of_forall_isBijectiveAt_plus`), and gives that composition
with `D_{w,t}` is bijective on morphisms out of every shift of `Λ`
(`Stacks.EtaleCohomology.bijective_comp_curveDualityMap_of_isBijectiveAt`). Over a separably
closed field `Λ` is a projective generator of the sheaves of `Λ`-modules
(`Stacks.EtaleCohomology.exists_ne_zero_hom_unitSheaf_of_isSepClosed`), so its shifts detect
isomorphisms in `D((Spec k)_étale, Λ)`
(`Stacks.EtaleCohomology.isIso_of_bijective_comp_unitSheaf_shift_of_isSepClosed`).

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor Stacks.RelativeDuality

section Multiplication

variable (ℓ : ℕ) {S X : Scheme.{u}} (f : X ⟶ S)

/-- **Changing the multiplication by an endomorphism of `E` changes the trace**:
`D_{w ≫ a, t} = D_{w, Rf_*(a) ≫ t}`. -/
theorem curveDualityMap_comp
    (w : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f)
    (a : curveDualityUnit ℓ f ⟶ curveDualityUnit ℓ f)
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := S) ℓ)) (-2)) :
    curveDualityMap ℓ f (w ≫ a) t =
      curveDualityMap ℓ f w
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).map a ≫ t) := by
  simp only [curveDualityMap, Functor.map_comp, Category.assoc]

end Multiplication

section SepClosed

variable (k : Type u) [Field k] [IsSepClosed k] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`Λ` is a generator over a separably closed field**: every nonzero sheaf of `ℤ/ℓ`-modules on
`(Spec k)_ét` receives a nonzero morphism from `Λ`. -/
theorem exists_ne_zero_hom_unitSheaf_of_isSepClosed
    (F : EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k))) (hF : ¬ IsZero F) :
    ∃ ψ : unitSheaf (X := Spec (.of k)) ℓ ⟶ F, ψ ≠ 0 := by
  have := isEquivalence_etaleModuleGlobalSections_of_isSepClosed (ZMod ℓ) k
  let T := etaleSiteTerminal (Spec (.of k))
  let ev :=
    (sheafSections (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj (op T)
  have hev : ev.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful
      (etaleModuleGlobalSections.{u, 0} (ZMod ℓ) (Spec (.of k)))).ofIso
      (Sheaf.ΓNatIsoSheafSections _ _ (etaleSiteTerminalIsTerminal (Spec (.of k))))
  have := hev.full
  have := hev.faithful
  by_contra hψ
  push Not at hψ
  let hM := homUnitSheafEquiv ℓ F
  apply hF
  refine IsZero.of_full_of_faithful_of_isZero ev F ?_
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun s₁ s₂ => ?_⟩
  exact hM.symm.injective ((hψ _).trans (hψ _).symm)

/-- **The shifts of `Λ` detect isomorphisms in `D((Spec k)_étale, Λ)`**, `k` separably closed: if
`z ↦ z ∘ φ` is bijective on morphisms out of `Λ[0][m]` for every `m`, then `φ` is an
isomorphism. -/
theorem isIso_of_bijective_comp_unitSheaf_shift_of_isSepClosed
    {K K' : DerivedCategory (EtaleModules.{u, 0} (ZMod ℓ) (Spec (.of k)))} (φ : K ⟶ K')
    (h : ∀ m : ℤ, Function.Bijective (fun z : ((DerivedCategory.singleFunctor _ 0).obj
      (unitSheaf (X := Spec (.of k)) ℓ))⟦m⟧ ⟶ K => z ≫ φ)) :
    IsIso φ := by
  have := projective_etaleModule_of_isSepClosed k ℓ (unitSheaf (X := Spec (.of k)) ℓ)
  refine DerivedCategory.isIso_of_bijective_comp_singleFunctor_projective
    (unitSheaf (X := Spec (.of k)) ℓ) (exists_ne_zero_hom_unitSheaf_of_isSepClosed k ℓ) φ
    (fun j => ?_)
  let e : ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ))⟦-j⟧ ≅
      (DerivedCategory.singleFunctor _ j).obj (unitSheaf (X := Spec (.of k)) ℓ) :=
    ((DerivedCategory.singleFunctors _).shiftIso (-j) j 0 (by omega)).app _
  have hfac : (fun a : (DerivedCategory.singleFunctor _ j).obj
      (unitSheaf (X := Spec (.of k)) ℓ) ⟶ K => a ≫ φ) =
      e.homCongr (Iso.refl K') ∘ (fun z : ((DerivedCategory.singleFunctor _ 0).obj
        (unitSheaf (X := Spec (.of k)) ℓ))⟦-j⟧ ⟶ K => z ≫ φ) ∘
        (e.homCongr (Iso.refl K)).symm := by
    funext a
    simp
  rw [hfac]
  exact (e.homCongr (Iso.refl K')).bijective.comp
    ((h (-j)).comp (e.homCongr (Iso.refl K)).symm.bijective)

end SepClosed

section Fibre

variable {k : Type u} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]

/-- **The duality map of a smooth proper curve over an algebraically closed field is an
isomorphism**: for `ℓ` invertible in `k`, every invertible multiplication `w : E ⊗^L E ⟶ E` of
`E = f⁻¹Λ[0]` and every top-degree trace `t : Rf_* E ⟶ Λ[-2]`, the duality map
`D_{w,t} : Rf_* E ⟶ RHom(Rf_* E, Λ[-2])` is invertible. -/
theorem isIso_curveDualityMap_fibre (hℓ : IsUnit (ℓ : k))
    (w : ((etaleDerivedTensor.{u, 0} (ZMod ℓ) X).obj (curveDualityUnit ℓ f)).obj
      (curveDualityUnit ℓ f) ⟶ curveDualityUnit ℓ f) [IsIso w]
    (t : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) (-2))
    (ht : IsIso ((DerivedCategory.homologyFunctor _ 2).map t)) :
    IsIso (curveDualityMap ℓ f w t) := by
  let a : curveDualityUnit ℓ f ⟶ curveDualityUnit ℓ f :=
    inv (curveDualityMultiplication ℓ f) ≫ w
  have hw : w = curveDualityMultiplication ℓ f ≫ a := by simp [a]
  rw [hw, curveDualityMap_comp]
  let τ : ShiftedHom (curveDualityComplex ℓ f)
      ((DerivedCategory.singleFunctor _ 0).obj (unitSheaf (X := Spec (.of k)) ℓ)) (-2) :=
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).map a ≫ t
  have hτ : IsIso ((DerivedCategory.homologyFunctor _ 2).map τ) := by
    simp only [τ, CategoryTheory.Functor.map_comp]
    infer_instance
  have hB := isBijectiveAt_of_forall_isBijectiveAt_plus ℓ f
    (fun τ' hτ' => isBijectiveAt_properCurveFibre f hℓ τ' hτ') τ hτ
  exact isIso_of_bijective_comp_unitSheaf_shift_of_isSepClosed k ℓ _
    (fun m => bijective_comp_curveDualityMap_of_isBijectiveAt ℓ f τ hB m)

end Fibre

end Stacks.EtaleCohomology

end

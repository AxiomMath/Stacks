module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Local

/-!
# A coherent module with free stalks of rank one is invertible

On a locally Noetherian scheme, a coherent module whose stalk at `x` is free of rank one over
`𝒪_{X, x}` is isomorphic to the structure sheaf on a neighbourhood of `x` ([Stacks, Tag 0B8J],
`Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free`); if this holds at every point,
the module is invertible.

## Main results

* `AlgebraicGeometry.Scheme.Modules.exists_restrict_iso_unit_of_stalk_linearEquiv`
* `AlgebraicGeometry.Scheme.Modules.isInvertibleModule_of_forall_stalk_linearEquiv`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **A coherent module whose stalk at `x` is free of rank one is trivial near `x`.** The stalk
identification `𝒪_{X, x}`-linear `M_x ≅ 𝒪_{X, x}` is transported to the spelling of the stalk
ring computed in `RingCat` (`SemilinearStalk.commStalkRingEquiv`), and [Stacks, Tag 0B8J]
spreads it to an isomorphism `M|_W ≅ 𝒪_W` on an open neighbourhood. -/
theorem exists_restrict_iso_unit_of_stalk_linearEquiv {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M) (x : X)
    (e : letI : Module (X.presheaf.stalk x) (ToType (M.presheaf.stalk x)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) M.val x
      ToType (M.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x) :
    ∃ W : X.Opens, x ∈ W ∧
      Nonempty (M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  classical
  let A := ToType (X.presheaf.stalk x)
  let B := ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
    (X.sheaf.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}) x)
  let N := ToType (M.presheaf.stalk x)
  let : Module A N :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) M.val x
  let : Module B N :=
    PresheafOfModules.instModuleCarrierStalkRingCatCarrierAbPresheafOpensCarrier M.val x
  let e : N ≃ₗ[A] A := e
  let eBA : B ≃+* A := SemilinearStalk.commStalkRingEquiv X.sheaf.obj x
  have hsmul (t : B) (n : N) : eBA t • n = t • n :=
    SemilinearStalk.comm_smul_eq X.sheaf.obj x M.val t n
  let eB : N ≃ₗ[B] B :=
    { toFun := fun n => eBA.symm (e n)
      invFun := fun t => e.symm (eBA t)
      left_inv := fun n => by simp
      right_inv := fun t => by simp
      map_add' := fun n n' => by simp
      map_smul' := fun t n => by
        rw [← hsmul, e.map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
        rfl }
  have hstalk : Nonempty (N ≃ₗ[B] (ULift.{u} (Fin 1) →₀ B)) :=
    ⟨eB.trans (Finsupp.uniqueLinearEquiv B (α := ULift.{u} (Fin 1)) B default).symm⟩
  obtain ⟨W, hxW, ⟨eW⟩⟩ :=
    Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free M
      (isFinitePresentation_of_isCoherent M) x 1 hstalk
  exact ⟨W, hxW, ⟨Stacks.Modules.restrictIsoFree W M (ULift.{u} (Fin 1)) eW.symm ≪≫
    Limits.coproductUniqueIso (fun _ : ULift.{u} (Fin 1) => SheafOfModules.unit _)⟩⟩

/-- **A coherent module all of whose stalks are free of rank one is invertible.** -/
theorem isInvertibleModule_of_forall_stalk_linearEquiv {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent.{u} M)
    (e : ∀ x : X,
      letI : Module (X.presheaf.stalk x) (ToType (M.presheaf.stalk x)) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) M.val x
      Nonempty (ToType (M.presheaf.stalk x) ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x)) :
    Stacks.Ample.IsInvertibleModule X M :=
  Stacks.AlgebraicGeometry.TwistMapsInvertible.isInvertibleModule_of_forall_exists_restrict_isoUnit
    M fun x => exists_restrict_iso_unit_of_stalk_linearEquiv M hM x (e x).some

end AlgebraicGeometry.Scheme.Modules

end

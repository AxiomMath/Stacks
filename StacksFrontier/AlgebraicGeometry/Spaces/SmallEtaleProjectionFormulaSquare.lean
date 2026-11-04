module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensorClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackCompAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleProjectionFormulaIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Braiding

/-!
# The projection formula around a commutative square of algebraic spaces

Let `p : T ⟶ X`, `q : T ⟶ P`, `π : P ⟶ S'` and `t : X ⟶ S'` be quasi-compact and quasi-separated
morphisms of algebraic spaces with `q ≫ π = p ≫ t`. For `K ∈ D_QCoh(𝒪_X)`, `E ∈ D_QCoh(𝒪_T)` and
`W ∈ D_QCoh(𝒪_P)`, two applications of Stacks 08IN give

`Rπ_*(Rq_*(Lp^*K ⊗^𝐋 E) ⊗^𝐋 W) ≅ Rt_*(Rp_*(E ⊗^𝐋 Lq^*W) ⊗^𝐋 K)`.

This is the computation in the proof of Stacks 0CTT, for `T = X ×_A ℙⁿ_A`.

## Main results

* `AlgebraicGeometry.Space.nonempty_derivedModulePushforward_projectionFormula_square_iso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T X P S' : AlgebraicSpaces B S hS}

/-- **The projection formula around a commutative square** (two applications of Stacks 08IN). -/
theorem nonempty_derivedModulePushforward_projectionFormula_square_iso
    (p : T ⟶ X) (q : T ⟶ P) (π : P ⟶ S') (t : X ⟶ S') (w : q ≫ π = p ≫ t)
    (hpqc : IsQuasiCompact B S hS p.hom) (hpqs : IsQuasiSeparated B S hS p.hom)
    (hqqc : IsQuasiCompact B S hS q.hom) (hqqs : IsQuasiSeparated B S hS q.hom)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (hK : QcohDerived B S hS X K)
    (E : DerivedCategory (Modules.{u, u} B S hS T.1 T.2)) (hE : QcohDerived B S hS T E)
    (W : DerivedCategory (Modules.{u, u} B S hS P.1 P.2)) (hW : QcohDerived B S hS P W) :
    Nonempty ((derivedModulePushforward B S hS π).obj
        (((smallEtaleDerivedTensor B S hS P).obj
          ((derivedModulePushforward B S hS q).obj
            (((smallEtaleDerivedTensor B S hS T).obj
              ((smallEtaleDerivedModulePullback B S hS p).obj K)).obj E))).obj W) ≅
      (derivedModulePushforward B S hS t).obj
        (((smallEtaleDerivedTensor B S hS X).obj
          ((derivedModulePushforward B S hS p).obj
            (((smallEtaleDerivedTensor B S hS T).obj E).obj
              ((smallEtaleDerivedModulePullback B S hS q).obj W)))).obj K)) := by
  have hLK := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ p K hK
  have hLW := derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ q W hW
  have hN₀ := qcohDerived_smallEtaleDerivedTensor T _ _ hLK hE
  have hE' := qcohDerived_smallEtaleDerivedTensor T _ _ hE hLW
  have h₁ := isIso_smallEtaleProjectionFormulaMap B S hS q hqqc hqqs
    (((smallEtaleDerivedTensor B S hS T).obj
      ((smallEtaleDerivedModulePullback B S hS p).obj K)).obj E) hN₀ W hW
  have h₂ := isIso_smallEtaleProjectionFormulaMap B S hS p hpqc hpqs
    (((smallEtaleDerivedTensor B S hS T).obj E).obj
      ((smallEtaleDerivedModulePullback B S hS q).obj W)) hE' K hK
  exact ⟨(derivedModulePushforward B S hS π).mapIso
      (@asIso _ _ _ _ _ h₁) ≪≫
    (smallEtaleDerivedPushforwardCompIsoToposHom B S hS q π).app _ ≪≫
    eqToIso (congrArg (fun f => (derivedModulePushforward B S hS f).obj
      (((smallEtaleDerivedTensor B S hS T).obj
        (((smallEtaleDerivedTensor B S hS T).obj
          ((smallEtaleDerivedModulePullback B S hS p).obj K)).obj E)).obj
        ((smallEtaleDerivedModulePullback B S hS q).obj W))) w) ≪≫
    ((smallEtaleDerivedPushforwardCompIsoToposHom B S hS p t).app _).symm ≪≫
    (derivedModulePushforward B S hS t).mapIso
      ((derivedModulePushforward B S hS p).mapIso
        (smallEtaleDerivedTensorAssociator T _ _ _ ≪≫
          (smallEtaleDerivedTensorProduct B S hS T).braiding _ _) ≪≫
        (@asIso _ _ _ _ _ h₂).symm)⟩

end AlgebraicGeometry.Space

end

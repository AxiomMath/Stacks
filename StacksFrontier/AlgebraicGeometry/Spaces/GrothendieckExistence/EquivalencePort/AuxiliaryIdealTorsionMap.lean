module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CompletionQuotientCommute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentCompletionExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact

namespace AlgebraicGeometry.Space.C1573.TorsionAlgebraization
end AlgebraicGeometry.Space.C1573.TorsionAlgebraization

/-!
# The map `(G_e)_e ⟶ (𝓗 / 𝓚^(e+1) 𝓗)_e` of the proof of Stacks 08BC

Given `α : (F_n) ⟶ 𝓗^∧` and algebraizations `G_e` of `(F_n / 𝓚^(e+1) F_n)_n`, the reductions
of `α` modulo `𝓚^(e+1)` algebraize to maps `γ_e : G_e ⟶ 𝓗 / 𝓚^(e+1) 𝓗`
(`AlgebraicGeometry.Space.C1573.TorsionAlgebraization.γ`), forming a morphism of coherent `𝓚`-adic
systems (`AlgebraicGeometry.Space.C1573.TorsionAlgebraization.γSystem`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA} {I : Ideal A}
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  [IsNoetherianRing A] [IsAdicComplete I A] {f : X ⟶ schemeSpace (baseObject A B hA)}
  {hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom}
  {K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule}
  {hK : K.toSheafOfModules.IsQuasicoherentOnSite}
  {E : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)}

namespace C1573.TorsionAlgebraization

variable (d : TorsionAlgebraization X I f hf K hK E)
  (H : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
  (α : E ⟶ (baseCompletion X I).obj H)

/-- `𝓗 / 𝓚^(e+1) 𝓗`, as a coherent module. -/
def quotientH (e : ℕ) : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  ⟨smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1) H.obj,
    isCoherent_idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 K hK _ H.property (e + 1)⟩

/-- The reduction of `α` modulo `𝓚^(e+1)`, as a map into the completion of `𝓗 / 𝓚^(e+1) 𝓗`. -/
def αQuotient (e : ℕ) :
    quotientAdicSystem X I K hK E (e + 1) ⟶ (baseCompletion X I).obj (quotientH H (hK := hK) e) :=
  ObjectProperty.homMk (Functor.whiskerRight α.hom
      (smallEtaleAdicQuotientFunctor B (Spec (.of A)) hA X.1 X.2 K (e + 1)) ≫
    (completionQuotientIso B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) K (e + 1)
      H.obj).inv)

/-- **The map `γ_e : G_e ⟶ 𝓗 / 𝓚^(e+1) 𝓗`.** -/
def γ (e : ℕ) : d.G e ⟶ quotientH H (hK := hK) e :=
  ((bijective_baseCompletion_map X I f hf (d.proper e)).2
    ((d.ρ e).hom ≫ αQuotient (hK := hK) H α e)).choose

/-- The completion of `γ_e` is `ρ_e` followed by the reduction of `α` modulo `𝓚^(e+1)`. -/
theorem baseCompletion_map_γ (e : ℕ) :
    (baseCompletion X I).map (d.γ H α e) = (d.ρ e).hom ≫ αQuotient (hK := hK) H α e :=
  ((bijective_baseCompletion_map X I f hf (d.proper e)).2
    ((d.ρ e).hom ≫ αQuotient (hK := hK) H α e)).choose_spec

/-- The transition `𝓗 / 𝓚^(e+2) ⟶ 𝓗 / 𝓚^(e+1)`, as a map of coherent modules. -/
def quotientHTransition (e : ℕ) : quotientH H (hK := hK) (e + 1) ⟶ quotientH H (hK := hK) e :=
  ObjectProperty.homMk
    (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1) H.obj)

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- The `n`-th component of the reduction of `α` modulo `𝓚^(e+1)` is the reduction of `α_n`
followed by the isomorphism exchanging the two quotients. -/
theorem αQuotient_app (e n : ℕ) :
    (αQuotient (hK := hK) (E := E) H α e).hom.app (op n) =
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1) (α.hom.app (op n)) ≫
        adicQuotientCommHom B (Spec (.of A)) hA X.1 X.2 K (baseIdealSubmodule X.1 X.2 I) (n + 1)
          (e + 1) H.obj :=
  rfl

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A] in
/-- Reduction of a morphism `φ : M ⟶ N` modulo powers of `𝓚` commutes with the transition maps
`M / 𝓚^(e+2) M ⟶ M / 𝓚^(e+1) M`. -/
theorem transition_mapOfHom (e : ℕ) {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (φ : M ⟶ N) :
    smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1) φ ≫
        smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K e N =
      smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K e M ≫
        smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K e φ :=
  smallEtaleAdicQuotientTransition_naturality B (Spec (.of A)) hA X.1 X.2 K e φ

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] [IsNoetherianRing A]
  [IsAdicComplete I A] in
/-- The reduction modulo `𝓚^(e+2)` of a map into `N / I^(n+1) N`, composed with the exchange of
quotients, is compatible with the transitions from `𝓚^(e+2)` to `𝓚^(e+1)`. -/
theorem commHom_transition_mapOfHom (e n : ℕ) {M N : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (φ : M ⟶ smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
      (n + 1) N) :
    (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1 + 1) φ ≫
        adicQuotientCommHom B (Spec (.of A)) hA X.1 X.2 K (baseIdealSubmodule X.1 X.2 I) (n + 1)
          (e + 1 + 1) N) ≫
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1) N) =
    smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1) M ≫
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1) φ ≫
        adicQuotientCommHom B (Spec (.of A)) hA X.1 X.2 K (baseIdealSubmodule X.1 X.2 I) (n + 1)
          (e + 1) N := by
  have h1 := adicQuotientCommHom_naturality B (Spec (.of A)) hA X.1 X.2 K
    (baseIdealSubmodule X.1 X.2 I) (n + 1) (e + 1) N
  have h2 := smallEtaleAdicQuotientTransition_naturality B (Spec (.of A)) hA X.1 X.2 K (e + 1) φ
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1 + 1) φ ≫ ·)
    h1).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ adicQuotientCommHom B (Spec (.of A)) hA X.1 X.2 K
    (baseIdealSubmodule X.1 X.2 I) (n + 1) (e + 1) N) h2).trans ?_
  exact Category.assoc _ _ _

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- The `n`-th component of the completion of `g : M ⟶ N` is the reduction of `g` modulo
`I^(n+1)`. -/
theorem baseCompletion_map_app {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (g : M ⟶ N) (n : ℕ) :
    ((baseCompletion X I).map g).hom.app (op n) =
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) g.hom :=
  (smallEtaleAdicQuotientMapOfHom_eq B (Spec (.of A)) hA X.1 X.2 _ (n + 1) g.hom).symm

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- The reductions of `α` modulo `𝓚^(e+2)` and `𝓚^(e+1)` commute with the transition maps. -/
theorem αQuotient_transition (e : ℕ) :
    αQuotient (hK := hK) H α (e + 1) ≫
        (baseCompletion X I).map (quotientHTransition H (hK := hK) e) =
      quotientAdicSystemTransition X I K hK E (e + 1) ≫ αQuotient (hK := hK) H α e := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun n => ?_))
  obtain ⟨n⟩ := n
  show (αQuotient (hK := hK) (E := E) H α (e + 1)).hom.app (op n) ≫
      ((baseCompletion X I).map (quotientHTransition H (hK := hK) e)).hom.app (op n) =
    (quotientAdicSystemTransition X I K hK E (e + 1)).hom.app (op n) ≫
      (αQuotient (hK := hK) (E := E) H α e).hom.app (op n)
  rw [baseCompletion_map_app, αQuotient_app, αQuotient_app]
  exact commHom_transition_mapOfHom (I := I) (K := K) e n (α.hom.app (op n))

/-- The maps `γ_e` commute with the transitions `G_(e+1) ⟶ G_e` and
`𝓗 / 𝓚^(e+2) 𝓗 ⟶ 𝓗 / 𝓚^(e+1) 𝓗`. -/
theorem γ_transition (e : ℕ) :
    d.γ H α (e + 1) ≫ quotientHTransition H (hK := hK) e = d.τ e ≫ d.γ H α e := by
  refine (bijective_baseCompletion_map X I f hf (d.proper (e + 1))).1 ?_
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, baseCompletion_map_γ,
    baseCompletion_map_γ, baseCompletion_map_τ, Category.assoc, αQuotient_transition]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **The morphism `(G_e)_e ⟶ 𝓗^∧` of coherent `𝓚`-adic systems.** -/
def γSystem : d.adicSystem ⟶ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).obj H :=
  ObjectProperty.homMk (NatTrans.ofOpSequence (fun e => (d.γ H α e).hom) fun e => by
    refine (congrArg (· ≫ (d.γ H α e).hom) (Functor.ofOpSequence_map_homOfLE_succ
      (X := fun e => (d.G e).obj) (fun e => (d.τ e).hom) e)).trans ?_
    refine Eq.trans ?_ (congrArg ((d.γ H α (e + 1)).hom ≫ ·)
      (adicQuotientSystem_map_succ B (Spec (.of A)) hA X.1 X.2 K H.obj e).symm)
    exact (congrArg (fun k => k.hom) (d.γ_transition H α e)).symm)

/-- The `e`-th component of `γSystem` is `γ_e`. -/
theorem γSystem_app (e : ℕ) : (d.γSystem H α).hom.app (op e) = (d.γ H α e).hom := rfl

/-- The reduction of `γ_e` modulo `I^(n+1)` is `ρ_(e,n)` followed by the reduction of `α_n`
modulo `𝓚^(e+1)` and the exchange of the two quotients. -/
theorem mapOfHom_γ (e n : ℕ) :
    smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) (d.γ H α e).hom =
      (d.ρApp e n).hom ≫ (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
        (α.hom.app (op n)) ≫
        (adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 K (baseIdealSubmodule X.1 X.2 I) (n + 1)
          (e + 1) H.obj).hom) := by
  rw [← baseCompletion_map_app]
  exact congrArg (fun k => k.hom.app (op n)) (d.baseCompletion_map_γ H α e)

variable {H α} in
/-- **The kernels and cokernels of the `γ_e` are annihilated by `𝓚^(2t)`** when those of the
`α_n` are annihilated by `𝓚^t`. -/
theorem isSystemKernelCokernelAnnihilatedByPower_γSystem
    (hH : HasProperSupportOverBase X f hf H)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom) :
    IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K (d.γSystem H α).hom := by
  obtain ⟨t, ht, hall⟩ := hα
  have hKcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _ hK
  have hcart : ∀ (M : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I)) n, IsCartesianOnAffineCharts (M.obj.obj (op n)) :=
    fun M n => isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _
      (M.property.1 n).toIsQuasicoherentOnSite
  have hk : ∀ n, IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K t (kernel (α.hom.app (op n))) :=
    fun n => (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 K t _).1 (hall n).1
  have hc : ∀ n, IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K t (cokernel (α.hom.app (op n))) :=
    fun n => (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 K t _).1 (hall n).2
  have hHe : ∀ e, HasProperSupportOverBase X f hf (quotientH (hK := hK) H e) := fun e =>
    hasProperSupport_idealPowerQuotient B (Spec (.of A)) hA X.2 _ f.hom hf K (e + 1) _
      H.property hH
  have hw : ∀ e n, smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) (d.γ H α e).hom ≫
        (adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 K (baseIdealSubmodule X.1 X.2 I) (n + 1)
          (e + 1) H.obj).symm.hom =
      (d.ρApp e n).hom ≫ smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
        (α.hom.app (op n)) := fun e n =>
    (congrArg (· ≫ _) (d.mapOfHom_γ H α e n)).trans ((Category.assoc _ _ _).trans
      (congrArg ((d.ρApp e n).hom ≫ ·) ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 K
          (baseIdealSubmodule X.1 X.2 I) (n + 1) (e + 1) H.obj).hom_inv_id).trans
          (Category.comp_id _)))))
  refine ⟨2 * t, by omega, fun e => ⟨?_, ?_⟩⟩
  · rw [idealPowerMultiple_eq_bot_iff]
    refine isPowAnnihilated_kernel_of_reductions X I f hf K hK (d.proper e) (d.γ H α e) (2 * t)
      fun n => ?_
    refine isPowAnnihilated_of_iso B (Spec (.of A)) hA X.1 X.2 K
      (kernel.mapIso _ _ (d.ρApp e n) _ (hw e n)).symm (2 * t) ?_
    exact isPowAnnihilated_kernel_mapOfHom B (Spec (.of A)) hA X.1 X.2 K K t (e + 1)
      (α.hom.app (op n)) hKcart (hcart E n) (hcart _ n) (hk n) (hc n)
  · rw [idealPowerMultiple_eq_bot_iff]
    refine isPowAnnihilated_cokernel_of_reductions X I f hf K hK (hHe e) (d.γ H α e) (2 * t)
      fun n => ?_
    refine isPowAnnihilated_of_iso B (Spec (.of A)) hA X.1 X.2 K
      (cokernel.mapIso _ _ (d.ρApp e n) _ (hw e n)).symm (2 * t) ?_
    exact isPowAnnihilated_of_le B (Spec (.of A)) hA X.1 X.2 K (by omega) _
      (isPowAnnihilated_cokernel_mapOfHom B (Spec (.of A)) hA X.1 X.2 K K t (e + 1)
        (α.hom.app (op n)) (hc n))

end C1573.TorsionAlgebraization




end AlgebraicGeometry.Space

end

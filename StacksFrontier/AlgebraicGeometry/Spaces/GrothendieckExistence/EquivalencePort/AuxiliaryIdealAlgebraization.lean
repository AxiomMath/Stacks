module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.AuxiliaryIdealTorsionMap

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573
namespace AlgebraicGeometry.Space.C1573.TorsionAlgebraization
end AlgebraicGeometry.Space.C1573.TorsionAlgebraization

/-!
# Algebraizing along the auxiliary ideal in the proof of Stacks 08BC

Let `(F_n)` be a coherent `I 𝒪_X`-adic system with proper support, `α : (F_n) ⟶ 𝓗^∧` a map whose
kernels and cokernels are killed by a power of `𝓚`, and `G_e` algebraizations of
`(F_n / 𝓚^(e+1) F_n)_n`.  Stacks 08BB along `𝓚` applied to `(G_e)_e ⟶ 𝓗^∧` gives a coherent
`𝓕`, a map `a : 𝓕 ⟶ 𝓗` and `β : (G_e)_e ≅ 𝓕^∧`.  Reducing modulo `𝓘^(n+1)` gives, for every
`n`, a second algebraization of the reduction of `α_n` modulo the powers of `𝓚`, so the
uniqueness half of Stacks 08BB identifies `𝓕 / 𝓘^(n+1) 𝓕` with `F_n`.
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

section Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- Reduction modulo `𝓘^k` sends a composite `φ ≫ ψ` to the composite of the reductions. -/
@[reassoc]
theorem C1573.smallEtaleAdicQuotientMapOfHom_comp (k : ℕ) {M N P : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N) (ψ : N ⟶ P) :
    smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 k (φ ≫ ψ) =
      smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 k φ ≫
        smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 k ψ :=
  (smallEtaleAdicQuotientFunctor B S hS F hF 𝓘 k).map_comp φ ψ

/-- The level-`n` component of the completion of `g : M ⟶ N` is the reduction
`M / 𝓘^(n+1) M ⟶ N / 𝓘^(n+1) N` of `g`. -/
theorem C1573.completionFunctor_map_hom_app
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) {M N : CoherentModules.{u, u} B S hS F hF}
    (g : M ⟶ N) (n : ℕ) :
    ((completionFunctor B S hS F hF 𝓘 hI).map g).hom.app (op n) =
      smallEtaleAdicQuotientMapOfHom B S hS F hF 𝓘 (n + 1) g.hom :=
  (smallEtaleAdicQuotientMapOfHom_eq B S hS F hF 𝓘 (n + 1) g.hom).symm

attribute [reassoc] smallEtaleAdicQuotientMapOfHom_compat

/-- `𝓘^t` annihilation is invariant under isomorphism of modules. -/
private theorem isPowAnnihilated_iff_of_iso {M N : Modules.{u, u} B S hS F hF} (e : M ≅ N)
    (t : ℕ) :
    IsPowAnnihilated B S hS F hF 𝓘 t M ↔ IsPowAnnihilated B S hS F hF 𝓘 t N :=
  ⟨isPowAnnihilated_of_iso B S hS F hF 𝓘 e t, isPowAnnihilated_of_iso B S hS F hF 𝓘 e.symm t⟩

end Generic

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}
  {X : AlgebraicSpaces B (Spec (.of A)) hA} {I : Ideal A}
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  {K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule}

section Reduction

variable (I) in
/-- `M / 𝓘^(n+1) M`, as a coherent module. -/
def C1573.baseReduction (n : ℕ) (M : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2) :
    CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  ⟨smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1) M.obj,
    isCoherent_idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 _
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I) _ M.property (n + 1)⟩

variable (I) in
/-- The reduction `M / 𝓘^(n+1) M ⟶ N / 𝓘^(n+1) N` of a map of coherent modules. -/
def C1573.baseReductionMap (n : ℕ) {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
    (a : M ⟶ N) : baseReduction I n M ⟶ baseReduction I n N :=
  ObjectProperty.homMk
    (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
      (n + 1) a.hom)

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
/-- `𝓚^t` annihilates the kernel of `a` taken among coherent modules if and only if it
annihilates the kernel of the underlying map of modules. -/
theorem C1573.idealPowerMultiple_kernel_eq_bot_iff
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2} (a : M ⟶ N) (t : ℕ) :
    idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K t (kernel a).obj = ⊥ ↔
      IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K t (kernel a.hom) := by
  rw [idealPowerMultiple_eq_bot_iff]
  exact isPowAnnihilated_iff_of_iso B (Spec (.of A)) hA X.1 X.2 K
    (PreservesKernel.iso (ObjectProperty.ι (isCoherent.{u, u} B (Spec (.of A)) hA X.1 X.2)) a) t

omit [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))] in
/-- `𝓚^t` annihilates the cokernel of `a` taken among coherent modules if and only if it
annihilates the cokernel of the underlying map of modules. -/
theorem C1573.idealPowerMultiple_cokernel_eq_bot_iff
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2} (a : M ⟶ N) (t : ℕ) :
    idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K t (cokernel a).obj = ⊥ ↔
      IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K t (cokernel a.hom) := by
  rw [idealPowerMultiple_eq_bot_iff]
  exact isPowAnnihilated_iff_of_iso B (Spec (.of A)) hA X.1 X.2 K
    (PreservesCokernel.iso (ObjectProperty.ι (isCoherent.{u, u} B (Spec (.of A)) hA X.1 X.2)) a) t

/-- **Reducing modulo `𝓘^(n+1)` keeps the kernel and cokernel of a map killed by a power of
`𝓚`**: by `K^(2t)` for the kernel and `K^t` for the cokernel when `K^t` kills both before. -/
theorem C1573.isMapKernelCokernelAnnihilatedByPower_baseReductionMap (n : ℕ)
    {M N : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2} (a : M ⟶ N)
    (ha : IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K a) :
    IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K
      (baseReductionMap I n a) := by
  obtain ⟨t, ht, hk, hc⟩ := ha
  rw [idealPowerMultiple_kernel_eq_bot_iff] at hk
  rw [idealPowerMultiple_cokernel_eq_bot_iff] at hc
  have cart : ∀ P : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2,
      IsCartesianOnAffineCharts P.obj := fun P =>
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _
      P.property.toIsQuasicoherentOnSite
  refine ⟨2 * t, by omega, ?_, ?_⟩
  · rw [idealPowerMultiple_kernel_eq_bot_iff]
    exact isPowAnnihilated_kernel_mapOfHom B (Spec (.of A)) hA X.1 X.2 K
      (baseIdealSubmodule X.1 X.2 I) t (n + 1) a.hom
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B (Spec (.of A)) hA X.1 X.2 _
        (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I))
      (cart M) (cart N) hk hc
  · rw [idealPowerMultiple_cokernel_eq_bot_iff]
    exact isPowAnnihilated_of_le B (Spec (.of A)) hA X.1 X.2 K (by omega) _
      (isPowAnnihilated_cokernel_mapOfHom B (Spec (.of A)) hA X.1 X.2 K
        (baseIdealSubmodule X.1 X.2 I) t (n + 1) a.hom hc)

end Reduction

section Algebraization

variable [IsNoetherianRing A] [IsAdicComplete I A] {f : X ⟶ schemeSpace (baseObject A B hA)}
  {hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom}
  {hK : K.toSheafOfModules.IsQuasicoherentOnSite}
  {E : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)}

namespace C1573.TorsionAlgebraization

variable (d : TorsionAlgebraization X I f hf K hK E)

/-- The term `F_n`, as a coherent module. -/
def level (E : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I))
    (n : ℕ) : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  ⟨E.obj.obj (op n), E.property.1 n⟩

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- The isomorphisms `G_e / 𝓘^(n+1) G_e ≅ F_n / 𝓚^(e+1) F_n` of `ρApp` are compatible with the
transition maps in `n`. -/
theorem ρApp_naturality (e n : ℕ) :
    (d.ρApp e (n + 1)).inv ≫
        smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
          (n + 1) (d.G e).obj =
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (E.obj.map (homOfLE (Nat.le_add_right n 1)).op) ≫ (d.ρApp e n).inv := by
  have h := (d.ρ e).hom.hom.naturality (homOfLE (Nat.le_add_right n 1)).op
  have h' : smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) (d.G e).obj ≫ (d.ρApp e n).hom =
      (d.ρApp e (n + 1)).hom ≫ smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (E.obj.map (homOfLE (Nat.le_add_right n 1)).op) :=
    (congrArg (· ≫ (d.ρApp e n).hom) (adicQuotientSystem_map_succ B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (d.G e).obj n)).symm.trans h
  rw [Iso.inv_comp_eq, ← Category.assoc, ← h', Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {H : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2}
  {α : E ⟶ (baseCompletion X I).obj H}
  {F' : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2} {a : F' ⟶ H}
  {β : d.adicSystem ≅ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).obj F'}

variable (β) in
/-- The level-`e` component `G_e ≅ 𝓕 / 𝓚^(e+1) 𝓕` of `β`. -/
def βApp (e : ℕ) :
    (d.G e).obj ≅ smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1) F'.obj :=
  ((ObjectProperty.ι _).mapIso β).app (op e)

/-- The components `G_e ≅ 𝓕 / 𝓚^(e+1) 𝓕` of `β` are compatible with the transition maps
`G_(e+1) ⟶ G_e` and `𝓕 / 𝓚^(e+2) 𝓕 ⟶ 𝓕 / 𝓚^(e+1) 𝓕`. -/
theorem βApp_naturality (e : ℕ) :
    (d.βApp β (e + 1)).hom ≫ smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1)
        F'.obj = (d.τ e).hom ≫ (d.βApp β e).hom := by
  have h := β.hom.hom.naturality (homOfLE (Nat.le_add_right e 1)).op
  exact ((congrArg ((d.βApp β (e + 1)).hom ≫ ·) (adicQuotientSystem_map_succ B (Spec (.of A)) hA
    X.1 X.2 K F'.obj e)).symm.trans h.symm).trans (congrArg (· ≫ (d.βApp β e).hom)
      (Functor.ofOpSequence_map_homOfLE_succ (X := fun e => (d.G e).obj) (fun e => (d.τ e).hom) e))

include d in
/-- If `γSystem H α = β ≫ a^∧`, then the level-`e` component of `γ` is the component of `β`
followed by the reduction of `a` modulo `𝓚^(e+1)`. -/
theorem γ_eq_βApp
    (hβ : d.γSystem H α = β.hom ≫ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map a)
    (e : ℕ) :
    (d.γ H α e).hom = (d.βApp β e).hom ≫
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1) a.hom :=
  (congrArg (fun k => k.hom.app (op e)) hβ).trans
    (congrArg ((d.βApp β e).hom ≫ ·)
      (completionFunctor_map_hom_app B (Spec (.of A)) hA X.1 X.2 K hK a e))

variable (β) in
/-- The level-`e` component of `β mod 𝓘^(n+1)`, read on `F_n`:
`F_n / 𝓚^(e+1) ≅ G_e / 𝓘^(n+1) ≅ (𝓕 / 𝓚^(e+1)) / 𝓘^(n+1) ≅ (𝓕 / 𝓘^(n+1)) / 𝓚^(e+1)`. -/
def βLevelApp (n e : ℕ) :
    smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1) (E.obj.obj (op n)) ≅
      smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1)
        (smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1)
          F'.obj) :=
  (d.ρApp e n).symm ≪≫
    (smallEtaleAdicQuotientFunctor B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
      (n + 1)).mapIso (d.βApp β e) ≪≫
    adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) K (e + 1) (n + 1)
      F'.obj

/-- `βLevelApp β n e` is the composite of the inverse of `ρApp e n`, the reduction of `βApp β e`
modulo `𝓘^(n+1)`, and the isomorphism exchanging the two reductions. -/
theorem βLevelApp_hom (n e : ℕ) :
    (d.βLevelApp β n e).hom = (d.ρApp e n).inv ≫
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) (d.βApp β e).hom ≫
      adicQuotientCommHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) K (e + 1)
        (n + 1) F'.obj :=
  rfl

/-- The isomorphisms `βLevelApp β n e` are compatible with the transition maps in `e`. -/
theorem βLevelApp_transition (n e : ℕ) :
    smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1) (E.obj.obj (op n)) ≫
        (d.βLevelApp β n e).hom =
      (d.βLevelApp β n (e + 1)).hom ≫
        smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1)
            F'.obj) := by
  rw [βLevelApp_hom, βLevelApp_hom, Category.assoc, Category.assoc,
    adicQuotientCommHom_transition, ← smallEtaleAdicQuotientMapOfHom_comp_assoc, βApp_naturality,
    smallEtaleAdicQuotientMapOfHom_comp_assoc, mapOfHom_τ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The isomorphisms `βLevelApp β n e` are compatible with the transition maps `F_(n+1) ⟶ F_n`
and `𝓕 / 𝓘^(n+2) 𝓕 ⟶ 𝓕 / 𝓘^(n+1) 𝓕`. -/
theorem βLevelApp_succ (n e : ℕ) :
    (d.βLevelApp β (n + 1) e).hom ≫
        smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
            (baseIdealSubmodule X.1 X.2 I) (n + 1) F'.obj) =
      smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (E.obj.map (homOfLE (Nat.le_add_right n 1)).op) ≫ (d.βLevelApp β n e).hom := by
  rw [βLevelApp_hom, βLevelApp_hom, Category.assoc, Category.assoc,
    adicQuotientCommHom_naturality, ← smallEtaleAdicQuotientMapOfHom_compat_assoc,
    ← Category.assoc, ρApp_naturality, Category.assoc]


variable (β) in
/-- **`β mod 𝓘^(n+1)`**, read on `F_n`: an isomorphism `F_n^∧ ≅ (𝓕 / 𝓘^(n+1) 𝓕)^∧` of
coherent `𝓚`-adic systems. -/
def βLevelHom (n : ℕ) :
    (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).obj (level E n) ⟶
      (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).obj (baseReduction I n F') :=
  ObjectProperty.homMk (NatTrans.ofOpSequence (fun e => (d.βLevelApp β n e).hom) fun e =>
    (congrArg (· ≫ (d.βLevelApp β n e).hom) (adicQuotientSystem_map_succ B (Spec (.of A)) hA
      X.1 X.2 K (E.obj.obj (op n)) e)).trans ((d.βLevelApp_transition n e).trans
      (congrArg ((d.βLevelApp β n (e + 1)).hom ≫ ·) (adicQuotientSystem_map_succ B (Spec (.of A))
        hA X.1 X.2 K (smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2
          (baseIdealSubmodule X.1 X.2 I) (n + 1) F'.obj) e).symm)))

/-- The level-`e` component of `βLevelHom β n` is `βLevelApp β n e`. -/
theorem βLevelHom_app (n e : ℕ) : (d.βLevelHom β n).hom.app (op e) = (d.βLevelApp β n e).hom :=
  rfl

/-- `βLevelHom β n` is an isomorphism. -/
instance isIso_βLevelHom (n : ℕ) : IsIso (d.βLevelHom β n) := by
  have happ : ∀ e : ℕᵒᵖ, IsIso ((d.βLevelHom β n).hom.app e) := fun e =>
    (d.βLevelApp β n e.unop).isIso_hom
  have : IsIso ((ObjectProperty.ι _).map (d.βLevelHom β n)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ
  exact isIso_of_reflects_iso _ (ObjectProperty.ι _)

variable (α) in
/-- `α_n : F_n ⟶ 𝓗 / 𝓘^(n+1) 𝓗`, as a map of coherent modules. -/
def αLevel (n : ℕ) : level E n ⟶ baseReduction I n H :=
  ObjectProperty.homMk (α.hom.app (op n))

include d in
/-- If `γSystem H α = β ≫ a^∧`, then the completion of `α_n` is `βLevelHom β n` followed by the
completion of `a mod 𝓘^(n+1)`. -/
theorem completionFunctor_map_αLevel
    (hβ : d.γSystem H α = β.hom ≫ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map a)
    (n : ℕ) :
    (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map (αLevel α n) =
      d.βLevelHom β n ≫ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map
        (baseReductionMap I n a) := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun e => ?_))
  obtain ⟨e⟩ := e
  change ((completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map (αLevel α n)).hom.app (op e) =
    (d.βLevelHom β n).hom.app (op e) ≫
      ((completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map (baseReductionMap I n a)).hom.app
        (op e)
  rw [completionFunctor_map_hom_app, completionFunctor_map_hom_app, βLevelHom_app]
  change smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1) (α.hom.app (op n)) =
    (d.βLevelApp β n e).hom ≫ smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
      (smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) a.hom)
  have hinv : (adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 K (baseIdealSubmodule X.1 X.2 I)
      (n + 1) (e + 1) H.obj).inv = adicQuotientCommHom B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) K (e + 1) (n + 1) H.obj := rfl
  rw [βLevelApp_hom, Category.assoc, Category.assoc, adicQuotientCommHom_natural,
    ← smallEtaleAdicQuotientMapOfHom_comp_assoc, ← γ_eq_βApp d hβ]
  refine Eq.trans ?_ (congrArg ((d.ρApp e n).inv ≫ · ≫ adicQuotientCommHom B (Spec (.of A)) hA
    X.1 X.2 (baseIdealSubmodule X.1 X.2 I) K (e + 1) (n + 1) H.obj) (d.mapOfHom_γ H α e n)).symm
  rw [← hinv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
    (Category.comp_id _))).symm

omit [IsNoetherianRing A] [IsAdicComplete I A] in
variable (α) in
/-- If the kernels and cokernels of `α` are annihilated by a power of `𝓚`, then so are the
kernel and cokernel of each `α_n`. -/
theorem isMapKernelCokernelAnnihilatedByPower_αLevel
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom) (n : ℕ) :
    IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K (αLevel α n) := by
  obtain ⟨t, ht, hall⟩ := hα
  refine ⟨t, ht, ?_, ?_⟩
  · rw [idealPowerMultiple_kernel_eq_bot_iff]
    exact (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 K t _).1 (hall n).1
  · rw [idealPowerMultiple_cokernel_eq_bot_iff]
    exact (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 K t _).1 (hall n).2

include d in
/-- **`𝓕 / 𝓘^(n+1) 𝓕 ≅ F_n`**, compatibly with `a mod 𝓘^(n+1)`, `α_n` and `β mod 𝓘^(n+1)`:
the uniqueness half of Stacks 08BB along `𝓚`, applied to the reductions of `α_n`. -/
theorem exists_levelIso
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B (Spec (.of A)) hA hZ X.1)
    (hβ : d.γSystem H α = β.hom ≫ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map a)
    (ha : IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K a)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom) (n : ℕ) :
    ∃ i : level E n ≅ baseReduction I n F', i.hom ≫ baseReductionMap I n a = αLevel α n ∧
      (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map i.hom = d.βLevelHom β n := by
  have := preservesFiniteLimits_completionFunctor_of_isNoetherian B (Spec (.of A)) hA X.1 X.2 K hK
    hZ hN
  have hb := isMapKernelCokernelAnnihilatedByPower_baseReductionMap (I := I) n a ha
  have hb' := isMapKernelCokernelAnnihilatedByPower_αLevel α hα n
  have heq := d.completionFunctor_map_αLevel hβ n
  obtain ⟨c, hc1, hc2⟩ := exists_lift_of_completion_lift B (Spec (.of A)) hA X.1 X.2 K hK
    (αLevel α n) (baseReductionMap I n a) hb (d.βLevelHom β n) heq.symm
  obtain ⟨c', hc'1, hc'2⟩ := exists_lift_of_completion_lift B (Spec (.of A)) hA X.1 X.2 K hK
    (baseReductionMap I n a) (αLevel α n) hb' (inv (d.βLevelHom β n))
    (by rw [heq, IsIso.inv_hom_id_assoc])
  obtain ⟨t, ht, hkt, -⟩ := hb'
  obtain ⟨s, hs, hks, -⟩ := hb
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  refine ⟨⟨c, c', ?_, ?_⟩, hc1, hc2⟩
  · exact eq_of_comp_eq_of_completionFunctor_map_eq B (Spec (.of A)) hA X.1 X.2 K hK
      (αLevel α n) t' hkt (by rw [Category.assoc, hc'1, hc1, Category.id_comp])
      (by rw [Functor.map_comp, hc2, hc'2, IsIso.hom_inv_id, CategoryTheory.Functor.map_id])
  · exact eq_of_comp_eq_of_completionFunctor_map_eq B (Spec (.of A)) hA X.1 X.2 K hK
      (baseReductionMap I n a) s' hks (by rw [Category.assoc, hc1, hc'1, Category.id_comp])
      (by rw [Functor.map_comp, hc2, hc'2, IsIso.inv_hom_id, CategoryTheory.Functor.map_id])

include d in
/-- Isomorphisms `F_n ≅ 𝓕 / 𝓘^(n+1) 𝓕` compatible with `a mod 𝓘^(n+1)` and `α_n`, and whose
completions are `β mod 𝓘^(n+1)`, are compatible with the transition maps in `n`. -/
theorem levelIso_compat
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B (Spec (.of A)) hA hZ X.1)
    (ha : IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K a)
    (i : ∀ n, level E n ≅ baseReduction I n F')
    (hi1 : ∀ n, (i n).hom ≫ baseReductionMap I n a = αLevel α n)
    (hi2 : ∀ n, (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map (i n).hom =
      d.βLevelHom β n) (n : ℕ) :
    (i (n + 1)).hom.hom ≫ smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
        (baseIdealSubmodule X.1 X.2 I) (n + 1) F'.obj =
      E.obj.map (homOfLE (Nat.le_add_right n 1)).op ≫ (i n).hom.hom := by
  have := preservesFiniteLimits_completionFunctor_of_isNoetherian B (Spec (.of A)) hA X.1 X.2 K hK
    hZ hN
  let trF : baseReduction I (n + 1) F' ⟶ baseReduction I n F' :=
    ObjectProperty.homMk (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) F'.obj)
  let trE : level E (n + 1) ⟶ level E n :=
    ObjectProperty.homMk (E.obj.map (homOfLE (Nat.le_add_right n 1)).op)
  obtain ⟨s, hs, hks, -⟩ := isMapKernelCokernelAnnihilatedByPower_baseReductionMap (I := I) n a ha
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  have hαnat : α.hom.app (op (n + 1)) ≫ smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1
      X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1) H.obj =
      E.obj.map (homOfLE (Nat.le_add_right n 1)).op ≫ α.hom.app (op n) :=
    (congrArg (α.hom.app (op (n + 1)) ≫ ·) (adicQuotientSystem_map_succ B (Spec (.of A)) hA X.1
      X.2 (baseIdealSubmodule X.1 X.2 I) H.obj n)).symm.trans (α.hom.naturality _).symm
  let trH : baseReduction I (n + 1) H ⟶ baseReduction I n H :=
    ObjectProperty.homMk (smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) (n + 1) H.obj)
  have hF : trF ≫ baseReductionMap I n a = baseReductionMap I (n + 1) a ≫ trH :=
    ObjectProperty.hom_ext _ (smallEtaleAdicQuotientMapOfHom_compat B (Spec (.of A)) hA X.1 X.2
      (baseIdealSubmodule X.1 X.2 I) n a.hom)
  have hA' : αLevel α (n + 1) ≫ trH = trE ≫ αLevel α n := ObjectProperty.hom_ext _ hαnat
  have key : (i (n + 1)).hom ≫ trF = trE ≫ (i n).hom := by
    refine eq_of_comp_eq_of_completionFunctor_map_eq B (Spec (.of A)) hA X.1 X.2 K hK
      (baseReductionMap I n a) s' hks ?_ ?_
    · rw [Category.assoc, hF, ← Category.assoc, hi1, hA', Category.assoc, hi1]
    · rw [Functor.map_comp, Functor.map_comp, hi2, hi2]
      refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun e => ?_))
      obtain ⟨e⟩ := e
      change (d.βLevelHom β (n + 1)).hom.app (op e) ≫
          ((completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map trF).hom.app (op e) =
        ((completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map trE).hom.app (op e) ≫
          (d.βLevelHom β n).hom.app (op e)
      rw [completionFunctor_map_hom_app, completionFunctor_map_hom_app, βLevelHom_app,
        βLevelHom_app]
      exact d.βLevelApp_succ n e
  exact congrArg (fun k => k.hom) key

include d in
/-- **The isomorphism `(F_n) ≅ 𝓕^∧`** assembled from the levelwise isomorphisms. -/
theorem nonempty_iso_baseCompletion
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B (Spec (.of A)) hA hZ X.1)
    (hβ : d.γSystem H α = β.hom ≫ (completionFunctor B (Spec (.of A)) hA X.1 X.2 K hK).map a)
    (ha : IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K a)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom) :
    Nonempty ((baseCompletion X I).obj F' ≅ E) := by
  choose i hi1 hi2 using d.exists_levelIso hZ hN hβ ha hα
  have hc := d.levelIso_compat hZ hN ha i hi1 hi2
  let φ : E ⟶ (baseCompletion X I).obj F' :=
    ObjectProperty.homMk (NatTrans.ofOpSequence (fun n => (i n).hom.hom) fun n =>
      (hc n).symm.trans (congrArg ((i (n + 1)).hom.hom ≫ ·) (adicQuotientSystem_map_succ B
        (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) F'.obj n).symm))
  have happ : ∀ n : ℕᵒᵖ, IsIso (φ.hom.app n) := fun n =>
    (ObjectProperty.ι _).map_isIso (i n.unop).hom
  have : IsIso ((ObjectProperty.ι _).map φ) := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ
  have : IsIso φ := isIso_of_reflects_iso _ (ObjectProperty.ι _)
  exact ⟨(asIso φ).symm⟩

variable (β) in
include d β in
/-- **The kernel of `a : 𝓕 ⟶ 𝓗` has proper support.**  It is annihilated by `𝓚^s`, so by
Artin–Rees (Stacks 07UL, through the Artin–Rees step of Stacks 08B5) it embeds into
`𝓕 / 𝓚^(s+c+1) 𝓕 ≅ G_(s+c)`, whose support is proper. -/
theorem hasProperSupport_kernel (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B (Spec (.of A)) hA hZ X.1)
    (ha : IsMapKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K a) :
    HasProperSupportOverBase X f hf
      ⟨kernel a.hom, isCoherent_kernel B (Spec (.of A)) hA X.1 X.2
        F'.property H.property a.hom⟩ := by
  obtain ⟨s, -, hks, -⟩ := ha
  rw [idealPowerMultiple_kernel_eq_bot_iff] at hks
  let P : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
    ⟨kernel a.hom, isCoherent_kernel B (Spec (.of A)) hA X.1 X.2 F'.property H.property a.hom⟩
  let ι : P ⟶ F' := ObjectProperty.homMk (kernel.ι a.hom)
  have : Mono ι := ⟨fun g h hgh => ObjectProperty.hom_ext _
    ((cancel_mono (kernel.ι a.hom)).1 (congrArg (fun k => k.hom) hgh))⟩
  obtain ⟨c, hc⟩ := exists_comp_completionTermProjection_eq_zero_of_mono B (Spec (.of A)) hA X.1
    X.2 K hK hZ hN ι
  have hPs : idealPowerMultiple B (Spec (.of A)) hA X.1 X.2 K (s + 1) P.obj = ⊥ :=
    (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 K _ _).2
      (isPowAnnihilated_of_le B (Spec (.of A)) hA X.1 X.2 K (Nat.le_succ s) _ hks)
  have : IsIso (completionTermProjection B (Spec (.of A)) hA X.1 X.2 K hK P s) :=
    isIso_π_idealPowerMultiple_of_eq_bot B (Spec (.of A)) hA X.1 X.2 K (s + 1) P.obj hPs
  have : Mono (completionTermProjection B (Spec (.of A)) hA X.1 X.2 K hK P s) :=
    IsIso.mono_of_iso _
  let ψ : P.obj ⟶ smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (s + c + 1) F'.obj :=
    ι.hom ≫ completionTermProjection B (Spec (.of A)) hA X.1 X.2 K hK F' (s + c)
  have : Mono ψ := by
    refine Preadditive.mono_of_cancel_zero (C := SheafOfModules _) _ fun {T} g hg => ?_
    exact (cancel_mono (completionTermProjection B (Spec (.of A)) hA X.1 X.2 K hK P s)).1
      ((hc s g hg).trans zero_comp.symm)
  let φ : P.obj ⟶ (d.G (s + c)).obj := ψ ≫ (d.βApp β (s + c)).inv
  have : Mono φ := mono_comp' ‹Mono ψ› (IsIso.mono_of_iso (d.βApp β (s + c)).inv)
  have hinj : ∀ U : SmallEtale B (Spec (.of A)) hA X.1, Function.Injective (φ.val.app (op U)) :=
    fun U => (ModuleCat.mono_iff_injective _).mp
      (Functor.map_mono (SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).O)
        (op (U : (smallEtaleRingedSite B (Spec (.of A)) hA X.1 X.2).C))) φ)
  exact hasProperSupportOverBase_of_injective X f hf (M := P) (N := d.G (s + c)) φ hinj
    (d.proper (s + c))

end C1573.TorsionAlgebraization

/-- **Stacks 08BC, with hypothesis (1) read on `X`.**  Let `(F_n)` be a coherent `I 𝒪_X`-adic
system with support proper over `A`, and `α : (F_n) ⟶ 𝓗^∧` a map from it to the completion of a
coherent module with proper support whose kernels and cokernels are annihilated by a power of
`𝓚`.  If every coherent adic system with proper support annihilated by a power of `𝓚` is a
completion, then `(F_n)` is in the essential image of the completion functor (Stacks 08B8). -/
theorem C1573.essImage_completionFunctorProperOver_of_kTorsionEssSurj
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite) (hZ : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B (Spec (.of A)) hA hZ X.1)
    (h1 : ∀ e, KTorsionEssSurj X I f hf K (e + 1))
    (E : CoherentAdicSystemsProperOver B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2
      f.hom hf (baseIdealSubmodule X.1 X.2 I))
    (H : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2)
    (hH : HasProperSupportOverBase X f hf H)
    (α : E.obj ⟶ (baseCompletion X I).obj H)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B (Spec (.of A)) hA X.1 X.2 K α.hom) :
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).essImage E := by
  obtain ⟨d⟩ := nonempty_torsionAlgebraization X I f hf K hK E.obj h1 E.property
  obtain ⟨F', a, β, ha, hβ⟩ := exists_algebraization B (Spec (.of A)) hA X.1 X.2 K hK
    (d.γSystem H α) (d.isSystemKernelCokernelAnnihilatedByPower_γSystem hH hα)
  obtain ⟨e⟩ := d.nonempty_iso_baseCompletion hZ hN hβ ha hα
  have hker := d.hasProperSupport_kernel β hZ hN ha
  have := F'.property.toIsCoherentOnSite
  have := H.property.toIsCoherentOnSite
  have hF' : HasProperSupportOverBase X f hf F' :=
    hasProperSupport_of_subset_union B (Spec (.of A)) hA X.2 _ f.hom hf
      (isClosed_supportOfSheaf_coherent X F')
      (supportOfSheaf_subset_union_kernel B (Spec (.of A)) hA X a.hom) hker hH
  exact essImage_completionFunctorProperOver_of_hasProperSupport B (Spec (.of A)) hA X.1 _ X.2 _
    f.hom hf _ _ E F' hF' e

end Algebraization

end AlgebraicGeometry.Space

end

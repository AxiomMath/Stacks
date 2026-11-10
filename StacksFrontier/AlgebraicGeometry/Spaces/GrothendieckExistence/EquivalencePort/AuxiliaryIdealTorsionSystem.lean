module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.BaseCompletionProperSupport

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573
namespace AlgebraicGeometry.Space.C1573.TorsionAlgebraization
end AlgebraicGeometry.Space.C1573.TorsionAlgebraization

/-!
# The `𝓚`-adic system of algebraizations of `(F_n / 𝓚^e F_n)_n`

Let `(F_n)` be a coherent `I 𝒪_X`-adic system with proper support and `𝓚` a quasi-coherent sheaf
of ideals. Granted that every such system annihilated by `𝓚^e` is a completion, choose coherent
`G_e` with `G_e^∧ ≅ (F_n / 𝓚^(e+1) F_n)_n`; the transition maps of the systems algebraize to maps
`G_{e+1} ⟶ G_e`, and `(G_e)_e` is a coherent `𝓚`-adic system.

## Main definitions

* `AlgebraicGeometry.Space.C1573.TorsionAlgebraization`: a choice of coherent `G_e` with proper
  support, annihilated by `𝓚^(e+1)`, whose completion is `(F_n / 𝓚^(e+1) F_n)_n`.
* `AlgebraicGeometry.Space.C1573.TorsionAlgebraization.τ`: the algebraized transition map
  `G_{e+1} ⟶ G_e`.
* `AlgebraicGeometry.Space.C1573.TorsionAlgebraization.adicSystem`: `(G_e)_e` as a coherent
  `𝓚`-adic system.

## Main results

* `AlgebraicGeometry.Space.C1573.nonempty_torsionAlgebraization`: such algebraizations exist.
* `AlgebraicGeometry.Space.C1573.TorsionAlgebraization.isCoherentAdicSystem_system`: `(G_e)_e`
  is a coherent `𝓚`-adic system.
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
  (X : AlgebraicSpaces B (Spec (.of A)) hA) (I : Ideal A)
  [Fact (HasEtaleLocalProperty B (Spec (.of A)) hA X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  [IsNoetherianRing A] [IsAdicComplete I A] (f : X ⟶ schemeSpace (baseObject A B hA))
  (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
  (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X.1
        X.2).O))).Submodule)
  (hK : K.toSheafOfModules.IsQuasicoherentOnSite)

/-- The transition `M / 𝓚^(e+1) M ⟶ M / 𝓚^e M`, as a natural transformation. -/
def C1573.adicQuotientFunctorTransition (e : ℕ) :
    smallEtaleAdicQuotientFunctor B (Spec (.of A)) hA X.1 X.2 K (e + 1) ⟶
      smallEtaleAdicQuotientFunctor B (Spec (.of A)) hA X.1 X.2 K e where
  app M := smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K e M
  naturality _ _ φ := smallEtaleAdicQuotientTransition_naturality B (Spec (.of A)) hA X.1 X.2 K e φ

/-- **Hypothesis (1) of Stacks 08BC, read on `X`**: every coherent `I 𝒪_X`-adic system with
proper support whose terms are annihilated by `𝓚^e` is the completion of a coherent module with
proper support annihilated by `𝓚^e`. -/
def C1573.KTorsionEssSurj (e : ℕ) : Prop :=
  ∀ E' : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I),
    HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj (E'.obj.obj (op 0))) →
    (∀ n, IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K e (E'.obj.obj (op n))) →
    ∃ G : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2, HasProperSupportOverBase X f hf G ∧
      IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K e G.obj ∧
      Nonempty ((baseCompletion X I).obj G ≅ E')

variable (E : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I))

/-- The coherent `I 𝒪_X`-adic system `(F_n / 𝓚^e F_n)_n`. -/
def C1573.quotientAdicSystem (e : ℕ) :
    CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) :=
  ⟨quotientSystem B (Spec (.of A)) hA X.1 X.2 K E.obj e,
    isCoherentAdicSystem_quotientSystem B (Spec (.of A)) hA X.1 X.2 _ K hK E.property e⟩

/-- The transition `(F_n / 𝓚^(e+1))_n ⟶ (F_n / 𝓚^e)_n`. -/
def C1573.quotientAdicSystemTransition (e : ℕ) :
    quotientAdicSystem X I K hK E (e + 1) ⟶ quotientAdicSystem X I K hK E e :=
  ObjectProperty.homMk (Functor.whiskerLeft E.obj (adicQuotientFunctorTransition X K e))

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- If `F_0` has proper support, so does `F_0 / 𝓚^e F_0`. -/
theorem C1573.hasProperSupport_quotientAdicSystem
    (hE : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj (E.obj.obj (op 0)))) (e : ℕ) :
    HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj ((quotientAdicSystem X I K hK E e).obj.obj (op 0))) :=
  hasProperSupport_idealPowerQuotient B (Spec (.of A)) hA X.2 _ f.hom hf K e _
    (E.property.1 0) hE

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- Each term `F_n / 𝓚^e F_n` is annihilated by `𝓚^e`. -/
theorem C1573.isPowAnnihilated_quotientAdicSystem (e n : ℕ) :
    IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K e
      ((quotientAdicSystem X I K hK E e).obj.obj (op n)) :=
  isPowAnnihilated_smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K e _

/-- A family of coherent modules `G_e` with proper support, annihilated by `𝓚^(e+1)`, together
with isomorphisms `G_e^∧ ≅ (F_n / 𝓚^(e+1) F_n)_n`. -/
structure C1573.TorsionAlgebraization where
  /-- The algebraization of `(F_n / 𝓚^(e+1) F_n)_n`. -/
  G : ℕ → CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2
  /-- Each `G_e` has proper support over the base. -/
  proper : ∀ e, HasProperSupportOverBase X f hf (G e)
  /-- Each `G_e` is annihilated by `𝓚^(e+1)`. -/
  annih : ∀ e, IsPowAnnihilated B (Spec (.of A)) hA X.1 X.2 K (e + 1) (G e).obj
  /-- The identification of its completion. -/
  ρ : ∀ e, (baseCompletion X I).obj (G e) ≅ quotientAdicSystem X I K hK E (e + 1)

omit [IsNoetherianRing A] [IsAdicComplete I A] in
/-- If every coherent `I 𝒪_X`-adic system with proper support annihilated by a power of `𝓚` is a
completion, and `F_0` has proper support, then the quotients `(F_n / 𝓚^(e+1) F_n)_n` admit
algebraizations. -/
theorem C1573.nonempty_torsionAlgebraization (h1 : ∀ e, KTorsionEssSurj X I f hf K (e + 1))
    (hE : HasProperSupport B (Spec (.of A)) hA X.2 (schemeSpace (baseObject A B hA)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj (E.obj.obj (op 0)))) :
    Nonempty (TorsionAlgebraization X I f hf K hK E) := by
  have hex := fun e => h1 e (quotientAdicSystem X I K hK E (e + 1))
    (hasProperSupport_quotientAdicSystem X I f hf K hK E hE (e + 1))
    (isPowAnnihilated_quotientAdicSystem X I K hK E (e + 1))
  choose G hGp hGK hρ using hex
  exact ⟨⟨G, hGp, hGK, fun e => (hρ e).some⟩⟩

namespace C1573.TorsionAlgebraization

variable {X I f hf K hK E} (d : TorsionAlgebraization X I f hf K hK E)

/-- The algebraized transition map `G_{e+1} ⟶ G_e`. -/
def τ (e : ℕ) : d.G (e + 1) ⟶ d.G e :=
  ((bijective_baseCompletion_map X I f hf (d.proper (e + 1))).2
    ((d.ρ (e + 1)).hom ≫ quotientAdicSystemTransition X I K hK E (e + 1) ≫ (d.ρ e).inv)).choose

/-- The completion of `τ_e` is the transition `(F_n / 𝓚^(e+2))_n ⟶ (F_n / 𝓚^(e+1))_n`, read
through `ρ`. -/
theorem baseCompletion_map_τ (e : ℕ) :
    (baseCompletion X I).map (d.τ e) =
      (d.ρ (e + 1)).hom ≫ quotientAdicSystemTransition X I K hK E (e + 1) ≫ (d.ρ e).inv :=
  ((bijective_baseCompletion_map X I f hf (d.proper (e + 1))).2 _).choose_spec

/-- The level-`n` component of `ρ_e`. -/
def ρApp (e n : ℕ) :
    smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) (n + 1)
        (d.G e).obj ≅
      smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1) (E.obj.obj (op n)) :=
  ((ObjectProperty.ι _).mapIso (d.ρ e)).app (op n)

/-- At level `n`, `τ_e` modulo `I^(n+1)` is the transition `F_n / 𝓚^(e+2) ⟶ F_n / 𝓚^(e+1)`, read
through `ρ`. -/
theorem mapOfHom_τ (e n : ℕ) :
    smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) (d.τ e).hom =
      (d.ρApp (e + 1) n).hom ≫
        smallEtaleAdicQuotientTransition B (Spec (.of A)) hA X.1 X.2 K (e + 1) (E.obj.obj (op n)) ≫
          (d.ρApp e n).inv := by
  rw [smallEtaleAdicQuotientMapOfHom_eq]
  exact congrArg (fun t => t.hom.app (op n)) (d.baseCompletion_map_τ e)

/-- The map `G_{e+1} / 𝓚^(e+1) G_{e+1} ⟶ G_e` induced by the transition. -/
def σ (e : ℕ) :
    smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1) (d.G (e + 1)).obj ⟶ (d.G e).obj :=
  smallEtaleAdicQuotientLift B (Spec (.of A)) hA X.1 X.2 K (e + 1) (d.τ e).hom (d.annih e)

/-- `G_{e+1} / 𝓚^(e+1) G_{e+1}`, as a coherent module. -/
def quotientG (e : ℕ) : CoherentModules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  ⟨smallEtaleAdicQuotient B (Spec (.of A)) hA X.1 X.2 K (e + 1) (d.G (e + 1)).obj,
    isCoherent_idealPowerQuotient B (Spec (.of A)) hA X.1 X.2 K hK _ (d.G (e + 1)).property (e + 1)⟩

/-- At level `n`, `σ_e` modulo `I^(n+1)` is the composite of the canonical isomorphisms with the
level-`n` components of `ρ`. -/
theorem mapOfHom_σ (e n : ℕ) :
    smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
        (n + 1) (d.σ e) =
      (adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) K (e + 1)
          (n + 1) (d.G (e + 1)).obj).hom ≫
        smallEtaleAdicQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (d.ρApp (e + 1) n).hom ≫
        (adicQuotientQuotientIso B (Spec (.of A)) hA X.1 X.2 K (e + 1)
          (E.obj.obj (op n))).hom ≫ (d.ρApp e n).inv := by
  refine (cancel_epi (smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 K (e + 1)
      (d.G (e + 1)).obj ≫
    smallEtaleAdicQuotientProjection B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I)
      (n + 1) _)).1 ?_
  rw [Category.assoc, smallEtaleAdicQuotientProjection_mapOfHom, ← Category.assoc, σ,
    smallEtaleAdicQuotientProjection_lift, Category.assoc, adicQuotientCommIso,
    adicQuotientCommHom_spec_assoc, smallEtaleAdicQuotientProjection_mapOfHom_assoc]
  rw [smallEtaleAdicQuotientProjection_adicQuotientQuotientIso_hom_assoc, ← mapOfHom_τ,
    smallEtaleAdicQuotientProjection_mapOfHom]

/-- The map `G_{e+1} / 𝓚^(e+1) G_{e+1} ⟶ G_e` is an isomorphism. -/
theorem isIso_σ (e : ℕ) : IsIso (d.σ e) := by
  have hQ : HasProperSupportOverBase X f hf (d.quotientG e) :=
    hasProperSupport_idealPowerQuotient B (Spec (.of A)) hA X.2 _ f.hom hf K (e + 1) _
      (d.G (e + 1)).property (d.proper (e + 1))
  let σ' : d.quotientG e ⟶ d.G e := ObjectProperty.homMk (d.σ e)
  have happ : ∀ n : ℕᵒᵖ,
      IsIso (((ObjectProperty.ι _).map ((baseCompletion X I).map σ')).app n) := by
    intro n
    obtain ⟨n⟩ := n
    change IsIso (idealPowerQuotientMapOfHom B (Spec (.of A)) hA X.1 X.2 _ (n + 1) (d.σ e))
    rw [← smallEtaleAdicQuotientMapOfHom_eq, mapOfHom_σ]
    exact (adicQuotientCommIso B (Spec (.of A)) hA X.1 X.2 (baseIdealSubmodule X.1 X.2 I) K (e + 1)
      (n + 1) (d.G (e + 1)).obj ≪≫
      (smallEtaleAdicQuotientFunctor B (Spec (.of A)) hA X.1 X.2 K (e + 1)).mapIso
        (d.ρApp (e + 1) n) ≪≫
      adicQuotientQuotientIso B (Spec (.of A)) hA X.1 X.2 K (e + 1) (E.obj.obj (op n)) ≪≫
      (d.ρApp e n).symm).isIso_hom
  have : IsIso ((ObjectProperty.ι _).map ((baseCompletion X I).map σ')) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ happ
  have : IsIso ((baseCompletion X I).map σ') :=
    isIso_of_reflects_iso _ (ObjectProperty.ι _)
  have := isIso_of_isIso_baseCompletion_map X I f hf hQ (d.proper e) σ'
  exact (inferInstance : IsIso ((ObjectProperty.ι _).map σ'))

/-- The inverse system `(G_e)_e`. -/
def system : ℕᵒᵖ ⥤ Modules.{u, u} B (Spec (.of A)) hA X.1 X.2 :=
  Functor.ofOpSequence (X := fun e => (d.G e).obj) fun e => (d.τ e).hom

/-- **`(G_e)_e` is a coherent `𝓚`-adic system.** -/
theorem isCoherentAdicSystem_system :
    IsCoherentAdicSystem B (Spec (.of A)) hA X.1 X.2 K d.system := by
  refine ⟨fun e => (d.G e).property,
    fun e => (idealPowerMultiple_eq_bot_iff B (Spec (.of A)) hA X.1 X.2 K _ _).2 (d.annih e),
    fun e => ?_⟩
  refine ⟨@asIso _ _ _ _ (d.σ e) (d.isIso_σ e), ?_⟩
  refine (smallEtaleAdicQuotientProjection_lift B (Spec (.of A)) hA X.1 X.2 K (e + 1) (d.τ e).hom
    (d.annih e)).trans ?_
  exact (Functor.ofOpSequence_map_homOfLE_succ (X := fun e => (d.G e).obj)
    (fun e => (d.τ e).hom) e).symm

/-- `(G_e)_e`, as an object of `Coh(X, 𝓚)`. -/
def adicSystem : CoherentAdicSystems B (Spec (.of A)) hA X.1 X.2 K :=
  ⟨d.system, d.isCoherentAdicSystem_system⟩

end C1573.TorsionAlgebraization



end AlgebraicGeometry.Space

end

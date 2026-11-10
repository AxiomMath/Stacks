module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartAdicSystemTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge

namespace Stacks.TensorProduct.C1573
end Stacks.TensorProduct.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The kernel–cokernel bound of Stacks 08BD over an affine chart

Let `f : X ⟶ Y` be a representable proper morphism of algebraic spaces with `Y` locally
Noetherian, `𝒥 ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals, `𝓘 = f⁻¹𝒥 · 𝒪_X`, `(𝒢_n)` a coherent
`𝒥`-adic system, `𝓕` a coherent `𝒪_X`-module and `β : (f^*𝒢_n) ≅ 𝓕^` an isomorphism of inverse
systems, with maps `γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/𝓘ⁿ⁺¹𝓕)`.  Over an affine étale chart `V` of
`Y` all the data are read on the affine scheme of `V` and on the proper scheme `V ×_Y X` over
it, and the maps `γ_n` become the maps `γ_n` of a scheme datum to which the kernel–cokernel bound
of Stacks 088B applies.

## Main definitions

* `AlgebraicGeometry.Space.C1573.directImageUnitComparison`: the maps `γ_n`.
* `AlgebraicGeometry.Space.C1573.chartGammaSections`: `γ_n` on the sections over `V`, read through
  the identification of the sections of `f_*(𝓕/𝓘ⁿ⁺¹𝓕)` with those of the scheme quotient.
* `AlgebraicGeometry.Space.C1573.chartGamma`: the scheme maps `γ'_n`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

open _root_.CategoryTheory.C1573
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **Bijectivity of a map out of a tensor product is detected after a bijective change of the
tensor product**: if `e ∘ Θ` and `Ψ ∘ τ` agree on pure tensors, with `τ`, `Ψ` and `e` bijective
and everything additive, then `Θ` is bijective. -/
theorem Stacks.TensorProduct.C1573.bijective_of_tmul_eq_of_bijective {R : Type*} [CommSemiring R]
    {A M : Type*}
    [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M] {P N N' : Type*}
    [AddCommMonoid P] [AddCommMonoid N] [AddCommMonoid N']
    (Θ : TensorProduct R A M →+ N) (τ : TensorProduct R A M →+ P) (hτ : Function.Bijective τ)
    (Ψ : P →+ N') (hΨ : Function.Bijective Ψ) (e : N ≃+ N')
    (h : ∀ a m, e (Θ (a ⊗ₜ m)) = Ψ (τ (a ⊗ₜ m))) : Function.Bijective Θ := by
  have key : ∀ t, e (Θ t) = Ψ (τ t) := fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul a m => exact h a m
    | add t₁ t₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, h₁, h₂]
  have hΘ : ⇑Θ = e.symm ∘ (Ψ ∘ τ) := funext fun t => by
    rw [Function.comp_apply, Function.comp_apply, ← key, AddEquiv.symm_apply_apply]
  rw [hΘ]
  exact e.symm.bijective.comp (hΨ.comp hτ)

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
  (F : Modules.{u, u} B S hS X.1 X.2)
  (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
  (β : G.obj ⋙ modulePullback B S hS f ≅
    adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F)

/-- **The maps `γ_n : 𝒢_n ⟶ f_*f^*𝒢_n ⟶ f_*(𝓕/𝓘ⁿ⁺¹𝓕)` of Stacks 08BD**: the adjunction map
followed by `f_*β_n`. -/
def C1573.directImageUnitComparison :
    G.obj ⟶ adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F ⋙
      modulePushforward B S hS f :=
  pullbackPushforwardUnitSystem B S hS f G.obj ≫
    Functor.whiskerRight β.hom (modulePushforward B S hS f)

variable (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
  (hF : IsCoherent B S hS X.1 X.2 F)
  (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
  (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
    (chartSectionsIdeal B S hS Y J Q).FG)

/-- The identification of the sections over `V` of `f_*(𝓕/𝓘ⁿ⁺¹𝓕)` with the global sections of
`f_{V*}(𝓕|_U/ℐⁿ⁺¹)`, with target the evaluation at `⊤`. -/
def C1573.chartDirectImageAdicQuotientEvalIso (n : ℕ) :
    (chartSectionsTop B S hS V).obj ((modulePushforward B S hS f).obj
        (smallEtaleAdicQuotient B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1) F)) ≅
      (SheafOfModules.evaluation (chartScheme V).ringCatSheaf (op ⊤)).obj
        ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
          (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n))) :=
  chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n ≪≫
    ModuleCat.restrictScalarsId'App (RingHom.id _) rfl _

/-- `γ_n` on the sections over `V`. -/
def C1573.chartGammaSections (n : ℕ) :
    (chartSectionsTop B S hS V).obj (G.obj.obj (op n)) ⟶
      (SheafOfModules.evaluation (chartScheme V).ringCatSheaf (op ⊤)).obj
        ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).obj
          (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
            (chartCoherentModule B S hS f hf V F hF)).obj.obj (op n))) :=
  (chartSectionsTop B S hS V).map ((directImageUnitComparison B S hS f hf J F G β).app (op n)) ≫
    (chartDirectImageAdicQuotientEvalIso B S hS f hf J F V hF hJ hJfg n).hom

/-- The maps `chartGammaSections` commute with the transition maps of `𝒢` and of the scheme
adic quotient system. -/
theorem C1573.chartGammaSections_naturality (n : ℕ) :
    (chartSectionsTop B S hS V).map (G.obj.map (homOfLE (Nat.le_add_right n 1)).op) ≫
        chartGammaSections B S hS f hf J F G β V hF hJ hJfg n =
      chartGammaSections B S hS f hf J F G β V hF hJ hJfg (n + 1) ≫
        (SheafOfModules.evaluation (chartScheme V).ringCatSheaf (op ⊤)).map
          ((Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V)).map
            (((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
              (chartCoherentModule B S hS f hf V F hF)).obj.map
                (homOfLE (Nat.le_add_right n 1)).op)) := by
  refine ModuleCat.hom_ext (DFunLike.ext _ _ fun m => ?_)
  have h1 := congrArg (fun k => k.val.app (op V) m)
    ((directImageUnitComparison B S hS f hf J F G β).naturality (homOfLE (Nat.le_add_right n 1)).op)
  have h2 := congrArg (fun k => ((modulePushforward B S hS f).map k).val.app (op V)
      (((directImageUnitComparison B S hS f hf J F G β).app (op (n + 1))).val.app (op V) m))
    (adicQuotientSystem_map_succ B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F n)
  have h3 := chartDirectImageAdicQuotientIso_transition B S hS f hf V J F hF hJ hJfg n
    (((directImageUnitComparison B S hS f hf J F G β).app (op (n + 1))).val.app (op V) m)
  change (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom
      (((directImageUnitComparison B S hS f hf J F G β).app (op n)).val.app (op V)
        ((G.obj.map (homOfLE (Nat.le_add_right n 1)).op).val.app (op V) m)) = _
  exact (congrArg (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom h1).trans
    ((congrArg (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom h2).trans h3)

omit [IsAffine (chartScheme V)]
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))] in
/-- **The isomorphism `β_n` carries the chart section of the pullback to the image of `γ_n`**:
`β_n(f^*s|_U) = γ_n(s)|_U` over a chart diagram `U ⟶ V`. -/
theorem C1573.β_modulePullbackChartSection (n : ℕ) (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : (G.obj.obj (op n)).val.obj (op d.V)) :
    (β.hom.app (op n)).val.app (op d.U)
        (modulePullbackChartSection B S hS f (G.obj.obj (op n)) d s) =
      modulePushforwardCounitApp B S hS f _ d
        (((directImageUnitComparison B S hS f hf J F G β).app (op n)).val.app (op d.V) s) := by
  rw [← modulePullbackUnitSection_eq_modulePullbackChartSection]
  exact (modulePushforwardCounitApp_map B S hS f (β.hom.app (op n)) d _).symm

variable [IsNoetherianRing Γ(chartScheme V, ⊤)] (hJqc : J.toSheafOfModules.IsQuasicoherentOnSite)

/-- **The scheme maps `γ'_n : 𝒢_n(V)~ ⟶ f_{V*}(𝓕|_U/ℐⁿ⁺¹)`** adjoint to `γ_n` on the sections over
`V`. -/
def C1573.chartGamma : (chartTildeSystem B S hS V J hJqc G).obj ⟶
    ((Stacks.Algebraization.completionFunctor _ (chartBaseChangeIdeal B S hS f hf V J)).obj
      (chartCoherentModule B S hS f hf V F hF)).obj ⋙
      Scheme.Modules.pushforward (chartBaseChangeSchemeHom B S hS f hf V) :=
  NatTrans.ofOpSequence (fun n => ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv
      _ _).symm (chartGammaSections B S hS f hf J F G β V hF hJ hJfg n))
    (fun n => by
      change (Stacks.Coherent.affineTilde (chartScheme V)).map ((chartSectionsTop B S hS V).map
        (G.obj.map (homOfLE (Nat.le_add_right n 1)).op)) ≫ _ = _ ≫ _
      exact ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_naturality_left_symm
        _ _).symm.trans ((congrArg (fun k => ((Stacks.Coherent.affineTildeAdjunction
          (chartScheme V)).homEquiv _ _).symm k)
            (chartGammaSections_naturality B S hS f hf J F G β V hF hJ hJfg n)).trans
          ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_naturality_right_symm
            _ _)))

/-- The component of `chartGamma` at `n` is the adjoint of `chartGammaSections` at `n`. -/
theorem C1573.chartGamma_app (n : ℕ) :
    (chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n) =
      ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _).symm
        (chartGammaSections B S hS f hf J F G β V hF hJ hJfg n) :=
  rfl

/-- The global sections of `γ'_n` on the image of a section of `𝒢_n(V)` are `γ_n` on the sections
over `V`. -/
theorem C1573.chartGamma_app_top (n : ℕ) (m : (G.obj.obj (op n)).val.obj (op V)) :
    Scheme.Modules.Hom.app ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n)) ⊤
        ((Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op n)))).hom.hom m) =
      (chartGammaSections B S hS f hf J F G β V hF hJ hJfg n).hom m := by
  have h1 : ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _)
      ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n)) =
        chartGammaSections B S hS f hf J F G β V hF hJ hJfg n :=
    ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _).apply_symm_apply _
  have h2 := (Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_unit
    ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))) _
    ((chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc).app (op n))
  exact (ConcreteCategory.congr_hom (h1.symm.trans h2) m).symm

end AlgebraicGeometry.Space

end

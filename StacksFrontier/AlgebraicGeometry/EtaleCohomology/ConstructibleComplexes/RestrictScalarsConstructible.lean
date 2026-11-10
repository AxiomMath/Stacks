module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfUnderlyingAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# Restriction of scalars preserves constructibility

Let `ρ : R →+* Λ` be a ring homomorphism, `Λ` finite. Restricting the scalars of a sheaf of
`Λ`-modules on the small étale site of a scheme along `ρ` carries constructible sheaves of
`Λ`-modules to constructible sheaves of `R`-modules: on the strata of a constructible
stratification on which the sheaf is locally constant with finitely generated values `E`, its
restriction is locally constant with values the restrictions of `E`, which are finite sets.

This is the direction of the comparison of constructibility over `Λ` and over `ℤ/n` (`n` the
characteristic of `Λ`) that carries hypotheses on `D_ctf(X_étale, Λ)` to the constructibility
statements over the commutative ring `ℤ/n`, such as Tag 0GL0, for the finite, possibly
noncommutative, coefficient rings of the trace formula (Tag 03SZ).

## Main results

* `Stacks.ConstantSheaf.isLocallyConstantWith_restrictScalars`: local constancy passes to the
  restriction of scalars, on any site.
* `AlgebraicGeometry.restrictScalarsSheafPullbackIso`: inverse image along base change on the
  small étale sites of Tag 021B commutes with restriction of scalars.
* `AlgebraicGeometry.isConstructibleModuleSheaf_restrictScalars`: **restriction of scalars from
  a finite ring preserves constructibility.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w c v u

namespace Stacks.ModuleSheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) {R Λ : Type} [Ring R]
  [Ring Λ] (ρ : R →+* Λ)

/-- The restriction of scalars along `ρ` of a sheaf of modules is a sheaf. -/
public theorem hasSheafCompose_restrictScalars_of_ring :
    J.HasSheafCompose (ModuleCat.restrictScalars.{w} ρ) :=
  hasSheafCompose_of_preservesLimitsOfSize (J := J) (F := ModuleCat.restrictScalars.{w} ρ)

/-- **Restriction of scalars commutes with sheafification.** -/
public theorem preservesSheafification_restrictScalars [UnivLE.{max c v, w}] :
    J.PreservesSheafification (ModuleCat.restrictScalars.{w} ρ) := by
  have hlim : HasLimitsOfSize.{max c v, max c v} (ModuleCat.{w} Λ) := ModuleCat.hasLimitsOfSize
  have hlim' : HasLimitsOfSize.{max c v, max c v} (ModuleCat.{w} R) := ModuleCat.hasLimitsOfSize
  have hsc := hasSheafCompose_restrictScalars_of_ring.{w} J ρ
  have hR : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget (ModuleCat.{w} R)) :=
    fun Y => preservesColimitsOfShape_forget_moduleCat R J Y
  have hM : ∀ Y : C, PreservesColimitsOfShape (J.Cover Y)ᵒᵖ (forget (ModuleCat.{w} Λ)) :=
    fun Y => preservesColimitsOfShape_forget_moduleCat Λ J Y
  exact GrothendieckTopology.instPreservesSheafification J (ModuleCat.restrictScalars.{w} ρ)

end Stacks.ModuleSheaf

namespace Stacks.ConstantSheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) {R Λ : Type} [Ring R]
  [Ring Λ] (ρ : R →+* Λ) [UnivLE.{max c v, w}]

/-- **Local constancy passes to the restriction of scalars.** If a sheaf of `Λ`-modules is, on a
covering of every object, constant with values satisfying `Q`, its restriction of scalars along
`ρ` is, on the same coverings, constant with values the restrictions of scalars of those values. -/
public theorem isLocallyConstantWith_restrictScalars
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} Λ)]
    [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} R)]
    (Q : ModuleCat.{w} Λ → Prop) (F : Sheaf J (ModuleCat.{w} Λ))
    (hF : IsLocallyConstantWith Λ J Q F) :
    IsLocallyConstantWith R J
      (fun E' => ∃ E : ModuleCat.{w} Λ, Q E ∧ Nonempty ((ModuleCat.restrictScalars ρ).obj E ≅ E'))
      ((sheafCompose J (ModuleCat.restrictScalars.{w} ρ)).obj F) := by
  intro U
  obtain ⟨I, V, f, hcover, hloc⟩ := hF U
  refine ⟨I, V, f, hcover, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hloc i
  have : (J.over (V i)).HasSheafCompose (ModuleCat.restrictScalars.{w} ρ) :=
    Stacks.ModuleSheaf.hasSheafCompose_restrictScalars_of_ring.{w} (J.over (V i)) ρ
  have : (J.over (V i)).PreservesSheafification (ModuleCat.restrictScalars.{w} ρ) :=
    Stacks.ModuleSheaf.preservesSheafification_restrictScalars.{w} (J.over (V i)) ρ
  refine ⟨(ModuleCat.restrictScalars ρ).obj E, ⟨E, hE, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  exact (constantCommuteCompose (J.over (V i)) (ModuleCat.restrictScalars.{w} ρ)).symm.app E ≪≫
    (sheafCompose (J.over (V i)) (ModuleCat.restrictScalars.{w} ρ)).mapIso e

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {R Λ : Type} [Ring R] [Ring Λ] (ρ : R →+* Λ)

/-- Weak sheafification on the localizations of a small étale site at the coefficient universe
`u + 1`, for a ring in `Type`. -/
theorem hasWeakSheafify_over_moduleCat_type (A : Type) [Ring A] (T : B.Scheme)
    (V : SmallEtale B T.obj T.property) :
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} A) :=
  SmallEtale.hasWeakSheafify_over_moduleCat_ring.{u, 0} B A T V

/-- Direct image between small étale sites is a right adjoint at the coefficient universe
`u + 1`, for a ring in `Type`. -/
theorem isRightAdjoint_smallEtalePushforward_moduleCat_type (A : Type) [Ring A] (S T : B.Scheme)
    (g : T ⟶ S) :
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{u + 1} A)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring.{u, 0} B A S T g

attribute [local instance high] hasWeakSheafify_over_moduleCat_type
  isRightAdjoint_smallEtalePushforward_moduleCat_type

/-- **Inverse image along base change on the sites of Tag 021B commutes with restriction of
scalars.** -/
public def restrictScalarsSheafPullbackIso {S T : B.Scheme} (f : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)) :
    ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} R)
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj
        ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).obj F) ≅
      (sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).obj
        (((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F) :=
  haveI := Stacks.ModuleSheaf.hasSheafCompose_restrictScalars_of_ring.{u + 1}
    (SmallEtale.topology B S.obj S.property) ρ
  haveI := Stacks.ModuleSheaf.hasSheafCompose_restrictScalars_of_ring.{u + 1}
    (SmallEtale.topology B T.obj T.property) ρ
  haveI := Stacks.ModuleSheaf.preservesSheafification_restrictScalars.{u + 1}
    (SmallEtale.topology B T.obj T.property) ρ
  asIso ((Stacks.EtaleCohomology.coefficientSheafPullbackTwoSquare (smallEtaleBaseChange B f)
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (ModuleCat.restrictScalars.{u + 1} ρ)).app F)

/-- **Restriction of scalars from a finite ring preserves constructibility.** For a ring
homomorphism `ρ : R →+* Λ` with `Λ` finite and a constructible sheaf `F` of `Λ`-modules on the
small étale site of `X`, the sheaf of `R`-modules obtained by restricting scalars along `ρ` is
constructible. -/
public theorem isConstructibleModuleSheaf_restrictScalars [Finite Λ] (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ F) :
    IsConstructibleModuleSheaf B X R
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  refine ⟨s, fun i ↦ ?_⟩
  have h := Stacks.ConstantSheaf.isLocallyConstantWith_restrictScalars
    (SmallEtale.topology B (s.piece i).obj (s.piece i).property) ρ
    (fun E : ModuleCat.{u + 1} Λ => ModuleCat.isFG Λ E) _ (hs i)
  have hmono : ∀ E' : ModuleCat.{u + 1} R,
      (∃ E : ModuleCat.{u + 1} Λ, ModuleCat.isFG Λ E ∧
        Nonempty ((ModuleCat.restrictScalars ρ).obj E ≅ E')) → ModuleCat.isFG R E' := by
    rintro E' ⟨E, hE, ⟨e⟩⟩
    rw [ModuleCat.isFG_iff] at hE ⊢
    have : Finite E := Module.finite_of_finite Λ
    have : Finite ((ModuleCat.restrictScalars ρ).obj E) := (inferInstance : Finite E)
    have : Finite E' := Finite.of_equiv _ e.toLinearEquiv.toEquiv
    exact Module.Finite.of_finite
  have h' : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant R
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} ρ)).obj
        (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)) := by
    intro V
    obtain ⟨I, W, f, hcov, hloc⟩ := h V
    exact ⟨I, W, f, hcov, fun j => let ⟨E', hE', he⟩ := hloc j; ⟨E', hmono E' hE', he⟩⟩
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ R
    (restrictScalarsSheafPullbackIso B ρ (s.inclusion i) F).symm h'

end AlgebraicGeometry

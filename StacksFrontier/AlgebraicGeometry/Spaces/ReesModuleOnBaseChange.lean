module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSpectrumBaseChangeSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness

/-!
# The Rees module on the base change to the spectrum of an algebra map

Let `f : X ⟶ h_T` with `T` affine, `φ : R →ₐ[A] R'` a map of finitely generated `A`-algebras,
`π : X_R ⟶ X`, `π' : X_{R'} ⟶ X` the base changes and `ψ : X_{R'} ⟶ X_R` the induced morphism.
For an `𝒪_X`-module `F` the module of the proof of [Stacks, Tag 08AW] is the image of

`π^*F ⟶ ψ_*ψ^*π^*F ≅ ψ_*π'^*F`,

the unit of `ψ^* ⊣ ψ_*`.  For the Rees embedding `A[Jt] ⊆ A[s]` its direct image to `X` is the
Rees module `⨁ Iⁿ F`.

## Main definitions

* `AlgebraicGeometry.Space.algebraImageModule`: the image module on `X_R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)
  (R : Type u) [CommRing R] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
  (R' : Type u) [CommRing R'] [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
  (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R')

/-- The unit `π^*F ⟶ ψ_*ψ^*π^*F`. -/
def algebraImageUnit (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (algebraBaseChangeProjection B S hS T f R)).obj F ⟶
      (modulePushforward B S hS (algebraBaseChangeMap B S hS T f R R' φ)).obj
        ((modulePullback B S hS (algebraBaseChangeMap B S hS T f R R' φ)).obj
          ((modulePullback B S hS (algebraBaseChangeProjection B S hS T f R)).obj F)) :=
  (modulePullbackAdjunction B S hS (algebraBaseChangeMap B S hS T f R R' φ)).unit.app _

/-- **The image module** `im(π^*F ⟶ ψ_*ψ^*π^*F)` on `X_R`. -/
def algebraImageModule (F : Modules.{u, u} B S hS X.1 X.2) :
    Modules.{u, u} B S hS (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2 :=
  Limits.image (algebraImageUnit B S hS T f R R' φ F)

/-- `ψ : X_{R'} ⟶ X_R` is affine: it is the base change of `Spec R' ⟶ Spec R`. -/
theorem isAffineHom_algebraBaseChangeMap :
    IsAffineHom B S hS (algebraBaseChangeMap B S hS T f R R' φ).hom :=
  isAffineHom_of_isPullback' B S hS (isPullback_algebraBaseChangeMap B S hS T f R R' φ).flip
    (isAffineHom_yoneda_map B S hS (algebraSpectrumSiteMap B S hS T R R' φ))

/-- The factorization map `π^*F ⟶ im(π^*F ⟶ ψ_*ψ^*π^*F)` is an epimorphism. -/
private theorem epi_factorThruImage_algebraImageUnit (F : Modules.{u, u} B S hS X.1 X.2) :
    Epi (factorThruImage (algebraImageUnit B S hS T f R R' φ F)) :=
  ⟨fun _ _ w => image.ext _ w⟩

/-- **The image module is quasi-coherent** for a quasi-coherent `F`. -/
theorem isQuasicoherentOnSite_algebraImageModule (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    (algebraImageModule B S hS T f R R' φ F).IsQuasicoherentOnSite := by
  have h1 := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (algebraBaseChangeProjection B S hS T f R) F hF
  have h2 := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (algebraBaseChangeMap B S hS T f R R' φ) _ h1
  have h3 := isQuasicoherentOnSite_modulePushforward_of_isAffineHom_unconditional B S hS
    (algebraBaseChangeMap B S hS T f R R' φ) (isAffineHom_algebraBaseChangeMap B S hS T f R R' φ)
    _ h2
  exact isQuasicoherentOnSite_image_unconditional B S hS _ _ (algebraImageUnit B S hS T f R R' φ F)
    h1 h3

/-- **The image module is coherent** for a coherent `F` on a locally Noetherian `X_R`: it is
quasi-coherent and a quotient of `π^*F`, which is of finite type. -/
theorem isCoherent_algebraImageModule
    (hN : HasEtaleLocalProperty B S hS (algebraBaseChange B S hS T f R).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    IsCoherent B S hS (algebraBaseChange B S hS T f R).1 (algebraBaseChange B S hS T f R).2
      (algebraImageModule B S hS T f R R' φ F) := by
  have : Fact (HasEtaleLocalProperty B S hS (algebraBaseChange B S hS T f R).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hN⟩
  have : SheafOfModules.IsCoherentOnSite F := hF.toIsCoherentOnSite
  have hFt := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X F
  have h1 :=
    isFiniteTypeOnSite_modulePullback B S hS (algebraBaseChangeProjection B S hS T f R) F hFt
  have h2 : SheafOfModules.IsFiniteTypeOnSite (algebraImageModule B S hS T f R R' φ F) :=
    @isFiniteTypeOnSite_of_epi B S hS _ _ _ _
      (factorThruImage (algebraImageUnit B S hS T f R R' φ F))
      (epi_factorThruImage_algebraImageUnit B S hS T f R R' φ F) h1
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS _ _ _).2
    ⟨isQuasicoherentOnSite_algebraImageModule B S hS T f R R' φ F hF.toIsQuasicoherentOnSite,
      Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _ h2⟩

/-- **The direct image along the affine `π` of the image factorization is an epi-mono
factorization**: `π_*` preserves epimorphisms of quasi-coherent modules
(`AlgebraicGeometry.Space.epi_modulePushforward_map_of_isAffineHom`) and, being a right adjoint,
monomorphisms.  So `π_*` of the image module is the image of `π_*` of the unit. -/
theorem epi_mono_modulePushforward_algebraImageModule (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) :
    Epi ((modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
        (factorThruImage (algebraImageUnit B S hS T f R R' φ F))) ∧
      Mono ((modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)).map
        (image.ι (algebraImageUnit B S hS T f R R' φ F))) := by
  have h1 := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (algebraBaseChangeProjection B S hS T f R) F hF
  have hG := isQuasicoherentOnSite_algebraImageModule B S hS T f R R' φ F hF
  refine ⟨@epi_modulePushforward_map_of_isAffineHom B S hS _ _
    (algebraBaseChangeProjection B S hS T f R)
    (isAffineHom_algebraBaseChangeProjection B S hS T f R) _ _ h1 hG _
    (epi_factorThruImage_algebraImageUnit B S hS T f R R' φ F), ?_⟩
  have : PreservesLimitsOfSize.{0, 0}
      (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)) :=
    (modulePullbackAdjunction B S hS
      (algebraBaseChangeProjection B S hS T f R)).rightAdjoint_preservesLimits
  have : PreservesLimitsOfShape WalkingCospan
      (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R)) :=
    PreservesLimitsOfSize.preservesLimitsOfShape
  exact @Functor.map_mono _ _ _ _
    (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f R))
    (preservesMonomorphisms_of_preservesLimitsOfShape _) _ _
    (image.ι (algebraImageUnit B S hS T f R R' φ F)) inferInstance

end AlgebraicGeometry.Space

end

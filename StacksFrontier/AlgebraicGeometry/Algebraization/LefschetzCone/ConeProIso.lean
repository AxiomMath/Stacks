module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConeAlgebraization
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.TildeTorsionIso
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.NoetherianCoherent
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantNoetherianCompletion

/-!
# The cone system as the sheaves of the twisted sections, and pro-isomorphisms

For an object `(ℱₙ)` of `Coh(X, 𝓘)` the object `(ℱ_U,ₙ)` of `Coh(U, f𝒪_U)` on the punctured cone
(`Stacks.LefschetzCone.coneSystem`) is built from `Γ_*(X, L, ℱₙ) / fⁿ⁺¹`; since `fⁿ⁺¹Γ_*(X, L, ℱₙ)`
is `A₊`-power torsion, it is also `Ψ(ℱₙ) = Γ_*(X, L, ℱₙ)~|_U` (`coneSystemIso`). As `Ψ` is a
functor, a pro-isomorphism of `(ℱₙ)` with an inverse system `(ℱ''ₙ)` of `𝒪_X`-modules gives one of
`(ℱ_U,ₙ)` with `(Ψ(ℱ''ₙ))`, which is the input of Stacks 0EJI in the proof of Stacks 0EL5.

## Main definitions

* `Stacks.LefschetzCone.coneFunctor`: `Ψ : G ↦ Γ_*(X, L, G)~|_U`.
* `Stacks.LefschetzCone.coneSystemIso`: `(ℱ_U,ₙ) ≅ (Ψ(ℱₙ))`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open scoped Stacks.GradedLocalization Pointwise

universe u

namespace Stacks.LefschetzCone

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local instance] ProjectiveSpectrum.isPrime

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)] (s : Γ(L, ⊤))
  [IsNoetherianRing (sectionRing L)] [IsLocallyNoetherian X]

/-- **`Ψ : G ↦ Γ_*(X, L, G)~|_U`**, from `𝒪_X`-modules to modules on the punctured cone. -/
abbrev coneFunctor : X.Modules ⥤ (coneSituation L s).U.toScheme.Modules :=
  Stacks.SectionRingProjQuasicoherent.gradedTwistedSectionsFunctor L ⋙
    GradedModuleCat.toModuleCat (grading L) ⋙ tilde.functor (CommRingCat.of (coneSituation L s).A) ⋙
      Scheme.Modules.restrictFunctor (coneSituation L s).U.ι

/-- `Ψ(G)` is coherent when `Γ_*(X, L, G)` is a finite module. -/
theorem isCoherent_coneFunctor_obj (G : X.Modules)
    (hG : Module.Finite (sectionRing L) (Stacks.TwistedSections.twistModule G L)) :
    ((coneFunctor L s).obj G).IsCoherent := by
  let M : ModuleCat.{u} (CommRingCat.of (coneSituation L s).A) :=
    ModuleCat.of _ (Stacks.TwistedSections.twistModule G L)
  have : Module.Finite (CommRingCat.of (coneSituation L s).A) M := hG
  have : SheafOfModules.IsFiniteType.{u, u, u} (tilde M) :=
    (AlgebraicGeometry.tilde_isFiniteType_iff M).mpr inferInstance
  exact AlgebraicGeometry.isCoherent_restrict_of_isOpenImmersion (coneSituation L s).U.ι _
    (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent'_of_isQuasicoherent_of_isFiniteType
      (tilde M))

/-- The projections `Tₙ ⟶ Tₙ / fⁿ⁺¹ Tₙ`, as a map of inverse systems. -/
def truncatedSystemπ (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L)) :
    T ⟶ truncatedSystem L s T where
  app n := powQuotientπ L s (T.obj n) (n.unop + 1)
  naturality _ _ _ := GradedModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- **`fⁿ⁺¹ Tₙ` is `A₊`-power torsion**, for `(Tₙ)` whose sheaves on `X` form a coherent adic
system along the zero scheme of `s`. -/
theorem isIPowerTorsion_ker_powQuotientπ (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL)) (n : ℕ) :
    IsIPowerTorsion (sectionRing L)
      (LinearMap.ker (powQuotientπ L s (T.obj (op n)) (n + 1)).toLinearMap)
      (HomogeneousIdeal.irrelevant (grading L)).toIdeal := by
  refine Stacks.DegreeOneUnitAway.isIPowerTorsion_of_forall_pow_smul _
    (IsNoetherian.noetherian _) _ (exists_mem_range_gR_notMem L hL) fun x g hg => ?_
  obtain ⟨ch, rfl⟩ := hg
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Ideal.span {sectionElt L s} ^ (n + 1) •
      (⊤ : Submodule (sectionRing L) (T.obj (op n)).carrier) := by
    have hx2 : (Submodule.Quotient.mk x : (T.obj (op n)).carrier ⧸
        (Ideal.span {sectionElt L s} ^ (n + 1) •
          (⊤ : Submodule (sectionRing L) (T.obj (op n)).carrier))) = 0 := hx
    rwa [Submodule.Quotient.mk_eq_zero] at hx2
  obtain ⟨y, rfl⟩ := (Stacks.DegreeOneUnitAway.mem_span_pow_smul_top_iff (n + 1) _).1 hx'
  obtain ⟨p, hp⟩ := Stacks.DegreeOneUnitAway.exists_pow_smul_pow_smul_eq_zero
    (𝓜 := (T.obj (op n)).grade) ch.cR_mem ch.bR_mem ch.cR_mul_bR (sectionElt_mem L s) (n + 1)
    (fun z hz => congrArg Subtype.val
      (chartRatio_pow_smul_eq_zero L hL s (T.obj (op n)) (n + 1) (hT.idealPowerMultiple_eq_bot n)
        ch ⟨z, hz⟩)) y
  exact ⟨p, Subtype.ext hp⟩

/-- The points of the punctured cone lie off `V(A₊)`. -/
theorem not_irrelevant_le_coneSituation (y : (coneSituation L s).U.toScheme) :
    ¬ (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤
      ((coneSituation L s).U.ι.base y).asIdeal :=
  y.2

/-- The presentation of the cone system by the truncated twisted sections. -/
def coneSystemPresIso (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s))
    (hfin : ∀ n : ℕ, Module.Finite (sectionRing L)
      (Stacks.TwistedSections.twistModule (F.obj.obj (op n)) L)) :
    (coneSystem L hL s F hfin).obj ≅
      truncatedSystem L s (twistedSectionsSystem L F.obj (isCoherent_obj L s F)) ⋙
        (GradedModuleCat.toModuleCat (grading L) ⋙
          tilde.functor (CommRingCat.of (coneSituation L s).A) ⋙
            Scheme.Modules.restrictFunctor (coneSituation L s).U.ι) :=
  (Iso.refl _ : (coneSystem L hL s F hfin).obj ≅
      (truncatedSystem L s (twistedSectionsSystem L F.obj (isCoherent_obj L s F)) ⋙
        GradedModuleCat.toModuleCat (grading L)) ⋙
          (tilde.functor (CommRingCat.of (coneSituation L s).A) ⋙
            Scheme.Modules.pullback (coneSituation L s).U.ι)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Scheme.Modules.restrictFunctorIsoPullback (coneSituation L s).U.ι).symm))

/-- `Ψ(Tₙ) ⟶ Ψ(Tₙ / fⁿ⁺¹ Tₙ)` is an isomorphism. -/
theorem isIso_coneMap_powQuotientπ (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL)) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (coneSituation L s).U.ι).map
      (tilde.map ((GradedModuleCat.toModuleCat (grading L)).map
        (powQuotientπ L s (T.obj (op n)) (n + 1))))) :=
  isIso_restrict_tilde_map_of_isIPowerTorsion_ker (R := CommRingCat.of (coneSituation L s).A) _
    (HomogeneousIdeal.irrelevant (grading L)).toIdeal (coneSituation L s).U
    (not_irrelevant_le_coneSituation L s) (Submodule.mkQ_surjective _)
    (isIPowerTorsion_ker_powQuotientπ L hL s T hT n)

/-- `Ψ` inverts the projections onto the truncations. -/
theorem isIso_whiskerRight_truncatedSystemπ (T : ℕᵒᵖ ⥤ GradedModuleCat.{u, u, u} (grading L))
    (hT : Stacks.Coherent.IsCoherentAdicSystem (zeroScheme X L s)
      (T ⋙ restrictedTildeFunctor L hL)) :
    IsIso (Functor.whiskerRight (truncatedSystemπ L s T)
      (GradedModuleCat.toModuleCat (grading L) ⋙
          tilde.functor (CommRingCat.of (coneSituation L s).A) ⋙
            Scheme.Modules.restrictFunctor (coneSituation L s).U.ι)) :=
  @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n => isIso_coneMap_powQuotientπ L hL s T hT n.unop

/-- **`(ℱ_U,ₙ) ≅ (Ψ(ℱₙ))`**: the cone system is the system of the sheaves on the punctured cone of
the twisted sections. -/
def coneSystemIso (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s))
    (hfin : ∀ n : ℕ, Module.Finite (sectionRing L)
      (Stacks.TwistedSections.twistModule (F.obj.obj (op n)) L)) :
    (coneSystem L hL s F hfin).obj ≅ F.obj ⋙ coneFunctor L s :=
  coneSystemPresIso L hL s F hfin ≪≫
    (@asIso _ _ _ _ _ (isIso_whiskerRight_truncatedSystemπ L hL s _
      (isCoherentAdicSystem_twistedSectionsSystem L hL s F))).symm ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (ObjectProperty.liftCompιIso _ _ _) _

/-- **A pro-isomorphism `(ℱ''ₙ) ≅ (ℱₙ)` gives one `(ℱ_U,ₙ) ≅ (Ψ(ℱ''ₙ))`.** -/
def coneSystemProIso (F : Stacks.Coherent.CoherentAdicSystems (zeroScheme X L s))
    (hfin : ∀ n : ℕ, Module.Finite (sectionRing L)
      (Stacks.TwistedSections.twistModule (F.obj.obj (op n)) L))
    (G : ℕᵒᵖ ⥤ X.Modules) (e : InverseSequence.ProIso G F.obj) :
    InverseSequence.ProIso (coneSystem L hL s F hfin).obj (G ⋙ coneFunctor L s) :=
  (InverseSequence.ProIso.ofNatIso (coneSystemIso L hL s F hfin)).trans
    (e.whiskerRight (coneFunctor L s)).symm

end Monoidal

end Stacks.LefschetzCone

end

module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ConsecutiveCharts
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.SubmoduleBasis
public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzCone.ProjSide
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections

/-!
# The sheaves of the adic quotients of a graded module are a completion

Let `X` be a scheme with an ample invertible `𝒪_X`-module `L` for which the canonical morphism
`f : X ⟶ Proj A`, `A = Γ_*(X, L)`, is an isomorphism, let `s` be a global section of `L`, `f ∈ A₁`
its image in degree one, and `𝓘` the ideal sheaf of the zero scheme of `s`. For a graded
`A`-module `N` the sheaf associated to `N / fᵏ N` is the quotient of the sheaf associated to `N` by
`𝓘ᵏ`:

`(N / fᵏN)~|_X = Ñ|_X / 𝓘ᵏ Ñ|_X`.

On a chart `X_{cb}` of consecutive degrees both sides are computed in the degree-zero localization
`N₍cb₎`: the left-hand kernel is `wᵏ N₍cb₎` by `Stacks.DegreeOneUnitAway.map_mkQ_eq_zero_iff`, and
the right-hand submodule is `𝓘(X_{cb})ᵏ N₍cb₎ = wᵏ N₍cb₎` because `𝓘` is generated there by the
chart ratio `w`. These charts form a basis, and a submodule of a sheaf of modules is determined on
a basis.

Consequently the system `(N / fⁿ⁺¹N)~|_X` is the completion of `Ñ|_X` along `𝓘`, which is what the
graded algebraization of Stacks 0EL4 needs on the projective side in the proof of Stacks 0EL5.

## Main results

* `Stacks.LefschetzCone.ker_eq_idealPowerMultiple`: the kernel of `Ñ|_X → (N / fᵏ N)~|_X` is
  `𝓘ᵏ Ñ|_X`.
* `Stacks.LefschetzCone.adicQuotientsIsoCompletion`: `(N / fⁿ⁺¹N)~|_X` is the completion of
  `Ñ|_X`, as inverse systems.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
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
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  (hL : Stacks.Ample.IsAmple X L) [IsIso (projHomOfIsAmple L hL)] (s : Γ(L, ⊤))

omit [Stacks.Ample.IsInvertibleModule X L] [IsIso (projHomOfIsAmple L hL)] in
/-- Membership in `(r) • ⊤`. -/
theorem mem_span_singleton_smul_top_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (x : M) :
    x ∈ Ideal.span {r} • (⊤ : Submodule R M) ↔ ∃ y : M, r • y = x := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- The section `s`, read in degree one of the section ring. -/
abbrev sectionElt : sectionRing L := DirectSum.of (powSections L) 1 (degreeOneSection L s)

/-- The element `sectionElt L s` is homogeneous of degree one. -/
theorem sectionElt_mem : sectionElt L s ∈ grading L 1 :=
  Stacks.ExternalGrading.of_mem_summand _ _

/-- The ideal `(f)` of the section ring is homogeneous. -/
public theorem isHomogeneous_span_sectionElt :
    (Ideal.span {sectionElt L s}).IsHomogeneous (grading L) :=
  Ideal.homogeneous_span _ _ (by
    rintro x rfl
    exact ⟨1, sectionElt_mem L s⟩)

/-- The submodule `fᵏ N` of a graded module is homogeneous. -/
public theorem isHomogeneous_span_pow_smul_top (N : GradedModuleCat.{u, u, u} (grading L))
    (k : ℕ) :
    (Ideal.span {sectionElt L s} ^ k • (⊤ : Submodule (sectionRing L) N.carrier)).IsHomogeneous
      N.grade :=
  Submodule.isHomogeneous_smul_top (grading L) N.grade
    (fun _ _ _ _ ha hx => GradedModuleCat.smul_mem_grade (grading L) N ha hx)
    ((isHomogeneous_span_sectionElt L s).pow (grading L) _)

/-- The projection `N ⟶ N / fᵏ N` of graded modules. -/
abbrev powQuotientπ (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ) :
    N ⟶ GradedModuleCat.quotient (grading L) N
      (Ideal.span {sectionElt L s} ^ k • (⊤ : Submodule (sectionRing L) N.carrier))
      (isHomogeneous_span_pow_smul_top L s N k) :=
  GradedModuleCat.quotientπ (grading L) N _ _

/-- The quotient `N / fᵏ N`, as a graded module. -/
abbrev powQuotient (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ) :
    GradedModuleCat.{u, u, u} (grading L) :=
  GradedModuleCat.quotient (grading L) N
    (Ideal.span {sectionElt L s} ^ k • (⊤ : Submodule (sectionRing L) N.carrier))
    (isHomogeneous_span_pow_smul_top L s N k)

/-- **On a chart, `Ñ|_X ⟶ (N / fᵏN)~|_X` kills a section exactly when it is `eᵏ` times a section**,
`e` the local equation of the zero scheme of `s`. -/
public theorem map_powQuotientπ_app_eq_zero_iff (N : GradedModuleCat.{u, u, u} (grading L))
    (k : ℕ) (ch : ConsecutiveChart L) (x : Γ(restrictedTilde L hL N, ch.nv)) :
    ((restrictedTildeFunctor L hL).map (powQuotientπ L s N k)).app ch.nv x = 0 ↔
      ∃ y : Γ(restrictedTilde L hL N, ch.nv), Stacks.SectionRingChartMap.chartRingMap L ch.prod
        le_rfl ((Stacks.DegreeOneUnitAway.chartRatio ch.cR_mem ch.bR_mem ch.cR_mul_bR
          (sectionElt_mem L s)) ^ k) • y = x := by
  set w := (Stacks.DegreeOneUnitAway.chartRatio ch.cR_mem ch.bR_mem ch.cR_mul_bR
    (sectionElt_mem L s)) ^ k
  set e := chartSectionsOf L hL N ch.prod ch.deg_pos with he
  have hchart : ∀ y : Γ(restrictedTilde L hL N, ch.nv),
      e (Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl w • y) = w • e y :=
    fun y => chartSectionsOf_smul L hL N ch.prod ch.deg_pos w y
  have hmap : ((restrictedTildeFunctor L hL).map (powQuotientπ L s N k)).app ch.nv x = 0 ↔
      LocalizedModule.map (Submonoid.powers ch.gR)
        (powQuotientπ L s N k).toLinearMap
        (e x : LocalizedModule.Away ch.gR N.carrier) = 0 := by
    rw [he, ← coe_chartSectionsOf_map L hL (powQuotientπ L s N k) ch.prod ch.deg_pos x]
    refine ⟨fun h => by rw [h, map_zero, Submodule.coe_zero], fun h => ?_⟩
    exact (chartSectionsOf L hL (powQuotient L s N k) ch.prod ch.deg_pos).injective
      ((Subtype.ext h).trans (map_zero _).symm)
  refine (hmap.trans (Stacks.DegreeOneUnitAway.map_mkQ_eq_zero_iff ch.cR_mem ch.bR_mem
    ch.cR_mul_bR (sectionElt_mem L s) k (e x).2)).trans ?_
  constructor
  · rintro ⟨z', hz', hzx⟩
    obtain ⟨y, hy⟩ := e.surjective ⟨z', hz'⟩
    refine ⟨y, e.injective ?_⟩
    rw [hchart, hy]
    exact Subtype.ext hzx.symm
  · rintro ⟨y, rfl⟩
    refine ⟨_, (e y).2, ?_⟩
    rw [hchart]
    rfl

/-- **The kernel of `Ñ|_X ⟶ (N / fᵏN)~|_X` is `𝓘ᵏ Ñ|_X`**, `𝓘` the ideal sheaf of the zero scheme
of `s`. -/
public theorem ker_eq_idealPowerMultiple (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ) :
    SheafOfModules.Submodule.ker ((restrictedTildeFunctor L hL).map (powQuotientπ L s N k)) =
      Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k (restrictedTilde L hL N) := by
  have := isQuasicoherent_restrictedTilde L hL N
  refine submodule_eq_of_isBasis (isBasis_consecutiveChart L hL) fun ch => ?_
  have hR : (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
      (restrictedTilde L hL N)).obj (op ch.nv) =
      Ideal.span {Stacks.SectionRingChartMap.chartRingMap L ch.prod le_rfl
        ((Stacks.DegreeOneUnitAway.chartRatio ch.cR_mem ch.bR_mem ch.cR_mul_bR
          (sectionElt_mem L s)) ^ k)} •
        (⊤ : Submodule Γ(X, ch.nv) Γ(restrictedTilde L hL N, ch.nv)) := by
    rw [show (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
        (restrictedTilde L hL N)).obj (op ch.nv) =
        (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
          (restrictedTilde L hL N)).toSubmodule.obj (op (ch.affineOpen hL).1) from rfl,
      Stacks.Algebraization.idealPowerMultiple_toSubmodule_obj_affine,
      zeroScheme_ideal_consecutiveChart L hL s ch, Ideal.span_singleton_pow, map_pow]
  refine SetLike.ext fun (x : Γ(restrictedTilde L hL N, ch.nv)) => ?_
  rw [hR]
  exact (map_powQuotientπ_app_eq_zero_iff L hL s N k ch x).trans
    (mem_span_singleton_smul_top_iff _ x).symm

/-- The map `Ñ|_X ⟶ (N / fᵏN)~|_X` is an epimorphism. -/
public instance epi_map_powQuotientπ (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ) :
    Epi ((restrictedTildeFunctor L hL).map (powQuotientπ L s N k)) := by
  haveI : Epi ((Stacks.SectionRingProjQuasicoherent.associatedSchemeFunctor L).map
      (powQuotientπ L s N k)) :=
    epi_map_associatedModuleSheafFunctor (grading L) _ (Submodule.mkQ_surjective _)
  exact (inferInstance : (Scheme.Modules.restrictFunctor
    (projHomOfIsAmple L hL)).PreservesEpimorphisms).preserves _

/-- **`(N / fᵏN)~|_X ≅ Ñ|_X / 𝓘ᵏ Ñ|_X`**, compatibly with the projections from `Ñ|_X`. -/
public def powQuotientIso (N : GradedModuleCat.{u, u, u} (grading L)) (k : ℕ) :
    restrictedTilde L hL (powQuotient L s N k) ≅
      Stacks.Algebraization.idealPowerQuotient (zeroScheme X L s) k (restrictedTilde L hL N) :=
  (cokernelIsoOfEqKer _ _ (ker_eq_idealPowerMultiple L hL s N k).symm).symm

/-- The projection `Ñ|_X ⟶ (N / fᵏN)~|_X` followed by `powQuotientIso` is the cokernel projection
`Ñ|_X ⟶ Ñ|_X / 𝓘ᵏ Ñ|_X`. -/
@[reassoc]
public theorem map_powQuotientπ_powQuotientIso_hom (N : GradedModuleCat.{u, u, u} (grading L))
    (k : ℕ) :
    (restrictedTildeFunctor L hL).map (powQuotientπ L s N k) ≫ (powQuotientIso L hL s N k).hom =
      cokernel.π (Stacks.Algebraization.idealPowerMultiple (zeroScheme X L s) k
        (restrictedTilde L hL N)).ι :=
  (Iso.comp_inv_eq _).2 (cokernelIsoOfEqKer_hom _ _ _).symm

/-- The inverse system `(N / fⁿ⁺¹N)~|_X` of `𝒪_X`-modules. -/
abbrev adicQuotientSheaves (N : GradedModuleCat.{u, u, u} (grading L)) : ℕᵒᵖ ⥤ X.Modules :=
  GradedModuleCat.adicQuotients (grading L) N (Ideal.span {sectionElt L s})
    (isHomogeneous_span_sectionElt L s) ⋙ restrictedTildeFunctor L hL

/-- The projections `Ñ|_X ⟶ (N / fⁿ⁺¹N)~|_X`. -/
abbrev adicQuotientSheavesπ (N : GradedModuleCat.{u, u, u} (grading L)) (n : ℕ) :
    restrictedTilde L hL N ⟶ (adicQuotientSheaves L hL s N).obj (op n) :=
  (restrictedTildeFunctor L hL).map (GradedModuleCat.adicQuotientsπ (grading L) N
    (Ideal.span {sectionElt L s}) (isHomogeneous_span_sectionElt L s) n)

/-- The projections `Ñ|_X ⟶ (N / fⁿ⁺¹N)~|_X` commute with the transition maps of the inverse
system `(N / fⁿ⁺¹N)~|_X`. -/
theorem adicQuotientSheavesπ_map (N : GradedModuleCat.{u, u, u} (grading L)) {m n : ℕᵒᵖ}
    (f : m ⟶ n) :
    adicQuotientSheavesπ L hL s N m.unop ≫ (adicQuotientSheaves L hL s N).map f =
      adicQuotientSheavesπ L hL s N n.unop :=
  ((restrictedTildeFunctor L hL).map_comp _ _).symm.trans
    (congrArg (restrictedTildeFunctor L hL).map (GradedModuleCat.hom_ext rfl))

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The `n`-th projection of the completion of `G` along `J`, followed by the identification of its
`n`-th term with `G / Jⁿ⁺¹ G`, is the cokernel projection `G ⟶ G / Jⁿ⁺¹ G`. -/
theorem completionProjection_comp_eqToHom [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (G : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    Stacks.Algebraization.completionProjection X J G n ≫
        eqToHom (Stacks.Algebraization.completionFunctor_obj X J G n) =
      cokernel.π (Stacks.Algebraization.idealPowerMultiple J (n + 1) G.obj).ι :=
  (Category.assoc _ _ _).trans ((congrArg (fun t => cokernel.π
    (Stacks.Algebraization.idealPowerMultiple J (n + 1) G.obj).ι ≫ t)
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))).trans (Category.comp_id _))

/-- **The adic quotients `(N / fⁿ⁺¹N)~|_X` are the completion of `Ñ|_X` along `𝓘`**, as inverse
systems of `𝒪_X`-modules, for `Ñ|_X` coherent. -/
public def adicQuotientSheavesIsoCompletion [IsLocallyNoetherian X]
    (N : GradedModuleCat.{u, u, u} (grading L)) (hN : (restrictedTilde L hL N).IsCoherent) :
    ((Stacks.Algebraization.completionFunctor X (zeroScheme X L s)).obj
        ⟨restrictedTilde L hL N, hN⟩).obj ≅ adicQuotientSheaves L hL s N :=
  Stacks.Algebraization.completionIsoOfProjections X (zeroScheme X L s)
    ⟨restrictedTilde L hL N, hN⟩ (adicQuotientSheaves L hL s N)
    (fun n => adicQuotientSheavesπ L hL s N n) (fun f => adicQuotientSheavesπ_map L hL s N f)
    (fun n => eqToIso (Stacks.Algebraization.completionFunctor_obj X (zeroScheme X L s)
      ⟨restrictedTilde L hL N, hN⟩ n) ≪≫ (powQuotientIso L hL s N (n + 1)).symm)
    (fun n => (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (powQuotientIso L hL s N (n + 1)).inv)
        (completionProjection_comp_eqToHom (zeroScheme X L s) ⟨restrictedTilde L hL N, hN⟩ n)).trans
        ((Iso.comp_inv_eq _).2 (map_powQuotientπ_powQuotientIso_hom L hL s N (n + 1)).symm)))

/-- **`(N / fⁿ⁺¹N)~|_X` is the completion of `Ñ|_X` along `𝓘`**, in the form of the graded
algebraization through `Φ = (-)~|_X`. -/
public def adicQuotientsIsoCompletion [IsLocallyNoetherian X]
    (N : GradedModuleCat.{u, u, u} (grading L)) (hN : (restrictedTilde L hL N).IsCoherent) :
    (GradedModuleCat.adicQuotients (grading L) N (Ideal.span {sectionElt L s})
        (isHomogeneous_span_sectionElt L s) ⋙ sheafFunctor L hL) ⋙ ObjectProperty.ι _ ≅
      ((Stacks.Algebraization.completionFunctor X (zeroScheme X L s)).obj
        ⟨restrictedTilde L hL N, hN⟩).obj :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
    (adicQuotientSheavesIsoCompletion L hL s N hN).symm

end Monoidal

end Stacks.LefschetzCone

end

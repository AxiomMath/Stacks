module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import StacksFrontier.Algebra.Homology.InverseLimit
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Rlim
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of an inverse limit of complexes on a ringed site

Let `X` be a ringed site and let `(ℱ_n)` be an inverse system of complexes of modules on `X`,
indexed by `ℕ`. Stacks 08CT says that if, on each object of a generating family `B` of the
site, the sections of the system have vanishing `R¹ lim` in degrees `m - 2` and `m - 1` and
in degree `m - 1` cohomology, and if degree-`m` cohomology of the sections is eventually
constant from some stage `n₀` on, then degree-`m` cohomology commutes with the termwise
inverse limit and the limit of the cohomology sheaves is already reached at stage `n₀`.

## Main definitions

* `Stacks.Cohomology.InverseLimits.sectionsComplexFunctor`: a complex of sheaves of modules
  evaluated at an object of the site and regarded as a complex of abelian groups.

## Main results

* `Stacks.Cohomology.InverseLimits.homology_isLimit_of_local_rlim_vanishing`: the canonical
  cone on the degree-`m` cohomology of the termwise inverse limit is a limit cone.
* `Stacks.Cohomology.InverseLimits.homology_limit_projection_isIso_of_local_rlim_vanishing`:
  the projection from the limit of the degree-`m` cohomology sheaves to the stage `n₀` is an
  isomorphism.

## Implementation notes

The generating family is a set `B` of objects of the site satisfying
`GrothendieckTopology.HasEnoughObjects`, which is the covering condition the source uses.
Vanishing of `R¹ lim` is `IsZero` applied to `Rlim.firstDerivedLimit`, and eventual
constancy of cohomology is invertibility of the canonical transition maps. Both conclusions
are stated about the canonical maps — the limit cone and the projection.

The sheaf of rings of a ringed site is `AlgebraicGeometry.RingedSite.ringSheaf`, the
structure sheaf with commutativity forgotten. The universe of module sections is independent
of the universes of the site and of the structure sheaf.

## References

* [Stacks Project, Tag 08CT](https://stacks.math.columbia.edu/tag/08CT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.InverseLimits

universe w v u t

section Sections

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Taking sections of a sheaf of modules over an object of the site and forgetting the
module structure is additive. -/
public instance sections_additive (R : Sheaf J RingCat.{w}) (U : C) :
    (SheafOfModules.evaluation R (op U) ⋙
      forget₂ (ModuleCat.{t} (R.obj.obj (op U))) Ab.{t}).Additive where
  map_add := rfl

/-- The complex of abelian groups of sections of a complex of sheaves of modules over an
object of the site. -/
public abbrev sectionsComplexFunctor (R : Sheaf J RingCat.{w}) (U : C) :
    CochainComplex (SheafOfModules.{t} R) ℤ ⥤ CochainComplex Ab.{t} ℤ :=
  (SheafOfModules.evaluation R (op U) ⋙
    forget₂ (ModuleCat.{t} (R.obj.obj (op U))) Ab.{t}).mapHomologicalComplex
      (ComplexShape.up ℤ)

end Sections

attribute [local instance] HasDerivedCategory.standard

noncomputable local instance : HasDerivedCategory Ab.{t} := HasDerivedCategory.standard _

noncomputable local instance : HasDerivedCategory Rlim.InvSystemAb.{t} :=
  HasDerivedCategory.standard _

noncomputable local instance : (lim : Rlim.InvSystemAb.{t} ⥤ Ab.{t}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### The four-term comparison for an inverse system of complexes of abelian groups -/

/-- A pair of composable maps of inverse systems whose composite vanishes termwise, as a
short complex of inverse systems. -/
private def systemShortComplex
    {A B D : Rlim.InvSystemAb.{t}} (f : A ⟶ B) (g : B ⟶ D)
    (h : ∀ i, f.app i ≫ g.app i = 0) :
    ShortComplex Rlim.InvSystemAb.{t} :=
  ShortComplex.mk f g (NatTrans.ext (funext h))

/-- The homology of a short complex of inverse systems, computed degreewise, is the inverse
system of homologies. -/
private def systemShortComplexHomologyIso (S : ShortComplex Rlim.InvSystemAb.{t}) :
    S.homology ≅
      (ShortComplex.FunctorEquivalence.functor ℕᵒᵖ Ab.{t}).obj S ⋙
        ShortComplex.homologyFunctor Ab.{t} := by
  refine NatIso.ofComponents
    (fun i => (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj i)).symm) ?_
  intro i j φ
  apply (cancel_mono (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj j)).hom).1
  calc
    (S.homology.map φ ≫
        (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj j)).inv) ≫
        (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj j)).hom =
        S.homology.map φ := by simp
    _ = (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj i)).inv ≫
        ShortComplex.homologyMap (S.mapNatTrans ((evaluation ℕᵒᵖ Ab.{t}).map φ)) ≫
          (S.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj j)).hom :=
      NatTrans.app_homology ((evaluation ℕᵒᵖ Ab.{t}).map φ) S

section Devissage

variable (RF : DerivedCategory Rlim.InvSystemAb.{t} ⥤ DerivedCategory Ab.{t})
  (α : (lim : Rlim.InvSystemAb.{t} ⥤ Ab.{t}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  (hRF : RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso Rlim.InvSystemAb.{t} (ComplexShape.up ℤ)))

include α hRF

/-- The first derived inverse limit, as the degree-one cohomology of a right derived functor
of `lim`. -/
private abbrev derivedLimOne (A : Rlim.InvSystemAb.{t}) : Ab.{t} :=
  (DerivedCategory.homologyFunctor Ab.{t} 1).obj
    (RF.obj ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{t} 0).obj A))

/-- The first derived inverse limit of an inverse system does not depend on the right derived
functor of `lim` used to compute it. -/
private lemma isZero_derivedLimOne_iff
    {RF' : DerivedCategory Rlim.InvSystemAb.{t} ⥤ DerivedCategory Ab.{t}}
    {α' : (lim : Rlim.InvSystemAb.{t} ⥤ Ab.{t}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF'}
    (hRF' : RF'.IsRightDerivedFunctor α'
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{t} (ComplexShape.up ℤ)))
    (A : Rlim.InvSystemAb.{t}) :
    IsZero (derivedLimOne RF A) ↔ IsZero (derivedLimOne RF' A) := by
  let _ : RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{t} (ComplexShape.up ℤ)) := hRF
  let _ : RF'.IsRightDerivedFunctor α'
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{t} (ComplexShape.up ℤ)) := hRF'
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor Ab.{t} 1).mapIso
    ((Functor.rightDerivedUnique RF RF' α α'
      (HomotopyCategory.quasiIso Rlim.InvSystemAb.{t} (ComplexShape.up ℤ))).app
        ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{t} 0).obj A)))

/-- A short exact sequence of inverse systems stays right exact under inverse limit when the
first derived limit of its kernel vanishes. -/
private lemma epi_limMap_of_shortExact_of_isZero_R1
    {S : ShortComplex Rlim.InvSystemAb.{t}} (hS : S.ShortExact)
    (hZ : IsZero (derivedLimOne RF S.X₁)) :
    Epi ((lim : Rlim.InvSystemAb.{t} ⥤ Ab.{t}).map S.g) := by
  obtain ⟨RF', α', commShift, hRF', _, e₀, hex, _, _, _⟩ :=
    Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one hS
  exact ((hex.sc 1).exact_iff_epi
    (((isZero_derivedLimOne_iff RF α hRF hRF' S.X₁).1 hZ).eq_of_tgt _ _)).1 (hex.exact 1)

/-- The first derived inverse limit of the middle term of a short exact sequence vanishes
when it vanishes on both ends. -/
private lemma isZero_R1_middle_of_shortExact
    {S : ShortComplex Rlim.InvSystemAb.{t}} (hS : S.ShortExact)
    (h₁ : IsZero (derivedLimOne RF S.X₁)) (h₃ : IsZero (derivedLimOne RF S.X₃)) :
    IsZero (derivedLimOne RF S.X₂) := by
  obtain ⟨RF', α', commShift, hRF', _, e₀, hex, _, _, _⟩ :=
    Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one hS
  exact (isZero_derivedLimOne_iff RF α hRF hRF' S.X₂).2
    ((hex.exact 3).isZero_of_both_isZero ((isZero_derivedLimOne_iff RF α hRF hRF' S.X₁).1 h₁)
      ((isZero_derivedLimOne_iff RF α hRF hRF' S.X₃).1 h₃))

/-- The first derived inverse limit of a quotient vanishes when it vanishes on the term it is
a quotient of: inverse systems indexed by `ℕ` have no higher derived limits. -/
private lemma isZero_R1_quotient_of_shortExact
    {S : ShortComplex Rlim.InvSystemAb.{t}} (hS : S.ShortExact)
    (h₂ : IsZero (derivedLimOne RF S.X₂)) :
    IsZero (derivedLimOne RF S.X₃) := by
  obtain ⟨RF', α', commShift, hRF', _, e₀, hex, _, hepi, _⟩ :=
    Rlim.exists_sixTerm_exact_sequence_lim_rightDerived_one hS
  exact (isZero_derivedLimOne_iff RF α hRF hRF' S.X₃).2
    (IsZero.of_epi ((DerivedCategory.singleFunctor Rlim.InvSystemAb.{t} 0 ⋙ RF' ⋙
      DerivedCategory.homologyFunctor Ab.{t} 1).map S.g)
      ((isZero_derivedLimOne_iff RF α hRF hRF' S.X₂).1 h₂))

end Devissage

/-- The coimage injection of a morphism together with a map killing the morphism, as a
short complex. -/
private abbrev coimageComplex
    {A B D : Rlim.InvSystemAb.{t}} (f : A ⟶ B) (p : B ⟶ D) (w : f ≫ p = 0) :
    ShortComplex Rlim.InvSystemAb.{t} :=
  ShortComplex.mk (Abelian.factorThruCoimage f) p (by
    apply (cancel_epi (Abelian.coimage.π f)).1
    rw [← Abelian.coimage.fac f] at w
    simpa only [Category.assoc, comp_zero] using w)

/-- The kernel inclusion of a morphism together with its coimage projection form a short exact
sequence. -/
private lemma shortExact_kernel_coimage {A B : Rlim.InvSystemAb.{t}} (f : A ⟶ B) :
    (ShortComplex.mk (kernel.ι f) (Abelian.coimage.π f) (cokernel.condition _)).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

/-- The coimage injection of a morphism together with any cokernel projection of it form a
short exact sequence. -/
private lemma shortExact_coimage_cokernel
    {A B D : Rlim.InvSystemAb.{t}} (f : A ⟶ B) (p : B ⟶ D) (w : f ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p w)) :
    (coimageComplex f p w).ShortExact := by
  let S₀ := ShortComplex.mk f p w
  let S₁ := coimageComplex f p w
  let φ : S₀ ⟶ S₁ :=
    { τ₁ := Abelian.coimage.π f
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S₀, S₁]
      comm₂₃ := by simp [S₀, S₁] }
  have hex₀ : S₀.Exact := ShortComplex.exact_of_g_is_cokernel _ hp
  have hex₁ : S₁.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hex₀
  exact { exact := hex₁, mono_f := inferInstance, epi_g := epi_of_isColimit_cofork hp }

section Devissage2

variable (RF : DerivedCategory Rlim.InvSystemAb.{t} ⥤ DerivedCategory Ab.{t})
  (α : (lim : Rlim.InvSystemAb.{t} ⥤ Ab.{t}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
  (hRF : RF.IsRightDerivedFunctor α
    (HomotopyCategory.quasiIso Rlim.InvSystemAb.{t} (ComplexShape.up ℤ)))

include α hRF

/-- Inverse limit preserves the cokernel of a morphism whose source and kernel have vanishing
first derived limits. -/
private lemma preservesCokernel_of_isZero_R1_kernel_and_source
    {A B : Rlim.InvSystemAb.{t}} (f : A ⟶ B)
    (hK : IsZero (derivedLimOne RF (kernel f))) (hA : IsZero (derivedLimOne RF A)) :
    PreservesColimit (parallelPair f 0) (lim : Rlim.InvSystemAb.{t} ⥤ Ab.{t}) := by
  let F : Rlim.InvSystemAb.{t} ⥤ Ab.{t} := lim
  have hS₁ := shortExact_kernel_coimage f
  have hepi₁ : Epi (F.map (Abelian.coimage.π f)) :=
    epi_limMap_of_shortExact_of_isZero_R1 RF α hRF hS₁ hK
  have hQ : IsZero (derivedLimOne RF (Abelian.coimage f)) :=
    isZero_R1_quotient_of_shortExact RF α hRF hS₁ hA
  let S₂ := coimageComplex f (cokernel.π f) (cokernel.condition f)
  have hS₂ : S₂.ShortExact :=
    shortExact_coimage_cokernel f (cokernel.π f) (cokernel.condition f) (cokernelIsCokernel f)
  have hepi₂ : Epi (F.map (cokernel.π f)) :=
    epi_limMap_of_shortExact_of_isZero_R1 RF α hRF hS₂ hQ
  have hex₂ : (S₂.map F).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS₂.fIsKernel F)
  let S₀ : ShortComplex Rlim.InvSystemAb.{t} :=
    ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  let φ : S₀.map F ⟶ S₂.map F :=
    { τ₁ := F.map (Abelian.coimage.π f)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        dsimp [S₀, S₂]
        simp only [Category.comp_id, ← F.map_comp, Abelian.coimage.fac]
      comm₂₃ := by simp [S₀, S₂] }
  have hex₀ : (S₀.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hex₂
  have hcok : IsColimit (CokernelCofork.ofπ (F.map (cokernel.π f)) (by
      rw [← F.map_comp, cokernel.condition, F.map_zero])) :=
    (ShortComplex.exact_and_epi_g_iff_g_is_cokernel (S₀.map F)).1 ⟨hex₀, hepi₂⟩ |>.some
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
    ((CokernelCofork.isColimitMapCoconeEquiv _ F).2 hcok)

/-- Vanishing of the first derived limit on the first term and on the homology of a short
complex implies vanishing on its cycles. -/
private lemma isZero_R1_cycles_of_isZero_R1_first_and_homology
    (S : ShortComplex Rlim.InvSystemAb.{t})
    (h₁ : IsZero (derivedLimOne RF S.X₁)) (hH : IsZero (derivedLimOne RF S.homology)) :
    IsZero (derivedLimOne RF S.cycles) := by
  have hQ := isZero_R1_quotient_of_shortExact RF α hRF (shortExact_kernel_coimage S.toCycles) h₁
  exact isZero_R1_middle_of_shortExact RF α hRF
    (shortExact_coimage_cokernel S.toCycles S.homologyπ S.toCycles_comp_homologyπ
      S.homologyIsCokernel) hQ hH

/-- Let `A⁻² ⟶ A⁻¹ ⟶ A⁰ ⟶ A¹` be an inverse system of four-term complexes of abelian
groups. If the first derived limit vanishes on `A⁻²`, on `A⁻¹` and on the inverse system of
degree `-1` cohomologies, then the canonical map from the degree-zero cohomology of the
termwise inverse limit to the inverse limit of the degree-zero cohomologies is an
isomorphism. -/
@[ega "0 13.2.3" "Bijectivity of h_n", sga "4½ Rapport 4.11" "partial"]
private theorem comparisonHomologyLimit_isIso_of_isZero_derivedLimOne
    (A₂ A₁ A₀ A' : Rlim.InvSystemAb.{t})
    (d₂ : A₂ ⟶ A₁) (d₁ : A₁ ⟶ A₀) (d₀ : A₀ ⟶ A')
    (h₁ : ∀ i, d₂.app i ≫ d₁.app i = 0) (h₀ : ∀ i, d₁.app i ≫ d₀.app i = 0)
    (hA₂ : IsZero (derivedLimOne RF A₂)) (hA₁ : IsZero (derivedLimOne RF A₁))
    (hH₁ : IsZero (derivedLimOne RF (homologyInvSystem d₂ d₁ h₁))) :
    IsIso (comparisonHomologyLimit d₁ d₀ h₀) := by
  let R₁ : Rlim.InvSystemAb.{t} ⥤ Ab.{t} :=
    DerivedCategory.singleFunctor Rlim.InvSystemAb.{t} 0 ⋙ RF ⋙
      DerivedCategory.homologyFunctor Ab.{t} 1
  let F : Rlim.InvSystemAb.{t} ⥤ Ab.{t} := lim
  let Sneg := systemShortComplex d₂ d₁ h₁
  have hHom : IsZero (R₁.obj Sneg.homology) :=
    IsZero.of_iso hH₁ (R₁.mapIso (systemShortComplexHomologyIso Sneg))
  have hCycles : IsZero (R₁.obj Sneg.cycles) :=
    isZero_R1_cycles_of_isZero_R1_first_and_homology RF α hRF Sneg hA₂ hHom
  have hKer : IsZero (R₁.obj (kernel d₁)) :=
    IsZero.of_iso hCycles (R₁.mapIso Sneg.cyclesIsoKernel).symm
  let S₀ := systemShortComplex d₁ d₀ h₀
  have hKer₀ : IsZero (R₁.obj (kernel S₀.f)) := by
    simpa only [S₀, systemShortComplex] using hKer
  have hKer' : IsZero (R₁.obj (kernel S₀.toCycles)) := by
    apply IsZero.of_iso hKer₀
    simpa only [S₀.toCycles_i] using
      (R₁.mapIso (kernelCompMono S₀.toCycles S₀.iCycles)).symm
  have hPres : PreservesColimit (parallelPair S₀.toCycles 0) F :=
    preservesCokernel_of_isZero_R1_kernel_and_source RF α hRF S₀.toCycles hKer' hA₁
  have hPresF : PreservesColimit (parallelPair S₀.f 0) F :=
    preservesCokernel_of_isZero_R1_kernel_and_source RF α hRF S₀.f hKer₀ hA₁
  let _ : (ShortComplex.LeftHomologyData.canonical S₀).IsPreservedBy F :=
    ⟨inferInstance, hPres⟩
  let _ : F.PreservesLeftHomologyOf S₀ :=
    Functor.PreservesLeftHomologyOf.mk' F (ShortComplex.LeftHomologyData.canonical S₀)
  let _ : (ShortComplex.RightHomologyData.canonical S₀).IsPreservedBy F :=
    ⟨hPresF, inferInstance⟩
  let _ : F.PreservesRightHomologyOf S₀ :=
    Functor.PreservesRightHomologyOf.mk' F (ShortComplex.RightHomologyData.canonical S₀)
  let e := S₀.mapHomologyIso F
  let κ : S₀.homology ≅ homologyInvSystem d₁ d₀ h₀ := systemShortComplexHomologyIso S₀
  have hcomp : comparisonHomologyLimit d₁ d₀ h₀ = e.hom ≫ F.map κ.hom := by
    apply limit.hom_ext
    intro i
    have hnat : limit.π S₀.homology i =
        e.inv ≫ ShortComplex.homologyMap (S₀.mapNatTrans (lim.π i)) ≫
          (S₀.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj i)).hom := by
      simpa only [lim.π_app] using NatTrans.app_homology (lim.π i) S₀
    have hκ : κ.hom.app i =
        (S₀.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj i)).inv := rfl
    have hπκ : limit.π S₀.homology i ≫ κ.hom.app i =
        e.inv ≫ ShortComplex.homologyMap (S₀.mapNatTrans (lim.π i)) := by
      rw [hnat, hκ]
      exact (Category.assoc _ _ _).trans (congrArg (e.inv ≫ ·)
        ((Category.assoc _ _ _).trans
          ((congrArg (ShortComplex.homologyMap (S₀.mapNatTrans (lim.π i)) ≫ ·)
            (S₀.mapHomologyIso ((evaluation ℕᵒᵖ Ab.{t}).obj i)).hom_inv_id).trans
              (Category.comp_id _))))
    have hRHS : e.hom ≫ F.map κ.hom ≫ limit.π (homologyInvSystem d₁ d₀ h₀) i =
        ShortComplex.homologyMap (S₀.mapNatTrans (lim.π i)) := by
      rw [show F.map κ.hom ≫ limit.π (homologyInvSystem d₁ d₀ h₀) i =
        limit.π S₀.homology i ≫ κ.hom.app i from limMap_π κ.hom i, hπκ]
      exact e.hom_inv_id_assoc _
    exact (limit.lift_π _ i).trans ((Category.assoc _ _ _).trans hRHS).symm
  rw [hcomp]
  exact inferInstanceAs (IsIso (e.hom ≫ (F.mapIso κ).hom))

end Devissage2

/-- The four-term comparison of Stacks 0918, with the hypotheses stated through
`Rlim.firstDerivedLimit`. -/
private theorem comparisonHomologyLimit_isIso_of_firstDerivedLimit
    (A₂ A₁ A₀ A' : Rlim.InvSystemAb.{t})
    (d₂ : A₂ ⟶ A₁) (d₁ : A₁ ⟶ A₀) (d₀ : A₀ ⟶ A')
    (h₁ : ∀ i, d₂.app i ≫ d₁.app i = 0) (h₀ : ∀ i, d₁.app i ≫ d₀.app i = 0)
    (hA₂ : IsZero (Rlim.firstDerivedLimit A₂)) (hA₁ : IsZero (Rlim.firstDerivedLimit A₁))
    (hH₁ : IsZero (Rlim.firstDerivedLimit (homologyInvSystem d₂ d₁ h₁))) :
    IsIso (comparisonHomologyLimit d₁ d₀ h₀) := by
  obtain ⟨RF, α, hRF, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations.{t}
  have transfer (A : Rlim.InvSystemAb.{t}) (hA : IsZero (Rlim.firstDerivedLimit A)) :
      IsZero (derivedLimOne RF A) := by
    obtain ⟨e⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF A
    exact (Iso.isZero_iff e).2 hA
  exact comparisonHomologyLimit_isIso_of_isZero_derivedLimOne RF α hRF
    A₂ A₁ A₀ A' d₂ d₁ d₀ h₁ h₀ (transfer A₂ hA₂) (transfer A₁ hA₁) (transfer _ hH₁)

/-- Vanishing of the first derived limit transports along an isomorphism of inverse
systems. -/
private lemma isZero_firstDerivedLimit_of_iso
    {A B : Rlim.InvSystemAb.{t}} (e : A ≅ B)
    (hB : IsZero (Rlim.firstDerivedLimit B)) :
    IsZero (Rlim.firstDerivedLimit A) := by
  obtain ⟨RF, α, hRF, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations.{t}
  obtain ⟨eA⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF A
  obtain ⟨eB⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF B
  exact IsZero.of_iso hB (eA.symm ≪≫
    (DerivedCategory.singleFunctor Rlim.InvSystemAb.{t} 0 ⋙ RF ⋙
      DerivedCategory.homologyFunctor Ab.{t} 1).mapIso e ≪≫ eB)

/-- For an inverse system of complexes of abelian groups, the comparison between the
degree-`m` cohomology of the termwise limit and the limit of the degree-`m` cohomologies is
an isomorphism as soon as the first derived limit vanishes in degrees `m - 2` and `m - 1` and
on the degree `m - 1` cohomology. -/
@[sga "4½ Rapport 4.11" "partial"]
private theorem sectionsHomologyLimitComparison_isIso
    (G : ℕᵒᵖ ⥤ CochainComplex Ab.{t} ℤ) (m : ℤ)
    (hneg2 : IsZero (Rlim.firstDerivedLimit
      (G ⋙ HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m - 2))))
    (hneg1 : IsZero (Rlim.firstDerivedLimit
      (G ⋙ HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m - 1))))
    (hHneg1 : IsZero (Rlim.firstDerivedLimit
      (G ⋙ HomologicalComplex.homologyFunctor Ab.{t} (ComplexShape.up ℤ) (m - 1)))) :
    IsIso (comparisonHomologyLimit
      (Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
        (ComplexShape.up ℤ) (m - 1) m))
      (Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
        (ComplexShape.up ℤ) m (m + 1)))
      (fun i => (G.obj i).d_comp_d (m - 1) m (m + 1))) := by
  let d₂ := Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
    (ComplexShape.up ℤ) (m - 2) (m - 1))
  let d₁ := Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
    (ComplexShape.up ℤ) (m - 1) m)
  let d₀ := Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
    (ComplexShape.up ℤ) m (m + 1))
  let A₂ := G ⋙ HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m - 2)
  let A₁ := G ⋙ HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m - 1)
  let A₀ := G ⋙ HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) m
  let A' := G ⋙ HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m + 1)
  have hcomp₁ : ∀ i, d₂.app i ≫ d₁.app i = 0 :=
    fun i => (G.obj i).d_comp_d (m - 2) (m - 1) m
  have hcomp₀ : ∀ i, d₁.app i ≫ d₀.app i = 0 :=
    fun i => (G.obj i).d_comp_d (m - 1) m (m + 1)
  have hH : IsZero (Rlim.firstDerivedLimit (homologyInvSystem d₂ d₁ hcomp₁)) :=
    isZero_firstDerivedLimit_of_iso (Functor.isoWhiskerLeft G
      (HomologicalComplex.homologyFunctorIso' Ab.{t} (ComplexShape.up ℤ) (m - 2) (m - 1) m
        ((ComplexShape.up ℤ).prev_eq' (by change m - 2 + 1 = m - 1; omega))
        ((ComplexShape.up ℤ).next_eq' (by change m - 1 + 1 = m; omega))).symm) hHneg1
  simpa [d₁, d₀] using comparisonHomologyLimit_isIso_of_firstDerivedLimit
    A₂ A₁ A₀ A' d₂ d₁ d₀ hcomp₁ hcomp₀ hneg2 hneg1 hH

/-- When the four-term comparison is an isomorphism, degree-`m` cohomology of complexes of
abelian groups commutes with the inverse limit. -/
private lemma preservesHomology_of_comparison
    (G : ℕᵒᵖ ⥤ CochainComplex Ab.{t} ℤ) (m : ℤ)
    (h : IsIso (comparisonHomologyLimit
      (Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
        (ComplexShape.up ℤ) (m - 1) m))
      (Functor.whiskerLeft G (HomologicalComplex.dNatTrans Ab.{t}
        (ComplexShape.up ℤ) m (m + 1)))
      (fun i => (G.obj i).d_comp_d (m - 1) m (m + 1)))) :
    PreservesLimit G (HomologicalComplex.homologyFunctor Ab.{t} (ComplexShape.up ℤ) m) := by
  let H := HomologicalComplex.shortComplexFunctor' Ab.{t} (ComplexShape.up ℤ)
    (m - 1) m (m + 1) ⋙ ShortComplex.homologyFunctor Ab.{t}
  let c := HomologicalComplex.coneOfHasLimitEval G
  have hcomp : IsIso ((limit.isLimit (G ⋙ H)).lift (H.mapCone c)) := h
  have hlim : IsLimit (H.mapCone c) := (limit.isLimit (G ⋙ H)).ofPointIso
  have : PreservesLimit G H := preservesLimit_of_preserves_limit_cone
    (HomologicalComplex.isLimitConeOfHasLimitEval G) hlim
  exact preservesLimit_of_natIso G (HomologicalComplex.homologyFunctorIso' Ab.{t}
    (ComplexShape.up ℤ) (m - 1) m (m + 1)
    ((ComplexShape.up ℤ).prev_eq' (by change m - 1 + 1 = m; omega))
    ((ComplexShape.up ℤ).next_eq' rfl)).symm

/-! ### From sections to sheaves -/

section Local

variable {C : Type u} [Category.{v} C]

/-- A morphism of short complexes of abelian sheaves which is a quasi-isomorphism on sections
over a generating family is a quasi-isomorphism. -/
private lemma sheaf_quasiIso_of_local (J : GrothendieckTopology C)
    [HasSheafify J Ab.{t}] [J.WEqualsLocallyBijective Ab.{t}]
    {S T : ShortComplex (Sheaf J Ab.{t})} (φ : S ⟶ T)
    (B : Set C) (hB : J.HasEnoughObjects (· ∈ B))
    (h : ∀ U ∈ B, ShortComplex.QuasiIso
      (((sheafToPresheaf J Ab.{t} ⋙
        (evaluation Cᵒᵖ Ab.{t}).obj (op U)).mapShortComplex).map φ)) :
    ShortComplex.QuasiIso φ := by
  let P := sheafToPresheaf J Ab.{t}
  let L := presheafToSheaf J Ab.{t}
  let ψ := P.mapShortComplex.map φ
  have hloc : ∀ U ∈ B, IsIso ((ShortComplex.homologyMap ψ).app (op U)) := by
    intro U hU
    let E := (evaluation Cᵒᵖ Ab.{t}).obj (op U)
    have : IsIso (ShortComplex.homologyMap (E.mapShortComplex.map ψ)) :=
      (ShortComplex.quasiIso_iff _).1 (h U hU)
    exact IsIso.of_isIso_fac_left (ShortComplex.mapHomologyIso_hom_naturality ψ E).symm
  have hL : IsIso (L.map (ShortComplex.homologyMap ψ)) := by
    apply Presheaf.isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective
    intro U
    obtain ⟨I, V, f, hf, hV⟩ := hB U
    refine ⟨I, V, f, hf, fun i => ?_⟩
    have := hloc (V i) (hV i)
    exact ConcreteCategory.bijective_of_isIso _
  have hψ : ShortComplex.QuasiIso (L.mapShortComplex.map ψ) := by
    rw [ShortComplex.quasiIso_iff]
    exact IsIso.of_isIso_fac_right (ShortComplex.mapHomologyIso_hom_naturality ψ L)
  let e : 𝟭 (Sheaf J Ab.{t}) ≅ P ⋙ L := sheafificationNatIso J Ab.{t}
  exact (ShortComplex.quasiIso_iff_of_arrow_mk_iso φ (L.mapShortComplex.map ψ)
    (Arrow.isoMk (S.mapNatIso e) (T.mapNatIso e) (ShortComplex.hom_ext _ _
      (e.hom.naturality φ.τ₁).symm (e.hom.naturality φ.τ₂).symm
      (e.hom.naturality φ.τ₃).symm))).2 hψ

/-- A morphism of complexes of sheaves of modules which is an isomorphism on degree-`m`
cohomology of sections over a generating family is an isomorphism on the degree-`m`
cohomology sheaf. -/
private lemma homologyMap_isIso_of_local_sections {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{w}) [HasSheafify J Ab.{t}] [J.WEqualsLocallyBijective Ab.{t}]
    {K L : CochainComplex (SheafOfModules.{t} R) ℤ} (φ : K ⟶ L)
    (m : ℤ) (B : Set C) (hB : J.HasEnoughObjects (· ∈ B))
    (h : ∀ U ∈ B, IsIso ((HomologicalComplex.homologyFunctor Ab.{t}
      (ComplexShape.up ℤ) m).map ((sectionsComplexFunctor R U).map φ))) :
    IsIso (HomologicalComplex.homologyMap φ m) := by
  let D := SheafOfModules.toSheaf.{t} R
  let ψ := (HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) m).map φ
  have hD : ShortComplex.QuasiIso (D.mapShortComplex.map ψ) :=
    sheaf_quasiIso_of_local J _ B hB fun U hU => (ShortComplex.quasiIso_iff _).2 (h U hU)
  exact (ShortComplex.quasiIso_iff ψ).1
    ((ShortComplex.quasiIso_map_iff_of_preservesLeftHomology D ψ).1 hD)

end Local

/-- A functor on `ℕᵒᵖ` which is invertible on the maps `n ⟶ n₀` given by `n₀ ≤ n` is
eventually constant to `n₀`. -/
private lemma isEventuallyConstantTo_of_homOfLE {D : Type*} [Category D]
    (G : ℕᵒᵖ ⥤ D) (n₀ : ℕ) (h : ∀ n (hn : n₀ ≤ n), IsIso (G.map (homOfLE hn).op)) :
    G.IsEventuallyConstantTo (op n₀) := by
  intro n f
  have hn : n₀ ≤ n.unop := leOfHom f.unop
  have hf : f = (homOfLE hn).op := Subsingleton.elim _ _
  simpa only [hf] using h n.unop hn

/-! ### The two conclusions of Stacks 08CT -/

/-- **Stacks 08CT.** The canonical cone from the degree-`m` cohomology of the termwise
inverse limit of an inverse system of complexes of modules on a ringed site to the
degree-`m` cohomologies is a limit cone, provided the first derived limits of the sections
vanish in degrees `m - 2` and `m - 1` and on the degree `m - 1` cohomology over a generating
family, and the degree-`m` cohomology of sections is constant from stage `n₀` on. -/
@[stacks 08CT "canonical cohomology-limit comparison"]
public theorem homology_isLimit_of_local_rlim_vanishing
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{t}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    (F : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) (B : Set X.C) (hB : X.J.HasEnoughObjects (· ∈ B))
    (hneg2 : ∀ U ∈ B, IsZero (Rlim.firstDerivedLimit
      (F ⋙ sectionsComplexFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m - 2))))
    (hneg1 : ∀ U ∈ B, IsZero (Rlim.firstDerivedLimit
      (F ⋙ sectionsComplexFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        HomologicalComplex.eval Ab.{t} (ComplexShape.up ℤ) (m - 1))))
    (hHneg1 : ∀ U ∈ B, IsZero (Rlim.firstDerivedLimit
      (F ⋙ sectionsComplexFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
        HomologicalComplex.homologyFunctor Ab.{t} (ComplexShape.up ℤ) (m - 1))))
    (n₀ : ℕ)
    (hstable : ∀ U ∈ B, ∀ (n : ℕ) (hn : n₀ ≤ n), IsIso
      ((HomologicalComplex.homologyFunctor Ab.{t} (ComplexShape.up ℤ) m).map
        ((sectionsComplexFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          (F.map (homOfLE hn).op)))) :
    Nonempty (IsLimit
      ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) m).mapCone (limit.cone F))) := by
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let H := HomologicalComplex.homologyFunctor (SheafOfModules.{t} R) (ComplexShape.up ℤ) m
  have hH : (F ⋙ H).IsEventuallyConstantTo (op n₀) :=
    isEventuallyConstantTo_of_homOfLE _ n₀ fun n hn =>
      homologyMap_isIso_of_local_sections R (F.map (homOfLE hn).op) m B hB fun U hU =>
        hstable U hU n hn
  have hπ : IsIso (HomologicalComplex.homologyMap (limit.π F (op n₀)) m) := by
    apply homologyMap_isIso_of_local_sections R _ m B hB
    intro U hU
    have : PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.evaluation.{t} R (op U)) :=
      SheafOfModules.evaluationPreservesLimitsOfShape.{t} (R := R) (D := ℕᵒᵖ) (op U)
    let G := F ⋙ sectionsComplexFunctor R U
    let HAb := HomologicalComplex.homologyFunctor Ab.{t} (ComplexShape.up ℤ) m
    have : PreservesLimit G HAb := preservesHomology_of_comparison G m
      (sectionsHomologyLimitComparison_isIso G m (hneg2 U hU) (hneg1 U hU) (hHneg1 U hU))
    have hG : (G ⋙ HAb).IsEventuallyConstantTo (op n₀) :=
      isEventuallyConstantTo_of_homOfLE _ n₀ (hstable U hU)
    exact hG.isIso_π_of_isLimit
      (isLimitOfPreserves HAb
        (isLimitOfPreserves (sectionsComplexFunctor R U) (limit.isLimit F)))
  have : IsIso ((H.mapCone (limit.cone F)).π.app (op n₀)) := hπ
  exact ⟨hH.isLimitOfIsIso (H.mapCone (limit.cone F))⟩

/-- **Stacks 08CT.** The limit of the degree-`m` cohomology sheaves of an inverse system of
complexes of modules on a ringed site projects isomorphically to any stage from which the
degree-`m` cohomology of sections over a generating family is constant. -/
@[stacks 08CT "projection to a stable stage"]
public theorem homology_limit_projection_isIso_of_local_rlim_vanishing
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{t}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{t}]
    (F : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{t}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) (B : Set X.C) (hB : X.J.HasEnoughObjects (· ∈ B)) (n₀ : ℕ)
    (hstable : ∀ U ∈ B, ∀ (n : ℕ) (hn : n₀ ≤ n), IsIso
      ((HomologicalComplex.homologyFunctor Ab.{t} (ComplexShape.up ℤ) m).map
        ((sectionsComplexFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map
          (F.map (homOfLE hn).op)))) :
    IsIso (limit.π (F ⋙ HomologicalComplex.homologyFunctor
      (SheafOfModules.{t} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ) m) (op n₀)) := by
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let H := F ⋙ HomologicalComplex.homologyFunctor (SheafOfModules.{t} R)
    (ComplexShape.up ℤ) m
  have hH : H.IsEventuallyConstantTo (op n₀) :=
    isEventuallyConstantTo_of_homOfLE _ n₀ fun n hn =>
      homologyMap_isIso_of_local_sections R (F.map (homOfLE hn).op) m B hB fun U hU =>
        hstable U hU n hn
  exact hH.isIso_π_of_isLimit (limit.isLimit H)

end Stacks.Cohomology.InverseLimits

end

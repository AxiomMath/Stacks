module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpAssembly
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyModelBridge
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutVanishing
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpRationalSingularity

/-!
# The low-degree Leray sequence for a modification over a two-dimensional local ring

Let `A` be a two-dimensional Noetherian normal local domain, `f : X ⟶ Spec A` a modification
with `X` normal, and `g : X' ⟶ X` a morphism with `X'` normal and `g ≫ f` a modification. The
Leray sequence

  `0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ Γ(X, R¹g_*𝒪_{X'}) ⟶ H²(X, 𝒪_X) = 0`

shows that `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})` is injective, and that `R¹g_*𝒪_{X'}` has no nonzero
global section when it is onto. This is `AlgebraicGeometry.LerayFirstCohomologyExact A`, the
input of [Stacks, Tag 0AXF] (1) used by [Stacks, Tag 0B4P].

The proof works with one injective resolution step `0 ⟶ 𝒪_{X'} ⟶ I ⟶ Q ⟶ 0` on `X'`: with
`C = coker(𝒪_X ⟶ g_* I)`, there are short exact sequences `0 ⟶ 𝒪_X ⟶ g_* I ⟶ C ⟶ 0` and
`0 ⟶ C ⟶ g_* Q ⟶ R¹g_*𝒪_{X'} ⟶ 0`, the first giving `H¹(X, C) ⊆ H²(X, 𝒪_X) = 0` ([Stacks,
Tag 02V7] through `AlgebraicGeometry.subsingleton_cohomologyPresheaf_two_top_of_isModification`),
so that `Γ(g_* Q) ⟶ Γ(R¹g_*𝒪_{X'})` is onto; surjectivity of
`H¹(X, 𝒪_X) = Γ(C)/Γ(g_* I) ⟶ Γ(Q)/Γ(I) = H¹(X', 𝒪_{X'})` says `Γ(C) = Γ(g_* Q)`.

## Main results

* `AlgebraicGeometry.lerayFirstCohomologyExact_of_ringKrullDim_eq_two`.

## References

* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- In a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of modules with `H¹(X, B) = 0` and
`H²(X, A) = 0`, also `H¹(X, C) = 0`. -/
theorem isZero_firstCohomology_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (h1 : IsZero (((Scheme.sectionsFunctor X).rightDerived 1).obj S.X₂))
    (h2 : IsZero (((Scheme.sectionsFunctor X).rightDerived 2).obj S.X₁)) :
    IsZero (((Scheme.sectionsFunctor X).rightDerived 1).obj S.X₃) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.sectionsFunctor X)
  have hmono : Mono (D.δ hS 1) :=
    (ShortComplex.exact_iff_mono _ (h1.eq_of_src _ _)).1 (D.exact_δ₁ hS 1)
  exact @IsZero.of_mono _ _ _ _ _ (D.δ hS 1) hmono h2

/-- In a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of modules with `H¹(X, A) = 0`,
if `Γ(X, A) ⟶ Γ(X, B)` is onto then `Γ(X, C) = 0`. -/
theorem subsingleton_sections_of_shortExact {X : Scheme.{u}}
    {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)} (hS : S.ShortExact)
    (h1 : IsZero (((Scheme.sectionsFunctor X).rightDerived 1).obj S.X₁))
    (hf : Function.Surjective ((Scheme.sectionsFunctor X).map S.f).hom) :
    Subsingleton ((Scheme.sectionsFunctor X).obj S.X₃) := by
  let Γ := Scheme.sectionsFunctor X
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives Γ
  have hepi0 : Epi ((Γ.rightDerived 0).map S.g) :=
    (ShortComplex.exact_iff_epi _ (h1.eq_of_tgt _ _)).1 (D.exact_δ₁ hS 0)
  let uΓ : Γ ⟶ Γ.rightDerived 0 := Γ.toRightDerivedZero
  have hcomm : Γ.map S.g ≫ uΓ.app _ = uΓ.app _ ≫ (Γ.rightDerived 0).map S.g :=
    uΓ.naturality S.g
  have hfac : Γ.map S.g = (uΓ.app _ ≫ (Γ.rightDerived 0).map S.g) ≫ inv (uΓ.app _) := by
    rw [← hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hepi' : Epi (Γ.map S.g) := by
    rw [hfac]
    exact epi_comp _ _
  have hsurjg : Function.Surjective (Γ.map S.g).hom := (ModuleCat.epi_iff_surjective _).1 hepi'
  refine ⟨fun a b => ?_⟩
  suffices h0 : ∀ y : Γ.obj S.X₃, y = 0 from (h0 a).trans (h0 b).symm
  intro y
  obtain ⟨z, rfl⟩ := hsurjg y
  obtain ⟨c, rfl⟩ := hf z
  change (Γ.map S.f ≫ Γ.map S.g).hom c = 0
  rw [← Functor.map_comp, S.zero, Functor.map_zero]
  rfl

/-- **The low-degree Leray sequence for a morphism with `H²` of the target vanishing.** Let
`g : X' ⟶ X` be a morphism of schemes with `g^♯` an isomorphism and `H²(X, 𝒪_X) = 0`. There is
an injective map `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})`, semilinear along `g^♯`, and if it is onto then
`R¹g_*𝒪_{X'}` has no nonzero global section. -/
theorem exists_injective_firstCohomology_and_sections_rightDerived_eq_zero {X X' : Scheme.{u}}
    (g : X' ⟶ X) [IsIso g.c]
    (hH2 : IsZero (((Scheme.sectionsFunctor X).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ θ : ((Scheme.sectionsFunctor X).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)
        →ₛₗ[SeparableGoUp.sectionsRingHom g]
        ((Scheme.sectionsFunctor X').rightDerived 1).obj (SheafOfModules.unit X'.ringCatSheaf),
      Function.Injective θ ∧ (Function.Surjective θ →
        Subsingleton ((Scheme.sectionsFunctor X).obj
          (((Scheme.Modules.pushforward g).rightDerived 1).obj
            (SheafOfModules.unit X'.ringCatSheaf)))) := by
  let Γ := Scheme.sectionsFunctor X
  let Γ' := Scheme.sectionsFunctor X'
  let G := SheafOfModules.unit X'.ringCatSheaf
  let P := SheafOfModules.pushforward.{u} g.toRingCatSheafHom
  let I := Injective.under G
  let ι : G ⟶ I := Injective.ι G
  have : Mono ι := Injective.ι_mono G
  have : Injective I := Injective.injective_under G
  let πQ := cokernel.π ι
  have hS₂ : (ShortComplex.cokernelSequence ι).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := Injective.ι_mono G }
  have : P.IsRightAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have : PreservesFiniteLimits P := inferInstance
  have : P.Additive := inferInstanceAs (Scheme.Modules.pushforward g).Additive
  obtain ⟨hexact, hmonoP⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono P).1 inferInstance _ hS₂
  have hS₁ : (ShortComplex.cokernelSequence (P.map ι)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := hmonoP }
  have hI' : IsZero ((Γ'.rightDerived 1).obj I) := Γ'.isZero_rightDerived_obj_injective_succ 0 I
  have hPI : IsZero (((Scheme.sectionsFunctor X).rightDerived 1).obj (P.obj I)) := by
    let := HasDerivedCategory.standard X.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
    have hac := Stacks.Cohomology.AffineComparison.rightAcyclic_moduleGlobalSections_pushforward_obj
      g I (Injective.injective_under G)
    exact (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).1 hac 1 Nat.one_pos
  obtain ⟨e₁⟩ := SeparableGoUp.exists_firstCohomology_equiv_quotient hS₁ hPI
  obtain ⟨e₂⟩ := SeparableGoUp.exists_firstCohomology_equiv_quotient hS₂ hI'
  have hzero : P.map ι ≫ P.map πQ = 0 :=
    (P.map_comp ι πQ).symm.trans ((congrArg P.map (cokernel.condition ι)).trans (P.map_zero _ _))
  let m : cokernel (P.map ι) ⟶ P.obj (cokernel ι) := cokernel.desc (P.map ι) (P.map πQ) hzero
  have : Mono m := hexact.mono_cokernelDesc
  have hm : Function.Injective (Γ.map m).hom := (ModuleCat.mono_iff_injective _).1 inferInstance
  let mΓ : Γ.obj (cokernel (P.map ι)) →ₛₗ[SeparableGoUp.sectionsRingHom g] Γ'.obj (cokernel ι) :=
    { toFun := fun c => (Γ.map m).hom c
      map_add' := fun c c' => map_add _ c c'
      map_smul' := fun r c => (Γ.map m).hom.map_smul r c }
  have hcomp : ∀ i : Γ.obj (P.obj I),
      mΓ ((Γ.map (cokernel.π (P.map ι))).hom i) = (Γ'.map πQ).hom i := fun i => by
    change (Γ.map (cokernel.π (P.map ι)) ≫ Γ.map m).hom i = _
    rw [← Functor.map_comp, cokernel.π_desc]
    rfl
  have hle : LinearMap.range (Γ.map (cokernel.π (P.map ι))).hom ≤
      (LinearMap.range (Γ'.map πQ).hom).comap mΓ := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (hcomp i).symm⟩
  let θ₀ := Submodule.mapQ _ _ mΓ hle
  have hθ₀ : Function.Injective θ₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ z
    have hc : mΓ c ∈ LinearMap.range (Γ'.map πQ).hom := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hz
    obtain ⟨i, hi⟩ := hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨i, hm ?_⟩
    exact (hcomp i).trans hi
  have := SeparableGoUp.isIso_unitToPushforwardObjUnit g
  let e := (Γ.rightDerived 1).mapIso
    (asIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom))
  refine ⟨((e₂.toLinearMap.comp θ₀).comp e₁.symm.toLinearMap).comp e.toLinearEquiv.toLinearMap,
    (e₂.injective.comp (hθ₀.comp e₁.symm.injective)).comp e.toLinearEquiv.injective,
    fun hsurj => ?_⟩
  -- surjectivity says that `Γ(C) ⟶ Γ(g_* Q)` is onto
  have hθ₀s : Function.Surjective θ₀ := by
    intro z
    obtain ⟨w, hw⟩ := hsurj (e₂ z)
    refine ⟨e₁.symm (e.toLinearEquiv w), ?_⟩
    apply e₂.injective
    exact hw
  have hmΓs : Function.Surjective mΓ := by
    intro y
    obtain ⟨z, hz⟩ := hθ₀s (Submodule.Quotient.mk y)
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ z
    have h1 : Submodule.Quotient.mk (mΓ c) = Submodule.Quotient.mk (p := LinearMap.range
        (Γ'.map πQ).hom) y := hz
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨i, hi⟩ := h1
    refine ⟨c - (Γ.map (cokernel.π (P.map ι))).hom i, ?_⟩
    calc mΓ (c - (Γ.map (cokernel.π (P.map ι))).hom i)
        = mΓ c - mΓ ((Γ.map (cokernel.π (P.map ι))).hom i) := map_sub _ _ _
      _ = mΓ c - (Γ'.map πQ).hom i := congrArg (mΓ c - ·) (hcomp i)
      _ = y := by rw [hi]; abel
  -- the short exact sequence `0 ⟶ C ⟶ g_* Q ⟶ R¹g_* 𝒪_{X'} ⟶ 0`
  let DP := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives P
  let δP : (P.rightDerived 0).obj (cokernel ι) ⟶ (P.rightDerived 1).obj G := DP.δ hS₂ 0
  let uP : P ⟶ P.rightDerived 0 := P.toRightDerivedZero
  have hR1I : IsZero ((P.rightDerived 1).obj I) := P.isZero_rightDerived_obj_injective_succ 0 I
  have hz' : P.map πQ ≫ (uP.app (cokernel ι) ≫ δP) = 0 := by
    rw [← Category.assoc, uP.naturality, Category.assoc]
    change uP.app I ≫ ((P.rightDerived 0).map πQ ≫ DP.δ hS₂ 0) = 0
    rw [show (P.rightDerived 0).map πQ ≫ DP.δ hS₂ 0 = 0 from DP.map_g_δ hS₂ 0, comp_zero]
  let S' := ShortComplex.mk (P.map πQ) (uP.app (cokernel ι) ≫ δP) hz'
  have hS' : S'.Exact := by
    let φ : S' ⟶ ShortComplex.mk ((P.rightDerived 0).map πQ) δP (DP.map_g_δ hS₂ 0) :=
      { τ₁ := uP.app I
        τ₂ := uP.app (cokernel ι)
        τ₃ := 𝟙 _
        comm₁₂ := (uP.naturality πQ).symm
        comm₂₃ := (Category.comp_id _).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (DP.exact_δ₁ hS₂ 0)
  have hz3 : m ≫ (uP.app (cokernel ι) ≫ δP) = 0 := by
    rw [← cancel_epi (cokernel.π (P.map ι)), ← Category.assoc, cokernel.π_desc, comp_zero]
    exact hz'
  let S3 := ShortComplex.mk m (uP.app (cokernel ι) ≫ δP) hz3
  have hS3e : S3.Exact := by
    let φ : S' ⟶ S3 :=
      { τ₁ := cokernel.π (P.map ι)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := (cokernel.π_desc _ _ _).trans (Category.comp_id _).symm
        comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS'
  have hδPepi : Epi δP := by
    have h := DP.exact_δ₂ hS₂ 0
    exact (ShortComplex.exact_iff_epi _ (hR1I.eq_of_tgt _ _)).1 h
  have hS3 : S3.ShortExact := { exact := hS3e, mono_f := inferInstance, epi_g := epi_comp _ _ }
  have hH2' : IsZero (((Scheme.sectionsFunctor X).rightDerived 2).obj (P.obj G)) :=
    hH2.of_iso (((Scheme.sectionsFunctor X).rightDerived 2).mapIso
      (asIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom))).symm
  have hH1C := isZero_firstCohomology_of_shortExact hS₁ hPI hH2'
  exact subsingleton_sections_of_shortExact hS3 hH1C hmΓs

/-- A sheaf of modules on a scheme whose global sections form a subsingleton has a subsingleton
type of sections. -/
theorem subsingleton_sections_of_subsingleton {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf)
    (h : Subsingleton ((Scheme.sectionsFunctor X).obj M)) : Subsingleton M.sections := by
  refine ⟨fun s t => Subtype.ext (funext fun U => ?_)⟩
  rw [← s.2 (homOfLE (le_top : U.unop ≤ ⊤)).op, ← t.2 (homOfLE (le_top : U.unop ≤ ⊤)).op,
    @Subsingleton.elim _ h (s.1 (op ⊤)) (t.1 (op ⊤))]

/-- **The low-degree Leray sequence of [Stacks, Tag 0AXF] (1) over a two-dimensional local ring.**
Let `A` be a two-dimensional Noetherian normal local domain. For every modification
`f : X ⟶ Spec A` with `X` normal and every `g : X' ⟶ X` with `X'` normal and `g ≫ f` a
modification, `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})` is injective and, when it is onto, `R¹g_*𝒪_{X'}` has
no nonzero global section. -/
theorem lerayFirstCohomologyExact_of_ringKrullDim_eq_two (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    LerayFirstCohomologyExact A := by
  intro X X' f g hX hX' hf hgf
  have := hX
  have := hX'
  have : IsIntegral X := hf.source_isIntegral
  have : IsIntegral X' := hgf.source_isIntegral
  have hg : IsModification g := SeparableGoUp.isModification_of_comp hf hgf
  have : IsProper g := hg.isProper
  have : IsIso g.c := isIso_c_of_isBirational_of_isNormal g hg.isBirational
  have hH2 : IsZero (((Scheme.sectionsFunctor X).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
    let : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      IsGrothendieckAbelian.enoughInjectives
    let : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      hasExt_of_enoughInjectives _
    have h := subsingleton_cohomologyPresheaf_two_top_of_isModification A hdim f hf
    have h' := (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
      (structureAbelianSheaf X) 2).2 h
    exact (subsingleton_sheafH_unit_iff_isZero_rightDerived_evaluation X 2).1 h'
  obtain ⟨θ, hθ, hsurj⟩ := exists_injective_firstCohomology_and_sections_rightDerived_eq_zero g hH2
  exact ⟨{ toFun := θ
           map_add' := θ.map_add
           map_smul' := fun b x => θ.map_smulₛₗ _ x }, hθ,
    fun hs => subsingleton_sections_of_subsingleton _ (hsurj hs)⟩

end AlgebraicGeometry

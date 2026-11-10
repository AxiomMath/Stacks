module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.TorsionInFirstCohomology

/-!
# `H¹(Y, 𝒪_Y)` injects into `H¹(Y', 𝒪_{Y'})` when `q_* 𝒪_{Y'} = 𝒪_Y`

Let `q : Y' ⟶ Y` be a morphism of schemes for which `q_* 𝒪_{Y'} = 𝒪_Y`, the comparison being
`q^♯`. Then the map `H¹(Y, 𝒪_Y) ⟶ H¹(Y', 𝒪_{Y'})` is injective. This is the injectivity half of
the first conclusion of [Stacks, Tag 0AXF].

## Main results

* `AlgebraicGeometry.SeparableGoUp.exists_injective_firstCohomology`: an injective map
  `H¹(Y, 𝒪_Y) ⟶ H¹(Y', 𝒪_{Y'})`, semilinear along `q^♯ : Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})`.
* `AlgebraicGeometry.SeparableGoUp.length_firstCohomology_le_of_isIso_c`: for `Y` over `Spec B`
  and `q_* 𝒪_{Y'} = 𝒪_Y`, the length of `H¹(Y, 𝒪_Y)` over `B` is at most that of
  `H¹(Y', 𝒪_{Y'})`.

## References

* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SeparableGoUp

attribute [local instance] HasDerivedCategory.standard

variable {Y : Scheme.{u}}

/-- For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of modules on `Y` with
`H¹(Y, B) = 0`, the first cohomology of `A` is the cokernel of `Γ(Y, B) ⟶ Γ(Y, C)`. -/
theorem exists_firstCohomology_equiv_quotient
    {S : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf)} (hS : S.ShortExact)
    (hB : IsZero (((Scheme.sectionsFunctor Y).rightDerived 1).obj S.X₂)) :
    Nonempty (((Scheme.sectionsFunctor Y).obj S.X₃ ⧸
        LinearMap.range ((Scheme.sectionsFunctor Y).map S.g).hom) ≃ₗ[Scheme.sectionsRing Y]
      ((Scheme.sectionsFunctor Y).rightDerived 1).obj S.X₁) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (Scheme.sectionsFunctor Y)
  let δ' : ((Scheme.sectionsFunctor Y).rightDerived 0).obj S.X₃ ⟶
      ((Scheme.sectionsFunctor Y).rightDerived 1).obj S.X₁ := D.δ hS 0
  let u : Scheme.sectionsFunctor Y ⟶ (Scheme.sectionsFunctor Y).rightDerived 0 :=
    (Scheme.sectionsFunctor Y).toRightDerivedZero
  have e1 : LinearMap.range (((Scheme.sectionsFunctor Y).rightDerived 0).map S.g).hom =
      LinearMap.ker δ'.hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (D.exact_δ₁ hS 0)
  have e2 : LinearMap.range δ'.hom =
      LinearMap.ker (((Scheme.sectionsFunctor Y).rightDerived 1).map S.f).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (D.exact_δ₂ hS 0)
  have hsurj : Function.Surjective (u.app S.X₃ ≫ δ').hom := by
    intro y
    obtain ⟨w, rfl⟩ : y ∈ LinearMap.range δ'.hom :=
      e2 ▸ (ModuleCat.isZero_iff_subsingleton.mp hB).elim _ _
    obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (u.app S.X₃)).2 w
    exact ⟨x, by rw [ModuleCat.hom_comp, LinearMap.comp_apply, hx]⟩
  have hker : LinearMap.ker (u.app S.X₃ ≫ δ').hom =
      LinearMap.range ((Scheme.sectionsFunctor Y).map S.g).hom := by
    ext x
    have hnat : ∀ z,
        (((Scheme.sectionsFunctor Y).rightDerived 0).map S.g).hom ((u.app S.X₂).hom z) =
        (u.app S.X₃).hom (((Scheme.sectionsFunctor Y).map S.g).hom z) := fun z =>
      (congrArg (fun φ : (Scheme.sectionsFunctor Y).obj S.X₂ ⟶
        ((Scheme.sectionsFunctor Y).rightDerived 0).obj S.X₃ => φ.hom z) (u.naturality S.g)).symm
    refine ⟨fun hx => ?_, ?_⟩
    · have hx' : (u.app S.X₃).hom x ∈ LinearMap.ker δ'.hom := hx
      rw [← e1] at hx'
      obtain ⟨y, hy⟩ := hx'
      obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso (u.app S.X₂)).2 y
      refine ⟨z, (ConcreteCategory.bijective_of_isIso (u.app S.X₃)).1 ?_⟩
      rw [← hnat z, hy]
    · rintro ⟨z, rfl⟩
      change δ'.hom ((u.app S.X₃).hom (((Scheme.sectionsFunctor Y).map S.g).hom z)) = 0
      rw [← hnat z, ← LinearMap.mem_ker, ← e1]
      exact LinearMap.mem_range_self _ _
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((u.app S.X₃ ≫ δ').hom.quotKerEquivOfSurjective hsurj)⟩

variable {Y' : Scheme.{u}} (q : Y' ⟶ Y)

/-- The map `Γ(Y, 𝒪_Y) ⟶ Γ(Y', 𝒪_{Y'})` of a morphism, in the spelling of the rings of global
sections of the sheaves of rings. -/
abbrev sectionsRingHom : Scheme.sectionsRing Y →+* Scheme.sectionsRing Y' :=
  (q.toRingCatSheafHom.hom.app (op ⊤)).hom

/-- **`H¹(Y, q_* G)` injects into `H¹(Y', G)`**, semilinearly along `q^♯`, for every sheaf of
modules `G` on `Y'`. -/
theorem exists_injective_firstCohomology_pushforward (G : SheafOfModules.{u} Y'.ringCatSheaf) :
    ∃ θ : ((Scheme.sectionsFunctor Y).rightDerived 1).obj
        ((Scheme.Modules.pushforward q).obj G) →ₛₗ[sectionsRingHom q]
        ((Scheme.sectionsFunctor Y').rightDerived 1).obj G,
      Function.Injective θ := by
  let P := SheafOfModules.pushforward.{u} q.toRingCatSheafHom
  let I := Injective.under G
  let ι : G ⟶ I := Injective.ι G
  have : Mono ι := Injective.ι_mono G
  have : Injective I := Injective.injective_under G
  let πQ := cokernel.π ι
  have hS₂ : (ShortComplex.cokernelSequence ι).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := Injective.ι_mono G }
  have : P.IsRightAdjoint := (Scheme.Modules.pullbackPushforwardAdjunction q).isRightAdjoint
  have : PreservesFiniteLimits P := inferInstance
  have : P.Additive := inferInstanceAs (Scheme.Modules.pushforward q).Additive
  obtain ⟨hexact, hmonoP⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono P).1 inferInstance _ hS₂
  have hS₁ : (ShortComplex.cokernelSequence (P.map ι)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := hmonoP }
  have hI' : IsZero (((Scheme.sectionsFunctor Y').rightDerived 1).obj I) :=
    (Scheme.sectionsFunctor Y').isZero_rightDerived_obj_injective_succ 0 I
  have hPI : IsZero (((Scheme.sectionsFunctor Y).rightDerived 1).obj (P.obj I)) :=
    (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).1
      (Stacks.Cohomology.AffineComparison.rightAcyclic_moduleGlobalSections_pushforward_obj
        q I (Injective.injective_under G)) 1 Nat.one_pos
  obtain ⟨e₁⟩ := exists_firstCohomology_equiv_quotient hS₁ hPI
  obtain ⟨e₂⟩ := exists_firstCohomology_equiv_quotient hS₂ hI'
  have hzero : P.map ι ≫ P.map πQ = 0 :=
    (P.map_comp ι πQ).symm.trans ((congrArg P.map (cokernel.condition ι)).trans (P.map_zero _ _))
  let m : cokernel (P.map ι) ⟶ P.obj (cokernel ι) :=
    cokernel.desc (P.map ι) (P.map πQ) hzero
  have : Mono m := hexact.mono_cokernelDesc
  have hm : Function.Injective ((Scheme.sectionsFunctor Y).map m).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  let mΓ : (Scheme.sectionsFunctor Y).obj (cokernel (P.map ι)) →ₛₗ[sectionsRingHom q]
      (Scheme.sectionsFunctor Y').obj (cokernel ι) :=
    { toFun := fun c => ((Scheme.sectionsFunctor Y).map m).hom c
      map_add' := fun c c' => map_add _ c c'
      map_smul' := fun r c => ((Scheme.sectionsFunctor Y).map m).hom.map_smul r c }
  have hcomp : ∀ i : (Scheme.sectionsFunctor Y).obj (P.obj I),
      mΓ (((Scheme.sectionsFunctor Y).map (cokernel.π (P.map ι))).hom i) =
        ((Scheme.sectionsFunctor Y').map πQ).hom i := fun i => by
    change ((Scheme.sectionsFunctor Y).map (cokernel.π (P.map ι)) ≫
      (Scheme.sectionsFunctor Y).map m).hom i = _
    rw [← Functor.map_comp, cokernel.π_desc]
    rfl
  have hle : LinearMap.range ((Scheme.sectionsFunctor Y).map (cokernel.π (P.map ι))).hom ≤
      (LinearMap.range ((Scheme.sectionsFunctor Y').map πQ).hom).comap mΓ := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i, (hcomp i).symm⟩
  let θ₀ := Submodule.mapQ _ _ mΓ hle
  have hθ₀ : Function.Injective θ₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ z
    have hc : mΓ c ∈ LinearMap.range ((Scheme.sectionsFunctor Y').map πQ).hom := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact hz
    obtain ⟨i, hi⟩ := hc
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨i, hm ((hcomp i).trans hi)⟩
  exact ⟨(e₂.toLinearMap.comp θ₀).comp e₁.symm.toLinearMap,
    e₂.injective.comp (hθ₀.comp e₁.symm.injective)⟩

/-- The comparison `𝒪_Y ⟶ q_* 𝒪_{Y'}` is an isomorphism as soon as `q^♯` is. -/
theorem isIso_unitToPushforwardObjUnit [IsIso q.c] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom) := by
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _),
    ← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _), NatTrans.isIso_iff_isIso_app]
  intro U
  have : IsIso (q.c.app U) := inferInstance
  exact (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map_isIso (q.c.app U)

/-- **`H¹(Y, 𝒪_Y)` injects into `H¹(Y', 𝒪_{Y'})` when `q_* 𝒪_{Y'} = 𝒪_Y`**, semilinearly along
`q^♯`. -/
theorem exists_injective_firstCohomology [IsIso q.c] :
    ∃ θ : ((Scheme.sectionsFunctor Y).rightDerived 1).obj (SheafOfModules.unit Y.ringCatSheaf)
        →ₛₗ[sectionsRingHom q]
        ((Scheme.sectionsFunctor Y').rightDerived 1).obj (SheafOfModules.unit Y'.ringCatSheaf),
      Function.Injective θ := by
  have := isIso_unitToPushforwardObjUnit q
  obtain ⟨θ, hθ⟩ := exists_injective_firstCohomology_pushforward q
    (SheafOfModules.unit Y'.ringCatSheaf)
  let e := ((Scheme.sectionsFunctor Y).rightDerived 1).mapIso
    (asIso (SheafOfModules.unitToPushforwardObjUnit q.toRingCatSheafHom))
  exact ⟨θ.comp e.toLinearEquiv.toLinearMap, hθ.comp e.toLinearEquiv.injective⟩

/-- **The length of `H¹` only grows along a morphism with `q_* 𝒪_{Y'} = 𝒪_Y`.** For `Y` over
`Spec B` and `q : Y' ⟶ Y` with `q^♯` an isomorphism, the length of `H¹(Y, 𝒪_Y)` over `B` is at
most that of `H¹(Y', 𝒪_{Y'})`. -/
theorem length_firstCohomology_le_of_isIso_c {B : Type u} [CommRing B] (g : Y ⟶ Spec (.of B))
    [IsIso q.c] :
    Module.length B (firstCohomologyAsBaseModule Y g) ≤
      Module.length B (firstCohomologyAsBaseModule Y' (q ≫ g)) := by
  obtain ⟨θ, hθ⟩ := exists_injective_firstCohomology q
  let θ' : firstCohomologyAsBaseModule Y g →ₗ[B] firstCohomologyAsBaseModule Y' (q ≫ g) :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun b x => θ.map_smulₛₗ _ x }
  exact Module.length_le_of_injective θ' hθ

end AlgebraicGeometry.SeparableGoUp

end

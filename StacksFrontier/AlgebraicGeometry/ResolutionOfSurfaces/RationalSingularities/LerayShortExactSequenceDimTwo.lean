module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayFirstCohomologyDimTwo
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.HigherDirectImageBoundedness
import StacksCore.Tactic.StacksAttribute

/-!
# The short exact sequence of the low-degree Leray sequence of a morphism of modifications

Let `g : X' ⟶ X` be a morphism of schemes with `g^♯ : 𝒪_X ⟶ g_*𝒪_{X'}` an isomorphism and with
`H²(X, 𝒪_X) = 0`.  Then

  `0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0`

is a short exact sequence of modules over `Γ(X, 𝒪_X)`.  For a two-dimensional Noetherian normal
local domain `A`, a modification `f : X ⟶ Spec(A)` with `X` normal and a morphism `g : X' ⟶ X`
whose composite with `f` is again a modification, both hypotheses hold: `g` is proper and
birational onto the normal scheme `X`, and the fibres of `f` have dimension at most one.

The sequence is read off one injective resolution step `0 ⟶ 𝒪_{X'} ⟶ I ⟶ Q ⟶ 0` on `X'`.  With
`C = coker(𝒪_X ⟶ g_*I)` there are short exact sequences `0 ⟶ 𝒪_X ⟶ g_*I ⟶ C ⟶ 0` and
`0 ⟶ C ⟶ g_*Q ⟶ R¹g_*𝒪_{X'} ⟶ 0`, the second because `g_*` is exact and kills the higher
cohomology of an injective.  As `H¹(X, g_*I) = 0` and `H¹(X', I) = 0`, the first cohomology
groups are the quotients `H¹(X, 𝒪_X) = Γ(X, C)/Γ(X, g_*I)` and
`H¹(X', 𝒪_{X'}) = Γ(X', Q)/Γ(X', I)`, and `Γ(X, C)` is a submodule of `Γ(X, g_*Q) = Γ(X', Q)`
containing the image of `Γ(X', I)`.  The vanishing of `H²(X, 𝒪_X)` forces `H¹(X, C) = 0`, so
`Γ(X, R¹g_*𝒪_{X'}) = Γ(X', Q)/Γ(X, C)`.  The sequence is then the tower of submodules

  `Γ(X', I) ⊆ Γ(X, C) ⊆ Γ(X', Q)`.

## Main results

* `AlgebraicGeometry.exists_shortExact_of_tower`: the elementary step, a tower of two submodules
  read as a short exact sequence of the quotients.
* `AlgebraicGeometry.sections_surjective_and_ker_eq_range_of_shortExact`: global sections take a
  short exact sequence whose subobject has vanishing `H¹` to a short exact sequence of modules.
* `AlgebraicGeometry.exists_surjective_firstCohomology_of_shortExact`: the connecting map
  `Γ(Y, C) ⟶ H¹(Y, A)` of a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` with `H¹(Y, B) = 0`, as a
  surjection whose kernel is the image of `Γ(Y, B)`.
* `AlgebraicGeometry.exists_shortExact_firstCohomology_pushforward`: the short exact sequence,
  for a morphism with `g_*𝒪_{X'} = 𝒪_X` and `H²(X, 𝒪_X) = 0`.
* `AlgebraicGeometry.SemistableReduction.TwoModifications.exists_shortExact_firstCohomology`:
  the short exact sequence for two modifications of the spectrum of a two-dimensional Noetherian
  normal local domain.

## References

* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A tower of two submodules read as a short exact sequence of quotients.**  Let `σ : R →+* S`,
let `mh : N ⟶ M` be an injective `R`-linear map, and let `p₁ : N ⟶ W₁`, `p₂ : M ⟶ W₂` and
`q : M ⟶ W₃` be surjections, `p₂` semilinear along `σ`, whose kernels are the image of
`ah : A ⟶ N`, the image of `mh ∘ ah` and the image of `mh`.  Then there are maps
`W₁ ⟶ W₂ ⟶ W₃` making `0 ⟶ W₁ ⟶ W₂ ⟶ W₃ ⟶ 0` exact. -/
theorem exists_shortExact_of_tower {R S : Type*} [Ring R] [Ring S] (σ : R →+* S)
    {A N M W₁ W₂ W₃ : Type*} [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [AddCommGroup W₁] [Module R W₁] [AddCommGroup W₂]
    [Module S W₂] [AddCommGroup W₃] [Module R W₃]
    (ah : A →ₗ[R] N) (mh : N →ₗ[R] M) (p₁ : N →ₗ[R] W₁) (p₂ : M →ₛₗ[σ] W₂) (q : M →ₗ[R] W₃)
    (hmh : Function.Injective mh) (hp₁surj : Function.Surjective p₁)
    (hp₂surj : Function.Surjective p₂) (hqsurj : Function.Surjective q)
    (hp₁zero : ∀ n, p₁ n = 0 ↔ ∃ i, ah i = n)
    (hp₂zero : ∀ x, p₂ x = 0 ↔ ∃ i, mh (ah i) = x)
    (hqzero : ∀ x, q x = 0 ↔ ∃ n, mh n = x) :
    ∃ (θ : W₁ →ₛₗ[σ] W₂) (ψ : W₂ →+ W₃),
      Function.Injective θ ∧ (∀ (r : R) y, ψ (σ r • y) = r • ψ y) ∧
        (∀ y, ψ y = 0 ↔ ∃ x, θ x = y) ∧ Function.Surjective ψ := by
  classical
  have hs₁ := hp₁surj
  have hs₂ := hp₂surj
  choose lift₁ hlift₁ using hs₁
  choose lift₂ hlift₂ using hs₂
  set θf : W₁ → W₂ := fun w => p₂ (mh (lift₁ w))
  set ψf : W₂ → W₃ := fun y => q (lift₂ y)
  have hθspec : ∀ n, θf (p₁ n) = p₂ (mh n) := by
    intro n
    have hd : p₁ (lift₁ (p₁ n) - n) = 0 := by rw [map_sub, hlift₁, sub_self]
    obtain ⟨i, hi⟩ := (hp₁zero _).1 hd
    have hsplit : mh (lift₁ (p₁ n)) = mh n + mh (ah i) := by
      rw [hi, ← map_add]
      congr 1
      abel
    change p₂ (mh (lift₁ (p₁ n))) = p₂ (mh n)
    rw [hsplit, map_add, (hp₂zero (mh (ah i))).2 ⟨i, rfl⟩, add_zero]
  have hψspec : ∀ x, ψf (p₂ x) = q x := by
    intro x
    have hd : p₂ (lift₂ (p₂ x) - x) = 0 := by rw [map_sub, hlift₂, sub_self]
    obtain ⟨i, hi⟩ := (hp₂zero _).1 hd
    have hq0 : q (lift₂ (p₂ x) - x) = 0 := by
      rw [← hi]
      exact (hqzero _).2 ⟨ah i, rfl⟩
    change q (lift₂ (p₂ x)) = q x
    rw [map_sub] at hq0
    exact sub_eq_zero.1 hq0
  have hθadd : ∀ w w', θf (w + w') = θf w + θf w' := by
    intro w w'
    obtain ⟨n, rfl⟩ := hp₁surj w
    obtain ⟨n', rfl⟩ := hp₁surj w'
    rw [← map_add, hθspec, hθspec, hθspec, map_add, map_add]
  have hθsmul : ∀ (r : R) w, θf (r • w) = σ r • θf w := by
    intro r w
    obtain ⟨n, rfl⟩ := hp₁surj w
    rw [← map_smul, hθspec, hθspec, map_smul, map_smulₛₗ]
  have hψadd : ∀ y y', ψf (y + y') = ψf y + ψf y' := by
    intro y y'
    obtain ⟨x, rfl⟩ := hp₂surj y
    obtain ⟨x', rfl⟩ := hp₂surj y'
    rw [← map_add, hψspec, hψspec, hψspec, map_add]
  have hθinj : ∀ w, θf w = 0 → w = 0 := by
    intro w hw
    obtain ⟨n, rfl⟩ := hp₁surj w
    rw [hθspec] at hw
    obtain ⟨i, hi⟩ := (hp₂zero _).1 hw
    exact (hp₁zero n).2 ⟨i, hmh hi⟩
  let Θ : W₁ →ₛₗ[σ] W₂ :=
    { toAddHom := { toFun := θf, map_add' := hθadd }, map_smul' := hθsmul }
  refine ⟨Θ, AddMonoidHom.mk' ψf hψadd, ?_, ?_, ?_, ?_⟩
  · exact (injective_iff_map_eq_zero Θ).2 hθinj
  · intro r y
    obtain ⟨x, rfl⟩ := hp₂surj y
    change ψf (σ r • p₂ x) = r • ψf (p₂ x)
    rw [← map_smulₛₗ, hψspec, hψspec, map_smul]
  · intro y
    refine ⟨fun hy => ?_, ?_⟩
    · obtain ⟨x, rfl⟩ := hp₂surj y
      obtain ⟨n, rfl⟩ := (hqzero x).1 ((hψspec x).symm.trans hy)
      exact ⟨p₁ n, hθspec n⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨n, hn⟩ := hp₁surj z
      change ψf (θf z) = 0
      rw [← hn, hθspec, hψspec]
      exact (hqzero _).2 ⟨n, rfl⟩
  · intro t
    obtain ⟨x, rfl⟩ := hqsurj t
    exact ⟨p₂ x, hψspec x⟩

attribute [local instance] HasDerivedCategory.standard

/-- **Global sections of a short exact sequence whose subobject has no first cohomology.**  For a
short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of modules on `Y` with `H¹(Y, A) = 0`, the
map `Γ(Y, B) ⟶ Γ(Y, C)` is surjective and its kernel is the image of `Γ(Y, A)`. -/
theorem sections_surjective_and_ker_eq_range_of_shortExact {Y : Scheme.{u}}
    {S : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf)} (hS : S.ShortExact)
    (hA : IsZero (((Scheme.sectionsFunctor Y).rightDerived 1).obj S.X₁)) :
    Function.Surjective ((Scheme.sectionsFunctor Y).map S.g).hom ∧
      LinearMap.ker ((Scheme.sectionsFunctor Y).map S.g).hom =
        LinearMap.range ((Scheme.sectionsFunctor Y).map S.f).hom := by
  let Γ := Scheme.sectionsFunctor Y
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives Γ
  let u : Γ ⟶ Γ.rightDerived 0 := Γ.toRightDerivedZero
  have hnat : ∀ {A B : SheafOfModules.{u} Y.ringCatSheaf} (h : A ⟶ B) (z : Γ.obj A),
      ((Γ.rightDerived 0).map h).hom ((u.app A).hom z) = (u.app B).hom ((Γ.map h).hom z) :=
    fun h z => (congrArg (fun φ => φ.hom z) (u.naturality h)).symm
  refine ⟨?_, ?_⟩
  · have hepi0 : Epi ((Γ.rightDerived 0).map S.g) :=
      (ShortComplex.exact_iff_epi _ (hA.eq_of_tgt _ _)).1 (D.exact_δ₁ hS 0)
    have : Epi (Γ.map S.g) := by
      rw [(IsIso.eq_comp_inv (u.app S.X₃)).2 (u.naturality S.g)]
      exact epi_comp _ _
    exact (ModuleCat.epi_iff_surjective _).1 this
  · have hrk : LinearMap.range ((Γ.rightDerived 0).map S.f).hom =
        LinearMap.ker ((Γ.rightDerived 0).map S.g).hom := by
      have h := D.exact_map hS 0
      rwa [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    ext x
    refine ⟨fun hx => ?_, ?_⟩
    · have hx0 : (Γ.map S.g).hom x = 0 := hx
      have h1 : (u.app S.X₂).hom x ∈ LinearMap.ker ((Γ.rightDerived 0).map S.g).hom := by
        change ((Γ.rightDerived 0).map S.g).hom ((u.app S.X₂).hom x) = 0
        rw [hnat S.g x, hx0, map_zero]
      rw [← hrk] at h1
      obtain ⟨w, hw⟩ := h1
      obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (u.app S.X₁)).2 w
      refine ⟨z, (ConcreteCategory.bijective_of_isIso (u.app S.X₂)).1 ?_⟩
      rw [← hnat S.f z, hz, hw]
    · rintro ⟨z, rfl⟩
      change ((Γ.map S.f) ≫ (Γ.map S.g)).hom z = 0
      rw [← Functor.map_comp, S.zero, Functor.map_zero]
      rfl

/-- **The connecting map of a short exact sequence whose middle term has no first cohomology.**
For a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of modules on `Y` with `H¹(Y, B) = 0`
there is a surjection `Γ(Y, C) ⟶ H¹(Y, A)` whose kernel is the image of `Γ(Y, B)`. -/
theorem exists_surjective_firstCohomology_of_shortExact {Y : Scheme.{u}}
    {S : ShortComplex (SheafOfModules.{u} Y.ringCatSheaf)} (hS : S.ShortExact)
    (hB : IsZero (((Scheme.sectionsFunctor Y).rightDerived 1).obj S.X₂)) :
    ∃ p : (Scheme.sectionsFunctor Y).obj S.X₃ →ₗ[Scheme.sectionsRing Y]
        ((Scheme.sectionsFunctor Y).rightDerived 1).obj S.X₁,
      Function.Surjective p ∧
        LinearMap.ker p = LinearMap.range ((Scheme.sectionsFunctor Y).map S.g).hom := by
  obtain ⟨e⟩ := SeparableGoUp.exists_firstCohomology_equiv_quotient hS hB
  refine ⟨e.toLinearMap.comp (Submodule.mkQ _),
    e.surjective.comp (Submodule.mkQ_surjective _), ?_⟩
  rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.2 e.injective, Submodule.comap_bot,
    Submodule.ker_mkQ]

/-- **[Stacks, Tag 0AXF], first conclusion, for a morphism with `g_*𝒪_{X'} = 𝒪_X` and
`H²(X, 𝒪_X) = 0`.**  There is a short exact sequence

  `0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0`

of modules over `Γ(X, 𝒪_X)`: the first map is injective and semilinear along `g^♯`, its image is
the kernel of the second, and the second is surjective and carries the `g^♯`-twisted action to
the action of `Γ(X, 𝒪_X)`.  Both maps come from one injective resolution step on `X'`. -/
theorem exists_shortExact_firstCohomology_pushforward {X X' : Scheme.{u}} (g : X' ⟶ X)
    [IsIso g.c]
    (hH2 : IsZero (((Scheme.sectionsFunctor X).rightDerived 2).obj
      (SheafOfModules.unit X.ringCatSheaf))) :
    ∃ (θ : ((Scheme.sectionsFunctor X).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)
          →ₛₗ[SeparableGoUp.sectionsRingHom g]
        ((Scheme.sectionsFunctor X').rightDerived 1).obj (SheafOfModules.unit X'.ringCatSheaf))
      (ψ : (((Scheme.sectionsFunctor X').rightDerived 1).obj
            (SheafOfModules.unit X'.ringCatSheaf)) →+
        (Scheme.sectionsFunctor X).obj (((Scheme.Modules.pushforward g).rightDerived 1).obj
          (SheafOfModules.unit X'.ringCatSheaf))),
      Function.Injective θ ∧
        (∀ (r : Scheme.sectionsRing X) y, ψ (SeparableGoUp.sectionsRingHom g r • y) = r • ψ y) ∧
        (∀ y, ψ y = 0 ↔ ∃ x, θ x = y) ∧
        Function.Surjective ψ := by
  let Γ := Scheme.sectionsFunctor X
  let Γ' := Scheme.sectionsFunctor X'
  let G := SheafOfModules.unit X'.ringCatSheaf
  let P := SheafOfModules.pushforward.{u} g.toRingCatSheafHom
  have := SeparableGoUp.isIso_unitToPushforwardObjUnit g
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
  obtain ⟨hexactP, hmonoP⟩ :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono P).1 inferInstance _ hS₂
  have hS₁ : (ShortComplex.cokernelSequence (P.map ι)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := hmonoP }
  have hI' : IsZero ((Γ'.rightDerived 1).obj I) := Γ'.isZero_rightDerived_obj_injective_succ 0 I
  have hPI : IsZero ((Γ.rightDerived 1).obj (P.obj I)) := by
    let := HasDerivedCategory.standard X.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
    exact (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).1
      (Stacks.Cohomology.AffineComparison.rightAcyclic_moduleGlobalSections_pushforward_obj g I
        (Injective.injective_under G)) 1 Nat.one_pos
  -- the comparison `C ⟶ g_* Q`, injective on global sections
  have hzero : P.map ι ≫ P.map πQ = 0 :=
    (P.map_comp ι πQ).symm.trans ((congrArg P.map (cokernel.condition ι)).trans (P.map_zero _ _))
  let m : cokernel (P.map ι) ⟶ P.obj (cokernel ι) := cokernel.desc (P.map ι) (P.map πQ) hzero
  have : Mono m := hexactP.mono_cokernelDesc
  have hm : Function.Injective (Γ.map m).hom := (ModuleCat.mono_iff_injective _).1 inferInstance
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
  have hδPepi : Epi δP := (ShortComplex.exact_iff_epi _ (hR1I.eq_of_tgt _ _)).1 (DP.exact_δ₂ hS₂ 0)
  have hS3 : S3.ShortExact := { exact := hS3e, mono_f := inferInstance, epi_g := epi_comp _ _ }
  have hH1C : IsZero ((Γ.rightDerived 1).obj (cokernel (P.map ι))) :=
    isZero_firstCohomology_of_shortExact hS₁ hPI <| hH2.of_iso ((Γ.rightDerived 2).mapIso
      (asIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom))).symm
  -- the three surjections of the tower
  obtain ⟨p₁, hp₁surj, hp₁ker⟩ := exists_surjective_firstCohomology_of_shortExact hS₁ hPI
  obtain ⟨p₂, hp₂surj, hp₂ker⟩ := exists_surjective_firstCohomology_of_shortExact hS₂ hI'
  obtain ⟨hqsurj, hqker⟩ := sections_surjective_and_ker_eq_range_of_shortExact hS3 hH1C
  let e := (Γ.rightDerived 1).mapIso
    (asIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom))
  -- the maps of the tower, with the `Γ(X, 𝒪_X)`-module `Γ(X, g_* Q)` as middle term
  let mh : Γ.obj (cokernel (P.map ι)) →ₗ[Scheme.sectionsRing X] Γ.obj (P.obj (cokernel ι)) :=
    (Γ.map m).hom
  let ah : Γ.obj (P.obj I) →ₗ[Scheme.sectionsRing X] Γ.obj (cokernel (P.map ι)) :=
    (Γ.map (cokernel.π (P.map ι))).hom
  let q : Γ.obj (P.obj (cokernel ι)) →ₗ[Scheme.sectionsRing X]
      Γ.obj ((P.rightDerived 1).obj G) := (Γ.map S3.g).hom
  let eL := e.toLinearEquiv
  let p₁' : Γ.obj (cokernel (P.map ι)) →ₗ[Scheme.sectionsRing X]
      (Γ.rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf) := eL.symm.toLinearMap.comp p₁
  let p₂' : Γ.obj (P.obj (cokernel ι)) →ₛₗ[SeparableGoUp.sectionsRingHom g]
      (Γ'.rightDerived 1).obj G :=
    { toFun := fun x => p₂ x
      map_add' := fun x x' => map_add _ x x'
      map_smul' := fun r x => p₂.map_smul _ x }
  have hcomp : ∀ i, mh (ah i) = (Γ'.map πQ).hom i := by
    intro i
    change (Γ.map (cokernel.π (P.map ι)) ≫ Γ.map m).hom i = _
    rw [← Functor.map_comp, cokernel.π_desc]
    rfl
  have hp₁zero : ∀ n, p₁' n = 0 ↔ ∃ i, ah i = n := fun n => by
    have hiff : p₁' n = 0 ↔ p₁ n = 0 := by
      change eL.symm (p₁ n) = 0 ↔ p₁ n = 0
      exact eL.symm.map_eq_zero_iff
    exact hiff.trans (SetLike.ext_iff.1 hp₁ker n)
  have hp₂zero : ∀ x, p₂' x = 0 ↔ ∃ i, mh (ah i) = x := fun x => by
    simp only [hcomp]
    exact SetLike.ext_iff.1 hp₂ker x
  have hqzero : ∀ x, q x = 0 ↔ ∃ n, mh n = x := fun x => SetLike.ext_iff.1 hqker x
  exact exists_shortExact_of_tower (SeparableGoUp.sectionsRingHom g) ah mh p₁' p₂' q hm
    (eL.symm.surjective.comp hp₁surj) hp₂surj hqsurj hp₁zero hp₂zero hqzero

namespace SemistableReduction.TwoModifications

variable (S : TwoModifications.{u})

/-- `H²(X, 𝒪_X) = 0` for the intermediate scheme of two modifications: the fibres of
`f : X ⟶ Spec(A)` have dimension at most one and the base is affine and Noetherian. -/
theorem isZero_rightDerived_two_sections_unit :
    IsZero (((Scheme.sectionsFunctor S.X).rightDerived 2).obj
      (SheafOfModules.unit S.X.ringCatSheaf)) := by
  let : EnoughInjectives (Sheaf (Opens.grothendieckTopology S.X) AddCommGrpCat.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology S.X) AddCommGrpCat.{u}) :=
    hasExt_of_enoughInjectives _
  exact (subsingleton_sheafH_unit_iff_isZero_rightDerived_evaluation S.X 2).1
    ((Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top
      (structureAbelianSheaf S.X) 2).2
      (subsingleton_cohomologyPresheaf_two_top_of_isModification S.A
        S.situation.dimension_two S.f S.situation.modification))

/-- **[Stacks, Tag 0AXF], first conclusion.**  There is a short exact sequence

  `0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0`

of modules over `Γ(X, 𝒪_X)`: the first map is injective and semilinear along `g^♯`, its image is
the kernel of the second, and the second is surjective and carries the `g^♯`-twisted action to
the action of `Γ(X, 𝒪_X)`. -/
@[stacks 0AXF "the short exact sequence 0 → H¹(X, 𝒪_X) → H¹(X', 𝒪_{X'}) → H⁰(X, R¹g_*𝒪_{X'}) → 0"]
theorem exists_shortExact_firstCohomology :
    ∃ (θ : ((Scheme.sectionsFunctor S.X).rightDerived 1).obj
            (SheafOfModules.unit S.X.ringCatSheaf)
          →ₛₗ[SeparableGoUp.sectionsRingHom S.g]
        ((Scheme.sectionsFunctor S.X').rightDerived 1).obj
          (SheafOfModules.unit S.X'.ringCatSheaf))
      (ψ : (((Scheme.sectionsFunctor S.X').rightDerived 1).obj
            (SheafOfModules.unit S.X'.ringCatSheaf)) →+
        (Scheme.sectionsFunctor S.X).obj (((Scheme.Modules.pushforward S.g).rightDerived 1).obj
          (SheafOfModules.unit S.X'.ringCatSheaf))),
      Function.Injective θ ∧
        (∀ (r : Scheme.sectionsRing S.X) y,
          ψ (SeparableGoUp.sectionsRingHom S.g r • y) = r • ψ y) ∧
        (∀ y, ψ y = 0 ↔ ∃ x, θ x = y) ∧
        Function.Surjective ψ := by
  have : IsIso S.g.c := isIso_c_of_isBirational_of_isNormal S.g S.isBirational_g
  exact exists_shortExact_firstCohomology_pushforward S.g S.isZero_rightDerived_two_sections_unit

end SemistableReduction.TwoModifications

end AlgebraicGeometry

end

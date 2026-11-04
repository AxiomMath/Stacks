module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections

/-!
# The diagonal condition on an affine chart, from the algebraic side

Let `f : X ⟶ S` be flat and locally of finite presentation, `W ⊆ X ×_S X` an open through which
the relative diagonal factors as a closed immersion `Δ : X ⟶ W`, and `U ⊆ X`, `V ⊆ S` affine
opens with `U ⊆ f⁻¹(V)`; put `R = Γ(S, V)` and `A = Γ(X, U)`. The proof of Stacks 0E2U carries
the condition on `ξ` of a relative dualizing complex to the condition of Stacks 0E2C on
`RΓ(U, K)`, through a chain of isomorphisms: the ring identification `Γ(U ×_V U) ≅ A ⊗_R A`,
the affine comparison of Stacks 0A78 part (2) on the chart `U ×_V U`, and the reading of derived
sheaf Hom with exact support on `W ∩ (U ×_V U)`. Every step of that chain is an isomorphism of
objects, so it runs backwards, which is what the proof of Stacks 0E2X does ("arguing backwards
through the proof of Lemma 0E2U"): if `K` has quasi-coherent cohomology and `RΓ(U, K)` is a
relative dualizing complex for `R → A`, then `R ℰom(𝒪_X, L pr₁^*K|_W)` is `𝒪_U[0]` over `U`.
When `U` is all of `X`, Stacks 0A77 turns this into an isomorphism
`Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)` of objects.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_restrict_diagonalExactSupport_iso`: if
  `RΓ(U, K)` is a relative dualizing complex for `R → A`, then
  `R ℰom(𝒪_X, L pr₁^*K|_W)|_U ≅ 𝒪_U[0]`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_diagonalObject_iso_derivedSheafHom`: for
  `U = X`, `Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`.

## Implementation notes

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model at
which `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex`, `Dualizing.derivedHom` and the
chart comparisons of Stacks 0E2U are stated.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Definition 47.27.1 (Tag 0E2C)](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- If `β : Hom(B, L) → End(B)` is injective, `End(B)`-linear for precomposition and sends `ζ₁`
to `𝟙 B`, then `Hom(B, L)` is free of rank one over `End(B)` with basis `ζ₁`. -/
private theorem CategoryTheory.exists_eq_comp_and_cancel_of_injective.{v, w} {C : Type w}
    [Category.{v} C] {B L : C} (β : (B ⟶ L) → (B ⟶ B)) (hinj : Function.Injective β)
    (hcomp : ∀ (x : B ⟶ B) ζ, β (x ≫ ζ) = x ≫ β ζ) (ζ₁ : B ⟶ L) (h₁ : β ζ₁ = 𝟙 B) :
    (∀ ζ, ∃ x : B ⟶ B, ζ = x ≫ ζ₁) ∧ ∀ x y : B ⟶ B, x ≫ ζ₁ = y ≫ ζ₁ → x = y :=
  ⟨fun ζ => ⟨β ζ, hinj (by rw [hcomp, h₁, Category.comp_id])⟩, fun x y hxy => by
    have := congrArg β hxy
    rwa [hcomp, hcomp, h₁, Category.comp_id, Category.comp_id] at this⟩

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U)
  (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V)

/-- Pushing `𝒪[0]` forward along the inverse of an isomorphism of schemes `e : Y ≅ Z` gives
`𝒪_Y[0]`. -/
private def pushforwardInvStructureSingleIso {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (Modules.pushforward e.inv).mapDerivedCategory.obj (structureSingle Z) ≅ structureSingle Y :=
  ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
    (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv e)).app _).symm ≪≫
    restrictStructureSingleIso e.hom

open CochainComplex.DerivedExtensionScalars in
/-- **The diagonal condition of Stacks 0E2C, transported to the chart.** If
`RHom_{A ⊗_R A}(A, M ⊗ᴸ_A (A ⊗_R A))` is `A` in degree zero, then so is derived Hom from
`Γ(X, U)` over `Γ(U ×_V U, ⊤)` into the derived pullback of `M` along the first projection. This
is the converse of `nonempty_diagonalDerivedHom_iso_of_chart`. -/
theorem nonempty_chartDerivedHom_iso_of_diagonal [Flat f] [LocallyOfFinitePresentation f]
    (M : DerivedCategory (ModuleCat.{u} Γ(X, U)))
    (h : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
      Nonempty ((Dualizing.derivedHom.{u, u} (Algebra.TensorProduct.lmul' Γ(S, V) :
        Γ(X, U) ⊗[Γ(S, V)] Γ(X, U) →ₐ[Γ(S, V)] Γ(X, U)).toRingHom).obj
          ((Dualizing.diagonalDerivedExtension Γ(S, V) Γ(X, U)).obj M) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
          (ModuleCat.of Γ(X, U) Γ(X, U)))) :
    Nonempty ((Dualizing.derivedHom.{u, u} (chartDiagonalRing hUV).hom).obj
        ((totalDerivedExtensionScalars.{u, u, u} (chartProjRing hUV).hom).functor.obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U))) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  obtain ⟨e₀⟩ := h
  obtain ⟨e₁⟩ := nonempty_diagonalDerivedExtension_iso_chart hU hV hUV M
  let ePush := chartSquareRingEquiv hU hV hUV
  let f' := (RingEquiv.refl Γ(X, U)).symm.toRingHom.comp
    ((chartDiagonalRing hUV).hom.comp ePush.toRingHom)
  have hf' : f' = (Algebra.TensorProduct.lmul' Γ(S, V) :
      Γ(X, U) ⊗[Γ(S, V)] Γ(X, U) →ₐ[Γ(S, V)] Γ(X, U)).toRingHom :=
    chartDiagonalRing_comp_ringEquiv hU hV hUV
  have e₂ := StacksDraft.DerivedRingEquivIso.derivedHomRingEquivIso.{u, 0} ePush
    (RingEquiv.refl Γ(X, U)) (chartDiagonalRing hUV).hom
  let EC := Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u, u, u} (RingEquiv.refl Γ(X, U)))
  have e₃ : EC.functor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
      (ModuleCat.of Γ(X, U) Γ(X, U))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U)) :=
    (Dualizing.mapDerivedCategoryIdIso).app _
  have χ := (Dualizing.derivedHom.{u, u} _).mapIso e₁ ≪≫
    eqToIso (congrArg (fun g => (Dualizing.derivedHom.{u, u} g).obj _) hf'.symm) ≪≫ e₂.app _
  exact ⟨EC.fullyFaithfulFunctor.preimageIso (χ.symm ≪≫ e₀ ≪≫ e₃.symm)⟩

open Stacks.Duality.ClosedImmersionRestriction in
include hU hV in
/-- **The affine computation on the chart, backwards**, Stacks 0A78 part (2). Let
`φ : Γ(U ×_V U, ⊤) ⟶ Γ(X, U)` be the ring map of the diagonal `U ⟶ U ×_V U`, let `N` be a
bounded below object of `D(Γ(U ×_V U, ⊤))` and let `L'` be the sheaf associated to `N`. If
`R Hom_{Γ(U ×_V U, ⊤)}(Γ(X, U), N)` is `Γ(X, U)[0]`, then derived sheaf Hom with exact support
along the diagonal carries `L'` to `𝒪_U[0]`. This is the converse of
`nonempty_derivedHom_iso_of_chartExactSupport`. -/
theorem nonempty_chartExactSupport_iso_of_derivedHom [Flat f] [LocallyOfFinitePresentation f]
    (L' : DerivedCategory (chartSquare hUV).Modules)
    (φ : Γ(chartSquare hUV, ⊤) ⟶ Γ(X, U))
    (hφ : haveI := isAffine_chartSquare hU hV hUV
      chartDiagonal hUV ≫ (chartSquare hUV).isoSpec.hom = hU.isoSpec.hom ≫ Spec.map φ)
    (N : DerivedCategory (ModuleCat.{u} Γ(chartSquare hUV, ⊤)))
    (hN : DerivedCategoryB.IsBoundedBelow N)
    (eN : haveI := isAffine_chartSquare hU hV hUV
      L' ≅ (Modules.pushforward (chartSquare hUV).isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor _).mapDerivedCategory.obj N))
    (h : Nonempty ((Dualizing.derivedHom.{u, u, u} φ.hom).obj N ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U)))) :
    haveI := isClosedImmersion_chartDiagonal hU hV hUV
    Nonempty ((cq (chartDiagonal hUV)).derivedSheafHomExactSupport.obj L' ≅
      structureSingle U.toScheme) := by
  have := isAffine_chartSquare hU hV hUV
  have := isClosedImmersion_chartDiagonal hU hV hUV
  obtain ⟨e₀⟩ := h
  have hSpec :
      Spec.map φ = hU.isoSpec.inv ≫ chartDiagonal hUV ≫ (chartSquare hUV).isoSpec.hom := by
    rw [hφ, Iso.inv_hom_id_assoc]
  have : IsClosedImmersion (Spec.map φ) := by
    rw [hSpec]
    infer_instance
  have hpc : PseudoCoherent (Spec.map φ) := by
    have : PseudoCoherent (chartDiagonal hUV) := by
      have : PseudoCoherent (chartDiagonal hUV ≫ pullback.fst (chartMap hUV) (chartMap hUV) ≫
          chartMap hUV) := by
        rw [pullback.diagonal_fst_assoc]
        infer_instance
      exact pseudoCoherent_of_comp _ (pullback.fst (chartMap hUV) (chartMap hUV) ≫ chartMap hUV)
    rw [hSpec]
    infer_instance
  have := isIso_affineDerivedSheafHomComparison_app _ _ φ hpc N hN
  have e₁ : (Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.obj
      ((tilde.functor Γ(X, U)).mapDerivedCategory.obj
        ((Dualizing.derivedHom.{u, u, u} φ.hom).obj N)) ≅
      (cq (chartDiagonal hUV)).derivedSheafHomExactSupport.obj L' :=
    (Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.mapIso
      (asIso ((affineDerivedSheafHomComparison _ _ φ).app N)) ≪≫
    ((derivedSheafHomTransportIso (chartDiagonal hUV) (Spec.map φ) hU.isoSpec
      (chartSquare hUV).isoSpec hφ).app _).symm ≪≫
    (cq (chartDiagonal hUV)).derivedSheafHomExactSupport.mapIso eN.symm
  let e₃ : (tilde.functor Γ(X, U)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U))) ≅ structureSingle (Spec Γ(X, U)) :=
    ((tilde.functor Γ(X, U)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso tildeSelf
  exact ⟨e₁.symm ≪≫ (Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.mapIso
    ((tilde.functor Γ(X, U)).mapDerivedCategory.mapIso e₀ ≪≫ e₃) ≪≫
    pushforwardInvStructureSingleIso hU.isoSpec⟩

/-! ### Reading `R ℰom(𝒪_X, L pr₁^*K|_W)` from the chart -/

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

variable (D : DiagonalOpen f)

open Stacks.Duality.ClosedImmersionRestriction in
include hU hV in
/-- **`R ℰom(𝒪_X, L pr₁^*K|_W)` over `U`, from the chart.** If `L'` agrees with
`L pr₁^*K|_W` on `W ∩ (U ×_V U)` and derived sheaf Hom with exact support along the diagonal
`U ⟶ U ×_V U` carries `L'` to `𝒪_U[0]`, then `R ℰom(𝒪_X, L pr₁^*K|_W)` restricted to
`Δ⁻¹(W ∩ (U ×_V U)) = U` is `𝒪[0]`. This is the converse of `nonempty_chartExactSupport_iso`. -/
theorem nonempty_restrict_diagonalExactSupport_iso_of_chart (K : DerivedCategory X.Modules)
    (L' : DerivedCategory (chartSquare hUV).Modules)
    (eL : (Modules.restrictFunctor (D.chartOpen hUV).ι).mapDerivedCategory.obj
        (D.derivedPullbackProj K) ≅
      (Modules.pushforward (D.chartOpenIso hUV).inv).mapDerivedCategory.obj
        ((Modules.restrictFunctor (D.chartOpen' hUV).ι).mapDerivedCategory.obj L'))
    (hT : haveI := isClosedImmersion_chartDiagonal hU hV hUV
      Nonempty ((cq (chartDiagonal hUV)).derivedSheafHomExactSupport.obj L' ≅
        structureSingle U.toScheme)) :
    Nonempty ((Modules.restrictFunctor (D.diag ⁻¹ᵁ D.chartOpen hUV).ι).mapDerivedCategory.obj
        (D.diagonalExactSupport K) ≅ structureSingle (D.diag ⁻¹ᵁ D.chartOpen hUV).toScheme) := by
  have := isClosedImmersion_chartDiagonal hU hV hUV
  obtain ⟨eT⟩ := hT
  let V₁ := D.chartOpen hUV
  let V₂ := D.chartOpen' hUV
  let d := chartDiagonal hUV
  have e₂ : (Modules.restrictFunctor (D.diag ⁻¹ᵁ V₁).ι).mapDerivedCategory.obj
      (D.diagonalExactSupport K) ≅
      (Modules.pushforward (D.chartDiagIso hUV).inv).mapDerivedCategory.obj
        ((Modules.restrictFunctor (d ⁻¹ᵁ V₂).ι).mapDerivedCategory.obj
          ((cq d).derivedSheafHomExactSupport.obj L')) :=
    (derivedSheafHomRestrictIso D.diag V₁).app (D.derivedPullbackProj K) ≪≫
      (cq (D.diag ∣_ V₁)).derivedSheafHomExactSupport.mapIso eL ≪≫
      (derivedSheafHomTransportIso (D.diag ∣_ V₁) (d ∣_ V₂) (D.chartDiagIso hUV)
        (D.chartOpenIso hUV) (D.diag_restrict_comp_chartOpenIso hUV)).app
          ((Modules.restrictFunctor V₂.ι).mapDerivedCategory.obj L') ≪≫
      (Modules.pushforward (D.chartDiagIso hUV).inv).mapDerivedCategory.mapIso
        ((derivedSheafHomRestrictIso d V₂).app L').symm
  exact ⟨e₂ ≪≫ (Modules.pushforward (D.chartDiagIso hUV).inv).mapDerivedCategory.mapIso
    ((Modules.restrictFunctor (d ⁻¹ᵁ V₂).ι).mapDerivedCategory.mapIso eT ≪≫
      restrictStructureSingleIso _) ≪≫
    pushforwardInvStructureSingleIso (D.chartDiagIso hUV)⟩

open CochainComplex.DerivedExtensionScalars in
include hU hV in
/-- **Stacks 0E2U, backwards.** Let `f` be flat and locally of finite presentation, `K` an object
of `D(𝒪_X)` with quasi-coherent cohomology sheaves, and `U ⊆ X`, `V ⊆ S` affine opens with
`U ⊆ f⁻¹(V)`. If `RΓ(U, K)` is a relative dualizing complex for `Γ(S, V) → Γ(X, U)` in the sense
of Stacks 0E2C, then `R ℰom(𝒪_X, L pr₁^*K|_W)` restricted to `U = Δ⁻¹(W ∩ (U ×_V U))` is
`𝒪_U[0]`. -/
theorem nonempty_restrict_diagonalExactSupport_iso [Flat f] [LocallyOfFinitePresentation f]
    (K : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hK : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
      letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
        algebraFinitePresentation_appLE f hV hU hUV rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, V) Γ(X, U)
        ((derivedSectionsUnbounded X U).obj K)) :
    Nonempty ((Modules.restrictFunctor (D.diag ⁻¹ᵁ D.chartOpen hUV).ι).mapDerivedCategory.obj
        (D.diagonalExactSupport K) ≅ structureSingle (D.diag ⁻¹ᵁ D.chartOpen hUV).toScheme) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hU hUV rfl
  have := isAffine_chartSquare hU hV hUV
  let M := (derivedSectionsUnbounded X U).obj K
  obtain ⟨eP⟩ := nonempty_chartPullback_iso hU hV hUV K hE (chartProjRing hUV)
    (IsAffineOpen.comp_isoSpec_hom hU _)
  have hN := isBoundedBelow_chartExtension hU hV hUV M hK.relativelyPerfect
  have hA := nonempty_chartDerivedHom_iso_of_diagonal hU hV hUV M hK.diagonalDerivedHom
  have hT := nonempty_chartExactSupport_iso_of_derivedHom hU hV hUV (chartPullback hUV K)
    (chartDiagonalRing hUV) (IsAffineOpen.comp_isoSpec_hom' hU _) _ hN eP hA
  exact D.nonempty_restrict_diagonalExactSupport_iso_of_chart hU hV hUV K
    (chartPullback hUV K) (D.restrictDerivedPullbackProjIso hUV K) hT

open CochainComplex.DerivedExtensionScalars in
include hU hV in
/-- **Stacks 0E2U backwards, on an affine source.** If `U = X`, the conclusion of
`nonempty_restrict_diagonalExactSupport_iso` holds on all of `X`:
`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`. -/
theorem nonempty_diagonalExactSupport_iso_of_top [Flat f] [LocallyOfFinitePresentation f]
    (hUtop : U = ⊤) (K : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (hK : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
      letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
        algebraFinitePresentation_appLE f hV hU hUV rfl
      Dualizing.IsRelativeDualizingComplex Γ(S, V) Γ(X, U)
        ((derivedSectionsUnbounded X U).obj K)) :
    Nonempty (D.diagonalExactSupport K ≅ structureSingle X) := by
  obtain ⟨e⟩ := D.nonempty_restrict_diagonalExactSupport_iso hU hV hUV K hE hK
  have htop : D.diag ⁻¹ᵁ D.chartOpen hUV = ⊤ := by
    rw [D.diag_preimage_chartOpen hUV, hUtop]
  have hιiso : IsIso (D.diag ⁻¹ᵁ D.chartOpen hUV).ι := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
    have hx : x ∈ D.diag ⁻¹ᵁ D.chartOpen hUV := by simp [htop]
    exact ⟨⟨x, hx⟩, rfl⟩
  exact nonempty_iso_structureSingle_of_restrict _ _ ⟨e⟩

/-- **`Δ_*𝒪_X ≅ R SheafHom_{𝒪_W}(Δ_*𝒪_X, L pr₁^*K|_W)`** as soon as
`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`: by Stacks 0A77 the right-hand side is
`Δ_* R ℰom(𝒪_X, L pr₁^*K|_W)`. -/
theorem nonempty_diagonalObject_iso_derivedSheafHom (K : DerivedCategory X.Modules)
    (h : Nonempty (D.diagonalExactSupport K ≅ structureSingle X)) :
    Nonempty (D.diagonalObject ≅
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).obj (op D.diagonalObject)).obj
        (D.derivedPullbackProj K)) := by
  obtain ⟨e⟩ := h
  let F := RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i
  exact ⟨D.diagonalObjectIso ≪≫ F.mapDerivedCategory.mapIso e.symm ≪≫
    D.diagQuotient.derivedSheafHomExactSupportPushforwardNatIso.app (D.derivedPullbackProj K) ≪≫
    ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).mapIso
      D.diagonalObjectIso.op).app (D.derivedPullbackProj K)⟩

/-! ### Morphisms `Δ_*𝒪_X ⟶ L pr₁^*K|_W` -/

/-- **Derived pushforward along `Δ` is bijective on endomorphisms of `𝒪_X[0]`.** On objects in
degree zero it is the pushforward of modules followed by the degree-zero inclusion, and both are
fully faithful, the first because `Δ` is a closed immersion. -/
def diagFullyFaithfulSingle :
    (DerivedCategory.singleFunctor X.Modules 0 ⋙
      (RingedSpaceModuleAdjunction.modulePushforward
        D.diagQuotient.i).mapDerivedCategory).FullyFaithful :=
  let F := RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i
  let hff : F.FullyFaithful := Stacks.ToposBridge.fullyFaithfulModulePushforward
    D.diag.toLRSHom.toShHom (IsClosedImmersion.isClosedEmbedding D.diag).isInducing
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom D.diag)
  (hff.comp (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor D.W.Modules 0))).ofIso
      (F.mapDerivedCategorySingleFunctor 0).symm

/-- **The generator of `Hom(Δ_*𝒪_X, L pr₁^*K|_W)`** attached to an isomorphism
`e : R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`: the transpose of `e⁻¹` under the adjunction
`Δ_* ⊣ R ℰom(𝒪_X, -)` of Stacks 0A76. -/
def diagonalGenerator (K : DerivedCategory X.Modules)
    (e : D.diagonalExactSupport K ≅ structureSingle X) :
    D.diagonalObject ⟶ D.derivedPullbackProj K :=
  D.diagonalObjectIso.hom ≫
    (D.diagQuotient.derivedModulePushforwardSheafHomExactSupportAdjunction.homEquiv _ _).symm e.inv

/-- **`Hom(Δ_*𝒪_X, L pr₁^*K|_W)` is free of rank one over `End(Δ_*𝒪_X)`**, acting by
precomposition, with basis `diagonalGenerator e` for any `e : R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`.
By the adjunction of Stacks 0A76, `Hom(Δ_*𝒪_X, L pr₁^*K|_W) = Hom(𝒪_X, R ℰom(𝒪_X, L pr₁^*K|_W))
= End(𝒪_X[0])`, and `Δ_*` identifies `End(𝒪_X[0])` with `End(Δ_*𝒪_X)` compatibly with
precomposition. -/
theorem diagonalGenerator_spec (K : DerivedCategory X.Modules)
    (e : D.diagonalExactSupport K ≅ structureSingle X) :
    (∀ ζ : D.diagonalObject ⟶ D.derivedPullbackProj K, ∃ x : D.diagonalObject ⟶ D.diagonalObject,
        ζ = x ≫ D.diagonalGenerator K e) ∧
      ∀ x y : D.diagonalObject ⟶ D.diagonalObject,
        x ≫ D.diagonalGenerator K e = y ≫ D.diagonalGenerator K e → x = y := by
  let F := (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).mapDerivedCategory
  let adj := D.diagQuotient.derivedModulePushforwardSheafHomExactSupportAdjunction
  let hG := D.diagFullyFaithfulSingle
  -- all morphisms below are read in `D(𝒪_W)`
  let C := DerivedCategory (Stacks.SheafOfModules.StructureSheafModules D.W.sheaf)
  let B : C := D.diagonalObject
  let L : C := D.derivedPullbackProj K
  let B' : C := F.obj (structureSingle X)
  let δ : B ≅ B' := D.diagonalObjectIso
  let Fm : (structureSingle X ⟶ structureSingle X) → (B' ⟶ B') := fun y => F.map y
  let hom : (B' ⟶ L) ≃ (structureSingle X ⟶ D.diagonalExactSupport K) := adj.homEquiv _ _
  have hFm_comp : ∀ y₁ y₂, Fm (y₁ ≫ y₂) = Fm y₁ ≫ Fm y₂ := fun y₁ y₂ => F.map_comp y₁ y₂
  have hFm_id : Fm (𝟙 _) = 𝟙 B' := F.map_id _
  have hhom : ∀ (y : structureSingle X ⟶ structureSingle X) (k : B' ⟶ L),
      hom (Fm y ≫ k) = y ≫ hom k := fun y k => adj.homEquiv_naturality_left y k
  -- every endomorphism of `Δ_*𝒪_X` is `Δ_*` of an endomorphism of `𝒪_X[0]`
  have hsurj : ∀ x : B ⟶ B, ∃ y, x = δ.hom ≫ Fm y ≫ δ.inv := fun x => by
    refine ⟨(DerivedCategory.singleFunctor X.Modules 0).map (hG.preimage (δ.inv ≫ x ≫ δ.hom)), ?_⟩
    have hm : Fm ((DerivedCategory.singleFunctor X.Modules 0).map
        (hG.preimage (δ.inv ≫ x ≫ δ.hom))) = δ.inv ≫ x ≫ δ.hom :=
      hG.map_preimage (δ.inv ≫ x ≫ δ.hom)
    rw [hm, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
  have hinj : ∀ y₁ y₂, Fm y₁ = Fm y₂ → y₁ = y₂ := by
    intro y₁ y₂ hy
    obtain ⟨z₁, rfl⟩ := (DerivedCategory.singleFunctor X.Modules 0).map_surjective y₁
    obtain ⟨z₂, rfl⟩ := (DerivedCategory.singleFunctor X.Modules 0).map_surjective y₂
    exact congrArg _ (hG.map_injective hy)
  let β : (B ⟶ L) → (B ⟶ B) := fun ζ => δ.hom ≫ Fm (hom (δ.inv ≫ ζ) ≫ e.hom) ≫ δ.inv
  have hβinj : Function.Injective β := by
    intro ζ ζ' hζ
    have h₁ : Fm (hom (δ.inv ≫ ζ) ≫ e.hom) = Fm (hom (δ.inv ≫ ζ') ≫ e.hom) :=
      (Iso.cancel_iso_inv_right _ _ δ).1 ((Iso.cancel_iso_hom_left δ _ _).1 hζ)
    exact (Iso.cancel_iso_inv_left δ _ _).1
      (hom.injective ((Iso.cancel_iso_hom_right _ _ e).1 (hinj _ _ h₁)))
  have hβcomp : ∀ x ζ, β (x ≫ ζ) = x ≫ β ζ := by
    intro x ζ
    obtain ⟨y, rfl⟩ := hsurj x
    have h1 : δ.inv ≫ (δ.hom ≫ Fm y ≫ δ.inv) ≫ ζ = Fm y ≫ δ.inv ≫ ζ := by
      rw [Category.assoc, Iso.inv_hom_id_assoc, Category.assoc]
    show δ.hom ≫ Fm (hom (δ.inv ≫ (δ.hom ≫ Fm y ≫ δ.inv) ≫ ζ) ≫ e.hom) ≫ δ.inv =
      (δ.hom ≫ Fm y ≫ δ.inv) ≫ δ.hom ≫ Fm (hom (δ.inv ≫ ζ) ≫ e.hom) ≫ δ.inv
    rw [h1, hhom, Category.assoc, hFm_comp, Category.assoc, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
  let ζ₁ : B ⟶ L := δ.hom ≫ hom.symm e.inv
  have hβ₁ : β ζ₁ = 𝟙 _ := by
    show δ.hom ≫ Fm (hom (δ.inv ≫ δ.hom ≫ hom.symm e.inv) ≫ e.hom) ≫ δ.inv = 𝟙 _
    rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply, Iso.inv_hom_id, hFm_id,
      Category.id_comp, Iso.hom_inv_id]
  exact CategoryTheory.exists_eq_comp_and_cancel_of_injective β hβinj hβcomp ζ₁ hβ₁

/-- `Hom(Δ_*𝒪_X, L pr₁^*K|_W)` is free of rank one over `End(Δ_*𝒪_X)` as soon as
`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`; see `diagonalGenerator_spec`. -/
theorem exists_diagonalObject_generator (K : DerivedCategory X.Modules)
    (h : Nonempty (D.diagonalExactSupport K ≅ structureSingle X)) :
    ∃ ζ₁ : D.diagonalObject ⟶ D.derivedPullbackProj K,
      (∀ ζ : D.diagonalObject ⟶ D.derivedPullbackProj K, ∃ x : D.diagonalObject ⟶ D.diagonalObject,
        ζ = x ≫ ζ₁) ∧
      ∀ x y : D.diagonalObject ⟶ D.diagonalObject, x ≫ ζ₁ = y ≫ ζ₁ → x = y :=
  let ⟨e⟩ := h
  ⟨D.diagonalGenerator K e, D.diagonalGenerator_spec K e⟩

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end

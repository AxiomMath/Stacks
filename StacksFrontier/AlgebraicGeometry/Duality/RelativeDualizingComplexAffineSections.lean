module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChartRing

/-!
# A relative dualizing complex restricts to one on a compatible pair of affine opens

Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)` be a relative
dualizing complex for `f` (Stacks 0E2T). For affine opens `U ⊆ X` and `V ⊆ S` with
`U ⊆ f⁻¹(V)`, put `R = Γ(S, V)` and `A = Γ(X, U)`. Stacks 0E2U says that `RΓ(U, K)`, the object
of `D(A)` attached to `K|_U` by Stacks 06Z0, is a relative dualizing complex for `R → A` in the
sense of Stacks 0E2C.

The first condition of Stacks 0E2C, `R`-perfectness of `RΓ(U, K)`, is the implication
`(1) ⟹ (2)` of Stacks 0DI2. For the second, the proof follows the source. The condition on `ξ`
is moved to the affine scheme `U ×_V U` in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChart`: derived sheaf Hom
with exact support along the diagonal `U ⟶ U ×_V U` carries `L pr₁^*K` to `𝒪_U[0]`. On
`U ×_V U` the object `L pr₁^*K` is the sheaf associated to `RΓ(U, K) ⊗ᴸ_A Γ(U ×_V U, ⊤)`, by
Stacks 06Z0 and the affine comparison of Stacks 08DW part (2); `A` is pseudo-coherent over
`Γ(U ×_V U, ⊤)` (Stacks 0683) and the extended complex is bounded below, so the affine
comparison of Stacks 0A78 part (2) turns derived sheaf Hom with exact support into
`R Hom_{Γ(U ×_V U, ⊤)}(A, -)`, and full faithfulness of derived sheafification gives
`R Hom(A, RΓ(U, K) ⊗ᴸ_A Γ(U ×_V U, ⊤)) ≅ A[0]`. The ring identification
`Γ(U ×_V U, ⊤) ≅ A ⊗_R A` of
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChartRing` turns this into
the condition of Stacks 0E2C.

## Main results

* `isRelativeDualizingComplex_derivedSections`, in the namespace
  `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex`, is Stacks 0E2U.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_chartPullback_iso`: `L pr₁^*K` on
  `U ×_V U` is a sheafification.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_derivedHom_iso_of_chartExactSupport`: the
  affine computation on the chart.

## Implementation notes

`S`-perfectness is read at the canonical family of derived tensor products of Stacks 06YU on the
open subspaces of `(X, f⁻¹𝒪_S)`, which is where Stacks 0DI2 is stated: an arbitrary family of
certified tensorings carries arbitrary underived tensor products, against which finite Tor
dimension says nothing about `RΓ(U, K)`. The `R`-algebra structure on `A` is the chart ring map
`f.appLE V U`, as in `AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect`; its flatness and
finite presentation come from those of `f`.

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model at
which `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex` and `Dualizing.derivedHom` are
stated.

## References

* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Definition 47.27.1 (Tag 0E2C)](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.3.8 (Tag 08DW)](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

/-- Derived pullback along equal morphisms of schemes. -/
def derivedPullbackCongrObj {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (h : a = b)
    (K : DerivedCategory Z.Modules) :
    (derivedPullback a.toLRSHom.toShHom).obj K ≅ (derivedPullback b.toLRSHom.toShHom).obj K :=
  eqToIso (by rw [h])

/-- Derived pullback along a composite of morphisms of schemes, Stacks 0D5S. -/
def derivedPullbackCompObj {Y Z T : Scheme.{u}} (a : Y ⟶ Z) (b : Z ⟶ T)
    (K : DerivedCategory T.Modules) :
    (derivedPullback a.toLRSHom.toShHom).obj ((derivedPullback b.toLRSHom.toShHom).obj K) ≅
      (derivedPullback (a ≫ b).toLRSHom.toShHom).obj K :=
  (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    a.toLRSHom.toShHom b.toLRSHom.toShHom).app K

/-- Pushing forward along the inverse of an isomorphism of schemes is derived pullback along it. -/
def pushforwardInvIsoDerivedPullback {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    (Modules.pushforward e.inv).mapDerivedCategory ≅ derivedPullback e.hom.toLRSHom.toShHom :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
    (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv e)).symm ≪≫
    Modules.derivedRestrictIsoDerivedPullback e.hom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.IsAffineOpen

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- A morphism `g : T ⟶ U` from an affine scheme is `Spec` of the ring map
`Γ(X, U) ⟶ Γ(T, ⊤)` it induces, read along `T ≅ Spec Γ(T, ⊤)` and `U ≅ Spec Γ(X, U)`. -/
theorem comp_isoSpec_hom {T : Scheme.{u}} [IsAffine T] (g : T ⟶ U.toScheme) :
    g ≫ hU.isoSpec.hom = T.isoSpec.hom ≫ Spec.map (U.topIso.inv ≫ g.appTop) := by
  rw [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.Opens.toSpecΓ,
    Scheme.toSpecΓ_naturality_assoc, Spec.map_comp]

/-- A morphism `g : U ⟶ T` to an affine scheme is `Spec` of the ring map
`Γ(T, ⊤) ⟶ Γ(X, U)` it induces, read along `U ≅ Spec Γ(X, U)` and `T ≅ Spec Γ(T, ⊤)`. -/
theorem comp_isoSpec_hom' {T : Scheme.{u}} [IsAffine T] (g : U.toScheme ⟶ T) :
    g ≫ T.isoSpec.hom = hU.isoSpec.hom ≫ Spec.map (g.appTop ≫ U.topIso.hom) := by
  rw [IsAffineOpen.isoSpec_hom, Scheme.isoSpec_hom, Scheme.Opens.toSpecΓ,
    Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.IsAffineOpen

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)
  {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (hUV : U ≤ f ⁻¹ᵁ V)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- The first projection `U ×_V U ⟶ X`. -/
abbrev chartProj : chartSquare hUV ⟶ X := chartSquareι hUV ≫ pullback.fst f f

/-- `L pr₁^*K` on `U ×_V U`. -/
abbrev chartPullback (K : DerivedCategory X.Modules) :
    DerivedCategory (chartSquare hUV).Modules :=
  (derivedPullback (chartProj hUV).toLRSHom.toShHom).obj K

/-- `L pr₁^*K|_W` and `L pr₁^*K` on `U ×_V U` agree on `W ∩ (U ×_V U)`. -/
def restrictDerivedPullbackProjIso (K : DerivedCategory X.Modules) :
    (Modules.restrictFunctor (D.chartOpen hUV).ι).mapDerivedCategory.obj
        (D.derivedPullbackProj K) ≅
      (Modules.pushforward (D.chartOpenIso hUV).inv).mapDerivedCategory.obj
        ((Modules.restrictFunctor (D.chartOpen' hUV).ι).mapDerivedCategory.obj
          (chartPullback hUV K)) := by
  have h : (D.chartOpen hUV).ι ≫ D.proj =
      (D.chartOpenIso hUV).hom ≫ (D.chartOpen' hUV).ι ≫ chartProj hUV := by
    simp only [chartProj, proj, chartOpenIso_hom_fac_assoc]
  exact (Modules.derivedRestrictIsoDerivedPullback (D.chartOpen hUV).ι).app _ ≪≫
    derivedPullbackCompObj _ _ K ≪≫ derivedPullbackCongrObj h K ≪≫
    (derivedPullbackCompObj _ _ K).symm ≪≫
    (derivedPullback (D.chartOpenIso hUV).hom.toLRSHom.toShHom).mapIso
      ((derivedPullbackCompObj _ _ K).symm ≪≫
        ((Modules.derivedRestrictIsoDerivedPullback (D.chartOpen' hUV).ι).app _).symm) ≪≫
    ((pushforwardInvIsoDerivedPullback (D.chartOpenIso hUV)).app _).symm

include hV in
/-- **`L pr₁^*K` on the affine chart `U ×_V U` is a sheafification**, Stacks 06Z0 and the affine
comparison of Stacks 08DW part (2): for `K` with quasi-coherent cohomology, and for the ring map
`ψ : Γ(X, U) ⟶ Γ(U ×_V U, ⊤)` of the first projection, `L pr₁^*K` is the sheaf associated to
`RΓ(U, K) ⊗ᴸ_{Γ(X, U)} Γ(U ×_V U, ⊤)`. -/
theorem nonempty_chartPullback_iso (K : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (ψ : Γ(X, U) ⟶ Γ(chartSquare hUV, ⊤))
    (hψ : haveI := isAffine_chartSquare hU hV hUV
      pullback.fst (chartMap hUV) (chartMap hUV) ≫ hU.isoSpec.hom =
        (chartSquare hUV).isoSpec.hom ≫ Spec.map ψ) :
    haveI := isAffine_chartSquare hU hV hUV
    Nonempty (chartPullback hUV K ≅
      (Modules.pushforward (chartSquare hUV).isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor _).mapDerivedCategory.obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            ψ.hom).functor.obj ((derivedSectionsUnbounded X U).obj K)))) := by
  have := isAffine_chartSquare hU hV hUV
  obtain ⟨eK⟩ := hU.nonempty_iso_derivedTilde_derivedSectionsSpec K hE
  obtain ⟨eM⟩ := hU.nonempty_iso_derivedSectionsSpec K
  let pfst := pullback.fst (chartMap hUV) (chartMap hUV)
  let M := (derivedSectionsUnbounded X U).obj K
  have h₁ : chartProj hUV = pfst ≫ U.ι := pullback.lift_fst _ _ _
  have eK' : (Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
      (derivedPullback hU.isoSpec.hom.toLRSHom.toShHom).obj
        ((tilde.functor Γ(X, U)).mapDerivedCategory.obj M) :=
    eK ≪≫ (pushforwardInvIsoDerivedPullback hU.isoSpec).app _ ≪≫
      (derivedPullback hU.isoSpec.hom.toLRSHom.toShHom).mapIso
        ((tilde.functor Γ(X, U)).mapDerivedCategory.mapIso eM)
  refine ⟨derivedPullbackCongrObj h₁ K ≪≫ (derivedPullbackCompObj pfst U.ι K).symm ≪≫
    (derivedPullback pfst.toLRSHom.toShHom).mapIso
      (((Modules.derivedRestrictIsoDerivedPullback U.ι).app K).symm ≪≫ eK') ≪≫
    derivedPullbackCompObj _ _ _ ≪≫ derivedPullbackCongrObj hψ _ ≪≫
    (derivedPullbackCompObj _ _ _).symm ≪≫
    (derivedPullback (chartSquare hUV).isoSpec.hom.toLRSHom.toShHom).mapIso
      ((StandardModel.affinePullbackComparison _ _ ψ).app M) ≪≫
    ((pushforwardInvIsoDerivedPullback (chartSquare hUV).isoSpec).app _).symm⟩

open Stacks.Duality.ClosedImmersionRestriction in
include hU hV in
/-- **The affine computation on the chart**, Stacks 0A78 part (2). Let
`φ : Γ(U ×_V U, ⊤) ⟶ Γ(X, U)` be the ring map of the diagonal `U ⟶ U ×_V U`, let `N` be a bounded
below object of `D(Γ(U ×_V U, ⊤))` and let `L'` be the sheaf associated to `N`. If derived sheaf
Hom with exact support along the diagonal carries `L'` to `𝒪_U[0]`, then
`R Hom_{Γ(U ×_V U, ⊤)}(Γ(X, U), N)` is `Γ(X, U)[0]`. -/
theorem nonempty_derivedHom_iso_of_chartExactSupport [Flat f] [LocallyOfFinitePresentation f]
    (L' : DerivedCategory (chartSquare hUV).Modules)
    (hT : haveI := isClosedImmersion_chartDiagonal hU hV hUV
      Nonempty ((cq (chartDiagonal hUV)).derivedSheafHomExactSupport.obj L' ≅
        structureSingle U.toScheme))
    (φ : Γ(chartSquare hUV, ⊤) ⟶ Γ(X, U))
    (hφ : haveI := isAffine_chartSquare hU hV hUV
      chartDiagonal hUV ≫ (chartSquare hUV).isoSpec.hom = hU.isoSpec.hom ≫ Spec.map φ)
    (N : DerivedCategory (ModuleCat.{u} Γ(chartSquare hUV, ⊤)))
    (hN : DerivedCategoryB.IsBoundedBelow N)
    (eN : haveI := isAffine_chartSquare hU hV hUV
      L' ≅ (Modules.pushforward (chartSquare hUV).isoSpec.inv).mapDerivedCategory.obj
        ((tilde.functor _).mapDerivedCategory.obj N)) :
    Nonempty ((Dualizing.derivedHom.{u, u, u} φ.hom).obj N ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U))) := by
  have := isAffine_chartSquare hU hV hUV
  have := isClosedImmersion_chartDiagonal hU hV hUV
  obtain ⟨eT⟩ := hT
  have hSpec : Spec.map φ =
      hU.isoSpec.inv ≫ chartDiagonal hUV ≫ (chartSquare hUV).isoSpec.hom := by
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
      structureSingle U.toScheme :=
    (Modules.pushforward hU.isoSpec.inv).mapDerivedCategory.mapIso
      (asIso ((affineDerivedSheafHomComparison _ _ φ).app N)) ≪≫
    ((derivedSheafHomTransportIso (chartDiagonal hUV) (Spec.map φ) hU.isoSpec
      (chartSquare hUV).isoSpec hφ).app _).symm ≪≫
    (cq (chartDiagonal hUV)).derivedSheafHomExactSupport.mapIso eN.symm ≪≫ eT
  obtain ⟨e₂⟩ := nonempty_iso_structureSingle_of_restrict hU.isoSpec.hom _
    ⟨(Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv
        hU.isoSpec)).app _ ≪≫ e₁⟩
  let e₃ : (tilde.functor Γ(X, U)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
        (ModuleCat.of Γ(X, U) Γ(X, U))) ≅ structureSingle (Spec Γ(X, U)) :=
    ((tilde.functor Γ(X, U)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso tildeSelf
  exact ⟨(StandardModel.mapDerivedCategoryFullyFaithful Γ(X, U)).preimageIso (e₂ ≪≫ e₃.symm)⟩

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen


namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]

/-- **Stacks 0E2U.** Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)`
be a relative dualizing complex for `f` (Stacks 0E2T), relative to an open `W ⊆ X ×_S X` through
which the relative diagonal factors as a closed immersion. Let `U ⊆ X` be an affine open lying
over an affine open `V ⊆ S`, and put `R = Γ(S, V)` and `A = Γ(X, U)`, an `R`-algebra through `f`.
Then `RΓ(U, K)`, the object of `D(A)` corresponding to `K|_U` under Stacks 06Z0, is a relative
dualizing complex for `R → A` in the sense of Stacks 0E2C.

`S`-perfectness is read at the derived tensor product of Stacks 06YU on the open subspaces of
`(X, f⁻¹𝒪_S)`, as in Stacks 0DI2. -/
@[stacks 0E2U]
theorem isRelativeDualizingComplex_derivedSections {D : DiagonalOpen f}
    {K : DerivedCategory X.Modules} {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
    letI : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
      algebraFinitePresentation_appLE f hV hU hUV rfl
    Dualizing.IsRelativeDualizingComplex Γ(S, V) Γ(X, U)
      ((derivedSectionsUnbounded X U).obj K) := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU hUV rfl
  let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hU hUV rfl
  have := DiagonalOpen.isAffine_chartSquare hU hV hUV
  have hE := isQuasicoherentDerived_of_isPseudoCoherent X K hK.isPerfectRelativeTo.1
  have h12 := (isPerfectRelativeTo_tfae f K hE).out 1 2
  have hperf : SectionsRelativelyPerfect f K hV hU hUV :=
    h12.mp hK.isPerfectRelativeTo U hU V hV hUV
  refine ⟨hperf, ?_⟩
  let M := (derivedSectionsUnbounded X U).obj K
  obtain ⟨eP⟩ := DiagonalOpen.nonempty_chartPullback_iso hU hV hUV K hE
    (DiagonalOpen.chartProjRing hUV) (IsAffineOpen.comp_isoSpec_hom hU _)
  have hT := D.nonempty_chartExactSupport_iso hU hV hUV K ξ hK.isIso_diagonalAction
    (DiagonalOpen.chartPullback hUV K) (D.restrictDerivedPullbackProjIso hUV K)
  exact DiagonalOpen.nonempty_diagonalDerivedHom_iso_of_chart hU hV hUV M
    (DiagonalOpen.nonempty_derivedHom_iso_of_chartExactSupport hU hV hUV _ hT
      (DiagonalOpen.chartDiagonalRing hUV) (IsAffineOpen.comp_isoSpec_hom' hU _) _
      (DiagonalOpen.isBoundedBelow_chartExtension hU hV hUV M hperf) eP)

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

end

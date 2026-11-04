module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentHomComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoverDeckPerfect
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusTraceIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleInjectiveSections
public import StacksFrontier.Homology.Perfect.GroupAlgebraInjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionIntegralDirectImage

/-!
# Perfectness and the trace for `RΓ_c(U_k̄, D(A[H]))` and `RΓ_c(U_k̄, Hom_{A[H]}(X, D(A[H])))`

Let `U` be a smooth curve over a finite field `k`, `G : V ⟶ U` a connected finite étale Galois
covering with group `H`, `A = ℤ/ℓⁿ` with `ℓ` invertible in `k`, and `D = D(A[H])` the regular
descent sheaf. Let `T` be a twisted injective resolution of `(j_! D)|_{Ū_k̄}` and
`J = Γ(Spec k̄, g_* T)`, a bounded below complex of injective `A[H]`-modules computing
`RΓ_c(U_k̄, D)`.

* (I1) `RΓ_c(U_k̄, D)` is perfect over `A[H]`: `J` has finite cohomology vanishing above degree
  `2` (read over `A` through `Hom_{A[H]}(A[H], -)`), and every `3`-cocycle `A[H]/𝔞 ⟶ J³` is a
  coboundary because `H³(Hom_{A[H]}(A[H]/𝔞, J)) = H³_c(U_k̄, Hom_{A[H]}(A[H]/𝔞, D)) = 0` on a
  curve; `A[H]` being quasi-Frobenius this is
  `StacksDraft.Perfect.isPerfect_of_injective_of_cocycle_zmod`.
* (I2a) For an `(A[H], Λ)`-bimodule `X`, finite over `A[H]`, with `A` acting centrally, and
  `Φ = Hom_{A[H]}(X, -)` carrying finite projective modules to finite projective modules,
  `RΓ_c(U_k̄, Hom_{A[H]}(X, D)) = Φ(J)` is perfect over `Λ`.
* (I2b) `Tr_Λ(π_U^* | RΓ_c(U_k̄, Hom_{A[H]}(X, D))) = Φ♮(Tr_{A[H]}(π_U^* | RΓ_c(U_k̄, D)))`.

This is Step 7 of the proof of [Stacks, Tag 03UG], with the perfectness of Step 6.

## Main results

* `isPerfect_compactSupportFrobeniusCohomology_regularDescentSheaf`: (I1).
* `isPerfect_compactSupportFrobeniusCohomology_etaleModuleHom_regularDescentSheaf`: (I2a).
* `perfectDerivedTrace_canonicalCompactSupportFrobenius_etaleModuleHom_regularDescentSheaf`: (I2b).

## Implementation notes

The statements involve `Stacks.EtaleCohomology.canonicalCompactSupportFrobenius` and
`CategoryTheory.FilteredDerived.perfectDerivedTrace`, defined in the model
`HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius CategoryTheory.FilteredDerived

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- **A perfect complex over a Noetherian ring has finite cohomology.** -/
theorem module_finite_homology_of_isPerfect {A : Type} [Ring A] [IsNoetherianRing A]
    {K : DerivedCategory (ModuleCat.{u + 1} A)} (hK : StacksDraft.Perfect.IsPerfect K) (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).obj K) := by
  obtain ⟨P, -, -, -, -, hfin, -, ⟨e⟩⟩ := hK
  have : IsNoetherian A (P.X i) := isNoetherian_of_isNoetherianRing_of_finite A (P.X i)
  have : Module.Finite A (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite A (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  have : Module.Finite A ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} A)
      (ComplexShape.up ℤ) i).obj P) := inferInstanceAs (Module.Finite A (P.homology i))
  exact Module.Finite.equiv (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) i).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) i).app P).symm.toLinearEquiv)

section Regular

variable {A : Type} [CommRing A] {R : Type} [Ring R] [Algebra A R]

/-- The cohomology of `Hom_R(R, K)` is the cohomology of `K` read over `A`. -/
def homologyHomFunctorRegularIso (K : CochainComplex (ModuleCat.{u + 1} R) ℤ) (i : ℤ) :
    (((homFunctor (regularModuleU.{u} R)
      (centralScalars (A := A) (regularModuleU.{u} R))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology i ≅
      (ModuleCat.restrictScalars.{u + 1} (algebraMap A R)).obj (K.homology i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso
      ((NatIso.mapHomologicalComplex homFunctorRegularIso (ComplexShape.up ℤ)).app K) ≪≫
    (K.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u + 1} (algebraMap A R))

/-- A module finite over `A` through `A ⟶ R` is finite over `R`. -/
lemma module_finite_of_restrictScalars (X : ModuleCat.{u + 1} R)
    (h : Module.Finite A ((ModuleCat.restrictScalars.{u + 1} (algebraMap A R)).obj X)) :
    Module.Finite R X := by
  obtain ⟨s, hs⟩ := h.fg_top
  refine ⟨⟨s, eq_top_iff.2 fun x hxt => ?_⟩⟩
  clear hxt
  have hx : x ∈ Submodule.span A
      (s : Set ((ModuleCat.restrictScalars.{u + 1} (algebraMap A R)).obj X)) := by
    rw [hs]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul a y _ hy => exact Submodule.smul_mem _ (algebraMap A R a) hy

end Regular

section Curve

variable {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
  [IsCurve k pU] [Smooth pU] (J : CompactificationOf (Over.mk pU)) (kbar : Type u) [Field kbar]
  [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q) {m : ℕ} [NeZero m] {R : Type} [Ring R]
  [Algebra (ZMod m) R] [IsNoetherianRing R] {D : EtaleModules.{u, 0} R U}

/-- **`H^i(Hom_R(M, J)) = 0` for `i > 2` on a curve**, for the model `J` of `RΓ_c(U_k̄, D)` given
by a twisted injective resolution of a locally injective `(j_! D)|_{Ū_k̄}`, `R` an algebra over
`ℤ/m` and `M` a finite `R`-module. -/
theorem isZero_homology_map_homFunctor_of_two_lt
    (hD : ∀ {N₁ N₂ : ModuleCat.{u + 1} R} [Module.Finite R N₁] [Module.Finite R N₂]
      (v : N₁ ⟶ N₂) [Mono v], Epi ((homSheafPrecomp (A := ZMod m) v
        (fieldBaseChange (Over.mk J.toBase) kbar)).app
          ((etaleModuleInverseImage.{u, 0} R (fieldBaseChangeProj (Over.mk J.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} R J.immersion).obj D))))
    (Rs : CompactSupportTwistResolution J kbar p q hcard D) (M : ModuleCat.{u + 1} R)
    [Module.Finite R M] (i : ℤ) (hi : 2 < i) :
    IsZero ((((homFunctor M (centralScalars (A := ZMod m) M)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        ((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} R (pullback.snd (Over.mk J.toBase).hom
            (specAlgebraMap k kbar))).mapCochainComplexPlus.obj Rs.T)).obj).homology i) := by
  obtain ⟨E, -⟩ := exists_compactSupportHomModel J kbar p q hcard M (centralScalars M)
    (fun a => rfl) hD Rs
  have hz := isZero_compactSupportFrobeniusCohomologyGroup_single_of_topologicalKrullDim_le pU J
    kbar m ((etaleModuleHom M (centralScalars (A := ZMod m) M) U).obj D) 1
    (IsCurve.topologicalKrullDim_eq_one pU).le i (by omega)
  exact hz.of_iso
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} (ZMod m)) i).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso E.symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso (DerivedCategory.Plus.ι.mapIso
      ((compactSupportFrobeniusFunctor.{u, 0} (ZMod m) pU J kbar).mapIso
        (mapCochainComplexPlusSinglePlusIso
          (etaleModuleHom M (centralScalars (A := ZMod m) M) U) D))))

end Curve

/-- The terms of `Γ(Spec k̄, g_* T)` are injective when those of `T` are. -/
private theorem injective_X_globalSections_directImage
    {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
    (J : CompactificationOf (Over.mk pU)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) {R : Type} [Ring R]
    {D : EtaleModules.{u, 0} R U}
    (Rs : CompactSupportTwistResolution J kbar p q hcard D) (i : ℤ) :
    Injective (((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).mapCochainComplexPlus.obj
      ((etaleModuleDirectImage.{u, 0} R (pullback.snd (Over.mk J.toBase).hom
        (specAlgebraMap k kbar))).mapCochainComplexPlus.obj Rs.T)).obj.X i) := by
  have : Injective (((CochainComplex.Plus.ι _).obj Rs.T).X i) := Rs.injective i
  have : Injective ((etaleModuleDirectImage.{u, 0} R
    (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))).obj (Rs.T.obj.X i)) :=
    inferInstance
  exact Injective.of_iso ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).app _).symm
    (injective_obj_obj_of_injective _ _)

/-- The complex `Γ(Spec k̄, g_* T)` is concentrated in nonnegative degrees. -/
private theorem isStrictlyGE_globalSections_directImage
    {k : Type u} [Field k] [Fintype k] {U : Scheme.{u}} {pU : U ⟶ Spec (.of k)}
    (J : CompactificationOf (Over.mk pU)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) {R : Type} [Ring R]
    {D : EtaleModules.{u, 0} R U}
    (Rs : CompactSupportTwistResolution J kbar p q hcard D) :
    ((etaleModuleGlobalSections.{u, 0} R (Spec (.of kbar))).mapCochainComplexPlus.obj
      ((etaleModuleDirectImage.{u, 0} R (pullback.snd (Over.mk J.toBase).hom
        (specAlgebraMap k kbar))).mapCochainComplexPlus.obj Rs.T)).obj.IsStrictlyGE 0 :=
  @isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0
    (@isStrictlyGE_mapHomologicalComplex _ _ _ _ _ _ _ _ _ _ _ 0 Rs.isStrictlyGE)

section RegularDescent

variable {k : Type u} [Field k] [Fintype k] [PerfectField k] {U : Scheme.{u}} {H : Type} [Group H]
  [Fintype H] {pU : U ⟶ Spec (.of k)} [IsCurve k pU] [Smooth pU]
  (J : CompactificationOf (Over.mk pU))
  (G : EtaleGaloisCovering U H) [IsFinite (G.cover.hom : G.cover.left ⟶ U)]
  [ConnectedSpace G.cover.left] [ConnectedSpace ((𝟭 Scheme).obj G.cover.left)]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (ℓ n : ℕ) [Fact ℓ.Prime]

/-- **`RΓ_c(U_k̄, D(A[H]))` read over `A = ℤ/ℓⁿ` is perfect**: it is `RΓ_c(V_k̄, ℤ/ℓⁿ)` for the
covering `V`, computed on a smooth projective compactification of `V`. -/
theorem isPerfect_compactSupportFrobeniusCohomology_restrictScalars_regularDescentSheaf
    (hn : 1 ≤ n) : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ n)) pU J kbar
        ((etaleModuleRestrictScalars (MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H))
          U).mapCochainComplexPlus.obj
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) := by
  have : NeZero n := ⟨by omega⟩
  have : IsProper (Over.mk J.toBase).hom := inferInstanceAs (IsProper J.toBase)
  obtain ⟨C⟩ := nonempty_coverCompactification k pU (Over.mk J.toBase).hom J.immersion
    (show J.immersion ≫ (Over.mk J.toBase).hom = pU from Over.w J.obj.hom)
    (G.cover.hom : G.cover.left ⟶ U)
  have : IsProper C.toOver.hom := C.isProper
  have hZ := isPerfect_extensionByZeroConstantComplex_zmod ℓ n C.toOver
    (IsCurve.topologicalKrullDim_eq_one C.q).le C.j kbar
  have : IsIntegralHom (Over.homMk (U := C.toOver) (V := Over.mk J.toBase) C.fb C.hq).left :=
    inferInstanceAs (IsIntegralHom C.fb)
  have : Etale (G.cover.hom : G.cover.left ⟶ U) := G.cover.prop
  let i := Over.homMk (U := C.toOver) (V := Over.mk J.toBase) C.fb C.hq
  have e₁ := frobeniusRestrictionDirectImageIso (ZMod (ℓ ^ n)) i kbar
    (extensionByZeroConstantComplex (ZMod (ℓ ^ n)) C.toOver C.j (zmodSingleComplex.{u} ℓ n))
  have e₂ := openExtensionIso (ZMod (ℓ ^ n)) i J.immersion C.j G.cover.hom C.isPullback.flip
    (zmodSingleComplex.{u} ℓ n)
  have e₃ :=
    (etaleModuleExtensionByZero.{u, 0} (ZMod (ℓ ^ n)) J.immersion).mapCochainComplexPlus.mapIso
      (coverDescentComplexIso (Over.mk J.toBase) G C (ZMod (ℓ ^ n)))
  let F := fieldBaseChangeRestrictionFunctor.{u, 0} (ZMod (ℓ ^ n)) (Over.mk J.toBase) kbar ⋙
    etaleModuleDerivedDirectImage.{u, 0} (ZMod (ℓ ^ n))
      (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar)) ⋙
    etaleModuleDerivedGlobalSections.{u, 0} (ZMod (ℓ ^ n)) (Spec (.of kbar))
  exact StacksDraft.Perfect.isPerfect_of_iso (DerivedCategory.Plus.ι.mapIso
    (e₁ ≪≫ F.mapIso e₂.symm ≪≫ F.mapIso e₃).symm) hZ

/-- **The injective model `J = Γ(Spec k̄, g_* T)` of `RΓ_c(U_k̄, D(A[H]))` is perfect over
`A[H]`**: its terms are injective, its cohomology is finite and vanishes above degree `2`, and its
`3`-cocycles from cyclic modules are coboundaries. -/
theorem isPerfect_regularDescentModel (hn : 1 ≤ n) (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q)
    (Rs : CompactSupportTwistResolution J kbar p q hcard
      (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Q.obj
      ((etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (Spec (.of kbar))).mapCochainComplexPlus.obj
          ((etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
            (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
              Rs.T)).obj) := by
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero n := ⟨by omega⟩
  have : Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) := Module.finite_of_finite (ZMod (ℓ ^ n))
  have : IsNoetherianRing (MonoidAlgebra (ZMod (ℓ ^ n)) H) :=
    isNoetherian_of_finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) (MonoidAlgebra (ZMod (ℓ ^ n)) H)
  have hD := fun {N₁ N₂ : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)}
      [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₁]
      [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₂] (v : N₁ ⟶ N₂) [Mono v] =>
    epi_homSheafPrecomp_fieldBaseChange_extensionByZero_regularDescentSheaf J kbar G v
  let Jc := ((etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
    (Spec (.of kbar))).mapCochainComplexPlus.obj
      ((etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
          Rs.T)).obj
  have hge : Jc.IsStrictlyGE 0 := isStrictlyGE_globalSections_directImage J kbar _ q hcard Rs
  have hinj : ∀ i, Injective (Jc.X i) :=
    injective_X_globalSections_directImage J kbar _ q hcard Rs
  have hc : ∀ i, 2 < i → Jc.ExactAt i := fun i hi => by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    have h := (isZero_homology_map_homFunctor_of_two_lt J kbar p q hcard hD Rs
      (regularModuleU.{u} (MonoidAlgebra (ZMod (ℓ ^ n)) H)) i hi).of_iso
        (homologyHomFunctorRegularIso (A := ZMod (ℓ ^ n)) Jc i).symm
    rwa [ModuleCat.isZero_iff_subsingleton] at h ⊢
  have hf : ∀ i, Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) (Jc.homology i) := fun i => by
    apply module_finite_of_restrictScalars (A := ZMod (ℓ ^ n))
    obtain ⟨E, -⟩ := exists_compactSupportHomModel J kbar _ q hcard
      (regularModuleU.{u} (MonoidAlgebra (ZMod (ℓ ^ n)) H)) (centralScalars _) (fun a => rfl) hD Rs
    have h1 := isPerfect_compactSupportFrobeniusCohomology_restrictScalars_regularDescentSheaf J G
      kbar ℓ n hn
    rw [show MonoidAlgebra.singleOneRingHom (R := ZMod (ℓ ^ n)) (M := H) =
      algebraMap (ZMod (ℓ ^ n)) (MonoidAlgebra (ZMod (ℓ ^ n)) H) from
        RingHom.ext fun _ => rfl] at h1
    have hP := isPerfect_compactSupportFrobeniusCohomology_of_iso (ZMod (ℓ ^ n)) pU J kbar
      (K' := (etaleModuleHom (regularModuleU.{u} (MonoidAlgebra (ZMod (ℓ ^ n)) H))
        (centralScalars (A := ZMod (ℓ ^ n)) _) U).mapCochainComplexPlus.obj
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
            (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))
      (ObjectProperty.isoMk _ ((NatIso.mapHomologicalComplex
        (etaleModuleHomRegularIso (A := ZMod (ℓ ^ n)) (R := MonoidAlgebra (ZMod (ℓ ^ n)) H) U).symm
          (ComplexShape.up ℤ)).app
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))).obj)) h1
    have := module_finite_homology_of_isPerfect hP i
    exact Module.Finite.equiv ((DerivedCategory.homologyFunctor _ i).mapIso E ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _ ≪≫
      homologyHomFunctorRegularIso (A := ZMod (ℓ ^ n)) Jc i).toLinearEquiv
  have hcoc : ∀ (𝔞 : Ideal (MonoidAlgebra (ZMod (ℓ ^ n)) H))
      (ψ : (MonoidAlgebra (ZMod (ℓ ^ n)) H ⧸ 𝔞) →ₗ[MonoidAlgebra (ZMod (ℓ ^ n)) H] Jc.X (2 + 1)),
      (Jc.d (2 + 1) (2 + 1 + 1)).hom ∘ₗ ψ = 0 →
        ∃ χ : (MonoidAlgebra (ZMod (ℓ ^ n)) H ⧸ 𝔞) →ₗ[MonoidAlgebra (ZMod (ℓ ^ n)) H] Jc.X 2,
          (Jc.d 2 (2 + 1)).hom ∘ₗ χ = ψ := by
    intro 𝔞 ψ hψ
    let M := ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ n)) H)
      (ULift.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H ⧸ 𝔞))
    have : Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) M :=
      Module.Finite.equiv ULift.moduleEquiv.symm
    have hex := (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_homology_map_homFunctor_of_two_lt J kbar p q hcard hD Rs M 3 (by norm_num))
    rw [HomologicalComplex.exactAt_iff' _ 2 3 4 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at hex
    let x : M ⟶ Jc.X 3 := ModuleCat.ofHom (ψ ∘ₗ ULift.moduleEquiv.toLinearMap)
    have hx : x ≫ Jc.d 3 4 = 0 := by
      ext t
      exact congrArg (fun φ => φ t.down) hψ
    obtain ⟨y, hy⟩ := hex x hx
    exact ⟨(show M ⟶ Jc.X 2 from y).hom ∘ₗ ULift.moduleEquiv.symm.toLinearMap,
      LinearMap.ext fun r => congrArg (fun z => (show M ⟶ Jc.X 3 from z).hom (ULift.up r)) hy⟩
  exact StacksDraft.Perfect.isPerfect_of_injective_of_cocycle_zmod Jc 0 2 hinj hc hf hcoc

/-- **(I1) `RΓ_c(U_k̄, D(A[H]))` is perfect over `A[H]`**, `A = ℤ/ℓⁿ`, for a connected finite
étale Galois covering of a smooth curve over a finite field. -/
theorem isPerfect_compactSupportFrobeniusCohomology_regularDescentSheaf (hn : 1 ≤ n) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))))) := by
  obtain ⟨q, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  obtain ⟨Rs⟩ := CompactSupportTwistResolution.nonempty J kbar (ringChar k) q hcard
    (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))
  exact StacksDraft.Perfect.isPerfect_of_iso
    (Functor.twistResolutionIso
      (etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) (Spec (.of kbar)))
      Rs.ψ Rs.injective)
    (isPerfect_regularDescentModel J G kbar ℓ n hn (ringChar k) q hcard Rs)

/-- Finite projective modules over `(ℤ/ℓⁿ)[H]` are injective. -/
lemma injective_of_finite_projective_groupAlgebra
    (M : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H))
    (h₁ : Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) M)
    (h₂ : Module.Projective (MonoidAlgebra (ZMod (ℓ ^ n)) H) M) : Injective M := by
  have := MonoidAlgebra.injective_of_finite_projective (A := ZMod (ℓ ^ n)) (H := H)
    Stacks.ZModPrimePower.baer_self M
  exact Module.injective_object_of_injective_module (MonoidAlgebra (ZMod (ℓ ^ n)) H) M

variable {Λ : Type} [Ring Λ] [Algebra (ZMod (ℓ ^ n)) Λ]
  (X : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H))
  (hX : Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) X) (ρ : Λ →+* (End X)ᵐᵒᵖ)
  (hρ : ∀ a : ZMod (ℓ ^ n), ρ (algebraMap (ZMod (ℓ ^ n)) Λ a) = centralScalars X a)
  (hΦ : PreservesFiniteProjective (homFunctor X ρ))

include hX hρ hΦ in
/-- **(I2a) `RΓ_c(U_k̄, Hom_{A[H]}(X, D(A[H])))` is perfect over `Λ`** for an `(A[H], Λ)`-bimodule
`X`, finite over `A[H]`, with `A` acting centrally through `Λ`, such that `Hom_{A[H]}(X, -)`
carries finite projective modules to finite projective modules. -/
theorem isPerfect_compactSupportFrobeniusCohomology_etaleModuleHom_regularDescentSheaf
    (hn : 1 ≤ n) :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} Λ pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          ((etaleModuleHom X ρ U).obj (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) := by
  have := hX
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero n := ⟨by omega⟩
  have : Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) := Module.finite_of_finite (ZMod (ℓ ^ n))
  have : IsNoetherianRing (MonoidAlgebra (ZMod (ℓ ^ n)) H) :=
    isNoetherian_of_finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) (MonoidAlgebra (ZMod (ℓ ^ n)) H)
  obtain ⟨q, hp, hcard⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  obtain ⟨Rs⟩ := CompactSupportTwistResolution.nonempty J kbar (ringChar k) q hcard
    (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))
  have hD := fun {N₁ N₂ : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)}
      [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₁]
      [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₂] (v : N₁ ⟶ N₂) [Mono v] =>
    epi_homSheafPrecomp_fieldBaseChange_extensionByZero_regularDescentSheaf J kbar G v
  let Jc := ((etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
    (Spec (.of kbar))).mapCochainComplexPlus.obj
      ((etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
          Rs.T)).obj
  have hge : Jc.IsStrictlyGE 0 := isStrictlyGE_globalSections_directImage J kbar _ q hcard Rs
  have hinj : ∀ i, Injective (Jc.X i) :=
    injective_X_globalSections_directImage J kbar _ q hcard Rs
  have hJ := isPerfect_regularDescentModel J G kbar ℓ n hn (ringChar k) q hcard Rs
  have hΦJ := isPerfect_map_of_injective (homFunctor X ρ) hΦ
    (injective_of_finite_projective_groupAlgebra ℓ n) Jc 0 hinj hJ
  obtain ⟨E, -⟩ := exists_compactSupportHomModel J kbar (ringChar k) q hcard X ρ hρ hD Rs
  exact isPerfect_compactSupportFrobeniusCohomology_of_iso Λ pU J kbar
    (mapCochainComplexPlusSinglePlusIso (etaleModuleHom X ρ U) _)
    (StacksDraft.Perfect.isPerfect_of_iso E hΦJ)

include hX hρ in
/-- **(I2b) Step 7 of [Stacks, Tag 03UG]**: for `Φ = Hom_{A[H]}(X, -)`,
`Tr_Λ(π_U^* | RΓ_c(U_k̄, Hom_{A[H]}(X, D(A[H])))) = Φ♮(Tr_{A[H]}(π_U^* | RΓ_c(U_k̄, D(A[H]))))`. -/
theorem perfectDerivedTrace_canonicalCompactSupportFrobenius_etaleModuleHom_regularDescentSheaf
    (hn : 1 ≤ n) (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q) :
    perfectDerivedTrace Λ
      ⟨_, isPerfect_compactSupportFrobeniusCohomology_etaleModuleHom_regularDescentSheaf
        J G kbar ℓ n X hX ρ hρ hΦ hn⟩ (DerivedCategory.Plus.ι.map
          (canonicalCompactSupportFrobenius.{u, 0} Λ pU J kbar p q hcard
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
              ((etaleModuleHom X ρ U).obj (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) =
      functorTraceMap (homFunctor X ρ) (𝟙 _) hΦ
        (perfectDerivedTrace (MonoidAlgebra (ZMod (ℓ ^ n)) H)
          ⟨_, isPerfect_compactSupportFrobeniusCohomology_regularDescentSheaf J G kbar ℓ n hn⟩
          (DerivedCategory.Plus.ι.map
            (canonicalCompactSupportFrobenius.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar p q
              hcard
              ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
                (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))))) := by
  have := hX
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero n := ⟨by omega⟩
  have : Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) := Module.finite_of_finite (ZMod (ℓ ^ n))
  have : IsNoetherianRing (MonoidAlgebra (ZMod (ℓ ^ n)) H) :=
    isNoetherian_of_finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) (MonoidAlgebra (ZMod (ℓ ^ n)) H)
  obtain ⟨Rs⟩ := CompactSupportTwistResolution.nonempty J kbar p q hcard
    (G.regularDescentSheaf (A := ZMod (ℓ ^ n)))
  have hD := fun {N₁ N₂ : ModuleCat.{u + 1} (MonoidAlgebra (ZMod (ℓ ^ n)) H)}
      [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₁]
      [Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) N₂] (v : N₁ ⟶ N₂) [Mono v] =>
    epi_homSheafPrecomp_fieldBaseChange_extensionByZero_regularDescentSheaf J kbar G v
  let Jc := ((etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
    (Spec (.of kbar))).mapCochainComplexPlus.obj
      ((etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))).mapCochainComplexPlus.obj
          Rs.T)).obj
  have hge : Jc.IsStrictlyGE 0 := isStrictlyGE_globalSections_directImage J kbar _ q hcard Rs
  have hinj : ∀ i, Injective (Jc.X i) :=
    injective_X_globalSections_directImage J kbar _ q hcard Rs
  have hJ := isPerfect_regularDescentModel J G kbar ℓ n hn p q hcard Rs
  have hΦJ := isPerfect_map_of_injective (homFunctor X ρ) hΦ
    (injective_of_finite_projective_groupAlgebra ℓ n) Jc 0 hinj hJ
  obtain ⟨E, hE⟩ := exists_compactSupportHomModel J kbar p q hcard X ρ hρ hD Rs
  let eR : DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) pU J kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj
          (G.regularDescentSheaf (A := ZMod (ℓ ^ n))))) ≅ DerivedCategory.Q.obj Jc :=
    Functor.twistResolutionIso (etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
        (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar)))
      (etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) (Spec (.of kbar)))
      Rs.ψ Rs.injective
  have hER := Functor.twistResolutionIso_hom_comp
    (etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
      (geometricFrobeniusBaseChange (Over.mk J.toBase) kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
      (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H) (Spec (.of kbar)))
    (etaleModuleDirectImageComp.{u, 0} (MonoidAlgebra (ZMod (ℓ ^ n)) H)
      (geometricFrobeniusBaseChange (Over.mk J.toBase) kbar p q hcard)
      (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))
      (pullback.snd (Over.mk J.toBase).hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase (Over.mk J.toBase) kbar p q hcard).symm)
    Rs.ψ Rs.injective _ Rs.twist Rs.twist_comm
  rw [← perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_of_iso Λ pU J kbar p q hcard
    (mapCochainComplexPlusSinglePlusIso (etaleModuleHom X ρ U) _)
    (StacksDraft.Perfect.isPerfect_of_iso E hΦJ),
    perfectDerivedTrace_congr Λ _ ⟨_, hΦJ⟩ E _ _ hE,
    perfectDerivedTrace_map_of_injective (homFunctor X ρ) hΦ
      (injective_of_finite_projective_groupAlgebra ℓ n) Jc 0 hinj hJ _ hΦJ]
  exact congrArg (functorTraceMap (homFunctor X ρ) (𝟙 _) hΦ)
    (perfectDerivedTrace_congr (MonoidAlgebra (ZMod (ℓ ^ n)) H)
      ⟨_, isPerfect_compactSupportFrobeniusCohomology_regularDescentSheaf J G kbar ℓ n hn⟩
      ⟨_, hJ⟩ eR _ _ hER).symm

end RegularDescent

end Stacks.EtaleCohomology

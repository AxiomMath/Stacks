module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeUpperShriek
public import StacksFrontier.RingTheory.Dualizing.RelativeEndomorphisms
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetyColimit
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetyUniqueness
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor

/-!
# The derived endomorphisms of a relative dualizing complex over an arbitrary base

Let `R → A` be a flat ring map of finite presentation and `K` a relative dualizing complex.
[stacks 0E2G] asserts that `A ⟶ RHom_A(K, K)` is an isomorphism.  This file carries out the
source's proof over an arbitrary, not necessarily Noetherian, base.

1. By [stacks 02JO] (`Dualizing.exists_noetherianFlatModel`) `A = A₁ ⊗_{R₁} R` for a flat map of
   finite type `R₁ → A₁` of Noetherian rings, and `ω₁ = φ^!(R₁)` is a relative dualizing complex
   over `A₁` that stays one under every base change ([stacks 0E2E], [stacks 0E2F] (2) at a
   Noetherian base, `StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeUpperShriek`).
2. `R` is the filtered colimit of its finitely generated `R₁`-subalgebras `Rᵢ`, which are
   Noetherian; at each stage `ωᵢ = ω₁ ⊗ᴸ (Rᵢ ⊗_{R₁} A₁)` is a relative dualizing complex over a
   Noetherian base, so its homothety is invertible, which means that scalars exhaust
   `End(ωᵢ)` and that `ωᵢ` has no self-extensions in nonzero degree
   (`StacksFrontier.RingTheory.Dualizing.RelativeHomothetySelfExt`).
3. Those two statements are about morphism groups, so they pass to the colimit
   `ω = ω₁ ⊗ᴸ (R ⊗_{R₁} A₁)` by [stacks 0DHX]
   (`StacksFrontier.RingTheory.Dualizing.RelativeHomothetyColimit`).
4. `K` and `ω` are relative dualizing complexes for the same map, hence isomorphic by
   [stacks 0E2D]; scalars act injectively on `End(K)` by the defining condition alone; and the
   rank-one criterion turns the two statements at `K` back into invertibility of the homothety.

## Main results

* `Dualizing.exists_isUniversallyRelativeDualizing_of_isNoetherianRing`
* `Dualizing.isRelativeDualizingComplex_includeRight_of_isUniversallyRelativeDualizing`
* `Dualizing.isIso_relativeHomothety_baseChange_of_isNoetherianRing`
* `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_uniqueness` — the
  assembly, with the uniqueness of [stacks 0E2D] as a hypothesis.
* `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex` — **[stacks 0E2G]**.

## References

* [Stacks Project, Tag 0E2G](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

namespace Dualizing

attribute [local instance 10000] HasDerivedCategory.standard

universe u

noncomputable section

/-- **A Noetherian relative dualizing complex stable under every base change.**  For a flat map
of finite type `R₁ → A₁` with `R₁` Noetherian, `ω₁ = φ^!(R₁)` is a relative dualizing complex
([stacks 0E2E]) whose derived base change along every `R₁ → R'` is again one (the Noetherian case
of [stacks 0E2F] (2),
`Dualizing.isRelativeDualizingComplex_baseChange_relativeDualizingComplex_of_representation`). -/
theorem exists_isUniversallyRelativeDualizing_of_isNoetherianRing
    (R₁ A₁ : Type u) [CommRing R₁] [CommRing A₁] [Algebra R₁ A₁] [IsNoetherianRing R₁]
    [Module.Flat R₁ A₁] [Algebra.FinitePresentation R₁ A₁] :
    ∃ ω : DerivedCategory (ModuleCat.{u} A₁),
      IsRelativeDualizingComplex R₁ A₁ ω ∧ IsUniversallyRelativeDualizing R₁ A₁ ω := by
  classical
  have : IsNoetherianRing A₁ := Algebra.FiniteType.isNoetherianRing R₁ A₁
  obtain ⟨p₁⟩ := nonempty_polynomialPresentation (algebraMap R₁ A₁)
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hflat₁ : (algebraMap R₁ A₁).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hK₁ := p₁.relativeDualizingComplex_isRelativeDualizingComplex hflat₁
  let : Algebra.FiniteType R₁ (A₁ ⊗[R₁] A₁) :=
    Algebra.FiniteType.trans (R := R₁) (S := A₁) (A := A₁ ⊗[R₁] A₁) inferInstance inferInstance
  let : IsNoetherianRing (A₁ ⊗[R₁] A₁) :=
    Algebra.FiniteType.isNoetherianRing R₁ (A₁ ⊗[R₁] A₁)
  obtain ⟨P, F, E, dP, dF, hPLE, hPproj, hPkflat, ⟨eP⟩, hFLE, hFflat, ⟨eF⟩, hE, hEflat, hEfin⟩ :=
    exists_diagonalHomComplexRepresentation R₁ A₁ _ hK₁
  have := hPLE
  have := hPproj
  have := hFLE
  exact ⟨_, hK₁, fun R' _ _ =>
    isRelativeDualizingComplex_baseChange_relativeDualizingComplex_of_representation
      R₁ A₁ R' p₁ P dP hPkflat eP F dF hFflat eF E hE hEflat hEfin⟩

/-- **The base change of a universally relative dualizing complex along `A₁ → S ⊗[R₁] A₁`.**
If `ω` is universally relative dualizing for `R₁ → A₁`, its derived base change along the right
coprojection `A₁ → S ⊗[R₁] A₁` is a relative dualizing complex for `S → S ⊗[R₁] A₁`, for every
`R₁`-algebra `S`: this is the definition read through `S ⊗[R₁] A₁ ≅ A₁ ⊗[R₁] S`. -/
theorem isRelativeDualizingComplex_includeRight_of_isUniversallyRelativeDualizing
    {R₁ A₁ : Type u} [CommRing R₁] [CommRing A₁] [Algebra R₁ A₁] [Module.Flat R₁ A₁]
    [Algebra.FinitePresentation R₁ A₁] {ω : DerivedCategory (ModuleCat.{u} A₁)}
    (hU : IsUniversallyRelativeDualizing R₁ A₁ ω) (S : Type u) [CommRing S] [Algebra R₁ S] :
    IsRelativeDualizingComplex S (S ⊗[R₁] A₁)
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[R₁] S ⊗[R₁] A₁).toRingHom).functor.obj ω) := by
  let : Algebra S (A₁ ⊗[R₁] S) := Algebra.TensorProduct.rightAlgebra
  let : Module.Flat S (A₁ ⊗[R₁] S) := flat_baseChange R₁ A₁ S
  let : Algebra.FinitePresentation S (A₁ ⊗[R₁] S) :=
    Algebra.FinitePresentation.equiv (baseChangeComm R₁ A₁ S)
  exact isRelativeDualizingComplex_totalDerivedExtension_of_algEquiv (baseChangeComm R₁ A₁ S)
    Algebra.TensorProduct.includeLeftRingHom
    (Algebra.TensorProduct.includeRight : A₁ →ₐ[R₁] S ⊗[R₁] A₁).toRingHom
    (by ext a; simp [baseChangeComm]) ω (hU S)

/-- **The homothety is invertible at every Noetherian base change of a universally relative
dualizing complex.**  If `ω` is universally relative dualizing for `R₁ → A₁` and `S` is a
Noetherian `R₁`-algebra, then `ω ⊗ᴸ_{A₁} (S ⊗[R₁] A₁)` is a relative dualizing complex for the flat
map of finite presentation `S → S ⊗[R₁] A₁` of Noetherian rings, so [stacks 0E2G] over a Noetherian
base applies to it: by the uniqueness `huniq` of [stacks 0E2D] it is isomorphic to the relative
dualizing complex `φ^!(S)` of [stacks 0E2E], at which the homothety is invertible by
[stacks 0BZW] (1)(c). -/
theorem isIso_relativeHomothety_baseChange_of_isNoetherianRing
    (huniq : ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B] [Module.Flat S B]
      [Algebra.FinitePresentation S B] (K L : DerivedCategory (ModuleCat.{u} B)),
      IsRelativeDualizingComplex S B K → IsRelativeDualizingComplex S B L → Nonempty (K ≅ L))
    {R₁ A₁ : Type u} [CommRing R₁] [CommRing A₁] [Algebra R₁ A₁] [Module.Flat R₁ A₁]
    [Algebra.FinitePresentation R₁ A₁] {ω : DerivedCategory (ModuleCat.{u} A₁)}
    (hU : IsUniversallyRelativeDualizing R₁ A₁ ω) (S : Type u) [CommRing S] [Algebra R₁ S]
    [IsNoetherianRing S] :
    IsIso (relativeHomothety (S ⊗[R₁] A₁)
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeRight : A₁ →ₐ[R₁] S ⊗[R₁] A₁).toRingHom).functor.obj ω)) := by
  classical
  have : Algebra.FiniteType S (S ⊗[R₁] A₁) := inferInstance
  have : IsNoetherianRing (S ⊗[R₁] A₁) := Algebra.FiniteType.isNoetherianRing S _
  have hflat : (algebraMap S (S ⊗[R₁] A₁)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨p⟩ := nonempty_polynomialPresentation (algebraMap S (S ⊗[R₁] A₁))
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact isIso_relativeHomothety_of_nonempty_iso_upperShriekFunctor_unit S (S ⊗[R₁] A₁) p _
    (huniq S (S ⊗[R₁] A₁) _ _
      (isRelativeDualizingComplex_includeRight_of_isUniversallyRelativeDualizing hU S)
      (p.relativeDualizingComplex_isRelativeDualizingComplex hflat))

/-- Vanishing of a morphism group transfers along isomorphisms of source and target. -/
private theorem subsingleton_hom_of_iso {C : Type*} [Category C] {X X' Y Y' : C} (e : X ≅ X')
    (f : Y ≅ Y') (h : Subsingleton (X' ⟶ Y')) : Subsingleton (X ⟶ Y) :=
  (Iso.homCongr e f).subsingleton

open PseudoCoherence in
/-- **The conclusion of [stacks 0E2G] over any base, from uniqueness.**  Let `R → A` be flat of
finite presentation and `K` a relative dualizing complex.  If any two relative dualizing complexes
of a flat map of finite presentation are isomorphic (`huniq`, the statement of [stacks 0E2D]),
then `A ⟶ RHom_A(K, K)` is an isomorphism.  No Noetherian hypothesis is made; see the module
documentation for the proof.  `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex`
discharges `huniq`. -/
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex_of_uniqueness
    (huniq : ∀ (S B : Type u) [CommRing S] [CommRing B] [Algebra S B] [Module.Flat S B]
      [Algebra.FinitePresentation S B] (K L : DerivedCategory (ModuleCat.{u} B)),
      IsRelativeDualizingComplex S B K → IsRelativeDualizingComplex S B L → Nonempty (K ≅ L))
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) :
    IsIso (relativeHomothety A K) := by
  classical
  obtain ⟨R₁, A₁, _, _, _, _, hR₁, hA₁, hflat, hfp, ⟨eA⟩⟩ := exists_noetherianFlatModel R A
  obtain ⟨ω, hω, hU⟩ := exists_isUniversallyRelativeDualizing_of_isNoetherianRing R₁ A₁
  let F := fgSubalgebraDiagram R₁ R
  let c := fgSubalgebraCocone R₁ R
  have hc := isColimit_mapCocone_commAlgCat_uliftFunctor (fgSubalgebraCoconeIsColimit R₁ R)
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent ω := hω.relativelyPerfect.1
  have htor : StacksDraft.TorAmplitude.HasFiniteTorDimensionCanonical R₁
      ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj ω) :=
    (hasFiniteTorDimension_canonicalDerivedTensoringDatum_iff R₁ _).1 hω.relativelyPerfect.2
  -- the stages
  have hstage (i : FGSubalgebra R₁ R) :
      IsIso (relativeHomothety (stageAlgebra F A₁ i) (stageDerivedObj F A₁ i ω)) := by
    have : Algebra.FiniteType R₁ i.1 := i.1.fg_iff_finiteType.mp i.2
    have : IsNoetherianRing i.1 := Algebra.FiniteType.isNoetherianRing R₁ i.1
    exact (isIso_relativeHomothety_iff_of_iso _ (extendLiftIso (baseToStageMap F A₁ i) ω)).2
      (isIso_relativeHomothety_baseChange_of_isNoetherianRing huniq hU i.1)
  have hsurjStage (i : FGSubalgebra R₁ R) :
      Function.Surjective (fun a : stageAlgebra F A₁ i => a • 𝟙 (stageDerivedObj F A₁ i ω)) :=
    have := hstage i
    (bijective_smul_id_of_isIso_relativeHomothety (stageAlgebra F A₁ i)
      (stageDerivedObj F A₁ i ω)).2
  have hvanStage (n : ℤ) (hn : n ≠ 0) (i : FGSubalgebra R₁ R) :
      Subsingleton (stageDerivedObj F A₁ i ω ⟶ stageDerivedObj F A₁ i (ω⟦n⟧)) :=
    have := hstage i
    subsingleton_hom_of_iso (Iso.refl _) (extendLiftShiftIso _ ω n)
      (subsingleton_shift_of_isIso_relativeHomothety (stageAlgebra F A₁ i)
        (stageDerivedObj F A₁ i ω) n hn)
  -- the colimit
  let L : DerivedCategory (ModuleCat.{u} (R ⊗[R₁] A₁)) := limitDerivedObj c A₁ ω
  have hsurjL : Function.Surjective (fun a : R ⊗[R₁] A₁ => a • 𝟙 L) :=
    surjective_smul_id_limitDerivedObj F c hc A₁ ω hpc htor hsurjStage
  have hvanL (n : ℤ) (hn : n ≠ 0) :
      Subsingleton (L ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{u} (R ⊗[R₁] A₁))) n).obj L) :=
    have := subsingleton_limitDerivedObj F c hc A₁ ω (ω⟦n⟧) hpc
      (hasFiniteTorDimensionCanonical_restrictScalars_shift ω n htor) (hvanStage n hn)
    subsingleton_hom_of_iso (Iso.refl _) (extendLiftShiftIso _ ω n).symm this
  have hL : IsRelativeDualizingComplex R (R ⊗[R₁] A₁) L :=
    isRelativeDualizingComplex_of_iso _ _
      (isRelativeDualizingComplex_includeRight_of_isUniversallyRelativeDualizing hU R)
      (extendLiftIso (baseToLimitMap c A₁) ω).symm
  -- the given complex, over the model
  let : Algebra R (A₁ ⊗[R₁] R) := Algebra.TensorProduct.rightAlgebra
  let ε : R ⊗[R₁] A₁ ≃ₐ[R] A := (baseChangeComm R₁ A₁ R).trans eA
  let Φ := (ModuleCat.restrictScalars.{u} ε.toRingEquiv.toRingHom).mapDerivedCategory
  have hKbar : IsRelativeDualizingComplex R (R ⊗[R₁] A₁) (Φ.obj K) :=
    RelativeExistence.isRelativeDualizingComplex_of_algEquiv ε.symm K hK
  obtain ⟨eK⟩ := huniq R (R ⊗[R₁] A₁) (Φ.obj K) L hKbar hL
  have : (ModuleCat.restrictScalars.{u} ε.toRingEquiv.toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv ε.toRingEquiv).isEquivalence_functor
  have : Φ.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence _
  have hsurjK : Function.Surjective (fun a : A => a • 𝟙 K) :=
    surjective_smul_id_of_faithful Φ ε (fun s X => by
      rw [show ε s = ε.toRingEquiv.toRingHom s from rfl,
        restrictScalars_mapDerivedCategory_map_smul, CategoryTheory.Functor.map_id])
      K (surjective_smul_id_of_iso eK hsurjL)
  have hvanK (n : ℤ) (hn : n ≠ 0) : Subsingleton (K ⟶ K⟦n⟧) := by
    have := hvanL n hn
    exact subsingleton_of_faithful Φ (subsingleton_hom_of_iso (Iso.refl _)
      ((Φ.commShiftIso n).app K)
      (subsingleton_hom_of_iso eK ((shiftFunctor _ n).mapIso eK) this))
  obtain ⟨P, a, b, hGE, hLE, -, -, ⟨eP⟩⟩ :=
    (isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation _ _ _ K).1 hK.relativelyPerfect
  have := hGE
  have : K.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eP.symm a
  exact isIso_relativeHomothety_of_bijective_smul_id A K a
    ⟨injective_smul_id_of_isRelativeDualizingComplex K hK, hsurjK⟩ hvanK

/-- **Stacks Project, Tag 0E2G.**  Let `R → A` be a flat ring map of finite presentation and let
`K` be a relative dualizing complex for `R → A` ([stacks 0E2C]).  Then the canonical map
`A ⟶ RHom_A(K, K)` is an isomorphism.

This is `Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex_of_uniqueness` with the
uniqueness of relative dualizing complexes supplied by [stacks 0E2D],
`Dualizing.IsRelativeDualizingComplex.nonempty_iso`.  The proof is the source's: reduction to a
Noetherian model by [stacks 02JO], the Noetherian case through [stacks 0E2E], [stacks 0E2F] and
[stacks 0BZW], and the passage to an arbitrary base by [stacks 0DHX]; see the module
documentation. -/
@[stacks 0E2G]
theorem isIso_relativeHomothety_of_isRelativeDualizingComplex
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.FinitePresentation R A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsRelativeDualizingComplex R A K) :
    IsIso (relativeHomothety A K) :=
  isIso_relativeHomothety_of_isRelativeDualizingComplex_of_uniqueness
    (fun _ _ _ _ _ _ _ _ _ hK hL => hK.nonempty_iso hL) R A K hK

end

end Dualizing

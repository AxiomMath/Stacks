module

public import StacksFrontier.Homology.HomComplex.RHom
public import StacksFrontier.Homology.RelativelyPerfect.CochainBaseChange
public import StacksFrontier.Homology.Tor.IndependenceFlatModule
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import
  StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingTorAmplitudeVariableCount
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.TorIndependentBaseChange
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology of the derived base change of a relative dualizing complex

Let `R → A` be a flat finite type homomorphism of Noetherian rings all of whose fibres have
dimension at most `d`, and let `R → R'` be a homomorphism to a Noetherian ring.  This file proves
that `ω^•_{A/R} ⊗_R^L R'`, the derived base change of the relative dualizing complex read as a
complex of `R`-modules, has no cohomology in degrees below `-d`.  This is the step of the proof of
the Tor-amplitude clause of [Stacks, Tag 0E9Q] that the source performs through the base change
[Stacks, Tag 0BZV].

## Main results

* `StacksDraft.RelativelyPerfect.linearMap_isBaseChange_of_finite_projective` — linear maps out
  of a finite projective module base-change to linear maps out of the scalar extension.
* `StacksDraft.RelativelyPerfect.homComplexBaseChangeIsoOfProjective` — the base change of the
  Hom complex out of a complex of finite projectives into a bounded complex is the Hom complex
  between the base changes.
* `Dualizing.exists_projectiveResolution_relativeDualizingComplex_iso` — `ω^•_{A/R}` read over
  the polynomial algebra `P` of a presentation is `Hom^•_P(F, P)[n]` for a finite projective
  resolution `F` of `A`.
* `Dualizing.nonempty_extendScalars_resolution_iso` — `F ⊗_P P'` resolves `A' = R' ⊗_R A`.
* `Dualizing.isZero_homology_totalDerivedExtensionScalars_relativeDualizingComplex` — the
  vanishing for `ω^•_{A/R} ⊗_P^L P'` over `P' = R'[x_1, …, x_n]`.
* `Dualizing.isZero_homology_totalDerivedExtensionScalars_upperShriekFunctor_of_lt` — the
  vanishing for `ω^•_{A/R} ⊗_R^L R'`.

## Implementation notes

The source identifies `ω^•_{A/R} ⊗_A^L A'` with `ω^•_{A'/R'}` by [Stacks, Tag 0BZV] and reads off
the cohomology of the latter.  Only cohomology modules are needed here, and they are computed on
complexes, so no identification of `A'`-linear structures enters.  Write `P = R[x_1, …, x_n] → A`
for the presentation and `P' = R'[x_1, …, x_n]`.  Flatness of `A` over `R` makes `A` perfect over
`P` with a finite projective resolution `F` in degrees `[-n, 0]` ([Stacks, Tag 068X]), and
`ω^•_{A/R}` read over `P` is `Hom^•_P(F, P)[n]`.  By [Stacks, Tag 0661] along the flat `R → P`,
`ω^•_{A/R} ⊗_R^L R'` is `ω^•_{A/R} ⊗_P^L P'` restricted to `R'`; on the bounded complex of
projectives `Hom^•_P(F, P)` derived base change is termwise, and termwise it is
`Hom^•_{P'}(F ⊗_P P', P')` because the terms of `F` are finite projective.  Since `A` and `P` are
flat over `R`, `F ⊗_P P'` resolves `A'`, so the cohomology in degree `n + i` is
`Ext^{n+i}_{P'}(A', P')` ([Stacks, Tag 0A66]), which is the cohomology of `ω^•_{A'/R'}` in degree
`i` ([Stacks, Tag 0A71]); it vanishes for `i < -d` by [Stacks, Tag 0E9P] for `R' → A'`, whose
fibres have dimension at most `d`.

## References

* [Stacks Project, Tag 0E9Q](https://stacks.math.columbia.edu/tag/0E9Q)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 0A66](https://stacks.math.columbia.edu/tag/0A66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace StacksDraft.RelativelyPerfect

open scoped TensorProduct

/-- The canonical map `B ⊗_A Hom_A(X, N) → Hom_B(B ⊗_A X, B ⊗_A N)` is natural in `X`. -/
private lemma liftBaseChange_baseChangeHom_lcomp
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Type*} (N : Type*) [AddCommGroup X] [AddCommGroup Y] [AddCommGroup N]
    [Module A X] [Module A Y] [Module A N] (h : X →ₗ[A] Y)
    (t : B ⊗[A] (Y →ₗ[A] N)) :
    LinearMap.liftBaseChange B (LinearMap.baseChangeHom A B X N)
        (LinearMap.baseChange B (LinearMap.lcomp A N h) t) =
      (LinearMap.liftBaseChange B (LinearMap.baseChangeHom A B Y N) t).comp
        (LinearMap.baseChange B h) := by
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs, LinearMap.add_comp]
  | tmul b φ =>
    simp only [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul,
      LinearMap.baseChangeHom_apply, LinearMap.smul_comp]
    change b • LinearMap.baseChange B (φ ∘ₗ h) = _
    rw [LinearMap.baseChange_comp]

/-- **Linear maps out of a finite projective module base-change to linear maps out of the scalar
extension.**  A finite projective module is a retract of a finite free one, for which this is
`Module.isBaseChange_map_of_finite_free`, and the canonical comparison is natural in the source. -/
lemma linearMap_isBaseChange_of_finite_projective
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M N : Type*) [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A M] [Module.Projective A M] :
    IsBaseChange B (LinearMap.baseChangeHom A B M N) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  have hF := Module.isBaseChange_map_of_finite_free (R := A) N B (Fin n)
  let ΦM := LinearMap.liftBaseChange B (LinearMap.baseChangeHom A B M N)
  let ΦF := LinearMap.liftBaseChange B (LinearMap.baseChangeHom A B (Fin n → A) N)
  have hΦF : ΦF = hF.equiv.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext b φ
    simp [ΦF]
  have hΦFbij : Function.Bijective ΦF := by rw [hΦF]; exact hF.equiv.bijective
  let α := LinearMap.baseChange B (LinearMap.lcomp A N g)
  let β := LinearMap.baseChange B (LinearMap.lcomp A N f)
  have hαβ : ∀ t, α (β t) = t := by
    intro t
    change (α ∘ₗ β) t = t
    rw [← LinearMap.baseChange_comp]
    have : (LinearMap.lcomp A N g) ∘ₗ (LinearMap.lcomp A N f) = LinearMap.id := by
      ext φ x
      change φ (f (g x)) = φ x
      rw [← LinearMap.comp_apply f g, hfg, LinearMap.id_apply]
    rw [this, LinearMap.baseChange_id, LinearMap.id_apply]
  have hnatα : ∀ t, ΦM (α t) = (ΦF t).comp (LinearMap.baseChange B g) :=
    liftBaseChange_baseChangeHom_lcomp N g
  have hnatβ : ∀ t, ΦF (β t) = (ΦM t).comp (LinearMap.baseChange B f) :=
    liftBaseChange_baseChangeHom_lcomp N f
  have hfgB : (LinearMap.baseChange B f).comp (LinearMap.baseChange B g) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_id]
  have hbij : Function.Bijective ΦM := by
    refine ⟨fun t s hts => ?_, fun ψ => ?_⟩
    · have h1 : ΦF (β t) = ΦF (β s) := by rw [hnatβ, hnatβ, hts]
      rw [← hαβ t, ← hαβ s, hΦFbij.1 h1]
    · obtain ⟨y, hy⟩ := hΦFbij.2 (ψ.comp (LinearMap.baseChange B f))
      exact ⟨α y, by rw [hnatα, hy, LinearMap.comp_assoc, hfgB, LinearMap.comp_id]⟩
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective ΦM hbij) fun x => ?_
  change ΦM (1 ⊗ₜ x) = _
  simp [ΦM]

section

open scoped ModuleCat.Algebra

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower

/-- For a finite projective source and a bounded target, base change of cochains is bijective. -/
lemma homCochainBaseChange_bijective_of_projective
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{u} A) ℤ) (a b n : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Projective A (P.X i)] :
    Function.Bijective (homCochainBaseChange f P F n) := by
  let := f.toAlgebra
  let I := {t : CochainComplex.HomComplex.Triplet n // a ≤ t.q ∧ t.q ≤ b}
  have : Finite I := finite_homCochain_support n a b
  let Ext := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)
  let P' := Ext.obj P
  let F' := Ext.obj F
  let eM := (homCochainRestrict P F n a b).trans
    (LinearEquiv.piCongrRight fun t : I ↦
      (ModuleCat.homLinearEquiv (S := A) (M := P.X t.val.p) (N := F.X t.val.q)))
  let eN := (homCochainRestrict P' F' n a b).trans
    (LinearEquiv.piCongrRight fun t : I ↦
      (ModuleCat.homLinearEquiv (S := B) (M := P'.X t.val.p) (N := F'.X t.val.q)))
  dsimp [P', F', Ext] at eN
  have : IsScalarTower A B ((t : I) →
      B ⊗[A] (P.X t.val.p) →ₗ[B] B ⊗[A] (F.X t.val.q)) :=
    ⟨fun r s z ↦ by funext t; apply LinearMap.ext; intro x; exact smul_assoc r s (z t x)⟩
  let g := LinearMap.pi fun t : I ↦
    (LinearMap.baseChangeHom A B (P.X t.val.p) (F.X t.val.q)).comp (LinearMap.proj t)
  have hg : IsBaseChange B g :=
    IsBaseChange.pi _ (fun t ↦ linearMap_isBaseChange_of_finite_projective _ _)
  let e := (eM.baseChange A B).trans (hg.equiv.trans eN.symm)
  have he : homCochainBaseChange f P F n = e.toLinearMap := by
    refine LinearMap.ext fun t => ?_
    change B ⊗[A] CochainComplex.HomComplex.Cochain P F n at t
    change (LinearMap.liftBaseChange B (homCochainExtendScalars f P F n)) t = e t
    apply eN.injective
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [map_add, ht, hs]
    | tmul c z =>
      simp only [LinearMap.liftBaseChange_tmul, map_smul, e, LinearEquiv.trans_apply,
        LinearEquiv.baseChange_tmul]
      change c • eN ((homCochainExtendScalars f P F n) z) =
        eN (eN.symm (hg.equiv (c ⊗ₜ[A] eM z)))
      refine Eq.trans ?_ (eN.apply_symm_apply (hg.equiv (c ⊗ₜ[A] eM z))).symm
      rfl
  rw [he]
  exact e.bijective

/-- The base change of the Hom complex out of a finite projective complex into a bounded
complex is the Hom complex between the base changes. -/
noncomputable def homComplexBaseChangeIsoOfProjective
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (P F : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [F.IsStrictlyGE a] [F.IsStrictlyLE b]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Projective A (P.X i)] :
    ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.HomComplexR A P F) ≅
      CochainComplex.HomComplexR B
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (.up ℤ)).obj F) := by
  have : ∀ n, IsIso ((homComplexBaseChange f P F).f n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (homCochainBaseChange_bijective_of_projective f P F a b n)
  have : IsIso (homComplexBaseChange f P F) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (homComplexBaseChange f P F)

end

end StacksDraft.RelativelyPerfect

namespace Dualizing

/-- The degree-`i` term of the Hom complex into the unit is the `P`-linear dual of the term in
degree `-i`. -/
def homComplexUnitTermLinearEquiv {P : Type u} [CommRing P]
    (E : CochainComplex (ModuleCat.{u} P) ℤ) (i : ℤ) :
    (CochainComplex.HomComplexR P E
        ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P))).X i ≃ₗ[P]
      Module.Dual P (E.X (-i)) :=
  ((CochainComplex.HomComplex.Cochain.toSingleEquiv
      (K := E) (X := ModuleCat.of P P) (by omega : -i + i = 0)).toLinearEquiv
        (by
          intro c x
          ext y
          change c * _ = c * _
          rfl)).trans ModuleCat.homLinearEquiv

/-- `A` itself, read in `D(P)` along the presenting surjection, is isomorphic to `ULift A` read
there. -/
private noncomputable def singleRestrictScalarsULiftIso' {R A : Type u} [CommRing R]
    [CommRing A] [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) :
    (ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
        ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))) :=
  ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of A A) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).mapIso
      ((ModuleCat.restrictScalars.{u} p.toRingHom).mapIso
        (LinearEquiv.toModuleIso (ULift.moduleEquiv.{u, u, u} (R := A) (M := A)).symm))

/-- **A projective resolution of `A` over `P` and the dual it presents.**  For a flat finite type
homomorphism of Noetherian rings and a polynomial presentation `R → P → A` in `n` variables, `A`
read over `P` is represented by a complex `F` of finite projective `P`-modules in degrees
`[-n, 0]`, and `ω^•_{A/R}` read over `P` is the `n`-fold shift of the Hom complex
`Hom^•_P(F, P)`. -/
@[sga "6 VI 1.5.2" "special case"]
theorem exists_projectiveResolution_relativeDualizingComplex_iso
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [IsNoetherianRing A]
    [Algebra R A] [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A)) :
    ∃ F : CochainComplex (ModuleCat.{u} p.Poly) ℤ,
      (∀ i, Module.Finite p.Poly (F.X i) ∧ Module.Projective p.Poly (F.X i)) ∧
      F.IsStrictlyGE (-(p.variableCount : ℤ)) ∧ F.IsStrictlyLE 0 ∧
      Nonempty (DerivedCategory.Q.obj F ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))) ∧
      Nonempty ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (DerivedCategory.Q.obj (CochainComplex.HomComplexR p.Poly F
          ((CochainComplex.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
            (ModuleCat.of p.Poly p.Poly))))⟦(p.variableCount : ℤ)⟧) := by
  let P := p.Poly
  let U := ModuleCat.restrictScalars.{u} p.toRingHom
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  let instM₀ : Module P (M₀ : Type u) := M₀.isModule
  have hM₀ : Module.Finite P (M₀ : Type u) := finite_restrictScalars_ulift p
  have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M₀) :=
    isPseudoCoherent_single_of_finite M₀
  have hamp := (isPerfect_and_hasFlatRepresentative_single_restrictScalars_ulift_of_flat p).2
  obtain ⟨F, hfp, hGE, hLE, ⟨e⟩⟩ :=
    (StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, u}
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M₀)).2 _ _ hpc hamp
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let Punit := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let (i : ℤ) := (hfp i).1
  let (i : ℤ) := (hfp i).2
  have : F.IsStrictlyLE 0 := hLE
  let n : ℤ := p.variableCount
  let e' : U.mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) ≅
      DerivedCategory.Q.obj F := singleRestrictScalarsULiftIso' p ≪≫ e
  let eHom : (StacksDraft.DerivedHom.DerivedInternalHom.Model.hom P).obj
      (Opposite.op (U.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))), Punit) ≅
      DerivedCategory.Q.obj (CochainComplex.HomComplexR P F J) :=
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := P)).hom.mapIso
        (e'.symm.op.prod (Iso.refl _)) ≪≫
      StacksDraft.DerivedHom.projectiveHomComparison.iso F J 0
  refine ⟨F, hfp, hGE, hLE, ⟨e.symm⟩, ⟨?_⟩⟩
  exact U.mapDerivedCategory.mapIso ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso
        ((derivedHom.{u, 0, u} p.toRingHom).mapIso p.derivedExtensionUnitIso)) ≪≫
      (U.mapDerivedCategory.commShiftIso n).app ((derivedHom.{u, 0, u} p.toRingHom).obj Punit) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} P)) n).mapIso
        ((nonempty_modelHomIsoRestrictScalarsDerivedHom p.toRingHom Punit).some.symm ≪≫ eHom)

/-- The Hom complex has no cohomology in a degree where its cohomology classes vanish. -/
theorem isZero_homology_homComplexR_of_subsingleton_cohomologyClass {S : Type u} [CommRing S]
    (K L : CochainComplex (ModuleCat.{u} S) ℤ) (k : ℤ)
    [Subsingleton (CochainComplex.HomComplex.CohomologyClass K L k)] :
    IsZero ((CochainComplex.HomComplexR S K L).homology k) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (k - 1) k (k + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : CochainComplex.HomComplex.δ k (k + 1) x = 0 := hx
  let c : CochainComplex.HomComplex.Cocycle K L k :=
    CochainComplex.HomComplex.Cocycle.mk x (k + 1) rfl hx'
  have hc : CochainComplex.HomComplex.CohomologyClass.mk c = 0 := Subsingleton.elim _ _
  rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff,
    CochainComplex.HomComplex.mem_coboundaries_iff c (k - 1) (by omega)] at hc
  obtain ⟨β, hβ⟩ := hc
  exact ⟨β, by
    change CochainComplex.HomComplex.δ (k - 1) k β = x
    rw [hβ]
    rfl⟩

/-- **Cohomological concentration after base change.**  For a flat finite type homomorphism of
Noetherian rings whose fibres have dimension at most `d`, and for a Noetherian base change
`R → R'`, the relative dualizing complex of `R' → R' ⊗_R A` has cohomology only in degrees
`[-d, 0]`: the fibres of the base change have dimension at most `d` as well. -/
theorem isZero_homology_upperShriekFunctor_baseChange
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : i ∉ Set.Icc (-(d : ℤ)) 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (TensorProduct R R' A)) i).obj
      ((p.baseChange (R' := R')).upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R')))) := by
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  let : Algebra A (TensorProduct R R' A) := Algebra.TensorProduct.rightAlgebra
  let : Algebra R' (TensorProduct R R' A) := Algebra.TensorProduct.leftAlgebra
  have : Algebra.IsPushout R A R' (TensorProduct R R' A) :=
    Algebra.IsPushout.symm (TensorProduct.isPushout (R := R) (S := R') (T := A))
  have hft : Algebra.FiniteType R' (TensorProduct R R' A) :=
    RingHom.finiteType_algebraMap.mp (p.baseChange (R' := R')).finiteType
  have : IsNoetherianRing (TensorProduct R R' A) :=
    Algebra.FiniteType.isNoetherianRing R' (TensorProduct R R' A)
  have : Module.Flat R' (TensorProduct R R' A) := Module.Flat.baseChange R R' A
  have hd' : ∀ q : PrimeSpectrum (TensorProduct R R' A),
      Algebra.relativeDimensionAt R' q.asIdeal ≤ (d : WithBot ℕ∞) := by
    intro q
    rw [← Algebra.IsPushout.relativeDimensionAt_comap_eq R A R' (TensorProduct R R' A) q]
    exact (le_iSup (fun q : PrimeSpectrum A => Algebra.relativeDimensionAt R q.asIdeal) _).trans
      (iSup_le hd)
  exact isZero_homology_upperShriekFunctor_unit_of_notMem_Icc (p.baseChange (R' := R')) d hd' i hi

/-- **`Ext` into the polynomial algebra after base change.**  With `p'` the base change of the
presentation to a Noetherian `R'`, `P'` its polynomial algebra and `A' = R' ⊗_R A`,
`Ext^{n+i}_{P'}(A', P')` vanishes for `i < -d`. -/
theorem subsingleton_ext_baseChange_poly
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : i < -(d : ℤ)) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (p.baseChange (R' := R')).Poly) 0).obj
        ((ModuleCat.restrictScalars (p.baseChange (R' := R')).toRingHom).obj
          (ModuleCat.of (TensorProduct R R' A) (ULift.{u} (TensorProduct R R' A)))))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (p.baseChange (R' := R')).Poly) 0).obj
        (ModuleCat.of (p.baseChange (R' := R')).Poly (p.baseChange (R' := R')).Poly))
      ((p.variableCount : ℤ) + i)) := by
  let p' := p.baseChange (R' := R')
  let T := TensorProduct R R' A
  let RF := derivedHom.{u, 0, u} p'.toRingHom
  let input := (DerivedCategory.singleFunctor (ModuleCat.{u} p'.Poly) 0).obj
    (ModuleCat.of p'.Poly p'.Poly)
  have hzeroω := isZero_homology_upperShriekFunctor_baseChange (R' := R') p d hd i
    (fun h => not_le.2 hi h.1)
  have eUpper : (p'.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R') 0).obj (ModuleCat.of R' R'))) ≅
        (shiftFunctor (DerivedCategory (ModuleCat.{u} T)) (p'.variableCount : ℤ)).obj
          (RF.obj input) := by
    dsimp [PolynomialPresentation.upperShriekFunctor, RF, input]
    exact (shiftFunctor (DerivedCategory (ModuleCat.{u} T)) (p'.variableCount : ℤ)).mapIso
      ((derivedHom.{u, 0, u} p'.toRingHom).mapIso p'.derivedExtensionUnitIso)
  have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} T)
      ((p'.variableCount : ℤ) + i)).obj (RF.obj input)) :=
    (hzeroω.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) i).mapIso
      eUpper.symm)).of_iso
      ((StacksDraft.PseudoCoherence.homologyFunctorShiftIso.{u, u}
        (R := T) (p'.variableCount : ℤ) i).app (RF.obj input)).symm
  let α := (coextendScalarsToDerivedCategory p'.toRingHom).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} p'.Poly) (ComplexShape.up ℤ))
  let eExt := (derivedCoextendScalarsHomologyLinearEquivExt p'.toRingHom RF α).linearEquiv
    input ((p'.variableCount : ℤ) + i)
  have : Subsingleton ((ModuleCat.restrictScalars p'.toRingHom).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) ((p'.variableCount : ℤ) + i)).obj
        (RF.obj input))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      ((ModuleCat.restrictScalars p'.toRingHom).map_isZero hzero)
  exact eExt.toEquiv.symm.subsingleton

/-- **`P' ⊗_P A = A'` as `P'`-modules.**  Extending scalars along `P → P'` the target `A` of a
presentation, read over `P`, gives the base-changed algebra `A' = R' ⊗_R A` read over `P'` through
the base-changed presentation. -/
noncomputable def extendScalarsTargetIso {R A R' : Type u} [CommRing R] [CommRing A]
    [CommRing R'] [Algebra R A] [Algebra R R'] (p : PolynomialPresentation (algebraMap R A)) :
    letI : Algebra p.Poly (p.baseChange (R' := R')).Poly := MvPolynomial.algebraMvPolynomial
    (ModuleCat.extendScalars.{u, u, u} (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).obj
        ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))) ≅
      (ModuleCat.restrictScalars (p.baseChange (R' := R')).toRingHom).obj
        (ModuleCat.of (TensorProduct R R' A) (ULift.{u} (TensorProduct R R' A))) := by
  let P := MvPolynomial (Fin p.variableCount) R
  let p' := p.baseChange (R' := R')
  let P' := MvPolynomial (Fin p.variableCount) R'
  let : Algebra P A := p.toRingHom.toAlgebra
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  have : IsScalarTower R P A := IsScalarTower.of_algebraMap_eq' p.commutes.symm
  have : IsScalarTower R P P' := inferInstance
  have : IsScalarTower R R' P' := inferInstance
  have : Algebra.IsPushout R R' P P' := inferInstance
  have hmap : algebraMap P P' = MvPolynomial.map (algebraMap R R') :=
    MvPolynomial.algebraMap_def
  have hp' := baseChange_toRingHom_eq p rfl hmap
  let c := Algebra.IsPushout.cancelBaseChangeAlg R R' P P' A
  have hc : ∀ x : P', c (x ⊗ₜ[P] (1 : A)) = p'.toRingHom x := by
    intro x
    rw [hp']
    let : Algebra P' (TensorProduct P A P') := Algebra.TensorProduct.rightAlgebra
    change _ = c ((Algebra.TensorProduct.commRight P P' A).symm ((1 : A) ⊗ₜ[P] x))
    rw [Algebra.TensorProduct.commRight_symm_tmul]
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  let e₀ : (M₀ : Type u) ≃ₗ[P] A :=
    { toFun := fun x => x.down
      invFun := fun a => ULift.up a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₁ := LinearEquiv.baseChange P P' (M₀ : Type u) A e₀
  let X := (ModuleCat.restrictScalars p'.toRingHom).obj
      (ModuleCat.of (TensorProduct R R' A) (ULift.{u} (TensorProduct R R' A)))
  letI : Module P' (X : Type u) := X.isModule
  let e₂ : TensorProduct P P' A ≃ₗ[P'] (X : Type u) :=
    { toFun := fun t => ULift.up (c t)
      invFun := fun y => c.symm y.down
      map_add' := fun t s => by
        change ULift.up (c (t + s)) = ULift.up (c t + c s)
        rw [map_add]
      map_smul' := fun x t => by
        change ULift.up (c (x • t)) = ULift.up (p'.toRingHom x * c t)
        rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply, hc]
        rfl
      left_inv := fun t => by simp
      right_inv := fun y => by
        change ULift.up (c (c.symm y.down)) = y
        rw [AlgEquiv.apply_symm_apply]
        rfl }
  let iso : ModuleCat.of P' (TensorProduct P P' (M₀ : Type u)) ≅ ModuleCat.of P' (X : Type u) :=
    (e₁.trans e₂).toModuleIso
  exact iso

/-- Extending scalars termwise commutes with placing a module in degree `0` in the derived
category. -/
private noncomputable def extendScalarsSingleIso {P P' : Type u} [CommRing P] [CommRing P']
    (f : P →+* P') (M : ModuleCat.{u} P) :
    DerivedCategory.Q.obj (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} P') 0).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars.{u, u, u} f)
        (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _).symm

/-- A polynomial algebra over `R` is flat, so Tor independent over `R` from every `R`-algebra. -/
private theorem torIndependent_mvPolynomial_left {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] (n : ℕ) :
    RingTheory.TorIndependence.TorIndependent R (MvPolynomial (Fin n) R) R' := by
  rw [RingTheory.TorIndependence.torIndependent_iff_isZero_tor]
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact isZero_Tor_succ_of_flat (ModuleCat.of R (MvPolynomial (Fin n) R)) (ModuleCat.of R R') k

/-- **The base change of a resolution of `A` resolves `A'`.**  Let `F` be a bounded above complex
of projective `P`-modules representing `A` over `P`.  Extending scalars along `P → P'` in each
degree gives a complex representing `A' = R' ⊗_R A` over `P'`: `A` is flat over `R` and `P` is flat
over `R`, so `A ⊗_P^L P' = A ⊗_R^L R' = A'` by the Tor independence of [Stacks, Tag 0661]. -/
theorem nonempty_extendScalars_resolution_iso
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    [Module.Flat R A] (p : PolynomialPresentation (algebraMap R A))
    (F : CochainComplex (ModuleCat.{u} p.Poly) ℤ) (b : ℤ) [F.IsStrictlyLE b]
    [∀ i, Projective (F.X i)]
    (eF : DerivedCategory.Q.obj F ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
      ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))) :
    letI : Algebra p.Poly (p.baseChange (R' := R')).Poly := MvPolynomial.algebraMvPolynomial
    Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u}
          (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj F) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (p.baseChange (R' := R')).Poly) 0).obj
        ((ModuleCat.restrictScalars (p.baseChange (R' := R')).toRingHom).obj
          (ModuleCat.of (TensorProduct R R' A) (ULift.{u} (TensorProduct R R' A))))) := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  have : IsScalarTower R P P' := inferInstance
  have : IsScalarTower R R' P' := inferInstance
  have : Algebra.IsPushout R P R' P' :=
    (inferInstance : Algebra.IsPushout R R' P P').symm
  have hTor := torIndependent_mvPolynomial_left (R := R) (R' := R') p.variableCount
  let f := algebraMap P P'
  let DP := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  have hr (r : R) : p.toRingHom (algebraMap R P r) = algebraMap R A r :=
    congrArg (fun g : R →+* A => g r) p.commutes
  have hM : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R P)).obj M₀) := by
    let eR : ((ModuleCat.restrictScalars (algebraMap R P)).obj M₀ : Type u) ≃ₗ[R] A :=
      { toFun := fun x => x.down
        invFun := fun a => ULift.up a
        map_add' := fun _ _ => rfl
        map_smul' := by
          intro r x
          change p.toRingHom (algebraMap R P r) * x.down = r • x.down
          rw [hr, Algebra.smul_def]
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Module.Flat.of_linearEquiv eR
  have h1 : IsIso (DP.comparison.app F) := DP.comparison_isIso_of_projective F b
  have h2 : IsIso (DP.comparison.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M₀)) :=
    RingTheory.TorIndependence.isIso_comparison_single_of_flat (T := P') hTor M₀ hM
  let e₁ : DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ≅
      DP.functor.obj (DerivedCategory.Q.obj F) := (asIso (DP.comparison.app F)).symm
  let e₂ : DP.functor.obj (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M₀)) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M₀)) :=
    @asIso _ _ _ _ (DP.comparison.app ((CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj M₀))
      h2
  exact ⟨e₁ ≪≫ DP.functor.mapIso (eF ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ 0).app M₀) ≪≫
    e₂ ≪≫ extendScalarsSingleIso f M₀ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (extendScalarsTargetIso p)⟩

/-- **The base-changed resolution sees no `Ext` into `P'` below `n - d`.**  Let `F` be a bounded
above complex of finite projective `P`-modules representing `A` over `P`.  The Hom complex from
its base change to `P'` into the base change of `P` has no cohomology classes in degrees `n + i`
for `i < -d`: it computes `Ext^{n+i}_{P'}(A', P')`, which vanishes by
`Dualizing.subsingleton_ext_baseChange_poly`. -/
theorem subsingleton_cohomologyClass_extendScalars_resolution
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (F : CochainComplex (ModuleCat.{u} p.Poly) ℤ) [F.IsStrictlyLE 0]
    [∀ i, Module.Projective p.Poly (F.X i)]
    (eF : DerivedCategory.Q.obj F ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
      ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))))
    (i : ℤ) (hi : i < -(d : ℤ)) :
    letI : Algebra p.Poly (p.baseChange (R' := R')).Poly := MvPolynomial.algebraMvPolynomial
    Subsingleton (CochainComplex.HomComplex.CohomologyClass
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)
      (((ModuleCat.extendScalars.{u, u, u}
        (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
          (ModuleCat.of p.Poly p.Poly)))
      ((p.variableCount : ℤ) + i)) := by
  let P := p.Poly
  let p' := p.baseChange (R' := R')
  let P' := p'.Poly
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let f := algebraMap P P'
  let E := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)
  let F' := E.obj F
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let J' := E.obj J
  let k : ℤ := (p.variableCount : ℤ) + i
  have hF'LE : CochainComplex.IsStrictlyLE F' 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact (ModuleCat.extendScalars.{u, u, u} f).map_isZero (F.isZero_of_isStrictlyLE 0 j hj)
  have hF'proj : ∀ j, Projective (F'.X j) := fun j =>
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).map_projective _ inferInstance
  let e₁ := cohomologyClassRHomAddEquiv F' J' 0 k
  obtain ⟨eF'⟩ := nonempty_extendScalars_resolution_iso (R' := R') p F 0 eF
  let eJ' : DerivedCategory.Q.obj J' ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} P') 0).obj (ModuleCat.of P' P') :=
    extendScalarsSingleIso f (ModuleCat.of P P) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (extendScalarsUnitIso f)
  let eSrc : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{u} P') (ComplexShape.up ℤ)).obj F') ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} P') 0).obj
        ((ModuleCat.restrictScalars p'.toRingHom).obj
          (ModuleCat.of (TensorProduct R R' A) (ULift.{u} (TensorProduct R R' A)))) :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} P')).app F' ≪≫ eF'
  let eTgt : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{u} P') (ComplexShape.up ℤ)).obj (J'⟦k⟧)) ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P') 0).obj (ModuleCat.of P' P'))⟦k⟧ :=
    (DerivedCategory.quotientCompQhIso (ModuleCat.{u} P')).app (J'⟦k⟧) ≪≫
      (DerivedCategory.Q.commShiftIso k).app J' ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} P')) k).mapIso eJ'
  have : Subsingleton (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{u} P') (ComplexShape.up ℤ)).obj F') ⟶
      DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{u} P') (ComplexShape.up ℤ)).obj (J'⟦k⟧))) :=
    (Iso.homCongr eSrc eTgt).subsingleton_congr.mpr
      (subsingleton_ext_baseChange_poly (R' := R') p d hd i hi)
  exact e₁.toEquiv.subsingleton

/-- **Cohomology of `ω^•_{A/R} ⊗_P^L P'` below `-d`.**  For a flat finite type homomorphism of
Noetherian rings all of whose fibres have dimension at most `d`, a polynomial presentation
`R → P → A` and a Noetherian `R'`, the derived base change along `P → P' = R'[x_1, …, x_n]` of
`ω^•_{A/R}` read over `P` has no cohomology in degrees below `-d`.

`ω^•_{A/R}` over `P` is `Hom^•_P(F, P)[n]` for a finite projective resolution `F` of `A`, so its
base change is `Hom^•_{P'}(F ⊗_P P', P')[n]`; by Tor independence `F ⊗_P P'` resolves
`A' = R' ⊗_R A`, so this computes `Ext^{n+i}_{P'}(A', P')`, which is the cohomology of
`ω^•_{A'/R'}` in degree `i` and vanishes for `i < -d`. -/
theorem isZero_homology_totalDerivedExtensionScalars_relativeDualizingComplex
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : i < -(d : ℤ)) :
    letI : Algebra p.Poly (p.baseChange (R' := R')).Poly := MvPolynomial.algebraMvPolynomial
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (p.baseChange (R' := R')).Poly) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap p.Poly (p.baseChange (R' := R')).Poly)).functor.obj
        ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))) := by
  let P := p.Poly
  let p' := p.baseChange (R' := R')
  let P' := p'.Poly
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  let f := algebraMap P P'
  let n : ℤ := p.variableCount
  obtain ⟨F, hfp, hGE, hLE, ⟨eF⟩, ⟨eG⟩⟩ :=
    exists_projectiveResolution_relativeDualizingComplex_iso p
  let (j : ℤ) := (hfp j).1
  let (j : ℤ) := (hfp j).2
  have : F.IsStrictlyLE 0 := hLE
  have : F.IsStrictlyGE (-n) := hGE
  let J := (CochainComplex.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let Hc := CochainComplex.HomComplexR P F J
  have hHcLE : CochainComplex.IsStrictlyLE Hc n := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have : Subsingleton (F.X (-j)) :=
      ModuleCat.isZero_iff_subsingleton.mp (F.isZero_of_isStrictlyGE (-n) (-j) (by omega))
    exact (homComplexUnitTermLinearEquiv F j).injective.subsingleton
  have hHcproj : ∀ j, Projective (Hc.X j) := fun j => by
    have : Module.Projective P (Hc.X j) :=
      Module.Projective.of_equiv (homComplexUnitTermLinearEquiv F j).symm
    infer_instance
  let DP := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  have hc : IsIso (DP.comparison.app Hc) := DP.comparison_isIso_of_projective Hc n
  let E := (ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex (ComplexShape.up ℤ)
  let eDP : DP.functor.obj ((ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅
      (DerivedCategory.Q.obj (E.obj Hc))⟦n⟧ :=
    DP.functor.mapIso eG ≪≫ (DP.functor.commShiftIso n).app (DerivedCategory.Q.obj Hc) ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} P')) n).mapIso
        (@asIso _ _ _ _ (DP.comparison.app Hc) hc)
  have : Subsingleton (CochainComplex.HomComplex.CohomologyClass (E.obj F) (E.obj J) (n + i)) :=
    subsingleton_cohomologyClass_extendScalars_resolution (R' := R') p d hd F eF i hi
  have hzero : IsZero ((CochainComplex.HomComplexR P' (E.obj F) (E.obj J)).homology (n + i)) :=
    isZero_homology_homComplexR_of_subsingleton_cohomologyClass _ _ _
  exact hzero.of_iso <| (DerivedCategory.homologyFunctor (ModuleCat.{u} P') i).mapIso eDP ≪≫
    (StacksDraft.PseudoCoherence.homologyFunctorShiftIso.{u, u} (R := P') n i).app _ ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} P') (n + i)).app (E.obj Hc) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} P') (ComplexShape.up ℤ) (n + i)).mapIso
      (StacksDraft.RelativelyPerfect.homComplexBaseChangeIsoOfProjective f F J 0 0)

/-- `PseudoCoherence.restrictScalarsDerivedCompIso` with the composite given by an equation. -/
private noncomputable def restrictScalarsDerivedCompIsoOfEq' {R P A : Type u} [CommRing R]
    [CommRing P] [CommRing A] (f : R →+* P) (g : P →+* A) (fg : R →+* A) (hfg : fg = g.comp f)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.restrictScalars.{u} fg).mapDerivedCategory.obj K ≅
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars.{u} g).mapDerivedCategory.obj K) := by
  subst hfg
  exact PseudoCoherence.restrictScalarsDerivedCompIso f g K

/-- **The derived base change of `ω^•_{A/R}` has no cohomology below `-d`.**  For a flat finite
type homomorphism of Noetherian rings all of whose fibres have dimension at most `d` and a
Noetherian `R'`, the derived base change `ω^•_{A/R} ⊗_R^L R'` of the relative dualizing complex,
read as a complex of `R`-modules, has no cohomology in degrees below `-d`.

Nothing is carried.  By the Tor-independent base change of [Stacks, Tag 0661] along the flat
`R → P`, the derived base change along `R → R'` of `ω^•_{A/R}` read over `R` is the derived base
change along `P → P'` of `ω^•_{A/R}` read over `P`, restricted to `R'`; and that has no cohomology
below `-d` by
`Dualizing.isZero_homology_totalDerivedExtensionScalars_relativeDualizingComplex`. -/
theorem isZero_homology_totalDerivedExtensionScalars_upperShriekFunctor_of_lt
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing R']
    [Algebra R A] [Algebra R R'] [Module.Flat R A]
    (p : PolynomialPresentation (algebraMap R A)) (d : ℕ)
    (hd : ∀ q : PrimeSpectrum A, Algebra.relativeDimensionAt R q.asIdeal ≤ (d : WithBot ℕ∞))
    (i : ℤ) (hi : i < -(d : ℤ)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (algebraMap R R')).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R R)))))) := by
  let P := MvPolynomial (Fin p.variableCount) R
  let P' := MvPolynomial (Fin p.variableCount) R'
  let : Algebra P P' := MvPolynomial.algebraMvPolynomial
  have : IsScalarTower R P P' := inferInstance
  have : IsScalarTower R R' P' := inferInstance
  have : Algebra.IsPushout R P R' P' :=
    (inferInstance : Algebra.IsPushout R R' P P').symm
  have hTor := torIndependent_mvPolynomial_left (R := R) (R' := R') p.variableCount
  let ω := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))
  let G := (ModuleCat.restrictScalars.{u} p.toRingHom).mapDerivedCategory.obj ω
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R R')
  let DP := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap P P')
  have : Tg.functor.IsLeftDerivedFunctor Tg.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := Tg.isLeftDerived
  have : DP.functor.IsLeftDerivedFunctor DP.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} P) (ComplexShape.up ℤ)) := DP.isLeftDerived
  let cmp :=
    (@RingTheory.TorIndependence.derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1,
        u + 1} R P R' P' _ _ _ _ _ _ _ _ (algebraMap R P) (algebraMap R R')
      (algebraMap P P') (algebraMap R' P')
      ((IsScalarTower.algebraMap_eq R P P').symm.trans (IsScalarTower.algebraMap_eq R R' P'))
      Tg.functor DP.functor Tg.comparison DP.comparison Tg.isLeftDerived DP.isLeftDerived).2.1
  have : IsIso cmp :=
    @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u,
        u, u + 1, u + 1, u + 1, u + 1} R P R' P' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hTor
      Tg.functor DP.functor Tg.comparison DP.comparison Tg.isLeftDerived DP.isLeftDerived
  have hcomp : algebraMap R A = p.toRingHom.comp (algebraMap R P) := p.commutes.symm
  have hP' := isZero_homology_totalDerivedExtensionScalars_relativeDualizingComplex
    (R' := R') p d hd i hi
  let F := ModuleCat.restrictScalars.{u} (algebraMap R' P')
  have hres : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
      (F.mapDerivedCategory.obj (DP.functor.obj G))) :=
    (F.map_isZero hP').of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F i).app _)
  refine hres.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).mapIso ?_)
  exact Tg.functor.mapIso (restrictScalarsDerivedCompIsoOfEq' (algebraMap R P) p.toRingHom _
    hcomp ω) ≪≫ asIso (cmp.app G)

end Dualizing

end

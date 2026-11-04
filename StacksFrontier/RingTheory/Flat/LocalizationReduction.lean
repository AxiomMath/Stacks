module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison

/-!
# Flatness from localization and reduction modulo an element

Let `M` be an object of the derived category of modules over a commutative ring `R`. If `M` has
no positive cohomology, and its derived base changes to both `R_f` and `R / fR` are flat modules
placed in degree zero, then `M` itself is a flat `R`-module placed in degree zero.

## Main definitions

There are no new definitions.

## Main results

* `Stacks.Flatness.LocalizationReduction.isomorphic_to_flat_module_of_localization_and_quotient`
  proves the local-to-global
  flatness criterion.

## Implementation notes

The two derived tensor products in the source are expressed by the canonical total derived
extension-of-scalars functors
(`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`). Being a module placed in
degree zero is expressed using the degree-zero single-object functor into the derived category.
The base-change comparison for derived tensor products is provided separately by
`CochainComplex.DerivedTensor.derivedExtensionScalarsTensorIso`; it is not a field of Equation
064H, and it uses canonically equivalent lifted scalar rings. The separate
`CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso` acts on the original rings
and identifies homology after localization with the literal localized module used in Tag 0H84.

The ring `R` lives in `Type u` while the modules live in `ModuleCat.{max v u} R`, so the shared
universe theory of termwise Tor amplitude does not apply directly. The bridge is
`StacksDraft.TorAmplitude.scalarLift`, the coefficient change along `ULift.ringEquiv`, which moves
the problem to the ring `ULift.{v} R` whose own universe is that of the modules; this is the same
device `StacksDraft.TorAmplitude.cokernel_flat_of_torAmplitude` uses internally.

## References

* [Stacks Project, Tag 0H85](https://stacks.math.columbia.edu/tag/0H85)
-/

open CategoryTheory CategoryTheory.Limits StacksDraft.TorAmplitude

namespace Stacks.Flatness.LocalizationReduction

universe u v w

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

/-! ### Termwise tensoring with independent ring and module universes -/

/-- The termwise tensor product complex `K ⊗ M`, with the ring universe and the module universe
independent. This is the spelling used by the large-universe Tor-amplitude theory of
`StacksDraft.TorAmplitude`, so its theorems apply without glue. -/
private noncomputable abbrev tensorCx {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (M : ModuleCat.{w} R) :
    CochainComplex (ModuleCat.{w} R) ℤ :=
  ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Termwise Tor amplitude in `[a, b]`: the cohomology of `K ⊗ M` vanishes outside `[a, b]` for
every module `M`. With the ring universe and the module universe independent. -/
private def HasTorAmplitudeIn {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{w} R) (i : ℤ), (i < a ∨ b < i) → IsZero ((tensorCx K M).homology i)

/-! ### Termwise vanishing from a bounded flat representative -/

/-- Shared-universe form: two bounded above complexes of flat modules that become isomorphic in
the derived category have isomorphic termwise tensor products in the derived category, hence the
same termwise cohomology.

The counit of the total left derived functor of termwise tensoring is invertible at a bounded
above complex of flats (`isIso_termwiseDerivedCounit_app_of_flat`), so that counit transports the
given isomorphism. -/
private theorem termwise_isZero_homology_of_flat_rep_same {S : Type w} [CommRing S]
    (K E : CochainComplex (ModuleCat.{w} S) ℤ)
    (hKb : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (K.X j))
    (hKf : ∀ j : ℤ, Module.Flat S (K.X j))
    (hEb : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (E.X j))
    (hEf : ∀ j : ℤ, Module.Flat S (E.X j))
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj E)
    (N : ModuleCat.{w} S) (i : ℤ) (hE : IsZero ((tensorCx E N).homology i)) :
    IsZero ((tensorCx K N).homology i) := by
  have hK := isIso_termwiseDerivedCounit_app_of_flat N K hKb hKf
  have hEiso := isIso_termwiseDerivedCounit_app_of_flat N E hEb hEf
  have hd : DerivedCategory.Q.obj (tensorCx K N) ≅ DerivedCategory.Q.obj (tensorCx E N) :=
    (asIso ((termwiseDerivedCounit N).app K)).symm ≪≫ (termwiseDerived N).mapIso e ≪≫
      asIso ((termwiseDerivedCounit N).app E)
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).obj
      (DerivedCategory.Q.obj (tensorCx E N))) :=
    hE.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} S) i).app (tensorCx E N))
  exact hz.of_iso
    (((DerivedCategory.homologyFunctorFactors (ModuleCat.{w} S) i).app (tensorCx K N)).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{w} S) i).mapIso hd)

/-- Change of coefficient ring on cochain complexes, along `ULift.ringEquiv`. -/
private noncomputable abbrev liftCx {R : Type u} [CommRing R] :
    CochainComplex (ModuleCat.{max u v} R) ℤ ⥤
      CochainComplex (ModuleCat.{max u v} (ULift.{v} R)) ℤ :=
  (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise tensoring commutes with the change of coefficient ring, on cochain complexes. -/
private noncomputable def liftCxTensorIso {R : Type u} [CommRing R]
    (M : ModuleCat.{max u v} R) :
    liftCx.{u, v} (R := R) ⋙
        (tensorModuleRight (scalarLift.obj M)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ liftCx.{u, v} (R := R) :=
  Functor.mapHomologicalComplexCompIso
      (Iso.refl (scalarLift.{u, v} (R := R) ⋙ tensorModuleRight (scalarLift.obj M)))
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (tensorScalarLiftIso M) (ComplexShape.up ℤ)).symm

/-- The change of coefficient ring is exact, so it preserves vanishing of cohomology. -/
private theorem isZero_homology_liftCx {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ) (h : IsZero (C.homology i)) :
    IsZero (((liftCx.{u, v} (R := R)).obj C).homology i) :=
  ((scalarLift.{u, v} (R := R)).map_isZero h).of_iso
    ((C.sc i).mapHomologyIso (scalarLift.{u, v} (R := R)))

/-- The change of coefficient ring is fully faithful, so it reflects vanishing of cohomology. -/
private theorem isZero_homology_of_liftCx {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (i : ℤ)
    (h : IsZero (((liftCx.{u, v} (R := R)).obj C).homology i)) :
    IsZero (C.homology i) :=
  IsZero.of_full_of_faithful_of_isZero (scalarLift.{u, v} (R := R)) _
    (h.of_iso ((C.sc i).mapHomologyIso (scalarLift.{u, v} (R := R))).symm)

/-- Independent-universe form: a bounded above complex of flat modules that is isomorphic in the
derived category to another bounded above complex of flats has the same termwise cohomology.

Over `ULift.{v} R` the ring and its modules share the universe `max u v`, so the shared-universe
statement applies to the lifted complexes; termwise tensoring commutes with the lift, and the lift
preserves and reflects vanishing of cohomology. -/
private theorem termwise_isZero_homology_of_flat_rep {R : Type u} [CommRing R]
    (K E : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hKb : BoundedAbove K) (hKf : ∀ j : ℤ, Module.Flat R (K.X j))
    (hEb : BoundedAbove E) (hEf : ∀ j : ℤ, Module.Flat R (E.X j))
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj E)
    (N : ModuleCat.{max u v} R) (i : ℤ) (hE : IsZero ((tensorCx E N).homology i)) :
    IsZero ((tensorCx K N).homology i) := by
  have hb (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (hC : BoundedAbove C) :
      ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (((liftCx.{u, v} (R := R)).obj C).X j) := by
    obtain ⟨n, hn⟩ := hC
    exact ⟨n, fun j hj => (scalarLift.{u, v} (R := R)).map_isZero (hn j hj)⟩
  have hf (C : CochainComplex (ModuleCat.{max u v} R) ℤ) (hC : ∀ j : ℤ, Module.Flat R (C.X j))
      (j : ℤ) : Module.Flat (ULift.{v} R) (((liftCx.{u, v} (R := R)).obj C).X j) := by
    show Module.Flat (ULift.{v} R) (C.X j)
    rw [Module.Flat.ulift_left_iff]
    exact hC j
  have e' : DerivedCategory.Q.obj ((liftCx.{u, v} (R := R)).obj K) ≅
      DerivedCategory.Q.obj ((liftCx.{u, v} (R := R)).obj E) :=
    ((scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors.app K).symm ≪≫
      (scalarLift.{u, v} (R := R)).mapDerivedCategory.mapIso e ≪≫
      (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors.app E
  have hEup : IsZero ((tensorCx ((liftCx.{u, v} (R := R)).obj E)
      ((scalarLift.{u, v} (R := R)).obj N)).homology i) :=
    (isZero_homology_liftCx (tensorCx E N) i hE).of_iso
      (HomologicalComplex.homologyMapIso ((liftCxTensorIso.{u, v} N).app E) i)
  have hKup := termwise_isZero_homology_of_flat_rep_same
    ((liftCx.{u, v} (R := R)).obj K) ((liftCx.{u, v} (R := R)).obj E)
    (hb K hKb) (hf K hKf) (hb E hEb) (hf E hEf) e' ((scalarLift.{u, v} (R := R)).obj N) i hEup
  exact isZero_homology_of_liftCx (tensorCx K N) i
    (hKup.of_iso (HomologicalComplex.homologyMapIso ((liftCxTensorIso.{u, v} N).app K) i).symm)

/-! ### The flat-localization homology comparison -/

/-- The flat-localization homology comparison supplies the literal localized-module
vanishing hypothesis of Tag 0H84 from vanishing after derived base change. -/
public theorem localizedHomology_isZero_of_baseChange
    {R : Type u} [CommRing R] (f : R)
    (N : DerivedCategory (ModuleCat.{max v u} R)) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max v u} (Localization.Away f)) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (algebraMap R (Localization.Away f))).functor.obj N))) :
    IsZero (ModuleCat.of R (LocalizedModule.Away f
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj N))) :=
  ((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).map_isZero h).of_iso
    ((CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso.{u, v} f i).app N).symm

/-! ### The chain-level argument -/

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Termwise extension of scalars of cochain complexes. -/
private noncomputable abbrev extC (φ : R →+* A) :
    CochainComplex (ModuleCat.{max v u} R) ℤ ⥤ CochainComplex (ModuleCat.{max v u} A) ℤ :=
  (ModuleCat.extendScalars.{u, u, max v u} φ).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Termwise additive isomorphisms commuting with differentials transfer exactness. -/
private lemma exactAt_of_addEquiv {R₁ R₂ : Type*} [Ring R₁] [Ring R₂]
    {K : CochainComplex (ModuleCat.{v} R₁) ℤ} {L : CochainComplex (ModuleCat.{u} R₂) ℤ}
    (e : ∀ n, K.X n ≃+ L.X n) (he : ∀ n m (x : K.X n), e m (K.d n m x) = L.d n m (e n x))
    (i : ℤ) (hL : L.ExactAt i) : K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff' K (i - 1) i (i + 1) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  rw [HomologicalComplex.exactAt_iff' L (i - 1) i (i + 1) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hL
  exact (Function.Exact.iff_of_ladder_addEquiv (e (i - 1)) (e i) (e (i + 1))
    (f₁₂ := (K.d (i - 1) i).hom.toAddMonoidHom) (f₂₃ := (K.d i (i + 1)).hom.toAddMonoidHom)
    (g₁₂ := (L.d (i - 1) i).hom.toAddMonoidHom) (g₂₃ := (L.d i (i + 1)).hom.toAddMonoidHom)
    (AddMonoidHom.ext fun x => (he _ _ x).symm) (AddMonoidHom.ext fun x => (he _ _ x).symm)).1 hL

private noncomputable def baseChangeTensorEquiv (φ : R →+* A)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (N : ModuleCat.{max v u} R) (n : ℤ) :
    ((extC φ).obj (tensorCx P N)).X n ≃+
    (tensorCx ((extC φ).obj P) ((ModuleCat.extendScalars φ).obj N)).X n :=
  letI := φ.toAlgebra
  (TensorProduct.AlgebraTensorModule.distribBaseChange R A (P.X n) N).toAddEquiv

private lemma baseChangeTensorEquiv_d (φ : R →+* A)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (N : ModuleCat.{max v u} R) (n m : ℤ) (x) :
    baseChangeTensorEquiv φ P N m (((extC φ).obj (tensorCx P N)).d n m x) =
      (tensorCx ((extC φ).obj P) ((ModuleCat.extendScalars φ).obj N)).d n m
        (baseChangeTensorEquiv φ P N n x) := by
  let := φ.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
  | tmul a y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add] at *; rw [hx, hy]
    | tmul p q => rfl

/-- For an `A`-module `N` whose `R`-module structure is restricted along `φ`,
`P ⊗_R N ≅ (A ⊗_R P) ⊗_A N` termwise. -/
private noncomputable def restrictTensorEquiv (φ : R →+* A)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (N : Type (max v u)) [AddCommGroup N]
    [Module R N] [Module A N] (hN : ∀ (r : R) (x : N), φ r • x = r • x) (n : ℤ) :
    (tensorCx P (ModuleCat.of R N)).X n ≃+
    (tensorCx ((extC φ).obj P) (ModuleCat.of A N)).X n :=
  letI := φ.toAlgebra
  haveI : IsScalarTower R A N := ⟨fun r a x => by
    change (φ r * a) • x = r • (a • x); rw [mul_smul, hN]⟩
  ((TensorProduct.comm R (P.X n) N).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R A A N (P.X n)).symm.restrictScalars R)
    |>.trans ((TensorProduct.comm A N (TensorProduct R A (P.X n))).restrictScalars R)).toAddEquiv

private lemma restrictTensorEquiv_d (φ : R →+* A)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) (N : Type (max v u)) [AddCommGroup N]
    [Module R N] [Module A N] (hN : ∀ (r : R) (x : N), φ r • x = r • x) (n m : ℤ) (x) :
    restrictTensorEquiv φ P N hN m
        ((tensorCx P (ModuleCat.of R N)).d n m x) =
      (tensorCx ((extC φ).obj P) (ModuleCat.of A N)).d n m
        (restrictTensorEquiv φ P N hN n x) := by
  let := φ.toAlgebra
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
  | tmul p q => rfl

/-- Termwise extension of a strictly `≤ 0` complex of projectives, if its image in the derived
category is a flat module in degree `0`, has termwise Tor amplitude in `[0, 0]`. -/
private lemma hasTorAmplitudeIn_extC (φ : R →+* A)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) [P.IsStrictlyLE 0]
    (hproj : ∀ n, Projective (P.X n)) (F : ModuleCat.{max v u} A) (hF : Module.Flat A F)
    (e : DerivedCategory.Q.obj ((extC φ).obj P) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj F) :
    HasTorAmplitudeIn ((extC φ).obj P) 0 0 := by
  let E := (HomologicalComplex.single (ModuleCat.{max v u} A) (ComplexShape.up ℤ) 0).obj F
  have hbd : BoundedAbove ((extC φ).obj P) :=
    ⟨0, fun n hn => (ModuleCat.extendScalars.{u, u, max v u} φ).map_isZero
      (CochainComplex.isZero_of_isStrictlyLE P 0 n hn)⟩
  have hflat : ∀ n : ℤ, Module.Flat A (((extC φ).obj P).X n) := fun n =>
    @Module.Flat.of_projective _ _ _ _ _ ((IsProjective.iff_projective
      ((ModuleCat.extendScalars φ).obj (P.X n))).2
        ((ModuleCat.extendRestrictScalarsAdj φ).map_projective _ (hproj n)))
  have hEbd : BoundedAbove E :=
    ⟨0, fun n hn => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n (by omega)⟩
  have hEflat : ∀ n : ℤ, Module.Flat A (E.X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hF
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).toLinearEquiv.symm
    · have := ModuleCat.isZero_iff_subsingleton.1
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn)
      have := Module.Free.of_subsingleton A (E.X n)
      exact Module.Flat.of_free
  intro N i hi
  refine termwise_isZero_homology_of_flat_rep _ E hbd hflat hEbd hEflat
    (e ≪≫ (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{max v u} A) 0).app F) N i ?_
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ((tensorModuleRight N).map_isZero ?_)
  exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i
    (by rcases hi with hi | hi <;> omega)

/-- The map `P ⊗ N₁ ⟶ P ⊗ N₂` of termwise tensor complexes induced by `g : N₁ ⟶ N₂`. -/
private noncomputable def tensorMap (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    {N₁ N₂ : ModuleCat.{max v u} R} (g : N₁ ⟶ N₂) :
    tensorCx P N₁ ⟶ tensorCx P N₂ where
  f n := ModuleCat.ofHom (g.hom.lTensor (P.X n))
  comm' i j _ := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add] at *; rw [hx, hy]
    | tmul p q => rfl

private lemma tensorMap_f_apply (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    {N₁ N₂ : ModuleCat.{max v u} R} (g : N₁ ⟶ N₂) (n : ℤ) (x) :
    (tensorMap P g).f n x = g.hom.lTensor (P.X n) x := rfl

private lemma tensorMap_comp (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    {N₁ N₂ N₃ : ModuleCat.{max v u} R} (g : N₁ ⟶ N₂) (h : N₂ ⟶ N₃) :
    tensorMap P (g ≫ h) = tensorMap P g ≫ tensorMap P h := by
  ext n : 2
  simp [tensorMap, LinearMap.lTensor_comp]

private lemma tensorMap_smul_id (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (N : ModuleCat.{max v u} R) (r : R) :
    tensorMap P (r • 𝟙 N) = r • 𝟙 _ := by
  ext n : 2
  simp [tensorMap, LinearMap.lTensor_smul]

/-- Tensoring a short exact sequence of modules with a termwise flat complex. -/
private lemma tensorMap_shortExact (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hflat : ∀ n, Module.Flat R (P.X n)) (S : ShortComplex (ModuleCat.{max v u} R))
    (hS : S.ShortExact) :
    (ShortComplex.mk (tensorMap P S.f) (tensorMap P S.g)
      (by rw [← tensorMap_comp, S.zero]; ext n : 2;
          simp [tensorMap])).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hex : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  have hsurj : Function.Surjective S.g.hom := hS.moduleCat_surjective_g
  exact ModuleCat.shortComplex_shortExact _ (lTensor_exact (P.X n) hex hsurj)
    (@Module.Flat.lTensor_preserves_injective_linearMap _ _ _ _ _ _ _ _ _ _ _ (hflat n) _
      hS.moduleCat_injective_f)
    (LinearMap.lTensor_surjective _ hsurj)

private lemma homologyMap_smul_id (K : CochainComplex (ModuleCat.{max v u} R) ℤ) (r : R) (i : ℤ) :
    HomologicalComplex.homologyMap (r • 𝟙 K) i = r • 𝟙 _ := by
  show ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{max v u} R) (ComplexShape.up ℤ) i).map
      (r • 𝟙 K)) = _
  rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat.{max v u} R)
    (ComplexShape.up ℤ) i).map (r • 𝟙 K) = r •
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{max v u} R)
        (ComplexShape.up ℤ) i).map (𝟙 K) by rfl, ShortComplex.homologyMap_smul]
  show r • HomologicalComplex.homologyMap (𝟙 K) i = _
  rw [HomologicalComplex.homologyMap_id]

/-- **Cone step.** If the negative homology of `P ⊗ N'` vanishes for every module `N'`
annihilated by `f`, then multiplication by `f` is injective on `Hⁱ(P ⊗ N)` for `i < 0`. -/
private lemma smul_injective_homology (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hflat : ∀ n, Module.Flat R (P.X n)) (f : R)
    (hann : ∀ (N' : Type (max v u)) [AddCommGroup N'] [Module R N'], (∀ x : N', f • x = 0) →
      ∀ j : ℤ, j < 0 → IsZero ((tensorCx P (ModuleCat.of R N')).homology j))
    (N : ModuleCat.{max v u} R) (i : ℤ) (hi : i < 0) :
    Function.Injective (fun x : (tensorCx P N).homology i => f • x) := by
  let μ : N →ₗ[R] N := f • LinearMap.id
  let S₁ : ShortComplex (ModuleCat.{max v u} R) :=
    ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker μ).subtype)
      (ModuleCat.ofHom μ.rangeRestrict) (by
        ext x
        exact LinearMap.mem_ker.1 x.2)
  let S₂ : ShortComplex (ModuleCat.{max v u} R) :=
    ShortComplex.mk (ModuleCat.ofHom (LinearMap.range μ).subtype)
      (ModuleCat.ofHom (LinearMap.range μ).mkQ) (by
        ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.2)
  have hS₁ : S₁.ShortExact :=
    ModuleCat.shortComplex_shortExact _
      (fun y => ⟨fun hy => ⟨⟨y, congrArg Subtype.val hy⟩, rfl⟩,
        by rintro ⟨z, rfl⟩; exact Subtype.ext (LinearMap.mem_ker.1 z.2)⟩)
      Subtype.val_injective (LinearMap.surjective_rangeRestrict μ)
  have hS₂ : S₂.ShortExact :=
    ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ _)
      Subtype.val_injective (Submodule.mkQ_surjective _)
  have h₁ := tensorMap_shortExact P hflat S₁ hS₁
  have h₂ := tensorMap_shortExact P hflat S₂ hS₂
  have hK : IsZero ((tensorCx P S₁.X₁).homology i) :=
    hann (LinearMap.ker μ) (fun x => Subtype.ext (LinearMap.mem_ker.1 x.2)) i hi
  have hQ : IsZero ((tensorCx P S₂.X₃).homology (i - 1)) := by
    refine hann (N ⧸ LinearMap.range μ) (fun x => ?_) (i - 1) (by omega)
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
  have hm₁ : Mono (HomologicalComplex.homologyMap (tensorMap P S₁.g) i) :=
    (h₁.homology_exact₂ i).mono_g (hK.eq_of_src _ _)
  have hm₂ : Mono (HomologicalComplex.homologyMap (tensorMap P S₂.f) i) :=
    (h₂.homology_exact₁ (i - 1) i (by simp)).mono_g (hQ.eq_of_src _ _)
  have hcomp : S₁.g ≫ S₂.f = f • 𝟙 N := by ext; rfl
  have hmap : HomologicalComplex.homologyMap (tensorMap P S₁.g) i ≫
      HomologicalComplex.homologyMap (tensorMap P S₂.f) i = f • 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← tensorMap_comp, hcomp, tensorMap_smul_id,
      homologyMap_smul_id]
  have hmono : Mono (f • 𝟙 ((tensorCx P N).homology i)) := by
    rw [← hmap]; infer_instance
  exact (ModuleCat.mono_iff_injective _).1 hmono

/-- **Localization step.** If termwise extension of `P` to `R_f` has Tor amplitude in `[0, 0]`,
then every class in negative homology of `P ⊗ N` is killed by a power of `f`. -/
private lemma exists_pow_smul_eq_zero_homology (f : R)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (htor : HasTorAmplitudeIn ((extC (algebraMap R (Localization.Away f))).obj P) 0 0)
    (N : ModuleCat.{max v u} R) (i : ℤ) (hi : i < 0)
    (x : (tensorCx P N).homology i) : ∃ n : ℕ, f ^ n • x = 0 := by
  let φ := algebraMap R (Localization.Away f)
  let C := tensorCx P N
  have hex : ((extC φ).obj C).ExactAt i :=
    exactAt_of_addEquiv (baseChangeTensorEquiv φ P N) (baseChangeTensorEquiv_d φ P N) i
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (htor _ i (Or.inl hi)))
  have : (CochainComplex.DerivedTensor.extensionScalars.{u, u, v} φ).PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology φ
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers f)))
  have hz : IsZero ((ModuleCat.extendScalars φ).obj (C.homology i)) :=
    hex.isZero_homology.of_iso ((C.sc i).mapHomologyIso (ModuleCat.extendScalars φ)).symm
  have hz' : IsZero (ModuleCat.of R (LocalizedModule (Submonoid.powers f) (C.homology i))) :=
    ((ModuleCat.restrictScalars φ).map_isZero hz).of_iso
      (CochainComplex.DerivedTensor.extensionScalarsLocalizedModuleIso
        (Submonoid.powers f) _).symm
  let q := LocalizedModule.mkLinearMap (Submonoid.powers f) (C.homology i)
  have : Subsingleton (LocalizedModule (Submonoid.powers f) (C.homology i)) :=
    ModuleCat.isZero_iff_subsingleton.mp hz'
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := q) f (x := x) (y := 0)
    (Subsingleton.elim _ _)
  exact ⟨n, by rw [hn, smul_zero]⟩

/-- **Quotient step.** If termwise extension of `P` to `R / fR` has Tor amplitude in `[0, 0]`,
then `P ⊗ N'` has no negative homology for every module `N'` annihilated by `f`. -/
private lemma homology_isZero_of_smul_eq_zero (f : R)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (htor : HasTorAmplitudeIn ((extC (Ideal.Quotient.mk (Ideal.span {f}))).obj P) 0 0)
    (N' : Type (max v u)) [AddCommGroup N'] [Module R N'] (hN : ∀ x : N', f • x = 0)
    (j : ℤ) (hj : j < 0) :
    IsZero ((tensorCx P (ModuleCat.of R N')).homology j) := by
  have ht : Module.IsTorsionBySet R N' (Ideal.span {f}) :=
    (Module.isTorsionBySet_span_singleton_iff f).2 hN
  let : Module (R ⧸ Ideal.span {f}) N' := ht.module
  exact (exactAt_of_addEquiv
    (restrictTensorEquiv (Ideal.Quotient.mk (Ideal.span {f})) P N' ht.mk_smul)
    (restrictTensorEquiv_d (Ideal.Quotient.mk (Ideal.span {f})) P N' ht.mk_smul) j
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (htor (ModuleCat.of _ N') j (Or.inl hj)))).isZero_homology

/-- **Tag 0H84 at the chain level.** Under the localization and quotient hypotheses,
`P` has termwise Tor amplitude in `[0, 0]`. -/
private lemma hasTorAmplitudeIn_zero (f : R)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) [P.IsStrictlyLE 0]
    (hflat : ∀ n, Module.Flat R (P.X n))
    (hloc : HasTorAmplitudeIn ((extC (algebraMap R (Localization.Away f))).obj P) 0 0)
    (hquot : HasTorAmplitudeIn ((extC (Ideal.Quotient.mk (Ideal.span {f}))).obj P) 0 0) :
    HasTorAmplitudeIn P 0 0 := by
  intro N i hi
  rcases hi with hi | hi
  · rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun x y => ?_⟩
    have hinj := smul_injective_homology P hflat f
      (homology_isZero_of_smul_eq_zero f P hquot) N i hi
    have hp : ∀ (n : ℕ) (z : (tensorCx P N).homology i),
        f ^ n • z = 0 → z = 0 := by
      intro n
      induction n with
      | zero => intro z hz; rwa [pow_zero, one_smul] at hz
      | succ n ih =>
        intro z hz
        apply ih
        apply hinj
        show f • f ^ n • z = f • 0
        rw [smul_zero, ← mul_smul, ← pow_succ']
        exact hz
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_homology f P hloc N i hi (x - y)
    exact sub_eq_zero.1 (hp n _ hn)
  · exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((tensorModuleRight N).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE P 0 i hi))

/-- For a strictly `≤ 0` complex of projectives `P`, a flat module in degree `0` isomorphic to
the derived extension of scalars of `P` gives termwise Tor amplitude `[0, 0]` of the
termwise extension of `P`. -/
private lemma hasTorAmplitudeIn_extC_of_total {A : Type u} [CommRing A] (φ : R →+* A)
    (P : CochainComplex (ModuleCat.{max v u} R) ℤ) [P.IsStrictlyLE 0]
    [hproj : ∀ n, Projective (P.X n)]
    (h : ∃ F : ModuleCat.{max v u} A, Module.Flat A F ∧
      Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        φ).functor.obj (DerivedCategory.Q.obj P) ≅
          (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj F)) :
    HasTorAmplitudeIn ((extC φ).obj P) 0 0 := by
  obtain ⟨F, hF, ⟨e⟩⟩ := h
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} φ
  have := D.comparison_isIso_of_projective P 0
  exact hasTorAmplitudeIn_extC φ P hproj F hF ((asIso (D.comparison.app P)).symm ≪≫ e)

/-! ### Tag 0H85 -/

/-- Let `M ∈ D(R)` have no positive cohomology. If its derived base changes to the
localization `R_f` and the quotient `R / fR` are each isomorphic to a flat module placed in
degree zero, then `M` is isomorphic to a flat `R`-module placed in degree zero. -/
@[stacks 0H85]
public theorem isomorphic_to_flat_module_of_localization_and_quotient
    {R : Type u} [CommRing R] (f : R)
    (M : DerivedCategory (ModuleCat.{max v u} R))
    (hM : ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj M))
    (hAway : ∃ F : ModuleCat.{max v u} (Localization.Away f),
      Module.Flat (Localization.Away f) F ∧
        Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (algebraMap R (Localization.Away f))).functor.obj M ≅
            (DerivedCategory.singleFunctor
              (ModuleCat.{max v u} (Localization.Away f)) 0).obj F))
    (hQuot : ∃ F : ModuleCat.{max v u} (R ⧸ Ideal.span {f}),
      Module.Flat (R ⧸ Ideal.span {f}) F ∧
        Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
          (Ideal.Quotient.mk (Ideal.span {f}))).functor.obj M ≅
            (DerivedCategory.singleFunctor
              (ModuleCat.{max v u} (R ⧸ Ideal.span {f})) 0).obj F)) :
    ∃ F : ModuleCat.{max v u} R, Module.Flat R F ∧
      Nonempty (M ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj F) := by
  have hLE : M.IsLE 0 := (DerivedCategory.isLE_iff M 0).2 hM
  obtain ⟨K, hK, ⟨eK⟩⟩ := M.exists_iso_Q_obj_of_isLE 0
  obtain ⟨Pr, -⟩ := ProjectiveResolutionLemma.statement3 0 K hK
  let P := Pr.complex
  have : P.IsStrictlyLE 0 := Pr.boundedAbove
  have hproj : ∀ n, Projective (P.X n) := Pr.projective
  have : QuasiIso Pr.α := Pr.quasiIso
  let eP : M ≅ DerivedCategory.Q.obj P := eK ≪≫ (asIso (DerivedCategory.Q.map Pr.α)).symm
  have hflat : ∀ n, Module.Flat R (P.X n) := fun n =>
    @Module.Flat.of_projective _ _ _ _ _ ((IsProjective.iff_projective _).2 (hproj n))
  have htrans {A : Type u} [CommRing A] (φ : R →+* A)
      (h : ∃ F : ModuleCat.{max v u} A, Module.Flat A F ∧
        Nonempty ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          φ).functor.obj M ≅
          (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj F)) :
      HasTorAmplitudeIn ((extC φ).obj P) 0 0 := by
    obtain ⟨F, hF, ⟨e⟩⟩ := h
    exact hasTorAmplitudeIn_extC_of_total φ P ⟨F, hF, ⟨
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        φ).functor.mapIso eP).symm ≪≫ e⟩⟩
  have htor := hasTorAmplitudeIn_zero f P hflat (htrans _ hAway) (htrans _ hQuot)
  have hcok : Module.Flat R (cokernel (P.d (0 - 1) 0) : ModuleCat.{max v u} R) :=
    cokernel_flat_of_termwise_isZero_homology P 0 0 hflat htor
  have hP : ∀ i : ℤ, i < 0 → P.ExactAt i := by
    intro i hi
    let U := ModuleCat.of R (ULift.{max v u} R)
    let e : ∀ n, P.X n ≃+ (tensorCx P U).X n := fun n =>
      ((TensorProduct.congr (LinearEquiv.refl R (P.X n)) ULift.moduleEquiv).trans
        (TensorProduct.rid R (P.X n))).symm.toAddEquiv
    exact exactAt_of_addEquiv e (fun _ _ _ => rfl) i
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (htor U i (Or.inl hi)))
  have hGE : (DerivedCategory.Q.obj P).IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact ((hP i hi).isZero_homology).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} R) i).app P)
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj P) 0
  let eH : Y ≅ cokernel (P.d (0 - 1) 0) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max v u} R) 0).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) 0).mapIso eY.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max v u} R) 0).app P ≪≫
      P.isoHomologyι 0 1 (by simp)
        ((CochainComplex.isZero_of_isStrictlyLE P 0 1 (by omega)).eq_of_tgt _ _) ≪≫
      IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (0 - 1) 0 (by simp))
        (colimit.isColimit _)
  exact ⟨Y, @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hcok eH.toLinearEquiv, ⟨eP ≪≫ eY⟩⟩

end Stacks.Flatness.LocalizationReduction

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibre.ProperOverDvr
public import StacksFrontier.RingTheory.Flat.Finiteness
public import StacksFrontier.RingTheory.Valuation.Constructions

/-!
# Reducedness of a proper flat scheme over a valuation ring

Let `R` be a valuation ring and let `f : X ⟶ Spec R` be proper and flat. If the special fibre of
`f` is reduced, then `X` and every fibre of `f` are reduced.

## Main results

* `isReduced_and_isReduced_fiber_of_isProper_over_valuationRing`: `X` and every fibre of `f` are
  reduced.
* `isReduced_of_isProper_over_valuationRing_of_isReduced_specialFiber`: the total space is
  reduced.
* `isReduced_fiber_of_isProper_over_valuationRing_of_isReduced_specialFiber`: every fibre is
  reduced.

## References

* [Stacks Project, Tag 0H2T](https://stacks.math.columbia.edu/tag/0H2T)
* [Stacks Project, Tag 0GSE](https://stacks.math.columbia.edu/tag/0GSE)
* [Stacks Project, Tag 053E](https://stacks.math.columbia.edu/tag/053E)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

attribute [local instance 2000] CategoryTheory.CategoryStruct.toQuiver

/-- Over a valuation ring `R`, every element of `I · B` is of the form `π b` with `π ∈ I`. -/
private theorem exists_mem_mul_of_mem_map_of_valuationRing
    {R B : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) {a : B} (ha : a ∈ I.map (algebraMap R B)) :
    ∃ π ∈ I, ∃ b : B, a = algebraMap R B π * b := by
  have : Nonempty I := ⟨⟨0, I.zero_mem⟩⟩
  let F : I → Ideal B := fun π => Ideal.span {algebraMap R B (π : R)}
  have hle (π₁ π₂ : I) (h : (π₁ : R) ∣ π₂) : F π₂ ≤ F π₁ :=
    Ideal.span_singleton_le_span_singleton.2 (map_dvd _ h)
  have hdir : Directed (· ≤ ·) F := fun π₁ π₂ =>
    (ValuationRing.dvd_total (π₁ : R) π₂).elim (fun h => ⟨π₁, le_rfl, hle _ _ h⟩)
      fun h => ⟨π₂, hle _ _ h, le_rfl⟩
  have hsup : I.map (algebraMap R B) = ⨆ π, F π := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun x hx => ?_) (iSup_le fun π => ?_)
    · exact Ideal.mem_comap.2 (le_iSup F ⟨x, hx⟩ (Ideal.mem_span_singleton_self _))
    · exact Ideal.span_le.2 (by rintro y (rfl : y = _); exact Ideal.mem_map_of_mem _ π.2)
  rw [hsup] at ha
  obtain ⟨π, hπ⟩ := (Submodule.mem_iSup_of_directed F hdir).1 ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hπ
  exact ⟨(π : R), π.2, b, by rw [← hb, mul_comm]⟩

/-- The quotient of a torsion free algebra over a valuation ring by its nilradical is torsion
free. -/
private instance isTorsionFree_quotient_nilradical
    {R B : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [CommRing B] [Algebra R B]
    [Module.IsTorsionFree R B] :
    Module.IsTorsionFree R (B ⧸ nilradical B) := by
  refine ⟨fun r hr x y hxy => ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmk : ∀ d : B, r • (Ideal.Quotient.mk (nilradical B) d) =
      Ideal.Quotient.mk (nilradical B) (r • d) := by
    intro d
    rw [Algebra.smul_def, Algebra.smul_def, ← Ideal.Quotient.algebraMap_eq, map_mul]
    rfl
  replace hxy : r • (Ideal.Quotient.mk (nilradical B) b) =
      r • (Ideal.Quotient.mk (nilradical B) c) := hxy
  rw [hmk, hmk, Ideal.Quotient.eq] at hxy
  obtain ⟨k, hk⟩ := mem_nilradical.1 hxy
  rw [← smul_sub, smul_pow] at hk
  refine Ideal.Quotient.eq.2 (mem_nilradical.2 ⟨k, (hr.pow k).isSMulRegular ?_⟩)
  change r ^ k • (b - c) ^ k = r ^ k • (0 : B)
  rw [hk, smul_zero]

/-- Let `R` be a valuation ring and let `B` be a local `R`-algebra which is essentially of finite
type, flat, and whose structure map is local. If `B / 𝔪_R B` is reduced then `B` is reduced. -/
private theorem isReduced_of_isReduced_quotient_map_maximalIdeal
    {R B : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Algebra.EssFiniteType R B] [Module.Flat R B]
    (hred : IsReduced (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B))) :
    IsReduced B := by
  have : Module.IsTorsionFree R B := Module.Flat.isTorsionFree
  have : Module.Flat R (B ⧸ nilradical B) := Module.Flat.of_isTorsionFree_of_valuationRing
  have : Module.Finite B (B ⧸ nilradical B) :=
    Module.Finite.of_surjective (nilradical B).mkQ (Submodule.mkQ_surjective _)
  have : Module.FinitePresentation B (B ⧸ nilradical B) :=
    (essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
      (A := R) (B := B) (M := B ⧸ nilradical B)).2 inferInstance inferInstance
  have hfg : (nilradical B).FG := by
    have := Module.FinitePresentation.fg_ker (nilradical B).mkQ (Submodule.mkQ_surjective _)
    rwa [Submodule.ker_mkQ] at this
  have hsmul : (nilradical B) ≤ (IsLocalRing.maximalIdeal B) • (nilradical B) := by
    intro a ha
    obtain ⟨n, hn⟩ : IsNilpotent a := by obtain ⟨n, hn⟩ := ha; exact ⟨n, by simpa using hn⟩
    have hmem : a ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R B) := by
      have : IsNilpotent (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal R).map (algebraMap R B)) a) := ⟨n, by rw [← map_pow, hn]; simp⟩
      exact Ideal.Quotient.eq_zero_iff_mem.1 (hred.eq_zero _ this)
    obtain ⟨π, hπI, b, hb⟩ := exists_mem_mul_of_mem_map_of_valuationRing _ hmem
    rcases eq_or_ne π 0 with rfl | hπ0
    · simp only [map_zero, zero_mul] at hb
      exact hb ▸ Submodule.zero_mem _
    · have hreg : IsSMulRegular B (π ^ n) :=
        ((isRegular_iff_ne_zero (a := π ^ n)).2 (pow_ne_zero n hπ0)).isSMulRegular
      have hbnil : b ∈ nilradical B := by
        refine ⟨n, ?_⟩
        refine (show b ^ n = 0 from hreg ?_) ▸ Submodule.zero_mem _
        show π ^ n • b ^ n = π ^ n • (0 : B)
        rw [smul_zero, Algebra.smul_def, map_pow, ← mul_pow, ← hb, hn]
      have hπB : algebraMap R B π ∈ IsLocalRing.maximalIdeal B := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact ((IsLocalRing.mem_maximalIdeal π).1 hπI) (isUnit_of_map_unit _ _ hu)
      rw [hb]
      exact Submodule.mul_mem_mul hπB hbnil
  have hbot : nilradical B = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg hsmul
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  exact ⟨fun a ha => Ideal.mem_bot.1 (hbot ▸ mem_nilradical.2 ha)⟩

private theorem exists_specializes_closedPoint_of_closedMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (x : X) (hf : IsClosedMap f) :
    ∃ y : X, f y = IsLocalRing.closedPoint (CommRingCat.of R) ∧ x ⤳ y := by
  obtain ⟨y, hyC, hyf⟩ := (IsLocalRing.specializes_closedPoint (f x)).mem_closed
    (hf _ isClosed_closure) ⟨x, subset_closure (Set.mem_singleton x), rfl⟩
  exact ⟨y, hyf, specializes_iff_mem_closure.mpr hyC⟩

private theorem isReduced_tensorProduct_localization
    {R S : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [IsReduced A] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] :
    IsReduced (TensorProduct R S A) := by
  let B := TensorProduct R R A
  let T := TensorProduct R S A
  let : Algebra B T :=
    (Algebra.TensorProduct.map (Algebra.ofId R S) (AlgHom.id R A)).toRingHom.toAlgebra
  let : IsScalarTower R B T := .of_algebraMap_eq' (R := R) (S := B) (A := T) (by
    ext r
    show (algebraMap R S r) ⊗ₜ[R] (1 : A) =
      (Algebra.TensorProduct.map (Algebra.ofId R S) (AlgHom.id R A))
        ((algebraMap R R r) ⊗ₜ[R] (1 : A))
    rw [Algebra.TensorProduct.map_tmul]
    simp)
  have hcomp : (algebraMap B T).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom := by
    ext a
    show (Algebra.TensorProduct.map (Algebra.ofId R S) (AlgHom.id R A))
      (1 ⊗ₜ[R] a) = 1 ⊗ₜ[R] a
    rw [Algebra.TensorProduct.map_tmul]
    simp
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B M) T :=
    IsLocalization.tensorProduct_tensorProduct R A M S hcomp
  let : IsReduced B := by
    let e : B ≃ₐ[R] A := Algebra.TensorProduct.lid R A
    exact isReduced_of_injective e.toRingHom e.injective
  let : IsLocalization (Algebra.algebraMapSubmonoid B M) T := hloc
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B M) T inferInstance

/-- The fibre of `Spec φ` at `y` is reduced iff the tensor product `κ(y) ⊗ A` is. -/
private theorem isReduced_fiber_spec_map_iff {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (y : PrimeSpectrum R) :
    IsReduced ((Spec.map (CommRingCat.ofHom (algebraMap R A))).fiber (y : Spec (.of R))) ↔
      IsReduced (y.asIdeal.Fiber A) := by
  rw [← affine_isReduced_iff (.of (y.asIdeal.Fiber A))]
  let e := Spec.fiberToSpecResidueFieldIso R A y
  exact ⟨fun h => @isReduced_of_isOpenImmersion _ _ e.inv.left _ h,
    fun h => @isReduced_of_isOpenImmersion _ _ e.hom.left _ h⟩

private theorem isReduced_genericFiber_of_isReduced
    {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsReduced X] :
    IsReduced (f.fiber (⟨⊥, inferInstance⟩ : Spec (.of R))) := by
  let η : Spec (.of R) := ⟨⊥, inferInstance⟩
  let K := η.asIdeal.ResidueField
  let : Algebra R K :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime η.asIdeal)
  have : IsFractionRing R K := by
    show IsFractionRing R ((⊥ : Ideal R).ResidueField)
    infer_instance
  let 𝒰 := X.affineOpenCover.openCover.pullback₁ (f.fiberι η)
  let : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
    intro i
    let A := ↑(X.affineOpenCover.X i)
    let U := Spec (.of A)
    let u := X.affineOpenCover.f i
    have : IsOpenImmersion u := X.affineOpenCover.map_prop i
    let φ : R →+* A := (Spec.preimage (u ≫ f)).hom
    have he : u ≫ f = Spec.map (CommRingCat.ofHom φ) := by
      simp [φ]
    let : Algebra R A := RingHom.toAlgebra φ
    have hredA : IsReduced A := by
      have : IsReduced U := isReduced_of_isOpenImmersion u
      exact (affine_isReduced_iff (.of A)).mp ‹IsReduced U›
    have hredT : IsReduced (η.asIdeal.Fiber A) := by
      simpa [η, Ideal.Fiber] using
        (isReduced_tensorProduct_localization (R := R) (A := A) (S := K) (nonZeroDivisors R))
    have : IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber η) :=
      (isReduced_fiber_spec_map_iff (R := R) (A := A) η).2 hredT
    let e1 : 𝒰.X i ≅ pullback (u ≫ f) ((Spec (.of R)).fromSpecResidueField η) :=
      pullbackSymmetry _ _ ≪≫
        pullbackRightPullbackFstIso f ((Spec (.of R)).fromSpecResidueField η) u
    let e2 : pullback (u ≫ f) ((Spec (.of R)).fromSpecResidueField η) ≅
        pullback (Spec.map (CommRingCat.ofHom φ)) ((Spec (.of R)).fromSpecResidueField η) :=
      pullback.congrHom he rfl
    let eC : 𝒰.X i ≅ (Spec.map (CommRingCat.ofHom φ)).fiber η := e1 ≪≫ e2
    exact isReduced_of_isOpenImmersion eC.hom
  exact IsReduced.of_openCover (f.fiber η) 𝒰

private noncomputable def fiberIsoFiberOfIsPullback
    {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y)
    [IsIso (g.residueFieldMap y)] : snd.fiber y ≅ f.fiber (g y) := by
  have hfiber := isPullback_fiberToSpecResidueField_of_isPullback h y
  have : IsIso (Spec.map (g.residueFieldMap y)) := by infer_instance
  let e := pullback.map snd (Y.fromSpecResidueField y) f (Z.fromSpecResidueField (g y))
      fst (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)
  have hIso : IsIso e := by
    dsimp [e]
    exact hfiber.isIso_fst_of_isIso
  exact @CategoryTheory.asIso _ _ _ _ e hIso

private theorem isReduced_quotient_localization_of_isReduced_fiber
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (y : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : PrimeSpectrum.comap φ q = y)
    [IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber (y : Spec (.of R)))] :
    IsReduced (Localization.AtPrime q.asIdeal ⧸
      Ideal.map (algebraMap A (Localization.AtPrime q.asIdeal))
        (Ideal.map φ y.asIdeal)) := by
  let : Algebra R A := RingHom.toAlgebra φ
  have hq' : PrimeSpectrum.comap (algebraMap R A) q = y := hq
  let α := PrimeSpectrum.preimageEquivFiber R A y
  let qbar : PrimeSpectrum (y.asIdeal.Fiber A) := α ⟨q, hq'⟩
  have hunder : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal =
      q.asIdeal := by
    show (α.invFun qbar).1.asIdeal = q.asIdeal
    simpa [qbar, α, PrimeSpectrum.preimageEquivFiber] using
      congrArg (fun z : {r // PrimeSpectrum.comap (algebraMap R A) r = y} => z.1.asIdeal)
        (α.left_inv ⟨q, hq'⟩)
  have : IsReduced (y.asIdeal.Fiber A) := (isReduced_fiber_spec_map_iff (R := R) (A := A) y).1 ‹_›
  have : IsReduced (Localization.AtPrime qbar.asIdeal) :=
    isReduced_localizationPreserves qbar.asIdeal.primeCompl
      (Localization.AtPrime qbar.asIdeal) inferInstance
  let eFiber := Ideal.Fiber.algEquivAux₂ y.asIdeal qbar.asIdeal
  let r : Ideal A := Ideal.comap Algebra.TensorProduct.includeRight.toRingHom qbar.asIdeal
  let Sr := Localization.AtPrime r
  let : Algebra A Sr := inferInstance
  let : IsScalarTower R A Sr := inferInstance
  let : Algebra R Sr := inferInstance
  let Jbar : Ideal Sr :=
    Ideal.map (algebraMap A Sr) (Ideal.map φ y.asIdeal)
  have hredJbar : IsReduced (Sr ⧸ Jbar) :=
    isReduced_of_injective eFiber.symm.toRingHom eFiber.symm.injective
  let p : PrimeSpectrum A := ⟨r, inferInstance⟩
  have hpq : p = q := PrimeSpectrum.ext hunder
  have hred : IsReduced (Localization.AtPrime p.asIdeal ⧸
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal))
        (Ideal.map φ y.asIdeal)) := hredJbar
  exact hpq ▸ hred

private theorem isReduced_stalk_of_closedFiber
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] [Flat f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] (x : X)
    (hfx : f x = IsLocalRing.closedPoint (CommRingCat.of R)) :
    IsReduced (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let A := Γ(X, U)
  let q := hU.primeIdealOf ⟨x, hxU⟩
  let φ : R →+* A := (Spec.preimage (hU.fromSpec ≫ f)).hom
  have he : hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom φ) := by
    simp [φ]
  have hqx : hU.fromSpec q = x := by
    simpa [q] using hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have heval : f x = (PrimeSpectrum.comap φ q : Spec (.of R)) := by
    have hcomp : f x = (hU.fromSpec ≫ f) q := by rw [← hqx]; rfl
    have hmap : (hU.fromSpec ≫ f) q = (Spec.map (CommRingCat.ofHom φ)) q :=
      congrArg (fun g => g q) he
    exact hcomp.trans (hmap.trans rfl)
  let y : PrimeSpectrum R := f x
  have hq : PrimeSpectrum.comap φ q = y :=
    PrimeSpectrum.ext (congrArg (fun z : Spec (.of R) => z.asIdeal) heval).symm
  have hy : y = IsLocalRing.closedPoint (CommRingCat.of R) :=
    congrArg (fun z : Spec (.of R) => (z : PrimeSpectrum R)) hfx
  have : IsReduced ((Spec.map (CommRingCat.ofHom φ)).fiber (y : Spec (.of R))) := by
    have : IsReduced (f.fiber (y : Spec (.of R))) := by
      rw [hy]
      infer_instance
    exact isReduced_fiber_of_isOpenImmersion_comp hU.fromSpec f
      (Spec.map (CommRingCat.ofHom φ)) he (y : Spec (.of R))
  let : Algebra R A := RingHom.toAlgebra φ
  have hredQuot := isReduced_quotient_localization_of_isReduced_fiber φ y q hq
  let B := Localization.AtPrime q.asIdeal
  let : Algebra A B := inferInstance
  let : IsLocalization.AtPrime B q.asIdeal := Localization.isLocalization
  let : IsScalarTower R A B := inferInstance
  let : Algebra R B := inferInstance
  have hredQuot' : IsReduced (B ⧸
      (IsLocalRing.maximalIdeal R).map (algebraMap R B)) := by
    have hIeq : Ideal.map (algebraMap A B) (Ideal.map φ y.asIdeal) =
        Ideal.map (algebraMap R B) y.asIdeal := by
      have hcomp : (algebraMap A B).comp φ = algebraMap R B := by
        ext r
        rw [IsScalarTower.algebraMap_apply R A B r]
        rfl
      rw [Ideal.map_map, hcomp]
    have hmax : y.asIdeal = IsLocalRing.maximalIdeal R :=
      congrArg (fun z : Spec (.of R) => z.asIdeal) hfx
    rwa [hIeq, hmax] at hredQuot
  have : IsLocalHom (algebraMap R B) := by
    refine ⟨fun a hunit => ?_⟩
    by_contra ha
    have hamax : a ∈ IsLocalRing.maximalIdeal R :=
      (IsLocalRing.mem_maximalIdeal a).2 ha
    have hφq : φ a ∈ q.asIdeal := by
      have hcomap : q.asIdeal.comap φ = y.asIdeal :=
        congrArg PrimeSpectrum.asIdeal hq
      show a ∈ q.asIdeal.comap φ
      rwa [hcomap, hy]
    have hBmax : algebraMap R B a ∈ IsLocalRing.maximalIdeal B := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem (algebraMap A B) hφq
    exact (IsLocalRing.mem_maximalIdeal (algebraMap R B a)).mp hBmax hunit
  have hfinite : RingHom.FiniteType φ := by
    have hLFT : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom φ)) := he ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hLFT
  have hφflat : RingHom.Flat φ := by
    have hFlat : Flat (Spec.map (CommRingCat.ofHom φ)) := he ▸ inferInstance
    exact Flat.SpecMap_iff.mp hFlat
  have : Module.Flat R A := RingHom.flat_algebraMap_iff.mp hφflat
  have : Module.Flat A B := inferInstance
  have : Module.Flat R B := Module.Flat.trans R A B
  have : Algebra.FiniteType R A := hfinite
  have : Algebra.EssFiniteType R A := inferInstance
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.of_isLocalization
    (R := ↑A) (S := B) q.asIdeal.primeCompl
  have : Algebra.EssFiniteType R B := Algebra.EssFiniteType.comp R A B
  have : IsReduced B := isReduced_of_isReduced_quotient_map_maximalIdeal hredQuot'
  let : Algebra A (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) q.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let eX : X.presheaf.stalk x ≃ₐ[A] B :=
    IsLocalization.algEquiv q.asIdeal.primeCompl (X.presheaf.stalk x) B
  exact isReduced_of_injective eX.toRingHom eX.injective

/-- Let `R` be a valuation ring and let `f : X ⟶ Spec R` be proper and flat. If the special
fibre of `f` is reduced then `X` is reduced. -/
public theorem isReduced_of_isProper_over_valuationRing_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))] :
    IsReduced X := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  obtain ⟨x', hx'm, hxx'⟩ := exists_specializes_closedPoint_of_closedMap f x f.isClosedMap
  have : IsReduced (X.presheaf.stalk x') := isReduced_stalk_of_closedFiber f x' hx'm
  exact isReduced_stalk_of_specializes_of_isReduced hxx' inferInstance

/-- Let `R` be a valuation ring and let `f : X ⟶ Spec R` be proper and flat with reduced special
fibre. Then every fibre of `f` is reduced. -/
public theorem isReduced_fiber_of_isProper_over_valuationRing_of_isReduced_specialFiber
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    [IsReduced (f.fiber (IsLocalRing.closedPoint R))]
    (s : Spec (.of R)) :
    IsReduced (f.fiber s) := by
  let p := s.asIdeal
  have : p.IsPrime := s.isPrime
  let R' := R ⧸ p
  let : IsDomain R' := inferInstance
  let : ValuationRing R' := valuationRing_quotient_of_prime p
  let φ : R →+* R' := Ideal.Quotient.mk p
  let : IsLocalHom φ := IsLocalHom.of_surjective φ Ideal.Quotient.mk_surjective
  let j : Spec (.of R') ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom φ)
  have : IsClosedImmersion j :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) Ideal.Quotient.mk_surjective
  have : IsPreimmersion j := inferInstance
  have hres (y : Spec (.of R')) : IsIso (j.residueFieldMap y) :=
    isIso_residueFieldMap_of_isPreimmersion j y
  let y₀ : Spec (.of R') := IsLocalRing.closedPoint (CommRingCat.of R')
  have hj₀ : j y₀ = IsLocalRing.closedPoint (CommRingCat.of R) := by
    show Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint (CommRingCat.of R')) = _
    exact Spec_closedPoint
  let P := pullback f j
  let g : P ⟶ Spec (.of R') := pullback.snd f j
  have hPB : IsPullback (pullback.fst f j) g f j := IsPullback.of_hasPullback f j
  let : IsReduced (g.fiber y₀) := by
    let := hres y₀
    have : IsReduced (f.fiber (j y₀)) := by rw [hj₀]; infer_instance
    exact isReduced_of_isOpenImmersion (fiberIsoFiberOfIsPullback hPB y₀).hom
  let : IsReduced P :=
    isReduced_of_isProper_over_valuationRing_of_isReduced_specialFiber g
  let η₀ : PrimeSpectrum R' := ⟨⊥, inferInstance⟩
  have hη : j η₀ = s := by
    apply PrimeSpectrum.ext
    show Ideal.comap φ η₀.asIdeal = s.asIdeal
    rw [show η₀.asIdeal = (⊥ : Ideal R') by rfl,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have : IsReduced (g.fiber (η₀ : Spec (.of R'))) := isReduced_genericFiber_of_isReduced g
  let := hres (η₀ : Spec (.of R'))
  let e := fiberIsoFiberOfIsPullback hPB (η₀ : Spec (.of R'))
  simpa [hη] using (isReduced_of_isOpenImmersion e.inv :
    IsReduced (f.fiber (j (η₀ : Spec (.of R')))))

/-- Let `f : X ⟶ Spec R` be a proper flat morphism where `R` is a valuation ring. If the special
fibre is reduced, then `X` and every fibre of `X ⟶ Spec R` are reduced. -/
@[stacks 0H2T]
public theorem isReduced_and_isReduced_fiber_of_isProper_over_valuationRing
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
    (hspecial : IsReduced (f.fiber (IsLocalRing.closedPoint R))) :
    IsReduced X ∧ ∀ s : Spec (.of R), IsReduced (f.fiber s) :=
  ⟨isReduced_of_isProper_over_valuationRing_of_isReduced_specialFiber f,
    isReduced_fiber_of_isProper_over_valuationRing_of_isReduced_specialFiber f⟩

end

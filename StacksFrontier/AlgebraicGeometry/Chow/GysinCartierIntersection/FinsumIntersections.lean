module


public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.InvertibleChernSpecialization
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.LocalEquation
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.FrameSections
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Codimension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.KerDetected.RingColimit
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.ChartMembership
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.Stalkwise
import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatAtDivisor

/-!
# Gysin classes of cycles as sums of intersections

Local lengths, the reduced closure of a point, and the Gysin class of a cycle none of whose
components lies in `D` as the class of the sum of its intersections with `D`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

open TopologicalSpace

open scoped TensorProduct

-- The stalk of an ideal sheaf at a point is `AlgebraicGeometry.IdealSheafData.stalk`
-- (StacksFrontier/AlgebraicGeometry/Divisors/FittingIdeals/Basic.lean:63).


universe v w

open CategoryTheory.Limits Opposite

private lemma ker_subscheme_stalkMap_eq_map_ideal
    {X : Scheme.{u}} (D : X.IdealSheafData) (U : X.affineOpens)
    (y : D.subscheme) (hy : D.subschemeι y ∈ U.1) :
    RingHom.ker (D.subschemeι.stalkMap y).hom =
      (D.ideal U).map (X.presheaf.germ U.1 (D.subschemeι y) hy).hom := by
  let V : D.subscheme.affineOpens := ⟨D.subschemeι ⁻¹ᵁ U.1, U.2.preimage D.subschemeι⟩
  let p := U.2.primeIdealOf ⟨D.subschemeι y, hy⟩
  let q := V.2.primeIdealOf ⟨y, hy⟩
  let f := (D.subschemeι.app U.1).hom
  let : Algebra Γ(X, U.1) (X.presheaf.stalk (D.subschemeι y)) :=
    X.presheaf.algebra_section_stalk ⟨D.subschemeι y, hy⟩
  let : Algebra Γ(D.subscheme, V.1) (D.subscheme.presheaf.stalk y) :=
    D.subscheme.presheaf.algebra_section_stalk ⟨y, hy⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk (D.subschemeι y)) p.asIdeal :=
    U.2.isLocalization_stalk ⟨D.subschemeι y, hy⟩
  let : IsLocalization.AtPrime (D.subscheme.presheaf.stalk y) q.asIdeal :=
    V.2.isLocalization_stalk ⟨y, hy⟩
  have hp : q.asIdeal.comap f = p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 V.1 V.2
      (show V.1 ≤ D.subschemeι ⁻¹ᵁ U.1 from le_rfl) (show y ∈ V.1 from hy)
    simpa [Scheme.Hom.appLE, f, p, q, V, Functor.map_id] using congrArg PrimeSpectrum.asIdeal h
  have hcomp : p.asIdeal.primeCompl.map f = q.asIdeal.primeCompl := by
    simpa only [hp] using
      Ideal.map_primeCompl_comap_of_surjective f (D.subschemeι_app_surjective U) q.asIdeal
  have heq := IsLocalization.map_unique (M := p.asIdeal.primeCompl)
    (Q := D.subscheme.presheaf.stalk y) (g := f)
    (hcomp.symm ▸ p.asIdeal.primeCompl.le_comap_map)
    (D.subschemeι.stalkMap y).hom (fun a => D.subschemeι.germ_stalkMap_apply U.1 y hy a)
  rw [← heq, IsLocalization.ker_map _ f hcomp]
  rw [D.ker_subschemeι_app U]
  rfl

/-- Over a Noetherian ring a finite module has only finitely many minimal primes in its support. -/
lemma finite_minimalSupport
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Set.Finite {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q} := by
  apply Set.Finite.of_finite_image (f := fun q : PrimeSpectrum R => q.asIdeal)
  · apply (associatedPrimes.finite R M).subset
    rintro I ⟨q, hq, rfl⟩
    exact Module.mem_associatedPrimes_of_minimal_mem_support hq
  · exact fun _ _ _ _ h => PrimeSpectrum.ext h

private lemma intCast_toNat_finsum_mem
    {ι : Type*} (f : ι → ℕ∞) {S : Set ι} (hS : S.Finite)
    (hfinite : ∀ i ∈ S, f i ≠ ⊤) :
    ((∑ᶠ i ∈ S, f i).toNat : ℤ) =
      ∑ᶠ i ∈ S, ((f i).toNat : ℤ) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum f hS,
    finsum_mem_eq_finite_toFinset_sum (fun i => ((f i).toNat : ℤ)) hS,
    ENat.toNat_sum (by simpa using hfinite)]
  norm_cast

/-- A finite sum of extended naturals whose total is finite may be truncated to `ℤ` termwise. -/
lemma intCast_toNat_finsum_mem_of_sum_ne_top
    {ι : Type*} (f : ι → ℕ∞) {S : Set ι} (hS : S.Finite)
    (hsum : (∑ᶠ i ∈ S, f i) ≠ ⊤) :
    ((∑ᶠ i ∈ S, f i).toNat : ℤ) =
      ∑ᶠ i ∈ S, ((f i).toNat : ℤ) := by
  rw [finsum_mem_eq_finite_toFinset_sum f hS] at hsum
  exact intCast_toNat_finsum_mem f hS fun i hi =>
    ENat.sum_ne_top.mp hsum i (hS.mem_toFinset.mpr hi)

/-- Every point of an open subset of `X` has an affine open neighbourhood contained in it on which
an invertible module is trivial, together with the resulting trivialization of its sections. -/
theorem exists_affine_frame_subset (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (x : X) (V : X.Opens) (hx : x ∈ V) :
    ∃ (U : X.affineOpens)
      (eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
      (e : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1)),
      x ∈ U.1 ∧ U.1 ≤ V := by
  classical
  have hfree :=
    (Stacks.ModuleDescent.isInvertible_iff_isFiniteLocallyFreeOfRank_one X L).mp inferInstance
  obtain ⟨q, hq, hrank⟩ := hfree.exists_isFiniteLocallyFreeOfRankData
  have hxcover : x ∈ ⨆ i, q.X i := by
    rw [(Opens.coversTop_iff X q.X).mp q.coversTop]
    simp
  rw [TopologicalSpace.Opens.mem_iSup] at hxcover
  obtain ⟨i, hxi⟩ := hxcover
  have hxmeet : x ∈ V ⊓ q.X i := ⟨hx, hxi⟩
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWmeet⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxmeet (V ⊓ q.X i).isOpen
  let U : X.affineOpens := ⟨W, hW⟩
  have hWsubset : (U : X.Opens) ≤ V ⊓ q.X i := by
    intro y hy
    exact hWmeet hy
  have hUV : (U : X.Opens) ≤ V := hWsubset.trans inf_le_left
  have hUqi : (U : X.Opens) ≤ q.X i := hWsubset.trans inf_le_right
  let : IsIso (q.generators i).π := hq.isIso i
  let e₁ := (hrank i).some
  let eIndex : (q.generators i).I ≃ PUnit.{u + 1} := e₁.trans (Equiv.equivPUnit _)
  let eFree := (SheafOfModules.freeFunctor
    (R := X.ringCatSheaf.over (q.X i))).mapIso eIndex.toIso
  let eUnit := Limits.coproductUniqueIso
    (fun _ : PUnit.{u + 1} => SheafOfModules.unit (X.ringCatSheaf.over (q.X i)))
  let eV : L.over (q.X i) ≅ SheafOfModules.unit
      (X.ringCatSheaf.over (q.X i)) :=
    (asIso (q.generators i).π).symm ≪≫ eFree ≪≫ eUnit
  let f : (U : X.Opens) ⟶ q.X i := homOfLE hUqi
  let F := SheafOfModules.overMap X.ringCatSheaf f
  let eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1) :=
    ((SheafOfModules.overFunctorMap X.ringCatSheaf f).app L).symm ≪≫
      F.mapIso eV ≪≫ SheafOfModules.overMapUnitIso f
  let z := Opposite.op (Over.mk (𝟙 (U : X.Opens)))
  let eΓ : Γ(L, U) ≃ₗ[Γ(X, U)] Γ(X, U) :=
    ((_root_.SheafOfModules.evaluation (X.ringCatSheaf.over U.1) z).mapIso eU).toLinearEquiv
  exact ⟨U, eU, eΓ, hxW, hUV⟩

/-- At a point of the zero scheme of a global section `s` of an invertible module, the germ of the
frame coordinate of `s` on a trivializing affine open lies in the maximal ideal of the local
ring. -/
lemma frame_coordinate_mem_maximalIdeal
    (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (U : X.affineOpens)
    (eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (x : X) (hxU : x ∈ U.1)
    (hxD : x ∈ (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).support) :
    (X.presheaf.germ U.1 x hxU).hom
      (Stacks.Divisors.frameSections X L eU
        (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤)))) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let D := Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))
  let e := Stacks.Divisors.frameSections X L eU
  let a := e (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤)))
  have hgen : D.ideal U = Ideal.span ({a} : Set Γ(X, U.1)) :=
    Stacks.Divisors.zeroScheme_ideal_of_trivialization X L (s.eval (.op ⊤)) U e a rfl
  have hxZero : x ∈ X.zeroLocus (U := U.1) (D.ideal U : Set Γ(X, U.1)) :=
    (D.mem_support_iff_of_mem hxU).mp hxD
  rw [Scheme.mem_zeroLocus_iff] at hxZero
  have haI : a ∈ D.ideal U := by
    rw [hgen]
    exact Ideal.subset_span (by simp [a])
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun ha => hxZero a haI ((X.mem_basicOpen a x hxU).mpr ha)

/-- On a trivializing affine open, the kernel of the stalk map of the zero scheme of a global
section `s` of an invertible module is generated by the germ of the frame coordinate of `s`. -/
lemma ker_zeroScheme_stalkMap_of_frame
    (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (U : X.affineOpens)
    (eU : L.over U.1 ≅ SheafOfModules.unit (X.ringCatSheaf.over U.1))
    (y : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subscheme)
    (hy : (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι y ∈ U.1) :
    RingHom.ker ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι.stalkMap y).hom =
      Ideal.span {(X.presheaf.germ U.1 _ hy).hom
                    (Stacks.Divisors.frameSections X L eU
                      (L.presheaf.map (homOfLE le_top).op (s.eval (.op ⊤))))} := by
  rw [ker_subscheme_stalkMap_eq_map_ideal _ U y hy,
    Stacks.Divisors.zeroScheme_ideal_of_trivialization X L (s.eval (.op ⊤)) U
      (Stacks.Divisors.frameSections X L eU) _ rfl,
    Ideal.map_span, Set.image_singleton]

open CategoryTheory.Limits Opposite
lemma supportDim_quotSMulTop_eq_zero_of_dim_one
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hM : Module.supportDim R M = 1)
    (hx : IsSMulRegular M x) (hxm : x ∈ IsLocalRing.maximalIdeal R) :
    Module.supportDim R (QuotSMulTop x M) = 0 := by
  have h := Module.supportDim_quotSMulTop_succ_eq_supportDim hx hxm
  rw [hM] at h
  cases hd : Module.supportDim R (QuotSMulTop x M) with
  | bot => simp [hd] at h
  | coe d =>
    cases d with
    | top =>
      rw [hd] at h
      have h' : (⊤ : ℕ∞) + 1 = 1 := WithBot.coe_inj.mp h
      simp at h'
    | coe n =>
      rw [hd] at h
      have hn : (n : ℕ) + 1 = 1 := by
        norm_cast at h ⊢
      have hn0 : n = 0 := by omega
      simp [hn0]

private lemma depth_eq_zero_of_supportDim_eq_zero
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : Module.supportDim R M = 0) : Module.depth R (IsLocalRing.maximalIdeal R) M = 0 := by
  have hle := Module.depth_le_supportDim R (IsLocalRing.maximalIdeal R) M
    (Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (by
      rw [IsLocalRing.jacobson_eq_maximalIdeal _
        (Module.annihilator_eq_top_iff.not.mpr (not_subsingleton M))])))
  rw [hM] at hle
  exact le_antisymm (by exact_mod_cast hle) zero_le

private lemma isCohenMacaulayAtMaximalIdeal_of_supportDim_eq_zero
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hM : Module.supportDim R M = 0) :
    Module.IsCohenMacaulayAtMaximalIdeal R M := by
  show (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) =
    Module.supportDim R M
  rw [depth_eq_zero_of_supportDim_eq_zero hM, hM]
  norm_num

private lemma isCohenMacaulayAtMaximalIdeal_iff_quotSMulTop
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hx : IsSMulRegular M x) :
    Module.IsCohenMacaulayAtMaximalIdeal R M ↔
      Module.IsCohenMacaulayAtMaximalIdeal R (QuotSMulTop x M) := by
  show (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) =
      Module.supportDim R M ↔
    (Module.depth R (IsLocalRing.maximalIdeal R) (QuotSMulTop x M) : WithBot ℕ∞) =
      Module.supportDim R (QuotSMulTop x M)
  exact Module.depth_eq_supportDim_iff_quotSMulTop hxm hx

/-- **Stacks 02QG** for a module of support dimension one: for a nonzerodivisor `x` in the maximal
ideal, the length of `M / xM` is the sum over the minimal primes `q` of `Supp(M)` of the length
of `R / (x, q)` times the length of `M_q`. -/
lemma length_quotSMulTop_eq_sum_of_regular_of_supportDim_eq_one
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : IsSMulRegular M x) (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hM : Module.supportDim R M = 1) :
    Module.length R (QuotSMulTop x M) =
      ∑ᶠ q ∈ {q : PrimeSpectrum R | Minimal (· ∈ Module.support R M) q},
        Module.length R (R ⧸ (Ideal.span {x} ⊔ q.asIdeal)) *
          Module.length (Localization.AtPrime q.asIdeal)
            (LocalizedModule q.asIdeal.primeCompl M) := by
  have hQ := supportDim_quotSMulTop_eq_zero_of_dim_one hM hx hxm
  let : Nontrivial (QuotSMulTop x M) :=
    (Module.supportDim_ne_bot_iff_nontrivial R _).mp (by rw [hQ]; simp)
  have hCM := (isCohenMacaulayAtMaximalIdeal_iff_quotSMulTop hxm hx).mpr
    (isCohenMacaulayAtMaximalIdeal_of_supportDim_eq_zero hQ)
  exact AlgebraicGeometry.length_quotSMulTop_eq_sum_minimal_support x hCM hM hQ

/-- Relative dimension drops strictly along a nontrivial specialization. -/
lemma relativeDimension_lt_of_specializes
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {x y : X}
    (hxy : x ⤳ y) (hne : x ≠ y) :
    relativeDimension C.dimensionFunction f y <
      relativeDimension C.dimensionFunction f x := by
  obtain ⟨dX, hdX⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  simpa only [← hdX x, ← hdX y] using dX.strictAnti_specializes hxy hne

private lemma relativeDimension_le_schemeDeltaDimension_at
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (x : X) :
    (relativeDimension C.dimensionFunction f x : EInt) ≤
      schemeDeltaDimension C f := by
  classical
  have hirr : IsIrreducible (closure ({x} : Set X)) :=
    isIrreducible_iff_closure.mpr isIrreducible_singleton
  obtain ⟨W, hW, hsub⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  let Wc : irreducibleComponents X := ⟨W, hW⟩
  let Q : IrreducibleCloseds X :=
    ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩
  let η : X := Q.isIrreducible.genericPoint
  have hη : IsGenericPoint η (W : Set X) := by
    simpa [η, Q, isClosed_of_mem_irreducibleComponents W hW] using
      hW.1.isGenericPoint_genericPoint_closure
  have hspec : η ⤳ x := hη.specializes (hsub (subset_closure rfl))
  have hrel : relativeDimension C.dimensionFunction f x ≤
      relativeDimension C.dimensionFunction f η := by
    by_cases hηx : η = x
    · simp [hηx]
    · exact (relativeDimension_lt_of_specializes C f hspec hηx).le
  rw [schemeDeltaDimension_eq_iSup]
  exact (WithBotTop.coe_le_coe.mpr hrel).trans (le_iSup (fun V : irreducibleComponents X =>
    (deltaDimension C f
      ⟨V, V.2.1, isClosed_of_mem_irreducibleComponents (V : Set X) V.2⟩ : EInt)) Wc)

/-- The relative dimension at a point of a closed subscheme is at most the delta-dimension of that
subscheme. -/
lemma relativeDimension_le_closedSubschemeDimension_at
    (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    (relativeDimension C.dimensionFunction f (i z) : EInt) ≤
      schemeDeltaDimension C (i ≫ f) := by
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction i f z]
  exact relativeDimension_le_schemeDeltaDimension_at C (i ≫ f) z

/-- The reduced induced closed subscheme structure on the closure of a point: the integral closed
subscheme with that point as generic point. -/
noncomputable def reducedPointClosure {Y : Scheme.{u}} (y : Y) :
    Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({y} : Set Y), isClosed_closure⟩ : Closeds Y)

private lemma coe_support_reducedPointClosure {Y : Scheme.{u}} (y : Y) :
    ((reducedPointClosure y).support : Set Y) = closure ({y} : Set Y) := by
  simp [reducedPointClosure]

lemma isIntegral_reducedPointClosure {Y : Scheme.{u}} (y : Y) :
    IsIntegral (reducedPointClosure y).subscheme := by
  let D := reducedPointClosure y
  have hsup := coe_support_reducedPointClosure y
  have hred : IsReduced D.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hirr : IsIrreducible (Set.range D.subschemeι) := by
    rw [D.range_subschemeι, hsup]
    exact isIrreducible_singleton.closure
  let : IsReduced D.subscheme := hred
  let : IrreducibleSpace D.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme Y D hirr
  exact isIntegral_of_irreducibleSpace_of_isReduced D.subscheme

private lemma point_is_generic_in_reducedPointClosure {Y : Scheme.{u}} (y : Y) :
    ∃ z : (reducedPointClosure y).subscheme,
      (reducedPointClosure y).subschemeι z = y ∧ IsGenericPoint z Set.univ := by
  let D := reducedPointClosure y
  have hsup := coe_support_reducedPointClosure y
  have hy : y ∈ (D.support : Set Y) := by
    rw [hsup]
    exact subset_closure rfl
  rw [← D.range_subschemeι] at hy
  obtain ⟨z, hzy⟩ := hy
  refine ⟨z, hzy, ?_⟩
  apply isGenericPoint_def.mpr
  rw [D.subschemeι.isEmbedding.closure_eq_preimage_closure_image,
    Set.image_singleton, hzy]
  show D.subschemeι ⁻¹' closure ({y} : Set Y) = Set.univ
  rw [← hsup, ← D.range_subschemeι]
  simp

private lemma reducedPointClosure_genericPoint_map {Y : Scheme.{u}} (y : Y)
    [IsIntegral (reducedPointClosure y).subscheme] :
    (reducedPointClosure y).subschemeι (genericPoint (reducedPointClosure y).subscheme) = y := by
  obtain ⟨z, hzy, hzgen⟩ := point_is_generic_in_reducedPointClosure y
  have hz : z = genericPoint (reducedPointClosure y).subscheme :=
    ((genericPoint_spec (reducedPointClosure y).subscheme).eq hzgen).symm
  simpa [hz] using hzy

private theorem schemeDeltaDimension_eq_genericPoint_of_integral
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] :
    schemeDeltaDimension C p =
      (relativeDimension C.dimensionFunction p (genericPoint X) : EInt) := by
  let W : irreducibleComponents X := ⟨Set.univ, by
    simp [irreducibleComponents_eq_singleton]⟩
  let : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  rw [schemeDeltaDimension_eq_iSup, ciSup_subsingleton W]
  exact congrArg (fun z : ℤ => (z : EInt))
    (deltaDimension_eq_of_isGenericPoint C p
      ⟨(W : Set X), W.2.1,
        isClosed_of_mem_irreducibleComponents (W : Set X) W.2⟩
      (genericPoint X) (genericPoint_spec X))

attribute [local instance] Classical.propDecidable
lemma reducedPointClosure_schemeDeltaDimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (x : X) :
    schemeDeltaDimension C ((reducedPointClosure x).subschemeι ≫ p) =
      (relativeDimension C.dimensionFunction p x : EInt) := by
  let := isIntegral_reducedPointClosure x
  rw [schemeDeltaDimension_eq_genericPoint_of_integral,
    relativeDimension_comp_closedImmersion,
    reducedPointClosure_genericPoint_map]

private lemma cycle_reducedPointClosure_apply
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (x y : X)
    (hx : relativeDimension C.dimensionFunction p x = k) :
    (cycleAssociatedToClosedSubscheme C p
      (reducedPointClosure x).subschemeι k).1 y = if x = y then 1 else 0 := by
  classical
  let W := reducedPointClosure x
  let : IsIntegral W.subscheme := isIntegral_reducedPointClosure x
  have hg : ∀ ξ : genericPoints W.subscheme, W.subschemeι ξ.1 = x := by
    intro ξ
    have hξ : IsGenericPoint ξ.1 (Set.univ : Set W.subscheme) := by
      have h := ξ.2
      change closure ({ξ.1} : Set W.subscheme) ∈ irreducibleComponents W.subscheme at h
      rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
      exact isGenericPoint_def.mpr h
    have heq := hξ.eq (genericPoint_spec W.subscheme)
    rw [heq]
    exact reducedPointClosure_genericPoint_map x
  by_cases hxy : x = y
  · subst y
    obtain ⟨z, hz, hzg⟩ := point_is_generic_in_reducedPointClosure x
    change W.subschemeι z = x at hz
    let ξ : genericPoints W.subscheme := ⟨z, by
      show closure ({z} : Set W.subscheme) ∈ irreducibleComponents W.subscheme
      rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
      exact hzg⟩
    have h := cycleAssociatedToClosedSubscheme_apply C p W.subschemeι k ξ
      (by simpa only [ξ, hz] using hx)
    rw [componentMultiplicity_eq_one_of_reduced] at h
    simpa only [ξ, hz, ite_true] using h
  · rw [if_neg hxy]
    apply cycleAssociatedToClosedSubscheme_apply_eq_zero
    rintro ⟨ξ, hξ, _⟩
    exact hxy ((hg ξ).symm.trans hξ)

/-- A point carrying a nonzero coefficient in a `k`-cycle has relative dimension `k`. -/
lemma cycle_dimension_at_support
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (α : CycleGroup C p k) (x : X) (hx : α.1 x ≠ 0) :
    relativeDimension C.dimensionFunction p x = k := by
  let W : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  have hg : W.isIrreducible.genericPoint = x :=
    irreducibleSetEquivPoints.apply_symm_apply x
  have h := α.2 W (by simpa [hg] using hx)
  simpa only [deltaDimension, hg] using h

lemma cycle_eq_finsum_reducedPointClosure
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (α : CycleGroup C p k) (x : X) :
    α.1 x = ∑ᶠ y : {y : X // α.1 y ≠ 0}, α.1 y.1 *
      (cycleAssociatedToClosedSubscheme C p
        (reducedPointClosure y.1).subschemeι k).1 x := by
  classical
  have hc (y : {y : X // α.1 y ≠ 0}) := cycle_reducedPointClosure_apply C p k y.1 x
    (cycle_dimension_at_support C p k α y.1 y.2)
  simp_rw [hc]
  by_cases hx : α.1 x = 0
  · rw [hx]
    symm
    apply finsum_eq_zero_of_forall_eq_zero
    intro y
    rw [if_neg (fun (h : y.1 = x) => y.2 (by rw [h]; exact hx)), mul_zero]
  · let y : {y : X // α.1 y ≠ 0} := ⟨x, hx⟩
    rw [finsum_eq_single _ y]
    · simp [y]
    · intro z hz
      rw [if_neg (fun h => hz (Subtype.ext h)), mul_zero]

lemma locallyFinite_reducedPointClosure_support
    {X : Scheme.{u}} (α : AlgebraicCycle X ℤ) :
    LocallyFinite (fun x : {x : X // α x ≠ 0} =>
      ((reducedPointClosure x.1).support : Set X)) := by
  intro x
  obtain ⟨V, hV, hfin⟩ := α.locallyFiniteSupport x
  obtain ⟨U, hUV, hU, hxU⟩ := mem_nhds_iff.mp hV
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  apply (hfin.preimage (f := fun y : {y : X // α y ≠ 0} => y.1)
    Subtype.val_injective.injOn).subset
  rintro y ⟨z, hz, hzU⟩
  have hzy : y.1 ⤳ z := by
    rw [specializes_iff_mem_closure]
    simpa [reducedPointClosure] using hz
  exact ⟨hUV (hzy.mem_open hU hzU), y.2⟩

/-- A point carrying a nonzero coefficient in the fundamental cycle of a closed subscheme lies in
that closed subscheme. -/
lemma closedSubscheme_cycle_nonzero_mem_support
    (C : ChowSituation.{u}) {X Z : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (i : Z ⟶ X) [IsClosedImmersion i] (k : ℤ) (x : X)
    (h : (cycleAssociatedToClosedSubscheme C p i k).1 x ≠ 0) :
    x ∈ Set.range i := by
  by_contra hx
  have hz := cycleAssociatedToClosedSubscheme_apply_eq_zero
    C p i k x (by
      rintro ⟨ξ, hξ, _⟩
      exact hx ⟨ξ.1, hξ⟩)
  exact h hz

/-- If no integral closed subscheme occurring in a `(k+1)`-cycle `α` is contained in the zero
scheme of `s`, the Gysin class of `α` is represented by the coefficientwise sum of the
fundamental cycles of the intersections of those subschemes with the zero scheme. -/
lemma gysinHomomorphism_eq_finsum_intersections
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (α : CycleGroup C p (k + 1))
    (havoid : ∀ x : X, α.1 x ≠ 0 →
      ¬ Stacks.Divisors.zeroScheme X L s ≤ reducedPointClosure x) :
    ∃ β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      gysinHomomorphismOfInvertible C p k L s α = QuotientAddGroup.mk β ∧
      ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
        β.1 x = ∑ᶠ y : {y : X // α.1 y ≠ 0}, α.1 y.1 *
          (cycleAssociatedToClosedSubscheme C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
            (((reducedPointClosure y.1).comap
              (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k).1 x := by
  classical
  let J := {y : X // α.1 y ≠ 0}
  let W : J → X.IdealSheafData := fun y => reducedPointClosure y.1
  have hW (y : J) : IsIntegral (W y).subscheme := isIntegral_reducedPointClosure y.1
  have hd (y : J) : schemeDeltaDimension C ((W y).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt) := by
    rw [reducedPointClosure_schemeDeltaDimension,
      cycle_dimension_at_support C p (k + 1) α y.1 y.2]
  obtain ⟨β, hβ, hb⟩ := gysinHomomorphismOfInvertible_finsum C p k L s W hW hd
    (locallyFinite_reducedPointClosure_support α.1) (fun y => α.1 y.1) α
    (cycle_eq_finsum_reducedPointClosure C p (k + 1) α)
  refine ⟨β, hβ, fun x => ?_⟩
  rw [hb]
  apply finsum_congr
  intro y
  congr 2
  simp only [gysinComponentCycle, W, dif_neg (havoid y.1 y.2)]



theorem stalk_ker_closedImmersion
    {T Y : Scheme.{u}} (i : T ⟶ Y) [IsClosedImmersion i] (ξ : T) :
    IdealSheafData.stalk i.ker (i ξ) =
      RingHom.ker (i.stalkMap ξ).hom := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hξU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i ξ)) isOpen_univ
  exact AlgebraicGeometry.stalk_ker_eq_of_affine_target i ξ U hU hξU

/- Colength of an ideal transported along a surjection: the quotient of `B` by
`J ⊔ ker ψ` is the quotient of `C` by the image of `J`. This is the general-ideal
form of the usual principal-ideal statement. -/
lemma length_quotient_sup_ker_eq_length_quotient_map
    {B C : Type*} [CommRing B] [CommRing C]
    (ψ : B →+* C) (hψ : Function.Surjective ψ) (J : Ideal B) :
    Module.length B (B ⧸ (J ⊔ RingHom.ker ψ)) =
      Module.length C (C ⧸ Ideal.map ψ J) := by
  let q := RingHom.ker ψ
  let D := B ⧸ q
  let e0 : D ≃+* C := RingHom.quotientKerEquivOfSurjective hψ
  let I : Ideal D := Ideal.map (Ideal.Quotient.mk q) J
  let JC : Ideal C := Ideal.map ψ J
  have he0 : ∀ b : B, e0 (Ideal.Quotient.mk q b) = ψ b := by
    intro b
    rw [RingHom.quotientKerEquivOfSurjective_apply_mk]
  have hcomp : (e0 : D →+* C).comp (Ideal.Quotient.mk q) = ψ := RingHom.ext he0
  have hIJ : JC = Ideal.map (e0 : D →+* C) I := by
    show Ideal.map ψ J = Ideal.map (e0 : D →+* C) (Ideal.map (Ideal.Quotient.mk q) J)
    rw [Ideal.map_map, hcomp]
  let e1 : D ⧸ I ≃+* C ⧸ JC := Ideal.quotientEquiv I JC e0 hIJ
  let eDQ : D ⧸ I ≃+* B ⧸ (q ⊔ J) :=
    DoubleQuot.quotQuotEquivQuotSup q J
  let e : B ⧸ (q ⊔ J) ≃+* C ⧸ JC := eDQ.symm.trans e1
  let φ : B →+* C ⧸ JC := (Ideal.Quotient.mk JC).comp ψ
  let : Algebra B (B ⧸ (q ⊔ J)) :=
    (Ideal.Quotient.mk (q ⊔ J)).toAlgebra
  let : Algebra B C := ψ.toAlgebra
  let : Algebra C (C ⧸ JC) := (Ideal.Quotient.mk JC).toAlgebra
  let : Algebra B (C ⧸ JC) := φ.toAlgebra
  let : IsScalarTower B C (C ⧸ JC) := IsScalarTower.of_algebraMap_eq' rfl
  have he : ∀ b : B,
      e (algebraMap B (B ⧸ (q ⊔ J)) b) = algebraMap B (C ⧸ JC) b := by
    intro b
    show e (Ideal.Quotient.mk (q ⊔ J) b) = Ideal.Quotient.mk JC (ψ b)
    show e1 (eDQ.symm (Ideal.Quotient.mk (q ⊔ J) b)) = _
    rw [DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk]
    show (Ideal.quotientEquiv I JC e0 hIJ)
      (Ideal.Quotient.mk I (Ideal.Quotient.mk q b)) = _
    rw [Ideal.quotientEquiv_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]
  let eA : (B ⧸ (q ⊔ J)) ≃ₐ[B] (C ⧸ JC) :=
    AlgEquiv.ofRingEquiv (f := e) he
  calc
    Module.length B (B ⧸ (J ⊔ q)) =
        Module.length B (B ⧸ (q ⊔ J)) := by rw [sup_comm]
    _ = Module.length B (C ⧸ JC) := eA.toLinearEquiv.length_eq
    _ = Module.length C (C ⧸ JC) :=
      Module.length_eq_of_surjective (M := C ⧸ JC) hψ

end Stacks.Chow

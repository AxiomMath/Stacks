module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.CohenMacaulay.OpenLocus
public import StacksFrontier.RingTheory.CompleteIntersection.AtPrime
public import StacksFrontier.RingTheory.Dualizing.Depth
public import StacksFrontier.RingTheory.Dualizing.DepthLemmas.Ext
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs
public import StacksFrontier.RingTheory.RegularLocalRing.MvPolynomialFiber
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.RingTheory.Depth.AlgebraMap

/-!
# A lower bound for the cohomology of a relative dualizing complex

Let `R → A` be a finite type homomorphism of Noetherian rings, let `𝔮 ⊂ A` be a prime and let `d`
be the dimension at `𝔮` of the fibre of `Spec(A) → Spec(R)` through `𝔮`.  Then the localization at
`𝔮` of `H^i(ω^•_{A/R})` vanishes for every `i < -d`, where `ω^•_{A/R} = f^!(R)` is the relative
dualizing complex.

## Main results

* `Dualizing.upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology` — the
  bound `-d ≤ i`, for the upper shriek functor of an arbitrary polynomial presentation.

## Implementation notes

The relative dualizing complex of [Stacks, Tag 0E9M] is `f^!` applied to `R` placed in degree
zero, and `f^!` is only defined up to isomorphism; the statement below is therefore made for the
functor of an arbitrary polynomial presentation `R → P = R[x_1, …, x_n] → A`, which is stronger
than any statement about one chosen presentation.

The argument is the source's.  Writing `I = ker(P → A)` and `𝔯 ⊂ P` for the prime below `𝔮`, the
identification `f^!(R) = RHom_P(A, P)[n]` turns the claim into the vanishing of
`Ext^j_{P_𝔯}(A_𝔯, P_𝔯)` for `j < n - d`, which by Rees' theorem — [Stacks, Tag 0AVZ] — follows
from `depth_{I P_𝔯}(P_𝔯) ≥ n - d`.  That inequality is [Stacks, Tag 0BUY] applied to the flat
local homomorphism `R_𝔭 → P_𝔯` with Cohen--Macaulay closed fibre, which bounds the depth below by
the drop in dimension `dim((P ⊗_R κ(𝔭))_𝔯) - dim((A ⊗_R κ(𝔭))_𝔮)`; the codimension formula of
[Stacks, Tag 00P2] identifies that drop with `n - d`.

Cohomology is indexed so that the single complex of a module sits in degree zero, and the
localization of a cohomology module at `𝔮` is `LocalizedModule` at the prime complement; `𝔮` is
therefore in the support of `H^i(ω^•_{A/R})` exactly when the localization is nontrivial.

## References

* [Stacks Project, Tag 0E9P](https://stacks.math.columbia.edu/tag/0E9P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Extension of scalars along `φ : R →+* P` carries `R` to `P`**, by the right unitor of the
tensor product. -/
public noncomputable def extendScalarsUnitIso {R P : Type u} [CommRing R] [CommRing P]
    (φ : R →+* P) :
    (ModuleCat.extendScalars.{u, u, u} φ).obj (ModuleCat.of R R) ≅ ModuleCat.of P P := by
  letI := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R P P).toModuleIso

/-- **Derived base change along the polynomial algebra of a presentation carries the base ring to
that algebra**: the identification `R ⊗_R^L P = P` in degree zero. This is where the relative
dualizing complex `φ^!(R) = RHom_P(A, R ⊗_R^L P)[n]` becomes `RHom_P(A, P)[n]`. -/
public noncomputable def PolynomialPresentation.derivedExtensionUnitIso
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A} (p : PolynomialPresentation f) :
    (p.derivedExtension.{u, 0}).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
        (ModuleCat.of p.Poly p.Poly) := by
  let F := ModuleCat.extendScalars.{u, u, u} (MvPolynomial.C : R →+* p.Poly)
  letI : Limits.PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, 0} _ p.flat_C
  change F.mapDerivedCategory.obj _ ≅ _
  exact (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of R R) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).mapIso
      (extendScalarsUnitIso (MvPolynomial.C : R →+* p.Poly))

/-- Cohomology in degree `i` of a shift by `n` is cohomology in degree `i + n`. -/
private noncomputable def homologyOfShiftIso
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (i n : ℤ) :
    ((DerivedCategory.homologyFunctor C i).obj
      ((shiftFunctor (DerivedCategory C) n).obj K)) ≅
      ((DerivedCategory.homologyFunctor C (i + n)).obj K) := by
  rw [← DerivedCategory.shift_homologyFunctor C i,
    ← DerivedCategory.shift_homologyFunctor C (i + n)]
  exact ((DerivedCategory.homologyFunctor C 0).shiftIso n i (i + n) (by omega)).app K

/-- A quotient of a local ring which is maximal Cohen--Macaulay over itself is Cohen--Macaulay at
the maximal ideal as a module over the ambient ring. -/
theorem isCohenMacaulayAtMaximalIdeal_quotient
    {S : Type*} [CommRing S] [IsLocalRing S] (J : Ideal S)
    [IsLocalRing (S ⧸ J)]
    (h : Module.IsMaximalCohenMacaulay (S ⧸ J) (S ⧸ J)) :
    Module.IsCohenMacaulayAtMaximalIdeal S (S ⧸ J) := by
  change (Module.depth S (IsLocalRing.maximalIdeal S) (S ⧸ J) : WithBot ℕ∞) = _
  rw [Module.supportDim_quotient_eq_ringKrullDim,
    Module.depth_eq_depth_map_algebraMap (B := S ⧸ J) Ideal.Quotient.mk_surjective]
  have hmap : (IsLocalRing.maximalIdeal S).map (algebraMap S (S ⧸ J)) =
      IsLocalRing.maximalIdeal (S ⧸ J) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  rw [hmap]
  exact h

/-- A ring isomorphic to the localization of a ring at a prime has the height of that prime as its
Krull dimension. -/
theorem ringKrullDim_eq_height_of_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (q : Ideal A) [q.IsPrime]
    (e : Localization.AtPrime q ≃+* B) : ringKrullDim B = (q.height : WithBot ℕ∞) :=
  (ringKrullDim_eq_of_ringEquiv e).symm.trans
    (IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q))

/-- Transport of the nonvanishing of a localized `Ext` along an equality of primes. -/
private theorem nontrivial_localized_derivedExt_congr
    {P M : Type u} [CommRing P] [AddCommGroup M] [Module P M]
    (r s : Ideal P) [r.IsPrime] [s.IsPrime] (h : r = s) (k : ℤ) :
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime r)) 0).obj
        (ModuleCat.of (Localization.AtPrime r) (LocalizedModule r.primeCompl M)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime r)) 0).obj
        (ModuleCat.of (Localization.AtPrime r) (Localization.AtPrime r))) k) ↔
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime s)) 0).obj
        (ModuleCat.of (Localization.AtPrime s) (LocalizedModule s.primeCompl M)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime s)) 0).obj
        (ModuleCat.of (Localization.AtPrime s) (Localization.AtPrime s))) k) := by
  subst s
  rfl

/-- Rees' theorem of [Stacks, Tag 0AVZ] in the shape used below: `Ext^i(N, M)` vanishes below the
`I`-depth of `M` when some power of `I` annihilates `N`. -/
private theorem ext_subsingleton_of_lt_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{u} R]
    (I : Ideal R) (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤)
    (hN : ∃ n : ℕ, I ^ n ≤ Module.annihilator R N)
    (i : ℕ) (hi : (i : ℕ∞) < Module.depth R I M) :
    Subsingleton (Ext N M i) := by
  obtain ⟨n, hn⟩ := hN
  exact ModuleCat.subsingleton_ext_of_lt_ideal_depth I M N hIM hn hi

/-- The support of a module over the target of a surjection is the preimage of its support over
the source. -/
private theorem support_restrictScalars_iff
    {R A M : Type u} [CommRing R] [CommRing A] [AddCommGroup M]
    [Module A M] [SMul R A] [Module R M] [IsScalarTower R A M]
    (f : R →+* A) (hf : Function.Surjective f) [Module.Finite A M]
    [Module.Finite R M] (hsmul : ∀ r a, r • a = f r * a)
    (q : PrimeSpectrum A) :
    q ∈ Module.support A M ↔
      PrimeSpectrum.comap f q ∈ Module.support R M := by
  have hann : Module.annihilator R M = Ideal.comap f (Module.annihilator A M) := by
    ext r
    simp only [Module.mem_annihilator, Ideal.mem_comap]
    change (∀ m, r • m = 0) ↔ ∀ m, f r • m = 0
    have heq (m : M) : r • m = f r • m := by
      calc
        r • m = r • ((1 : A) • m) := by simp
        _ = (r • (1 : A)) • m := by rw [← smul_assoc]
        _ = f r • m := by rw [hsmul, mul_one]
    simp only [heq]
  rw [Module.support_eq_zeroLocus, Module.support_eq_zeroLocus, hann,
    PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus]
  change Module.annihilator A M ≤ q.asIdeal ↔
    Ideal.comap f (Module.annihilator A M) ≤ q.asIdeal.comap f
  constructor
  · intro h x hx
    exact Ideal.mem_comap.mpr (h (Ideal.mem_comap.mp hx))
  · intro h a ha
    obtain ⟨x, rfl⟩ := hf a
    exact Ideal.mem_comap.mp (h (Ideal.mem_comap.mpr ha))

/-- A module finite over the source of a surjection of rings is finite over the target. -/
private theorem finite_of_surjective_scalarMap
    {R A M : Type u} [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Module A M] [SMul R A] [Module R M] [IsScalarTower R A M]
    [Module.Finite R M] : Module.Finite A M :=
  Module.Finite.of_fg_top (Submodule.FG.of_restrictScalars R Module.Finite.fg_top)

/-- `Ext` between modules placed in degree zero vanishes in negative degrees. -/
theorem subsingleton_derivedExt_of_neg
    {P : Type u} [CommRing P] (N M : ModuleCat.{u} P) (k : ℤ) (hk : ¬ 0 ≤ k) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj N)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M) k) := by
  have hsrc : (((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj N)).IsLE 0 :=
    inferInstance
  have htgt : (((shiftFunctor (DerivedCategory (ModuleCat.{u} P)) k).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M))).IsGE 1 := by
    have h0 : ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M).IsGE 0 :=
      inferInstance
    have hge := DerivedCategory.TStructure.t.ge_shift 0 k (-k) (by omega) _ h0.ge
    rcases hge with ⟨K, e, hK⟩
    let : K.IsStrictlyGE (-k) := hK
    exact ⟨⟨K, e, K.isStrictlyGE_of_ge 1 (-k) (by omega)⟩⟩
  refine Subsingleton.intro fun x y => sub_eq_zero.mp ?_
  exact DerivedCategory.TStructure.t.zero' (x - y) hsrc.le htgt.ge

/-- `Ext` between finite modules over a Noetherian ring is finite. -/
theorem finite_derivedExt
    {P : Type u} [CommRing P] [IsNoetherianRing P] [Small.{u} P]
    (N M : ModuleCat.{u} P) [Module.Finite P N] [Module.Finite P M] (k : ℤ) :
    Module.Finite P (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj N)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M) k) := by
  classical
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} P) :=
    HasDerivedCategory.standard.{u, u + 1} _
  let : CategoryTheory.HasExt.{u} (ModuleCat.{u} P) := inferInstance
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    let e₀ : Abelian.Ext N M n ≃+
        DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj N)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M) (n : ℤ) :=
      Abelian.Ext.homAddEquiv.{u + 1, u, u, u + 1}
        (C := ModuleCat.{u} P) (X := N) (Y := M) (n := n)
    let : Module.Finite P (Abelian.Ext N M n) := inferInstance
    exact Module.Finite.equiv (e₀.linearEquiv P)
  · have := subsingleton_derivedExt_of_neg N M k hk
    exact Module.Finite.of_finite

/-- A finite module over a Noetherian ring, placed in degree zero, is pseudo-coherent. -/
@[sga "6 I 5.0" "partial"]
public theorem isPseudoCoherent_single_of_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  change StacksDraft.PseudoCoherence.IsPseudoCoherent K
  refine (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    K 0 (M : Type u)).2.1.mpr ⟨⟨0, ?_⟩, ?_⟩
  · exact fun i hi => DerivedCategory.isZero_of_isLE K 0 i hi
  · intro i
    by_cases hi : i = 0
    · subst i
      have hM : Module.Finite R ((𝟭 (ModuleCat.{u} R)).obj M) := by
        simpa using (inferInstance : Module.Finite R M)
      exact Module.Finite.equiv
        (((DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{u} R) 0).app M).symm.toLinearEquiv)
    · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
        rcases lt_or_gt_of_ne hi with h | h
        · exact DerivedCategory.isZero_of_isGE K 0 i h
        · exact DerivedCategory.isZero_of_isLE K 0 i h
      let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      exact Module.Finite.of_finite

/-- The target of a polynomial presentation, restricted along the presenting surjection, is a
finite module over the polynomial algebra. -/
public theorem finite_restrictScalars_ulift
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A} (p : PolynomialPresentation f) :
    Module.Finite p.Poly
      ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))) := by
  let g : p.Poly →ₗ[p.Poly] ↑((ModuleCat.restrictScalars p.toRingHom).obj
      (ModuleCat.of A (ULift.{u} A))) :=
    { toFun := fun x => ULift.up (p.toRingHom x),
      map_add' := fun x y => congrArg ULift.up (map_add p.toRingHom x y),
      map_smul' := by
        intro x y
        change ULift.up (p.toRingHom (x * y)) = ULift.up (p.toRingHom x * p.toRingHom y)
        simp }
  refine Module.Finite.of_surjective g ?_
  intro x
  obtain ⟨a⟩ := x
  obtain ⟨b, hb⟩ := p.surjective a
  exact ⟨b, congrArg ULift.up hb⟩

/-- **The homological half of [Stacks, Tag 0E9P].** Nonvanishing of the localization at `𝔮` of
`H^i(f^!(R))` forces the localization at the prime `𝔯` of `P` below `𝔮` of
`Ext^{i+n}_P(A, P)` to be nonzero, where `P` is the polynomial algebra of the presentation and
`n` its number of variables.  This is the identification `f^!(R) = RHom_P(A, P)[n]` of
[Stacks, Tag 0BZI] together with [Stacks, Tag 0A71]. -/
private theorem nontrivial_localized_ext_of_nontrivial_localizedHomology
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    {f : R →+* A} (p : PolynomialPresentation f) (q : PrimeSpectrum A) (i : ℤ)
    (hlocal : Nontrivial
      (LocalizedModule q.asIdeal.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))) :
    Nontrivial
      (LocalizedModule (PrimeSpectrum.comap p.toRingHom q).asIdeal.primeCompl
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
            ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))))
          ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
            (ModuleCat.of p.Poly p.Poly))
          (i + p.variableCount))) := by
  let P := p.Poly
  let RF := derivedHom.{u, 0, u} p.toRingHom
  let input := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let shifted := (shiftFunctor (DerivedCategory (ModuleCat.{u} A))
    (p.variableCount : ℤ)).obj (RF.obj input)
  have eUpper :
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        shifted := by
    dsimp [PolynomialPresentation.upperShriekFunctor, shifted, RF, input]
    exact (shiftFunctor (DerivedCategory (ModuleCat.{u} A))
      (p.variableCount : ℤ)).mapIso
        ((derivedHom.{u, 0, u} p.toRingHom).mapIso p.derivedExtensionUnitIso)
  let k : ℤ := i + p.variableCount
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj (RF.obj input)
  let eH : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) ≅ H :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eUpper ≪≫
      homologyOfShiftIso (RF.obj input) i (p.variableCount : ℤ)
  have hlocalH : Nontrivial (LocalizedModule q.asIdeal.primeCompl H) :=
    (IsLocalizedModule.mapEquiv q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl _)
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl _)
      (Localization.AtPrime q.asIdeal) eH.toLinearEquiv).nontrivial_congr.mp hlocal
  let : Algebra P A := p.toRingHom.toAlgebra
  have hpMap : algebraMap P A = p.toRingHom := RingHom.algebraMap_toAlgebra p.toRingHom
  let extSource := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj
    ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))
  have : Module.Finite P
      ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))) :=
    finite_restrictScalars_ulift p
  let α := (coextendScalarsToDerivedCategory p.toRingHom).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} P) (ComplexShape.up ℤ))
  let eExt := (derivedCoextendScalarsHomologyLinearEquivExt p.toRingHom RF α).linearEquiv input k
  have hfiniteExt : Module.Finite P (DerivedCategory.Ext extSource input k) :=
    finite_derivedExt _ _ k
  have hfiniteHP : Module.Finite P ((ModuleCat.restrictScalars p.toRingHom).obj H) :=
    Module.Finite.equiv eExt.symm
  let : Module P (H : Type u) := ((ModuleCat.restrictScalars p.toRingHom).obj H).isModule
  let : Module P A := Module.compHom A p.toRingHom
  let : IsScalarTower P A (H : Type u) := IsScalarTower.of_compHom P A (H : Type u)
  let : Module.Finite P (H : Type u) := hfiniteHP
  have hfiniteH : Module.Finite A H :=
    finite_of_surjective_scalarMap (R := P) (A := A) (M := (H : Type u))
  have hsupportA : q ∈ Module.support A H := Module.mem_support_iff.mpr hlocalH
  have hsupportP : PrimeSpectrum.comap p.toRingHom q ∈
      Module.support P ((ModuleCat.restrictScalars p.toRingHom).obj H) := by
    change PrimeSpectrum.comap p.toRingHom q ∈ Module.support P (H : Type u)
    exact (support_restrictScalars_iff p.toRingHom p.surjective
      (fun r' a => by rw [Algebra.smul_def, hpMap]) q).mp hsupportA
  have hlocHP : Nontrivial
      (LocalizedModule (PrimeSpectrum.comap p.toRingHom q).asIdeal.primeCompl
        ((ModuleCat.restrictScalars p.toRingHom).obj H)) :=
    Module.mem_support_iff.mp hsupportP
  exact (IsLocalizedModule.mapEquiv
    (PrimeSpectrum.comap p.toRingHom q).asIdeal.primeCompl
    (LocalizedModule.mkLinearMap _ _) (LocalizedModule.mkLinearMap _ _)
    (Localization.AtPrime (PrimeSpectrum.comap p.toRingHom q).asIdeal)
    eExt).nontrivial_congr.mp hlocHP

/-- Nonvanishing of a localized `Ext` out of a finite module into the ring itself is nonvanishing
of the corresponding `Ext` over the localization: the base change of derived Hom along the flat
map to a localization is invertible. -/
private theorem nontrivial_ext_localization_of_nontrivial_localized_ext
    {P : Type u} [CommRing P] [IsNoetherianRing P] (M : ModuleCat.{u} P) [Module.Finite P M]
    (r : Ideal P) [r.IsPrime] (k : ℤ)
    (h : Nontrivial (LocalizedModule r.primeCompl
      (DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj M)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)) k))) :
    Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime r)) 0).obj
        (ModuleCat.of (Localization.AtPrime r)
          (LocalizedModule r.primeCompl (M : Type u))))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime r)) 0).obj
        (ModuleCat.of (Localization.AtPrime r) (Localization.AtPrime r))) k) := by
  let T := r.primeCompl
  let input := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let G := ModuleCat.localizedModuleFunctor T
  have hKge : ∃ b : ℤ, input.IsGE b := ⟨0, inferInstance⟩
  have h' : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj (G.obj M))
      (G.mapDerivedCategory.obj input) k) :=
    (localized_ext_nontrivial_iff (A := P) (T := T) (K := input) hKge
      (M := (M : Type u)) k).mp h
  let eP₀ : LocalizedModule T P ≃ₗ[Localization T] Localization T :=
    IsLocalizedModule.mapEquiv T
      (LocalizedModule.mkLinearMap T P)
      (Algebra.linearMap P (Localization T)) (Localization T) (LinearEquiv.refl P P)
  let eP : G.obj (ModuleCat.of P P) ≅ ModuleCat.of (Localization T) (Localization T) :=
    LinearEquiv.toModuleIso ((Shrink.linearEquiv (Localization T) _).trans eP₀)
  let eTarget := (G.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of P P) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).mapIso eP
  let eM : G.obj M ≅ ModuleCat.of (Localization T) (LocalizedModule T (M : Type u)) :=
    LinearEquiv.toModuleIso
      (Shrink.linearEquiv (Localization T) (LocalizedModule T (M : Type u)))
  let eSource := (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).mapIso eM
  exact (CategoryTheory.Linear.homCongr ℤ eSource
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (Localization T))) k).mapIso
      eTarget)).toAddEquiv.nontrivial_congr.mp h'

/-- **[Stacks, Tag 0E9P].** Let `R → A` be a finite type homomorphism of Noetherian rings, let
`𝔮 ⊂ A` be a prime and let `d` be the dimension at `𝔮` of the fibre of `Spec(A) → Spec(R)` over
the prime below `𝔮`.  If the localization at `𝔮` of `H^i(ω^•_{A/R})` is nonzero then `-d ≤ i`.
Here `ω^•_{A/R} = f^!(R)` is computed from an arbitrary polynomial presentation of `f`. -/
@[stacks 0E9P "for the upper shriek functor of an arbitrary polynomial presentation of the \
homomorphism, the relative dualizing complex being well defined only up to isomorphism, and with \
the fibre dimension named by a hypothesis identifying it with a natural number"]
theorem upperShriekFunctor_neg_relativeDimensionAt_le_of_nontrivial_localizedHomology
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A))
    (q : PrimeSpectrum A) (d : ℕ)
    (hd : Algebra.relativeDimensionAt R q.asIdeal = (d : WithBot ℕ∞)) (i : ℤ) :
    Nontrivial
        (LocalizedModule q.asIdeal.primeCompl
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            (p.upperShriekFunctor.{u, 0}.obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
                (ModuleCat.of R R))))) →
      -(d : ℤ) ≤ i := by
  intro hlocal
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  let P := p.Poly
  let k : ℤ := i + p.variableCount
  let r : PrimeSpectrum P := PrimeSpectrum.comap p.toRingHom q
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  let instM₀ : Module P (M₀ : Type u) := M₀.isModule
  have hM₀ : Module.Finite P (M₀ : Type u) := finite_restrictScalars_ulift p
  have hrLocal : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime r.asIdeal)) 0).obj
        (ModuleCat.of (Localization.AtPrime r.asIdeal)
          (LocalizedModule r.asIdeal.primeCompl (M₀ : Type u))))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime r.asIdeal)) 0).obj
        (ModuleCat.of (Localization.AtPrime r.asIdeal) (Localization.AtPrime r.asIdeal))) k) :=
    nontrivial_ext_localization_of_nontrivial_localized_ext M₀ r.asIdeal k
      (nontrivial_localized_ext_of_nontrivial_localizedHomology p q i hlocal)
  let pBase : Ideal R := q.asIdeal.under R
  let K := pBase.ResidueField
  let FpP := pBase.Fiber P
  let FpA := pBase.Fiber A
  let fPA : P →ₐ[R] A :=
    { toRingHom := p.toRingHom
      commutes' := fun x => congrArg (fun g : R →+* A => g x) p.commutes }
  let fFiber : FpP →ₐ[K] FpA := Algebra.TensorProduct.map (AlgHom.id K K) fPA
  let fFiberRing : FpP →+* FpA := fFiber
  have hFiberSurj : Function.Surjective fFiber :=
    Algebra.TensorProduct.map_surjective (AlgHom.id K K) fPA
      Function.surjective_id p.surjective
  let ePoly : FpP ≃ₐ[K] MvPolynomial (Fin p.variableCount) K :=
    MvPolynomial.algebraTensorAlgEquiv R K
  let gFiber : MvPolynomial (Fin p.variableCount) K →ₐ[K] FpA :=
    fFiber.comp ePoly.symm.toAlgHom
  have hgFiberSurj : Function.Surjective gFiber := hFiberSurj.comp ePoly.symm.surjective
  have hrUnder : r.asIdeal.under R = pBase := by
    change Ideal.comap (MvPolynomial.C : R →+* P) (Ideal.comap p.toRingHom q.asIdeal) = _
    rw [Ideal.comap_comap, p.commutes]
  obtain ⟨QA, hQA, hQAcomp⟩ :=
    Ideal.Fiber.exists_comap_includeRight_eq q.asIdeal pBase rfl
  let : QA.IsPrime := hQA
  let Qp : Ideal FpP := Ideal.comap fFiberRing QA
  let : Qp.IsPrime := Ideal.comap_isPrime fFiberRing QA
  have hcompFiber : fFiberRing.comp
      (Algebra.TensorProduct.includeRight : P →ₐ[R] FpP).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] FpA).toRingHom.comp p.toRingHom := by
    change ((AlgHom.restrictScalars R
      (Algebra.TensorProduct.map (AlgHom.id K K) fPA)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : P →ₐ[R] FpP).toRingHom) =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] FpA).toRingHom.comp p.toRingHom
    exact congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.map_restrictScalars_comp_includeRight (AlgHom.id K K) fPA)
  let qA : PrimeSpectrum FpA := ⟨QA, inferInstance⟩
  have hrelFiber : Algebra.relativeDimensionAt R q.asIdeal =
      TopologicalSpace.localKrullDim (PrimeSpectrum FpA) qA :=
    Algebra.relativeDimensionAt_eq_localKrullDim q.asIdeal pBase rfl QA hQAcomp
  have h00P2 := PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height
    K gFiber hgFiberSurj qA
  have hheight : (Ideal.comap gFiber.toRingHom QA).height = Qp.height := by
    change (Ideal.comap ePoly.symm.toRingHom Qp).height = Qp.height
    exact RingEquiv.height_comap ePoly.symm.toRingEquiv Qp
  have hdimFiber : (d : WithBot ℕ∞) + Qp.height =
      (p.variableCount : WithBot ℕ∞) + QA.height := by
    rw [← hd.symm.trans hrelFiber] at h00P2
    change (d : WithBot ℕ∞) + (Ideal.comap gFiber.toRingHom QA).height =
      (Nat.card (Fin p.variableCount) : WithBot ℕ∞) + QA.height at h00P2
    rw [hheight, Nat.card_fin] at h00P2
    exact h00P2
  let rP : Ideal P := Ideal.comap
    (Algebra.TensorProduct.includeRight : P →ₐ[R] FpP).toRingHom Qp
  let rA : Ideal A := Ideal.comap
    (Algebra.TensorProduct.includeRight : A →ₐ[R] FpA).toRingHom QA
  have hrPA : rP = Ideal.comap p.toRingHom rA := by
    change Ideal.comap (fFiberRing.comp
      (Algebra.TensorProduct.includeRight : P →ₐ[R] FpP).toRingHom) QA = _
    rw [hcompFiber, ← Ideal.comap_comap]
  have hQpcomp : rP = r.asIdeal := hrPA.trans (congrArg (Ideal.comap p.toRingHom) hQAcomp)
  let R₀ := Localization.AtPrime pBase
  let S₀ := Localization.AtPrime rP
  let T₀ := Localization.AtPrime rA
  let : rP.IsPrime := Ideal.comap_isPrime _ _
  let : rA.IsPrime := Ideal.comap_isPrime _ _
  have hrPUnder : rP.under R = pBase := by
    rw [hQpcomp]
    exact hrUnder
  have hrAUnder : rA.under R = pBase := by
    rw [show rA = q.asIdeal from hQAcomp]
  let : rP.LiesOver pBase := ⟨hrPUnder.symm⟩
  let : rA.LiesOver pBase := ⟨hrAUnder.symm⟩
  let : Algebra R₀ S₀ := Localization.AtPrime.algebraOfLiesOver pBase rP
  let : Algebra R₀ T₀ := Localization.AtPrime.algebraOfLiesOver pBase rA
  let : IsScalarTower R R₀ S₀ := inferInstance
  let : IsScalarTower R R₀ T₀ := inferInstance
  let fLocal : S₀ →+* T₀ := Localization.localRingHom rP rA p.toRingHom hrPA
  have hfLocal : Function.Surjective fLocal := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective rA.primeCompl x
    obtain ⟨b, hb⟩ := p.surjective a
    obtain ⟨c, hc⟩ := p.surjective s.1
    have hc' : c ∉ rP := by
      intro hcr
      rw [hrPA] at hcr
      have hmem : p.toRingHom c ∈ rA := Ideal.mem_comap.mpr hcr
      exact s.2 (by simpa [hc] using hmem)
    let sc : rP.primeCompl := ⟨c, hc'⟩
    refine ⟨IsLocalization.mk' S₀ b sc, ?_⟩
    rw [Localization.localRingHom_mk', hb]
    congr 1
    exact Subtype.ext hc
  let I₀ : Ideal S₀ := RingHom.ker fLocal
  let J₀ : Ideal S₀ := (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ S₀)
  let J₀' : Ideal S₀ := pBase.map (algebraMap R S₀)
  have hJ₀ : J₀ = J₀' := by
    change (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ S₀) = pBase.map (algebraMap R S₀)
    rw [← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq R R₀ S₀]
  let : Algebra R₀ (Localization.AtPrime
      (Ideal.comap (Algebra.TensorProduct.includeRight : P →ₐ[R] FpP) Qp)) :=
    Localization.AtPrime.algebraOfLiesOver pBase _
  let eFiberP := Ideal.Fiber.localizationAlgEquivQuotient pBase Qp
  have hCMQ : Module.IsMaximalCohenMacaulay (Localization.AtPrime Qp)
      (Localization.AtPrime Qp) :=
    pBase.isMaximalCohenMacaulay_localization_fiber_mvPolynomial (Fin p.variableCount) Qp
  let : Nontrivial (S₀ ⧸ J₀') :=
    eFiberP.toRingEquiv.toEquiv.nontrivial_congr.mp inferInstance
  let : IsLocalRing (S₀ ⧸ J₀') := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hCMQuot : Module.IsMaximalCohenMacaulay (S₀ ⧸ J₀') (S₀ ⧸ J₀') :=
    (@Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv
      (Localization.AtPrime Qp) (S₀ ⧸ J₀') inferInstance inferInstance
      inferInstance inferInstance eFiberP.toRingEquiv).mp hCMQ
  have hCM : Module.IsCohenMacaulayAtMaximalIdeal S₀ (S₀ ⧸ J₀) := by
    rw [hJ₀]
    exact isCohenMacaulayAtMaximalIdeal_quotient J₀' hCMQuot
  have hdimP : ringKrullDim (S₀ ⧸ J₀) = (Qp.height : WithBot ℕ∞) := by
    rw [hJ₀]
    exact ringKrullDim_eq_height_of_ringEquiv Qp eFiberP.toRingEquiv
  have hcompR : fLocal.comp (algebraMap R S₀) = algebraMap R T₀ := by
    ext x
    change fLocal (algebraMap R S₀ x) = algebraMap R T₀ x
    rw [IsScalarTower.algebraMap_apply R P S₀, Localization.localRingHom_to_map]
    have hpC : p.toRingHom (algebraMap R P x) = algebraMap R A x :=
      congrArg (fun g : R →+* A => g x) p.commutes
    rw [hpC, ← IsScalarTower.algebraMap_apply R A T₀]
  let JA : Ideal T₀ := pBase.map (algebraMap R T₀)
  have hmapJ : J₀.map fLocal = JA := by
    rw [hJ₀]
    change (pBase.map (algebraMap R S₀)).map fLocal = _
    rw [Ideal.map_map, hcompR]
  let g : S₀ →+* T₀ ⧸ JA := (Ideal.Quotient.mk JA).comp fLocal
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hfLocal
  have hker : RingHom.ker g = J₀ ⊔ I₀ := by
    change Ideal.comap fLocal (RingHom.ker (Ideal.Quotient.mk JA)) = _
    rw [Ideal.mk_ker, ← hmapJ, Ideal.comap_map_of_surjective _ hfLocal,
      ← RingHom.ker_eq_comap_bot]
  let eQuot := (Ideal.quotEquivOfEq hker.symm).trans (g.quotientKerEquivOfSurjective hg)
  let : Algebra R₀ (Localization.AtPrime
      (Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] FpA) QA)) :=
    Localization.AtPrime.algebraOfLiesOver pBase _
  let eFiberA := Ideal.Fiber.localizationAlgEquivQuotient pBase QA
  have hdimA : ringKrullDim (S₀ ⧸ (J₀ ⊔ I₀)) = (QA.height : WithBot ℕ∞) :=
    (ringKrullDim_eq_of_ringEquiv eQuot).trans
      (ringKrullDim_eq_height_of_ringEquiv QA eFiberA.toRingEquiv)
  have hI₀ : I₀ ≠ ⊤ := RingHom.ker_ne_top fLocal
  have hdepth := (ringKrullDim_fiber_le_depth_add_ringKrullDim_quotient_of_flat
    R₀ S₀ I₀ hCM).resolve_left hI₀
  change ringKrullDim (S₀ ⧸ J₀) ≤
    (Module.depth S₀ I₀ S₀ : WithBot ℕ∞) + ringKrullDim (S₀ ⧸ (J₀ ⊔ I₀)) at hdepth
  rw [hdimP, hdimA] at hdepth
  have hrMap : rP.primeCompl.map p.toRingHom = rA.primeCompl := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩ hxa
      exact hx (hrPA ▸ hxa)
    · intro ha
      obtain ⟨x, rfl⟩ := p.surjective a
      refine ⟨x, ?_, rfl⟩
      change x ∉ rP
      rw [hrPA]
      exact ha
  have hIMap : I₀ = (RingHom.ker p.toRingHom).map (algebraMap P S₀) :=
    IsLocalization.ker_map (S := S₀) T₀ p.toRingHom hrMap
  let N := ModuleCat.of S₀ (LocalizedModule rP.primeCompl (M₀ : Type u))
  have hNann : I₀ ≤ Module.annihilator S₀ N := by
    rw [hIMap, Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap P S₀ x ∈ Module.annihilator S₀ N
    rw [Module.mem_annihilator]
    intro y
    change algebraMap P S₀ x • y = 0
    rw [algebraMap_smul]
    induction y using LocalizedModule.induction_on with
    | h a t =>
      rw [LocalizedModule.smul'_mk]
      have hxa : x • a = 0 := by
        change ULift.up (p.toRingHom x * a.down) = ULift.up 0
        rw [RingHom.mem_ker.mp hx, zero_mul]
      rw [hxa, LocalizedModule.zero_mk]
  have hrLocal' : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S₀) 0).obj N)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} S₀) 0).obj (ModuleCat.of S₀ S₀)) k) :=
    (nontrivial_localized_derivedExt_congr (M := (M₀ : Type u)) rP r.asIdeal hQpcomp k).mpr
      hrLocal
  have hk : 0 ≤ k := by
    by_contra hneg
    have := subsingleton_derivedExt_of_neg N (ModuleCat.of S₀ S₀) k hneg
    exact not_nontrivial _ hrLocal'
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hk
  have hdepthle : Module.depth S₀ I₀ S₀ ≤ (j : ℕ∞) := by
    by_contra hle
    have : Subsingleton (Abelian.Ext N (ModuleCat.of S₀ S₀) j) :=
      ext_subsingleton_of_lt_depth I₀ (ModuleCat.of S₀ S₀) N
        (by simpa using hI₀) ⟨1, by simpa using hNann⟩ j (lt_of_not_ge hle)
    have := (Abelian.Ext.homAddEquiv
      (X := N) (Y := ModuleCat.of S₀ S₀) (n := j)).toEquiv.symm.subsingleton
    rw [hj] at hrLocal'
    exact not_nontrivial _ hrLocal'
  have hdimFiber' : (d : ℕ∞) + Qp.height = (p.variableCount : ℕ∞) + QA.height := by
    exact_mod_cast hdimFiber
  have hdepth' : Qp.height ≤ Module.depth S₀ I₀ S₀ + QA.height := by exact_mod_cast hdepth
  have hbound : (p.variableCount : ℕ∞) + QA.height ≤ (d + j : ℕ∞) + QA.height := by
    rw [← hdimFiber', add_assoc]
    exact add_le_add le_rfl (hdepth'.trans (add_le_add hdepthle le_rfl))
  let : IsNoetherianRing FpA := Algebra.FiniteType.isNoetherianRing K FpA
  have hnat : p.variableCount ≤ d + j := by
    exact_mod_cast (ENat.add_le_add_iff_right
      (Ideal.height_ne_top_of_isPrime (I := QA))).mp hbound
  dsimp [k] at hj
  omega

end Dualizing

end

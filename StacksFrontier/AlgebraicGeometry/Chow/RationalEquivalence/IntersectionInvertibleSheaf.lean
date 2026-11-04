module

public import Mathlib.Data.ENat.BigOperators
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeRank
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAssociatedClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.StructureSheafStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.CartierRegular.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatAtDivisor
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Sheaves.Modules.StalkTensorRing
import all StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Factorization

/-!
# Intersecting with an invertible sheaf: the zero cycle of a section

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `Y` be locally of
finite type over `S`, let `L` be an invertible `𝒪_Y`-module and let `s` be a global section of
`L`. Assume `dim_δ(Y) ≤ k + 1`, that `dim_δ(Z(s)) ≤ k`, and that multiplication by `s` is
injective on the local ring at the generic point of every `δ`-dimension `k` component of the
zero scheme `Z(s)`. Then the `k`-cycle of `Z(s)` is the sum, over the `δ`-dimension `k + 1`
irreducible components `Y_i` of `Y`, of the `k`-cycle of `Z(s|_{Y_i})` weighted by the
multiplicity of `Y_i` in the fundamental cycle `[Y]_{k + 1}`.

The computation is entirely local at a point `x` of `δ`-dimension `k`. Writing `A = 𝒪_{Y, x}`
and choosing a local generator of `L` at `x`, the section becomes a single element `f ∈ A`; the
coefficient of `[Z(s)]_k` at `x` is the length of `A ⧸ (f)`, the components of `Y` through `x`
correspond to the minimal primes of `A`, and the identity is then the quotient-ring formula of
Stacks 02QG applied to `f` in the one-dimensional local ring `A`.

## Main definitions

* `AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes` — the irreducible components of a
  scheme through a point correspond to the minimal primes of the local ring there.
* `Stacks.Divisors.zeroSchemeAffineOpenIso` — on a trivializing affine open, the zero scheme of
  a section is the spectrum of the quotient by the function cutting it out.

## Main results

* `Stacks.Chow.zeroCycle_eq_sum_components` — **Stacks 0EPI**, the componentwise identity of
  `k`-cycles.
* `Stacks.Chow.componentMultiplicity_eq_length_quotient_ker` and
  `Stacks.Chow.componentMultiplicity_eq_length_quotient_stalk` — the multiplicity of a component
  of a closed subscheme as the colength of the stalk of its ideal sheaf.
* `Stacks.Chow.ringKrullDim_stalk_le_one` — the local ring at a point of `δ`-dimension `k` of a
  scheme of `δ`-dimension at most `k + 1` has Krull dimension at most one.
* `Stacks.Chow.length_quotient_eq_sum_components` — the local form of the identity: the colength
  of the local equation is the weighted sum of the coefficients contributed by the components.

## Implementation notes

An irreducible component is given its reduced induced closed-subscheme structure through
`Scheme.IdealSheafData.vanishingIdeal`. The zero scheme of the restricted section, viewed as a
closed subscheme of the ambient scheme, is the scheme-theoretic intersection of that component
with `Z(s)`, which is the supremum of the two ideal sheaves; cycles on the components are
therefore already cycles on `Y`. The sum is expressed coefficientwise because a locally
Noetherian scheme need not have finitely many irreducible components globally — only finitely
many contribute to each coefficient, which is what makes the `finsum` finite.

The trivialization of `L` near a point is taken in the concrete shape of a `Γ(Y, U)`-linear
equivalence `Γ(L, U) ≃ₗ Γ(Y, U)`, namely `Stacks.Divisors.frameSections` of a sheaf-level
trivialization. The injectivity hypothesis of the source is the injectivity of the induced map
on module stalks; `AlgebraicGeometry.stalkLMap_unitHomEquiv_symm_apply` turns it into the
statement that the local equation is a nonzerodivisor, by identifying the stalk of the structure
sheaf as a module over itself with the local ring.

## References

* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace

universe u

namespace AlgebraicGeometry

/-! ### Lengths along a surjection and along a ring equivalence -/

/-- For a surjective ring homomorphism `f : R →+* S`, the length of `S` as an `R`-module through
`f` is the length of `R ⧸ ker f`. -/
theorem length_quotient_ker_eq_length {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    letI : Module R S := Module.compHom S f
    Module.length R (R ⧸ RingHom.ker f) = Module.length R S := by
  let : Module R S := Module.compHom S f
  let e := RingHom.quotientKerEquivOfSurjective hf
  let eL : (R ⧸ RingHom.ker f) ≃ₗ[R] S :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r z
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
        show e (algebraMap R (R ⧸ RingHom.ker f) r *
          Ideal.Quotient.mk (RingHom.ker f) a) = f r * f a
        rw [map_mul]
        simp [e, RingHom.quotientKerEquivOfSurjective_apply_mk] }
  exact eL.length_eq

/-- A ring `R` regarded as a module over itself through a homomorphism that is the identity has
the same length as any ring `S` isomorphic to it, regarded as a module over itself. -/
theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* R) (hf : f = RingHom.id R) (e : R ≃+* S) :
    @Module.length R R _ _ (Module.compHom R f) = Module.length S S := by
  let : Module R R := Module.compHom R f
  let : Algebra R S := e.toRingHom.toAlgebra
  let hlin : R ≃ₗ[R] S :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro r x
        show e (f r * x) = e r * e x
        rw [hf]
        exact e.map_mul r x }
  let : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  calc
    Module.length R R = Module.length R S := hlin.length_eq
    _ = Module.length S S :=
      Module.length_eq_of_surjective (R := S) (S := R) (M := S) e.surjective

/-- Localizing `R ⧸ (0)` at a prime gives the localization of `R` at that prime, so the two have
the same length over it. -/
theorem length_localizedModule_quotientBot {R : Type*} [CommRing R] (p : PrimeSpectrum R) :
    Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (R ⧸ (⊥ : Ideal R))) =
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) :=
  (IsLocalizedModule.mapEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (R ⧸ (⊥ : Ideal R)))
    (Algebra.linearMap R (Localization.AtPrime p.asIdeal))
    (Localization.AtPrime p.asIdeal) (AlgEquiv.quotientBot R R).toLinearEquiv).length_eq

/-- **Stacks 02QG**, in the form used for cycles. For a nonzerodivisor `a` of a one-dimensional
Noetherian local ring `R` of finite colength, the colength of `(a)` is the sum over the minimal
primes `p` of `R` of the length of `R_p` times the colength of `(a, p)`. -/
theorem natCast_length_quotient_span_eq_sum_minimalPrimes {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (a : R) (ha : IsSMulRegular R a)
    (hdim : ringKrullDim R = 1)
    (hfinite : Module.length R (R ⧸ Ideal.span {a}) ≠ ⊤) :
    ((Module.length R (R ⧸ Ideal.span {a})).toNat : ℤ) =
      ∑ᶠ p : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
            (Localization.AtPrime p.1.asIdeal)).toNat : ℤ) *
          ((Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal))).toNat : ℤ) := by
  classical
  have hfin : {p : PrimeSpectrum R | p.asIdeal ∈ minimalPrimes R}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥).preimage
      (fun p _ q _ h => PrimeSpectrum.ext h)
  let : Fintype {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R} := hfin.fintype
  have h := length_quotient_span_sup_eq_sum_minimalPrimes a ⊥
    (((AlgEquiv.quotientBot R R).toLinearEquiv.isSMulRegular_congr a).mpr ha)
    ((RingEquiv.quotientBot R).ringKrullDim.trans hdim)
  rw [sup_bot_eq, ← finsum_set_coe_eq_finsum_mem] at h
  simp_rw [length_localizedModule_quotientBot] at h
  change Module.length R (R ⧸ Ideal.span {a}) =
    ∑ᶠ p : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R},
      Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal)) *
        Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal) at h
  rw [finsum_eq_sum_of_fintype] at h ⊢
  have hterms (p : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R}) :
      Module.length R (R ⧸ (Ideal.span {a} ⊔ p.1.asIdeal)) *
        Module.length (Localization.AtPrime p.1.asIdeal)
          (Localization.AtPrime p.1.asIdeal) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hfinite
    rw [h]
    exact Finset.single_le_sum
      (f := fun q : {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R} =>
        Module.length R (R ⧸ (Ideal.span {a} ⊔ q.1.asIdeal)) *
          Module.length (Localization.AtPrime q.1.asIdeal)
            (Localization.AtPrime q.1.asIdeal))
      (fun _ _ => zero_le) (Finset.mem_univ p)
  rw [h, ENat.toNat_sum (fun p _ => hterms p), Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [ENat.toNat_mul, Nat.cast_mul, mul_comm]

/-! ### Stalks of ideal sheaves -/

/-- The stalk of a supremum of quasi-coherent ideal sheaves is the supremum of the stalks. -/
theorem IdealSheafData.stalk_sup {Y : Scheme.{u}} (I J : Y.IdealSheafData) (x : Y) :
    IdealSheafData.stalk (I ⊔ J) x =
      IdealSheafData.stalk I x ⊔ IdealSheafData.stalk J x := by
  unfold IdealSheafData.stalk
  simp [Scheme.IdealSheafData.ideal_sup, Ideal.map_sup, iSup_sup_eq]

/-- The part of a closed subscheme lying over an affine open `U` is exactly the image of the
member of `Scheme.IdealSheafData.subschemeCover` indexed by `U`. -/
theorem range_ι_preimage_eq_range_subschemeCover {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    Set.range ((I.subschemeι ⁻¹ᵁ U.1).ι) = Set.range (I.subschemeCover.f U) := by
  have : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  calc
    Set.range ((I.subschemeι ⁻¹ᵁ U.1).ι) = ↑(I.subschemeι ⁻¹ᵁ U.1) := Scheme.Opens.range_ι _
    _ = ↑(I.subschemeCover.f U).opensRange := by rw [I.opensRange_subschemeCover_map]
    _ = Set.range (I.subschemeCover.f U) := (I.subschemeCover.f U).coe_opensRange.symm

/-! ### Irreducible components and the minimal primes of a local ring -/

/-- The canonical morphism `Spec 𝒪_{X, x} ⟶ X` is an isomorphism on stalks at every prime: it
factors as the spectrum of a localization map followed by an open immersion. -/
@[ega "I 1.6.2" "special case"]
theorem isIso_stalkMap_fromSpecStalk {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap p) := by
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := X.affineCover.covers x
  let R := Γ(X, U)
  let A := X.presheaf.stalk x
  let q : PrimeSpectrum R := hU.primeIdealOf ⟨x, hxU⟩
  let g := X.presheaf.germ U x hxU
  let : Algebra R A := g.hom.toAlgebra
  let : IsLocalization.AtPrime A q.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  let e : Localization.AtPrime q.asIdeal ≃ₐ[R] A :=
    IsLocalization.algEquiv q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal) A
  let eIso := e.toRingEquiv.toCommRingCatIso
  have hSpecIso : IsIso (Spec.map eIso.hom) := (Scheme.Spec.mapIso eIso.op).isIso_hom
  let pS : Spec A := p
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.AtPrime q.asIdeal)))).stalkMap
      (PrimeSpectrum.comap e.toRingHom p)) :=
    AlgebraicGeometry.isIso_SpecMap_stakMap_localization (CommRingCat.of R)
      q.asIdeal.primeCompl (PrimeSpectrum.comap e.toRingHom p)
  have he : IsIso ((Spec.map eIso.hom).stalkMap pS) :=
    ((AlgebraicGeometry.isIso_iff_isIso_stalkMap (Spec.map eIso.hom)).mp hSpecIso).2 pS
  have hfac : CommRingCat.ofHom (algebraMap R A) =
      CommRingCat.ofHom (algebraMap R (Localization.AtPrime q.asIdeal)) ≫
        CommRingCat.ofHom e.toRingHom := by
    ext r
    simp [e]
  have hEq : Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map eIso.hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime q.asIdeal))) := by
    rw [← Spec.map_comp, hfac]
    rfl
  have hfirst : IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R A))).stalkMap pS) := by
    rw [hEq, Scheme.Hom.stalkMap_comp]
    exact IsIso.comp_isIso' hloc he
  have hgerm : g = CommRingCat.ofHom (algebraMap R A) := by
    ext r
    rfl
  have hfirst' : IsIso ((Spec.map g).stalkMap pS) := by rwa [hgerm]
  have hfromSpecIso : ∀ z : Spec R, IsIso (hU.fromSpec.stalkMap z) :=
    (IsOpenImmersion.iff_isIso_stalkMap).mp hU.isOpenImmersion_fromSpec |>.2
  show IsIso ((X.fromSpecStalk x).stalkMap pS)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.stalkMap_comp]
  exact IsIso.comp_isIso' (hfromSpecIso _) hfirst'

/-- The stalk at `x` of the vanishing ideal of an irreducible component through `x` is a minimal
prime of the local ring at `x`: on an affine chart it is the localization of the prime of the
component, which is a minimal prime of the ring of sections. -/
theorem stalk_vanishingIdeal_mem_minimalPrimes {Y : Scheme.{u}} (x : Y)
    (W : irreducibleComponents Y) (hxW : x ∈ (W : Set Y)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
        ⟨(W : Set Y), isClosed_of_mem_irreducibleComponents W.1 W.2⟩) x ∈
      minimalPrimes (Y.presheaf.stalk x) := by
  classical
  let U : Y.affineOpens :=
    ⟨(Y.affineCover.f (Y.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
  have hxU : x ∈ (U : Set Y) := Y.affineCover.covers x
  have hU := U.2
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  let : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let W' : irreducibleComponents (PrimeSpectrum Γ(Y, U)) :=
    ⟨hU.fromSpec ⁻¹' (W : Set Y),
      preimage_mem_irreducibleComponents W.2 hU.fromSpec.isOpenEmbedding
        ⟨hU.fromSpec p, by rw [hp]; exact hxW, p, rfl⟩⟩
  let q : Ideal Γ(Y, U) := PrimeSpectrum.vanishingIdeal (W' : Set (PrimeSpectrum Γ(Y, U)))
  have hq : q.IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp W'.2.1
  have hqp : q ≤ p.asIdeal := fun r hr =>
    (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr p
      (by change hU.fromSpec p ∈ (W : Set Y); rw [hp]; exact hxW)
  let A := Y.presheaf.stalk x
  let g := Y.presheaf.germ U x hxU
  let : Algebra Γ(Y, U) A := g.hom.toAlgebra
  let : IsLocalization.AtPrime A p.asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have hdisj : Disjoint (p.asIdeal.primeCompl : Set Γ(Y, U)) (q : Set Γ(Y, U)) :=
    Set.disjoint_left.mpr fun r hrp hrq => hrp (hqp hrq)
  have hqmin : q ∈ (⊥ : Ideal Γ(Y, U)).minimalPrimes := by
    rw [PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
    have hclosed : IsClosed (W' : Set (PrimeSpectrum Γ(Y, U))) :=
      isClosed_of_mem_irreducibleComponents W'.1 W'.2
    simpa only [hclosed.closure_eq] using W'.2
  have hmapmin : Ideal.map g.hom q ∈ (⊥ : Ideal A).minimalPrimes := by
    have hbot : Ideal.map g.hom (⊥ : Ideal Γ(Y, U)) = ⊥ := by simp
    rw [← hbot]
    show Ideal.map (algebraMap Γ(Y, U) A) q ∈
      (Ideal.map (algebraMap Γ(Y, U) A) (⊥ : Ideal Γ(Y, U))).minimalPrimes
    rw [IsLocalization.minimalPrimes_map p.asIdeal.primeCompl A (⊥ : Ideal Γ(Y, U))]
    show Ideal.under Γ(Y, U) (Ideal.map (algebraMap Γ(Y, U) A) q) ∈
      (⊥ : Ideal Γ(Y, U)).minimalPrimes
    rw [IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl A hq hdisj]
    exact hqmin
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hxU]
  exact hmapmin

/-- Every irreducible component through `x` is the closure of the image of a minimal prime of the
local ring at `x` under `Spec 𝒪_{X, x} ⟶ X`. -/
theorem exists_mem_minimalPrimes_fromSpecStalk_eq {X : Scheme.{u}} (x : X)
    (W : irreducibleComponents X) (hxW : x ∈ (W : Set X)) :
    ∃ p : PrimeSpectrum (X.presheaf.stalk x),
      p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x) ∧
        X.fromSpecStalk x p = (genericPoints.ofComponent W : X) := by
  have hη := genericPoints.isGenericPoint_ofComponent W
  have hrange : (genericPoints.ofComponent W : X) ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hη.specializes hxW
  obtain ⟨p, hp⟩ := hrange
  refine ⟨p, PrimeSpectrum.isMin_iff.mp ?_, hp⟩
  intro q hqp
  have hspec : X.fromSpecStalk x q ⤳ (genericPoints.ofComponent W : X) := by
    rw [← hp]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hqp).map (X.fromSpecStalk x).continuous
  have hsub : (W : Set X) ⊆ closure ({X.fromSpecStalk x q} : Set X) := by
    rw [← hη]
    exact hspec.closure_subset
  have heq : X.fromSpecStalk x q = (genericPoints.ofComponent W : X) := by
    have hcl : closure ({X.fromSpecStalk x q} : Set X) = W :=
      subset_antisymm (W.2.2 isIrreducible_singleton.closure hsub) hsub
    exact (show IsGenericPoint (X.fromSpecStalk x q) (W : Set X) from hcl).eq hη
  have hqp' : q = p := (X.fromSpecStalk x).isEmbedding.injective (heq.trans hp.symm)
  exact le_of_eq hqp'.symm

/-- Every minimal prime of the local ring at `x` maps to the generic point of an irreducible
component through `x`. -/
theorem exists_irreducibleComponents_fromSpecStalk_eq {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)) :
    ∃ W : irreducibleComponents X, x ∈ (W : Set X) ∧
      X.fromSpecStalk x p = (genericPoints.ofComponent W : X) := by
  have hpx : X.fromSpecStalk x p ⤳ x := by
    have h : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({X.fromSpecStalk x p} : Set X)) isIrreducible_singleton.closure
  let W' : irreducibleComponents X := ⟨W, hW⟩
  have hxW : x ∈ (W' : Set X) := hsub hpx.mem_closure
  obtain ⟨q, hq, heq⟩ := exists_mem_minimalPrimes_fromSpecStalk_eq x W' hxW
  have hqp : q ≤ p := by
    refine (PrimeSpectrum.le_iff_specializes q p).mpr ?_
    refine (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp ?_
    rw [heq]
    exact (genericPoints.isGenericPoint_ofComponent W').specializes (hsub (subset_closure rfl))
  have hEq : p = q := le_antisymm ((PrimeSpectrum.isMin_iff.mpr hp) hqp) hqp
  exact ⟨W', hxW, hEq ▸ heq⟩

/-- **The irreducible components of a scheme through a point correspond to the minimal primes of
its local ring there.** A component is sent to the minimal prime whose image under
`Spec 𝒪_{X, x} ⟶ X` is its generic point. -/
def irreducibleComponentsEquivMinimalPrimes {X : Scheme.{u}} (x : X) :
    {W : irreducibleComponents X // x ∈ (W : Set X)} ≃
      {p : PrimeSpectrum (X.presheaf.stalk x) //
        p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} := by
  classical
  let g : {W : irreducibleComponents X // x ∈ (W : Set X)} →
      {p : PrimeSpectrum (X.presheaf.stalk x) //
        p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} := fun W =>
    ⟨(exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose,
      (exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose_spec.1⟩
  have hg (W) : X.fromSpecStalk x (g W).1 = (genericPoints.ofComponent W.1 : X) :=
    (exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose_spec.2
  refine Equiv.ofBijective g ⟨?_, ?_⟩
  · intro W V h
    have hη : (genericPoints.ofComponent W.1 : X) = (genericPoints.ofComponent V.1 : X) :=
      (hg W).symm.trans ((congrArg (fun p : {p : PrimeSpectrum (X.presheaf.stalk x) //
        p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x)} =>
          X.fromSpecStalk x p.1) h).trans (hg V))
    refine Subtype.ext (Subtype.ext ?_)
    exact (genericPoints.isGenericPoint_ofComponent W.1).symm.trans
      ((congrArg (fun z : X => closure ({z} : Set X)) hη).trans
        (genericPoints.isGenericPoint_ofComponent V.1))
  · intro p
    obtain ⟨W, hxW, hpW⟩ := exists_irreducibleComponents_fromSpecStalk_eq x p.1 p.2
    exact ⟨⟨W, hxW⟩, Subtype.ext
      ((X.fromSpecStalk x).isEmbedding.injective ((hg ⟨W, hxW⟩).trans hpW.symm))⟩

/-- The minimal prime attached to an irreducible component by
`AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes` maps to its generic point. -/
theorem fromSpecStalk_irreducibleComponentsEquivMinimalPrimes {X : Scheme.{u}} (x : X)
    (W : {W : irreducibleComponents X // x ∈ (W : Set X)}) :
    X.fromSpecStalk x (irreducibleComponentsEquivMinimalPrimes x W).1 =
      (genericPoints.ofComponent W.1 : X) :=
  (exists_mem_minimalPrimes_fromSpecStalk_eq x W.1 W.2).choose_spec.2

/-- A minimal prime of the local ring at `x` whose image is a point of the component `W` is the
stalk at `x` of the vanishing ideal of `W`. -/
theorem stalk_vanishingIdeal_eq_of_mem_minimalPrimes {X : Scheme.{u}} (x : X)
    (W : irreducibleComponents X) (hxW : x ∈ (W : Set X))
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : p.asIdeal ∈ minimalPrimes (X.presheaf.stalk x))
    (hpW : X.fromSpecStalk x p ∈ (W : Set X)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal
      ⟨W.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩) x = p.asIdeal := by
  have hmin := stalk_vanishingIdeal_mem_minimalPrimes x W hxW
  apply le_antisymm ?_ (hp.2 ⟨hmin.1.1, bot_le⟩ ?_)
  all_goals
    let U : X.affineOpens :=
      ⟨(X.affineCover.f (X.affineCover.idx x)).opensRange, isAffineOpen_opensRange _⟩
    have hxU : x ∈ U.1 := X.affineCover.covers x
    rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hxU]
    refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
    refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha
      (PrimeSpectrum.comap (X.presheaf.germ U.1 x hxU).hom p) ?_
    show U.2.fromSpecStalk hxU p ∈ (W : Set X)
    rw [U.2.fromSpecStalk_eq_fromSpecStalk hxU]
    exact hpW

/-! ### The structure sheaf as a module over itself, on stalks -/

/-- The identification of the stalk of the structure sheaf, read as a module over itself, with
the local ring sends the germ of a function to itself. -/
theorem structureSheafStalkLinearEquiv_germ {X : Scheme.{u}} (x : X) (U : X.Opens) (hx : x ∈ U)
    (a : Γ(X, U)) :
    structureSheafStalkLinearEquiv X x
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (structureSheafModule X).val.presheaf U x hx a) =
      (X.presheaf.germ U x hx).hom a := by
  show SemilinearStalk.commStalkRingEquiv X.presheaf x
    (LocallyFreeRank.unitStalkLEquiv (X.presheaf ⋙ forget₂ CommRingCat RingCat) x
      (TopCat.Presheaf.germ
        (PresheafOfModules.unit (X.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf U x hx a))
    = _
  rw [LocallyFreeRank.unitStalkLEquiv_germ, commStalkRingEquiv_germ]

/-- Multiplication by a global section `s` of a module `L`, read on stalks, is multiplication of
the germ of `s` by the scalar corresponding to a germ of the structure sheaf. -/
theorem stalkLMap_unitHomEquiv_symm_apply {X : Scheme.{u}} (L : X.Modules)
    (s : L.sections) (x : X)
    (r : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      (structureSheafModule X).val.presheaf x) :
    LocallyFreeRank.stalkLMap (L.unitHomEquiv.symm s).val x r =
      structureSheafStalkLinearEquiv X x r •
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf ⊤ x trivial
          (s.eval (.op ⊤)) := by
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) L.val.presheaf x) :=
    L.val.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier x
  obtain ⟨U, hx, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (C := AddCommGrpCat.{u}) (structureSheafModule X).val.presheaf r
  rw [structureSheafStalkLinearEquiv_germ x U hx a,
    ← commStalkRingEquiv_germ X.presheaf x U hx a]
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (L.unitHomEquiv.symm s).val)
      (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).obj
          (SheafOfModules.unit X.ringCatSheaf).val) U x hx a) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (L.unitHomEquiv.symm s).val) a]
  let aR : ToType (X.ringCatSheaf.obj.obj (.op U)) := a
  show TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf U x hx
      (aR • s.eval (.op U)) = _
  rw [PresheafOfModules.germ_ringCat_smul L.val x U hx aR (s.eval (.op U))]
  have hs := s.property (homOfLE (show U ≤ ⊤ from le_top)).op
  change L.val.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s.eval (.op ⊤)) =
    s.eval (.op U) at hs
  rw [← hs, TopCat.Presheaf.germ_res_apply L.val.presheaf
    (homOfLE (show U ≤ ⊤ from le_top)) x hx (s.eval (.op ⊤))]
  exact (SheafOfModules.commStalk_smul_eq X.presheaf x L.val
    (TopCat.Presheaf.germ (C := RingCat.{u})
      (X.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u}) U x hx a)
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf ⊤ x trivial
      (s.eval (.op ⊤)))).symm

end AlgebraicGeometry

namespace Stacks.Divisors

/-! ### The zero scheme on a trivializing affine open -/

/-- The stalk at a point of a trivializing affine open of the ideal of the zero scheme of a
section is generated by the germ of the function cutting the zero scheme out there. -/
theorem stalk_zeroScheme_eq_span_germ {Y : Scheme.{u}} (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (U : Y.affineOpens) (e : Γ(L, U.1) ≃ₗ[Γ(Y, U.1)] Γ(Y, U.1))
    (a : Γ(Y, U.1)) (he : e (L.presheaf.map (homOfLE le_top).op s) = a)
    (x : Y) (hx : x ∈ U.1) :
    IdealSheafData.stalk (zeroScheme Y L s) x =
      Ideal.span {(Y.presheaf.germ U.1 x hx).hom a} := by
  rw [AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ x U hx,
    zeroScheme_ideal_of_trivialization Y L s U e a he, Ideal.map_span, Set.image_singleton]

/-- Taking spectra of the quotients by two equal ideals is compatible with the quotient maps:
the identification of the two quotients composed with one quotient map is the other. -/
theorem specMapIso_quotientMk {R : Type u} [CommRing R] (I J : Ideal R) (h : I = J) :
    (Scheme.Spec.mapIso (eqToIso (congrArg (fun K : Ideal R =>
        op (CommRingCat.of (R ⧸ K))) h))).hom ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  show Scheme.Spec.map (eqToHom (congrArg (fun K : Ideal R =>
      op (CommRingCat.of (R ⧸ K))) h)) ≫
      Scheme.Spec.map (op (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
    Scheme.Spec.map (op (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  rw [← Functor.map_comp]
  congr 1
  cases h
  simp

/-- On a trivializing affine open `U`, the part of the zero scheme of a section lying over `U` is
the spectrum of the quotient of `Γ(X, U)` by the function cutting the zero scheme out. -/
def zeroSchemeAffineOpenIso (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (U : X.affineOpens) (e : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))
    (a : Γ(X, U.1)) (he : e (L.presheaf.map (homOfLE le_top).op s) = a) :
    ((zeroScheme X L s).subschemeι ⁻¹ᵁ U.1).toScheme ≅
      Spec (.of (Γ(X, U.1) ⧸ Ideal.span ({a} : Set Γ(X, U.1)))) :=
  haveI : IsOpenImmersion ((zeroScheme X L s).subschemeCover.f U) :=
    (zeroScheme X L s).subschemeCover.map_prop U
  IsOpenImmersion.isoOfRangeEq (((zeroScheme X L s).subschemeι ⁻¹ᵁ U.1).ι)
      ((zeroScheme X L s).subschemeCover.f U)
      (AlgebraicGeometry.range_ι_preimage_eq_range_subschemeCover _ U) ≪≫
    Scheme.Spec.mapIso (eqToIso (congrArg (fun K : Ideal Γ(X, U.1) =>
      op (CommRingCat.of (Γ(X, U.1) ⧸ K)))
      (zeroScheme_ideal_of_trivialization X L s U e a he)))

/-- The identification of `Stacks.Divisors.zeroSchemeAffineOpenIso` is compatible with the
canonical closed immersion of the zero scheme into the ambient scheme. -/
theorem zeroSchemeAffineOpenIso_comp (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (U : X.affineOpens) (e : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1))
    (a : Γ(X, U.1)) (he : e (L.presheaf.map (homOfLE le_top).op s) = a) :
    (zeroSchemeAffineOpenIso X L s U e a he).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span ({a} : Set Γ(X, U.1))))) ≫ U.2.fromSpec =
      ((zeroScheme X L s).subschemeι ⁻¹ᵁ U.1).ι ≫ (zeroScheme X L s).subschemeι := by
  set I := zeroScheme X L s with hIdef
  have hI : I.ideal U = Ideal.span ({a} : Set Γ(X, U.1)) :=
    zeroScheme_ideal_of_trivialization X L s U e a he
  have : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  have hrange := AlgebraicGeometry.range_ι_preimage_eq_range_subschemeCover I U
  have hfac : (IsOpenImmersion.isoOfRangeEq ((I.subschemeι ⁻¹ᵁ U.1).ι)
      (I.subschemeCover.f U) hrange).hom ≫ I.subschemeCover.f U =
      (I.subschemeι ⁻¹ᵁ U.1).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac
      ((I.subschemeι ⁻¹ᵁ U.1).ι) (I.subschemeCover.f U) hrange
  have hq := specMapIso_quotientMk (I.ideal U) (Ideal.span ({a} : Set Γ(X, U.1))) hI
  have hkey : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) ≫ U.2.fromSpec =
      I.subschemeCover.f U ≫ I.subschemeι :=
    ((I.subschemeCover_map_subschemeι U).trans (I.glueDataObjι_ι U)).symm
  have hhom : (zeroSchemeAffineOpenIso X L s U e a he).hom =
      (IsOpenImmersion.isoOfRangeEq ((I.subschemeι ⁻¹ᵁ U.1).ι)
          (I.subschemeCover.f U) hrange).hom ≫
        (Scheme.Spec.mapIso (eqToIso (congrArg (fun K : Ideal Γ(X, U.1) =>
          op (CommRingCat.of (Γ(X, U.1) ⧸ K))) hI))).hom := rfl
  have h₁ : (Scheme.Spec.mapIso (eqToIso (congrArg (fun K : Ideal Γ(X, U.1) =>
          op (CommRingCat.of (Γ(X, U.1) ⧸ K))) hI))).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span ({a} : Set Γ(X, U.1))))) ≫ U.2.fromSpec =
      I.subschemeCover.f U ≫ I.subschemeι :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m => m ≫ U.2.fromSpec) hq).trans hkey)
  rw [hhom]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m =>
    (IsOpenImmersion.isoOfRangeEq ((I.subschemeι ⁻¹ᵁ U.1).ι)
      (I.subschemeCover.f U) hrange).hom ≫ m) h₁).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ I.subschemeι) hfac)

end Stacks.Divisors

namespace Stacks.Chow

/-! ### Delta-dimension bounds -/

/-- The delta-dimension of an irreducible component of `X` is bounded by the delta-dimension of
`X`, of which it is one of the terms of the defining supremum. -/
theorem deltaDimension_le_of_mem_irreducibleComponents (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {k : ℤ}
    (hX : schemeDeltaDimension C f ≤ (k : EInt)) (W : irreducibleComponents X) :
    deltaDimension C f ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ ≤ k := by
  rw [schemeDeltaDimension_eq_iSup] at hX
  exact WithBotTop.coe_le_coe.mp
    ((le_iSup (fun V : irreducibleComponents X =>
      (deltaDimension C f
        ⟨V.1, V.2.1, isClosed_of_mem_irreducibleComponents V.1 V.2⟩ : EInt)) W).trans hX)

/-- A closed subscheme of a scheme of delta-dimension at most `k` has delta-dimension at most
`k`. -/
theorem schemeDeltaDimension_le_of_isClosedImmersion (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] {k : ℤ} (hX : schemeDeltaDimension C f ≤ (k : EInt)) :
    schemeDeltaDimension C (i ≫ f) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun W => ?_
  let Wc : IrreducibleCloseds Z :=
    ⟨(W : Set Z), W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩
  have hη : IsGenericPoint Wc.isIrreducible.genericPoint (W : Set Z) :=
    Wc.isIrreducible.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents (W : Set Z) W.2)
  have hdim : relativeDimension C.dimensionFunction f (i Wc.isIrreducible.genericPoint) ≤ k := by
    have h := relativeDimension_le_of_schemeDeltaDimension_le C f (𝟙 X) (k := k)
      (by simpa using hX) (i Wc.isIrreducible.genericPoint)
    simpa using h
  have hδ : deltaDimension C (i ≫ f) Wc =
      relativeDimension C.dimensionFunction f (i Wc.isIrreducible.genericPoint) := by
    rw [deltaDimension_eq_of_isGenericPoint C (i ≫ f) Wc _ hη,
      relativeDimension_comp_closedImmersion C.dimensionFunction i f]
  show (deltaDimension C (i ≫ f) Wc : EInt) ≤ (k : EInt)
  rw [hδ]
  exact WithBotTop.coe_le_coe.mpr hdim

/-- On a scheme of delta-dimension at most `k + 1`, the local ring at a point of relative
dimension `k` has Krull dimension at most one: no point can specialize to it through more than
one step, because the delta-dimension drops strictly along specializations. -/
theorem ringKrullDim_stalk_le_one (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {k : ℤ}
    (hX : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  have hupper (y : X) : deltaDimensionFunction C f y ≤ k + 1 := by
    rw [deltaDimensionFunction_apply]
    have h := relativeDimension_le_of_schemeDeltaDimension_le C f (𝟙 X) (k := k + 1)
      (by simpa using hX) y
    simpa using h
  have hx' : deltaDimensionFunction C f x = k := by
    rw [deltaDimensionFunction_apply]; exact hx
  have hcoh : Order.coheight x ≤ (1 : ℕ∞) := by
    refine (Order.coheight_le_coe_iff (x := x) (n := 1)).2 fun y hxy => ?_
    have hlt := (deltaDimensionFunction C f).strictAnti_specializes
      (Scheme.le_iff_specializes.mp hxy.le) (Ne.symm hxy.ne)
    have hy : deltaDimensionFunction C f y = k + 1 := by
      have := hupper y
      omega
    have hymax : IsMax y := by
      intro z hyz
      by_cases hzy : z = y
      · exact hzy.le
      · have hlt' := (deltaDimensionFunction C f).strictAnti_specializes
          (Scheme.le_iff_specializes.mp hyz) hzy
        have := hupper z
        omega
    rw [Order.coheight_eq_zero.mpr hymax]
    norm_num
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
  exact_mod_cast hcoh

/-- An irreducible component through a point `x` of relative dimension `k` has delta-dimension
`k + 1` as soon as the local equation at `x` is a nonzerodivisor lying in the maximal ideal: the
generic point of the component is then a proper specialization of `x`. -/
theorem deltaDimension_eq_succ_of_isSMulRegular (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {k : ℤ}
    (hX : schemeDeltaDimension C f ≤ (k + 1 : EInt))
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k)
    (a : X.presheaf.stalk x) (ha : IsSMulRegular (X.presheaf.stalk x) a)
    (ham : a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (W : irreducibleComponents X) (hxW : x ∈ (W : Set X)) :
    deltaDimension C f ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1 := by
  obtain ⟨p, hp, hpW⟩ := exists_mem_minimalPrimes_fromSpecStalk_eq x W hxW
  have hηne : (genericPoints.ofComponent W : X) ≠ x := by
    intro heq
    have hpclosed : p = IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (X.fromSpecStalk x).isEmbedding.injective
        ((hpW.trans heq).trans Scheme.fromSpecStalk_closedPoint.symm)
    refine ha.notMem_of_mem_minimalPrimes (p := p.asIdeal)
      (by rw [Module.annihilator_eq_bot.mpr inferInstance]; exact hp) ?_
    exact hpclosed ▸ ham
  have hlt := (deltaDimensionFunction C f).strictAnti_specializes
    ((genericPoints.isGenericPoint_ofComponent W).specializes hxW) hηne
  rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply, hx] at hlt
  have hdim := deltaDimension_le_of_mem_irreducibleComponents C f (k := k + 1) hX W
  rw [deltaDimension_eq_of_isGenericPoint C f _ _
    (genericPoints.isGenericPoint_ofComponent W)] at hdim ⊢
  omega

/-! ### Component multiplicities as colengths -/

/-- **Stacks 02QU.** The multiplicity of an irreducible component of a closed subscheme is the
colength of the kernel of the stalk map at the component's generic point. -/
theorem componentMultiplicity_eq_length_quotient_ker {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (ξ : genericPoints Z) :
    componentMultiplicity i ξ =
      (Module.length (X.presheaf.stalk (i ξ.1))
        (X.presheaf.stalk (i ξ.1) ⧸ RingHom.ker (i.stalkMap ξ.1).hom)).toNat := by
  classical
  dsimp only [componentMultiplicity]
  rw [length_quotient_ker_eq_length _ (i.stalkMap_surjective ξ.1)]

/-- **Stacks 02QU.** The multiplicity of an irreducible component of a closed subscheme is the
colength of the stalk of its ideal sheaf at the component's generic point. -/
theorem componentMultiplicity_eq_length_quotient_stalk {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (ξ : genericPoints Z) (U : X.Opens) (hU : IsAffineOpen U)
    (hx : i ξ.1 ∈ U) :
    componentMultiplicity i ξ =
      (Module.length (X.presheaf.stalk (i ξ.1))
        (X.presheaf.stalk (i ξ.1) ⧸ IdealSheafData.stalk i.ker (i ξ.1))).toNat := by
  classical
  rw [componentMultiplicity_eq_length_quotient_ker,
    stalk_ker_eq_of_affine_target i ξ.1 U hU hx]

/-- The multiplicity of an irreducible component of `X`, as a component of `X` itself, is the
length of the localization of the local ring at the corresponding minimal prime. -/
theorem componentMultiplicity_id_eq_length_localization {X : Scheme.{u}} (x : X)
    (W : irreducibleComponents X) (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = (genericPoints.ofComponent W : X)) :
    componentMultiplicity (𝟙 X) (genericPoints.ofComponent W) =
      (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)).toNat := by
  let η := (genericPoints.ofComponent W : X)
  let A := X.presheaf.stalk η
  have : IsIso ((X.fromSpecStalk x).stalkMap p) := isIso_stalkMap_fromSpecStalk x p
  let e : A ≃+* Localization.AtPrime p.asIdeal :=
    ((((X.presheaf.stalkCongr (Inseparable.of_eq hp)).symm).commRingCatIsoToRingEquiv).trans
        (asIso ((X.fromSpecStalk x).stalkMap p)).commRingCatIsoToRingEquiv).trans
      (Spec.stalkIso (CommRingCat.of (X.presheaf.stalk x)) p).commRingCatIsoToRingEquiv
  let fId := ((𝟙 X : X ⟶ X).stalkMap η).hom
  have hId : fId = RingHom.id A := by
    dsimp only [fId, A]
    simp only [Scheme.Hom.stalkMap_id]
    rfl
  have hlen := length_self_eq_of_ringEquiv fId hId e
  change @Module.length A A _ _ (Module.compHom A fId) = _ at hlen
  unfold componentMultiplicity
  show ((@Module.length A A _ _ (Module.compHom A fId)).toNat : ℤ) = _
  exact_mod_cast congrArg ENat.toNat hlen

/-! ### Local description of the two cycles -/

/-- Under a delta-dimension bound on a closed subscheme `Z`, a point of `Z` of relative dimension
`k` is the generic point of a component of `Z`. -/
private theorem exists_genericPoints_of_relativeDimension_eq (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ Y) [IsClosedImmersion i]
    {k : ℤ} (hZ : schemeDeltaDimension C (i ≫ f) ≤ (k : EInt)) (ξ : Z)
    (hξ : relativeDimension C.dimensionFunction f (i ξ) = k) :
    ∃ η : genericPoints Z, η.1 = ξ := by
  obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C f i hZ ξ hξ
  exact ⟨⟨ξ, show closure {ξ} ∈ irreducibleComponents Z from hW ▸ W.2⟩, rfl⟩

/-- At a point of relative dimension `k` lying in the supports of both `I` and `D`, the
coefficient of the `k`-cycle of the scheme-theoretic intersection `I ⊔ D` is the colength of the
sum of the two stalk ideals. -/
theorem cycleAssociatedToClosedSubscheme_sup_apply_eq_length (C : ChowSituation.{u})
    {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f] (I D : Y.IdealSheafData) {k : ℤ}
    (hD : schemeDeltaDimension C (D.subschemeι ≫ f) ≤ (k : EInt))
    (x : Y) (hxI : x ∈ I.support) (hxD : x ∈ D.support)
    (hxdim : relativeDimension C.dimensionFunction f x = k)
    (U : Y.affineOpens) (hxU : x ∈ U.1) (a : Γ(Y, U.1))
    (haD : IdealSheafData.stalk D x = Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a})
    (p : PrimeSpectrum (Y.presheaf.stalk x)) (haI : IdealSheafData.stalk I x = p.asIdeal) :
    (cycleAssociatedToClosedSubscheme C f ((I ⊔ D).subschemeι) k).1 x =
      (Module.length (Y.presheaf.stalk x)
        (Y.presheaf.stalk x ⧸
          (Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a} ⊔ p.asIdeal))).toNat := by
  classical
  have hxE : x ∈ (I ⊔ D).support := by
    rw [Scheme.IdealSheafData.support_sup]; exact ⟨hxI, hxD⟩
  have hxrange : x ∈ Set.range (I ⊔ D).subschemeι := by
    change x ∈ ((I ⊔ D).support : Set Y) at hxE
    simpa only [Scheme.IdealSheafData.range_subschemeι] using hxE
  have hE : schemeDeltaDimension C ((I ⊔ D).subschemeι ≫ f) ≤ (k : EInt) := by
    have h := schemeDeltaDimension_le_of_isClosedImmersion C (D.subschemeι ≫ f)
      (Scheme.IdealSheafData.inclusion (le_sup_right : D ≤ I ⊔ D)) (k := k) hD
    simpa only [← Category.assoc,
      Scheme.IdealSheafData.inclusion_subschemeι (le_sup_right : D ≤ I ⊔ D)] using h
  obtain ⟨y, hy⟩ := hxrange
  subst hy
  obtain ⟨ξ, rfl⟩ := exists_genericPoints_of_relativeDimension_eq C f (I ⊔ D).subschemeι hE y hxdim
  have hcycle := cycleAssociatedToClosedSubscheme_apply C f (I ⊔ D).subschemeι k ξ hxdim
  have hmult := componentMultiplicity_eq_length_quotient_stalk (I ⊔ D).subschemeι ξ U.1 U.2 hxU
  rw [Scheme.IdealSheafData.ker_subschemeι, IdealSheafData.stalk_sup, haI, haD] at hmult
  rw [hcycle, hmult, sup_comm p.asIdeal]

/-- The coefficient of the fundamental cycle `[Y]_{k + 1}` at the generic point of a component of
delta-dimension `k + 1` is the length of the localization of the local ring at `x` at the
corresponding minimal prime. -/
theorem cycleAssociatedToClosedSubscheme_id_apply_eq_length (C : ChowSituation.{u})
    {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (W : irreducibleComponents Y)
    (hW : deltaDimension C f
      ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1)
    (x : Y) (p : PrimeSpectrum (Y.presheaf.stalk x))
    (hp : Y.fromSpecStalk x p = (genericPoints.ofComponent W : Y)) :
    (cycleAssociatedToClosedSubscheme C f (𝟙 Y) (k + 1)).1
        (genericPoints.ofComponent W).1 =
      (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)).toNat := by
  have hdim : relativeDimension C.dimensionFunction f (genericPoints.ofComponent W).1 = k + 1 := by
    rw [← deltaDimension_eq_of_isGenericPoint C f
      ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩
      (genericPoints.ofComponent W).1 (genericPoints.isGenericPoint_ofComponent W)]
    exact hW
  show (cycleAssociatedToClosedSubscheme C f (𝟙 Y) (k + 1)).1
    ((𝟙 Y) (genericPoints.ofComponent W).1) = _
  rw [cycleAssociatedToClosedSubscheme_apply C f (𝟙 Y) (k + 1)
    (genericPoints.ofComponent W) hdim]
  exact componentMultiplicity_id_eq_length_localization x W p hp

/-- **The local form of Stacks 0EPI.** At a point `x` of relative dimension `k` of a scheme of
delta-dimension at most `k + 1`, where the ideal of `D` is generated by a nonzerodivisor `a` of
finite colength, the colength of `(a)` is the sum over the components of delta-dimension `k + 1`
of their multiplicity in the fundamental cycle times the coefficient at `x` of the `k`-cycle of
their intersection with `D`. -/
theorem length_quotient_eq_sum_components (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ C.S) [LocallyOfFiniteType f] (D : Y.IdealSheafData) (k : ℤ)
    (hY : schemeDeltaDimension C f ≤ (k + 1 : EInt))
    (hD : schemeDeltaDimension C (D.subschemeι ≫ f) ≤ (k : EInt))
    (x : Y) (hxD : x ∈ D.support)
    (hxdim : relativeDimension C.dimensionFunction f x = k)
    (U : Y.affineOpens) (hxU : x ∈ U.1) (a : Γ(Y, U.1))
    (haD : IdealSheafData.stalk D x = Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a})
    (ha : IsSMulRegular (Y.presheaf.stalk x) ((Y.presheaf.germ U.1 x hxU).hom a))
    (ham : (Y.presheaf.germ U.1 x hxU).hom a ∈
      IsLocalRing.maximalIdeal (Y.presheaf.stalk x))
    (hfinite : Module.length (Y.presheaf.stalk x)
      (Y.presheaf.stalk x ⧸ Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a}) ≠ ⊤) :
    ((Module.length (Y.presheaf.stalk x)
        (Y.presheaf.stalk x ⧸
          Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a})).toNat : ℤ) =
      ∑ᶠ W : {W : irreducibleComponents Y //
          deltaDimension C f
            ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1},
        (cycleAssociatedToClosedSubscheme C f (𝟙 Y) (k + 1)).1 W.1.2.1.genericPoint *
          (cycleAssociatedToClosedSubscheme C f
            ((Scheme.IdealSheafData.vanishingIdeal
              ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ D).subschemeι)
            k).1 x := by
  classical
  let R := Y.presheaf.stalk x
  let b : R := (Y.presheaf.germ U.1 x hxU).hom a
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hproper : Ideal.span {b} ≠ (⊤ : Ideal R) :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham))
  have : Nontrivial (R ⧸ Ideal.span {b}) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hb : b ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_left.mpr fun r hr =>
    ha (by simpa only [smul_eq_mul, mul_zero] using hr)
  have hdim : ringKrullDim R = 1 := by
    refine le_antisymm (ringKrullDim_stalk_le_one C f (k := k) hY x hxdim) ?_
    exact (show (1 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {b}) + 1 by
      simpa only [zero_add, add_comm] using add_le_add_right
        (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.span {b})) 1).trans
      (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hb)
  rw [natCast_length_quotient_span_eq_sum_minimalPrimes b ha hdim hfinite]
  let T := {W : irreducibleComponents Y //
    deltaDimension C f
      ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1}
  let F : T → ℤ := fun W =>
    (cycleAssociatedToClosedSubscheme C f (𝟙 Y) (k + 1)).1 W.1.2.1.genericPoint *
      (cycleAssociatedToClosedSubscheme C f
        ((Scheme.IdealSheafData.vanishingIdeal
          ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ D).subschemeι) k).1 x
  let B := {W : T // x ∈ (W.1 : Set Y)}
  let e : B ≃ {W : irreducibleComponents Y // x ∈ (W : Set Y)} :=
    { toFun := fun W => ⟨W.1.1, W.2⟩
      invFun := fun W => ⟨⟨W.1, deltaDimension_eq_succ_of_isSMulRegular C f (k := k) hY x
        hxdim b ha ham W.1 W.2⟩, W.2⟩
      left_inv := by intro W; rfl
      right_inv := by intro W; rfl }
  have hrestrict : (∑ᶠ W : T, F W) = ∑ᶠ W : B, F W.1 := by
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun W => ?_
    by_cases hxW : x ∈ (W.1 : Set Y)
    · simp only [hxW, finsum_true]
    · simp only [hxW, finsum_false]
      show _ * _ = 0
      refine mul_eq_zero_of_right _ ?_
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ _ _ _ ?_
      rintro ⟨ξ, hξx, _⟩
      refine hxW ?_
      have hx : x ∈ (Scheme.IdealSheafData.vanishingIdeal
          ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ D).support := by
        show x ∈ (_ : Set Y)
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨ξ.1, hξx⟩
      rw [Scheme.IdealSheafData.support_sup] at hx
      have hxI := hx.1
      change x ∈ (_ : Set Y) at hxI
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hxI
      exact hxI
  show _ = ∑ᶠ W : T, F W
  rw [hrestrict]
  let E := e.trans (irreducibleComponentsEquivMinimalPrimes x)
  refine (finsum_eq_of_bijective E E.bijective ?_).symm
  intro W
  let p := (E W).1
  have hp : p.asIdeal ∈ minimalPrimes R := (E W).2
  have hpW : Y.fromSpecStalk x p = (genericPoints.ofComponent W.1.1 : Y) :=
    fromSpecStalk_irreducibleComponentsEquivMinimalPrimes x (e W)
  have hI := stalk_vanishingIdeal_eq_of_mem_minimalPrimes x W.1.1 W.2 p hp
    (hpW ▸ (genericPoints.isGenericPoint_ofComponent W.1.1).mem)
  have hcoef := cycleAssociatedToClosedSubscheme_sup_apply_eq_length C f
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨W.1.1.1, isClosed_of_mem_irreducibleComponents W.1.1.1 W.1.1.2⟩)
    D (k := k) hD x (by
      show x ∈ (_ : Set Y)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact W.2)
    hxD hxdim U hxU a haD p hI
  have hmult := cycleAssociatedToClosedSubscheme_id_apply_eq_length C f k W.1.1 W.1.2 x p hpW
  show _ * _ = _ * _
  rw [hcoef]
  exact congrArg (fun z : ℤ => z * _) hmult

/-! ### The cycle identity -/

/-- **Stacks 0EPI.** Let `(S, δ)` be the base situation of chapter 42, let `Y` be locally of
finite type over `S`, let `L` be an invertible `𝒪_Y`-module and `s` a global section of `L`.
Assume `dim_δ(Y) ≤ k + 1`, `dim_δ(Z(s)) ≤ k`, and that multiplication by `s` is injective on
the stalk at the generic point of every component of `Z(s)` of delta-dimension `k`. Then the
`k`-cycle of `Z(s)` is the sum of the `k`-cycles of the zero schemes of the restrictions of `s`
to the components of `Y` of delta-dimension `k + 1`, weighted by their multiplicities in the
fundamental cycle `[Y]_{k + 1}`. -/
@[stacks 0EPI]
theorem zeroCycle_eq_sum_components (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ C.S) [LocallyOfFiniteType f] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : L.sections) (k : ℤ)
    (hY : schemeDeltaDimension C f ≤ (k + 1 : EInt))
    (hD : schemeDeltaDimension C
      ((Stacks.Divisors.zeroScheme Y L (s.eval (op ⊤))).subschemeι ≫ f) ≤ (k : EInt))
    (hs : ∀ ξ : genericPoints (Stacks.Divisors.zeroScheme Y L (s.eval (op ⊤))).subscheme,
      relativeDimension C.dimensionFunction f
        ((Stacks.Divisors.zeroScheme Y L (s.eval (op ⊤))).subschemeι ξ.1) = k →
      Function.Injective (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
          ((Stacks.Divisors.zeroScheme Y L (s.eval (op ⊤))).subschemeι ξ.1)).map
          ((Scheme.Modules.toPresheaf Y).map (L.unitHomEquiv.symm s))))) :
    let D := Stacks.Divisors.zeroScheme Y L (s.eval (op ⊤))
    ∀ x : Y,
      (cycleAssociatedToClosedSubscheme C f D.subschemeι k).1 x =
        ∑ᶠ W : {W : irreducibleComponents Y //
            deltaDimension C f
              ⟨W.1, W.2.1, isClosed_of_mem_irreducibleComponents W.1 W.2⟩ = k + 1},
          (cycleAssociatedToClosedSubscheme C f (𝟙 Y) (k + 1)).1 W.1.2.1.genericPoint *
            (cycleAssociatedToClosedSubscheme C f
              ((Scheme.IdealSheafData.vanishingIdeal
                ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ ⊔ D).subschemeι)
              k).1 x := by
  classical
  dsimp only
  intro x
  set D : Y.IdealSheafData := Stacks.Divisors.zeroScheme Y L (s.eval (op ⊤)) with hDdef
  by_cases hxD : ∃ ξ : genericPoints D.subscheme,
      D.subschemeι ξ.1 = x ∧ relativeDimension C.dimensionFunction f x = k
  · obtain ⟨ξ, hξx, hξdim⟩ := hxD
    have hξdim' : relativeDimension C.dimensionFunction f (D.subschemeι ξ.1) = k := by
      simpa [hξx] using hξdim
    have hinjective := hs ξ hξdim'
    obtain ⟨U, eU, hxU, -⟩ := Stacks.Divisors.exists_affine_frame_subset Y L x ⊤ trivial
    set eΓ := Stacks.Divisors.frameSections Y L eU with heΓ
    set a : Γ(Y, U.1) := eΓ (L.presheaf.map (homOfLE le_top).op (s.eval (op ⊤))) with hadef
    have hDstalk : IdealSheafData.stalk D x =
        Ideal.span {(Y.presheaf.germ U.1 x hxU).hom a} :=
      Stacks.Divisors.stalk_zeroScheme_eq_span_germ L (s.eval (op ⊤)) U eΓ a rfl x hxU
    have hkerD : RingHom.ker ((D.subschemeι.stalkMap ξ.1).hom) =
        Ideal.span {(Y.presheaf.germ U.1 (D.subschemeι ξ.1)
          (by simpa [hξx] using hxU)).hom a} := by
      have hker := stalk_ker_eq_of_affine_target D.subschemeι ξ.1 U.1 U.2
        (by simpa [hξx] using hxU)
      have hker' : RingHom.ker ((D.subschemeι.stalkMap ξ.1).hom) =
          IdealSheafData.stalk D (D.subschemeι ξ.1) := by
        simpa [hDdef] using hker.symm
      cases hξx
      exact hker'.trans hDstalk
    have hleft := cycleAssociatedToClosedSubscheme_apply C f D.subschemeι k ξ hξdim'
    rw [hξx] at hleft
    rw [hleft, componentMultiplicity_eq_length_quotient_ker, hkerD]
    cases hξx
    set x₀ : Y := D.subschemeι ξ.1 with hx₀
    have hstalkinj : Function.Injective
        (LocallyFreeRank.stalkLMap (L.unitHomEquiv.symm s).val x₀) := hinjective
    have hinjmul : Function.Injective (fun r : Y.presheaf.stalk x₀ =>
        LocallyFreeRank.stalkLMap (L.unitHomEquiv.symm s).val x₀
          ((structureSheafStalkLinearEquiv Y x₀).symm r)) := fun r t hrt =>
      (structureSheafStalkLinearEquiv Y x₀).symm.injective (hstalkinj hrt)
    have hsU : L.presheaf.map (homOfLE le_top).op (s.eval (op ⊤)) = a • eΓ.symm 1 := by
      refine eΓ.injective ?_
      calc
        eΓ (L.presheaf.map (homOfLE le_top).op (s.eval (op ⊤))) = a := rfl
        _ = a • eΓ (eΓ.symm 1) := by simp
        _ = eΓ (a • eΓ.symm 1) := by rw [map_smul]
    have hsx : TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf ⊤ x₀ trivial
        (s.eval (op ⊤)) =
        (Y.presheaf.germ U.1 x₀ hxU).hom a •
          TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf U.1 x₀ hxU
            (eΓ.symm 1) := by
      rw [← TopCat.Presheaf.germ_res_apply L.val.presheaf
        (homOfLE (show U.1 ≤ ⊤ from le_top)) x₀ hxU (s.eval (op ⊤))]
      show TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) L.val.presheaf U.1 x₀ hxU
        (L.presheaf.map (homOfLE le_top).op (s.eval (op ⊤))) = _
      rw [hsU]
      exact PresheafOfModules.germ_smul L.val x₀ U.1 hxU a (eΓ.symm 1)
    have haRegular : IsSMulRegular (Y.presheaf.stalk x₀)
        ((Y.presheaf.germ U.1 x₀ hxU).hom a) := by
      refine IsSMulRegular.of_right_eq_zero_of_smul ?_
      intro r hr
      refine hinjmul ?_
      dsimp only
      rw [stalkLMap_unitHomEquiv_symm_apply L s x₀
          ((structureSheafStalkLinearEquiv Y x₀).symm r),
        stalkLMap_unitHomEquiv_symm_apply L s x₀
          ((structureSheafStalkLinearEquiv Y x₀).symm (0 : Y.presheaf.stalk x₀)),
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hsx, smul_smul, zero_smul,
        show r * (Y.presheaf.germ U.1 x₀ hxU).hom a = 0 from (mul_comm _ _).trans hr, zero_smul]
    have ham : (Y.presheaf.germ U.1 x₀ hxU).hom a ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x₀) := by
      refine IsLocalRing.le_maximalIdeal
        (RingHom.ker_ne_top (D.subschemeι.stalkMap ξ.1).hom) ?_
      rw [hkerD]
      exact Ideal.subset_span (Set.mem_singleton _)
    have hfin := isFiniteLength_stalk_of_isGenericPoint_component C f D.subschemeι
      (genericPoints.component ξ).1 (genericPoints.component ξ).2 ξ.1
      (genericPoints.isGenericPoint ξ)
    let : Module (Y.presheaf.stalk x₀) (D.subscheme.presheaf.stalk ξ.1) :=
      Module.compHom _ (D.subschemeι.stalkMap ξ.1).hom
    have hfinite : Module.length (Y.presheaf.stalk x₀)
        (Y.presheaf.stalk x₀ ⧸
          Ideal.span {(Y.presheaf.germ U.1 x₀ hxU).hom a}) ≠ ⊤ := by
      rw [← hkerD, length_quotient_ker_eq_length _ (D.subschemeι.stalkMap_surjective ξ.1)]
      exact Module.length_ne_top_iff.mpr hfin
    exact length_quotient_eq_sum_components C f D k hY hD x₀
      (by
        show x₀ ∈ (D.support : Set Y)
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨ξ.1, rfl⟩)
      hξdim U hxU a hDstalk haRegular ham hfinite
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero C f D.subschemeι k x hxD,
      finsum_eq_zero_of_forall_eq_zero]
    intro W
    set I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
      ⟨W.1.1, isClosed_of_mem_irreducibleComponents W.1.1 W.1.2⟩ with hIdef
    have hterm : (cycleAssociatedToClosedSubscheme C f ((I ⊔ D).subschemeι) k).1 x = 0 := by
      refine cycleAssociatedToClosedSubscheme_apply_eq_zero C f (I ⊔ D).subschemeι k x ?_
      intro hx
      obtain ⟨ξ, hξx, hξdim⟩ := hx
      have hm : Scheme.IdealSheafData.inclusion (le_sup_right : D ≤ I ⊔ D) ≫ D.subschemeι =
          (I ⊔ D).subschemeι :=
        Scheme.IdealSheafData.inclusion_subschemeι (le_sup_right : D ≤ I ⊔ D)
      have hη : D.subschemeι (Scheme.IdealSheafData.inclusion
          (le_sup_right : D ≤ I ⊔ D) ξ.1) = x := by
        rw [← hξx, ← Scheme.Hom.comp_apply, hm]
      obtain ⟨η, hη'⟩ := exists_genericPoints_of_relativeDimension_eq C f D.subschemeι hD
        (Scheme.IdealSheafData.inclusion (le_sup_right : D ≤ I ⊔ D) ξ.1) (hη ▸ hξdim)
      exact hxD ⟨η, hη' ▸ hη, hξdim⟩
    simp [hterm]

end Stacks.Chow

end

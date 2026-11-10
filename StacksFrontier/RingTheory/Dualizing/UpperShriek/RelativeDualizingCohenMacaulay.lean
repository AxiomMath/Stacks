module

public import StacksFrontier.RingTheory.Dualizing.ExtCohenMacaulaySerre
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FibreDimensionBound
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingVanishing
public import StacksFrontier.RingTheory.DimensionFormulaMinimalPrimes
public import StacksFrontier.RingTheory.CohenMacaulay.FlatLocalHom
public import StacksFrontier.RingTheory.CohenMacaulay.Localization
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.Serre.Surjection
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.Depth.FlatLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative dualizing complex over a Cohen–Macaulay base

Let `φ : R → A` be a finite type homomorphism of Noetherian rings, let `𝔭 ⊂ R` be a prime, and let
`ω^•_{A/R} = φ^!(R)` be the relative dualizing complex.  This file proves [Stacks, Tag 0E9R]:
if `R_𝔭` is Cohen–Macaulay and `trdeg_{κ(R ∩ 𝔮)} κ(𝔮) ≤ r` for every minimal prime `𝔮 ⊂ A`, then

* `H^i(ω^•_{A/R})_𝔭 ≠ 0 ⟹ -r ≤ i`, and
* `H^{-r}(ω^•_{A/R})_𝔭` satisfies `(S₂)` as an `A_𝔭`-module.

Here `(-)_𝔭` is the localization at the image of `R ∖ 𝔭`, and `ω^•_{A/R}` is computed from an
arbitrary polynomial presentation `P = R[x_1, …, x_n] → A`.

## Main results

* `Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex` — the vanishing.
* `Dualizing.propertySkModule_localizedModule_homology_relativeDualizingComplex` — the `(S₂)`
  clause.
* `Dualizing.isMaximalCohenMacaulay_and_le_depth_ker_localRingHom` — the depth estimate: at a
  prime `𝔮 ⊂ A` with prime `𝔯 ⊂ P` below it, `P_𝔯` is Cohen–Macaulay and the kernel `I` of
  `P_𝔯 → A_𝔮` has `depth_I(P_𝔯) ≥ n - r`.

## Implementation notes

The source reduces to a complete Cohen–Macaulay local base with a dualizing complex and reads the
duality formula [Stacks, Tag 0E9L] against a normalized dualizing complex of `A_𝔪`.  The argument
here avoids dualizing complexes.  At a prime `𝔮 ⊂ A` lying over a prime contained in `𝔭`, the
identification `ω^•_{A/R} = RHom_P(A, P)[n]` gives

`H^i(ω^•_{A/R})_𝔮 = Ext^{i+n}_{P_𝔯}(A_𝔯, P_𝔯)` .

The local ring `P_𝔯` is flat over the Cohen–Macaulay ring `R_{𝔮 ∩ R}` with regular closed fibre,
hence Cohen–Macaulay [Stacks, Tag 045J], so `depth_I(P_𝔯) = dim(P_𝔯) - dim(A_𝔮)`
[Stacks, Tag 0BUX]; the dimension formula for the polynomial ring and the inequality
[Stacks, Tag 0BAE] for `A` (in its ring form, through the minimal primes of `A`) bound this below
by `n - r`.  Below the depth the `Ext` vanishes by Rees' theorem [Stacks, Tag 0AVZ]; in degree
`c ≤ depth_I(P_𝔯)` an `Ext^c` out of a module killed by `I` into a Cohen–Macaulay module is
`(S₂)`, by induction on `c` along a regular element of `I`, the case `c = 0` being
[Stacks, Tag 0AV6] (`Dualizing.min_two_le_moduleDepth_ext_of_le_depth`).

## References

* [Stacks Project, Tag 0E9R](https://stacks.math.columbia.edu/tag/0E9R)
* [Stacks Project, Tag 0E9P](https://stacks.math.columbia.edu/tag/0E9P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### Auxiliary facts -/

/-- Cohomology in degree `i` of a shift by `n` is cohomology in degree `i + n`. -/
noncomputable def homologyShiftObjIso
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : DerivedCategory C) (i n : ℤ) :
    ((DerivedCategory.homologyFunctor C i).obj
      ((shiftFunctor (DerivedCategory C) n).obj K)) ≅
      ((DerivedCategory.homologyFunctor C (i + n)).obj K) := by
  rw [← DerivedCategory.shift_homologyFunctor C i,
    ← DerivedCategory.shift_homologyFunctor C (i + n)]
  exact ((DerivedCategory.homologyFunctor C 0).shiftIso n i (i + n) (by omega)).app K

/-- A module killed by localizing at every prime disjoint from `S` is killed by localizing at
`S`: an element surviving the localization at `S` has an annihilator disjoint from `S`, hence
contained in a prime disjoint from `S`, and the element then survives at that prime. -/
private theorem subsingleton_localizedModule_of_forall_prime_disjoint {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] (S : Submonoid A)
    (h : ∀ 𝔮 : PrimeSpectrum A, Disjoint (𝔮.asIdeal : Set A) (S : Set A) →
      Subsingleton (LocalizedModule 𝔮.asIdeal.primeCompl M)) :
    Subsingleton (LocalizedModule S M) := by
  rw [LocalizedModule.subsingleton_iff]
  intro m
  by_contra hm
  push Not at hm
  have hker : ∀ a : A, a ∈ LinearMap.ker (LinearMap.toSpanSingleton A M m) ↔ a • m = 0 := by
    intro a
    simp [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
  have hdisj : Disjoint ((LinearMap.ker (LinearMap.toSpanSingleton A M m) : Ideal A) : Set A)
      (S : Set A) := by
    rw [Set.disjoint_left]
    intro a ha haS
    exact hm a haS ((hker a).mp ha)
  obtain ⟨𝔮, h𝔮, hle, hd⟩ := Ideal.exists_le_prime_disjoint _ S hdisj
  have hsub := h ⟨𝔮, h𝔮⟩ hd
  rw [LocalizedModule.subsingleton_iff] at hsub
  obtain ⟨t, ht, htm⟩ := hsub m
  exact ht (hle ((hker t).mpr htm))

/-! ### Serre's condition after localizing twice -/

/-- Localizing a finite module first at a submonoid `T` and then at a prime `Q` of `T⁻¹A` is
localizing it once at the contraction `q` of `Q`: depth and the dimension of the support over the
two local rings agree. -/
theorem moduleDepth_and_moduleSupportDim_localizedModule_atPrime_localizedModule
    {A : Type u} [CommRing A] (T : Submonoid A) (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (Q : Ideal (Localization T)) [Q.IsPrime] :
    moduleDepth (Localization.AtPrime Q) (LocalizedModule.AtPrime Q (LocalizedModule T M)) =
        moduleDepth (Localization.AtPrime (Q.comap (algebraMap A (Localization T))))
          (LocalizedModule.AtPrime (Q.comap (algebraMap A (Localization T))) M) ∧
      moduleSupportDim (Localization.AtPrime Q)
          (LocalizedModule.AtPrime Q (LocalizedModule T M)) =
        moduleSupportDim (Localization.AtPrime (Q.comap (algebraMap A (Localization T))))
          (LocalizedModule.AtPrime (Q.comap (algebraMap A (Localization T))) M) := by
  let B := Localization T
  let L := LocalizedModule T M
  let P := Localization.AtPrime Q
  let N := LocalizedModule.AtPrime Q L
  let q := Q.comap (algebraMap A B)
  let Qq := Localization.AtPrime q
  let g : M →ₗ[A] N :=
    ((LocalizedModule.mkLinearMap Q.primeCompl L).restrictScalars A).comp
      (LocalizedModule.mkLinearMap T M)
  have hg : IsBaseChange P g :=
    (LocalizedModule.isBaseChange T M).comp
      (LocalizedModule.isBaseChange Q.primeCompl L)
  have : IsLocalizedModule q.primeCompl g :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl P g).mpr hg
  let er : Qq ≃ₐ[A] P :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization T Q
  let _ : Algebra Qq P := er.toRingHom.toAlgebra
  let _ : IsScalarTower A Qq P :=
    IsScalarTower.of_algebraMap_eq' (by ext r; exact (er.commutes r).symm)
  let _ : Module Qq N := Module.compHom N (algebraMap Qq P)
  let _ : IsScalarTower A Qq N := IsScalarTower.of_algebraMap_smul fun r n => by
    change algebraMap Qq P (algebraMap A Qq r) • n = r • n
    rw [← IsScalarTower.algebraMap_apply A Qq P, IsScalarTower.algebraMap_smul]
  let _ : IsScalarTower Qq P N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let em : LocalizedModule.AtPrime q M ≃ₗ[Qq] N :=
    (IsLocalizedModule.iso q.primeCompl g).extendScalarsOfIsLocalization q.primeCompl Qq
  have hsurj : Function.Surjective (algebraMap Qq P) := er.surjective
  refine ⟨?_, ?_⟩
  · rw [moduleDepth_eq_of_linearEquiv em, moduleDepth_eq_of_surjective_algebraMap hsurj N]
  · rw [moduleSupportDim_eq_of_linearEquiv em, moduleSupportDim_eq_of_surjective_algebraMap hsurj N]

/-- **Serre's condition for a localization, from the local conditions.**  If a finite `A`-module
`M` satisfies the local form of `(Sₖ)` at every prime of `A` disjoint from `T`, then `T⁻¹M`
satisfies `(Sₖ)` over `T⁻¹A`. -/
theorem propertySkModule_localizedModule_of_forall {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] (k : ℕ)
    (h : ∀ (q : Ideal A) [q.IsPrime], Disjoint (T : Set A) (q : Set A) →
      min (k : ℕ∞) ((moduleSupportDim (Localization.AtPrime q)
          (LocalizedModule.AtPrime q M)).unbotD 0) ≤
        moduleDepth (Localization.AtPrime q) (LocalizedModule.AtPrime q M)) :
    PropertySkModule (Localization T) (LocalizedModule T M) k := by
  intro Q _
  obtain ⟨hd, hs⟩ := moduleDepth_and_moduleSupportDim_localizedModule_atPrime_localizedModule T M Q
  rw [hd, hs]
  refine h _ ?_
  rw [Set.disjoint_left]
  intro a haT haq
  have hunit : IsUnit (algebraMap A (Localization T) a) := IsLocalization.map_units _ ⟨a, haT⟩
  exact (Ideal.IsPrime.ne_top inferInstance) (Ideal.eq_top_of_isUnit_mem Q haq hunit)

/-! ### The residue field of a point of a fibre -/

open scoped TensorProduct in
/-- The structure map `κ(𝔭) → κ(Q)` at a prime `Q` of the fibre `κ(𝔭) ⊗_R S`, read on `R`, is the
structure map of the fibre followed by its residue map. -/
theorem algebraMap_residueField_fiber_apply {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (𝔭 : Ideal R) [𝔭.IsPrime] (Q : Ideal (𝔭.Fiber S)) [Q.IsPrime] (x : R) :
    letI : Algebra 𝔭.ResidueField Q.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q)
    algebraMap 𝔭.ResidueField Q.ResidueField (algebraMap R 𝔭.ResidueField x) =
      algebraMap (𝔭.Fiber S) Q.ResidueField (algebraMap R (𝔭.Fiber S) x) := by
  let : Algebra 𝔭.ResidueField Q.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q)
  change IsLocalRing.residue _ (algebraMap 𝔭.ResidueField (Localization.AtPrime Q)
      (algebraMap R 𝔭.ResidueField x)) =
    IsLocalRing.residue _ (algebraMap (𝔭.Fiber S) (Localization.AtPrime Q)
      (algebraMap R (𝔭.Fiber S) x))
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

open scoped TensorProduct in
/-- **The residue field of a point of a fibre is the residue field of its image.**  Let `Q` be a
prime of the fibre `κ(𝔭) ⊗_R S` and `q ⊂ S` its contraction.  Then `κ(q) → κ(Q)` is an
isomorphism of `κ(𝔭)`-algebras, so the two have the same transcendence degree over `κ(𝔭)`. -/
theorem trdeg_residueField_comap_includeRight_eq {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (𝔭 : Ideal R) [𝔭.IsPrime] (Q : Ideal (𝔭.Fiber S)) [Q.IsPrime]
    [(Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] 𝔭.Fiber S)).LiesOver 𝔭] :
    letI := Ideal.ResidueField.algebraOfLiesOver 𝔭
      (Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] 𝔭.Fiber S))
    letI : Algebra 𝔭.ResidueField Q.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q)
    Algebra.trdeg 𝔭.ResidueField
        (Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] 𝔭.Fiber S)).ResidueField =
      Algebra.trdeg 𝔭.ResidueField Q.ResidueField := by
  let iR : S →ₐ[R] 𝔭.Fiber S := Algebra.TensorProduct.includeRight
  let q := Q.comap iR
  let := Ideal.ResidueField.algebraOfLiesOver 𝔭 q
  let : Algebra 𝔭.ResidueField Q.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q)
  let φ : q.ResidueField →+* Q.ResidueField := Ideal.ResidueField.map q Q iR.toRingHom rfl
  have h1 := algebraMap_residueField_fiber_apply (S := S) 𝔭 Q
  have : IsScalarTower 𝔭.ResidueField (𝔭.Fiber S) Q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine Ideal.ResidueField.ringHom_ext ?_
    ext x
    change algebraMap 𝔭.ResidueField Q.ResidueField (algebraMap R 𝔭.ResidueField x) =
      algebraMap (𝔭.Fiber S) Q.ResidueField
        (algebraMap 𝔭.ResidueField (𝔭.Fiber S) (algebraMap R 𝔭.ResidueField x))
    rw [h1, ← IsScalarTower.algebraMap_apply R 𝔭.ResidueField (𝔭.Fiber S)]
  have hφ : ∀ y : S, φ (algebraMap S q.ResidueField y) =
      algebraMap (𝔭.Fiber S) Q.ResidueField (iR y) := fun y =>
    Ideal.ResidueField.map_algebraMap q Q iR.toRingHom rfl y
  have hcomm : ∀ a : 𝔭.ResidueField,
      φ (algebraMap 𝔭.ResidueField q.ResidueField a) =
        algebraMap 𝔭.ResidueField Q.ResidueField a := by
    intro a
    have h := Ideal.ResidueField.ringHom_ext (I := 𝔭)
      (f := φ.comp (algebraMap 𝔭.ResidueField q.ResidueField))
      (g := algebraMap 𝔭.ResidueField Q.ResidueField) (by
        ext x
        change φ (algebraMap 𝔭.ResidueField q.ResidueField (algebraMap R _ x)) =
          algebraMap 𝔭.ResidueField Q.ResidueField (algebraMap R _ x)
        have h2 : algebraMap 𝔭.ResidueField q.ResidueField (algebraMap R 𝔭.ResidueField x) =
            algebraMap S q.ResidueField (algebraMap R S x) :=
          Ideal.ResidueField.map_algebraMap 𝔭 q (algebraMap R S) Ideal.LiesOver.over x
        rw [h2, hφ, h1]
        congr 1
        exact iR.commutes x)
    exact congrArg (fun f => f a) h
  have hsurj : Function.Surjective φ := by
    have hrange : ∀ w : 𝔭.Fiber S, algebraMap (𝔭.Fiber S) Q.ResidueField w ∈ φ.fieldRange := by
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul a s =>
        have hw : (a ⊗ₜ[R] s : 𝔭.Fiber S) =
            algebraMap 𝔭.ResidueField (𝔭.Fiber S) a * iR s := by
          change a ⊗ₜ[R] s = (a ⊗ₜ[R] (1 : S)) * ((1 : 𝔭.ResidueField) ⊗ₜ[R] s)
          simp
        rw [hw, map_mul, ← IsScalarTower.algebraMap_apply]
        exact Subfield.mul_mem _ ⟨_, hcomm a⟩ ⟨algebraMap S q.ResidueField s, hφ s⟩
      | add x y hx hy => rw [map_add]; exact Subfield.add_mem _ hx hy
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝔭.Fiber S ⧸ Q) z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := hrange x
    have hy := hrange y
    rw [IsScalarTower.algebraMap_apply (𝔭.Fiber S) (𝔭.Fiber S ⧸ Q) Q.ResidueField] at hx hy
    exact Subfield.div_mem _ hx hy
  let e : q.ResidueField ≃+* Q.ResidueField :=
    RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  exact Algebra.trdeg_eq_of_ringEquiv (RingEquiv.refl _) e hcomm

/-! ### The depth estimate -/

/-- **The depth estimate behind [Stacks, Tag 0E9R].**  Let `R → A` be a finite type homomorphism
of Noetherian rings presented by `P = R[x_1, …, x_n] → A`, let `𝔮 ⊂ A` be a prime, `𝔯 ⊂ P` the
prime below it and `I₀` the kernel of `P_𝔯 → A_𝔮`.  If `R_{𝔮 ∩ R}` is Cohen--Macaulay and
`trdeg_{κ(R ∩ 𝔮')} κ(𝔮') ≤ r` at every minimal prime `𝔮' ⊆ 𝔮` of `A`, then `P_𝔯` is
Cohen--Macaulay and

`depth_{I₀}(P_𝔯) ≥ n - r` .

The local ring `P_𝔯` is Cohen--Macaulay because it is flat over the Cohen--Macaulay ring
`R_{𝔮 ∩ R}` with a regular, hence Cohen--Macaulay, closed fibre [Stacks, Tag 045J].  Then
`depth_{I₀}(P_𝔯) = dim(P_𝔯) - dim(A_𝔮)` [Stacks, Tag 0BUX]; the flat dimension formula gives
`dim(P_𝔯) = dim(R_{𝔮 ∩ R}) + n - t` with `t = trdeg_{κ(𝔮 ∩ R)} κ(𝔮)`, and the dimension formula
[Stacks, Tag 0BAE] gives `dim(A_𝔮) + t ≤ dim(R_{𝔮 ∩ R}) + r`. -/
theorem isMaximalCohenMacaulay_and_le_depth_ker_localRingHom
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hCMR : Module.IsMaximalCohenMacaulay (Localization.AtPrime (q.under R))
      (Localization.AtPrime (q.under R)))
    (r : ℕ)
    (hr : ∀ (q' : Ideal A) [q'.IsPrime], q' ∈ minimalPrimes A → q' ≤ q →
      (Ideal.underResidueTrdeg R q' : ℕ∞) ≤ r)
    (rP : Ideal p.Poly) [rP.IsPrime] (hrP : rP = q.comap p.toRingHom) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime rP) (Localization.AtPrime rP) ∧
      (p.variableCount : ℕ∞) ≤
        Module.depth (Localization.AtPrime rP)
          (RingHom.ker (Localization.localRingHom rP q p.toRingHom hrP))
          (Localization.AtPrime rP) + r := by
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  let P := p.Poly
  let pBase : Ideal R := q.under R
  have hrUnder : rP.under R = pBase := by
    rw [hrP]
    change Ideal.comap (MvPolynomial.C : R →+* P) (Ideal.comap p.toRingHom q) = _
    rw [Ideal.comap_comap, p.commutes]
  obtain ⟨Qp, hQp, hQpcomp⟩ := Ideal.Fiber.exists_comap_includeRight_eq rP pBase hrUnder
  subst hQpcomp
  let K := pBase.ResidueField
  let FpP := pBase.Fiber P
  let ePoly : FpP ≃ₐ[K] MvPolynomial (Fin p.variableCount) K :=
    MvPolynomial.algebraTensorAlgEquiv R K
  set rP := Ideal.comap (Algebra.TensorProduct.includeRight : P →ₐ[R] FpP) Qp with hrPdef
  let R₀ := Localization.AtPrime pBase
  let S₀ := Localization.AtPrime rP
  let T₀ := Localization.AtPrime q
  let : rP.LiesOver pBase := ⟨hrUnder.symm⟩
  let : Algebra R₀ S₀ := Localization.AtPrime.algebraOfLiesOver pBase rP
  let : IsScalarTower R R₀ S₀ := inferInstance
  let fLocal : S₀ →+* T₀ := Localization.localRingHom rP q p.toRingHom hrP
  have hfLocal : Function.Surjective fLocal :=
    Localization.surjective_localRingHom p.toRingHom p.surjective rP q hrP
  let I₀ : Ideal S₀ := RingHom.ker fLocal
  let J₀ : Ideal S₀ := (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ S₀)
  let J₀' : Ideal S₀ := pBase.map (algebraMap R S₀)
  have hJ₀ : J₀ = J₀' := by
    change (IsLocalRing.maximalIdeal R₀).map (algebraMap R₀ S₀) = pBase.map (algebraMap R S₀)
    rw [← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq R R₀ S₀]
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
  have hCMfib : Module.IsCohenMacaulayAtMaximalIdeal S₀ (S₀ ⧸ J₀) := by
    rw [hJ₀]
    exact isCohenMacaulayAtMaximalIdeal_quotient J₀' hCMQuot
  have hdimP : ringKrullDim (S₀ ⧸ J₀) = (Qp.height : WithBot ℕ∞) := by
    rw [hJ₀]
    exact ringKrullDim_eq_height_of_ringEquiv Qp eFiberP.toRingEquiv
  -- `P_𝔯` is Cohen--Macaulay
  have hCMS : Module.IsMaximalCohenMacaulay S₀ S₀ := by
    refine (Module.isMaximalCohenMacaulay_self_iff_of_flat R₀ S₀).mpr ⟨hCMR, ?_⟩
    unfold Module.IsCohenMacaulayAtMaximalIdeal at hCMfib
    rw [hCMfib, Module.supportDim_quotient_eq_ringKrullDim]
  refine ⟨hCMS, ?_⟩
  -- `depth_{I₀}(P_𝔯) + dim(A_𝔮) = dim(P_𝔯)`
  have hI₀ : I₀ ≠ ⊤ := RingHom.ker_ne_top fLocal
  have hCMS' : Module.IsCohenMacaulayAtMaximalIdeal S₀ S₀ :=
    Eq.trans hCMS (Module.supportDim_self_eq_ringKrullDim S₀).symm
  have h0BUX := supportDim_quotient_add_depth_eq_supportDim I₀ hI₀ hCMS'
  have hquot : Module.supportDim S₀ (S₀ ⧸ I₀ • (⊤ : Submodule S₀ S₀)) =
      (q.height : WithBot ℕ∞) := by
    rw [Module.supportDim_eq_of_equiv (Submodule.quotEquivOfEq _ (I₀ : Submodule S₀ S₀)
      (by simp)), Module.supportDim_quotient_eq_ringKrullDim,
      ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hfLocal),
      IsLocalization.AtPrime.ringKrullDim_eq_height q T₀]
  rw [hquot, Module.supportDim_self_eq_ringKrullDim,
    IsLocalization.AtPrime.ringKrullDim_eq_height rP S₀] at h0BUX
  -- `dim(P_𝔯) = dim(R_{𝔮 ∩ R}) + dim(fibre)`
  have hflat := Stacks.FlatLocalDimension.ringKrullDim_eq_add_ringKrullDim_closedFibre_of_flat
    (R := R₀) (S := S₀)
  change ringKrullDim S₀ = ringKrullDim R₀ + ringKrullDim (S₀ ⧸ J₀) at hflat
  rw [hdimP, IsLocalization.AtPrime.ringKrullDim_eq_height rP S₀,
    IsLocalization.AtPrime.ringKrullDim_eq_height pBase R₀] at hflat
  -- the fibre `κ(𝔭)[x_1, …, x_n]` at `Qp`: `ht(Qp) + trdeg_{κ(𝔭)} κ(Qp) = n`
  have : Algebra.FiniteType K FpP := Algebra.FiniteType.equiv inferInstance ePoly.symm
  have : IsNoetherianRing FpP := isNoetherianRing_of_ringEquiv _ ePoly.symm.toRingEquiv
  have hloc := PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField K (S := FpP)
    ⟨Qp, hQp⟩
  have h00P2 := PrimeSpectrum.localKrullDim_add_height_comap_eq_natCard_add_height K
    ePoly.symm.toAlgHom ePoly.symm.surjective ⟨Qp, hQp⟩
  have hht : (PrimeSpectrum.comap ePoly.symm.toAlgHom.toRingHom ⟨Qp, hQp⟩).asIdeal.height =
      Qp.height := RingEquiv.height_comap ePoly.symm.toRingEquiv Qp
  rw [hloc, hht, Nat.card_fin] at h00P2
  have hQpfin : Qp.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← WithBot.coe_add] at h00P2
  let : Algebra K Qp.ResidueField := IsLocalRing.ResidueField.algebra (Localization.AtPrime Qp)
  have hT : Qp.height + Cardinal.toENat (Algebra.trdeg K Qp.ResidueField) = p.variableCount :=
    ENat.add_left_injective_of_ne_top hQpfin (WithBot.coe_injective h00P2)
  -- the residue field extensions at `Qp`, at `𝔯` and at `𝔮` have one transcendence degree
  have hFI := trdeg_residueField_comap_includeRight_eq pBase Qp
  have : (Ideal.comap p.toRingHom q).LiesOver pBase := hrP ▸ (inferInstance : rP.LiesOver pBase)
  have hsurjT := resfield_trdeg_comap_eq (A := R) (C := P) (A' := A) p.toRingHom p.surjective
    p.commutes pBase q
  have hcongr := Ideal.toNat_trdeg_residue_congr pBase pBase rP (Ideal.comap p.toRingHom q)
    rfl hrP
  -- the dimension formula at `𝔮`
  have h0BAE := height_add_trdeg_residue_le_of_forall_minimalPrimes (R := R) (S := A) pBase q
    (r : ℕ∞) hr
  -- arithmetic
  obtain ⟨c, hc⟩ : ∃ c, c = Algebra.trdeg K Qp.ResidueField := ⟨_, rfl⟩
  rw [← hc] at hT hFI
  have hcfin : Cardinal.toENat c ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at hT
    exact ENat.top_ne_natCast _ hT
  have hclt : c < Cardinal.aleph0 := by
    by_contra hge
    exact hcfin (Cardinal.toENat_eq_top.mpr (not_lt.mp hge))
  rw [Cardinal.toENat_eq_toNat_of_lt_aleph0 hclt] at hT
  have ht : Cardinal.toNat c = Cardinal.toNat (let := Ideal.ResidueField.algebraOfLiesOver pBase q
      Algebra.trdeg pBase.ResidueField q.ResidueField) := by
    rw [← hFI, hcongr, hsurjT]
  rw [← ht] at h0BAE
  have hqfin : q.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  have hpfin : pBase.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hpfin
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hQpfin
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hqfin
  rw [← ha, ← hb] at hflat
  rw [← hb] at hT
  rw [← hh, ← ha] at h0BAE
  rw [← hh, hflat] at h0BUX
  change (p.variableCount : ℕ∞) ≤ Module.depth S₀ I₀ S₀ + r
  by_cases hD : Module.depth S₀ I₀ S₀ = ⊤
  · simp [hD]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hD
  rw [← hd] at h0BUX ⊢
  have e1 : h + d = a + b := by exact_mod_cast h0BUX
  have e2 : b + Cardinal.toNat c = p.variableCount := by exact_mod_cast hT
  have e3 : h + Cardinal.toNat c ≤ a + r := by exact_mod_cast h0BAE
  exact_mod_cast (show p.variableCount ≤ d + r by omega)

/-! ### The localized `Ext`, linearly -/

/-- **Localizing `Ext` out of a finite module, as a linear equivalence.**  For a Noetherian ring
`A`, a submonoid `T`, a finite `A`-module `M` and a bounded below `K ∈ D(A)`, the localization of
`Ext^i_A(M, K)` at `T` is `Ext^i_{T⁻¹A}(T⁻¹M, T⁻¹K)`, linearly over `T⁻¹A`.  This is
`Dualizing.localizedExtLinearEquivOfDerivedHom`, the identification behind
`Dualizing.localized_ext_nontrivial_iff`. -/
noncomputable def localizedExtLinearEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Submonoid A) (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) :
    LocalizedModule T (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) K i) ≃ₗ[
        Localization T]
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).obj
        ((ModuleCat.localizedModuleFunctor.{u} T).obj (ModuleCat.of A M)))
      ((ModuleCat.localizedModuleFunctor.{u} T).mapDerivedCategory.obj K) i :=
  localizedExtLinearEquivOfDerivedHom.{u} T M K hKge i

/-! ### The cohomology of the relative dualizing complex as an `Ext` -/

/-- **`H^i(ω^•_{A/R}) = Ext^{i+n}_P(A, P)` over the polynomial algebra.**  For a presentation
`P = R[x_1, …, x_n] → A`, the relative dualizing complex is `RHom_P(A, P)[n]`
[Stacks, Tag 0BZI], and the cohomology of derived Hom is `Ext` [Stacks, Tag 0A71]; this is the
resulting `P`-linear identification. -/
noncomputable def restrictScalarsHomologyUpperShriekLinearEquiv {R A : Type u} [CommRing R]
    [CommRing A] {f : R →+* A} (p : PolynomialPresentation f) (i : ℤ) :
    ((ModuleCat.restrictScalars p.toRingHom).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) ≃ₗ[p.Poly]
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj
        ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} p.Poly) 0).obj (ModuleCat.of p.Poly p.Poly))
      (i + p.variableCount) :=
  let P := p.Poly
  let RF := derivedHom.{u, 0, u} p.toRingHom
  let input := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let eUpper :
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))) ≅
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (p.variableCount : ℤ)).obj
          (RF.obj input) :=
    (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (p.variableCount : ℤ)).mapIso
      ((derivedHom.{u, 0, u} p.toRingHom).mapIso p.derivedExtensionUnitIso)
  let eH := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso eUpper ≪≫
    homologyShiftObjIso (RF.obj input) i (p.variableCount : ℤ)
  let α := (coextendScalarsToDerivedCategory p.toRingHom).totalRightDerivedUnit
    DerivedCategory.Qh (HomotopyCategory.quasiIso (ModuleCat.{u} P) (ComplexShape.up ℤ))
  ((ModuleCat.restrictScalars p.toRingHom).mapIso eH).toLinearEquiv.trans
    ((derivedCoextendScalarsHomologyLinearEquivExt p.toRingHom RF α).linearEquiv input
      (i + p.variableCount))

/-- **`H^i(ω^•_{A/R})` localized at a prime `𝔯` of the polynomial algebra.**  The localization at
`𝔯` of the `P`-module `H^i(ω^•_{A/R})` is `Ext^{i+n}_{P_𝔯}(A_𝔯, P_𝔯)`, linearly over `P_𝔯`. -/
noncomputable def localizedHomologyUpperShriekLinearEquiv {R A : Type u} [CommRing R]
    [CommRing A] [IsNoetherianRing R] {f : R →+* A} (p : PolynomialPresentation f)
    (rP : Ideal p.Poly) [rP.IsPrime] (i k : ℤ) (hk : i + p.variableCount = k) :
    LocalizedModule rP.primeCompl ((ModuleCat.restrictScalars p.toRingHom).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) ≃ₗ[
        Localization.AtPrime rP]
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime rP)) 0).obj
        (ModuleCat.of (Localization.AtPrime rP) (LocalizedModule rP.primeCompl
          ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))))))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime rP)) 0).obj
        (ModuleCat.of (Localization.AtPrime rP) (Localization.AtPrime rP)))
      k := by
  subst hk
  let P := p.Poly
  let T := rP.primeCompl
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  haveI : Module.Finite P M₀ := finite_restrictScalars_ulift p
  let input := (DerivedCategory.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)
  let k : ℤ := i + p.variableCount
  let e0 := IsLocalizedModule.mapEquiv T (LocalizedModule.mkLinearMap T _)
    (LocalizedModule.mkLinearMap T _) (Localization T)
    (restrictScalarsHomologyUpperShriekLinearEquiv p i)
  let e1 := localizedExtLinearEquiv T (M₀ : Type u) input ⟨0, inferInstance⟩ k
  let G := ModuleCat.localizedModuleFunctor.{u} T
  let eP₀ : LocalizedModule T P ≃ₗ[Localization T] Localization T :=
    IsLocalizedModule.mapEquiv T
      (LocalizedModule.mkLinearMap T P)
      (Algebra.linearMap P (Localization T)) (Localization T) (LinearEquiv.refl P P)
  let eP : G.obj (ModuleCat.of P P) ≅ ModuleCat.of (Localization T) (Localization T) :=
    LinearEquiv.toModuleIso ((Shrink.linearEquiv (Localization T) _).trans eP₀)
  let eTarget := (G.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of P P) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).mapIso eP
  let eM : G.obj (ModuleCat.of P M₀) ≅
      ModuleCat.of (Localization T) (LocalizedModule T (M₀ : Type u)) :=
    LinearEquiv.toModuleIso
      (Shrink.linearEquiv (Localization T) (LocalizedModule T (M₀ : Type u)))
  let eSource := (DerivedCategory.singleFunctor (ModuleCat.{u} (Localization T)) 0).mapIso eM
  let e2 := CategoryTheory.Linear.homCongr (Localization T) eSource
    ((shiftFunctor (DerivedCategory (ModuleCat.{u} (Localization T))) k).mapIso eTarget)
  exact e0.trans (e1.trans e2)

/-- **Depth and dimension at a prime, read over a surjection.**  Let `φ : P → A` be surjective, let
`𝔮 ⊂ A` be a prime and `𝔯 = φ⁻¹(𝔮)`.  For a finite `A`-module `H`, the depth and the dimension of
the support of `H_𝔮` over `A_𝔮` are those of the localization at `𝔯` of `H`, read as a
`P`-module, over `P_𝔯`. -/
@[ega "0 16.4.8" "special case", ega "IV 5.7.9" "special case"]
theorem moduleDepth_and_moduleSupportDim_localizedModule_restrictScalars {P A : Type u}
    [CommRing P] [CommRing A] (φ : P →+* A) (hφ : Function.Surjective φ) (q : Ideal A)
    [q.IsPrime] (rP : Ideal P) [rP.IsPrime] (hrP : rP = q.comap φ) (H : ModuleCat.{u} A)
    [Module.Finite A H] :
    moduleDepth (Localization.AtPrime q) (LocalizedModule.AtPrime q H) =
        moduleDepth (Localization.AtPrime rP)
          (LocalizedModule rP.primeCompl ((ModuleCat.restrictScalars φ).obj H)) ∧
      moduleSupportDim (Localization.AtPrime q) (LocalizedModule.AtPrime q H) =
        moduleSupportDim (Localization.AtPrime rP)
          (LocalizedModule rP.primeCompl ((ModuleCat.restrictScalars φ).obj H)) := by
  let : Algebra P A := φ.toAlgebra
  let : Module P H := Module.compHom H φ
  have : IsScalarTower P A H := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let Hq := LocalizedModule q.primeCompl H
  have : q.LiesOver rP := ⟨hrP⟩
  have hsub : Algebra.algebraMapSubmonoid A rP.primeCompl = q.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective q rP hφ
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid A rP.primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl H) := hsub ▸ inferInstance
  have : IsLocalizedModule rP.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl H).restrictScalars P) :=
    IsLocalizedModule.restrictScalars _ _
  let S₀ := Localization.AtPrime rP
  let T₀ := Localization.AtPrime q
  let : Algebra S₀ T₀ := (Localization.localRingHom rP q φ hrP).toAlgebra
  have hsurj : Function.Surjective (algebraMap S₀ T₀) :=
    Localization.surjective_localRingHom φ hφ rP q hrP
  let : Module S₀ Hq := Module.compHom Hq (algebraMap S₀ T₀)
  have : IsScalarTower S₀ T₀ Hq := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower P S₀ Hq := by
    refine IsScalarTower.of_algebraMap_smul fun x n => ?_
    rw [← algebraMap_smul A x n]
    change Localization.localRingHom rP q φ hrP (algebraMap P S₀ x) • n = algebraMap P A x • n
    rw [Localization.localRingHom_to_map, algebraMap_smul]
    rfl
  let e : LocalizedModule rP.primeCompl H ≃ₗ[S₀] Hq :=
    LinearEquiv.extendScalarsOfIsLocalization rP.primeCompl S₀
      (IsLocalizedModule.linearEquiv rP.primeCompl
        (LocalizedModule.mkLinearMap rP.primeCompl H)
        ((LocalizedModule.mkLinearMap q.primeCompl H).restrictScalars P))
  refine ⟨?_, ?_⟩
  · rw [← moduleDepth_eq_of_surjective_algebraMap hsurj Hq]
    exact (moduleDepth_eq_of_linearEquiv e).symm
  · rw [← moduleSupportDim_eq_of_surjective_algebraMap hsurj Hq]
    exact (moduleSupportDim_eq_of_linearEquiv e).symm

/-- The localization at `𝔯 = φ⁻¹(𝔮)` of an `A`-module read over `P` is its localization at `𝔮`,
for a surjection `φ : P → A`. -/
noncomputable def localizedModuleRestrictScalarsAddEquiv {P A : Type u}
    [CommRing P] [CommRing A] (φ : P →+* A) (hφ : Function.Surjective φ) (q : Ideal A)
    [q.IsPrime] (rP : Ideal P) [rP.IsPrime] (hrP : rP = q.comap φ) (H : ModuleCat.{u} A) :
    LocalizedModule rP.primeCompl ((ModuleCat.restrictScalars φ).obj H) ≃+
      LocalizedModule.AtPrime q H :=
  letI : Algebra P A := φ.toAlgebra
  letI : Module P H := Module.compHom H φ
  haveI : IsScalarTower P A H := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : q.LiesOver rP := ⟨hrP⟩
  haveI : IsLocalizedModule (Algebra.algebraMapSubmonoid A rP.primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl H) :=
    (Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective q rP hφ) ▸ inferInstance
  haveI : IsLocalizedModule rP.primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl H).restrictScalars P) :=
    IsLocalizedModule.restrictScalars _ _
  (IsLocalizedModule.linearEquiv rP.primeCompl
    (LocalizedModule.mkLinearMap rP.primeCompl H)
    ((LocalizedModule.mkLinearMap q.primeCompl H).restrictScalars P)).toAddEquiv

/-- **The cohomology of the relative dualizing complex is finite.** -/
theorem finite_homology_upperShriekFunctor {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] {f : R →+* A} (p : PolynomialPresentation f) (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) := by
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  have : Module.Finite p.Poly
      ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))) :=
    finite_restrictScalars_ulift p
  have := finite_derivedExt
    ((ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A)))
    (ModuleCat.of p.Poly p.Poly) (i + p.variableCount)
  have hP : Module.Finite p.Poly ((ModuleCat.restrictScalars p.toRingHom).obj H) :=
    Module.Finite.equiv (restrictScalarsHomologyUpperShriekLinearEquiv p i).symm
  let : Algebra p.Poly A := p.toRingHom.toAlgebra
  let : Module p.Poly H := Module.compHom H p.toRingHom
  have : IsScalarTower p.Poly A H := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite p.Poly H := hP
  exact Module.Finite.of_restrictScalars_finite p.Poly A H

/-- Cohen--Macaulayness of `R_𝔭` passes to `R_𝔮` for every prime `𝔮 ⊆ 𝔭`. -/
theorem isMaximalCohenMacaulay_localization_of_le {R : Type u} [CommRing R] [IsNoetherianRing R]
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (h : Module.IsMaximalCohenMacaulay (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔭))
    (𝔮 : Ideal R) [𝔮.IsPrime] (h𝔮 : 𝔮 ≤ 𝔭) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔮) := by
  let p' : Ideal (Localization.AtPrime 𝔭) := 𝔮.map (algebraMap R (Localization.AtPrime 𝔭))
  have hdisj : Disjoint (𝔭.primeCompl : Set R) (𝔮 : Set R) :=
    Set.disjoint_left.mpr fun _ ha ha' => ha (h𝔮 ha')
  have : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl _ 𝔮
    inferInstance hdisj
  have hc : p'.comap (algebraMap R (Localization.AtPrime 𝔭)) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl _ inferInstance hdisj
  have hCM' : Module.IsMaximalCohenMacaulay (Localization.AtPrime p') (Localization.AtPrime p') :=
    Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime h p' (Localization.AtPrime p')
  let e1 := IsLocalization.localizationLocalizationAtPrimeIsoLocalization 𝔭.primeCompl p'
  let e2 : Localization.AtPrime 𝔮 ≃+* Localization.AtPrime
      (p'.comap (algebraMap R (Localization.AtPrime 𝔭))) :=
    Localization.localRingEquiv 𝔮 _ (RingEquiv.refl R) (by rw [hc]; rfl)
  exact (Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv (e2.trans e1.toRingEquiv)).mpr hCM'

private theorem natCast_le_of_le_add {n r j : ℕ} {D : ℕ∞} (h : (n : ℕ∞) ≤ D + r)
    (hj : j + r ≤ n) : (j : ℕ∞) ≤ D := by
  induction D with
  | top => exact le_top
  | coe d =>
    have h' : n ≤ d + r := by exact_mod_cast h
    exact_mod_cast (show j ≤ d by omega)

/-- **[Stacks, Tag 0E9R] at a prime of `A`.**  Let `R → A` be a finite type homomorphism of
Noetherian rings presented by `P = R[x_1, …, x_n] → A`, and let `𝔮 ⊂ A` be a prime with
`R_{𝔮 ∩ R}` Cohen--Macaulay and with `trdeg_{κ(R ∩ 𝔮')} κ(𝔮') ≤ r` at every minimal prime
`𝔮' ⊆ 𝔮`.  Then `H^i(ω^•_{A/R})_𝔮 = 0` for `i < -r`, and `H^{-r}(ω^•_{A/R})_𝔮` satisfies the local
form of `(S₂)` at the maximal ideal of `A_𝔮`.

Write `𝔯 ⊂ P` for the prime below `𝔮` and `I₀` for the kernel of `P_𝔯 → A_𝔮`.  The localization of
`H^i(ω^•_{A/R})` is `Ext^{i+n}_{P_𝔯}(A_𝔯, P_𝔯)`, the ring `P_𝔯` is Cohen--Macaulay and
`depth_{I₀}(P_𝔯) ≥ n - r` (`Dualizing.isMaximalCohenMacaulay_and_le_depth_ker_localRingHom`).
Below that depth the `Ext` vanishes [Stacks, Tag 0AVZ]; at it, it is `(S₂)`
(`Dualizing.min_two_le_moduleDepth_ext_of_le_depth`). -/
theorem subsingleton_and_min_two_le_moduleDepth_localizedModule_homology_upperShriek
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (q : Ideal A) [q.IsPrime]
    (hCMR : Module.IsMaximalCohenMacaulay (Localization.AtPrime (q.under R))
      (Localization.AtPrime (q.under R)))
    (r : ℕ)
    (hr : ∀ (q' : Ideal A) [q'.IsPrime], q' ∈ minimalPrimes A → q' ≤ q →
      (Ideal.underResidueTrdeg R q' : ℕ∞) ≤ r) :
    (∀ i : ℤ, i < -(r : ℤ) → Subsingleton (LocalizedModule.AtPrime q
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))) ∧
    min (2 : ℕ∞) ((moduleSupportDim (Localization.AtPrime q) (LocalizedModule.AtPrime q
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))))).unbotD
          0) ≤
      moduleDepth (Localization.AtPrime q) (LocalizedModule.AtPrime q
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) := by
  let P := p.Poly
  let rP : Ideal P := q.comap p.toRingHom
  obtain ⟨hCMS, hdepth⟩ :=
    isMaximalCohenMacaulay_and_le_depth_ker_localRingHom p q hCMR r hr rP rfl
  let S₀ := Localization.AtPrime rP
  let T₀ := Localization.AtPrime q
  let fLocal : S₀ →+* T₀ := Localization.localRingHom rP q p.toRingHom rfl
  let I₀ : Ideal S₀ := RingHom.ker fLocal
  let M₀ := (ModuleCat.restrictScalars p.toRingHom).obj (ModuleCat.of A (ULift.{u} A))
  have : Module.Finite P M₀ := finite_restrictScalars_ulift p
  let N : ModuleCat.{u} S₀ := ModuleCat.of S₀ (LocalizedModule rP.primeCompl (M₀ : Type u))
  have hrMap : rP.primeCompl.map p.toRingHom = q.primeCompl := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩ hxa
      exact hx hxa
    · intro ha
      obtain ⟨x, rfl⟩ := p.surjective a
      exact ⟨x, ha, rfl⟩
  have hIMap : I₀ = (RingHom.ker p.toRingHom).map (algebraMap P S₀) :=
    IsLocalization.ker_map (S := S₀) T₀ p.toRingHom hrMap
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
  have hI₀ : I₀ ≠ ⊤ := RingHom.ker_ne_top fLocal
  let H : ℤ → ModuleCat.{u} A := fun i => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
    (p.upperShriekFunctor.{u, 0}.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  have key : ∀ (i : ℤ) (j : ℕ), i + p.variableCount = j →
      LocalizedModule rP.primeCompl ((ModuleCat.restrictScalars p.toRingHom).obj (H i)) ≃ₗ[S₀]
        Abelian.Ext N (ModuleCat.of S₀ S₀) j := fun i j hj =>
    (localizedHomologyUpperShriekLinearEquiv p rP i j hj).trans
      (Abelian.Ext.homLinearEquiv (R := S₀)).symm
  have hneg : ∀ i : ℤ, i + p.variableCount < 0 →
      Subsingleton (LocalizedModule rP.primeCompl
        ((ModuleCat.restrictScalars p.toRingHom).obj (H i))) := fun i hi =>
    (localizedHomologyUpperShriekLinearEquiv p rP i _ rfl).toEquiv.subsingleton_congr.mpr
      (subsingleton_derivedExt_of_neg _ _ _ (by omega))
  refine ⟨fun i hi => ?_, ?_⟩
  · have hsubP : Subsingleton (LocalizedModule rP.primeCompl
        ((ModuleCat.restrictScalars p.toRingHom).obj (H i))) := by
      by_cases h0 : i + p.variableCount < 0
      · exact hneg i h0
      · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h0)
        have hjd : (j : ℕ∞) < Module.depth S₀ I₀ S₀ :=
          ENat.natCast_add_one_le_iff.mp
            (by exact_mod_cast natCast_le_of_le_add hdepth (j := j + 1) (by omega))
        have := ModuleCat.subsingleton_ext_of_lt_ideal_depth I₀ (ModuleCat.of S₀ S₀) N
          (by simpa using hI₀) (k := 1) (by simpa using hNann) hjd
        exact (key i j hj).toEquiv.subsingleton_congr.mpr inferInstance
    exact (localizedModuleRestrictScalarsAddEquiv p.toRingHom p.surjective q rP rfl
      (H i)).toEquiv.subsingleton_congr.mp hsubP
  · have := finite_homology_upperShriekFunctor p (-(r : ℤ))
    obtain ⟨hd, hs⟩ := moduleDepth_and_moduleSupportDim_localizedModule_restrictScalars
      p.toRingHom p.surjective q rP rfl (H (-(r : ℤ)))
    change min (2 : ℕ∞) ((moduleSupportDim T₀ (LocalizedModule.AtPrime q (H (-(r : ℤ))))).unbotD
      0) ≤ moduleDepth T₀ (LocalizedModule.AtPrime q (H (-(r : ℤ))))
    rw [hd, hs]
    by_cases h0 : -(r : ℤ) + p.variableCount < 0
    · have := hneg _ h0
      exact min_two_le_moduleDepth_of_subsingleton _
    · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (not_lt.mp h0)
      have hjd : (j : ℕ∞) ≤ Module.depth S₀ I₀ S₀ := natCast_le_of_le_add hdepth (by omega)
      rw [moduleSupportDim_eq_of_linearEquiv (key _ j hj),
        moduleDepth_eq_of_linearEquiv (key _ j hj)]
      exact min_two_le_moduleDepth_ext_of_le_depth I₀ N hNann j (ModuleCat.of S₀ S₀)
        (Eq.trans hCMS (Module.supportDim_self_eq_ringKrullDim S₀).symm)
        (by simpa using hjd)

/-! ### Tag 0E9R -/

/-- The two hypotheses of [Stacks, Tag 0E9R], read at a prime `𝔮` of `A` lying over a prime
contained in `𝔭`: Cohen--Macaulayness of `R_{𝔮 ∩ R}`, and the transcendence-degree bound at the
minimal primes of `A` below `𝔮`. -/
private theorem hypotheses_at_prime {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    [Algebra R A] (𝔭 : Ideal R) [𝔭.IsPrime]
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime 𝔭)) (r : ℕ)
    (htrdeg : ∀ (q : Ideal A) [q.IsPrime], q ∈ minimalPrimes A →
      letI := Ideal.ResidueField.algebraOfLiesOver (q.under R) q
      Algebra.trdeg (q.under R).ResidueField q.ResidueField ≤ r)
    (q : Ideal A) [q.IsPrime]
    (hq : Disjoint ((Submonoid.map (algebraMap R A) 𝔭.primeCompl : Submonoid A) : Set A)
      (q : Set A)) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime (q.under R))
        (Localization.AtPrime (q.under R)) ∧
      ∀ (q' : Ideal A) [q'.IsPrime], q' ∈ minimalPrimes A → q' ≤ q →
        (Ideal.underResidueTrdeg R q' : ℕ∞) ≤ r := by
  refine ⟨?_, fun q' _ hq' _ => ?_⟩
  · have hle : q.under R ≤ 𝔭 := by
      intro a ha
      by_contra haP
      exact Set.disjoint_left.mp hq (Submonoid.mem_map.mpr ⟨a, haP, rfl⟩) ha
    exact isMaximalCohenMacaulay_localization_of_le 𝔭
      ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp hCM) (q.under R) hle
  · have h := htrdeg q' hq'
    have h' := Cardinal.toNat_le_toNat h (Cardinal.natCast_lt_aleph0 (n := r))
    rw [Cardinal.toNat_natCast] at h'
    exact_mod_cast h'

/-- **[Stacks, Tag 0E9R], the vanishing.**  Let `R → A` be a finite type homomorphism of
Noetherian rings and let `𝔭 ⊂ R` be a prime.  Assume that `R_𝔭` is Cohen--Macaulay and that
`trdeg_{κ(R ∩ 𝔮)} κ(𝔮) ≤ r` for every minimal prime `𝔮 ⊂ A`.  Then

`H^i(ω^•_{A/R})_𝔭 ≠ 0 ⟹ -r ≤ i` .

Here `ω^•_{A/R} = φ^!(R)` is the relative dualizing complex, computed from an arbitrary polynomial
presentation `p` of `R → A` (it is well defined only up to isomorphism, so the statement is made
for every presentation), and the localization at `𝔭` is the localization of the `A`-module at the
image of `R ∖ 𝔭`.

The proof does not go through a dualizing complex of `R_𝔭`.  At a prime `𝔮 ⊂ A` over a prime
contained in `𝔭`, the localization of `H^i(ω^•_{A/R})` is `Ext^{i+n}_{P_𝔯}(A_𝔯, P_𝔯)`, where
`P_𝔯` is Cohen--Macaulay and `depth_{I}(P_𝔯) ≥ n - r` by the dimension formula; see
`Dualizing.subsingleton_and_min_two_le_moduleDepth_localizedModule_homology_upperShriek`. -/
@[stacks 0E9R "the vanishing H^i(ω_{A/R})_𝔭 = 0 for i < -r, in full"]
theorem le_of_nontrivial_localizedModule_homology_relativeDualizingComplex
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime 𝔭)) (r : ℕ)
    (htrdeg : ∀ (q : Ideal A) [q.IsPrime], q ∈ minimalPrimes A →
      letI := Ideal.ResidueField.algebraOfLiesOver (q.under R) q
      Algebra.trdeg (q.under R).ResidueField q.ResidueField ≤ r)
    (i : ℤ) :
    Nontrivial (LocalizedModule (Submonoid.map (algebraMap R A) 𝔭.primeCompl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) →
      -(r : ℤ) ≤ i := by
  intro hnt
  by_contra hi
  push Not at hi
  refine (not_subsingleton_iff_nontrivial.mpr hnt) ?_
  refine subsingleton_localizedModule_of_forall_prime_disjoint _ fun q hq => ?_
  obtain ⟨hCMR, hr⟩ := hypotheses_at_prime 𝔭 hCM r htrdeg q.asIdeal hq.symm
  exact (subsingleton_and_min_two_le_moduleDepth_localizedModule_homology_upperShriek p
    q.asIdeal hCMR r hr).1 i hi

/-- **[Stacks, Tag 0E9R], the `(S₂)` clause.**  Let `R → A` be a finite type homomorphism of
Noetherian rings and let `𝔭 ⊂ R` be a prime.  Assume that `R_𝔭` is Cohen--Macaulay and that
`trdeg_{κ(R ∩ 𝔮)} κ(𝔮) ≤ r` for every minimal prime `𝔮 ⊂ A`.  Then `H^{-r}(ω^•_{A/R})_𝔭`
satisfies Serre's condition `(S₂)` as an `A_𝔭`-module, where `A_𝔭` is the localization of `A` at
the image of `R ∖ 𝔭`.

As in `Dualizing.le_of_nontrivial_localizedModule_homology_relativeDualizingComplex`,
`ω^•_{A/R} = φ^!(R)` is computed from an arbitrary polynomial presentation `p`. At a prime `𝔮`
of `A_𝔭`, the module is `Ext^{n-r}_{P_𝔯}(A_𝔯, P_𝔯)` with `P_𝔯` Cohen--Macaulay and
`n - r ≤ depth_I(P_𝔯)`, and such an `Ext` satisfies `(S₂)`
(`Dualizing.min_two_le_moduleDepth_ext_of_le_depth`). -/
@[stacks 0E9R "the (S_2) clause, H^{-r}(ω_{A/R})_𝔭 is (S_2) as an A_𝔭-module, in full"]
theorem propertySkModule_localizedModule_homology_relativeDualizingComplex
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    [Algebra R A] (p : PolynomialPresentation (algebraMap R A)) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime 𝔭)) (r : ℕ)
    (htrdeg : ∀ (q : Ideal A) [q.IsPrime], q ∈ minimalPrimes A →
      letI := Ideal.ResidueField.algebraOfLiesOver (q.under R) q
      Algebra.trdeg (q.under R).ResidueField q.ResidueField ≤ r) :
    letI : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
        (p.upperShriekFunctor.{u, 0}.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
      finite_homology_upperShriekFunctor p _
    PropertySkModule (Localization (Submonoid.map (algebraMap R A) 𝔭.primeCompl))
      (LocalizedModule (Submonoid.map (algebraMap R A) 𝔭.primeCompl)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
          (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R))))) 2 := by
  let : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(r : ℤ))).obj
      (p.upperShriekFunctor.{u, 0}.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))) :=
    finite_homology_upperShriekFunctor p _
  refine propertySkModule_localizedModule_of_forall _ _ 2 fun q _ hq => ?_
  obtain ⟨hCMR, hr⟩ := hypotheses_at_prime 𝔭 hCM r htrdeg q hq
  exact (subsingleton_and_min_two_le_moduleDepth_localizedModule_homology_upperShriek p
    q hCMR r hr).2

end Dualizing

end

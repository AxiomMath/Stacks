module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocalConverse.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.RelativeDefs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.AffineGenerators
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.ClosedBridge
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.Affine
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.OpenIndependence
public import StacksFrontier.RingTheory.Flat.LocalCriterionEssFP
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Koszul.Cone
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Relations
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.SyntomicIntoSmooth

/-!
# Flat neighbourhoods of relative `H₁`-regular immersions and of relative Cartier divisors

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation and let `i : Z ⟶ X` be
an immersion which is *relatively `H₁`-regular* over `S`:  `Z` is flat over `S` and the ideal
sheaf of `i` is `H₁`-regular.  Then `f` is flat on an open neighbourhood of the image of `Z`.
Specialising to the closed subscheme cut out by an invertible sheaf of ideals gives the same
statement for a relative effective Cartier divisor:  it lies in an open subscheme on which the
ambient morphism is flat.

## Main results

* `Stacks.AlgebraicGeometry.exists_open_flat_of_isRelativeH1RegularImmersion`: if `f` is locally
  of finite presentation and `i : Z ⟶ X` is a relative `H₁`-regular immersion over `S`, then `f`
  is flat on an open subscheme of `X` containing the image of `Z`.
* `Stacks.AlgebraicGeometry.isRegularImmersion_subschemeι_of_isEffectiveCartierDivisor`: an
  effective Cartier divisor is a regular immersion.
* `Stacks.AlgebraicGeometry.exists_open_flat_of_isRelativeEffectiveCartierDivisor`: a relative
  effective Cartier divisor for a morphism locally of finite presentation lies in an open
  subscheme on which the morphism is flat.

## References

* [Stacks Project, Lemma 31.18.9 (Tag 062V)](https://stacks.math.columbia.edu/tag/062V)
* [Stacks Project, Lemma 31.22.4 (Tag 063V)](https://stacks.math.columbia.edu/tag/063V)
* [Stacks Project, Definition 31.18.1 (Tag 062T)](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Lemma 31.18.2 (Tag 01WS)](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Lemma 15.26.6 (Tag 0471)](https://stacks.math.columbia.edu/tag/0471)
* [Stacks Project, Lemma 15.26.5 (Tag 063Q)](https://stacks.math.columbia.edu/tag/063Q)
* [Stacks Project, Theorem 10.129.4 (Tag 00RC)](https://stacks.math.columbia.edu/tag/00RC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open scoped TensorProduct

universe u v

namespace Stacks.AlgebraicGeometry

/-! ### The local criterion for flatness along an `H₁`-regular sequence -/

section LocalAlgebra

/-- **The `Tor` hypothesis of the local criterion, from `H₁`-regularity.**  If the image of a
sequence `f₁, …, f_r` of elements of `R` is `H₁`-regular in an `R`-algebra `B`, then the
canonical map `(f₁, …, f_r) ⊗_R B ⟶ B` is injective. -/
private theorem rTensor_subtype_injective_of_isH1Regular
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    {r : ℕ} (f : Fin r → R)
    (hf : Koszul.IsH1Regular (algebraMap R B ∘ f)) :
    Function.Injective ((Ideal.span (Set.range f)).subtype.rTensor B) := by
  classical
  let I := Ideal.span (Set.range f)
  let v : Fin r → I := fun i => ⟨f i, Ideal.subset_span ⟨i, rfl⟩⟩
  let τ : (Fin r → B) →ₗ[R] I ⊗[R] B :=
    ∑ i, (TensorProduct.mk R I B (v i)).comp (LinearMap.proj i)
  have hτ (b : Fin r → B) : τ b = ∑ i, v i ⊗ₜ[R] b i := by
    simp [τ]
  have hτsingle (i : Fin r) (b : B) : τ (Pi.single i b) = v i ⊗ₜ[R] b := by
    simp [hτ, Pi.single_apply, TensorProduct.tmul_ite]
  have hτsmul (c : B) (b : Fin r → B) :
      τ (c • b) = (Algebra.lsmul R R B c).lTensor I (τ b) := by
    simp [hτ]
  have htriv (i j : Fin r) : τ (Koszul.trivRel (algebraMap R B ∘ f) i j) = 0 := by
    rw [Koszul.trivRel, map_sub, hτsingle, hτsingle, sub_eq_zero]
    show v j ⊗ₜ[R] (algebraMap R B (f i)) = v i ⊗ₜ[R] (algebraMap R B (f j))
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    congr 1
    apply Subtype.ext
    exact mul_comm _ _
  have hrel : ∀ b ∈ Koszul.relSpan (algebraMap R B ∘ f), τ b = 0 := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb => obtain ⟨⟨i, j⟩, rfl⟩ := hb; exact htriv i j
    | zero => exact map_zero τ
    | add b c _ _ hb hc => rw [map_add, hb, hc, add_zero]
    | smul c b _ hb => rw [hτsmul, hb, map_zero]
  have hsurj : Function.Surjective τ := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero τ⟩
    | tmul y b =>
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp y.property
      have hy : (∑ i, a i • v i) = y := by
        apply Subtype.ext
        simpa [v] using ha
      refine ⟨fun i => a i • b, ?_⟩
      rw [hτ, ← hy, TensorProduct.sum_tmul]
      simp only [TensorProduct.smul_tmul]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add τ a b⟩
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨b, rfl⟩ := hsurj x
  have hzero : ∑ i, b i * algebraMap R B (f i) = 0 := by
    have h := congrArg (TensorProduct.lid R B) (LinearMap.mem_ker.mp hx)
    simpa [hτ, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      Algebra.smul_def, mul_comm, v] using h
  exact hrel b ((Koszul.isH1Regular_iff_forall _).mp hf b hzero)

/-- **The local criterion for flatness along an `H₁`-regular sequence from the base.**  For a
local homomorphism `R ⟶ B` of local rings essentially of finite presentation, a sequence in `R`
generating a proper ideal and `H₁`-regular in `B`, flatness of `B ⧸ (f) B` over `R ⧸ (f)`
implies flatness of `B` over `R`. -/
private theorem flat_of_isH1Regular_map
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [IsLocalRing R] [IsLocalRing B] [IsLocalHom (algebraMap R B)]
    (hB : (algebraMap R B).EssentiallyOfFinitePresentation)
    {r : ℕ} (f : Fin r → R) (hf : Koszul.IsH1Regular (algebraMap R B ∘ f))
    (hI : Ideal.span (Set.range f) ≠ ⊤)
    (hflat : Module.Flat (R ⧸ Ideal.span (Set.range f))
      (B ⧸ (Ideal.span (Set.range f) • (⊤ : Submodule R B)))) :
    Module.Flat R B :=
  Module.Flat.of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation
    B B hB _ hI (rTensor_subtype_injective_of_isH1Regular f hf) hflat

/-- **`H₁`-regularity ascends along a flat algebra.**  The image of an `H₁`-regular sequence in a
flat algebra is `H₁`-regular. -/
private theorem isH1Regular_map_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    {r : ℕ} (f : Fin r → R) (hf : Koszul.IsH1Regular f) :
    Koszul.IsH1Regular (algebraMap R S ∘ f) := by
  have h := KoszulC.isH1Regular_baseChange (S := S) f R
    ((Koszul.isH1RegularOn_self_iff f).2 hf)
  exact (Koszul.isH1RegularOn_self_iff _).1
    (Koszul.isH1RegularOn_of_linearEquiv _ (TensorProduct.AlgebraTensorModule.rid R S S) h)

/-- **The quotient of a polynomial algebra by its variables is the base.**  The structure map
`A ⟶ A[x_1, …, x_r] ⧸ (x_1, …, x_r)` is bijective, with inverse the constant coefficient. -/
private theorem bijective_algebraMap_quotient_vars
    (A : Type*) [CommRing A] (r : ℕ) :
    Function.Bijective (algebraMap A
      (MvPolynomial (Fin r) A ⧸
        Ideal.span (Set.range (MvPolynomial.X : Fin r → MvPolynomial (Fin r) A)))) := by
  classical
  let I : Ideal (MvPolynomial (Fin r) A) := Ideal.span (Set.range MvPolynomial.X)
  let l : (MvPolynomial (Fin r) A ⧸ I) →+* A :=
    Ideal.Quotient.lift I MvPolynomial.constantCoeff (by
      show I ≤ RingHom.ker MvPolynomial.constantCoeff
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp)
  refine ⟨?_, ?_⟩
  · have hl (a : A) : l (algebraMap A (MvPolynomial (Fin r) A ⧸ I) a) = a := by
      show MvPolynomial.constantCoeff (MvPolynomial.C a) = a
      simp
    intro a b hab
    exact (hl a).symm.trans ((congrArg l hab).trans (hl b))
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C a => exact ⟨a, rfl⟩
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p i _ =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, show Ideal.Quotient.mk I (MvPolynomial.X i) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩), mul_zero]

/-- A module flat over the base of a bijective structure map is flat over the algebra. -/
private theorem flat_of_bijective_algebraMap
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Bijective (algebraMap R S)) [Module.Flat R M] : Module.Flat S M := by
  let e := RingEquiv.ofBijective (algebraMap R S) h
  apply Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv e.symm
  intro s m
  have he : algebraMap R S (e.symm s) = s := e.apply_symm_apply s
  calc
    s • m = algebraMap R S (e.symm s) • m := congrArg (fun t => t • m) he.symm
    _ = e.symm s • m := algebraMap_smul S _ _

/-- **Flatness at a prime containing an `H₁`-regular ideal.**  Let `A ⟶ B` be of finite
presentation, let `f₁, …, f_r` be an `H₁`-regular sequence in `B` with `B ⧸ (f)` flat over `A`,
and let `q` be a prime of `B` containing `(f)`.  Then `B_q` is flat over `A`. -/
private theorem flat_localizationAtPrime_of_isH1Regular
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] {r : ℕ} (f : Fin r → B)
    (hf : Koszul.IsH1Regular f) (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (q : Ideal B) [q.IsPrime] (hq : Ideal.span (Set.range f) ≤ q) :
    Module.Flat A (Localization.AtPrime q) := by
  classical
  let R := MvPolynomial (Fin r) A
  let : Algebra R B := (MvPolynomial.aeval f).toRingHom.toAlgebra
  have : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A B a = MvPolynomial.aeval f (MvPolynomial.C a)
    simp
  have : Algebra.FinitePresentation R B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A R B
  let p : Ideal R := q.comap (algebraMap R B)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  have : q.LiesOver p := ⟨rfl⟩
  let P := Localization.AtPrime p
  let T := Localization.AtPrime q
  let : Algebra P T := Localization.AtPrime.algebraOfLiesOver p q
  let fP : Fin r → P := fun i => algebraMap R P (MvPolynomial.X i)
  let J : Ideal P := Ideal.span (Set.range fP)
  have hess : (algebraMap P T).EssentiallyOfFinitePresentation :=
    Koszul.essentiallyOfFinitePresentation_localization (S := B) p.primeCompl q.primeCompl
      (by rintro _ ⟨a, ha, rfl⟩; exact ha)
  have hX (i : Fin r) : algebraMap P T (fP i) = algebraMap B T (f i) := by
    rw [← IsScalarTower.algebraMap_apply R P T, IsScalarTower.algebraMap_apply R B T]
    show algebraMap B T (MvPolynomial.aeval f (MvPolynomial.X i)) = _
    simp
  have hfP : Koszul.IsH1Regular (algebraMap P T ∘ fP) := by
    convert isH1Regular_map_of_flat (S := T) f hf using 1
    exact funext hX
  have hJ : J ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal P).ne_top
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply Ideal.mem_map_of_mem
    show MvPolynomial.aeval f (MvPolynomial.X i) ∈ q
    simpa using hq (Ideal.subset_span (Set.mem_range_self i))
  let I : Ideal B := Ideal.span (Set.range f)
  let I₀ : Ideal R := Ideal.span (Set.range (MvPolynomial.X : Fin r → R))
  let K := I.map (algebraMap B T)
  have hmap : I₀.map (algebraMap R T) = K := by
    simp only [I₀, I, K, Ideal.map_span, ← Set.range_comp]
    congr 2
    exact funext fun i => (IsScalarTower.algebraMap_apply R P T _).trans (hX i)
  have hJmap : J = I₀.map (algebraMap R P) := by
    simp only [J, I₀, Ideal.map_span, ← Set.range_comp, fP, Function.comp_def]
  have hflatK : Module.Flat A (T ⧸ K) := by
    have : Module.Flat A (B ⧸ I) := hflat
    have : IsScalarTower A (B ⧸ I) (T ⧸ K) :=
      IsScalarTower.of_algebraMap_eq fun a => rfl
    have : Module.Flat (B ⧸ I) (T ⧸ K) :=
      IsLocalization.flat (T ⧸ K) (Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl)
    exact Module.Flat.trans A (B ⧸ I) (T ⧸ K)
  have hflat₀ : Module.Flat A (T ⧸ I₀ • (⊤ : Submodule R T)) := by
    have he : I₀ • (⊤ : Submodule R T) = K.restrictScalars R := by
      rw [Ideal.smul_top_eq_map, hmap]
    let e : (T ⧸ I₀ • (⊤ : Submodule R T)) ≃ₗ[R] (T ⧸ K) :=
      (Submodule.quotEquivOfEq _ _ he).trans (Submodule.Quotient.restrictScalarsEquiv R K)
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  have hflat₀' : Module.Flat (R ⧸ I₀) (T ⧸ I₀ • (⊤ : Submodule R T)) :=
    flat_of_bijective_algebraMap (bijective_algebraMap_quotient_vars A r)
  have hquot : Module.Flat (P ⧸ J) (T ⧸ J • (⊤ : Submodule P T)) := by
    rw [hJmap]
    exact Stacks.Flatness.flat_quotient_map_of_isLocalization p.primeCompl P I₀ T hflat₀'
  have : Module.Flat P T := flat_of_isH1Regular_map hess fP hfP hJ hquot
  have : Module.Flat R T := (Module.flat_iff_of_isLocalization P p.primeCompl T).mp this
  exact Module.Flat.trans A R T

/-- Flatness of a localization away from one element follows from flatness at each prime of the
corresponding basic open. -/
private theorem flat_localizationAway_of_basicOpen_subset
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (b : B)
    (h : ∀ p : PrimeSpectrum B, p ∈ PrimeSpectrum.basicOpen b →
      Module.Flat A (Localization.AtPrime p.asIdeal)) :
    Module.Flat A (Localization.Away b) := by
  let C := Localization.Away b
  apply Module.flat_of_isLocalized_maximal (R := A) C C
    (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap C (Localization.AtPrime P))
  intro P hP
  let p : PrimeSpectrum B := ⟨P.comap (algebraMap B C), inferInstance⟩
  have hp : p ∈ PrimeSpectrum.basicOpen b :=
    P.notMem_of_isUnit (IsLocalization.Away.algebraMap_isUnit b)
  have : Module.Flat A (Localization.AtPrime p.asIdeal) := h p hp
  have : IsLocalization.AtPrime (Localization.AtPrime P) p.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers b) (Localization.AtPrime P) P
  exact Module.Flat.of_linearEquiv
    (((Localization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime P)).toLinearEquiv).restrictScalars A).symm

/-- **Spreading the pointwise flatness out.**  In the situation of
`flat_localizationAtPrime_of_isH1Regular`, there is `b ∉ q` with `B_b` flat over `A`. -/
private theorem exists_flat_localizationAway_of_isH1Regular
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] {r : ℕ} (f : Fin r → B)
    (hf : Koszul.IsH1Regular f) (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range f)))
    (q : PrimeSpectrum B) (hq : Ideal.span (Set.range f) ≤ q.asIdeal) :
    ∃ b : B, b ∉ q.asIdeal ∧ Module.Flat A (Localization.Away b) := by
  let W : Set (PrimeSpectrum B) :=
    {p | Module.Flat A (LocalizedModule.AtPrime p.asIdeal B)}
  have hW : IsOpen W := Module.isOpen_setOf_flat_localizedModule_atPrime
  have hp (p : PrimeSpectrum B) : p ∈ W ↔ Module.Flat A (Localization.AtPrime p.asIdeal) :=
    Module.Flat.equiv_iff
      ((IsLocalizedModule.iso p.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime p.asIdeal))).restrictScalars A)
  have hqW : q ∈ W := (hp q).mpr (flat_localizationAtPrime_of_isH1Regular f hf hflat q.asIdeal hq)
  obtain ⟨V, ⟨b, rfl⟩, hb, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqW hW
  exact ⟨b, hb, flat_localizationAway_of_basicOpen_subset b (fun p hp' => (hp p).mp (hsub hp'))⟩

end LocalAlgebra

/-! ### From a chart to a flat open neighbourhood -/

section Charts

/-- **Flatness over an affine base from flatness of the sections on an affine open.**  If the
restriction map `Γ(S, ⊤) ⟶ Γ(X, V)` is flat then so is the restriction of `f` to the affine open
`V`. -/
private theorem flat_ι_of_flat_appLE {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    (V : X.Opens) (hV : IsAffineOpen V) (hle : V ≤ f ⁻¹ᵁ ⊤)
    (h : (f.appLE ⊤ V hle).hom.Flat) : Flat (V.ι ≫ f) := by
  let : IsAffine V.toScheme := hV
  let : IsAffine (⊤ : S.Opens).toScheme := isAffineOpen_top S
  have htop : (f.resLE ⊤ V hle).appTop =
      (⊤ : S.Opens).topIso.hom ≫ f.appLE ⊤ V hle ≫ V.topIso.inv :=
    Scheme.Hom.resLE_app_top f hle
  have hres : Flat (f.resLE ⊤ V hle) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), htop, ← Category.assoc]
    exact (RingHom.Flat.respectsIso.cancel_right_isIso _ V.topIso.inv).mpr
      ((RingHom.Flat.respectsIso.cancel_left_isIso (⊤ : S.Opens).topIso.hom _).mpr h)
  rw [← Scheme.Hom.resLE_comp_ι f hle]
  infer_instance

/-- **The chart form of the flat neighbourhood statement.**  Over an affine base, if the ideal of
a closed immersion `i` is cut out on an affine open `U` by an `H₁`-regular sequence and `Z` is
flat over the base, then a point of `U` in the image of `i` has a flat open neighbourhood. -/
private theorem exists_open_flat_of_affine_sequence
    {S X Z : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [LocallyOfFinitePresentation f] [Flat (i ≫ f)]
    (U : X.affineOpens) {r : ℕ} (s : Fin r → Γ(X, U.1))
    (hs : Koszul.IsH1Regular s)
    (hker : Ideal.span (Set.range s) = RingHom.ker (i.app U.1).hom)
    (z : Z) (hz : i z ∈ U.1) :
    ∃ V : X.Opens, i z ∈ V ∧ Flat (V.ι ≫ f) := by
  have hUle : (U.1 : X.Opens) ≤ f ⁻¹ᵁ ⊤ := by simp
  let A := Γ(S, ⊤)
  let B := Γ(X, U.1)
  let C := Γ(Z, i ⁻¹ᵁ U.1)
  let g := f.appLE ⊤ U.1 hUle
  let h := i.app U.1
  let gh := (i ≫ f).appLE ⊤ (i ⁻¹ᵁ U.1) (fun _ hz => hUle hz)
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra B C := h.hom.toAlgebra
  let : Algebra A C := gh.hom.toAlgebra
  have hcomp : g ≫ h = gh := (Stacks.AlgebraicGeometry.appLE_comp_app f i hUle).symm
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a =>
    (ConcreteCategory.congr_hom hcomp a).symm
  have : Algebra.FinitePresentation A B := f.finitePresentation_appLE (isAffineOpen_top S) U.2 _
  have hZ : IsAffineOpen (i ⁻¹ᵁ U.1) := IsAffineHom.isAffine_preimage (f := i) U.1 U.2
  have : Module.Flat A C := (i ≫ f).flat_appLE (isAffineOpen_top S) hZ _
  let e : (B ⧸ RingHom.ker h.hom) ≃ₐ[A] C :=
    Ideal.quotientKerAlgEquivOfSurjective (f := IsScalarTower.toAlgHom A B C)
      (i.app_surjective U.1 U.2)
  have hflat : Module.Flat A (B ⧸ Ideal.span (Set.range s)) := by
    rw [hker]
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  let q := U.2.primeIdealOf ⟨i z, hz⟩
  have hq : Ideal.span (Set.range s) ≤ q.asIdeal := by
    rw [hker]
    have he := IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 (i ⁻¹ᵁ U.1) hZ le_rfl hz
    dsimp only [q]
    rw [← he]
    intro a ha
    show (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl) a ∈ (hZ.primeIdealOf ⟨z, hz⟩).asIdeal
    rw [← Scheme.Hom.app_eq_appLE]
    rw [show i.app U.1 a = 0 from ha]
    exact Ideal.zero_mem _
  obtain ⟨b, hb, hflatb⟩ := exists_flat_localizationAway_of_isH1Regular s hs hflat q hq
  let V := X.basicOpen b
  have hV : IsAffineOpen V := U.2.basicOpen b
  have hVle : V ≤ f ⁻¹ᵁ ⊤ := by simp
  refine ⟨V, ?_, ?_⟩
  · have hfs : U.2.fromSpec q = i z := U.2.fromSpec_primeIdealOf ⟨i z, hz⟩
    have hmem : U.2.fromSpec q ∈ V := by
      show q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen b
      rw [U.2.fromSpec_preimage_basicOpen b]
      exact hb
    exact hfs ▸ hmem
  · let D := Γ(X, V)
    let k := X.presheaf.map (homOfLE (X.basicOpen_le b)).op
    let g' := f.appLE ⊤ V hVle
    let : Algebra B D := k.hom.toAlgebra
    let : Algebra A D := g'.hom.toAlgebra
    have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a => by
      show g' a = k (g a)
      exact (ConcreteCategory.congr_hom (f.appLE_map (U := ⊤) (V := U.1) hUle
        (homOfLE (X.basicOpen_le b)).op) a).symm
    have : IsLocalization.Away b D := U.2.isLocalization_basicOpen b
    have : Module.Flat A (Localization.Away b) := hflatb
    have : Module.Flat A D := Module.Flat.of_linearEquiv
      (((IsLocalization.algEquiv (Submonoid.powers b) D
        (Localization.Away b)).toLinearEquiv).restrictScalars A)
    exact flat_ι_of_flat_appLE f V hV hVle this

/-- The image of a flat open under an open immersion is flat over the base. -/
private theorem flat_image_open {S X Y : Scheme.{u}} (f : X ⟶ S) (e : Y ⟶ X)
    [IsOpenImmersion e] (V : Y.Opens) [Flat (V.ι ≫ e ≫ f)] :
    Flat ((e ''ᵁ V).ι ≫ f) := by
  rw [← e.isoImage_inv_ι V, Category.assoc, Category.assoc]
  infer_instance

/-- **A flat open neighbourhood of a point of the image, over an affine base.**  If `S` is affine,
`f` is locally of finite presentation and `i` is a relative `H₁`-regular immersion over `S`, then
every point `i z` has an open neighbourhood on which `f` is flat. -/
private theorem exists_open_flat_at_image_of_affine_base
    {S X Z : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (i : Z ⟶ X)
    [IsImmersion i] [LocallyOfFinitePresentation f]
    (hi : AlgebraicGeometry.IsRelativeH1RegularImmersion f i) (z : Z) :
    ∃ U : X.Opens, i z ∈ U ∧ Flat (U.ι ≫ f) := by
  let C := i.coborderRange
  let j := i.liftCoborder
  have hflat : Flat (j ≫ C.ι ≫ f) := by simpa [j, C] using hi.1
  have hJ : RegularIdealSheaf.IsH1RegularIdealSheaf
      C.toScheme.toLocallyRingedSpace.toRingedSpace
      (RegularIdealSheaf.definingIdealOfHom j) := hi.2
  obtain ⟨U, hz, r, s, hker, hs⟩ :=
    (AlgebraicGeometry.isH1RegularIdealSheaf_iff_kerGeneratedBy j).mp hJ (j z)
      (subset_closure ⟨z, rfl⟩)
  obtain ⟨V, hzV, hfV⟩ :=
    exists_open_flat_of_affine_sequence (C.ι ≫ f) j U s hs hker.symm z hz
  refine ⟨C.ι ''ᵁ V, ?_, ?_⟩
  · refine ⟨j z, hzV, ?_⟩
    exact congrArg (fun k : Z ⟶ X => k z) i.liftCoborder_ι
  · let := hfV
    exact flat_image_open f C.ι V

/-- **A flat open neighbourhood of a point of the image.**  If `f` is locally of finite
presentation and `i` is a relative `H₁`-regular immersion over `S`, then every point `i z` has an
open neighbourhood on which `f` is flat. -/
private theorem exists_open_flat_at_image
    {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsImmersion i] [LocallyOfFinitePresentation f]
    (hi : AlgebraicGeometry.IsRelativeH1RegularImmersion f i) (z : Z) :
    ∃ U : X.Opens, i z ∈ U ∧ Flat (U.ι ≫ f) := by
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (i z)) (U := ⊤) trivial
  let : IsAffine V.toScheme := hV
  let T := f ⁻¹ᵁ V
  let j := i.resLE T (i ⁻¹ᵁ T) le_rfl
  let f' := f ∣_ V
  have : Flat (i ≫ f) := hi.1
  have hflat : Flat (j ≫ f') := by
    dsimp [j, f']
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_comp_resLE]
    infer_instance
  have hH : AlgebraicGeometry.IsRelativeH1RegularImmersion f' j :=
    ⟨hflat, isH1RegularImmersion_resLE i hi.2 T⟩
  obtain ⟨W, hzW, hfW⟩ := exists_open_flat_at_image_of_affine_base f' j hH ⟨z, hzV⟩
  refine ⟨T.ι ''ᵁ W, ?_, ?_⟩
  · refine ⟨j ⟨z, hzV⟩, hzW, ?_⟩
    exact congrArg (fun k : (i ⁻¹ᵁ T).toScheme ⟶ X => k ⟨z, hzV⟩)
      (Scheme.Hom.resLE_comp_ι i le_rfl)
  · have : Flat (W.ι ≫ T.ι ≫ f) := by
      rw [← morphismRestrict_ι f V, ← Category.assoc]
      let := hfW
      infer_instance
    exact flat_image_open f T.ι W

/-- Flatness over the base is Zariski local at the source: a supremum of flat opens is flat. -/
private theorem flat_iSup_open {S X : Scheme.{u}} (f : X ⟶ S)
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ j, Flat ((U j).ι ≫ f)) :
    Flat ((iSup U).ι ≫ f) := by
  let : IsZariskiLocalAtSource @Flat.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.Flat)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Flat.{u})
    (fun j => (iSup U).ι ⁻¹ᵁ U j)
  · rw [← Scheme.Hom.preimage_iSup]
    simp
  · intro j
    rw [← Category.assoc, ← Scheme.Opens.isoOfLE_hom_ι (le_iSup U j), Category.assoc]
    let := hU j
    infer_instance

end Charts

/-! ### The flat neighbourhood theorems -/

/-- Let `f : X ⟶ S` be locally of finite presentation and let `i : Z ⟶ X` be a relative
`H₁`-regular immersion over `S`.  Then there is an open subscheme of `X` containing the image of
`Z` on which `f` is flat. -/
@[stacks 063V "part (1): flat open neighbourhood of a relative H₁-regular immersion"]
theorem exists_open_flat_of_isRelativeH1RegularImmersion
    {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsImmersion i]
    [LocallyOfFinitePresentation f]
    (hi : AlgebraicGeometry.IsRelativeH1RegularImmersion f i) :
    ∃ U : X.Opens, Set.range i.base ⊆ (U : Set X) ∧ Flat (U.ι ≫ f) := by
  classical
  choose U hx hflat using exists_open_flat_at_image f i hi
  refine ⟨iSup U, ?_, flat_iSup_open f U hflat⟩
  rintro _ ⟨z, rfl⟩
  exact (le_iSup U z) (hx z)

/-- **An effective Cartier divisor is a regular immersion.**  The closed immersion of the closed
subscheme of an effective Cartier divisor is a regular immersion. -/
@[ega "IV 21.2.12" "partial"]
theorem isRegularImmersion_subschemeι_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    IsRegularImmersion I.subschemeι := by
  refine isRegularImmersion_of_isRegularIdealSheaf _
    (isRegularIdealSheaf_of_exists_affine_generators X _ fun x _ => ?_)
  obtain ⟨V, hxV, t, ht, hgen⟩ :=
    (Stacks.CartierAffineLocalConverse.isEffectiveCartierDivisor_iff_nonZeroDivisor I).mp hI x
  have hker : RingHom.ker (I.subschemeι.app V.1).hom = Ideal.span (Set.range fun _ : Fin 1 => t) :=
    by rw [I.ker_subschemeι_app V, hgen, Set.range_const]
  refine ⟨V.1, V.2, hxV, 1, fun _ => t, ?_, ?_⟩
  · exact isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span I.subschemeι V.2 _ hker
  · rw [show List.ofFn (fun _ : Fin 1 => t) = [t] from rfl]
    exact (isWeaklyRegular_singleton_iff _ t).mpr
      (isRegular_iff_mem_nonZeroDivisors.mpr ht).left

/-- A relative effective Cartier divisor lies in an open subscheme on which the ambient morphism is
flat, provided that morphism is locally of finite presentation. -/
@[stacks 062V]
theorem exists_open_flat_of_isRelativeEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)
    (hI : Stacks.Divisors.IsRelativeEffectiveCartierDivisor f I)
    [LocallyOfFinitePresentation f] :
    ∃ U : X.Opens, I.supportSet ⊆ (U : Set X) ∧ Flat (U.ι ≫ f) := by
  obtain ⟨U, hU, hflat⟩ := exists_open_flat_of_isRelativeH1RegularImmersion f I.subschemeι
    ⟨hI.2, isH1RegularImmersion_of_isKoszulRegularImmersion _
      (isKoszulRegularImmersion_of_isRegularImmersion _
        (isRegularImmersion_subschemeι_of_isEffectiveCartierDivisor I hI.1))⟩
  refine ⟨U, ?_, hflat⟩
  rwa [I.range_subschemeι] at hU

end Stacks.AlgebraicGeometry

end

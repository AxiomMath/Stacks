module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CartierAffineLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.RelativeSum
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibreDegreeFinrank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.RingTheory.Artinian.Basic

/-!
# The degree of a sum of divisors on a smooth relative curve

Let `f : X ⟶ S` be a morphism of schemes smooth of relative dimension one, and let `D₁` and `D₂`
be closed subschemes of `X` that are finite locally free over `S` of degrees `d₁` and `d₂`. Then
the sum `D₁ + D₂`, the closed subscheme cut out by the product of the two sheaves of ideals, is
finite locally free over `S` of degree `d₁ + d₂`.

Both summands are relative effective Cartier divisors, hence so is their sum, and the sum is
therefore locally quasi-finite, flat and locally of finite presentation over `S`. The two
summands together cover the sum and are finite over `S`, so the sum is universally closed and
separated over `S`, hence proper, hence finite; being also flat and locally of finite
presentation it is finite locally free. Its degree is then computed fibrewise, and on a fibre,
a curve over a field, the degree is the sum over the points of the length of the local ring of
the divisor. At a point the two summands are cut out by nonzerodivisors `a` and `b` of a common
affine chart and the sum by `a * b`, and the exact sequence
`0 → A/(a) → A/(ab) → A/(b) → 0` makes those lengths additive.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_mul`: the sum of two finite locally free divisors
  on a smooth relative curve is finite locally free, of degree the sum of the two degrees.

## Implementation notes

A closed subscheme is presented by its quasi-coherent sheaf of ideals
`AlgebraicGeometry.Scheme.IdealSheafData`, and the sum of two divisors is the product `I * J` of
their sheaves of ideals; the structure morphism of the sum to the base is
`(I * J).subschemeι ≫ f`. Degrees are ranks in the sense of
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank`, that is, ranks of the direct image of the
structure sheaf.

The local degree of a divisor at a point of a curve over a field is the dimension over that
field of the stalk of the divisor, taken to be zero away from the support; it is computed on an
affine chart as the dimension of the quotient of the stalk of the curve by the ideal.

## References

* [Stacks Project, Tag 0B9E](https://stacks.math.columbia.edu/tag/0B9E)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pointwise

universe u

namespace AlgebraicGeometry

private theorem finrank_exact_sequence
    {k : Type u} [Field k]
    {K : Type u} {L : Type u} {M : Type u}
    [AddCommGroup K] [Module k K] [FiniteDimensional k K]
    [AddCommGroup L] [Module k L] [FiniteDimensional k L]
    [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (i : K →ₗ[k] L) (p : L →ₗ[k] M)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p) :
    Module.finrank k L = Module.finrank k K + Module.finrank k M := by
  have hker : p.ker = i.range := LinearMap.exact_iff.mp hip
  have h := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, hker,
    i.finrank_range_of_inj hi] at h
  simpa [add_comm] using h.symm

private theorem finrank_quotient_span_mul
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (a b : A) (hb : b ∈ nonZeroDivisors A)
    [Module.Finite k (A ⧸ Ideal.span {a * b})] :
    Module.finrank k (A ⧸ Ideal.span {a * b}) =
      Module.finrank k (A ⧸ Ideal.span {a}) + Module.finrank k (A ⧸ Ideal.span {b}) := by
  have hideal : Ideal.span {a * b} = b • Ideal.span {a} := by
    rw [← Submodule.ideal_span_singleton_smul b (Ideal.span {a}), Ideal.smul_eq_mul,
      Ideal.span_singleton_mul_span_singleton, mul_comm]
  let e : (A ⧸ Ideal.span {a * b}) ≃ₗ[A] (A ⧸ b • Ideal.span {a}) :=
    Submodule.quotEquivOfEq _ _ hideal
  have : Module.Finite k (A ⧸ b • Ideal.span {a}) :=
    Module.Finite.of_surjective (e.restrictScalars k).toLinearMap e.surjective
  let i : A ⧸ Ideal.span {a} →ₗ[A] A ⧸ b • Ideal.span {a} :=
    Ideal.mulQuot b (Ideal.span {a})
  let p : A ⧸ b • Ideal.span {a} →ₗ[A] A ⧸ Ideal.span {b} :=
    Ideal.quotOfMul b (Ideal.span {a})
  have hi : Function.Injective i := Ideal.mulQuot_injective _ hb
  have hp : Function.Surjective p := Ideal.quotOfMul_surjective _
  have : Module.Finite k (A ⧸ Ideal.span {a}) :=
    Module.Finite.of_injective (i.restrictScalars k) hi
  have : Module.Finite k (A ⧸ Ideal.span {b}) :=
    Module.Finite.of_surjective (p.restrictScalars k) hp
  have hex' : Function.Exact (i.restrictScalars k) (p.restrictScalars k) := by
    rw [LinearMap.exact_iff, LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars]
    exact congrArg (Submodule.restrictScalars k)
      (LinearMap.exact_iff.mp (Ideal.exact_mulQuot_quotOfMul _))
  have hdim := finrank_exact_sequence (i.restrictScalars k) (p.restrictScalars k) hi hp hex'
  rwa [← e.restrictScalars k |>.finrank_eq] at hdim

private theorem finrank_sections_eq_sum_stalks
    (k : Type u) [Field k] (X : Scheme.{u}) [IsAffine X]
    [Algebra k Γ(X, ⊤)] [Module.Finite k Γ(X, ⊤)]
    [Fintype (MaximalSpectrum Γ(X, ⊤))] :
    let x (m : MaximalSpectrum Γ(X, ⊤)) :=
      (isAffineOpen_top X).fromSpec m.toPrimeSpectrum
    let R (m : MaximalSpectrum Γ(X, ⊤)) : Type u := X.presheaf.stalk (x m)
    letI (m : MaximalSpectrum Γ(X, ⊤)) : Algebra k (R m) :=
      ((X.presheaf.germ ⊤ (x m) (by simp)).hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
    Module.finrank k Γ(X, ⊤) = ∑ m, Module.finrank k (R m) := by
  dsimp only
  let A := Γ(X, ⊤)
  let x (m : MaximalSpectrum A) := (isAffineOpen_top X).fromSpec m.toPrimeSpectrum
  let R (m : MaximalSpectrum A) : Type u := X.presheaf.stalk (x m)
  let (m : MaximalSpectrum A) : Algebra A (R m) :=
    (X.presheaf.germ ⊤ (x m) (by simp)).hom.toAlgebra
  let (m : MaximalSpectrum A) : Algebra k (R m) :=
    ((X.presheaf.germ ⊤ (x m) (by simp)).hom.comp (algebraMap k A)).toAlgebra
  have (m : MaximalSpectrum A) : IsScalarTower k A (R m) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have (m : MaximalSpectrum A) : IsLocalization.AtPrime (R m) m.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk' m.toPrimeSpectrum (by simp)
  let e : A ≃ₐ[A] (∀ m : MaximalSpectrum A, R m) :=
    AlgEquiv.ofBijective (Algebra.ofId A (∀ m : MaximalSpectrum A, R m))
      (MaximalSpectrum.algebraMap_pi_bijective A R)
  have (m : MaximalSpectrum A) : Module.Finite k (R m) :=
    Module.Finite.of_surjective
      ((Algebra.linearMap A (R m)).restrictScalars k)
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl (R m))
  change Module.finrank k A = ∑ m : MaximalSpectrum A, Module.finrank k (R m)
  calc
    Module.finrank k A = Module.finrank k (∀ m : MaximalSpectrum A, R m) :=
      (e.toLinearEquiv.restrictScalars k).finrank_eq
    _ = _ := Module.finrank_pi_fintype k

private theorem ker_stalkMap_eq_map_ker_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) (hsurj : Function.Surjective (f.app U))
    (x : X) (hx : f x ∈ U) :
    RingHom.ker (f.stalkMap x).hom =
      (RingHom.ker (f.app U).hom).map (Y.presheaf.germ U (f x) hx).hom := by
  let := Y.presheaf.algebra_section_stalk (⟨f x, hx⟩ : U)
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : f ⁻¹ᵁ U)
  have := hU.isLocalization_stalk ⟨f x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  let p := hU.primeIdealOf ⟨f x, hx⟩
  let q := hV.primeIdealOf ⟨x, hx⟩
  have hp : q.asIdeal.comap (f.app U).hom = p.asIdeal := by
    simpa [p, q, Scheme.Hom.appLE_eq_app] using congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU (f ⁻¹ᵁ U) hV le_rfl hx)
  have hT : Submonoid.map (f.app U).hom p.asIdeal.primeCompl =
      q.asIdeal.primeCompl := by
    simpa only [hp] using
      Ideal.map_primeCompl_comap_of_surjective (f.app U).hom hsurj q.asIdeal
  have he : (f.stalkMap x).hom =
      IsLocalization.map (M := p.asIdeal.primeCompl)
        (S := Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (f.app U).hom (hT.symm ▸ Submonoid.le_comap_map _) := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    rw [IsLocalization.map_comp]
    exact congrArg CommRingCat.Hom.hom (f.germ_stalkMap U x hx)
  rw [he, IsLocalization.ker_map (X.presheaf.stalk x) (f.app U).hom hT]
  rfl

private theorem ker_subscheme_stalkMap
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : I.subscheme) (hx : I.subschemeι x ∈ (U : X.Opens)) :
    RingHom.ker (I.subschemeι.stalkMap x).hom =
      (I.ideal U).map (X.presheaf.germ U (I.subschemeι x) hx).hom := by
  rw [ker_stalkMap_eq_map_ker_app I.subschemeι U U.2
    (U.2.preimage I.subschemeι) (I.subschemeι_app_surjective U) x hx,
    I.ker_subschemeι_app U]

private theorem exists_subscheme_stalk_quotientEquiv
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    (x : I.subscheme) (hx : I.subschemeι x ∈ (U : X.Opens)) :
    ∃ e : (X.presheaf.stalk (I.subschemeι x) ⧸
        (I.ideal U).map (X.presheaf.germ U (I.subschemeι x) hx).hom) ≃+*
        I.subscheme.presheaf.stalk x,
      ∀ a, e (Ideal.Quotient.mk _ a) = I.subschemeι.stalkMap x a := by
  let e := (Ideal.quotientEquivAlgOfEq (X.presheaf.stalk (I.subschemeι x))
    (ker_subscheme_stalkMap I U x hx)).symm.toRingEquiv.trans
    (RingHom.quotientKerEquivOfSurjective (I.subschemeι.stalkMap_surjective x))
  exact ⟨e, fun a => by simp [e]⟩

private theorem isRegular_restrict_affine {X : Scheme.{u}} {U V : X.affineOpens}
    (h : (U : X.Opens) ≤ V.1) (f : Γ(X, V)) (hf : _root_.IsRegular f) :
    _root_.IsRegular ((X.presheaf.map (homOfLE h).op) f) :=
  isRegular_map_of_flat _ ((𝟙 X : X ⟶ X).flat_appLE V.2 U.2 h) hf

private theorem isRegular_germ_of_affine {X : Scheme.{u}} (U : X.affineOpens)
    (x : X) (hx : x ∈ U.1) {a : Γ(X, U.1)} (ha : _root_.IsRegular a) :
    _root_.IsRegular ((X.presheaf.germ U.1 x hx).hom a) := by
  let p : PrimeSpectrum Γ(X, U.1) := U.2.primeIdealOf ⟨x, hx⟩
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization p.asIdeal.primeCompl (X.presheaf.stalk x) :=
    U.2.isLocalization_stalk ⟨x, hx⟩
  have hflat : Module.Flat Γ(X, U.1) (X.presheaf.stalk x) :=
    IsLocalization.flat (X.presheaf.stalk x) p.asIdeal.primeCompl
  change _root_.IsRegular (algebraMap Γ(X, U.1) (X.presheaf.stalk x) a)
  exact isRegular_map_of_flat _ (RingHom.flat_algebraMap_iff.mpr hflat) ha

private theorem exists_common_affine_generators
    {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ a b : Γ(X, U), _root_.IsRegular a ∧ _root_.IsRegular b ∧
        I.ideal U = Ideal.span {a} ∧ J.ideal U = Ideal.span {b} := by
  obtain ⟨V, hxV, a, ha, hIa⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpen_isRegular I hI x
  obtain ⟨W, hxW, b, hb, hJb⟩ :=
    Stacks.CartierAffineLocal.exists_affineOpen_isRegular J hJ x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (V : X.Opens) ⊓ W.1 from ⟨hxV, hxW⟩) (V.1 ⊓ W.1).isOpen
  let A : X.affineOpens := ⟨U, hU⟩
  have hv : A ≤ V := fun _ hx => (hUV hx).1
  have hw : A ≤ W := fun _ hx => (hUV hx).2
  refine ⟨A, hxU, (X.presheaf.map (homOfLE hv).op) a,
    (X.presheaf.map (homOfLE hw).op) b,
    isRegular_restrict_affine hv a ha, isRegular_restrict_affine hw b hb, ?_, ?_⟩
  · rw [← I.map_ideal hv, hIa, Ideal.map_span]
    simp
  · rw [← J.map_ideal hw, hJb, Ideal.map_span]
    simp

/-- The global sections of a scheme finite over a field are finite-dimensional. -/
private alias finite_global_sections_over_field := finite_globalSections

private theorem surjective_coprod_desc_of_comp_subschemeι {X : Scheme.{u}}
    (I J : X.IdealSheafData) (iI : I.subscheme ⟶ (I * J).subscheme)
    (iJ : J.subscheme ⟶ (I * J).subscheme)
    (hiI : iI ≫ (I * J).subschemeι = I.subschemeι)
    (hiJ : iJ ≫ (I * J).subschemeι = J.subschemeι) :
    Function.Surjective (coprod.desc iI iJ) := by
  intro z
  have hx : (I * J).subschemeι z ∈ (I * J).support := by
    change (I * J).subschemeι z ∈ ((I * J).support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hx : (I * J).subschemeι z ∈ I.support ⊔ J.support := by
    simpa only [Scheme.IdealSheafData.support_mul] using hx
  change (I * J).subschemeι z ∈
    ((I.support ⊔ J.support : TopologicalSpace.Closeds X) : Set X) at hx
  rw [TopologicalSpace.Closeds.coe_sup] at hx
  rcases hx with hxI | hxJ
  · obtain ⟨y, hy⟩ : (I * J).subschemeι z ∈ Set.range I.subschemeι :=
      I.range_subschemeι ▸ hxI
    refine ⟨(coprod.inl : I.subscheme ⟶ I.subscheme ⨿ J.subscheme) y, ?_⟩
    change (coprod.inl ≫ coprod.desc iI iJ) y = z
    rw [coprod.inl_desc]
    apply Scheme.Hom.injective (I * J).subschemeι
    change (iI ≫ (I * J).subschemeι) y = (I * J).subschemeι z
    rwa [hiI]
  · obtain ⟨y, hy⟩ : (I * J).subschemeι z ∈ Set.range J.subschemeι :=
      J.range_subschemeι ▸ hxJ
    refine ⟨(coprod.inr : J.subscheme ⟶ I.subscheme ⨿ J.subscheme) y, ?_⟩
    change (coprod.inr ≫ coprod.desc iI iJ) y = z
    rw [coprod.inr_desc]
    apply Scheme.Hom.injective (I * J).subschemeι
    change (iJ ≫ (I * J).subschemeι) y = (I * J).subschemeι z
    rwa [hiJ]

/-- A locally quasi-finite morphism `g`, locally of finite type, is finite as soon as `p ≫ g` is
finite for some finite surjective morphism `p`. -/
private theorem isFinite_of_surjective_of_isFinite_comp {Y Z S : Scheme.{u}} (p : Y ⟶ Z) (g : Z ⟶ S)
    [Surjective p] [IsFinite p] [IsFinite (p ≫ g)] [LocallyOfFiniteType g]
    [LocallyQuasiFinite g] : IsFinite g := by
  have hUC : UniversallyClosed g := UniversallyClosed.of_comp_surjective p g
  have hsep : IsSeparated (Over.mk g).hom := by
    let e : Over.mk (p ≫ g) ⟶ Over.mk g := Over.homMk p rfl
    have : Surjective e.left := inferInstanceAs (Surjective p)
    have : UniversallyClosed e.left := inferInstanceAs (UniversallyClosed p)
    have : IsFinite (Over.mk (p ≫ g)).hom := ‹IsFinite (p ≫ g)›
    have : IsSeparated (Over.mk (p ≫ g)).hom := inferInstance
    exact AlgebraicGeometry.isSeparated_of_surjective_universallyClosed e
  have : IsSeparated g := hsep
  have : IsProper g := (isProper_iff g).2 ⟨hsep, hUC, inferInstance⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

/-- A finite locally free morphism is finite. -/
private theorem isFinite_of_isFiniteLocallyFree {X S : Scheme.{u}} (g : X ⟶ S)
    [Stacks.Morphisms.IsFiniteLocallyFree g] : IsFinite g :=
  ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).1
    inferInstance).1

private theorem product_isFiniteLocallyFree {X S : Scheme.{u}}
    (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (I J : X.IdealSheafData) (d₁ d₂ : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ f) d₁]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (J.subschemeι ≫ f) d₂] :
    Stacks.Morphisms.IsFiniteLocallyFree ((I * J).subschemeι ≫ f) := by
  have : Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₁
  have : Stacks.Morphisms.IsFiniteLocallyFree (J.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₂
  have hIJ' := (isRelativeEffectiveCartierDivisor_iff_locallyQuasiFinite_flat f (I * J)).mp
    (isRelativeEffectiveCartierDivisor_mul f I J
      (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f I)
      (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f J))
  let iI : I.subscheme ⟶ (I * J).subscheme :=
    I.subschemeMap (I * J) (𝟙 X) (by
      intro U
      simp only [Scheme.IdealSheafData.map_id, Scheme.IdealSheafData.ideal_mul]
      exact Ideal.mul_le_left)
  let iJ : J.subscheme ⟶ (I * J).subscheme :=
    J.subschemeMap (I * J) (𝟙 X) (by
      intro U
      simp only [Scheme.IdealSheafData.map_id, Scheme.IdealSheafData.ideal_mul]
      exact Ideal.mul_le_right)
  have hiI : iI ≫ (I * J).subschemeι = I.subschemeι :=
    Scheme.IdealSheafData.subschemeMap_subschemeι I (I * J) (𝟙 X) _
  have hiJ : iJ ≫ (I * J).subschemeι = J.subschemeι :=
    Scheme.IdealSheafData.subschemeMap_subschemeι J (I * J) (𝟙 X) _
  have : IsClosedImmersion (iI ≫ (I * J).subschemeι) := by
    rw [hiI]
    infer_instance
  have : IsClosedImmersion (iJ ≫ (I * J).subschemeι) := by
    rw [hiJ]
    infer_instance
  have : IsClosedImmersion iI := IsClosedImmersion.of_comp_isClosedImmersion iI (I * J).subschemeι
  have : IsClosedImmersion iJ := IsClosedImmersion.of_comp_isClosedImmersion iJ (I * J).subschemeι
  have : IsFinite iI := inferInstance
  have : IsFinite iJ := inferInstance
  have : IsFinite (coprod.desc iI iJ) := inferInstance
  have : Surjective (coprod.desc iI iJ) :=
    ⟨surjective_coprod_desc_of_comp_subschemeι I J iI iJ hiI hiJ⟩
  have : IsFinite (I.subschemeι ≫ f) := isFinite_of_isFiniteLocallyFree _
  have : IsFinite (J.subschemeι ≫ f) := isFinite_of_isFiniteLocallyFree _
  have : IsFinite (coprod.desc iI iJ ≫ (I * J).subschemeι ≫ f) := by
    rw [← Category.assoc, coprod.desc_comp, hiI, hiJ, coprod.desc_comp]
    infer_instance
  have : LocallyOfFiniteType ((I * J).subschemeι ≫ f) := hIJ'.1
  have : LocallyQuasiFinite ((I * J).subschemeι ≫ f) := hIJ'.2.1
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).2
    ⟨isFinite_of_surjective_of_isFinite_comp (coprod.desc iI iJ) _, hIJ'.2.2.1, hIJ'.2.2.2⟩

private noncomputable abbrev sectionAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Algebra k Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra

private noncomputable abbrev stalkAlgebra {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x (by simp)).hom.comp
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)).toAlgebra

private noncomputable def localDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (x : X) : ℕ := by
  classical
  exact if hx : x ∈ I.supportSet then
    let := stalkAlgebra (I.subschemeι ≫ f) ⟨x, hx⟩
    Module.finrank k (I.subscheme.presheaf.stalk ⟨x, hx⟩)
  else 0

private theorem finrank_sections_eq_of_rank {k : Type u} [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) (r : ℕ) [IsFinite g]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r] :
    letI := sectionAlgebra g
    Module.finrank k Γ(Z, ⊤) = r :=
  (isFiniteLocallyFreeOfRank_iff_finrank_eq g r).1 inferInstance

private theorem stalkMap_algebraMap {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (i : Y ⟶ X) (y : Y) (a : k) :
    letI := stalkAlgebra f (i y)
    letI := stalkAlgebra (i ≫ f) y
    i.stalkMap y (algebraMap k (X.presheaf.stalk (i y)) a) =
      algebraMap k (Y.presheaf.stalk y) a := by
  change i.stalkMap y (X.presheaf.germ ⊤ (i y) (by simp)
    (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a))) =
      Y.presheaf.germ ⊤ y (by simp)
        (i.appTop (f.appTop ((Scheme.ΓSpecIso (.of k)).inv a)))
  exact i.germ_stalkMap_apply ⊤ y (by simp) _

private theorem map_ideal_germ_eq_top_of_notMem_supportSet {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (x : X) (hxU : x ∈ U.1)
    (hx : x ∉ I.supportSet) :
    (I.ideal U).map (X.presheaf.germ U x hxU).hom = ⊤ := by
  have hz : x ∉ X.zeroLocus (U := U.1) (I.ideal U) :=
    mt (I.mem_supportSet_iff_of_mem hxU).mpr hx
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hz
  push Not at hz
  obtain ⟨a, ha, hxa⟩ := hz
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
    ((X.mem_basicOpen a x hxU).mp hxa)

private theorem nonempty_stalk_quotient_algEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) (hx : x ∈ I.supportSet) :
    letI := stalkAlgebra f x
    letI := stalkAlgebra (I.subschemeι ≫ f) (⟨x, hx⟩ : I.subscheme)
    Nonempty ((X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hxU).hom) ≃ₐ[k]
      I.subscheme.presheaf.stalk (⟨x, hx⟩ : I.subscheme)) := by
  let := stalkAlgebra f x
  let y : I.subscheme := ⟨x, hx⟩
  let := stalkAlgebra (I.subschemeι ≫ f) y
  obtain ⟨e, he⟩ := exists_subscheme_stalk_quotientEquiv I U y hxU
  exact ⟨{
    __ := e
    commutes' a := (he _).trans (stalkMap_algebraMap f I.subschemeι y a) }⟩

private theorem localDegree_eq_finrank_quotient
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) :
    letI := stalkAlgebra f x
    localDegree f I x = Module.finrank k
      (X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hxU).hom) := by
  classical
  let := stalkAlgebra f x
  by_cases hx : x ∈ I.supportSet
  · let := stalkAlgebra (I.subschemeι ≫ f) (⟨x, hx⟩ : I.subscheme)
    obtain ⟨e'⟩ := nonempty_stalk_quotient_algEquiv f I U x hxU hx
    simpa only [localDegree, dite_eq_left hx] using e'.toLinearEquiv.finrank_eq.symm
  · simp only [localDegree, dite_eq_right hx]
    change 0 = Module.finrank k (X.presheaf.stalk x ⧸
      (I.ideal U).map (X.presheaf.germ U x hxU).hom)
    rw [map_ideal_germ_eq_top_of_notMem_supportSet I U x hxU hx]
    exact (Module.finrank_zero_of_subsingleton (R := k)).symm

private theorem finrank_sections_eq_finsum_stalks
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsFinite g] :
    letI := sectionAlgebra g
    Module.finrank k Γ(Y, ⊤) = ∑ᶠ y : Y,
      letI := stalkAlgebra g y
      Module.finrank k (Y.presheaf.stalk y) := by
  classical
  let := sectionAlgebra g
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : Module.Finite k Γ(Y, ⊤) := finite_global_sections_over_field g
  have : IsArtinianRing Γ(Y, ⊤) := IsArtinianRing.of_finite k _
  let : Fintype (MaximalSpectrum Γ(Y, ⊤)) := Fintype.ofFinite _
  have hb : Function.Bijective ((isAffineOpen_top Y).fromSpec) := by
    rw [IsAffineOpen.fromSpec_top]
    exact (Scheme.homeoOfIso Y.isoSpec.symm).bijective
  let e : MaximalSpectrum Γ(Y, ⊤) ≃ Y := Equiv.ofBijective
    (fun m => (isAffineOpen_top Y).fromSpec m.toPrimeSpectrum)
    (hb.comp IsArtinianRing.primeSpectrumEquivMaximalSpectrum.symm.bijective)
  rw [finrank_sections_eq_sum_stalks k Y, ← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  rfl

private theorem finite_points_over_field
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsFinite g] : Finite Y := by
  let := sectionAlgebra g
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : Module.Finite k Γ(Y, ⊤) := finite_global_sections_over_field g
  have : IsArtinianRing Γ(Y, ⊤) := IsArtinianRing.of_finite k _
  exact Finite.of_equiv (PrimeSpectrum Γ(Y, ⊤))
    (Scheme.homeoOfIso Y.isoSpec.symm).toEquiv

private theorem finite_stalk_over_field
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsFinite g] (y : Y) :
    letI := stalkAlgebra g y
    Module.Finite k (Y.presheaf.stalk y) := by
  let := sectionAlgebra g
  let := stalkAlgebra g y
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : Module.Finite k Γ(Y, ⊤) := finite_global_sections_over_field g
  have : IsArtinianRing Γ(Y, ⊤) := IsArtinianRing.of_finite k _
  let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ ⊤ y (by simp)).hom.toAlgebra
  have : IsScalarTower k Γ(Y, ⊤) (Y.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let p := (isAffineOpen_top Y).primeIdealOf ⟨y, by simp⟩
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) p.asIdeal :=
    (isAffineOpen_top Y).isLocalization_stalk ⟨y, by simp⟩
  exact Module.Finite.of_surjective
    ((Algebra.linearMap Γ(Y, ⊤) (Y.presheaf.stalk y)).restrictScalars k)
    (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Y.presheaf.stalk y))

private theorem finite_stalk_quotient
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    [IsFinite (I.subschemeι ≫ f)]
    (U : X.affineOpens) (x : X) (hxU : x ∈ U.1) :
    letI := stalkAlgebra f x
    Module.Finite k
      (X.presheaf.stalk x ⧸ (I.ideal U).map (X.presheaf.germ U x hxU).hom) := by
  classical
  let := stalkAlgebra f x
  by_cases hx : x ∈ I.supportSet
  · let y : I.subscheme := ⟨x, hx⟩
    let := stalkAlgebra (I.subschemeι ≫ f) y
    have : Module.Finite k (I.subscheme.presheaf.stalk y) :=
      finite_stalk_over_field (I.subschemeι ≫ f) y
    obtain ⟨e'⟩ := nonempty_stalk_quotient_algEquiv f I U x hxU hx
    exact Module.Finite.of_injective e'.toLinearMap e'.injective
  · rw [map_ideal_germ_eq_top_of_notMem_supportSet I U x hxU hx]
    infer_instance

private theorem localDegree_hasFiniteSupport
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    [IsFinite (I.subschemeι ≫ f)] : (localDegree f I).HasFiniteSupport := by
  have : Finite I.subscheme := finite_points_over_field (I.subschemeι ≫ f)
  have hfin : I.supportSet.Finite := by
    rw [show I.supportSet = (I.support : Set X) from
      Set.ext fun _ => Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
    simpa only [I.range_subschemeι] using Set.finite_range I.subschemeι
  apply hfin.subset
  intro x hx
  by_contra hn
  exact hx (by simp [localDegree, hn])

private theorem localDegree_mul
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I J : X.IdealSheafData)
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
    (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
    [IsFinite ((I * J).subschemeι ≫ f)] (x : X) :
    localDegree f (I * J) x = localDegree f I x + localDegree f J x := by
  obtain ⟨U, hxU, a, b, ha, hb, hIa, hJb⟩ := exists_common_affine_generators I J hI hJ x
  let := stalkAlgebra f x
  let ρ := (X.presheaf.germ U x hxU).hom
  have hIJ : ((I * J).ideal U).map ρ = Ideal.span {ρ a * ρ b} := by
    simp [Scheme.IdealSheafData.ideal_mul, hIa, hJb, Ideal.span_singleton_mul_span_singleton,
      Ideal.map_span]
  have hI' : (I.ideal U).map ρ = Ideal.span {ρ a} := by simp [hIa, Ideal.map_span]
  have hJ' : (J.ideal U).map ρ = Ideal.span {ρ b} := by simp [hJb, Ideal.map_span]
  have : Module.Finite k (X.presheaf.stalk x ⧸ Ideal.span {ρ a * ρ b}) := by
    rw [← hIJ]
    exact finite_stalk_quotient f (I * J) U x hxU
  rw [localDegree_eq_finrank_quotient f (I * J) U x hxU,
    localDegree_eq_finrank_quotient f I U x hxU,
    localDegree_eq_finrank_quotient f J U x hxU]
  change Module.finrank k (X.presheaf.stalk x ⧸ ((I * J).ideal U).map ρ) =
    Module.finrank k (X.presheaf.stalk x ⧸ (I.ideal U).map ρ) +
      Module.finrank k (X.presheaf.stalk x ⧸ (J.ideal U).map ρ)
  rw [hIJ, hI', hJ']
  exact finrank_quotient_span_mul (ρ a) (ρ b)
    (isRegular_iff_mem_nonZeroDivisors.mp (isRegular_germ_of_affine U x hxU hb))

private theorem finrank_sections_eq_finsum_localDegree
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    [IsFinite (I.subschemeι ≫ f)] :
    letI := sectionAlgebra (I.subschemeι ≫ f)
    Module.finrank k Γ(I.subscheme, ⊤) = ∑ᶠ x, localDegree f I x := by
  classical
  rw [finrank_sections_eq_finsum_stalks]
  change (∑ᶠ y : I.supportSet,
    let := stalkAlgebra (I.subschemeι ≫ f) y
    Module.finrank k (I.subscheme.presheaf.stalk y)) = _
  calc
    _ = ∑ᶠ y : I.supportSet, localDegree f I y := by
      refine finsum_congr fun y => ?_
      simp only [localDegree, dite_eq_left y.2]
      rfl
    _ = _ := by
      rw [finsum_subtype_eq_finsum_cond]
      refine finsum_congr fun x => ?_
      by_cases hx : x ∈ I.supportSet <;> simp [hx, localDegree]

private theorem isFiniteLocallyFreeOfRank_of_fibers
    {Y S : Scheme.{u}} (g : Y ⟶ S) [Stacks.Morphisms.IsFiniteLocallyFree g]
    (r : ℕ) (h : ∀ s, Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (g.fiberToSpecResidueField s) r) : Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r := by
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).1
      inferInstance
  have _ : IsFinite g := hfin
  have _ : Flat g := hflat
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq g r).2 fun s => ?_
  have hs : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
    (g.fiberToSpecResidueField s) r := h s
  obtain ⟨hfin', hflat', -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (g.fiberToSpecResidueField s)).1
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r)
  have _ : IsFinite (g.fiberToSpecResidueField s) := hfin'
  have _ : Flat (g.fiberToSpecResidueField s) := hflat'
  let y : Spec (S.residueField s) := IsLocalRing.closedPoint (S.residueField s)
  have h₁ : (g.fiberToSpecResidueField s).finrank y = r :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq
      (g.fiberToSpecResidueField s) r).1 (h s) y
  have h₂ : (g.fiberToSpecResidueField s).finrank y =
      g.finrank (S.fromSpecResidueField s y) :=
    Scheme.Hom.finrank_of_isPullback _ _ _ _ (IsPullback.of_hasPullback _ _) y
  rw [Scheme.fromSpecResidueField_apply] at h₂
  exact h₂.symm.trans h₁

/-- Base changing a closed subscheme: along a cartesian square, the structure morphism of the
closed subscheme cut out by the inverse image ideal sheaf is the base change of the structure
morphism of the closed subscheme cut out by the original ideal sheaf. -/
public theorem exists_isPullback_subschemeι_baseChange
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {g' : X' ⟶ X} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    (I : X.IdealSheafData) :
    ∃ a : (I.comap g').subscheme ⟶ I.subscheme,
      IsPullback a ((I.comap g').subschemeι ≫ f') (I.subschemeι ≫ f) g := by
  let a := (I.comapIso g').hom ≫ pullback.snd g' I.subschemeι
  have hs : IsPullback (I.comap g').subschemeι a g' I.subschemeι := by
    apply (IsPullback.of_hasPullback g' I.subschemeι).of_iso'
      (I.comapIso g') (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simp [a]
    · simp
    · simp
  exact ⟨a, hs.flip.paste_vert sq⟩

private theorem isFiniteLocallyFreeOfRank_mul_of_field
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    (I J : X.IdealSheafData) (d₁ d₂ : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ f) d₁]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (J.subschemeι ≫ f) d₂] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I * J).subschemeι ≫ f) (d₁ + d₂) := by
  have : Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₁
  have : Stacks.Morphisms.IsFiniteLocallyFree (J.subschemeι ≫ f) :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d₂
  have : Stacks.Morphisms.IsFiniteLocallyFree ((I * J).subschemeι ≫ f) :=
    product_isFiniteLocallyFree f I J d₁ d₂
  have : IsFinite (I.subschemeι ≫ f) := isFinite_of_isFiniteLocallyFree _
  have : IsFinite (J.subschemeι ≫ f) := isFinite_of_isFiniteLocallyFree _
  have : IsFinite ((I * J).subschemeι ≫ f) := isFinite_of_isFiniteLocallyFree _
  have hI := (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f I).1
  have hJ := (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree f J).1
  refine (isFiniteLocallyFreeOfRank_iff_finrank_eq ((I * J).subschemeι ≫ f) (d₁ + d₂)).2 ?_
  let := sectionAlgebra (I.subschemeι ≫ f)
  let := sectionAlgebra (J.subschemeι ≫ f)
  let := sectionAlgebra ((I * J).subschemeι ≫ f)
  rw [finrank_sections_eq_finsum_localDegree f (I * J)]
  simp_rw [localDegree_mul f I J hI hJ]
  rw [finsum_add_distrib (localDegree_hasFiniteSupport f I)
    (localDegree_hasFiniteSupport f J),
    ← finrank_sections_eq_finsum_localDegree f I,
    ← finrank_sections_eq_finsum_localDegree f J, finrank_sections_eq_of_rank (I.subschemeι ≫ f) d₁,
    finrank_sections_eq_of_rank (J.subschemeι ≫ f) d₂]

/-- **Stacks Project, Tag 0B9E.** Let `f : X ⟶ S` be smooth of relative dimension one and let
`I` and `J` be quasi-coherent sheaves of ideals on `X` whose closed subschemes are finite
locally free over `S` of degrees `d₁` and `d₂`. The sum of the two divisors, cut out by the
product `I * J`, is finite locally free over `S` of degree `d₁ + d₂`. -/
@[stacks 0B9E]
theorem isFiniteLocallyFreeOfRank_mul
    {X S : Scheme.{u}} (f : X ⟶ S) [SmoothOfRelativeDimension 1 f]
    (I J : X.IdealSheafData) (d₁ d₂ : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (I.subschemeι ≫ f) d₁]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (J.subschemeι ≫ f) d₂] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I * J).subschemeι ≫ f) (d₁ + d₂) := by
  have : Stacks.Morphisms.IsFiniteLocallyFree ((I * J).subschemeι ≫ f) :=
    product_isFiniteLocallyFree f I J d₁ d₂
  refine isFiniteLocallyFreeOfRank_of_fibers _ _ fun s => ?_
  let f' := f.fiberToSpecResidueField s
  let g' := f.fiberι s
  have sq : IsPullback g' f' f (S.fromSpecResidueField s) :=
    IsPullback.of_hasPullback f (S.fromSpecResidueField s)
  obtain ⟨aI, hI⟩ := exists_isPullback_subschemeι_baseChange sq I
  obtain ⟨aJ, hJ⟩ := exists_isPullback_subschemeι_baseChange sq J
  obtain ⟨aD, hD⟩ := exists_isPullback_subschemeι_baseChange sq (I * J)
  have hIrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((I.comap g').subschemeι ≫ f') d₁ :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hI
  have hJrank : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((J.comap g').subschemeι ≫ f') d₂ :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hJ
  have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have hsm : SmoothOfRelativeDimension 1 f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  have hd : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (((I * J).comap g').subschemeι ≫ f') (d₁ + d₂) := by
    rw [AlgebraicGeometry.comap_mul]
    exact @isFiniteLocallyFreeOfRank_mul_of_field (S.residueField s) inferInstance
      (f.fiber s) f' hsm (I.comap g') (J.comap g') d₁ d₂ hIrank hJrank
  have he : IsPullback hD.isoPullback.inv
      (((I * J).subschemeι ≫ f).fiberToSpecResidueField s)
      (((I * J).comap g').subschemeι ≫ f') (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      simpa only [Category.comp_id, Scheme.Hom.fiberToSpecResidueField]
        using hD.isoPullback_inv_snd⟩
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback he

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Curves.FlatMorphism
public import StacksFrontier.AlgebraicGeometry.Curves.FrobeniusTwistCurve
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.Curves.InseparableFrobeniusFactorization
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibreDegreeFinrank
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.ResidueFieldAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Closed points of small degree from a morphism to the projective line

Let `X` be a proper curve over a field `k` and `φ : X ⟶ 𝐏¹_k` a nonconstant morphism over `k`.
Then `φ` is finite and flat, hence finite locally free of rank `deg(X/𝐏¹_k)`, so every point of
`X` over a rational point of `𝐏¹_k` is a closed point whose residue field has degree at most
`deg(X/𝐏¹_k)` over `k`. Such a point has a separable residue field when `k` is perfect, or when
`φ` is étale at it; over an infinite field the image of a nonempty open on which `φ` is étale
contains a rational point. These are the steps of [Stacks, Tag 0CD4] that turn a morphism to
`𝐏¹_k` of degree at most `2g - 2` into a closed point with separable residue field of degree at
most `2g - 2`.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_degreeOver_of_not_constant`: a nonconstant
  morphism of proper curves with normal target is finite locally free of rank `deg(X/Y)`
  ([Stacks, Tag 0CCK], [Stacks, Tag 0CCL], [Stacks, Tag 02KB]).
* `AlgebraicGeometry.finrank_residueField_le_of_isFiniteLocallyFreeOfRank`: the residue degrees
  of a finite locally free morphism of rank `d` are at most `d` ([Stacks, Tag 0CC2],
  [Stacks, Tag 03J5]).
* `AlgebraicGeometry.finrank_residueField_le_degreeOver`: hence `[κ(x) : κ(f(x))] ≤ deg(X/Y)`.
* `AlgebraicGeometry.exists_section_projectiveLine_mem_of_isOpen`: over an infinite field every
  nonempty open of `𝐏¹_k` contains a rational point.
* `AlgebraicGeometry.exists_isClosed_isSeparable_finrank_le_degreeOver_of_perfectField` and
  `AlgebraicGeometry.exists_isClosed_isSeparable_finrank_le_degreeOver_of_etale`: a closed point
  with separable residue field of degree at most `deg(X/𝐏¹_k)`, over a perfect field, and over an
  infinite field when `φ` is étale on a nonempty open ([Stacks, Tag 02GL]).
* `AlgebraicGeometry.not_constant_of_etale`: a morphism to `𝐏¹_k` étale on a nonempty open is
  nonconstant.
* `AlgebraicGeometry.genus_frobeniusTwist_curve` and
  `AlgebraicGeometry.isIso_globalSections_frobeniusTwist_curve`: the Frobenius twist `X^{(p)}` has
  the genus of `X` and, when `H⁰(X, 𝒪_X) = k`, only constant global functions
  ([Stacks, Tag 0BY9] along the Frobenius of `k`).

## Implementation notes

The residue field `κ(x)` is a `k`-algebra through the structure morphism followed by evaluation
at `x`, the convention of `AlgebraicGeometry.isClosed_singleton_of_module_finite_residueField`. A
rational point of `𝐏¹_k` is a section of the structure morphism; the degree of its residue field
is computed by `AlgebraicGeometry.isClosed_and_finrank_residueField_of_section`.

## References

* [Stacks Project, Tag 0CD4](https://stacks.math.columbia.edu/tag/0CD4)
* [Stacks Project, Tag 0CCK](https://stacks.math.columbia.edu/tag/0CCK)
* [Stacks Project, Tag 0CCL](https://stacks.math.columbia.edu/tag/0CCL)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 0CC2](https://stacks.math.columbia.edu/tag/0CC2)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
* [Stacks Project, Tag 02GL](https://stacks.math.columbia.edu/tag/02GL)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of k))
  (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY] [IsProper πX] [IsProper πY]

/-- **A nonconstant morphism of proper curves with normal target is finite locally free of rank
its degree.** If `f : X ⟶ Y` is a nonconstant morphism over `k` of proper curves and `Y` is
normal, then `f` is finite locally free of rank `deg(X/Y)`. -/
theorem isFiniteLocallyFreeOfRank_degreeOver_of_not_constant [IsNormal Y] (f : X ⟶ Y)
    (hf : f ≫ πY = πX) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank f
      (@degreeOver X Y f _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY f hf)
        (isDominant_of_not_constant k πX πY f hnc)) := by
  have : IsFinite f := isFinite_of_not_constant k πX πY f hf hnc
  have hrange : (Set.range f).Nontrivial := by
    by_contra h
    rw [Set.not_nontrivial_iff] at h
    exact hnc ⟨f.base (genericPoint X), fun x => h ⟨x, rfl⟩ ⟨_, rfl⟩⟩
  have : Flat f :=
    (Flat.iff_flat_stalkMap f).2 (isFlat_of_nonconstant_of_isNormal πX πY f hf hrange)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian πY
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree f :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian f).2
      ⟨‹_›, ‹_›⟩
  have := hflf.toIsFiniteLocallyFree
  exact (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff f _).2 ⟨inferInstance,
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq _ _ (genericPoint Y)
      (fiberRank_pushforward_unit_genericPoint_eq_degreeOver k πX πY f hf hnc)⟩

/-- The canonical map from the fibre of a finite morphism to the spectrum of the residue field
is finite. -/
private theorem isFinite_fiberToSpecResidueField {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : Y) : IsFinite (f.fiberToSpecResidueField y) :=
  MorphismProperty.of_isPullback (P := @IsFinite)
    (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹_›

/-- The ring of global sections of a fibre of a finite locally free morphism of rank `d` has
dimension `d` over the residue field. -/
theorem finrank_globalSections_fiber_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] [IsFinite f] (y : Y) :
    letI := ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      (f.fiberToSpecResidueField y).appTop).hom.toAlgebra
    Module.finrank (Y.residueField y) Γ(f.fiber y, ⊤) = d := by
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (f.fiberToSpecResidueField y) d :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y))
  have := isFinite_fiberToSpecResidueField f y
  exact (@isFiniteLocallyFreeOfRank_iff_finrank_eq (Y.residueField y) _ _
    (f.fiberToSpecResidueField y) ‹_› d).mp ‹_›

/-- **The residue degrees of a finite locally free morphism of rank `d` are at most `d`.** The
point `x` is a closed point of the fibre through it, which is finite of degree `d` over the
residue field of the base point, so `κ(x)` is a quotient of the ring of functions on that
fibre. -/
theorem finrank_residueField_le_of_isFiniteLocallyFreeOfRank {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank f d] [IsFinite f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f.base x)) (X.residueField x) ∧
      Module.finrank (Y.residueField (f.base x)) (X.residueField x) ≤ d := by
  let := (f.residueFieldMap x).hom.toAlgebra
  let := ((Scheme.ΓSpecIso (Y.residueField (f.base x))).inv ≫
      (f.fiberToSpecResidueField (f.base x)).appTop).hom.toAlgebra
  have hd := finrank_globalSections_fiber_eq f d (f.base x)
  have := isFinite_fiberToSpecResidueField f (f.base x)
  have hfin : Module.Finite (Y.residueField (f.base x)) Γ(f.fiber (f.base x), ⊤) :=
    @module_finite_globalSections_of_isFinite _ _ (f.fiberToSpecResidueField (f.base x)) ‹_›
  have : IsArtinianRing Γ(f.fiber (f.base x), ⊤) :=
    IsArtinianRing.of_finite (Y.residueField (f.base x)) _
  have : DiscreteTopology (f.fiber (f.base x)) :=
    (f.fiber (f.base x)).isoSpec.hom.homeomorph.symm.discreteTopology
  have : IsClosedImmersion (f.asFiberHom x) :=
    .of_isPreimmersion _ (by rw [Scheme.Hom.range_asFiberHom]; exact isClosed_discrete _)
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (f.asFiberHom x)).2
  have hcomp : ∀ c : Y.residueField (f.base x),
      (Scheme.ΓSpecIso (X.residueField x)).hom ((f.asFiberHom x).appTop
        (algebraMap (Y.residueField (f.base x)) Γ(f.fiber (f.base x), ⊤) c)) =
        algebraMap (Y.residueField (f.base x)) (X.residueField x) c := by
    intro c
    have h1 := congrArg Scheme.Hom.appTop (f.asFiberHom_fiberToSpecResidueField x)
    rw [Scheme.Hom.comp_appTop] at h1
    have h2 := Scheme.ΓSpecIso_naturality (f.residueFieldMap x)
    have := congrArg (fun g => ((Scheme.ΓSpecIso (Y.residueField (f.base x))).inv ≫ g ≫
      (Scheme.ΓSpecIso (X.residueField x)).hom).hom c) h1
    simp only [Category.assoc, h2, Iso.inv_hom_id_assoc] at this
    exact this
  let L : Γ(f.fiber (f.base x), ⊤) →ₗ[Y.residueField (f.base x)] X.residueField x :=
    { toFun := fun a => (Scheme.ΓSpecIso (X.residueField x)).hom ((f.asFiberHom x).appTop a)
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hcomp]
        rfl }
  have hL : Function.Surjective L := fun z => by
    obtain ⟨a, ha⟩ := hsurj ((Scheme.ΓSpecIso (X.residueField x)).inv z)
    exact ⟨a, by simp [L, ha]⟩
  have := LinearMap.finrank_range_le L
  rw [LinearMap.range_eq_top.mpr hL, finrank_top] at this
  exact ⟨Module.Finite.of_surjective L hL, by omega⟩

/-- **The residue degrees of a nonconstant morphism of proper curves with normal target are at
most its degree.** The morphism is finite and flat, hence finite locally free, of rank
`deg(X/Y)`; each residue degree `[κ(x) : κ(f(x))]` is bounded by that rank. -/
theorem finrank_residueField_le_degreeOver [IsNormal Y] (f : X ⟶ Y) (hf : f ≫ πY = πX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (f.base x)) (X.residueField x) ∧
      Module.finrank (Y.residueField (f.base x)) (X.residueField x) ≤
        @degreeOver X Y f _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY f hf)
          (isDominant_of_not_constant k πX πY f hnc) := by
  have : IsFinite f := isFinite_of_not_constant k πX πY f hf hnc
  have := isFiniteLocallyFreeOfRank_degreeOver_of_not_constant πX πY f hf hnc
  exact finrank_residueField_le_of_isFiniteLocallyFreeOfRank f _ x

/-- **A point over a rational point of the target has residue degree at most the degree.** Let
`f : X ⟶ Y` be a nonconstant morphism of proper curves over `k` with normal target, and let `x`
map to a point `y` with `[κ(y) : k] = 1`. Then `x` is a closed point, `κ(x)` is finite over `k`
of degree at most `deg(X/Y)`, and `κ(x)/k` is separable as soon as `κ(x)/κ(y)` is. -/
theorem isClosed_finrank_residueField_le_degreeOver_of_finrank_eq_one [IsNormal Y]
    (f : X ⟶ Y) (hf : f ≫ πY = πX) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) (x : X)
    (hy : letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ πY.appTop ≫
        Y.Γevaluation (f.base x)).hom.toAlgebra
      Module.finrank k (Y.residueField (f.base x)) = 1) :
    IsClosed ({x} : Set X) ∧
      (letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom.toAlgebra;
      Module.Finite k (X.residueField x) ∧
        Module.finrank k (X.residueField x) ≤
          @degreeOver X Y f _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY f hf)
            (isDominant_of_not_constant k πX πY f hnc) ∧
        (letI := (f.residueFieldMap x).hom.toAlgebra;
          Algebra.IsSeparable (Y.residueField (f.base x)) (X.residueField x) →
            Algebra.IsSeparable k (X.residueField x))) := by
  obtain ⟨hfinxy, hle⟩ := finrank_residueField_le_degreeOver πX πY f hf hnc x
  let algY := ((Scheme.ΓSpecIso (.of k)).inv ≫ πY.appTop ≫
    Y.Γevaluation (f.base x)).hom.toAlgebra
  let algX := ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let algXY := (f.residueFieldMap x).hom.toAlgebra
  have htower : IsScalarTower k (Y.residueField (f.base x)) (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    show ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom c =
      (f.residueFieldMap x).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ πY.appTop ≫
        Y.Γevaluation (f.base x)).hom c)
    subst hf
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    exact (Scheme.Γevaluation_naturality_apply f x _).symm
  have hfinY : Module.Finite k (Y.residueField (f.base x)) :=
    Module.finite_of_finrank_eq_succ hy
  have hfinX : Module.Finite k (X.residueField x) :=
    Module.Finite.trans (Y.residueField (f.base x)) (X.residueField x)
  have hrank : Module.finrank k (X.residueField x) =
      Module.finrank (Y.residueField (f.base x)) (X.residueField x) := by
    rw [← Module.finrank_mul_finrank k (Y.residueField (f.base x)) (X.residueField x), hy,
      one_mul]
  refine ⟨isClosed_singleton_of_module_finite_residueField πX x hfinX, hfinX, hrank ▸ hle,
    fun hsep => ?_⟩
  have hbij : Function.Bijective (algebraMap k (Y.residueField (f.base x))) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hy
  have : Algebra.IsSeparable k (Y.residueField (f.base x)) :=
    Algebra.IsSeparable.of_algHom k k (AlgEquiv.ofBijective (Algebra.ofId k _) hbij).symm.toAlgHom
  exact Algebra.IsSeparable.trans k (Y.residueField (f.base x)) (X.residueField x)

/-! ### Rational points in open subsets of the affine and projective line -/

/-- **Over an infinite field every nonempty open subset of affine space contains a rational
point**: there is a section of `𝔸(σ; k) ⟶ Spec k` whose point lies in the open. A nonempty open
contains a basic open `D(p)` with `p ≠ 0`, and a nonzero polynomial over an infinite field does
not vanish at some `a ∈ k^σ`; the section is evaluation at `a`. -/
@[sga "3 VIA 2.5.4" "special case"]
theorem exists_section_affineSpace_mem_of_isOpen [Infinite k] {σ : Type u}
    (W : Set 𝔸(σ; Spec (.of k))) (hW : IsOpen W) (hne : W.Nonempty) :
    ∃ s : Spec (.of k) ⟶ 𝔸(σ; Spec (.of k)),
      s ≫ (𝔸(σ; Spec (.of k)) ↘ Spec (.of k)) = 𝟙 _ ∧ ∀ p, s.base p ∈ W := by
  classical
  let R := MvPolynomial σ k
  let e : 𝔸(σ; Spec (.of k)) ≅ Spec (.of R) := AffineSpace.SpecIso σ (.of k)
  obtain ⟨x₀, hx₀⟩ := hne
  let homeo := Scheme.homeoOfIso e
  have hO : IsOpen (homeo '' W) := homeo.isOpenMap _ hW
  obtain ⟨_, ⟨q, rfl⟩, hq, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp hO (homeo x₀) ⟨x₀, hx₀, rfl⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot] at hq
    exact absurd hq (Set.notMem_empty _)
  obtain ⟨a, ha⟩ : ∃ a : σ → k, MvPolynomial.eval a q ≠ 0 := by
    by_contra! h
    exact hq0 (MvPolynomial.funext fun x => by simpa using h x)
  let ψ : R →ₐ[k] k := MvPolynomial.aeval a
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ e.inv, ?_, fun p => ?_⟩
  · rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    show ψ (MvPolynomial.C c) = c
    rw [MvPolynomial.aeval_C]
    rfl
  · let qpt : PrimeSpectrum R := PrimeSpectrum.comap ψ.toRingHom ⊥
    have hqpt : qpt ∈ PrimeSpectrum.basicOpen q := by
      rw [PrimeSpectrum.mem_basicOpen]
      show q ∉ Ideal.comap ψ.toRingHom (⊥ : Ideal k)
      rw [Ideal.mem_comap, Ideal.mem_bot]
      show MvPolynomial.eval₂ (algebraMap k k) a q ≠ 0
      exact ha
    have hpt : Spec.map (CommRingCat.ofHom ψ.toRingHom) p = (qpt : Spec (.of R)) := by
      have : p = OrderDual.ofDual
          (AlgebraicGeometry.primeSpectrumOrderIsoSpec k (⊥ : PrimeSpectrum k)) :=
        Subsingleton.elim _ _
      rw [this, AlgebraicGeometry.Spec.map_apply]
      rfl
    have hp : Spec.map (CommRingCat.ofHom ψ.toRingHom) p ∈ PrimeSpectrum.basicOpen q := by
      rwa [hpt]
    obtain ⟨w, hw, hweq⟩ := hsub hp
    show e.inv (Spec.map (CommRingCat.ofHom ψ.toRingHom) p) ∈ W
    rw [← hweq]
    have h1 : e.inv (homeo w) = w := by
      show (e.hom ≫ e.inv).base w = w
      rw [e.hom_inv_id]
      rfl
    rwa [h1]

/-- **Over an infinite field every nonempty open subset of the projective line contains a
rational point**: there is a section of `𝐏¹_k ⟶ Spec k` whose point lies in the open. The
standard chart `𝔸¹_k ⟶ 𝐏¹_k` is an open immersion with nonempty image, which meets the open
because `𝐏¹_k` is irreducible, and the preimage contains a rational point of `𝔸¹_k`. -/
@[sga "3 VIA 2.5.4" "special case"]
theorem exists_section_projectiveLine_mem_of_isOpen [Infinite k]
    (U : Set (projectiveSpaceOver 1 (Spec (.of k)))) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ s : Spec (.of k) ⟶ projectiveSpaceOver 1 (Spec (.of k)),
      s ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 _ ∧ ∀ p, s.base p ∈ U := by
  let c := projectiveSpaceOver.affineChart 1 0
    (Equiv.ulift : ULift.{u} {j : Fin 2 // j ≠ 0} ≃ _) (Spec (.of k))
  have hW : IsOpen (c.base ⁻¹' U) := hU.preimage c.continuous
  have hWne : (c.base ⁻¹' U).Nonempty := by
    have hpt : (Set.range c.base).Nonempty :=
      ⟨_, ⟨(AffineSpace.homOfVector (n := ULift.{u} {j : Fin 2 // j ≠ 0})
        (𝟙 (Spec (.of k))) 0).base (IsLocalRing.closedPoint k), rfl⟩⟩
    obtain ⟨_, ⟨w, rfl⟩, hw⟩ :=
      nonempty_preirreducible_inter c.isOpenEmbedding.isOpen_range hU hpt hne
    exact ⟨w, hw⟩
  obtain ⟨s, hs, hsW⟩ := exists_section_affineSpace_mem_of_isOpen _ hW hWne
  refine ⟨s ≫ c, ?_, fun p => hsW p⟩
  rw [Category.assoc, projectiveSpaceOver.affineChart_over, hs]

/-! ### Closed points of small degree from a morphism to the projective line -/

attribute [local instance] isCurve_projectiveSpaceOver_one

/-- The projective line over a field is normal: it is smooth over the normal scheme `Spec k`. -/
theorem isNormal_projectiveSpaceOver_one (k : Type u) [Field k] :
    IsNormal (projectiveSpaceOver 1 (Spec (.of k))) := by
  have : IsNormal (Spec (CommRingCat.of k)) := isNormal_spec_of_isIntegrallyClosed k
  exact isNormal_of_smooth (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))

/-- **A point over a rational point of `𝐏¹_k`.** Let `φ : X ⟶ 𝐏¹_k` be a nonconstant morphism over
`k` from a proper curve and `σ` a rational point of `𝐏¹_k`. Some point `x` maps to `σ`; it is
closed, `κ(x)` is finite over `k` of degree at most `deg(X/𝐏¹_k)`, and `κ(x)/k` is separable as
soon as `κ(x)/κ(σ)` is. -/
theorem exists_isClosed_finrank_residueField_le_degreeOver_of_section
    (φ : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hφ : φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = πX)
    (hnc : ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, φ.base x = y)
    (σ : Spec (.of k) ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hσ : σ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = 𝟙 _)
    (x : X) (hx : φ.base x = σ.base (IsLocalRing.closedPoint k)) :
    IsClosed ({x} : Set X) ∧
      (letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom.toAlgebra;
      Module.Finite k (X.residueField x) ∧
        Module.finrank k (X.residueField x) ≤
          @degreeOver X _ φ _ _ (locallyOfFiniteType_of_isCurve_comp k πX
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hφ)
            (isDominant_of_not_constant k πX
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hnc) ∧
        (letI := (φ.residueFieldMap x).hom.toAlgebra;
          Algebra.IsSeparable (projectiveSpaceOver 1 (Spec (.of k)) |>.residueField (φ.base x))
            (X.residueField x) → Algebra.IsSeparable k (X.residueField x))) := by
  have := isNormal_projectiveSpaceOver_one k
  refine isClosed_finrank_residueField_le_degreeOver_of_finrank_eq_one πX
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hφ hnc x ?_
  have h := (isClosed_and_finrank_residueField_of_section
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) σ hσ (IsLocalRing.closedPoint k)).2
  rwa [← hx] at h

/-- **A separable closed point of small degree, over a perfect field.** A nonconstant morphism
`φ : X ⟶ 𝐏¹_k` from a proper curve over a perfect field `k` gives a closed point `x` of `X` with
`κ(x)/k` finite separable of degree at most `deg(X/𝐏¹_k)`: take any point over a rational point
of `𝐏¹_k`. -/
theorem exists_isClosed_isSeparable_finrank_le_degreeOver_of_perfectField [PerfectField k]
    (φ : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hφ : φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = πX)
    (hnc : ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, φ.base x = y) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      (letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom.toAlgebra;
      Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x) ∧
        Module.finrank k (X.residueField x) ≤
          @degreeOver X _ φ _ _ (locallyOfFiniteType_of_isCurve_comp k πX
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hφ)
            (isDominant_of_not_constant k πX
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hnc)) := by
  obtain ⟨σ, hσ⟩ := Stacks.ProjectiveBundleSplitting.exists_section_projectiveSpaceOver 1
    (Spec (.of k))
  have : IsFinite φ := isFinite_of_not_constant k πX
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hφ hnc
  have : IsDominant φ := isDominant_of_not_constant k πX
    (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hnc
  obtain ⟨x, hx⟩ := (surjective_of_isIntegralHom_of_isDominant φ).surj
    (σ.base (IsLocalRing.closedPoint k))
  obtain ⟨hcl, hfin, hle, -⟩ :=
    exists_isClosed_finrank_residueField_le_degreeOver_of_section πX φ hφ hnc σ hσ x hx
  let := ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  exact ⟨x, hcl, hfin, Algebra.IsAlgebraic.isSeparable_of_perfectField, hle⟩

/-- **A separable closed point of small degree, from a generically étale morphism.** Let `k` be
an infinite field and `φ : X ⟶ 𝐏¹_k` a nonconstant morphism over `k` from a proper curve which is
étale over a nonempty open `U ⊆ X`. Then `X` has a closed point `x` with `κ(x)/k` finite separable
of degree at most `deg(X/𝐏¹_k)`: the image of `U` is a nonempty open of `𝐏¹_k`, which contains a
rational point `t`; a point `u ∈ U` over `t` has `κ(u)/κ(t) = κ(u)/k` separable. -/
theorem exists_isClosed_isSeparable_finrank_le_degreeOver_of_etale [Infinite k]
    (φ : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hφ : φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = πX)
    (hnc : ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, φ.base x = y)
    (U : X.Opens) (hU : Nonempty U) (het : Etale (U.ι ≫ φ)) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      (letI := ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop ≫ X.Γevaluation x).hom.toAlgebra;
      Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x) ∧
        Module.finrank k (X.residueField x) ≤
          @degreeOver X _ φ _ _ (locallyOfFiniteType_of_isCurve_comp k πX
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hφ)
            (isDominant_of_not_constant k πX
            (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) φ hnc)) := by
  obtain ⟨u₀⟩ := hU
  obtain ⟨σ, hσ, hσU⟩ := exists_section_projectiveLine_mem_of_isOpen
    (Set.range (U.ι ≫ φ).base) (U.ι ≫ φ).isOpenMap.isOpen_range ⟨_, u₀, rfl⟩
  obtain ⟨u, hu⟩ := hσU (IsLocalRing.closedPoint k)
  obtain ⟨hcl, hfin, hle, hsep⟩ :=
    exists_isClosed_finrank_residueField_le_degreeOver_of_section πX φ hφ hnc σ hσ (U.ι u) hu
  refine ⟨U.ι u, hcl, hfin, hsep ?_, hle⟩
  let := (φ.residueFieldMap (U.ι u)).hom.toAlgebra
  let : Algebra ((projectiveSpaceOver 1 (Spec (.of k))).residueField (φ.base (U.ι u)))
      (U.toScheme.residueField u) := ((U.ι ≫ φ).residueFieldMap u).hom.toAlgebra
  have : Algebra.IsSeparable
      ((projectiveSpaceOver 1 (Spec (.of k))).residueField (φ.base (U.ι u)))
      (U.toScheme.residueField u) := by
    have h : let := ((U.ι ≫ φ).residueFieldMap u).hom.toAlgebra
      Algebra.IsSeparable
        ((projectiveSpaceOver 1 (Spec (.of k))).residueField ((U.ι ≫ φ).base u))
        (U.toScheme.residueField u) := inferInstance
    exact h
  exact Algebra.IsSeparable.of_algHom _ _
    { toRingHom := (U.ι.residueFieldMap u).hom
      commutes' := fun c => by
        show (U.ι.residueFieldMap u).hom ((φ.residueFieldMap (U.ι u)).hom c) =
          ((U.ι ≫ φ).residueFieldMap u).hom c
        rw [Scheme.residueFieldMap_comp]
        rfl }

/-- **A morphism to `𝐏¹_k` which is étale on a nonempty open is nonconstant.** Were it constant
with value `y`, the open image of the étale restriction would be `{y}`; but `y` is also the image
of a closed point under the closed map `φ`, so `{y}` would be open and closed in the connected
one-dimensional `𝐏¹_k`, which is impossible. -/
theorem not_constant_of_etale (φ : X ⟶ projectiveSpaceOver 1 (Spec (.of k)))
    (hφ : φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = πX)
    (U : X.Opens) (hU : Nonempty U) (het : Etale (U.ι ≫ φ)) :
    ¬ ∃ y : projectiveSpaceOver 1 (Spec (.of k)), ∀ x : X, φ.base x = y := by
  rintro ⟨y, hy⟩
  obtain ⟨u₀⟩ := hU
  have hrange : Set.range (U.ι ≫ φ).base = {y} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨u, rfl⟩
      exact hy _
    · rintro _ rfl
      exact ⟨u₀, hy _⟩
  have hopen : IsOpen ({y} : Set (projectiveSpaceOver 1 (Spec (.of k)))) :=
    hrange ▸ (U.ι ≫ φ).isOpenMap.isOpen_range
  have : IsProper (φ ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) := by
    rw [hφ]
    infer_instance
  have : IsProper φ := IsProper.of_comp φ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace πX
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := X)).exists_closed_singleton ⟨U.ι u₀, trivial⟩
  have hclosed : IsClosed ({y} : Set (projectiveSpaceOver 1 (Spec (.of k)))) := by
    have := φ.isClosedMap _ hz
    rwa [Set.image_singleton, hy] at this
  have huniv : ({y} : Set (projectiveSpaceOver 1 (Spec (.of k)))) = Set.univ :=
    (isClopen_iff.mp ⟨hclosed, hopen⟩).resolve_left (Set.singleton_nonempty y).ne_empty
  have hsub : Subsingleton (projectiveSpaceOver 1 (Spec (.of k))) :=
    ⟨fun a b => by
      have ha : a ∈ ({y} : Set _) := huniv ▸ trivial
      have hb : b ∈ ({y} : Set _) := huniv ▸ trivial
      exact ha.trans hb.symm⟩
  have hdim := IsCurve.topologicalKrullDim_eq_one (k := k)
    (f := projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))
  have : Subsingleton (TopologicalSpace.IrreducibleCloseds
      (projectiveSpaceOver 1 (Spec (.of k)))) := ⟨fun A B => by
    apply TopologicalSpace.IrreducibleCloseds.ext
    have hw : ∀ s : Set (projectiveSpaceOver 1 (Spec (.of k))), s.Nonempty → s = Set.univ :=
      fun s ⟨a, ha⟩ => Set.eq_univ_of_forall fun b => Subsingleton.elim a b ▸ ha
    rw [hw _ A.isIrreducible.nonempty, hw _ B.isIrreducible.nonempty]⟩
  have h0 := Order.krullDim_nonpos_of_subsingleton
    (α := TopologicalSpace.IrreducibleCloseds (projectiveSpaceOver 1 (Spec (.of k))))
  change topologicalKrullDim _ ≤ 0 at h0
  rw [hdim] at h0
  norm_num at h0

/-! ### The Frobenius twist of a curve -/

open Stacks.Frobenius

omit [IsCurve k πX] [IsProper πX] in
/-- The Frobenius twist `X^{(p)}` is the base change of `X` along `Spec` of the Frobenius of `k`,
read as the `k`-algebra structure `frobenius k p` on `k`. -/
theorem isPullback_frobeniusTwist_curve (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) :
    letI : Algebra k k := (frobenius k p).toAlgebra
    IsPullback (pullback.fst πX (absoluteFrobenius (Spec (.of k)) p hS))
      ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk πX)).hom πX
      (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
  let : Algebra k k := (frobenius k p).toAlgebra
  have h : Spec.map (CommRingCat.ofHom (algebraMap k k)) =
      absoluteFrobenius (Spec (.of k)) p hS :=
    specMap_frobenius_eq_absoluteFrobenius k p hS
  rw [h]
  exact IsPullback.of_hasPullback πX (absoluteFrobenius (Spec (.of k)) p hS)

omit [IsCurve k πX] in
/-- **The Frobenius twist of a proper curve has the same genus** ([Stacks, Tag 0BY9] along the
Frobenius of `k`). -/
theorem genus_frobeniusTwist_curve (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p) :
    genus ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk πX)).hom = genus πX := by
  let : Algebra k k := (frobenius k p).toAlgebra
  exact genus_baseChange k k _ _ πX (isPullback_frobeniusTwist_curve πX p hS)

omit [IsCurve k πX] in
/-- **The Frobenius twist of a proper curve with `H⁰(X, 𝒪_X) = k` again has only constant global
functions** ([Stacks, Tag 0BY9] along the Frobenius of `k`). -/
theorem isIso_globalSections_frobeniusTwist_curve (p : ℕ) [Fact p.Prime] [CharP k p]
    (hS : IsInCharacteristic (Spec (.of k)) p)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ πX.appTop)] :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((frobeniusTwist (Spec (.of k)) p hS).obj (Over.mk πX)).hom.appTop) := by
  let : Algebra k k := (frobenius k p).toAlgebra
  exact isIso_globalSections_baseChange k k _ _ πX (isPullback_frobeniusTwist_curve πX p hS)

end AlgebraicGeometry

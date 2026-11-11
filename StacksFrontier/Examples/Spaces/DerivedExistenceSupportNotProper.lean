module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Examples.Spaces.DerivedExistenceNotFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceSupportedAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineEtaleModuliSquare
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineHomologySupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationSquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.AffinePseudoCoherentSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPullbackSupport
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Examples.Algebra.StaircaseComplex
public import StacksFrontier.Examples.Algebra.TwoAdicTower

/-!
# The support clause of the generalization proposed in Stacks 0DIR fails

Stacks 0DIR proposes that the derived Grothendieck existence theorem 0DIQ holds for `X` only
separated and of finite presentation over `A = lim Aₙ`, with `Kₙ` pseudo-coherent relative to `Aₙ`
and supported on closed subsets `Zₙ ⊆ |Xₙ|` proper over `Aₙ`, the outcome being a `K`
pseudo-coherent relative to `A` with `Ljₙ^* K ≅ Kₙ`, *supported on a closed subset of `|X|` proper
over `A`*. The last clause is false, even for `X` flat over `A`, and this file proves it.

Let `A = ℤ_2 = lim ℤ/2^{n+1}`, `ϖ = 2`, `X = 𝔸¹_A = Spec A[x]` (separated, flat and of finite
presentation over `A`) and
`E = ⊕ᵢ 𝒪_X/(x - ϖ^{i+1})[2i]`, the associated object of the staircase complex of the
`x - ϖ^{i+1}` (`Stacks.Examples.StaircaseComplex.staircase`), and `Kₙ = Ljₙ^* E`, so that
`Liₙ^* Kₙ₊₁ ≅ Kₙ` canonically. On `Xₙ ≅ 𝔸¹_{Aₙ}`, `Kₙ` is the staircase complex of the
`x - ϖ^{i+1}` over `Aₙ[x]`, whose cohomology is killed by `x^{n+1}` (`ϖ^{n+1} = 0` in `Aₙ`); so
`Kₙ` is supported on `Zₙ = V(x)`, finite over `Aₙ`. But no `K` with `Ljₙ^* K ≅ Kₙ` for every `n`,
pseudo-coherent relative to `A`, is supported on a closed `T ⊆ |X|` proper over `A`:

* `T ≠ |X|`, the image of `V(ϖx - 1)` in `Spec A` missing the closed point
  (`not_isProperOver_univ`), so a nonzero `c ∈ A[x]` vanishes on `T`;
* `M = RΓ(X, K)` is pseudo-coherent over the Noetherian ring `A[x]`, so each `Hʲ(M)` is finite,
  supported on `V(c)`, hence killed by a power of `c`;
* `M ⊗^L Aₙ[x] ≅ RΓ(Xₙ, Kₙ)` is the staircase complex over `Aₙ[x]`, whose `H^{-2i}` contains
  `Aₙ[x]/(x - ϖ^{i+1})`, and the Tor sequence along `A[x] → Aₙ[x] = A[x]/(ϖ^{n+1})` makes
  `c^{2N}` kill it: `c(ϖ^{i+1})^{2N} = 0` in every `Aₙ`, so `c(ϖ^{i+1}) = 0` for every `i`, and
  `c = 0`.

See the entry 0DIR(support of K) in `errata.md`.

## Main results

In the namespace `Stacks.Examples.DerivedExistenceSupportNotProper`:

* `supportedSystem`: the system, a `AlgebraicGeometry.Space.SupportedDerivedExistenceSystem`.
* `not_isProperOver_univ`: `|𝔸¹_A|` is not proper over `Spec A`.
* `not_exists_isRelativelyPseudoCoherent_isProperOver_cohomologySupportedOn`: no lift of the
  system is supported on a closed subset proper over `A`.
* `not_forall_exists_isRelativelyPseudoCoherent_isProperOver_cohomologySupportedOn`: **the support
  clause proposed in Stacks 0DIR is false.**

## References

* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Space
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt baseProjection)
open Stacks.Examples.DerivedExistenceNotFlat (site site_contains site_contains_baseAt)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] pointTopology

universe u

namespace Stacks.Examples.DerivedExistenceSupportNotProper

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})
  (hFs : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op).hom)

/-! ### The affine line `X = 𝔸¹_A` and its reductions `𝔸¹_{Aₙ}` -/

/-- The ring `A[x]`. -/
abbrev lineRing : CommRingCat.{u} := CommRingCat.of (Polynomial (limit F : CommRingCat.{u}))

/-- The ring `Aₙ[x]`. -/
abbrev lineRingAt (n : ℕ) : CommRingCat.{u} := CommRingCat.of (Polynomial (F.obj (op n)))

/-- `𝔸¹_A ⟶ Spec A`. -/
abbrev lineSpecMap : Spec (lineRing F) ⟶ limitBase F :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- `𝔸¹_{Aₙ} ⟶ Spec Aₙ`. -/
abbrev lineSpecMapAt (n : ℕ) : Spec (lineRingAt F n) ⟶ baseAt F n :=
  Spec.map (CommRingCat.ofHom Polynomial.C)

/-- `A[x] ⟶ Aₙ[x]`. -/
abbrev lineRingProjection (n : ℕ) : lineRing F ⟶ lineRingAt F n :=
  CommRingCat.ofHom (Polynomial.mapRingHom (limit.π F (op n)).hom)

/-- The square of rings `A ⟶ A[x]`, `A ⟶ Aₙ`, `A[x] ⟶ Aₙ[x]`, `Aₙ ⟶ Aₙ[x]` is a pushout. -/
theorem isPushout_lineRing (n : ℕ) :
    IsPushout (CommRingCat.ofHom Polynomial.C) (limit.π F (op n)) (lineRingProjection F n)
      (CommRingCat.ofHom (Polynomial.C : F.obj (op n) →+* _)) := by
  algebraize [(limit.π F (op n)).hom, Polynomial.mapRingHom (limit.π F (op n)).hom]
  exact (CommRingCat.isPushout_of_isPushout (limit F : CommRingCat.{u}) (F.obj (op n))
    (Polynomial (limit F : CommRingCat.{u})) (Polynomial (F.obj (op n)))).flip

/-- `R ⟶ R[x]` is of finite presentation. -/
theorem finitePresentation_C (R : Type u) [CommRing R] :
    (Polynomial.C : R →+* Polynomial R).FinitePresentation := by
  rw [← Polynomial.algebraMap_eq]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- `𝔸¹_A` belongs to the chosen site. -/
theorem site_contains_line : (site F).Contains (Spec (lineRing F)) := by
  have : LocallyOfFiniteType (lineSpecMap F) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2
      (RingHom.FiniteType.of_finitePresentation (finitePresentation_C _))
  exact contains_of_locallyOfFiniteType (site F) (U := (site F).obj (site_contains F))
    (lineSpecMap F)

include hFs in
/-- `A[x] ⟶ Aₙ[x]` is surjective. -/
theorem surjective_lineRingProjection (n : ℕ) :
    Function.Surjective (lineRingProjection F n).hom :=
  Polynomial.map_surjective _ (GrothendieckExistence.surjective_limit_π F hFs n)

include hFs in
/-- `𝔸¹_{Aₙ} ⟶ 𝔸¹_A` is a closed immersion. -/
theorem isClosedImmersion_spec_lineRingProjection (n : ℕ) :
    IsClosedImmersion (Spec.map (lineRingProjection F n)) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_lineRingProjection F hFs n)

include hFs in
/-- `𝔸¹_{Aₙ}` belongs to the chosen site, a closed subscheme of `𝔸¹_A`. -/
theorem site_contains_lineAt (n : ℕ) : (site F).Contains (Spec (lineRingAt F n)) :=
  have := isClosedImmersion_spec_lineRingProjection F hFs n
  (site F).contains_of_mono (Spec.map (lineRingProjection F n)) (site_contains_line F)

/-- `𝔸¹_A`, as an object of the big fppf site over `Spec A`. -/
abbrev lineObject : BigFppfOver (site F) (limitBase F) (site_contains F) :=
  siteObject (site F) (limitBase F) (site_contains F) (site_contains_line F) (lineSpecMap F)

/-- The structure morphism `𝔸¹_A ⟶ Spec A` in the big fppf site over `Spec A`. -/
abbrev lineObjectToBase :
    lineObject F ⟶ limitBaseObject F (site F) (site_contains F) :=
  Over.homMk (lineObject F).hom (by simp)

/-- `X = 𝔸¹_A` as an algebraic space over `Spec A`. -/
abbrev space : Over (schemeSpace (limitBaseObject F (site F) (site_contains F))) :=
  Over.mk ((schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map (lineObjectToBase F))

instance isAffine_lineObject :
    IsAffine ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj (lineObject F)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- `𝔸¹_{Aₙ}`, as an object of the big fppf site over `Spec A`. -/
abbrev lineObjectAt (n : ℕ) : BigFppfOver (site F) (limitBase F) (site_contains F) :=
  siteObject (site F) (limitBase F) (site_contains F) (site_contains_lineAt F hFs n)
    (Spec.map (lineRingProjection F n) ≫ lineSpecMap F)

instance isAffine_lineObjectAt (n : ℕ) :
    IsAffine ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (lineObjectAt F hFs n)) :=
  inferInstanceAs (IsAffine (Spec _))

/-- `𝔸¹_{Aₙ} ⟶ 𝔸¹_A` in the big fppf site over `Spec A`. -/
abbrev lineObjectProjection (n : ℕ) : lineObjectAt F hFs n ⟶ lineObject F :=
  Over.homMk (ObjectProperty.homMk (Spec.map (lineRingProjection F n))) rfl

/-- `𝔸¹_{Aₙ} ⟶ Spec Aₙ` in the big fppf site over `Spec A`. -/
abbrev lineObjectToBaseAt (n : ℕ) :
    lineObjectAt F hFs n ⟶
      baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) n :=
  Over.homMk (ObjectProperty.homMk (lineSpecMapAt F n)) (by
    ext1
    change lineSpecMapAt F n ≫ baseProjection F n =
      Spec.map (lineRingProjection F n) ≫ lineSpecMap F
    rw [← Spec.map_comp, ← Spec.map_comp, (isPushout_lineRing F n).w])

/-- The square `𝔸¹_{Aₙ} ⟶ 𝔸¹_A`, `𝔸¹_{Aₙ} ⟶ Spec Aₙ` over `Spec A` is cartesian on schemes. -/
theorem isPullback_toScheme_lineObjectAt (n : ℕ) :
    IsPullback
      ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map
        (lineObjectToBaseAt F hFs n))
      ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map
        (lineObjectProjection F hFs n))
      ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map
        (baseObjectProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) n))
      ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map (lineObjectToBase F)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_lineRing F n)).flip

/-- The cartesian square of the algebraic spaces represented by `𝔸¹_{Aₙ}`, `𝔸¹_A`, `Spec Aₙ` and
`Spec A`. -/
theorem isPullback_schemeSpace_lineObjectAt (n : ℕ) :
    IsPullback ((schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map
        (lineObjectToBaseAt F hFs n))
      ((schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map
        (lineObjectProjection F hFs n))
      (baseSpaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) n)
      (space F).hom :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _)
    (AlgebraicGeometry.Stack.ChartBaseChange.isPullback_yoneda_of_isPullback_toScheme
      (isPullback_toScheme_lineObjectAt F hFs n))

/-- `Xₙ ≅ 𝔸¹_{Aₙ}`: the base change of `X = 𝔸¹_A` to `Spec Aₙ` is represented by `𝔸¹_{Aₙ}`. -/
abbrev lineSpaceIso (n : ℕ) :
    schemeSpace (lineObjectAt F hFs n) ≅
      spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n :=
  (isPullback_schemeSpace_lineObjectAt F hFs n).isoIsPullback _ _
    (isPullback_spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n)

/-- `𝔸¹_{Aₙ} ≅ Xₙ ⟶ X` is `𝔸¹_{Aₙ} ⟶ 𝔸¹_A`. -/
theorem lineSpaceIso_hom_spaceProjection (n : ℕ) :
    (lineSpaceIso F hFs n).hom ≫
        spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n =
      (schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map
        (lineObjectProjection F hFs n) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- `𝔸¹_{Aₙ} ≅ Xₙ ⟶ Spec Aₙ` is `𝔸¹_{Aₙ} ⟶ Spec Aₙ`. -/
theorem lineSpaceIso_hom_spaceBaseProjection (n : ℕ) :
    (lineSpaceIso F hFs n).hom ≫
        spaceBaseProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n =
      (schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map
        (lineObjectToBaseAt F hFs n) :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-! ### `X = 𝔸¹_A` is separated, flat and of finite presentation over `Spec A` -/

/-- `X ⟶ Spec A` is of finite presentation. -/
theorem isFinitePresentation_space_hom :
    IsFinitePresentation (site F) (limitBase F) (site_contains F) (space F).hom.hom :=
  isFinitePresentation_yoneda_map _ _ _ (lineObjectToBase F)
    ⟨(HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 (finitePresentation_C _),
      inferInstanceAs (QuasiCompact (lineSpecMap F)),
      inferInstanceAs (QuasiSeparated (lineSpecMap F))⟩

/-- `X ⟶ Spec A` is flat. -/
theorem isFlat_space_hom :
    Space.IsFlat (site F) (limitBase F) (site_contains F) (space F).hom.hom :=
  isFlat_yoneda_map _ _ _ (lineObjectToBase F)
    ((HasRingHomProperty.Spec_iff (P := @Flat)).2 (by
      rw [← Polynomial.algebraMap_eq]
      exact RingHom.flat_algebraMap_iff.mpr inferInstance))

/-- `X ⟶ Spec A` is separated. -/
theorem isSeparated_space_hom :
    IsSeparated (site F) (limitBase F) (site_contains F) (space F).hom.hom :=
  isSeparated_yoneda_map_of_isAffine _ _ _ (lineObjectToBase F)
    (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _)))

/-! ### The whole of `𝔸¹_A` is not proper over `Spec A` -/

/-- A morphism `Z ⟶ Spec R` along which `r` becomes a unit lands in `D(r)`. -/
theorem range_subset_basicOpen_of_isUnit {Z : Scheme.{u}} {R : CommRingCat.{u}} (φ : Z ⟶ Spec R)
    (r : R) (h : IsUnit (φ.appTop ((Scheme.ΓSpecIso R).inv r))) :
    Set.range φ ⊆ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ φ ⁻¹ᵁ (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r) := by
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ h]
    trivial
  have hz' : φ z ∈ (Spec R).basicOpen ((Scheme.ΓSpecIso R).inv r) := hz
  rw [basicOpen_eq_of_affine] at hz'
  exact hz'

/-- A nonempty closed subset of the spectrum of a local ring contains the closed point. -/
theorem closedPoint_mem_of_isClosed {R : Type u} [CommRing R] [IsLocalRing R]
    {C : Set (PrimeSpectrum R)} (hC : _root_.IsClosed C) (hne : C.Nonempty) :
    IsLocalRing.closedPoint R ∈ C := by
  obtain ⟨p, hp⟩ := hne
  have hle : p ≤ IsLocalRing.closedPoint R := IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  exact (hC.closure_subset_iff.2 (Set.singleton_subset_iff.2 hp))
    ((PrimeSpectrum.le_iff_mem_closure _ _).1 hle)

variable (ϖ : (limit F : CommRingCat.{u}))

/-- The ideal `(ϖx - 1)` of global functions on `𝔸¹_A`. -/
abbrev invertIdeal :
    Ideal Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (lineObject F), ⊤) :=
  Ideal.span {((Scheme.ΓSpecIso (lineRing F)).inv.hom
    (Polynomial.C ϖ * Polynomial.X - 1))}

/-- `A[x] ⧸ (ϖx - 1)` is not the zero ring when `A` is a domain and `ϖ ≠ 0`. -/
theorem invertIdeal_ne_top [IsDomain (limit F : CommRingCat.{u})] (hϖ : ϖ ≠ 0) :
    invertIdeal F ϖ ≠ ⊤ := by
  let K := FractionRing (limit F : CommRingCat.{u})
  let ψ : Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj (lineObject F), ⊤)
      →+* K :=
    (Polynomial.eval₂RingHom (algebraMap _ K) (algebraMap _ K ϖ)⁻¹).comp
      (Scheme.ΓSpecIso (lineRing F)).hom.hom
  have hϖK : algebraMap _ K ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ)
  have hle : invertIdeal F ϖ ≤ RingHom.ker ψ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    simp only [ψ, RingHom.comp_apply]
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
    simp [mul_inv_cancel₀ hϖK]
  intro htop
  have h1 : ψ 1 = 0 := RingHom.mem_ker.1 (hle (htop ▸ Submodule.mem_top))
  exact one_ne_zero (h1.symm.trans (map_one ψ)).symm

/-- **`|𝔸¹_A|` is not proper over `Spec A`** for `A` a local domain and `ϖ ∈ A` nonzero and not a
unit: the image in `Spec A` of the closed subset `V(ϖx - 1)` is `D(ϖ) ∩ (image)`, a nonempty
set missing the closed point, so not closed. -/
theorem not_isProperOver_univ [IsDomain (limit F : CommRingCat.{u})]
    [IsLocalRing (limit F : CommRingCat.{u})] (hϖ : ϖ ≠ 0) (hϖu : ¬ IsUnit ϖ)
    (hf : IsLocallyOfFiniteType (site F) (limitBase F) (site_contains F) (space F).hom.hom) :
    ¬ IsProperOver (site F) (limitBase F) (site_contains F) (space F).left.2
      (schemeSpace (limitBaseObject F (site F) (site_contains F))).2 (space F).hom.hom hf
      Set.univ isClosed_univ := by
  intro h
  let B := site F
  let S := limitBase F
  let hS := site_contains F
  let W := reducedClosedSubspace B S hS (space F).left.1 (space F).left.2 Set.univ isClosed_univ
  have hcl : IsClosedMap (pointsMap B S hS W.toFunctor (W.ι ≫ (space F).hom.hom)) :=
    isClosedMap_pointsMap_of_pullback_fst_id B S hS _
      ((Space.IsProper.universallyClosed B S hS h) _ (schemeSpace (limitBaseObject F B hS)).2
        (𝟙 _))
  let q := idealQuotientSpecMap B S hS (invertIdeal F ϖ)
  let V := Set.range (pointsMap B S hS _ (yoneda.map q))
  have hV : _root_.IsClosed V := isClosed_range_pointsMap_of_isClosedImmersion B S hS
    (space F).left.2 _ (isClosedImmersion_yoneda_map_idealQuotientSpecMap B S hS _)
  have himg := hcl _ (hV.preimage (continuous_pointsMap B S hS W.ι))
  have hrange : Set.range (pointsMap B S hS W.toFunctor W.ι) = Set.univ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS _ _ _ _
  have heq : pointsMap B S hS W.toFunctor (W.ι ≫ (space F).hom.hom) ''
      (pointsMap B S hS W.toFunctor W.ι ⁻¹' V) =
      pointsMap B S hS _ (yoneda.map (q ≫ lineObjectToBase F)) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨w, ⟨z, hz⟩, rfl⟩
      refine ⟨z, trivial, ?_⟩
      change pointsMap B S hS _ (yoneda.map q ≫ yoneda.map (lineObjectToBase F)) z =
        pointsMap B S hS _ (W.ι ≫ yoneda.map (lineObjectToBase F)) w
      exact (pointsMap_comp_apply B S hS (yoneda.map q) (yoneda.map (lineObjectToBase F)) z).trans
        ((congrArg _ hz).trans
          (pointsMap_comp_apply B S hS W.ι (yoneda.map (lineObjectToBase F)) w).symm)
    · rintro ⟨z, -, rfl⟩
      have hv : pointsMap B S hS _ (yoneda.map q) z ∈
          Set.range (pointsMap B S hS W.toFunctor W.ι) := by
        rw [hrange]
        trivial
      obtain ⟨w, hw⟩ := hv
      refine ⟨w, ⟨z, hw.symm⟩, ?_⟩
      change pointsMap B S hS _ (W.ι ≫ yoneda.map (lineObjectToBase F)) w =
        pointsMap B S hS _ (yoneda.map q ≫ yoneda.map (lineObjectToBase F)) z
      exact (pointsMap_comp_apply B S hS W.ι (yoneda.map (lineObjectToBase F)) w).trans
        ((congrArg _ hw).trans
          (pointsMap_comp_apply B S hS (yoneda.map q) (yoneda.map (lineObjectToBase F)) z).symm)
  rw [heq] at himg
  have hC := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS _ _).1 himg
  rw [image_pointsToScheme_image_pointsMap, Set.image_univ_of_surjective
    (surjective_pointsToScheme B S hS _), Set.image_univ] at hC
  -- the image of `Spec (A[x] ⧸ (ϖx - 1)) ⟶ Spec A`
  let φ : Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj (lineObject F), ⊤) ⧸ invertIdeal F ϖ)) ⟶
      Spec (limit F : CommRingCat.{u}) :=
    (BigFppfOver.toScheme B S hS).map (q ≫ lineObjectToBase F)
  have hunit : IsUnit (φ.appTop ((Scheme.ΓSpecIso _).inv ϖ)) := by
    have h1 : (lineSpecMap F).appTop ((Scheme.ΓSpecIso _).inv ϖ) =
        (Scheme.ΓSpecIso (lineRing F)).inv.hom (Polynomial.C ϖ) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    have hφ : φ.appTop ((Scheme.ΓSpecIso _).inv ϖ) =
        (Scheme.ΓSpecIso (.of (Γ((BigFppfOver.toScheme B S hS).obj (lineObject F), ⊤) ⧸
          invertIdeal F ϖ))).inv (Ideal.Quotient.mk _
            ((Scheme.ΓSpecIso (lineRing F)).inv.hom (Polynomial.C ϖ))) := by
      rw [← h1, ← idealQuotientSpecMap_appTop B S hS (invertIdeal F ϖ)]
      rfl
    rw [hφ]
    refine IsUnit.map _ (IsUnit.of_mul_eq_one
      (Ideal.Quotient.mk _ ((Scheme.ΓSpecIso (lineRing F)).inv.hom Polynomial.X)) ?_)
    rw [← map_mul, ← map_mul, ← map_one (Ideal.Quotient.mk (invertIdeal F ϖ)),
      ← map_one (Scheme.ΓSpecIso (lineRing F)).inv.hom, Ideal.Quotient.eq, ← map_sub]
    exact Ideal.subset_span rfl
  have hsub := range_subset_basicOpen_of_isUnit φ ϖ hunit
  have hne : (Set.range φ).Nonempty := by
    have : Nontrivial (Γ((BigFppfOver.toScheme B S hS).obj (lineObject F), ⊤) ⧸
        invertIdeal F ϖ) := Ideal.Quotient.nontrivial_iff.2 (invertIdeal_ne_top F ϖ hϖ)
    obtain ⟨z⟩ : Nonempty (PrimeSpectrum (Γ((BigFppfOver.toScheme B S hS).obj (lineObject F), ⊤) ⧸
        invertIdeal F ϖ)) := inferInstance
    exact ⟨φ z, z, rfl⟩
  have hm := hsub (closedPoint_mem_of_isClosed hC hne)
  have hm' : ϖ ∉ IsLocalRing.maximalIdeal (limit F : CommRingCat.{u}) := hm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hm'
  exact hϖu hm'

/-! ### The closed subsets `V(x) ⊆ Xₙ` -/

/-- The ideal `(x^{n+1})` of global functions on `𝔸¹_{Aₙ}`. -/
abbrev nilIdealAt (n : ℕ) :
    Ideal Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (lineObjectAt F hFs n), ⊤) :=
  Ideal.span {(Scheme.ΓSpecIso (lineRingAt F n)).inv.hom (Polynomial.X ^ (n + 1))}

/-- `Aₙ ⟶ Aₙ[x] ⧸ (x^{n+1})` is finite. -/
theorem finite_quotient_comp_appTop_lineObjectToBaseAt (n : ℕ) :
    ((Ideal.Quotient.mk (nilIdealAt F hFs n)).comp
      ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map
        (lineObjectToBaseAt F hFs n)).appTop.hom).Finite := by
  have happ : ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map
      (lineObjectToBaseAt F hFs n)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom Polynomial.C ≫ (Scheme.ΓSpecIso _).inv := by
    change (Spec.map (CommRingCat.ofHom (Polynomial.C : F.obj (op n) →+* _))).appTop = _
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let e := Scheme.ΓSpecIso (lineRingAt F n)
  let g : Polynomial (F.obj (op n)) := Polynomial.X ^ (n + 1)
  have hle : Ideal.span {g} ≤ (nilIdealAt F hFs n).comap e.inv.hom := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span rfl
  let ρ : AdjoinRoot g →+* _ := Ideal.quotientMap (nilIdealAt F hFs n) e.inv.hom hle
  have hρ : Function.Surjective ρ :=
    Ideal.quotientMap_surjective e.commRingCatIsoToRingEquiv.symm.surjective
  have hof : (AdjoinRoot.of g).Finite :=
    RingHom.finite_algebraMap.mpr (Polynomial.monic_X_pow (n + 1)).finite_adjoinRoot
  have heq : (Ideal.Quotient.mk (nilIdealAt F hFs n)).comp
      ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).map
        (lineObjectToBaseAt F hFs n)).appTop.hom =
      (ρ.comp (AdjoinRoot.of g)).comp (Scheme.ΓSpecIso (F.obj (op n))).hom.hom := by
    rw [happ]
    rfl
  rw [heq]
  exact ((RingHom.Finite.of_surjective ρ hρ).comp hof).comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (F.obj (op n))).commRingCatIsoToRingEquiv.surjective)

/-- The closed immersion `Spec (Aₙ[x] ⧸ (x^{n+1})) ⟶ 𝔸¹_{Aₙ} ≅ Xₙ`. -/
abbrev stageSupportMap (n : ℕ) :
    yoneda.obj (idealQuotientSpecObject (site F) (limitBase F) (site_contains F)
        (nilIdealAt F hFs n)) ⟶
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).1 :=
  yoneda.map (idealQuotientSpecMap (site F) (limitBase F) (site_contains F) (nilIdealAt F hFs n)) ≫
    (lineSpaceIso F hFs n).hom.hom

/-- `Spec (Aₙ[x] ⧸ (x^{n+1})) ⟶ Xₙ` is a closed immersion. -/
theorem isClosedImmersion_stageSupportMap (n : ℕ) :
    IsClosedImmersion (site F) (limitBase F) (site_contains F) (stageSupportMap F hFs n) :=
  isClosedImmersion_comp _ _ _ _ _
    (isClosedImmersion_yoneda_map_idealQuotientSpecMap _ _ _ _)
    (have : IsIso (lineSpaceIso F hFs n).hom.hom :=
      ⟨⟨(lineSpaceIso F hFs n).inv.hom,
        congrArg (fun t => t.hom) (lineSpaceIso F hFs n).hom_inv_id,
        congrArg (fun t => t.hom) (lineSpaceIso F hFs n).inv_hom_id⟩⟩
    isClosedImmersion_of_isIso _ _ _ (lineSpaceIso F hFs n).hom.hom)

/-- The closed subset `Zₙ = V(x) ⊆ |Xₙ|`. -/
abbrev stageSupport (n : ℕ) :
    Set (points (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).1) :=
  Set.range (pointsMap _ _ _ _ (stageSupportMap F hFs n))

/-- `Zₙ` is closed. -/
theorem isClosed_stageSupport (n : ℕ) : _root_.IsClosed (stageSupport F hFs n) :=
  isClosed_range_pointsMap_of_isClosedImmersion _ _ _
    (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).2 _
    (isClosedImmersion_stageSupportMap F hFs n)

/-- `X ⟶ Spec A` is locally of finite type. -/
theorem isLocallyOfFiniteType_space_hom :
    IsLocallyOfFiniteType (site F) (limitBase F) (site_contains F) (space F).hom.hom :=
  isLocallyOfFiniteType_of_isLocallyOfFinitePresentation _ _ _
    (isFinitePresentation_space_hom F).1

/-- `Zₙ` is proper over `Spec Aₙ`: it is `Spec (Aₙ[x] ⧸ (x^{n+1}))`, finite over `Aₙ`. -/
theorem isProperOver_stageSupport (n : ℕ) :
    IsProperOver (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).2
      (schemeSpace (baseObjectAt F (site F) (site_contains F) (site_contains_baseAt F hFs) n)).2
      (spaceBaseProjection F (site F) (site_contains F) (site_contains_baseAt F hFs)
        (space F) n).hom
      (isLocallyOfFiniteType_spaceBaseProjection F (site F) (site_contains F)
        (site_contains_baseAt F hFs) (space F) (isLocallyOfFiniteType_space_hom F) n)
      (stageSupport F hFs n) (isClosed_stageSupport F hFs n) := by
  refine isProperOver_of_isClosedImmersion_of_range _ _ _ (isAlgebraicSpace_yoneda _ _ _ _) _ _ _
    (isClosedImmersion_stageSupportMap F hFs n) _ _ _ _ rfl ?_
  have h : stageSupportMap F hFs n ≫
      (spaceBaseProjection F (site F) (site_contains F) (site_contains_baseAt F hFs)
        (space F) n).hom =
      yoneda.map (idealQuotientSpecMap (site F) (limitBase F) (site_contains F)
        (nilIdealAt F hFs n) ≫ lineObjectToBaseAt F hFs n) := by
    change yoneda.map _ ≫ ((lineSpaceIso F hFs n).hom ≫ spaceBaseProjection F (site F)
      (site_contains F) (site_contains_baseAt F hFs) (space F) n).hom = _
    rw [lineSpaceIso_hom_spaceBaseProjection, Functor.map_comp]
    rfl
  rw [h]
  exact isProper_yoneda_map_idealQuotientSpecMap_comp _ _ _ _ _
    (finite_quotient_comp_appTop_lineObjectToBaseAt F hFs n)

/-! ### The system `Kₙ = Ljₙ^* Φ(⊕ᵢ 𝒪/(x - ϖ^{i+1})[2i])` -/

section System

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Examples.StaircaseComplex

/-- The global function `x - ϖ^{i+1}` on `𝔸¹_A`. -/
abbrev stairCoeff (i : ℕ) :
    Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj (lineObject F), ⊤) :=
  (Scheme.ΓSpecIso (lineRing F)).inv.hom (Polynomial.X - Polynomial.C (ϖ ^ (i + 1)))

/-- The object `E = ⊕ᵢ 𝒪_X/(x - ϖ^{i+1})[2i]` of `D_QCoh(𝒪_X)`, the associated object of the
staircase complex of the `x - ϖ^{i+1}`. -/
abbrev limitObject :
    DerivedCategory (Space.Modules.{u, u} (site F) (limitBase F) (site_contains F)
      (yoneda.obj (lineObject F)) (isAlgebraicSpace_yoneda _ _ _ (lineObject F))) :=
  (representedAffineDerivedAssociated (site F) (limitBase F) (site_contains F) (lineObject F)).obj
    (DerivedCategory.Q.obj (staircase _ (stairCoeff F ϖ)))

/-- `Kₙ = Ljₙ^* E`. -/
abbrev stageObject (n : ℕ) :
    derivedCategoryAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n :=
  (smallEtaleDerivedModulePullback (site F) (limitBase F) (site_contains F)
    (spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n)).obj
      (limitObject F ϖ)

/-- `Liₙ^* Kₙ₊₁ ≅ Kₙ`: `Liₙ^* Ljₙ₊₁^* ≅ Ljₙ^*`. -/
def stageTransition (n : ℕ) :
    (transitionDerivedPullback F (site F) (site_contains F) (site_contains_baseAt F hFs)
      (space F) n).obj (stageObject F hFs ϖ (n + 1)) ≅ stageObject F hFs ϖ n :=
  (smallEtaleDerivedModulePullbackCompIso (site F) (limitBase F) (site_contains F)
      (transitionSpace F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n)
      (spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F)
        (n + 1))).app (limitObject F ϖ) ≪≫
    (smallEtaleDerivedModulePullbackCongr (site F) (limitBase F) (site_contains F)
      (transitionSpace_spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs)
        (space F) n)).app (limitObject F ϖ)

/-- `RΓ(X, E) ≅` the staircase complex. -/
def limitObjectSectionsIso :
    DerivedCategory.Q.obj (staircase _ (stairCoeff F ϖ)) ≅
      (representedAffineDerivedSections (site F) (limitBase F) (site_contains F) (lineObject F)).obj
        (limitObject F ϖ) :=
  have := isIso_representedAffineDerivedAdjunction_unit (site F) (limitBase F) (site_contains F)
    (lineObject F)
  (asIso (representedAffineDerivedAdjunction (site F) (limitBase F) (site_contains F)
    (lineObject F)).unit).app _

/-- `E` lies in `D_QCoh`. -/
theorem qcohDerived_limitObject :
    QcohDerived (site F) (limitBase F) (site_contains F) (space F).left (limitObject F ϖ) :=
  qcohDerived_representedAffineDerivedAssociated_obj _ _ _ _ _

/-- `E` is `m`-pseudo-coherent for every `m`. -/
theorem isPseudoCoherentFrom_limitObject (m : ℤ) :
    (smallEtaleRingedSite (site F) (limitBase F) (site_contains F) (space F).left.1
      (space F).left.2).IsPseudoCoherentFrom (limitObject F ϖ) m :=
  (isPseudoCoherentFrom_iff_representedAffineDerivedSections _ _ _ (lineObject F) _
    (qcohDerived_limitObject F ϖ) m).2
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).1
      ((isPseudoCoherent_Q_staircase _ _).ofIso (limitObjectSectionsIso F ϖ)) m)

/-- `Kₙ` is `m`-pseudo-coherent for every `m`. -/
theorem isPseudoCoherentFrom_stageObject (n : ℕ) (m : ℤ) :
    (smallEtaleRingedSite (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).1
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).2
      ).IsPseudoCoherentFrom (stageObject F hFs ϖ n) m :=
  isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general _ _ m
    (isPseudoCoherentFrom_limitObject F ϖ m)

/-- `Kₙ` lies in `D_QCoh`. -/
theorem qcohDerived_stageObject (n : ℕ) :
    QcohDerived (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n)
      (stageObject F hFs ϖ n) := fun i =>
  isQuasicoherentOnSite_homology_of_isPseudoCoherentFrom_unconditional _ _ _ _ _ _ (i - 1) i
    (isPseudoCoherentFrom_stageObject F hFs ϖ n (i - 1)) (by omega)

/-- Each `Kₙ` is pseudo-coherent: it is so relative to `Aₙ` in every degree, and `Xₙ` is flat and
of finite presentation over `Aₙ` (Stacks 0DII). -/
theorem isPseudoCoherentOn_stageObject (n : ℕ) :
    IsPseudoCoherentOn F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n
      (stageObject F hFs ϖ n) := by
  let f := spaceBaseProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n
  have hfl : Space.IsFlat (site F) (limitBase F) (site_contains F) f.hom :=
    isFlat_spaceBaseProjection _ _ _ _ _ (isFlat_space_hom F) n
  have hfp : IsFinitePresentation (site F) (limitBase F) (site_contains F) f.hom :=
    isFinitePresentation_spaceBaseProjection _ _ _ _ _ (isFinitePresentation_space_hom F) n
  refine (isRelativelyPseudoCoherent_iff_isPseudoCoherent _ _ _ f hfl hfp.1
    ⟨stageObject F hFs ϖ n, qcohDerived_stageObject F hFs ϖ n⟩).1 ?_
  refine (isRelativelyPseudoCoherent_iff_forall _ _ _ _ _ _ _ _).2 fun m => ?_
  exact (isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom _ _ _ f hfl hfp.1 _ m).2
    (isPseudoCoherentFrom_stageObject F hFs ϖ n m)

/-- The ring map `Γ(𝔸¹_A) ⟶ Γ(𝔸¹_{Aₙ})`. -/
abbrev lineRingMapAt (n : ℕ) :=
  (representedAffineCommRingCatHom (site F) (limitBase F) (site_contains F)
    (lineObjectProjection F hFs n)).hom

/-- `Γ(𝔸¹_A) ⟶ Γ(𝔸¹_{Aₙ})` is `A[x] ⟶ Aₙ[x]`, read through `Γ(Spec -) ≅ -`. -/
theorem lineRingMapAt_apply (n : ℕ) (p : Polynomial (limit F : CommRingCat.{u})) :
    lineRingMapAt F hFs n ((Scheme.ΓSpecIso (lineRing F)).inv.hom p) =
      (Scheme.ΓSpecIso (lineRingAt F n)).inv.hom (p.map (limit.π F (op n)).hom) := by
  change (Spec.map (lineRingProjection F n)).appTop.hom ((Scheme.ΓSpecIso _).inv.hom p) = _
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The object `⊕ᵢ 𝒪/(x - ϖ^{i+1})[2i]` on `𝔸¹_{Aₙ}`. -/
abbrev lineStageObject (n : ℕ) :
    DerivedCategory (Space.Modules.{u, u} (site F) (limitBase F) (site_contains F)
      (yoneda.obj (lineObjectAt F hFs n)) (isAlgebraicSpace_yoneda _ _ _ _)) :=
  (representedAffineDerivedAssociated (site F) (limitBase F) (site_contains F)
    (lineObjectAt F hFs n)).obj
      (DerivedCategory.Q.obj (staircase _ (fun i => lineRingMapAt F hFs n (stairCoeff F ϖ i))))

/-- The restriction of `E` to `𝔸¹_{Aₙ}` is `⊕ᵢ 𝒪/(x - ϖ^{i+1})[2i]`. -/
def lineStageObjectIso (n : ℕ) :
    (smallEtaleDerivedModulePullback (site F) (limitBase F) (site_contains F)
      (representedSpaceMap (site F) (limitBase F) (site_contains F)
        (lineObjectProjection F hFs n))).obj (limitObject F ϖ) ≅ lineStageObject F hFs ϖ n :=
  (representedAffineDerivedBaseChangeIso (site F) (limitBase F) (site_contains F)
      (lineObjectProjection F hFs n)).app _ ≪≫
    (representedAffineDerivedAssociated (site F) (limitBase F) (site_contains F)
      (lineObjectAt F hFs n)).mapIso
      (extendScalarsQStaircaseIso (stairCoeff F ϖ) (lineRingMapAt F hFs n)
        (representedAffineDerivedExtension (site F) (limitBase F) (site_contains F)
          (lineObjectProjection F hFs n)))

variable (hϖ : ∀ n : ℕ, (limit.π F (op n)).hom (ϖ ^ (n + 1)) = 0)

include hϖ in
/-- `x^{n+1}` is a multiple of `x - ϖ^{i+1}` on `𝔸¹_{Aₙ}`, `ϖ^{n+1}` vanishing in `Aₙ`. -/
theorem xPow_mem_span_lineRingMapAt_stairCoeff (n i : ℕ) :
    (Scheme.ΓSpecIso (lineRingAt F n)).inv.hom (Polynomial.X ^ (n + 1)) ∈
      Ideal.span {lineRingMapAt F hFs n (stairCoeff F ϖ i)} := by
  rw [lineRingMapAt_apply, Ideal.mem_span_singleton]
  apply map_dvd
  set b := (limit.π F (op n)).hom (ϖ ^ (i + 1))
  have hb : b ^ (n + 1) = 0 := by
    rw [← map_pow, ← pow_mul, mul_comm, pow_mul, map_pow, hϖ n, zero_pow (Nat.succ_ne_zero i)]
  have h := sub_dvd_pow_sub_pow (Polynomial.X : Polynomial (F.obj (op n))) (Polynomial.C b) (n + 1)
  rw [← Polynomial.C_pow, hb, Polynomial.C_0, sub_zero] at h
  simpa [Polynomial.map_sub, b] using h

include hϖ in
/-- `⊕ᵢ 𝒪/(x - ϖ^{i+1})[2i]` on `𝔸¹_{Aₙ}` is supported on `V(x)`. -/
theorem cohomologySupportedOn_lineStageObject (n : ℕ) :
    Space.CohomologySupportedOn (site F) (limitBase F) (site_contains F)
      (yoneda.obj (lineObjectAt F hFs n)) (isAlgebraicSpace_yoneda _ _ _ _)
      (Set.range (pointsMap _ _ _ _ (yoneda.map (idealQuotientSpecMap (site F) (limitBase F)
        (site_contains F) (nilIdealAt F hFs n))))) (lineStageObject F hFs ϖ n) := by
  refine cohomologySupportedOn_range_idealQuotientSpecMap _ _ _ _ _
    (qcohDerived_representedAffineDerivedAssociated_obj _ _ _ _ _) _ fun i r hr s => ?_
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  have := isIso_representedAffineDerivedAdjunction_unit (site F) (limitBase F) (site_contains F)
    (lineObjectAt F hFs n)
  exact smul_eq_zero_of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((asIso (representedAffineDerivedAdjunction (site F) (limitBase F) (site_contains F)
      (lineObjectAt F hFs n)).unit).app _).symm)
    (smul_eq_zero_homologyFunctor_Q_staircase _ _ _
      (fun j => Ideal.mul_mem_left _ b (xPow_mem_span_lineRingMapAt_stairCoeff F hFs ϖ hϖ n j)) i)
    s

include hϖ in
/-- `Kₙ` is supported on `Zₙ`. -/
theorem cohomologySupportedOn_stageObject (n : ℕ) :
    Space.CohomologySupportedOn (site F) (limitBase F) (site_contains F)
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).1
      (spaceAt F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n).2
      (stageSupport F hFs n) (stageObject F hFs ϖ n) := by
  let ι := lineSpaceIso F hFs n
  let g := (schemeSpaceFunctor (site F) (limitBase F) (site_contains F)).map
    (lineObjectProjection F hFs n)
  have hj : spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n =
      ι.inv ≫ g := (Iso.eq_inv_comp ι).2 (lineSpaceIso_hom_spaceProjection F hFs n)
  have h₁ := cohomologySupportedOn_smallEtaleDerivedModulePullback ι.inv _
    (cohomologySupportedOn_of_iso' _ _ _ (lineStageObjectIso F hFs ϖ n).symm
      (cohomologySupportedOn_lineStageObject F hFs ϖ hϖ n))
  have h₂ := cohomologySupportedOn_of_iso' _ _ _
    ((smallEtaleDerivedModulePullbackCompIso _ _ _ ι.inv g).app (limitObject F ϖ) ≪≫
      (smallEtaleDerivedModulePullbackCongr _ _ _ hj.symm).app (limitObject F ϖ)) h₁
  intro i x hx
  obtain ⟨z, hz⟩ := h₂ i hx
  refine ⟨z, ?_⟩
  have hid : ι.inv.hom ≫ ι.hom.hom = 𝟙 _ := congrArg (fun t => t.hom) ι.inv_hom_id
  exact (pointsMap_comp_apply _ _ _ (yoneda.map (idealQuotientSpecMap (site F) (limitBase F)
      (site_contains F) (nilIdealAt F hFs n))) ι.hom.hom z).trans ((congrArg _ hz).trans
    ((pointsMap_comp_apply _ _ _ ι.inv.hom ι.hom.hom x).symm.trans
      (by rw [hid, pointsMap_id]; rfl)))

variable (hFl : ∀ n : ℕ,
    (RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent)

/-- **The counterexample to the support clause of Stacks 0DIR**: `X = 𝔸¹_A`,
`Kₙ = ⊕ᵢ 𝒪_{Xₙ}/(x - ϖ^{i+1})[2i]`, supported on `Zₙ = V(x)`. -/
def supportedSystem : SupportedDerivedExistenceSystem.{u} where
  system := F
  transition_surjective := hFs
  transition_locallyNilpotent := hFl
  B := site F
  containsLimitBase := site_contains F
  containsBaseAt := site_contains_baseAt F hFs
  X := space F
  separated := isSeparated_space_hom F
  flat := isFlat_space_hom F
  finitePresentation := isFinitePresentation_space_hom F
  K := stageObject F hFs ϖ
  pseudoCoherent := isPseudoCoherentOn_stageObject F hFs ϖ
  φ n := (stageTransition F hFs ϖ n).hom
  φ_isIso _ := inferInstance
  support := stageSupport F hFs
  isClosed_support := isClosed_stageSupport F hFs
  isProperOver_support := isProperOver_stageSupport F hFs
  supported := cohomologySupportedOn_stageObject F hFs ϖ hϖ

end System

/-! ### No lift is supported on a closed subset proper over `A` -/

section Refutation

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Examples.StaircaseComplex

/-- The conclusion of Stacks 0DIR for a system `D`, with its support clause: some `K`
pseudo-coherent relative to `A` has `Ljₙ^* K ≅ Kₙ` for every `n` and is supported on a closed
subset of `|X|` proper over `A`. -/
abbrev SupportClauseHolds (D : SupportedDerivedExistenceSystem.{u}) : Prop :=
  ∃ (K : D.limitDerivedCategory)
    (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
    IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
        D.X.left.2 D.X.hom.hom
        (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
          D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
      (∀ n : ℕ, Nonempty ((D.stageDerivedPullback n).obj K ≅ D.K n)) ∧
      ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
        (hT : _root_.IsClosed T),
        IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
            (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
            (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
              D.containsLimitBase D.finitePresentation.1) T hT ∧
          ∀ i : ℤ, supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
                D.X.left.2).O)).obj
              ((DerivedCategory.homologyFunctor (Space.Modules.{u, u} D.B (limitBase D.system)
                D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T

variable (hϖ : ∀ n : ℕ, (limit.π F (op n)).hom (ϖ ^ (n + 1)) = 0)
  (hFl : ∀ n : ℕ,
    (RingHom.ker (F.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent)
  (hker : ∀ n : ℕ, RingHom.ker (limit.π F (op n)).hom = Ideal.span {ϖ ^ (n + 1)})

include hFs hker in
/-- `Γ(𝔸¹_A) ⟶ Γ(𝔸¹_{Aₙ})` is surjective with kernel generated by `ϖ^{n+1}`. -/
theorem ker_lineRingMapAt (n : ℕ) :
    RingHom.ker (lineRingMapAt F hFs n) =
      Ideal.span {(Scheme.ΓSpecIso (lineRing F)).inv.hom (Polynomial.C (ϖ ^ (n + 1)))} := by
  let eT := (Scheme.ΓSpecIso (lineRing F)).commRingCatIsoToRingEquiv
  ext x
  obtain ⟨p, rfl⟩ := eT.symm.surjective x
  change (Scheme.ΓSpecIso (lineRing F)).inv.hom p ∈ _ ↔ (Scheme.ΓSpecIso (lineRing F)).inv.hom p ∈ _
  have hinj : Function.Injective (Scheme.ΓSpecIso (lineRingAt F n)).inv.hom :=
    (Scheme.ΓSpecIso (lineRingAt F n)).commRingCatIsoToRingEquiv.symm.injective
  rw [RingHom.mem_ker, lineRingMapAt_apply, map_eq_zero_iff _ hinj, Ideal.mem_span_singleton]
  have hp : p.map (limit.π F (op n)).hom = 0 ↔ p ∈ RingHom.ker
      (Polynomial.mapRingHom (limit.π F (op n)).hom) := Iff.rfl
  rw [hp, Polynomial.ker_mapRingHom, hker n, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton]
  constructor
  · exact map_dvd (Scheme.ΓSpecIso (lineRing F)).inv.hom
  · intro h
    have := map_dvd (Scheme.ΓSpecIso (lineRing F)).hom.hom h
    simpa [← CommRingCat.comp_apply] using this

include hFs in
/-- `Γ(𝔸¹_A) ⟶ Γ(𝔸¹_{Aₙ})` is surjective. -/
theorem surjective_lineRingMapAt (n : ℕ) : Function.Surjective (lineRingMapAt F hFs n) := by
  intro y
  obtain ⟨q, rfl⟩ := (Scheme.ΓSpecIso (lineRingAt F n)).commRingCatIsoToRingEquiv.symm.surjective y
  obtain ⟨p, rfl⟩ := surjective_lineRingProjection F hFs n q
  exact ⟨_, lineRingMapAt_apply F hFs n p⟩

/-- The evaluation `Γ(𝔸¹_{Aₙ}) ⟶ Aₙ` at `x = b`. -/
abbrev evalAt (n : ℕ) (b : F.obj (op n)) :
    Γ((BigFppfOver.toScheme (site F) (limitBase F) (site_contains F)).obj
      (lineObjectAt F hFs n), ⊤) →+* F.obj (op n) :=
  (Polynomial.evalRingHom b).comp (Scheme.ΓSpecIso (lineRingAt F n)).hom.hom

/-- Evaluating at `x = π(a)` after `A[x] ⟶ Aₙ[x]` is evaluating at `x = a` and projecting. -/
theorem evalAt_lineRingMapAt (n : ℕ) (a : (limit F : CommRingCat.{u}))
    (p : Polynomial (limit F : CommRingCat.{u})) :
    evalAt F hFs n ((limit.π F (op n)).hom a)
        (lineRingMapAt F hFs n ((Scheme.ΓSpecIso (lineRing F)).inv.hom p)) =
      (limit.π F (op n)).hom (p.eval a) := by
  rw [lineRingMapAt_apply]
  simp only [evalAt, RingHom.comp_apply, Polynomial.coe_evalRingHom]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, Polynomial.eval_map,
    Polynomial.eval₂_at_apply]

variable [IsDomain (limit F : CommRingCat.{u})] [IsNoetherianRing (limit F : CommRingCat.{u})]
  [IsLocalRing (limit F : CommRingCat.{u})]

include hFs hϖ hFl hker in
/-- **No lift of `(Kₙ)` is supported on a closed subset of `|X|` proper over `A`.** If `K` is
pseudo-coherent relative to `A` with `Ljₙ^* K ≅ Kₙ` for every `n`, then no closed `T ⊆ |X|`
proper over `A` supports `K`: `RΓ(X, K)` has finite cohomology, killed by a power of a nonzero
`c ∈ A[x]` vanishing on `T`; base change to `Aₙ[x]` (a Tor argument) makes `c^N` kill
`Aₙ[x]/(x - ϖ^{i+1})`, so `c(ϖ^{i+1}) = 0` for every `i`, and `c = 0`. -/
theorem not_exists_isRelativelyPseudoCoherent_isProperOver_cohomologySupportedOn
    (hϖ0 : ϖ ≠ 0) (hϖu : ¬ IsUnit ϖ) (hpow : Function.Injective (fun i : ℕ => ϖ ^ (i + 1)))
    (hsep : ∀ (a : (limit F : CommRingCat.{u})) (N : ℕ), 0 < N →
      (∀ n, (limit.π F (op n)).hom a ^ N = 0) → a = 0) :
    ¬ SupportClauseHolds (supportedSystem F hFs ϖ hϖ hFl) := by
  rintro ⟨K, hK, hpc, hψ, T, hT, hTp, hTK⟩
  let B := site F
  let S := limitBase F
  let hS := site_contains F
  let U := lineObject F
  let RT := Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  let eT := Scheme.ΓSpecIso (lineRing F)
  have hnoeth : IsNoetherianRing RT :=
    isNoetherianRing_of_ringEquiv _ eT.commRingCatIsoToRingEquiv.symm
  -- `M = RΓ(X, K)` is pseudo-coherent with finite cohomology
  let M := (representedAffineDerivedSections B S hS U).obj K
  have hMpc : StacksDraft.PseudoCoherence.IsPseudoCoherent M := by
    rw [StacksDraft.PseudoCoherence.pseudoCoherent_iff_all]
    intro m
    have h₁ := (isRelativelyPseudoCoherent_iff_forall _ _ _ _ _ _ _ _).1 hpc m
    have h₂ := (isRelativelyPseudoCoherentFrom_iff_isPseudoCoherentFrom B S hS (space F).hom
      (isFlat_space_hom F) (isFinitePresentation_space_hom F).1 _ m).1 h₁
    exact (isPseudoCoherentFrom_iff_representedAffineDerivedSections B S hS U K hK m).1 h₂
  have hfin (i : ℤ) : Module.Finite RT ((DerivedCategory.homologyFunctor (ModuleCat.{u} RT) i).obj
      M) :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology M 0
      PUnit.{u + 1}).2.1.1 hMpc).2 i
  -- `T` is not all of `|X|`, so a nonzero `c` vanishes on `T`
  have hTne : T ≠ Set.univ := by
    rintro rfl
    exact not_isProperOver_univ F ϖ hϖ0 hϖu _ hTp
  let XU := (BigFppfOver.toScheme B S hS).obj U
  let T' : Set (PrimeSpectrum RT) :=
    {p | (pointsEquivScheme B S hS U).symm (XU.isoSpec.inv p) ∈ T}
  have hT' : _root_.IsClosed T' := by
    have hc := (isClosed_pointTopology_yoneda_iff_isClosed_image B S hS U T).1 hT
    have himg : pointsToScheme B S hS U '' T = (pointsEquivScheme B S hS U).symm ⁻¹' T :=
      (pointsEquivScheme B S hS U).image_eq_preimage_symm T
    rw [himg] at hc
    exact hc.preimage XU.isoSpec.inv.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal T').1 hT'
  have hIne : I ≠ ⊥ := by
    rintro rfl
    apply hTne
    rw [Set.eq_univ_iff_forall]
    intro y
    have hy : XU.isoSpec.hom (pointsEquivScheme B S hS U y) ∈ T' := by
      rw [hI, Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero]
      trivial
    have hy' : (pointsEquivScheme B S hS U).symm
        (XU.isoSpec.inv (XU.isoSpec.hom (pointsEquivScheme B S hS U y))) ∈ T := hy
    have hcancel : XU.isoSpec.inv (XU.isoSpec.hom (pointsEquivScheme B S hS U y)) =
        pointsEquivScheme B S hS U y := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [hcancel] at hy'
    exact ((pointsEquivScheme B S hS U).symm_apply_apply y) ▸ hy'
  obtain ⟨c, hcI, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIne
  have hkill (i : ℤ) : ∃ N : ℕ, ∀ s : (DerivedCategory.homologyFunctor (ModuleCat.{u} RT) i).obj
      M, c ^ N • s = 0 := by
    have hsupp : Module.support RT ((DerivedCategory.homologyFunctor (ModuleCat.{u} RT) i).obj M)
        ⊆ PrimeSpectrum.zeroLocus (Ideal.span {c} : Set RT) := by
      intro p hp
      have hx := pointsEquivScheme_symm_mem_of_mem_support_homology B S hS U K hK T hTK i
        (XU.isoSpec.inv p) (by
          have hcancel : XU.isoSpec.hom (XU.isoSpec.inv p) = p := by
            have h := Scheme.Hom.comp_apply XU.isoSpec.inv XU.isoSpec.hom p
            rw [Iso.inv_hom_id] at h
            exact h.symm
          rwa [hcancel])
      have hpT : p ∈ T' := hx
      rw [hI] at hpT
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
        Set.singleton_subset_iff]
      exact (PrimeSpectrum.mem_zeroLocus _ _).1 hpT hcI
    rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsupp
    obtain ⟨N, hN⟩ := hsupp (Ideal.subset_span rfl)
    exact ⟨N, fun s => Module.mem_annihilator.1 hN s⟩
  -- `c' ∈ A[x]` with `c = c'` vanishes at every `ϖ^{i+1}`
  let c' : Polynomial (limit F : CommRingCat.{u}) := eT.hom.hom c
  have hcc' : c = eT.inv.hom c' := by
    change c = (eT.hom ≫ eT.inv).hom c
    rw [Iso.hom_inv_id]
    rfl
  have heval (i : ℕ) : c'.eval (ϖ ^ (i + 1)) = 0 := by
    obtain ⟨N₁, hN₁⟩ := hkill (-(2 * (i : ℤ)))
    obtain ⟨N₂, hN₂⟩ := hkill (-(2 * (i : ℤ)) + 1)
    let a := c ^ (N₁ + N₂ + 1)
    have ha₁ : ∀ s : (DerivedCategory.homologyFunctor (ModuleCat.{u} RT) (-(2 * (i : ℤ)))).obj M,
        a • s = 0 := fun s => by
      rw [show a = c ^ (N₂ + 1) * c ^ N₁ by ring, mul_smul, hN₁, smul_zero]
    have ha₂ : ∀ s : (DerivedCategory.homologyFunctor (ModuleCat.{u} RT)
        (-(2 * (i : ℤ)) + 1)).obj M, a • s = 0 := fun s => by
      rw [show a = c ^ (N₁ + 1) * c ^ N₂ by ring, mul_smul, hN₂, smul_zero]
    refine hsep _ (2 * (N₁ + N₂ + 1)) (by omega) fun n => ?_
    let g := lineObjectProjection F hFs n
    let f := lineRingMapAt F hFs n
    let L := representedAffineDerivedExtension B S hS g
    have hw : (Scheme.ΓSpecIso (lineRing F)).inv.hom (Polynomial.C (ϖ ^ (n + 1))) ∈
        nonZeroDivisors RT := by
      have : IsDomain RT := MulEquiv.isDomain _ eT.commRingCatIsoToRingEquiv.toMulEquiv
      refine mem_nonZeroDivisors_of_ne_zero ?_
      have hinj : Function.Injective (Scheme.ΓSpecIso (lineRing F)).inv.hom :=
        eT.commRingCatIsoToRingEquiv.symm.injective
      rw [Ne, map_eq_zero_iff _ hinj, Polynomial.C_eq_zero]
      exact pow_ne_zero _ hϖ0
    have htor := smul_sq_homologyFunctor_eq_zero f (surjective_lineRingMapAt F hFs n) _
      (ker_lineRingMapAt F hFs ϖ hker n) hw L hMpc (-(2 * (i : ℤ))) a ha₁ ha₂
    -- `RΓ(X, K) ⊗^L Γ(𝔸¹_{Aₙ}) ≅` the staircase complex of the `x - ϖ^{i+1}` over `Aₙ[x]`
    let ι := lineSpaceIso F hFs n
    let gs := representedSpaceMap B S hS g
    let jn := spaceProjection F (site F) (site_contains F) (site_contains_baseAt F hFs) (space F) n
    have hj : gs = ι.hom ≫ jn := (lineSpaceIso_hom_spaceProjection F hFs n).symm
    obtain ⟨ψn⟩ := hψ n
    let e₁ : (smallEtaleDerivedModulePullback B S hS gs).obj K ≅
        (smallEtaleDerivedModulePullback B S hS gs).obj (limitObject F ϖ) :=
      (smallEtaleDerivedModulePullbackCongr B S hS hj).app K ≪≫
        ((smallEtaleDerivedModulePullbackCompIso B S hS ι.hom jn).app K).symm ≪≫
        (smallEtaleDerivedModulePullback B S hS ι.hom).mapIso ψn ≪≫
        (smallEtaleDerivedModulePullbackCompIso B S hS ι.hom jn).app (limitObject F ϖ) ≪≫
        (smallEtaleDerivedModulePullbackCongr B S hS hj.symm).app (limitObject F ϖ)
    have := isIso_representedAffineDerivedSectionsBaseChangeMap B S hS g K hK
    have := isIso_representedAffineDerivedSectionsBaseChangeMap B S hS g (limitObject F ϖ)
      (qcohDerived_limitObject F ϖ)
    let e₂ : L.functor.obj M ≅
        DerivedCategory.Q.obj (staircase _ (fun j => f (stairCoeff F ϖ j))) :=
      asIso (representedAffineDerivedSectionsBaseChangeMap B S hS g K) ≪≫
        (representedAffineDerivedSections B S hS (lineObjectAt F hFs n)).mapIso e₁ ≪≫
        (asIso (representedAffineDerivedSectionsBaseChangeMap B S hS g (limitObject F ϖ))).symm ≪≫
        L.functor.mapIso (limitObjectSectionsIso F ϖ).symm ≪≫
        extendScalarsQStaircaseIso (stairCoeff F ϖ) f L
    obtain ⟨s₀, hs₀⟩ := exists_homologyFunctor_Q_staircase _ (fun j => f (stairCoeff F ϖ j)) i
    have h₀ : f (a ^ 2) • s₀ = 0 :=
      smul_eq_zero_of_iso ((DerivedCategory.homologyFunctor _ (-(2 * (i : ℤ)))).mapIso e₂.symm)
        htor s₀
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (hs₀ _ h₀)
    -- evaluate at `x = ϖ^{i+1}`
    have hev := congrArg (evalAt F hFs n ((limit.π F (op n)).hom (ϖ ^ (i + 1)))) hr
    have ha2 : a ^ 2 = eT.inv.hom (c' ^ (2 * (N₁ + N₂ + 1))) := by
      rw [map_pow, ← hcc']
      ring
    rw [map_mul, evalAt_lineRingMapAt, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_self, map_zero, mul_zero, ha2, evalAt_lineRingMapAt, Polynomial.eval_pow, map_pow] at hev
    exact hev.symm
  exact hc0 (by
    rw [hcc', eq_zero_of_eval_pow_succ_eq_zero ϖ hpow c' heval, map_zero])

end Refutation

/-! ### The counterexample over `ℤ_2` -/

section TwoAdic

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Examples.TwoAdicTower

/-- `ϖ^{n+1}` vanishes in `Aₙ = ℤ/2^{n+1}`. -/
theorem limit_π_uniformizer_pow (n : ℕ) :
    (limit.π tower (op n)).hom (uniformizer ^ (n + 1)) = 0 := by
  rw [← RingHom.mem_ker, ker_limit_π]
  exact Ideal.subset_span rfl

/-- **The support clause of the generalized derived existence theorem proposed in Stacks 0DIR is
false.** There is a system satisfying all of its hypotheses, with `X` moreover flat over `A` —
`A = ℤ_2`, `X = 𝔸¹_A`, `Kₙ = ⊕ᵢ 𝒪_{Xₙ}/(x - 2^{i+1})[2i]`, each `Kₙ` supported on `V(x)`, finite
over `Aₙ` — for which no `K ∈ D_QCoh(𝒪_X)` pseudo-coherent relative to `A` with `Ljₙ^* K ≅ Kₙ`
for every `n` (with no compatibility asked of the isomorphisms) is supported on a closed subset
of `|X|` proper over `A`. -/
@[stacks 0DIR "refutation of the clause that K is supported on one closed subset proper over A: \
A = Z_2, X = A^1_A, K_n = sum_i O_{X_n}/(x - 2^{i+1})[2i] (errata entry 0DIR(support of K))"]
theorem not_forall_exists_isRelativelyPseudoCoherent_isProperOver_cohomologySupportedOn :
    ¬ ∀ D : SupportedDerivedExistenceSystem.{0},
      ∃ (K : D.limitDerivedCategory)
        (hK : QcohDerived D.B (limitBase D.system) D.containsLimitBase D.X.left K),
        IsRelativelyPseudoCoherent D.B (limitBase D.system) D.containsLimitBase D.X.left.1
            D.X.left.2 D.X.hom.hom
            (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
              D.containsLimitBase D.finitePresentation.1) ⟨K, hK⟩ ∧
          (∀ n : ℕ, Nonempty ((D.stageDerivedPullback n).obj K ≅ D.K n)) ∧
          ∃ (T : Set (points D.B (limitBase D.system) D.containsLimitBase D.X.left.1))
            (hT : _root_.IsClosed T),
            IsProperOver D.B (limitBase D.system) D.containsLimitBase D.X.left.2
                (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 D.X.hom.hom
                (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation D.B (limitBase D.system)
                  D.containsLimitBase D.finitePresentation.1) T hT ∧
              ∀ i : ℤ, supportOfSheaf D.B (limitBase D.system) D.containsLimitBase D.X.left.1
                ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
                  (smallEtaleRingedSite D.B (limitBase D.system) D.containsLimitBase D.X.left.1
                    D.X.left.2).O)).obj
                  ((DerivedCategory.homologyFunctor (Space.Modules.{0, 0} D.B (limitBase D.system)
                    D.containsLimitBase D.X.left.1 D.X.left.2) i).obj K)) ⊆ T := fun h =>
  not_exists_isRelativelyPseudoCoherent_isProperOver_cohomologySupportedOn tower
    surjective_tower_map_succ uniformizer limit_π_uniformizer_pow
    locallyNilpotent_ker_tower_map_succ ker_limit_π
    uniformizer_ne_zero not_isUnit_uniformizer injective_uniformizer_pow
    (fun a _ hN h => eq_zero_of_forall_limit_π_pow_eq_zero a hN h)
    (h (supportedSystem tower surjective_tower_map_succ uniformizer limit_π_uniformizer_pow
      locallyNilpotent_ker_tower_map_succ))

end TwoAdic

end Stacks.Examples.DerivedExistenceSupportNotProper

end

module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.RankOneLocusDivisor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.DerivedPushforwardToField
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorDegreeDifference
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafPullback

/-!
# The degree of the divisor of a generator

This is step (a) of the proof of [Stacks, Tag 0B9X]. Let `K` be a field and `Y` a proper
integral scheme of dimension at most one over `K` with `Γ(Y, 𝒪_Y) = K`. If `ℒ` is an invertible
`𝒪_Y`-module with `R p_*(ℒ[0]) ≅ 𝒪_K[0]`, so that `H⁰(Y, ℒ) = K` and `H¹(Y, ℒ) = 0`, then the
degree of `ℒ` is `χ(ℒ) - χ(𝒪_Y) = 1 - (1 - g) = g`, and the zero scheme of any nonzero section of
`ℒ` has `g`-dimensional ring of global functions ([Stacks, Tag 0AYR]).

## Main results

* `AlgebraicGeometry.finrank_moduleSpecΓFunctor_obj_unit`: `Γ(Spec K, 𝒪) = K` is one-dimensional.
* `AlgebraicGeometry.eulerCharacteristic_eq_one_of_derivedPushforward_iso`: `χ(ℒ) = 1` when
  `R p_*(ℒ[0]) ≅ 𝒪_K[0]`.
* `AlgebraicGeometry.finrank_globalSections_zeroScheme_eq_genus`: the zero scheme of a nonzero
  section of such an `ℒ` has degree `g`.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **`Γ(Spec K, 𝒪) = K` is one-dimensional over `K`.** -/
theorem finrank_moduleSpecΓFunctor_obj_unit (K : Type u) [Field K] :
    Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
      (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)) = 1 := by
  let φ := (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφ : Function.Bijective φ :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv
  let l : K →ₗ[K] ((moduleSpecΓFunctor (R := .of K)).obj
      (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)) :=
    { toFun := fun x => φ x
      map_add' := fun x y => map_add φ x y
      map_smul' := fun c x => map_mul φ c x }
  exact ((LinearEquiv.ofBijective l hφ).finrank_eq.symm).trans (Module.finrank_self K)


/-- **`χ(ℒ) = 1` when `R p_*(ℒ[0]) ≅ 𝒪_K[0]`**, for `p : Y ⟶ Spec K` proper and `ℒ` coherent. -/
theorem eulerCharacteristic_eq_one_of_derivedPushforward_iso (K : Type u) [Field K]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) [IsProper p] (L : Y.Modules) [L.IsCoherent]
    (hL : Nonempty ((derivedPushforward p.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj L) ≅
      (DerivedCategory.singleFunctor (Spec (.of K)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of K)).ringCatSheaf))) :
    eulerCharacteristic K p L = 1 := by
  obtain ⟨e⟩ := hL
  let : (moduleSpecΓFunctor (R := .of K)).Additive := ⟨by intro M N φ ψ; ext x; rfl⟩
  rw [eulerCharacteristic_eq_finsum_homology_derivedPushforward K p L,
    finsum_eq_single _ (0 : ℤ)]
  · have h0 : Module.finrank K ((moduleSpecΓFunctor (R := .of K)).obj
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules 0).obj
          ((derivedPushforward p.toLRSHom.toShHom).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj L)))) = 1 := by
      rw [((moduleSpecΓFunctor (R := .of K)).mapIso
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules 0).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso (Spec (.of K)).Modules 0).app
            _)).toLinearEquiv.finrank_eq]
      exact finrank_moduleSpecΓFunctor_obj_unit K
    simpa only [Int.negOnePow_zero, Units.val_one, one_mul, Nat.cast_eq_one] using h0
  · intro i hi
    have hz : IsZero ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).obj
        ((DerivedCategory.singleFunctor (Spec (.of K)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of K)).ringCatSheaf))) := by
      refine IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi)
        ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ (Spec (.of K)).Modules 0).app _) ≪≫
          (DerivedCategory.homologyFunctorFactors (Spec (.of K)).Modules i).app _)
    have hz' := (moduleSpecΓFunctor (R := .of K)).map_isZero
      (hz.of_iso ((DerivedCategory.homologyFunctor (Spec (.of K)).Modules i).mapIso e))
    have := (ModuleCat.isZero_iff_subsingleton).1 hz'
    rw [Module.finrank_zero_of_subsingleton]
    simp

/-- **The zero scheme of a nonzero section of an invertible module with `R p_*(ℒ[0]) ≅ 𝒪_K[0]`
has degree `g`**: on a proper integral scheme `Y` of dimension at most one over a field `K` with
`Γ(Y, 𝒪_Y) = K`, the degree `deg ℒ = χ(ℒ) - χ(𝒪_Y) = 1 - (1 - g)` ([Stacks, Tag 0AYR]) is the
dimension of the global functions of the zero scheme of any regular section. -/
theorem finrank_globalSections_zeroScheme_eq_genus (K : Type u) [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of K)) [IsProper p] [IsIntegral Y] (hdim : topologicalKrullDim Y ≤ 1)
    (hΓ : letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
      Module.finrank K Γ(Y, ⊤) = 1)
    (L : Y.Modules) [hLinv : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (hL : Nonempty ((derivedPushforward p.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj L) ≅
      (DerivedCategory.singleFunctor (Spec (.of K)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of K)).ringCatSheaf)))
    (t : Γ(L, ⊤)) (ht : t ≠ 0) :
    letI : Algebra K Γ((zeroScheme Y L t).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ ((zeroScheme Y L t).subschemeι ≫ p).appTop).hom.toAlgebra
    Module.finrank K Γ((zeroScheme Y L t).subscheme, ⊤) = genus p := by
  let : Algebra K Γ((zeroScheme Y L t).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ ((zeroScheme Y L t).subschemeι ≫ p).appTop).hom.toAlgebra
  have hnoeth : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hLstacks : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hLinv
  have hLcoh : SheafOfModules.IsCoherent L :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible Y L
  have : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit K p
  let s : L.sections := Stacks.Divisors.sectionsOfTop L t
  have hs : s.eval (op ⊤) = t := Stacks.Divisors.sectionsOfTop_eval_top L t
  have hreg := isRegularSection_of_eval_top_ne_zero L s (hs ▸ ht)
  have : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L := hLinv
  have hdeg := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_unit_zeroScheme K p hdim
    L s hreg
  rw [hs, finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K
    ((zeroScheme Y L t).subschemeι ≫ p),
    invertibleCurveDegree_eq_eulerCharacteristic_sub K p hdim L,
    eulerCharacteristic_eq_one_of_derivedPushforward_iso K p L hL,
    eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus K p hdim, hΓ] at hdeg
  omega

/-- **A morphism to the spectrum of a field which is bijective on global sections has
one-dimensional global sections.** -/
theorem finrank_globalSections_eq_one_of_bijective_appTop (K : Type u) [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of K)) (h : Function.Bijective p.appTop) :
    letI : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    Module.finrank K Γ(Y, ⊤) = 1 := by
  let : Algebra K Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  have hb : Function.Bijective (algebraMap K Γ(Y, ⊤)) :=
    h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv)
  exact ((LinearEquiv.ofBijective (Algebra.linearMap K Γ(Y, ⊤)) hb).finrank_eq.symm).trans
    (Module.finrank_self K)

end AlgebraicGeometry

namespace AlgebraicGeometry.RigidifiedPicard

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

include hσ in
/-- **The fibres of a base change of a pointed proper integral curve have only constant
functions**: the fibre of `X_T ⟶ T` over `v` is integral, proper over `κ(v)` and has the section
induced by `σ`, so `Γ(X_v, 𝒪) = κ(v)` ([Stacks, Tag 0B9U]). -/
theorem finrank_globalSections_fiber_pullbackSnd [IsVariety k f] [Smooth f] [IsProper f]
    {T : Scheme.{u}} (q : T ⟶ Spec (.of k)) (v : T) :
    letI : Algebra (T.residueField v) Γ((pullback.snd f q).fiber v, ⊤) :=
      ((Scheme.ΓSpecIso (.of (T.residueField v))).inv ≫
        ((pullback.snd f q).fiberToSpecResidueField v).appTop).hom.toAlgebra
    Module.finrank (T.residueField v) Γ((pullback.snd f q).fiber v, ⊤) = 1 := by
  have := isIntegral_fiber_pullbackSnd f σ hσ q v
  let sT : T ⟶ pullback f q :=
    pullback.lift (q ≫ σ) (𝟙 T) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  let σv : Spec (T.residueField v) ⟶ (pullback.snd f q).fiber v :=
    pullback.lift (T.fromSpecResidueField v ≫ sT) (𝟙 _)
      (by rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp])
  have hσv : σv ≫ (pullback.snd f q).fiberToSpecResidueField v = 𝟙 _ := pullback.lift_snd _ _ _
  have hUC : UniversallyClosed ((pullback.snd f q).fiberToSpecResidueField v) :=
    inferInstanceAs (UniversallyClosed (pullback.snd _ _))
  have hc := @isIso_c_of_section_of_universallyClosed (T.residueField v) _ _
    ((pullback.snd f q).fiberToSpecResidueField v) inferInstance hUC σv hσv
  exact finrank_globalSections_eq_one_of_bijective_appTop _ _
    ((Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_bijective_appTop _).1 hc)

/-- **The fibres of a base change of a proper scheme over `k` have the same genus**: the fibre
of `X_T ⟶ T` over `v` is the base change of `X` to `κ(v)`. -/
theorem genus_fiberToSpecResidueField_pullbackSnd [IsProper f] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) (v : T) :
    genus ((pullback.snd f q).fiberToSpecResidueField v) = genus f := by
  let φ : Spec (T.residueField v) ⟶ Spec (.of k) := T.fromSpecResidueField v ≫ q
  let : Algebra k (T.residueField v) := (Spec.preimage φ).hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k (T.residueField v))) = φ :=
    Spec.map_preimage φ
  have hsq : IsPullback ((pullback.snd f q).fiberι v ≫ pullback.fst f q)
      ((pullback.snd f q).fiberToSpecResidueField v) f φ :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback f q)
  rw [← hφ] at hsq
  exact genus_baseChange k (T.residueField v) _ _ f hsq

include σ hσ in
/-- **Step (a) of [Stacks, Tag 0B9X]: the divisor of a generator has degree `g`.** Let `f` be a
smooth proper curve over `k` with a rational point, `T` a `k`-scheme, `ℒ` invertible on `X_T` and
`s : 𝒪 ⟶ ℒ` a generator relative to `f_T` (so `Rf_{T,*}ℒ ≅ 𝒪_T[0]`). Then the zero scheme of
`s` is finite locally free of rank `g = genus f` over `T`: on the fibre over `v` it is the zero
scheme of a nonzero section of `ℒ_v`, and `R(f_v)_*(ℒ_v[0]) ≅ 𝒪_{κ(v)}[0]` gives
`deg ℒ_v = χ(ℒ_v) - χ(𝒪_{X_v}) = 1 - (1 - g)` ([Stacks, Tag 0AYR], [Stacks, Tag 0BY9]). -/
theorem isFiniteLocallyFreeOfRank_zeroScheme_of_isGenerator
    [IsCurve k f] [Smooth f] [IsProper f] {T : Scheme.{u}} (q : T ⟶ Spec (.of k))
    (L : (pullback f q).Modules)
    [SheafOfModules.IsInvertible (pullback f q).sheaf.obj (pullback f q).ringCatSheaf.property L]
    (s : SheafOfModules.unit (pullback f q).ringCatSheaf ⟶ L)
    (hs : PushforwardGenerator.IsGenerator (pullback.snd f q).toLRSHom.toShHom L s) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((zeroScheme (pullback f q) L ((L.unitHomEquiv s).eval (op ⊤))).subschemeι ≫
        pullback.snd f q) (genus f) := by
  set p := pullback.snd f q
  set Z := zeroScheme (pullback f q) L ((L.unitHomEquiv s).eval (op ⊤))
  have hflf : Stacks.Morphisms.IsFiniteLocallyFree (Z.subschemeι ≫ p) :=
    (isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator f σ hσ q L s hs).2
  obtain ⟨hfin, hflat, -⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (Z.subschemeι ≫ p)).1 hflf
  have := hfin
  have := hflat
  let : SmoothOfRelativeDimension 1 f := Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f
  let : SmoothOfRelativeDimension 1 p :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f q) inferInstance
  refine (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).2 fun v => ?_
  have sq : IsPullback (p.fiberι v) (p.fiberToSpecResidueField v) p (T.fromSpecResidueField v) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨a, ha⟩ := exists_isPullback_subschemeι_baseChange sq Z
  let y : Spec (T.residueField v) := IsLocalRing.closedPoint (T.residueField v)
  have hy := Scheme.Hom.finrank_of_isPullback a _ _ _ ha y
  rw [Scheme.fromSpecResidueField_apply] at hy
  rw [← hy]
  have hfin' : IsFinite ((Z.comap (p.fiberι v)).subschemeι ≫ p.fiberToSpecResidueField v) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ha hfin
  have hflat' : Flat ((Z.comap (p.fiberι v)).subschemeι ≫ p.fiberToSpecResidueField v) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback ha hflat
  suffices hr : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((Z.comap (p.fiberι v)).subschemeι ≫ p.fiberToSpecResidueField v) (genus f) from
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_forall_finrank_eq _ _).1 hr y
  have hz : zeroScheme (p.fiber v) ((Scheme.Modules.pullback (p.fiberι v)).obj L)
      (pullbackGlobalSections (p.fiberι v) L ((L.unitHomEquiv s).eval (op ⊤))) =
      Z.comap (p.fiberι v) :=
    Stacks.Divisors.zeroScheme_pullback (p.fiberι v) L ((L.unitHomEquiv s).eval (op ⊤))
  rw [← hz]
  have hfinz : IsFinite ((zeroScheme (p.fiber v) ((Scheme.Modules.pullback (p.fiberι v)).obj L)
      (pullbackGlobalSections (p.fiberι v) L ((L.unitHomEquiv s).eval (op ⊤)))).subschemeι ≫
        p.fiberToSpecResidueField v) := by
    rwa [hz]
  have := isIntegral_fiber_pullbackSnd f σ hσ q v
  have hpr : IsProper (p.fiberToSpecResidueField v) := inferInstanceAs (IsProper (pullback.snd _ _))
  refine (@isFiniteLocallyFreeOfRank_iff_finrank_eq (T.residueField v) _ _ _ hfinz _).2 ?_
  rw [@finrank_globalSections_zeroScheme_eq_genus (T.residueField v) _ _
    (p.fiberToSpecResidueField v) hpr inferInstance
    (topologicalKrullDim_fiber_le_of_smoothOfRelativeDimension 1 p v)
    (finrank_globalSections_fiber_pullbackSnd f σ hσ q v)
    ((Scheme.Modules.pullback (p.fiberι v)).obj L) inferInstance
    (PushforwardGenerator.nonempty_derivedPushforward_fiber_iso L p s hs v) _
    (PushforwardGenerator.pullbackGlobalSections_fiberι_ne_zero L p
      (Stacks.Divisors.isFiniteLocallyFree_of_isInvertible _ L)
      (Stacks.Chow.isFlat_of_isInvertible L) s hs v)]
  exact genus_fiberToSpecResidueField_pullbackSnd f q v

/-! ### The divisor of a generator is determined by its degree -/

/-- The global section of `w ≫ s`, for an endomorphism `w` of the structure sheaf, is a multiple
of the section of `s`. -/
theorem exists_unitHomEquiv_comp_eval_top {Y : Scheme.{u}} (L : Y.Modules)
    (w : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ L) :
    ∃ c : Γ(Y, ⊤), ∀ x y : Γ(L, ⊤), x = (L.unitHomEquiv (w ≫ s)).eval (op ⊤) →
      y = (L.unitHomEquiv s).eval (op ⊤) → x = c • y := by
  let c : Y.ringCatSheaf.obj.obj (op ⊤) := w.val.app (op ⊤) (1 : Y.ringCatSheaf.obj.obj (op ⊤))
  refine ⟨c, fun x y hx hy => ?_⟩
  subst hx hy
  have h1 : c • (1 : Y.ringCatSheaf.obj.obj (op ⊤)) = c := by rw [smul_eq_mul, mul_one]
  exact (congrArg (s.val.app (op ⊤)).hom h1.symm).trans
    ((s.val.app (op ⊤)).hom.map_smul c (1 : Y.ringCatSheaf.obj.obj (op ⊤)))

/-- **The zero scheme of a multiple of a section contains the zero scheme of the section**: the
ideal of `Z(c • x)` is contained in that of `Z(x)`. -/
theorem zeroScheme_smul_le {Y : Scheme.{u}} (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] (c : Γ(Y, ⊤))
    (x : Γ(L, ⊤)) : zeroScheme Y L (c • x) ≤ zeroScheme Y L x := by
  rw [Scheme.IdealSheafData.le_def]
  intro U
  rw [zeroScheme_ideal, zeroScheme_ideal, Ideal.span_le]
  rintro a ⟨φ, rfl⟩
  rw [Scheme.Modules.map_smul, map_smul, smul_eq_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨φ, rfl⟩)

/-- **A degree-`0` divisor is empty**: an ideal sheaf whose closed subscheme is finite locally
free of rank `0` over the base is the unit ideal. -/
theorem eq_top_of_isFiniteLocallyFreeOfRank_zero {Y S : Scheme.{u}} (p : Y ⟶ S)
    (D : Y.IdealSheafData) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ p) 0] :
    D = ⊤ := by
  have := Stacks.Morphisms.isEmpty_of_isFiniteLocallyFreeOfRank_zero (D.subschemeι ≫ p)
  rw [← Scheme.IdealSheafData.ker_subschemeι D]
  exact (Scheme.Hom.ker_eq_top_iff_isEmpty _).2 inferInstance

/-- **Two divisors of the same degree, one contained in the other, are equal** on a smooth
relative curve: the difference is a divisor of degree `0` ([Stacks, Tag 0B9F]), hence empty. -/
theorem eq_of_le_of_isFiniteLocallyFreeOfRank {Y S : Scheme.{u}} (p : Y ⟶ S)
    [SmoothOfRelativeDimension 1 p] (D₁ D₂ : Y.IdealSheafData) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D₁.subschemeι ≫ p) r]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D₂.subschemeι ≫ p) r] (hle : D₂ ≤ D₁) :
    D₂ = D₁ := by
  obtain ⟨D, hD, hr⟩ := exists_isFiniteLocallyFreeOfRank_sub_mul_eq_of_le p D₁ D₂ r r hle
  rw [Nat.sub_self] at hr
  have := hr
  rw [hD, eq_top_of_isFiniteLocallyFreeOfRank_zero p D, Scheme.IdealSheafData.mul_top]

/-- **The divisor of a generator is the only divisor of its degree cut out by a section**: if
`s : 𝒪_Y ⟶ ℒ` is a generator relative to a smooth relative curve `p : Y ⟶ S` and `t : 𝒪_Y ⟶ ℒ`
is any morphism whose zero scheme is finite locally free over `S` of the same rank as that of
`s`, then the two zero schemes agree. Indeed `t = p^*a ≫ s`
(`PushforwardGenerator.exists_eq_pullbackEnd_comp`), so `Z(s) ⊆ Z(t)`, and nested divisors of the
same degree are equal. This is step (d) of the proof of [Stacks, Tag 0B9X]. -/
theorem zeroScheme_eq_of_isGenerator {Y S : Scheme.{u}} (p : Y ⟶ S)
    [SmoothOfRelativeDimension 1 p] (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s t : SheafOfModules.unit Y.ringCatSheaf ⟶ L)
    (hs : PushforwardGenerator.IsGenerator p.toLRSHom.toShHom L s) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((zeroScheme Y L ((L.unitHomEquiv s).eval (op ⊤))).subschemeι ≫ p) r]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((zeroScheme Y L ((L.unitHomEquiv t).eval (op ⊤))).subschemeι ≫ p) r] :
    zeroScheme Y L ((L.unitHomEquiv t).eval (op ⊤)) =
      zeroScheme Y L ((L.unitHomEquiv s).eval (op ⊤)) := by
  obtain ⟨a, ha, -⟩ := PushforwardGenerator.exists_eq_pullbackEnd_comp p.toLRSHom.toShHom L s t hs
  refine eq_of_le_of_isFiniteLocallyFreeOfRank p _ _ r ?_
  obtain ⟨c, hc⟩ := exists_unitHomEquiv_comp_eval_top L
    (PushforwardGenerator.pullbackEnd p.toLRSHom.toShHom a) s
  set x : Γ(L, ⊤) := (L.unitHomEquiv t).eval (op ⊤) with hx
  set y : Γ(L, ⊤) := (L.unitHomEquiv s).eval (op ⊤)
  have hxy : x = c • y := hc x y
    (hx.trans (congrArg (fun t' => (L.unitHomEquiv t').eval (op ⊤)) ha)) rfl
  rw [hxy]
  exact zeroScheme_smul_le L c y

end AlgebraicGeometry.RigidifiedPicard

end

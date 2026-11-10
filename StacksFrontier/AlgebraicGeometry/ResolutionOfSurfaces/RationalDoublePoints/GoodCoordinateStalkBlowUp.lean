module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinateInfinity
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartCaseTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartPoint

/-!
# A good coordinate stays good at every singular point of the blowup

Let `A` be the ring of a Situation 0BGC and `x₁` a good coordinate of `A` (the first of
generators `x₁, x₂, x₃` of the maximal ideal with a quadratic relation whose form `q` has
`q(0, t₂, t₃)` not a scalar times a square). This file proves step (A2) of [Stacks, Section 54.12]
on the blowup `X` of `Spec(A)` in its maximal ideal: at every singular point `x` of `X`, the
maximal ideal of `A` generates the ideal of `x₁` in `𝒪_{X,x}`, the residue field at `x` is that
of `A`, and the image of `x₁` is a good coordinate of `𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.RationalDoublePointSituation.isGoodCoordinate_stalk_blowUp`.
* `AlgebraicGeometry.goodCoordinate_chart_conclusion`,
  `AlgebraicGeometry.false_of_chart_infinity_goodCoordinate`: the two chart computations, read in
  a local ring isomorphic to the local ring of the chart.
* `AlgebraicGeometry.exists_blowupChartι_eq_of_span_eq`: moving a point between two standard
  charts of a blowup by [Stacks, Tag 0BFL].

## References

* [Stacks Project, Section 54.12 (Tag 0BGB)](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BFL](https://stacks.math.columbia.edu/tag/0BFL)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AlgebraicGeometry

section Algebra

variable {A : Type u} [CommRing A] [IsLocalRing A] {y : Fin 3 → A}
  {R D C : Type u} [CommRing R] [CommRing D] [CommRing C] [IsLocalRing C] [Algebra R D]

omit [IsLocalRing C] in
/-- The local ring of the chart `A[𝔪/y₁]` at the contraction of a prime of a ring isomorphic to
it, read in a ring isomorphic to the localization at that prime. -/
theorem exists_ringEquiv_localizationAtPrime_chart
    (E : affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0)) ≃+* R)
    (pz : Ideal R) [pz.IsPrime] [IsLocalization.AtPrime D pz] (e : D ≃+* C) :
    ∃ ψ : Localization.AtPrime (Ideal.comap E.toRingHom pz) ≃+* C,
      ∀ c, ψ (algebraMap _ _ c) = e (algebraMap R D (E c)) := by
  have H : (Ideal.comap E.toRingHom pz).primeCompl.map E.toMonoidHom = pz.primeCompl := by
    ext r
    refine ⟨fun ⟨c, hc, h⟩ => h ▸ hc, fun hr => ⟨E.symm r, ?_, by simp⟩⟩
    change E (E.symm r) ∉ pz
    simpa using hr
  refine ⟨(IsLocalization.ringEquivOfRingEquiv _ D E H).trans e, fun c => ?_⟩
  rw [RingEquiv.trans_apply, IsLocalization.ringEquivOfRingEquiv_eq]

/-- The localization of `A[𝔪/y₁]` at the contraction of a maximal ideal `pz`, read in an
isomorphic local ring `C`, is Noetherian of dimension at least two and not regular, and `y₁` lies
in the contraction when it maps into the maximal ideal of `C`. -/
private theorem exists_ringEquiv_localizationAtPrime_chart_of_not_isRegularLocalRing
    (E : affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0)) ≃+* R)
    (pz : Ideal R) [pz.IsMaximal] [IsLocalization.AtPrime D pz] (e : D ≃+* C) (φ : A →+* C)
    (hφ : ∀ b, φ b = e (algebraMap R D (E (algebraMap A _ b))))
    (h0 : φ (y 0) ∈ maximalIdeal C) [IsNoetherianRing C] (hdim : 2 ≤ ringKrullDim C)
    (hsing : ¬ IsRegularLocalRing C) :
    ∃ ψ : Localization.AtPrime (Ideal.comap E.toRingHom pz) ≃+* C,
      (∀ c, ψ (algebraMap _ _ c) = e (algebraMap R D (E c))) ∧
      (Ideal.comap E.toRingHom pz).IsMaximal ∧
      IsNoetherianRing (Localization.AtPrime (Ideal.comap E.toRingHom pz)) ∧
      2 ≤ ringKrullDim (Localization.AtPrime (Ideal.comap E.toRingHom pz)) ∧
      ¬ IsRegularLocalRing (Localization.AtPrime (Ideal.comap E.toRingHom pz)) ∧
      algebraMap A (affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0))) (y 0) ∈
        Ideal.comap E.toRingHom pz := by
  obtain ⟨ψ, hψ⟩ := exists_ringEquiv_localizationAtPrime_chart E pz e
  have : (Ideal.comap E.toRingHom pz).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ E.surjective
  refine ⟨ψ, hψ, this, isNoetherianRing_of_ringEquiv C ψ.symm,
    by rwa [ringKrullDim_eq_of_ringEquiv ψ], fun _ => hsing (IsRegularLocalRing.of_ringEquiv ψ),
    ?_⟩
  by_contra hc
  have hu := IsLocalization.map_units (Localization.AtPrime (Ideal.comap E.toRingHom pz))
    (⟨_, hc⟩ : (Ideal.comap E.toRingHom pz).primeCompl)
  refine (mem_maximalIdeal _).mp h0 ?_
  rw [hφ, ← hψ]
  exact hu.map _

/-- **(A2) at a point of the chart of a good coordinate, read in an isomorphic local ring.** Let
`y₁` be a good coordinate of `A`, `R ≅ A[𝔪/y₁]`, `pz` a maximal ideal of `R`, `D` the localization
of `R` at `pz` and `C ≅ D`, with `φ : A → C` the composite. If `y₁` maps into the maximal ideal
of `C` and `C` is a Noetherian local ring of dimension at least two which is not regular, then
`𝔪C = (φ y₁)`, the residue field of `C` is that of `A`, and `φ y₁` is a good coordinate of `C`. -/
theorem goodCoordinate_chart_conclusion [IsNoetherianRing A]
    (hspan : Ideal.span (Set.range y) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (y p * y q) ∈ maximalIdeal A ^ 3)
    (hgood : IsGoodCoordinateForm fun p q => residue A (a p q))
    (E : affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0)) ≃+* R)
    (pz : Ideal R) [pz.IsMaximal] [IsLocalization.AtPrime D pz] (e : D ≃+* C) (φ : A →+* C)
    (hφ : ∀ b, φ b = e (algebraMap R D (E (algebraMap A _ b))))
    (h0 : φ (y 0) ∈ maximalIdeal C) [IsNoetherianRing C] (hdim : 2 ≤ ringKrullDim C)
    (hsing : ¬ IsRegularLocalRing C) :
    Ideal.map φ (maximalIdeal A) = Ideal.span {φ (y 0)} ∧
      Function.Surjective ((residue C).comp φ) ∧ IsFirstGeneratorOfGoodRelation C (φ (y 0)) := by
  have hy : ∀ i, y i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨ψ, hψ, hzmax, hnoeth, hdim', hsing', h0'⟩ :=
    exists_ringEquiv_localizationAtPrime_chart_of_not_isRegularLocalRing E pz e φ hφ h0 hdim hsing
  set z := Ideal.comap E.toRingHom pz
  have hφ' : φ = (ψ : Localization.AtPrime z →+* C).comp
      ((algebraMap (affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0)))
        (Localization.AtPrime z)).comp
        (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0))))) :=
    RingHom.ext fun b => by
      rw [hφ b, RingHom.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom, hψ]
  obtain ⟨b, hb⟩ := exists_cubicExpansion_of_mem_pow_three hspan hrel
  obtain ⟨hsurj, hgc⟩ := surjective_and_isGoodCoordinate_of_chart (Localization.Away (y 0)) hspan
    a b hupper (exists_notMem_maximalIdeal_of_isGoodCoordinateForm (a := a) hupper hgood) hb hgood
    z h0' hdim' hsing'
  have : IsLocalHom (ψ : Localization.AtPrime z →+* C) := IsLocalHom.of_surjective _ ψ.surjective
  refine ⟨?_, fun t => ?_, ?_⟩
  · rw [hφ', ← Ideal.map_map, ← Ideal.map_map,
      affineBlowupAlgebra.map_ideal_eq_span_singleton (maximalIdeal A) (y 0) (hy 0),
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    rfl
  · obtain ⟨s, hs⟩ := (ResidueField.mapEquiv ψ).surjective t
    obtain ⟨r, hr⟩ := hsurj s
    refine ⟨r, ?_⟩
    rw [RingHom.comp_apply, hφ', RingHom.comp_apply, residue_map_apply, ← hs]
    exact congrArg _ hr
  · rw [hφ']
    exact IsFirstGeneratorOfGoodRelation.map (ψ : Localization.AtPrime z →+* C)
      (IsLocalRing.map_ringEquiv_maximalIdeal ψ) (ResidueField.mapEquiv ψ).bijective hgc

/-- **No singular point of the blowup on the hyperplane of a good coordinate, in a chart read
in an isomorphic local ring.** Let `x₁` be a good coordinate of `A`, `σ` the transposition
`1 ↔ k+1` and `y = x ∘ σ`, so that `y₁ = x_{k+1}` and `y_{k+1} = x₁`. In the chart `A[𝔪/y₁]`, a
point at which `y₁` vanishes and the fraction `x₁ / x_{k+1}` vanishes is a regular point (if its
local ring has dimension at least two). -/
theorem false_of_chart_infinity_goodCoordinate [IsNoetherianRing A] {x : Fin 3 → A}
    (_hspanx : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) ∈ maximalIdeal A ^ 3)
    (hgood : IsGoodCoordinateForm fun p q => residue A (a p q)) (k : Fin 2)
    (hyx : ∀ p, y p = x (Equiv.swap 0 k.succ p))
    (hspan : Ideal.span (Set.range y) = maximalIdeal A)
    (E : affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0)) ≃+* R)
    (pz : Ideal R) [pz.IsMaximal] [IsLocalization.AtPrime D pz] (e : D ≃+* C) (φ : A →+* C)
    (hφ : ∀ b, φ b = e (algebraMap R D (E (algebraMap A _ b))))
    (h0 : φ (y 0) ∈ maximalIdeal C)
    (hk : E (chartFraction (Localization.Away (y 0))
      (fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩) k.succ) ∈ pz)
    [IsNoetherianRing C] (hdim : 2 ≤ ringKrullDim C) (hsing : ¬ IsRegularLocalRing C) :
    False := by
  obtain ⟨ψ, hψ, hzmax, hnoeth, hdim', hsing', h0'⟩ :=
    exists_ringEquiv_localizationAtPrime_chart_of_not_isRegularLocalRing E pz e φ hφ h0 hdim hsing
  set z := Ideal.comap E.toRingHom pz
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 k.succ
  obtain ⟨hupper', hunit', hrel', hcase'⟩ := exists_permuted_caseOne_relation
    (exists_notMem_maximalIdeal_of_isGoodCoordinateForm (a := a) hupper hgood) hupper hrel
    hgood.not_isScalarSqLinear σ
  have hrel'' : ∑ p, ∑ q, permuteRelation a σ p q * (y p * y q) ∈ maximalIdeal A ^ 3 := by
    simpa only [hyx] using hrel'
  obtain ⟨c, hck, h1, h2, h3⟩ := exists_rational_point_of_chart_not_isRegularLocalRing
    (Localization.Away (y 0)) hspan (permuteRelation a σ) hupper' hunit' hrel'' hcase' z h0' k hk
    hdim' hsing'
  simp only [permuteRelation_map] at h1 h2 h3
  exact not_exists_singular_point_at_infinity (fun p q => residue A (a p q))
    (fun p q h => by simp only [hupper p q h, map_zero]) hgood k ⟨c, hck, h1, h2, h3⟩

omit [IsLocalRing C] in
/-- Where the fraction `y_{k+1}/y₁` of the chart `A[𝔪/y₁]` does not vanish, `y₁` and `y_{k+1}`
generate the same ideal of the local ring, read in an isomorphic ring. -/
theorem span_singleton_eq_of_chartFraction_notMem
    (hspan : Ideal.span (Set.range y) = maximalIdeal A) (k : Fin 3)
    (E : affineBlowupAlgebra (maximalIdeal A) (y 0) (Localization.Away (y 0)) ≃+* R)
    (pz : Ideal R) [pz.IsPrime] [IsLocalization.AtPrime D pz] (e : D ≃+* C) (φ : A →+* C)
    (hφ : ∀ b, φ b = e (algebraMap R D (E (algebraMap A _ b))))
    (hf : E (chartFraction (Localization.Away (y 0))
      (fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩) k) ∉ pz) :
    Ideal.span {φ (y 0)} = Ideal.span {φ (y k)} := by
  have hunit : IsUnit (e (algebraMap R D (E (chartFraction (Localization.Away (y 0))
      (fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩) k)))) :=
    (IsLocalization.map_units D (⟨_, hf⟩ : pz.primeCompl)).map e
  have hym : ∀ i, y i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hfr := algebraMap_mul_chartFraction (Localization.Away (y 0)) hym k
  rw [hφ (y k), ← hfr, map_mul E, map_mul (algebraMap R D), map_mul e, ← hφ,
    Ideal.span_singleton_mul_right_unit hunit]

end Algebra

section BlowUp

open CategoryTheory TopologicalSpace

/-- A point of a standard chart of a blowup whose image is a closed point is a maximal ideal of
the chart ring. -/
theorem isMaximal_of_isClosed_singleton_blowupChartι {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : I.ideal U) (z : Spec (.of (blowupChartRing I U a)))
    (hz : IsClosed ({blowupChartι I U a z} : Set (blowUp I))) : z.asIdeal.IsMaximal := by
  refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp ?_
  have hset : ({z} : Set _) = (blowupChartι I U a).base ⁻¹' {blowupChartι I U a z} := by
    ext t
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => (blowupChartι I U a).isOpenEmbedding.injective h⟩
  exact hset ▸ hz.preimage (blowupChartι I U a).continuous

/-- **The local ring of the blowup of `Spec(A)` at a point of the standard chart at `b`, as a
localization of `A[𝔪/b]`.** In continuation-passing form: the chart ring is isomorphic to the
affine blowup algebra `A[𝔪/b]`, the stalk of `Spec` of the chart ring is its localization at the
point, it is isomorphic to the stalk of the blowup, and under these identifications
`AlgebraicGeometry.blowUpStalkHom` is the structure map. -/
theorem blowupChart_stalk_cps (A : Type u) [CommRing A] [IsLocalRing A] (b : A)
    (a : (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩)
    (ha : (a : Γ(Spec (.of A), ⊤)) = (Scheme.ΓSpecIso (.of A)).inv.hom b)
    (z : Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ a)))
    [z.asIdeal.IsPrime] {P : Prop}
    (h : ∀ (E : affineBlowupAlgebra (maximalIdeal A) b (Localization.Away b) ≃+*
          blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ a)
        (D : Type u) [CommRing D]
        [Algebra (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ a) D]
        [IsLocalization.AtPrime D z.asIdeal]
        (e : D ≃+* (blowUp (maximalIdealSheaf A)).presheaf.stalk
          (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ a z)),
        (∀ c, blowUpStalkHom A (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ a z) c =
          e (algebraMap _ D (E (algebraMap A _ c)))) → P) : P := by
  obtain ⟨E, hE⟩ := exists_ringEquiv_blowupChartRing_ofIdealTop A (maximalIdeal A) b a ha
  let : Algebra (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ a)
      ((Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
        a))).presheaf.stalk z) := StructureSheaf.stalkAlgebra _ z
  have : IsLocalization.AtPrime ((Spec (.of (blowupChartRing (maximalIdealSheaf A)
      ⟨⊤, isAffineOpen_top _⟩ a))).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk _ z
  have hkey := germ_comp_stalkMap_blowupChartι (I := maximalIdealSheaf A)
    (U := ⟨⊤, isAffineOpen_top _⟩) (a := a) z (TopologicalSpace.Opens.mem_top _)
  have h1 := stalkHomOfSpec_comp_stalkMap (blowUpToBase (maximalIdealSheaf A)) _ z _ hkey
  refine h E _ (asIso ((blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
    a).stalkMap z)).symm.commRingCatIsoToRingEquiv fun c => ?_
  refine Eq.trans ?_ (congrArg (fun r => (asIso ((blowupChartι (maximalIdealSheaf A)
    ⟨⊤, isAffineOpen_top _⟩ a).stalkMap z)).symm.commRingCatIsoToRingEquiv
      (algebraMap _ _ r)) (hE c)).symm
  exact ((asIso ((blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
    a).stalkMap z)).symm.commRingCatIsoToRingEquiv.symm_apply_eq).mp (h1 c)

/-- **Moving a point of a blowup between two standard charts, by [Stacks, Tag 0BFL].** If at a
point of the standard chart at `b` the germs of `a` and `b` generate the same ideal of the local
ring, then the point also lies in the standard chart at `a`. -/
theorem exists_blowupChartι_eq_of_span_eq {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a b : I.ideal U) (z : Spec (.of (blowupChartRing I U b)))
    (hU : blowUpToBase I (blowupChartι I U b z) ∈ U.1)
    (h : Ideal.span
        {((blowUpToBase I).stalkMap (blowupChartι I U b z))
          (X.presheaf.germ U.1 _ hU (b : Γ(X, U.1)))} =
      Ideal.span
        {((blowUpToBase I).stalkMap (blowupChartι I U b z))
          (X.presheaf.germ U.1 _ hU (a : Γ(X, U.1)))}) :
    ∃ z0 : Spec (.of (blowupChartRing I U a)), blowupChartι I U a z0 = blowupChartι I U b z := by
  have hb := (mem_affineBlowupStandardOpen_iff_exceptionalIdeal_stalk_eq_span I U b
    (blowupChartι I U b z) hU).mp (blowupChartι_mem_range_relativeProjChart z)
  obtain ⟨p, hp⟩ := (mem_affineBlowupStandardOpen_iff_exceptionalIdeal_stalk_eq_span I U a
    (blowupChartι I U b z) hU).mpr (hb.trans h)
  refine ⟨(affineBlowupStandardOpenIso I U a).inv p, ?_⟩
  have hcomp : (affineBlowupStandardOpenIso I U a).inv ≫ blowupChartι I U a =
      (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1).ι ≫ Stacks.RelativeProj.Situation.relativeProjChart
          (reesSituation I) U := by
    rw [blowupChartι, Iso.inv_hom_id_assoc]
  refine Eq.trans (Scheme.Hom.comp_apply _ _ _).symm ?_
  rwa [hcomp]

/-- `AlgebraicGeometry.stalkHomOfSpec` at an element of an ideal of the global sections, in the
form in which [Stacks, Tag 0BFL] states the generator of the exceptional ideal. -/
theorem stalkHomOfSpec_eq_stalkMap_germ {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (x : X) (J : Ideal Γ(Spec (.of A), ⊤)) {b : A}
    (hb : (Scheme.ΓSpecIso (.of A)).inv.hom b ∈ J)
    (hx : f x ∈ ((⟨⊤, isAffineOpen_top _⟩ : (Spec (.of A)).affineOpens) : (Spec (.of A)).Opens)) :
    stalkHomOfSpec f x b = (f.stalkMap x) ((Spec (.of A)).presheaf.germ
      ((⟨⊤, isAffineOpen_top _⟩ : (Spec (.of A)).affineOpens) : (Spec (.of A)).Opens) (f x) hx
        ((⟨_, hb⟩ : J) : Γ(Spec (.of A), ⊤))) :=
  (stalkHomOfSpec_apply f x b).trans rfl

/-- `AlgebraicGeometry.exists_blowupChartι_eq_of_span_eq` for the blowup of `Spec(A)` in its
maximal ideal, with the germs read through `AlgebraicGeometry.blowUpStalkHom`. -/
theorem exists_blowupChartι_eq_of_span_blowUpStalkHom_eq (A : Type u) [CommRing A]
    [IsLocalRing A] {a b : A}
    (ha : (Scheme.ΓSpecIso (.of A)).inv.hom a ∈ (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hb : (Scheme.ΓSpecIso (.of A)).inv.hom b ∈ (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩)
    (z : Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hb⟩)))
    (h : Ideal.span
        {blowUpStalkHom A (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
          ⟨_, hb⟩ z) b} =
      Ideal.span
        {blowUpStalkHom A (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
          ⟨_, hb⟩ z) a}) :
    ∃ z0 : Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, ha⟩)),
      blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, ha⟩ z0 =
        blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hb⟩ z := by
  refine exists_blowupChartι_eq_of_span_eq _ _ ⟨_, ha⟩ ⟨_, hb⟩ z
    (TopologicalSpace.Opens.mem_top _) ?_
  have e1 := stalkHomOfSpec_eq_stalkMap_germ (blowUpToBase (maximalIdealSheaf A))
    (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hb⟩ z) _ hb
    (TopologicalSpace.Opens.mem_top _)
  have e2 := stalkHomOfSpec_eq_stalkMap_germ (blowUpToBase (maximalIdealSheaf A))
    (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hb⟩ z) _ ha
    (TopologicalSpace.Opens.mem_top _)
  exact (congrArg (fun t => Ideal.span {t}) e1).symm.trans
    (h.trans (congrArg (fun t => Ideal.span {t}) e2))

/-- **A singular point of the blowup in the chart of another generator lies in the chart of the
good coordinate.** Let `x₁` be a good coordinate of `A` with generators `x₁, x₂, x₃`, and let `w`
be a point of the chart at `x_{k+1}`, closed, over the closed point, whose local ring is a
Noetherian local ring of dimension at least two which is not regular. Then `w` lies in the chart
at `x₁`. -/
theorem exists_chartZero_preimage_of_chart_succ (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {g : Fin 3 → A} (hspan : Ideal.span (Set.range g) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (hupper : ∀ p q, q < p → a p q = 0)
    (hrel : ∑ p, ∑ q, a p q * (g p * g q) ∈ maximalIdeal A ^ 3)
    (hgood : IsGoodCoordinateForm fun p q => residue A (a p q)) (k : Fin 2)
    (hg' : ∀ i, (Scheme.ΓSpecIso (.of A)).inv.hom (g i) ∈
      (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩)
    (z : Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
      ⟨_, hg' k.succ⟩))) [z.asIdeal.IsMaximal]
    [IsLocalHom (blowUpStalkHom A (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
      ⟨_, hg' k.succ⟩ z))]
    [IsNoetherianRing ((blowUp (maximalIdealSheaf A)).presheaf.stalk
      (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg' k.succ⟩ z))]
    (hdim : 2 ≤ ringKrullDim ((blowUp (maximalIdealSheaf A)).presheaf.stalk
      (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg' k.succ⟩ z)))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf A)).presheaf.stalk
      (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg' k.succ⟩ z))) :
    ∃ z0 : Spec (.of (blowupChartRing (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
        ⟨_, hg' 0⟩)),
      blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg' 0⟩ z0 =
        blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg' k.succ⟩ z := by
  obtain ⟨y, hyx⟩ : ∃ y : Fin 3 → A, ∀ p, y p = g (Equiv.swap 0 k.succ p) :=
    ⟨fun p => g (Equiv.swap 0 k.succ p), fun _ => rfl⟩
  have hy0 : y 0 = g k.succ := by rw [hyx, Equiv.swap_apply_left]
  have hyk : y k.succ = g 0 := by rw [hyx, Equiv.swap_apply_right]
  have hspany : Ideal.span (Set.range y) = maximalIdeal A := by
    rw [show y = g ∘ Equiv.swap 0 k.succ from funext hyx, Set.range_comp, Equiv.range_eq_univ,
      Set.image_univ, hspan]
  have ha : ((⟨_, hg' k.succ⟩ : (maximalIdealSheaf A).ideal ⟨⊤, isAffineOpen_top _⟩) :
      Γ(Spec (.of A), ⊤)) = (Scheme.ΓSpecIso (.of A)).inv.hom (y 0) := by
    rw [hy0]
  refine blowupChart_stalk_cps A (y 0) ⟨_, hg' k.succ⟩ ha z fun E D _ _ _ e hφ => ?_
  have h0y : blowUpStalkHom A (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩
      ⟨_, hg' k.succ⟩ z) (y 0) ∈ maximalIdeal ((blowUp (maximalIdealSheaf A)).presheaf.stalk
        (blowupChartι (maximalIdealSheaf A) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hg' k.succ⟩ z)) :=
    map_nonunit _ _ (hspany ▸ Ideal.subset_span ⟨0, rfl⟩)
  by_cases hf : E (chartFraction (Localization.Away (y 0))
      (fun i => hspany ▸ Ideal.subset_span ⟨i, rfl⟩) k.succ) ∈ z.asIdeal
  · exact (false_of_chart_infinity_goodCoordinate hspan a hupper hrel hgood k hyx hspany E
      z.asIdeal e _ hφ h0y hf hdim hx).elim
  refine exists_blowupChartι_eq_of_span_blowUpStalkHom_eq A (hg' 0) (hg' k.succ) z ?_
  simpa only [hy0, hyk] using
    span_singleton_eq_of_chartFraction_notMem hspany k.succ E z.asIdeal e _ hφ hf

/-- **(A2) of [Stacks, Section 54.12], on the scheme.** Let `A` be the ring of a Situation 0BGC
and `e` a good coordinate of `A`. At every singular point `x` of the blowup of `Spec(A)` in its
maximal ideal, the maximal ideal of `A` generates the ideal of `e` in `𝒪_{X, x}`, the residue
field at `x` is that of `A`, and the image of `e` is a good coordinate of `𝒪_{X, x}`. -/
theorem RationalDoublePointSituation.isGoodCoordinate_stalk_blowUp
    (S : RationalDoublePointSituation.{u}) {e : S.A}
    (he : IsFirstGeneratorOfGoodRelation S.A e) (x : blowUp (maximalIdealSheaf S.A))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    Ideal.map (blowUpStalkHom S.A x) (IsLocalRing.maximalIdeal S.A) =
        Ideal.span {blowUpStalkHom S.A x e} ∧
      Function.Surjective ((IsLocalRing.residue
        ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)).comp (blowUpStalkHom S.A x)) ∧
      IsFirstGeneratorOfGoodRelation ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
        (blowUpStalkHom S.A x e) := by
  obtain ⟨g, a, rfl, hspan, hupper, hrel, hgood⟩ := he
  have hgm : ∀ k, g k ∈ IsLocalRing.maximalIdeal S.A := fun k => hspan ▸ Ideal.subset_span ⟨k, rfl⟩
  have hover := S.blowUpToBase_eq_closedPoint_of_mem_singularLocus x hx
  have hclosed := S.isClosed_singleton_of_mem_singularLocus_blowUp x hx
  have : IsLocalHom (blowUpStalkHom S.A x) :=
    isLocalHom_germ_appTop (blowUpToBase (maximalIdealSheaf S.A)) x hover
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf S.A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf S.A))
  have hdim : 2 ≤ ringKrullDim ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
    (S.ringKrullDim_stalk_blowUp_eq_two x hclosed).ge
  have h0 : ∀ k, blowUpStalkHom S.A x (g k) ∈
      IsLocalRing.maximalIdeal ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) :=
    fun k => map_nonunit _ _ (hgm k)
  set g' : Fin 3 → Γ(Spec (.of S.A), ⊤) := fun k => (Scheme.ΓSpecIso (.of S.A)).inv.hom (g k)
  have hg' : ∀ k, g' k ∈ (maximalIdealSheaf S.A).ideal ⟨⊤, isAffineOpen_top _⟩ := fun k =>
    mem_ideal_ofIdealTop_isAffineOpen_top S.A (IsLocalRing.maximalIdeal S.A) (hgm k)
  have hspan' : (maximalIdealSheaf S.A).ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      Ideal.span (Set.range g') := by
    rw [ideal_top_maximalIdealSheaf, ← hspan, Ideal.map_span, ← Set.range_comp]
    rfl
  have key0 : ∀ z0 : Spec (.of (blowupChartRing (maximalIdealSheaf S.A) ⟨⊤, isAffineOpen_top _⟩
      ⟨g' 0, hg' 0⟩)), blowupChartι (maximalIdealSheaf S.A) ⟨⊤, isAffineOpen_top _⟩
        ⟨g' 0, hg' 0⟩ z0 = x →
      Ideal.map (blowUpStalkHom S.A x) (IsLocalRing.maximalIdeal S.A) =
          Ideal.span {blowUpStalkHom S.A x (g 0)} ∧
        Function.Surjective ((IsLocalRing.residue
          ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)).comp (blowUpStalkHom S.A x)) ∧
        IsFirstGeneratorOfGoodRelation ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)
          (blowUpStalkHom S.A x (g 0)) := by
    rintro z0 rfl
    have := isMaximal_of_isClosed_singleton_blowupChartι _ _ _ z0 hclosed
    exact blowupChart_stalk_cps S.A (g 0) ⟨g' 0, hg' 0⟩ rfl z0 fun E D _ _ _ e hφ =>
      goodCoordinate_chart_conclusion hspan a hupper hrel hgood E z0.asIdeal e _ hφ (h0 0) hdim hx
  obtain ⟨j, z, hz⟩ := exists_mem_range_blowupChartι (I := maximalIdealSheaf S.A)
    (U := ⟨⊤, isAffineOpen_top _⟩) g' hg' hspan' x (TopologicalSpace.Opens.mem_top _)
  by_cases hj : j = 0
  · subst hj
    exact key0 z hz
  obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.mpr hj
  have hcl : IsClosed
      ({blowupChartι (maximalIdealSheaf S.A) ⟨⊤, isAffineOpen_top _⟩
          ⟨g' k.succ, hg' k.succ⟩ z} : Set (blowUp (maximalIdealSheaf S.A))) := hz ▸ hclosed
  have := isMaximal_of_isClosed_singleton_blowupChartι _ _ _ z hcl
  have : IsLocalHom (blowUpStalkHom S.A (blowupChartι (maximalIdealSheaf S.A)
      ⟨⊤, isAffineOpen_top _⟩ ⟨g' k.succ, hg' k.succ⟩ z)) :=
    isLocalHom_germ_appTop (blowUpToBase (maximalIdealSheaf S.A)) _ (hz ▸ hover)
  have hdim' : 2 ≤ ringKrullDim ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk
      (blowupChartι (maximalIdealSheaf S.A) ⟨⊤, isAffineOpen_top _⟩ ⟨g' k.succ, hg' k.succ⟩ z)) :=
    hz ▸ hdim
  have hx' : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk
      (blowupChartι (maximalIdealSheaf S.A) ⟨⊤, isAffineOpen_top _⟩ ⟨g' k.succ, hg' k.succ⟩ z)) :=
    hz ▸ hx
  obtain ⟨z0, hz0⟩ := exists_chartZero_preimage_of_chart_succ S.A hspan a hupper hrel hgood k hg'
    z hdim' hx'
  exact key0 z0 (hz0.trans hz)

end BlowUp

end AlgebraicGeometry

end

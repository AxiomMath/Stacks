module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.ZetaFunction.PointDivisorClass

/-!
# The Kummer class of a section of a smooth proper family of curves

Let `p : Y ⟶ Spec R` be a separated smooth morphism of relative dimension one with a section `σ`,
`D = ker σ` the effective Cartier divisor it cuts out, `ℓ` invertible in `R`, and
`Z = Y ×_{Spec R} Spec Ω` the fibre over a geometric point `t : Spec Ω ⟶ Spec R`, with
`h : Z ⟶ Y`. The base change `σ_t` of `σ` is a rational point of `Z`, the inverse image of `D` in
`Z` is the divisor of `σ_t`, and the class of `𝒪_Y(D)` pulls back to a class of degree one on `Z`.
Hence the Kummer coboundary `c ∈ H²(Y, μ_ℓ)` of the class of `𝒪_Y(D)` restricts on `Z` to a class
of trace one: `tr_Z(h^* c) = 1`
(`Stacks.EtaleCohomology.CurveFamily.smoothProperCurveTrace_pullback_kummerClass`).

## Main definitions

* `Stacks.EtaleCohomology.CurveFamily.sectionBaseChange`: `σ_t : Spec Ω ⟶ Z`.
* `Stacks.EtaleCohomology.CurveFamily.kummerClass`: the Kummer coboundary of `[𝒪_Y(D)]`.

## Main results

* `Stacks.EtaleCohomology.CurveFamily.comap_ker_section`: `h⁻¹(ker σ) = ker σ_t`.
* `Stacks.EtaleCohomology.CurveFamily.picardDegree_schemePullbackClass_picardClass_ker`:
  `deg h^*[𝒪_Y(D)] = 1`.
* `Stacks.EtaleCohomology.CurveFamily.smoothProperCurveTrace_pullback_kummerClass`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.CurveFamily

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R)) [IsSeparated p]
  (σ : Spec (.of R) ⟶ Y) (hσ : σ ≫ p = 𝟙 _)
  {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
  {Z : Scheme.{u}} {h : Z ⟶ Y} {pZ : Z ⟶ Spec (.of Ω)} (sq : IsPullback h pZ p t)

include hσ in
/-- A section of a separated morphism is a closed immersion. -/
theorem isClosedImmersion_section : IsClosedImmersion σ := by
  have : IsClosedImmersion (σ ≫ p) := by rw [hσ]; infer_instance
  exact IsClosedImmersion.of_comp σ p

/-- **The base change of the section** to the fibre over `t`. -/
def sectionBaseChange : Spec (.of Ω) ⟶ Z :=
  sq.lift (t ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

omit [IsSeparated p] in
/-- The base-changed section followed by `h : Z ⟶ Y` is `t ≫ σ`. -/
@[reassoc (attr := simp)]
theorem sectionBaseChange_h : sectionBaseChange p σ hσ t sq ≫ h = t ≫ σ :=
  sq.lift_fst _ _ _

omit [IsSeparated p] in
/-- The base-changed section is a section of `pZ : Z ⟶ Spec Ω`. -/
@[reassoc (attr := simp)]
theorem sectionBaseChange_pZ : sectionBaseChange p σ hσ t sq ≫ pZ = 𝟙 _ :=
  sq.lift_snd _ _ _

omit [IsSeparated p] in
/-- The base change of the section is the inverse image of the section. -/
theorem isPullback_sectionBaseChange :
    IsPullback (sectionBaseChange p σ hσ t sq) t h σ := by
  have outer : IsPullback t (sectionBaseChange p σ hσ t sq ≫ pZ) (σ ≫ p) t := by
    rw [sectionBaseChange_pZ, hσ]
    exact IsPullback.id_vert t
  exact (IsPullback.of_bot outer (sectionBaseChange_h p σ hσ t sq).symm sq).flip

include hσ in
/-- **The inverse image of the divisor of the section is the divisor of the base-changed
section.** -/
theorem comap_ker_section : σ.ker.comap h = (sectionBaseChange p σ hσ t sq).ker := by
  have := isClosedImmersion_section p σ hσ
  have hpb := isPullback_sectionBaseChange p σ hσ t sq
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom, hpb.isoPullback_hom_fst]

/-- The divisor of the base-changed section maps isomorphically to `Spec Ω`. -/
theorem isIso_subschemeι_ker_sectionBaseChange :
    IsIso ((sectionBaseChange p σ hσ t sq).ker.subschemeι ≫ pZ) := by
  have : IsSeparated pZ := MorphismProperty.of_isPullback sq inferInstance
  have : IsClosedImmersion (sectionBaseChange p σ hσ t sq) :=
    isClosedImmersion_section pZ _ (sectionBaseChange_pZ p σ hσ t sq)
  have h1 : (sectionBaseChange p σ hσ t sq).toImage ≫
      ((sectionBaseChange p σ hσ t sq).ker.subschemeι ≫ pZ) = 𝟙 _ := by
    rw [← Category.assoc]
    change ((sectionBaseChange p σ hσ t sq).toImage ≫ (sectionBaseChange p σ hσ t sq).imageι) ≫
      pZ = _
    rw [Scheme.Hom.toImage_imageι, sectionBaseChange_pZ]
  have : IsIso ((sectionBaseChange p σ hσ t sq).toImage ≫
      ((sectionBaseChange p σ hσ t sq).ker.subschemeι ≫ pZ)) := by
    rw [h1]
    infer_instance
  exact IsIso.of_isIso_comp_left (sectionBaseChange p σ hσ t sq).toImage _

/-- **A divisor isomorphic to its base point has degree one.** On a proper scheme of dimension at
most one over a field `Ω`, an effective Cartier divisor `E` with `E ⟶ Spec Ω` an isomorphism has
degree one. -/
theorem picardDegree_picardClass_eq_one_of_isIso [IsProper pZ]
    (hdim : topologicalKrullDim Z ≤ 1) (E : Z.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor E] (hE : IsIso (E.subschemeι ≫ pZ)) :
    Stacks.Picard.picardDegree pZ hdim (Stacks.Divisors.picardClass E) = 1 := by
  have hdeg := Stacks.Picard.picardDegree_divisorPicardClass pZ hdim E
  let : Algebra Ω Γ(E.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (E.subschemeι ≫ pZ).appTop).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap Ω Γ(E.subscheme, ⊤)) := by
    have := hE
    have : IsIso (E.subschemeι ≫ pZ).appTop :=
      (inferInstance : IsIso (Scheme.Γ.map (E.subschemeι ≫ pZ).op))
    exact ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of Ω)).inv ≫ (E.subschemeι ≫ pZ).appTop)
  have h1 : Module.finrank Ω Γ(E.subscheme, ⊤) = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap Ω Γ(E.subscheme, ⊤)) hbij).finrank_eq,
      Module.finrank_self]
  rw [hdeg, h1, Nat.cast_one]

variable [SmoothOfRelativeDimension 1 p]

include hσ sq in
/-- The divisor of a section of a separated smooth relative curve pulls back to an effective
Cartier divisor on every fibre. -/
theorem isPullbackDefined_ker_section : Stacks.Divisors.IsPullbackDefined h σ.ker := by
  have : IsSeparated pZ := MorphismProperty.of_isPullback sq inferInstance
  have : SmoothOfRelativeDimension 1 pZ :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    MorphismProperty.of_isPullback sq inferInstance
  change Stacks.Divisors.IsEffectiveCartierDivisor _
  rw [comap_ker_section p σ hσ t sq]
  exact Stacks.Hilbert.isEffectiveCartierDivisor_ker_section _ (sectionBaseChange_pZ p σ hσ t sq)

include hσ sq in
/-- **The class of `𝒪_Y(D)` pulls back to a class of degree one on the fibre.** -/
theorem picardDegree_schemePullbackClass_picardClass_ker [IsProper pZ]
    (hdim : topologicalKrullDim Z ≤ 1) :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker :=
      Stacks.Hilbert.isEffectiveCartierDivisor_ker_section σ hσ
    Stacks.Picard.picardDegree pZ hdim
      (Stacks.Picard.schemePullbackClass h (Stacks.Divisors.picardClass σ.ker)) = 1 := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker :=
    Stacks.Hilbert.isEffectiveCartierDivisor_ker_section σ hσ
  have hpb := isPullbackDefined_ker_section p σ hσ t sq
  rw [Stacks.Zeta.schemePullbackClass_picardClass_comap h σ.ker hpb]
  have : Stacks.Divisors.IsEffectiveCartierDivisor (σ.ker.comap h) := hpb
  refine picardDegree_picardClass_eq_one_of_isIso hdim _ ?_
  rw [comap_ker_section p σ hσ t sq]
  exact isIso_subschemeι_ker_sectionBaseChange p σ hσ t sq

/-! ### The Kummer class -/

attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {ℓ : ℕ} (hℓ0 : ℓ ≠ 0) (hℓ : IsUnit (ℓ : R))

omit [IsSeparated p] [SmoothOfRelativeDimension 1 p] in
include p hℓ in
/-- An integer invertible in `R` is invertible on every scheme over `R`. -/
theorem isUnit_natCast_appTop_of_isUnit : IsUnit ((ℓ : ℕ) : Γ(Y, ⊤)) := by
  have := hℓ.map ((Scheme.ΓSpecIso (.of R)).inv ≫ p.appTop).hom
  rwa [map_natCast] at this

variable [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- **The Kummer coboundary of the divisor of the section**:
`δ[𝒪_Y(D)] ∈ H²(Y, μ_ℓ)`, `D = ker σ`. -/
def kummerClass : Sheaf.H.{u + 1, u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} Y ℓ) 2 :=
  Stacks.Kummer.kummerδ.{u + 1, u, u + 1} Y hℓ0 (isUnit_natCast_appTop_of_isUnit p hℓ) 1
    ((Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} Y).symm
      (@Stacks.Divisors.picardClass _ σ.ker
        (Stacks.Hilbert.isEffectiveCartierDivisor_ker_section σ hσ)))

variable [IsAlgClosed Ω] [IsCurve Ω pZ] [Smooth pZ] [IsProper pZ]
  [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})]

include sq in
/-- **The Kummer class of the section restricts to a class of trace one on every geometric
fibre**: `tr_Z(h^* δ[𝒪_Y(D)]) = 1`. -/
theorem smoothProperCurveTrace_pullback_kummerClass (hℓΩ : IsUnit (ℓ : Ω)) :
    Stacks.Kummer.smoothProperCurveTrace pZ hℓΩ
      (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} h ℓ 2
        (kummerClass p σ hσ hℓ0 hℓ)) = 1 := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor σ.ker :=
    Stacks.Hilbert.isEffectiveCartierDivisor_ker_section σ hσ
  set x := (Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard.{u + 1, u + 1, u} Y).symm
      (Stacks.Divisors.picardClass σ.ker)
  have hsq := Stacks.Kummer.etaleCohomologyRestrictionMap_kummerExtClass.{u, u + 1, u + 1} h
    hℓ0 (isUnit_natCast_appTop_of_isUnit p hℓ) 1 2 rfl x
  have hk : kummerClass p σ hσ hℓ0 hℓ = Stacks.Kummer.kummerδ.{u + 1, u, u + 1} Y hℓ0
      (isUnit_natCast_appTop_of_isUnit p hℓ) 1 x := rfl
  rw [hk]
  have h1 : Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, u + 1, u + 1} h ℓ 2
      (Stacks.Kummer.kummerδ.{u + 1, u, u + 1} Y hℓ0
        (isUnit_natCast_appTop_of_isUnit p hℓ) 1 x) =
      Stacks.Kummer.kummerδ.{u + 1, u, u + 1} Z hℓ0
        (Stacks.Kummer.isUnit_globalSections pZ hℓΩ) 1
        (Sheaf.H.map (Stacks.Kummer.multiplicativeInverseImageComparison.{u, u + 1} h) 1
          (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, u + 1, u + 1} h _ 1 x)) :=
    hsq
  rw [h1, Stacks.Kummer.smoothProperCurveTrace_kummerδ,
    Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard_naturality, AddEquiv.apply_symm_apply]
  have := picardDegree_schemePullbackClass_picardClass_ker p σ hσ t sq
    (IsCurve.topologicalKrullDim_eq_one (f := pZ)).le
  change ((Stacks.Picard.picardDegree pZ _
    (Stacks.Picard.schemePullbackClass h (Stacks.Divisors.picardClass σ.ker)) : ℤ) : ZMod ℓ) = 1
  rw [this, Int.cast_one]

end Stacks.EtaleCohomology.CurveFamily

end

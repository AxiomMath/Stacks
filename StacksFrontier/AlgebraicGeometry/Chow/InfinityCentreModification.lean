module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBlowup
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Graph

/-!
# The blowup at infinity as a modification of `X ×_S 𝐏¹_S`

Let `f : X ⟶ S` be a morphism of schemes and `Z ⊆ X` the closed subscheme of a quasi-coherent ideal
sheaf `ℐ`. The blowup `W ⟶ 𝐏¹_X` of `𝐏¹_X` in `∞(Z)` is a morphism to `𝐏¹_X`, while the class at
infinity of Stacks 0F9J is attached to morphisms `W ⟶ X ×_S 𝐏¹_S`. The two targets are identified
by the cartesian square `𝐏¹_X = X ×_S 𝐏¹_S`, and the blowup at infinity is read through that
identification as a morphism `b : W ⟶ X ×_S 𝐏¹_S`.

## Main definitions

* `Stacks.Chow.blowupAtInfinityToProjectiveLineProduct` — the blowup at infinity as a morphism
  `b : W ⟶ X ×_S 𝐏¹_S`.
* `Stacks.Chow.modificationFibreAtInfinityIso` — the fibre at infinity `W ×_{X ×_S 𝐏¹_S} X` of
  `b` is the closed subscheme `W_∞` of `W` cut out by `Stacks.Chow.fibreIdealAtInfinity`, as
  schemes over `W`.
* `Stacks.Chow.modificationFibreAtInfinityComplStrictTransform` — the open `W_∞ ∖ X'` of the
  fibre at infinity of `b`, and `Stacks.Chow.exceptionalComplToModificationFibreAtInfinity` the
  open immersion `E ∖ X' ⟶ W_∞` onto it
  (`Stacks.Chow.opensRange_exceptionalComplToModificationFibreAtInfinity`).

## Main results

* `Stacks.Chow.isProper_blowupAtInfinityToProjectiveLineProduct` — `b` is proper when `X` is
  locally Noetherian.
* `Stacks.Chow.isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct` — assertion (1) of
  Stacks 0FBG over the affine chart: the base change of `b` along `𝐀¹_X ⟶ X ×_S 𝐏¹_S` is an
  isomorphism.
* `Stacks.Chow.ker_modificationInclusionAtInfinity_blowupAtInfinity` — the inclusion of the
  fibre at infinity of `b` into `W` is the closed immersion of `W_∞`, so that the fibre at
  infinity is an effective Cartier divisor on `W`.
* Instances: `b`, `W ⟶ X` and `W_∞ ⟶ X` are proper and locally of finite type when `X` is
  locally Noetherian, in particular when `X` is locally of finite type over a locally Noetherian
  base.

## Implementation notes

`𝐏¹_X` and `X ×_S 𝐏¹_S` are identified by
`Stacks.Chow.relativeProjectiveLineIsoProjectiveLineProduct`. The affine chart of `X ×_S 𝐏¹_S`
is the affine chart of `𝐏¹_X` composed with that isomorphism
(`Stacks.Chow.affineChart_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom`), and the
infinity section of `X ×_S 𝐏¹_S ⟶ X` is the infinity section of `𝐏¹_X ⟶ X` composed with it
(`Stacks.Chow.infinitySection_eq`), so each statement about `b` reduces to the corresponding one
about the blowup morphism `W ⟶ 𝐏¹_X`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The affine chart and the identification `𝐏¹_X = X ×_S 𝐏¹_S` -/

/-- The affine chart of `X ×_S 𝐏¹_S` is the affine chart of `𝐏¹_X` read through the
identification `𝐏¹_X ≅ X ×_S 𝐏¹_S`. -/
@[reassoc]
theorem affineChart_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom {X S : Scheme.{u}}
    (f : X ⟶ S) :
    affineChart X ≫ (relativeProjectiveLineIsoProjectiveLineProduct f).hom =
      projectiveLineAffineChart f := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst, affineChart_comp,
      projectiveLineAffineChart, pullback.lift_fst]
  · rw [Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_snd,
      projectiveLineAffineChart, pullback.lift_snd]
    apply pullback.hom_ext
    · rw [Category.assoc, projectiveLineBaseChange_comp_fst, pullback.lift_fst,
        ← Category.assoc, affineChart_comp]
    · rw [Category.assoc, projectiveLineBaseChange_comp_snd, pullback.lift_snd, affineChart,
        pullback.lift_snd]

/-- The infinity section of `𝐏¹_X ⟶ X`, read through the identification `𝐏¹_X ≅ X ×_S 𝐏¹_S`, is
the infinity section of `X ×_S 𝐏¹_S ⟶ X`. -/
@[reassoc]
theorem lineInfinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom
    {X S : Scheme.{u}} (f : X ⟶ S) :
    lineInfinitySection X ≫ (relativeProjectiveLineIsoProjectiveLineProduct f).hom =
      infinitySection f :=
  (infinitySection_eq f).symm

/-! ### The blowup at infinity over `X ×_S 𝐏¹_S` -/

variable {X S : Scheme.{u}} (ℐ : X.IdealSheafData) (f : X ⟶ S)

/-- **The blowup at infinity as a modification of `X ×_S 𝐏¹_S`**: the blowup
`W ⟶ 𝐏¹_X` of `𝐏¹_X` in `∞(Z)`, followed by the identification `𝐏¹_X ≅ X ×_S 𝐏¹_S`. -/
def blowupAtInfinityToProjectiveLineProduct :
    blowupAtInfinity ℐ ⟶ projectiveLineProduct f :=
  blowupAtInfinityToLine ℐ ≫ (relativeProjectiveLineIsoProjectiveLineProduct f).hom

/-- The structure morphism `W ⟶ X` of the modification is the projection of the blowup at
infinity to `X`. -/
@[simp]
theorem modificationProjection_blowupAtInfinityToProjectiveLineProduct :
    modificationProjection f (blowupAtInfinityToProjectiveLineProduct ℐ f) =
      blowupAtInfinityToBase ℐ := by
  rw [modificationProjection, blowupAtInfinityToProjectiveLineProduct, Category.assoc,
    relativeProjectiveLineIsoProjectiveLineProduct_hom_fst, blowupAtInfinityToBase]

/-- The blowup at infinity of a locally Noetherian scheme is proper over `𝐏¹_X`. -/
instance isProper_blowupAtInfinityToLine [IsLocallyNoetherian X] :
    IsProper (blowupAtInfinityToLine ℐ) :=
  AlgebraicGeometry.isProper_blowUpToBase (infinityCentreIdeal ℐ)

/-- **The blowup at infinity is proper** over `X ×_S 𝐏¹_S` when `X` is locally Noetherian. -/
instance isProper_blowupAtInfinityToProjectiveLineProduct [IsLocallyNoetherian X] :
    IsProper (blowupAtInfinityToProjectiveLineProduct ℐ f) := by
  rw [blowupAtInfinityToProjectiveLineProduct]
  infer_instance

/-- The blowup at infinity of a locally Noetherian scheme is proper over `X`. -/
instance isProper_blowupAtInfinityToBase [IsLocallyNoetherian X] :
    IsProper (blowupAtInfinityToBase ℐ) := by
  rw [blowupAtInfinityToBase]
  infer_instance

/-- The structure morphism `W ⟶ X` of the modification is proper when `X` is locally
Noetherian. -/
instance isProper_modificationProjection_blowupAtInfinityToProjectiveLineProduct
    [IsLocallyNoetherian X] :
    IsProper (modificationProjection f (blowupAtInfinityToProjectiveLineProduct ℐ f)) := by
  rw [modificationProjection_blowupAtInfinityToProjectiveLineProduct]
  infer_instance

/-- The structure morphism `W ⟶ X` of the modification is locally of finite type when `X` is
locally Noetherian. -/
instance locallyOfFiniteType_modificationProjection_blowupAtInfinityToProjectiveLineProduct
    [IsLocallyNoetherian X] :
    LocallyOfFiniteType
      (modificationProjection f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

/-- The affine chart `𝐀¹_X ⊆ 𝐏¹_X` lies in the open `𝐀¹_X ∪ 𝐏¹_{X ∖ Z}` over which the blowup
at infinity is an isomorphism. -/
theorem opensRange_affineChart_le_isomorphismLocusAtInfinity :
    (affineChart X).opensRange ≤ isomorphismLocusAtInfinity ℐ :=
  le_sup_left

/-- The preimage of the affine chart of `X ×_S 𝐏¹_S` in `𝐏¹_X` is the affine chart of `𝐏¹_X`,
which lies in the open over which the blowup at infinity is an isomorphism. -/
theorem preimage_opensRange_projectiveLineAffineChart_le :
    (relativeProjectiveLineIsoProjectiveLineProduct f).hom ⁻¹ᵁ
        (projectiveLineAffineChart f).opensRange ≤ isomorphismLocusAtInfinity ℐ := by
  intro x hx
  obtain ⟨y, hy⟩ : (relativeProjectiveLineIsoProjectiveLineProduct f).hom x ∈
      Set.range (projectiveLineAffineChart f) := hx
  refine opensRange_affineChart_le_isomorphismLocusAtInfinity ℐ ⟨y, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (relativeProjectiveLineIsoProjectiveLineProduct f).hom.base).1
  rwa [← Scheme.Hom.comp_apply,
    affineChart_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom]

/-- The blowup at infinity restricted over the affine chart of `X ×_S 𝐏¹_S` is an
isomorphism. -/
theorem isIso_blowupAtInfinityToProjectiveLineProduct_restrict :
    IsIso (blowupAtInfinityToProjectiveLineProduct ℐ f ∣_
      (projectiveLineAffineChart f).opensRange) := by
  have := isIso_blowupAtInfinityToLine_restrict ℐ
  have h₁ : IsIso (blowupAtInfinityToLine ℐ ∣_
      ((relativeProjectiveLineIsoProjectiveLineProduct f).hom ⁻¹ᵁ
        (projectiveLineAffineChart f).opensRange)) :=
    Stacks.PicFinite.isIso_morphismRestrict_of_le _
      (preimage_opensRange_projectiveLineAffineChart_le ℐ f)
  rw [blowupAtInfinityToProjectiveLineProduct, morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ inferInstance

/-- **Assertion (1) of Stacks 0FBG over the affine chart, in the spelling of Stacks 0F9J.** The
base change of `b : W ⟶ X ×_S 𝐏¹_S` along the affine chart `𝐀¹_X ⟶ X ×_S 𝐏¹_S` is an
isomorphism. -/
theorem isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct :
    IsIso (pullback.snd (blowupAtInfinityToProjectiveLineProduct ℐ f)
      (projectiveLineAffineChart f)) :=
  ((MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff
    (morphismRestrictOpensRange _ (projectiveLineAffineChart f))).mp
    (isIso_blowupAtInfinityToProjectiveLineProduct_restrict ℐ f)

/-! ### The fibre at infinity -/

/-- **The fibre at infinity of `b` is `W_∞`.** The inclusion of the fibre at infinity
`W ×_{X ×_S 𝐏¹_S} X` of `b` into `W` is a closed immersion whose ideal sheaf is
`Stacks.Chow.fibreIdealAtInfinity`, the inverse image of the divisor at infinity of `𝐏¹_X`. -/
theorem ker_modificationInclusionAtInfinity_blowupAtInfinity :
    (modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)).ker =
      fibreIdealAtInfinity ℐ := by
  let e := relativeProjectiveLineIsoProjectiveLineProduct f
  rw [modificationInclusionAtInfinity, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← lineInfinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom,
    Scheme.Hom.ker_comp, blowupAtInfinityToProjectiveLineProduct,
    Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_map_of_isClosedImmersion _ e.hom]
  rfl

/-- **The fibre at infinity in the spelling of Stacks 0F9J.** The fibre at
infinity `W ×_{X ×_S 𝐏¹_S} X` of `b` is the closed subscheme `W_∞` of `W` cut out by
`Stacks.Chow.fibreIdealAtInfinity`, as schemes over `W`. -/
def modificationFibreAtInfinityIso :
    modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f) ≅
      (fibreIdealAtInfinity ℐ).subscheme :=
  have h : (fibreIdealAtInfinity ℐ).subschemeι.ker =
      (modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ker_modificationInclusionAtInfinity_blowupAtInfinity]
  have := IsClosedImmersion.isIso_lift _ _ h
  asIso (IsClosedImmersion.lift _ _ h.le)

/-- The identification `modificationFibreAtInfinityIso` is compatible with the inclusions of the
fibre at infinity and of `W_∞` into `W`. -/
@[reassoc (attr := simp)]
theorem modificationFibreAtInfinityIso_hom_subschemeι :
    (modificationFibreAtInfinityIso ℐ f).hom ≫ (fibreIdealAtInfinity ℐ).subschemeι =
      modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f) :=
  IsClosedImmersion.lift_fac _ _ _

/-- The inverse of `modificationFibreAtInfinityIso` followed by the inclusion of the fibre at
infinity into `W` is the inclusion of `W_∞` into `W`. -/
@[reassoc (attr := simp)]
theorem modificationFibreAtInfinityIso_inv_inclusion :
    (modificationFibreAtInfinityIso ℐ f).inv ≫
        modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f) =
      (fibreIdealAtInfinity ℐ).subschemeι := by
  rw [Iso.inv_comp_eq, modificationFibreAtInfinityIso_hom_subschemeι]

/-- The fibre at infinity of `b` is an effective Cartier divisor on `W`: its ideal sheaf in `W`
is that of `W_∞`. -/
theorem isEffectiveCartierDivisor_ker_modificationInclusionAtInfinity :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)).ker := by
  rw [ker_modificationInclusionAtInfinity_blowupAtInfinity]
  exact isEffectiveCartierDivisor_fibreIdealAtInfinity ℐ

/-- The inclusion of the fibre at infinity of `b` is proper: it is a closed immersion. -/
instance isProper_modificationInclusionAtInfinity_blowupAtInfinity :
    IsProper (modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

/-- The projection `W_∞ ⟶ X` of the fibre at infinity is proper when `X` is locally
Noetherian. -/
instance isProper_modificationProjectionAtInfinity_blowupAtInfinity [IsLocallyNoetherian X] :
    IsProper (modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

/-- The projection `W_∞ ⟶ X` of the fibre at infinity is locally of finite type when `X` is
locally Noetherian. -/
instance locallyOfFiniteType_modificationProjectionAtInfinity_blowupAtInfinity
    [IsLocallyNoetherian X] :
    LocallyOfFiniteType
      (modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

/-! ### The open `W_∞ ∖ X'` of the fibre at infinity -/

/-- **The open `W_∞ ∖ X'` of the fibre at infinity of `b`**: the inverse image in the fibre at
infinity of the complement of the strict transform `X' ⊆ W`. This is the open subscheme of `W_∞`
onto which the open immersion `C_ZX ⟶ W_∞` of Stacks 0FBH lands. -/
abbrev modificationFibreAtInfinityComplStrictTransform :
    (modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)).Opens :=
  modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f) ⁻¹ᵁ
    strictTransformComplAtInfinity ℐ

/-- **`E ∖ X'` as an open subscheme of the fibre at infinity of `b`**: the identification
`E ∖ X' = W_∞ ∖ X'` of `Stacks.Chow.exceptionalComplIsoFibreCompl` followed by the inclusion of
`W_∞ ∖ X'` into the fibre at infinity. -/
def exceptionalComplToModificationFibreAtInfinity :
    ((exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ strictTransformComplAtInfinity ℐ).toScheme ⟶
      modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f) :=
  (exceptionalComplIsoFibreCompl ℐ).hom ≫
    ((fibreIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ strictTransformComplAtInfinity ℐ).ι ≫
    (modificationFibreAtInfinityIso ℐ f).inv

/-- The morphism `E ∖ X' ⟶ W_∞` is an open immersion. -/
instance isOpenImmersion_exceptionalComplToModificationFibreAtInfinity :
    IsOpenImmersion (exceptionalComplToModificationFibreAtInfinity ℐ f) := by
  rw [exceptionalComplToModificationFibreAtInfinity]
  infer_instance

/-- The open immersion `E ∖ X' ⟶ W_∞` is a morphism over `W`. -/
@[reassoc (attr := simp)]
theorem exceptionalComplToModificationFibreAtInfinity_inclusion :
    exceptionalComplToModificationFibreAtInfinity ℐ f ≫
        modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f) =
      ((exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ strictTransformComplAtInfinity ℐ).ι ≫
        (exceptionalIdealAtInfinity ℐ).subschemeι := by
  rw [exceptionalComplToModificationFibreAtInfinity, Category.assoc, Category.assoc,
    modificationFibreAtInfinityIso_inv_inclusion]
  exact exceptionalComplToFibreCompl_ι_subschemeι ℐ

/-- **The image of `E ∖ X' ⟶ W_∞` is `W_∞ ∖ X'`.** -/
theorem opensRange_exceptionalComplToModificationFibreAtInfinity :
    (exceptionalComplToModificationFibreAtInfinity ℐ f).opensRange =
      modificationFibreAtInfinityComplStrictTransform ℐ f := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, modificationFibreAtInfinityComplStrictTransform,
    Scheme.Hom.mem_preimage]
  constructor
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, exceptionalComplToModificationFibreAtInfinity_inclusion,
      Scheme.Hom.comp_apply]
    exact y.2
  · intro hx
    have hx' : (modificationFibreAtInfinityIso ℐ f).hom x ∈
        Set.range ((fibreIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ strictTransformComplAtInfinity ℐ).ι := by
      rw [Scheme.Opens.range_ι, SetLike.mem_coe, Scheme.Hom.mem_preimage,
        ← Scheme.Hom.comp_apply, modificationFibreAtInfinityIso_hom_subschemeι]
      exact hx
    obtain ⟨w, hw⟩ := hx'
    refine ⟨(exceptionalComplIsoFibreCompl ℐ).inv w, ?_⟩
    rw [exceptionalComplToModificationFibreAtInfinity, Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply (exceptionalComplIsoFibreCompl ℐ).inv, Iso.inv_hom_id]
    change (modificationFibreAtInfinityIso ℐ f).inv
      (((fibreIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ strictTransformComplAtInfinity ℐ).ι w) = x
    rw [hw, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-! ### Over a locally Noetherian base

In the situation of Stacks 0F9J and 0FBK, `X` is locally of finite type over a locally Noetherian
base `S`, and is therefore itself locally Noetherian. The instances below record the finiteness
and properness of `b` and of its fibre at infinity in that form. -/

section LocallyNoetherianBase

variable [IsLocallyNoetherian S] [LocallyOfFiniteType f]

/-- `b : W ⟶ X ×_S 𝐏¹_S` is proper when `X` is locally of finite type over a locally Noetherian
base. -/
instance isProper_blowupAtInfinityToProjectiveLineProduct_of_locallyOfFiniteType :
    IsProper (blowupAtInfinityToProjectiveLineProduct ℐ f) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

/-- The structure morphism `W ⟶ X` of `b` is proper when `X` is locally of finite type over a
locally Noetherian base. -/
instance isProper_modificationProjection_blowupAtInfinity_of_locallyOfFiniteType :
    IsProper (modificationProjection f (blowupAtInfinityToProjectiveLineProduct ℐ f)) := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  infer_instance

/-- The structure morphism `W ⟶ X` of `b` is locally of finite type when `X` is locally of
finite type over a locally Noetherian base. -/
instance locallyOfFiniteType_modificationProjection_blowupAtInfinity_of_locallyOfFiniteType :
    LocallyOfFiniteType (modificationProjection f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

/-- The projection `W_∞ ⟶ X` of the fibre at infinity of `b` is proper when `X` is locally of
finite type over a locally Noetherian base. -/
instance isProper_modificationProjectionAtInfinity_blowupAtInfinity_of_locallyOfFiniteType :
    IsProper (modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

/-- The projection `W_∞ ⟶ X` of the fibre at infinity of `b` is locally of finite type when `X`
is locally of finite type over a locally Noetherian base. -/
instance locallyOfFiniteType_modificationProjectionAtInfinity_blowupAtInfinity_of_lft :
    LocallyOfFiniteType
      (modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct ℐ f)) :=
  inferInstance

end LocallyNoetherianBase

end Stacks.Chow

end

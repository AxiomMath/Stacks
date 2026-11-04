module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreNormalConeIso
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityRestrictedBaseChange
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul

/-!
# Base change of the blowup at infinity

Let `f : X' ⟶ X` be a morphism of schemes, `ℐ` a quasi-coherent ideal sheaf on `X` with closed
subscheme `Z`, and `ℐ' = f⁻¹ℐ · 𝒪_{X'}` its inverse image, cutting out `Z' = Z ×_X X'`. Let
`W ⟶ 𝐏¹_X` and `W' ⟶ 𝐏¹_{X'}` be the blowups at infinity of Stacks 0FBG, in the centres `∞(Z)`
and `∞(Z')`. The centre `∞(Z)` pulls back to `∞(Z')` along `𝐏¹_{X'} ⟶ 𝐏¹_X`, so its inverse
image on `W'` is the exceptional divisor `E'` of `W'`, an effective Cartier divisor, and the
universal property of the blowup (Stacks 0806) gives a morphism `W' ⟶ W` over
`𝐏¹_{X'} ⟶ 𝐏¹_X`. Along it `E`, the fibre at infinity `W_∞` and the strict transform `X̃` of `X`
pull back to `E'`, `W'_∞` and the strict transform of `X'`; the last because `W_∞ = E + X̃` pulls
back to `W'_∞ = E' + (W' ⟶ W)⁻¹X̃`, and the residual divisor of `E'` in `W'_∞` is the strict
transform of `X'` (Stacks 0FBG (4)).

## Main definitions

* `Stacks.Chow.blowupAtInfinityComap` — the comparison `W' ⟶ W`.
* `Stacks.Chow.blowupAtInfinityToRestrictedModification` — the comparison
  `W' ⟶ W ×_{𝐏¹_X} 𝐏¹_{X'}` over `𝐏¹_{X'}`, into the base change of Stacks 0GUH.

## Main results

* `Stacks.Chow.comap_infinityCentreIdeal_projectiveLineBaseChange_eq` — `∞(Z)` pulls back to
  `∞(Z ×_X X')`.
* `Stacks.Chow.comap_exceptionalIdealAtInfinity_blowupAtInfinityComap`,
  `Stacks.Chow.comap_fibreIdealAtInfinity_blowupAtInfinityComap`,
  `Stacks.Chow.comap_strictTransformIdealAtInfinity_blowupAtInfinityComap` — `E`, `W_∞` and `X̃`
  pull back to `E'`, `W'_∞` and the strict transform of `X'`.
* `Stacks.Chow.preimage_strictTransformComplAtInfinity_blowupAtInfinityComap` — `W' ∖ X̃'` is the
  inverse image of `W ∖ X̃`.
* `Stacks.Chow.ker_pullbackSnd_eq_comap` — the ideal of `Z ×_X X'` is the inverse image of the
  ideal of `Z`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open GysinAtInfinity (baseChangedModification modificationProjectionAtInfinity_eq_snd)

variable {X X' : Scheme.{u}} (f : X' ⟶ X)

/-- The infinity section of `𝐏¹_{X'}` is the base change of that of `𝐏¹_X`. -/
theorem isPullback_lineInfinitySection_projectiveLineBaseChange :
    IsPullback (lineInfinitySection X') f (projectiveLineBaseChange f) (lineInfinitySection X) := by
  refine IsPullback.of_right (h₁₂ := relativeProjectiveLine X' ↘ X')
    (h₂₂ := relativeProjectiveLine X ↘ X) (v₁₃ := f) ?_
    (absoluteConstantSection_comp_projectiveLineBaseChange integralInfinitySection f)
    (isPullback_projectiveLineBaseChange f)
  rw [lineInfinitySection_comp, lineInfinitySection_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The divisor at infinity of `𝐏¹_X` pulls back to that of `𝐏¹_{X'}`. -/
theorem comap_lineInfinityDivisor_projectiveLineBaseChange :
    (lineInfinityDivisor X).comap (projectiveLineBaseChange f) = lineInfinityDivisor X' := by
  rw [lineInfinityDivisor, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    lineInfinityDivisor,
    ← (isPullback_lineInfinitySection_projectiveLineBaseChange f).isoPullback_inv_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- The kernel of the base change of a closed immersion is the inverse image of its kernel. -/
theorem ker_pullbackSnd_eq_comap {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    (pullback.snd i f).ker = i.ker.comap f := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← pullbackSymmetry_hom_comp_fst,
    Scheme.Hom.ker_comp_of_isIso]

/-- **The centre `∞(Z)` pulls back to `∞(Z ×_X X')`**: the inverse image of the ideal of `∞(Z)`
along `𝐏¹_{X'} ⟶ 𝐏¹_X` is the ideal of the centre of the inverse image of `ℐ`. -/
theorem comap_infinityCentreIdeal_projectiveLineBaseChange_eq (ℐ : X.IdealSheafData) :
    (infinityCentreIdeal ℐ).comap (projectiveLineBaseChange f) =
      infinityCentreIdeal (ℐ.comap f) := by
  rw [infinityCentreIdeal_eq_sup, infinityCentreIdeal_eq_sup, Scheme.IdealSheafData.comap_sup,
    ← Scheme.IdealSheafData.comap_comp, projectiveLineBaseChange_over,
    Scheme.IdealSheafData.comap_comp, comap_lineInfinityDivisor_projectiveLineBaseChange]

section Blowup

variable (ℐ : X.IdealSheafData) (ℐ' : X'.IdealSheafData) (h : ℐ' = ℐ.comap f)

include h in
/-- The centre `∞(Z)` pulls back to the exceptional divisor of the blowup at infinity of `X'`
along `W' ⟶ 𝐏¹_{X'} ⟶ 𝐏¹_X`, an effective Cartier divisor. -/
theorem isCartierOver_infinityCentreIdeal_blowupAtInfinityComap :
    Stacks.Blowup.IsCartierOver (infinityCentreIdeal ℐ)
      (Over.mk (blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f)) := by
  show Stacks.Divisors.IsEffectiveCartierDivisor
    ((infinityCentreIdeal ℐ).comap (blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f))
  rw [Scheme.IdealSheafData.comap_comp, comap_infinityCentreIdeal_projectiveLineBaseChange_eq,
    ← h]
  exact isEffectiveCartierDivisor_exceptionalIdealAtInfinity ℐ'

/-- **The comparison `W' ⟶ W` of the blowups at infinity** of `X' ⟶ X`, for an ideal `ℐ'` on
`X'` which is the inverse image of `ℐ`: the classifying morphism of `W' ⟶ 𝐏¹_{X'} ⟶ 𝐏¹_X`, along
which the centre `∞(Z)` pulls back to the exceptional divisor of `W'`. -/
def blowupAtInfinityComap : blowupAtInfinity ℐ' ⟶ blowupAtInfinity ℐ :=
  blowUpLift (infinityCentreIdeal ℐ) (blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f)
    (isCartierOver_infinityCentreIdeal_blowupAtInfinityComap f ℐ ℐ' h)

/-- The comparison `W' ⟶ W` lies over `𝐏¹_{X'} ⟶ 𝐏¹_X`. -/
@[reassoc]
theorem blowupAtInfinityComap_comp :
    blowupAtInfinityComap f ℐ ℐ' h ≫ blowupAtInfinityToLine ℐ =
      blowupAtInfinityToLine ℐ' ≫ projectiveLineBaseChange f :=
  blowUpLift_comp _ _ _

/-- The comparison `W' ⟶ W` lies over `X' ⟶ X`. -/
@[reassoc]
theorem blowupAtInfinityComap_toBase :
    blowupAtInfinityComap f ℐ ℐ' h ≫ blowupAtInfinityToBase ℐ =
      blowupAtInfinityToBase ℐ' ≫ f := by
  rw [blowupAtInfinityToBase, blowupAtInfinityComap_comp_assoc, projectiveLineBaseChange_over,
    blowupAtInfinityToBase, Category.assoc]

/-- An ideal on `𝐏¹_X` pulled back to `W` and then to `W'` is the pullback to `W'` of its
pullback to `𝐏¹_{X'}`. -/
private theorem comap_comap_blowupAtInfinityComap {J : (relativeProjectiveLine X).IdealSheafData}
    {J' : (relativeProjectiveLine X').IdealSheafData}
    (hJ : J.comap (projectiveLineBaseChange f) = J') :
    (J.comap (blowupAtInfinityToLine ℐ)).comap (blowupAtInfinityComap f ℐ ℐ' h) =
      J'.comap (blowupAtInfinityToLine ℐ') := by
  rw [← Scheme.IdealSheafData.comap_comp, blowupAtInfinityComap_comp,
    Scheme.IdealSheafData.comap_comp, hJ]

/-- The exceptional divisor of `W` pulls back to the exceptional divisor of `W'`. -/
theorem comap_exceptionalIdealAtInfinity_blowupAtInfinityComap :
    (exceptionalIdealAtInfinity ℐ).comap (blowupAtInfinityComap f ℐ ℐ' h) =
      exceptionalIdealAtInfinity ℐ' :=
  comap_comap_blowupAtInfinityComap f ℐ ℐ' h
    (by rw [comap_infinityCentreIdeal_projectiveLineBaseChange_eq, h])

/-- The fibre at infinity of `W` pulls back to the fibre at infinity of `W'`. -/
theorem comap_fibreIdealAtInfinity_blowupAtInfinityComap :
    (fibreIdealAtInfinity ℐ).comap (blowupAtInfinityComap f ℐ ℐ' h) =
      fibreIdealAtInfinity ℐ' :=
  comap_comap_blowupAtInfinityComap f ℐ ℐ' h (comap_lineInfinityDivisor_projectiveLineBaseChange f)

/-- **The strict transform `X̃` of `X` in `W` pulls back to the strict transform of `X'` in `W'`.**
Pulling back `W_∞ = E + X̃` along `W' ⟶ W` gives `W'_∞ = E' + (W' ⟶ W)⁻¹X̃`, and the residual
divisor of `E'` in `W'_∞` is the strict transform of `X'` (Stacks 0FBG (4)). -/
theorem comap_strictTransformIdealAtInfinity_blowupAtInfinityComap :
    (strictTransformIdealAtInfinity ℐ).comap (blowupAtInfinityComap f ℐ ℐ' h) =
      strictTransformIdealAtInfinity ℐ' := by
  refine eq_strictTransformIdealAtInfinity_of_mul_eq ℐ' _ ?_
  rw [← comap_fibreIdealAtInfinity_blowupAtInfinityComap f ℐ ℐ' h,
    ← comap_exceptionalIdealAtInfinity_blowupAtInfinityComap f ℐ ℐ' h,
    fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity,
    Stacks.IdealSheaf.comap_mul]

/-- **`W' ∖ X̃'` is the inverse image of `W ∖ X̃`** under the comparison `W' ⟶ W`: the open
complement of the strict transform pulls back to the open complement of the strict transform. -/
theorem preimage_strictTransformComplAtInfinity_blowupAtInfinityComap :
    blowupAtInfinityComap f ℐ ℐ' h ⁻¹ᵁ strictTransformComplAtInfinity ℐ =
      strictTransformComplAtInfinity ℐ' := by
  refine TopologicalSpace.Opens.ext ?_
  show (blowupAtInfinityComap f ℐ ℐ' h).base ⁻¹'
      ((strictTransformIdealAtInfinity ℐ).support : Set (blowupAtInfinity ℐ))ᶜ =
    ((strictTransformIdealAtInfinity ℐ').support : Set (blowupAtInfinity ℐ'))ᶜ
  rw [← comap_strictTransformIdealAtInfinity_blowupAtInfinityComap f ℐ ℐ' h,
    Scheme.IdealSheafData.support_comap]
  rfl

end Blowup

section Modification

variable {S : Scheme.{u}} (sX : X ⟶ S) (ℐ : X.IdealSheafData) (ℐ' : X'.IdealSheafData)
  (h : ℐ' = ℐ.comap f)

/-- The identifications `𝐏¹_X ≅ X ×_S 𝐏¹_S` are compatible with base change along `X' ⟶ X`. -/
theorem projectiveLineBaseChange_comp_relativeProjectiveLineIsoProjectiveLineProduct :
    projectiveLineBaseChange f ≫ (relativeProjectiveLineIsoProjectiveLineProduct sX).hom =
      (relativeProjectiveLineIsoProjectiveLineProduct (f ≫ sX)).hom ≫ familyBaseChange sX f := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst,
      projectiveLineBaseChange_over, Category.assoc, familyBaseChange_comp_fst,
      relativeProjectiveLineIsoProjectiveLineProduct_hom_fst_assoc]
  · rw [Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_snd, Category.assoc,
      familyBaseChange_comp_snd, relativeProjectiveLineIsoProjectiveLineProduct_hom_snd,
      ← projectiveLineBaseChange_comp]

/-- **The comparison `W' ⟶ W ×_{𝐏¹_X} 𝐏¹_{X'}`** of the blowup at infinity of `X'` with the base
change of the blowup at infinity of `X`, over `𝐏¹_{X'}`. -/
def blowupAtInfinityToRestrictedModification :
    blowupAtInfinity ℐ' ⟶
      pullback (blowupAtInfinityToProjectiveLineProduct ℐ sX) (familyBaseChange sX f) :=
  pullback.lift (blowupAtInfinityComap f ℐ ℐ' h)
    (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) (by
      rw [blowupAtInfinityToProjectiveLineProduct, blowupAtInfinityComap_comp_assoc,
        projectiveLineBaseChange_comp_relativeProjectiveLineIsoProjectiveLineProduct,
        blowupAtInfinityToProjectiveLineProduct, Category.assoc])

/-- The comparison `W' ⟶ W ×_{𝐏¹_X} 𝐏¹_{X'}` followed by the first projection is the
comparison `W' ⟶ W`. -/
@[reassoc (attr := simp)]
theorem blowupAtInfinityToRestrictedModification_fst :
    blowupAtInfinityToRestrictedModification f sX ℐ ℐ' h ≫ pullback.fst _ _ =
      blowupAtInfinityComap f ℐ ℐ' h :=
  pullback.lift_fst _ _ _

/-- The comparison `W' ⟶ W ×_{𝐏¹_X} 𝐏¹_{X'}` lies over `𝐏¹_{X'}`. -/
@[reassoc (attr := simp)]
theorem blowupAtInfinityToRestrictedModification_comp :
    blowupAtInfinityToRestrictedModification f sX ℐ ℐ' h ≫
        baseChangedModification sX (blowupAtInfinityToProjectiveLineProduct ℐ sX) f =
      blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX) :=
  pullback.lift_snd _ _ _

/-- The comparison `W' ⟶ W` intertwines the two modifications of `X' ×_S 𝐏¹_S` and
`X ×_S 𝐏¹_S`. -/
@[reassoc]
theorem blowupAtInfinityComap_comp_toProjectiveLineProduct :
    blowupAtInfinityComap f ℐ ℐ' h ≫ blowupAtInfinityToProjectiveLineProduct ℐ sX =
      blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX) ≫ familyBaseChange sX f := by
  rw [← blowupAtInfinityToRestrictedModification_fst f sX ℐ ℐ' h, Category.assoc,
    pullback.condition, ← Category.assoc, blowupAtInfinityToRestrictedModification_comp]

/-- **The comparison `W'_∞ ⟶ W_∞` of the fibres at infinity**, induced by `W' ⟶ W`. -/
def blowupAtInfinityFibreComap :
    modificationFibreAtInfinity (f ≫ sX) (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) ⟶
      modificationFibreAtInfinity sX (blowupAtInfinityToProjectiveLineProduct ℐ sX) :=
  pullback.map _ _ _ _ (blowupAtInfinityComap f ℐ ℐ' h) f (familyBaseChange sX f)
    (blowupAtInfinityComap_comp_toProjectiveLineProduct f sX ℐ ℐ' h).symm
    (infinitySection_comp_familyBaseChange sX f)

/-- The comparison of the fibres at infinity is compatible with their inclusions. -/
@[reassoc (attr := simp)]
theorem blowupAtInfinityFibreComap_inclusion :
    blowupAtInfinityFibreComap f sX ℐ ℐ' h ≫
        modificationInclusionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct ℐ sX) =
      modificationInclusionAtInfinity (f ≫ sX)
          (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) ≫
        blowupAtInfinityComap f ℐ ℐ' h :=
  pullback.lift_fst _ _ _

/-- The comparison of the fibres at infinity lies over `X' ⟶ X`. -/
@[reassoc]
theorem blowupAtInfinityFibreComap_projection :
    blowupAtInfinityFibreComap f sX ℐ ℐ' h ≫
        modificationProjectionAtInfinity sX (blowupAtInfinityToProjectiveLineProduct ℐ sX) =
      modificationProjectionAtInfinity (f ≫ sX)
          (blowupAtInfinityToProjectiveLineProduct ℐ' (f ≫ sX)) ≫ f := by
  rw [modificationProjectionAtInfinity_eq_snd, modificationProjectionAtInfinity_eq_snd]
  exact pullback.lift_snd _ _ _

/-- **`W'_∞ ∖ X̃'` is the inverse image of `W_∞ ∖ X̃`** under the comparison of the fibres at
infinity. -/
theorem preimage_modificationFibreAtInfinityComplStrictTransform :
    blowupAtInfinityFibreComap f sX ℐ ℐ' h ⁻¹ᵁ
        modificationFibreAtInfinityComplStrictTransform ℐ sX =
      modificationFibreAtInfinityComplStrictTransform ℐ' (f ≫ sX) := by
  rw [modificationFibreAtInfinityComplStrictTransform,
    modificationFibreAtInfinityComplStrictTransform, ← Scheme.Hom.comp_preimage,
    blowupAtInfinityFibreComap_inclusion, Scheme.Hom.comp_preimage,
    preimage_strictTransformComplAtInfinity_blowupAtInfinityComap]

end Modification

section NormalCone

/-- The kernel of the base change of a closed immersion along a cartesian square is the inverse
image of its kernel. -/
theorem ker_eq_comap_of_isPullback {Z Z' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    [IsClosedImmersion i] {g : Z' ⟶ Z} (sq : IsPullback i' g f i) : i'.ker = i.ker.comap f := by
  rw [← ker_pullbackSnd_eq_comap f i, ← sq.flip.isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

variable {S : Scheme.{u}} (sX : X ⟶ S) {Z Z' : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  (i' : Z' ⟶ X') [IsClosedImmersion i'] (hker : i'.ker = i.ker.comap f)

/-- **The comparison `C_{Z'}X' ⟶ C_ZX` of the normal cones** of a closed immersion `Z ⟶ X` and of
a closed immersion `Z' ⟶ X'` cut out by the inverse image of its ideal, read through the open
immersions `j` of Stacks 0FBH: the restriction of the comparison `W'_∞ ⟶ W_∞` of the fibres at
infinity to the opens `C_{Z'}X' = W'_∞ ∖ X̃'` and `C_ZX = W_∞ ∖ X̃`. -/
def normalConeBaseChangeMap :
    Stacks.Conormal.normalCone i' ⟶ Stacks.Conormal.normalCone i :=
  IsOpenImmersion.lift (normalConeToFibreAtInfinity i sX)
    (normalConeToFibreAtInfinity i' (f ≫ sX) ≫
      blowupAtInfinityFibreComap f sX i.ker i'.ker hker) (by
      rintro _ ⟨x, rfl⟩
      have hx : normalConeToFibreAtInfinity i' (f ≫ sX) x ∈
          blowupAtInfinityFibreComap f sX i.ker i'.ker hker ⁻¹ᵁ
            modificationFibreAtInfinityComplStrictTransform i.ker sX := by
        rw [preimage_modificationFibreAtInfinityComplStrictTransform,
          ← opensRange_normalConeToFibreAtInfinity]
        exact ⟨x, rfl⟩
      rwa [Scheme.Hom.mem_preimage, ← opensRange_normalConeToFibreAtInfinity] at hx)

/-- The comparison of the normal cones is the comparison of the fibres at infinity, through the
open immersions `j` of Stacks 0FBH. -/
@[reassoc (attr := simp)]
theorem normalConeBaseChangeMap_comp :
    normalConeBaseChangeMap f sX i i' hker ≫ normalConeToFibreAtInfinity i sX =
      normalConeToFibreAtInfinity i' (f ≫ sX) ≫
        blowupAtInfinityFibreComap f sX i.ker i'.ker hker :=
  IsOpenImmersion.lift_fac _ _ _

/-- The comparison of the normal cones lies over `Z' ⟶ Z`. -/
@[reassoc]
theorem normalConeBaseChangeMap_toBase (g : Z' ⟶ Z) (hcomm : i' ≫ f = g ≫ i) :
    normalConeBaseChangeMap f sX i i' hker ≫ Stacks.Conormal.normalConeToBase i =
      Stacks.Conormal.normalConeToBase i' ≫ g := by
  rw [← cancel_mono i, Category.assoc, Category.assoc, ← hcomm,
    ← normalConeToFibreAtInfinity_comp_projection i sX, ← Category.assoc,
    normalConeBaseChangeMap_comp, Category.assoc, blowupAtInfinityFibreComap_projection,
    ← Category.assoc, normalConeToFibreAtInfinity_comp_projection, Category.assoc]

/-- **`C_{Z'}X'` is the inverse image of `C_ZX` in the fibre at infinity**: the square formed by
the comparisons `C_{Z'}X' ⟶ C_ZX` and `W'_∞ ⟶ W_∞` and the open immersions `j` of Stacks 0FBH
is cartesian. -/
theorem isPullback_normalConeBaseChangeMap :
    IsPullback (normalConeBaseChangeMap f sX i i' hker)
      (normalConeToFibreAtInfinity i' (f ≫ sX))
      (normalConeToFibreAtInfinity i sX)
      (blowupAtInfinityFibreComap f sX i.ker i'.ker hker) :=
  IsOpenImmersion.isPullback _ _ _ _ (normalConeBaseChangeMap_comp f sX i i' hker).symm (by
    rw [opensRange_normalConeToFibreAtInfinity, opensRange_normalConeToFibreAtInfinity,
      preimage_modificationFibreAtInfinityComplStrictTransform])

end NormalCone

end Stacks.Chow

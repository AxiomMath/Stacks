module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.AdicStages

/-!
# The two ends of the adic tower of a family

`Stacks.BaseAdicFiltration.adicStage` filters a family `p : U ⟶ Spec A` by the closed
subschemes cut out by the powers `Iⁿ⁺¹𝒪_U`. An induction running up that tower has to recognize
its two ends:

* at the bottom, stage `0` is the special fibre, so a closed immersion cut out by `I 𝒪_U` — the
  identification a deformation carries — is canonically isomorphic to it over `U`;
* at the top, the filtration reaches `U` itself, because over an Artinian local base `I = 𝔪` is
  nilpotent, so a high enough power of `I 𝒪_U` vanishes and the stage's closed immersion into
  `U` is invertible.

Both are what the essential-surjectivity direction of [Stacks, Tag 0E3X] needs: it starts the
downstairs induction from the morphism `f : X ⟶ Y` it is given, and ends it with a morphism out
of `U`, so it must know that stage `0` *is* `X` and that the last stage *is* `U`.

## Main results

* `Stacks.BaseAdicFiltration.baseIdeal_pow_eq_bot` — a vanishing power of `I` makes the
  corresponding power of `I 𝒪_U` vanish.
* `Stacks.BaseAdicFiltration.isIso_adicStageι_of_pow_eq_bot` and
  `Stacks.BaseAdicFiltration.exists_isIso_adicStageι` — **the top of the tower is the family
  itself**, the second specializing the first to an Artinian local base.
* `Stacks.BaseAdicFiltration.adicStageZeroIso` and
  `Stacks.BaseAdicFiltration.adicStageZeroIso_hom_comp_adicStageι` — **the bottom of the tower
  is the special fibre**: a closed immersion with ideal sheaf `I 𝒪_U` is isomorphic to stage `0`
  over `U`.

## Implementation notes

The power computation is pointwise on affine opens: `AlgebraicGeometry.Scheme.IdealSheafData`
takes powers componentwise (`ideal_pow` holds by definition), the component of `I 𝒪_U` is the
image ideal `Ideal.map` of `I` (`Stacks.BaseAdicFiltration.baseIdeal_ideal`), and `Ideal.map`
commutes with powers and kills `⊥`.

The bottom identification is Mathlib's universal property of closed immersions,
`AlgebraicGeometry.IsClosedImmersion.lift` together with
`AlgebraicGeometry.IsClosedImmersion.isIso_lift`: two closed immersions into `U` with the same
ideal sheaf are identified by the lift of either through the other. Nothing is proved chart by
chart.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.BaseAdicFiltration

variable {A : Type u} [CommRing A] {U : Scheme.{u}} (p : U ⟶ Spec (CommRingCat.of A))

/-- **A vanishing power of `I` kills the corresponding power of `I 𝒪_U`.** The ideal sheaf
`I 𝒪_U` has, over every affine open, the image of `I` as its component, and taking the image
ideal commutes with powers. -/
theorem baseIdeal_pow_eq_bot {I : Ideal A} {n : ℕ} (hI : I ^ n = ⊥) :
    baseIdeal p I ^ n = ⊥ := by
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  have h : (baseIdeal p I ^ n).ideal V = ((baseIdeal p I).ideal V) ^ n := rfl
  rw [h, baseIdeal_ideal, ← Ideal.map_pow, hI, Ideal.map_bot]
  rfl

/-- A stage of the adic filtration is a closed subscheme of the family. -/
instance isClosedImmersion_adicStageι (I : Ideal A) (n : ℕ) :
    IsClosedImmersion (adicStageι p I n) :=
  inferInstanceAs (IsClosedImmersion (baseIdeal p I ^ (n + 1)).subschemeι)

/-- **The top of the adic tower is the family itself.** If `Iⁿ⁺¹` vanishes then the stage `n`
of the filtration is cut out by the zero ideal sheaf, so its closed immersion into `U` is an
isomorphism. -/
theorem isIso_adicStageι_of_pow_eq_bot (I : Ideal A) (n : ℕ) (hI : I ^ (n + 1) = ⊥) :
    IsIso (adicStageι p I n) :=
  (Scheme.isIso_subschemeι_iff_eq_bot (baseIdeal p I ^ (n + 1))).mpr
    (baseIdeal_pow_eq_bot p hI)

/-- **Over an Artinian local base the adic tower reaches the family.** The maximal ideal of an
Artinian local ring is nilpotent, so some stage of the `𝔪`-adic filtration of `U` is `U`
itself. -/
theorem exists_isIso_adicStageι [IsArtinianRing A] [IsLocalRing A] :
    ∃ N : ℕ, IsIso (adicStageι p (IsLocalRing.maximalIdeal A) N) := by
  obtain ⟨N, hN⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).1 ‹IsArtinianRing A›
  refine ⟨N, isIso_adicStageι_of_pow_eq_bot p _ N ?_⟩
  rw [pow_succ, hN, zero_mul]
  rfl

section Bottom

variable {X : Scheme.{u}} (I : Ideal A) (iX : X ⟶ U) [IsClosedImmersion iX]
  (hk : iX.ker = baseIdeal p I)

/-- The lift of a closed immersion with ideal sheaf `I 𝒪_U` through the bottom stage of the
adic filtration, by the universal property of the bottom stage as a closed subscheme. -/
def adicStageZeroLift : X ⟶ adicStage p I 0 :=
  IsClosedImmersion.lift (adicStageι p I 0) iX
    ((ker_adicStageι_zero p I).trans hk.symm).le

omit [IsClosedImmersion iX] in
/-- The lift through the bottom stage is a morphism over `U`. -/
@[simp]
theorem adicStageZeroLift_comp_adicStageι :
    adicStageZeroLift p I iX hk ≫ adicStageι p I 0 = iX :=
  IsClosedImmersion.lift_fac _ _ _

/-- The lift through the bottom stage is invertible: both closed immersions into `U` are cut
out by `I 𝒪_U`. -/
instance isIso_adicStageZeroLift : IsIso (adicStageZeroLift p I iX hk) :=
  IsClosedImmersion.isIso_lift (adicStageι p I 0) iX
    ((ker_adicStageι_zero p I).trans hk.symm)

/-- **The bottom of the adic tower is the special fibre.** A closed immersion into `U` whose
ideal sheaf is `I 𝒪_U` — the identification of the special fibre carried by a deformation — is
isomorphic over `U` to the stage `0` of the `I`-adic filtration. -/
def adicStageZeroIso : X ≅ adicStage p I 0 :=
  asIso (adicStageZeroLift p I iX hk)

/-- The identification of the bottom stage is a morphism over `U`. -/
@[simp]
theorem adicStageZeroIso_hom_comp_adicStageι :
    (adicStageZeroIso p I iX hk).hom ≫ adicStageι p I 0 = iX :=
  IsClosedImmersion.lift_fac _ _ _

/-- The identification of the bottom stage, read backwards, is a morphism over `U`. -/
@[simp]
theorem adicStageZeroIso_inv_comp :
    (adicStageZeroIso p I iX hk).inv ≫ iX = adicStageι p I 0 :=
  calc (adicStageZeroIso p I iX hk).inv ≫ iX
      = (adicStageZeroIso p I iX hk).inv ≫
          (adicStageZeroIso p I iX hk).hom ≫ adicStageι p I 0 := by
        rw [adicStageZeroIso_hom_comp_adicStageι]
    _ = adicStageι p I 0 := Iso.inv_hom_id_assoc _ _

/-- The bottom stage is a morphism over the base. -/
@[simp]
theorem adicStageZeroIso_hom_comp_adicStageToBase :
    (adicStageZeroIso p I iX hk).hom ≫ adicStageToBase p I 0 = iX ≫ p := by
  rw [adicStageToBase, ← Category.assoc, adicStageZeroIso_hom_comp_adicStageι]

end Bottom

end Stacks.BaseAdicFiltration

end

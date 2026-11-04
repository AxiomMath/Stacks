module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Modification
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.DivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.BaseChangeDivisor

/-!
# The fibre at zero of a modification of the relative projective line

Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`. The fibre at zero lies over the
chart, and on `b⁻¹(𝐀¹_X) ×_X T ≅ T ×_S 𝐀¹_S` it is a relative effective Cartier divisor mapping
isomorphically to `T` (Stacks 056Q). By Stacks 02TR the Gysin map of the fibre at zero sends a
lift of `α ∈ A_k(T)` to `α`, read on `W ×_X T` through the section at zero. This is the step
`i_0^* β = α` of the proof of Stacks 0F9J.

## Main results

* `Stacks.Chow.GysinAtInfinity.onChow_openZeroDivisor_flatPullbackChow` — Stacks 02TR on the open
  part.
* `Stacks.Chow.GysinAtInfinity.pushforward_onChow_testZeroDivisor_of_isLift` — the Gysin map of
  the fibre at zero recovers the class from a lift.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

/-- In a cartesian square, the base change of a closed subscheme mapping isomorphically to the
base maps isomorphically to the base. -/
theorem isIso_comap_subschemeι_comp {P A T S' : Scheme.{u}} {ρ : P ⟶ A} {p : P ⟶ T}
    {F : A ⟶ S'} {G : T ⟶ S'} (hsq : IsPullback ρ p F G) (I : A.IdealSheafData)
    [IsIso (I.subschemeι ≫ F)] : IsIso ((I.comap ρ).subschemeι ≫ p) := by
  have h2 : IsPullback (pullback.snd ρ I.subschemeι) (pullback.fst ρ I.subschemeι ≫ p)
      (I.subschemeι ≫ F) G :=
    (IsPullback.of_hasPullback ρ I.subschemeι).flip.paste_vert hsq
  have : IsIso (pullback.fst ρ I.subschemeι ≫ p) := h2.isIso_snd_of_isIso
  rw [← Scheme.IdealSheafData.comapIso_hom_fst I ρ, Category.assoc]
  infer_instance

section Affine

variable (S : Scheme.{u})

/-- The zero section of `𝐀¹_S`. -/
abbrev affineZeroSection : S ⟶ affineLineOver S :=
  affineLineConstantSection S integralAffineZeroSection

/-- The zero section of `𝐀¹_S` is a section of the projection `𝐀¹_S ⟶ S`. -/
@[reassoc (attr := simp)]
theorem affineZeroSection_fst :
    affineZeroSection S ≫ pullback.fst (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) = 𝟙 S :=
  pullback.lift_fst _ _ _

/-- The zero section of `𝐀¹_S` followed by the projection to `𝐀¹_ℤ` is the zero point of `𝐀¹_ℤ`. -/
theorem affineZeroSection_snd :
    affineZeroSection S ≫ pullback.snd (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) =
        terminal.from S ≫ integralAffineZeroSection :=
  pullback.lift_snd _ _ _

/-- `D₀` meets the chart `𝐀¹_S` in the image of the zero section. -/
abbrev chartZeroDivisor : (affineLineOver S).IdealSheafData := (affineZeroSection S).ker

/-- The pullback of `D₀` along the chart `𝐀¹_S ⟶ 𝐏¹_S` is `chartZeroDivisor S`. -/
theorem comap_lineZeroDivisor_affineChart' :
    (lineZeroDivisor S).comap (affineChart S) = chartZeroDivisor S :=
  comap_lineZeroDivisor_affineChart S

/-- The image of the zero section of `𝐀¹_S` maps isomorphically to `S`. -/
instance isIso_chartZeroDivisor_over :
    IsIso ((chartZeroDivisor S).subschemeι ≫ pullback.fst (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) := by
  have h : IsIso (affineZeroSection S).toImage := inferInstance
  have hfac : (affineZeroSection S).toImage ≫ ((affineZeroSection S).imageι ≫
      pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) =
      𝟙 S := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, affineZeroSection_fst]
  have : IsIso ((affineZeroSection S).toImage ≫ ((affineZeroSection S).imageι ≫
      pullback.fst (terminal.from S)
        (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))) := by
    rw [hfac]
    infer_instance
  exact IsIso.of_isIso_comp_left (affineZeroSection S).toImage _

/-- The image of the zero section of `𝐀¹_S` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_chartZeroDivisor :
    Stacks.Divisors.IsEffectiveCartierDivisor (chartZeroDivisor S) := by
  rw [← comap_lineZeroDivisor_affineChart']
  exact Stacks.Divisors.isPullbackDefined_of_flat (affineChart S) (lineZeroDivisor S)
    (lineZeroDivisor_isEffectiveCartierDivisor S)

/-- The zero section of `𝐀¹_X` lies over the zero section of `𝐀¹_S`. -/
theorem affineZeroSection_comp_affineLineMap {X : Scheme.{u}} (f : X ⟶ S) :
    affineZeroSection X ≫ affineLineMap f = f ≫ affineZeroSection S := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, affineLineMap_fst, affineZeroSection_fst_assoc, Category.assoc,
      affineZeroSection_fst, Category.comp_id]
  · rw [Category.assoc, affineLineMap_snd, affineZeroSection_snd, Category.assoc,
      affineZeroSection_snd, ← Category.assoc, terminal.comp_from]

/-- The zero section of `𝐏¹_X` factors through the chart `𝐀¹_X`. -/
theorem affineZeroSection_comp_projectiveLineAffineChart {X : Scheme.{u}} (f : X ⟶ S) :
    affineZeroSection X ≫ projectiveLineAffineChart f = zeroSection f := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projectiveLineAffineChart_comp_fst, affineZeroSection_fst,
      zeroSection_comp_fst]
  · rw [Category.assoc, projectiveLineAffineChart_comp_snd, ← Category.assoc,
      affineZeroSection_comp_affineLineMap, Category.assoc,
      affineLineConstantSection_comp_affineChart,
      integralAffineZeroSection_comp_projectiveLineXChart, zeroSection_comp_snd]

end Affine

/-! ### The modification over the affine chart -/

section Modification

attribute [local instance] lineZeroDivisor_isEffectiveCartierDivisor

variable {X W S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)

/-- The map `b⁻¹(𝐀¹_X) ⟶ 𝐏¹_S` factors as `b⁻¹(𝐀¹_X) ≅ 𝐀¹_X ⟶ 𝐀¹_S ⟶ 𝐏¹_S`. -/
theorem chartInclusion_comp_lineMap :
    chartInclusion f b ≫ lineMap f b =
      pullback.snd b (projectiveLineAffineChart f) ≫ affineLineMap f ≫ affineChart S := by
  rw [lineMap, ← Category.assoc, pullback.condition, Category.assoc,
    projectiveLineAffineChart_comp_snd]

/-- If `b` is an isomorphism over `𝐀¹_X`, its fibre over the zero section maps isomorphically to
`X`. -/
instance isIso_modificationFibreAtZeroProjection
    [IsIso (pullback.snd b (projectiveLineAffineChart f))] :
    IsIso (modificationFibreAtZeroProjection f b) := by
  have key : ∀ (z : X ⟶ projectiveLineProduct f)
      (_ : z = affineZeroSection X ≫ projectiveLineAffineChart f), IsIso (pullback.snd b z) := by
    intro z hz
    subst hz
    have hh : pullback.snd b (affineZeroSection X ≫ projectiveLineAffineChart f) =
        (pullbackLeftPullbackSndIso b (projectiveLineAffineChart f) (affineZeroSection X)).inv ≫
          pullback.snd (pullback.snd b (projectiveLineAffineChart f)) (affineZeroSection X) := by
      rw [Iso.eq_inv_comp, pullbackLeftPullbackSndIso_hom_snd]
    rw [hh]
    have : IsIso (pullback.snd (pullback.snd b (projectiveLineAffineChart f))
        (affineZeroSection X)) :=
      (IsPullback.of_hasPullback (pullback.snd b (projectiveLineAffineChart f))
        (affineZeroSection X)).isIso_snd_of_isIso
    infer_instance
  exact key _ (affineZeroSection_comp_projectiveLineAffineChart S f).symm

/-- The section at zero of `W ⟶ X` is a section of the projection `W ⟶ X`. -/
theorem modificationSectionAtZero_comp
    [IsIso (pullback.snd b (projectiveLineAffineChart f))] :
    modificationSectionAtZero f b inferInstance ≫ modificationProjection f b = 𝟙 X := by
  rw [modificationSectionAtZero, modificationProjection, Category.assoc,
    ← Category.assoc (pullback.fst b (zeroSection f)), pullback.condition, Category.assoc,
    zeroSection_comp_fst, Category.comp_id, IsIso.inv_hom_id]

/-- `U ×_X T` is `T ×_S 𝐀¹_S`. -/
theorem isPullback_openTest [IsIso (pullback.snd b (projectiveLineAffineChart f))] {T : Scheme.{u}}
    (g : T ⟶ X) :
    IsPullback (pullback.fst (chartInclusion f b ≫ modificationProjection f b) g ≫
        pullback.snd b (projectiveLineAffineChart f) ≫ affineLineMap f)
      (pullback.snd (chartInclusion f b ≫ modificationProjection f b) g)
      (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (g ≫ f) := by
  have h1 : IsPullback (pullback.snd b (projectiveLineAffineChart f))
      (chartInclusion f b ≫ modificationProjection f b)
      (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, chartInclusion_comp_modificationProjection]⟩
  have h2 := h1.paste_horiz (isPullback_affineLineMap f)
  rw [Category.id_comp] at h2
  exact (IsPullback.of_hasPullback _ g).paste_horiz h2

end Modification

/-! ### The Gysin map of the fibre at zero -/

section ZeroGysin

attribute [local instance] lineZeroDivisor_isEffectiveCartierDivisor
  lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  [IsIso (pullback.snd b (projectiveLineAffineChart f))]
  {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t]

/-- The map `U ×_X T ⟶ W`. -/
abbrev openToW : pullback (chartInclusion f b ≫ modificationProjection f b) t ⟶ W :=
  openBaseChange (modificationProjection f b) (chartInclusion f b) t ≫
    pullback.fst (modificationProjection f b) t

/-- The fibre at zero on `U ×_X T`. -/
abbrev openZeroDivisor := gysinTripleDivisor (zeroModule f b) (zeroSectionOnW f b) (openToW C f b t)

/-- The fibre at zero on `W ×_X T`. -/
abbrev testZeroDivisor :=
  gysinTripleDivisor (zeroModule f b) (zeroSectionOnW f b)
    (pullback.fst (modificationProjection f b) t)

omit [LocallyOfFiniteType f] [IsProper b] [IsIso (pullback.snd b (projectiveLineAffineChart f))]
  [LocallyOfFiniteType t] in
/-- The fibre at zero on `U ×_X T` is the pullback of the image of the zero section of `𝐀¹_S` along
`U ×_X T ⟶ 𝐀¹_S`. -/
theorem openZeroDivisor_eq :
    openZeroDivisor C f b t = (chartZeroDivisor C.S).comap
      (pullback.fst (chartInclusion f b ≫ modificationProjection f b) t ≫
        pullback.snd b (projectiveLineAffineChart f) ≫ affineLineMap f) := by
  have h : openToW C f b t ≫ lineMap f b =
      (pullback.fst (chartInclusion f b ≫ modificationProjection f b) t ≫
        pullback.snd b (projectiveLineAffineChart f) ≫ affineLineMap f) ≫ affineChart C.S := by
    rw [openToW, Category.assoc, openBaseChange_fst_assoc, chartInclusion_comp_lineMap]
    simp only [Category.assoc]
  rw [openZeroDivisor, gysinTripleDivisor, Stacks.Divisors.zeroScheme_pullback,
    zeroScheme_zeroSectionOnW, ← Scheme.IdealSheafData.comap_comp, h,
    Scheme.IdealSheafData.comap_comp, comap_lineZeroDivisor_affineChart']

/-- The fibre at zero on `U ×_X T` maps isomorphically to `T`. -/
instance isIso_openZeroDivisor :
    IsIso ((openZeroDivisor C f b t).subschemeι ≫
      pullback.snd (chartInclusion f b ≫ modificationProjection f b) t) := by
  rw [openZeroDivisor_eq C f b t]
  exact isIso_comap_subschemeι_comp (isPullback_openTest f b t) _

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType t] in
/-- The fibre at zero on `U ×_X T` is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_openZeroDivisor :
    Stacks.Divisors.IsEffectiveCartierDivisor (openZeroDivisor C f b t) := by
  rw [openZeroDivisor_eq C f b t]
  have hsq := (isPullback_openTest f b t).flip
  rw [← hsq.isoPullback_hom_snd, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (isEffectiveCartierDivisor_comap_pullback _ _ _ (isEffectiveCartierDivisor_chartZeroDivisor _))

/-- The section at zero `T ⟶ W ×_X T`: the inverse of the projection of the fibre at zero,
followed by its inclusion. -/
def zeroFibreSection : T ⟶ pullback (modificationProjection f b) t :=
  inv ((openZeroDivisor C f b t).subschemeι ≫
      pullback.snd (chartInclusion f b ≫ modificationProjection f b) t) ≫
    (openZeroDivisor C f b t).subschemeι ≫
      openBaseChange (modificationProjection f b) (chartInclusion f b) t

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType t] in
/-- The section at zero is a section of the projection `W ×_X T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem zeroFibreSection_snd :
    zeroFibreSection C f b t ≫ pullback.snd (modificationProjection f b) t = 𝟙 T := by
  rw [zeroFibreSection, Category.assoc, Category.assoc, openBaseChange_snd, IsIso.inv_hom_id]

/-- The section at zero `T ⟶ W ×_X T` is a closed immersion. -/
instance isClosedImmersion_zeroFibreSection :
    IsClosedImmersion (zeroFibreSection C f b t) := by
  have hsep : IsSeparated (pullback.snd (modificationProjection f b) t) := by
    have : IsSeparated (modificationProjection f b) := inferInstance
    infer_instance
  have : IsClosedImmersion (zeroFibreSection C f b t ≫ pullback.snd (modificationProjection f b) t)
      := by
    rw [zeroFibreSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.snd (modificationProjection f b) t)

/-- Stacks 02TR, first equality, for a section given as a global section. -/
theorem gysinHomomorphismOfInvertible_flatPullback_divisor_section {Y Y' : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (p : Y ⟶ Y') [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY' = sY) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) :
    ∀ [Flat ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ p)]
      (_hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
        (Stacks.Divisors.zeroScheme Y L σ))
      (hq : AlgebraicGeometry.RelativeDimension
        ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ p) r)
      (hcast : k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1) (α : CycleGroup C sY' (k + 1)),
      gysinHomomorphismOfInvertible C sY (k + 1 + (r : ℤ)) L σ
          (hcast ▸ flatPullback C sY sY' p hbase (r + 1) hp (k + 1) α) =
        QuotientAddGroup.mk
          (flatPullback C ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ sY) sY'
            ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ p)
            (by rw [Category.assoc, hbase]) r hq (k + 1) α) := by
  rw [← Stacks.Divisors.sectionsOfTop_eval_top L σ]
  intro _ hD hq hcast α
  exact gysinHomomorphismOfInvertible_flatPullback_divisor C sY sY' p hbase r hp k L
    (Stacks.Divisors.sectionsOfTop L σ) hD hq hcast α

/-- The module of the fibre at zero on `U ×_X T`. -/
abbrev openZeroModule : (pullback (chartInclusion f b ≫ modificationProjection f b) t).Modules :=
  (Scheme.Modules.pullback (openToW C f b t)).obj (zeroModule f b)

/-- The section of the fibre at zero on `U ×_X T`. -/
abbrev openZeroSection : Γ(openZeroModule C f b t, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (openToW C f b t) _ (zeroSectionOnW f b)

/-- The projection `U ×_X T ⟶ T`. -/
abbrev openSnd : pullback (chartInclusion f b ≫ modificationProjection f b) t ⟶ T :=
  pullback.snd (chartInclusion f b ≫ modificationProjection f b) t

/-- Two cycles of possibly different dimensions, with equal underlying cycles, are heterogeneously
equal. -/
theorem cycleGroup_heq_of_val_eq {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    {i i' : ℤ} (h : i = i') {a : CycleGroup C q i} {a' : CycleGroup C q i'} (ha : a.1 = a'.1) :
    a ≍ a' := by
  subst h
  exact heq_of_eq (Subtype.ext ha)

/-- Heterogeneously equal cycles have heterogeneously equal Chow classes. -/
theorem chowGroup_mk_heq {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    {i i' : ℤ} (h : i = i') {a : CycleGroup C q i} {a' : CycleGroup C q i'} (ha : a ≍ a') :
    (QuotientAddGroup.mk' (rationalEquivalences C q i) a : chowGroup C q i) ≍
      (QuotientAddGroup.mk' (rationalEquivalences C q i') a' : chowGroup C q i') := by
  subst h
  rw [eq_of_heq ha]

/-- Cycles with equal underlying cycles have heterogeneously equal Chow classes. -/
theorem chowGroup_mk_heq_mk' {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    {i i' : ℤ} (h : i = i') {a : CycleGroup C q i} {a' : CycleGroup C q i'} (ha : a.1 = a'.1) :
    (QuotientAddGroup.mk a : chowGroup C q i) ≍
      (QuotientAddGroup.mk' (rationalEquivalences C q i') a' : chowGroup C q i') := by
  subst h
  rw [Subtype.ext ha]
  rfl

/-- Flat pullback along an isomorphism `e` agrees with proper pushforward along `e⁻¹`. -/
theorem flatPullback_val_eq_of_isIso {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : A ⟶ B) [IsIso e] [LocallyOfFiniteType e]
    [Flat e] (he : e ≫ sB = sA) (hr : AlgebraicGeometry.RelativeDimension e 0) (k : ℤ)
    (c : CycleGroup C sB k) :
    (flatPullback C sA sB e he 0 hr k c).1 =
      (properPushforward C sB sA (inv e) (by rw [IsIso.inv_comp_eq, he]) k c).1 := by
  rw [← cycleGroupRestrict_eq_flatPullback, cycleGroupRestrict_of_isIso]

/-- The Gysin map of an invertible module with a section sends heterogeneously equal cycles to
heterogeneously equal classes. -/
theorem gysinHomomorphismOfInvertible_heq {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (σ : Γ(M, ⊤)) {i i' : ℤ} (h : i = i') {a : CycleGroup C q (i + 1)}
    {a' : CycleGroup C q (i' + 1)} (ha : a ≍ a') :
    gysinHomomorphismOfInvertible C q i M σ a ≍ gysinHomomorphismOfInvertible C q i' M σ a' := by
  subst h
  rw [eq_of_heq ha]

/-- Stacks 02TR for a relative effective Cartier divisor mapping isomorphically to the base: the
Gysin map undoes flat pullback, up to the identification of the divisor with the base. -/
theorem gysinHomomorphismOfInvertible_flatPullback_heq_of_isIso {Y Y' : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (p : Y ⟶ Y') [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY' = sY)
    (hp : AlgebraicGeometry.RelativeDimension p 1) (k : ℤ) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (σ : Γ(L, ⊤)) [IsIso ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme Y L σ))
    (α : CycleGroup C sY' (k + 1)) :
    gysinHomomorphismOfInvertible C sY (k + 1) L σ (flatPullback C sY sY' p hbase 1 hp (k + 1) α) ≍
      (QuotientAddGroup.mk' (rationalEquivalences C ((Stacks.Divisors.zeroScheme Y L σ).subschemeι
          ≫ sY) (k + 1))
        (properPushforward C sY' ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ sY)
          (inv ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ p))
          (by rw [IsIso.inv_comp_eq, Category.assoc, hbase]) (k + 1) α) :
        chowGroup C ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ sY) (k + 1)) := by
  have hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme Y L σ).subschemeι ≫ p) 0 := relativeDimension_of_isIso _
  have h02 := gysinHomomorphismOfInvertible_flatPullback_divisor_section C sY sY' p hbase 0 hp k
    L σ ⟨hD, inferInstance⟩ hq (by push_cast; ring) α
  refine HEq.trans ?_ ((heq_of_eq h02).trans ?_)
  · exact gysinHomomorphismOfInvertible_heq C _ _ _ (by simp)
      (cycleGroup_heq_of_val_eq C _ (by push_cast; ring) (val_cycleGroup_cast C _ _ _).symm)
  · exact chowGroup_mk_heq_mk' C _ (by simp) (flatPullback_val_eq_of_isIso C _ _ _ _ hq (k + 1) α)

/-- **Stacks 02TR on the open part.** On `U ×_X T ≅ 𝐀¹_T` the Gysin map of the fibre at zero
undoes flat pullback from `T`: the fibre at zero is a relative effective Cartier divisor mapping
isomorphically to `T`. -/
theorem onChow_openZeroDivisor_flatPullbackChow (k : ℤ) (α : chowGroup C (t ≫ f) k) :
    (gysinSystemOfInvertible C).onChow (openStr C f (modificationProjection f b)
        (chartInclusion f b) t)
        ((Scheme.Modules.pullback (openToW C f b t)).obj (zeroModule f b))
        (AlgebraicGeometry.pullbackGlobalSections (openToW C f b t) _ (zeroSectionOnW f b)) k
        (flatPullbackChow C (openStr C f (modificationProjection f b) (chartInclusion f b) t)
          (t ≫ f) (pullback.snd (chartInclusion f b ≫ modificationProjection f b) t) rfl 1
          (relativeDimension_openSnd (modificationProjection f b) (chartInclusion f b)
            (relativeDimension_chartInclusion_comp f b) t) k
          (flatPullbackDescends C _ _ _ _ _ _ _) α) =
      chowPushforwardOfIso C (t ≫ f) ((openZeroDivisor C f b t).subschemeι ≫
          openStr C f (modificationProjection f b) (chartInclusion f b) t)
        (inv ((openZeroDivisor C f b t).subschemeι ≫
          pullback.snd (chartInclusion f b ≫ modificationProjection f b) t))
        (by rw [IsIso.inv_comp_eq, Category.assoc]) k α := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by ring⟩
  have hrel := relativeDimension_openSnd (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) t
  have : Flat ((openZeroDivisor C f b t).subschemeι ≫ openSnd C f b t) := inferInstance
  have hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor (openSnd C f b t)
      (openZeroDivisor C f b t) :=
    ⟨isEffectiveCartierDivisor_openZeroDivisor C f b t, inferInstance⟩
  have hq : AlgebraicGeometry.RelativeDimension
      ((openZeroDivisor C f b t).subschemeι ≫ openSnd C f b t) 0 :=
    relativeDimension_of_isIso _
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have hmk : (QuotientAddGroup.mk a : chowGroup C (t ≫ f) (k' + 1)) =
        QuotientAddGroup.mk' (rationalEquivalences C (t ≫ f) (k' + 1)) a := rfl
    have hfp : flatPullbackChow C (openStr C f (modificationProjection f b) (chartInclusion f b) t)
        (t ≫ f) (openSnd C f b t) rfl 1 hrel (k' + 1) (flatPullbackDescends C _ _ _ _ _ _ _)
        (QuotientAddGroup.mk' (rationalEquivalences C (t ≫ f) (k' + 1)) a) =
        QuotientAddGroup.mk' (rationalEquivalences C
          (openStr C f (modificationProjection f b) (chartInclusion f b) t) (k' + 1 + 1))
          (flatPullback C (openStr C f (modificationProjection f b) (chartInclusion f b) t)
            (t ≫ f) (openSnd C f b t) rfl 1 hrel (k' + 1) a) :=
      flatPullbackChow_mk C _ _ _ rfl 1 hrel (k' + 1) _ a
    rw [hmk, hfp, GysinSystem.onChow_mk, chowPushforwardOfIso_mk]
    exact eq_of_heq (gysinHomomorphismOfInvertible_flatPullback_heq_of_isIso C _ _
      (openSnd C f b t) rfl hrel k' (openZeroModule C f b t) (openZeroSection C f b t)
      (isEffectiveCartierDivisor_openZeroDivisor C f b t) a)

omit [IsProper b] [IsIso (pullback.snd b (projectiveLineAffineChart f))] in
omit [LocallyOfFiniteType f] [LocallyOfFiniteType t] in
/-- The fibre at zero lies in the open part. -/
theorem range_testZeroDivisor_subset :
    Set.range (testZeroDivisor C f b t).subschemeι.base ⊆
      Set.range (openBaseChange (modificationProjection f b) (chartInclusion f b) t).base := by
  intro z hz
  rw [range_openBaseChange, Set.mem_preimage]
  have hcompl := range_zeroScheme_infinitySectionOnW f b
  rw [← compl_compl (Set.range (chartInclusion f b).base), ← hcompl]
  intro hinf
  rw [Scheme.IdealSheafData.range_subschemeι, testZeroDivisor, gysinTripleDivisor,
    Stacks.Divisors.zeroScheme_pullback, Scheme.IdealSheafData.support_comap] at hz
  change (pullback.fst (modificationProjection f b) t).base z ∈
    ((Stacks.Divisors.zeroScheme W (zeroModule f b) (zeroSectionOnW f b)).support : Set W) at hz
  rw [zeroScheme_zeroSectionOnW, Scheme.IdealSheafData.support_comap] at hz
  rw [Scheme.IdealSheafData.range_subschemeι, zeroScheme_infinitySectionOnW,
    Scheme.IdealSheafData.support_comap] at hinf
  exact Set.disjoint_left.mp (disjoint_support_lineZeroDivisor_lineInfinityDivisor C.S) hz hinf

/-- The open immersion of the fibre at zero of `U ×_X T` into that of `W ×_X T`. -/
abbrev zeroFibreRestrictMap :=
  zeroSchemeRestrictMap (openToW C f b t) (pullback.fst (modificationProjection f b) t)
    (openBaseChange (modificationProjection f b) (chartInclusion f b) t) rfl (zeroModule f b)
    (zeroSectionOnW f b)

/-- The fibre at zero of `U ×_X T` is isomorphic to that of `W ×_X T`. -/
instance isIso_zeroFibreRestrictMap : IsIso (zeroFibreRestrictMap C f b t) := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨?_⟩⟩
  have hsnd : Function.Surjective (pullback.snd
      (openBaseChange (modificationProjection f b) (chartInclusion f b) t)
      (testZeroDivisor C f b t).subschemeι).base := by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Set.preimage_eq_univ_iff]
    exact range_testZeroDivisor_subset C f b t
  rw [zeroFibreRestrictMap, zeroSchemeRestrictMap, comapSubschemeMap]
  rw [Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp]
  exact (hsnd.comp (Scheme.Hom.surjective _)).comp (Scheme.Hom.surjective _)

/-- For an isomorphism `e`, pushforward along `e` inverts restriction along `e` on Chow groups. -/
theorem chowPushforwardOfIso_chowGroupRestrict {A B : Scheme.{u}} (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (e : B ⟶ A) [IsIso e]
    (he : e ≫ sA = sB) (k : ℤ) (x : chowGroup C sA k) :
    chowPushforwardOfIso C sB sA e he k (chowGroupRestrict C sA sB e he k x) = x := by
  rw [chowGroupRestrict_of_isIso]
  exact (chowGroupEquivOfIso C sB sA e he k).right_inv x

omit [LocallyOfFiniteType f] [IsProper b] [IsIso (pullback.snd b (projectiveLineAffineChart f))]
  [LocallyOfFiniteType t] in
/-- The inclusion of the fibre at zero of `U ×_X T` into `W ×_X T` factors through the fibre at
zero of `W ×_X T`. -/
theorem zeroFibreRestrictMap_comp_subschemeι :
    zeroFibreRestrictMap C f b t ≫ (testZeroDivisor C f b t).subschemeι =
      (openZeroDivisor C f b t).subschemeι ≫
        openBaseChange (modificationProjection f b) (chartInclusion f b) t :=
  zeroSchemeRestrictMap_comp_subschemeι _ _ _ _ _ _

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType t] in
/-- The section at zero `T ⟶ W ×_X T` lies over `S`. -/
theorem zeroFibreSection_comp_testStr :
    zeroFibreSection C f b t ≫ testStr C f (modificationProjection f b) t = t ≫ f := by
  rw [testStr, ← Category.assoc, ← Category.assoc, Category.assoc (zeroFibreSection C f b t),
    pullback.condition, ← Category.assoc, zeroFibreSection_snd, Category.id_comp]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType t] in
/-- The section at zero factors through the fibre at zero of `W ×_X T`. -/
theorem zeroFibreSection_eq :
    inv ((openZeroDivisor C f b t).subschemeι ≫ openSnd C f b t) ≫ zeroFibreRestrictMap C f b t ≫
      (testZeroDivisor C f b t).subschemeι = zeroFibreSection C f b t := by
  rw [zeroFibreRestrictMap_comp_subschemeι, zeroFibreSection]

/-- **The fibre at zero recovers the class from a lift**: for a lift `β` of `α`, the Gysin map of
the fibre at zero sends `β` to `α`, read on `W ×_X T` through the section at zero. This is the
step `i_0^* β = α` of Stacks 0F9J, from Stacks 02TR on `U ×_X T ≅ 𝐀¹_T`. -/
theorem pushforward_onChow_testZeroDivisor_of_isLift {k : ℤ} {α : chowGroup C (t ≫ f) k}
    {β : chowGroup C (testStr C f (modificationProjection f b) t) (k + 1)}
    (hl : IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) t k α β) :
    chowPushforwardOfIsClosedImmersion C ((testZeroDivisor C f b t).subschemeι ≫
        testStr C f (modificationProjection f b) t) (testStr C f (modificationProjection f b) t)
        (testZeroDivisor C f b t).subschemeι rfl k
        ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) t)
          (gysinTripleModule (zeroModule f b) (pullback.fst (modificationProjection f b) t))
          (gysinTripleSection (zeroModule f b) (zeroSectionOnW f b)
            (pullback.fst (modificationProjection f b) t)) k β) =
      properChowPushforward C (t ≫ f) (testStr C f (modificationProjection f b) t)
        (zeroFibreSection C f b t)
        (zeroFibreSection_comp_testStr C f b t) k
        (properPushforwardDescends C _ _ _ _ _) α := by
  have := isOpenImmersion_openBaseChange (modificationProjection f b) (chartInclusion f b) t
  have hj : zeroFibreRestrictMap C f b t ≫ ((testZeroDivisor C f b t).subschemeι ≫
      testStr C f (modificationProjection f b) t) =
      (openZeroDivisor C f b t).subschemeι ≫
        openStr C f (modificationProjection f b) (chartInclusion f b) t := by
    rw [← Category.assoc (zeroFibreRestrictMap C f b t), zeroFibreRestrictMap_comp_subschemeι,
      Category.assoc ((openZeroDivisor C f b t).subschemeι),
      openBaseChange_comp_testStr C f (modificationProjection f b) (chartInclusion f b) t]
  have : IsOpenImmersion (zeroFibreRestrictMap C f b t) := inferInstance
  have e2 := GysinSystem.onChow_openImmersion
    (gysinSystemOfInvertible_isNaturalUnderOpenImmersion C) (modificationProjection f b ≫ f)
    (openToW C f b t) (pullback.fst (modificationProjection f b) t)
    (openStr C f (modificationProjection f b) (chartInclusion f b) t)
    (testStr C f (modificationProjection f b) t)
    (openBaseChange_comp_testStr C f (modificationProjection f b) (chartInclusion f b) t)
    rfl (openBaseChange (modificationProjection f b) (chartInclusion f b) t) rfl
    (zeroModule f b) (zeroSectionOnW f b) k (zeroFibreRestrictMap C f b t)
    (zeroFibreRestrictMap_comp_subschemeι C f b t) hj
    (openBaseChange_comp_testStr C f (modificationProjection f b) (chartInclusion f b) t) β
  unfold IsLift at hl
  have e3 := e2.trans ((congrArg _ hl).trans (onChow_openZeroDivisor_flatPullbackChow C f b t k α))
  have e4 := (chowPushforwardOfIso_chowGroupRestrict C _ _ (zeroFibreRestrictMap C f b t) hj k
    _).symm.trans (congrArg (chowPushforwardOfIso C _ _ (zeroFibreRestrictMap C f b t) hj k) e3)
  refine (congrArg _ e4).trans ?_
  have hc1 := properChowPushforward_comp_apply C (t ≫ f)
    ((openZeroDivisor C f b t).subschemeι ≫
      openStr C f (modificationProjection f b) (chartInclusion f b) t)
    ((testZeroDivisor C f b t).subschemeι ≫ testStr C f (modificationProjection f b) t)
    (inv ((openZeroDivisor C f b t).subschemeι ≫ openSnd C f b t))
    (zeroFibreRestrictMap C f b t)
    (inv ((openZeroDivisor C f b t).subschemeι ≫ openSnd C f b t) ≫ zeroFibreRestrictMap C f b t)
    rfl (by rw [IsIso.inv_comp_eq, Category.assoc]) hj
    (by rw [Category.assoc, hj, IsIso.inv_comp_eq, Category.assoc]) k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) α
  have hc2 := properChowPushforward_comp_apply C (t ≫ f)
    ((testZeroDivisor C f b t).subschemeι ≫ testStr C f (modificationProjection f b) t)
    (testStr C f (modificationProjection f b) t)
    (inv ((openZeroDivisor C f b t).subschemeι ≫ openSnd C f b t) ≫ zeroFibreRestrictMap C f b t)
    (testZeroDivisor C f b t).subschemeι (zeroFibreSection C f b t)
    (by rw [Category.assoc]; exact zeroFibreSection_eq C f b t)
    (by rw [Category.assoc, hj, IsIso.inv_comp_eq, Category.assoc]) rfl
    (zeroFibreSection_comp_testStr C f b t) k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) α
  exact (congrArg _ hc1.symm).trans hc2.symm

end ZeroGysin

end GysinAtInfinity

end Stacks.Chow

end

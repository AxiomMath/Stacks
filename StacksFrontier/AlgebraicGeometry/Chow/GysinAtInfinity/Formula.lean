module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ZeroFibre
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.ChernComparison

/-!
# The class at infinity: its construction and its pushforward identity

For the class `C ∈ A⁰(W_∞ ⟶ X)` of a modification `b : W ⟶ 𝐏¹_X`, this file proves that
`C ∩ α = i_∞^* β` for every lift `β` of `α`, and that `i_{∞,*}(C ∩ α) = i_{0,*} α` on every test
scheme: by Stacks 02T9 both sides are first Chern classes capped with `β`, of the pullbacks of
`𝒪(D_∞)` and `𝒪(D_0)`, which agree on Chow groups, and `i_0^* β = α`.

## Main results

* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_cap_eq_of_isLift` — the construction.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass_pushforward` — the pushforward identity.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

namespace GysinAtInfinity

section Instances

variable {X W S T : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f) (g : T ⟶ X)

/-- The base change `W_∞ ×_X T ⟶ W ×_X T` of the inclusion `W_∞ ⟶ W` and the first projections
to `W_∞` and `W` form a pullback square. -/
theorem isPullback_modificationInfinityBaseChange :
    IsPullback (pullback.fst (modificationProjectionAtInfinity f b) g)
      (modificationInfinityBaseChange f b g) (modificationInclusionAtInfinity f b)
      (pullback.fst (modificationProjection f b) g) := by
  refine IsPullback.of_bot ?_ (modificationInfinityBaseChange_comp_fst f b g).symm
    (IsPullback.of_hasPullback (modificationProjection f b) g)
  rw [modificationInfinityBaseChange_comp_snd]
  exact IsPullback.of_hasPullback (modificationProjectionAtInfinity f b) g

/-- The base change `W_∞ ×_X T ⟶ W ×_X T` of the fibre at infinity is a closed immersion. -/
instance isClosedImmersion_modificationInfinityBaseChange :
    IsClosedImmersion (modificationInfinityBaseChange f b g) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_modificationInfinityBaseChange f b g) inferInstance

/-- The base change `T ⟶ W ×_X T` of the section at zero is proper. -/
instance isProper_modificationSectionAtZeroBaseChange [IsProper b]
    (h : IsIso (modificationFibreAtZeroProjection f b))
    (hzero : modificationSectionAtZero f b h ≫ modificationProjection f b = 𝟙 X) :
    IsProper (modificationSectionAtZeroBaseChange f b h hzero g) := by
  have : IsSeparated (pullback.snd (modificationProjection f b) g) := inferInstance
  have : IsClosedImmersion (modificationSectionAtZeroBaseChange f b h hzero g ≫
      pullback.snd (modificationProjection f b) g) := by
    rw [modificationSectionAtZeroBaseChange_comp_snd]
    infer_instance
  have : IsClosedImmersion (modificationSectionAtZeroBaseChange f b h hzero g) :=
    IsClosedImmersion.of_comp _ (pullback.snd (modificationProjection f b) g)
  infer_instance

end Instances

section ZeroSection

variable {X W S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)

/-- The zero section `X ⟶ b⁻¹(𝐀¹_X)`. -/
abbrev chartZeroSection [IsIso (pullback.snd b (projectiveLineAffineChart f))] :
    X ⟶ chartOpen f b :=
  affineZeroSection X ≫ inv (pullback.snd b (projectiveLineAffineChart f))

/-- When `b` is an isomorphism over `𝐀¹_X`, the section at zero `X ⟶ W` is the zero section into
`b⁻¹(𝐀¹_X)` followed by the inclusion of `b⁻¹(𝐀¹_X)` in `W`. -/
theorem modificationSectionAtZero_eq [IsIso (pullback.snd b (projectiveLineAffineChart f))] :
    modificationSectionAtZero f b inferInstance = chartZeroSection f b ≫ chartInclusion f b := by
  have key : ∀ (z : X ⟶ projectiveLineProduct f) (_ : z = affineZeroSection X ≫
      projectiveLineAffineChart f) [IsIso (pullback.snd b z)],
      inv (pullback.snd b z) ≫ pullback.fst b z = chartZeroSection f b ≫ chartInclusion f b := by
    intro z hz _
    subst hz
    rw [IsIso.inv_comp_eq,
      ← cancel_epi (pullbackLeftPullbackSndIso b (projectiveLineAffineChart f)
        (affineZeroSection X)).hom,
      pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
    have h1 : pullback.fst (pullback.snd b (projectiveLineAffineChart f)) (affineZeroSection X) =
        pullback.snd (pullback.snd b (projectiveLineAffineChart f)) (affineZeroSection X) ≫
          affineZeroSection X ≫ inv (pullback.snd b (projectiveLineAffineChart f)) := by
      rw [← Category.assoc, IsIso.eq_comp_inv, pullback.condition]
    rw [h1]
    simp only [Category.assoc]
  exact key _ (affineZeroSection_comp_projectiveLineAffineChart S f).symm

/-- The image of the zero section of `𝐀¹_S` lies over `0 ∈ 𝐀¹_ℤ`. -/
theorem chartZeroDivisor_subschemeι_snd :
    (chartZeroDivisor S).subschemeι ≫ pullback.snd (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      terminal.from _ ≫ integralAffineZeroSection := by
  have h : (chartZeroDivisor S).subschemeι =
      inv (affineZeroSection S).toImage ≫ affineZeroSection S := by
    rw [IsIso.eq_inv_comp, Scheme.Hom.toImage_imageι]
  rw [h, Category.assoc, affineZeroSection_snd, ← Category.assoc, terminal.comp_from]

/-- If `J` is the pullback of the zero divisor of `𝐀¹_S` along `ρ : P ⟶ 𝐀¹_S`, then the composite
`V(J) ⟶ P ⟶ 𝐀¹_S ⟶ 𝐀¹_ℤ` factors through `0 ∈ 𝐀¹_ℤ`. -/
theorem comap_chartZeroDivisor_subschemeι_snd {P : Scheme.{u}} (ρ : P ⟶ affineLineOver S)
    (J : P.IdealSheafData) (hJ : J = (chartZeroDivisor S).comap ρ) :
    J.subschemeι ≫ ρ ≫ pullback.snd (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      terminal.from _ ≫ integralAffineZeroSection := by
  subst hJ
  rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc,
    chartZeroDivisor_subschemeι_snd]
  simp only [← Category.assoc, terminal.comp_from]

end ZeroSection

section Formula

attribute [local instance] lineZeroDivisor_isEffectiveCartierDivisor
  lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The normal bundle of `W_0` is trivial: Stacks 0F93 pulled back. -/
theorem isTrivial_zeroModule :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme W (zeroModule f b) (zeroSectionOnW f b)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme W (zeroModule f b) (zeroSectionOnW f
          b)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W (zeroModule f b)
        (zeroSectionOnW f b)).subschemeι).obj (zeroModule f b)) := by
  refine Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections (lineMap f b) _ _ ?_
  rw [zeroScheme_lineZeroDivisor]
  exact isTrivial_pullback_divisorSheaf_lineZeroDivisor C.S

/-- The fibre at infinity on `W ×_X T`, as the zero scheme of the pulled-back section. -/
abbrev testInfinityDivisor :=
  gysinTripleDivisor (infinityModule f b) (infinitySectionOnW f b)
    (pullback.fst (modificationProjection f b) g)

/-- The identification of the zero scheme `Z(b^* 1_{D_∞})` on `W ×_X T` with `W_∞ ×_X T`. -/
def testInfinityIso :
    (testInfinityDivisor C f b g).subscheme ⟶ pullback (modificationProjectionAtInfinity f b) g :=
  (gysinDivisorBaseChangeIso (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) g)).hom ≫
    (pullbackRightPullbackFstIso (modificationProjection f b) g
      (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b))).hom ≫
    (transportPullbackIso
      (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
        modificationProjection f b)
      (modificationProjectionAtInfinity f b) (infinityIso f b)
      (infinityIso_hom_comp_modificationProjectionAtInfinity C f b) g).hom

/-- The identification `testInfinityIso` is an isomorphism. -/
instance isIso_testInfinityIso : IsIso (testInfinityIso C f b g) := by
  unfold testInfinityIso
  infer_instance

omit [LocallyOfFiniteType f] [IsProper b] in
omit [LocallyOfFiniteType g] in
/-- Read on `W ×_X T`, the identification is the inclusion of the zero scheme. -/
theorem testInfinityIso_comp_modificationInfinityBaseChange :
    testInfinityIso C f b g ≫ modificationInfinityBaseChange f b g =
      (testInfinityDivisor C f b g).subschemeι := by
  rw [testInfinityIso]
  refine pullback.hom_ext ?_ ?_
  · simpa [modificationInfinityBaseChange_comp_fst, infinityIso_hom_comp] using
      gysinDivisorBaseChangeIso_hom_comp_test _ _ _
  · simp [modificationInfinityBaseChange_comp_snd]

omit [LocallyOfFiniteType f] [IsProper b] in
omit [LocallyOfFiniteType g] in
/-- The identification `testInfinityIso` is compatible with the structure morphisms to `S`. -/
theorem testInfinityIso_comp_structure :
    testInfinityIso C f b g ≫ (pullback.fst (modificationProjectionAtInfinity f b) g ≫
        (modificationProjectionAtInfinity f b ≫ f)) =
      (testInfinityDivisor C f b g).subschemeι ≫ testStr C f (modificationProjection f b) g := by
  rw [← testInfinityIso_comp_modificationInfinityBaseChange C f b g, testStr,
    Category.assoc (testInfinityIso C f b g),
    ← Category.assoc (modificationInfinityBaseChange f b g),
    modificationInfinityBaseChange_comp_fst]
  simp only [Category.assoc]

/-- **The construction of Stacks 0F9J.** For every lift `β ∈ A_{k+1}(W ×_X T)` of
`α ∈ A_k(T)` — a class whose restriction to `b⁻¹(𝐀¹_X) ×_X T` is the flat pullback of `α` — the
class at infinity caps `α` to the Gysin image `i_∞^* β` of `β`, read on `W_∞ ×_X T`. -/
theorem gysinAtInfinityClass_cap_eq_of_isLift {k : ℤ} {α : chowGroup C (g ≫ f) k}
    {β : chowGroup C (testStr C f (modificationProjection f b) g) (k + 1)}
    (hβ : IsLift C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) g k α β) :
    (gysinAtInfinityClass C f b hA).cap g k α =
      chowGroupDegreeEquiv C _ (sub_zero k).symm
        (chowPushforwardOfIso C ((testInfinityDivisor C f b g).subschemeι ≫
            testStr C f (modificationProjection f b) g)
          (pullback.fst (modificationProjectionAtInfinity f b) g ≫
            (modificationProjectionAtInfinity f b ≫ f)) (testInfinityIso C f b g)
          (testInfinityIso_comp_structure C f b g) k
          ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
            (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
            (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
              (pullback.fst (modificationProjection f b) g)) k β)) := by
  have := hA
  show chowPushforwardOfIso C _ _ _ _ (k - 0)
    (infinityCap C f (modificationProjection f b) (chartInclusion f b)
      (relativeDimension_chartInclusion_comp f b) (infinityModule f b) (infinitySectionOnW f b)
      (range_zeroScheme_infinitySectionOnW f b) (isTrivial_infinityModule f b) g k α) = _
  rw [infinityCap_eq_of_isLift C f _ _ _ _ _ _ _ hβ, divisorMiddleCap, middleCap_apply,
    (gysinBivariantClass C (modificationProjection f b ≫ f) (infinityModule f b)
      (infinitySectionOnW f b)).2, gysinBivariantCap_apply]
  apply eq_of_heq
  refine HEq.trans (properChowPushforward_heq C _ _ _ _ (by ring : k - 0 = k + 1 - 1) _
    (properPushforwardDescends C _ _ _ _ _) (chowGroupDegreeEquiv_heq C _ _ _)) ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq C _ _ _).symm
  rw [← properChowPushforward_comp_apply C _ _ _ _ _ _ rfl _ _
      (by rw [Category.assoc, transportPullbackIso_hom_comp_base C
          (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
            (modificationProjection f b ≫ f)) (modificationProjectionAtInfinity f b ≫ f) f
          (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
            modificationProjection f b) (Category.assoc _ _ _)
          (modificationProjectionAtInfinity f b) rfl (infinityIso f b)
          (infinityIso_hom_comp_modificationProjectionAtInfinity C f b) g,
        pullbackRightPullbackFstIso_hom_comp_fst_comp]) _
      (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _)]
  refine HEq.trans (heq_of_eq (properChowPushforward_comp_apply C _ _ _
    (gysinDivisorBaseChangeIso (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) g)).hom _ (testInfinityIso C f b g) rfl _ _
    (testInfinityIso_comp_structure C f b g) (k + 1 - 1)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) _).symm) ?_
  exact heq_map_index (α := fun n ↦ chowGroup C (testStr C f (modificationProjection f b) g)
      (n + 1))
    (β := fun n ↦ chowGroup C (pullback.fst (modificationProjectionAtInfinity f b) g ≫
      (modificationProjectionAtInfinity f b ≫ f)) n) (by ring : k + 1 - 1 = k)
    (chowGroupDegreeEquiv_heq C _ _ _)
    (fun n x ↦ properChowPushforward C _ _ (testInfinityIso C f b g)
      (testInfinityIso_comp_structure C f b g) n (properPushforwardDescends C _ _ _ _ _)
      ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
        (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
        (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
          (pullback.fst (modificationProjection f b) g)) n x))

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- The section `T ⟶ W ×_X T` through the zero fibre is the base change of the section at zero. -/
theorem zeroFibreSection_eq_modificationSectionAtZeroBaseChange :
    haveI := hA
    zeroFibreSection C f b g = modificationSectionAtZeroBaseChange f b inferInstance
      (modificationSectionAtZero_comp f b) g := by
  have := hA
  refine pullback.hom_ext ?_ ?_
  · rw [modificationSectionAtZeroBaseChange, pullback.lift_fst, modificationSectionAtZero_eq]
    have hfst : zeroFibreSection C f b g ≫ pullback.fst (modificationProjection f b) g =
        (inv ((openZeroDivisor C f b g).subschemeι ≫ openSnd C f b g) ≫
          (openZeroDivisor C f b g).subschemeι ≫
            pullback.fst (chartInclusion f b ≫ modificationProjection f b) g) ≫
          chartInclusion f b := by
      simp only [zeroFibreSection, Category.assoc, openBaseChange_fst]
    rw [hfst, ← Category.assoc g]
    congr 1
    rw [← cancel_mono (pullback.snd b (projectiveLineAffineChart f))]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    refine pullback.hom_ext ?_ ?_
    · have e1 : pullback.fst (chartInclusion f b ≫ modificationProjection f b) g ≫
          pullback.snd b (projectiveLineAffineChart f) ≫ pullback.fst (terminal.from X)
            (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) =
          openSnd C f b g ≫ g := by
        rw [← chartInclusion_comp_modificationProjection, pullback.condition]
      simp only [Category.assoc]
      rw [e1, affineZeroSection_fst, Category.comp_id, ← Category.assoc, ← Category.assoc,
        Category.assoc (inv _), IsIso.inv_hom_id, Category.id_comp]
    · have e2 := comap_chartZeroDivisor_subschemeι_snd (S := C.S)
        (pullback.fst (chartInclusion f b ≫ modificationProjection f b) g ≫
          pullback.snd b (projectiveLineAffineChart f) ≫ affineLineMap f)
        (openZeroDivisor C f b g) (openZeroDivisor_eq C f b g)
      simp only [Category.assoc, affineLineMap_snd] at e2
      simp only [Category.assoc]
      rw [e2, affineZeroSection_snd]
      simp only [← Category.assoc, terminal.comp_from]
  · rw [zeroFibreSection_snd, modificationSectionAtZeroBaseChange_comp_snd]

/-- Casting a class back along `n = m` inverts the degree identification `A_m ≃ A_n`. -/
theorem eqMp_chowGroupDegreeEquiv {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] {m n : ℤ}
    (h : m = n) (h' : n = m) (x : chowGroup C q m) :
    Eq.mp (congrArg (chowGroup C q) h') (chowGroupDegreeEquiv C q h x) = x := by
  subst h
  rfl

/-- **Stacks 0F9J, the pushforward identity.** For every test scheme `g : T ⟶ X` locally of
finite type and every `α ∈ A_k(T)`, `i_{∞,*}(C ∩ α) = i_{0,*} α` in `A_k(W ×_X T)`. -/
theorem gysinAtInfinityClass_pushforward (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    haveI := hA
    properChowPushforward C (modificationInfinityBaseChangeOver f b g)
        (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
        (modificationInfinityBaseChange_over f b g) k (properPushforwardDescends C _ _ _ _ _)
        (Eq.mp (congrArg (chowGroup C (modificationInfinityBaseChangeOver f b g)) (sub_zero k))
          ((gysinAtInfinityClass C f b hA).cap g k α)) =
      properChowPushforward C (g ≫ f) (modificationBaseChangeOver f b g)
        (modificationSectionAtZeroBaseChange f b inferInstance
          (modificationSectionAtZero_comp f b) g)
        (modificationSectionAtZeroBaseChange_over f b g inferInstance
          (modificationSectionAtZero_comp f b)) k (properPushforwardDescends C _ _ _ _ _) α := by
  have := hA
  obtain ⟨β, hβ⟩ := exists_isLift C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) g k α
  rw [gysinAtInfinityClass_cap_eq_of_isLift C f b hA g hβ,
    eqMp_chowGroupDegreeEquiv C _ (sub_zero k).symm (sub_zero k)]
  have hcomp := properChowPushforward_comp_apply C _ _ (modificationBaseChangeOver f b g)
    (testInfinityIso C f b g) (modificationInfinityBaseChange f b g)
    (testInfinityDivisor C f b g).subschemeι
    (testInfinityIso_comp_modificationInfinityBaseChange C f b g)
    (testInfinityIso_comp_structure C f b g) (modificationInfinityBaseChange_over f b g) rfl k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)
    ((gysinSystemOfInvertible C).onChow (testStr C f (modificationProjection f b) g)
      (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
      (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
        (pullback.fst (modificationProjection f b) g)) k β)
  refine hcomp.symm.trans ?_
  have hcc := chowPushforward_onChow_zero_eq_infinity C (testStr C f (modificationProjection f b) g)
    (pullback.fst (modificationProjection f b) g ≫ lineMap f b)
    (gysinTripleModule (zeroModule f b) (pullback.fst (modificationProjection f b) g))
    (gysinTripleModule (infinityModule f b) (pullback.fst (modificationProjection f b) g))
    (gysinTripleSection (zeroModule f b) (zeroSectionOnW f b)
      (pullback.fst (modificationProjection f b) g))
    (gysinTripleSection (infinityModule f b) (infinitySectionOnW f b)
      (pullback.fst (modificationProjection f b) g))
    (by rw [Stacks.Divisors.zeroScheme_pullback, zeroScheme_zeroSectionOnW,
      ← Scheme.IdealSheafData.comap_comp])
    (by rw [Stacks.Divisors.zeroScheme_pullback, zeroScheme_infinitySectionOnW,
      ← Scheme.IdealSheafData.comap_comp])
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections _ _ _
      (isTrivial_zeroModule C f b))
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections _ _ _
      (isTrivial_infinityModule f b)) k β
  refine hcc.symm.trans ?_
  refine (pushforward_onChow_testZeroDivisor_of_isLift C f b g hβ).trans ?_
  exact congrFun (congrArg DFunLike.coe (properChowPushforward_congr C (g ≫ f)
    (modificationBaseChangeOver f b g) _ _
    (zeroFibreSection_eq_modificationSectionAtZeroBaseChange C f b hA g) _ _ k
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _))) α

end Formula

end GysinAtInfinity

end Stacks.Chow

end

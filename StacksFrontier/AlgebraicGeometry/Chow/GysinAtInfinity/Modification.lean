module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Class
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.SectionPresentation
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveLineDivisorDegree.Infinity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections

/-!
# The geometry of a modification of the relative projective line

Let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over the chart `𝐀¹_X`. The chart is the base
change of the chart `𝐀¹_S ⟶ 𝐏¹_S`, so `b⁻¹(𝐀¹_X) ≅ 𝐀¹_X` is flat of relative dimension one over
`X`; its complement is the zero scheme of the pullback of the canonical section of `𝒪(D_∞)`,
which has trivial normal bundle (Stacks 0F93) and is the fibre `W_∞` at infinity. The construction
of `StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Class` therefore applies.

## Main definitions

* `Stacks.Chow.GysinAtInfinity.infinityIso` — the zero scheme of `b^* 1_{D_∞}` is `W_∞`.
* `Stacks.Chow.GysinAtInfinity.gysinAtInfinityClass` — **Stacks 0F9J, the class**
  `C ∈ A⁰(W_∞ ⟶ X)`.

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0F93](https://stacks.math.columbia.edu/tag/0F93)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The affine line over a morphism -/

section AffineLine

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism `𝐀¹_X ⟶ 𝐀¹_S` over `f`. -/
def affineLineMap : affineLineOver X ⟶ affineLineOver S :=
  pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

/-- The morphism `𝐀¹_X ⟶ 𝐀¹_S` lies over `f : X ⟶ S`. -/
@[reassoc (attr := simp)]
theorem affineLineMap_fst :
    affineLineMap f ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f :=
  pullback.lift_fst _ _ _

/-- The morphism `𝐀¹_X ⟶ 𝐀¹_S` commutes with the projections to `𝐀¹_ℤ`. -/
@[reassoc (attr := simp)]
theorem affineLineMap_snd :
    affineLineMap f ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- `𝐀¹_X = X ×_S 𝐀¹_S`. -/
theorem isPullback_affineLineMap :
    IsPullback (affineLineMap f)
      (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
      f := by
  refine IsPullback.of_right ?_ (affineLineMap_fst f)
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))).flip
  rw [affineLineMap_snd, show f ≫ terminal.from S = terminal.from X from terminal.hom_ext _ _]
  exact (IsPullback.of_hasPullback _ _).flip

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` lies over the chart `𝐀¹_S ⟶ 𝐏¹_S`. -/
theorem projectiveLineAffineChart_comp_snd :
    projectiveLineAffineChart f ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      affineLineMap f ≫ affineChart S := by
  unfold projectiveLineAffineChart
  dsimp only
  rw [pullback.lift_snd]
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, affineChart, Category.assoc, pullback.lift_fst, affineLineMap_fst]
  · rw [pullback.lift_snd, affineChart, Category.assoc, pullback.lift_snd, affineLineMap_snd_assoc]

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` commutes with the projections to `X`. -/
@[reassoc (attr := simp)]
theorem projectiveLineAffineChart_comp_fst :
    projectiveLineAffineChart f ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` is the base change of the chart `𝐀¹_S ⟶ 𝐏¹_S`. -/
theorem isPullback_projectiveLineAffineChart :
    IsPullback (affineLineMap f) (projectiveLineAffineChart f) (affineChart S)
      (pullback.snd f (relativeProjectiveLine S ↘ S)) := by
  refine IsPullback.of_bot ?_ (projectiveLineAffineChart_comp_snd f).symm
    (IsPullback.of_hasPullback f (relativeProjectiveLine S ↘ S)).flip
  rw [projectiveLineAffineChart_comp_fst, affineChart_comp]
  exact isPullback_affineLineMap f

/-- The chart `𝐀¹_X ⟶ 𝐏¹_X` is an open immersion. -/
instance isOpenImmersion_projectiveLineAffineChart :
    IsOpenImmersion (projectiveLineAffineChart f) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_projectiveLineAffineChart f)
    inferInstance

/-- The image of the chart `𝐀¹_X ⟶ 𝐏¹_X` is the inverse image of the image of the chart
`𝐀¹_S ⟶ 𝐏¹_S`. -/
theorem range_projectiveLineAffineChart :
    Set.range (projectiveLineAffineChart f).base =
      (pullback.snd f (relativeProjectiveLine S ↘ S)).base ⁻¹' Set.range (affineChart S).base :=
  range_fst_of_isPullback (isPullback_projectiveLineAffineChart f).flip

end AffineLine

/-! ### The affine line over the integers is flat of relative dimension one -/

section Integral

/-- The ring `ℤ` in the universe of the chapter. -/
abbrev integerRing : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)

/-- The structure morphism of `𝐀¹_ℤ` factors as `Spec ℤ[t] ⟶ Spec ℤ ⟶ ⊤_`, the first map
induced by the constant embedding `Polynomial.C`. -/
theorem terminalFrom_affineLine_eq :
    terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : integerRing.{u} →+* Polynomial integerRing.{u})) ≫
        terminal.from (Spec integerRing.{u}) :=
  terminal.hom_ext _ _

/-- The morphism from `Spec ℤ` to the terminal scheme is an isomorphism. -/
instance isIso_terminalFrom_specULiftZ :
    IsIso (terminal.from (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
  isIso_of_isTerminal specULiftZIsTerminal.{u} terminalIsTerminal _

/-- The morphism from `Spec integerRing` to the terminal scheme is an isomorphism. -/
instance isIso_terminalFrom_specIntegerRing : IsIso (terminal.from (Spec integerRing.{u})) :=
  isIso_terminalFrom_specULiftZ

attribute [local instance] flat_affineSpaceOver in
/-- The morphism `Spec ℤ[t] ⟶ Spec ℤ` is flat. -/
instance flat_specMap_C_integerRing :
    Flat (Spec.map (CommRingCat.ofHom (Polynomial.C : integerRing.{u} →+* Polynomial
        integerRing.{u}))) := by
  rw [← specPolynomialToAffineLine_over]
  infer_instance

/-- The morphism `Spec ℤ[t] ⟶ Spec ℤ` is locally of finite type. -/
instance locallyOfFiniteType_specMap_C_integerRing :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : integerRing.{u} →+* Polynomial
          integerRing.{u}))) := by
  rw [← specPolynomialToAffineLine_over]
  infer_instance

/-- The structure morphism of `𝐀¹_ℤ` is flat. -/
instance flat_terminalFrom_affineLine :
    Flat (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
  rw [terminalFrom_affineLine_eq]
  infer_instance

/-- The structure morphism of `𝐀¹_ℤ` is locally of finite type. -/
instance locallyOfFiniteType_terminalFrom_affineLine :
    LocallyOfFiniteType (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
  rw [terminalFrom_affineLine_eq]
  infer_instance

/-- Relative dimension transfers along an equality of a morphism with a composite. -/
private theorem relativeDimension_of_eq_comp {A B D : Scheme.{u}} {g : A ⟶ D} {p : A ⟶ B}
    {q : B ⟶ D} [LocallyOfFiniteType g] [LocallyOfFiniteType (p ≫ q)] (hg : g = p ≫ q) {n : ℕ}
    (h : AlgebraicGeometry.RelativeDimension (p ≫ q) n) :
    AlgebraicGeometry.RelativeDimension g n := by
  subst hg
  exact h

/-- The structure morphism of `𝐀¹_ℤ` has relative dimension one. -/
theorem relativeDimension_terminalFrom_affineLine :
    AlgebraicGeometry.RelativeDimension
      (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) 1 := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat
    (Spec.map (CommRingCat.ofHom (Polynomial.C : integerRing.{u} →+* Polynomial integerRing.{u})))
    (terminal.from (Spec integerRing.{u})) (relativeDimension_specMap_C _)
    (relativeDimension_of_isIso _)
  exact relativeDimension_of_eq_comp terminalFrom_affineLine_eq h

variable (S : Scheme.{u})

/-- The projection `𝐀¹_S ⟶ S` is flat. -/
instance flat_affineLineOver_fst :
    Flat (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) :=
  MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip inferInstance

/-- The projection `𝐀¹_S ⟶ S` is locally of finite type. -/
instance locallyOfFiniteType_affineLineOver_fst :
    LocallyOfFiniteType
      (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback _ _).flip
    inferInstance

/-- The projection `𝐀¹_S ⟶ S` has relative dimension one. -/
theorem relativeDimension_affineLineOver_fst :
    AlgebraicGeometry.RelativeDimension
      (pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))) 1 :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback _ _).flip
    relativeDimension_terminalFrom_affineLine

end Integral

/-! ### The modification -/

namespace GysinAtInfinity

section Modification

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor
  lineZeroDivisor_isEffectiveCartierDivisor

variable {X W S : Scheme.{u}} (f : X ⟶ S) (b : W ⟶ projectiveLineProduct f)

/-- For proper `b`, the projection `W ⟶ X` is locally of finite type. -/
instance locallyOfFiniteType_modificationProjection [IsProper b] :
    LocallyOfFiniteType (modificationProjection f b) := by
  unfold modificationProjection
  infer_instance

/-- For proper `b`, the projection `W ⟶ X` is proper. -/
instance isProper_modificationProjection [IsProper b] :
    IsProper (modificationProjection f b) := by
  unfold modificationProjection
  infer_instance

/-- The inclusion `W_∞ ⟶ W` of the fibre at infinity is a closed immersion. -/
instance isClosedImmersion_modificationInclusionAtInfinity :
    IsClosedImmersion (modificationInclusionAtInfinity f b) := by
  unfold modificationInclusionAtInfinity
  infer_instance

/-- For proper `b`, the projection `W_∞ ⟶ X` is locally of finite type. -/
instance locallyOfFiniteType_modificationProjectionAtInfinity [IsProper b] :
    LocallyOfFiniteType (modificationProjectionAtInfinity f b) := by
  unfold modificationProjectionAtInfinity
  infer_instance

/-- For proper `b`, the projection `W_∞ ⟶ X` is proper. -/
instance isProper_modificationProjectionAtInfinity [IsProper b] :
    IsProper (modificationProjectionAtInfinity f b) := by
  unfold modificationProjectionAtInfinity
  infer_instance

/-- The morphism `W ⟶ 𝐏¹_S`. -/
abbrev lineMap : W ⟶ relativeProjectiveLine S :=
  b ≫ pullback.snd f (relativeProjectiveLine S ↘ S)

/-- The pullback `b^* 𝒪(D_∞)` of the invertible module of the divisor at infinity. -/
abbrev infinityModule : W.Modules :=
  (Scheme.Modules.pullback (lineMap f b)).obj
    (Stacks.Divisors.divisorSheaf (lineInfinityDivisor S))

/-- The pullback of the canonical section of `𝒪(D_∞)`. -/
abbrev infinitySectionOnW : Γ(infinityModule f b, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (lineMap f b) _
    (Stacks.Divisors.divisorSheafGlobalSection (lineInfinityDivisor S))

/-- The pullback `b^* 𝒪(D_0)` of the invertible module of the divisor at zero. -/
abbrev zeroModule : W.Modules :=
  (Scheme.Modules.pullback (lineMap f b)).obj (Stacks.Divisors.divisorSheaf (lineZeroDivisor S))

/-- The pullback of the canonical section of `𝒪(D_0)`. -/
abbrev zeroSectionOnW : Γ(zeroModule f b, ⊤) :=
  AlgebraicGeometry.pullbackGlobalSections (lineMap f b) _
    (Stacks.Divisors.divisorSheafGlobalSection (lineZeroDivisor S))

/-- The zero scheme of `b^* 1_{D_∞}` is the inverse image of `D_∞`. -/
theorem zeroScheme_infinitySectionOnW :
    Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f b) =
      (lineInfinityDivisor S).comap (lineMap f b) := by
  rw [Stacks.Divisors.zeroScheme_pullback, zeroScheme_lineInfinityDivisor]

/-- The zero scheme of `b^* 1_{D_0}` is the inverse image of `D_0`. -/
theorem zeroScheme_zeroSectionOnW :
    Stacks.Divisors.zeroScheme W (zeroModule f b) (zeroSectionOnW f b) =
      (lineZeroDivisor S).comap (lineMap f b) := by
  rw [Stacks.Divisors.zeroScheme_pullback, zeroScheme_lineZeroDivisor]

/-- The normal bundle of `W_∞` is trivial: Stacks 0F93 pulled back. -/
theorem isTrivial_infinityModule :
    AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f
          b)).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme W (infinityModule f b)
        (infinitySectionOnW f b)).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme W (infinityModule f b)
        (infinitySectionOnW f b)).subschemeι).obj (infinityModule f b)) := by
  refine Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections (lineMap f b) _ _ ?_
  rw [zeroScheme_lineInfinityDivisor]
  exact isTrivial_pullback_divisorSheaf_lineInfinityDivisor S

/-- The open `b⁻¹(𝐀¹_X) ⊆ W`. -/
abbrev chartOpen : Scheme.{u} := pullback b (projectiveLineAffineChart f)

/-- The inclusion `b⁻¹(𝐀¹_X) ⟶ W`. -/
abbrev chartInclusion : chartOpen f b ⟶ W := pullback.fst b (projectiveLineAffineChart f)

/-- The composite `b⁻¹(𝐀¹_X) ⟶ W ⟶ X` factors through `b⁻¹(𝐀¹_X) ⟶ 𝐀¹_X ⟶ X`. -/
theorem chartInclusion_comp_modificationProjection :
    chartInclusion f b ≫ modificationProjection f b =
      pullback.snd b (projectiveLineAffineChart f) ≫
        pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
  rw [modificationProjection, ← Category.assoc, pullback.condition, Category.assoc,
    projectiveLineAffineChart_comp_fst]

/-- If `b` is proper and an isomorphism over `𝐀¹_X`, then `b⁻¹(𝐀¹_X) ⟶ X` is flat. -/
instance flat_chartInclusion_comp [IsProper b] [IsIso (pullback.snd b (projectiveLineAffineChart
    f))] :
    Flat (chartInclusion f b ≫ modificationProjection f b) := by
  rw [chartInclusion_comp_modificationProjection]
  infer_instance

/-- If `b` is proper and an isomorphism over `𝐀¹_X`, then `b⁻¹(𝐀¹_X) ⟶ X` has relative
dimension one. -/
theorem relativeDimension_chartInclusion_comp [IsProper b]
    [IsIso (pullback.snd b (projectiveLineAffineChart f))] :
    AlgebraicGeometry.RelativeDimension (chartInclusion f b ≫ modificationProjection f b) 1 := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat
    (pullback.snd b (projectiveLineAffineChart f))
    (pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))))
    (relativeDimension_of_isIso _) (relativeDimension_affineLineOver_fst X)
  rw [Nat.zero_add] at h
  exact relativeDimension_of_eq_comp (chartInclusion_comp_modificationProjection f b) h

/-- `W_∞` is the complement of `b⁻¹(𝐀¹_X)`. -/
theorem range_zeroScheme_infinitySectionOnW :
    Set.range (Stacks.Divisors.zeroScheme W (infinityModule f b)
      (infinitySectionOnW f b)).subschemeι.base = (Set.range (chartInclusion f b).base)ᶜ := by
  ext x
  rw [Scheme.IdealSheafData.range_subschemeι, zeroScheme_infinitySectionOnW,
    Scheme.IdealSheafData.support_comap]
  show (lineMap f b).base x ∈ ((lineInfinityDivisor S).support : Set _) ↔
    x ∈ (Set.range (chartInclusion f b).base)ᶜ
  rw [coe_support_lineInfinityDivisor, ← compl_range_affineChart, Scheme.Pullback.range_fst,
    range_projectiveLineAffineChart]
  rfl

/-- The fibre at infinity `W ×_{𝐏¹_X} X` is the zero scheme of `b^* 1_{D_∞}`. -/
theorem ker_modificationInclusionAtInfinity :
    (modificationInclusionAtInfinity f b).ker =
      Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f b) := by
  rw [zeroScheme_infinitySectionOnW, lineMap, Scheme.IdealSheafData.comap_comp,
    ← ker_infinitySection, modificationInclusionAtInfinity]
  exact AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (IsPullback.of_hasPullback _ _)

/-- The identification of the zero scheme of `b^* 1_{D_∞}` with the fibre at infinity. -/
def infinityIso :
    (Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f b)).subscheme ≅
      modificationFibreAtInfinity f b :=
  haveI := IsClosedImmersion.isIso_lift (modificationInclusionAtInfinity f b)
    (Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f b)).subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_modificationInclusionAtInfinity])
  asIso (IsClosedImmersion.lift (modificationInclusionAtInfinity f b)
    (Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f b)).subschemeι
    (by rw [Scheme.IdealSheafData.ker_subschemeι, ker_modificationInclusionAtInfinity]))

/-- The isomorphism `infinityIso` commutes with the closed immersions into `W`. -/
@[reassoc (attr := simp)]
theorem infinityIso_hom_comp :
    (infinityIso f b).hom ≫ modificationInclusionAtInfinity f b =
      (Stacks.Divisors.zeroScheme W (infinityModule f b) (infinitySectionOnW f b)).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

end Modification

section Class

attribute [local instance] lineInfinityDivisor_isEffectiveCartierDivisor

variable (C : ChowSituation.{u}) {X W : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))

/-- The class at infinity, on the zero-scheme model `Z(b^* 1_{D_∞})` of the fibre at infinity. -/
def zeroSchemeClass :
    BivariantClass C (gysinSystemOfInvertible C)
      (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
        (modificationProjection f b ≫ f)) f
      (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
        modificationProjection f b) (Category.assoc _ _ _) 0 :=
  haveI := hA
  infinityClass C f (modificationProjection f b) (chartInclusion f b)
    (relativeDimension_chartInclusion_comp f b) (infinityModule f b) (infinitySectionOnW f b)
    (range_zeroScheme_infinitySectionOnW f b) (isTrivial_infinityModule f b)

omit [LocallyOfFiniteType f] [IsProper b] in
/-- The isomorphism `infinityIso` commutes with the projections to `X`. -/
theorem infinityIso_hom_comp_modificationProjectionAtInfinity :
    (infinityIso f b).hom ≫ modificationProjectionAtInfinity f b =
      gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
        modificationProjection f b := by
  rw [modificationProjectionAtInfinity, infinityIso_hom_comp_assoc]

/-- **Stacks 0F9J, the class.** The bivariant class `C ∈ A⁰(W_∞ ⟶ X)` of the fibre at infinity
of a proper `b : W ⟶ 𝐏¹_X` which is an isomorphism over `𝐀¹_X`: on a test scheme `T ⟶ X` it caps
`α ∈ A_k(T)` to `i_∞^* β` for any `β ∈ A_{k+1}(W ×_X T)` restricting to the flat pullback of `α`
over `𝐀¹_X`. -/
def gysinAtInfinityClass :
    BivariantClass C (gysinSystemOfInvertible C) (modificationProjectionAtInfinity f b ≫ f) f
      (modificationProjectionAtInfinity f b) rfl 0 :=
  bivariantTransport C (gysinSystemOfInvertible C)
    (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
      (modificationProjection f b ≫ f)) (modificationProjectionAtInfinity f b ≫ f) f
    (gysinTripleInclusion (infinityModule f b) (infinitySectionOnW f b) ≫
      modificationProjection f b) (Category.assoc _ _ _) (modificationProjectionAtInfinity f b) rfl
    (infinityIso f b) (infinityIso_hom_comp_modificationProjectionAtInfinity C f b) 0
    (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) (zeroSchemeClass C f b hA)

end Class

end GysinAtInfinity

end Stacks.Chow

end

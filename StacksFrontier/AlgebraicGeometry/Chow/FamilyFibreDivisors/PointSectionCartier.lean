module

public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.SectionCartier
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor.ZeroCartier
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections

/-!
# The section of a family of projective lines at an arbitrary point is a Cartier divisor

Let `f : X ⟶ S` be a morphism of schemes and let `t : Γ(S, ⊤)` be a global function on `S`,
that is, an `S`-point of the affine chart `𝔸¹_S ⊆ ℙ¹_S`. The image of the section
`X ⟶ X ×_S ℙ¹_S` of the family of projective lines over `X` whose coordinate is `t` is an
effective Cartier divisor on the whole family, with no hypothesis on `X`, `S` or `t`.

For a scheme `S` over an algebraically closed field `k` every `k`-rational point of `ℙ¹_S` other
than `∞` is of this form: a closed point `a ∈ 𝔸¹_k = k` is the global function `a` on
`S = Spec k`.

## Main definitions

* `Stacks.Chow.affineSpaceTranslation`: translation of Mathlib's affine space `𝔸(n; S)` by a
  global function on `S`, in the coordinate `T ↦ T + t`.
* `Stacks.Chow.affineTranslation`: the same translation read on the affine line `𝔸¹_S` of this
  chapter, through `Stacks.Chow.affineLineToAffineSpace`.
* `Stacks.Chow.affineLineSection` and `Stacks.Chow.lineSection`: the `S`-point of `𝔸¹_S`,
  resp. of `ℙ¹_S`, with coordinate `t`.
* `Stacks.Chow.pointSection`: the section `X ⟶ X ×_S ℙ¹_S` of the family at that point, and
  `Stacks.Chow.affinePointSection`, the same read on the chart `X ×_S 𝔸¹_S`.

## Main results

* `Stacks.Chow.affineLineSection_appTop_affineCoordinate`: the coordinate of the section of
  `𝔸¹_S` at `t` is `t`.
* `Stacks.Chow.pointSection_zero`: at `t = 0` the section is the zero section.
* `Stacks.Chow.isPullback_pointSection` and `Stacks.Chow.ker_pointSection`: the section of the
  family is the base change of the section of `ℙ¹_S ⟶ S`, so the divisor it cuts out is the
  inverse image `X ×_S {t}` of the point.
* `Stacks.Chow.isEffectiveCartierDivisor_ker_pointSection`: **the image of the section at `t` is
  an effective Cartier divisor on `X ×_S ℙ¹_S`.**
* `Stacks.Chow.isEffectiveCartierDivisor_ker_lineSection`: the same on `ℙ¹_S` itself.
* `Stacks.Chow.isLocallyPrincipal_ker_pointSection`: it is in particular locally principal.
* `Stacks.Chow.isEffectiveCartierDivisor_of_comap_of_isOpenImmersion`: a closed subscheme whose
  support lies in an open and which is an effective Cartier divisor there is one on the whole
  scheme.

## Implementation notes

The translations of the affine line act transitively on its `S`-points, so the divisor cut out
by the section at `t` is the inverse image of the divisor cut out by the zero section under an
automorphism, and local principality and the nonzerodivisor generator transport along it
(`Stacks.Divisors.isPullbackDefined_of_flat`, an isomorphism being flat). The translation
`T ↦ T + t` is built on Mathlib's `AlgebraicGeometry.AffineSpace` with `AffineSpace.homOfVector`
and `AffineSpace.hom_ext`, and carried to the affine line through
`Stacks.Chow.affineLineToAffineSpace`.

Passing from the chart `X ×_S 𝔸¹_S` to `X ×_S ℙ¹_S` is
`Stacks.Chow.isEffectiveCartierDivisor_of_comap_of_isOpenImmersion`: the support of the divisor
is the image of the section, which factors through the chart, and off the chart the ideal is the
unit ideal.

## References

* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 01WS](https://stacks.math.columbia.edu/tag/01WS)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### An effective Cartier divisor supported in an open -/

/-- **A closed subscheme supported in an open is an effective Cartier divisor as soon as it is
one on that open.** -/
theorem isEffectiveCartierDivisor_of_comap_of_isOpenImmersion {T W : Scheme.{u}}
    (J : T.IdealSheafData) (q : W ⟶ T) [IsOpenImmersion q]
    (hsupp : J.supportSet ⊆ Set.range q)
    (h : Stacks.Divisors.IsEffectiveCartierDivisor (J.comap q)) :
    Stacks.Divisors.IsEffectiveCartierDivisor J := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen _ fun x => ?_
  by_cases hx : x ∈ J.supportSet
  · obtain ⟨z, rfl⟩ := hsupp hx
    obtain ⟨V, hzV, -, g, hg, hgen⟩ :=
      Stacks.Blowup.exists_affineOpens_ideal_eq_span_le (J.comap q) h z ⊤ trivial
    have hsurj : Function.Surjective ((q.appIso (V : W.Opens)).inv).hom :=
      (ConcreteCategory.bijective_of_isIso _).2
    refine ⟨q ''ᵁ (V : W.Opens), V.2.image_of_isOpenImmersion q, ⟨z, hzV, rfl⟩,
      ((q.appIso (V : W.Opens)).inv) g,
      Stacks.Divisors.isRegular_ringEquiv
        (q.appIso (V : W.Opens)).symm.commRingCatIsoToRingEquiv hg, ?_⟩
    rw [← Ideal.map_comap_of_surjective _ hsurj
        (J.ideal ⟨q ''ᵁ (V : W.Opens), V.2.image_of_isOpenImmersion q⟩),
      ← Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J q V, hgen, Ideal.map_span,
      Set.image_singleton]
  · exact Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_notMem_support _ x hx

/-- The support of the kernel ideal of a closed immersion is its range. -/
private theorem supportSet_ker_eq_range {A B : Scheme.{u}} (g : A ⟶ B) [IsClosedImmersion g] :
    g.ker.supportSet = Set.range g := by
  rw [show g.ker.supportSet = (g.ker.support : Set B) from rfl, Scheme.Hom.support_ker,
    IsClosed.closure_eq g.isClosedEmbedding.isClosed_range]

/-- The kernel of a section composed with an isomorphism is the inverse image of its kernel. -/
private theorem ker_comp_eq_comap_ker_inv {A B C : Scheme.{u}} (s : A ⟶ B) [IsClosedImmersion s]
    (φ : B ⟶ C) [IsIso φ] :
    (s ≫ φ).ker = s.ker.comap (inv φ) := by
  refine AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (b := 𝟙 A) (i := s)
    (IsPullback.of_vert_isIso_mono ⟨?_⟩)
  rw [Category.id_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-! ### The translations of affine space -/

section Point

variable (S : Scheme.{u})

/-- **The translation of `𝔸(n; S)` by a global function `t` on `S`**: in coordinates it is
`T ↦ T + t`, with `t` read on `𝔸(n; S)` through the structure morphism. -/
def affineSpaceTranslation {n : Type u} (t : Γ(S, ⊤)) : 𝔸(n; S) ⟶ 𝔸(n; S) :=
  AffineSpace.homOfVector (𝔸(n; S) ↘ S)
    (fun i => AffineSpace.coord S i + (𝔸(n; S) ↘ S).appTop t)

/-- A translation of `𝔸(n; S)` lies over `S`. -/
@[simp]
theorem affineSpaceTranslation_over {n : Type u} (t : Γ(S, ⊤)) :
    affineSpaceTranslation S (n := n) t ≫ (𝔸(n; S) ↘ S) = 𝔸(n; S) ↘ S :=
  AffineSpace.homOfVector_over _ _

/-- A translation of `𝔸(n; S)` adds `t` to every coordinate. -/
@[simp]
theorem affineSpaceTranslation_appTop_coord {n : Type u} (t : Γ(S, ⊤)) (i : n) :
    (affineSpaceTranslation S (n := n) t).appTop (AffineSpace.coord S i) =
      AffineSpace.coord S i + (𝔸(n; S) ↘ S).appTop t :=
  AffineSpace.homOfVector_appTop_coord _ _ _

/-- Translating by `t` and then by `t'` is translating by `t + t'`. -/
theorem affineSpaceTranslation_comp {n : Type u} (t t' : Γ(S, ⊤)) :
    affineSpaceTranslation S (n := n) t ≫ affineSpaceTranslation S (n := n) t' =
      affineSpaceTranslation S (n := n) (t + t') := by
  refine AffineSpace.hom_ext ?_ fun i => ?_
  · rw [Category.assoc, affineSpaceTranslation_over, affineSpaceTranslation_over,
      affineSpaceTranslation_over]
  · have hpull : (affineSpaceTranslation S (n := n) t).appTop ((𝔸(n; S) ↘ S).appTop t') =
        (𝔸(n; S) ↘ S).appTop t' := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, affineSpaceTranslation_over]
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, affineSpaceTranslation_appTop_coord,
      map_add, affineSpaceTranslation_appTop_coord, affineSpaceTranslation_appTop_coord, hpull,
      map_add, add_assoc]

/-- Translating by `0` is the identity. -/
@[simp]
theorem affineSpaceTranslation_zero {n : Type u} :
    affineSpaceTranslation S (n := n) 0 = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ fun i => ?_
  · rw [affineSpaceTranslation_over, Category.id_comp]
  · rw [affineSpaceTranslation_appTop_coord, map_zero, add_zero, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]

/-- A translation of `𝔸(n; S)` is an isomorphism, the translation by `-t` being its inverse. -/
instance isIso_affineSpaceTranslation {n : Type u} (t : Γ(S, ⊤)) :
    IsIso (affineSpaceTranslation S (n := n) t) :=
  ⟨affineSpaceTranslation S (n := n) (-t), by
      rw [affineSpaceTranslation_comp, add_neg_cancel, affineSpaceTranslation_zero], by
      rw [affineSpaceTranslation_comp, neg_add_cancel, affineSpaceTranslation_zero]⟩

/-! ### The translations of the affine line -/

/-- The structure morphism of the affine line `𝔸¹_S` of this chapter. -/
abbrev affineLineOverHom : affineLineOver S ⟶ S :=
  pullback.fst (terminal.from S) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ)))))

/-- **The translation of `𝔸¹_S` by a global function `t` on `S`**, read through the
identification of `𝔸¹_S` with Mathlib's one-dimensional affine space. -/
def affineTranslation (t : Γ(S, ⊤)) : affineLineOver S ⟶ affineLineOver S :=
  affineLineToAffineSpace S ≫
    affineSpaceTranslation S (n := PUnit.{u + 1}) t ≫ inv (affineLineToAffineSpace S)

/-- A translation of `𝔸¹_S` is an isomorphism. -/
instance isIso_affineTranslation (t : Γ(S, ⊤)) : IsIso (affineTranslation S t) := by
  rw [affineTranslation]
  infer_instance

/-- Reading a global section of `𝔸¹_S` through the identification with affine space and back
changes nothing. -/
private theorem appTop_inv_affineLineToAffineSpace (z : Γ(𝔸(PUnit.{u + 1}; S), ⊤)) :
    (inv (affineLineToAffineSpace S)).appTop ((affineLineToAffineSpace S).appTop z) = z := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, IsIso.inv_hom_id,
    Scheme.Hom.id_appTop, CommRingCat.id_apply]

/-- The coordinate `T` of `𝔸¹_S`, read on affine space, is the coordinate there. -/
private theorem appTop_inv_affineCoordinate :
    (inv (affineLineToAffineSpace S)).appTop (affineCoordinate S) =
      AffineSpace.coord S PUnit.unit := by
  rw [← affineLineToAffineSpace_appTop_coord S PUnit.unit,
    appTop_inv_affineLineToAffineSpace]

/-- A translation of `𝔸¹_S` lies over `S`. -/
@[simp]
theorem affineTranslation_over (t : Γ(S, ⊤)) :
    affineTranslation S t ≫ affineLineOverHom S = affineLineOverHom S := by
  have hj : inv (affineLineToAffineSpace S) ≫ affineLineOverHom S =
      (𝔸(PUnit.{u + 1}; S) ↘ S) := by
    rw [affineLineOverHom, ← affineLineToAffineSpace_over S, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  rw [affineTranslation, Category.assoc, Category.assoc, hj, affineSpaceTranslation_over,
    affineLineOverHom, ← affineLineToAffineSpace_over S]

/-- **A translation of `𝔸¹_S` adds `t` to the coordinate `T`.** -/
@[simp]
theorem affineTranslation_appTop_affineCoordinate (t : Γ(S, ⊤)) :
    (affineTranslation S t).appTop (affineCoordinate S) =
      affineCoordinate S + (affineLineOverHom S).appTop t := by
  have hlast : (affineLineToAffineSpace S).appTop ((𝔸(PUnit.{u + 1}; S) ↘ S).appTop t) =
      (affineLineOverHom S).appTop t := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, affineLineToAffineSpace_over,
      affineLineOverHom]
  rw [affineTranslation, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_inv_affineCoordinate,
    affineSpaceTranslation_appTop_coord, map_add, affineLineToAffineSpace_appTop_coord, hlast]

/-- Translating `𝔸¹_S` by `t` and then by `t'` is translating by `t + t'`. -/
theorem affineTranslation_comp (t t' : Γ(S, ⊤)) :
    affineTranslation S t ≫ affineTranslation S t' = affineTranslation S (t + t') := by
  rw [affineTranslation, affineTranslation, affineTranslation, ← affineSpaceTranslation_comp]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]

/-- Translating `𝔸¹_S` by `0` is the identity. -/
@[simp]
theorem affineTranslation_zero : affineTranslation S (0 : Γ(S, ⊤)) = 𝟙 _ := by
  rw [affineTranslation, affineSpaceTranslation_zero, Category.id_comp, IsIso.hom_inv_id]

/-! ### The section of the projective line at a global function -/

/-- **The `S`-point of `𝔸¹_S` with coordinate `t`**: the zero section translated by `t`. -/
def affineLineSection (t : Γ(S, ⊤)) : S ⟶ affineLineOver S :=
  affineLineConstantSection S integralAffineZeroSection ≫ affineTranslation S t

/-- The second component of a constant section of `𝔸¹_S` is the constant morphism at the
chosen integral point. -/
theorem affineLineConstantSection_comp_snd
    (e : (⊤_ Scheme.{u}) ⟶ Spec (.of (Polynomial (ULift.{u} ℤ)))) :
    affineLineConstantSection S e ≫ pullback.snd (terminal.from S)
        (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) =
      terminal.from S ≫ e := by
  rw [affineLineConstantSection, pullback.lift_snd]

/-- A constant section of `𝔸¹_S` is a section of its structure morphism. -/
@[simp]
theorem affineLineConstantSection_comp_fst
    (e : (⊤_ Scheme.{u}) ⟶ Spec (.of (Polynomial (ULift.{u} ℤ)))) :
    affineLineConstantSection S e ≫ affineLineOverHom S = 𝟙 S := by
  rw [affineLineOverHom, affineLineConstantSection, pullback.lift_fst]

/-- **The zero section of `𝔸¹_S` has coordinate `0`.** -/
theorem affineLineConstantSection_appTop_affineCoordinate_zero :
    (affineLineConstantSection S integralAffineZeroSection).appTop (affineCoordinate S) = 0 := by
  have hstep : (affineLineConstantSection S integralAffineZeroSection).appTop
      (affineCoordinate S) =
      (terminal.from S ≫ integralAffineZeroSection.{u}).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X) := by
    rw [affineCoordinate, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      affineLineConstantSection_comp_snd]
  have hzero : (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (0 : ULift.{u} ℤ)))).appTop
      ((Scheme.ΓSpecIso (.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X) = 0 := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    show (Scheme.ΓSpecIso (.of (ULift.{u} ℤ))).inv
      (Polynomial.evalRingHom (0 : ULift.{u} ℤ) Polynomial.X) = 0
    simp
  rw [hstep, integralAffineZeroSection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hzero, map_zero, map_zero]

/-- **The coordinate of the section of `𝔸¹_S` at `t` is `t`.** -/
theorem affineLineSection_appTop_affineCoordinate (t : Γ(S, ⊤)) :
    (affineLineSection S t).appTop (affineCoordinate S) = t := by
  have hpull : (affineLineConstantSection S integralAffineZeroSection).appTop
      ((affineLineOverHom S).appTop t) = t := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      affineLineConstantSection_comp_fst, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  rw [affineLineSection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    affineTranslation_appTop_affineCoordinate, map_add,
    affineLineConstantSection_appTop_affineCoordinate_zero, hpull, zero_add]

/-- The section of `𝔸¹_S` at `t` is a section of the structure morphism. -/
@[simp]
theorem affineLineSection_comp (t : Γ(S, ⊤)) :
    affineLineSection S t ≫ affineLineOverHom S = 𝟙 S := by
  rw [affineLineSection, Category.assoc, affineTranslation_over,
    affineLineConstantSection_comp_fst]

/-- At `t = 0` the section of `𝔸¹_S` is the zero section. -/
theorem affineLineSection_zero :
    affineLineSection S (0 : Γ(S, ⊤)) =
      affineLineConstantSection S integralAffineZeroSection := by
  rw [affineLineSection, affineTranslation_zero, Category.comp_id]

/-- **The `S`-point of `ℙ¹_S` with coordinate `t`**, the section of `ℙ¹_S ⟶ S` obtained by
reading the point `t` of the affine chart in `ℙ¹_S`. -/
def lineSection (t : Γ(S, ⊤)) : S ⟶ relativeProjectiveLine S :=
  affineLineSection S t ≫ affineChart S

/-- The section of `ℙ¹_S` at `t` is a section of the structure morphism. -/
@[simp]
theorem lineSection_comp (t : Γ(S, ⊤)) :
    lineSection S t ≫ (relativeProjectiveLine S ↘ S) = 𝟙 S := by
  rw [lineSection, Category.assoc, affineChart_comp, ← affineLineOverHom,
    affineLineSection_comp]

/-- At `t = 0` the section of `ℙ¹_S` is the zero section. -/
theorem lineSection_zero : lineSection S (0 : Γ(S, ⊤)) = lineZeroSection S := by
  rw [lineSection, affineLineSection_zero, lineZeroSection_eq]

/-- The section of `ℙ¹_S` at `t` is a closed immersion, being a section of a separated
morphism. -/
instance isClosedImmersion_lineSection (t : Γ(S, ⊤)) :
    IsClosedImmersion (lineSection S t) := by
  have hsep : IsSeparated (relativeProjectiveLine S ↘ S) := inferInstance
  have : IsClosedImmersion (lineSection S t ≫ (relativeProjectiveLine S ↘ S)) := by
    rw [lineSection_comp]
    infer_instance
  exact IsClosedImmersion.of_comp _ (relativeProjectiveLine S ↘ S)

end Point

/-! ### The section of the family at a global function -/

section Family

variable {X S : Scheme.{u}} (f : X ⟶ S) (t : Γ(S, ⊤))

/-- The affine chart `X ×_S 𝔸¹_S` of the family `X ×_S ℙ¹_S`. -/
abbrev affineLineProduct : Scheme.{u} := pullback f (affineLineOverHom S)

/-- The open immersion `X ×_S 𝔸¹_S ⟶ X ×_S ℙ¹_S`, the base change of the affine chart. -/
def affineChartProduct : affineLineProduct f ⟶ projectiveLineProduct f :=
  pullback.lift (pullback.fst f (affineLineOverHom S))
    (pullback.snd f (affineLineOverHom S) ≫ affineChart S) (by
      rw [Category.assoc, affineChart_comp, ← affineLineOverHom]
      exact pullback.condition)

/-- The chart of the family lies over `X`. -/
@[simp]
theorem affineChartProduct_comp_fst :
    affineChartProduct f ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst f (affineLineOverHom S) :=
  pullback.lift_fst _ _ _

/-- The chart of the family lies over the affine chart of `ℙ¹_S`. -/
@[simp]
theorem affineChartProduct_comp_snd :
    affineChartProduct f ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      pullback.snd f (affineLineOverHom S) ≫ affineChart S :=
  pullback.lift_snd _ _ _

/-- The chart of the family is the base change of the chart of `ℙ¹_S` along the projection to
`ℙ¹_S`. -/
theorem isPullback_affineChartProduct :
    IsPullback (affineChartProduct f) (pullback.snd f (affineLineOverHom S))
      (pullback.snd f (relativeProjectiveLine S ↘ S)) (affineChart S) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (relativeProjectiveLine S ↘ S))
    ?_ (affineChartProduct_comp_snd f) (IsPullback.of_hasPullback _ _)
  rw [affineChartProduct_comp_fst, affineChart_comp, ← affineLineOverHom]
  exact IsPullback.of_hasPullback _ _

/-- The chart of the family is an open immersion. -/
instance isOpenImmersion_affineChartProduct : IsOpenImmersion (affineChartProduct f) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_affineChartProduct f).flip inferInstance

/-- **The section `X ⟶ X ×_S ℙ¹_S` of the family at the point `t` of `ℙ¹_S`.** -/
def pointSection : X ⟶ projectiveLineProduct f :=
  pullback.lift (𝟙 X) (f ≫ lineSection S t) (by
    rw [Category.id_comp, Category.assoc, lineSection_comp, Category.comp_id])

/-- The same section read on the chart `X ×_S 𝔸¹_S`. -/
def affinePointSection : X ⟶ affineLineProduct f :=
  pullback.lift (𝟙 X) (f ≫ affineLineSection S t) (by
    rw [Category.id_comp, Category.assoc, affineLineSection_comp, Category.comp_id])

/-- The section of the family at `t` is a section of the first projection. -/
@[simp]
theorem pointSection_comp_fst :
    pointSection f t ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second component of the section of the family at `t` is the section of `ℙ¹_S` at `t`. -/
@[simp]
theorem pointSection_comp_snd :
    pointSection f t ≫ pullback.snd f (relativeProjectiveLine S ↘ S) = f ≫ lineSection S t :=
  pullback.lift_snd _ _ _

/-- The section of the chart at `t` is a section of the first projection. -/
@[simp]
theorem affinePointSection_comp_fst :
    affinePointSection f t ≫ pullback.fst f (affineLineOverHom S) = 𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second component of the section of the chart at `t` is the section of `𝔸¹_S` at `t`. -/
@[simp]
theorem affinePointSection_comp_snd :
    affinePointSection f t ≫ pullback.snd f (affineLineOverHom S) =
      f ≫ affineLineSection S t :=
  pullback.lift_snd _ _ _

/-- The section of the family at `t` factors through the chart. -/
theorem affinePointSection_comp_affineChartProduct :
    affinePointSection f t ≫ affineChartProduct f = pointSection f t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, affineChartProduct_comp_fst, affinePointSection_comp_fst,
      pointSection_comp_fst]
  · rw [Category.assoc, affineChartProduct_comp_snd, ← Category.assoc,
      affinePointSection_comp_snd, pointSection_comp_snd, Category.assoc, lineSection]

/-- **At `t = 0` the section of the family is the zero section.** -/
theorem pointSection_zero : pointSection f (0 : Γ(S, ⊤)) = zeroSection f := by
  refine pullback.hom_ext ?_ ?_
  · rw [pointSection_comp_fst, zeroSection_comp_fst]
  · rw [pointSection_comp_snd, zeroSection_comp_snd, lineSection_zero]

/-- The section at `t` is a section of the first projection, hence a split monomorphism. -/
instance isSplitMono_pointSection : IsSplitMono (pointSection f t) :=
  IsSplitMono.mk' ⟨pullback.fst f (relativeProjectiveLine S ↘ S), pointSection_comp_fst f t⟩

/-- The section at `t` is a closed immersion, being a section of a proper, hence separated,
morphism. -/
instance isClosedImmersion_pointSection : IsClosedImmersion (pointSection f t) := by
  have : IsClosedImmersion
      (pointSection f t ≫ pullback.fst f (relativeProjectiveLine S ↘ S)) := by
    rw [pointSection_comp_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst f (relativeProjectiveLine S ↘ S))

/-- The section of the family at `t` is the base change of the section of `ℙ¹_S ⟶ S` at `t`. -/
theorem isPullback_pointSection :
    IsPullback (pointSection f t) f (pullback.snd f (relativeProjectiveLine S ↘ S))
      (lineSection S t) := by
  refine IsPullback.of_right ?_ (pointSection_comp_snd f t) (IsPullback.of_hasPullback _ _)
  rw [pointSection_comp_fst, lineSection_comp]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- **The image of the section at `t` is the inverse image `X ×_S {t}` of the point `t`.** -/
theorem ker_pointSection :
    (pointSection f t).ker =
      (lineSection S t).ker.comap (pullback.snd f (relativeProjectiveLine S ↘ S)) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_pointSection f t)

/-- The section read on the chart is the base change of the section of the family along the
chart. -/
theorem isPullback_affinePointSection :
    IsPullback (affinePointSection f t) (𝟙 X) (affineChartProduct f) (pointSection f t) :=
  IsPullback.of_vert_isIso_mono ⟨by
    rw [Category.id_comp, affinePointSection_comp_affineChartProduct]⟩

/-- The section of the chart at `t` is a closed immersion. -/
instance isClosedImmersion_affinePointSection :
    IsClosedImmersion (affinePointSection f t) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_affinePointSection f t).flip inferInstance

/-- The divisor cut out on the chart by the section at `t` is the inverse image of the one cut out
on the family. -/
theorem ker_affinePointSection :
    (affinePointSection f t).ker = (pointSection f t).ker.comap (affineChartProduct f) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback (isPullback_affinePointSection f t)

/-! ### The translations of the chart of the family -/

/-- The translation of `X ×_S 𝔸¹_S` by a global function `t` on `S`, the base change of the
translation of `𝔸¹_S`. -/
def affineTranslationProduct : affineLineProduct f ⟶ affineLineProduct f :=
  pullback.lift (pullback.fst f (affineLineOverHom S))
    (pullback.snd f (affineLineOverHom S) ≫ affineTranslation S t) (by
      rw [Category.assoc, affineTranslation_over]
      exact pullback.condition)

/-- A translation of the chart of the family lies over `X`. -/
@[simp]
theorem affineTranslationProduct_comp_fst :
    affineTranslationProduct f t ≫ pullback.fst f (affineLineOverHom S) =
      pullback.fst f (affineLineOverHom S) :=
  pullback.lift_fst _ _ _

/-- A translation of the chart of the family lies over the translation of `𝔸¹_S`. -/
@[simp]
theorem affineTranslationProduct_comp_snd :
    affineTranslationProduct f t ≫ pullback.snd f (affineLineOverHom S) =
      pullback.snd f (affineLineOverHom S) ≫ affineTranslation S t :=
  pullback.lift_snd _ _ _

/-- Translating the chart of the family by `t` and then by `t'` is translating by `t + t'`. -/
theorem affineTranslationProduct_comp (t' : Γ(S, ⊤)) :
    affineTranslationProduct f t ≫ affineTranslationProduct f t' =
      affineTranslationProduct f (t + t') := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, affineTranslationProduct_comp_fst, affineTranslationProduct_comp_fst,
      affineTranslationProduct_comp_fst]
  · rw [Category.assoc, affineTranslationProduct_comp_snd, ← Category.assoc,
      affineTranslationProduct_comp_snd, affineTranslationProduct_comp_snd, Category.assoc,
      affineTranslation_comp]

/-- Translating the chart of the family by `0` is the identity. -/
@[simp]
theorem affineTranslationProduct_zero :
    affineTranslationProduct f (0 : Γ(S, ⊤)) = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · rw [affineTranslationProduct_comp_fst, Category.id_comp]
  · rw [affineTranslationProduct_comp_snd, affineTranslation_zero, Category.comp_id,
      Category.id_comp]

/-- A translation of the chart of the family is an isomorphism, the translation by `-t` being its
inverse. -/
instance isIso_affineTranslationProduct : IsIso (affineTranslationProduct f t) :=
  ⟨affineTranslationProduct f (-t), by
      rw [affineTranslationProduct_comp, add_neg_cancel, affineTranslationProduct_zero], by
      rw [affineTranslationProduct_comp, neg_add_cancel, affineTranslationProduct_zero]⟩

/-- **The section of the chart at `t` is the zero section translated by `t`.** -/
theorem affinePointSection_eq_comp_affineTranslationProduct :
    affinePointSection f t =
      affinePointSection f (0 : Γ(S, ⊤)) ≫ affineTranslationProduct f t := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, affineTranslationProduct_comp_fst, affinePointSection_comp_fst,
      affinePointSection_comp_fst]
  · rw [Category.assoc, affineTranslationProduct_comp_snd, ← Category.assoc,
      affinePointSection_comp_snd, affinePointSection_comp_snd, Category.assoc,
      affineLineSection_zero, affineLineSection]

/-! ### The divisor cut out by the section at `t` -/

/-- The divisor cut out on the chart of the family by the zero section is an effective Cartier
divisor: it is the inverse image of the zero-section divisor of `X ×_S ℙ¹_S` under an open
immersion. -/
theorem isEffectiveCartierDivisor_ker_affinePointSection_zero :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (affinePointSection f (0 : Γ(S, ⊤))).ker := by
  rw [ker_affinePointSection, pointSection_zero]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (isEffectiveCartierDivisor_ker_zeroSection f)

/-- **The divisor cut out on the chart of the family by the section at `t` is an effective
Cartier divisor**: the translation by `t` carries the zero-section divisor to it. -/
theorem isEffectiveCartierDivisor_ker_affinePointSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (affinePointSection f t).ker := by
  rw [affinePointSection_eq_comp_affineTranslationProduct f t, ker_comp_eq_comap_ker_inv]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (isEffectiveCartierDivisor_ker_affinePointSection_zero f)

/-- The support of the divisor cut out by the section at `t` lies in the chart. -/
theorem supportSet_ker_pointSection_subset :
    (pointSection f t).ker.supportSet ⊆ Set.range (affineChartProduct f) := by
  rw [supportSet_ker_eq_range, ← affinePointSection_comp_affineChartProduct f t, range_comp_scheme]
  exact Set.image_subset_range _ _

/-- **The image of the section of `X ×_S ℙ¹_S ⟶ X` at an arbitrary point `t` of `ℙ¹_S` is an
effective Cartier divisor**, with no hypothesis on `X`, `S` or `t`. -/
theorem isEffectiveCartierDivisor_ker_pointSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (pointSection f t).ker := by
  refine isEffectiveCartierDivisor_of_comap_of_isOpenImmersion _ (affineChartProduct f)
    (supportSet_ker_pointSection_subset f t) ?_
  rw [← ker_affinePointSection]
  exact isEffectiveCartierDivisor_ker_affinePointSection f t

/-- **The image of the section at `t` is locally principal.** -/
theorem isLocallyPrincipal_ker_pointSection :
    Stacks.Divisors.IsLocallyPrincipal (pointSection f t).ker :=
  Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _
    (isEffectiveCartierDivisor_ker_pointSection f t)

end Family

/-! ### The divisor cut out on `ℙ¹_S` itself -/

section Line

variable (S : Scheme.{u}) (t : Γ(S, ⊤))

/-- A constant section of `𝔸¹_S` is a closed immersion, being the base change of the
corresponding point of `𝔸¹_ℤ`. -/
instance isClosedImmersion_affineLineConstantSection
    (e : (⊤_ Scheme.{u}) ⟶ Spec (.of (Polynomial (ULift.{u} ℤ)))) [IsClosedImmersion e] :
    IsClosedImmersion (affineLineConstantSection S e) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_affineLineConstantSection S e).flip inferInstance

/-- A constant section of `𝔸¹_S` is a split monomorphism. -/
instance isSplitMono_affineLineConstantSection
    (e : (⊤_ Scheme.{u}) ⟶ Spec (.of (Polynomial (ULift.{u} ℤ)))) :
    IsSplitMono (affineLineConstantSection S e) :=
  IsSplitMono.mk' ⟨affineLineOverHom S, affineLineConstantSection_comp_fst S e⟩

/-- The divisor cut out on `𝔸¹_S` by the zero section is an effective Cartier divisor: it is
the inverse image of `D₀ ⊆ ℙ¹_S` under the chart. -/
theorem isEffectiveCartierDivisor_ker_affineLineConstantSection_zero :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (affineLineConstantSection S integralAffineZeroSection).ker := by
  rw [← comap_lineZeroDivisor_affineChart S]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (lineZeroDivisor_isEffectiveCartierDivisor S)

/-- **The divisor cut out on `𝔸¹_S` by the section at `t` is an effective Cartier divisor**:
the translation by `t` carries the zero-section divisor to it. -/
theorem isEffectiveCartierDivisor_ker_affineLineSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (affineLineSection S t).ker := by
  rw [affineLineSection, ker_comp_eq_comap_ker_inv]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (isEffectiveCartierDivisor_ker_affineLineConstantSection_zero S)

/-- The divisor cut out on `ℙ¹_S` by the section at `t` meets the chart in the divisor cut out
there by the section at `t`. -/
theorem ker_affineLineSection_eq_comap :
    (affineLineSection S t).ker = (lineSection S t).ker.comap (affineChart S) :=
  AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (b := 𝟙 S) (i := lineSection S t)
    (IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, lineSection]⟩)

/-- The support of the divisor cut out on `ℙ¹_S` by the section at `t` lies in the chart. -/
theorem supportSet_ker_lineSection_subset :
    (lineSection S t).ker.supportSet ⊆ Set.range (affineChart S) := by
  rw [supportSet_ker_eq_range, lineSection, range_comp_scheme]
  exact Set.image_subset_range _ _

/-- **The image of the section of `ℙ¹_S ⟶ S` at an arbitrary point `t` is an effective Cartier
divisor on `ℙ¹_S`**, with no hypothesis on `S` or `t`. -/
theorem isEffectiveCartierDivisor_ker_lineSection :
    Stacks.Divisors.IsEffectiveCartierDivisor (lineSection S t).ker := by
  refine isEffectiveCartierDivisor_of_comap_of_isOpenImmersion _ (affineChart S)
    (supportSet_ker_lineSection_subset S t) ?_
  rw [← ker_affineLineSection_eq_comap]
  exact isEffectiveCartierDivisor_ker_affineLineSection S t

end Line

end Stacks.Chow

end

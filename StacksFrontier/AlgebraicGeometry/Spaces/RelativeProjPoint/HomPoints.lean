module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.AlgebraHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjHomBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.CanonicalSymHom

/-!
# A map of graded algebras on an algebraic space, over the scheme points of the base

In Situation 0849 let `ψ : 𝒜₁ ⟶ 𝒜₂` be a map of quasi-coherent graded `𝒪_X`-algebras, and let
`P = Proj_X(𝒜₁)` and `Q = Proj_X(𝒜₂)` be the relative Projs of Stacks 084C, presented through
their base changes to the scheme points of `X` by the second assertion of Stacks 084B
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`).

The restrictions `f^*ψ : f^*𝒜₁ ⟶ f^*𝒜₂` of `ψ` to the scheme points `f : T ⟶ X`
(`AlgebraicGeometry.Space.RelativeProjSituation.restrictHom`) commute with the identifications
`(f ∘ τ)^*𝒜ᵢ ≅ τ^*(f^*𝒜ᵢ)` of the restriction data of Stacks 084A of the two situations
(`AlgebraicGeometry.Space.RelativeProjSituation.restrictHom_comp_restrict_app`). So the family
`T, f ↦ f^*ψ` is a map of graded algebras over the scheme points of the base in the sense of
`AlgebraicGeometry.Space.RelativeProjHomPoints`, whose two compatibility conditions —
that the open `U(f^*ψ)` and the morphism `r_{f^*ψ}` of Tag 07ZG are compatible with base change in
the test object — are proved by
`AlgebraicGeometry.Space.GradedAlgebraRestriction.homPoints` from the canonicity of the
identifications of Stacks 084B. This is `AlgebraicGeometry.Space.RelativeProjSituation.homPoints`:
the data of Tag 085F attached to `ψ` itself, with nothing assumed.

The construction carries a composite to the composite
(`AlgebraicGeometry.Space.RelativeProjSituation.homPoints_comp`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.homPoints`: the map `ψ : 𝒜₁ ⟶ 𝒜₂`, read over the
  scheme points of the base, between the presentations of Stacks 084B of the two relative Projs.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.restrictHom_comp_restrict_app`: the restrictions
  of `ψ` commute with the restriction data of the two situations.
* `AlgebraicGeometry.Space.RelativeProjSituation.homPoints_comp`: `ψ ∘ φ` gives the composite of
  the maps given by `φ` and `ψ`.

## Implementation notes

The commutation `restrictHom_comp_restrict_app` is the inverted form of
`AlgebraicGeometry.Space.pointComparison_comp_pointAlgebraHom_app`. The restriction data of the
two situations unfold to inverses of the comparisons `AlgebraicGeometry.Space.pointComparison`
of the two shrunk situations, each spelled through its own situation; the proof first rewrites
each side, by lemmas stated in exactly the spelling the restriction data produce, into the spelling
of `pointComparison_comp_pointAlgebraHom_app`, and only then compares, so that no definitional
unfolding across the two spellings is asked of the elaborator.

## References

* [Stacks Project, Tag 0849](https://stacks.math.columbia.edu/tag/0849)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

universe u m

namespace AlgebraicGeometry.Space.RelativeProjHomPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}
    {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}

/-- Two maps of graded algebras over the scheme points of the base agree as soon as their
restrictions to the scheme points do: the two remaining fields are properties. -/
theorem ext {h₁ h₂ : RelativeProjHomPoints dP dQ} (h : h₁.hom = h₂.hom) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases h
  rfl

end AlgebraicGeometry.Space.RelativeProjHomPoints

namespace AlgebraicGeometry.Space.RelativeProjSituation

/-- Two inverses of equal morphisms are equal, whichever proofs of invertibility are used. -/
theorem inv_congr_of_eq {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y} (h : f = g)
    (i : IsIso f) (j : IsIso g) : @inv _ _ _ _ f i = @inv _ _ _ _ g j := by
  subst h
  rfl

/-- A commutative square with invertible horizontal sides, read with those sides inverted; the
invertibility is passed as proofs rather than found by instance search. -/
theorem comp_inv_eq_inv_comp_of_comp_eq {C : Type*} [Category C] {W X Y Z : C}
    {c₁ : W ⟶ X} {c₂ : Y ⟶ Z} {a : X ⟶ Z} {b : W ⟶ Y} (i₁ : IsIso c₁) (i₂ : IsIso c₂)
    (h : c₁ ≫ a = b ≫ c₂) : a ≫ inv c₂ = inv c₁ ≫ b := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, h]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-! ### The restriction datum of one situation, as inverted comparisons -/

section One

variable {𝒜 : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (hc : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜.piece i).val.obj U)
    (b : (𝒜.piece j).val.obj U), HEq ((𝒜.mul i j).app U a b) ((𝒜.mul j i).app U b a))
  (hn : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜.piece n))
  (hq : ∀ n : ℤ, (𝒜.piece n).IsQuasicoherentOnSite)
  (hk : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜.piece n).val.obj U) B.cutoff)
  {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1) (n : ℤ)

local notation "𝔰" => RelativeProjSituation.mk B S hS X 𝒜 hc hn hq hk

/-- The restriction map of the restriction datum is the inverse of the comparison of the shrunk
situation, spelled through that situation. -/
theorem quadrupleRestriction_restrict_app_eq_inv_shrink :
    ((𝔰).quadrupleRestriction.restrict τ f _ rfl).app n =
      @inv _ _ _ _ ((pointComparison (𝔰).shrink.algebra τ f _ rfl).app n)
        (isIso_pointComparison_app (𝔰).shrink.algebra (𝔰).shrink.isQuasicoherent τ f _ rfl n) :=
  rfl

/-- The comparison of the shrunk situation, spelled through the base of the situation. -/
theorem pointComparison_shrink_app :
    (pointComparison (𝔰).shrink.algebra τ f _ rfl).app n =
      (@pointComparison B S hS X (𝔰).shrink.algebra T T' τ f _ rfl).app n :=
  rfl

/-- The comparison of the shrunk situation is invertible in every degree. -/
theorem isIso_pointComparison_shrink_app :
    IsIso ((@pointComparison B S hS X (𝔰).shrink.algebra T T' τ f _ rfl).app n) :=
  @isIso_pointComparison_app B S hS X (𝔰).shrink.algebra (𝔰).shrink.isQuasicoherent T T' τ f _
    rfl n

/-- **The restriction map of the restriction datum of Situation 0849 is the inverse of the
comparison of restricted algebras.** -/
theorem quadrupleRestriction_restrict_app_eq_inv :
    ((𝔰).quadrupleRestriction.restrict τ f _ rfl).app n =
      @inv _ _ _ _ ((@pointComparison B S hS X (𝔰).shrink.algebra T T' τ f _ rfl).app n)
        (isIso_pointComparison_shrink_app hc hn hq hk τ f n) :=
  (quadrupleRestriction_restrict_app_eq_inv_shrink hc hn hq hk τ f n).trans
    (inv_congr_of_eq (pointComparison_shrink_app hc hn hq hk τ f n) _ _)

end One

/-! ### The restrictions of a map commute with the restriction data -/

section Map

variable {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "Φ" => shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ
local notation "α" => restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ

/-- The inverse image of `restrictHom` along a morphism of test objects, in degree `n`. -/
theorem restrictHom_pullback_toSituationHom_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    ((α T f).pullback ((BigFppfOver.toScheme B S hS).map τ)).toSituationHom.app n =
      (Stacks.RingedSpace.pullbackFunctor
        (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
          ((@pointAlgebraHom B S hS X _ _ Φ T f).app n) :=
  rfl

/-- `pointComparison_comp_pointAlgebraHom_app` for the shrunk situations, with the comparisons
inverted. -/
theorem pointAlgebraHom_comp_inv_pointComparison_shrink_app {T T' : BigFppfOver B S hS}
    (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (@pointAlgebraHom B S hS X _ _ Φ T' (yoneda.map τ ≫ f)).app n ≫
        @inv _ _ _ _ ((@pointComparison B S hS X (𝔰₂).shrink.algebra T T' τ f _ rfl).app n)
          (isIso_pointComparison_shrink_app h₂c h₂n h₂q h₂k τ f n) =
      @inv _ _ _ _ ((@pointComparison B S hS X (𝔰₁).shrink.algebra T T' τ f _ rfl).app n)
          (isIso_pointComparison_shrink_app h₁c h₁n h₁q h₁k τ f n) ≫
        (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
            ((@pointAlgebraHom B S hS X _ _ Φ T f).app n) :=
  comp_inv_eq_inv_comp_of_comp_eq (isIso_pointComparison_shrink_app h₁c h₁n h₁q h₁k τ f n)
    (isIso_pointComparison_shrink_app h₂c h₂n h₂q h₂k τ f n)
    (@pointComparison_comp_pointAlgebraHom_app B S hS X _ _ Φ T T' τ f _ rfl n)

/-- The left-hand side of `restrictHom_comp_restrict_app`, rewritten. -/
theorem restrictHom_comp_restrict_app_eq {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (α T' (yoneda.map τ ≫ f)).toSituationHom.app n ≫
        ((𝔰₂).quadrupleRestriction.restrict τ f _ rfl).app n =
      (@pointAlgebraHom B S hS X _ _ Φ T' (yoneda.map τ ≫ f)).app n ≫
        @inv _ _ _ _ ((@pointComparison B S hS X (𝔰₂).shrink.algebra T T' τ f _ rfl).app n)
          (isIso_pointComparison_shrink_app h₂c h₂n h₂q h₂k τ f n) := by
  rw [restrictHom_toSituationHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ T' _ n,
    quadrupleRestriction_restrict_app_eq_inv h₂c h₂n h₂q h₂k τ f n]
  rfl

/-- The right-hand side of `restrictHom_comp_restrict_app`, rewritten. -/
theorem restrict_comp_restrictHom_pullback_app_eq {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    ((𝔰₁).quadrupleRestriction.restrict τ f _ rfl).app n ≫
        ((α T f).pullback ((BigFppfOver.toScheme B S hS).map τ)).toSituationHom.app n =
      @inv _ _ _ _ ((@pointComparison B S hS X (𝔰₁).shrink.algebra T T' τ f _ rfl).app n)
          (isIso_pointComparison_shrink_app h₁c h₁n h₁q h₁k τ f n) ≫
        (Stacks.RingedSpace.pullbackFunctor
          (ringedSpaceHom ((BigFppfOver.toScheme B S hS).map τ))).map
            ((@pointAlgebraHom B S hS X _ _ Φ T f).app n) := by
  rw [restrictHom_pullback_toSituationHom_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ τ f n,
    quadrupleRestriction_restrict_app_eq_inv h₁c h₁n h₁q h₁k τ f n]
  rfl

/-- **The restrictions of a map of graded algebras commute with the restriction data**: for
`τ : T' ⟶ T` and a scheme point `f` at `T`, the restriction `(f ∘ τ)^*ψ` followed by the
identification `(f ∘ τ)^*𝒜₂ ≅ τ^*(f^*𝒜₂)` is the identification for `𝒜₁` followed by
`τ^*(f^*ψ)`. -/
theorem restrictHom_comp_restrict_app {T T' : BigFppfOver B S hS} (τ : T' ⟶ T)
    (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (α T' (yoneda.map τ ≫ f)).toSituationHom.app n ≫
        ((𝔰₂).quadrupleRestriction.restrict τ f _ rfl).app n =
      ((𝔰₁).quadrupleRestriction.restrict τ f _ rfl).app n ≫
        ((α T f).pullback ((BigFppfOver.toScheme B S hS).map τ)).toSituationHom.app n := by
  rw [restrictHom_comp_restrict_app_eq h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ τ f n,
    pointAlgebraHom_comp_inv_pointComparison_shrink_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ τ f n,
    restrict_comp_restrictHom_pullback_app_eq h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ τ f n]

/-- **A map `ψ : 𝒜₁ ⟶ 𝒜₂` of quasi-coherent graded `𝒪_X`-algebras, read over the scheme points of
the base**: at a scheme point `f : T ⟶ X` the restriction `f^*ψ`, between the presentations of
Stacks 084B of `Proj_X(𝒜₁)` and `Proj_X(𝒜₂)`. Both compatibility conditions of
`AlgebraicGeometry.Space.RelativeProjHomPoints` are proved, from
`restrictHom_comp_restrict_app` and the canonicity of the identifications of Stacks 084B
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.homPoints`). -/
noncomputable def homPoints :
    @RelativeProjHomPoints B S hS X.1 _ _ _ _ (𝔰₁).relativeProjPoints (𝔰₂).relativeProjPoints :=
  GradedAlgebraRestriction.homPoints (𝔰₁).quadrupleRestriction (𝔰₂).quadrupleRestriction
    (𝔰₁).shrink.contains_relativeProj_pointAlgebra (𝔰₂).shrink.contains_relativeProj_pointAlgebra
    α X.property.isSheaf
    (fun τ f n => restrictHom_comp_restrict_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ τ f n)

/-- At a scheme point of the base, `homPoints` is the restriction of the map. -/
theorem homPoints_hom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    (homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ).hom T f = α T f :=
  rfl

end Map


/-! ### Composites -/

section Comp

variable {𝒜₁ 𝒜₂ 𝒜₃ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (h₃c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₃.piece i).val.obj U)
    (b : (𝒜₃.piece j).val.obj U), HEq ((𝒜₃.mul i j).app U a b) ((𝒜₃.mul j i).app U b a))
  (h₃n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₃.piece n))
  (h₃q : ∀ n : ℤ, (𝒜₃.piece n).IsQuasicoherentOnSite)
  (h₃k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₃.piece n).val.obj U) B.cutoff)
  (φ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₂ 𝒜₃)

/-- `shrinkMap` carries a composite to the composite. -/
theorem shrinkMap_comp :
    shrinkMap h₁c h₁n h₁q h₁k h₃c h₃n h₃q h₃k (φ.comp ψ) =
      (shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k φ).comp
        (shrinkMap h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k ψ) :=
  @SheafOfModules.GradedAlgebra.smallPresentationMap_comp _ _ _ _ 𝒜₁ 𝒜₂
    (RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k).small_sections
    (RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k).small_sections 𝒜₃
    (RelativeProjSituation.mk B S hS X 𝒜₃ h₃c h₃n h₃q h₃k).small_sections φ ψ

/-- The degree-`n` component of `restrictHom` is that of the restriction `pointAlgebraHom`. -/
theorem restrictHom_app {𝒜 𝒜' : SheafOfModules.GradedAlgebra.{u, m, u, u + 1}
      (structureRingSheaf B S hS X)}
    (hc : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜.piece i).val.obj U)
      (b : (𝒜.piece j).val.obj U), HEq ((𝒜.mul i j).app U a b) ((𝒜.mul j i).app U b a))
    (hn : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜.piece n))
    (hq : ∀ n : ℤ, (𝒜.piece n).IsQuasicoherentOnSite)
    (hk : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
      HasCardinalLT ↥((𝒜.piece n).val.obj U) B.cutoff)
    (hc' : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜'.piece i).val.obj U)
      (b : (𝒜'.piece j).val.obj U), HEq ((𝒜'.mul i j).app U a b) ((𝒜'.mul j i).app U b a))
    (hn' : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜'.piece n))
    (hq' : ∀ n : ℤ, (𝒜'.piece n).IsQuasicoherentOnSite)
    (hk' : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
      HasCardinalLT ↥((𝒜'.piece n).val.obj U) B.cutoff)
    (χ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜 𝒜')
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (restrictHom hc hn hq hk hc' hn' hq' hk' χ T f).app n =
      (@pointAlgebraHom B S hS X _ _ (shrinkMap hc hn hq hk hc' hn' hq' hk' χ) T f).app n :=
  rfl

/-- The restriction to a scheme point of the shrunk composite is the composite of the
restrictions, in degree `n`. -/
theorem pointAlgebraHom_shrinkMap_comp_app (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1)
    (n : ℤ) :
    (@pointAlgebraHom B S hS X _ _
        (shrinkMap h₁c h₁n h₁q h₁k h₃c h₃n h₃q h₃k (φ.comp ψ)) T f).app n =
      (@pointAlgebraHom B S hS X _ _ (shrinkMap h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k φ) T f).app n ≫
        (@pointAlgebraHom B S hS X _ _
          (shrinkMap h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k ψ) T f).app n := by
  rw [shrinkMap_comp h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k φ ψ]
  exact pointAlgebraHom_comp_app _ _ T f n

/-- The restriction of a composite to a scheme point is the composite of the restrictions, in
degree `n`. -/
theorem restrictHom_comp_app (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (n : ℤ) :
    (restrictHom h₁c h₁n h₁q h₁k h₃c h₃n h₃q h₃k (φ.comp ψ) T f).app n =
      ((restrictHom h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k ψ T f).comp
        (restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k φ T f)).app n := by
  rw [SheafGradedAlgebraHom.comp_app, restrictHom_app, restrictHom_app, restrictHom_app,
    pointAlgebraHom_shrinkMap_comp_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k φ ψ T f n]
  rfl

/-- **The restriction of a composite to a scheme point is the composite of the restrictions.** -/
theorem restrictHom_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) :
    restrictHom h₁c h₁n h₁q h₁k h₃c h₃n h₃q h₃k (φ.comp ψ) T f =
      (restrictHom h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k ψ T f).comp
        (restrictHom h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k φ T f) :=
  SheafGradedAlgebraHom.ext
    (restrictHom_comp_app h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k φ ψ T f)

/-- **The map attached to a composite `ψ ∘ φ` is the composite of the maps attached to `φ` and
`ψ`**, as maps of graded algebras over the scheme points of the base. -/
theorem homPoints_comp :
    homPoints h₁c h₁n h₁q h₁k h₃c h₃n h₃q h₃k (φ.comp ψ) =
      (homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k φ).comp
        (homPoints h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k ψ) :=
  RelativeProjHomPoints.ext (funext fun T => funext fun f =>
    restrictHom_comp h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k φ ψ T f)

end Comp

end AlgebraicGeometry.Space.RelativeProjSituation

end

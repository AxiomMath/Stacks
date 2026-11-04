module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.SectionsInfinitesimalBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RestrictedSharpEndomorphism

/-!
# Lemma 0CKF: the bijection (0CKE) is an isomorphism of groups

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a scheme `S`, let `U₀ ⊆ U` be an
`R`-invariant closed subspace such that `U` is a first order thickening of `U₀`, let
`R₀ = s^{-1}(U₀) = t^{-1}(U₀)` and let `Γ₀` be the set of sections `δ` of `s` with
`δ|_{U₀} = e₀`, with the composition `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)` of
[Stacks Project, Tag 0CKC].  Equation [Stacks Project, Tag 0CKE],
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv`, is the bijection

`Hom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U}) ⟶ Γ₀,   θ ↦ θ · e`.

This file proves [Stacks Project, Tag 0CKF]: that bijection takes the sum of two linear maps to
the composite of the two sections.

## The argument

Instead of computing on the local rings at the geometric points, as the source does, the
comparison is made globally.  Write `λ_δ : R ⟶ R` for the left translation by a section `δ`,
`r ↦ c(δ(t(r)), r)`.  Then

* `δ₁ ∘ δ₂ = λ_{δ₁} ∘ δ₂` and `δ₁ = λ_{δ₁} ∘ e`, directly from the formula of the composition
  and the unit law of the groupoid;
* `λ_{δ₁}` is the identity on `R₀`: for `r ∈ R₀` the target `t(r)` lies in `U₀`, because `U₀` is
  invariant, so `δ₁(t(r)) = e(t(r))` and `c(e(t(r)), r) = r`.

The source's formula `D(ζ) = (δ₂ ∘ t)(D₁(ζ)) + D₂(ζ)` together with
[Stacks Project, Tag 0CKD] is replaced by the observation that **the difference of two elements
of `Γ₀` does not change when both are followed by an endomorphism of `R` which is the identity
on `R₀`** (`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_comp_eq`): the
difference is the derivation `x ↦ a^♯(x) - b^♯(x)` of `𝒪_{R₀}`, and following both by `λ`
replaces `x` by `λ^♯(x)`, which has the same image in `𝒪_{R₀}` as `x` when `λ|_{R₀} = id`.  On
the sheaf level this is
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_endomorphism` and
`AlgebraicGeometry.Space.restrictedEndomorphismSharp_comp_structureSharpRingInverseImage`.
Hence, writing `d(·, ·)` for the difference,

`d(e, δ₁ ∘ δ₂) = d(e, δ₁) + d(δ₁, δ₁ ∘ δ₂) = d(e, δ₁) + d(λ_{δ₁} ∘ e, λ_{δ₁} ∘ δ₂)
  = d(e, δ₁) + d(e, δ₂)`,

which is the assertion, the inverse of the bijection (0CKE) being `δ ↦ d(e, δ)`.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sectionTranslation`: the left translation
  `λ_δ : R ⟶ R`, `r ↦ c(δ(t(r)), r)`, by a section `δ` of the source.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.instMulInfinitesimalSections`: the composition
  of [Stacks Project, Tag 0CKC] on `Γ₀`, as a multiplication.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddMulEquiv`: **Lemma 0CKF** — the bijection
  of Equation (0CKE) as an isomorphism from the additive group of the linear maps onto `Γ₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionsGroup`: the group structure
  of `Γ₀` whose multiplication is the composition of sections and whose identity is the unit.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.sectionCompHom_eq_comp_sectionTranslation`:
  `δ₁ ∘ δ₂ = λ_{δ₁} ∘ δ₂`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow_comp_sectionTranslation`:
  `λ_δ ∘ e = δ`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.subspaceInclusion_comp_sectionTranslation`:
  `λ_δ` is the identity on `R₀` for `δ ∈ Γ₀`, when `U₀` is invariant.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionDiff_comp_eq`: the difference
  of two elements of `Γ₀` is unchanged by an endomorphism of `R` fixing `R₀`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv_add`: **Lemma 0CKF** — the
  bijection of Equation (0CKE) sends `θ₁ + θ₂` to `(θ₁ · e) ∘ (θ₂ · e)`.

## Implementation notes

**Hypotheses.**  Exactly those of the source's section: `U₀` is a closed subspace, `U` is a
first order thickening of `U₀`, and `U₀` is `R`-invariant, in the form
`U₀.preimage t = U₀.preimage s` of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsInvariantClosed`.  No flatness of `s` or `t` is
assumed: the source states the lemma without it, and the argument above does not use
[Stacks Project, Tag 0CKD], which is where flatness enters the source's proof.

**The group structure of `Γ₀`.**  The source calls `Γ₀` a group; its composition is
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.infinitesimalSectionComp`, which is installed here
as the multiplication of `Γ₀`.  `unitVAddMulEquiv` is a multiplicative equivalence from
`Multiplicative (Hom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U}))` onto `Γ₀` with that multiplication,
whose underlying function is the bijection (0CKE); in particular the composition of `Γ₀` is a
group law, which `infinitesimalSectionsGroup` records with the unit `e` as identity.

## References

* [Stacks Project, Tag 0CKF](https://stacks.math.columbia.edu/tag/0CKF)
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKC](https://stacks.math.columbia.edu/tag/0CKC)
* [Stacks Project, Tag 0CKB](https://stacks.math.columbia.edu/tag/0CKB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

open AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {Bas : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS Bas)

/-! ### Left translation by a section -/

/-- The pair `(δ ∘ t, id_R)` is composable: the source of `δ(t(r))` is `t(r)`. -/
theorem target_comp_section_comp_source (δ : Section G) :
    (G.target.hom ≫ δ.1.hom) ≫ G.source.hom = 𝟙 G.arrows.obj ≫ G.target.hom := by
  have h : δ.1.hom ≫ G.source.hom = 𝟙 G.objects.obj := congrArg (fun f => f.hom) δ.2
  rw [Category.assoc, h, Category.comp_id, Category.id_comp]

/-- **The left translation `λ_δ : R ⟶ R` by a section `δ` of the source**,
`r ↦ c(δ(t(r)), r)`: the groupoid composition applied to the composable pair `(δ ∘ t, id_R)`. -/
def sectionTranslation (δ : Section G) : G.arrows ⟶ G.arrows :=
  (ObjectProperty.homMk (pullback.lift (G.target.hom ≫ δ.1.hom) (𝟙 G.arrows.obj)
      (target_comp_section_comp_source G δ)) :
    G.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS G.source G.target) ≫ G.comp

/-- **The left translation at a point:** `λ_δ(r)` is the composite of `r` with the arrow `δ`
assigns to the target of `r`. -/
theorem sectionTranslation_hom_app (δ : Section G) (T : (BigFppfOver C S hS)ᵒᵖ)
    (r : G.arrows.obj.obj T)
    (h : G.source.hom.app T (δ.1.hom.app T (G.target.hom.app T r)) = G.target.hom.app T r) :
    (sectionTranslation G δ).hom.app T r =
      G.toGroupoidInFunctors.compose T (δ.1.hom.app T (G.target.hom.app T r)) r h :=
  composeMor_app G (G.target.hom ≫ δ.1.hom) (𝟙 G.arrows.obj)
    (target_comp_section_comp_source G δ) T r h

/-- A section of the source is a right inverse of the source pointwise. -/
private theorem source_hom_app_section (δ : Section G) (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : G.objects.obj.obj T) : G.source.hom.app T (δ.1.hom.app T z) = z :=
  congrArg (fun m : G.objects ⟶ G.objects => m.hom.app T z) δ.2

/-- **`δ₁ ∘ δ₂ = λ_{δ₁} ∘ δ₂`:** the composite of two sections of [Stacks Project, Tag 0CKC] is
the second followed by the left translation by the first. -/
theorem sectionCompHom_eq_comp_sectionTranslation (δ₁ δ₂ : Section G) :
    sectionCompHom G δ₁ δ₂ = δ₂.1 ≫ sectionTranslation G δ₁ := by
  apply ObjectProperty.hom_ext
  ext T y
  show (sectionCompHom G δ₁ δ₂).hom.app T y =
    (sectionTranslation G δ₁).hom.app T (δ₂.1.hom.app T y)
  rw [sectionCompHom_hom_app G δ₁ δ₂ T y (source_hom_app_section G δ₁ _ _),
    sectionTranslation_hom_app G δ₁ T _ (source_hom_app_section G δ₁ _ _)]

/-- **`λ_δ ∘ e = δ`:** the left translation by `δ` of the unit is `δ`, by the right unit law of
the groupoid. -/
theorem identityArrow_comp_sectionTranslation (δ : Section G) :
    identityArrow G ≫ sectionTranslation G δ = δ.1 := by
  apply ObjectProperty.hom_ext
  ext T y
  show (sectionTranslation G δ).hom.app T ((identityArrow G).hom.app T y) = δ.1.hom.app T y
  have hide : (identityArrow G).hom.app T y = G.toGroupoidInFunctors.identity T y :=
    identityArrow_hom_app G T y
  have htgt : G.target.hom.app T ((identityArrow G).hom.app T y) = y := by
    rw [hide]
    exact target_identity_app G T y
  have ha : δ.1.hom.app T (G.target.hom.app T ((identityArrow G).hom.app T y)) =
      δ.1.hom.app T y := by
    rw [htgt]
  have hb : (identityArrow G).hom.app T y =
      G.toGroupoidInFunctors.identity T (G.source.hom.app T (δ.1.hom.app T y)) := by
    rw [source_hom_app_section, hide]
  have h' : G.source.hom.app T (δ.1.hom.app T y) =
      G.target.hom.app T
        (G.toGroupoidInFunctors.identity T (G.source.hom.app T (δ.1.hom.app T y))) :=
    (target_identity_app G T _).symm
  rw [sectionTranslation_hom_app G δ T _ (source_hom_app_section G δ _ _),
    compose_congr G T ha hb (source_hom_app_section G δ _ _) h']
  exact compose_identity_right_app G T (δ.1.hom.app T y) h'

variable (U₀ : ClosedSubspaces C S hS G.objects.1)

/-- **The left translation by an element of `Γ₀` is the identity on `R₀`, when `U₀` is
invariant.**  For `r ∈ R₀ = s^{-1}(U₀) = t^{-1}(U₀)` the target `t(r)` lies in `U₀`, so
`δ(t(r)) = e(t(r))`, and `c(e(t(r)), r) = r` by the left unit law of the groupoid. -/
theorem subspaceInclusion_comp_sectionTranslation
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom)
    (δ : InfinitesimalSections G U₀) :
    subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) ≫
        sectionTranslation G δ.1 =
      subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) := by
  apply ObjectProperty.hom_ext
  ext T r
  show (sectionTranslation G δ.1).hom.app T r.val = r.val
  have hmem : G.target.hom.app T r.val ∈ U₀.1.obj T := by
    have hr : r.val ∈ (U₀.1.preimage G.target.hom).obj T := by
      rw [hinv]
      exact r.property
    exact hr
  have hres : δ.1.1.hom.app T (G.target.hom.app T r.val) =
      (identityArrow G).hom.app T (G.target.hom.app T r.val) :=
    congrArg (fun m : (⟨U₀.1.toFunctor, U₀.2.1⟩ : AlgebraicSpaces C S hS) ⟶ G.arrows =>
      m.hom.app T ⟨G.target.hom.app T r.val, hmem⟩) δ.2
  have ha : δ.1.1.hom.app T (G.target.hom.app T r.val) =
      G.toGroupoidInFunctors.identity T (G.target.hom.app T r.val) :=
    hres.trans (identityArrow_hom_app G T _)
  have h' : G.source.hom.app T
      (G.toGroupoidInFunctors.identity T (G.target.hom.app T r.val)) =
        G.target.hom.app T r.val :=
    source_identity_app G T _
  rw [sectionTranslation_hom_app G δ.1 T r.val (source_hom_app_section G δ.1 _ _),
    compose_congr G T ha rfl (source_hom_app_section G δ.1 _ _) h']
  exact compose_identity_app G T r.val h'

/-! ### The difference is unchanged by an endomorphism fixing `R₀` -/

/-- The transported comorphism depends on the morphism only, not on the proof that its
restriction to the thickening factors through `R₀`. -/
private theorem restrictedSharpThroughThickening_congr {X W : AlgebraicSpaces C S hS}
    (Z : ClosedSubspaces C S hS X.1) (W₀ : ClosedSubspaces C S hS W.1) {c c' : X ⟶ W}
    (hc : c = c')
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces C S hS))
    (h : subspaceInclusion C S hS X Z ≫ c = e₀ ≫ subspaceInclusion C S hS W W₀)
    (h' : subspaceInclusion C S hS X Z ≫ c' = e₀ ≫ subspaceInclusion C S hS W W₀) :
    restrictedSharpThroughThickening C S hS Z W₀ c e₀ h =
      restrictedSharpThroughThickening C S hS Z W₀ c' e₀ h' := by
  subst hc
  rfl

variable (hU₀ : IsFirstOrderThickening C S hS G.objects U₀.1)

include hU₀ in
/-- **The difference of two elements of `Γ₀` is unchanged when both are followed by an
endomorphism `λ` of `R` which is the identity on `R₀`.**

The difference is the descent of `x ↦ a^♯(x) - b^♯(x)` along `j^♯ : j^{-1}𝒪_R ⟶ 𝒪_{R₀}`.  The
transported comorphisms of `a ≫ λ` and `b ≫ λ` are those of `a` and `b` precomposed with the
endomorphism `λ̃` of `j^{-1}𝒪_R`
(`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp_endomorphism`), and
`λ̃(x) - x` is killed by `j^♯`
(`AlgebraicGeometry.Space.restrictedEndomorphismSharp_comp_structureSharpRingInverseImage`), so
the difference of `a` and `b` takes the same value at `λ̃(x)` as at `x`. -/
theorem infinitesimalSectionDiff_comp_eq (a b a' b' : InfinitesimalSections G U₀)
    (l : G.arrows ⟶ G.arrows)
    (hl : subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) ≫ l =
      subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀))
    (ha : a'.1.1 = a.1.1 ≫ l) (hb : b'.1.1 = b.1.1 ≫ l) :
    infinitesimalSectionDiff G U₀ hU₀ a' b' = infinitesimalSectionDiff G U₀ hU₀ a b := by
  have hres : ∀ δ δ' : InfinitesimalSections G U₀, δ'.1.1 = δ.1.1 ≫ l →
      restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
          δ'.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ'.2) =
        restrictedEndomorphismSharp C S hS (preimageSubspace C S hS G.source U₀) l hl ≫
          restrictedSharpThroughThickening C S hS U₀ (preimageSubspace C S hS G.source U₀)
            δ.1.1 (restrictedUnit G U₀) (comp_eq_restrictedUnit_comp G U₀ δ.2) := by
    intro δ δ' hδ
    have h' : subspaceInclusion C S hS G.objects U₀ ≫ δ.1.1 ≫ l =
        restrictedUnit G U₀ ≫
          subspaceInclusion C S hS G.arrows (preimageSubspace C S hS G.source U₀) :=
      (congrArg (subspaceInclusion C S hS G.objects U₀ ≫ ·) hδ).symm.trans
        (comp_eq_restrictedUnit_comp G U₀ δ'.2)
    exact (restrictedSharpThroughThickening_congr U₀ (preimageSubspace C S hS G.source U₀) hδ
      (restrictedUnit G U₀) _ h').trans
      (restrictedSharpThroughThickening_comp_endomorphism C S hS
        (preimageSubspace C S hS G.source U₀) U₀ δ.1.1 (restrictedUnit G U₀)
        (comp_eq_restrictedUnit_comp G U₀ δ.2) l hl h')
  have := isLocallySurjective_restrictedArrowsSharp G U₀
  have hd : ∀ (V : (Space.SmallEtale C S hS
        (⟨(preimageSubspace C S hS G.source U₀).1.toFunctor,
          (preimageSubspace C S hS G.source U₀).2.1⟩ : AlgebraicSpaces C S hS).1)ᵒᵖ)
      (x : ToType ((structureRingSheafInverseImage C S hS
        (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).obj.obj V)),
      (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a' b').toQuotientDerivation.d x =
        (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b).toQuotientDerivation.d x +
          (infinitesimalSectionLiftDifferenceData G U₀ hU₀ b b).toQuotientDerivation.d x := by
    intro V x
    show (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a' b').diff x =
      (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b).diff x +
        (infinitesimalSectionLiftDifferenceData G U₀ hU₀ b b).diff x
    rw [Stacks.Sites.LiftDifferenceData.diff_eq_zero_of_eq _
        ((infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ b b).trans
          (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ b b).symm) x, add_zero]
    have hf : (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a' b').f =
        restrictedEndomorphismSharp C S hS (preimageSubspace C S hS G.source U₀) l hl ≫
          (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b).f :=
      (infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ a' b').trans
        ((hres a a' ha).trans (congrArg (_ ≫ ·)
          (infinitesimalSectionLiftDifferenceData_f G U₀ hU₀ a b).symm))
    have hg : (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a' b').g =
        restrictedEndomorphismSharp C S hS (preimageSubspace C S hS G.source U₀) l hl ≫
          (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b).g :=
      (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ a' b').trans
        ((hres b b' hb).trans (congrArg (_ ≫ ·)
          (infinitesimalSectionLiftDifferenceData_g G U₀ hU₀ a b).symm))
    have hq : (structureSharpRingInverseImage C S hS (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).hom.app V
          ((restrictedEndomorphismSharp C S hS (preimageSubspace C S hS G.source U₀) l
            hl).hom.app V x) =
        (structureSharpRingInverseImage C S hS (subspaceInclusion C S hS G.arrows
          (preimageSubspace C S hS G.source U₀))).hom.app V x :=
      ringSheafHom_congr_app_apply
        (restrictedEndomorphismSharp_comp_structureSharpRingInverseImage C S hS
          (preimageSubspace C S hS G.source U₀) l hl) V x
    have hsplit := Stacks.Sites.LiftDifferenceData.diff_comp_eq_of_comp_eq
      (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b)
      (restrictedEndomorphismSharp C S hS (preimageSubspace C S hS G.source U₀) l hl) x hq
    refine (restrictedSquareZeroValues C S hS U₀ (preimageSubspace C S hS G.source U₀)
      (restrictedUnit G U₀) hU₀).ι_injective ?_
    exact ((infinitesimalSectionLiftDifferenceData G U₀ hU₀ a' b').ι_diff x).trans
      ((congrArg₂ (· - ·) (ringSheafHom_congr_app_apply hf V x)
        (ringSheafHom_congr_app_apply hg V x)).trans
        (((infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b).ι_diff _).symm.trans
          (congrArg _ hsplit)))
  have hadd := descendedDifferentialsHom_add C S hS (preimageProjection C S hS G.source U₀)
    (restrictedUnit G U₀) (conormalModule C S hS G.objects U₀)
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a b).toQuotientDerivation
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ b b).toQuotientDerivation
    (infinitesimalSectionLiftDifferenceData G U₀ hU₀ a' b').toQuotientDerivation
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ a b)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ b b)
    (descend_structureSharpInverseImage_eq_zero G U₀ hU₀ a' b') hd
  have hbb := infinitesimalSectionDiff_self G U₀ hU₀ b
  rw [infinitesimalSectionDiff_eq] at hbb
  rw [infinitesimalSectionDiff_eq, infinitesimalSectionDiff_eq]
  refine hadd.symm.trans ?_
  refine (congrArg (_ + ·) hbb).trans (add_zero _)

/-! ### Lemma 0CKF -/

/-- **The group law of `Γ₀`:** the composition `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)` of
[Stacks Project, Tag 0CKC], restricted to the sections infinitesimally close to the unit. -/
instance instMulInfinitesimalSections : Mul (InfinitesimalSections G U₀) :=
  ⟨infinitesimalSectionComp G U₀⟩

/-- The product `δ₁ * δ₂` of two sections in `Γ₀` is their composite
`infinitesimalSectionComp G U₀ δ₁ δ₂`. -/
theorem infinitesimalSections_mul_def (δ₁ δ₂ : InfinitesimalSections G U₀) :
    δ₁ * δ₂ = infinitesimalSectionComp G U₀ δ₁ δ₂ := rfl

include hU₀ in
/-- **Lemma 0CKF.**  Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, `U₀ ⊆ U` an
`R`-invariant closed subspace such that `U` is a first order thickening of `U₀`.  The bijection
of Equation [Stacks Project, Tag 0CKE],
`θ ↦ θ · e` from `Hom_{𝒪_{U₀}}(e₀^*Ω_{R₀/U₀}, 𝒞_{U₀/U})` onto `Γ₀`, sends a sum of linear maps
to the composite of the corresponding sections:

`(θ₁ + θ₂) · e = (θ₁ · e) ∘ (θ₂ · e)`.

With `InfinitesimalSectionDifference.unitVAddEquiv_zero` (`0 · e = e`) this says that the
bijection is an isomorphism of groups. -/
@[stacks 0CKF "the bijection theta |-> theta . e of (0CKE) carries the sum of two linear maps \
e_0^*Omega_{R_0/U_0} -> C_{U_0/U} to the composite of the two sections in Gamma_0, for an \
R-invariant first order thickening U_0 of U"]
theorem unitVAddEquiv_add (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom)
    (θ₁ θ₂ : InfinitesimalSectionsHom G U₀) :
    unitVAddEquiv G U₀ hU₀ (θ₁ + θ₂) =
      infinitesimalSectionComp G U₀ (unitVAddEquiv G U₀ hU₀ θ₁) (unitVAddEquiv G U₀ hU₀ θ₂) := by
  set D := infinitesimalSectionDifference G U₀ hU₀
  set δ₁ := unitVAddEquiv G U₀ hU₀ θ₁
  set δ₂ := unitVAddEquiv G U₀ hU₀ θ₂
  have hsymm : ∀ δ, (unitVAddEquiv G U₀ hU₀).symm δ =
      infinitesimalSectionDiff G U₀ hU₀ (unitInfinitesimalSection G U₀) δ :=
    fun δ => D.unitVAddEquiv_symm_apply δ
  refine ((unitVAddEquiv G U₀ hU₀).symm_apply_eq).1 ?_ |>.symm
  rw [hsymm, ← infinitesimalSectionDiff_add_infinitesimalSectionDiff G U₀ hU₀
    (unitInfinitesimalSection G U₀) δ₁]
  have h₁ : infinitesimalSectionDiff G U₀ hU₀ (unitInfinitesimalSection G U₀) δ₁ = θ₁ := by
    rw [← hsymm, Equiv.symm_apply_apply]
  have h₂ : infinitesimalSectionDiff G U₀ hU₀ (unitInfinitesimalSection G U₀) δ₂ = θ₂ := by
    rw [← hsymm, Equiv.symm_apply_apply]
  have h₁₂ : infinitesimalSectionDiff G U₀ hU₀ δ₁ (infinitesimalSectionComp G U₀ δ₁ δ₂) =
      infinitesimalSectionDiff G U₀ hU₀ (unitInfinitesimalSection G U₀) δ₂ :=
    infinitesimalSectionDiff_comp_eq G U₀ hU₀ _ _ _ _ (sectionTranslation G δ₁.1)
      (subspaceInclusion_comp_sectionTranslation G U₀ hinv δ₁)
      (identityArrow_comp_sectionTranslation G δ₁.1).symm
      (sectionCompHom_eq_comp_sectionTranslation G δ₁.1 δ₂.1)
  rw [h₁₂, h₁, h₂]

include hU₀ in
/-- **Lemma 0CKF, bundled: the bijection (0CKE) is an isomorphism of groups.**  For an
`R`-invariant closed subspace `U₀ ⊆ U` of which `U` is a first order thickening, the bijection
`θ ↦ θ · e` of Equation [Stacks Project, Tag 0CKE] is a multiplicative equivalence from the
additive group of the `𝒪_{U₀}`-linear maps `e₀^*Ω_{R₀/U₀} ⟶ 𝒞_{U₀/U}` (written
multiplicatively) onto `Γ₀` with the composition of [Stacks Project, Tag 0CKC]. -/
@[stacks 0CKF "the bijection Hom_{O_{U_0}}(e_0^*Omega_{R_0/U_0}, C_{U_0/U}) -> Gamma_0 of (0CKE) \
as an isomorphism from the additive group of linear maps onto Gamma_0 with its composition, for \
an R-invariant first order thickening U_0 of U"]
noncomputable def unitVAddMulEquiv
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom) :
    Multiplicative (InfinitesimalSectionsHom G U₀) ≃* InfinitesimalSections G U₀ where
  toEquiv := Multiplicative.toAdd.trans (unitVAddEquiv G U₀ hU₀)
  map_mul' θ₁ θ₂ := unitVAddEquiv_add G U₀ hU₀ hinv θ₁.toAdd θ₂.toAdd

include hU₀ in
/-- The underlying function of `unitVAddMulEquiv` is the bijection of Equation (0CKE). -/
theorem unitVAddMulEquiv_apply
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom)
    (θ : Multiplicative (InfinitesimalSectionsHom G U₀)) :
    unitVAddMulEquiv G U₀ hU₀ hinv θ = unitVAddEquiv G U₀ hU₀ θ.toAdd := rfl

include hU₀ in
/-- The bijection of Equation (0CKE) sends the zero map to the unit, as a statement about
`unitVAddMulEquiv`. -/
theorem unitVAddMulEquiv_one
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom) :
    unitVAddMulEquiv G U₀ hU₀ hinv 1 = unitInfinitesimalSection G U₀ :=
  (infinitesimalSectionDifference G U₀ hU₀).unitVAddEquiv_zero

include hU₀ in
/-- **`Γ₀` is a group under the composition of [Stacks Project, Tag 0CKC]**, with the unit `e`
for its identity: the group law transported from the linear maps along the bijection of
Equation (0CKE), whose multiplication *is* the composition of sections, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv_add`.  The inverse of `δ = θ · e` is
`(-θ) · e`. -/
@[reducible] noncomputable def infinitesimalSectionsGroup
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom) :
    Group (InfinitesimalSections G U₀) where
  mul := infinitesimalSectionComp G U₀
  one := unitInfinitesimalSection G U₀
  inv δ := unitVAddMulEquiv G U₀ hU₀ hinv ((unitVAddMulEquiv G U₀ hU₀ hinv).symm δ)⁻¹
  mul_assoc a b c := (unitVAddMulEquiv G U₀ hU₀ hinv).symm.injective (by
    change (unitVAddMulEquiv G U₀ hU₀ hinv).symm (infinitesimalSectionComp G U₀
        (infinitesimalSectionComp G U₀ a b) c) =
      (unitVAddMulEquiv G U₀ hU₀ hinv).symm (infinitesimalSectionComp G U₀ a
        (infinitesimalSectionComp G U₀ b c))
    simp only [← infinitesimalSections_mul_def, map_mul, mul_assoc])
  one_mul a := (unitVAddMulEquiv G U₀ hU₀ hinv).symm.injective (by
    change (unitVAddMulEquiv G U₀ hU₀ hinv).symm
      (infinitesimalSectionComp G U₀ (unitInfinitesimalSection G U₀) a) = _
    rw [← infinitesimalSections_mul_def, map_mul, ← unitVAddMulEquiv_one G U₀ hU₀ hinv,
      MulEquiv.symm_apply_apply, one_mul])
  mul_one a := (unitVAddMulEquiv G U₀ hU₀ hinv).symm.injective (by
    change (unitVAddMulEquiv G U₀ hU₀ hinv).symm
      (infinitesimalSectionComp G U₀ a (unitInfinitesimalSection G U₀)) = _
    rw [← infinitesimalSections_mul_def, map_mul, ← unitVAddMulEquiv_one G U₀ hU₀ hinv,
      MulEquiv.symm_apply_apply, mul_one])
  inv_mul_cancel a := (unitVAddMulEquiv G U₀ hU₀ hinv).symm.injective (by
    change (unitVAddMulEquiv G U₀ hU₀ hinv).symm (infinitesimalSectionComp G U₀
      (unitVAddMulEquiv G U₀ hU₀ hinv ((unitVAddMulEquiv G U₀ hU₀ hinv).symm a)⁻¹) a) =
      (unitVAddMulEquiv G U₀ hU₀ hinv).symm (unitInfinitesimalSection G U₀)
    rw [← infinitesimalSections_mul_def, map_mul, MulEquiv.symm_apply_apply,
      ← unitVAddMulEquiv_one G U₀ hU₀ hinv, MulEquiv.symm_apply_apply, inv_mul_cancel])

/-- The multiplication of the group `Γ₀` is the composition of sections. -/
theorem infinitesimalSectionsGroup_mul
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom)
    (δ₁ δ₂ : InfinitesimalSections G U₀) :
    letI := infinitesimalSectionsGroup G U₀ hU₀ hinv
    δ₁ * δ₂ = infinitesimalSectionComp G U₀ δ₁ δ₂ := rfl

/-- The identity of the group `Γ₀` is the unit section. -/
theorem infinitesimalSectionsGroup_one
    (hinv : U₀.1.preimage G.target.hom = U₀.1.preimage G.source.hom) :
    letI := infinitesimalSectionsGroup G U₀ hU₀ hinv
    (1 : InfinitesimalSections G U₀) = unitInfinitesimalSection G U₀ := rfl

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end

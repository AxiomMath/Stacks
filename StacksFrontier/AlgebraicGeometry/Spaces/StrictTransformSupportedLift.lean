module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspacePowerChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformLocalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsLift
public import StacksFrontier.AlgebraicGeometry.Spaces.PrincipalChartDiagramCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Lifting sections supported on the exceptional preimage

Let `b : A' ⟶ A` be a morphism of algebraic spaces over a scheme `S`, let `f : X ⟶ A` be an
algebraic space over `A`, let `E ⊆ A'` be a closed subspace and let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a
sequence of quasi-coherent `𝒪_X`-modules which stays short exact after every base change
`Y ⟶ A`.  This file proves that, when `E` is an effective Cartier divisor, the morphism induced
on the subsheaves of sections of `pr_X^*Fᵢ` supported on the exceptional preimage
`|pr_{A'}^{-1}E|` is an epimorphism.  By
`AlgebraicGeometry.Space.exact_supportedQuotientShortComplex_iff` that is exactly exactness in
the middle of the sequence of strict transforms, so this is the content of Stacks 0869 beyond
the two halves settled for an arbitrary pair `(b, E)`; the tag itself is assembled in
`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformShortExactBlowup.lean`.

## Main results

* `AlgebraicGeometry.Space.epi_supportedSectionsMap`: **the induced morphism on the supported
  sections is an epimorphism**, with
  `AlgebraicGeometry.Space.isLocallySurjective_supportedSectionsMap` the local surjectivity it
  is read off.
* `AlgebraicGeometry.Space.surjective_supportedSectionsMap_val_app`: over a chart on which the
  exceptional preimage has a local equation, the induced morphism is surjective on sections.
* `AlgebraicGeometry.Space.injective_val_app_modulePullback_map_f`: the left-hand map of the
  base change of the sequence to a thickening of the exceptional preimage is injective on the
  sections over every chart.
* `AlgebraicGeometry.Space.isPullback_exceptionalThickening` and
  `AlgebraicGeometry.Space.isPullback_exceptionalThickening_comp`: the preimage of a closed
  subspace of `A'` in `X ×_A A'` is the fibre product, and is a base change of `X` over `A`.
* `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_span` and
  `AlgebraicGeometry.Space.definingIdealAt_preimage_iterSum_eq_span`: the local equation of the
  exceptional preimage, and of the preimage of an `n`-fold sum of `E`, on a chart of `X ×_A A'`.

## The argument

This is the argument of the scheme-level Stacks 080W, run on the charts of the small étale site
of `X ×_A A'` rather than transported along Stacks 0863.  Fix a chart `W` of `X ×_A A'` which is
affine and lies over an affine chart `V` of `A'` on which the defining ideal of `E` is generated
by one function `a`; such charts generate covering sieves by
`AlgebraicGeometry.Space.mem_topology_of_hasPrincipalChartDiagram`, because an effective Cartier
divisor has a local equation on an étale chart through every point (Stacks 083C).  Over `W`:

* a section `s` of `pr_X^*F₃` supported on the exceptional preimage is annihilated by a power of
  `a`, by Stacks 0859 part (2);
* `s` lifts to a section `y` of `pr_X^*F₂`, the sections of a short exact sequence of
  quasi-coherent modules over an affine chart being right exact;
* `a ^ n • y` comes from a section `x` of `pr_X^*F₁`, by exactness of the sections in the middle;
* `x` is divisible by `a ^ n`: the `n`-fold sum of `E` with itself is a closed subspace of `A'`
  whose defining ideal at `V` is `(a ^ n)`, its preimage in `X ×_A A'` is a base change of `X`
  over `A`, so the universal short exactness makes the left-hand map injective after that base
  change, and reading that off the chart gives the divisibility;
* correcting `y` by the image of the quotient gives a section of `pr_X^*F₂` annihilated by
  `a ^ n`, hence supported on the exceptional preimage, which maps to `s`.

The last three steps are `AlgebraicGeometry.Space.injective_val_app_modulePullback_map_f`,
`AlgebraicGeometry.Space.exists_eq_smul_of_injective_of_ker_eq_span` and
`Stacks.SupportedSectionsLift.exists_smul_eq_zero_of_divisibility`.

Two incidental choices.  The abelian structure on sheaves of modules is installed as a local
instance at a raised priority, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModulePushforwardRightExact.lean`: the
generic one leaves the module universe a join that is never the universe `u` of the schemes, and
a search reaching it first ends in an unsolvable universe constraint.  And the three small
commutative-algebra steps are stated over abstract rings rather than over the chart rings, since
performed in place they exceed the heartbeat ceiling at `isDefEq` on the instance paths of the
chart ring.

## References

* [Stacks Project, Tag 0869](https://stacks.math.columbia.edu/tag/0869)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A cartesian square of algebraic spaces is detected on the underlying presheaves: the
inclusion of the algebraic spaces into the presheaves on the big fppf site is fully faithful,
and a fully faithful functor reflects limits. -/
theorem isPullback_of_isPullback_hom {F G H P : AlgebraicSpaces B S hS} {f : F ⟶ H} {g : G ⟶ H}
    {fst : P ⟶ F} {snd : P ⟶ G} (sq : IsPullback fst.hom snd.hom f.hom g.hom) :
    IsPullback fst snd f g :=
  sq.of_map_of_faithful (ObjectProperty.ι _)

section Thickening

variable {A X A' : AlgebraicSpaces B S hS}

/-- A closed subspace of an algebraic space, read as an algebraic space over `S`. -/
abbrev subspaceSpace (Zc : ClosedSubspaces B S hS A'.1) : AlgebraicSpaces B S hS :=
  ⟨Zc.1.toFunctor, Zc.2.1⟩

/-- The inclusion of a closed subspace, read as a morphism of algebraic spaces. -/
abbrev subspaceSpaceι (Zc : ClosedSubspaces B S hS A'.1) : subspaceSpace B S hS Zc ⟶ A' :=
  ObjectProperty.homMk Zc.1.ι

/-- The preimage `pr_{A'}^{-1}Zc` of a closed subspace `Zc ⊆ A'` in `X ×_A A'`, read as an
algebraic space over `S`. -/
abbrev exceptionalThickening (f : X ⟶ A) (b : A' ⟶ A) (Zc : ClosedSubspaces B S hS A'.1) :
    AlgebraicSpaces B S hS :=
  subspaceSpace B S hS (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b) Zc)

/-- The inclusion of `pr_{A'}^{-1}Zc` into `X ×_A A'`. -/
abbrev exceptionalThickeningι (f : X ⟶ A) (b : A' ⟶ A) (Zc : ClosedSubspaces B S hS A'.1) :
    exceptionalThickening B S hS f b Zc ⟶ strictTransformPullback B S hS f b :=
  subspaceSpaceι B S hS (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b) Zc)

/-- The projection of `pr_{A'}^{-1}Zc` onto `Zc`. -/
abbrev exceptionalThickeningToSubspace (f : X ⟶ A) (b : A' ⟶ A)
    (Zc : ClosedSubspaces B S hS A'.1) :
    exceptionalThickening B S hS f b Zc ⟶ subspaceSpace B S hS Zc :=
  ObjectProperty.homMk (Zc.1.fromPreimage (strictTransformPullbackToBlowUp B S hS f b).hom)

/-- **The preimage of a closed subspace of `A'` is the fibre product.**  Stacks 083Q. -/
theorem isPullback_exceptionalThickening (f : X ⟶ A) (b : A' ⟶ A)
    (Zc : ClosedSubspaces B S hS A'.1) :
    IsPullback (exceptionalThickeningι B S hS f b Zc)
      (exceptionalThickeningToSubspace B S hS f b Zc)
      (strictTransformPullbackToBlowUp B S hS f b) (subspaceSpaceι B S hS Zc) :=
  isPullback_of_isPullback_hom B S hS
    (CategoryTheory.Subfunctor.isPullback_preimage
      (strictTransformPullbackToBlowUp B S hS f b).hom Zc.1).flip

/-- **The preimage of a closed subspace of `A'` is a base change of `X` over `A`.**  Pasting the
cartesian square of the preimage with the cartesian square defining `X ×_A A'`. -/
theorem isPullback_exceptionalThickening_comp (f : X ⟶ A) (b : A' ⟶ A)
    (Zc : ClosedSubspaces B S hS A'.1) :
    IsPullback (exceptionalThickeningι B S hS f b Zc ≫
        strictTransformPullbackToSource B S hS f b)
      (exceptionalThickeningToSubspace B S hS f b Zc) f (subspaceSpaceι B S hS Zc ≫ b) :=
  ((isPullback_exceptionalThickening B S hS f b Zc).flip.paste_vert
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f b).flip).flip

end Thickening

/-! ### Injectivity after base change to a thickening of the exceptional preimage -/

section Injectivity

variable {A X A' : AlgebraicSpaces B S hS}

/-- **The left-hand map of the base change of `C` to `pr_{A'}^{-1}Zc` is injective on the
sections over every chart.**

The universal short exactness of `C` is applied to the cartesian square of
`AlgebraicGeometry.Space.isPullback_exceptionalThickening_comp`, which presents
`pr_{A'}^{-1}Zc` as the base change of `X` along `Zc ⟶ A' ⟶ A`; a monomorphism of sheaves of
modules is injective on sections, and the comparison of a composite of inverse images with the
composite of the comparisons, `AlgebraicGeometry.Space.modulePullbackCompIso`, carries that
across to the two-step base change. -/
theorem injective_val_app_modulePullback_map_f (f : X ⟶ A) (b : A' ⟶ A)
    (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact)
    (Zc : ClosedSubspaces B S hS A'.1)
    (V : (SmallEtale B S hS (exceptionalThickening B S hS f b Zc).1)ᵒᵖ) :
    Function.Injective
      (((modulePullback B S hS (exceptionalThickeningι B S hS f b Zc)).map
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map
          C.f)).val.app V) := by
  have hse := hC (subspaceSpace B S hS Zc) (exceptionalThickening B S hS f b Zc)
    (subspaceSpaceι B S hS Zc ≫ b)
    (exceptionalThickeningι B S hS f b Zc ≫ strictTransformPullbackToSource B S hS f b)
    (exceptionalThickeningToSubspace B S hS f b Zc)
    (isPullback_exceptionalThickening_comp B S hS f b Zc)
  have h0 : Function.Injective
      (((modulePullback B S hS (exceptionalThickeningι B S hS f b Zc ≫
        strictTransformPullbackToSource B S hS f b)).map C.f).val.app V) :=
    SheafOfModules.injective_f_val_app_of_shortExact hse V
  have hα := modulePullbackCompIso B S hS (exceptionalThickeningι B S hS f b Zc)
    (strictTransformPullbackToSource B S hS f b)
  have hbij := SheafOfModules.bijective_iso_hom_val_app (hα.app C.X₁) V
  have hnat : ∀ x, (hα.hom.app C.X₂).val.app V
        ((((modulePullback B S hS (exceptionalThickeningι B S hS f b Zc)).map
          ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map
            C.f)).val.app V) x) =
      (((modulePullback B S hS (exceptionalThickeningι B S hS f b Zc ≫
        strictTransformPullbackToSource B S hS f b)).map C.f).val.app V)
        ((hα.hom.app C.X₁).val.app V x) := by
    intro x
    exact congrArg (fun m : (modulePullback B S hS
      (exceptionalThickeningι B S hS f b Zc)).obj
        ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj C.X₁) ⟶ _ =>
      m.val.app V x) (hα.hom.naturality C.f)
  exact fun x y hxy => hbij.1 (h0 ((hnat x).symm.trans
    ((congrArg (fun z => (hα.hom.app C.X₂).val.app V z) hxy).trans (hnat y))))

end Injectivity

/-! ### The local equation of a thickening of the exceptional preimage -/

section LocalEquation

variable {A X A' : AlgebraicSpaces B S hS}

/-- The extension of a principal ideal along a ring map is the principal ideal generated by the
image of the generator. -/
private theorem ideal_map_span_singleton {R₀ R₁ : Type*} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (x : R₀) : Ideal.map φ (Ideal.span {x}) = Ideal.span {φ x} := by
  rw [Ideal.map_span, Set.image_singleton]

/-- The defining ideal of the preimage of a closed subspace on a chart of `X ×_A A'` is generated
by the image of a generator of its defining ideal on a chart of `A'` below it. -/
private theorem definingIdealAt_preimage_eq_span_map (f : X ⟶ A) (b : A' ⟶ A)
    (Z : ClosedSubspaces B S hS A'.1)
    (W : SmallEtale B S hS (strictTransformPullback B S hS f b).1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left))
    (V : SmallEtale B S hS A'.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
    (ha : definingIdealAt B S hS A' Z (op V) = Ideal.span {a}) :
    definingIdealAt B S hS (strictTransformPullback B S hS f b)
        (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b) Z) (op W) =
      Ideal.span {((BigFppfOver.toScheme B S hS).map q).appTop.hom a} :=
  (definingIdealAt_preimage_eq_map B S hS (strictTransformPullbackToBlowUp B S hS f b)
    Z V W q hq).trans
    ((congrArg (Ideal.map ((BigFppfOver.toScheme B S hS).map q).appTop.hom) ha).trans
      (ideal_map_span_singleton _ a))

/-- **The local equation of the `n`-fold thickening of `E`, pulled back to a chart of
`X ×_A A'`.**  On an affine chart `W` of `X ×_A A'` lying over an affine chart `V` of `A'` over
the atlas chart, if the defining ideal of `E` at `V` is generated by `a`, then the defining ideal
of `pr_{A'}^{-1}(E + ⋯ + E)` at `W` is generated by the `(n+1)`st power of the pullback of `a`.

The inverse image of a closed subspace is cut out on a chart by the extension of the ideal
(`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_map`), and the defining ideal of the
`n`-fold sum is the `(n+1)`st power
(`AlgebraicGeometry.Space.definingIdealAt_iterSumClosedSubspaces_eq_span_pow`). -/
theorem definingIdealAt_preimage_iterSum_eq_span (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1) (n : ℕ)
    (W : SmallEtale B S hS (strictTransformPullback B S hS f b).1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left))
    (V : SmallEtale B S hS A'.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)
    (m : V ⟶ (⟨CostructuredArrow.mk (atlasHom B S hS A'), atlasHom_etale B S hS A'⟩ :
      SmallEtale B S hS A'.1))
    (a : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
    (ha : definingIdealAt B S hS A' E (op V) = Ideal.span {a}) :
    definingIdealAt B S hS (strictTransformPullback B S hS f b)
        (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b)
          (iterSumClosedSubspaces B S hS A' E n)) (op W) =
      Ideal.span {((BigFppfOver.toScheme B S hS).map q).appTop.hom a ^ (n + 1)} := by
  rw [← map_pow]
  exact definingIdealAt_preimage_eq_span_map B S hS f b _ W hW V hV q hq _
    (definingIdealAt_iterSumClosedSubspaces_eq_span_pow B S hS A' E n V m a ha)

/-- **The local equation of the exceptional preimage on a chart of `X ×_A A'`.**  The case
`n = 0` of `AlgebraicGeometry.Space.definingIdealAt_preimage_iterSum_eq_span`, written without
the exponent. -/
theorem definingIdealAt_preimage_eq_span (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1)
    (W : SmallEtale B S hS (strictTransformPullback B S hS f b).1)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left))
    (V : SmallEtale B S hS A'.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left))
    (q : W.1.left ⟶ V.1.left)
    (hq : yoneda.map q ≫ V.1.hom = W.1.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)
    (a : Γ((BigFppfOver.toScheme B S hS).obj V.1.left, ⊤))
    (ha : definingIdealAt B S hS A' E (op V) = Ideal.span {a}) :
    definingIdealAt B S hS (strictTransformPullback B S hS f b)
        (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b) E) (op W) =
      Ideal.span {((BigFppfOver.toScheme B S hS).map q).appTop.hom a} :=
  definingIdealAt_preimage_eq_span_map B S hS f b E W hW V hV q hq a ha

end LocalEquation

/-! ### Lifting a supported section over a principal chart -/

section ChartSurjectivity

variable {A X A' : AlgebraicSpaces B S hS}

/-- A power of a ring element one higher than the exponent lies in that power of the principal
ideal it generates. -/
private theorem pow_succ_mem_span_pow {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    x ^ (n + 1) ∈ (Ideal.span {x} : Ideal R) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨x, (pow_succ' x n).symm⟩

/-- An element annihilated by `x ^ (n + 1)` is annihilated by the `(n+1)`st power of the
principal ideal generated by `x`. -/
private theorem smul_eq_zero_of_mem_span_pow {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] (x : R) (n : ℕ) (y : M) (hy : x ^ (n + 1) • y = 0)
    (c : R) (hc : c ∈ (Ideal.span {x} : Ideal R) ^ (n + 1)) : c • y = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hc
  obtain ⟨r, rfl⟩ := hc
  rw [mul_smul, hy, smul_zero]

/-- **A section of `pr_X^*F₃` supported on the exceptional preimage lifts, over an affine chart
carrying a local equation, to a section of `pr_X^*F₂` supported there.**

This is the argument of the scheme-level Stacks 080W.  Over the chart the exceptional preimage is
cut out by one function `aW`, so being supported on it means being annihilated by a power of
`aW` (Stacks 0859, part (2)); the sections of a short exact sequence of quasi-coherent modules
over an affine chart are exact, and surjective on the right; and the universal short exactness
supplies the divisibility, by base change along the `n`-fold sum of the exceptional divisor,
whose local equation is the corresponding power of `aW`. -/
theorem surjective_supportedSectionsMap_val_app_of_span (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1)
    (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact)
    (hq1 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₁).IsQuasicoherentOnSite)
    (hq2 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₂).IsQuasicoherentOnSite)
    (hq3 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₃).IsQuasicoherentOnSite)
    (W : SmallEtale B S hS (strictTransformPullback B S hS f b).1)
    (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left))
    (aW : chartRing B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2 W)
    (hzl : chartPointsMap W ⁻¹' exceptionalPreimageSet B S hS f b E.1 =
      (chartScheme W).zeroLocus (U := ⊤)
        ((Ideal.span {aW} : Ideal (chartRing B S hS (strictTransformPullback B S hS f b).1
            (strictTransformPullback B S hS f b).2 W)) :
          Set (chartRing B S hS (strictTransformPullback B S hS f b).1
            (strictTransformPullback B S hS f b).2 W)))
    (hthick : ∀ n : ℕ, definingIdealAt B S hS (strictTransformPullback B S hS f b)
      (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b)
        (iterSumClosedSubspaces B S hS A' E n)) (op W) = Ideal.span {aW ^ (n + 1)}) :
    Function.Surjective ((supportedSectionsMap (exceptionalPreimageSet B S hS f b E.1)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g)).val.app
      (op W)) := by
  have hD : (C.map (modulePullback B S hS
      (strictTransformPullbackToSource B S hS f b))).ShortExact :=
    hC A' (strictTransformPullback B S hS f b) b _ _
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f b)
  intro s
  have hsupp := (mem_supportedSectionsSubmodule_iff B S hS
    (strictTransformPullback B S hS f b).1 (strictTransformPullback B S hS f b).2
    (exceptionalPreimageSet B S hS f b E.1)
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj C.X₃) W s.1).mp s.2
  obtain ⟨n, hn⟩ := (sectionSupportedIn_iff_exists_pow_le_annihilator B S hS
    (strictTransformPullback B S hS f b).2
    ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj C.X₃) hq3
    (exceptionalPreimageSet B S hS f b E.1) W hWaff
    (Submodule.fg_span_singleton _) hzl s.1).mp hsupp
  have hkill := hn _ (pow_succ_mem_span_pow aW n)
  have hdvd : ∀ (x : ((modulePullback B S hS
        (strictTransformPullbackToSource B S hS f b)).obj C.X₁).val.obj (op W))
      (y : ((modulePullback B S hS
        (strictTransformPullbackToSource B S hS f b)).obj C.X₂).val.obj (op W)),
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map
          C.f).val.app (op W) x = (aW ^ (n + 1)) • y →
      ∃ z, x = (aW ^ (n + 1)) • z := by
    intro x y hxy
    obtain ⟨U, gm, hcomm, hUaff, hsurj, hker⟩ :=
      exists_affine_chartDiagram_of_closedSubspace B S hS
        (strictTransformPullback B S hS f b)
        (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b)
          (iterSumClosedSubspaces B S hS A' E n)) W hWaff
    exact exists_eq_smul_of_injective_of_ker_eq_span B S hS
      (exceptionalThickeningι B S hS f b (iterSumClosedSubspaces B S hS A' E n)) hq1 hq2
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.f)
      { U := U, V := W, g := gm, comm := hcomm } hUaff hWaff
      (injective_val_app_modulePullback_map_f B S hS f b C hC
        (iterSumClosedSubspaces B S hS A' E n) (op U))
      hsurj _ (hker.trans (hthick n)) x y hxy
  obtain ⟨y, hy0, hy1⟩ := Stacks.SupportedSectionsLift.exists_smul_eq_zero_of_divisibility
    (((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map
      C.f).val.app (op W)).hom
    (((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map
      C.g).val.app (op W)).hom
    (SheafOfModules.exact_val_app_of_shortExact hD (op W))
    (surjective_val_app_of_epi_of_isQuasicoherentOnSite _ hD.epi_g hq2 hq3 W hWaff)
    (aW ^ (n + 1)) hdvd s.1 hkill
  have hysupp : SectionSupportedIn B S hS (strictTransformPullback B S hS f b).1
      (strictTransformPullback B S hS f b).2 (exceptionalPreimageSet B S hS f b E.1)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj C.X₂) W y :=
    (sectionSupportedIn_iff_exists_pow_le_annihilator B S hS
      (strictTransformPullback B S hS f b).2
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj C.X₂) hq2
      (exceptionalPreimageSet B S hS f b E.1) W hWaff
      (Submodule.fg_span_singleton _) hzl y).mpr
      ⟨n + 1, fun c hc => smul_eq_zero_of_mem_span_pow aW n y hy0 c hc⟩
  refine ⟨⟨y, (mem_supportedSectionsSubmodule_iff B S hS _ _ _ _ W y).mpr hysupp⟩, ?_⟩
  refine Subtype.ext ?_
  have hcomp := congrArg (fun m : (supportedSectionsSubmodule B S hS
      (strictTransformPullback B S hS f b).1 (strictTransformPullback B S hS f b).2
      (exceptionalPreimageSet B S hS f b E.1)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
        C.X₂)).toSheafOfModules ⟶ _ => m.val.app (op W)
      ⟨y, (mem_supportedSectionsSubmodule_iff B S hS _ _ _ _ W y).mpr hysupp⟩)
    (supportedSectionsMap_comp_ι (exceptionalPreimageSet B S hS f b E.1)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g))
  exact hcomp.trans hy1

/-- **A section supported on the exceptional preimage lifts over a principal chart.**  The local
equation of the exceptional preimage and of each of its thickenings is read off the principal
chart diagram by `AlgebraicGeometry.Space.definingIdealAt_preimage_eq_span` and
`AlgebraicGeometry.Space.definingIdealAt_preimage_iterSum_eq_span`. -/
theorem surjective_supportedSectionsMap_val_app (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1)
    (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact)
    (hq1 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₁).IsQuasicoherentOnSite)
    (hq2 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₂).IsQuasicoherentOnSite)
    (hq3 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₃).IsQuasicoherentOnSite)
    (W : SmallEtale B S hS (strictTransformPullback B S hS f b).1)
    (hW : HasPrincipalChartDiagram B S hS (strictTransformPullbackToBlowUp B S hS f b) E W) :
    Function.Surjective ((supportedSectionsMap (exceptionalPreimageSet B S hS f b E.1)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g)).val.app
      (op W)) := by
  obtain ⟨hWaff, V, q, hq, hVaff, ⟨matlas⟩, a, ha⟩ := hW
  exact surjective_supportedSectionsMap_val_app_of_span B S hS f b E C hC hq1 hq2 hq3 W hWaff
    (((BigFppfOver.toScheme B S hS).map q).appTop.hom a)
    (preimage_chartPointsMap_range_ι_eq_zeroLocus B S hS
      (strictTransformPullback B S hS f b)
      (preimageClosedSubspace (strictTransformPullbackToBlowUp B S hS f b) E) W hWaff _
      (definingIdealAt_preimage_eq_span B S hS f b E W hWaff V hVaff q hq a ha))
    (fun n => definingIdealAt_preimage_iterSum_eq_span B S hS f b E n W hWaff V hVaff q hq
      matlas a ha)


end ChartSurjectivity

/-! ### Epimorphy of the induced map on the supported sections -/

section Epi

variable {A X A' : AlgebraicSpaces B S hS}

/-- **The morphism induced on the subsheaves of sections supported on the exceptional preimage is
locally surjective.**  The principal chart diagrams over the projection to `A'` generate covering
sieves, and over such a chart the induced morphism is surjective on sections. -/
theorem isLocallySurjective_supportedSectionsMap (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1)
    (hE : HasEffectiveCartierEtalePullbacks B S hS A' E)
    (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact)
    (hq1 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₁).IsQuasicoherentOnSite)
    (hq2 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₂).IsQuasicoherentOnSite)
    (hq3 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₃).IsQuasicoherentOnSite) :
    Presheaf.IsLocallySurjective
      (SmallEtale.topology B S hS (strictTransformPullback B S hS f b).1)
      ((PresheafOfModules.toPresheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
            (strictTransformPullback B S hS f b).1
            (strictTransformPullback B S hS f b).2).O).obj).map
        (supportedSectionsMap (exceptionalPreimageSet B S hS f b E.1)
          ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map
            C.g)).val) :=
  ⟨fun {U} _ => mem_topology_of_hasPrincipalChartDiagram B S hS
    (strictTransformPullbackToBlowUp B S hS f b) E hE U _ fun W _ hW =>
      surjective_supportedSectionsMap_val_app B S hS f b E C hC hq1 hq2 hq3 W hW _⟩

/-- **The morphism induced on the subsheaves of sections supported on the exceptional preimage is
an epimorphism.**  Local surjectivity on the small étale site is epimorphy for sheaves of
modules. -/
theorem epi_supportedSectionsMap (f : X ⟶ A) (b : A' ⟶ A)
    (E : ClosedSubspaces B S hS A'.1)
    (hE : HasEffectiveCartierEtalePullbacks B S hS A' E)
    (C : ShortComplex (Modules.{u, u} B S hS X.1 X.2))
    (hC : ∀ (Y P : AlgebraicSpaces B S hS) (t : Y ⟶ A) (pX : P ⟶ X) (pY : P ⟶ Y),
      IsPullback pX pY f t → (C.map (modulePullback B S hS pX)).ShortExact)
    (hq1 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₁).IsQuasicoherentOnSite)
    (hq2 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₂).IsQuasicoherentOnSite)
    (hq3 : ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).obj
      C.X₃).IsQuasicoherentOnSite) :
    Epi (supportedSectionsMap (exceptionalPreimageSet B S hS f b E.1)
      ((modulePullback B S hS (strictTransformPullbackToSource B S hS f b)).map C.g)) :=
  Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (isLocallySurjective_supportedSectionsMap B S hS f b E hE C hC hq1 hq2 hq3)

end Epi

end AlgebraicGeometry.Space

end

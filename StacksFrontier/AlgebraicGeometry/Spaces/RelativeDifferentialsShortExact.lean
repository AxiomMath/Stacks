module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallySmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Short exactness of the relative differentials sequence

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces over a scheme `S` with `f`
formally smooth, the three-term sequence of relative differentials of
`AlgebraicGeometry.Space.pullbackDifferentialsMap` and
`AlgebraicGeometry.Space.toRelativeDifferentials` is short exact.

Exactness at the middle term and surjectivity at the right are already available; the content
here is injectivity at the left, which is reduced along a surjective étale chart to the
corresponding statement for a morphism of schemes.

## The one hypothesis, and what it is not

`AlgebraicGeometry.Space.PullbackDifferentialsMapChartComparison` carries the chart step of that
reduction, and it is a shadow of Stacks 04CS, which this tree carries in one canonical statement
as `AlgebraicGeometry.Space.SchemeDifferentialsComparison`
(`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsSchemeComparison.lean`).  It is
**not** a restatement of that statement and does not follow from it.  The canonical statement is
a family of isomorphisms of *objects* — the spaces-level `Ω` of a morphism of schemes of the site
and the small-étale module associated to its Zariski `Ω` — and it asserts no compatibility with
`AlgebraicGeometry.Space.pullbackDifferentialsMap`, nor indeed with any morphism; the hypothesis
here is the monomorphy of a *map*, the comparison map `f^*Ω_{Y/Z} ⟶ Ω_{X/Z}` of Stacks 05Z8
restricted to a chart, over a diagram of *three* charts rather than a square of two.  Isomorphic
objects do not transport a property of maps between them, so the two statements are kept apart.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

section AffineLocal

open CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.RelativeDifferentialStalk Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

variable {X' Y' Z' : Scheme.{u}}

/-- **The stalk maps of an affine-locally formally smooth morphism of schemes are formally
smooth ring maps.**  A point of the source lies in an affine open `V` inside the preimage of an
affine open `U` of the target; the ring map on those sections is formally smooth by hypothesis,
and formal smoothness of such a ring map at the prime of the point is formal smoothness of the
induced map of local rings. -/
theorem formallySmooth_stalkMap_of_formallySmoothAffineLocally {k : X' ⟶ Y'}
    (hk : Stacks.Smooth.FormallySmoothAffineLocally k) (x : X') :
    (k.stalkMap x).hom.FormallySmooth := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (k.base x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X'.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage k.base.hom.continuous)
  have hVU' : V ≤ k ⁻¹ᵁ U := hVU
  have happ : (k.appLE U V hVU').hom.FormallySmooth :=
    (Stacks.Smooth.formallySmoothAffineLocally_iff_appLE k).mp hk ⟨U, hU⟩ ⟨V, hV⟩ hVU'
  let : IsAffine (V : Scheme.{u}) := hV
  let : IsAffine (U : Scheme.{u}) := hU
  let : Algebra Γ(Y', U) Γ(X', V) := (k.appLE U V hVU').hom.toAlgebra
  let : Algebra.FormallySmooth Γ(Y', U) Γ(X', V) := happ
  exact (formallySmooth_stalkMap_iff U hU V hV hVU' hxV).mpr
    (inferInstance : Algebra.FormallySmooth Γ(Y', U)
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal))

/-- A morphism of sheaves of modules on a scheme which is a monomorphism on every stalk is a
monomorphism. -/
private theorem mono_of_mono_stalkFunctor_map {M N : X'.Modules} (φ : M ⟶ N)
    (h : ∀ x : X', Mono ((TopCat.Presheaf.stalkFunctor (C := AddCommGrpCat.{u}) x).map
      ((SheafOfModules.toSheaf X'.ringCatSheaf).map φ).hom)) : Mono φ :=
  (SheafOfModules.toSheaf X'.ringCatSheaf).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 h)

/-- **The canonical map `k^*Ω_{Y'/Z'} ⟶ Ω_{X'/Z'}` is a monomorphism as soon as the ring maps
that `k` induces on affine opens are formally smooth.**

This is `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmooth` with the
infinitesimal lifting property of Stacks 02H0 replaced by condition (3) of Stacks 0D0F, which
is all its proof consumes: monomorphy is checked on stalks, where the map is the base-change
map `KaehlerDifferential.mapBaseChange` of the tower of local rings by
`AlgebraicGeometry.Scheme.Hom.exists_relativeDifferentialsPullbackStalkEquiv`, and that map is
injective once the stalk map of `k` is a formally smooth ring map. -/
@[ega "0 20.6.18" "(ii), case C = B",
  ega "0 20.6.2" "partial",
  ega "IV 16.4.24" "(i)",
  ega "IV 17.2.3" "(ii)",
  sga "1 II 4.2" "partial",
  sga "1 II 4.3" "(i)",
  sga "1 II 4.4" "Injectivity clause only",
  sga "6 VIII 2.2" "partial",
  sga "6 VIII 2.6" "partial"]
theorem relativeDifferentialsMap_mono_of_formallySmoothAffineLocally (k : X' ⟶ Y') (l : Y' ⟶ Z')
    (hk : Stacks.Smooth.FormallySmoothAffineLocally k) :
    Mono (relativeDifferentialsMap k l (k ≫ l) (𝟙 Z') (Category.comp_id (k ≫ l)).symm) := by
  classical
  refine mono_of_mono_stalkFunctor_map _ fun x ↦ ?_
  let R : Type u := ToType (Z'.presheaf.stalk (l.base (k.base x)))
  let A : Type u := ToType (Y'.sheaf.presheaf.stalk (k.base x))
  let Bb : Type u := ToType (X'.sheaf.presheaf.stalk x)
  let : Algebra R A := algebraStalkMap l (k.base x)
  let : Algebra A Bb := (k.stalkMap x).hom.toAlgebra
  let : Algebra R Bb := algebraStalkMap (k ≫ l) x
  let : IsScalarTower R A Bb := isScalarTower_stalkMap k l x
  let : Algebra.FormallySmooth A Bb :=
    formallySmooth_stalkMap_of_formallySmoothAffineLocally hk x
  obtain ⟨e, -, hbridge⟩ := exists_relativeDifferentialsPullbackStalkEquiv k l x
  rw [AddCommGrpCat.mono_iff_injective]
  show Function.Injective (Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom
    X'.sheaf.presheaf x
    (relativeDifferentialsMap k l (k ≫ l) (𝟙 Z') (Category.comp_id (k ≫ l)).symm).val)
  intro z₁ z₂ hz
  refine e.injective (KaehlerDifferential.mapBaseChange_injective R A Bb ?_)
  rw [hbridge, hbridge, hz]

end AffineLocal

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Space

section ShortExact

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z : AlgebraicSpaces B S hS}

/-- **The étale-chart comparison of Stacks 04CU and 04CS for the first map of the transitivity
sequence.**  In every commuting diagram of étale scheme charts `a : U ⟶ X`, `b : V ⟶ Y`,
`c : W ⟶ B` over scheme morphisms `ψ : U ⟶ V` and `χ : V ⟶ W` whose chart of the source is
surjective, the restriction along `a` of the comparison map `c_f : f^*Ω_{Y/B} ⟶ Ω_{X/B}` is a
monomorphism as soon as the corresponding map `ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of the chart schemes is.

This is the identification `Ω_{X/B}|_{U_étale} = Ω_{U/W}` of Stacks 04CU, read through the
comparison of Stacks 04CS between the small Zariski and the small étale differentials of a
morphism of schemes, in the single form in which the proof of Stacks 06BI consumes it.

It is a statement about a *map* and not about objects, so it is not a restatement of
`AlgebraicGeometry.Space.SchemeDifferentialsComparison`, the canonical form of Stacks 04CS in
this tree, and does not follow from it; the module docstring says why. -/
abbrev PullbackDifferentialsMapChartComparison (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  ∀ (U V W : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1)
      (c : yoneda.obj W ⟶ Z.1) (ψ : U ⟶ V) (χ : V ⟶ W),
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b →
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c →
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a →
    yoneda.map ψ ≫ b = a ≫ f.hom → yoneda.map χ ≫ c = b ≫ g.hom →
    Mono (Scheme.Hom.relativeDifferentialsMap ((BigFppfOver.toScheme B S hS).map ψ)
      ((BigFppfOver.toScheme B S hS).map χ)
      ((BigFppfOver.toScheme B S hS).map ψ ≫ (BigFppfOver.toScheme B S hS).map χ)
      (𝟙 ((BigFppfOver.toScheme B S hS).obj W)) (Category.comp_id _).symm) →
    Mono ((modulePullback B S hS (ObjectProperty.homMk a : schemeSpace U ⟶ X)).map
      (pullbackDifferentialsMap B S hS f g))

/-- **A composable pair of morphisms of algebraic spaces has a commuting diagram of étale
scheme charts whose chart of the first source is surjective.**  An atlas of `B` is lifted along
`g` and the resulting chart of `Y` is lifted along `f`, both by Stacks 02X1. -/
theorem exists_etale_chart_diagram (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ (U V W : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) (b : yoneda.obj V ⟶ Y.1)
      (c : yoneda.obj W ⟶ Z.1) (ψ : U ⟶ V) (χ : V ⟶ W),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage
            (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf b ∧
        (MorphismProperty.inverseImage
            (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf c ∧
        (MorphismProperty.inverseImage
            (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf a ∧
        yoneda.map ψ ≫ b = a ≫ f.hom ∧ yoneda.map χ ≫ c = b ≫ g.hom := by
  obtain ⟨W, c, hcSurj, hcEtale⟩ := Z.2.exists_atlas
  obtain ⟨V, b, χ, hsqχ, hbSurj, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS Y.2 Z.2 g.hom W c hcSurj hcEtale
  obtain ⟨U, a, ψ, hsqψ, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS X.2 Y.2 f.hom V b hbSurj hbEtale
  exact ⟨U, V, W, a, b, c, ψ, χ, haEtale, hbEtale, hcEtale, haSurj, hsqψ.symm, hsqχ.symm⟩

/-- **Monomorphy of the first map of the transitivity sequence is étale local on `X`.**  The
pullback of sheaves of modules along a surjective étale scheme chart is faithful by
`AlgebraicGeometry.Space.faithful_modulePullback`, and a faithful functor reflects
monomorphisms. -/
theorem mono_of_mono_modulePullback_chart (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
    (haEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (haSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (h : Mono ((modulePullback B S hS
      (ObjectProperty.homMk a : schemeSpace U ⟶ X)).map
        (pullbackDifferentialsMap B S hS f g))) :
    Mono (pullbackDifferentialsMap B S hS f g) := by
  have hfaithful := faithful_modulePullback B S hS U
    (ObjectProperty.homMk a : schemeSpace U ⟶ X)
    (isEtale_of_presheaf_etale B S hS haEtale) haSurj
  exact (modulePullback B S hS
    (ObjectProperty.homMk a : schemeSpace U ⟶ X)).mono_of_mono_map h

/-- **The first map `f^*Ω_{Y/B} ⟶ Ω_{X/B}` of the transitivity sequence of a formally smooth
`f : X ⟶ Y` is a monomorphism**, granted the chart comparison
`AlgebraicGeometry.Space.PullbackDifferentialsMapChartComparison`.

An atlas of `B` and two applications of Stacks 02X1 produce a commuting diagram of étale scheme
charts of `X`, `Y` and `B` whose chart `a` of `X` is surjective.  Stacks 061K, in the form
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_formallySmoothAffineLocally`, makes the chart
morphism `ψ` affine-locally formally smooth, and the case of schemes then makes the map of the
chart schemes a monomorphism; the hypothesis carries that to the restriction of `c_f` along
`a`.  Finally the pullback along `a` is faithful,
`AlgebraicGeometry.Space.faithful_modulePullback`, and a faithful functor reflects
monomorphisms. -/
theorem pullbackDifferentialsMap_mono_of_formallySmooth (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : FormallySmooth f.hom)
    (hchart : PullbackDifferentialsMapChartComparison B S hS f g) :
    Mono (pullbackDifferentialsMap B S hS f g) := by
  obtain ⟨U, V, W, a, b, c, ψ, χ, haEtale, hbEtale, hcEtale, haSurj, hsqψ, hsqχ⟩ :=
    exists_etale_chart_diagram B S hS f g
  have hψ : Stacks.Smooth.FormallySmoothAffineLocally
      ((BigFppfOver.toScheme B S hS).map ψ) :=
    holdsOnEveryEtaleChart_formallySmoothAffineLocally hf U V a b ψ haEtale hbEtale hsqψ
  have hscheme := Scheme.Hom.relativeDifferentialsMap_mono_of_formallySmoothAffineLocally
    ((BigFppfOver.toScheme B S hS).map ψ) ((BigFppfOver.toScheme B S hS).map χ) hψ
  exact mono_of_mono_modulePullback_chart B S hS f g U a haEtale haSurj
    (hchart U V W a b c ψ χ haEtale hbEtale hcEtale haSurj hsqψ hsqχ hscheme)

/-- The transitivity sequence `0 ⟶ f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0` is short exact as soon
as its first map is a monomorphism: the composite of the two maps is zero and the sequence is
exact at `Ω_{X/B}` by `AlgebraicGeometry.Space.triangleDifferentials_exact`, and it is exact at
`Ω_{X/Y}` by `AlgebraicGeometry.Space.triangleDifferentials_epi`, both of Stacks 05Z8. -/
theorem triangleDifferentials_shortExact_of_mono (f : X ⟶ Y) (g : Y ⟶ Z)
    (hmono : Mono (pullbackDifferentialsMap B S hS f g)) :
    ∃ h : pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  obtain ⟨h, hexact⟩ := triangleDifferentials_exact B S hS f g
  exact ⟨h, ShortComplex.ShortExact.mk' hexact hmono (triangleDifferentials_epi B S hS f g)⟩

/-- **Stacks 06BI.** For morphisms `f : X ⟶ Y` and `g : Y ⟶ B` of algebraic spaces over `S`
with `f` formally smooth, the transitivity sequence
`0 ⟶ f^*Ω_{Y/B} ⟶ Ω_{X/B} ⟶ Ω_{X/Y} ⟶ 0` of Stacks 05Z8 is short exact.

Short exactness adds monomorphy of the first map to the three clauses of Stacks 05Z8, and
`AlgebraicGeometry.Space.pullbackDifferentialsMap_mono_of_formallySmooth` supplies it from the
case of schemes by étale localization, granted the chart comparison. -/
@[stacks 06BI "granted as `hchart` the étale localization of 04CU and 04CS identifying the
  restriction of the comparison map of Ω to a surjective étale chart with the chart morphisms'
  own comparison map of Ω"]
theorem triangleDifferentials_shortExact (f : X ⟶ Y) (g : Y ⟶ Z) (hf : FormallySmooth f.hom)
    (hchart : PullbackDifferentialsMapChartComparison B S hS f g) :
    ∃ h : pullbackDifferentialsMap B S hS f g ≫ toRelativeDifferentials B S hS f g = 0,
      (ShortComplex.mk _ _ h).ShortExact :=
  triangleDifferentials_shortExact_of_mono B S hS f g
    (pullbackDifferentialsMap_mono_of_formallySmooth B S hS f g hf hchart)

end ShortExact
end AlgebraicGeometry.Space

end

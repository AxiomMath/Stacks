module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRestrictedData
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder

/-!
# Injectivity of the first arrow of Stacks 05ZA from local retractions

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, with inclusion
`i : Z ⟶ X`, and let `p : X ⟶ Y` be a morphism.  This file proves that the first arrow
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Y}
```
of the sequence of [Stacks Project, Tag 05ZA] is a **monomorphism** as soon as, on every affine
étale chart `V ⟶ X`, the restricted thickening `Z ×_X V ⊂ V` admits a retraction `V ⟶ Z ×_X V`
over `Y`.  This is the injectivity the proof of [Stacks Project, Tag 06BJ] obtains from the
étale-local splitting: there the retractions are produced by formal smoothness of `Z` over `Y`.

## The argument

The first arrow is the transpose of `D : 𝓘 ⟶ i_*i^*Ω_{X/Y}`, `a ↦ 1 ⊗ d a`, and since the unit
`𝓘 ⟶ i_*i^*𝓘` is invertible for a first order thickening and the direct image along a closed
immersion is faithful, it is enough that `D` is injective on sections.  Being a sheaf, `𝓘` is
separated, so it is enough to test on affine étale charts `A` of `X`, where a retraction
`r : V ⟶ Z_V` is available (`V` the scheme of `A`, `φ : V ⟶ X` the chart).

The two morphisms `φ` and `φ' = r ≫ Z_V ⟶ V ⟶ X` agree on `Z_V` and over `Y`.  By
[Stacks Project, Tag 0618] they differ by an `𝒪_{Z_V}`-linear map
`θ : κ^*Ω_{X/Y} ⟶ 𝒞_{Z_V/V}`, `κ = Z_V ⟶ X`, whose transpose carries `d a` to the difference
`φ^♯(a) - φ'^♯(a)` read in `κ_*(i_V^{-1}𝒪_V)`.  Here this map is built **on the small étale site
of the common target `X`**, for the identity of `𝒪_X` in the role of the quotient map
(`AlgebraicGeometry.Space.thickeningLiftDifferenceDataAt`), and not on a closed subspace of it as
`AlgebraicGeometry.Space.restrictedLiftDifferenceData` does; nothing about the target being
undeformed has to be transported.  For `a ∈ 𝓘(A)` with `D(a) = 0`:

* `1 ⊗ d a` vanishes in `κ_*κ^*Ω_{X/Y}`, the unit along `κ = (Z_V ⟶ Z) ≫ i` factoring through
  the unit along `i` (`AlgebraicGeometry.Space.exists_modulePullbackAdjunction_comp_unit_app`), so
  the two comorphisms agree at `a`;
* `φ'` factors through `i`, whose comorphism kills `a`;
* so the comorphism of `φ` read through `Z_V` kills `a`, hence so does the comorphism of `φ`
  itself, the unit `𝒪_V ⟶ i_{V*}i_V^{-1}𝒪_V` being invertible for a thickening;
* and the comorphism of a chart is injective on the sections over that chart, its projection to
  the identity chart being the identity
  (`AlgebraicGeometry.Space.eq_zero_of_structureSharp_chartHom_app_eq_zero`).

No comparison of the sequence of Stacks 05ZA with its restriction along an étale chart is used:
the chart enters only through the comorphism of `φ`, and the étale localization of the sheaf of
differentials (Stacks 04CU) is not needed.

## Main results

* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_app_eq_of_unit_eq_zero`: two
  morphisms over a base agreeing on a first order thickening have the same comorphism read
  through the thickening at every function whose differential is killed by the unit.
* `AlgebraicGeometry.Space.eq_zero_of_unit_differential_eq_zero_of_retraction`: the chart-level
  vanishing.
* `AlgebraicGeometry.Space.mono_conormalSequenceIdealPullbackMap_of_retractions`: **the first arrow
  of Stacks 05ZA is a monomorphism given retractions over the base on affine étale charts.**

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA), the sequence.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  morphisms agreeing on a first order thickening.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), its reading as a map on
  differentials.
* [Stacks Project, Tag 06BJ](https://stacks.math.columbia.edu/tag/06BJ), which this serves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-- Evaluating a composite of morphisms of sheaves of modules on a section, in the form in which
it is cheap to apply to morphisms whose types are large. -/
private theorem comp_val_app_apply_of_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P)
    (h : M ⟶ P) (hfg : f ≫ g = h) (V : Cᵒᵖ) (x : M.val.obj V) :
    (g.val.app V).hom ((f.val.app V).hom x) = (h.val.app V).hom x := by
  subst hfg
  rfl

/-- A composite of morphisms of sheaves of modules kills what its first factor kills. -/
private theorem comp_val_app_apply_eq_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} R} (f : M ⟶ N) (g : N ⟶ P) (V : Cᵒᵖ)
    (x : M.val.obj V) (hx : (f.val.app V).hom x = 0) : ((f ≫ g).val.app V).hom x = 0 :=
  (comp_val_app_apply_of_eq f g _ rfl V x).symm.trans (by rw [hx, map_zero])

/-- A composite of three morphisms of sheaves of rings kills what its first factor kills. -/
private theorem comp_comp_app_eq_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A₁ A₂ A₃ A₄ : Sheaf J RingCat.{u}} (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) (k : A₃ ⟶ A₄) {V : Cᵒᵖ}
    (a : A₁.obj.obj V) (ha : f.hom.app V a = 0) : ((f ≫ g) ≫ k).hom.app V a = 0 := by
  show k.hom.app V (g.hom.app V (f.hom.app V a)) = 0
  rw [ha, map_zero, map_zero]

/-- A morphism of sheaves of rings equal to a composite of three kills what the first factor
kills. -/
private theorem app_eq_zero_of_comp_comp_eq {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A₁ A₂ A₃ A₄ : Sheaf J RingCat.{u}} (f : A₁ ⟶ A₂)
    (g : A₂ ⟶ A₃) (k : A₃ ⟶ A₄) (t : A₁ ⟶ A₄) (hk : (f ≫ g) ≫ k = t) {V : Cᵒᵖ}
    (a : A₁.obj.obj V) (ha : f.hom.app V a = 0) : t.hom.app V a = 0 := by
  subst hk
  exact comp_comp_app_eq_zero f g k a ha

variable (hZ : IsFirstOrderThickening B S hS X Z.1)

variable {W : AlgebraicSpaces B S hS}
  (κ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)

/-- **The difference of two morphisms agreeing on a first order thickening, on the site of their
common target**, as the datum the descent consumes, for the identity of `𝒪_W`: the ideal of
values is `AlgebraicGeometry.Space.squareZeroValuesAt` at `T = W`. -/
def thickeningLiftDifferenceDataAt (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) (h' : subspaceInclusion B S hS X Z ≫ c' = κ) :
    Stacks.Sites.LiftDifferenceData (𝟙 (structureRingSheaf B S hS W))
      (squareZeroValuesAt B S hS Z W κ hZ) where
  f := structureSharpThroughThickeningAt B S hS Z c κ h
  g := structureSharpThroughThickeningAt B S hS Z c' κ h'
  ι_smul {V} x m := squareZeroValuesAt_ι_smul B S hS Z W κ hZ (𝟙 _) _
    ((structureSharpThroughThickeningAt_comp_reduction B S hS Z c κ h).trans
      (Category.id_comp _).symm) x m
  diff {V} x := sharpDiffAt B S hS Z W κ hZ _ _
    (structureSharpThroughThickeningAt_comp_reduction_eq B S hS Z c c' κ h h') x
  ι_diff {V} x := squareZeroValuesAt_ι_sharpDiffAt B S hS Z W κ hZ _ _
    (structureSharpThroughThickeningAt_comp_reduction_eq B S hS Z c c' κ h h') x
  app_eq_of_app_eq_zero {V} x hx := by
    have hx0 : x = 0 := hx
    rw [hx0, map_zero, map_zero]

variable {Bas : AlgebraicSpaces B S hS} (qb : W ⟶ Bas)

/-- **The difference of two morphisms over `qb` kills the functions read from `Bas`.** -/
theorem descend_thickeningLiftDifferenceDataAt_eq_zero (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) (h' : subspaceInclusion B S hS X Z ≫ c' = κ)
    (hcc : c ≫ qb = c' ≫ qb) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS qb).obj.obj V) :
    (thickeningLiftDifferenceDataAt B S hS Z hZ κ c c' h h').toQuotientDerivation.descend
        ((structureSharpInverseImage B S hS qb).hom.app V s) = 0 := by
  have key := (thickeningLiftDifferenceDataAt B S hS Z hZ κ c c' h h').descend_eq_zero_of_comp_eq
    (structureSharpRingInverseImage B S hS qb) (structureSharpRingInverseImage B S hS qb)
    (Category.comp_id _)
    (structureSharpRingInverseImage_comp_structureSharpThroughThickeningAt_eq' B S hS Z c c' qb
      κ h h' hcc) (V := V) s
  rw [structureSharpRingInverseImage_eq_forget₂] at key
  exact key

/-- **The linear map `κ^*Ω_{W/Bas} ⟶ 𝒞_{Z/X}` by which two morphisms `c, c' : X ⟶ W` over `qb`,
agreeing on the first order thickening `Z ⊂ X`, differ**, built on the small étale site of the
common target `W` rather than on a closed subspace of it. -/
noncomputable def thickeningLiftDifferenceHomAt (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) (h' : subspaceInclusion B S hS X Z ≫ c' = κ)
    (hcc : c ≫ qb = c' ≫ qb) :
    (modulePullback B S hS κ).obj (sheafOfDifferentials B S hS qb) ⟶ conormalModule B S hS X Z :=
  liftDifferenceDifferentialsHom B S hS qb κ (conormalModule B S hS X Z)
    (thickeningLiftDifferenceDataAt B S hS Z hZ κ c c' h h')
    (descend_thickeningLiftDifferenceDataAt_eq_zero B S hS Z hZ κ qb c c' h h' hcc)

include hZ in
/-- **Two morphisms over `qb` agreeing on a first order thickening have the same comorphism at
every function whose differential is killed by the unit `Ω_{W/Bas} ⟶ κ_*κ^*Ω_{W/Bas}`.**

The transpose of the linear map by which they differ is the unit followed by the direct image of
that map, and it carries `d a` to the difference of the two comorphisms at `a`. -/
theorem structureSharpThroughThickeningAt_app_eq_of_unit_eq_zero (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) (h' : subspaceInclusion B S hS X Z ≫ c' = κ)
    (hcc : c ≫ qb = c' ≫ qb) {V : (SmallEtale B S hS W.1)ᵒᵖ}
    (a : (structureRingSheaf B S hS W).obj.obj V)
    (ha : (((modulePullbackAdjunction B S hS κ).unit.app
      (sheafOfDifferentials B S hS qb)).val.app V).hom
        ((universalDerivation B S hS qb).d a) = 0) :
    (structureSharpThroughThickeningAt B S hS Z c κ h).hom.app V a =
      (structureSharpThroughThickeningAt B S hS Z c' κ h').hom.app V a := by
  have hspec := liftDifferenceDifferentialsHom_spec B S hS qb κ (conormalModule B S hS X Z)
    (thickeningLiftDifferenceDataAt B S hS Z hZ κ c c' h h')
    (descend_thickeningLiftDifferenceDataAt_eq_zero B S hS Z hZ κ qb c c' h h' hcc) (V := V) a
  rw [Adjunction.homEquiv_unit] at hspec
  have hzero : (thickeningLiftDifferenceDataAt B S hS Z hZ κ c c' h h').diff a = 0 := by
    exact hspec.symm.trans (comp_val_app_apply_eq_zero _ _ V _ ha)
  have hι := (thickeningLiftDifferenceDataAt B S hS Z hZ κ c c' h h').ι_diff a
  rw [hzero, map_zero] at hι
  exact sub_eq_zero.1 hι.symm

/-- The comorphism read through the thickening at an equal composite vanishes where the plain
one does: the two differ by an `eqToHom`. -/
theorem structureSharpThroughThickeningAt_app_eq_zero_iff (c : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) {V : (SmallEtale B S hS W.1)ᵒᵖ}
    (a : (structureRingSheaf B S hS W).obj.obj V) :
    (structureSharpThroughThickeningAt B S hS Z c κ h).hom.app V a = 0 ↔
      (structureSharpThroughThickening B S hS Z c).hom.app V a = 0 := by
  subst h
  rfl

/-- Two comorphisms read through the thickening which agree at `a` after the `eqToHom`s vanish at
`a` together. -/
theorem structureSharpThroughThickening_app_eq_zero_of_eq (c c' : X ⟶ W)
    (h : subspaceInclusion B S hS X Z ≫ c = κ) (h' : subspaceInclusion B S hS X Z ≫ c' = κ)
    {V : (SmallEtale B S hS W.1)ᵒᵖ} (a : (structureRingSheaf B S hS W).obj.obj V)
    (heq : (structureSharpThroughThickeningAt B S hS Z c κ h).hom.app V a =
      (structureSharpThroughThickeningAt B S hS Z c' κ h').hom.app V a)
    (h0 : (structureSharpThroughThickening B S hS Z c').hom.app V a = 0) :
    (structureSharpThroughThickening B S hS Z c).hom.app V a = 0 :=
  (structureSharpThroughThickeningAt_app_eq_zero_iff B S hS Z κ c h a).1
    (heq.trans ((structureSharpThroughThickeningAt_app_eq_zero_iff B S hS Z κ c' h' a).2 h0))

/-- **The comorphism of a morphism factoring through `p : W₀ ⟶ W`, read through the thickening,
kills what the comorphism of `p` kills.** -/
theorem structureSharpThroughThickeningAt_comp_app_eq_zero {W₀ : AlgebraicSpaces B S hS}
    (c₀ : X ⟶ W₀) (e : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W₀)
    (h₀ : subspaceInclusion B S hS X Z ≫ c₀ = e) (p : W₀ ⟶ W) {V : (SmallEtale B S hS W.1)ᵒᵖ}
    (a : (structureRingSheaf B S hS W).obj.obj V)
    (ha : (structureSharp B S hS p).hom.app V a = 0) :
    (structureSharpThroughThickeningAt B S hS Z (c₀ ≫ p) (e ≫ p)
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ p) h₀))).hom.app V a = 0 :=
  app_eq_zero_of_comp_comp_eq _ _ _ _
    (structureSharp_comp_map_structureSharpThroughThickeningAt' B S hS Z c₀ p e h₀) a ha

/-- The comparison of iterated direct images of a sheaf of rings is invertible. -/
instance isIso_pushforwardRingSheafCompHom {V₁ V₂ V₃ : AlgebraicSpaces B S hS} (f : V₁ ⟶ V₂)
    (g : V₂ ⟶ V₃) (O : Sheaf (SmallEtale.topology B S hS V₁.1) RingCat.{u}) :
    IsIso (pushforwardRingSheafCompHom B S hS f g O) :=
  ⟨⟨pushforwardRingSheafCompInv B S hS f g O, pushforwardRingSheafCompHom_comp_inv B S hS f g O,
    pushforwardRingSheafCompInv_comp_hom B S hS f g O⟩⟩

/-- A morphism of sheaves of rings followed by an isomorphism kills only what it kills. -/
private theorem app_eq_zero_of_comp_isIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A₁ A₂ A₃ : Sheaf J RingCat.{u}} (f : A₁ ⟶ A₂)
    (t : A₂ ⟶ A₃) [ht : IsIso t] {V : Cᵒᵖ} (a : A₁.obj.obj V) (ha : (f ≫ t).hom.app V a = 0) :
    f.hom.app V a = 0 := by
  have e : f = (f ≫ t) ≫ inv t := by simp
  rw [e]
  show (inv t).hom.app V ((f ≫ t).hom.app V a) = 0
  rw [ha, map_zero]

include hZ in
/-- **For a first order thickening, the comorphism read through the thickening kills only what
the comorphism itself kills.**  It is the comorphism followed by the direct image of the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X`, which is invertible for a thickening, and by the comparison of iterated
direct images. -/
theorem structureSharp_app_eq_zero_of_structureSharpThroughThickening (c : X ⟶ W)
    {V : (SmallEtale B S hS W.1)ᵒᵖ} (a : (structureRingSheaf B S hS W).obj.obj V)
    (ha : (structureSharpThroughThickening B S hS Z c).hom.app V a = 0) :
    (structureSharp B S hS c).hom.app V a = 0 := by
  have : IsIso (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
      (structureRingSheaf B S hS X)) := isIso_thickeningRingUnit B S hS Z hZ.1
  have h2 : IsIso ((pullbackRingSheafComp (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS W.1)
      (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z)).pushforward
      (smallToposMorphismTypeU B S hS c).pushforward
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))).hom ≫
    pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS W.1)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
      (smallToposMorphismTypeU_comp B S hS (subspaceInclusion B S hS X Z) c).hom) :=
    isIso_pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X Z) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z))
  have h1 : IsIso ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
      (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X Z))
        (structureRingSheaf B S hS X))) := Functor.map_isIso _ _
  rw [structureSharpThroughThickening_eq] at ha
  exact app_eq_zero_of_comp_isIso (structureSharp B S hS c) _ (ht := IsIso.comp_isIso' h1 h2) a ha

/-! ### The comorphism of an étale chart is injective on the sections over that chart -/

/-- An étale chart `A` of an algebraic space `W`, as a morphism of algebraic spaces out of the
representable algebraic space of its underlying object. -/
noncomputable abbrev etaleChartHom (A : SmallEtale B S hS W.1) : yonedaSpace B S hS A.1.left ⟶ W :=
  ObjectProperty.homMk A.1.hom

/-- The commutative diagram of étale scheme charts over `etaleChartHom A` whose upper chart is the
identity chart of `A` and whose lower chart is `A` itself. -/
noncomputable def chartHomDiagram (A : SmallEtale B S hS W.1) :
    ChartDiagram B S hS (yonedaSpace B S hS A.1.left).1 W.1 (etaleChartHom B S hS A).hom where
  U := ⟨CostructuredArrow.mk (𝟙 (yoneda.obj A.1.left)), presheaf_etale_id B S hS A.1.left⟩
  V := A
  g := 𝟙 _
  comm := by simp

/-- **The comorphism of an étale chart `A ⟶ W` is injective on the sections over `A`.**  Its
projection to the identity chart of `A` is the pullback of regular functions along the identity
of `A`. -/
theorem eq_zero_of_structureSharp_chartHom_app_eq_zero (A : SmallEtale B S hS W.1)
    (b : (structureRingSheaf B S hS W).obj.obj (op A))
    (hb : (structureSharp B S hS (etaleChartHom B S hS A)).hom.app (op A) b = 0) : b = 0 := by
  have h1 := directImageChartProjection_structureSharpSet_chartDiagram B S hS
    (etaleChartHom B S hS A) (chartHomDiagram B S hS A) b
  have h0 := directImageChartProjection_structureSharpSet_chartDiagram B S hS
    (etaleChartHom B S hS A) (chartHomDiagram B S hS A)
    (0 : (structureRingSheaf B S hS W).obj.obj (op A))
  have hsh : (structureSharpSet B S hS (etaleChartHom B S hS A)).hom.app (op A) b =
      (structureSharpSet B S hS (etaleChartHom B S hS A)).hom.app (op A)
        (0 : (structureRingSheaf B S hS W).obj.obj (op A)) := by
    show (structureSharp B S hS (etaleChartHom B S hS A)).hom.app (op A) b =
      (structureSharp B S hS (etaleChartHom B S hS A)).hom.app (op A) 0
    rw [hb, map_zero]
  have hpb : ∀ y, (chartDiagramPullback B S hS (etaleChartHom B S hS A)
      (chartHomDiagram B S hS A)).hom y = y := fun y => by
    simp only [chartDiagramPullback, chartHomDiagram, CategoryTheory.Functor.map_id, op_id]
    exact congrArg (fun φ => RingCat.Hom.hom φ y)
      (((forget₂ CommRingCat RingCat).congr_map (Scheme.Γ.map_id _)).trans
        ((forget₂ CommRingCat RingCat).map_id _))
  have := h1.symm.trans ((congrArg _ hsh).trans h0)
  exact (hpb b).symm.trans (this.trans (hpb 0))

/-! ### The unit of a composite factors through the unit of its last factor -/

/-- The unit of an adjunction whose right adjoint is replaced by an isomorphic one. -/
private theorem ofNatIsoRight_unit_app {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) (M : C) :
    (adj.ofNatIsoRight iso).unit.app M = adj.unit.app M ≫ iso.hom.app (F.obj M) := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

/-- **The unit of an adjunction with a composite right adjoint factors through the unit of the
first factor.** -/
private theorem exists_unit_app_eq_comp {C D E : Type*} [Category C] [Category D] [Category E]
    {F₁ : C ⥤ D} {G₁ : D ⥤ C} (adj₁ : F₁ ⊣ G₁) {F₂ : D ⥤ E} {G₂ : E ⥤ D} (adj₂ : F₂ ⊣ G₂)
    {F : C ⥤ E} {G : E ⥤ C} (adj : F ⊣ G) (e : G₂ ⋙ G₁ ≅ G) (M : C) :
    ∃ T, adj.unit.app M = adj₁.unit.app M ≫ T := by
  refine ⟨G₁.map (adj₂.unit.app (F₁.obj M)) ≫ e.hom.app _ ≫
    G.map ((((adj₁.comp adj₂).ofNatIsoRight e).leftAdjointUniq adj).hom.app M), ?_⟩
  rw [← Adjunction.unit_leftAdjointUniq_hom_app ((adj₁.comp adj₂).ofNatIsoRight e) adj M,
    ofNatIsoRight_unit_app, Adjunction.comp_unit_app]
  simp only [Category.assoc]
  rfl

/-- **The unit of `(f ≫ g)^* ⊣ (f ≫ g)_*` factors through the unit of `g^* ⊣ g_*`.** -/
theorem exists_modulePullbackAdjunction_comp_unit_app {X₁ X₂ X₃ : AlgebraicSpaces B S hS}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (M : Modules B S hS X₃.1 X₃.2) :
    ∃ T, (modulePullbackAdjunction B S hS (f ≫ g)).unit.app M =
      (modulePullbackAdjunction B S hS g).unit.app M ≫ T :=
  exists_unit_app_eq_comp (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS f)
    (modulePullbackAdjunction B S hS (f ≫ g)) (modulePushforwardCompIso B S hS f g) M

/-- **A section killed by the unit of `g` is killed by the unit of any `f ≫ g`.** -/
theorem modulePullbackAdjunction_comp_unit_app_eq_zero {X₁ X₂ X₃ : AlgebraicSpaces B S hS}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (M : Modules B S hS X₃.1 X₃.2)
    {V : (SmallEtale B S hS X₃.1)ᵒᵖ} (m : M.val.obj V)
    (hm : (((modulePullbackAdjunction B S hS g).unit.app M).val.app V).hom m = 0) :
    (((modulePullbackAdjunction B S hS (f ≫ g)).unit.app M).val.app V).hom m = 0 := by
  obtain ⟨T, hT⟩ := exists_modulePullbackAdjunction_comp_unit_app B S hS f g M
  rw [hT]
  exact comp_val_app_apply_eq_zero _ T V m hm

/-! ### A section of the ideal killed by the differential, on a chart carrying a retraction -/

section Chart

variable {Y : AlgebraicSpaces B S hS} (p : X ⟶ Y) (A : SmallEtale B S hS X.1)

variable (r : yonedaSpace B S hS A.1.left ⟶
      (⟨(preimageSubspace B S hS (etaleChartHom B S hS A) Z).1.toFunctor,
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z).2.1⟩ : AlgebraicSpaces B S hS))
    (hr : subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫ r = 𝟙 _)
    (hrp : r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
      etaleChartHom B S hS A ≫ p = etaleChartHom B S hS A ≫ p)

include hr in
/-- The retraction followed by the inclusion of the restricted thickening and the chart restricts
on the restricted thickening to its projection to `Z` followed by the inclusion of `Z`. -/
theorem chartRetraction_comp_eq :
    subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
      r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
          (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
        etaleChartHom B S hS A =
      preimageProjection B S hS (etaleChartHom B S hS A) Z ≫ subspaceInclusion B S hS X Z := by
  rw [← Category.assoc, hr, Category.id_comp]
  rfl

include hrp in
/-- The chart and the retraction followed by the inclusion and the chart agree over `Y`. -/
theorem chartRetraction_comp_comp_eq : etaleChartHom B S hS A ≫ p =
    (r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
      etaleChartHom B S hS A) ≫ p := by
  rw [Category.assoc, Category.assoc, hrp]

include hZ hr hrp in
/-- The chart and the retraction followed by the inclusion have the same comorphism through the
restricted thickening at every function whose differential the unit of `i^* ⊣ i_*` kills. -/
theorem structureSharpThroughThickeningAt_chartHom_app_eq
    (a : (structureRingSheaf B S hS X).obj.obj (op A))
    (hd : (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
      (sheafOfDifferentials B S hS p)).val.app (op A)).hom
        ((universalDerivation B S hS p).d a) = 0) :
    (structureSharpThroughThickeningAt B S hS (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
        (etaleChartHom B S hS A)
        (preimageProjection B S hS (etaleChartHom B S hS A) Z ≫ subspaceInclusion B S hS X Z)
        rfl).hom.app (op A) a =
      (structureSharpThroughThickeningAt B S hS (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
        (r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
            (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
          etaleChartHom B S hS A)
        (preimageProjection B S hS (etaleChartHom B S hS A) Z ≫ subspaceInclusion B S hS X Z)
        (chartRetraction_comp_eq B S hS Z A r hr)).hom.app (op A) a :=
  structureSharpThroughThickeningAt_app_eq_of_unit_eq_zero B S hS
    (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
    (isFirstOrderThickening_preimage B S hS Z.1 (etaleChartHom B S hS A) hZ)
    (preimageProjection B S hS (etaleChartHom B S hS A) Z ≫ subspaceInclusion B S hS X Z) p
    (etaleChartHom B S hS A)
    (r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
      etaleChartHom B S hS A) rfl (chartRetraction_comp_eq B S hS Z A r hr)
    (chartRetraction_comp_comp_eq B S hS Z p A r hrp) (V := op A) a
    (modulePullbackAdjunction_comp_unit_app_eq_zero B S hS _ _ _ _ hd)

include hZ hr hrp in
/-- The comorphism of the chart through the restricted thickening kills `a` as soon as the
comorphism of the retraction followed by the inclusion does. -/
theorem structureSharpThroughThickening_chartHom_app_eq_zero
    (a : (structureRingSheaf B S hS X).obj.obj (op A))
    (hd : (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
      (sheafOfDifferentials B S hS p)).val.app (op A)).hom
        ((universalDerivation B S hS p).d a) = 0)
    (h0 : (structureSharpThroughThickening B S hS
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
        (r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
            (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
          etaleChartHom B S hS A)).hom.app (op A) a = 0) :
    (structureSharpThroughThickening B S hS (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
        (etaleChartHom B S hS A)).hom.app (op A) a = 0 :=
  structureSharpThroughThickening_app_eq_zero_of_eq B S hS _ _ _ _ _ _ a
    (structureSharpThroughThickeningAt_chartHom_app_eq B S hS Z hZ p A r hr hrp a hd) h0

include hr in
/-- The comorphism of the retraction followed by the inclusion, read through the restricted
thickening, kills every section of the defining ideal of `Z`. -/
theorem structureSharpThroughThickening_retraction_app_eq_zero
    (a : (structureRingSheaf B S hS X).obj.obj (op A))
    (ha : (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app (op A) a = 0) :
    (structureSharpThroughThickening B S hS
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
        (r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
          (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
          etaleChartHom B S hS A)).hom.app (op A) a = 0 := by
  have h₀ : subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
        (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
      r ≫ preimageProjection B S hS (etaleChartHom B S hS A) Z =
      preimageProjection B S hS (etaleChartHom B S hS A) Z := by
    rw [← Category.assoc, hr, Category.id_comp]
  have hzero := (structureSharpThroughThickeningAt_app_eq_zero_iff B S hS _ _ _ _ a).1
    (structureSharpThroughThickeningAt_comp_app_eq_zero B S hS
      (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
      (r ≫ preimageProjection B S hS (etaleChartHom B S hS A) Z) _ h₀
      (subspaceInclusion B S hS X Z) a ha)
  have hc' : (r ≫ preimageProjection B S hS (etaleChartHom B S hS A) Z) ≫
      subspaceInclusion B S hS X Z =
      r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
          (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫ etaleChartHom B S hS A := by
    rw [Category.assoc]
    rfl
  rwa [hc'] at hzero

include hZ hr hrp in
/-- **On an étale chart of `X` over which the thickening `Z ⊂ X` has a retraction over `Y`, a
section of the defining ideal whose differential is killed by the unit of `i^* ⊣ i_*` vanishes.**

Write `φ : V ⟶ X` for the chart, `Z_V = φ⁻¹(Z) ⊂ V` for the restricted thickening and
`r : V ⟶ Z_V` for the retraction.  The comorphisms of `φ` and of `r ≫ Z_V ⟶ V ⟶ X`, read through
`Z_V`, agree at `a`; the second factors through `i : Z ⟶ X`, whose comorphism kills `a`; and the
first kills only what the comorphism of the chart kills, which over the chart itself is
nothing. -/
theorem eq_zero_of_unit_differential_eq_zero_of_retraction
    (a : (structureRingSheaf B S hS X).obj.obj (op A))
    (ha : (structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app (op A) a = 0)
    (hd : (((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
      (sheafOfDifferentials B S hS p)).val.app (op A)).hom
        ((universalDerivation B S hS p).d a) = 0) :
    a = 0 :=
  eq_zero_of_structureSharp_chartHom_app_eq_zero B S hS A a
    (structureSharp_app_eq_zero_of_structureSharpThroughThickening B S hS
      (preimageSubspace B S hS (etaleChartHom B S hS A) Z)
      (isFirstOrderThickening_preimage B S hS Z.1 (etaleChartHom B S hS A) hZ)
      (etaleChartHom B S hS A) a
      (structureSharpThroughThickening_chartHom_app_eq_zero B S hS Z hZ p A r hr hrp a hd
        (structureSharpThroughThickening_retraction_app_eq_zero B S hS Z A r hr a ha)))

end Chart

/-! ### Injectivity of the first arrow from retractions on affine charts -/

section Mono

variable {Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)

/-- A section of the structure sheaf vanishing on every affine étale chart over its chart is
zero: the affine charts cover, and the structure sheaf is separated. -/
theorem eq_zero_of_forall_affineChart_map_eq_zero (U : SmallEtale B S hS X.1)
    (s : (structureRingSheaf B S hS X).obj.obj (op U))
    (h : ∀ (K : SmallEtale B S hS X.1) (f : K ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj K.1.left) →
        (structureRingSheaf B S hS X).obj.map f.op s = 0) : s = 0 := by
  have hsep : Presheaf.IsSeparated (SmallEtale.topology B S hS X.1)
      ((structureRingSheaf B S hS X).obj ⋙ CategoryTheory.forget RingCat.{u}) :=
    ((sheafCompose (SmallEtale.topology B S hS X.1)
      (CategoryTheory.forget RingCat.{u})).obj (structureRingSheaf B S hS X)).cond.isSeparated
  obtain ⟨I, Yc, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 U
  refine hsep U (Sieve.ofArrows Yc a) hcov s 0 ?_
  rintro K f ⟨K', g, m, ⟨j⟩, rfl⟩
  show (structureRingSheaf B S hS X).obj.map (g ≫ a j).op s =
    (structureRingSheaf B S hS X).obj.map (g ≫ a j).op 0
  rw [op_comp, Functor.map_comp, map_zero, ConcreteCategory.comp_apply, h _ (a j) (haff j),
    map_zero]

include hZ in
/-- **The adjoint form of the first arrow of Stacks 05ZA is injective on sections** as soon as
the thickening has a retraction over `Y` on every affine étale chart of `X`. -/
theorem conormalSequenceIdealDifferential_injective
    (hloc : ∀ A : SmallEtale B S hS X.1, IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) →
      ∃ r : yonedaSpace B S hS A.1.left ⟶
          (⟨(preimageSubspace B S hS (etaleChartHom B S hS A) Z).1.toFunctor,
            (preimageSubspace B S hS (etaleChartHom B S hS A) Z).2.1⟩ : AlgebraicSpaces B S hS),
        subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
            (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫ r = 𝟙 _ ∧
          r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
              (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
            etaleChartHom B S hS A ≫ p = etaleChartHom B S hS A ≫ p)
    (U : SmallEtale B S hS X.1)
    (x : (definingIdealSheaf B S hS X Z).toSheafOfModules.val.obj (op U))
    (hx : ((conormalSequenceIdealDifferential B S hS Z p).val.app (op U)).hom x = 0) :
    x = 0 := by
  refine Subtype.ext (eq_zero_of_forall_affineChart_map_eq_zero B S hS U x.1 fun K f hK => ?_)
  obtain ⟨r, hr, hrp⟩ := hloc K hK
  set y := (definingIdealSheaf B S hS X Z).toSheafOfModules.val.map f.op x
  have hy : ((conormalSequenceIdealDifferential B S hS Z p).val.app (op K)).hom y = 0 :=
    (PresheafOfModules.naturality_apply (conormalSequenceIdealDifferential B S hS Z p).val
      f.op x).trans ((congrArg _ hx).trans (map_zero _))
  have hy' := ((conormalSequenceUnitDerivation_d B S hS Z p (op K) y.1).symm.trans
    (conormalSequenceIdealDifferential_val_app_apply B S hS Z p (op K) y).symm).trans hy
  exact eq_zero_of_unit_differential_eq_zero_of_retraction B S hS Z hZ p K r hr hrp y.1
    ((mem_definingIdealAt_iff B S hS X Z (op K) y.1).1 y.2) hy'

include hZ in
/-- **The first arrow of Stacks 05ZA for a first order thickening `Z ⊂ X` over `Y` is a
monomorphism as soon as the thickening has a retraction over `Y` on every affine étale chart of
`X`.**

Its transpose `𝓘 ⟶ i_*i^*Ω_{X/Y}` is injective on sections by
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential_injective`, hence a monomorphism; it is
the unit `𝓘 ⟶ i_*i^*𝓘`, an isomorphism for a first order thickening, followed by the direct image
of the first arrow; and the direct image along a closed immersion is faithful. -/
theorem mono_conormalSequenceIdealPullbackMap_of_retractions
    (hloc : ∀ A : SmallEtale B S hS X.1, IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) →
      ∃ r : yonedaSpace B S hS A.1.left ⟶
          (⟨(preimageSubspace B S hS (etaleChartHom B S hS A) Z).1.toFunctor,
            (preimageSubspace B S hS (etaleChartHom B S hS A) Z).2.1⟩ : AlgebraicSpaces B S hS),
        subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
            (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫ r = 𝟙 _ ∧
          r ≫ subspaceInclusion B S hS (yonedaSpace B S hS A.1.left)
              (preimageSubspace B S hS (etaleChartHom B S hS A) Z) ≫
            etaleChartHom B S hS A ≫ p = etaleChartHom B S hS A ≫ p) :
    @Mono (Modules.{u, u} B S hS Z.1.toFunctor Z.2.1) _ _ _
      (conormalSequenceIdealPullbackMap B S hS Z p) := by
  have hD : @Mono (Modules.{u, u} B S hS X.1 X.2) _ _ _
      (conormalSequenceIdealDifferential B S hS Z p) := by
    refine ⟨fun {P} g h hgh => ?_⟩
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun t => ?_))
    have e := (comp_val_app_apply_of_eq g _ _ rfl V t).trans
      ((congrArg (fun m => (m.val.app V).hom t) hgh).trans
        (comp_val_app_apply_of_eq h _ _ rfl V t).symm)
    rw [← sub_eq_zero]
    refine conormalSequenceIdealDifferential_injective B S hS Z hZ p hloc V.unop _ ?_
    show ((conormalSequenceIdealDifferential B S hS Z p).val.app V).hom
      ((g.val.app V).hom t - (h.val.app V).hom t) = 0
    rw [map_sub, sub_eq_zero]
    exact e
  have := isIso_unit_definingIdealSheaf_of_isFirstOrderThickening B S hS Z hZ
  have h1 : (modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≫
      (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        (conormalSequenceIdealPullbackMap B S hS Z p) =
      conormalSequenceIdealDifferential B S hS Z p := by
    refine ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).homEquiv_unit _ _
      (conormalSequenceIdealPullbackMap B S hS Z p)).symm.trans ?_
    rw [conormalSequenceIdealPullbackMap_eq_homEquiv_symm]
    exact Equiv.apply_symm_apply _ _
  have hff := fullyFaithfulModulePushforward B S hS (subspaceInclusion B S hS X Z) Z.2.2
  have := hff.faithful
  refine (modulePushforward B S hS (subspaceInclusion B S hS X Z)).mono_of_mono_map ?_
  have hm : (modulePushforward B S hS (subspaceInclusion B S hS X Z)).map
        (conormalSequenceIdealPullbackMap B S hS Z p) =
      inv ((modulePullbackAdjunction B S hS (subspaceInclusion B S hS X Z)).unit.app
        (definingIdealSheaf B S hS X Z).toSheafOfModules) ≫
        conormalSequenceIdealDifferential B S hS Z p := by
    rw [← h1, IsIso.inv_hom_id_assoc]
  rw [hm]
  exact @mono_comp (Modules.{u, u} B S hS X.1 X.2) _ _ _ _ _ (IsIso.mono_of_iso _) _ hD

end Mono

end AlgebraicGeometry.Space

end

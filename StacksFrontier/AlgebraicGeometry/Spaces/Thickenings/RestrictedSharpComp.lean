module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivationMoveRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceBaseAgreement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftChartKernel

/-!
# The restricted comorphism of a composite of morphisms of thickenings

Let `k : U' ⟶ X'` and `c : X' ⟶ W` be morphisms of algebraic spaces, and let `Z_U ⊆ U'`,
`Z_X ⊆ X'` and `W₀ ⊆ W` be closed subspaces with `i_U ≫ k = k₀ ≫ i_X` and `i_X ≫ c = e₀ ≫ j`, so
that `(k₀, k)` and `(e₀, c)` are morphisms of pairs.  The comorphism of `c` read on the small étale
site of `W₀`, `AlgebraicGeometry.Space.restrictedSharpThroughThickening`, is a morphism of sheaves
of rings `j^{-1}𝒪_W ⟶ (e₀)_*(i_X^{-1}𝒪_{X'})`; that of `k` is a morphism
`i_X^{-1}𝒪_{X'} ⟶ (k₀)_*(i_U^{-1}𝒪_{U'})`.

This file proves that the restricted comorphism of the composite `k ≫ c` is the composite of the
two, read through the comparison of iterated direct images.  This is the source-side composition
law that the target-side law `AlgebraicGeometry.Space.structureSharpThroughThickening_comp`
does not cover: there the second factor is composed after the thickening, here before it.

## Main results

* `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_left`: the comorphism of
  `k ≫ c` read through the thickening of `U'` is that of `c`, followed by the direct image of the
  restricted comorphism of `k` and the comparison of iterated direct images.
* `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp`: **the restricted comorphism of
  `k ≫ c` is the restricted comorphism of `c` followed by the direct image along `e₀` of the
  restricted comorphism of `k`**, read through the comparison of iterated direct images.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), whose difference this
  law makes compatible with restriction along a morphism of thickenings.
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), part (3).
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the comorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Comp

variable {X' U' W : AlgebraicSpaces B S hS} (ZX : ClosedSubspaces B S hS X'.1)
  (ZU : ClosedSubspaces B S hS U'.1) (k : U' ⟶ X')
  (k₀ : (⟨ZU.1.toFunctor, ZU.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS))
  (hk : subspaceInclusion B S hS U' ZU ≫ k = k₀ ≫ subspaceInclusion B S hS X' ZX)

/-- The restricted comorphism of `k`, read back on the small étale site of `X'`: the unit of
`i_X^{-1} ⊣ (i_X)_*` followed by its direct image, composed with the comparison of iterated direct
images, is the comorphism of `k` read in the direct image along `k₀ ≫ i_X`. -/
theorem structureSharpThroughThickeningAt_eq_ringUnit_comp :
    structureSharpThroughThickeningAt B S hS ZU k (k₀ ≫ subspaceInclusion B S hS X' ZX) hk =
      ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX))
          (structureRingSheaf B S hS X') ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X' ZX))).map
          (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
        pushforwardRingSheafCompHom B S hS k₀ (subspaceInclusion B S hS X' ZX)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)) := by
  have hσ := ringUnit_comp_map_restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk
  have hinv := pushforwardRingSheafCompInv_comp_hom B S hS k₀ (subspaceInclusion B S hS X' ZX)
    (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))
  exact ((Category.comp_id _).symm.trans (congrArg (fun m => structureSharpThroughThickeningAt
      B S hS ZU k (k₀ ≫ subspaceInclusion B S hS X' ZX) hk ≫ m) hinv.symm)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ pushforwardRingSheafCompHom
      B S hS k₀ (subspaceInclusion B S hS X' ZX)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))) hσ.symm).trans
      (Category.assoc _ _ _)))

/-- The shape of the chase behind
`AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_left`, in an arbitrary
category. -/
private theorem comp_chase_left {Cc : Type*} [Category Cc] {A Bq Bq' D D' E F : Cc}
    (x : A ⟶ E) (u : A ⟶ Bq) (s : Bq ⟶ D) (t : D ⟶ E) (v : E ⟶ F) (w : Bq ⟶ Bq')
    (s' : Bq' ⟶ D') (w' : D ⟶ D') (v' : D' ⟶ F) (hx : x = u ≫ s ≫ t)
    (hassoc : t ≫ v = w' ≫ v') (hnat : s ≫ w' = w ≫ s') :
    x ≫ v = u ≫ w ≫ s' ≫ v' := by
  rw [hx, Category.assoc, Category.assoc, hassoc, ← Category.assoc s, hnat, Category.assoc]

/-- The chase behind `AlgebraicGeometry.Space.structureSharpThroughThickeningAt_comp_left`:
the direct image along `c` of the restricted comorphism of `k`, read back on `X'`, followed by the
comparison of iterated direct images. -/
theorem map_ringUnit_comp_compHom (c : X' ⟶ W) :
    (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
        (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX))
            (structureRingSheaf B S hS X') ≫
          (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
            (subspaceInclusion B S hS X' ZX))).map
            (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
          pushforwardRingSheafCompHom B S hS k₀ (subspaceInclusion B S hS X' ZX)
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))) ≫
      pushforwardRingSheafCompHom B S hS (k₀ ≫ subspaceInclusion B S hS X' ZX) c
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)) =
    (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
        (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX))
          (structureRingSheaf B S hS X')) ≫
      pushforwardRingSheafCompHom B S hS (subspaceInclusion B S hS X' ZX) c
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' ZX)) ≫
      (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS X' ZX ≫ c))).map
        (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
      pushforwardRingSheafCompHom B S hS k₀ (subspaceInclusion B S hS X' ZX ≫ c)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)) := by
  refine comp_chase_left _ _ _ _ _ _ _ _ _ ?_
    (pushforwardRingSheafCompHom_assoc B S hS k₀ (subspaceInclusion B S hS X' ZX) c
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)))
    (pushforwardRingSheafCompHom_naturality B S hS (subspaceInclusion B S hS X' ZX) c
      (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk))
  exact ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map_comp _ _).trans
    (congrArg (fun m => (pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map
      (ringUnit (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS X' ZX))
        (structureRingSheaf B S hS X')) ≫ m)
      ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS c)).map_comp _ _))

/-- **The comorphism of a composite `k ≫ c` read through the thickening of the source of `k`.**
It is the comorphism of `c` read through the thickening of `X'`, followed by the direct image of
the restricted comorphism of `k` and by the comparison of iterated direct images. -/
theorem structureSharpThroughThickeningAt_comp_left (c : X' ⟶ W)
    (κ : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS) ⟶ W)
    (h : subspaceInclusion B S hS X' ZX ≫ c = κ)
    (h₂ : subspaceInclusion B S hS U' ZU ≫ k ≫ c = k₀ ≫ κ) :
    structureSharpThroughThickeningAt B S hS ZU (k ≫ c) (k₀ ≫ κ) h₂ =
      structureSharpThroughThickeningAt B S hS ZX c κ h ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS κ)).map
          (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
        pushforwardRingSheafCompHom B S hS k₀ κ
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)) := by
  subst h
  have key := structureSharp_comp_map_structureSharpThroughThickeningAt' B S hS ZU k c
    (k₀ ≫ subspaceInclusion B S hS X' ZX) hk
  have e1 : structureSharpThroughThickeningAt B S hS ZX c
      (subspaceInclusion B S hS X' ZX ≫ c) rfl = structureSharpThroughThickening B S hS ZX c :=
    Category.comp_id _
  rw [structureSharpThroughThickeningAt_eq_ringUnit_comp] at key
  rw [e1, structureSharpThroughThickening_eq_compHom]
  refine key.symm.trans ((Category.assoc _ _ _).trans ((congrArg
    (fun m => structureSharp B S hS c ≫ m) (map_ringUnit_comp_compHom B S hS ZX ZU k k₀ hk c)).trans
    (congrArg (fun m => structureSharp B S hS c ≫ m) (Category.assoc _ _ _).symm)))

/-- The shape of the chase behind `AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp`,
in an arbitrary category. -/
private theorem comp_chase_right {Cc : Type*} [Category Cc] {A A' Bq Bq' D E : Cc}
    (r : A ⟶ Bq) (ci : A ⟶ A') (m : A' ⟶ Bq') (ci' : Bq ⟶ Bq') (jc : Bq' ⟶ D) (chk : D ⟶ E)
    (che : Bq' ⟶ Bq) (chk2 : Bq ⟶ E) (cik : E ⟶ D) (hn : r ≫ ci' = ci ≫ m)
    (has : jc ≫ chk = che ≫ chk2) (hinv₁ : ci' ≫ che = 𝟙 Bq) (hinv₂ : chk ≫ cik = 𝟙 D) :
    ci ≫ m ≫ jc = r ≫ chk2 ≫ cik := by
  rw [← reassoc_of% hn, ← Category.comp_id jc, ← hinv₂, reassoc_of% has, reassoc_of% hinv₁]

variable {W : AlgebraicSpaces B S hS} (W₀ : ClosedSubspaces B S hS W.1)

/-- The adjunct of the restricted comorphism of `c` is the comorphism of `c` read through the
thickening, followed by the inverse comparison of iterated direct images. -/
private theorem homEquiv_restrictedSharpThroughThickening {X : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS X.1) (c : X ⟶ W)
    (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    ((ringImageAdjunction (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).homEquiv _ _)
        (restrictedSharpThroughThickening B S hS Z W₀ c e₀ h) =
      structureSharpThroughThickeningAt B S hS Z c (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
        pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X Z)) :=
  (ringImageAdjunction_homEquiv_apply _ _ _ _).trans
    (ringUnit_comp_map_restrictedSharpThroughThickening B S hS Z W₀ c e₀ h)

/-- **The restricted comorphism of a composite of morphisms of pairs.**  For morphisms of pairs
`(k₀, k) : (Z_U ⊆ U') ⟶ (Z_X ⊆ X')` and `(e₀, c) : (Z_X ⊆ X') ⟶ (W₀ ⊆ W)`, the comorphism of
`k ≫ c` read on the small étale site of `W₀` is the comorphism of `c` read there, followed by the
direct image along `e₀` of the comorphism of `k` read on the small étale site of `Z_X`, and by the
comparison of iterated direct images:

`(k ≫ c)^♯ = (e₀)_*(k^♯) ∘ c^♯ : j^{-1}𝒪_W ⟶ (e₀)_*(i_X^{-1}𝒪_{X'}) ⟶ (k₀ ≫ e₀)_*(i_U^{-1}𝒪_{U'})`.

This is what makes the difference of two morphisms of [Stacks Project, Tag 0618] compatible with
precomposition by a morphism of thickenings. -/
theorem restrictedSharpThroughThickening_comp (c : X' ⟶ W)
    (e₀ : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X' ZX ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₂ : subspaceInclusion B S hS U' ZU ≫ k ≫ c =
      (k₀ ≫ e₀) ≫ subspaceInclusion B S hS W W₀) :
    restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c) (k₀ ≫ e₀) h₂ =
      restrictedSharpThroughThickening B S hS ZX W₀ c e₀ h ≫
        (pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
        pushforwardRingSheafCompHom B S hS k₀ e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)) := by
  apply ((ringImageAdjunction (smallToposMorphismTypeU B S hS
    (subspaceInclusion B S hS W W₀))).homEquiv _ _).injective
  have L := homEquiv_restrictedSharpThroughThickening B S hS W₀ ZU (k ≫ c) (k₀ ≫ e₀) h₂
  have Rc := homEquiv_restrictedSharpThroughThickening B S hS W₀ ZX c e₀ h
  have R := (ringImageAdjunction (smallToposMorphismTypeU B S hS
      (subspaceInclusion B S hS W W₀))).homEquiv_naturality_right
    (restrictedSharpThroughThickening B S hS ZX W₀ c e₀ h)
    ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
          (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
        pushforwardRingSheafCompHom B S hS k₀ e₀
          (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)))
  have S1 := structureSharpThroughThickeningAt_comp_left B S hS ZX ZU k k₀ hk c
    (e₀ ≫ subspaceInclusion B S hS W W₀) h h₂
  have hch := comp_chase_right _ _ _ _ _ _ _ _ _
    (pushforwardRingSheafCompInv_naturality B S hS e₀ (subspaceInclusion B S hS W W₀)
      (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk))
    (pushforwardRingSheafCompHom_assoc B S hS k₀ e₀ (subspaceInclusion B S hS W W₀)
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU)))
    (pushforwardRingSheafCompInv_comp_hom B S hS e₀ (subspaceInclusion B S hS W W₀) _)
    (pushforwardRingSheafCompHom_comp_inv B S hS (k₀ ≫ e₀) (subspaceInclusion B S hS W W₀) _)
  refine L.trans ((congrArg (· ≫ _) S1).trans ?_)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    hch.symm)).trans ?_)
  refine Eq.trans ?_ (R.trans (congrArg (· ≫ _) Rc)).symm
  have hmap : (pushforwardRingFunctor (smallToposMorphismTypeU B S hS
        (subspaceInclusion B S hS W W₀))).map
        ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
            (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
          pushforwardRingSheafCompHom B S hS k₀ e₀
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))) =
      pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward
          (pullbackRingSheafMap (SmallEtale.topology B S hS
            (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)
            (smallToposMorphismTypeU B S hS e₀).pushforward
            (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk)) ≫
        pullbackRingSheafMap (SmallEtale.topology B S hS W.1)
          (smallToposMorphismTypeU B S hS (subspaceInclusion B S hS W W₀)).pushforward
          (pushforwardRingSheafCompHom B S hS k₀ e₀
            (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))) :=
    Functor.map_comp _ _ _
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t =>
    (structureSharpThroughThickeningAt B S hS ZX c (e₀ ≫ subspaceInclusion B S hS W W₀) h ≫
      pushforwardRingSheafCompInv B S hS e₀ (subspaceInclusion B S hS W W₀)
        (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS X' ZX))) ≫ t) hmap.symm)

include hk in
/-- **Hypothesis (2) of [Stacks Project, Tag 0618] is stable under precomposition by a morphism of
pairs.**  If the restricted comorphisms of `c` and `c'` agree on the sections killed by
`j^♯ : j^{-1}𝒪_W ⟶ 𝒪_{W₀}`, so do those of `k ≫ c` and `k ≫ c'`: by
`AlgebraicGeometry.Space.restrictedSharpThroughThickening_comp` both are obtained from the former
by one and the same morphism of sheaves of rings. -/
theorem restrictedSharpThroughThickening_comp_app_eq (c c' : X' ⟶ W)
    (e₀ : (⟨ZX.1.toFunctor, ZX.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
    (h : subspaceInclusion B S hS X' ZX ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h' : subspaceInclusion B S hS X' ZX ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (h₂ : subspaceInclusion B S hS U' ZU ≫ k ≫ c =
      (k₀ ≫ e₀) ≫ subspaceInclusion B S hS W W₀)
    (h₂' : subspaceInclusion B S hS U' ZU ≫ k ≫ c' =
      (k₀ ≫ e₀) ≫ subspaceInclusion B S hS W W₀)
    (hker : ∀ (V : (SmallEtale B S hS
        (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).obj.obj V),
      (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app V x = 0 →
        (restrictedSharpThroughThickening B S hS ZX W₀ c e₀ h).hom.app V x =
          (restrictedSharpThroughThickening B S hS ZX W₀ c' e₀ h').hom.app V x)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x = 0) :
    (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c) (k₀ ≫ e₀) h₂).hom.app V x =
      (restrictedSharpThroughThickening B S hS ZU W₀ (k ≫ c') (k₀ ≫ e₀) h₂').hom.app V x := by
  rw [restrictedSharpThroughThickening_comp B S hS ZX ZU k k₀ hk W₀ c e₀ h h₂,
    restrictedSharpThroughThickening_comp B S hS ZX ZU k k₀ hk W₀ c' e₀ h' h₂']
  exact congrArg (fun y => ((pushforwardRingFunctor (smallToposMorphismTypeU B S hS e₀)).map
      (restrictedSharpThroughThickening B S hS ZU ZX k k₀ hk) ≫
    pushforwardRingSheafCompHom B S hS k₀ e₀
      (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS U' ZU))).hom.app V y)
    (hker V x hx)

end Comp

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftDerivationActionChart

/-!
# The action of a derivation on a morphism of first order thickenings

Let `B` be a big fppf site, `S` a scheme contained in it and `Bas` an algebraic space over `S`.
Let `Z ⊂ X` be a first order thickening and `W₀ ⊂ W` a closed subspace of algebraic spaces, with
inclusions `i : Z ⟶ X` and `j : W₀ ⟶ W`, where `X` and `W` lie over `Bas` through `p : X ⟶ Bas`
and `r : W ⟶ Bas`, and let `e₀ : Z ⟶ W₀`.  A morphism `c : X ⟶ W` over `Bas` with
`i ≫ c = e₀ ≫ j` is the same thing as a morphism of thickenings `(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)`
over `Bas`; these are the elements of `AlgebraicGeometry.Space.ThickeningLiftOver`.

[Stacks Project, Tag 04D0] says that for such a `c` and an `𝒪_Z`-linear map
`θ : e₀^*Ω_{W₀/Bas} ⟶ 𝒞_{Z/X}` there is exactly one morphism of thickenings `(e₀, c')` over `Bas`
whose comorphism agrees with that of `c` on the ideal of `W₀` and differs from it by the
`𝒪_{Bas}`-derivation `D = d_{W₀/Bas} ∘ θ` which Equation (0619) attaches to `θ`.
[Stacks Project, Tag 0CK6] writes `θ · c` for it and observes that the notation means nothing
else than this: `c^♯` and `(θ · c)^♯` differ by the derivation `D` related to `θ` by Equation
(0619).  This file constructs `θ · c`, proves both statements, and shows that `θ · c` is an
additive action of the group of such maps `θ` on the morphisms of thickenings extending `e₀`.

## Main definitions

* `AlgebraicGeometry.Space.ThickeningLiftOver`: the morphisms of thickenings
  `(Z ⊂ X) ⟶ (W₀ ⊂ W)` over `Bas` restricting to `e₀` on `Z`.
* `AlgebraicGeometry.Space.thickeningLiftSharp`: the comorphism of such a morphism, read on the
  small étale site of `W₀` as a map `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)`.
* `AlgebraicGeometry.Space.thickeningDerivationValue`: the value `ι (D (j^♯ s))` at a section `s`
  of `j^{-1}𝒪_W` of the composite `j^{-1}𝒪_W ⟶ 𝒪_{W₀} ⟶ (e₀)_*𝒞_{Z/X} ⟶ (e₀)_*(i^{-1}𝒪_X)`, where
  `D` is the derivation attached to `θ` by Equation (0619).
* `AlgebraicGeometry.Space.derivationTranslate`: **the morphism `θ · c`** of Tag 0CK6.
* `AlgebraicGeometry.Space.derivationAddAction`: **the action `θ · c`**, as an `AddAction`.

## Main results

* `AlgebraicGeometry.Space.thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate`:
  **[Stacks Project, Tag 0CK6]**, the comorphisms of `c` and of `θ · c` differ by `D`.
* `AlgebraicGeometry.Space.eq_derivationTranslate_iff`: **[Stacks Project, Tag 0CK6]**, that
  property characterises `θ · c`; `AlgebraicGeometry.Space.eq_derivationTranslate_of_sub` is the
  uniqueness for an arbitrary morphism agreeing with `e₀` on `Z`, not asked to lie over `Bas`.
* `AlgebraicGeometry.Space.thickeningLiftSharp_app_eq_derivationTranslate_of_app_eq_zero`:
  condition (2) of [Stacks Project, Tag 0618] for the pair `(c, θ · c)`.
* `AlgebraicGeometry.Space.existsUnique_thickeningLiftOver_sub_eq`:
  **[Stacks Project, Tag 04D0]**, existence and uniqueness of `θ · c`.
* `AlgebraicGeometry.Space.derivationTranslate_zero` and
  `AlgebraicGeometry.Space.derivationTranslate_add`: the laws of an action.

## Implementation notes

**Where the comorphisms are compared.**  Throughout Section 0617 the source reads sheaves on a
thickening as sheaves on the thickened space (Equations (05ZL) and (05ZM)).  Here the comorphism
of `c` is read on the small étale site of `W₀`, as `restrictedSharpThroughThickening`, a map
`j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)` into the ambient sheaf of rings of
`AlgebraicGeometry.Space.restrictedSquareZeroValues`, whose square-zero ideal is `(e₀)_*𝒞_{Z/X}`,
included by `ι`.  The factorisation `𝒪_{Y'} ⟶ 𝒪_Y ⟶ a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}` of Tag 0618 is
then literally `s ↦ ι (D (j^♯ s))`.  Every morphism of thickenings determines its comorphism in
this spelling and is determined by it, by
`AlgebraicGeometry.Space.eq_of_restrictedSharpThroughThickening_eq`.

**The sign.**  Tag 0618 attaches its derivation to the difference `(a')^♯ − (b')^♯` of the pair
`((a, a'), (b, b'))`, and Tag 04D0 asks for the derivation of the pair `((a, a'), (b, b'))` to be
`d_{Y/B} ∘ θ`; so `c^♯ − (θ · c)^♯ = ι ∘ D ∘ j^♯` is the convention of the statements.  The proof
of Tag 04D0 writes `α = (a')^♯ + D`, which is the same construction at `−θ`; the statements are
followed here, as in `AlgebraicGeometry.Space.restrictedLiftSolutionOfHom`.

**Condition (2) of Tag 0618.**  The two maps `a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of Tag 04CP are induced
by the restrictions of the two comorphisms to the ideal of `Y` in `Y'`, so they are equal exactly
when the comorphisms agree on the sections killed by `j^♯`.  That is how the condition is stated
here, as it is in `AlgebraicGeometry.Space.restrictedLiftDifferenceData`.

**The base of the differentials.**  The differentials are `Ω_{W₀/Bas₀}` for a morphism
`b : W₀ ⟶ Bas₀` and a morphism `ib : Bas₀ ⟶ Bas` with `j ≫ r = b ≫ ib`.  The source's
`Ω_{Y/B}` is the case `Bas₀ = Bas`, `b = j ≫ r`, `ib = 𝟙`; the square is all that is used of it.
Likewise `W₀ ⊂ W` is only asked to be a closed subspace, where the source asks for a first order
thickening.

**Local sections.**  Tag 0CK6 speaks of a local section `θ`, a section over an étale `U'` of the
sheaf `Hom(a^*Ω_{Y/B}, 𝒞_{X/X'})`.  The statements here are made for an arbitrary first order
thickening, so they apply to the first order thickening `U ⊂ U'`, `U = Z ×_X U'`, and the
restriction of `e₀`; such a section is a map into `𝒞_{U/U'}` through the étale restriction of the
conormal module, `AlgebraicGeometry.Space.conormalModuleEtaleRestrictionIso`.

## References

* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

section Additivity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y T : AlgebraicSpaces B S hS} (a : X ⟶ Y) (b : Y ⟶ T) (C : Modules B S hS X.1 X.2)

/-- **The derivation attached by Equation (0619) is additive in the linear map.**  For
`a : X ⟶ Y`, `b : Y ⟶ T` and an `𝒪_X`-module `C`, the derivation `d_{Y/T} ∘ (θ₁ + θ₂)` is the sum
of `d_{Y/T} ∘ θ₁` and `d_{Y/T} ∘ θ₂`, on every section of `𝒪_Y`. -/
theorem derivationDirectImageEquiv_add_d
    (θ₁ θ₂ : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS b) ⟶ C)
    (V : (SmallEtale B S hS Y.1)ᵒᵖ) (y : (structureRingSheaf B S hS Y).obj.obj V) :
    (derivationDirectImageEquiv B S hS a b C (θ₁ + θ₂)).d (X := V) y =
      (derivationDirectImageEquiv B S hS a b C θ₁).d (X := V) y +
        (derivationDirectImageEquiv B S hS a b C θ₂).d (X := V) y := by
  have hadd : (modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS b) C
        (θ₁ + θ₂) =
      (modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS b) C θ₁ +
        (modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS b) C θ₂ :=
    map_add ((modulePullbackAdjunction B S hS a).homAddEquiv
      (sheafOfDifferentials B S hS b) C) _ _
  rw [derivationDirectImageEquiv_apply, derivationDirectImageEquiv_apply,
    derivationDirectImageEquiv_apply, hadd]
  rfl

/-- **The derivation attached by Equation (0619) to the zero map is zero.** -/
theorem derivationDirectImageEquiv_zero_d (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (y : (structureRingSheaf B S hS Y).obj.obj V) :
    (derivationDirectImageEquiv B S hS a b C 0).d (X := V) y = 0 := by
  have h := derivationDirectImageEquiv_add_d B S hS a b C 0 0 V y
  rw [add_zero] at h
  exact left_eq_add.mp h

end Additivity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X W Bas : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1) (W₀ : ClosedSubspaces B S hS W.1)
  (e₀ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
    (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  {Bas₀ : AlgebraicSpaces B S hS}
  (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
  (r : W ⟶ Bas) (ib : Bas₀ ⟶ Bas)
  (hsq : subspaceInclusion B S hS W W₀ ≫ r = b ≫ ib) (p : X ⟶ Bas)

/-- **The morphisms of thickenings `(Z ⊂ X) ⟶ (W₀ ⊂ W)` over `Bas` extending `e₀`**: the
morphisms `c : X ⟶ W` with `i ≫ c = e₀ ≫ j` and `c ≫ r = p`.  In the notation of
[Stacks Project, Tag 04D0] these are the morphisms of first order thickenings `(a, a')` over `B`
with `a = e₀`. -/
def ThickeningLiftOver : Type (u + 1) :=
  {c : X ⟶ W // subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀ ∧
    c.hom ≫ r.hom = p.hom}

/-- **The comorphism of a morphism of thickenings**, read on the small étale site of `W₀`: for
`c : X ⟶ W` with `i ≫ c = e₀ ≫ j`, the map `j^{-1}𝒪_W ⟶ (e₀)_*(i^{-1}𝒪_X)` of
`AlgebraicGeometry.Space.restrictedSharpThroughThickening`, with its target written as the ambient
sheaf of rings of the square-zero ideal `(e₀)_*𝒞_{Z/X}`. -/
noncomputable def thickeningLiftSharp (c : X ⟶ W)
    (hc : subspaceInclusion B S hS X Z ≫ c = e₀ ≫ subspaceInclusion B S hS W W₀) :
    structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀) ⟶
      (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ambient :=
  restrictedSharpThroughThickening B S hS Z W₀ c e₀ hc

/-- **The derivation of Equation (0619), read as a map into the ambient sheaf of rings.**  For
an `𝒪_Z`-linear map `θ : e₀^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}` and a section `s` of `j^{-1}𝒪_W`, this is
`ι (D (j^♯ s))`, where `D = d_{W₀/Bas₀} ∘ θ : 𝒪_{W₀} ⟶ (e₀)_*𝒞_{Z/X}` is the `𝒪_{Bas₀}`-derivation
attached to `θ` by `AlgebraicGeometry.Space.derivationDirectImageEquiv` and `ι` the inclusion of
the ideal `(e₀)_*𝒞_{Z/X}` into `(e₀)_*(i^{-1}𝒪_X)`.  It is the composite
`𝒪_{Y'} ⟶ 𝒪_Y ⟶ a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}` of [Stacks Project, Tag 0618]. -/
noncomputable abbrev thickeningDerivationValue
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V) :
    (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ambient.obj.obj V :=
  (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ).ι
    ((derivationDirectImageEquiv B S hS e₀ b (conormalModule B S hS X Z) θ).d (X := V)
      ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x))

/-- **The morphism `θ · c`.**  For a morphism of thickenings `c` extending `e₀` and an
`𝒪_Z`-linear map `θ : e₀^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}`, the morphism of thickenings extending `e₀`
whose comorphism is that of `c` moved by the derivation attached to `θ` by Equation (0619). -/
@[stacks 0CK6 "the morphism theta . a' of thickenings over the base"]
noncomputable def derivationTranslate
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p) : ThickeningLiftOver B S hS Z W₀ e₀ r p :=
  let h := exists_hom_restrictedSharpThroughThickening_eq_restrictedLiftSolutionOfHom_of_square
    B S hS Z hZ c.1 W₀ e₀ c.2.1 b θ r ib hsq p c.2.2
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1⟩

/-- The comorphism of `θ · c` is the solution of the lifting problem attached to `θ`,
`AlgebraicGeometry.Space.restrictedLiftSolutionOfHom`. -/
theorem restrictedSharpThroughThickening_derivationTranslate
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p) :
    restrictedSharpThroughThickening B S hS Z W₀
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).1 e₀
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).2.1 =
      restrictedLiftSolutionOfHom B S hS Z hZ c.1 W₀ e₀ c.2.1 b θ :=
  (exists_hom_restrictedSharpThroughThickening_eq_restrictedLiftSolutionOfHom_of_square
    B S hS Z hZ c.1 W₀ e₀ c.2.1 b θ r ib hsq p c.2.2).choose_spec.choose_spec.2

/-- **The comorphisms of `c` and of `θ · c` differ by the derivation related to `θ` by
Equation (0619).**  On every section `s` of `j^{-1}𝒪_W`,

`c^♯ s − (θ · c)^♯ s = ι (D (j^♯ s))`, where `D = d_{W₀/Bas₀} ∘ θ`.

That is, `(a')^♯ − (θ · a')^♯` factors as `𝒪_{Y'} ⟶ 𝒪_Y ⟶ a_*𝒞_{X/X'} ⟶ a_*𝒪_{X'}` through the
derivation `D` that Equation (0619) attaches to `θ`. -/
@[stacks 0CK6 "the comorphisms of a' and theta . a' differ by the derivation D = d o theta of \
Equation 0619"]
theorem thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V) :
    (thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1).hom.app V x -
        (thickeningLiftSharp B S hS Z hZ W₀ e₀
          (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).1
          (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).2.1).hom.app V x =
      thickeningDerivationValue B S hS Z hZ W₀ e₀ b θ V x := by
  have key := (liftDifferenceDataOfHom B S hS b e₀ (conormalModule B S hS X Z)
    (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
    (restrictedSharpThroughThickening B S hS Z W₀ c.1 e₀ c.2.1)
    (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c.1 c.2.1 x m) θ).ι_diff x
  have hg : (liftDifferenceDataOfHom B S hS b e₀ (conormalModule B S hS X Z)
      (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c.1 e₀ c.2.1)
      (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c.1 c.2.1 x m) θ).g =
      thickeningLiftSharp B S hS Z hZ W₀ e₀
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).1
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).2.1 :=
    (restrictedSharpThroughThickening_derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).symm
  have hf : (liftDifferenceDataOfHom B S hS b e₀ (conormalModule B S hS X Z)
      (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c.1 e₀ c.2.1)
      (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c.1 c.2.1 x m) θ).f =
      thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1 :=
    liftDifferenceDataOfHom_f B S hS b e₀ (conormalModule B S hS X Z) _ _ θ
  have hd : (liftDifferenceDataOfHom B S hS b e₀ (conormalModule B S hS X Z)
      (E := restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c.1 e₀ c.2.1)
      (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c.1 c.2.1 x m) θ).diff x =
      (derivationDirectImageEquiv B S hS e₀ b (conormalModule B S hS X Z) θ).d (X := V)
        ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x) :=
    Stacks.Sites.derivationActionData_diff (restrictedSquareZeroValues B S hS Z W₀ e₀ hZ)
      (restrictedSharpThroughThickening B S hS Z W₀ c.1 e₀ c.2.1)
      (derivationFamilyOfHom B S hS b e₀ (conormalModule B S hS X Z) θ)
      (derivationFamilyOfHom_mul B S hS b e₀ (conormalModule B S hS X Z) θ)
      (derivationFamilyOfHom_map B S hS b e₀ (conormalModule B S hS X Z) θ)
      (fun _ x m ↦ restrictedSquareZeroValues_ι_smul B S hS Z W₀ e₀ hZ c.1 c.2.1 x m) V x
  rw [hf, hg] at key
  rw [← key, hd]

/-- **A morphism whose comorphism differs from that of `c` by the derivation attached to `θ` is
`θ · c`.**  The morphism `c'` is only asked to agree with `e₀` on `Z`; that it lies over `Bas`
follows.  This is the uniqueness half of [Stacks Project, Tag 04D0]. -/
theorem eq_derivationTranslate_of_sub
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p) (c' : X ⟶ W)
    (hc' : subspaceInclusion B S hS X Z ≫ c' = e₀ ≫ subspaceInclusion B S hS W W₀)
    (hd : ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
      (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V),
      (thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1).hom.app V x -
          (thickeningLiftSharp B S hS Z hZ W₀ e₀ c' hc').hom.app V x =
        thickeningDerivationValue B S hS Z hZ W₀ e₀ b θ V x) :
    c' = (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).1 := by
  have h : thickeningLiftSharp B S hS Z hZ W₀ e₀ c' hc' =
      thickeningLiftSharp B S hS Z hZ W₀ e₀
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).1
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).2.1 :=
    Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ConcreteCategory.hom_ext _ _ fun x ↦
      sub_right_injective ((hd V x).trans
        (thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
          B S hS Z hZ W₀ e₀ b r ib hsq p θ c V x).symm)))
  exact eq_of_restrictedSharpThroughThickening_eq B S hS Z hZ W₀ c' _ e₀ hc'
    (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).2.1 h

/-- **The notation `θ · c` means nothing else than that the comorphisms differ by the
derivation related to `θ` by Equation (0619).**  A morphism of thickenings `c'` over `Bas`
extending `e₀` equals `θ · c` if and only if `c^♯ s − c'^♯ s = ι (D (j^♯ s))` for every section
`s` of `j^{-1}𝒪_W`, where `D = d_{W₀/Bas₀} ∘ θ`. -/
@[stacks 0CK6 "that theta . a' is characterised by the comorphisms of a' and theta . a' \
differing by the derivation D = d o theta of Equation 0619"]
theorem eq_derivationTranslate_iff
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c c' : ThickeningLiftOver B S hS Z W₀ e₀ r p) :
    c' = derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c ↔
      ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V),
        (thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1).hom.app V x -
            (thickeningLiftSharp B S hS Z hZ W₀ e₀ c'.1 c'.2.1).hom.app V x =
          thickeningDerivationValue B S hS Z hZ W₀ e₀ b θ V x := by
  refine ⟨?_, fun hd ↦ Subtype.ext
    (eq_derivationTranslate_of_sub B S hS Z hZ W₀ e₀ b r ib hsq p θ c c'.1 c'.2.1 hd)⟩
  rintro rfl
  exact thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
    B S hS Z hZ W₀ e₀ b r ib hsq p θ c

/-- **Condition (2) of [Stacks Project, Tag 0618] for the pair `(c, θ · c)`.**  The comorphisms
of `c` and of `θ · c` agree on every section killed by `j^♯`, that is on the ideal of `W₀` in
`W`; equivalently they induce the same map `e₀^*𝒞_{W₀/W} ⟶ 𝒞_{Z/X}`. -/
theorem thickeningLiftSharp_app_eq_derivationTranslate_of_app_eq_zero
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p)
    (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : (structureRingSheafInverseImage B S hS (subspaceInclusion B S hS W W₀)).obj.obj V)
    (hx : (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x =
      0) :
    (thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1).hom.app V x =
      (thickeningLiftSharp B S hS Z hZ W₀ e₀
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).1
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c).2.1).hom.app V x := by
  have h := thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
    B S hS Z hZ W₀ e₀ b r ib hsq p θ c V x
  have h0 : (derivationDirectImageEquiv B S hS e₀ b (conormalModule B S hS X Z) θ).d (X := V)
      ((structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x) =
      0 := by
    rw [hx]
    exact map_zero _
  simp only [thickeningDerivationValue, h0, map_zero] at h
  exact sub_eq_zero.1 h

include ib hsq in
/-- Let `(e₀, c) : (Z ⊂ X) ⟶ (W₀ ⊂ W)` be a morphism of first order thickenings over `Bas` and
let `θ : e₀^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}` be `𝒪_Z`-linear.  Then
there is exactly one morphism of thickenings `(e₀, c')` over `Bas` — so condition (1) of
[Stacks Project, Tag 0618], `b = a`, holds — such that

* condition (2) of Tag 0618 holds: the comorphisms of `c` and `c'` agree on the sections killed
  by `j^♯`, and
* the derivation by which the comorphisms differ is related to `θ` by Equation (0619):
  `c^♯ s − c'^♯ s = ι (D (j^♯ s))` with `D = d_{W₀/Bas₀} ∘ θ`.

It is `θ · c`. -/
@[stacks 04D0 "existence and uniqueness of the morphism of pairs (a, b') satisfying (1) and (2) \
of 0618 whose comorphism differs from that of a' by the derivation d o theta of Equation 0619"]
theorem existsUnique_thickeningLiftOver_sub_eq
    (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p) :
    ∃! c' : ThickeningLiftOver B S hS Z W₀ e₀ r p,
      (∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V),
        (structureSharpRingInverseImage B S hS (subspaceInclusion B S hS W W₀)).hom.app V x =
            0 →
          (thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1).hom.app V x =
            (thickeningLiftSharp B S hS Z hZ W₀ e₀ c'.1 c'.2.1).hom.app V x) ∧
      ∀ (V : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
        (x : (structureRingSheafInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).obj.obj V),
        (thickeningLiftSharp B S hS Z hZ W₀ e₀ c.1 c.2.1).hom.app V x -
            (thickeningLiftSharp B S hS Z hZ W₀ e₀ c'.1 c'.2.1).hom.app V x =
          thickeningDerivationValue B S hS Z hZ W₀ e₀ b θ V x :=
  ⟨derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ c,
    ⟨thickeningLiftSharp_app_eq_derivationTranslate_of_app_eq_zero
        B S hS Z hZ W₀ e₀ b r ib hsq p θ c,
      thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
        B S hS Z hZ W₀ e₀ b r ib hsq p θ c⟩,
    fun c' hc' ↦ (eq_derivationTranslate_iff B S hS Z hZ W₀ e₀ b r ib hsq p θ c c').2 hc'.2⟩

/-- **The zero map acts trivially**: `0 · c = c`. -/
theorem derivationTranslate_zero (c : ThickeningLiftOver B S hS Z W₀ e₀ r p) :
    derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p 0 c = c := by
  refine ((eq_derivationTranslate_iff B S hS Z hZ W₀ e₀ b r ib hsq p 0 c c).2 ?_).symm
  intro V x
  rw [sub_self, thickeningDerivationValue, derivationDirectImageEquiv_zero_d, map_zero]

/-- **The action is additive**: `(θ₁ + θ₂) · c = θ₁ · (θ₂ · c)`. -/
theorem derivationTranslate_add
    (θ₁ θ₂ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z)
    (c : ThickeningLiftOver B S hS Z W₀ e₀ r p) :
    derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p (θ₁ + θ₂) c =
      derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ₁
        (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ₂ c) := by
  refine ((eq_derivationTranslate_iff B S hS Z hZ W₀ e₀ b r ib hsq p (θ₁ + θ₂) c
    (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ₁
      (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ₂ c))).2 fun V x ↦ ?_).symm
  have h₁ := thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
    B S hS Z hZ W₀ e₀ b r ib hsq p θ₂ c V x
  have h₂ := thickeningLiftSharp_sub_thickeningLiftSharp_derivationTranslate
    B S hS Z hZ W₀ e₀ b r ib hsq p θ₁
    (derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p θ₂ c) V x
  have h₄ : thickeningDerivationValue B S hS Z hZ W₀ e₀ b (θ₁ + θ₂) V x =
      thickeningDerivationValue B S hS Z hZ W₀ e₀ b θ₁ V x +
        thickeningDerivationValue B S hS Z hZ W₀ e₀ b θ₂ V x := by
    unfold thickeningDerivationValue
    rw [derivationDirectImageEquiv_add_d]
    exact map_add _ _ _
  rw [h₄, ← h₁, ← h₂]
  exact (sub_add_sub_cancel' _ _ _).symm

/-- **The action `θ · c`.**  The group of `𝒪_Z`-linear maps `θ : e₀^*Ω_{W₀/Bas₀} ⟶ 𝒞_{Z/X}`
acts on the morphisms of thickenings over `Bas` extending `e₀` by `θ +ᵥ c = θ · c`. -/
@[stacks 0CK6 "the action of theta on a', written theta . a'", instance_reducible]
noncomputable def derivationAddAction :
    AddAction ((modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶
      conormalModule B S hS X Z) (ThickeningLiftOver B S hS Z W₀ e₀ r p) where
  vadd := derivationTranslate B S hS Z hZ W₀ e₀ b r ib hsq p
  zero_vadd := derivationTranslate_zero B S hS Z hZ W₀ e₀ b r ib hsq p
  add_vadd := derivationTranslate_add B S hS Z hZ W₀ e₀ b r ib hsq p

end AlgebraicGeometry.Space

end

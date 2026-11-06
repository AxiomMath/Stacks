module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChangeAlgebraicStacks
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.TwoSquareSheafBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.ProperBaseChangeAtAPoint

/-!
# The base change map for direct images along a 1-morphism of algebraic stacks

Let `S` be a scheme, let `τ` be a topology on the schemes of a big fppf site, and let

```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   v                 v
  𝒴' ------ g -----> 𝒴
```

be the 2-cartesian square of a cospan `f : 𝒳 ⟶ 𝒴`, `g : 𝒴' ⟶ 𝒴` of algebraic stacks over `S`.
Stacks 075H says that the base change map

`g⁻¹Rf_*ℱ ⟶ Rf'_*(g')⁻¹ℱ`

is an isomorphism, functorially in `ℱ`, for abelian sheaves and for sheaves of `𝒪_𝒳`-modules on
`𝒳_τ`. This file constructs that map and proves that it is an isomorphism.

The base change map is the one of Stacks 0736. In degree zero it is the mate of the
2-commutativity `f ∘ g' ≅ g ∘ f'` of the square under the adjunctions `f⁻¹ ⊣ f_*` and
`f'⁻¹ ⊣ f'_*`: the 2-cell `g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ (g')⁻¹` of inverse images, transposed through
the unit of `f'⁻¹ ⊣ f'_*` and the counit of `f⁻¹ ⊣ f_*`
(`CategoryTheory.TwoSquare.sheafBaseChange`). On underlying presheaves that is the base change of
right Kan extensions, which is invertible because the square is Guitart exact (Stacks 075B). The
inverse images `g⁻¹` and `(g')⁻¹` are exact, so their right derived functors are computed
degreewise, and the degree-zero map descends uniquely to a natural transformation
`Rf_* ⋙ R(g⁻¹) ⟶ R(g')⁻¹ ⋙ Rf'_*` of functors on bounded below derived categories
(`Stacks.Cohomology.BaseChange.derived`), characterized by its composite with the derived-functor
unit of `Rf_*`.

That it is an isomorphism is the source's argument: both sides are computed on a bounded below
complex of injectives, where the map is the degree-zero map applied degreewise, provided
`(g')⁻¹` carries injectives to `f'_*`-acyclic objects. That acyclicity is where the source uses
Stacks 075G: the fibre of `f'` over an object `y'` of `𝒴'` maps faithfully to `𝒳`, so the
restriction of `(g')⁻¹I` to it is injective for `I` injective (Stacks 06X1, Stacks 06X2 for
modules).

## Main definitions

* `AlgebraicGeometry.Stack.abelianDirectImageBaseChange`: the base change map
  `g⁻¹f_* ⟶ f'_*(g')⁻¹` of abelian sheaves.
* `AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange`: the base change map
  `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` of abelian sheaves, on bounded below derived categories.
* `AlgebraicGeometry.Stack.moduleDerivedDirectImageBaseChange`: the base change map
  `g^*Rf_* ⟶ Rf'_*(g')^*` of sheaves of modules, on bounded below derived categories.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_abelianDerivedDirectImageBaseChange`:
  **Stacks 075H** for abelian sheaves.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_moduleDerivedDirectImageBaseChange`:
  **Stacks 075H** for sheaves of modules.
* `AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange_fac` and
  `AlgebraicGeometry.Stack.moduleDerivedDirectImageBaseChange_fac`: the characterization of the
  derived base change maps by the derived-functor unit of `Rf_*`.

## Implementation notes

The map is stated on the bounded below derived categories, for all bounded below complexes `ℱ`;
the source's `ℱ`, an abelian sheaf or a sheaf of modules, is the complex concentrated in degree
zero. The inverse image is written through its right derived functor `R(g⁻¹)`, which the
exactness of `g⁻¹` identifies with `g⁻¹` applied degreewise
(`Stacks.Cohomology.BaseChange.exactUnit_isIso`).

The degree-zero map for sheaves of modules is the linear lift
`Stacks.SheafOfModules.directImageBaseChange` of the base change of right Kan extensions, which is
also what the base change map of the underlying abelian sheaves is on underlying presheaves.

The source restricts `τ` to the Zariski, étale, smooth, syntomic and fppf topologies. The abelian
statement holds for every topology on the schemes of the big fppf site and the module statement
for every topology coarser than the fppf topology; the five topologies of the source are among
these.

The isomorphisms `g⁻¹Rⁱf_*ℱ ≅ Rⁱf'_*(g')⁻¹ℱ` degree by degree are
`AlgebraicGeometry.Stack.AlgebraicStacks.abelianHigherDirectImageBaseChangeIso` and
`AlgebraicGeometry.Stack.AlgebraicStacks.moduleHigherDirectImageBaseChangeIso`.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u a

attribute [local instance] hasSheafify_associatedTopology_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Abelian sheaves -/

section Abelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- **The base change map `g⁻¹f_* ⟶ f'_*(g')⁻¹` of abelian sheaves.** For the canonical
2-cartesian square of categories fibred in groupoids over the big fppf category of `S` and any
topology `τ`, it is the mate, under the adjunctions `f⁻¹ ⊣ f_*` and `f'⁻¹ ⊣ f'_*`, of the 2-cell
`g⁻¹ ⋙ f'⁻¹ ⟶ f⁻¹ ⋙ (g')⁻¹` of inverse images given by the 2-commutativity `f ∘ g' ≅ g ∘ f'` of
the square (`CategoryTheory.TwoSquare.sheafBaseChange`). On underlying presheaves it is the base
change of right Kan extensions (`CategoryTheory.TwoSquare.sheafBaseChange_app_hom`). -/
noncomputable def abelianDirectImageBaseChange
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI : p𝒳.IsFibered := h𝒳.isFibered
    letI : p𝒴'.IsFibered := h𝒴'.isFibered
    letI : p𝒴.IsFibered := h𝒴.isFibered
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
    letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ) ⋙
        g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ) ⟶
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒳 τ) ⋙
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒴' τ) :=
  letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
    isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  letI : p𝒳.IsFibered := h𝒳.isFibered
  letI : p𝒴'.IsFibered := h𝒴'.isFibered
  letI : p𝒴.IsFibered := h𝒴.isFibered
  letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
  letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
  letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
  letI := isContinuous_of_isFiberedInGroupoids B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
  letI := isCocontinuous_of_isFiberedInGroupoids B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
  letI := isContinuous_of_isFiberedInGroupoids B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
  (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).sheafBaseChange AddCommGrpCat.{max (u + 1) a}
    (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
    (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴' τ)
    (associatedTopology B S hS p𝒴 τ)

/-- **Stacks 075B for abelian sheaves: the base change map is invertible.** The canonical square
is Guitart exact, so `CategoryTheory.TwoSquare.isIso_sheafBaseChange` applies. -/
instance isIso_abelianDirectImageBaseChange
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    IsIso (abelianDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc) := by
  have : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  unfold abelianDirectImageBaseChange
  infer_instance

/-- **The base change map `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` of abelian sheaves** on bounded below derived
categories, constructed as in Stacks 0736. It is the descent to right derived functors
(`Stacks.Cohomology.BaseChange.derived`) of the degree-zero base change map
`AlgebraicGeometry.Stack.abelianDirectImageBaseChange`: the inverse image `g⁻¹` is exact, so its
right derived functor is computed degreewise, and `Rf_* ⋙ R(g⁻¹)` is a right derived functor of
`f_* ⋙ g⁻¹`, so the degree-zero map followed by the derived-functor units of `R(g')⁻¹` and `Rf'_*`
descends uniquely (`AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange_fac`). -/
noncomputable def abelianDerivedDirectImageBaseChange
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI : p𝒳.IsFibered := h𝒳.isFibered
    letI : p𝒴'.IsFibered := h𝒴'.isFibered
    letI : p𝒴.IsFibered := h𝒴.isFibered
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
    letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    letI : (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ (h𝒴.isFibredOneMorphism hfc)
    letI : ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
    letI : (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
      additive_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ (h𝒴.isFibredOneMorphism hgc)
    letI : ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒳 τ)).Additive :=
      additive_sheafPushforwardContinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒳.isFibredOneMorphism TwoFibreProductOver.fst_comp_eq)
    (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
            (associatedTopology B S hS p𝒳 τ)
            (associatedTopology B S hS p𝒴 τ)).rightDerivedFunctorPlus ⋙
        (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
            (associatedTopology B S hS p𝒴' τ)
            (associatedTopology B S hS p𝒴 τ)).rightDerivedFunctorPlus ⟶
      ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒳 τ)).rightDerivedFunctorPlus ⋙
        ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
          AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒴' τ)).rightDerivedFunctorPlus := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let A := AddCommGrpCat.{max (u + 1) a}
  let JX := associatedTopology B S hS p𝒳 τ
  let JX' := associatedTopology B S hS pX' τ
  let JY := associatedTopology B S hS p𝒴 τ
  let JY' := associatedTopology B S hS p𝒴' τ
  have hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let : pX'.IsFibered := hX'.isFibered
  let : p𝒳.IsFibered := h𝒳.isFibered
  let : p𝒴'.IsFibered := h𝒴'.isFibered
  let : p𝒴.IsFibered := h𝒴.isFibered
  let hf := h𝒴.isFibredOneMorphism hfc
  let hg := h𝒴.isFibredOneMorphism hgc
  let hprX := h𝒳.isFibredOneMorphism
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let hprY := h𝒴'.isFibredOneMorphism
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := (hg.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprX.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprY.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let F := f.sheafPushforwardCocontinuous A JX JY
  let F' := f'.sheafPushforwardCocontinuous A JX' JY'
  let G := g.sheafPushforwardContinuous A JY' JY
  let G' := g'.sheafPushforwardContinuous A JX' JX
  let : F.Additive := additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ hf
  let : F'.Additive := additive_sheafPushforwardCocontinuous B S hS pX' p𝒴' f' τ hprY
  let : G.Additive := additive_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ hg
  let : G'.Additive := additive_sheafPushforwardContinuous B S hS pX' p𝒳 g' τ hprX
  let : PreservesFiniteLimits G := hg.preservesFiniteLimits_inverseImage
    (J := τ.over (B.obj hS)) (A := A)
  let := (hg.sheafAdjunctionInheritedTopology (τ.over (B.obj hS)) A).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits G := inferInstance
  exact Stacks.Cohomology.BaseChange.derived F F' G G'
    (abelianDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc)
    (asIso G.rightDerivedFunctorPlusUnith)

/-- **The derived base change map is the canonical one.** Precomposed with `g⁻¹` of the
derived-functor unit of `Rf_*`, the base change map
`AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange` is, on a bounded below complex, the
degree-zero base change map applied degreewise followed by the derived-functor units of
`R(g')⁻¹` and `Rf'_*`. Since `Rf_* ⋙ R(g⁻¹)` is a right derived functor of `f_* ⋙ g⁻¹` with that
unit, this equation determines the map. -/
theorem abelianDerivedDirectImageBaseChange_fac
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI : p𝒳.IsFibered := h𝒳.isFibered
    letI : p𝒴'.IsFibered := h𝒴'.isFibered
    letI : p𝒴.IsFibered := h𝒴.isFibered
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
    letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    letI : (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ (h𝒴.isFibredOneMorphism hfc)
    letI : ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
    letI : (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
      additive_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ (h𝒴.isFibredOneMorphism hgc)
    letI : ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒳 τ)).Additive :=
      additive_sheafPushforwardContinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒳.isFibredOneMorphism TwoFibreProductOver.fst_comp_eq)
    letI : PreservesFiniteLimits (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒴' τ)
          (associatedTopology B S hS p𝒴 τ)) :=
      (h𝒴.isFibredOneMorphism hgc).preservesFiniteLimits_inverseImage
        (J := τ.over (B.obj hS)) (A := AddCommGrpCat.{max (u + 1) a})
    letI := ((h𝒴.isFibredOneMorphism hgc).sheafAdjunctionInheritedTopology (τ.over (B.obj hS))
      AddCommGrpCat.{max (u + 1) a}).leftAdjoint_preservesColimits
    letI : PreservesFiniteColimits (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒴' τ)
          (associatedTopology B S hS p𝒴 τ)) := inferInstance
    Functor.whiskerRight (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒳 τ)
          (associatedTopology B S hS p𝒴 τ)).rightDerivedFunctorPlusUnith
        (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒴' τ)
          (associatedTopology B S hS p𝒴 τ)).rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (abelianDerivedDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc) =
    Stacks.Cohomology.BaseChange.onHomotopy
      (f.sheafPushforwardCocontinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒳 τ)
        (associatedTopology B S hS p𝒴 τ))
      ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ))
      (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒴' τ)
        (associatedTopology B S hS p𝒴 τ))
      ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒳 τ))
      (abelianDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc)
      (asIso (g.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
          (associatedTopology B S hS p𝒴' τ)
          (associatedTopology B S hS p𝒴 τ)).rightDerivedFunctorPlusUnith) := by
  have := h𝒳.isFibered
  have := h𝒴'.isFibered
  have := h𝒴.isFibered
  have := isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  have := additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ (h𝒴.isFibredOneMorphism hfc)
  have := additive_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ (h𝒴.isFibredOneMorphism hgc)
  have := additive_sheafPushforwardCocontinuous B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ
    (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
  have := additive_sheafPushforwardContinuous B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ
    (h𝒳.isFibredOneMorphism TwoFibreProductOver.fst_comp_eq)
  exact Stacks.Cohomology.BaseChange.derived_fac _ _ _ _ _ _

/-- The inverse image of abelian sheaves along a fibred 1-morphism preserves finite limits and
finite colimits. -/
private theorem preservesFiniteLimits_and_colimits_sheafPushforwardContinuous
    [p𝒳.IsFibered] [p𝒴.IsFibered] (hf : p𝒳.IsFibredOneMorphism p𝒴 f) :
    letI := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
    PreservesFiniteLimits (f.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)) ∧
      PreservesFiniteColimits (f.sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)) := by
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := hf.preservesFiniteLimits_inverseImage (J := τ.over (B.obj hS))
    (A := AddCommGrpCat.{max (u + 1) a})
  let := (hf.sheafAdjunctionInheritedTopology (τ.over (B.obj hS))
    AddCommGrpCat.{max (u + 1) a}).leftAdjoint_preservesColimits
  exact ⟨inferInstance, inferInstance⟩

/-- **Stacks 075H for abelian sheaves, on categories fibred in groupoids.** For the canonical
2-cartesian square of categories fibred in groupoids over the big fppf category of `S` whose apex
has equalizers, and any topology `τ`, the base change map `g⁻¹Rf_* ⟶ Rf'_*(g')⁻¹` of
`AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange` is an isomorphism of functors on the
bounded below derived category of abelian sheaves on `𝒳`.

Both sides are computed on a bounded below complex of injectives `I`: the left side by `f_*I`
followed by `g⁻¹` degreewise, the right side by `f'_*` of `(g')⁻¹I`, because `(g')⁻¹` carries
injectives to `f'_*`-acyclic sheaves
(`AlgebraicGeometry.Stack.isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj`, the input of
Stacks 075G and Stacks 06X1); on such a complex the map is the degree-zero base change map applied
degreewise, which is invertible (Stacks 075B). -/
theorem isIso_abelianDerivedDirectImageBaseChange
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)] :
    IsIso (abelianDerivedDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ
      h𝒳 h𝒴' h𝒴 hfc hgc) := by
  have := h𝒳.isFibered
  have := h𝒴'.isFibered
  have := h𝒴.isFibered
  have := isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  have hprY := h𝒴'.isFibredOneMorphism
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  have := additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ (h𝒴.isFibredOneMorphism hfc)
  have := additive_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ (h𝒴.isFibredOneMorphism hgc)
  have := additive_sheafPushforwardCocontinuous B S hS _ p𝒴' _ τ hprY
  have hprX := h𝒳.isFibredOneMorphism
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  have := additive_sheafPushforwardContinuous B S hS _ p𝒳 _ τ hprX
  obtain ⟨_, _⟩ := preservesFiniteLimits_and_colimits_sheafPushforwardContinuous.{u, a} B S hS
    p𝒴' p𝒴 g τ (h𝒴.isFibredOneMorphism hgc)
  obtain ⟨_, _⟩ := preservesFiniteLimits_and_colimits_sheafPushforwardContinuous.{u, a} B S hS
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ hprX
  have := (hprY.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  have := (hprX.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  have := (hprY.sheafAdjunctionInheritedTopology (τ.over (B.obj hS))
    AddCommGrpCat.{max (u + 1) a}).rightAdjoint_preservesLimits
  let F' := (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
    AddCommGrpCat.{max (u + 1) a}
    (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
    (associatedTopology B S hS p𝒴' τ)
  let G' := (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) a}
    (associatedTopology B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
    (associatedTopology B S hS p𝒳 τ)
  have : PreservesFiniteLimits F' := inferInstance
  exact Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived _ F' _ G'
    (abelianDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc)
    (fun M _ => inferInstance) (asIso _) fun I hI => by
      have := hI
      refine (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic _ _).2 fun m hm => ?_
      exact isZero_rightDerived_sheafPushforwardCocontinuous_snd_obj B S hS p𝒳 p𝒴' p𝒴 f g τ
        h𝒳 h𝒴' h𝒴 hfc hgc I m hm

end Abelian

/-! ### Sheaves of modules -/

section Module

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴' : Type (u + 1)} [Category.{u} 𝒴']
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

attribute [local instance] wEqualsLocallyBijective_associatedTopology_of_essentiallySmall
attribute [local instance] additive_modulePullback_ofFiberedInGroupoids
attribute [local instance] additive_moduleSheafPushforward_univ

/-- **The base change map `g^*Rf_* ⟶ Rf'_*(g')^*` of sheaves of modules** on bounded below
derived categories, constructed as in Stacks 0736: the descent to right derived functors of the
degree-zero base change map of `AlgebraicGeometry.Stack.moduleSheafPushforwardBaseChangeIso`, as
for abelian sheaves in `AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange`; the inverse
image `g^*` of sheaves of modules is exact, so `R(g^*)` is computed degreewise. The degree-zero
map is `Stacks.SheafOfModules.directImageBaseChange`, which on underlying abelian presheaves is
the base change of right Kan extensions
(`Stacks.SheafOfModules.directImageBaseChangeApp_toPresheaf`), as is the base change map of
abelian sheaves (`CategoryTheory.TwoSquare.sheafBaseChange_app_hom`). -/
noncomputable def moduleDerivedDirectImageBaseChange
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).rightDerivedFunctorPlus ⋙
        (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
          p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).rightDerivedFunctorPlus ⟶
      (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        τ hτ).rightDerivedFunctorPlus ⋙
        (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
        τ hτ).rightDerivedFunctorPlus := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let Pf := moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ
  let Pf' := moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS pX' p𝒴' hX' h𝒴' f'
    TwoFibreProductOver.snd_comp_eq τ hτ
  let Qg := modulePullback.{u, u + 1, u, max (u + 1) a} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
  let Qg' := modulePullback.{u, u + 1, u, max (u + 1) a} B S hS pX' p𝒳 hX' h𝒳 g'
    TwoFibreProductOver.fst_comp_eq τ hτ
  let : PreservesFiniteLimits Qg :=
    preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, max (u + 1) a}
      B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g
    hgc τ hτ).leftAdjoint_preservesColimits
  let : PreservesFiniteColimits Qg := inferInstance
  exact Stacks.Cohomology.BaseChange.derived Pf Pf' Qg Qg'
    (moduleSheafPushforwardBaseChangeIso.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc).hom
    (asIso Qg.rightDerivedFunctorPlusUnith)

/-- **The derived base change map of sheaves of modules is the canonical one**: precomposed with
`g^*` of the derived-functor unit of `Rf_*`, it is the degree-zero base change map applied
degreewise followed by the derived-functor units of `R(g')^*` and `Rf'_*`, which determines it. -/
theorem moduleDerivedDirectImageBaseChange_fac
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    letI : PreservesFiniteLimits (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) :=
      preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, max (u + 1) a}
        B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
    letI := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g
      hgc τ hτ).leftAdjoint_preservesColimits
    letI : PreservesFiniteColimits (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) :=
      inferInstance
    Functor.whiskerRight (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).rightDerivedFunctorPlusUnith
        (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
          p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        (moduleDerivedDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc) =
    Stacks.Cohomology.BaseChange.onHomotopy
      (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
      (moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq
        τ hτ)
      (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)
      (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq
        τ hτ)
      (moduleSheafPushforwardBaseChangeIso.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc).hom
      (asIso (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
          p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).rightDerivedFunctorPlusUnith) := by
  exact Stacks.Cohomology.BaseChange.derived_fac _ _ _ _ _ _

/-- The inverse image of sheaves of modules along a fibred 1-morphism preserves finite limits and
finite colimits. -/
private theorem preservesFiniteLimits_and_colimits_modulePullback
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) :
    PreservesFiniteLimits (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ) ∧
      PreservesFiniteColimits (modulePullback.{u, u + 1, u, max (u + 1) a} B S hS
        p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ) := by
  let := preservesFiniteLimits_modulePullback'.{u, u + 1, u, u + 1, u, max (u + 1) a}
    B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f
    hfc τ hτ).leftAdjoint_preservesColimits
  exact ⟨inferInstance, inferInstance⟩

/-- **Stacks 075H for sheaves of modules, on categories fibred in groupoids.** For the canonical
2-cartesian square of categories fibred in groupoids over the big fppf category of `S` whose apex
has equalizers, and any topology `τ` coarser than the fppf topology, the base change map
`g^*Rf_* ⟶ Rf'_*(g')^*` of `AlgebraicGeometry.Stack.moduleDerivedDirectImageBaseChange` is an
isomorphism of functors on the bounded below derived category of sheaves of `𝒪_𝒳`-modules.

As for abelian sheaves: the degree-zero base change map is invertible (Stacks 075B), `g^*` and
`(g')^*` are exact, and `(g')^*` carries injective sheaves of modules to `f'_*`-acyclic ones
(`AlgebraicGeometry.Stack.isZero_rightDerived_moduleSheafPushforward_snd_obj`, from Stacks 075G
and Stacks 06X2). -/
theorem isIso_moduleDerivedDirectImageBaseChange
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [HasEqualizers (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)] :
    IsIso (moduleDerivedDirectImageBaseChange.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ
      h𝒳 h𝒴' h𝒴 hfc hgc) := by
  let pX' := TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g
  let hX' : pX'.IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let g' := TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g
  let f' := TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g
  let Pf' := moduleSheafPushforward.{u, u + 1, u, max (u + 1) a} B S hS pX' p𝒴' hX' h𝒴' f'
    TwoFibreProductOver.snd_comp_eq τ hτ
  let Qg' := modulePullback.{u, u + 1, u, max (u + 1) a} B S hS pX' p𝒳 hX' h𝒳 g'
    TwoFibreProductOver.fst_comp_eq τ hτ
  obtain ⟨_, _⟩ := preservesFiniteLimits_and_colimits_modulePullback B S hS p𝒴' p𝒴 g τ hτ h𝒴' h𝒴 hgc
  obtain ⟨_, _⟩ := preservesFiniteLimits_and_colimits_modulePullback B S hS pX' p𝒳 g' τ hτ hX' h𝒳
    TwoFibreProductOver.fst_comp_eq
  let := (moduleSheafAdjunction.{u, u + 1, u, max (u + 1) a, u + 1, u} B S hS pX' p𝒴' hX' h𝒴'
    f' TwoFibreProductOver.snd_comp_eq τ hτ).rightAdjoint_preservesLimits
  let : PreservesFiniteLimits Pf' := inferInstance
  have hac : ∀ I, Injective I → Pf'.rightAcyclic (Qg'.obj I) := fun I hI => by
    let := hI
    refine (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic Pf' (Qg'.obj I)).2 fun m hm => ?_
    exact isZero_rightDerived_moduleSheafPushforward_snd_obj B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴'
      h𝒴 hfc hgc I m hm
  exact Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived _ Pf' _ Qg'
    (moduleSheafPushforwardBaseChangeIso.{u, a} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc).hom
    (fun M _ => inferInstance) (asIso _) hac

end Module

/-! ### Algebraic stacks -/

namespace AlgebraicStacks

universe w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 075H for abelian sheaves.** Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` be 1-morphisms of
algebraic stacks over `S`, with 2-cartesian square
```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   v                 v
  𝒴' ------ g -----> 𝒴
```
For every topology `τ` on the schemes of the big fppf site, the base change map
`g⁻¹Rf_*ℱ ⟶ Rf'_*(g')⁻¹ℱ` (`AlgebraicGeometry.Stack.abelianDerivedDirectImageBaseChange`, the
map of Stacks 0736 built from the adjunctions `f⁻¹ ⊣ f_*`, `f'⁻¹ ⊣ f'_*` and the 2-commutativity
of the square) is an isomorphism, functorially in `ℱ` in the bounded below derived category of
abelian sheaves on `𝒳_τ`; in particular for `ℱ` an abelian sheaf, placed in degree zero. -/
@[stacks 075H "abelian sheaves: the base change map g⁻¹Rf_*F ⟶ Rf'_*(g')⁻¹F is an isomorphism, \
functorially in F in D⁺(Ab(𝒳_τ))"]
theorem isIso_abelianDerivedDirectImageBaseChange {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (τ : GrothendieckTopology B.Schemes) :
    IsIso (abelianDerivedDirectImageBaseChange.{u, a} B S hS _ _ _
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ
      𝒳.val.property 𝒴'.val.property 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) :=
  let := hasEqualizers_twoFibreProductOver B S hS f g
  AlgebraicGeometry.Stack.isIso_abelianDerivedDirectImageBaseChange B S hS _ _ _
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ
    𝒳.val.property 𝒴'.val.property 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)

/-- **Stacks 075H for sheaves of modules.** For 1-morphisms `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` of
algebraic stacks over `S` with 2-cartesian square `𝒴' ×_𝒴 𝒳` as in
`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_abelianDerivedDirectImageBaseChange`, and every
topology `τ` coarser than the fppf topology, the base change map `g^*Rf_*ℱ ⟶ Rf'_*(g')^*ℱ`
(`AlgebraicGeometry.Stack.moduleDerivedDirectImageBaseChange`) is an isomorphism, functorially in
`ℱ` in the bounded below derived category of sheaves of `𝒪_𝒳`-modules on `𝒳_τ`; in particular for
`ℱ` a sheaf of `𝒪_𝒳`-modules, placed in degree zero. -/
@[stacks 075H "sheaves of modules: the base change map g⁻¹Rf_*F ⟶ Rf'_*(g')⁻¹F is an \
isomorphism, functorially in F in D⁺(Mod(𝒳_τ, O_𝒳))"]
theorem isIso_moduleDerivedDirectImageBaseChange {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    IsIso (moduleDerivedDirectImageBaseChange.{u, a} B S hS _ _ _
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ hτ
      𝒳.val.property 𝒴'.val.property 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)) :=
  let := hasEqualizers_twoFibreProductOver B S hS f g
  AlgebraicGeometry.Stack.isIso_moduleDerivedDirectImageBaseChange B S hS _ _ _
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ hτ
    𝒳.val.property 𝒴'.val.property 𝒴.val.property
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom)

end AlgebraicStacks

end AlgebraicGeometry.Stack

end

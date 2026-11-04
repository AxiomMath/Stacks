module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartLocalizedTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# The morphism of small étale topoi of a morphism of étale scheme charts

Let `S` be a scheme and let
```
  U --g--> V
  |        |
  p        q
  v        v
  X --f--> Y
```
be a commutative diagram of algebraic spaces over `S` with `p` and `q` étale and `U`, `V`
schemes. Stacks 04M5 asserts that, via the identifications of Stacks 04M1 of the small étale
ringed topoi of `U` and `V` with the localizations of those of `X` at `h_U` and of `Y` at `h_V`,
the morphism of small étale ringed topoi `(g_small, g♯)` is 2-isomorphic to the morphism
`(f_{small,s}, f_s♯)` that Stacks 04J8 builds from `(f_small, f♯)` and the map
`s : h_U ⟶ f_small⁻¹h_V` corresponding to `g`.

## Main definitions

* `AlgebraicGeometry.Space.chartSquareTwoIso`: the 2-isomorphism `f_small ∘ p_small ≅ q_small ∘
  g_small` of the commutative square, from the composition law of Stacks 03G8.
* `AlgebraicGeometry.Space.chartRelocalizationSheafMap`: the map `s : h_U ⟶ f_small⁻¹h_V`
  corresponding to `g`.

## Main results

* `AlgebraicGeometry.Space.chartRelocalizedTwoIso`: **Stacks 04M5.**
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The 2-isomorphism of the morphisms of small étale ringed topoi of two equal morphisms of
algebraic spaces. -/
noncomputable def smallEtaleRingedToposHomEqTwoIso {X Y : AlgebraicSpaces B S hS} {a b : X ⟶ Y}
    (h : a = b) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a)
      (smallEtaleRingedToposHom B S hS b) := by
  subst h
  exact RingedToposHom.TwoIso.refl (smallEtaleRingedToposHom B S hS a)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (U : SmallEtale B S hS X.1)
  (V : SmallEtale B S hS Y.1) (g : chartSpace B S hS X U ⟶ chartSpace B S hS Y V)
  (hg : g ≫ chartToSpace B S hS Y V = chartToSpace B S hS X U ≫ f)

/-- **The commutative square of charts, on small étale ringed topoi.** The composites
`f_small ∘ p_small` and `q_small ∘ g_small` are 2-isomorphic, by the composition law of
Stacks 03G8 and the commutativity `p ≫ f = g ≫ q`. -/
noncomputable def chartSquareTwoIso :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS f)
        (smallEtaleRingedToposHom B S hS (chartToSpace B S hS X U)))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (chartToSpace B S hS Y V))
        (smallEtaleRingedToposHom B S hS g)) :=
  (smallEtaleRingedToposHom_compTwoIso B S hS (chartToSpace B S hS X U) f).trans
    ((smallEtaleRingedToposHomEqTwoIso B S hS hg.symm).trans
      (smallEtaleRingedToposHom_compTwoIso B S hS g (chartToSpace B S hS Y V)).symm)

/-- The tautological section of `h_V` on the small étale site of `V`, pulled back along `g` and
carried through the commutative square of charts to a section of `p_small⁻¹ f_small⁻¹ h_V`, read on
the site of elements of `h_U` through the identification of Stacks 04M1. This is the section of
`f_small⁻¹h_V` over `U` that `g` determines. -/
noncomputable def chartRelocalizationSection :
    (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.obj
        ((chartLocalizationHom B S hS Y V).toToposHom.inverseImage.obj
          (CategoryTheory.Stacks.Topos.Localized.terminalFiber (SmallEtale.topology B S hS Y.1)
            (chartSheaf B S hS Y V))) ⟶
      (chartLocalizationHom B S hS X U).toToposHom.inverseImage.obj
        (((smallEtaleRingedTopos B S hS X).localizationMorphism
          (chartSheaf B S hS X U)).toToposHom.inverseImage.obj
            ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
              (chartSheaf B S hS Y V))) :=
  (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
      ((chartLocalizationHom B S hS Y V).toToposHom.inverseImage.map
          (RingedTopos.tautologicalSection (smallEtaleRingedTopos B S hS Y)
            (chartSheaf B S hS Y V)) ≫
        (chartLocalizationInverseImageIso B S hS Y V).inv.app (chartSheaf B S hS Y V)) ≫
    (chartSquareTwoIso B S hS f U V g hg).inverseImageIso.hom.app (chartSheaf B S hS Y V) ≫
    (chartLocalizationInverseImageIso B S hS X U).hom.app
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj (chartSheaf B S hS Y V))

/-- **The map `s : h_U ⟶ f_small⁻¹h_V` corresponding to `g`.** By the Yoneda lemma for the site
of elements of `h_U` (Stacks 0791) and the identification of Stacks 04M1, a map
`h_U ⟶ f_small⁻¹h_V` is a section of `f_small⁻¹h_V` over the chart `U`; this is the one
`AlgebraicGeometry.Space.chartRelocalizationSection` that `g` determines. -/
noncomputable def chartRelocalizationSheafMap :
    chartSheaf B S hS X U ⟶
      (smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj (chartSheaf B S hS Y V) :=
  (CategoryTheory.Stacks.Topos.Localized.homEquivFiberSheaf (chartSheaf B S hS X U).obj
      (SmallEtale.topology B S hS X.1) (chartSheaf B S hS X U).property
      (Over.mk (𝟙 (chartSheaf B S hS X U)))
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
        (chartSheaf B S hS Y V))).symm
    ((chartLocalizationHom_fullyFaithful B S hS X U).preimage
      ((((RingedTopos.isTerminalTautologicalSource (smallEtaleRingedTopos B S hS Y)
          (chartSheaf B S hS Y V)).isTerminalObj
          ((RingedToposHom.comp (chartLocalizationHom B S hS Y V)
            (smallEtaleRingedToposHom B S hS g)).toToposHom.inverseImage)).from _) ≫
        chartRelocalizationSection B S hS f U V g hg))

/-- **The defining property of `s`.** Pulled back along the identification of Stacks 04M1, the
section `τ ≫ j_U⁻¹(s)` of `j_U⁻¹ f_small⁻¹ h_V` is the section that `g` determines. -/
theorem chartRelocalizationSheafMap_spec :
    (chartLocalizationHom B S hS X U).toToposHom.inverseImage.map
        (RingedTopos.tautologicalSection (smallEtaleRingedTopos B S hS X) (chartSheaf B S hS X U) ≫
          ((smallEtaleRingedTopos B S hS X).localizationMorphism
            (chartSheaf B S hS X U)).toToposHom.inverseImage.map
              (chartRelocalizationSheafMap B S hS f U V g hg)) =
      (((RingedTopos.isTerminalTautologicalSource (smallEtaleRingedTopos B S hS Y)
          (chartSheaf B S hS Y V)).isTerminalObj
          ((RingedToposHom.comp (chartLocalizationHom B S hS Y V)
            (smallEtaleRingedToposHom B S hS g)).toToposHom.inverseImage)).from _) ≫
        chartRelocalizationSection B S hS f U V g hg := by
  have h := (CategoryTheory.Stacks.Topos.Localized.homEquivFiberSheaf (chartSheaf B S hS X U).obj
      (SmallEtale.topology B S hS X.1) (chartSheaf B S hS X U).property
      (Over.mk (𝟙 (chartSheaf B S hS X U)))
      ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
        (chartSheaf B S hS Y V))).apply_symm_apply
    ((chartLocalizationHom_fullyFaithful B S hS X U).preimage
      ((((RingedTopos.isTerminalTautologicalSource (smallEtaleRingedTopos B S hS Y)
          (chartSheaf B S hS Y V)).isTerminalObj
          ((RingedToposHom.comp (chartLocalizationHom B S hS Y V)
            (smallEtaleRingedToposHom B S hS g)).toToposHom.inverseImage)).from _) ≫
        chartRelocalizationSection B S hS f U V g hg))
  rw [CategoryTheory.Stacks.Topos.Localized.homEquivFiberSheaf_apply] at h
  exact (congrArg (chartLocalizationHom B S hS X U).toToposHom.inverseImage.map h).trans
    ((chartLocalizationHom_fullyFaithful B S hS X U).map_preimage _)

local notation "𝒰" => smallEtaleRingedTopos B S hS (chartSpace B S hS X U)
local notation "𝒱" => smallEtaleRingedTopos B S hS (chartSpace B S hS Y V)
local notation "𝒳" => smallEtaleRingedTopos B S hS X
local notation "𝒴" => smallEtaleRingedTopos B S hS Y
local notation "𝒳ᵤ" => RingedTopos.localizedRingedTopos (smallEtaleRingedTopos B S hS X)
  (chartSheaf B S hS X U)
local notation "𝒴ᵥ" => RingedTopos.localizedRingedTopos (smallEtaleRingedTopos B S hS Y)
  (chartSheaf B S hS Y V)

/-- The morphism of ringed topoi `(f_{small,s}, f_s♯) ∘ ι_U` from the small étale ringed topos of
`U` to the localization of the small étale ringed topos of `Y` at `h_V`: the identification of
Stacks 04M1 at `U` followed by the relocalized morphism of Stacks 04J8. -/
noncomputable abbrev chartRelocalizedHom : RingedToposHom 𝒰 𝒴ᵥ :=
  RingedToposHom.comp (X := 𝒰) (Y := 𝒳ᵤ) (Z := 𝒴ᵥ)
    ((smallEtaleRingedToposHom B S hS f).relocalized
      (chartRelocalizationSheafMap B S hS f U V g hg))
    (chartLocalizationHom B S hS X U)

/-- The morphism of ringed topoi `ι_V ∘ (g_small, g♯)` from the small étale ringed topos of `U` to
the localization of the small étale ringed topos of `Y` at `h_V`: the morphism of small étale
ringed topoi of `g` followed by the identification of Stacks 04M1 at `V`. -/
noncomputable abbrev chartMorphismHom : RingedToposHom 𝒰 𝒴ᵥ :=
  RingedToposHom.comp (X := 𝒰) (Y := 𝒱) (Z := 𝒴ᵥ) (chartLocalizationHom B S hS Y V)
    (smallEtaleRingedToposHom B S hS g)

/-- The 2-isomorphism of the two composites with the localization morphism `j_{h_V}`: the square of
Stacks 04J8 for `f_s`, the identifications of Stacks 04M1 lying over `X` and over `Y`, and the
commutative square of charts. -/
noncomputable def chartRelocalizationLocalizationTwoIso :
    RingedToposHom.TwoIso (A := 𝒰) (B := 𝒴)
      (RingedToposHom.comp (X := 𝒰) (Y := 𝒴ᵥ) (Z := 𝒴)
        (RingedTopos.localizationMorphism 𝒴 (chartSheaf B S hS Y V))
        (chartRelocalizedHom B S hS f U V g hg))
      (RingedToposHom.comp (X := 𝒰) (Y := 𝒴ᵥ) (Z := 𝒴)
        (RingedTopos.localizationMorphism 𝒴 (chartSheaf B S hS Y V))
        (chartMorphismHom B S hS U V g)) :=
  (RingedToposHom.TwoIso.associator (A := 𝒰) (B := 𝒳ᵤ) (C := 𝒴ᵥ) (D := 𝒴)
    (chartLocalizationHom B S hS X U)
    ((smallEtaleRingedToposHom B S hS f).relocalized
      (chartRelocalizationSheafMap B S hS f U V g hg))
    (RingedTopos.localizationMorphism 𝒴 (chartSheaf B S hS Y V))).trans <|
  (RingedToposHom.TwoIso.whiskerLeft (A := 𝒰) (B := 𝒳ᵤ) (C := 𝒴)
    (chartLocalizationHom B S hS X U)
    ((smallEtaleRingedToposHom B S hS f).relocalizedRingedSquare
      (chartRelocalizationSheafMap B S hS f U V g hg))).trans <|
  (RingedToposHom.TwoIso.associator (A := 𝒰) (B := 𝒳ᵤ) (C := 𝒳) (D := 𝒴)
    (chartLocalizationHom B S hS X U)
    (RingedTopos.localizationMorphism 𝒳 (chartSheaf B S hS X U))
    (smallEtaleRingedToposHom B S hS f)).symm.trans <|
  (RingedToposHom.TwoIso.whiskerRight (A := 𝒰) (B := 𝒳) (C := 𝒴)
    (chartLocalizationTwoIso B S hS X U) (smallEtaleRingedToposHom B S hS f)).trans <|
  (chartSquareTwoIso B S hS f U V g hg).trans <|
  (RingedToposHom.TwoIso.whiskerLeft (A := 𝒰) (B := 𝒱) (C := 𝒴)
    (smallEtaleRingedToposHom B S hS g)
    (chartLocalizationTwoIso B S hS Y V).symm).trans <|
  (RingedToposHom.TwoIso.associator (A := 𝒰) (B := 𝒱) (C := 𝒴ᵥ) (D := 𝒴)
    (smallEtaleRingedToposHom B S hS g) (chartLocalizationHom B S hS Y V)
    (RingedTopos.localizationMorphism 𝒴 (chartSheaf B S hS Y V))).symm

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The component at `h_V` of the conjugate of `chartRelocalizationLocalizationTwoIso`. -/
theorem chartRelocalizationLocalizationTwoIso_inverseImageIso_hom_app :
    (chartRelocalizationLocalizationTwoIso B S hS f U V g hg).inverseImageIso.hom.app
        (chartSheaf B S hS Y V) =
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
          ((chartLocalizationInverseImageIso B S hS Y V).inv.app (chartSheaf B S hS Y V)) ≫
        (chartSquareTwoIso B S hS f U V g hg).inverseImageIso.hom.app (chartSheaf B S hS Y V) ≫
        (chartLocalizationInverseImageIso B S hS X U).hom.app
          ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
            (chartSheaf B S hS Y V)) ≫
        (chartLocalizationHom B S hS X U).toToposHom.inverseImage.map
          ((RingedTopos.relocalizationMorphismOfTopoi 𝒳
            (chartRelocalizationSheafMap B S hS f U V g hg)).inverseImage.map
            (((smallEtaleRingedToposHom B S hS f).inverseImageCompLocalizationIso
              (chartSheaf B S hS Y V)).hom.app (chartSheaf B S hS Y V))) := by
  simp only [chartRelocalizationLocalizationTwoIso, RingedToposHom.TwoIso.inverseImageIso_trans,
    RingedToposHom.TwoIso.inverseImageIso_symm, RingedToposHom.TwoIso.inverseImageIso_associator,
    RingedToposHom.TwoIso.inverseImageIso_whiskerLeft,
    RingedToposHom.TwoIso.inverseImageIso_whiskerRight, chartLocalizationTwoIso,
    RingedTopos.compLocalizationMorphismTwoIsoOfInverseImageIso_inverseImageIso,
    RingedToposHom.relocalizedRingedSquare, RingedToposHom.TwoIso.inverseImageIso_ofInverseImageIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    RingedToposHom.relocalizedInverseImageSquare_hom_app]
  exact (Category.comp_id _).trans ((congrArg (· ≫ _) ((Category.comp_id _).trans
    (congrArg (· ≫ _) (congrArg (· ≫ _) (Category.id_comp _))))).trans
    (by simp only [Category.assoc]; rfl))

/-- The tautological section pulled back along `ι_V ∘ g_small`, followed by the comparisons of the
commutative square of charts, is the section
`AlgebraicGeometry.Space.chartRelocalizationSection`. -/
theorem chartMorphismHom_map_tautologicalSection_comp :
    (chartMorphismHom B S hS U V g).toToposHom.inverseImage.map
        (RingedTopos.tautologicalSection 𝒴 (chartSheaf B S hS Y V)) ≫
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
          ((chartLocalizationInverseImageIso B S hS Y V).inv.app (chartSheaf B S hS Y V)) ≫
        (chartSquareTwoIso B S hS f U V g hg).inverseImageIso.hom.app (chartSheaf B S hS Y V) ≫
          (chartLocalizationInverseImageIso B S hS X U).hom.app
            ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
              (chartSheaf B S hS Y V)) =
      chartRelocalizationSection B S hS f U V g hg := by
  rw [chartRelocalizationSection, Functor.map_comp, Category.assoc]
  rfl

/-- A composite through a terminal object `T` of maps `T ⟶ P ⟶ Q ⟶ T` may be dropped, in the
bracketing in which it occurs below. -/
private theorem terminal_reassoc {𝒞 : Type*} [Category* 𝒞] {T P Q A₁ A₂ A₃ A₄ A₅ : 𝒞}
    (hT : IsTerminal T) (x : T ⟶ P) (y : P ⟶ Q) (z : Q ⟶ T) (h₁ : T ⟶ A₁) (h₂ : A₁ ⟶ A₂)
    (h₃ : A₂ ⟶ A₃) (h₄ : A₃ ⟶ A₄) (e : A₄ ⟶ A₅) :
    h₁ ≫ h₂ ≫ h₃ ≫ h₄ ≫ e = x ≫ (y ≫ z ≫ h₁ ≫ h₂ ≫ h₃ ≫ h₄) ≫ e := by
  have hxyz : x ≫ y ≫ z = 𝟙 T := hT.hom_ext _ _
  simp only [Category.assoc, reassoc_of% hxyz]

/-- **The 2-isomorphism over the localization carries the tautological section.** This is where
the choice of `s` enters: Stacks 04IF's localized morphism and Stacks 04J4's relocalization pull
the tautological section of `h_V` back to `τ_U ≫ j_U⁻¹(s)`, and `s` was defined so that this is
the section that `g` determines. -/
theorem chartRelocalization_carriesTautologicalSection :
    RingedTopos.CarriesTautologicalSection (chartRelocalizedHom B S hS f U V g hg)
      (chartMorphismHom B S hS U V g)
      (chartRelocalizationLocalizationTwoIso B S hS f U V g hg) := by
  unfold RingedTopos.CarriesTautologicalSection
  rw [chartRelocalizationLocalizationTwoIso_inverseImageIso_hom_app]
  have spec := chartRelocalizationSheafMap_spec B S hS f U V g hg
  have hR := congrArg (chartLocalizationHom B S hS X U).toToposHom.inverseImage.map
    (RingedToposHom.relocalized_map_tautologicalSection (smallEtaleRingedToposHom B S hS f)
      (chartRelocalizationSheafMap B S hS f U V g hg))
  replace hR := hR.trans (((chartLocalizationHom B S hS X U).toToposHom.inverseImage.map_comp _
    _).trans (congrArg (· ≫ _) (((chartLocalizationHom B S hS X U).toToposHom.inverseImage.map_comp
      _ _).trans (congrArg (_ ≫ ·) (spec.trans (congrArg (_ ≫ ·)
        (chartMorphismHom_map_tautologicalSection_comp B S hS f U V g hg).symm))))))
  refine Eq.trans ?_ (congrArg (_ ≫ ·) hR).symm
  exact terminal_reassoc
    ((RingedTopos.isTerminalTautologicalSource 𝒴 (chartSheaf B S hS Y V)).isTerminalObj
    (chartMorphismHom B S hS U V g).toToposHom.inverseImage) _ _ _ _ _ _ _ _

/-- **Stacks 04M5.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, let `U ⟶ X` and
`V ⟶ Y` be étale morphisms from schemes (objects of the small étale sites of `X` and `Y`) and let
`g : U ⟶ V` be a morphism of schemes with `q ∘ g = f ∘ p`. Via the identifications of Stacks 04M1
of the small étale ringed topoi of `U` and `V` with the localizations of those of `X` at `h_U` and
of `Y` at `h_V` (`AlgebraicGeometry.Space.chartLocalizationHom`, an equivalence of topoi), the
morphism of small étale ringed topoi `(g_small, g♯)` is 2-isomorphic to the morphism
`(f_{small,s}, f_s♯)` of Stacks 04J8 built from `(f_small, f♯)` and the map
`s : h_U ⟶ f_small⁻¹h_V` corresponding to `g`
(`AlgebraicGeometry.Space.chartRelocalizationSheafMap`). -/
@[stacks 04M5 "via the identifications of 04M1 at U and V, the morphism (g_small, g^sharp) is
  2-isomorphic to the morphism (f_{small,s}, f_s^sharp) of 04J8 for the map s : h_U -> f^{-1}h_V
  corresponding to g"]
noncomputable def chartRelocalizedTwoIso :
    RingedToposHom.TwoIso (A := 𝒰) (B := 𝒴ᵥ) (chartRelocalizedHom B S hS f U V g hg)
      (chartMorphismHom B S hS U V g) :=
  RingedTopos.localizationTwoIso (chartRelocalization_carriesTautologicalSection B S hS f U V g hg)

end AlgebraicGeometry.Space

end

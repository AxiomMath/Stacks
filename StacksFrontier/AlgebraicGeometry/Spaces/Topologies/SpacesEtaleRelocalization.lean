module

public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.RelocalizedMorphism
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RelocalizationDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# Étale localization is compatible with morphisms

Let `S` be a scheme and let

```
  U --g--> V
  |        |
  p        q
  v        v
  X --f--> Y
```

be a commutative diagram of algebraic spaces over `S` with `p` and `q` étale. Via the
identifications of Stacks 04LZ of the ringed spaces-étale site of `U` with the localization of
that of `X` at `U`, and likewise for `V` over `Y`, the morphism of ringed topoi
`(g_{spaces,étale}, g^♯)` is 2-isomorphic to the morphism `(f_{spaces,étale,c}, f_c^♯)` that
Stacks 04J1 builds from the morphism of ringed sites `(f_{spaces,étale}, f^♯)` and the map
`c : U ⟶ V ×_Y X` corresponding to `g`. The map `c` is characterised by its composite with the
cartesian projection `V ×_Y X ⟶ V` being `g`, and this property forces the square to commute.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleRingedSite`: the ringed site
  `(X_{spaces,étale}, 𝒪_X)`, in the structure that carries morphisms of ringed *sites*.
* `AlgebraicGeometry.Space.spacesEtaleRingedSiteHom`: the morphism of ringed sites
  `(f_{spaces,étale}, f^♯)` attached to a morphism of algebraic spaces.
* `AlgebraicGeometry.Space.spacesEtaleLocalizationRingedSiteHom`: the identification of
  Stacks 04LZ, as a morphism of ringed sites.
* `AlgebraicGeometry.Space.spacesEtaleComparisonMap`: the map `c : U ⟶ V ×_Y X` corresponding
  to `g`.
* `AlgebraicGeometry.Space.relocalizationComparisonArrow` and
  `AlgebraicGeometry.Space.relocalizedSiteIso`: the comparison of the two functors of sites.

## Main results

* `AlgebraicGeometry.Space.relocalizationComparisonArrow_isPullback`: for `T` étale over `V`,
  the base change of `T` along `g`, read as an algebraic space over `U`, is the fibre product of
  the base change of `T` along `f` with `U` over `V ×_Y X`.
* `AlgebraicGeometry.Space.relocalizedUnderlyingIso`: the induced isomorphism of the two
  direct images.
* `AlgebraicGeometry.Space.spacesEtaleRelocalizedTwoIso`: the 2-isomorphism of morphisms of
  ringed topoi: the square of ringed topoi whose vertical arrows are the two identifications of
  Stacks 04LZ commutes up to an invertible 2-morphism.

## References

* [Stacks Project, Tag 04LY](https://stacks.math.columbia.edu/tag/04LY)
* [Stacks Project, Tag 04LZ](https://stacks.math.columbia.edu/tag/04LZ)
* [Stacks Project, Tag 04J1](https://stacks.math.columbia.edu/tag/04J1)
* [Stacks Project, Tag 04M4](https://stacks.math.columbia.edu/tag/04M4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₁ v₁ u₂ v₂

/-! ### The ringed spaces-étale site and its functoriality -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The spaces-étale site of an algebraic space has all finite limits. -/
instance hasFiniteLimits_spacesEtale (X : AlgebraicSpaces B S hS) :
    HasFiniteLimits (SpacesEtale B S hS X) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

variable {X Y U V : AlgebraicSpaces B S hS}

/-- The morphism of ringed spaces-étale sites of Stacks 03G8,
`(f_{spaces,étale}, f^♯) : (X_{spaces,étale}, 𝒪_X) ⟶ (Y_{spaces,étale}, 𝒪_Y)`, attached to a
morphism `f : X ⟶ Y` of algebraic spaces: the underlying morphism of sites is the cartesian
base change of Stacks 03G2, and the structure map sends a regular function on an algebraic
space `V'` étale over `Y` to its pullback along the cartesian projection `V' ×_Y X ⟶ V'`. -/
noncomputable def spacesEtaleRingedSiteHom (f : X ⟶ Y) :
    RingedSite.Hom (spacesEtaleRingedSite B S hS X) (spacesEtaleRingedSite B S hS Y) where
  u := (spacesBaseChange B S hS f).functor
  isMorphismOfSites := spacesBaseChange_isMorphismOfSites B S hS f
  fsharp := ⟨Functor.whiskerRight (NatTrans.op (spacesBaseChange B S hS f).projection)
    (globalFunctionsPresheaf B S hS)⟩

/-- The functor of sites underlying `(f_{spaces,étale}, f^♯)` is the base-change functor. -/
@[simp]
theorem spacesEtaleRingedSiteHom_u (f : X ⟶ Y) :
    (spacesEtaleRingedSiteHom B S hS f).u = (spacesBaseChange B S hS f).functor := rfl

attribute [local instance] spacesEtaleLocalization_isContinuous

/-- The localization equivalence of Stacks 04LY is a morphism of sites. -/
theorem spacesEtaleLocalization_isMorphismOfSites (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    (spacesEtaleLocalization B S hS p hp).functor.IsMorphismOfSites
      (SpacesEtale.topology B S hS U)
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp)) := by
  have : (spacesEtaleLocalization B S hS p hp).functor.IsRightAdjoint :=
    ⟨_, ⟨(spacesEtaleLocalization B S hS p hp).symm.toAdjunction⟩⟩
  exact Functor.isMorphismOfSites_of_representablyFlat _ _ _

/-- The identification of Stacks 04LZ of the ringed spaces-étale site of an algebraic space `U`
étale over `X` with the localization of the ringed spaces-étale site of `X` at `U`, as a
morphism of ringed *sites*: the underlying functor is the equivalence of Stacks 04LY and the
structure map is the comparison of structure sheaves of Stacks 04LZ. -/
noncomputable def spacesEtaleLocalizationRingedSiteHom (p : U ⟶ X)
    (hp : IsEtale B S hS p.hom) :
    RingedSite.Hom ((spacesEtaleRingedSite B S hS X).over (etaleObject B S hS p hp))
      (spacesEtaleRingedSite B S hS U) where
  u := (spacesEtaleLocalization B S hS p hp).functor
  isMorphismOfSites := spacesEtaleLocalization_isMorphismOfSites B S hS p hp
  fsharp := eqToHom (spacesEtaleLocalization_structureSheaf B S hS p hp).symm

/-- The functor of sites underlying the identification of Stacks 04LZ is the localization
equivalence of Stacks 04LY. -/
@[simp]
theorem spacesEtaleLocalizationRingedSiteHom_u (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    (spacesEtaleLocalizationRingedSiteHom B S hS p hp).u =
      (spacesEtaleLocalization B S hS p hp).functor := rfl

/-- The identification of Stacks 04LZ has the same underlying data as the morphism of ringed
topoi recorded at Stacks 04LZ. -/
theorem spacesEtaleLocalizationRingedSiteHom_fsharp (p : U ⟶ X) (hp : IsEtale B S hS p.hom) :
    (spacesEtaleLocalizationRingedSiteHom B S hS p hp).fsharp =
      (spacesEtaleLocalizationRingedHom B S hS p hp).fSharp := rfl

/-! ### The cartesian comparison square -/

/-- Transporting a cartesian square along equalities of its left and bottom edges. -/
private theorem isPullback_of_eq {C : Type u₁} [Category.{v₁} C] {P A A' Z : C}
    {fst fst' : P ⟶ A} {snd : P ⟶ A'} {top : A ⟶ Z} {bot bot' : A' ⟶ Z}
    (h : IsPullback fst snd top bot) (e₁ : fst' = fst) (e₂ : bot' = bot) :
    IsPullback fst' snd top bot' :=
  e₁ ▸ e₂ ▸ h

/-- A three-fold composite, read through a presheaf. -/
private theorem map_op_comp₃ {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
    (H : Cᵒᵖ ⥤ A) {X₀ X₁ X₂ X₃ : C} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (d : X₂ ⟶ X₃)
    (e : X₀ ⟶ X₃) (h : (a ≫ b) ≫ d = e) :
    H.map d.op ≫ H.map b.op ≫ H.map a.op = H.map e.op := by
  subst h
  simp only [op_comp, Functor.map_comp, Category.assoc]

/-- Two arrows of the spaces-étale site are equal once their underlying arrows of algebraic
spaces over the base are. -/
private theorem spacesEtale_hom_ext {Z : AlgebraicSpaces B S hS} {M N : SpacesEtale B S hS Z}
    {s t : M ⟶ N} (e : s.hom.left = t.hom.left) : s = t :=
  (SpacesEtale.toSpaces B S hS Z).map_injective e

/-- A square of the spaces-étale site of an algebraic space which becomes cartesian on the
underlying algebraic spaces is cartesian. -/
theorem isPullback_of_toSpaces {Z : AlgebraicSpaces B S hS}
    {P A D E : SpacesEtale B S hS Z}
    {r₁ : P ⟶ A} {r₂ : P ⟶ D} {a : A ⟶ E} {b : D ⟶ E}
    (h : IsPullback r₁.hom.left r₂.hom.left a.hom.left b.hom.left) :
    IsPullback r₁ r₂ a b := by
  have w : r₁ ≫ a = r₂ ≫ b := spacesEtale_hom_ext B S hS h.w
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _ (fun t => ?_) ?_ ?_ ?_⟩⟩
  · exact ObjectProperty.homMk (Over.homMk
      (h.lift t.fst.hom.left t.snd.hom.left
        (congrArg (fun k => k.hom.left) t.condition)) (by
          rw [← Over.w r₁.hom, ← Category.assoc, h.lift_fst]
          exact Over.w t.fst.hom))
  · exact fun t => spacesEtale_hom_ext B S hS (h.lift_fst _ _ _)
  · exact fun t => spacesEtale_hom_ext B S hS (h.lift_snd _ _ _)
  · intro t m hm₁ hm₂
    refine spacesEtale_hom_ext B S hS (h.hom_ext ?_ ?_)
    · exact (congrArg (fun k => k.hom.left) hm₁).trans (h.lift_fst _ _ _).symm
    · exact (congrArg (fun k => k.hom.left) hm₂).trans (h.lift_snd _ _ _).symm

/-- Naturality of the cartesian projection of Stacks 03G2 is itself a cartesian square: for an
arrow `a : A ⟶ D` of the spaces-étale site of `Y`, the square with sides the two projections,
`a` and the base change of `a` is a fibre product. -/
theorem spacesBaseChange_naturality_isPullback (f : X ⟶ Y)
    {A D : SpacesEtale B S hS Y} (a : A ⟶ D) :
    IsPullback ((spacesBaseChange B S hS f).projection.app A)
      (((spacesBaseChange B S hS f).functor.map a).hom.left)
      a.hom.left ((spacesBaseChange B S hS f).projection.app D) := by
  have h : IsPullback ((spacesBaseChange B S hS f).projection.app A)
      (((spacesBaseChange B S hS f).functor.map a).hom.left ≫
        ((spacesBaseChange B S hS f).functor.obj D).obj.hom)
      (a.hom.left ≫ D.obj.hom) f := by
    rw [Over.w, Over.w]
    exact (spacesBaseChange B S hS f).isPullback A
  exact h.of_bot ((spacesBaseChange B S hS f).projection.naturality a).symm
    ((spacesBaseChange B S hS f).isPullback D)

variable (f : X ⟶ Y) (g : U ⟶ V) (p : U ⟶ X) (hp : IsEtale B S hS p.hom)
    (q : V ⟶ Y) (hq : IsEtale B S hS q.hom)
    (c : etaleObject B S hS p hp ⟶
      (spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq))

/-- The arrow of algebraic spaces `U ⟶ V ×_Y X` underlying an arrow `c` of the spaces-étale
site of `X` from `U` to the base change of `V`. -/
noncomputable abbrev comparisonSpaceHom :
    U ⟶ ((spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq)).obj.left :=
  (SpacesEtale.toSpaces B S hS X).map c

/-- The map `c : U ⟶ V ×_Y X` corresponding to `g`, as an arrow of the spaces-étale site of
`X` from `U` to the cartesian base change of `V` along `f`. -/
@[stacks 04M4 "the map `c : U ⟶ V ×_Y X` corresponding to `g`, and nothing else"]
noncomputable def spacesEtaleComparisonMap (hsq : g ≫ q = p ≫ f) :
    etaleObject B S hS p hp ⟶
      (spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq) :=
  ObjectProperty.homMk (Over.homMk
    (((spacesBaseChange B S hS f).isPullback (etaleObject B S hS q hq)).lift g p hsq)
    (((spacesBaseChange B S hS f).isPullback (etaleObject B S hS q hq)).lift_snd g p hsq))

/-- The map `c` corresponding to `g` is characterised by the property that its composite with
the cartesian projection `V ×_Y X ⟶ V` is `g`. -/
theorem spacesEtaleComparisonMap_projection (hsq : g ≫ q = p ≫ f) :
    comparisonSpaceHom B S hS f p hp q hq
          (spacesEtaleComparisonMap B S hS f g p hp q hq hsq) ≫
        (spacesBaseChange B S hS f).projection.app (etaleObject B S hS q hq) = g :=
  ((spacesBaseChange B S hS f).isPullback (etaleObject B S hS q hq)).lift_fst g p hsq

variable (hc : comparisonSpaceHom B S hS f p hp q hq c ≫
  (spacesBaseChange B S hS f).projection.app (etaleObject B S hS q hq) = g)

include hc

/-- If the composite of `c` with the cartesian projection `V ×_Y X ⟶ V` is `g`, then the square
commutes: `g ≫ q = p ≫ f`. -/
theorem comparisonSpaceHom_square : g ≫ q = p ≫ f :=
  (congrArg (fun z => z ≫ q) hc.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => comparisonSpaceHom B S hS f p hp q hq c ≫ z)
          ((spacesBaseChange B S hS f).isPullback (etaleObject B S hS q hq)).w).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ f) (Over.w c.hom)))))

/-- The square used to construct the comparison arrow commutes. -/
theorem relocalizationComparison_w (T : SpacesEtale B S hS V) :
    (spacesBaseChange B S hS g).projection.app T ≫ T.obj.hom =
      ((spacesBaseChange B S hS g).functor.obj T).obj.hom ≫
        (comparisonSpaceHom B S hS f p hp q hq c ≫
          (spacesBaseChange B S hS f).projection.app (etaleObject B S hS q hq)) := by
  rw [hc]
  exact ((spacesBaseChange B S hS g).isPullback T).w

/-- For an algebraic space `T` étale over `V`, the canonical arrow comparing the base change
of `T` along `g`, read over `U`, with the base change along `f` of `T` read over `Y`. -/
noncomputable def relocalizationComparisonArrow (T : SpacesEtale B S hS V) :
    (((spacesEtaleLocalization B S hS p hp).functor.obj
        ((spacesBaseChange B S hS g).functor.obj T)).left) ⟶
      (spacesBaseChange B S hS f).functor.obj
        (((spacesEtaleLocalization B S hS q hq).functor.obj T).left) :=
  ObjectProperty.homMk (Over.homMk
    ((spacesBaseChange_naturality_isPullback B S hS f
        (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom)).lift
      ((spacesBaseChange B S hS g).projection.app T)
      (((spacesBaseChange B S hS g).functor.obj T).obj.hom ≫
        comparisonSpaceHom B S hS f p hp q hq c)
      ((relocalizationComparison_w B S hS f g p hp q hq c hc T).trans
        (Category.assoc _ _ _).symm))
    (by
      change _ ≫ ((spacesBaseChange B S hS f).functor.obj
          (((spacesEtaleLocalization B S hS q hq).functor.obj T).left)).obj.hom =
        ((spacesBaseChange B S hS g).functor.obj T).obj.hom ≫ p
      have hcX : comparisonSpaceHom B S hS f p hp q hq c ≫
          ((spacesBaseChange B S hS f).functor.obj
            (etaleObject B S hS q hq)).obj.hom = p := Over.w c.hom
      have hls := (spacesBaseChange_naturality_isPullback B S hS f
        (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom)).lift_snd
        ((spacesBaseChange B S hS g).projection.app T)
        (((spacesBaseChange B S hS g).functor.obj T).obj.hom ≫
          comparisonSpaceHom B S hS f p hp q hq c)
        ((relocalizationComparison_w B S hS f g p hp q hq c hc T).trans
          (Category.assoc _ _ _).symm)
      have hOw := Over.w ((spacesBaseChange B S hS f).functor.map
        (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom)).hom
      have key := congrArg (fun z => z ≫ ((spacesBaseChange B S hS f).functor.obj
        (etaleObject B S hS q hq)).obj.hom) hls
      simp only [Category.assoc] at key
      rw [← hOw]
      exact key.trans (congrArg (fun z =>
        ((spacesBaseChange B S hS g).functor.obj T).obj.hom ≫ z) hcX)))

/-- The comparison arrow is compatible with the cartesian projections. -/
theorem relocalizationComparisonArrow_projection (T : SpacesEtale B S hS V) :
    (relocalizationComparisonArrow B S hS f g p hp q hq c hc T).hom.left ≫
        (spacesBaseChange B S hS f).projection.app
          (((spacesEtaleLocalization B S hS q hq).functor.obj T).left) =
      (spacesBaseChange B S hS g).projection.app T :=
  (spacesBaseChange_naturality_isPullback B S hS f
    (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom)).lift_fst _ _ _

/-- The comparison arrow is compatible with the slice arrows to `U` and to `V ×_Y X`. -/
theorem relocalizationComparisonArrow_comp (T : SpacesEtale B S hS V) :
    relocalizationComparisonArrow B S hS f g p hp q hq c hc T ≫
        (spacesBaseChange B S hS f).functor.map
          (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom) =
      ((spacesEtaleLocalization B S hS p hp).functor.obj
        ((spacesBaseChange B S hS g).functor.obj T)).hom ≫ c :=
  spacesEtale_hom_ext B S hS
    ((spacesBaseChange_naturality_isPullback B S hS f
      (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom)).lift_snd _ _ _)

/-- The comparison arrow exhibits the base change of `T` along `g`, read over `U`, as the
fibre product of the base change of `T` along `f` with `U` over `V ×_Y X`. -/
theorem relocalizationComparisonArrow_isPullback (T : SpacesEtale B S hS V) :
    IsPullback (relocalizationComparisonArrow B S hS f g p hp q hq c hc T)
      (((spacesEtaleLocalization B S hS p hp).functor.obj
        ((spacesBaseChange B S hS g).functor.obj T)).hom)
      ((spacesBaseChange B S hS f).functor.map
        (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom)) c := by
  apply isPullback_of_toSpaces B S hS
  have h := isPullback_of_eq ((spacesBaseChange B S hS g).isPullback T)
    (relocalizationComparisonArrow_projection B S hS f g p hp q hq c hc T) hc
  exact h.of_right (congrArg (fun k => k.hom.left)
    (relocalizationComparisonArrow_comp B S hS f g p hp q hq c hc T))
    (spacesBaseChange_naturality_isPullback B S hS f
      (((spacesEtaleLocalization B S hS q hq).functor.obj T).hom))

/-- The comparison arrow is natural in `T`. -/
theorem relocalizationComparisonArrow_naturality {T T' : SpacesEtale B S hS V} (a : T ⟶ T') :
    ((spacesEtaleLocalization B S hS p hp).functor.map
          ((spacesBaseChange B S hS g).functor.map a)).left ≫
        relocalizationComparisonArrow B S hS f g p hp q hq c hc T' =
      relocalizationComparisonArrow B S hS f g p hp q hq c hc T ≫
        (spacesBaseChange B S hS f).functor.map
          (((spacesEtaleLocalization B S hS q hq).functor.map a).left) := by
  refine spacesEtale_hom_ext B S hS
    (((spacesBaseChange B S hS f).isPullback
      (((spacesEtaleLocalization B S hS q hq).functor.obj T').left)).hom_ext ?_ ?_)
  · have h₁ := relocalizationComparisonArrow_projection B S hS f g p hp q hq c hc T'
    have h₂ := relocalizationComparisonArrow_projection B S hS f g p hp q hq c hc T
    have h₃ : (((spacesBaseChange B S hS f).functor.map
            (((spacesEtaleLocalization B S hS q hq).functor.map a).left)).hom.left) ≫
          (spacesBaseChange B S hS f).projection.app
            (((spacesEtaleLocalization B S hS q hq).functor.obj T').left) =
        (spacesBaseChange B S hS f).projection.app
            (((spacesEtaleLocalization B S hS q hq).functor.obj T).left) ≫
          (((spacesEtaleLocalization B S hS q hq).functor.map a).left).hom.left :=
      (spacesBaseChange B S hS f).projection.naturality _
    have h₄ : (((spacesBaseChange B S hS g).functor.map a).hom.left) ≫
          (spacesBaseChange B S hS g).projection.app T' =
        (spacesBaseChange B S hS g).projection.app T ≫ a.hom.left :=
      (spacesBaseChange B S hS g).projection.naturality a
    show (((spacesBaseChange B S hS g).functor.map a).hom.left ≫
        (relocalizationComparisonArrow B S hS f g p hp q hq c hc T').hom.left) ≫ _ =
      ((relocalizationComparisonArrow B S hS f g p hp q hq c hc T).hom.left ≫
        ((spacesBaseChange B S hS f).functor.map
          (((spacesEtaleLocalization B S hS q hq).functor.map a).left)).hom.left) ≫ _
    exact (Category.assoc _ _ _).trans
      (((congrArg (fun z => ((spacesBaseChange B S hS g).functor.map a).hom.left ≫ z) h₁).trans
        (h₄.trans
          ((congrArg (fun z => z ≫ ((((spacesEtaleLocalization B S hS q hq).functor.map
              a).left).hom.left)) h₂.symm).trans
            ((Category.assoc _ _ _).trans
              (congrArg (fun z =>
                (relocalizationComparisonArrow B S hS f g p hp q hq c hc T).hom.left ≫ z)
                h₃.symm))))).trans (Category.assoc _ _ _).symm)
  · exact (Over.w (((spacesEtaleLocalization B S hS p hp).functor.map
      ((spacesBaseChange B S hS g).functor.map a)).left ≫
        relocalizationComparisonArrow B S hS f g p hp q hq c hc T').hom).trans
      (Over.w (relocalizationComparisonArrow B S hS f g p hp q hq c hc T ≫
        (spacesBaseChange B S hS f).functor.map
          (((spacesEtaleLocalization B S hS q hq).functor.map a).left)).hom).symm

/-- On the underlying sites: the functor of sites of `(g_{spaces,étale}, g^♯)` followed by the
identification of Stacks 04LZ for `U ⟶ X` is canonically isomorphic to the identification for
`V ⟶ Y` followed by the functor of sites of the relocalization of `f_{spaces,étale}` along `c`. -/
noncomputable def relocalizedSiteIso :
    (spacesBaseChange B S hS g).functor ⋙ (spacesEtaleLocalization B S hS p hp).functor ≅
      (spacesEtaleLocalization B S hS q hq).functor ⋙
        Over.post (spacesBaseChange B S hS f).functor ⋙ Over.pullback c := by
  refine NatIso.ofComponents (fun T => Over.isoMk
    (relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc T).isoPullback
    ((relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc
      T).isoPullback_hom_snd)) ?_
  intro T T' a
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)
  · simp only [Functor.comp_map, Over.comp_left, Category.assoc, Over.pullback_map_left,
      pullback.lift_fst]
    exact ((congrArg (fun z => ((spacesEtaleLocalization B S hS p hp).functor.map
        ((spacesBaseChange B S hS g).functor.map a)).left ≫ z)
        (relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc
          T').isoPullback_hom_fst).trans
      ((relocalizationComparisonArrow_naturality B S hS f g p hp q hq c hc a).trans
        ((congrArg (fun z => z ≫ (((Over.post (spacesBaseChange B S hS f).functor).map
            ((spacesEtaleLocalization B S hS q hq).functor.map a)).left))
          (relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc
            T).isoPullback_hom_fst.symm).trans (Category.assoc _ _ _))))
  · simp only [Functor.comp_map, Over.comp_left, Category.assoc, Over.pullback_map_left,
      pullback.lift_snd]
    exact ((congrArg (fun z => ((spacesEtaleLocalization B S hS p hp).functor.map
        ((spacesBaseChange B S hS g).functor.map a)).left ≫ z)
        (relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc
          T').isoPullback_hom_snd).trans
      (Over.w ((spacesEtaleLocalization B S hS p hp).functor.map
        ((spacesBaseChange B S hS g).functor.map a)))).trans
      (relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc
        T).isoPullback_hom_snd.symm

/-- On the underlying morphisms of topoi: the direct image of `(g_{spaces,étale}, g^♯)` after
the identification of Stacks 04LZ for `U ⟶ X` agrees with the direct image of the relocalization
of `f_{spaces,étale}` along `c` after the identification for `V ⟶ Y`. -/
noncomputable def relocalizedUnderlyingIso :
    (AlgebraicGeometry.RingedToposHom.comp
        (spacesEtaleLocalizationRingedSiteHom B S hS q hq).ringedToposHom
        ((spacesEtaleRingedSiteHom B S hS f).relocalized c)).toToposHom.pushforward ≅
      (AlgebraicGeometry.RingedToposHom.comp
          (spacesEtaleRingedSiteHom B S hS g).ringedToposHom
          (spacesEtaleLocalizationRingedSiteHom B S hS p
            hp).ringedToposHom).toToposHom.pushforward := by
  haveI : (spacesEtaleLocalization B S hS p hp).functor.IsContinuous
      (SpacesEtale.topology B S hS U)
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp)) :=
    spacesEtaleLocalization_isContinuous B S hS p hp
  haveI : (spacesEtaleLocalization B S hS q hq).functor.IsContinuous
      (SpacesEtale.topology B S hS V)
      ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq)) :=
    spacesEtaleLocalization_isContinuous B S hS q hq
  haveI : (Over.pullback c).IsContinuous
      ((SpacesEtale.topology B S hS X).over
        ((spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq)))
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp)) :=
    (StacksRelocalization.isMorphismOfSites_overPullback
      (SpacesEtale.topology B S hS X) c).isContinuous
  haveI : (Over.post (spacesBaseChange B S hS f).functor).IsContinuous
      ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq))
      ((SpacesEtale.topology B S hS X).over
        ((spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq))) :=
    (Functor.isMorphismOfSites_overPost_of_isMorphismOfSites
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
      (spacesBaseChange B S hS f).functor (etaleObject B S hS q hq)
      (spacesBaseChange_isMorphismOfSites B S hS f)).isContinuous
  haveI : (Over.post (spacesBaseChange B S hS f).functor ⋙ Over.pullback c).IsContinuous
      ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq))
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp)) :=
    Functor.isContinuous_comp (Over.post (spacesBaseChange B S hS f).functor)
      (Over.pullback c) ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq))
      ((SpacesEtale.topology B S hS X).over
        ((spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq)))
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp))
  haveI : ((spacesEtaleLocalization B S hS q hq).functor ⋙
      Over.post (spacesBaseChange B S hS f).functor ⋙ Over.pullback c).IsContinuous
      (SpacesEtale.topology B S hS V)
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp)) :=
    Functor.isContinuous_comp (spacesEtaleLocalization B S hS q hq).functor
      (Over.post (spacesBaseChange B S hS f).functor ⋙ Over.pullback c)
      (SpacesEtale.topology B S hS V)
      ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq))
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp))
  haveI : ((spacesBaseChange B S hS g).functor ⋙
      (spacesEtaleLocalization B S hS p hp).functor).IsContinuous
      (SpacesEtale.topology B S hS V)
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp)) :=
    Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
      (spacesEtaleLocalization B S hS p hp).functor
      (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U)
      ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp))
  refine (Functor.isoWhiskerRight (Functor.isoWhiskerRight
    ((spacesEtaleRingedSite B S hS X).relocalizationDirectImageIso c)
    ((Over.post (spacesBaseChange B S hS f).functor).sheafPushforwardContinuous
      (Type (u + 1)) ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq))
      ((SpacesEtale.topology B S hS X).over
        ((spacesBaseChange B S hS f).functor.obj (etaleObject B S hS q hq)))))
    ((spacesEtaleLocalization B S hS q hq).functor.sheafPushforwardContinuous
      (Type (u + 1)) (SpacesEtale.topology B S hS V)
      ((SpacesEtale.topology B S hS Y).over (etaleObject B S hS q hq)))) ≪≫ ?_
  exact Functor.sheafPushforwardContinuousIso
    (relocalizedSiteIso B S hS f g p hp q hq c hc).symm (Type (u + 1))
    (SpacesEtale.topology B S hS V)
    ((SpacesEtale.topology B S hS X).over (etaleObject B S hS p hp))

/-- The comparison isomorphism of sites is compatible with the cartesian projections: its
component at `T` followed by the projection of the fibre product and by the cartesian
projection of `f` is the cartesian projection of `g`. -/
theorem relocalizedSiteIso_projection (T : SpacesEtale B S hS V) :
    ((((relocalizedSiteIso B S hS f g p hp q hq c hc).hom.app T).left ≫
        pullback.fst ((Over.post (spacesBaseChange B S hS f).functor).obj
          ((spacesEtaleLocalization B S hS q hq).functor.obj T)).hom c).hom.left ≫
      (spacesBaseChange B S hS f).projection.app
        (((spacesEtaleLocalization B S hS q hq).functor.obj T).left)) =
      (spacesBaseChange B S hS g).projection.app T :=
  (congrArg (fun k => k.hom.left ≫ (spacesBaseChange B S hS f).projection.app
      (((spacesEtaleLocalization B S hS q hq).functor.obj T).left))
    (relocalizationComparisonArrow_isPullback B S hS f g p hp q hq c hc
      T).isoPullback_hom_fst).trans
    (relocalizationComparisonArrow_projection B S hS f g p hp q hq c hc T)

/-- The compatibility of the comparison isomorphism with the cartesian projections, read through
an arbitrary presheaf on the algebraic spaces over the base. -/
theorem relocalizedSiteIso_map_projection {A : Type u₁} [Category.{v₁} A]
    (H : (AlgebraicSpaces B S hS)ᵒᵖ ⥤ A) (T : SpacesEtale B S hS V) :
    H.map ((spacesBaseChange B S hS f).projection.app
          (((spacesEtaleLocalization B S hS q hq).functor.obj T).left)).op ≫
        H.map ((pullback.fst ((Over.post (spacesBaseChange B S hS f).functor).obj
          ((spacesEtaleLocalization B S hS q hq).functor.obj T)).hom c).hom.left).op ≫
        H.map ((((relocalizedSiteIso B S hS f g p hp q hq c hc).hom.app T).left).hom.left).op =
      H.map ((spacesBaseChange B S hS g).projection.app T).op :=
  map_op_comp₃ H _ _ _ _ (relocalizedSiteIso_projection B S hS f g p hp q hq c hc T)

/-- Via the identifications of Stacks 04LZ for `U ⟶ X` and for `V ⟶ Y`, the morphism of ringed
topoi `(g_{spaces,étale}, g^♯)` is 2-isomorphic to the morphism `(f_{spaces,étale,c}, f_c^♯)` of
Stacks 04J1 built from `(f_{spaces,étale}, f^♯)` and the map `c : U ⟶ V ×_Y X` corresponding to
`g`: the square of ringed topoi whose vertical arrows are the two identifications commutes, up
to an invertible 2-morphism. -/
@[stacks 04M4 "the two morphisms of ringed topoi are 2-isomorphic, via the identifications of
  04LZ read as the two vertical arrows of a commuting square"]
noncomputable def spacesEtaleRelocalizedTwoIso :
    AlgebraicGeometry.RingedToposHom.TwoIso
      (A := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        ((spacesEtaleRingedSite B S hS X).over (etaleObject B S hS p hp)))
      (B := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (spacesEtaleRingedSite B S hS V))
      (AlgebraicGeometry.RingedToposHom.comp
        (X := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          ((spacesEtaleRingedSite B S hS X).over (etaleObject B S hS p hp)))
        (Y := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          ((spacesEtaleRingedSite B S hS Y).over (etaleObject B S hS q hq)))
        (Z := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (spacesEtaleRingedSite B S hS V))
        (spacesEtaleLocalizationRingedSiteHom B S hS q hq).ringedToposHom
        ((spacesEtaleRingedSiteHom B S hS f).relocalized c))
      (AlgebraicGeometry.RingedToposHom.comp
        (X := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          ((spacesEtaleRingedSite B S hS X).over (etaleObject B S hS p hp)))
        (Y := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (spacesEtaleRingedSite B S hS U))
        (Z := AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
          (spacesEtaleRingedSite B S hS V))
        (spacesEtaleRingedSiteHom B S hS g).ringedToposHom
        (spacesEtaleLocalizationRingedSiteHom B S hS p hp).ringedToposHom) where
  e := relocalizedUnderlyingIso B S hS f g p hp q hq c hc
  commutes := by
    have hL := AlgebraicGeometry.RingedSite.forgetFSharp_comp_ringedToposHom_comp
      (spacesEtaleLocalizationRingedSiteHom B S hS q hq)
      ((spacesEtaleRingedSiteHom B S hS f).localized (etaleObject B S hS q hq))
      ((spacesEtaleRingedSite B S hS X).relocalizationRingedToposHom c)
    have hR := AlgebraicGeometry.RingedSite.forgetFSharp_comp_ringedToposHom
      (spacesEtaleRingedSiteHom B S hS g)
      (spacesEtaleLocalizationRingedSiteHom B S hS p hp)
    refine ((congrArg (fun z => z ≫ (relocalizedUnderlyingIso B S hS f g p hp q hq c hc).hom.app
      ((AlgebraicGeometry.RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        ((spacesEtaleRingedSite B S hS X).over
          (etaleObject B S hS p hp))).forgetRing.obj
        ((spacesEtaleRingedSite B S hS X).over (etaleObject B S hS p hp)).O)) hL).trans
      (Eq.trans ?_ hR.symm))
    refine Sheaf.hom_ext (NatTrans.ext (funext fun T => ?_))
    have hrel := (spacesEtaleRingedSite B S hS X).relocalizationDirectImageIso_fSharp_app c
      (Opposite.op ((Over.post (spacesBaseChange B S hS f).functor).obj
        ((spacesEtaleLocalization B S hS q hq).functor.obj T.unop)))
    have key := relocalizedSiteIso_map_projection B S hS f g p hp q hq c hc
      (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}) T.unop
    exact (congrArg (fun z =>
      (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          ((spacesBaseChange B S hS f).projection.app
            (((spacesEtaleLocalization B S hS q hq).functor.obj T.unop).left)).op ≫
        z ≫ (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          ((((relocalizedSiteIso B S hS f g p hp q hq c hc).hom.app T.unop).left).hom.left).op)
      hrel).trans key

end AlgebraicGeometry.Space

end

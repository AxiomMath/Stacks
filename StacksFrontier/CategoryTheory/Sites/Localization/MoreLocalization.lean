module
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproductSheaf
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizationCofinality
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Open
public import Std.Tactic.BVDecide.Normalize.Prop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction along `j_U` undoes `j_{U!}` and `j_{U*}` when `U` is subterminal

Let `(C, J)` be a site and let `U` be an object of `C` such that every object of `C` admits at
most one morphism to `U`, that is, `U` is a subobject of the final object. The localization
functor `j_U = Over.forget U : C/U ⥤ C` is then fully faithful, and its restriction functor
`j_U^{-1} : Sh(C) ⥤ Sh(C/U)` sits in an adjoint triple `j_{U!} ⊣ j_U^{-1} ⊣ j_{U*}`
(Stacks 00XS, 00XO). For an open immersion of topological spaces both the extension by the empty
set and the pushforward restrict back to the sheaf one started with; the same holds here: the
canonical maps
`F ⟶ j_U^{-1}j_{U!}F` and `j_U^{-1}j_{U*}F ⟶ F`
— the unit of `j_{U!} ⊣ j_U^{-1}` and the counit of `j_U^{-1} ⊣ j_{U*}` — are isomorphisms for
every sheaf `F` on `C/U`. This is false for a general `U`, where `j_U^{-1}j_{U*}F(X/U)` is a limit
over all morphisms `X ⟶ U`, not just the structure morphism.

## Main results

* `GrothendieckTopology.isIso_unit_and_sheafAdjunctionCocontinuous_counit_of_isSubterminal`: for
  `U` subterminal the canonical maps `F ⟶ j_U^{-1}j_{U!}F` and `j_U^{-1}j_{U*}F ⟶ F` are
  isomorphisms.
* `GrothendieckTopology.isIso_unit_and_counit_of_isSubterminal_addCommGrpCat`: the same for
  abelian sheaves.

## References

* [Stacks 00Y2](https://stacks.math.columbia.edu/tag/00Y2)
-/

section

universe w' w v u v₁ v₂ u₁ u₂
open CategoryTheory

namespace CategoryTheory.GrothendieckTopology

@[expose] public section

/-- Let `C` be a site, and let `U` be an object of `C` such that every object of `C` has at most
one morphism to `U`, i.e. `U` is subterminal. Let `L` be a left adjoint of
`j_U^{-1} = J.overPullback A U : Sh(C) ⥤ Sh(C/U)`, i.e. let `L` be `j_{U!}`, and let
`j_{U*} = {}_pj_U` be the pushforward along the cocontinuous localization functor. Then the
canonical maps `F ⟶ j_U^{-1}j_{U!}F` and `j_U^{-1}j_{U*}F ⟶ F` are isomorphisms for every sheaf
`F` on `C/U`: they are the unit of `j_{U!} ⊣ j_U^{-1}` and the counit of `j_U^{-1} ⊣ j_{U*}`.
Equivalently, `j_{U!}` and `j_{U*}` are fully faithful. -/
@[stacks 00Y2 "if every object of `C` has at most one morphism to `U`, the canonical maps \
  `F ⟶ j_U^{-1}j_{U!}F` and `j_U^{-1}j_{U*}F ⟶ F` are isomorphisms, for coefficients in an \
  arbitrary category `A`", sga "4 VIII 5.7" "open immersion case", sga "4 I 5.6" "special case"]
public theorem isIso_unit_and_sheafAdjunctionCocontinuous_counit_of_isSubterminal {C : Type u}
    [Category.{v} C] (J : GrothendieckTopology C) (U : C) (hU : IsSubterminal U) (A : Type w)
    [Category.{w'} A] [∀ (F : (Over U)ᵒᵖ ⥤ A), (Over.forget U).op.HasPointwiseRightKanExtension F]
    {L : Sheaf (J.over U) A ⥤ Sheaf J A} (adj : L ⊣ J.overPullback A U) :
    IsIso adj.unit ∧
      IsIso ((Over.forget U).sheafAdjunctionCocontinuous A (J.over U) J).counit := by
  have : (Over.forget U).Full := (full_overForget_iff_isSubterminal U).2 hU
  exact
    ⟨Functor.isIso_unit_of_sheafPushforwardContinuous (Over.forget U) A (J.over U) J adj,
      inferInstance⟩

/-- Let `C` be a site and `U` an object of `C` such that every object of `C` has at most one
morphism to `U`. For an abelian sheaf `F` on `C/U` the canonical maps
`F ⟶ j_U^{-1}j_{U!}F` and `j_U^{-1}j_{U*}F ⟶ F` are isomorphisms. -/
@[stacks 0F6Z]
public theorem isIso_unit_and_counit_of_isSubterminal_addCommGrpCat {C : Type u}
    [Category.{v} C] (J : GrothendieckTopology C) (U : C) (hU : IsSubterminal U)
    [∀ (F : (Over U)ᵒᵖ ⥤ AddCommGrpCat.{w}),
      (Over.forget U).op.HasPointwiseRightKanExtension F]
    {L : Sheaf (J.over U) AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w}}
    (adj : L ⊣ J.overPullback AddCommGrpCat.{w} U) :
    IsIso adj.unit ∧
      IsIso ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat.{w}
        (J.over U) J).counit :=
  isIso_unit_and_sheafAdjunctionCocontinuous_counit_of_isSubterminal J U hU _ adj

end

end CategoryTheory.GrothendieckTopology

end

/-!
# `j_{U!}` needs no sheafification when the representable `h_U` is a sheaf

Let `(C, J)` be a site, let `U` be an object of `C` and let `G` be a sheaf of sets on the localized
site `C/U`. Stacks 03CD computes the lower shriek `j_{U!}` of a *sheafification*: `j_{U!}(G^#)` is
the sheaf associated to the coproduct presheaf `V ↦ ∐_{φ ∈ Hom_C(V, U)} G(V →φ U)`. If the
representable presheaf `h_U = yoneda.obj U` is a `J`-sheaf — in particular if `J` is subcanonical,
Stacks 00WQ — then no sheafification is needed: the coproduct presheaf is already a sheaf, and it
*is* `j_{U!}G`, so that
`j_{U!}G(V) = ∐_{φ ∈ Hom_C(V, U)} G(V →φ U)`.

## Main results

* `CategoryTheory.OverShriek.isIso_ofRestricted_unit`: if `h_U` is a sheaf, the canonical map
  from the coproduct presheaf `V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` (`CategoryTheory.OverShriek.presheaf`)
  to the underlying presheaf of `j_{U!}G` is an isomorphism.

## References

* [Stacks 03HT](https://stacks.math.columbia.edu/tag/03HT)
-/

section

universe v u
open CategoryTheory Opposite OverShriek

namespace Stacks.Sites.LowerShriekCoproduct

section Iso

variable {C : Type u} [Category.{v} C] {U : C}

/-- If the coproduct presheaf `V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` is a `J`-sheaf, then the canonical
map from it to the presheaf underlying `j_{U!}G` is an isomorphism. -/
private lemma isIso_ofRestricted_unit_of_isSheaf (J : GrothendieckTopology C)
    {L : Sheaf (J.over U) (Type v) ⥤ Sheaf J (Type v)} (adj : L ⊣ J.overPullback (Type v) U)
    (G : Sheaf (J.over U) (Type v)) (hP : Presheaf.IsSheaf J (presheaf G.obj)) :
    IsIso (ofRestricted G.obj (F := (L.obj G).obj) (adj.unit.app G).hom) := by
  let S : Sheaf J (Type v) := ⟨presheaf G.obj, hP⟩
  let a : S ⟶ L.obj G :=
    ObjectProperty.homMk (ofRestricted G.obj (F := (L.obj G).obj) (adj.unit.app G).hom)
  let u' : G ⟶ (J.overPullback (Type v) U).obj S :=
    ObjectProperty.homMk (homEquiv G.obj (presheaf G.obj) (𝟙 (presheaf G.obj)))
  let b : L.obj G ⟶ S := (adj.homEquiv G S).symm u'
  have hu : u' ≫ (J.overPullback (Type v) U).map a = adj.unit.app G := by
    refine Sheaf.hom_ext ?_
    change
      homEquiv G.obj (presheaf G.obj) (𝟙 (presheaf G.obj)) ≫
          Functor.whiskerLeft (Over.forget U).op a.hom =
        (adj.unit.app G).hom
    rw [← homEquiv_naturality, Category.id_comp]
    rfl
  refine (ObjectProperty.isIso_hom_iff a).2 ⟨b, ?_, ?_⟩
  · refine Sheaf.hom_ext ?_
    rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom]
    refine (homEquiv G.obj (presheaf G.obj)).injective ?_
    rw [homEquiv_naturality]
    have h := (adj.homEquiv G S).apply_symm_apply u'
    rw [Adjunction.homEquiv_unit] at h
    exact Sheaf.hom_ext_iff.1 h
  · refine (adj.homEquiv G (L.obj G)).injective ?_
    rw [adj.homEquiv_id, adj.homEquiv_naturality_right, (adj.homEquiv G S).apply_symm_apply u']
    exact hu

end Iso

end Stacks.Sites.LowerShriekCoproduct

namespace CategoryTheory.OverShriek

@[expose] public section

open Stacks.Sites.LowerShriekCoproduct in
/-- Let `C` be a site, let `U` be an object of `C` whose representable presheaf `h_U` is a sheaf
(for instance because the topology is subcanonical), and let `G` be a sheaf of sets on `C/U`. Let
`L` be a left adjoint of the restriction functor `j_U^{-1} = J.overPullback : Sh(C) ⥤ Sh(C/U)`,
i.e. let `L` be `j_{U!}`. Then the canonical map from the coproduct presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` to the presheaf underlying `j_{U!}G`, which over `V` sends a pair
`(φ, s)` to the section `s` of `j_{U!}G`, is an isomorphism:
`j_{U!}G(V) = ∐_{φ ∈ Hom_C(V, U)} G(V →φ U)`. -/
@[stacks 03HT "j_{U!}G(V) = ∐_{φ : V ⟶ U} G(V →φ U) for a subcanonical topology."]
public theorem isIso_ofRestricted_unit {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (U : C) (hU : Presieve.IsSheaf J (yoneda.obj U))
    {L : Sheaf (J.over U) (Type v) ⥤ Sheaf J (Type v)} (adj : L ⊣ J.overPullback (Type v) U)
    (G : Sheaf (J.over U) (Type v)) :
    IsIso (ofRestricted G.obj (F := (L.obj G).obj) (adj.unit.app G).hom) :=
  isIso_ofRestricted_unit_of_isSheaf J adj G <|
    (isSheaf_iff_isSheaf_of_type J _).2 <|
    CategoryTheory.OverShriek.isSheaf_presheaf J G.obj hU
      ((isSheaf_iff_isSheaf_of_type (J.over U) _).1 G.property)

end

end CategoryTheory.OverShriek

end

/-!
# Base change for the relocalization morphisms of a cartesian square

Let `(C, J)` be a site and let

```
  U' --a--> U
  |b        |c
  V' --d--> V
```

be a commutative square of `C`. Each of its four morphisms `f : X ⟶ Y` gives a relocalization
functor `Over.map f : C/X ⥤ C/Y` (Stacks 03EH), continuous and cocontinuous for the localized
topologies `J.over •` of Stacks 00XZ, hence a morphism of topoi `j : Sh(C/X) ⟶ Sh(C/Y)` whose
inverse image `j^{-1}` is restriction along it, `GrothendieckTopology.overMapPullback`, and whose
pushforward `j_* = {}_p j` is the right Kan extension along its opposite. The square of sites
commutes on the nose, `Over.map a ⋙ Over.map c = Over.map (a ≫ c) = Over.map (b ≫ d) =
Over.map b ⋙ Over.map d`, and restriction turns that into the commutation isomorphism
`j_{V'/V}^{-1} ⋙ j_{U'/V'}^{-1} ≅ j_{U/V}^{-1} ⋙ j_{U'/U}^{-1}`, which is the assertion that the
square of topoi commutes.

If the square is cartesian, the pushforwards satisfy base change:
`j_{V'/V}^{-1} ∘ j_{U/V, *} = j_{U'/V', *} ∘ j_{U'/U}^{-1}`. The content is that the canonical
comparison — the mate of the commutation isomorphism above, taken through the two adjunctions
`j^{-1} ⊣ j_*` — is invertible; for `C` the opens of a topological space this is the classical
statement that pushing a sheaf forward along an open immersion and restricting to a smaller open
of the target is the same as restricting first and pushing forward along the base change.

## Main definitions

* `CategoryTheory.GrothendieckTopology.overMapPullbackSquare`: for a commutative square, the
  commutation isomorphism `j_{V'/V}^{-1} ⋙ j_{U'/V'}^{-1} ≅ j_{U/V}^{-1} ⋙ j_{U'/U}^{-1}` of the
  square of inverse images.
* `CategoryTheory.GrothendieckTopology.overMapPushforwardBaseChange`: the base change
  transformation `j_{V'/V}^{-1} ∘ j_{U/V, *} ⟶ j_{U'/V', *} ∘ j_{U'/U}^{-1}`, the mate of that
  isomorphism.

## Main results

* `CategoryTheory.GrothendieckTopology.isIso_overMapPushforwardBaseChange`: for a cartesian square,
  the base change transformation is an isomorphism.

## References

* [Stacks 0EYV](https://stacks.math.columbia.edu/tag/0EYV)
-/

section

universe w' w v u v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
open CategoryTheory Stacks.Sites.RelocalizationCofinality

namespace Stacks.Sites.RelocalizationBaseChange

section Mate

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [Category.{v₁} C₁]
  [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄] {G : C₁ ⥤ C₃} {H : C₂ ⥤ C₄}
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₃ ⥤ C₄} {R₂ : C₄ ⥤ C₃}

/-- The mate of a 2-cell `α : G ⋙ L₂ ⟶ L₁ ⋙ H` is, at every object, the transpose under the
adjunction `L₂ ⊣ R₂` of the composite of `α` with the counit of `L₁ ⊣ R₁`. -/
private lemma mateEquiv_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (X : C₂) :
    (mateEquiv adj₁ adj₂ α).app X =
      adj₂.homEquiv _ _ (α.app (R₁.obj X) ≫ H.map (adj₁.counit.app X)) := by
  simp [mateEquiv_apply, Adjunction.homEquiv_unit]

end Mate

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U' U V' V : C} {a : U' ⟶ U}
  {b : U' ⟶ V'} {c : U ⟶ V} {d : V' ⟶ V} (A : Type w) [Category.{w'} A]

/-- The 2-square of slice functors is the composite of the canonical identifications
`Over.mapComp` and `Over.mapCongr` of the two ways of reading the commutative square: both sides
are the identity on underlying objects of `C`. -/
private lemma overMapSquare_natTrans_app (sq : CommSq a b c d) (W : Over U') :
    (overMapSquare sq).app W =
      (Over.mapComp a c).inv.app W ≫
        (Over.mapCongr (b ≫ d) (a ≫ c) sq.w.symm).inv.app W ≫ (Over.mapComp b d).hom.app W := by
  ext
  simp [overMapSquare, Over.mapComp, Over.mapCongr]

end

end Stacks.Sites.RelocalizationBaseChange


namespace CategoryTheory.GrothendieckTopology

@[expose] public section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {U' U V' V : C} {a : U' ⟶ U}
  {b : U' ⟶ V'} {c : U ⟶ V} {d : V' ⟶ V} (A : Type w) [Category.{w'} A]

/-- The square of topoi attached to a commutative square

```
  U' --a--> U
  |b        |c
  V' --d--> V
```

of `C` by the relocalization morphisms commutes, in the form of the commutation isomorphism
`j_{V'/V}^{-1} ⋙ j_{U'/V'}^{-1} ≅ j_{U/V}^{-1} ⋙ j_{U'/U}^{-1}` between the two composite inverse
images. -/
@[simps!,
  stacks 0EYV "The relocalization morphisms of a commutative square form a commutative
  square of topoi: the two composites `j_{V'/V}^{-1} ⋙ j_{U'/V'}^{-1}` and
  `j_{U/V}^{-1} ⋙ j_{U'/U}^{-1}` of inverse images are canonically isomorphic."]
public def overMapPullbackSquare (sq : CommSq a b c d) :
    J.overMapPullback A d ⋙ J.overMapPullback A b ≅
      J.overMapPullback A c ⋙ J.overMapPullback A a :=
  J.overMapPullbackComp A b d ≪≫
    J.overMapPullbackCongr A sq.w.symm ≪≫ (J.overMapPullbackComp A a c).symm

/-- The base change transformation `j_{V'/V}^{-1} ∘ j_{U/V, *} ⟶ j_{U'/V', *} ∘ j_{U'/U}^{-1}`
attached to a commutative square

```
  U' --a--> U
  |b        |c
  V' --d--> V
```

of `C`: the mate of the commutation isomorphism `overMapPullbackSquare` of the square of inverse
images, through the adjunctions `j^{-1} ⊣ j_*`. -/
public noncomputable def overMapPushforwardBaseChange (sq : CommSq a b c d)
    [∀ (F : (Over U)ᵒᵖ ⥤ A), (Over.map c).op.HasPointwiseRightKanExtension F]
    [∀ (F : (Over U')ᵒᵖ ⥤ A), (Over.map b).op.HasPointwiseRightKanExtension F] :
    TwoSquare ((Over.map c).sheafPushforwardCocontinuous A (J.over U) (J.over V))
      (J.overMapPullback A a) (J.overMapPullback A d)
      ((Over.map b).sheafPushforwardCocontinuous A (J.over U') (J.over V')) :=
  mateEquiv ((Over.map c).sheafAdjunctionCocontinuous A (J.over U) (J.over V))
    ((Over.map b).sheafAdjunctionCocontinuous A (J.over U') (J.over V'))
    (TwoSquare.mk _ _ _ _ (J.overMapPullbackSquare A sq).hom)

section

open Stacks.Sites.RelocalizationBaseChange

variable [∀ (F : (Over U)ᵒᵖ ⥤ A), (Over.map c).op.HasPointwiseRightKanExtension F]
  [∀ (F : (Over U')ᵒᵖ ⥤ A), (Over.map b).op.HasPointwiseRightKanExtension F]

omit [∀ (F : (Over U')ᵒᵖ ⥤ A), (Over.map b).op.HasPointwiseRightKanExtension F] in
/-- The presheaf map whose transpose is the base change transformation is the right extension
obtained from the counit of `j_{U/V, *}` by composing with the 2-square of relocalization
functors. -/
private lemma overMapPullbackSquare_comp_counit_hom (sq : CommSq a b c d)
    (F : Sheaf (J.over U) A) :
    ((J.overMapPullbackSquare A sq).hom.app
            (((Over.map c).sheafPushforwardCocontinuous A (J.over U) (J.over V)).obj F) ≫
          (J.overMapPullback A a).map
            (((Over.map c).sheafAdjunctionCocontinuous A (J.over U) (J.over V)).counit.app
              F)).hom =
      ((Functor.RightExtension.mk _ ((Over.map c).op.ranCounit.app F.obj)).compTwoSquare
          (overMapSquare sq).op).hom := by
  ext X
  dsimp [overMapPullbackSquare]
  rw [overMapSquare_natTrans_app]
  simp only [Functor.sheafAdjunctionCocontinuous_counit_app_hom,
    Functor.ranAdjunction_counit,
    GrothendieckTopology.overMapPullbackComp_hom_app_hom_app,
    GrothendieckTopology.overMapPullbackCongr_hom_app_hom_app,
    GrothendieckTopology.overMapPullbackComp_inv_app_hom_app,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.comp_obj, op_comp,
    Category.assoc, Functor.map_comp, Category.id_comp]
  change
    (((Over.map c).op.ran.obj F.obj).map ((Over.mapComp b d).hom.app X.unop).op ≫
          ((Over.map c).op.ran.obj F.obj).map
            ((Over.mapCongr (b ≫ d) (a ≫ c) sq.w.symm).inv.app X.unop).op ≫
          ((Over.map c).op.ran.obj F.obj).map ((Over.mapComp a c).inv.app X.unop).op) ≫
        ((Over.map c).op.ranCounit.app F.obj).app (Opposite.op ((Over.map a).obj X.unop)) =
      _
  simp [Category.assoc]

/-- The base change transformation, at a sheaf, has as underlying presheaf map the transpose of
the presheaf map of `overMapPullbackSquare_comp_counit_hom`. -/
private lemma overMapPushforwardBaseChange_natTrans_app_hom (sq : CommSq a b c d)
    (F : Sheaf (J.over U) A) :
    ((J.overMapPushforwardBaseChange A sq).app F).hom =
      ((Over.map b).op.ranAdjunction A).homEquiv _ _
        ((Functor.RightExtension.mk _ ((Over.map c).op.ranCounit.app F.obj)).compTwoSquare
            (overMapSquare sq).op).hom := by
  change
    ((mateEquiv ((Over.map c).sheafAdjunctionCocontinuous A (J.over U) (J.over V))
              ((Over.map b).sheafAdjunctionCocontinuous A (J.over U') (J.over V'))
              (TwoSquare.mk _ _ _ _ (J.overMapPullbackSquare A sq).hom)).app
          F).hom =
      _
  rw [mateEquiv_app, Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom,
    overMapPullbackSquare_comp_counit_hom]
  rfl

end

/-- If the square

```
  U' --a--> U
  |b        |c
  V' --d--> V
```

of `C` is cartesian, then the relocalization morphisms satisfy base change,
`j_{V'/V}^{-1} ∘ j_{U/V, *} = j_{U'/V', *} ∘ j_{U'/U}^{-1}`: the base change transformation
`overMapPushforwardBaseChange` is an isomorphism. -/
@[stacks 0EYV "For a cartesian square, the base change transformation
  `j_{V'/V}^{-1} ∘ j_{U/V,*} ⟶ j_{U'/V',*} ∘ j_{U'/U}^{-1}` of the relocalization morphisms is an
  isomorphism."]
public theorem isIso_overMapPushforwardBaseChange (hsq : IsPullback a b c d)
    [∀ (F : (Over U)ᵒᵖ ⥤ A), (Over.map c).op.HasPointwiseRightKanExtension F]
    [∀ (F : (Over U')ᵒᵖ ⥤ A), (Over.map b).op.HasPointwiseRightKanExtension F] :
    IsIso (J.overMapPushforwardBaseChange A hsq.toCommSq) := by
  have := guitartExact_overMapSquare hsq
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  rw [← ObjectProperty.isIso_hom_iff, overMapPushforwardBaseChange_natTrans_app_hom]
  exact
    (Functor.isIso_ranAdjunction_homEquiv_iff _ _).2
      ((Functor.isPointwiseRightKanExtensionOfIsRightKanExtension ((Over.map c).op.ran.obj F.obj)
              ((Over.map c).op.ranCounit.app F.obj)).compTwoSquare
          (overMapSquare hsq.toCommSq).op).isRightKanExtension

end

end CategoryTheory.GrothendieckTopology

end

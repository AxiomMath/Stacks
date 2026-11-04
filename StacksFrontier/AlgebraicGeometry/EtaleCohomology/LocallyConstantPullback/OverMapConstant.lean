module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.ConstantInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Restriction of a constant sheaf of sets along a morphism of the site

Let `J` be a Grothendieck topology on a category `C` with pullbacks and let `f : X ⟶ Y` be a
morphism of `C`. Restriction of sheaves along `Over.map f`, that is
`GrothendieckTopology.overMapPullback`, is the inverse image of a morphism of topoi
`Sh(C/X) ⟶ Sh(C/Y)`: it is left exact because it is a restriction along a continuous functor
(Tag 04J4), and it is a left adjoint because `Over.map f ⊣ Over.pullback f` is an adjoint pair of
continuous functors (Tag 03CE). Consequently
`Stacks.ConstantSheaf.inverseImageConstantSheafIso` applies, and restriction along `f` carries
the constant sheaf on a set to the constant sheaf on the *same* set.

This settles, unconditionally and for a carrier universe unrelated to the site, the statement that
`Stacks.ConstantSheaf.constantSheafOverMapComparison` was only known to satisfy under a
subsingleton or detector hypothesis; see the implementation notes of
the file `Constructible/Localization/SimultaneousTrivialization.lean` of this directory's parent.
The route taken there, local bijectivity of the comparison map, needs the injectivity of
`B ⟶ B̲(V)` and hence `GrothendieckTopology.WEqualsLocallyBijective`, which the library has only at
carrier universe `max u v`. Uniqueness of left adjoints needs neither.

The consequence used downstream is the *stability of a trivialization under refinement*: if a
sheaf on `C` becomes constant with value `A` after restriction to `Y`, it becomes constant with
the same value `A` after restriction to any `X` lying over `Y`. Local constancy therefore survives
refinement of the trivializing covering, which is what the simultaneous trivializations of Tags
093S and 093U need.

## Main results

* `Stacks.ConstantSheaf.overMapMorphismOfTopoi` — the morphism of topoi `Sh(C/X) ⟶ Sh(C/Y)`
  whose inverse image is `GrothendieckTopology.overMapPullback`.
* `Stacks.ConstantSheaf.overMapPullbackConstantSheafIso` — restriction along `Over.map f`
  commutes with the constant sheaf functor.
* `Stacks.ConstantSheaf.isConstant_overMapPullback` — restriction along `Over.map f` preserves
  constant sheaves.
* `Stacks.ConstantSheaf.overPullbackIsoOfMap` — a trivialization of a sheaf over `Y`, with value
  `A`, restricts to a trivialization over `X` with the same value `A`, along an arbitrary
  `f : X ⟶ Y`.
* `Stacks.ConstantSheaf.isConstant_over_of_isConstant_over` — its `Prop`-valued form.
* `Stacks.ConstantSheaf.overMorphismOfTopoi`,
  `Stacks.ConstantSheaf.overPullbackConstantSheafIsoType`
  and `Stacks.ConstantSheaf.isConstant_overPullback` — the same for restriction to an object of
  the site, `GrothendieckTopology.overPullback`, when the site has binary products.

## References

* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 03CE](https://stacks.math.columbia.edu/tag/03CE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [HasPullbacks C]
  [∀ U : C, HasWeakSheafify (J.over U) (Type w)]

/-- **The localization morphism of topoi `Sh(C/X) ⟶ Sh(C/Y)` of `f : X ⟶ Y`.** Its inverse image
is restriction along `Over.map f`, which is left exact by Tag 04J4 and a left adjoint because
`Over.map f ⊣ Over.pullback f` is an adjoint pair of continuous functors (Tag 03CE). -/
public def overMapMorphismOfTopoi {X Y : C} (f : X ⟶ Y) :
    MorphismOfTopoi (Sheaf (J.over X) (Type w)) (Sheaf (J.over Y) (Type w)) where
  inverseImage := J.overMapPullback (Type w) f
  pushforward := (Over.pullback f).sheafPushforwardContinuous (Type w) (J.over Y) (J.over X)
  adj := (Over.mapPullbackAdj f).sheafPushforwardAdjunction (Type w)
  preservesFiniteLimits := inferInstance

/-- **Restriction of a constant sheaf of sets along a morphism of the site is constant**, with the
same value. This is the localization case of Tag 093R, in the form of a natural isomorphism of
functors, and it holds unconditionally. -/
public def overMapPullbackConstantSheafIso {X Y : C} (f : X ⟶ Y) :
    constantSheaf (J.over Y) (Type w) ⋙ J.overMapPullback (Type w) f ≅
      constantSheaf (J.over X) (Type w) :=
  (overMapMorphismOfTopoi J f).constantSheafIso Over.mkIdTerminal Over.mkIdTerminal

/-- Restriction along a morphism of the site preserves constant sheaves of sets. -/
public lemma isConstant_overMapPullback {X Y : C} (f : X ⟶ Y) (G : Sheaf (J.over Y) (Type w))
    [Sheaf.IsConstant (J.over Y) G] :
    Sheaf.IsConstant (J.over X) ((J.overMapPullback (Type w) f).obj G) :=
  (overMapMorphismOfTopoi J f).isConstant_inverseImage Over.mkIdTerminal Over.mkIdTerminal G

/-- **A trivialization survives refinement.** If the restriction of `G` to `Y` is the constant
sheaf on `A`, then its restriction to any `X` over `Y` is the constant sheaf on the *same* `A`.

Keeping the value unchanged is what makes the statement usable for *finite* local constancy: any
property of the constant value, finiteness in particular, is transported along with it. -/
public def overPullbackIsoOfMap {X Y : C} (f : X ⟶ Y) (G : Sheaf J (Type w)) (A : Type w)
    (e : (constantSheaf (J.over Y) (Type w)).obj A ≅ (J.overPullback (Type w) Y).obj G) :
    (constantSheaf (J.over X) (Type w)).obj A ≅ (J.overPullback (Type w) X).obj G :=
  (overMapPullbackConstantSheafIso J f).symm.app A ≪≫
    (J.overMapPullback (Type w) f).mapIso e ≪≫ G.pushforwardOverMapIso f

/-- The `Prop`-valued form of `Stacks.ConstantSheaf.overPullbackIsoOfMap`: a sheaf which becomes
constant after restriction to `Y` becomes constant after restriction to any `X` over `Y`. -/
public lemma isConstant_over_of_isConstant_over {X Y : C} (f : X ⟶ Y) (G : Sheaf J (Type w))
    [Sheaf.IsConstant (J.over Y) ((J.overPullback (Type w) Y).obj G)] :
    Sheaf.IsConstant (J.over X) ((J.overPullback (Type w) X).obj G) :=
  have := isConstant_overMapPullback J f ((J.overPullback (Type w) Y).obj G)
  Sheaf.isConstant_congr (J.over X) (G.pushforwardOverMapIso f)

section Forget

variable [HasBinaryProducts C] [HasWeakSheafify J (Type w)]

/-- **The localization morphism of topoi `Sh(C/U) ⟶ Sh(C)`.** Its inverse image is restriction
to `U`, that is `GrothendieckTopology.overPullback`, which is left exact by Tag 04J4 and a left
adjoint because `Over.forget U ⊣ Over.star U` is an adjoint pair of continuous functors
(Tag 03CE). -/
public def overMorphismOfTopoi (U : C) :
    MorphismOfTopoi (Sheaf (J.over U) (Type w)) (Sheaf J (Type w)) where
  inverseImage := J.overPullback (Type w) U
  pushforward := (Over.star U).sheafPushforwardContinuous (Type w) J (J.over U)
  adj := (Over.forgetAdjStar U).sheafPushforwardAdjunction (Type w)
  preservesFiniteLimits := inferInstance

/-- **Restriction to an object of the site carries a constant sheaf of sets to a constant
sheaf**, with the same value. 

The name says `Type` because `Stacks.ConstantSheaf.overPullbackConstantSheafIso` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom` is the comparison in the
opposite direction, for an arbitrary coefficient category. -/
public def overPullbackConstantSheafIsoType {T : C} (hT : IsTerminal T) (U : C) :
    constantSheaf J (Type w) ⋙ J.overPullback (Type w) U ≅ constantSheaf (J.over U) (Type w) :=
  (overMorphismOfTopoi J U).constantSheafIso Over.mkIdTerminal hT

omit [HasPullbacks C] in
/-- Restriction to an object of the site preserves constant sheaves of sets. -/
public lemma isConstant_overPullback {T : C} (hT : IsTerminal T) (U : C) (F : Sheaf J (Type w))
    [Sheaf.IsConstant J F] :
    Sheaf.IsConstant (J.over U) ((J.overPullback (Type w) U).obj F) :=
  (overMorphismOfTopoi J U).isConstant_inverseImage Over.mkIdTerminal hT F

end Forget

end Stacks.ConstantSheaf

end

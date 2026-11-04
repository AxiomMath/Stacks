module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparisonComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleRestrictionFinalSections

/-!
# The comparison maps of Stacks 06W2 against the sections at the structure object

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `φ : x ⟶ y` an arrow of `𝒳`
lying over a morphism of schemes `a : U ⟶ V`, and `F` a presheaf on `𝒳`. The restriction of
**Stacks 06W1** reads the sections of `F|_{V_ét}` over a small étale object `W / V` as the
sections of `F` at an object of `𝒳` lying over `W`; that object comes with a canonical arrow
down to `y`, and restriction of `F` along it is a map

`F(y) ⟶ (F|_{V_ét})(W)`,

the *evaluation* map of this file. At the final object `V / V` it is the inverse of
`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso`.

The one statement with content here is that the comparison map `c_φ` of **Stacks 06W2** is
`F(φ)` through these evaluation maps:

`eval_y(W) ≫ c_φ(W) = F(φ) ≫ eval_x(a^{-1}W)`.

That is a reformulation of the component formula
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app`: the arrow of `𝒳` which computes
`c_φ(W)` is characterized by a commuting square whose statement *is* this equality.

Two things follow at once, and they are what the step of **Stacks 076T** carried in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean` needs of
the global-sections half of its composite identification.

* The comparison maps compose in the sense of **Stacks 075D (1)** when read through the
  evaluation maps: both the composite `c_φ ∘ c_ψ` and `c_{ψ ∘ φ}` become `F(ψ ∘ φ)`, so no
  comparison of base changes is left over. This is the form in which the identification used by
  Stacks 076T is natural in the arrow of `𝒳`, rather than four unrelated bijections.
* At the final object the comparison is restriction along the arrow itself: conjugating
  `c_φ(V / V)` by `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso` at `y` and at `x`
  returns `F(φ) : F(y) ⟶ F(x)`. The identification of the base change `a^{-1}(V / V)` with the
  final object `U / U` of the small étale site of `U` that this needs is the canonical arrow to
  the final object, no more.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleLiftObject` and
  `AlgebraicGeometry.Stack.smallEtaleLiftHom`: the object of `𝒳` at which the restriction of
  Stacks 06W1 reads the sections over a small étale object, and its canonical arrow to `x`.
* `AlgebraicGeometry.Stack.restrictToSmallEtaleEval`: the evaluation map
  `F(x) ⟶ (F|_{U_ét})(W)`.

## Main results

* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval`: **the comparison map of
  Stacks 06W2 is restriction along the arrow, through the evaluation maps.**
* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval_comp`: **Stacks 075D (1)
  through the evaluation maps**, with no comparison of base changes left over.
* `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison`: **the comparison
  map at the final object of the small étale site is `F(φ)`**, conjugated by
  `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso`.
* `AlgebraicGeometry.Stack.restrictToSmallEtaleEval_comp_map`: the evaluation maps are
  compatible with the restriction maps of `F|_{U_ét}`.
* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_eval` and
  `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_eval_comp`: the same two
  statements for the module comparison of Stacks 06WC, on sections.

## Implementation notes

The evaluation map is restriction of `F` along the structure arrow of the object of `𝒳` that
the restriction of Stacks 06W1 evaluates at, so every statement below is an equality between
two restrictions of `F` along arrows of `𝒳` and reduces to an equality of those arrows. The
three equalities used are: the commuting square of
`AlgebraicGeometry.Stack.exists_restrictionComparisonLift`, which gives the comparison; the
triangle `CategoryTheory.Over.w` of the slice at `x`, which gives compatibility with the
restriction maps; and `CategoryTheory.Functor.map_comp`, which gives the composition statement.

`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso` is restriction along the counit of the
localization equivalence of Stacks 06W0, and its inverse is the evaluation map at the final
object because the unique arrow from the lifted final object to `id : x ⟶ x` in the slice `𝒳/x`
has the structure arrow as its component — that is `CategoryTheory.Over.w` again.

Nothing here asks the comparison map to be an isomorphism. Hypothesis (b) of Stacks 076T
supplies that only along arrows lying over a flat morphism locally of finite presentation, and
these statements are needed along all of them at once.

## References

* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The object of `𝒳` at which the restriction of Stacks 06W1 at `x` reads the sections over a
small étale object `W` of the scheme below `x`: `W`, included into the big fppf slice over that
scheme and transported back across the localization equivalence of Stacks 06W0.

`AlgebraicGeometry.Stack.smallEtaleFinalObject` is this object at the final object of the small
étale site. -/
noncomputable abbrev smallEtaleLiftObject (x : 𝒳)
    (W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) : 𝒳 :=
  letI := isEquivalence_overPost B S hS p hp x
  ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
    ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj W)).left

/-- The canonical arrow of `𝒳` from `AlgebraicGeometry.Stack.smallEtaleLiftObject` down to `x`:
the structure morphism of the object of the slice `𝒳/x` which the localization equivalence of
Stacks 06W0 produces. -/
noncomputable abbrev smallEtaleLiftHom (x : 𝒳)
    (W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    smallEtaleLiftObject B E h S hS p hp x W ⟶ x :=
  letI := isEquivalence_overPost B S hS p hp x
  ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.obj
    ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).obj W)).hom

/-- **The evaluation map of the restriction of Stacks 06W1.** Restriction of `F` along the
canonical arrow `AlgebraicGeometry.Stack.smallEtaleLiftHom`, read as a map from the sections of
`F` at `x` to the sections of `F|_{U_ét}` over a small étale object `W`.

At the final object of the small étale site this is the inverse of
`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso`. -/
noncomputable abbrev restrictToSmallEtaleEval (x : 𝒳) {A : Type t} [Category.{s} A]
    (F : 𝒳ᵒᵖ ⥤ A) (W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    F.obj (op x) ⟶ (restrictToSmallEtale B E h S hS p hp x F).obj (op W) :=
  F.map (smallEtaleLiftHom B E h S hS p hp x W).op

/-- **The evaluation maps are compatible with the restriction maps of `F|_{U_ét}`.** Restricting
from a small étale object `W'` to `W` after evaluating at `W'` is evaluating at `W`.

The canonical arrows of `AlgebraicGeometry.Stack.smallEtaleLiftHom` form a cone under the lifted
objects, that being the triangle `CategoryTheory.Over.w` of the slice `𝒳/x`. -/
theorem restrictToSmallEtaleEval_comp_map (x : 𝒳) {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A)
    {W W' : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)} (r : W ⟶ W') :
    restrictToSmallEtaleEval B E h S hS p hp x F W' ≫
        (restrictToSmallEtale B E h S hS p hp x F).map r.op =
      restrictToSmallEtaleEval B E h S hS p hp x F W := by
  have := isEquivalence_overPost B S hS p hp x
  show F.map _ ≫ F.map _ = F.map _
  rw [← F.map_comp]
  refine congrArg F.map (Quiver.Hom.unop_inj ?_)
  exact Over.w ((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv.map
    ((smallEtaleInclusion B E h (p.obj x).left.1
      (contains_base B E h S hS p x)).map r))

variable {x y z : 𝒳}

/-- **The comparison map of Stacks 06W2 is restriction along the arrow.** For `φ : x ⟶ y` an
arrow of `𝒳` lying over `a : U ⟶ V` and `W` a small étale object over `V`, the comparison map
`c_φ` at `W`, precomposed with the evaluation map at `W` over `y`, is restriction of `F` along
`φ` followed by the evaluation map at the base change `a^{-1}W` over `x`.

This is `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app` read off its own
characterization: the arrow of `𝒳` computing `c_φ(W)` is one making the square of
`AlgebraicGeometry.Stack.exists_restrictionComparisonLift` commute, and that square *is* this
equality after applying `F`. -/
theorem restrictionPushforwardComparison_app_eval {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A)
    (φ : x ⟶ y) (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y)) :
    restrictToSmallEtaleEval B E h S hS p hp y F W ≫
        (restrictionPushforwardComparison B E h S hS p hp φ F).app (op W) =
      F.map φ.op ≫ restrictToSmallEtaleEval B E h S hS p hp x F
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W) := by
  have := isEquivalence_overPost B S hS p hp x
  have := isEquivalence_overPost B S hS p hp y
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W
  rw [restrictionPushforwardComparison_app B E h S hS p hp φ F W φ' hfac hproj]
  show F.map _ ≫ F.map _ = F.map _ ≫ F.map _
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp]
  exact congrArg (fun k => F.map (op k)) hfac

/-- **Stacks 075D (1) through the evaluation maps.** For arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of
`𝒳`, the composite of the two comparison maps of Stacks 06W2, precomposed with the evaluation
map over `z`, is restriction of `F` along `ψ ∘ φ` followed by the evaluation map over `x`.

Read this way the composition statement of Stacks 075D (1) leaves no comparison of base changes
over: both the composite `c_φ ∘ c_ψ` and the single `c_{ψ ∘ φ}` become restriction along
`ψ ∘ φ`, and
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval_comp_eq_app_comp` recovers
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_comp` from this form. -/
@[stacks 075D "part (1), the direct-image comparisons read through the evaluation maps of the \
restriction of Stacks 06W1, so that no comparison of base changes is left over"]
theorem restrictionPushforwardComparison_app_eval_comp {A : Type t} [Category.{s} A]
    (F : 𝒳ᵒᵖ ⥤ A) (φ : x ⟶ y) (ψ : y ⟶ z)
    (W : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)) :
    restrictToSmallEtaleEval B E h S hS p hp z F W ≫
        (restrictionPushforwardComparison B E h S hS p hp ψ F).app (op W) ≫
          (restrictionPushforwardComparison B E h S hS p hp φ F).app (op
            ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W)) =
      F.map (φ ≫ ψ).op ≫ restrictToSmallEtaleEval B E h S hS p hp x F
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W)) := by
  rw [← Category.assoc, restrictionPushforwardComparison_app_eval, Category.assoc,
    restrictionPushforwardComparison_app_eval, ← Category.assoc, ← F.map_comp, ← op_comp]

/-- The composition statement through the evaluation maps implies the one with the comparison of
base changes: precomposing
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_comp` with the evaluation map over
`z` gives `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval_comp`, the
restriction map along the comparison of base changes being absorbed by
`AlgebraicGeometry.Stack.restrictToSmallEtaleEval_comp_map`. -/
theorem restrictionPushforwardComparison_app_eval_comp_eq_app_comp {A : Type t} [Category.{s} A]
    (F : 𝒳ᵒᵖ ⥤ A) (φ : x ⟶ y) (ψ : y ⟶ z)
    (W : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z)) :
    restrictToSmallEtaleEval B E h S hS p hp z F W ≫
        (restrictionPushforwardComparison B E h S hS p hp (φ ≫ ψ) F).app (op W) ≫
          (restrictToSmallEtale B E h S hS p hp x F).map
            ((smallEtaleBaseChangeCompIso B E h S hS p φ ψ).hom.app W).op =
      F.map (φ ≫ ψ).op ≫ restrictToSmallEtaleEval B E h S hS p hp x F
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W)) := by
  rw [← Category.assoc, restrictionPushforwardComparison_app_eval, Category.assoc,
    restrictToSmallEtaleEval_comp_map]
  rfl

/-- The counit of Stacks 06W0 at the final object of the small étale site is the canonical arrow
of `AlgebraicGeometry.Stack.smallEtaleLiftHom` there: the unique arrow of the slice `𝒳/x` from
the lifted final object to `id : x ⟶ x` has the structure arrow as its component. -/
theorem smallEtaleFinalObjectIso_hom (x : 𝒳) :
    (smallEtaleFinalObjectIso B E h S hS p hp x).hom =
      smallEtaleLiftHom B E h S hS p hp x (smallEtaleFinal B E h S hS p x) := by
  have := isEquivalence_overPost B S hS p hp x
  have hw := Over.w ((IsTerminal.isTerminalObj
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv _
    (isTerminal_smallEtaleInclusion_obj_final B E h S hS p x)).uniqueUpToIso
      Over.mkIdTerminal).hom
  exact (Category.comp_id _).symm.trans hw

/-- The identification of the global sections of a small étale restriction with the sections at
the object inverts the evaluation map at the final object. -/
theorem restrictToSmallEtaleFinalIso_inv (x : 𝒳) {A : Type t} [Category.{s} A] (F : 𝒳ᵒᵖ ⥤ A) :
    (restrictToSmallEtaleFinalIso B E h S hS p hp x F).inv =
      restrictToSmallEtaleEval B E h S hS p hp x F (smallEtaleFinal B E h S hS p x) := by
  show F.map (smallEtaleFinalObjectIso B E h S hS p hp x).hom.op = _
  rw [smallEtaleFinalObjectIso_hom]

/-- **The comparison map of Stacks 06W2 at the final object is restriction along the arrow.**
For `φ : x ⟶ y` lying over `a : U ⟶ V`, conjugating `c_φ` at the final object `V / V` by
`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso` at `y` and at `x` returns
`F(φ) : F(y) ⟶ F(x)`.

The identification of the base change `a^{-1}(V / V)` with the final object `U / U` of the small
étale site of `U` is the canonical arrow to the final object and nothing more; by
`AlgebraicGeometry.Stack.restrictToSmallEtaleEval_comp_map` the evaluation maps absorb it. -/
theorem restrictToSmallEtaleFinalIso_inv_comp_comparison {A : Type t} [Category.{s} A]
    (F : 𝒳ᵒᵖ ⥤ A) (φ : x ⟶ y) :
    (restrictToSmallEtaleFinalIso B E h S hS p hp y F).inv ≫
        (restrictionPushforwardComparison B E h S hS p hp φ F).app
          (op (smallEtaleFinal B E h S hS p y)) =
      F.map φ.op ≫ (restrictToSmallEtaleFinalIso B E h S hS p hp x F).inv ≫
        (restrictToSmallEtale B E h S hS p hp x F).map
          ((SmallEtale.finalIsTerminal E (p.obj x).left.1
            (contains_base B E h S hS p x)).from
              ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
                (smallEtaleFinal B E h S hS p y))).op := by
  rw [restrictToSmallEtaleFinalIso_inv, restrictToSmallEtaleFinalIso_inv,
    restrictToSmallEtaleEval_comp_map, restrictionPushforwardComparison_app_eval]

variable (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **The module comparison of Stacks 06WC is restriction along the arrow, on sections.** The
module form of `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval`: on sections
the comparison of a presheaf of modules is the comparison of Stacks 06W2 for the underlying
abelian presheaf, by `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app`. -/
theorem restrictModulePushforwardComparison_app_eval
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) (φ : x ⟶ y)
    (W : SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y))
    (n : F.presheaf.obj (op y)) :
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app (op W)
        (restrictToSmallEtaleEval B E h S hS p hp y F.presheaf W n) =
      restrictToSmallEtaleEval B E h S hS p hp x F.presheaf
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)
        (F.presheaf.map φ.op n) := by
  exact ConcreteCategory.congr_hom
    (restrictionPushforwardComparison_app_eval B E h S hS p hp F.presheaf φ W) n

/-- **Stacks 075D (1) for the module comparison of Stacks 06WC, through the evaluation maps.**
The module form of `AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval_comp`. -/
@[stacks 075D "part (1), for the direct-image comparison of a presheaf of modules read through \
the evaluation maps of the restriction of Stacks 06W1"]
theorem restrictModulePushforwardComparison_app_eval_comp
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (φ : x ⟶ y) (ψ : y ⟶ z)
    (W : SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z))
    (n : F.presheaf.obj (op z)) :
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F).app
        (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W))
        ((restrictModulePushforwardComparison B E h S hS p hp ψ τ hτ F).app (op W)
          (restrictToSmallEtaleEval B E h S hS p hp z F.presheaf W n)) =
      restrictToSmallEtaleEval B E h S hS p hp x F.presheaf
        ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj
          ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ)).obj W))
        (F.presheaf.map (φ ≫ ψ).op n) := by
  exact ConcreteCategory.congr_hom
    (restrictionPushforwardComparison_app_eval_comp B E h S hS p hp F.presheaf φ ψ W) n

end AlgebraicGeometry.Stack

end

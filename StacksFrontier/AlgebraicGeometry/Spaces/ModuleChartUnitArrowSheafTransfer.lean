module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitChain
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardCompIsoSheafTransfer

/-!
# The unit factor of the first arrow of Stacks 03M8 under the sheaf-of-sets functor

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `τ : U ⟶ X` be étale, and write `𝒱` for
`CategoryTheory.Sheaf.moduleSheafFunctor` at the structure sheaf.  The first arrow
`f_*F ⟶ a_*(F|_U)` of the sequence of Stacks 03M8, for `a = τ ≫ f`, is
`AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow`: the direct image along `f` of the
unit of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at `τ`, followed by the
composition comparison of Stacks 03LU.  Reading it on underlying sheaves of sets, so that the
sequence of `𝒪`-modules can be compared with the sequence of sheaves of sets of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean`, means reading
each of its two factors there.

The comparison factor is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean`).  This file
supplies the **unit factor**:

`𝒱.map ((modulePushforward f).map ((etaleModulePullbackAdjunction τ hτ).unit.app F))
  = (smallEtaleDirectImage f).map (moduleSheafRestrictionUnitApp τ hτ F)`.

The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean` record that
clause as going through only with the inner arrow's type pinned by a `show`; this file names the
pinned arrow instead, which is what makes the clause an ordinary `congrArg` and keeps the pin out
of every statement downstream.

## Main definitions

* `AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`: **the unit of étale restriction of
  sheaves of sets at the sheaf of sets underlying an `𝒪_X`-module**, with its type written as
  `𝒱F ⟶ 𝒱(τ_*(F|_U))` rather than as `(𝟭 _).obj (𝒱F) ⟶ (τ^* ⋙ τ_*).obj (𝒱F)`.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_eq`:
  the comparison of the two units of étale restriction, read at that name.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map_unit_app`: **the unit
  factor of the first arrow of Stacks 03M8 on underlying sheaves of sets** — the direct image
  along `f` of the unit of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at `τ` is the
  direct image along `f` of the unit of
  `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`.

## Implementation notes

**Why the unit is given a name.**  The comparison of the two units is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`
(`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitChain.lean`), and the factor wanted
here is its image under the direct image along `f`, so an ordinary `congrArg`.  What stands in
the way is that `(smallEtaleSetRestrictionAdjunction τ hτ).unit.app (𝒱F)` is typed through the
small étale site, as `(𝟭 _).obj (𝒱F) ⟶ (smallEtaleSetRestriction τ hτ ⋙ smallEtaleDirectImage
τ).obj (𝒱F)`, while the left-hand side's arrow is typed through `𝒱`, as
`𝒱F ⟶ 𝒱((modulePushforward τ).obj (F|_U))`; the two are definitionally equal, and reconciling
them inside the implicit object arguments of `(smallEtaleDirectImage f).map` does not terminate.
Stated with the set-level arrow passed raw, the clause reports

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been
reached`

in the *statement*, before any proof is attempted.
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp` below is that arrow with its declared
type the `𝒱`-spelling, so the reconciliation happens once,
in the body of a definition, on the `Hom` type alone; every statement here then names objects in
one spelling only and the clause is a `congrArg`.  This is the discipline of
`AlgebraicGeometry.Space.modulePullbackUnitApp`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationTriangle.lean`), applied on
the sheaf-of-sets side.

Nothing here raises a compiler limit or disables a linter.

## What is not done

**The first arrow itself is not assembled**, and what is missing is now a single spelling
identification, with both factors in hand.  Writing `P` for `𝒱F`, the set-level first arrow
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` is by definition

`(smallEtaleDirectImage f).map ((smallEtaleSetRestrictionAdjunction τ hτ).unit.app P) ≫
  (smallEtaleDirectImageCompIso τ f).hom.app ((smallEtaleSetRestriction τ hτ).obj P)`

and the two results above give the same composite with its two factors spelled through `𝒱`, so
all that is left is that these two composites are equal — which they are by `Eq.refl`, both
factors being the same terms with their implicit object arguments spelled differently.  That
`rfl` is where the obstruction now sits: stated on sheaves it reports

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been
reached`

and the same `rfl` stated on a single local section — the manoeuvre that dissolved the
comparison factor, see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardCompIsoSheafTransfer.lean` — does not
help, because the two sides' *result* type carries the same reconciliation. Without the named
arrow it is worse: with the set-level unit passed raw
the first factor cannot be stated at all (the timeout quoted in the implementation notes above),
stating the whole first arrow in one `show` reports `(deterministic) timeout at 'isDefEq'`, and
the section-level form of either diverges in the same way.

The candidate not tried is to give the *composite* a name as well, in the manner of
`AlgebraicGeometry.Space.restrictionUnitArrow`: a set-level first arrow whose declared type is
the `𝒱`-spelling, together with the one `rfl` identifying it with
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` proved in a declaration that does nothing
else, so that the reconciliation is spent once rather than inside a composite.

## References

* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y U : AlgebraicSpaces B S hS}

/-! ### The unit of étale restriction of sheaves of sets, in the module spelling -/

/-- **The unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the sheaf of
sets underlying an `𝒪_X`-module**, with its type written as `𝒱F ⟶ 𝒱(τ_*(F|_U))` rather than as
`(𝟭 _).obj (𝒱F) ⟶ (τ^* ⋙ τ_*).obj (𝒱F)`.

The two spellings are definitionally equal — by
`AlgebraicGeometry.Space.moduleSheaf_modulePushforward` and
`AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback`, both `Eq.refl` — and the `𝒱` one is
the spelling the image under `𝒱` of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` carries.  Naming the arrow confines the
identification to this definition's body; passing the arrow raw makes the clauses below
unstateable, as this file's implementation notes record. -/
def moduleSheafRestrictionUnitApp (τ : U ⟶ X) (hτ : IsEtale B S hS τ.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F ⟶
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj
        ((modulePushforward B S hS τ).obj
          ((etaleModulePullback.{u, u} B S hS τ hτ).obj F)) :=
  (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).obj F)

/-- **The comparison of the two units of étale restriction, at the name
`AlgebraicGeometry.Space.moduleSheafRestrictionUnitApp`.**  The sheaf of sets underlying the unit
`F ⟶ τ_*(F|_U)` of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`.

It is `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`,
which crosses between the two spellings of the target; this restatement is a declaration of its
own so that the crossing is spent here and nowhere else. -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_eq (τ : U ⟶ X)
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F) =
      moduleSheafRestrictionUnitApp B S hS τ hτ F :=
  moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app B S hS τ hτ F

/-! ### The unit factor of the first arrow of Stacks 03M8 -/

/-- **The unit factor of the first arrow `f_*F ⟶ a_*(F|_U)` of Stacks 03M8, on underlying
sheaves of sets.**  The direct image along `f` of the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` at `τ` is, on underlying sheaves of sets,
the direct image along `f` of the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at the sheaf of sets underlying `F`.

Together with
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardCompIso_hom_app` this reads both
factors of `AlgebraicGeometry.Space.moduleChartDirectImageUnitArrow` on underlying sheaves of
sets; what still separates their composite from
`AlgebraicGeometry.Space.chartDirectImageUnitArrow` is one spelling identification, described in
this file's "What is not done".

That the direct image of modules is the direct image of sheaves of sets on the underlying sheaves
is `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map`, which holds by `rfl`;
so this is the previous comparison under `(smallEtaleDirectImage f).map`. -/
theorem moduleSheafFunctor_map_modulePushforward_map_unit_app (f : X ⟶ Y) {τ : U ⟶ X}
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS Y)).map
        ((modulePushforward B S hS f).map
          ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F)) =
      (smallEtaleDirectImage B S hS f).map (moduleSheafRestrictionUnitApp B S hS τ hτ F) :=
  congrArg (smallEtaleDirectImage B S hS f).map
    (moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_eq B S hS τ hτ F)

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# The unit of étale restriction, read on the sections over a chart

Let `j : V ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `F` be an `𝒪_X`-module.  Restriction of modules along `j` is plain
restriction along postcomposition of charts, `AlgebraicGeometry.Space.etaleModulePullback`
(Stacks 03LV), and it is left adjoint to the direct image,
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` (Stacks 03LU).  This file reads the unit

`η : F ⟶ j_*(F|_V)`

of that adjunction on the sections over a chart of `X` which comes from a chart of `V`: over such
a chart the unit is **injective**, and consequently a section of `F` killed by the unit over a
chart `W` of `X` restricts to zero on every chart of `X` that factors through `V`.

That last statement is the input that identifies, for an *open* immersion `j` with point set the
complement of a closed subset `T ⊆ |X|`, the kernel of the unit with the sections supported on
`T`: a section is supported on `T` exactly when it dies on the part of its chart lying over
`Tᶜ`, and the complement is covered by charts factoring through `V`.  It is the space-level
counterpart of the scheme-level
`AlgebraicGeometry.Scheme.Modules.mem_supportedSectionsSubmodule_compl_iff_unit_app_eq_zero`,
in the direction a consumer needs.

## Main results

* `AlgebraicGeometry.Space.injective_etaleModulePullbackAdjunction_unit_val_app`: the unit of
  Stacks 03LU for an étale `j : V ⟶ X` is injective on the sections over a chart of `X` of the
  form `Φ U` for `U` a chart of `V`, where `Φ` is the postcomposition functor
  `AlgebraicGeometry.Space.smallEtalePostcomp`.
* `AlgebraicGeometry.Space.restrict_eq_zero_of_etaleModulePullbackAdjunction_unit_eq_zero`: a
  section of `F` over a chart `W` of `X` killed by the unit restricts to zero along every
  morphism of charts `Φ U ⟶ W` with `U` a chart of `V`.
* `AlgebraicGeometry.Space.injective_map_unit_val_app` and
  `AlgebraicGeometry.Space.eq_zero_of_unit_val_app_eq_zero_of_injective`: the two steps carried
  out for an arbitrary adjunction between categories of modules on algebraic spaces, which is
  where the triangle identity and the naturality of the unit are used.

## Implementation notes

**Why injectivity rather than the full kernel description.**  The forward implication — that a
section supported on `T` *is* killed by the unit — is not needed by the consumer of this file:
in the universal property of the supported-sections quotient
(`StacksFrontier/AlgebraicGeometry/Spaces/StrictTransformUniversalProperty.lean`) the hypothesis
`AlgebraicGeometry.Space.supportedSectionsInclusion_comp_eq_zero` already supplies it from the
target having no supported sections.  What that file's
`AlgebraicGeometry.Space.KernelSectionsSupportedIn` asks for is exactly the direction proved
here.

**The triangle identity is what makes it work, and it needs no hypothesis on `j`.**  The left
triangle identity of the adjunction says `(F|_V ⟶ (j_*(F|_V))|_V ⟶ F|_V)` is the identity.  Over
a chart `U` of `V` the first map is the unit over the composite chart `Φ U` of `X`, because étale
restriction of a morphism of modules is that morphism read over the composite chart,
`AlgebraicGeometry.Space.etaleModulePullback_map_val_app`, and the sections of an étale
restriction over `U` are the sections of the original module over `Φ U`,
`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj` — both `rfl`.  So the unit over `Φ U`
has a left inverse on sections.  No étaleness beyond what defines `Φ` is used, and in
particular no open-immersion hypothesis.

**Why the arithmetic of the proof is split off into lemmas about an arbitrary adjunction.**  The
terms `etaleModulePullbackAdjunction B S hS j hj` and its unit and counit are large, and
elaborating a definitional identity between two spellings of a map of sections built from them
exceeds the heartbeat ceiling at `whnf`.  Every such identity is therefore proved once, with the
adjunction, the functors and the modules opaque local hypotheses, and only then instantiated;
instantiation is substitution and costs nothing.  For the same reason
`AlgebraicGeometry.Space.eq_zero_of_unit_val_app_eq_zero_of_injective` takes the injectivity
hypothesis *before* the morphism of charts: that way the chart over which injectivity is needed
is read off the hypothesis by first-order matching rather than compared to a chart already fixed
by the morphism, which is the comparison that does not elaborate.

The module universe is `u`, the universe of the schemes, which is the one at which
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is available.

No `@[stacks]` attribute is carried: neither statement is an assertion of a numbered result.
They are the reading on sections of the unit of Stacks 03LU, whose own tag sits on
`AlgebraicGeometry.Space.modulePullbackAdjunction`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Sections of a morphism of modules -/

section Sections

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}

/-- Two equal morphisms of `𝒪_Y`-modules agree on every local section. -/
theorem modulesHom_val_app_congr {M N : Modules.{u, u} B S hS Y hY} {f g : M ⟶ N} (h : f = g)
    (W : (SmallEtale B S hS Y)ᵒᵖ) (x : M.val.obj W) :
    f.val.app W x = g.val.app W x := by rw [h]

/-- A composite of morphisms of `𝒪_Y`-modules acts on a local section as the composite of the
two actions. -/
theorem modulesHom_comp_val_app_apply {M N P : Modules.{u, u} B S hS Y hY} (f : M ⟶ N)
    (g : N ⟶ P) (W : (SmallEtale B S hS Y)ᵒᵖ) (x : M.val.obj W) :
    (f ≫ g).val.app W x = g.val.app W (f.val.app W x) := rfl

/-- The identity morphism of an `𝒪_Y`-module fixes every local section. -/
theorem modulesHom_id_val_app_apply {M : Modules.{u, u} B S hS Y hY}
    (W : (SmallEtale B S hS Y)ᵒᵖ) (x : M.val.obj W) :
    (𝟙 M : M ⟶ M).val.app W x = x := rfl

/-- A morphism of `𝒪_Y`-modules kills every restriction of a section it kills: this is
naturality of the morphism, read on sections. -/
theorem val_app_map_eq_zero {M N : Modules.{u, u} B S hS Y hY} (φ : M ⟶ N)
    {W W' : (SmallEtale B S hS Y)ᵒᵖ} (m : W ⟶ W') (s : M.val.obj W)
    (hs : φ.val.app W s = 0) : φ.val.app W' (M.val.map m s) = 0 :=
  (PresheafOfModules.naturality_apply φ.val m s).trans
    ((congrArg (fun y => N.val.map m y) hs).trans (map_zero _))

end Sections

/-! ### The unit of an arbitrary adjunction, on sections -/

section Adjunction

variable {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
    {hZ : IsAlgebraicSpace B S hS Z}
    {L : Modules.{u, u} B S hS Y hY ⥤ Modules.{u, u} B S hS Z hZ}
    {R : Modules.{u, u} B S hS Z hZ ⥤ Modules.{u, u} B S hS Y hY}

/-- **The left adjoint of the unit is injective on sections.**  For an adjunction `L ⊣ R`
between categories of modules on algebraic spaces over `S`, the morphism `L(η_F)` obtained by
applying the left adjoint to the unit at `F` is injective on the sections over every chart.

This is the left triangle identity `L(η_F) ≫ ε_{L F} = 𝟙` read on sections: the counit provides
a left inverse. -/
theorem injective_map_unit_val_app (adj : L ⊣ R) (F : Modules.{u, u} B S hS Y hY)
    (U : (SmallEtale B S hS Z)ᵒᵖ) :
    Function.Injective ((L.map (adj.unit.app F)).val.app U) := by
  have key : ∀ x, (adj.counit.app (L.obj F)).val.app U
      ((L.map (adj.unit.app F)).val.app U x) = x := fun x =>
    (modulesHom_comp_val_app_apply (L.map (adj.unit.app F))
        (adj.counit.app (L.obj F)) U x).symm.trans
      ((modulesHom_val_app_congr (adj.left_triangle_components F) U x).trans
        (modulesHom_id_val_app_apply U x))
  exact fun a b hab => (key a).symm.trans ((congrArg _ hab).trans (key b))

/-- **A section killed by the unit restricts to zero wherever the unit is injective.**  If the
unit of `L ⊣ R` at `F` kills a section `s` of `F` over a chart `W`, and the unit is injective on
the sections over a chart `W'`, then `s` restricts to zero along every morphism `W ⟶ W'` of
charts.

Naturality of the unit carries the hypothesis to `W'`, where injectivity concludes. -/
theorem eq_zero_of_unit_val_app_eq_zero_of_injective (adj : L ⊣ R)
    (F : Modules.{u, u} B S hS Y hY) {W' : (SmallEtale B S hS Y)ᵒᵖ}
    (hinj : Function.Injective ((adj.unit.app F).val.app W'))
    {W : (SmallEtale B S hS Y)ᵒᵖ} (m : W ⟶ W') (s : F.val.obj W)
    (hs : (adj.unit.app F).val.app W s = 0) :
    F.val.map m s = (0 : F.val.obj W') :=
  hinj ((val_app_map_eq_zero (adj.unit.app F) m s hs).trans (map_zero _).symm)

end Adjunction

/-! ### The unit of étale restriction -/

section Etale

variable {V X : AlgebraicSpaces B S hS}

/-- **The unit of Stacks 03LU for an étale morphism is injective on the sections over a chart
pulled back from the source.**  Let `j : V ⟶ X` be an étale morphism of algebraic spaces and let
`F` be an `𝒪_X`-module.  For every chart `U` of `V` the unit `F ⟶ j_*(F|_V)` is injective on the
sections of `F` over the composite chart `Φ U` of `X`.

The sections of `F|_V` over `U` *are* the sections of `F` over `Φ U`
(`AlgebraicGeometry.Space.etaleModulePullback_obj_val_obj`), and under that identification the
restriction of the unit to `V`, read over `U`, *is* the unit read over `Φ U`
(`AlgebraicGeometry.Space.etaleModulePullback_map_val_app`); so this is
`AlgebraicGeometry.Space.injective_map_unit_val_app` for the adjunction of Stacks 03LU. -/
theorem injective_etaleModulePullbackAdjunction_unit_val_app (j : V ⟶ X)
    (hj : IsEtale B S hS j.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (U : SmallEtale B S hS V.1) :
    Function.Injective
      (((etaleModulePullbackAdjunction B S hS j hj).unit.app F).val.app
        (op ((smallEtalePostcomp B S hS j hj).obj U))) :=
  injective_map_unit_val_app (etaleModulePullbackAdjunction B S hS j hj) F (op U)

/-- **A section killed by the unit of Stacks 03LU dies on every chart factoring through the
source.**  Let `j : V ⟶ X` be an étale morphism of algebraic spaces, let `F` be an
`𝒪_X`-module, and let `s` be a section of `F` over a chart `W` of `X` which the unit
`F ⟶ j_*(F|_V)` kills.  Then `s` restricts to zero along every morphism of charts
`Φ U ⟶ W` with `U` a chart of `V`.

This is the input that identifies the kernel of the unit with the supported sections of
Stacks 0859 when `j` is the inclusion of the open subspace with point set the complement of a
closed subset. -/
theorem restrict_eq_zero_of_etaleModulePullbackAdjunction_unit_eq_zero (j : V ⟶ X)
    (hj : IsEtale B S hS j.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (W : SmallEtale B S hS X.1) (s : F.val.obj (op W))
    (hs : ((etaleModulePullbackAdjunction B S hS j hj).unit.app F).val.app (op W) s = 0)
    (U : SmallEtale B S hS V.1) (m : (smallEtalePostcomp B S hS j hj).obj U ⟶ W) :
    F.val.map m.op s = 0 :=
  eq_zero_of_unit_val_app_eq_zero_of_injective (etaleModulePullbackAdjunction B S hS j hj) F
    (injective_etaleModulePullbackAdjunction_unit_val_app j hj F U) m.op s hs

end Etale

end AlgebraicGeometry.Space

end

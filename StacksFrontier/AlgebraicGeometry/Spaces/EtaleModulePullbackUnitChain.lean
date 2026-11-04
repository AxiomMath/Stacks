module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepThree

/-!
# The comparison of the two units of étale restriction, assembled

Let `τ : V ⟶ W` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and write `𝒱` for `CategoryTheory.Sheaf.moduleSheafFunctor`.  Stacks 03LU and
Stacks 03LW give the adjunction `τ^* ⊣ τ_*` of `𝒪`-modules with `τ^*` étale restriction, and
Stacks 03LQ gives the corresponding adjunction for sheaves of *sets*; the two units are maps
`F ⟶ τ_*(F|_V)`, and the sheaf of sets underlying the first ought to be the second.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` reduce that to
four steps.  All four are now proved: steps 1 and 4 there, step 2 in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepTwo.lean` and step 3 in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepThree.lean`.

This file joins them, and the comparison is reached:
`AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app` is the
assertion that the sheaf of sets underlying the unit of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`.

## Main results

* `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_homEquiv` is
  step 2 with the sheaf of rings written as `AlgebraicGeometry.Space.structureRingSheaf`, which
  is the spelling step 1 uses.
* `AlgebraicGeometry.Space.homEquiv_pullbackScalarUnit_comp` is naturality of the transpose at
  the change-of-rings map and the identification of Stacks 03LW.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv`:
  **the unit of étale restriction of modules, on underlying sheaves of sets, is the transpose of
  the change-of-rings map followed by the identification of Stacks 03LW.**  This is steps 1
  and 2 joined.
* `AlgebraicGeometry.Space.homEquiv_toToposHom_adj_eq_smallToposMorphismTypeU_adj`: the
  adjunction of small étale topoi underlying the morphism of ringed topoi of Stacks 03G8 is the
  morphism of small étale topoi of Stacks 03G2, part (3) — the two spellings that steps 2 and 3
  on the one hand and step 4 on the other are stated for.  It holds by `Eq.refl`.
* `AlgebraicGeometry.Space.homEquiv_pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback`
  is step 3 carried under the transpose.
* `moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv_inverseImageIso`:
  the unit of étale restriction of modules, on underlying sheaves of sets, is the transpose of
  the comparison of Stacks 03LQ.  This is steps 1, 2 and 3.
* `AlgebraicGeometry.Space.homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app_moduleSheaf`
  is step 4 in the adjunction spelling of steps 2 and 3.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app`: **the
  sheaf of sets underlying the unit of étale restriction of `𝒪`-modules is the unit of étale
  restriction of sheaves of sets.**  This is the comparison the four steps are for.

## Implementation notes

Step 2 is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepTwo.lean` in the ringed-topos
spelling of the structure sheaf, for the reasons that file's implementation notes give;
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_homEquiv` is
the same statement in the `AlgebraicGeometry.Space` spelling, and crossing between the two is
affordable **only** in a declaration that does nothing else.  That is why it is a declaration of
its own even though its proof is a single application.

**Two identifications of one sheaf of sets are in play, and no declaration can afford to spend
either of them twice.**  They are
`𝒱(τ_*N) = τ_*(𝒱N)` for the direct image and `𝒱(F|_V) = (𝒱F)|_{V_étale}` for the restriction,
both `Eq.refl` (`AlgebraicGeometry.Space.moduleSheaf_modulePushforward` and
`AlgebraicGeometry.Space.moduleSheaf_etaleModulePullback`).  The statement of the comparison
spends both: its left-hand side is typed through `𝒱` and its right-hand side through the small
étale site.  So the two halves of the join have to meet at a *syntactically* common type, and
they do not do so on their own: the transpose's second object argument, left implicit, is
determined by its argument — the composite of step 3 types it as `𝒱(F|_V)` and the comparison of
Stacks 03LQ types it as `(𝒱F)|_{V_étale}` — so `Eq.trans` of the two halves spends the
restriction identification a second time and reports

`error: (deterministic) timeout at 'whnf', maximum number of heartbeats (200000) has been reached`

(and `at 'isDefEq'` with the halves chained in the other grouping).  The halves below therefore
*pin* that argument, both of them in the `𝒱(F|_V)` spelling, which is the one the left-hand side
of the comparison already carries; then the middle terms agree syntactically, the trans spends
only the direct-image identification, and the join elaborates in seconds.  Pinning it in the
other spelling, the `(𝒱F)|_{V_étale}` one that step 4 produces, does not work: it moves the same
failure onto the join of steps 1 and 2.

Nothing here raises a compiler limit or disables a linter.

## What is not done

The comparison is of the two *units*.  One module-level consequence is not drawn here: the
hypothesis `hu` of
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackCompIsoEtaleRestriction.lean`),
which is an equality of units of two adjunctions of modules.

This section used to name a second one, the module-level reading of the sequence of Stacks 03M8,
as also waiting on this comparison.  It is not waiting on it.  That sequence is a complex by
`AlgebraicGeometry.Space.moduleChartDirectImage_comp_sub_eq_zero` and exact by
`AlgebraicGeometry.Space.exact_moduleChartDirectImage`, which carries the attribute for
Tag 03M8, both in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationExactSequence.lean` and
neither conditional; they are proved by reflecting a limiting fork of sheaves of sets back to
modules, a route on which this comparison does not appear.  What
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean` measures is the
*other* route to the complex law, the one through this comparison, and that route's remaining
obstruction is a kernel timeout on the Stacks 03LU composition comparison rather than anything
owed by this file.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraEssentiallySmall

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W : AlgebraicSpaces B S hS} (τ : V ⟶ W) (hτ : IsEtale B S hS τ.hom)

/-! ### Step 2 in the spelling step 1 uses -/

/-- **Step 2 of the comparison**, with the sheaf of rings written as
`AlgebraicGeometry.Space.structureRingSheaf`: the unit of the Stacks 03LU adjunction, on
underlying sheaves of sets, is the transpose of its change-of-rings half.

This is `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app`, which
is stated in the ringed-topos spelling of the structure sheaf; the two spellings are
definitionally equal, and crossing between them is affordable only in a declaration that does
nothing else, which is what this one is. -/
theorem moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_homEquiv
    (M : Modules.{u, u} B S hS W.1 W.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS W)).map
        ((modulePullbackAdjunction B S hS τ).unit.app M) =
      (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv _ _
        (pullbackScalarUnit (smallEtaleRingedToposHom B S hS τ) M) :=
  moduleSheafFunctor_map_modulePullbackAdjunction_unit_app B S hS τ M

include hτ

/-! ### Naturality of the transpose -/

/-- Naturality of the transpose of the adjunction of small étale topoi in its second variable, at
the change-of-rings half of the unit and the identification of Stacks 03LW: transposing the
change-of-rings map and then pushing the identification forward is transposing the composite.

It is `CategoryTheory.Adjunction.homEquiv_naturality_right`, and the direct image it produces is
`AlgebraicGeometry.Space.smallEtaleDirectImage` on the nose, by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward_eq`. -/
theorem homEquiv_pullbackScalarUnit_comp (F : Modules.{u, u} B S hS W.1 W.2) :
    (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv _ _
          (pullbackScalarUnit (smallEtaleRingedToposHom B S hS τ) F) ≫
        (smallEtaleDirectImage B S hS τ).map
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).map
            ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F)) =
      (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv _ _
        (pullbackScalarUnit (smallEtaleRingedToposHom B S hS τ) F ≫
          (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).map
            ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F)) :=
  ((smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv_naturality_right _ _).symm

/-! ### Steps 1 and 2 joined -/

/-- **The unit of étale restriction of modules, on underlying sheaves of sets, is the transpose
of the change-of-rings map followed by the identification of Stacks 03LW.**  For an étale
`τ : V ⟶ W` and an `𝒪_W`-module `F`, the sheaf of sets underlying the unit `F ⟶ τ_*(F|_V)` of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the adjunct, across the adjunction
`τ⁻¹ ⊣ τ_*` of small étale topoi, of the map `x ↦ 1 ⊗ x` from `τ⁻¹(𝒱F)` to the pullback of
modules followed by the sheaf of sets underlying Stacks' Equation 03LW.

This is steps 1 and 2 of the comparison of that unit with the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`, joined by naturality of the
transpose: step 1 is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_comp`,
step 2 is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_homEquiv` and
naturality is `AlgebraicGeometry.Space.homEquiv_pullbackScalarUnit_comp`.  By step 3,
`AlgebraicGeometry.Space.pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback`, the
transposed composite is the comparison of Stacks 03LQ, and by step 4 its transpose is the unit
for sheaves of sets; joining those two to this is where the budget runs out, and the measurement
is in this file's "What is not done". -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS W)).map
        ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F) =
      (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv _ _
        (pullbackScalarUnit (smallEtaleRingedToposHom B S hS τ) F ≫
          (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).map
            ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F)) :=
  ((moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_comp B S hS τ hτ F).trans
    (congrArg
      (fun k ↦ k ≫ (smallEtaleDirectImage B S hS τ).map
        ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).map
          ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F)))
      (moduleSheafFunctor_map_modulePullbackAdjunction_unit_app_homEquiv B S hS τ F))).trans
    (homEquiv_pullbackScalarUnit_comp B S hS τ hτ F)

/-! ### The two spellings of the adjunction of small étale topoi -/

/-- The adjunction `τ⁻¹ ⊣ τ_*` underlying the morphism of small étale *ringed* topoi of
Stacks 03G8, through which steps 2 and 3 are stated, is the one of the morphism of small étale
topoi of Stacks 03G2, part (3), through which step 4 is stated.  It holds by `Eq.refl`, by
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_toToposHom`.

It is recorded at the comparison of Stacks 03LQ, which is the argument the two transposes are
applied to in the chain. -/
theorem homEquiv_toToposHom_adj_eq_smallToposMorphismTypeU_adj
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv
          (moduleSetSheaf B S hS W F)
          ((smallEtaleSetRestriction B S hS τ hτ).obj (moduleSetSheaf B S hS W F))
        ((smallToposMorphismTypeU_inverseImageIso B S hS τ hτ).hom.app
          (moduleSetSheaf B S hS W F)) =
      (smallToposMorphismTypeU B S hS τ).adj.homEquiv _ _
        ((smallToposMorphismTypeU_inverseImageIso B S hS τ hτ).hom.app
          (moduleSetSheaf B S hS W F)) := rfl

/-! ### Step 3 under the transpose -/

/-- **Step 3 carried under the transpose**: the transpose of the change-of-rings map followed by
the identification of Stacks 03LW is the transpose of the comparison of Stacks 03LQ.

It is step 3, `pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback`, under `congrArg`.
The two sides of step 3 carry the two readings of one sheaf of sets — the target of the composite
is `𝒱(F|_V)` and the target of the comparison of Stacks 03LQ is `(𝒱F)|_{V_étale}` — so this
declaration spends that identification, and does nothing else. -/
theorem homEquiv_pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv _ _
        (pullbackScalarUnit (smallEtaleRingedToposHom B S hS τ) F ≫
          (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).map
            ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F)) =
      (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv _ _
        ((smallToposMorphismTypeU_inverseImageIso B S hS τ hτ).hom.app
          (moduleSetSheaf B S hS W F)) :=
  congrArg _ (pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback B S hS τ hτ F)

/-! ### The two halves of the comparison, at a common spelling of the transpose -/

/-- **The unit of étale restriction of modules, on underlying sheaves of sets, is the transpose
of the comparison of Stacks 03LQ.**  For an étale `τ : V ⟶ W` and an `𝒪_W`-module `F`, the sheaf
of sets underlying the unit `F ⟶ τ_*(F|_V)` of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the adjunct, across the adjunction
`τ⁻¹ ⊣ τ_*` of small étale topoi, of the canonical map `τ⁻¹(𝒱F) ⟶ (𝒱F)|_{V_étale}` of
Stacks 03LQ.

This is steps 1, 2 and 3 of the comparison: the join of steps 1 and 2,
`AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv`,
followed by step 3 under the transpose.  The second object argument of the transpose is pinned in
the `𝒱(F|_V)` spelling, which is the one the left-hand side carries; see this file's
implementation notes. -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv_inverseImageIso
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS W)).map
        ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F) =
      (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv
          (moduleSetSheaf B S hS W F)
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).obj
            ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))
        ((smallToposMorphismTypeU_inverseImageIso B S hS τ hτ).hom.app
          (moduleSetSheaf B S hS W F)) :=
  (moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv B S hS τ hτ F).trans
    (homEquiv_pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback B S hS τ hτ F)

/-- **Step 4 at the spelling steps 2 and 3 are stated in**: the adjunct of the comparison of
Stacks 03LQ, across the adjunction of small étale topoi underlying the morphism of ringed topoi
of Stacks 03G8 and with the target of the transpose written as the sheaf of sets underlying
`F|_V`, is the unit of `AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`.

It is `AlgebraicGeometry.Space.homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app`, which
is uniqueness of a left adjoint, after
`AlgebraicGeometry.Space.homEquiv_toToposHom_adj_eq_smallToposMorphismTypeU_adj`, which
identifies the two adjunctions. -/
theorem homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app_moduleSheaf
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (smallEtaleRingedToposHom B S hS τ).toToposHom.adj.homEquiv
          (moduleSetSheaf B S hS W F)
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS V)).obj
            ((etaleModulePullback.{u, u} B S hS τ hτ).obj F))
        ((smallToposMorphismTypeU_inverseImageIso B S hS τ hτ).hom.app
          (moduleSetSheaf B S hS W F)) =
      (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app
        (moduleSetSheaf B S hS W F) :=
  (homEquiv_toToposHom_adj_eq_smallToposMorphismTypeU_adj B S hS τ hτ F).trans
    (homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app B S hS τ hτ
      (moduleSetSheaf B S hS W F))

/-! ### The comparison -/

/-- **The sheaf of sets underlying the unit of étale restriction of `𝒪`-modules is the unit of
étale restriction of sheaves of sets.**  For an étale morphism `τ : V ⟶ W` of algebraic spaces
and an `𝒪_W`-module `F`, the image under
`CategoryTheory.Sheaf.moduleSheafFunctor` of the unit `F ⟶ τ_*(F|_V)` of
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` — the adjunction of Stacks 03LU read
through the identification of Stacks 03LW — is the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`, the adjunction of Stacks 03LQ and
03G2, part (1), at the sheaf of sets underlying `F`.

Both units are maps `F ⟶ τ_*(F|_V)`, the first of `𝒪_W`-modules and the second of sheaves of
sets on the small étale site of `W`, and this says that the first is the second: étale
restriction of modules introduces no twist over étale restriction of sheaves of sets, and the
`𝒪`-module structure is carried along for free.

It is the four steps of the comparison, joined: steps 1, 2 and 3 are
`moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv_inverseImageIso`
and step 4 is
`AlgebraicGeometry.Space.homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app_moduleSheaf`. -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1} (structureRingSheaf B S hS W)).map
        ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F) =
      (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app
        (moduleSetSheaf B S hS W F) :=
  (moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_homEquiv_inverseImageIso
      B S hS τ hτ F).trans
    (homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app_moduleSheaf B S hS τ hτ F)

end AlgebraicGeometry.Space

end

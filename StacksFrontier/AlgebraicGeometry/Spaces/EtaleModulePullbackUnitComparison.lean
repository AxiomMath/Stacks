module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInverseImageIsoComp

/-!
# The unit of étale restriction of modules against the unit for sheaves of sets

Let `τ : U ⟶ X` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 03LU gives the adjunction `τ^* ⊣ τ_*` of `𝒪`-modules and Stacks 03LW
identifies `τ^*` with étale restriction, so
`AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is an adjunction between étale
restriction of modules and the direct image.  Stacks 03LQ gives the corresponding adjunction
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` for sheaves of *sets* at the
universe of the structure rings.  Both units are maps `F ⟶ τ_*(F|_U)`, the first in `Mod(𝒪_X)`
and the second in the small étale topos of `X`, and the sheaf of sets underlying the first ought
to be the second.

That comparison is what the hypothesis `hu` of
`AlgebraicGeometry.Space.modulePullbackCompIsoEtaleRestriction_of_unit` needs.  This file
supplies the two steps of it that are about *adjunctions* rather than about identifying two
spellings of one sheaf; see "What the comparison needs, and where each step is" for the other
two steps.

The module-level reading of the sequence of Stacks 03M8 does not need the comparison: that sequence
is a complex by `AlgebraicGeometry.Space.moduleChartDirectImage_comp_sub_eq_zero` and exact by
`AlgebraicGeometry.Space.exact_moduleChartDirectImage`, which carries the attribute for
Tag 03M8, both unconditional and both proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationExactSequence.lean` by
reflecting a limiting fork of sheaves of sets back to modules — a route on which this comparison
does not appear.  The comparison is needed only by the alternative route to the complex law that
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardPresentationArrows.lean` describes.

## Main results

* `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app`: the unit of étale
  restriction of modules is the unit of the Stacks 03LU adjunction followed by the direct image
  of the identification of Stacks 03LW.  It holds by `Eq.refl`, the first adjunction being the
  second transported along that identification.
* `AlgebraicGeometry.Space.homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app`: **the
  transpose of the comparison of Stacks 03LQ is the unit of the étale restriction adjunction for
  sheaves of sets.**  This is uniqueness of a left adjoint and nothing else, and it is the step
  that makes the comparison a formal consequence rather than a computation.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_comp`:
  the unit of étale restriction of modules, on underlying sheaves of sets, split into the unit of
  Stacks 03LU and the direct image of the identification of Stacks 03LW.
* `CategoryTheory.map_hom_app_of_eq_trans`: the image under a functor of a component of an
  isomorphism presented as a composite of two isomorphisms.  The factorization is a hypothesis
  rather than something matched against the definition of the isomorphism, which is what makes it
  usable at the concrete comparisons of Stacks 03LU: the factorization of those is affordable as
  an equality of *isomorphisms* — `AlgebraicGeometry.Space.modulePushforwardIso_eq` — and not as
  an equality of their components, where the composition instance of a category of sheaves of
  modules has to be identified.

## Implementation notes

The route is uniqueness of left adjoints, and no unit is computed by unfolding an adjunction.
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` *is*
`CategoryTheory.Adjunction.leftAdjointUniq` of the inverse image of the morphism of small étale
topoi of Stacks 03G8 and of étale restriction, so
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` identifies its transpose with the
unit of the set-level adjunction with no computation at all.  Nothing here unfolds
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`, where unfolding reaches the
heartbeat limit inside `whnf`.

**The kernel budget is per declaration**, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSpellingBridge.lean` record: each step forces
the elaborator to identify two spellings of one sheaf of sets, each identification is affordable
on its own, and a chain of them is not.  So the assembly is written as one-step declarations.
`rw` is avoided throughout: its motives are not type-correct at `instances` transparency at these
types.

Nothing in this file raises a compiler limit or disables a linter.

## What the comparison needs, and where each step is

**The comparison is not proved in this file**, which supplies two of its four steps; it is
`AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app` in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitChain.lean`, where the four are
joined.  Writing `V` for
`CategoryTheory.Sheaf.moduleSheafFunctor` at the structure sheaf, the statement wanted is

`V.map ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F)
  = (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app (moduleSetSheaf B S hS W F)`

and the chain that proves it has four steps, of which the first and the last are here:

1. `AlgebraicGeometry.Space.etaleModulePullbackAdjunction_unit_app` together with
   `CategoryTheory.Functor.map_comp` and
   `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforward_map`, which is
   `AlgebraicGeometry.Space.moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_comp`
   below;
2. that `V` of the unit of `AlgebraicGeometry.Space.modulePullbackAdjunction` is the transpose
   of `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit` — that is,
   `Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_modulesPullbackUnit`
   after dropping the comparison of the two readings of the direct image, which is the identity
   on underlying sheaves of sets by
   `AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePushforwardIso_hom_app`;
3. that `pullbackScalarUnit` followed by `V` of the identification of Stacks 03LW is the
   comparison of Stacks 03LQ at the underlying sheaf of sets — which on *sections* is exactly
   `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`;
4. `CategoryTheory.Adjunction.homEquiv_naturality_right` and
   `AlgebraicGeometry.Space.homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app` below.

Steps 2 and 3, each of which is a single identification of two spellings of one sheaf of sets,
are proved in `StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepTwo.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepThree.lean`, each in
declarations of its own, since a chain of such identifications exceeds the heartbeat limit.  In
the same way, splitting either comparison of direct images of Stacks 03LU at the level of
*morphisms* — `(modulePushforwardIso B S hS τ).hom = _ ≫ eqToHom _` by `Eq.refl`, or the same
through `CategoryTheory.NatTrans.comp_app` — reaches the limit in `whnf`, while the
corresponding equality of *isomorphisms* (`AlgebraicGeometry.Space.modulePushforwardIso_eq`) is
affordable.  That is why `CategoryTheory.map_hom_app_of_eq_trans` below takes the factorization
as a hypothesis.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraEssentiallySmall

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {CC : Type u₁} [Category.{v₁} CC] {DD : Type u₂} [Category.{v₂} DD]
  {EE : Type u₃} [Category.{v₃} EE]

/-- **The image of a component of a composite isomorphism.**  If an isomorphism `I` of functors
is the composite of `α` and `β`, then the image under `Φ` of its component at `N` is the
composite of the images of the components of `α` and of `β`.

The factorization is a hypothesis rather than something matched against the definition of `I`.
That is what makes this usable at the comparisons of direct images of Stacks 03LU, whose
factorizations are affordable as equalities of isomorphisms and not as equalities of their
components; see this file's implementation notes. -/
theorem map_hom_app_of_eq_trans {F G H : CC ⥤ DD} (I : F ≅ H) (α : F ≅ G) (β : G ≅ H)
    (hI : I = α ≪≫ β) (Φ : DD ⥤ EE) (N : CC) :
    Φ.map (I.hom.app N) = Φ.map (α.hom.app N) ≫ Φ.map (β.hom.app N) := by
  subst hI
  exact (congrArg Φ.map (NatTrans.comp_app α.hom β.hom N)).trans (Φ.map_comp _ _)

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W : AlgebraicSpaces B S hS} (τ : V ⟶ W)

/-! ### The unit of étale restriction of modules, split -/

/-- The unit of `AlgebraicGeometry.Space.etaleModulePullbackAdjunction` is the unit of the
Stacks 03LU adjunction followed by the direct image of the identification of Stacks 03LW: the
former adjunction is the latter transported along that identification, so this holds by
`Eq.refl`. -/
theorem etaleModulePullbackAdjunction_unit_app (hτ : IsEtale B S hS τ.hom)
    (F : Modules.{u, u} B S hS W.1 W.2) :
    (etaleModulePullbackAdjunction B S hS τ hτ).unit.app F =
      (modulePullbackAdjunction B S hS τ).unit.app F ≫
        (modulePushforward B S hS τ).map
          ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F) := rfl

/-- **The unit of étale restriction of modules on underlying sheaves of sets, split** into the
unit of the Stacks 03LU adjunction and the direct image of sheaves of sets of the identification
of Stacks 03LW.

This is the first of the four steps of the comparison of that unit with the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction`; see this file's "What is not
done". -/
theorem moduleSheafFunctor_map_etaleModulePullbackAdjunction_unit_app_comp
    (hτ : IsEtale B S hS τ.hom) (F : Modules.{u, u} B S hS W.1 W.2) :
    (Sheaf.moduleSheafFunctor.{u, u, u + 1}
          (AlgebraicGeometry.Space.structureRingSheaf B S hS W)).map
        ((etaleModulePullbackAdjunction B S hS τ hτ).unit.app F) =
      (Sheaf.moduleSheafFunctor.{u, u, u + 1}
            (AlgebraicGeometry.Space.structureRingSheaf B S hS W)).map
          ((modulePullbackAdjunction B S hS τ).unit.app F) ≫
        (smallEtaleDirectImage B S hS τ).map
          ((Sheaf.moduleSheafFunctor.{u, u, u + 1}
            (AlgebraicGeometry.Space.structureRingSheaf B S hS V)).map
              ((modulePullbackIsoEtaleModulePullback B S hS τ hτ).hom.app F)) :=
  (congrArg (Sheaf.moduleSheafFunctor.{u, u, u + 1}
        (AlgebraicGeometry.Space.structureRingSheaf B S hS W)).map
      (etaleModulePullbackAdjunction_unit_app B S hS τ hτ F)).trans
    ((Sheaf.moduleSheafFunctor.{u, u, u + 1}
      (AlgebraicGeometry.Space.structureRingSheaf B S hS W)).map_comp _ _)

/-! ### The set-level unit as a transpose -/

/-- **The transpose of the comparison of Stacks 03LQ is the unit of the étale restriction
adjunction for sheaves of sets.**  For an étale `τ : U ⟶ X` and a sheaf of sets `P` on the small
étale site of `X` at the universe of the structure rings, the adjunct of
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` at `P` under the adjunction
`τ⁻¹ ⊣ τ_*` of the morphism of small étale topoi of Stacks 03G8 is the unit of
`AlgebraicGeometry.Space.smallEtaleSetRestrictionAdjunction` at `P`.

The comparison is `CategoryTheory.Adjunction.leftAdjointUniq` of the two left adjoints of `τ_*`,
so this is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` and nothing else.  It is
the step that makes the comparison of the two units a formal consequence of uniqueness of left
adjoints rather than a computation with either unit. -/
theorem homEquiv_smallToposMorphismTypeU_inverseImageIso_hom_app (hτ : IsEtale B S hS τ.hom)
    (P : Sheaf (SmallEtale.topology B S hS W.1) (Type u)) :
    (smallToposMorphismTypeU B S hS τ).adj.homEquiv _ _
        ((smallToposMorphismTypeU_inverseImageIso B S hS τ hτ).hom.app P) =
      (smallEtaleSetRestrictionAdjunction B S hS τ hτ).unit.app P :=
  Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ P

end AlgebraicGeometry.Space

end

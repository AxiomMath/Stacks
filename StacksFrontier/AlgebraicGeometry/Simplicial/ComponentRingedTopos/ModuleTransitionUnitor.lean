module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensor
public import
    StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposLeftUnitorUnconditional

/-! # The unitor half of the compatibility of Stacks 09WF with Stacks 03EL

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. `CategoryTheory.SimplicialSiteSituation.TransitionUnitorCoherence` — the unitor half
of the compatibility of the pullback transition of Stacks 09WF with the comparison of
Stacks 03EL, and one of the two hypotheses of the sheaf-level residual square of Stacks 0D9E (2)
— **is proved here**, with no hypothesis.

What `ModuleTransitionTensor.lean` records as owed is the *left*-unitor coherence of Stacks 03EL
at the transition morphism of ringed topoi, in the presentation of Stacks 03LU. Both halves of
that debt are now paid elsewhere:

* the left-unitor coherence itself is
  `Stacks.Sheaves.RingedToposModules.map_tensorSheafUnitLeftIso_inv_comp_pullbackTensorIso`,
  deduced from the right-unitor coherence through the compatibility of the comparison with the
  braiding;
* the identification of the two unit comparisons is
  `Stacks.Sheaves.RingedToposModules.pullbackModulesUnitComparison_eq_inv`, which holds for an
  arbitrary morphism of ringed topoi, so no presentation of the transition morphism by a
  morphism of sites is needed.

Unlike the tensorator half, this statement mentions **one** morphism of ringed topoi — the
transition `f_φ` — and no composite: the component inclusions `g_n` and `g_m` do not appear, so
the non-invertible 2-morphism
`CategoryTheory.CocontinuousSimplicialSite.componentRingedTwoMorphism` relating `g_m` to
`g_n ∘ f_φ` is not in the way.

## Main results

* `CategoryTheory.SimplicialSiteSituation.transitionUnitorCoherence`: **the unitor half**, with
  no hypothesis.

## Implementation notes

Three identifications carry the general coherence to the simplicial spelling, and all three are
cheap once stated as `have`s ascribed at the goal's spelling.

*The transition pullback is the pullback of modules.*
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` is
`AlgebraicGeometry.RingedToposHom.pullbackModules` of the transition morphism, which is
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules` of its four-field reading by
definition, so the two functors are the same term.

*The left unitor of the component is the left unitor of the tensor product sheaf.*
`CategoryTheory.SimplicialSiteSituation.componentModuleUnitTensorLeftUnitor` is built
componentwise from `Stacks.SheafOfModules.Strict.unitTensorIso`, the left unitor of
`Stacks.SheafOfModules.Strict.monoidalCategoryRingSheaf`; that is
`Stacks.SheafOfModules.tensorSheafUnitLeftIso` by
`Stacks.SheafOfModules.Strict.unitTensorIso_eq`. Note that it is *not*
`SheafOfModules.leftUnitor_sheafTensor_eq` that applies here: that lemma is about the re-seated
`SheafOfModules.monoidalCategorySheafTensor`, a different monoidal structure from the one
`Strict.unitTensorIso` is the unitor of.

*Both substitutions are `have`s, not rewrites.* The two sides of the goal cross
`(Stacks.SheafOfModules.Tensor.ringSheaf 𝒪).property` and
`(Stacks.SheafOfModules.Tensor.ringSheaf _.O).property`, which are equal only by
proof irrelevance; a `rw` whose motive mentions one while the goal mentions the other is reported
ill-typed at the implicit transparency level. `substituteEnds` is therefore stated over an
abstract category and applied by `exact`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

section Bookkeeping

universe vv uu

/-- Substituting the two outer factors of a coherence identity whose inner factors already
match. Stated over an abstract category and applied by `exact`: the two spellings of the sheaf
condition of the structure sheaf of a component are equal only by proof irrelevance, and there a
rewrite under a motive does not typecheck. -/
private lemma substituteEnds {D : Type uu} [Category.{vv} D] {a b c e : D}
    (p p' : a ⟶ b) (q : b ⟶ c) (r r' : a ⟶ e) (s : e ⟶ c)
    (hp : p = p') (hr : r = r') (h : p' ≫ q = r' ≫ s) : p ≫ q = r ≫ s :=
  ((congrArg (fun z ↦ z ≫ q) hp).trans h).trans (congrArg (fun z ↦ z ≫ s) hr.symm)

end Bookkeeping

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent GrothendieckTopology.hasSheafify_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The inverse left unitor of a component is the inverse left unitor of the tensor product
sheaf.** `CategoryTheory.SimplicialSiteSituation.componentModuleUnitTensorLeftUnitor` is built
componentwise from `Stacks.SheafOfModules.Strict.unitTensorIso`, which is
`Stacks.SheafOfModules.tensorSheafUnitLeftIso` by
`Stacks.SheafOfModules.Strict.unitTensorIso_eq`; this is that identification with the sheaf
condition written at the `Stacks.Sheaves.RingedToposModules.structureRingSheaf` spelling the
coherence of Stacks 03EL uses. -/
theorem componentModuleUnitTensorLeftUnitor_inv_app (n : SimplexCategory)
    (X : SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :
    (S.componentModuleUnitTensorLeftUnitor O n).inv.app X =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso (S.componentRingedTopos O n).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O).property X).inv :=
  congrArg Iso.inv (Stacks.SheafOfModules.Strict.unitTensorIso_eq
    (S.componentRingedTopos O n).O X)

/-- **The left-unitor coherence of Stacks 03EL at the transition morphism**, written at the
spellings of the simplicial development: the transition pullback of Stacks 09WF in place of the
pullback of modules, and the curried tensor product of Tag 06YM.

This is
`Stacks.Sheaves.RingedToposModules.map_tensorSheafUnitLeftIso_inv_comp_pullbackTensorIso` at
`CategoryTheory.SimplicialSiteSituation.transitionRingedToposHom`; the transition pullback *is*
the pullback of modules along that morphism, by definition of both. -/
theorem transitionPullbackModules_map_tensorSheafUnitLeftIso_inv_comp
    {n m : SimplexCategory} (φ : n ⟶ m)
    (X : SheafOfModules.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :
    (S.transitionPullbackModules' O φ).map
          (Stacks.SheafOfModules.tensorSheafUnitLeftIso (S.componentRingedTopos O n).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O).property
            X).inv ≫
        (Stacks.SheafOfModules.pullbackTensorIso
            (S.transitionRingedToposHom O φ).toModulesHom).hom.app
          (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n), X) =
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso (S.componentRingedTopos O m).O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O).property
            ((S.transitionPullbackModules' O φ).obj X)).inv ≫
        ((sheafTensor (S.componentRingedTopos O m).O).map
            (pullbackModulesObjUnitIso
              (S.transitionRingedToposHom O φ).toModulesHom).hom).app
          ((S.transitionPullbackModules' O φ).obj X) :=
  map_tensorSheafUnitLeftIso_inv_comp_pullbackTensorIso
    (S.transitionRingedToposHom O φ).toModulesHom X

/-- **The unitor half of the compatibility of the pullback transition of Stacks 09WF with the
comparison of Stacks 03EL, unconditionally.** For every simplex map `phi : [n] ⟶ [m]` and every
sheaf of `O_n`-modules `X`, the pullback along `f_phi` of the inverse left unitor of the
degree-`n` component, followed by the comparison of Stacks 03EL at `f_phi`, is the inverse left
unitor of the degree-`m` component followed by the identification `O_m ≅ f_phi^*O_n` of
Stacks 03D6 in the left tensor factor.

This inhabits `CategoryTheory.SimplicialSiteSituation.TransitionUnitorCoherence`, one of the two
hypotheses of the sheaf-level residual square of Stacks 0D9E (2). -/
theorem transitionUnitorCoherence : S.TransitionUnitorCoherence O := fun {n m} φ X ↦
  substituteEnds
    ((S.transitionPullbackModules' O φ).map
      ((S.componentModuleUnitTensorLeftUnitor O n).inv.app X))
    ((S.transitionPullbackModules' O φ).map
      (Stacks.SheafOfModules.tensorSheafUnitLeftIso (S.componentRingedTopos O n).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O).property X).inv)
    ((Stacks.SheafOfModules.pullbackTensorIso
        (S.transitionRingedToposHom O φ).toModulesHom).hom.app
      (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n), X))
    ((S.componentModuleUnitTensorLeftUnitor O m).inv.app
      ((S.transitionPullbackModules' O φ).obj X))
    (Stacks.SheafOfModules.tensorSheafUnitLeftIso (S.componentRingedTopos O m).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O m).O).property
      ((S.transitionPullbackModules' O φ).obj X)).inv
    (((sheafTensor (S.componentRingedTopos O m).O).map
        (pullbackModulesObjUnitIso
          (S.transitionRingedToposHom O φ).toModulesHom).hom).app
      ((S.transitionPullbackModules' O φ).obj X))
    (congrArg (S.transitionPullbackModules' O φ).map
      (S.componentModuleUnitTensorLeftUnitor_inv_app O n X))
    (S.componentModuleUnitTensorLeftUnitor_inv_app O m ((S.transitionPullbackModules' O φ).obj X))
    (S.transitionPullbackModules_map_tensorSheafUnitLeftIso_inv_comp O φ X)

end CategoryTheory.SimplicialSiteSituation

end

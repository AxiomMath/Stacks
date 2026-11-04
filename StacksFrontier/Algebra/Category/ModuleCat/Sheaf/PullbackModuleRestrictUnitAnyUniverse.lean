module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.UliftTransport

/-!
# The inverse image of a ring sheaf viewed as a module over another, at any universes

Let `φ : O ⟶ O'` be a morphism of sheaves of commutative rings on a site, and read `O'` as a
sheaf of `O`-modules by restriction of scalars along `φ`. Its inverse image along a
finite-product-preserving functor `Φ` of sheaves of sets is `Φ O'` read as a sheaf of
`Φ O`-modules by restriction of scalars along `Φ φ`; the two have the same underlying sheaf of
sets, and the identity there is additive and compatible with the two scalar actions.

The universes of the two sites and of the sheaves are independent of each other.

## Main results

* `Stacks.Sheaves.ToposPullback.AnyUniverse.pullbackRestrictUnitIso`: the inverse image of `O'`
  read as an `O`-module is `Φ O'` read as a `Φ O`-module, by the identity on their common
  underlying sheaf of sets.

## Implementation notes

The additions and the scalar actions are compared by the same two-step reduction on each side,
through `Stacks.Sheaves.ToposPullback.moduleAddObj_pullbackModuleObj` and
`.moduleSMulObj_pullbackModuleObj`, which read an operation on an inverse image as the operation
on the original module transported through `Φ` and the sections functor, and through
`Stacks.Sheaves.RingedToposModules.moduleSMulObj_restrictScalars`, which reads the action on a
restriction of scalars as the action after pushing the scalar along the ring map. The unit module
needs no comparison of its own: by `Stacks.Sheaves.ToposPullback.pullbackModuleUnitIso` the
inverse image of the unit module *is* the unit module of the inverse-image ring.

For the scalar action the two pushed scalars have to be identified, and that is
`Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap`: on underlying
sheaves of sets the
inverse image of a morphism of sheaves of commutative rings is `Φ` of its underlying morphism.
Forgetting to sets through `RingCat` and forgetting directly agree by `rfl`, so that lemma
applies without a further comparison.

The statements are about the transported operations `CategoryTheory.Sheaf.moduleAddObj` and
`.moduleSMulObj` rather than about the operation *maps*, because the two operation maps live over
different sites and are only comparable after transport; at the level of maps the additive
identity is `rfl` but too large for the kernel to check directly.

The transporting functor is the sections functor rather than an arbitrary
finite-product-preserving functor to types. That is a cost constraint, not a mathematical one:
the proof goes through verbatim for a general such functor, but the kernel then has to
check the dependent types of the two operations against each other at that generality and times
out. The sections functor is also exactly what the consumers of these two comparisons need, since
`Stacks.Sheaves.RingedToposModules.moduleAddHom_comp_iff` and `.moduleSMulHom_comp_iff` — which
turn these into the hypotheses of
`Stacks.Sheaves.RingedToposModules.isoOfSheafIso` — are stated at it.

No `simp` normalisation intervenes when those two hypotheses are assembled: the comparison is
`Iso.refl`, and the sections functor sends an identity to an identity by `rfl`, so each
hypothesis is definitionally the bare equation of the two operations.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback.AnyUniverse

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (Φ : Sheaf K (Type w) ⥤ Sheaf J (Type w)) [PreservesFiniteProducts Φ]
  {O O' : Sheaf K CommRingCat.{w}} (φ : O ⟶ O')

/-- `O'` read as a sheaf of `O`-modules along `φ`, then pulled back along `Φ`. -/
abbrev pullbackRestrictUnitSource :
    SheafOfModules.{w} (pullbackRingSheaf J Φ (Stacks.commRingSheafToRingSheaf O)) :=
  pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O)
    ((SheafOfModules.restrictScalars
      ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ)).obj
      (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf O')))

/-- `Φ O'` read as a sheaf of `Φ O`-modules along `Φ φ`. -/
abbrev pullbackRestrictUnitTarget :
    SheafOfModules.{w} (pullbackRingSheaf J Φ (Stacks.commRingSheafToRingSheaf O)) :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
      ((pullbackCommRingSheafFunctor J Φ).map φ))).obj
    (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf (pullbackCommRingSheaf J Φ O')))

/-- **The inverse image of `O'` read as an `O`-module is `Φ O'` read as a `Φ O`-module.** The two
underlying sheaves of sets agree on the nose, and the identity on them is additive and compatible
with the two scalar actions, so it is an isomorphism of sheaves of modules. -/
def pullbackRestrictUnitIso :
    pullbackRestrictUnitSource Φ φ ≅ pullbackRestrictUnitTarget Φ φ :=
  isoOfSheafIso (Iso.refl _)
    ((moduleAddHom_comp_iff _).mpr fun X x y ↦
      have add_eq :
          Sheaf.moduleAddObj _ (pullbackRestrictUnitSource Φ φ) (Sheaf.sectionsFunctor J X) x y =
            Sheaf.moduleAddObj _ (pullbackRestrictUnitTarget Φ φ)
              (Sheaf.sectionsFunctor J X) x y :=
        (moduleAddObj_pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O) _
            (Sheaf.sectionsFunctor J X) x y).trans
          (moduleAddObj_pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O')
            (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf O'))
            (Sheaf.sectionsFunctor J X) x y).symm
      ((Sheaf.sectionsFunctor_map_moduleAddHom _ (pullbackRestrictUnitSource Φ φ)
            X x y).symm.trans add_eq).trans
        (Sheaf.sectionsFunctor_map_moduleAddHom _ (pullbackRestrictUnitTarget Φ φ) X x y))
    ((moduleSMulHom_comp_iff _).mpr fun X r x ↦
      have smul_eq :
          Sheaf.moduleSMulObj _ (pullbackRestrictUnitSource Φ φ) (Sheaf.sectionsFunctor J X) r x =
            Sheaf.moduleSMulObj _ (pullbackRestrictUnitTarget Φ φ)
              (Sheaf.sectionsFunctor J X) r x :=
        ((moduleSMulObj_pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O) _
              (Sheaf.sectionsFunctor J X) r x).trans
            ((moduleSMulObj_restrictScalars
                ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map φ)
                (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf O'))
                (Φ ⋙ Sheaf.sectionsFunctor J X) r x).trans
              (congrArg
                (fun s ↦ Sheaf.moduleSMulObj (Stacks.commRingSheafToRingSheaf O')
                  (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf O'))
                  (Φ ⋙ Sheaf.sectionsFunctor J X) s x)
                (congrArg (fun m ↦ (Sheaf.sectionsFunctor J X).map m r)
                  (underlyingRingSheaf_map_pullbackCommRingSheafMap J _ φ).symm)))).trans
          ((moduleSMulObj_pullbackModuleObj J Φ (Stacks.commRingSheafToRingSheaf O')
                (SheafOfModules.unit (Stacks.commRingSheafToRingSheaf O'))
                (Sheaf.sectionsFunctor J X) _ x).symm.trans
            (moduleSMulObj_restrictScalars
              ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
                ((pullbackCommRingSheafFunctor J Φ).map φ))
              (SheafOfModules.unit
                (Stacks.commRingSheafToRingSheaf (pullbackCommRingSheaf J Φ O')))
              (Sheaf.sectionsFunctor J X) r x).symm)
      ((Sheaf.sectionsFunctor_map_moduleSMulHom _ (pullbackRestrictUnitSource Φ φ)
            X r x).symm.trans smul_eq).trans
        (Sheaf.sectionsFunctor_map_moduleSMulHom _ (pullbackRestrictUnitTarget Φ φ) X r x))

end Stacks.Sheaves.ToposPullback.AnyUniverse

end

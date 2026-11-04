module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exactness of the inverse image on sheaves of modules

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and let `O` be a sheaf of rings on `D`. The
inverse image of sheaves of `O`-modules of Stacks 03D2
(`Stacks.Sheaves.RingedToposModules.inverseImageModules`) is **exact**. This is Stacks 04JC
for sheaves of modules; the corresponding statement for ordinary abelian sheaves is
`CategoryTheory.Sites.abelianInverseImage_exact`.

Right exactness is the adjunction of Stacks 03D3
(`Stacks.Sheaves.RingedToposModules.inverseImageAdjDirectImageModules`): a left adjoint
preserves colimits.

Left exactness is **Stacks 00YR at module level**. The module-level inverse image is
*constructed* by transporting the module structure along `f⁻¹` of the underlying sheaf of sets,
so `Stacks.Sheaves.RingedToposModules.inverseImageModuleSheafIso`
is the identity in each component: the
underlying sheaf of sets of `(inverseImageModules f O).obj G` **is** `f⁻¹` of the underlying
sheaf of sets of `G`, and
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_inverseImageModules_map` says the
same for morphisms. Since `CategoryTheory.Sheaf.moduleSheafFunctor` preserves finite limits
and reflects isomorphisms, it reflects finite limits, so left exactness of the module inverse
image follows from left exactness of `f⁻¹` on sheaves of sets, which is the defining property
of a morphism of topoi. No comparison of abelian-group structures is needed.

The statement is about the inverse image *with no change of rings*; the pullback of sheaves of
modules along a general morphism of ringed topoi is left exact only under a flatness
hypothesis.

## Main results

* `CategoryTheory.Sheaf.moduleSheafFunctor_preservesFiniteLimits`: the underlying-sheaf-of-sets
  functor on sheaves of modules preserves finite limits.
* `Stacks.Sheaves.RingedToposModules.inverseImageModules_preservesFiniteLimits` and
  `inverseImageModules_preservesFiniteColimits`.
* `Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules`: a short exact
  sequence of sheaves of `O`-modules has short exact inverse image.

## Implementation notes

`CategoryTheory.Limits.comp_preservesFiniteLimits` is a lemma and not an instance, so each
composite is supplied by hand rather than by instance search.

The universes of the two topoi stay independent: the site universes of source and target are
unrelated and the sections of the sheaf of rings and of the modules on each side lie in that
side's own universe, exactly as in `Stacks.Sheaves.RingedToposModules.inverseImageModules`.

## References

* [Stacks Project, Lemma 18.31.2 (Tag 04JC)](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Section 7.44 (Tag 00YR)](https://stacks.math.columbia.edu/tag/00YR)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w w' v u v' u'

namespace CategoryTheory.Sheaf

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}

/-- `sheafCompose J (forget AddCommGrpCat)` preserves finite limits. -/
theorem sheafComposeForgetAb_preservesFiniteLimits
    [K.HasSheafCompose (forget AddCommGrpCat.{w'})] :
    PreservesFiniteLimits (sheafCompose K (forget AddCommGrpCat.{w'})) := by
  have : PreservesFiniteLimits
      (sheafCompose K (forget AddCommGrpCat.{w'}) ⋙ sheafToPresheaf K (Type w')) := by
    show PreservesFiniteLimits
      (sheafToPresheaf K AddCommGrpCat.{w'} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{w'}))
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves
    (sheafCompose K (forget AddCommGrpCat.{w'})) (sheafToPresheaf K (Type w'))

variable [K.HasSheafCompose (forget RingCat.{w'})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]

omit [K.HasSheafCompose (forget RingCat.{w'})] in
/-- The underlying sheaf of sets of a sheaf of modules preserves finite limits. -/
theorem moduleSheafFunctor_preservesFiniteLimits (O : Sheaf K RingCat.{w'}) :
    PreservesFiniteLimits (Sheaf.moduleSheafFunctor O) := by
  have := sheafComposeForgetAb_preservesFiniteLimits (K := K)
  exact comp_preservesFiniteLimits _ _

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.RingedToposModules

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'})

omit [J.HasSheafCompose (forget RingCat.{w})] in
omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- **Stacks 04JC for sheaves of modules, left exactness.** The inverse image of sheaves of
modules along a morphism of topoi preserves finite limits. -/
@[sga "4 IV 13.7" "partial"]
theorem inverseImageModules_preservesFiniteLimits :
    PreservesFiniteLimits (inverseImageModules f O) := by
  have hA : PreservesFiniteLimits (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)) :=
    Sheaf.moduleSheafFunctor_preservesFiniteLimits (inverseImageRingSheaf f O)
  have : PreservesFiniteLimits (Sheaf.moduleSheafFunctor O) :=
    Sheaf.moduleSheafFunctor_preservesFiniteLimits O
  have : PreservesFiniteLimits f.inverseImage := f.preservesFiniteLimits
  have : PreservesFiniteLimits (Sheaf.moduleSheafFunctor O ⋙ f.inverseImage) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (inverseImageModules f O ⋙ Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O)) :=
    preservesFiniteLimits_of_natIso (inverseImageModuleSheafIso f O).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (inverseImageModules f O)
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf f O))

/-- **Stacks 04JC for sheaves of modules, right exactness.** The inverse image of sheaves of
modules preserves finite colimits. -/
theorem inverseImageModules_preservesFiniteColimits :
    PreservesFiniteColimits (inverseImageModules f O) := by
  have : PreservesColimitsOfSize.{0, 0} (inverseImageModules f O) :=
    (inverseImageAdjDirectImageModules f O).leftAdjoint_preservesColimits
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- The inverse image of sheaves of modules preserves finite limits, as an instance. -/
noncomputable instance inverseImageModules_preservesFiniteLimits_inst :
    PreservesFiniteLimits (inverseImageModules f O) :=
  inverseImageModules_preservesFiniteLimits f O

/-- The inverse image of sheaves of modules preserves finite colimits, as an instance. -/
noncomputable instance inverseImageModules_preservesFiniteColimits_inst :
    PreservesFiniteColimits (inverseImageModules f O) :=
  inverseImageModules_preservesFiniteColimits f O

/-- The inverse image of sheaves of modules is a left adjoint (Stacks 03D3). -/
noncomputable instance inverseImageModules_isLeftAdjoint :
    (inverseImageModules f O).IsLeftAdjoint :=
  (inverseImageAdjDirectImageModules f O).isLeftAdjoint

/-- **Stacks 04JC for sheaves of modules.** The inverse image along a morphism of topoi
carries a short exact sequence of sheaves of `O`-modules to a short exact sequence of sheaves
of `f⁻¹O`-modules. -/
theorem shortExact_map_inverseImageModules
    (S : CategoryTheory.ShortComplex (SheafOfModules.{w'} O)) (hS : S.ShortExact) :
    (S.map (inverseImageModules f O)).ShortExact :=
  hS.map_of_exact (inverseImageModules f O)

end Stacks.Sheaves.RingedToposModules

end

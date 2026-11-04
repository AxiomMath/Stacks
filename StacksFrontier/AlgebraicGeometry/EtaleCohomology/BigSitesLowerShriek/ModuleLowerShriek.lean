module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekOverMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesLowerShriek.AbelianExact
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSmoothStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSyntomicStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariskiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.MorphismOfTopoi
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiCovering.BigZariskiMorphism

/-!
# Lower shriek on modules of the big sites

Let `f : T ⟶ S` be a morphism in one of the big Zariski, étale, fppf, smooth or syntomic sites
of schemes. The inverse image of the induced morphism of topoi is restriction along
postcomposition with `f`, and it carries the structure sheaf of the big site over `S` to the
structure sheaf of the big site over `T`, so `f_big` is a morphism of ringed topoi with
`f_big^* = f_big^{-1}`. This file records that `f_big^*` on sheaves of modules has a left
adjoint `f_big!`, that `f_big!` is exact, and that `f_big!` on modules and `f_big!` on abelian
sheaves agree on underlying sheaves of abelian groups.

## Main definitions

* `AlgebraicGeometry.bigZariskiLowerShriekModules` and its étale, fppf, smooth and syntomic
  counterparts — `f_big! : Mod((Sch/T)_τ, O) ⥤ Mod((Sch/S)_τ, O)`.
* `AlgebraicGeometry.bigZariskiInverseImageModules` and its counterparts —
  `f_big^* : Mod((Sch/S)_τ, O) ⥤ Mod((Sch/T)_τ, O)`.

## Main results

* `AlgebraicGeometry.bigZariskiInverseImageRing_eq` and its counterparts:
  `f_big^{-1} O = O`, the structure sheaf of the big site over `T`.
* `AlgebraicGeometry.bigZariskiLowerShriekModulesAdjunction` and its counterparts:
  `f_big! ⊣ f_big^*`, the existence of the left adjoint.
* `AlgebraicGeometry.bigZariskiLowerShriekModulesToSheafIso` and its counterparts: the two
  `f_big!` agree on underlying sheaves of abelian groups.
* `AlgebraicGeometry.bigZariskiLowerShriekModules_preservesFiniteLimits` and
  `AlgebraicGeometry.bigZariskiLowerShriekModules_preservesFiniteColimits`, with their
  counterparts: `f_big!` on modules is exact.

## Implementation notes

`f_big^{-1} O = O` holds by `rfl` on each of the five sites, and is not a comparison
isomorphism: the structure sheaf of a big site over `S` is `Stacks.Sites.structurePresheaf`
of the inclusion into all schemes, whose value at an object is the ring of global functions on
its underlying scheme; restricting it along `CategoryTheory.Over.map f` forgets only the
structure morphism, which is not part of that value. Formally, postcomposition commutes with
the projection to schemes on the nose,
`Over.map f ⋙ Over.post G ⋙ Over.forget (G.obj S) = Over.post G ⋙ Over.forget (G.obj T)`,
and the sheaf condition is a proposition.

That identification is what lets the two functors be stated at the spelling the source uses,
with the big-site structure sheaf on both sides, rather than at the spelling
`Stacks.SheafOfModules.inverseImageRing` of the general construction; the type ascriptions
below are exactly that re-typing, and the two functors are abbreviations so that no second
definition of lower shriek is introduced.

Everything else is `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekOverMap` applied to
`CategoryTheory.Over.map f`: the lower shriek and its adjunction are those of Stacks 0797, and
the agreement on abelian sheaves is the Stacks 0798 criterion, whose hypothesis — that every
slice functor of the functor of sites is an equivalence — holds for postcomposition because
the slice of `(Sch/T)_τ` at an object `U` and the slice of `(Sch/S)_τ` at `U` are both
`(Sch/U)_τ`. This is the step the source performs by hand.

Exactness of `f_big!` on modules is not proved again from the criterion of Stacks 04BH:
right exactness is automatic, since `f_big!` is a left adjoint, and left exactness is
transported from part (1) of the tag — the exactness of `f_big!` on abelian sheaves, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesLowerShriek.AbelianExact` — across the
agreement above, because forgetting the module structure both preserves and reflects finite
limits.

## References

* [Stacks Project, Tag 04CC](https://stacks.math.columbia.edu/tag/04CC)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
* [Stacks Project, Tag 04HS](https://stacks.math.columbia.edu/tag/04HS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The big Zariski site -/

section Zariski

variable (B : BigZariskiSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

/-- **Stacks 04CC(2), Zariski case.** The inverse image of the structure sheaf of the big
Zariski site over `S` is the structure sheaf of the big Zariski site over `T`. -/
@[stacks 04CC "module_lower_shriek_inverse_image_structure_sheaf"]
public theorem bigZariskiInverseImageRing_eq :
    Stacks.SheafOfModules.inverseImageRing
        (BigZariskiOver.topology B T.1 T.property)
        (BigZariskiOver.topology B S.1 S.property) (Over.map f)
        (BigZariskiOver.structureSheaf B S.1 S.property) =
      BigZariskiOver.structureSheaf B T.1 T.property :=
  rfl

/-- **Stacks 04CC(2), Zariski case.** `f_big!` on sheaves of modules of the big Zariski
sites. -/
public abbrev bigZariskiLowerShriekModules :
    SheafOfModules.{u + 1} (BigZariskiOver.structureSheaf B T.1 T.property) ⥤
      SheafOfModules.{u + 1} (BigZariskiOver.structureSheaf B S.1 S.property) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1}
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property) (Over.map f)
    (BigZariskiOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), Zariski case.** `f_big^* = f_big^{-1}` on sheaves of modules of the big
Zariski sites: restriction along postcomposition with `f`. -/
public abbrev bigZariskiInverseImageModules :
    SheafOfModules.{u + 1} (BigZariskiOver.structureSheaf B S.1 S.property) ⥤
      SheafOfModules.{u + 1} (BigZariskiOver.structureSheaf B T.1 T.property) :=
  Stacks.SheafOfModules.inverseImage.{u + 1}
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property) (Over.map f)
    (BigZariskiOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), Zariski case.** `f_big^*` on sheaves of modules of the big Zariski sites
has `f_big!` as a left adjoint. -/
@[stacks 04CC "module_lower_shriek_adjunction"]
public def bigZariskiLowerShriekModulesAdjunction :
    bigZariskiLowerShriekModules B T S f ⊣ bigZariskiInverseImageModules B T S f :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property) (Over.map f)
    (BigZariskiOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), Zariski case.** The two `f_big!` agree on underlying sheaves of abelian
groups: the underlying abelian sheaf of `f_big! M` is `f_big!` of the underlying abelian sheaf
of `M`. -/
@[stacks 04CC "module_lower_shriek_agrees_on_abelian_sheaves"]
public def bigZariskiLowerShriekModulesToSheafIso :
    SheafOfModules.toSheaf.{u + 1} (BigZariskiOver.structureSheaf B T.1 T.property) ⋙
        (Over.map f).sheafPullback AddCommGrpCat.{u + 1}
          (BigZariskiOver.topology B T.1 T.property)
          (BigZariskiOver.topology B S.1 S.property) ≅
      bigZariskiLowerShriekModules B T S f ⋙
        SheafOfModules.toSheaf.{u + 1} (BigZariskiOver.structureSheaf B S.1 S.property) :=
  Stacks.SheafOfModules.overMapLowerShriekToSheafIso.{u, u + 1} f
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property)
    (BigZariskiOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), Zariski case.** `f_big!` on sheaves of modules of the big Zariski sites
preserves finite limits.  Lower shriek on abelian sheaves does, and forgetting the module
structure both preserves and reflects finite limits. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigZariskiLowerShriekModules_preservesFiniteLimits :
    PreservesFiniteLimits (bigZariskiLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteLimits_lowerShriek_overMap.{u, u + 1} f
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property)
    (BigZariskiOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), Zariski case.** `f_big!` on sheaves of modules of the big Zariski sites
preserves finite colimits: it is a left adjoint. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigZariskiLowerShriekModules_preservesFiniteColimits :
    PreservesFiniteColimits (bigZariskiLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteColimits_lowerShriek_overMap.{u, u + 1} f
    (BigZariskiOver.topology B T.1 T.property)
    (BigZariskiOver.topology B S.1 S.property)
    (BigZariskiOver.structureSheaf B S.1 S.property)

end Zariski

/-! ### The big étale site -/

section Etale

variable (B : BigEtaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- **Stacks 04CC(2), étale case.** The inverse image of the structure sheaf of the big étale
site over `S` is the structure sheaf of the big étale site over `T`. -/
@[stacks 04CC "module_lower_shriek_inverse_image_structure_sheaf"]
public theorem bigEtaleInverseImageRing_eq :
    Stacks.SheafOfModules.inverseImageRing
        (BigEtaleOver.topology B T.obj T.property)
        (BigEtaleOver.topology B S.obj S.property) (Over.map f)
        (BigEtaleOver.structureSheaf B S.obj S.property) =
      BigEtaleOver.structureSheaf B T.obj T.property :=
  rfl

/-- **Stacks 04CC(2), étale case.** `f_big!` on sheaves of modules of the big étale sites. -/
public abbrev bigEtaleLowerShriekModules :
    SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B T.obj T.property) ⥤
      SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1}
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property) (Over.map f)
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Stacks 04CC(2), étale case.** `f_big^* = f_big^{-1}` on sheaves of modules of the big
étale sites: restriction along postcomposition with `f`. -/
public abbrev bigEtaleInverseImageModules :
    SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) ⥤
      SheafOfModules.{u + 1} (BigEtaleOver.structureSheaf B T.obj T.property) :=
  Stacks.SheafOfModules.inverseImage.{u + 1}
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property) (Over.map f)
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Stacks 04CC(2), étale case.** `f_big^*` on sheaves of modules of the big étale sites has
`f_big!` as a left adjoint. -/
@[stacks 04CC "module_lower_shriek_adjunction"]
public def bigEtaleLowerShriekModulesAdjunction :
    bigEtaleLowerShriekModules B T S f ⊣ bigEtaleInverseImageModules B T S f :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property) (Over.map f)
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Stacks 04CC(2), étale case.** The two `f_big!` agree on underlying sheaves of abelian
groups. -/
@[stacks 04CC "module_lower_shriek_agrees_on_abelian_sheaves"]
public def bigEtaleLowerShriekModulesToSheafIso :
    SheafOfModules.toSheaf.{u + 1} (BigEtaleOver.structureSheaf B T.obj T.property) ⋙
        (Over.map f).sheafPullback AddCommGrpCat.{u + 1}
          (BigEtaleOver.topology B T.obj T.property)
          (BigEtaleOver.topology B S.obj S.property) ≅
      bigEtaleLowerShriekModules B T S f ⋙
        SheafOfModules.toSheaf.{u + 1} (BigEtaleOver.structureSheaf B S.obj S.property) :=
  Stacks.SheafOfModules.overMapLowerShriekToSheafIso.{u, u + 1} f
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Stacks 04CC(2), étale case.** `f_big!` on sheaves of modules of the big étale sites
preserves finite limits.  Lower shriek on abelian sheaves does, and forgetting the module
structure both preserves and reflects finite limits. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigEtaleLowerShriekModules_preservesFiniteLimits :
    PreservesFiniteLimits (bigEtaleLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteLimits_lowerShriek_overMap.{u, u + 1} f
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
    (BigEtaleOver.structureSheaf B S.obj S.property)

/-- **Stacks 04CC(2), étale case.** `f_big!` on sheaves of modules of the big étale sites
preserves finite colimits: it is a left adjoint. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigEtaleLowerShriekModules_preservesFiniteColimits :
    PreservesFiniteColimits (bigEtaleLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteColimits_lowerShriek_overMap.{u, u + 1} f
    (BigEtaleOver.topology B T.obj T.property)
    (BigEtaleOver.topology B S.obj S.property)
    (BigEtaleOver.structureSheaf B S.obj S.property)

end Etale

/-! ### The big fppf site -/

section Fppf

variable (B : BigFppfSite.{u}) (T S : B.Schemes) (f : T ⟶ S)

/-- **Stacks 04CC(2), fppf case.** The inverse image of the structure sheaf of the big fppf
site over `S` is the structure sheaf of the big fppf site over `T`. -/
@[stacks 04CC "module_lower_shriek_inverse_image_structure_sheaf"]
public theorem bigFppfInverseImageRing_eq :
    Stacks.SheafOfModules.inverseImageRing
        (B.topology.over T)
        (B.topology.over S) (Over.map f)
        (BigFppfOver.structureSheaf B S.1 S.property) =
      BigFppfOver.structureSheaf B T.1 T.property :=
  rfl

/-- **Stacks 04CC(2), fppf case.** `f_big!` on sheaves of modules of the big fppf sites. -/
public abbrev bigFppfLowerShriekModules :
    SheafOfModules.{u + 1} (BigFppfOver.structureSheaf B T.1 T.property) ⥤
      SheafOfModules.{u + 1} (BigFppfOver.structureSheaf B S.1 S.property) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1}
    (B.topology.over T)
    (B.topology.over S) (Over.map f)
    (BigFppfOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), fppf case.** `f_big^* = f_big^{-1}` on sheaves of modules of the big fppf
sites: restriction along postcomposition with `f`. -/
public abbrev bigFppfInverseImageModules :
    SheafOfModules.{u + 1} (BigFppfOver.structureSheaf B S.1 S.property) ⥤
      SheafOfModules.{u + 1} (BigFppfOver.structureSheaf B T.1 T.property) :=
  Stacks.SheafOfModules.inverseImage.{u + 1}
    (B.topology.over T)
    (B.topology.over S) (Over.map f)
    (BigFppfOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), fppf case.** `f_big^*` on sheaves of modules of the big fppf sites has
`f_big!` as a left adjoint. -/
@[stacks 04CC "module_lower_shriek_adjunction"]
public def bigFppfLowerShriekModulesAdjunction :
    bigFppfLowerShriekModules B T S f ⊣ bigFppfInverseImageModules B T S f :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
    (B.topology.over T)
    (B.topology.over S) (Over.map f)
    (BigFppfOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), fppf case.** The two `f_big!` agree on underlying sheaves of abelian
groups. -/
@[stacks 04CC "module_lower_shriek_agrees_on_abelian_sheaves"]
public def bigFppfLowerShriekModulesToSheafIso :
    SheafOfModules.toSheaf.{u + 1} (BigFppfOver.structureSheaf B T.1 T.property) ⋙
        (Over.map f).sheafPullback AddCommGrpCat.{u + 1}
          (B.topology.over T)
          (B.topology.over S) ≅
      bigFppfLowerShriekModules B T S f ⋙
        SheafOfModules.toSheaf.{u + 1} (BigFppfOver.structureSheaf B S.1 S.property) :=
  Stacks.SheafOfModules.overMapLowerShriekToSheafIso.{u, u + 1} f
    (B.topology.over T)
    (B.topology.over S)
    (BigFppfOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), fppf case.** `f_big!` on sheaves of modules of the big fppf sites
preserves finite limits.  Lower shriek on abelian sheaves does, and forgetting the module
structure both preserves and reflects finite limits. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigFppfLowerShriekModules_preservesFiniteLimits :
    PreservesFiniteLimits (bigFppfLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteLimits_lowerShriek_overMap.{u, u + 1} f
    (B.topology.over T)
    (B.topology.over S)
    (BigFppfOver.structureSheaf B S.1 S.property)

/-- **Stacks 04CC(2), fppf case.** `f_big!` on sheaves of modules of the big fppf sites
preserves finite colimits: it is a left adjoint. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigFppfLowerShriekModules_preservesFiniteColimits :
    PreservesFiniteColimits (bigFppfLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteColimits_lowerShriek_overMap.{u, u + 1} f
    (B.topology.over T)
    (B.topology.over S)
    (BigFppfOver.structureSheaf B S.1 S.property)

end Fppf

/-! ### The big smooth site -/

section Smooth

variable (B : BigSmoothSite.{u}) (T S : B.category) (f : T ⟶ S)

/-- **Stacks 04CC(2), smooth case.** The inverse image of the structure sheaf of the big smooth
site over `S` is the structure sheaf of the big smooth site over `T`. -/
@[stacks 04CC "module_lower_shriek_inverse_image_structure_sheaf"]
public theorem bigSmoothInverseImageRing_eq :
    Stacks.SheafOfModules.inverseImageRing
        (BigSmoothOver.topology B T.1 T.2)
        (BigSmoothOver.topology B S.1 S.2) (Over.map f)
        (BigSmoothOver.structureSheaf B S.1 S.2) =
      BigSmoothOver.structureSheaf B T.1 T.2 :=
  rfl

/-- **Stacks 04CC(2), smooth case.** `f_big!` on sheaves of modules of the big smooth sites. -/
public abbrev bigSmoothLowerShriekModules :
    SheafOfModules.{u + 1} (BigSmoothOver.structureSheaf B T.1 T.2) ⥤
      SheafOfModules.{u + 1} (BigSmoothOver.structureSheaf B S.1 S.2) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1}
    (BigSmoothOver.topology B T.1 T.2)
    (BigSmoothOver.topology B S.1 S.2) (Over.map f)
    (BigSmoothOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), smooth case.** `f_big^* = f_big^{-1}` on sheaves of modules of the big
smooth sites: restriction along postcomposition with `f`. -/
public abbrev bigSmoothInverseImageModules :
    SheafOfModules.{u + 1} (BigSmoothOver.structureSheaf B S.1 S.2) ⥤
      SheafOfModules.{u + 1} (BigSmoothOver.structureSheaf B T.1 T.2) :=
  Stacks.SheafOfModules.inverseImage.{u + 1}
    (BigSmoothOver.topology B T.1 T.2)
    (BigSmoothOver.topology B S.1 S.2) (Over.map f)
    (BigSmoothOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), smooth case.** `f_big^*` on sheaves of modules of the big smooth sites
has `f_big!` as a left adjoint. -/
@[stacks 04CC "module_lower_shriek_adjunction"]
public def bigSmoothLowerShriekModulesAdjunction :
    bigSmoothLowerShriekModules B T S f ⊣ bigSmoothInverseImageModules B T S f :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
    (BigSmoothOver.topology B T.1 T.2)
    (BigSmoothOver.topology B S.1 S.2) (Over.map f)
    (BigSmoothOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), smooth case.** The two `f_big!` agree on underlying sheaves of abelian
groups. -/
@[stacks 04CC "module_lower_shriek_agrees_on_abelian_sheaves"]
public def bigSmoothLowerShriekModulesToSheafIso :
    SheafOfModules.toSheaf.{u + 1} (BigSmoothOver.structureSheaf B T.1 T.2) ⋙
        (Over.map f).sheafPullback AddCommGrpCat.{u + 1}
          (BigSmoothOver.topology B T.1 T.2)
          (BigSmoothOver.topology B S.1 S.2) ≅
      bigSmoothLowerShriekModules B T S f ⋙
        SheafOfModules.toSheaf.{u + 1} (BigSmoothOver.structureSheaf B S.1 S.2) :=
  Stacks.SheafOfModules.overMapLowerShriekToSheafIso.{u, u + 1} f
    (BigSmoothOver.topology B T.1 T.2)
    (BigSmoothOver.topology B S.1 S.2)
    (BigSmoothOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), smooth case.** `f_big!` on sheaves of modules of the big smooth sites
preserves finite limits.  Lower shriek on abelian sheaves does, and forgetting the module
structure both preserves and reflects finite limits. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigSmoothLowerShriekModules_preservesFiniteLimits :
    PreservesFiniteLimits (bigSmoothLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteLimits_lowerShriek_overMap.{u, u + 1} f
    (BigSmoothOver.topology B T.1 T.2)
    (BigSmoothOver.topology B S.1 S.2)
    (BigSmoothOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), smooth case.** `f_big!` on sheaves of modules of the big smooth sites
preserves finite colimits: it is a left adjoint. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigSmoothLowerShriekModules_preservesFiniteColimits :
    PreservesFiniteColimits (bigSmoothLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteColimits_lowerShriek_overMap.{u, u + 1} f
    (BigSmoothOver.topology B T.1 T.2)
    (BigSmoothOver.topology B S.1 S.2)
    (BigSmoothOver.structureSheaf B S.1 S.2)

end Smooth

/-! ### The big syntomic site -/

section Syntomic

variable (B : BigSyntomicSite.{u}) (T S : B.category) (f : T ⟶ S)

/-- **Stacks 04CC(2), syntomic case.** The inverse image of the structure sheaf of the big
syntomic site over `S` is the structure sheaf of the big syntomic site over `T`. -/
@[stacks 04CC "module_lower_shriek_inverse_image_structure_sheaf"]
public theorem bigSyntomicInverseImageRing_eq :
    Stacks.SheafOfModules.inverseImageRing
        (BigSyntomicOver.topology B T.1 T.2)
        (BigSyntomicOver.topology B S.1 S.2) (Over.map f)
        (BigSyntomicOver.structureSheaf B S.1 S.2) =
      BigSyntomicOver.structureSheaf B T.1 T.2 :=
  rfl

/-- **Stacks 04CC(2), syntomic case.** `f_big!` on sheaves of modules of the big syntomic
sites. -/
public abbrev bigSyntomicLowerShriekModules :
    SheafOfModules.{u + 1} (BigSyntomicOver.structureSheaf B T.1 T.2) ⥤
      SheafOfModules.{u + 1} (BigSyntomicOver.structureSheaf B S.1 S.2) :=
  Stacks.SheafOfModules.lowerShriek.{u + 1}
    (BigSyntomicOver.topology B T.1 T.2)
    (BigSyntomicOver.topology B S.1 S.2) (Over.map f)
    (BigSyntomicOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), syntomic case.** `f_big^* = f_big^{-1}` on sheaves of modules of the big
syntomic sites: restriction along postcomposition with `f`. -/
public abbrev bigSyntomicInverseImageModules :
    SheafOfModules.{u + 1} (BigSyntomicOver.structureSheaf B S.1 S.2) ⥤
      SheafOfModules.{u + 1} (BigSyntomicOver.structureSheaf B T.1 T.2) :=
  Stacks.SheafOfModules.inverseImage.{u + 1}
    (BigSyntomicOver.topology B T.1 T.2)
    (BigSyntomicOver.topology B S.1 S.2) (Over.map f)
    (BigSyntomicOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), syntomic case.** `f_big^*` on sheaves of modules of the big syntomic
sites has `f_big!` as a left adjoint. -/
@[stacks 04CC "module_lower_shriek_adjunction"]
public def bigSyntomicLowerShriekModulesAdjunction :
    bigSyntomicLowerShriekModules B T S f ⊣ bigSyntomicInverseImageModules B T S f :=
  Stacks.SheafOfModules.lowerShriekAdjunction.{u + 1}
    (BigSyntomicOver.topology B T.1 T.2)
    (BigSyntomicOver.topology B S.1 S.2) (Over.map f)
    (BigSyntomicOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), syntomic case.** The two `f_big!` agree on underlying sheaves of abelian
groups. -/
@[stacks 04CC "module_lower_shriek_agrees_on_abelian_sheaves"]
public def bigSyntomicLowerShriekModulesToSheafIso :
    SheafOfModules.toSheaf.{u + 1} (BigSyntomicOver.structureSheaf B T.1 T.2) ⋙
        (Over.map f).sheafPullback AddCommGrpCat.{u + 1}
          (BigSyntomicOver.topology B T.1 T.2)
          (BigSyntomicOver.topology B S.1 S.2) ≅
      bigSyntomicLowerShriekModules B T S f ⋙
        SheafOfModules.toSheaf.{u + 1} (BigSyntomicOver.structureSheaf B S.1 S.2) :=
  Stacks.SheafOfModules.overMapLowerShriekToSheafIso.{u, u + 1} f
    (BigSyntomicOver.topology B T.1 T.2)
    (BigSyntomicOver.topology B S.1 S.2)
    (BigSyntomicOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), syntomic case.** `f_big!` on sheaves of modules of the big syntomic sites
preserves finite limits.  Lower shriek on abelian sheaves does, and forgetting the module
structure both preserves and reflects finite limits. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigSyntomicLowerShriekModules_preservesFiniteLimits :
    PreservesFiniteLimits (bigSyntomicLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteLimits_lowerShriek_overMap.{u, u + 1} f
    (BigSyntomicOver.topology B T.1 T.2)
    (BigSyntomicOver.topology B S.1 S.2)
    (BigSyntomicOver.structureSheaf B S.1 S.2)

/-- **Stacks 04CC(2), syntomic case.** `f_big!` on sheaves of modules of the big syntomic sites
preserves finite colimits: it is a left adjoint. -/
@[stacks 04CC "module_lower_shriek_exact", instance]
public theorem bigSyntomicLowerShriekModules_preservesFiniteColimits :
    PreservesFiniteColimits (bigSyntomicLowerShriekModules B T S f) :=
  Stacks.SheafOfModules.preservesFiniteColimits_lowerShriek_overMap.{u, u + 1} f
    (BigSyntomicOver.topology B T.1 T.2)
    (BigSyntomicOver.topology B S.1 S.2)
    (BigSyntomicOver.structureSheaf B S.1 S.2)

end Syntomic

end AlgebraicGeometry

end

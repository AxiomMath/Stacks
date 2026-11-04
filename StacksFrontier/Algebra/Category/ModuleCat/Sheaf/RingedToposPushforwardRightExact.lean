module

public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPointPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback

/-!
# Right exactness of the direct image of modules along a morphism of ringed topoi

`AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesFiniteLimits` is one half of
exactness and holds for every morphism of ringed topoi, the direct image being a right adjoint.
The other half is not automatic. This file reduces it to a statement about the underlying
morphism of topoi — that its direct image of sheaves of *sets* preserves epimorphisms — and
proves that statement for the direct image attached to a functor of sites which is both
continuous and cocontinuous.

## Main results

* `CategoryTheory.Functor.preservesEpimorphisms_sheafPushforwardContinuous`: restriction of
  sheaves of sets along a continuous cocontinuous functor of sites preserves epimorphisms.
* `AlgebraicGeometry.RingedToposHom.preservesFiniteColimits_pushforwardModules`: if the direct
  image of sheaves of sets along a morphism of ringed topoi preserves epimorphisms, then its
  direct image of sheaves of modules preserves finite colimits.
* `AlgebraicGeometry.RingedToposHom.exactFunctor_pushforwardModules`: the two halves together.

## Implementation notes

An epimorphism of sheaves of sets is a locally surjective map, and local surjectivity is
inherited by restriction along a cocontinuous functor
(`CategoryTheory.Presheaf.isLocallySurjective_whisker`); that is the whole of the first result,
and it is where cocontinuity enters.

The second result is the homology criterion. The underlying sheaf of sets of a sheaf of
modules, `CategoryTheory.Sheaf.moduleSheafFunctor`, preserves epimorphisms and is faithful,
hence reflects them, and `AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`
identifies it composed with the direct image of modules with the direct image of sheaves of
sets composed with it. So the direct image of modules preserves epimorphisms; being additive
and left exact, it then preserves homology, and a homology-preserving functor between abelian
categories is exact.

This is the route `Stacks.Sheaves.RingedPoint.RingedPointSituation.pushforwardModules_exact`
takes for a ringed point, where the epimorphism hypothesis is supplied instead by every
epimorphism of the point's topos being split; the argument is stated here for an arbitrary
morphism of ringed topoi with that one input named.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Functor

universe w v u v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (H : C ⥤ D)
  [H.IsContinuous J K] [H.IsCocontinuous J K] [HasSheafify K (Type w)]

/-- **Restriction of sheaves of sets along a continuous cocontinuous functor of sites preserves
epimorphisms.** An epimorphism of sheaves of sets is locally surjective, local surjectivity of
a map of presheaves is inherited by restriction along a cocontinuous functor, and a locally
surjective map of sheaves is an epimorphism. -/
instance preservesEpimorphisms_sheafPushforwardContinuous :
    PreservesEpimorphisms (H.sheafPushforwardContinuous (Type w) J K) where
  preserves {F G} g hg := by
    have hsurj : Sheaf.IsLocallySurjective g := (Sheaf.isLocallySurjective_iff_epi g).2 hg
    have : Sheaf.IsLocallySurjective ((H.sheafPushforwardContinuous (Type w) J K).map g) :=
      Presheaf.isLocallySurjective_whisker J K H g.hom
    exact Sheaf.epi_of_isLocallySurjective'
      ((H.sheafPushforwardContinuous (Type w) J K).map g)

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedToposHom

universe w w' v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

omit [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The direct image of sheaves of modules along a morphism of ringed topoi preserves
epimorphisms as soon as the direct image of sheaves of sets does: the two agree after
forgetting the module structure, by
`AlgebraicGeometry.RingedToposHom.pushforwardModulesUnderlyingIso`, and the underlying sheaf of
sets of a sheaf of modules preserves epimorphisms and is faithful, hence reflects them.

Composing a presheaf of types with the forgetful functor of `Type` changes nothing, so the
`CategoryTheory.GrothendieckTopology.HasSheafCompose` hypothesis that
`Stacks.Sheaves.RingedPoint.preservesEpimorphisms_moduleSheafFunctor` carries is discharged in
the proof rather than assumed. -/
theorem preservesEpimorphisms_pushforwardModules
    [PreservesEpimorphisms f.toToposHom.pushforward] :
    PreservesEpimorphisms (pushforwardModules f) := by
  have : X.J.HasSheafCompose (forget (Type w)) := ⟨fun {_} hP ↦ hP⟩
  have hX : PreservesEpimorphisms
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)) :=
    Stacks.Sheaves.RingedPoint.preservesEpimorphisms_moduleSheafFunctor X.J _
  have hcomp : PreservesEpimorphisms
      (pushforwardModules f ⋙
        Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :=
    PreservesEpimorphisms.of_iso f.pushforwardModulesUnderlyingIso.symm
      (F := Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
        f.toToposHom.pushforward)
  have : ReflectsEpimorphisms
      (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :=
    Functor.reflectsEpimorphisms_of_faithful _
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects (pushforwardModules f)
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))

/-- **The direct image of sheaves of modules is right exact when the direct image of sheaves of
sets preserves epimorphisms.** The direct image of modules is additive and left exact for every
morphism of ringed topoi; with epimorphisms preserved as well it preserves homology, and a
homology-preserving functor between abelian categories preserves finite colimits. -/
theorem preservesFiniteColimits_pushforwardModules
    [PreservesEpimorphisms f.toToposHom.pushforward] :
    PreservesFiniteColimits (pushforwardModules f) := by
  have : (pushforwardModules f).Additive := pushforwardModules_additive f
  have : PreservesFiniteLimits (pushforwardModules f) :=
    pushforwardModules_preservesFiniteLimits f
  have : PreservesEpimorphisms (pushforwardModules f) :=
    preservesEpimorphisms_pushforwardModules f
  have : (pushforwardModules f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- **The direct image of sheaves of modules is exact when the direct image of sheaves of sets
preserves epimorphisms.** The two halves are
`AlgebraicGeometry.RingedToposHom.pushforwardModules_preservesFiniteLimits` and
`AlgebraicGeometry.RingedToposHom.preservesFiniteColimits_pushforwardModules`. -/
theorem exactFunctor_pushforwardModules
    [PreservesEpimorphisms f.toToposHom.pushforward] :
    exactFunctor (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))
      (SheafOfModules.{w'} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))
      (pushforwardModules f) :=
  ⟨pushforwardModules_preservesFiniteLimits f,
    preservesFiniteColimits_pushforwardModules f⟩

end AlgebraicGeometry.RingedToposHom

end

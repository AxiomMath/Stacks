module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.Subtopos.Immersions

/-!
# Closed immersions of ringed topoi with surjective structure map

A *closed immersion of ringed topoi* is a morphism of ringed topoi whose underlying morphism of
topoi is a closed immersion and whose structure map `O ⟶ i_*O'` is locally surjective. Such a
morphism determines an ideal in the structure sheaf of the target, namely the kernel of the
structure map, and that ideal is the datum the Stacks 18.25 results about the direct image of
modules are stated relative to.

The ideal is produced the way the source describes it: its sections over a site object are the
kernel of the structure map on sections, these subsets are stable under restriction because the
structure map is a morphism of presheaves, and they form a subsheaf because a section whose
restrictions along a covering sieve all die must itself die, the target of the structure map
being a sheaf.

## Main definitions

* `AlgebraicGeometry.ClosedRingedImmersion`: a closed immersion of ringed topoi whose structure
  map is locally surjective.
* `AlgebraicGeometry.ClosedRingedImmersion.ideal`: the kernel ideal subsheaf of the structure
  sheaf of the target.

## Main results

* `AlgebraicGeometry.ClosedRingedImmersion.structureMap_epi`: a locally surjective structure map
  is an epimorphism of the underlying sheaves of sets.
* `AlgebraicGeometry.ClosedRingedImmersion.ideal_obj`: the sections of the kernel ideal over a
  site object are exactly the kernel of the structure map there.

## Implementation notes

Surjectivity of the structure map means local surjectivity after forgetting the ring structure
to sheaves of sets, which is the form in which Stacks 18.25 uses it.

`AlgebraicGeometry.RingedToposHom` is available only in the presence of four
`GrothendieckTopology.HasSheafCompose` instances, so those are carried as instance-implicit
fields of the structure rather than as parameters: the two ringed topoi they refer to are
themselves fields.

The ideal is a submodule subsheaf of the structure sheaf regarded as a module over itself,
with sections the objectwise ring-homomorphism kernel; its inclusion is the canonical
`SheafOfModules.Submodule.ι`.

## References

* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit

universe v u v' u' w

namespace AlgebraicGeometry

/-- A closed immersion of ringed topoi whose structure map is locally surjective. -/
structure ClosedRingedImmersion where
  /-- The source ringed topos. -/
  source : RingedTopos.{v, u, w}
  /-- The target ringed topos. -/
  target : RingedTopos.{v', u', w}
  [hasSheafComposeForgetRingSource : source.J.HasSheafCompose (forget RingCat.{w})]
  [hasSheafComposeForgetRingTarget : target.J.HasSheafCompose (forget RingCat.{w})]
  [hasSheafComposeForget₂Source :
    source.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [hasSheafComposeForget₂Target :
    target.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  /-- The morphism of ringed topoi. -/
  hom : RingedToposHom source target
  /-- The underlying morphism of topoi is a closed immersion. -/
  isClosedImmersion : MorphismOfTopoi.IsClosedImmersion hom.toToposHom
  /-- The structure map is locally surjective. -/
  structureMap_surjective :
    Sheaf.IsLocallySurjective (target.forgetRing.map hom.fSharp)

attribute [instance] ClosedRingedImmersion.hasSheafComposeForgetRingSource
  ClosedRingedImmersion.hasSheafComposeForgetRingTarget
  ClosedRingedImmersion.hasSheafComposeForget₂Source
  ClosedRingedImmersion.hasSheafComposeForget₂Target

namespace ClosedRingedImmersion

/-- The sheaf of rings underlying the structure sheaf of the target. -/
noncomputable abbrev targetRingSheaf (S : ClosedRingedImmersion.{v, u, v', u', w}) :
    Sheaf S.target.J RingCat.{w} :=
  letI := S.hasSheafComposeForget₂Target
  Stacks.SheafOfModules.Tensor.ringSheaf S.target.O

/-- The locally surjective structure map is an epimorphism of sheaves of sets. -/
theorem structureMap_epi (S : ClosedRingedImmersion.{v, u, v', u', w}) :
    Epi (S.target.forgetRing.map S.hom.fSharp) := by
  have := S.structureMap_surjective
  infer_instance

open Opposite

/-- The objectwise kernels of the structure map are stable under restriction. -/
lemma kernelIdeal_map (S : ClosedRingedImmersion.{v, u, v', u', w})
    {U V : S.target.Cᵒᵖ} (f : U ⟶ V) :
    RingHom.ker ((S.hom.fSharp.hom.app U).hom) ≤
      Submodule.comap
        ((SheafOfModules.unit (S.targetRingSheaf)).val.restrictₛₗ f)
        (RingHom.ker ((S.hom.fSharp.hom.app V).hom)) := by
  intro x hx
  let M : SheafOfModules (S.targetRingSheaf) :=
    SheafOfModules.unit (S.targetRingSheaf)
  show ((S.hom.fSharp.hom.app V).hom) (M.val.map f x) = 0
  have hnat := congrArg (fun g => g x) (S.hom.fSharp.hom.naturality f)
  change ((S.hom.fSharp.hom.app V).hom) (M.val.map f x) =
    (((Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      S.hom.toToposHom).obj S.source.O).obj.map f) ((S.hom.fSharp.hom.app U).hom x) at hnat
  change ((S.hom.fSharp.hom.app U).hom) x = 0 at hx
  rw [hnat, hx, map_zero]

/-- The kernel ideal subsheaf, together with the identification of its sections over every site
object of the target with the kernel of the structure map there. -/
noncomputable def kernelIdealData (S : ClosedRingedImmersion.{v, u, v', u', w}) :
    { I : (SheafOfModules.unit (S.targetRingSheaf)).Submodule //
      ∀ U : S.target.Cᵒᵖ,
        I.obj U = RingHom.ker ((S.hom.fSharp.hom.app U).hom) } := by
  classical
  let M : SheafOfModules (S.targetRingSheaf) :=
    SheafOfModules.unit (S.targetRingSheaf)
  let N : M.val.Submodule :=
    { obj U := RingHom.ker ((S.hom.fSharp.hom.app U).hom)
      map := fun {U V} f => kernelIdeal_map S f }
  refine ⟨⟨N, ?_⟩, ?_⟩
  · intro U s hs
    let T := N.toSubfunctor.sieveOfSection s
    have hT : T ∈ S.target.J U.unop := hs
    let F := (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor
      S.hom.toToposHom).obj S.source.O
    let F' := S.target.forgetRing.obj F
    change (S.hom.fSharp.hom.app U).hom s = 0
    apply (F'.2.isSheafFor T hT).isSeparatedFor.ext
    intro V f hf
    have hmem : M.val.map f.op s ∈ N.obj (op V) := hf
    change ((S.hom.fSharp.hom.app (op V)).hom) (M.val.map f.op s) = 0 at hmem
    have hnat := congrArg (fun g => g s) (S.hom.fSharp.hom.naturality f.op)
    change ((S.hom.fSharp.hom.app (op V)).hom) (M.val.map f.op s) =
      F'.obj.map f.op ((S.hom.fSharp.hom.app U).hom s) at hnat
    rw [← hnat, hmem]
    exact (map_zero (F.obj.map f.op).hom).symm
  · exact fun _ ↦ rfl

/-- The kernel ideal of the structure map of a closed immersion of ringed topoi. -/
noncomputable def ideal (S : ClosedRingedImmersion.{v, u, v', u', w}) :
    (SheafOfModules.unit (S.targetRingSheaf)).Submodule :=
  S.kernelIdealData.val

/-- Sections of the kernel ideal are exactly the kernel of the structure map. -/
@[simp]
theorem ideal_obj (S : ClosedRingedImmersion.{v, u, v', u', w}) (U : S.target.Cᵒᵖ) :
    S.ideal.obj U = RingHom.ker ((S.hom.fSharp.hom.app U).hom) :=
  S.kernelIdealData.property U

end ClosedRingedImmersion

end AlgebraicGeometry

end

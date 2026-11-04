module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact

/-!
# Exactness of the pullback of modules from left exactness of extension of scalars

`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap` — Stacks 04JC, second
assertion — deduces exactness of the pullback of sheaves of modules along a morphism of ringed
topoi from *flatness* of the inverse-image form of its structure map.  Flatness enters that
proof through exactly one step, `extendScalars_preservesFiniteLimits`; this module records the
statement with that step as the hypothesis instead.

The point of the weaker hypothesis is that left exactness of extension of scalars survives
replacing the structure map by any morphism differing from it by an isomorphism
(`Stacks.Sheaves.RingedToposModules.preservesFiniteLimits_extendScalars_comp_iso`), whereas
flatness, being stated after a universe lift of the sections, does not transport along an
isomorphism of the source sheaf of rings without further work.  A morphism of ringed topoi whose
structure map is only *known* up to such an isomorphism — which is the situation of the
canonical morphism from the small étale site of a scheme to its small Zariski site, where the
two constructions of `ε⁻¹𝒪` on sheaves of commutative rings are compared by uniqueness of left
adjoints — can therefore still be handled.

## Main results

* `Stacks.Sheaves.RingedToposModules.exactFunctor_pullbackModules_of_preservesFiniteLimits`:
  the pullback of sheaves of modules along a morphism of ringed topoi is exact as soon as
  extension of scalars along the inverse-image form of its structure map is left exact.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe v u v' u' w

namespace Stacks.Sheaves.RingedToposModules

open AlgebraicGeometry


variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Exactness of the pullback of sheaves of modules along a morphism of ringed topoi, from
left exactness of extension of scalars along its structure map.**  The pullback is the inverse
image of Stacks 03D2 followed by extension of scalars along the inverse-image form of the
structure map; the first factor is always left exact, the second is the hypothesis, and right
exactness is automatic, the pullback being a left adjoint.

This is `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`, Stacks 04JC
second assertion, with the flatness hypothesis replaced by the single consequence of it that
proof uses. -/
public theorem exactFunctor_pullbackModules_of_preservesFiniteLimits
    (f : AlgebraicGeometry.RingedToposHom X Y)
    (hf : PreservesFiniteLimits
      (extendScalars.{w, v, u} X.J f.fSharpInverseImage.hom
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((inverseImageCommRingFunctor f.toToposHom).obj Y.O)).property
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property)) :
    exactFunctor (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (f.toRingedToposModulesHom.pullbackModules) := by
  let := (pullbackAdjPushforwardModules f.toRingedToposModulesHom).isLeftAdjoint
  rw [exactFunctor_iff]
  refine ⟨?_, inferInstance⟩
  have h : PreservesFiniteLimits
      (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
        extendScalars.{w, v, u} X.J f.fSharpInverseImage.hom
          (Stacks.SheafOfModules.Tensor.ringSheaf
            ((inverseImageCommRingFunctor f.toToposHom).obj Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) :=
    preservesFiniteLimits_comp_of _ _
      (inverseImageModules_preservesFiniteLimits f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) hf
  exact h

end Stacks.Sheaves.RingedToposModules

end

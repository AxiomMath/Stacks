module

public import StacksFrontier.Deformation.Formal.VersalObject.MapsToFormalObject
public import StacksFrontier.Deformation.MinimalVersal
public import StacksFrontier.RingTheory.Noetherian.Endomorphism
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.Deformation.VersalObject.MinimalVersalDescent

/-!
# Uniqueness of minimal versal formal objects

Any two minimal versal formal objects of a predeformation category are isomorphic.

## Main results

* `Deformation.isomorphic_of_isMinimalVersal` gives the isomorphism.

## Implementation notes

The existence of a versal formal object follows already from either minimal
versal object in the hypotheses, so it is not assumed separately.

## References

* [Stacks Project, Tag 06T5](https://stacks.math.columbia.edu/tag/06T5)
-/

@[expose] public section

namespace Deformation

open CategoryTheory
open IsLocalRing

universe u v w uF vF

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}

private alias completeLocalAlgCat_hom_isIso :=
    Deformation.CompleteLocalAlgCat.isIso_of_bijective_hom

/-- Any two minimal versal formal objects are isomorphic. -/
@[stacks 06T5 "uniqueness", sga "7 VI 1.20" "uniqueness", sga "7 VI 1.10" "(ii) uniqueness"]
public theorem isomorphic_of_isMinimalVersal (hp : IsPredeformationCategory p)
    (ξ η : FormalObject p) (hξ : IsMinimalVersal hp.cofibered ξ)
    (hη : IsMinimalVersal hp.cofibered η) :
    Nonempty (ξ ≅ η) := by
  obtain ⟨f⟩ := nonempty_hom_of_isVersal hp ξ η hξ.1
  obtain ⟨g⟩ := nonempty_hom_of_isVersal hp η ξ hη.1
  have hf : Function.Surjective f.base.hom := hη.2 ξ f
  obtain ⟨e, he⟩ := surjective_endomorphism_noetherian_isomorphism
    (R := ξ.base) (g.base.hom.comp f.base.hom) ((hξ.2 η g).comp hf)
  have hbij : Function.Bijective f.base.hom := by
    refine ⟨fun a b hab ↦ e.injective ?_, hf⟩
    rw [he a, he b]
    exact congrArg g.base.hom hab
  have : IsIso f.base := completeLocalAlgCat_hom_isIso f.base hbij
  let π := FormalObject.projection (p := p)
  have : IsCofiberedInGroupoids π :=
    formalObjectProjection_isCofiberedInGroupoids p hp.cofibered
  have := isStronglyCocartesian_of_isCofiberedInGroupoids ‹_› f.base f
    (IsHomLift.of_fac π f.base f rfl rfl (FormalObject.projection_map f).symm)
  have : IsIso f := Functor.IsStronglyCocartesian.isIso_of_base_isIso π f.base f
  exact ⟨asIso f⟩

end Deformation

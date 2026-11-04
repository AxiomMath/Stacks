module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral

/-!
# Finite étale covers and a universal homeomorphism

Base change of finite étale covers along a surjective morphism of schemes is faithful: two
morphisms of finite étale covers of the target that agree after base change already agree,
because they agree on the preimage of the diagonal, which is open and meets every component of
the source. A universal homeomorphism is surjective, so this applies to it.

## Main results

* `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_surjective` — base change of finite étale
  covers along a surjective morphism is faithful.
* `AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_universalHomeomorphism` — the same for a
  universal homeomorphism.

## Implementation notes

Faithfulness along a surjective morphism `f` is the specialization hypothesis of
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes` at its weakest:
every point of the target lies in the image of `f`, hence specializes to a point of the image,
namely itself.

Fullness and essential surjectivity of base change on finite étale covers along a universal
homeomorphism are not proved here; essential surjectivity is where the source invokes Stacks
Project, Tag 0BTP.

## References

* [Stacks Project, Tag 0BQN](https://stacks.math.columbia.edu/tag/0BQN)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Base change of finite étale covers along a surjective morphism is faithful.** Every point
of the target is in the image, hence specializes into it, so
`AlgebraicGeometry.faithful_finiteEtaleBaseChange_of_forall_exists_specializes` applies. -/
theorem faithful_finiteEtaleBaseChange_of_surjective (f : X ⟶ Y) [Surjective f] :
    (finiteEtaleBaseChange f).Faithful :=
  faithful_finiteEtaleBaseChange_of_forall_exists_specializes f
    fun y ↦ ⟨y, f.surjective y, specializes_refl y⟩

/-- **Stacks Project, Tag 0BQN, faithfulness of the base change functor.** Let `f : X ⟶ Y` be a
universal homeomorphism. Base change along `f` is faithful on finite étale covers: two morphisms
`V₁ ⟶ V₂` of finite étale covers of `Y` whose base changes `V₁ ×_Y X ⟶ V₂ ×_Y X` agree are
equal.

A universal homeomorphism is surjective, which is all that faithfulness uses. -/
@[stacks 0BQN "faithfulness of the base change functor `FÉt_Y ⥤ FÉt_X`"]
theorem faithful_finiteEtaleBaseChange_of_universalHomeomorphism (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (finiteEtaleBaseChange f).Faithful :=
  have : Surjective f :=
    ⟨(UniversalHomeomorphism.universally_isHomeomorph _ _ _ IsPullback.of_id_snd).surjective⟩
  faithful_finiteEtaleBaseChange_of_surjective f

end AlgebraicGeometry

end

end

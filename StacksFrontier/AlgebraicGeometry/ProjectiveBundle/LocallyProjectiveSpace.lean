module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSurjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeFlat

/-!
# Morphisms which are Zariski-locally on the target a projective space

Let `f : H ⟶ P` be a morphism of schemes which is Zariski-locally on `P` a projective space
bundle, `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace`: every point of `P` has an open
neighbourhood `V` with an isomorphism `f⁻¹V ≅ ℙᵐ_V` over `V`. Then `f` is flat, surjective, locally
of finite type and of relative dimension `m`, because each of these properties is local on the
target and holds for `ℙᵐ_V ⟶ V` (`AlgebraicGeometry.flat_projectiveSpaceOver`,
`AlgebraicGeometry.projectiveSpaceOver.surjective`,
`AlgebraicGeometry.locallyOfFiniteType_projectiveSpaceOver` and
`AlgebraicGeometry.relativeDimension_projectiveSpaceOver`).

These are the hypotheses under which `Stacks.Chow.flatPullbackChowOfRelativeDimension` pulls
Chow classes back along `f`, raising dimension by `m`; the source applies this to the morphism
`Sⁿ(X) ⟶ Pic^n_{X/k}` in the proof of Stacks 0FH9.

## Main definitions

* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace`: `f` is Zariski-locally on the target the
  projective space `ℙᵐ`.

## Main results

* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.flat`: `f` is flat.
* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.surjective`: `f` is surjective.
* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.locallyOfFiniteType`: `f` is locally of
  finite type.
* `Stacks.ProjectiveBundle.IsLocallyProjectiveSpace.relativeDimension`: `f` has relative
  dimension `m`.

## References

* [Stacks Project, Tag 0FH9](https://stacks.math.columbia.edu/tag/0FH9)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.ProjectiveBundle

variable {H P : Scheme.{u}} (f : H ⟶ P) (m : ℕ)

/-- **`f : H ⟶ P` is Zariski-locally on `P` the projective space `ℙᵐ`**: every point of `P` has
an open neighbourhood `V` with an isomorphism `f⁻¹V ≅ ℙᵐ_V` over `V`. -/
def IsLocallyProjectiveSpace : Prop :=
  ∀ y : P, ∃ (V : P.Opens) (_ : y ∈ V) (e : (f ⁻¹ᵁ V).toScheme ≅ projectiveSpaceOver m V.toScheme),
    e.hom ≫ (projectiveSpaceOver m V.toScheme ↘ V.toScheme) = f ∣_ V

variable {f m}

/-- A morphism property which is local on the target, respects isomorphisms and holds for all
`ℙᵐ_V ⟶ V` holds for a morphism which is Zariski-locally on the target the projective space. -/
private theorem IsLocallyProjectiveSpace.morphismProperty
    (hbundle : IsLocallyProjectiveSpace f m) (Q : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget Q] (hQ : ∀ V : Scheme.{u}, Q (projectiveSpaceOver m V ↘ V)) : Q f := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun y => ?_
  obtain ⟨V, hyV, e, he⟩ := hbundle y
  exact ⟨V, hyV, he ▸ (Q.cancel_left_of_respectsIso e.hom _).mpr (hQ _)⟩

/-- **A morphism which is Zariski-locally on the target a projective space is flat.** -/
theorem IsLocallyProjectiveSpace.flat
    (hbundle : IsLocallyProjectiveSpace f m) :
    Flat f :=
  have := isZariskiLocalAtTarget_flat.{u}
  hbundle.morphismProperty @Flat fun V => flat_projectiveSpaceOver m V

/-- **A morphism which is Zariski-locally on the target a projective space is surjective**: the
fibre over a point of a chart `V` is the fibre of `ℙᵐ_V ⟶ V`, which is nonempty. -/
theorem IsLocallyProjectiveSpace.surjective (hbundle : IsLocallyProjectiveSpace f m) :
    Surjective f := by
  refine ⟨fun y => ?_⟩
  obtain ⟨V, hyV, e, he⟩ := hbundle y
  obtain ⟨z, hz⟩ := (projectiveSpaceOver.surjective m V.toScheme).surj ⟨y, hyV⟩
  refine ⟨(f ⁻¹ᵁ V).ι (e.inv z), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, ← he, Scheme.Hom.comp_apply,
    ← Scheme.Hom.comp_apply e.inv, Iso.inv_hom_id_assoc, hz]
  rfl

/-- **A morphism which is Zariski-locally on the target a projective space is locally of finite
type.** -/
theorem IsLocallyProjectiveSpace.locallyOfFiniteType
    (hbundle : IsLocallyProjectiveSpace f m) :
    LocallyOfFiniteType f :=
  have := isZariskiLocalAtTarget_locallyOfFiniteType.{u}
  hbundle.morphismProperty @LocallyOfFiniteType fun V => locallyOfFiniteType_projectiveSpaceOver m V

/-- **A morphism which is Zariski-locally on the target a projective space `ℙᵐ` has relative
dimension `m`**: every nonempty fibre is equidimensional of dimension `m`. -/
theorem IsLocallyProjectiveSpace.relativeDimension
    (hbundle : IsLocallyProjectiveSpace f m) :
    haveI := hbundle.locallyOfFiniteType
    RelativeDimension f m := by
  have := hbundle.locallyOfFiniteType
  refine relativeDimension_of_forall_exists_morphismRestrict f fun y => ?_
  obtain ⟨V, hyV, e, he⟩ := hbundle y
  exact ⟨V, hyV, inferInstance, relativeDimension_of_iso_over e _ _ he
    (relativeDimension_projectiveSpaceOver m V.toScheme)⟩

end Stacks.ProjectiveBundle

end

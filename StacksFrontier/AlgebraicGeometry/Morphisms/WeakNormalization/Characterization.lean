module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.SeminormalCriterion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological

/-!
# Characterizations of seminormal and absolutely weakly normal schemes

A scheme is seminormal exactly when it equals its own seminormalization, and exactly when every
universal homeomorphism to it from a reduced scheme inducing isomorphisms on residue fields is
an isomorphism. Dropping the condition on residue fields characterizes absolute weak normality
in the same two ways.

## Main results

* `AlgebraicGeometry.isSeminormal_iff_isIso_seminormalizationHom` and
  `AlgebraicGeometry.isSeminormal_iff_isIso_of_universalHomeomorphism` are conditions (2) and
  (3) of Stacks Tag 0H3G, each compared with condition (1).
* `AlgebraicGeometry.isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom'` and
  `AlgebraicGeometry.isAbsolutelyWeaklyNormal_iff_isIso_of_universalHomeomorphism'` are the same
  two comparisons for Stacks Tag 0H3H.

## Implementation notes

Both tags presuppose the construction of the seminormalization, respectively of the absolute
weak normalization, which is Stacks Tag 0EUS. For the seminormalization that construction is
unconditional: `AlgebraicGeometry.hasInitial_seminormalizationCategory` is a global instance
producing the initial seminormalization candidate over an arbitrary scheme by affine gluing, so
the two statements of Tag 0H3G below carry no hypothesis on `X` at all. In particular the
locality hypothesis `AlgebraicGeometry.HasLocallyInitialSeminormalizationCategory X`, which the
proof of the characterization `AlgebraicGeometry.isIso_initialTo_iff_isSeminormal` needs to run
the reduction to the affine case, is not a hypothesis of that characterization as finally
stated and so is not a hypothesis here either.

For the absolute weak normalization the corresponding class
`AlgebraicGeometry.HasLocallyInitialUniversalHomeomorphismOver X` likewise has an instance over
an arbitrary scheme, `AlgebraicGeometry.hasInitialUniversalHomeomorphismOver`, which this file
reaches through `StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.Functorial`. The two
comparisons for Tag 0H3H are proved below first in the form that takes that class as an
instance argument, matching the reduction to the affine case they run, and are then restated as
`AlgebraicGeometry.isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom'` and
`AlgebraicGeometry.isAbsolutelyWeaklyNormal_iff_isIso_of_universalHomeomorphism'`, which take
only `X : Scheme.{u}` because that instance supplies the argument. The primed pair is what
carries Tag 0H3H, so the tag is registered at the source lemma's own hypotheses; between them
they give the three-way equivalence of the source.

The remaining half of Stacks Tag 0EUS — that the canonical map from the seminormalization,
respectively the absolute weak normalization, of `X` to a candidate `Y ⟶ X` is an isomorphism
precisely when `Y` is seminormal, respectively absolutely weakly normal — is
`AlgebraicGeometry.isIso_initialTo_iff_isSeminormal` and
`AlgebraicGeometry.isIso_initialTo_iff_isAbsolutelyWeaklyNormal`.

Given the comparison of (1) with (2), the implication (1) ⟹ (3) is the observation that a
section of a universal homeomorphism `π` is an isomorphism: `π` is injective, hence separated,
so a section of it is a closed immersion, and it is surjective because `π` is injective; a
surjective closed immersion onto a reduced scheme is an isomorphism. The converse applies the
hypothesis to the initial object itself, which is its own canonical map and so trivially an
isomorphism.

## References

* [Stacks Project, Tag 0H3G](https://stacks.math.columbia.edu/tag/0H3G)
* [Stacks Project, Tag 0H3H](https://stacks.math.columbia.edu/tag/0H3H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A universal homeomorphism from a reduced scheme is an isomorphism if some isomorphism to
the base factors through it. -/
private theorem isIso_of_comp_eq_isIso_of_universalHomeomorphism {X Y Z : Scheme.{u}}
    (π : Y ⟶ X) (hπ : UniversalHomeomorphism π) (hY : IsReduced Y) (f : Z ⟶ X) [IsIso f]
    (t : Z ⟶ Y) (ht : t ≫ π = f) : IsIso π := by
  have hs : (inv f ≫ t) ≫ π = 𝟙 X := by rw [Category.assoc, ht, IsIso.inv_hom_id]
  generalize inv f ≫ t = s at hs
  have htop : IsHomeomorph π.base :=
    MorphismProperty.universally_le (topologically @IsHomeomorph) π hπ.universally_isHomeomorph
  have : IsSeparated π := isSeparated_of_injective π htop.injective
  have : IsClosedImmersion (s ≫ π) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s π
  have : IsReduced Y := hY
  have : Surjective s := ⟨fun y ↦ ⟨π.base y, htop.injective <| by
    simpa [Scheme.Hom.comp_base] using congrArg (fun g : X ⟶ X ↦ g (π.base y)) hs⟩⟩
  have : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  exact isIso_of_hom_comp_eq_id s hs

/-- **Stacks Project, Tag 0H3G.** A scheme is seminormal if and only if its canonical
seminormalization morphism is an isomorphism, i.e. if and only if it equals its own
seminormalization. -/
@[stacks 0H3G "conditions (1) and (2)"]
theorem isSeminormal_iff_isIso_seminormalizationHom (X : Scheme.{u}) :
    IsSeminormal X ↔ IsIso X.seminormalizationHom := by
  let obj : SeminormalizationCategory X :=
    ⟨Over.mk (𝟙 X), Stacks.Thickenings.universalHomeomorphism_id X, fun x ↦ by
      show IsIso (Scheme.Hom.residueFieldMap (𝟙 X) x); infer_instance⟩
  have heq : (initial.to obj).hom.left = X.seminormalizationHom := by
    simpa [obj] using (initial.to obj).hom.w
  rw [← heq]
  exact (isIso_initialTo_iff_isSeminormal X obj).symm

/-- **Stacks Project, Tag 0H3G.** A scheme is seminormal if and only if every universal
homeomorphism to it from a reduced scheme inducing isomorphisms on all residue fields is an
isomorphism. -/
@[stacks 0H3G "conditions (1) and (3)"]
theorem isSeminormal_iff_isIso_of_universalHomeomorphism (X : Scheme.{u}) :
    IsSeminormal X ↔
      ∀ (Y : Scheme.{u}) (π : Y ⟶ X), UniversalHomeomorphism π →
        (∀ y : Y, IsIso (π.residueFieldMap y)) → IsReduced Y → IsIso π := by
  constructor
  · intro hX Y π hπ hres hY
    let obj : SeminormalizationCategory X := ⟨Over.mk π, hπ, hres⟩
    have hiso : IsIso X.seminormalizationHom :=
      (isSeminormal_iff_isIso_seminormalizationHom X).mp hX
    exact isIso_of_comp_eq_isIso_of_universalHomeomorphism π hπ hY _ _ (initial.to obj).hom.w
  · intro hπ
    let sn : SeminormalizationCategory X := initial (SeminormalizationCategory X)
    have hsn : IsSeminormal X.seminormalization := by
      refine (isIso_initialTo_iff_isSeminormal X sn).mp ?_
      rw [show initial.to sn = 𝟙 sn from Subsingleton.elim _ _]
      show IsIso (𝟙 sn.obj.left)
      infer_instance
    exact (isSeminormal_iff_isIso_seminormalizationHom X).mpr
      (hπ X.seminormalization X.seminormalizationHom sn.property.1 sn.property.2
        (seminormal_isReduced hsn))

/-- A scheme whose universal homeomorphisms have locally initial absolute weak normalization is
absolutely weakly normal if and only if its canonical absolute weak normalization morphism is an
isomorphism. The instance argument is redundant and is dropped in
`AlgebraicGeometry.isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom'`, which is
the form registered for Stacks Tag 0H3H. -/
theorem isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom (X : Scheme.{u})
    [HasLocallyInitialUniversalHomeomorphismOver X] :
    IsAbsolutelyWeaklyNormal X ↔ IsIso X.absoluteWeakNormalizationHom := by
  let obj : UniversalHomeomorphismOver X :=
    ⟨Over.mk (𝟙 X), Stacks.Thickenings.universalHomeomorphism_id X⟩
  have heq : (initial.to obj).hom.left = X.absoluteWeakNormalizationHom := by
    simpa [obj] using (initial.to obj).hom.w
  rw [← heq]
  exact (isIso_initialTo_iff_isAbsolutelyWeaklyNormal X obj).symm

/-- **Stacks Project, Tag 0H3H.** A scheme is absolutely weakly normal if and only if its
canonical absolute weak normalization morphism is an isomorphism, i.e. if and only if it equals
its own absolute weak normalization. -/
@[stacks 0H3H "conditions (1) and (2)"]
theorem isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom' (X : Scheme.{u}) :
    IsAbsolutelyWeaklyNormal X ↔ IsIso X.absoluteWeakNormalizationHom :=
  isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom X

/-- A scheme whose universal homeomorphisms have locally initial absolute weak normalization is
absolutely weakly normal if and only if every universal homeomorphism to it from a reduced
scheme is an isomorphism. The instance argument is redundant and is dropped in
`AlgebraicGeometry.isAbsolutelyWeaklyNormal_iff_isIso_of_universalHomeomorphism'`, which is the
form registered for Stacks Tag 0H3H. -/
theorem isAbsolutelyWeaklyNormal_iff_isIso_of_universalHomeomorphism (X : Scheme.{u})
    [HasLocallyInitialUniversalHomeomorphismOver X] :
    IsAbsolutelyWeaklyNormal X ↔
      ∀ (Y : Scheme.{u}) (π : Y ⟶ X), UniversalHomeomorphism π → IsReduced Y → IsIso π := by
  constructor
  · intro hX Y π hπ hY
    let obj : UniversalHomeomorphismOver X := ⟨Over.mk π, hπ⟩
    have hiso : IsIso X.absoluteWeakNormalizationHom :=
      (isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom X).mp hX
    exact isIso_of_comp_eq_isIso_of_universalHomeomorphism π hπ hY _ _ (initial.to obj).hom.w
  · intro hπ
    let awn : UniversalHomeomorphismOver X := initial (UniversalHomeomorphismOver X)
    have hawn : IsAbsolutelyWeaklyNormal X.absoluteWeakNormalization := by
      refine (isIso_initialTo_iff_isAbsolutelyWeaklyNormal X awn).mp ?_
      rw [show initial.to awn = 𝟙 awn from Subsingleton.elim _ _]
      show IsIso (𝟙 awn.obj.left)
      infer_instance
    exact (isAbsolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationHom X).mpr
      (hπ X.absoluteWeakNormalization X.absoluteWeakNormalizationHom awn.property
        (absolutelyWeaklyNormal_isReduced hawn))

/-- **Stacks Project, Tag 0H3H.** A scheme is absolutely weakly normal if and only if every
universal homeomorphism to it from a reduced scheme is an isomorphism. -/
@[stacks 0H3H "conditions (1) and (3)"]
theorem isAbsolutelyWeaklyNormal_iff_isIso_of_universalHomeomorphism' (X : Scheme.{u}) :
    IsAbsolutelyWeaklyNormal X ↔
      ∀ (Y : Scheme.{u}) (π : Y ⟶ X), UniversalHomeomorphism π → IsReduced Y → IsIso π :=
  isAbsolutelyWeaklyNormal_iff_isIso_of_universalHomeomorphism X

end AlgebraicGeometry

end

module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism

/-!
# Full faithfulness of small étale direct image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `f_*` and `f⁻¹`
be the direct and inverse images on small étale sheaves of sets, that is, the two functors of
the morphism of small étale topoi of Stacks 03G2, part (3).  This file identifies full
faithfulness of `f_*` with invertibility of the adjunction map `f⁻¹f_*G → G`, and, once that
holds, identifies the essential image of `f_*` with the sheaves at which the other adjunction
map `F → f_*f⁻¹F` is invertible.

Both identifications hold for an arbitrary morphism of algebraic spaces and are formal
consequences of the adjunction `f⁻¹ ⊣ f_*`.  They are the shape in which Stacks 04E5 is proved
for a closed immersion `i : Z → X`: the source shows that `i⁻¹i_*G → G` is an isomorphism for
every sheaf `G` on `Z_étale` by reducing to a scheme chart, and then deduces full faithfulness
of `i_{small,*}` and the characterization of its essential image from the adjunction alone.

## Main results

* `AlgebraicGeometry.Space.full_pushforward_of_isIso_counit` and
  `AlgebraicGeometry.Space.faithful_pushforward_of_isIso_counit`: **small étale direct image is
  full and faithful as soon as the adjunction map `f⁻¹f_*G → G` is an isomorphism for every
  `G`.**
* `AlgebraicGeometry.Space.full_and_faithful_pushforward_iff_isIso_counit`: conversely, if
  direct image is full and faithful then that map is an isomorphism, by Mathlib's instance
  `CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful`; so **the inverse image is a left
  inverse of the direct image exactly when the direct image is fully faithful.**
* `AlgebraicGeometry.Space.mem_essImage_pushforward_iff_isIso_unit`: for a fully faithful
  direct image, a sheaf on `Y_étale` lies in its essential image exactly when the adjunction
  map `F → f_*f⁻¹F` is an isomorphism.

## Implementation notes

The direct and inverse images are the fields of
`AlgebraicGeometry.Space.smallToposMorphism`, whose adjunction `f⁻¹ ⊣ f_*` has the inverse
image as its left adjoint; `f⁻¹f_*G → G` is therefore the counit at `G` and `F → f_*f⁻¹F` the
unit at `F`.  Sheaves of sets are valued in `Type (u + 1)`, the universe in which both étale
sites of an algebraic space over `Scheme.{u}` have their objects, as for the morphism of topoi
itself.

Nothing below uses a property of `f`, so all four statements are about an arbitrary morphism of
algebraic spaces rather than about a closed immersion.

## What is not proved

That `f⁻¹f_*G → G` is an isomorphism, which by the equivalence below is the whole of full
faithfulness, is *not* formal and is not proved here.  For a closed immersion it is the
assertion of Stacks 04E5, and the source obtains it from the corresponding statement for a
closed immersion of schemes, Étale Cohomology Proposition 04CA, through the compatibility of
small étale direct image with restriction to an étale scheme chart, Stacks 03LR; neither is
available in the library.  The identification of the essential image by a condition away from
`Z` — triviality of the restriction to the open complement for sheaves of sets, and containment
of the support in `|Z|` for abelian sheaves — needs the same two inputs, and in addition the
abelian clause of Stacks 04E5 needs the inverse image on abelian sheaves, whose existence for
small étale sites of algebraic spaces the library does not record.

## References

* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Small étale direct image along `f` is full and faithful as soon as `f⁻¹f_*G → G` is an
isomorphism for every sheaf `G`. -/
private theorem full_and_faithful_pushforward_of_isIso_counit
    (h : ∀ G, IsIso ((smallToposMorphism B S hS f).adj.counit.app G)) :
    (smallToposMorphism B S hS f).pushforward.Full ∧
      (smallToposMorphism B S hS f).pushforward.Faithful :=
  have := h
  have : IsIso (smallToposMorphism B S hS f).adj.counit := NatIso.isIso_of_isIso_app _
  ⟨(smallToposMorphism B S hS f).adj.fullyFaithfulROfIsIsoCounit.full,
    (smallToposMorphism B S hS f).adj.fullyFaithfulROfIsIsoCounit.faithful⟩

/-- Small étale direct image along `f` is full as soon as `f⁻¹f_*G → G` is an isomorphism for
every sheaf `G` on the small étale site of `X`. -/
theorem full_pushforward_of_isIso_counit
    (h : ∀ G, IsIso ((smallToposMorphism B S hS f).adj.counit.app G)) :
    (smallToposMorphism B S hS f).pushforward.Full :=
  (full_and_faithful_pushforward_of_isIso_counit B S hS f h).1

/-- Small étale direct image along `f` is faithful as soon as `f⁻¹f_*G → G` is an isomorphism
for every sheaf `G` on the small étale site of `X`. -/
theorem faithful_pushforward_of_isIso_counit
    (h : ∀ G, IsIso ((smallToposMorphism B S hS f).adj.counit.app G)) :
    (smallToposMorphism B S hS f).pushforward.Faithful :=
  (full_and_faithful_pushforward_of_isIso_counit B S hS f h).2

/-- **Full faithfulness of small étale direct image is invertibility of `f⁻¹f_*G → G`.**  This
is the step by which Stacks 04E5 passes from the computation of that adjunction map to full
faithfulness of the direct image along a closed immersion. -/
theorem full_and_faithful_pushforward_iff_isIso_counit :
    ((smallToposMorphism B S hS f).pushforward.Full ∧
        (smallToposMorphism B S hS f).pushforward.Faithful) ↔
      ∀ G, IsIso ((smallToposMorphism B S hS f).adj.counit.app G) :=
  ⟨fun ⟨_, _⟩ _ => inferInstance,
    full_and_faithful_pushforward_of_isIso_counit B S hS f⟩

/-- **The essential image of a fully faithful small étale direct image.**  A sheaf `F` on the
small étale site of `Y` is a direct image exactly when the adjunction map `F → f_*f⁻¹F` is an
isomorphism. -/
theorem mem_essImage_pushforward_iff_isIso_unit
    [(smallToposMorphism B S hS f).pushforward.Full]
    [(smallToposMorphism B S hS f).pushforward.Faithful]
    (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1))) :
    (smallToposMorphism B S hS f).pushforward.essImage F ↔
      IsIso ((smallToposMorphism B S hS f).adj.unit.app F) :=
  (Adjunction.isIso_unit_app_iff_mem_essImage _).symm

end AlgebraicGeometry.Space

end

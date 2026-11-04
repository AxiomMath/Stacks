module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalenceObstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDirectImageChartEqualizer

/-!
# The direct image of the structure sheaf has sections below the cutoff, for every morphism

`AlgebraicGeometry.Space.AlgebraSheaf.SectionsBelowCutoff` is the size condition of the bounded
form of Stacks 081V: a sheaf of `𝒪_X`-algebras satisfies it when its ring of sections over every
étale scheme chart of `X` has fewer than `B.cutoff` elements. It holds for the direct-image
algebra `f_* 𝒪_Y` of an arbitrary morphism `f : Y ⟶ X` of algebraic spaces of the site, with no
hypothesis of affineness, quasi-compactness, quasi-separatedness or representability on `f`.

For `V` an étale scheme chart of `X`, Tag 03H7 in the shape of
`AlgebraicGeometry.Space.exists_smallEtaleDirectImageChartEqualizerEquiv` produces étale scheme
charts `W`, `W'` of `Y` and two morphisms `a, b : W' ⟶ W` with

`(f_* 𝒪_Y)(V) ≃ {y ∈ 𝒪_Y(W) | a^* y = b^* y}`,

an equalizer and in particular a subtype of `𝒪_Y(W) = Γ(W, 𝒪_W)`. The chart `W` is an object
of the site, so `AlgebraicGeometry.Space.mk_sections_lt_cutoff` bounds its regular functions by
the cutoff, and a subtype is no larger.

## Main results

* `AlgebraicGeometry.Space.mk_sections_smallEtaleDirectImage_lt_of_forall`: for a sheaf of sets
  `P` and a cardinal `κ`, if the sections of `P` over every étale scheme chart of `Y` are fewer
  than `κ`, then so are the sections of `AlgebraicGeometry.Space.smallEtaleDirectImage` of `P`
  over every étale scheme chart of `X`.
* `AlgebraicGeometry.Space.sectionsBelowCutoff_pushforwardAlgebra`: the size side-condition of
  the bounded form of Stacks 081V holds for `f_* 𝒪_Y`, for every morphism `f`.

## Implementation notes

The sections over `V` of `AlgebraicGeometry.Space.pushforwardAlgebra` are, definitionally, the
sections over `V` of `AlgebraicGeometry.Space.smallEtaleDirectImage` of the sheaf of sets
underlying `𝒪_Y`: the algebra is `AlgebraicGeometry.Space.AlgebraSheaf.ofHom` of the structure
map of `AlgebraicGeometry.Space.smallEtaleRingedToposHom`, whose codomain is the image of `𝒪_Y`
under `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor`, and that functor transports
the ring operations sectionwise onto the topos direct image of the underlying sheaf of sets.

No identification of `(f_* 𝒪_Y)(V)` with regular functions is used; such a formula
(`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, Stacks 03G8) needs `f` representable.
`AlgebraicGeometry.Space.mk_sections_lt_cutoff` spends one power of two through
`AlgebraicGeometry.Scheme.mk_sections_le_two_pow_size`, because the covering chart `W` of
`Y ×_X V` need not be affine, and `AlgebraicGeometry.BigFppfSite.cutoff_isStrongPrelimit`
absorbs it; no regularity of the cutoff is used.

## References

* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A bound on the sections of a sheaf over every étale scheme chart passes to its direct
image**, along an arbitrary morphism of algebraic spaces. -/
theorem mk_sections_smallEtaleDirectImage_lt_of_forall {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) {κ : Cardinal.{u}}
    (hP : ∀ W : SmallEtale B S hS X.1, #(P.obj.obj (op W)) < κ)
    (V : SmallEtale B S hS Y.1) :
    #(((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) < κ := by
  obtain ⟨W, W', a, b, ⟨e⟩⟩ :=
    exists_smallEtaleDirectImageChartEqualizerEquiv B S hS f P V
  exact ((mk_congr e).trans_le (mk_subtype_le _)).trans_lt (hP W)

/-- **The size side-condition of the bounded form of Stacks 081V, for an arbitrary morphism.**
The direct-image algebra `f_* 𝒪_Y` of any morphism `f : Y ⟶ X` of algebraic spaces of the site
has fewer than `B.cutoff` sections over every étale scheme chart of `X`. -/
theorem sectionsBelowCutoff_pushforwardAlgebra {X : AlgebraicSpaces B S hS} (Y : Over X) :
    AlgebraSheaf.SectionsBelowCutoff B S hS (pushforwardAlgebra B S hS Y) := fun V ↦ by
  show #(((smallEtaleDirectImage B S hS Y.hom).obj
    ((smallEtaleRingedTopos B S hS Y.left).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y.left).O)).obj.obj (op V)) < B.cutoff
  exact mk_sections_smallEtaleDirectImage_lt_of_forall B S hS Y.hom _
    (fun W ↦ mk_sections_lt_cutoff B W.obj.left.left.property ⊤) V

end AlgebraicGeometry.Space

end

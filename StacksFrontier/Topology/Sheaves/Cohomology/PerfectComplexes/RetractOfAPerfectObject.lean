module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.DirectSummands
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension

/-!
# A retract of a perfect object of `D(O_X)` is perfect

Let `(X, O_X)` be a ringed space and let `M` be a *retract* of an object `K` of `D(O_X)`: there
are `i : M ⟶ K` and `r : K ⟶ M` with `i ≫ r = 𝟙 M`. If `K` is perfect then so is `M`.

Tag 08CS is the biproduct form of this — both summands of a perfect biproduct are perfect — and
it is already proved, unconditionally and at the same universes, as
`Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`. The retract form is strictly more usable:
a retract is what a factorization argument produces, and nothing in the development turned a
retract in `D(O_X)` into a biproduct decomposition. That step is supplied here, once, in the
generality in which it is true — any pretriangulated category — and the ringed-space consequences
are read off it.

Nothing below is a clause of a tag. The biproduct form of 08CS carries the tag where it is
proved; these are strengthenings and reductions, so no `@[stacks …]` attribute is attached.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction`: in a pretriangulated
  category, a retract is a direct summand. The map `i` is a split mono, hence a mono, hence the
  connecting map of the distinguished triangle on `i` vanishes
  (`CategoryTheory.Pretriangulated.Triangle.mor₃_eq_zero_of_mono₁`), and a distinguished triangle
  with vanishing connecting map is a biproduct
  (`CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`). The isomorphism
  carries `i` to `biprod.inl`.
* `Stacks.Cohomology.PerfectDirectSummands.isPerfect_Q_obj_of_isStrictlyPerfect`: a strictly
  perfect complex represents a perfect object, in the Tag 08CM spelling
  `Stacks.Cohomology.PerfectComplexes.IsPerfect`. The one-member covering `{X}` of `X` serves,
  with the identity as its quasi-isomorphism.
* `Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract`: **a retract of a perfect object
  is perfect**, with no hypothesis beyond the retraction. This is the form that the direct-summand
  step of Stacks 0FPD consumes.

## Implementation notes

The splitting of a retract in a pretriangulated category has been written out inline twice in
this development — once as the `private`
`CategoryTheory.Pretriangulated.exists_complement_of_section` of
`StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant`, phrased as a splitting of the
complementary idempotent, and once inside the `private`
`StacksDraft.Perfect.isPerfect_isStableUnderRetracts` of
`StacksFrontier.Homology.Perfect.Characterizing` — and neither is reachable. The abelian-category
statement `CategoryTheory.exists_iso_biprod_of_retract` of
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardStrictlyPerfect` is public but does not
apply: `D(O_X)` is not abelian. Hence the public pretriangulated statement here.

`Mono i` is proved by hand rather than through `CategoryTheory.IsSplitMono`: the goal that
`CategoryTheory.Pretriangulated.Triangle.mor₃_eq_zero_of_mono₁` presents is
`Mono (Triangle.mk i p d).mor₁`, and instance synthesis does not unfold the projection out of
`Triangle.mk` at the transparency it uses, so an instance on `i` is not found even when it is
available. The two-line cancellation is cheaper than arranging for it to be seen.

`Stacks.Cohomology.PerfectComplexes.IsPerfect` is the Tag 08CM spelling, for a ringed space; the
ringed-*site* spelling `AlgebraicGeometry.RingedSite.IsPerfect` of Tag 08G5 is a different
predicate; the two are in fact equivalent on a ringed space, by
`Stacks.Cohomology.PerfectComplexes.isPerfect_of_ringedSite` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectnessFromTheRingedSite` and
`isPerfect_ringedSite_of_isPerfect` of `…PerfectComplexes.RingedSitePerfectnessFromTheSpace`.
The space
spelling is the one used here because the apparatus this file needs — Tag 08CQ in both
directions, Tag 08CS, Tag 08CE, Tag 08CK and the locality of perfectness of Tag 08CR — is
stated for a ringed space at a general universe `u`.

On the *site* side, the locality of perfectness,
`AlgebraicGeometry.RingedSite.isPerfect_of_locally`, is stated at `RingedSite.{u, u, w}`, the
sections of the structure sheaf at an arbitrary universe, and
`torAmplitudePerfectnessCriterion` and the Tag 08GA summand lemmas are stated at the diagonal
`RingedSite.{u, u, u}` — see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/PerfectnessCriterion.lean` — so the
site-side counterpart of `isPerfect_of_retract` below is available, as
`Stacks.SheafOfModules.DerivedTensorProduct.isPerfect_of_retract` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Retracts`, which reuses the pretriangulated
splitting proved here.

The space, ring and module universes coincide, as they already must for Tag 08CQ and for the
locality of perfectness; the derived categories are any models.

## References

* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

universe v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- **A retract in a pretriangulated category is a direct summand.** If `i : A ⟶ M` admits a
retraction `r`, then `M` decomposes as `A ⊞ Z` for some `Z`, by an isomorphism carrying `i` to
`biprod.inl`.

A map with a retraction is a monomorphism, and the connecting map of a distinguished triangle
whose first map is a monomorphism vanishes; a distinguished triangle with vanishing connecting
map exhibits its second vertex as the biproduct of the other two. The complement `Z` is the cone
of `i`. -/
theorem exists_iso_biprod_of_retraction {A M : C} (i : A ⟶ M) (r : M ⟶ A) (hir : i ≫ r = 𝟙 A) :
    ∃ (Z : C) (e : M ≅ A ⊞ Z), i ≫ e.hom = biprod.inl := by
  obtain ⟨Z, p, d, hT⟩ := distinguished_cocone_triangle i
  have hmono : Mono i :=
    ⟨fun {_} g h hgh => by
      rw [← Category.comp_id g, ← hir, ← Category.assoc, hgh, Category.assoc, hir,
        Category.comp_id]⟩
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i p d) hT
    (Triangle.mor₃_eq_zero_of_mono₁ (Triangle.mk i p d) hT hmono)
  exact ⟨Z, e, he⟩

end CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.PerfectDirectSummands

universe d d'

variable {X : RingedSpace.{u, u}}

open AlgebraicGeometry.RingedSpace.PseudoCoherence in
/-- **A strictly perfect complex represents a perfect object**, in the Tag 08CM spelling
`Stacks.Cohomology.PerfectComplexes.IsPerfect`.

The complex is its own perfect-complex witness: the one-member covering `{X}` of `X` has the
restriction of the complex to `X` itself as its strictly perfect model
(`AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_restrictComplex`), with the
identity as the quasi-isomorphism.

The companion `AlgebraicGeometry.RingedSpace.isPerfect_Q_obj_of_isStrictlyPerfect` of
`StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.BasicProperties` is the same statement
for `AlgebraicGeometry.RingedSpace.IsPerfect`, a second, untagged spelling of perfectness on a
ringed space; nothing in the development relates the two, so it does not serve here. -/
theorem isPerfect_Q_obj_of_isStrictlyPerfect [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (hP : IsStrictlyPerfect P) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (DerivedCategory.Q.obj P) :=
  ⟨P, ⟨PUnit.{u + 1}, fun _ => ⊤, by simp, fun _ =>
    ⟨AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P ⊤,
      isStrictlyPerfect_restrictComplex X ⊤ hP, 𝟙 _, inferInstance⟩⟩,
    ⟨Iso.refl _⟩⟩

/-- **A retract of a perfect object of `D(O_X)` is perfect.** If `i : M ⟶ K` has a retraction and
`K` is perfect, then `M` is perfect.

The retract is turned into a direct summand by
`CategoryTheory.Pretriangulated.exists_iso_biprod_of_retraction` — `D(O_X)` is pretriangulated —
and then Tag 08CS, `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`, applies. Perfectness is
closed under isomorphism, `Stacks.Cohomology.PerfectComplexes.isClosedUnderIsomorphisms_isPerfect`,
so the decomposition may be used to transport the hypothesis.

This is the conclusion half of the direct-summand step of the proof of Stacks 0FPD, conclusion
(a): there `M` is exhibited as a retract of a subcomplex of a representative of itself, through a
factorization of the coevaluation of an exact pairing, and perfectness of `M` is read off
perfectness of that subcomplex. The monoidal half of that step is
`CategoryTheory.ExactPairing.retractOfCoevaluationFactors`. -/
theorem isPerfect_of_retract [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    [∀ V : Opens X.carrier, HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict V.isOpenEmbedding))]
    {M K : DerivedCategory (OXMod.{u, u} X)} (i : M ⟶ K) (r : K ⟶ M) (hir : i ≫ r = 𝟙 M)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect M := by
  obtain ⟨Z, e, -⟩ := exists_iso_biprod_of_retraction i r hir
  exact (Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod M Z
    (ObjectProperty.prop_of_iso
      (fun L : DerivedCategory (OXMod.{u, u} X) =>
        Stacks.Cohomology.PerfectComplexes.IsPerfect L) e hK)).1

end Stacks.Cohomology.PerfectDirectSummands

end

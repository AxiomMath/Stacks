module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReduction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSolution

/-!
# One finite extension solving every bad generic point of a fibre

Let `A` be a Dedekind domain with fraction field `K` and let `f : X ⟶ Spec A` be flat,
quasi-compact and locally of finite type with `X` normal. Assume the generic fibre of `f` carries
a dense open subscheme smooth over `K`. Call a point `x : X` *bad* when it lies outside the
smooth locus of `f`, is a generic point of an irreducible component of its own fibre, and that
fibre is not the generic one. **Then a single finite extension `K₁/K` is a solution for the
extension of discrete valuation rings `A_x → 𝒪_{X, x}` at every bad point at once.**

This is the second and third paragraphs of the proof of the reduced fibre theorem, with the
finite family of bad points *produced* rather than supplied: the density hypothesis bounds the
bad locus (`AlgebraicGeometry.finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber`), and
elimination of ramification then serves the resulting finite family by a single extension
(`AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk`).

## Main results

* `AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth`: one
  finite extension of `K` is a solution for `A_x → 𝒪_{X, x}` at every bad point `x`.

## Implementation notes

`AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk` indexes its points by a type
in `Type`, while the bad locus is a subset of the carrier of a scheme in `Type u`; the bad locus
is therefore enumerated by `Fin n` through `Fintype.equivFin`, and the conclusion at an arbitrary
bad point is transported back along the resulting equality of points. That transport is
`AlgebraicGeometry.isSolutionForStalk_congr`: the two hypotheses `hs` and `hg` of
`AlgebraicGeometry.IsSolutionForStalk` are propositions, so once the points agree the two
instances of the predicate agree by proof irrelevance.

The hypothesis that the fibre through `x` is not the generic one is recorded as
`(f.base x).asIdeal ≠ ⊥`, as in `AlgebraicGeometry.IsSolutionForStalk`. It is a hypothesis of the
conclusion rather than a consequence of badness, and the bad locus enumerated in the proof is cut
down by it.

Finite presentation of `f` is not an extra hypothesis: a morphism locally of finite type to the
spectrum of a Noetherian ring is locally of finite presentation, which is what names the smooth
locus.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 054X](https://stacks.math.columbia.edu/tag/054X)
* [Stacks Project, Tag 09II](https://stacks.math.columbia.edu/tag/09II)
* [Stacks Project, Tag 0GLR](https://stacks.math.columbia.edu/tag/0GLR)
-/

public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsDedekindDomain A]
  (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f] [LocallyOfFiniteType f] [IsNormal X]

/-- **The solution property only depends on the point.** The two hypotheses of
`AlgebraicGeometry.IsSolutionForStalk` are propositions, so for equal points the predicate
transports along the equality by proof irrelevance. -/
theorem isSolutionForStalk_congr {x y : X} (h : x = y)
    (hsx : (f.base x).asIdeal ≠ ⊥)
    (hgx : f.asFiber x ∈ genericPoints (f.fiber (f.base x)))
    (hsy : (f.base y).asIdeal ≠ ⊥)
    (hgy : f.asFiber y ∈ genericPoints (f.fiber (f.base y)))
    (K₁ : Type u) [Field K₁] [Algebra K K₁] [Module.Finite K K₁]
    (H : IsSolutionForStalk K f x hsx hgx K₁) :
    IsSolutionForStalk K f y hsy hgy K₁ := by
  subst h
  exact H

/-- **One finite extension solving every bad generic point at once.** Let `A` be a Dedekind
domain with fraction field `K` and let `f : X ⟶ Spec A` be flat, quasi-compact and locally of
finite type with `X` normal. If the generic fibre of `f` has a dense open subscheme `U` smooth
over the residue field of the generic point of `Spec A`, then there is a finite extension `K₁/K`
which is a solution for the extension of discrete valuation rings `A_x → 𝒪_{X, x}` for *every*
point `x` outside the smooth locus of `f` which is a generic point of an irreducible component
of its own fibre, that fibre not the generic one.

The density hypothesis leaves only finitely many such points, by Tag 054X in the form
`AlgebraicGeometry.finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber`, and a single finite
extension serves a finite family of them by Tag 09II together with Tag 0GLR, in the form
`AlgebraicGeometry.exists_finite_extension_forall_isSolution_stalk`.

This is the second and third paragraphs of the proof of Tag 09IL, for a dense smooth open of the
generic fibre that is already available. Going down for the integral morphism `Y ⟶ X` rests on
normality of `X`, not on its finiteness: a finite morphism does not preserve coheight, as the
closed immersion of a closed point into a curve shows. The full statement of that tag is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`. -/
theorem exists_finite_extension_forall_isSolution_stalk_of_dense_open_smooth [QuasiCompact f]
    (U : (f.fiber (genericPoint (Spec (.of A)))).Opens)
    (hU : Dense (U : Set (f.fiber (genericPoint (Spec (.of A))))))
    (hsmooth : Smooth (U.ι ≫ f.fiberToSpecResidueField (genericPoint (Spec (.of A))))) :
    letI : LocallyOfFinitePresentation f := inferInstance
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Module.Finite K K₁),
      ∀ x : X, x ∉ f.smoothLocus → ∀ (hs : (f.base x).asIdeal ≠ ⊥)
        (hg : f.asFiber x ∈ genericPoints (f.fiber (f.base x))),
        IsSolutionForStalk K f x hs hg K₁ := by
  classical
  set S : Set X := {x : X | (x ∉ f.smoothLocus ∧
    f.asFiber x ∈ genericPoints (f.fiber (f.base x))) ∧ (f.base x).asIdeal ≠ ⊥}
  have hSfin : S.Finite :=
    (finite_setOf_notMem_smoothLocus_mem_genericPoints_fiber f U hU hsmooth).subset
      fun _ hx => hx.1
  let _ : Fintype ↥S := hSfin.fintype
  let e : ↥S ≃ Fin (Fintype.card ↥S) := Fintype.equivFin ↥S
  let x' : Fin (Fintype.card ↥S) → X := fun i => (e.symm i : X)
  obtain ⟨K₁, hfield, halg, hmodfin, hsol⟩ :=
    exists_finite_extension_forall_isSolution_stalk K f x'
      (fun i => (e.symm i).2.2) (fun i => (e.symm i).2.1.2)
  refine ⟨K₁, hfield, halg, hmodfin, fun x hx hs hg => ?_⟩
  have hxS : x ∈ S := ⟨⟨hx, hg⟩, hs⟩
  have hxe : x' (e ⟨x, hxS⟩) = x := congrArg Subtype.val (e.symm_apply_apply ⟨x, hxS⟩)
  exact isSolutionForStalk_congr K f hxe _ _ hs hg K₁ (hsol (e ⟨x, hxS⟩))

end AlgebraicGeometry

end

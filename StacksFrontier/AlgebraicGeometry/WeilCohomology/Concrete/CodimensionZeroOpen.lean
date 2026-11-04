module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition
public import StacksFrontier.AlgebraicGeometry.ClosedCoverGlue.Basic
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.Topology.Sober.SpecializationStableNeighborhood

/-!
# A smooth closed subscheme of codimension zero is open

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over a field `k` such that
every irreducible component of `Z` has codimension `0` in `X`, i.e. the image of the generic point
of each component of `Z` has coheight `0` in `X` (the form of the hypothesis of Lemma 0FIH used
by `Stacks.WeilCohomology.SmoothProjectiveScheme.relativeDimension_of_codimension`). Then `i`
is an open immersion. This is the case `r = 0` of Lemma 0FII.

The image of `i` is closed, hence stable under specialization. It is also stable under
generalization: if `y ⤳ i z`, let `z₀` be the generic point of an irreducible component of `Z`
through `z`. The local ring of `X` at `i z` is a domain because `X` is smooth over a field, hence
normal (`AlgebraicGeometry.isNormal_of_smooth_over_field`), so the generizations of `i z`, which
form the image of `Spec 𝒪_{X, i z}` (`AlgebraicGeometry.Scheme.range_fromSpecStalk`), all
specialize from a single point `g`. As `i z₀` has coheight `0`, it is maximal for generization,
so `i z₀ ⤳ g ⤳ y` and `y` lies in the closed image. On the Noetherian space `X` a set stable
under specialization and generalization is open
(`StableUnderSpecialization.isOpen_of_stableUnderGeneralization`), and a closed immersion with
open image into the reduced scheme `X` is an open immersion
(`StacksTag09NE.isOpenImmersion_of_closedImmersion_of_open_range`).

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.isOpenImmersion_of_coheight_eq_zero`: a
  closed immersion of smooth projective schemes all of whose components have codimension `0` is
  an open immersion.

## References

* [Stacks Project, Tag 0FII](https://stacks.math.columbia.edu/tag/0FII)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

namespace SmoothProjectiveScheme

/-- **A closed immersion of smooth projective schemes whose components all have codimension `0`
is an open immersion.** The codimension of the component `closure {z}` of `Z` in `X` is the
coheight of the image of its generic point `z`. Its image is closed and stable under
generalization, because the local rings of the smooth `k`-scheme `X` are domains, so it is open
in the Noetherian space `X`; a closed immersion with open image into a reduced scheme is an open
immersion. This is the case `r = 0` of Lemma 0FII. -/
theorem isOpenImmersion_of_coheight_eq_zero {Z X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : Z ⟶ X)
    [IsClosedImmersion i.hom.left]
    (hr : ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = 0) :
    IsOpenImmersion i.hom.left := by
  have : IsNormal X.obj.left := isNormal_of_smooth_over_field X.obj.hom
  have : IsLocallyNoetherian X.obj.left := LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  have : CompactSpace X.obj.left := SmoothProjectiveScheme.compactSpace X
  have : IsNoetherian X.obj.left := ⟨⟩
  have hclosed : IsClosed (Set.range i.hom.left) := i.hom.left.isClosedEmbedding.isClosed_range
  refine StacksTag09NE.isOpenImmersion_of_closedImmersion_of_open_range i.hom.left ?_
  refine hclosed.stableUnderSpecialization.isOpen_of_stableUnderGeneralization ?_
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  rintro x y hyx ⟨z, rfl⟩
  have hC := irreducibleComponent_mem_irreducibleComponents z
  have hz₀ : closure {hC.1.genericPoint} = irreducibleComponent z :=
    hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  have hmax : IsMax (i.hom.left hC.1.genericPoint) :=
    Order.coheight_eq_zero.mp (hr _ (hz₀.symm ▸ hC))
  have hz₀z : hC.1.genericPoint ⤳ z :=
    specializes_iff_mem_closure.mpr (hz₀.symm ▸ mem_irreducibleComponent)
  let φ := X.obj.left.fromSpecStalk (i.hom.left z)
  have hg : ∀ w, φ (genericPoint _) ⤳ φ w := fun w ↦
    (genericPoint_specializes w).map φ.continuous
  obtain ⟨w, rfl⟩ := Scheme.range_fromSpecStalk.ge hyx
  obtain ⟨w₀, hw₀⟩ := Scheme.range_fromSpecStalk.ge (hz₀z.map i.hom.left.continuous)
  have h₀ : i.hom.left hC.1.genericPoint ⤳ φ (genericPoint _) := hmax (hw₀ ▸ hg w₀)
  exact hclosed.stableUnderSpecialization (h₀.trans (hg w)) ⟨_, rfl⟩

end SmoothProjectiveScheme

end Stacks.WeilCohomology

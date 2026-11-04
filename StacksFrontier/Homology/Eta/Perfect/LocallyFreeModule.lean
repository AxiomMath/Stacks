module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeAffine
public import StacksFrontier.Homology.Eta.Perfect.LocallyFree

/-!
# The terms of the décalage are finite locally free modules

Let `A` be a commutative ring, `f ∈ A` a nonzerodivisor and `M^•` a bounded complex of finite
free `A`-modules written in chosen bases.  If the determinantal ideal `I_i(M^•, f)` is principal
then the degree-`i` term of the décalage `η_f M^•` is a finite locally free `A`-module in the
sense of More on Algebra, Tag 00NW (2): the term is finite and projective by Tag 0F7W, and a
finite projective module is finite locally free by Tag 00NX.

## Main results

* `EtaPow.LocallyFree.isFiniteLocallyFree_fetaTerm`: the degree-`i` term of `η_f M^•` is finite
  locally free when `I_i(M^•, f)` is principal.

## Implementation notes

The passage from finite and projective to finite locally free is
`Module.isFiniteLocallyFree_iff_finite_projective`, which is Tag 00NX in that form already; no
new characterization of finite local freeness is introduced here.

No `@[stacks]` attribute is attached: the statement is Tag 0F7W, already carried by
`EtaPow.LocallyFree.etaTerm_finite_projective_and_split_of_idealI_isPrincipal`, repackaged in the
form its consumers need.  Only the finiteness and projectivity of that tag are used; neither its
computation of `Module.rankAtStalk` nor the retraction of the graph map is needed, so a term of a
décalage is not shown here to be free of any particular rank.

## References

* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public section

universe u

namespace EtaPow.LocallyFree

/-- **The terms of the décalage are finite locally free.**  If the determinantal ideal
`I_i(M^•, f)` of a bounded complex of finite free modules is principal, then the degree-`i` term
of `η_f M^•` is a finite locally free `A`-module. -/
public theorem isFiniteLocallyFree_fetaTerm {A : Type u} [CommRing A] (C : BoundedComplex A)
    (f : A) (hf : IsRegular f) (i : ℤ) (hprin : Submodule.IsPrincipal (idealI C f i)) :
    Module.IsFiniteLocallyFree A ↥(EtaPow.fetaTerm f ((C.d i).mulVecLin) i) := by
  obtain ⟨⟨hfin, hproj, -⟩, -⟩ :=
    etaTerm_finite_projective_and_split_of_idealI_isPrincipal C f hf i hprin
  exact (Module.isFiniteLocallyFree_iff_finite_projective A _).mpr ⟨hfin, hproj⟩

end EtaPow.LocallyFree

end

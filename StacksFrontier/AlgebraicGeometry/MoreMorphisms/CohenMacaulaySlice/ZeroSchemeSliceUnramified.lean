module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.GivenSectionsSlice
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.SmoothSliceSeparablePoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.ZeroScheme

/-!
# The zero scheme of a slicing sequence is unramified over the base field

Let `V` be an affine scheme with a morphism `π : V ⟶ Spec k` to the spectrum of a field, and let
`g₁, …, g_r ∈ Γ(V, ⊤)` be global regular functions. The slice the chart construction of
**Stacks 06N3** cuts out is the scheme-theoretic zero scheme `V(g₁, …, g_r)`, that is the closed
subscheme `Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))`, and the criterion of
**Stacks 02GF** which makes that slice unramified over `Spec k` at a point — namely
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field` — asks
for three things: that the germs of the `g i` generate the maximal ideal of `𝒪_{V, v}`, that the
residue field extension `κ(v)/κ(π v)` be finite separable, and that the `g i` **pull back to
zero** on the slice.

The last of the three is the one the chart construction has to supply, and it holds of the zero
scheme by construction: the functions cutting it out lie in the kernel of pullback of global
regular functions along its closed immersion. This file supplies it, and with it states the
criterion at the zero scheme, so that a consumer has only the two geometric hypotheses left.

## Main results

* `appTop_subschemeι_ofIdealTop_eq_zero_of_mem`: a global regular function in the ideal cutting out
  a closed subscheme of an affine scheme pulls back to zero on it.
* `stalkMap_germ_subschemeι_ofIdealTop_eq_zero`: its germ therefore pulls back to zero in the local
  ring at any point of that subscheme — the vanishing hypothesis of the criterion.
* `unramifiedAt_subschemeι_comp_of_ofList_germ_eq_maximalIdeal_over_field`: the criterion at the
  zero scheme of the slicing sequence, with the vanishing hypothesis discharged.

## Implementation notes

The statements are phrased so that the slice is the zero scheme **definitionally**: no hypothesis
of the form `Z = V(g)` with `Z` a scheme occurs, since such an equation in a dependent position
cannot be used without transporting the point of the slice along it.

The ideal is written `Ideal.ofList (List.ofFn g)`, the form in which the scheme-level slicing
lemma **Stacks 06LI** and the criterion of **Stacks 02GF** both phrase it, and the kernel
computation is `Stacks.AlgebraicGeometry.ker_appTop_subschemeι_ofIdealTop`, which is where
affineness of `V` enters — on an affine scheme an ideal sheaf is determined by its ideal of
global sections.

No `@[stacks]` attribute is claimed: this is a step of the proof of **Stacks 06N3**, whose
registration sits on
`AlgebraicGeometry.Stack.isAbsolutelyDM_iff_isDeligneMumfordStack_unconditional`.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Stacks.AlgebraicGeometry

universe u

/-- **A global regular function in the ideal of a closed subscheme of an affine scheme pulls back
to zero on that subscheme.** The ideal is the kernel of pullback of global regular functions
along the closed immersion, by
`Stacks.AlgebraicGeometry.ker_appTop_subschemeι_ofIdealTop`. -/
theorem appTop_subschemeι_ofIdealTop_eq_zero_of_mem {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) {s : Γ(X, ⊤)} (hs : s ∈ I) :
    (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop s = 0 := by
  change (Scheme.IdealSheafData.ofIdealTop I).subschemeι.appTop.hom s = 0
  refine RingHom.mem_ker.mp ?_
  rw [ker_appTop_subschemeι_ofIdealTop I]
  exact hs

/-- **The germ of a global regular function in the ideal of a closed subscheme of an affine
scheme pulls back to zero in the local ring at any point of that subscheme.** This is the
vanishing hypothesis of the criterion of **Stacks 02GF** at the zero scheme of a slicing
sequence: the function pulls back to zero globally by
`Stacks.AlgebraicGeometry.appTop_subschemeι_ofIdealTop_eq_zero_of_mem`, and the stalk map
carries the germ of a function to the germ of its pullback,
`Stacks.AlgebraicGeometry.germ_appTop_eq_stalkMap_germ`. -/
theorem stalkMap_germ_subschemeι_ofIdealTop_eq_zero {X : Scheme.{u}} [IsAffine X]
    (I : Ideal Γ(X, ⊤)) (z : (Scheme.IdealSheafData.ofIdealTop I).subscheme)
    {s : Γ(X, ⊤)} (hs : s ∈ I) :
    ((Scheme.IdealSheafData.ofIdealTop I).subschemeι.stalkMap z).hom
        (X.presheaf.germ ⊤ ((Scheme.IdealSheafData.ofIdealTop I).subschemeι z) trivial s) = 0 := by
  rw [← germ_appTop_eq_stalkMap_germ (Scheme.IdealSheafData.ofIdealTop I).subschemeι z s,
    appTop_subschemeι_ofIdealTop_eq_zero_of_mem I hs]
  exact map_zero _

/-- **The slice cut out by a slicing sequence of global functions is unramified over the base
field at a point where the sequence generates the maximal ideal.** Let `V` be an affine scheme
with a morphism `π : V ⟶ Spec k`, let `g₁, …, g_r ∈ Γ(V, ⊤)`, and let `z` be a point of the
scheme-theoretic zero scheme `V(g₁, …, g_r)` at which the germs of the `g i` generate the
maximal ideal of `𝒪_{V, v}`, `v` the image of `z`, and at which `κ(v)` is finite separable over
the residue field of `Spec k`. Then the composite `V(g₁, …, g_r) ⟶ V ⟶ Spec k` is unramified
at `z`.

This is
`Stacks.AlgebraicGeometry.unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field` with its
**vanishing hypothesis discharged**, by
`Stacks.AlgebraicGeometry.stalkMap_germ_subschemeι_ofIdealTop_eq_zero`: the functions cutting
out the zero scheme pull back to zero on it, so the generation of `𝔪_v` by their germs is by
itself enough. It is the shape in which the chart construction of **Stacks 06N3** uses the
criterion, the slice there being cut out of an affine chart by global regular functions and the
base of the source's cartesian diagram being the spectrum of a field. -/
theorem unramifiedAt_subschemeι_comp_of_ofList_germ_eq_maximalIdeal_over_field
    {k : Type u} [Field k] {V : Scheme.{u}} [IsAffine V] {r : ℕ} (g : Fin r → Γ(V, ⊤))
    (π : V ⟶ Spec (.of k))
    [LocallyOfFiniteType
      ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι ≫ π)]
    (z : (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subscheme)
    (hgen : Ideal.ofList (List.ofFn fun i => V.presheaf.germ ⊤
          ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z)
          trivial (g i)) =
      maximalIdeal (V.presheaf.stalk
        ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z)))
    (hsep : letI := (π.residueFieldMap ((Scheme.IdealSheafData.ofIdealTop
          (Ideal.ofList (List.ofFn g))).subschemeι z)).hom.toAlgebra
      Module.Finite ((Spec (.of k)).residueField
          (π ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z)))
          (V.residueField
            ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z)) ∧
        Algebra.IsSeparable ((Spec (.of k)).residueField
            (π ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z)))
            (V.residueField
              ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z))) :
    UnramifiedAt
      ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι ≫ π) z :=
  unramifiedAt_comp_of_ofList_eq_maximalIdeal_stalk_over_field
    (Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι π z
    (fun i => V.presheaf.germ ⊤
      ((Scheme.IdealSheafData.ofIdealTop (Ideal.ofList (List.ofFn g))).subschemeι z) trivial (g i))
    (fun i => stalkMap_germ_subschemeι_ofIdealTop_eq_zero (Ideal.ofList (List.ofFn g)) z
      (Ideal.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    hgen hsep

end Stacks.AlgebraicGeometry

end

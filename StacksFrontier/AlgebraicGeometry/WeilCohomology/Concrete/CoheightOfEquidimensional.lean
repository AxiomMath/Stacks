module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupDimension

/-!
# The codimension of the components of an equidimensional closed subscheme

Let `i : Z ⟶ X` be a closed immersion of smooth projective schemes over `k`, with `X`
equidimensional of dimension `n` and `Z` equidimensional of dimension `e`. Then `e ≤ n`, and every
irreducible component of `Z` has codimension `n - e` in `X`: the image of its generic point has
coheight `n - e` in `X`. This is the hypothesis "every irreducible component of `Z` has
codimension `r` in `X`" of Lemma 0FIH, in the form used there (the coheight of the image of the
generic point of each component), for `Z` and `X` equidimensional as in Lemma 0FIR and
Tag 0FIT. It is the converse of `SmoothProjectiveScheme.relativeDimension_of_codimension`.

The proof is the dimension formula of Tag 0A21 at `x = i(z)`, `z` the generic point of a
component `W = closure {z}` of `Z`: `n = dim_x X = dim closure{x} + dim 𝒪_{X,x}`, with
`dim closure{x} = dim W = dim_z Z = e` (a component through `z` contains `W`, hence is `W`) and
`dim 𝒪_{X,x}` the coheight of `x` (Tag 02IZ).

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.coheight_eq_of_relativeDimension`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.le_of_relativeDimension`.

## References

* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Topology

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k] {Z X : (SmoothProjectiveScheme k).FullSubcategory} (i : Z ⟶ X)
  [IsClosedImmersion i.hom.left]

/-- The dimension formula at the image of the generic point of a component of `Z`:
`n = e + coheight(i z)`. -/
theorem coheight_add_eq_of_relativeDimension {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) (z : Z.obj.left)
    (hz : closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left) :
    ∃ m : ℕ, Order.coheight (i.hom.left z) = m ∧ n = e + m := by
  have hloc := (relativeDimension_iff_forall_topologicalKrullDimAt_of_field Z.obj.hom e).1 hZ z
  obtain ⟨W, hW, hzW, hWdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k Z.obj.left
      Z.obj.hom z
  have hsub : closure ({z} : Set Z.obj.left) ⊆ W :=
    closure_minimal (Set.singleton_subset_iff.mpr hzW) (isClosed_of_mem_irreducibleComponents W hW)
  have hcl : closure ({z} : Set Z.obj.left) = W := hz.eq_of_le hW.1 hsub
  have hδ := Stacks.Chow.relativeDimension_comp_closedImmersion
    (Stacks.Chow.fieldChowSituation k).dimensionFunction i.hom.left X.obj.hom z
  rw [Over.w i.hom] at hδ
  have h3 := topologicalKrullDimAt_eq_add_ringKrullDim_stalk k X.obj.hom (i.hom.left z)
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq k X.obj.hom, ← hδ,
    ← Stacks.Chow.topologicalKrullDim_closure_singleton_eq k Z.obj.hom z, hcl, hWdim, hloc,
    (relativeDimension_iff_forall_topologicalKrullDimAt_of_field X.obj.hom n).1 hX,
    ringKrullDim_stalk_eq_coheight] at h3
  generalize Order.coheight (i.hom.left z) = c at h3 ⊢
  induction c using ENat.recTopCoe with
  | top =>
    exfalso
    norm_cast at h3
  | coe m =>
    refine ⟨m, rfl, ?_⟩
    exact_mod_cast h3

/-- **Every component of `Z` has codimension `n - e` in `X`**: the image of the generic point of
each irreducible component of `Z` has coheight `n - e`, for `X` and `Z` equidimensional of
dimensions `n` and `e`. This is the hypothesis of Lemma 0FIH with `r = n - e`. -/
theorem coheight_eq_of_relativeDimension {n e : ℕ} (hX : RelativeDimension X.obj.hom n)
    (hZ : RelativeDimension Z.obj.hom e) :
    ∀ z : Z.obj.left, closure ({z} : Set Z.obj.left) ∈ irreducibleComponents Z.obj.left →
      Order.coheight (i.hom.left z) = ((n - e : ℕ) : ℕ∞) := by
  intro z hz
  obtain ⟨m, hm, hn⟩ := coheight_add_eq_of_relativeDimension i hX hZ z hz
  rw [hm, show n - e = m by omega]

include i in
/-- **`dim Z ≤ dim X`** for a closed immersion of nonempty equidimensional schemes. -/
theorem le_of_relativeDimension [Nonempty Z.obj.left] {n e : ℕ}
    (hX : RelativeDimension X.obj.hom n) (hZ : RelativeDimension Z.obj.hom e) : e ≤ n := by
  obtain ⟨z₀⟩ := ‹Nonempty Z.obj.left›
  have hC := irreducibleComponent_mem_irreducibleComponents z₀
  have hz : closure {hC.1.genericPoint} = irreducibleComponent z₀ :=
    hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
  obtain ⟨m, -, hn⟩ := coheight_add_eq_of_relativeDimension i hX hZ _ (hz.symm ▸ hC)
  omega

end Stacks.WeilCohomology.SmoothProjectiveScheme

end

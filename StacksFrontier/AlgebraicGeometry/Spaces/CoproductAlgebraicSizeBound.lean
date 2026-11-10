module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic

/-!
# A coproduct of algebraic spaces under a uniform size bound on the atlases

`AlgebraicGeometry.isAlgebraicSpace_coproduct` — Stacks 02WQ — concludes that a coproduct of
algebraic spaces over `S` is an algebraic space, but it asks for the disjoint union `V` of the
chosen atlases *inside the big fppf site* as data, together with the colimit cofan exhibiting
it. This file discharges that hypothesis from a size bound, which is the form in which the
set-theoretic tail of a descent argument produces it: a uniform bound `μ < B.cutoff` on the
sizes of the atlases, together with a bound `#K ≤ μ` on an index type of the working universe
in bijection with the given index type.

This is the last step of the closing paragraph of Stacks 04U1. That paragraph bounds the size
of each atlas `U_i` of a member by `max (size U) (size S)`, using Stacks 04T6 for the fibre
product `U_i = U ×_S S_i` and Stacks 04T7 for `size (S_i) ≤ size (S)`, then invokes Stacks 000Q
to bound the size of `∐ U_i` and Stacks 02WQ to conclude. Every ingredient of that chain is
already available: Stacks 04T6 as `AlgebraicGeometry.Scheme.size_pullback_le` and, for a fibre
product formed in the site, as `AlgebraicGeometry.Space.size_pullback_le`; Stacks 04T7 as
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`; Stacks 000Q as
`AlgebraicGeometry.Scheme.size_le_of_iSup_eq_top`, applied to a disjoint union by
`AlgebraicGeometry.schemeSize_coproduct_le`; and the passage from the bound on `∐ U_i` to an
object of the site carrying the universal property as
`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_le`. What is added here is only
the resulting form of Stacks 02WQ, in which the size bound replaces the disjoint union supplied
as data.

The conclusion is stated exactly as the hypothesis `hG` of
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering` — Stacks 04SK — consumes it, namely
`IsAlgebraicSpace B S hS G.obj` for a sheaf `G` presented by `IsColimit (Cofan.mk G ι)`. The
index type is left in an arbitrary universe `v`, so it may be the `Type (u + 1)` index type of
a `CategoryTheory.PreZeroHypercover.{u + 1}` covering, which is what Stacks 04SK uses; the
bijection `eK` with a type of the working universe is the source's own bound on the cardinality
of the index set.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt`: a family of objects
  of the site whose disjoint union of underlying schemes is of size below the cutoff has a
  coproduct inside the site, presented by a colimit cofan. This is the shape in which Stacks 02WQ
  and Stacks 04SK consume a disjoint union, and it strengthens
  `AlgebraicGeometry.BigFppfOver.exists_coproduct_of_size_le`, which returns the disjoint open
  cover rather than the universal property.
* `AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le`: a coproduct of algebraic spaces
  over `S` whose chosen atlases are uniformly bounded in size, indexed in bijection with a type
  of the working universe of cardinality at most that bound, is an algebraic space.

## Implementation notes

Stacks 04U0 (`AlgebraicGeometry.isAlgebraicSpace_of_isCovering_of_isFiniteType`) *derives* the
uniform bound on the atlases from finite type over the members via Stacks 04T7. The statement
below assumes that bound instead, so it also serves the cases where it comes from elsewhere —
in Stacks 04U1 from Stacks 04T6, the atlases there being fibre products of a single atlas of the
group algebraic space with the members of the covering.

Nothing here carries a `@[stacks 02WQ]` attribute: that tag is already attached to
`AlgebraicGeometry.isAlgebraicSpace_coproduct`, and the statement below is a corollary of it
under a stronger hypothesis on the atlases, not a second formalization of the tag. No
`@[stacks 04U1]` attribute is carried either: this is one step of that tag's proof, not its
statement, which is about descent of fppf torsors.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe v u

namespace AlgebraicGeometry

/-! ### Coproducts of bounded families in the site, with their universal property -/

/-- **A family of objects of the big fppf site over `S` whose disjoint union of underlying
schemes is of size below the cutoff has a coproduct inside the site.**

The underlying scheme is that disjoint union, and the structure morphism is assembled from those
of the members. The universal property is inherited from the disjoint union of schemes because
the inclusion of the site into schemes is fully faithful and a morphism out of the disjoint union
commutes with the structure morphisms as soon as its restrictions do.

`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_le` is the case where the size of
the disjoint union is bounded through `AlgebraicGeometry.schemeSize_coproduct_le` by uniform
bounds on the index type and on the members. -/
theorem BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {K : Type u} (R : K → BigFppfOver B S hS)
    (hZsize : (∐ fun k => (BigFppfOver.toScheme B S hS).obj (R k)).size < B.cutoff) :
    ∃ (Z : BigFppfOver B S hS) (c : ∀ k, R k ⟶ Z), Nonempty (IsColimit (Cofan.mk Z c)) := by
  classical
  set Z : BigFppfOver B S hS := Over.mk (B.inclusion.preimage (X := B.obj hZsize)
    (Y := B.obj hS)
    (show B.inclusion.obj (B.obj hZsize) ⟶ B.inclusion.obj (B.obj hS) from
      Sigma.desc fun k => B.inclusion.map (R k).hom)) with hZdef
  have hZhom : B.inclusion.map Z.hom = Sigma.desc fun k => B.inclusion.map (R k).hom :=
    B.inclusion.map_preimage _
  -- the coproduct injections of the underlying schemes are morphisms of the site
  have hc : ∀ k, ∃ ψ : R k ⟶ Z, (BigFppfOver.toScheme B S hS).map ψ =
      Sigma.ι (fun k => (BigFppfOver.toScheme B S hS).obj (R k)) k := by
    intro k
    refine BigFppfOver.exists_hom_of_comp_eq B S hS _ ?_
    rw [hZhom, Sigma.ι_comp_desc]
  choose c hcmap using hc
  -- the universal property, transported from the disjoint union of schemes
  have key : ∀ t : Cofan R, ∃! m : Z ⟶ t.pt, ∀ k, c k ≫ m = t.inj k := by
    intro t
    obtain ⟨m, hm⟩ : ∃ m : Z ⟶ t.pt, (BigFppfOver.toScheme B S hS).map m =
        Sigma.desc fun k => (BigFppfOver.toScheme B S hS).map (t.inj k) := by
      refine BigFppfOver.exists_hom_of_comp_eq B S hS _ ?_
      rw [hZhom]
      refine Sigma.hom_ext _ _ fun k => ?_
      rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      exact (Functor.map_comp B.inclusion (t.inj k).left t.pt.hom).symm.trans
        (congrArg B.inclusion.map (Over.w (t.inj k)))
    refine ⟨m, fun k => (BigFppfOver.toScheme B S hS).map_injective ?_, fun m' hm' => ?_⟩
    · rw [Functor.map_comp, hcmap k, hm, Sigma.ι_comp_desc]
    · refine (BigFppfOver.toScheme B S hS).map_injective
        (Sigma.hom_ext _ _ fun k => ?_)
      rw [hm, Sigma.ι_comp_desc, ← hcmap k, ← Functor.map_comp, hm' k]
  exact ⟨Z, c, ⟨Cofan.IsColimit.mk _ (fun t => (key t).choose)
    (fun t k => (key t).choose_spec.1 k) fun t m hm => (key t).choose_spec.2 m hm⟩⟩

/-! ### Stacks 02WQ under a uniform size bound on the atlases -/

/-- **A coproduct of algebraic spaces over `S` whose chosen atlases are uniformly bounded in
size is an algebraic space over `S`.**

This is `AlgebraicGeometry.isAlgebraicSpace_coproduct` — Stacks 02WQ — with the disjoint union
of the atlases inside the site replaced by the size bound which produces it. The hypotheses are:
`F` is a family of algebraic spaces over `S` with chosen surjective étale scheme atlases
`f i : yoneda.obj (U i) ⟶ F i`; the sheaf `G` is their coproduct, presented by the colimit cofan
`hG`; the index type `I` is in bijection with a type `K` of the working universe; and `μ` is an
infinite cardinal below the cutoff of the site bounding both `#K` and every `size (U i)`.

`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt`, with
`AlgebraicGeometry.schemeSize_coproduct_le`, turns those bounds into the
disjoint union of the atlases inside the site together with its universal property, and
Stacks 02WQ concludes, the cofan presenting `G` being reindexed along the bijection by
`CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv`.

The conclusion is in the shape that the hypothesis `hG` of
`AlgebraicGeometry.isAlgebraicSpace_of_isCovering` — Stacks 04SK — consumes. -/
theorem isAlgebraicSpace_coproduct_of_size_le
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v}
    (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : ∀ i, IsAlgebraicSpace B S hS (F i))
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι))
    (U : I → BigFppfOver B S hS)
    (f : ∀ i, yoneda.obj (U i) ⟶ F i)
    (hsurj : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    (hetale : ∀ i, (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (f i))
    {K : Type u} (eK : K ≃ I) {μ : Cardinal.{u}}
    (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hsize : ∀ i, ((BigFppfOver.toScheme B S hS).obj (U i)).size ≤ μ) :
    IsAlgebraicSpace B S hS G.obj := by
  obtain ⟨V, j, ⟨hV⟩⟩ := BigFppfOver.exists_isColimit_cofan_of_size_sigma_lt B S hS
    (fun k => U (eK k)) ((schemeSize_coproduct_le _ μ hℵ hK fun k => hsize (eK k)).trans_lt hμ)
  refine isAlgebraicSpace_coproduct B S hS (fun k : K => F (eK k)) (fun k => hF (eK k))
    G (fun k => ι (eK k)) ?_ (fun k => U (eK k)) (fun k => f (eK k))
    (fun k => hsurj (eK k)) (fun k => hetale (eK k)) V j hV
  simpa using (Cofan.isColimitEquivOfEquiv eK (Cofan.mk G ι)) hG

end AlgebraicGeometry

end

module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsAtOneOpen

/-!
# The descent datum of Tag 0D69, from the glueing of morphisms at the overlap alone

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67.  [Stacks, Tag 0D69] produces, for two members `U` and `V` of
`ℬ`, a unique isomorphism `ρ_{U,V} : K_U|_{U ∩ V} ≅ K_V|_{U ∩ V}` compatible with the prescribed
transitions below the overlap, and shows that these isomorphisms satisfy the cocycle condition
over a triple intersection.

The source obtains both from the uniqueness clause of [Stacks, Tag 0D68], applied on the ringed
space `U ∩ V` — in this development the predicate
`Stacks.DerivedGlueing.HasUniqueSolutionOverIso`, which quantifies over *every* open that the
collection covers.  Both statements use far less than that.  The argument for `ρ_{U,V}` reads the
clause at the single open `U ∩ V`, and the argument for the cocycle condition reads it at the
single open `U ∩ V ∩ W`; and at a single open the clause is
`Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt`, which asks only for
the sheaf condition of [Stacks, Tag 0D66] part (2) *at that open*, in the form
`Stacks.DerivedGlueing.HasGluingForHomsAt`.

This file states the two clauses of Tag 0D69 in that form.  Two things change beyond the
localisation of the granted hypothesis.  First, the covering hypothesis
`hinter` — that the intersection of two members of the collection is the union of the members
contained in it — **disappears entirely**: it was present only to apply the general predicate at
the overlap, and no step of either argument uses it.  Second, the covering hypothesis (1) of
Tag 0D68, that the collection covers `X`, is not assumed either, exactly as in
`Stacks.DerivedGlueing.exists_unique_overlapIso`.

So of the source's hypotheses only the vanishing of negative self-`Ext` survives, and the one
granted statement is the sheaf condition of Tag 0D66 part (2) read at one open at a time.

That statement is itself a theorem of this development at every open the collection covers,
`Stacks.DerivedGlueing.hasGluingForHomsAt_of_covers`, so the two clauses below are a conditional
form kept for a consumer that has the condition by some other route; the two clauses at the
source's own hypotheses and nothing else are
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers` and
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers`, in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HomVanishingOverASubcollection`.

## Main results

* `Stacks.DerivedGlueing.exists_unique_overlapIso_of_hasGluingForHomsAt`: **[Stacks, Tag 0D69]**,
  the unique compatible isomorphism `ρ_{U,V}` over an overlap, granted the glueing of morphisms
  at `U ∩ V` alone.
* `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_hasGluingForHomsAt`: **[Stacks, Tag
  0D69]**, the cocycle condition `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}` over a triple intersection,
  granted the glueing of morphisms at `U ∩ V ∩ W` alone.
* `Stacks.DerivedGlueing.exists_unique_overlapIso_of_hasGluingForHomsOver` and
  `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_hasGluingForHomsOver`: the same two
  clauses granted the sheaf condition in its collection-wide form, which is how a proof of that
  condition for a covering collection will discharge them.
* `Stacks.DerivedGlueing.hasGluingForHomsAt_of_mem`: the glueing of morphisms at a member of the
  collection, granted nothing.
* `Stacks.DerivedGlueing.exists_unique_overlapIso_of_inf_mem_opens` and
  `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_inf_mem_opens`: both clauses granted
  nothing, for a collection closed under pairwise intersection — the certificate that the
  granted hypothesis above is satisfiable, and satisfiable away from `⊤ ∈ ℬ`.

## References

* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-! ### The comparison isomorphism over an overlap -/

/-- **The comparison isomorphism over an overlap, from the glueing of morphisms at that
overlap.** In Situation 0D67, assume that the prescribed objects have no negative self-`Ext` and
that `Stacks.DerivedGlueing.HasGluingForHomsAt S (U ⊓ V)` holds, the sheaf condition of
[Stacks, Tag 0D66] part (2) at the overlap.  Then for members `U` and `V` of the collection there
is a unique isomorphism `K_U|_{U ∩ V} ≅ K_V|_{U ∩ V}` compatible with the prescribed transitions
on the members of the collection contained in `U ∩ V`.

Both restrictions are solutions over `U ∩ V`, by
`Stacks.DerivedGlueing.SolutionOver.restrictOpen` applied to
`Stacks.DerivedGlueing.selfSolutionOver`, and
`Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt` identifies them.
The statement of [Stacks, Tag 0D69] is
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_covers`. -/
theorem exists_unique_overlapIso_of_hasGluingForHomsAt (S : LocallyGiven X)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens)
    (hglue : HasGluingForHomsAt S (U ⊓ V)) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom := by
  obtain ⟨φ, hφ, hφuniq⟩ := existsUnique_solutionOverIso_of_hasGluingForHomsAt S hglue hExt
    ((selfSolutionOver S U hU).restrictOpen (U ⊓ V) inf_le_left)
    ((selfSolutionOver S V hV).restrictOpen (U ⊓ V) inf_le_right)
  refine ⟨φ, (isOverlapHom_iff hU hV inf_le_left inf_le_right φ.hom).mpr hφ, fun ψ hψ => ?_⟩
  exact hφuniq ψ ((isOverlapHom_iff hU hV inf_le_left inf_le_right ψ.hom).mp hψ)

/-! ### The cocycle condition -/

/-- **The cocycle condition, from the glueing of morphisms at the triple intersection.** Let
`U`, `V` and `W` be members of the collection, assume
`Stacks.DerivedGlueing.HasGluingForHomsAt S (U ⊓ V ⊓ W)`, and let `ρ_{U,V}`, `ρ_{V,W}` and
`ρ_{U,W}` be compatible isomorphisms between the restrictions of the prescribed objects to the
corresponding overlaps.  Then over the triple intersection `ρ_{U,W} = ρ_{V,W} ∘ ρ_{U,V}`.

Both sides are morphisms of the solutions over `U ∩ V ∩ W` defined by the prescribed objects on
`U` and on `W`, by `Stacks.DerivedGlueing.IsOverlapHom.restrict`, so
`Stacks.DerivedGlueing.existsUnique_solutionOverIso_of_hasGluingForHomsAt` identifies them.
The statement of [Stacks, Tag 0D69] is
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_covers`. -/
theorem restrictOverlapHom_cocycle_of_hasGluingForHomsAt (S : LocallyGiven X)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
    (hglue : HasGluingForHomsAt S (U ⊓ V ⊓ W))
    (φUV : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV))
    (hφUV : IsOverlapHom S hU hV inf_le_left inf_le_right φUV.hom)
    (φVW : (S.restriction (V ⊓ W) V inf_le_left).obj (S.obj V hV) ≅
      (S.restriction (V ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφVW : IsOverlapHom S hV hW inf_le_left inf_le_right φVW.hom)
    (φUW : (S.restriction (U ⊓ W) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφUW : IsOverlapHom S hU hW inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom S hU hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom S hU hV inf_le_left inf_le_right
          (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom S hV hW inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom := by
  obtain ⟨φ, -, hφuniq⟩ := existsUnique_solutionOverIso_of_hasGluingForHomsAt S hglue hExt
    ((selfSolutionOver S U hU).restrictOpen (U ⊓ V ⊓ W) (inf_le_left.trans inf_le_left))
    ((selfSolutionOver S W hW).restrictOpen (U ⊓ V ⊓ W) inf_le_right)
  have h₁ := hφuniq (restrictOverlapIso S hU hW inf_le_left inf_le_right
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) φUW)
    ((isOverlapHom_iff hU hW _ _ _).mp (hφUW.restrict _))
  have h₂ := hφuniq (restrictOverlapIso S hU hV inf_le_left inf_le_right inf_le_left φUV ≪≫
      restrictOverlapIso S hV hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) φVW)
    ((isOverlapHom_iff hU hW _ _ _).mp
      ((hφUV.restrict _).comp (hφVW.restrict _)))
  rw [← restrictOverlapIso_hom, ← restrictOverlapIso_hom, ← restrictOverlapIso_hom, h₁, ← h₂]
  rfl

/-! ### The two clauses granted the collection-wide sheaf condition -/

/-- **[Stacks, Tag 0D69], the comparison isomorphism over an overlap, granted the sheaf condition
of [Stacks, Tag 0D66] part (2) for the collection.** This is
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_hasGluingForHomsAt` fed the instance of
`Stacks.DerivedGlueing.HasGluingForHomsOver` at the overlap, which
`Stacks.DerivedGlueing.hasGluingForHomsAt_of_hasGluingForHomsOver` extracts; the covering
hypothesis `hinter` reappears because it is what licenses that extraction. -/
theorem exists_unique_overlapIso_of_hasGluingForHomsOver (S : LocallyGiven X)
    (hglue : HasGluingForHomsOver S)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom :=
  exists_unique_overlapIso_of_hasGluingForHomsAt S hExt U V hU hV
    (hasGluingForHomsAt_of_hasGluingForHomsOver S hglue (U ⊓ V) (hinter U hU V hV) hinter)

/-- **[Stacks, Tag 0D69], the cocycle condition, granted the sheaf condition of [Stacks, Tag
0D66] part (2) for the collection.** This is
`Stacks.DerivedGlueing.restrictOverlapHom_cocycle_of_hasGluingForHomsAt` fed the instance of
`Stacks.DerivedGlueing.HasGluingForHomsOver` at the triple intersection, which is covered by
members of the collection by `Stacks.DerivedGlueing.inf_inf_eq_sSup`. -/
theorem restrictOverlapHom_cocycle_of_hasGluingForHomsOver (S : LocallyGiven X)
    (hglue : HasGluingForHomsOver S)
    (hinter : ∀ U ∈ S.opens, ∀ V ∈ S.opens, U ⊓ V = sSup {W | W ∈ S.opens ∧ W ≤ U ⊓ V})
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
    (φUV : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV))
    (hφUV : IsOverlapHom S hU hV inf_le_left inf_le_right φUV.hom)
    (φVW : (S.restriction (V ⊓ W) V inf_le_left).obj (S.obj V hV) ≅
      (S.restriction (V ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφVW : IsOverlapHom S hV hW inf_le_left inf_le_right φVW.hom)
    (φUW : (S.restriction (U ⊓ W) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφUW : IsOverlapHom S hU hW inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom S hU hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom S hU hV inf_le_left inf_le_right
          (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom S hV hW inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom :=
  restrictOverlapHom_cocycle_of_hasGluingForHomsAt S hExt U V W hU hV hW
    (hasGluingForHomsAt_of_hasGluingForHomsOver S hglue (U ⊓ V ⊓ W)
      (inf_inf_eq_sSup S hinter U V W hU hV hW) hinter)
    φUV hφUV φVW hφVW φUW hφUW

/-! ### The granted hypothesis is satisfiable, at a collection that need not contain `⊤` -/

/-- **The glueing of morphisms holds at any member of the collection.** Over a member there is
nothing to glue: the glued morphism is the family's own value there, read through the
identification of restriction from the member to itself with the identity.  This is
`Stacks.DerivedGlueing.exists_unique_hom_of_mem`, and it is
`Stacks.DerivedGlueing.hasGluingForHomsAt_top_of_mem` with `⊤` replaced by an arbitrary
member. -/
theorem hasGluingForHomsAt_of_mem (S : LocallyGiven X) {O : Opens X.carrier}
    (hO : O ∈ S.opens) : HasGluingForHomsAt S O :=
  fun K L _ φ hφ => exists_unique_hom_of_mem S hO K L φ hφ

/-- **The comparison isomorphism over an overlap, granted nothing, for a collection closed
under pairwise intersection.** If `U ⊓ V` is itself a member of the collection then the glueing
condition holds there by `Stacks.DerivedGlueing.hasGluingForHomsAt_of_mem`, so the comparison
isomorphism of [Stacks, Tag 0D69] exists and is unique with no granted hypothesis at all — only
the vanishing of negative self-`Ext`, which the source assumes.

This is the non-degeneracy certificate for
`Stacks.DerivedGlueing.exists_unique_overlapIso_of_hasGluingForHomsAt`: its granted hypothesis
is satisfiable, and satisfiable at collections that do **not** contain `⊤`, for instance the
collection of all opens contained in a fixed proper open, whose closure under pairwise
intersection is `Stacks.DerivedGlueing.inf_eq_sSup_opensLE`. -/
theorem exists_unique_overlapIso_of_inf_mem_opens (S : LocallyGiven X)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens)
    (hUV : U ⊓ V ∈ S.opens) :
    ∃! φ : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
        (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV),
      IsOverlapHom S hU hV inf_le_left inf_le_right φ.hom :=
  exists_unique_overlapIso_of_hasGluingForHomsAt S hExt U V hU hV
    (hasGluingForHomsAt_of_mem S hUV)

/-- **The cocycle condition, granted nothing, for a collection closed under pairwise
intersection.** As for `Stacks.DerivedGlueing.exists_unique_overlapIso_of_inf_mem_opens`, with
the triple intersection `U ⊓ V ⊓ W` in place of the overlap. -/
theorem restrictOverlapHom_cocycle_of_inf_mem_opens (S : LocallyGiven X)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ S.opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom (S.obj U hU) (S.obj U hU) i))
    (U V W : Opens X.carrier) (hU : U ∈ S.opens) (hV : V ∈ S.opens) (hW : W ∈ S.opens)
    (hUVW : U ⊓ V ⊓ W ∈ S.opens)
    (φUV : (S.restriction (U ⊓ V) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ V) V inf_le_right).obj (S.obj V hV))
    (hφUV : IsOverlapHom S hU hV inf_le_left inf_le_right φUV.hom)
    (φVW : (S.restriction (V ⊓ W) V inf_le_left).obj (S.obj V hV) ≅
      (S.restriction (V ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφVW : IsOverlapHom S hV hW inf_le_left inf_le_right φVW.hom)
    (φUW : (S.restriction (U ⊓ W) U inf_le_left).obj (S.obj U hU) ≅
      (S.restriction (U ⊓ W) W inf_le_right).obj (S.obj W hW))
    (hφUW : IsOverlapHom S hU hW inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom S hU hW inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom S hU hV inf_le_left inf_le_right
          (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom S hV hW inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom :=
  restrictOverlapHom_cocycle_of_hasGluingForHomsAt S hExt U V W hU hV hW
    (hasGluingForHomsAt_of_mem S hUVW) φUV hφUV φVW hφVW φUW hφUW

end Stacks.DerivedGlueing

end

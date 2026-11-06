module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteSheafCondition

/-!
# The Comparison Lemma for sheaves of abelian groups on the charts of the members

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of algebraic
spaces étale over `X`.  The charts of the members of that family form a site,
`AlgebraicGeometry.Space.QuasiCoherentDescent.MemberSite`, with the topology
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberTopology` restricted from the small étale
topology of `X` along the fully faithful
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor`; for an étale covering that functor
is cover dense, hence exhibits the charts of the members as a **dense subsite** of the small étale
site of `X`.

This file states, for sheaves of **abelian groups**, the Comparison Lemma on that pair of sites:
restriction of sections along `AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor` is an
equivalence from the sheaves of abelian groups on the small étale site of `X` to the sheaves of
abelian groups on the charts of the members.  This is the hypothesis of
`Stacks.DenseSubsiteModules.essSurj_moduleRestriction`,
`.isEquivalence_moduleRestriction` and `.moduleRestrictionEquivalence`, and hence the input of the
transport of a sheaf of modules on the charts of the members to an `𝒪_X`-module.

Nothing here is conditional: no form of the Comparison Lemma is assumed as a hypothesis.  The
only hypothesis in scope is cover density of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberFunctor`, which is the geometric input — it
is proved for an étale covering by
`AlgebraicGeometry.Space.QuasiCoherentDescent.isCoverDense_memberFunctor` and for a Zariski
covering by `.isCoverDense_memberFunctor_of_isZariskiCovering`.  Nothing here mentions a descent
datum.

All names below are in the namespace `AlgebraicGeometry.Space.QuasiCoherentDescent`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberAbRestriction`: the restriction functor
  `(memberFunctor …).sheafPushforwardContinuous AddCommGrpCat (memberTopology …)
  (SmallEtale.topology …)`.  **The Comparison Lemma for sheaves of abelian groups on the charts
  of the members**, that it is an equivalence, is Mathlib's instance for a dense subsite (see the
  implementation notes); this is the instance the transport of modules needs.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.memberAbEquivalence`: that equivalence itself,
  with `.memberAbEquivalence_functor` identifying its functor as restriction.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_isSheaf_memberFunctor_op_comp_iso`:
  **every sheaf of abelian groups on the charts of the members is, up to isomorphism, a sheaf of
  abelian groups on the small étale site of `X` read on the charts of the members.**  This is the
  form a consumer holding a presheaf and its sheaf condition — say by
  `.isSheaf_memberTopology_iff_isSheafFor` — uses; the converse direction is
  `.isSheaf_memberFunctor_op_comp`.

## Implementation notes

The Comparison Lemma for sheaves of abelian groups is the unnamed instance that closes Mathlib's
`Mathlib/CategoryTheory/Sites/DenseSubsite/SheafEquiv.lean`, deducing
`(G.sheafPushforwardContinuous A J K).IsEquivalence` from
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`.  Its two hypotheses are
`(memberFunctor …).IsDenseSubsite (memberTopology …) (SmallEtale.topology …)` — which cover
density supplies, through the unnamed instance for a restricted topology in
`Mathlib/CategoryTheory/Sites/DenseSubsite/InducedTopology.lean`, the topology of the charts of
the members being the restricted one — and
`∀ W, HasLimitsOfShape (StructuredArrow W (memberFunctor …).op) AddCommGrpCat`, which
`AlgebraicGeometry.Space.QuasiCoherentDescent`
`.hasLimitsOfShape_structuredArrow_memberFunctor_anyIndex`
supplies in exactly that form.  So the content of this file is already in instance search; what
the file adds is the restriction functor and the equivalence, under names a consumer can cite,
and the record of which input carries which half.

`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget` is **not** usable on this site, and is not
used: it asks `HasLimitsOfSize.{v₁, max v₁ u₁} AddCommGrpCat.{u}`, and the objects of the charts
of the members live one universe above `u` — the site is a full subcategory of the charts of `X`,
which are a `CostructuredArrow yoneda` category — so the demand would be for limits of size
`u + 1` in `AddCommGrpCat.{u}`, which do not exist.  The way round it is that the diagrams of the
Comparison Lemma are *essentially small*: `CategoryTheory.StructuredArrow.essentiallySmall`
reduces `StructuredArrow W (memberFunctor …).op` to a model in `Type u` from
`AlgebraicGeometry.Space.QuasiCoherentDescent.essentiallySmall_memberSite_anyIndex` and local
smallness of
the charts of `X`, and `CategoryTheory.Limits.hasLimitsOfShape_of_essentiallySmall` then asks
`AddCommGrpCat.{u}` only for limits of size `u`.  Only the *shape* of the limits is cut down this
way; the sheaves themselves keep their sections in `Type u`.

Everything below is at the level of sites and categories.  No identification of sections is
performed: no `restrictScalars` is stripped, no chart is crossed and no inverse image is crossed.

## References

* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X) (hf : ∀ i, IsEtale B S hS (f i).hom)

section CoverDense

variable [(memberFunctor B S hS Yi f hf).IsCoverDense (SmallEtale.topology B S hS X.1)]

/-! ### The Comparison Lemma -/

/-- Restriction of sheaves of abelian groups from the small étale site of `X` to the charts of the
members.  It is an equivalence by the Comparison Lemma, Mathlib's unnamed instance
`(G.sheafPushforwardContinuous A J K).IsEquivalence` for a dense subsite `G`: see the module
docstring. -/
abbrev memberAbRestriction :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ⥤
      Sheaf (memberTopology B S hS Yi f hf) AddCommGrpCat.{u} :=
  (memberFunctor B S hS Yi f hf).sheafPushforwardContinuous AddCommGrpCat.{u}
    (memberTopology B S hS Yi f hf) (SmallEtale.topology B S hS X.1)

/-- Restriction of a sheaf of abelian groups to the charts of the members is, on underlying
presheaves, composition with `.memberFunctor`. -/
theorem memberAbRestriction_obj_val
    (Q : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :
    ((memberAbRestriction B S hS Yi f hf).obj Q).obj =
      (memberFunctor B S hS Yi f hf).op ⋙ Q.obj :=
  rfl

/-- **The sheaves of abelian groups on the small étale site of `X` are the sheaves of abelian
groups on the charts of the members.** -/
def memberAbEquivalence :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} ≌
      Sheaf (memberTopology B S hS Yi f hf) AddCommGrpCat.{u} :=
  (memberAbRestriction B S hS Yi f hf).asEquivalence

/-- The equivalence of `AlgebraicGeometry.Space.QuasiCoherentDescent.memberAbEquivalence` is
restriction. -/
theorem memberAbEquivalence_functor :
    (memberAbEquivalence B S hS Yi f hf).functor = memberAbRestriction B S hS Yi f hf :=
  rfl

/-! ### Every sheaf on the charts of the members comes from the small étale site -/

/-- **Every sheaf of abelian groups on the charts of the members is the restriction of a sheaf of
abelian groups on the small étale site of `X`.**  This is essential surjectivity of
`AlgebraicGeometry.Space.QuasiCoherentDescent.memberAbRestriction` read on underlying presheaves:
a presheaf of abelian groups on the charts of the members satisfying the sheaf condition there is
isomorphic to a sheaf of abelian groups on the charts of `X` composed with
`.memberFunctor`.  The converse — that such a composition always satisfies the sheaf condition on
the charts of the members — is
`AlgebraicGeometry.Space.QuasiCoherentDescent.isSheaf_memberFunctor_op_comp`. -/
theorem exists_isSheaf_memberFunctor_op_comp_iso
    (P : (MemberSite B S hS Yi f hf)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (hP : Presheaf.IsSheaf (memberTopology B S hS Yi f hf) P) :
    ∃ Q : (SmallEtale B S hS X.1)ᵒᵖ ⥤ AddCommGrpCat.{u},
      Presheaf.IsSheaf (SmallEtale.topology B S hS X.1) Q ∧
        Nonempty ((memberFunctor B S hS Yi f hf).op ⋙ Q ≅ P) := by
  refine ⟨((memberAbRestriction B S hS Yi f hf).objPreimage ⟨P, hP⟩).obj,
    ((memberAbRestriction B S hS Yi f hf).objPreimage ⟨P, hP⟩).property, ⟨?_⟩⟩
  exact (sheafToPresheaf (memberTopology B S hS Yi f hf) AddCommGrpCat.{u}).mapIso
    ((memberAbRestriction B S hS Yi f hf).objObjPreimageIso ⟨P, hP⟩)

end CoverDense

end AlgebraicGeometry.Space.QuasiCoherentDescent

end

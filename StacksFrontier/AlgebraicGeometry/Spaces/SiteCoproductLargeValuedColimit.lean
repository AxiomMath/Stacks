module

public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.CategoryTheory.Sites.UliftYonedaCoproduct

/-!
# The coproduct of a uniformly bounded family of the big fppf site, among sheaves of `Type (u+1)`

A big fppf site `B` contains the coproduct of a family of its schemes as soon as the index type
and the components carry one common size bound below the cutoff, and the representable sheaf of
that coproduct — formed among sheaves of `Type (u + 1)`, the value universe in which a formal
algebraic space over `S` lives — is the coproduct of the representable sheaves of the members.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_sigma_of_size_le`: a big fppf site contains the
  coproduct of a family of its schemes of uniformly bounded size, indexed by a type of
  cardinality below the same bound.
* `AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaCofan`: if the underlying scheme of an
  object `V` of the big fppf site of `S` is the coproduct of the underlying schemes of a family
  `X`, then the universe-lifted representable sheaf of `V` is the coproduct, among fppf sheaves
  of `Type (u + 1)`, of the universe-lifted representable sheaves of the `X i`.
* `AlgebraicGeometry.BigFppfOver.exists_isColimitUliftYoneda_of_size_le`: the two put together.
  A uniformly bounded family of objects of the big fppf site of `S` has a coproduct `V` in that
  site, computed on underlying schemes, whose injections are open immersions covering `V`, and
  the universe-lifted representable sheaf of `V` is the coproduct of those of the members.
* `AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_isColimit_of_etaleCover`: a
  uniformly bounded family of morphisms into an object of the site, étale on underlying schemes
  and covering it, is refined by a single surjective étale morphism out of one object of the
  site, namely the coproduct of the family.
* `AlgebraicGeometry.BigFppfOver.exists_surjective_etale_sigma_of_openCover`: the same for a
  uniformly bounded open covering.
* `AlgebraicGeometry.BigFppfOver.exists_affineOpens_surjective_etale_sigma`: every object of
  the site — quasi-compact or not — is covered surjectively and étale by one object of the
  site which is the coproduct of its affine opens.

## Implementation notes

*Why the size bound and not a cofinality bound.*
`AlgebraicGeometry.BigFppfSite.contains_sigma` already puts the coproduct of a family of schemes
of the site in the site, but under `AlgebraicGeometry.BigFppfSite.AdmitsCoproductIndex`, which
asks for `#ι` below the *cofinality* of the cutoff. That hypothesis is the right one for a
family whose members are known only to lie in the site, since a cutoff produced by Tag 000J need
not be regular and a supremum of `#ι` many cardinals below it can reach it. It is the wrong one
for the family this file is built for — the affine opens of a single object `T` of the site —
because `#T.affineOpens` carries no cofinality bound. That family does carry a *uniform* bound:
both the index type and every member have size at most `T.size`, which is below the cutoff, and
`AlgebraicGeometry.schemeSize_coproduct_le` bounds the coproduct by it directly.

*Why the value universe `Type (u + 1)`.*
`AlgebraicGeometry.BigFppfOver.isColimit_yoneda_cofan` is the same statement for sheaves of
`Type u`, the value universe of the site. A formal algebraic space over `S` is a sheaf of
`Type (u + 1)`, so a coproduct of representables occurring in that theory is formed among
sheaves of `Type (u + 1)` and the statement in the value universe of the site does not apply to
it. The descent criterion behind both is the same;
`CategoryTheory.GrothendieckTopology.isColimitCofanMkUliftYoneda` is its universe-raising form.

*What makes the criterion apply.* The injections into a coproduct of schemes are open
immersions, jointly surjective, pairwise disjoint and monomorphisms, and each of those four
facts transports to `V` along the comparison isomorphism `∐ᵢ Xᵢ ≅ V` supplied by the hypothesis.
Joint surjectivity by open immersions makes the injections generate a covering sieve of the fppf
topology (`AlgebraicGeometry.BigFppfOver.ofArrows_mem_topology_of_isOpenImmersion`), and
disjointness makes the pairwise intersections initial, which is
`AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne` read in the slice.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal

universe v u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Cofan

variable {ι : Type v} [Small.{u} ι] (X : ι → BigFppfOver B S hS)
  {V : BigFppfOver B S hS} (j : ∀ i, X i ⟶ V)
  (hj : IsColimit (Cofan.mk ((toScheme B S hS).obj V)
    fun i => (toScheme B S hS).map (j i)))

include hj

end Cofan

/-- **A uniformly bounded étale covering of an object of the site is refined by a single
surjective étale morphism out of one object of the site.**

Given a family `g : X i ⟶ T` of morphisms étale on underlying schemes whose images cover `T`
and whose index type and members are bounded by one cardinal below the cutoff, the coproduct
`V` of the `X i` lies in the site and the induced `q : V ⟶ T` is surjective and étale; the
universe-lifted representable sheaf of `V` is the coproduct, among fppf sheaves of
`Type (u + 1)`, of those of the `X i`.

This is the shape in which a *non-quasi-compact* object of the site supplies a covering by one
object of the site: the covering family may be infinite, so no finite coproduct suffices, and
only a uniform size bound — not a cofinality bound — is available for it. The members of the
family need not be open immersions; the injections of the coproduct are, which is what makes
étaleness of `q` local on its source. -/
theorem exists_surjective_etale_sigma_isColimit_of_etaleCover {ι : Type u}
    (X : ι → BigFppfOver B S hS)
    (T : BigFppfOver B S hS) (g : ∀ i, X i ⟶ T)
    (hg : ∀ i, Etale ((toScheme B S hS).map (g i)))
    (hcov : ∀ x : (toScheme B S hS).obj T, ∃ i, x ∈ Set.range ((toScheme B S hS).map (g i)))
    {μ : Cardinal.{u}} (hμ : μ < B.cutoff) (hι : #ι ≤ μ)
    (hX : ∀ i, ((toScheme B S hS).obj (X i)).size ≤ μ) :
    ∃ (V : BigFppfOver B S hS) (j : ∀ i, X i ⟶ V) (q : V ⟶ T),
      (∀ i, j i ≫ q = g i) ∧
      (∀ i, IsOpenImmersion ((toScheme B S hS).map (j i))) ∧
      (∀ x : (toScheme B S hS).obj V, ∃ i, x ∈ Set.range ((toScheme B S hS).map (j i))) ∧
      Surjective ((toScheme B S hS).map q) ∧
      Etale ((toScheme B S hS).map q) ∧
      Nonempty (IsColimit (Cofan.mk V j)) ∧
      Nonempty (IsColimit (Cofan.mk ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V)
        fun i => (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (j i))) ∧
      Nonempty (IsColimit (Cofan.mk ((toScheme B S hS).obj V)
        fun i => (toScheme B S hS).map (j i))) := by
  obtain ⟨V, j, hjopen, hjcov, hjsch, ⟨hjsite⟩, hjsheaf⟩ :=
    exists_isColimitUliftYoneda_of_size_le B S hS X hμ hι hX
  have hfac : ∀ i, (toScheme B S hS).map (j i) ≫
      (toScheme B S hS).map (Cofan.IsColimit.desc hjsite g) = (toScheme B S hS).map (g i) :=
    fun i => by
      rw [← Functor.map_comp]
      exact congrArg _ (Cofan.IsColimit.fac hjsite g i)
  refine ⟨V, j, Cofan.IsColimit.desc hjsite g, fun i => Cofan.IsColimit.fac hjsite g i,
    hjopen, hjcov, ?_, ?_, ⟨hjsite⟩, hjsheaf, hjsch⟩
  · rw [surjective_iff]
    intro t
    obtain ⟨i, y, hy⟩ := hcov t
    exact ⟨_, by rw [← hy, ← hfac i]; rfl⟩
  · let 𝒰 : ((toScheme B S hS).obj V).OpenCover.{u} :=
      { I₀ := ι
        X := fun i => (toScheme B S hS).obj (X i)
        f := fun i => (toScheme B S hS).map (j i)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          exact ⟨hjcov, hjopen⟩ }
    have : IsZariskiLocalAtSource (@Etale.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u}) (Q := RingHom.Etale)
    refine IsZariskiLocalAtSource.of_openCover 𝒰 fun i => ?_
    change Etale ((toScheme B S hS).map (j i) ≫ _)
    rw [hfac i]
    exact hg i

end BigFppfOver

end AlgebraicGeometry

end

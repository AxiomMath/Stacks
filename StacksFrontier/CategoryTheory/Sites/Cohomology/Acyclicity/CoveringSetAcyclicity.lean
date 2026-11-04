module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.FiniteCoproductsOfRepresentables

/-!
# Acyclicity on a covering set, and why it does not give condition (2) of Stacks 07A1

Condition (1) of [Stacks, Tag 07A1] — `Stacks.Cohomology.VanishesOnObjects` — asks an abelian
sheaf `F` to be acyclic over every **object** of the site. This file upgrades that to acyclicity
over every member of the covering set of Stacks 0GN4, the finite coproducts
`∐_{i = 1, …, n} h_{U_i}^♯` of sheafified representables
(`Stacks.Cohomology.ColimitsOfCohomology.FiniteCoproductSheafifiedYoneda`): `Ext^p(ℤ_K^♯, F) = 0`
in positive degrees for every `K` in that set. The upgrade is free — `Ext` out of a coproduct is
the product of the `Ext`s — and it is the sharpest form in which a covering set bears on the
acyclicity of `F`.

It was written to settle a specific question, and the answer is negative, so the measurement is
recorded here next to the positive statement.

## The question, and the measurement

Condition (2) of Stacks 07A1 is `Stacks.Cohomology.CechComplexExactPos`: for **every** surjection
`g : K' ⟶ K` of sheaves of sets and every `n`, the Čech complex `Hom(ℤ_{K'_•}^♯, F)` is exact at
`n + 1`. For `F` the colimit `colim_i f_i⁻¹F_i` of pullbacks of a pointwise injective system it is
the one input of
`Stacks.WeakSites.ColimitSiteCohomology.isZero_rightDerivedΓ_of_pointwise_injective`, and the
natural hope is that a covering set supplies it: deriving it from the levels asks
`Hom(ℤ_{K'_n}^♯, -)` to commute with the colimit for the Čech terms `K'_n`, which is
quasi-compactness of those terms, which is what a covering set is about.

**It does not, and the obstruction is not the arbitrariness of the surjection.** Three
measurements, in increasing order of decisiveness.

1. The Čech terms of a surjection one did not choose are the fibre powers `K'^{n+1}_{/K}`, and
   nothing about a covering set `S` bounds them: `K'` is not required to lie in `S`, and a fibre
   power over an arbitrary sheaf of two members of `S` is not a member of `S` — `S` is stable
   under *covering* a product, not under taking one.
2. There is no refinement step. Given `g' : K'' ⟶ K` factoring through `g` the induced map of Čech
   nerves gives `Hom(ℤ_{K'_•}^♯, F) ⟶ Hom(ℤ_{K''_•}^♯, F)`, so exactness for the refinement does
   not imply exactness for the original: the map goes the wrong way, and replacing the surjection
   changes the conclusion rather than preserving it.
3. Decisively, and this is what makes (1) and (2) moot: **the consumer does not need arbitrary
   surjections at all.** `Stacks.Cohomology.isTotallyAcyclic_of_conditions` applies its condition
   (2) exactly once, inside `Stacks.Cohomology.subsingleton_ext_freeAbelianSheaf_succ`, to the one
   surjection handed to it by `Stacks.Cohomology.exists_epi_subsingleton_ext` — whose source is
   `F`-acyclic in all positive degrees. In that application the acyclicity of the Čech *terms* in
   every degree `1 ≤ q ≤ n` is already supplied by the induction hypothesis, which is quantified
   over all presheaves of sets. So condition (2) contributes nothing except the top degree
   `n + 1`, in exactly the degree the induction is trying to reach. Condition (2) is an
   induction-breaking input of the same strength as the conclusion in each degree, not a
   quasi-compactness statement in disguise;
   `Stacks.Cohomology.cechComplexExactPos_of_isTotallyAcyclic` is the converse that makes this
   precise.

So `CechComplexExactPos` is **not** a covering-set consequence, and no weakening of condition (2)
to surjections with quasi-compact, or `S`-indexed, or `F`-acyclic source makes it one. What a
covering set does give towards the acyclicity of `F` is exactly
`subsingleton_ext_freeAbelianSheaf_of_mem_finiteCoproductSheafifiedYoneda` below, and that is
condition (1) restated, not condition (2).

## Main results

* `Stacks.Cohomology.subsingleton_ext_freeAbelianSheaf_of_mem_finiteCoproductSheafifiedYoneda`:
  **an abelian sheaf acyclic over every object of the site is acyclic over every member of the
  covering set of Stacks 0GN4.**

## Implementation notes

The index type of a member of the covering set is `Fin n`, while the coproducts and the `Ext`
comparison `CategoryTheory.Abelian.Ext.coproductAddEquiv` are at the universe of the site; the
family is therefore reindexed along `Equiv.ulift` as in the proof of Stacks 0GN4 itself.

The passage from a coproduct of *sheaves* of sets to the coproduct of the free abelian sheaves
goes through the *presheaf* coproduct: `Stacks.Cohomology.VanishesOnObjects` is stated at
`CategoryTheory.Presheaf.freeAbelianSheaf` of a presheaf, that functor is a left adjoint and so
preserves the presheaf coproduct, and it inverts `CategoryTheory.toSheafify` because that is a
`J.W`-morphism (`CategoryTheory.Presheaf.isIso_freeAbelianSheaf_map_of_W`). This is the chain of
`Stacks.Cohomology.exists_epi_subsingleton_ext`, run at a finite family of objects of the site
instead of at the family of Stacks 00WS.

## References

* [Stacks Project, Tag 07A1](https://stacks.math.columbia.edu/tag/07A1)
* [Stacks Project, Tag 0GN4](https://stacks.math.columbia.edu/tag/0GN4)
* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace Stacks.Cohomology

open Stacks.Cohomology.ColimitsOfCohomology

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

attribute [local instance] ColimitsOfCohomology.sheafOfTypes_hasColimitsOfSize

/-- **An abelian sheaf acyclic over every object of the site is acyclic over every member of the
covering set of Stacks 0GN4.** If `F` satisfies condition (1) of Stacks 07A1 — `Ext^p(ℤ_U^♯, F)`
vanishes in positive degrees for every object `U` — then `Ext^p(ℤ_K^♯, F)` vanishes in positive
degrees for every finite coproduct `K = ∐_{i = 1, …, n} h_{U_i}^♯` of sheafified representables of
objects of any `B ⊆ Ob(C)`.

Nothing about `B` is used: the statement is about the *shape* of the members of the covering set,
and it holds for the covering set of any collection of objects. In particular it holds for
`B = Set.univ`, the only collection for which condition (2) of Stacks 0GN4 can hold at all.

The free abelian sheaf functor is a left adjoint, so it carries the coproduct to a coproduct, and
`Ext` out of a coproduct is the product of the `Ext`s
(`CategoryTheory.Abelian.Ext.coproductAddEquiv`); each factor vanishes by condition (1). -/
theorem subsingleton_ext_freeAbelianSheaf_of_mem_finiteCoproductSheafifiedYoneda
    (F : Sheaf J AddCommGrpCat.{u}) (h₁ : VanishesOnObjects.{w} J F) (B : Set C)
    {K : Sheaf J (Type u)} (hK : K ∈ FiniteCoproductSheafifiedYoneda J B)
    (p : ℕ) (hp : 1 ≤ p) :
    Subsingleton (Abelian.Ext.{w} ((Presheaf.freeAbelianSheaf J).obj K.obj) F p) := by
  classical
  obtain ⟨n, U, -, ⟨e⟩⟩ := hK
  have hpres : PreservesColimitsOfSize.{u, u} (Presheaf.freeAbelianSheaf J) :=
    (Presheaf.freeAbelianSheafAdj J).leftAdjoint_preservesColimits
  have hpresSet : PreservesColimitsOfSize.{u, u} (presheafToSheaf J (Type u)) :=
    (sheafificationAdjunction J (Type u)).leftAdjoint_preservesColimits
  -- the family, reindexed to the universe of the site
  set O := ULift.{u} (Fin n) with hO
  set V : O → C := fun i => U i.down with hV
  -- `K` is the sheafification of the presheaf coproduct of the `h_{V i}`
  set P : Cᵒᵖ ⥤ Type u := ∐ fun i : O => uliftYoneda.{u}.obj (V i) with hP
  have eK : K ≅ (presheafToSheaf J (Type u)).obj P :=
    e.trans ((Sigma.reindex (Equiv.ulift.{u}).symm
        fun i : O => (Sheaf.sheafifiedYoneda J).obj (V i)).trans
      (PreservesCoproduct.iso (presheafToSheaf J (Type u))
        fun i : O => uliftYoneda.{u}.obj (V i)).symm)
  -- transport along that isomorphism, then invert the sheafification map
  refine subsingleton_ext_of_iso
    ((Presheaf.freeAbelianSheaf J).mapIso ((sheafToPresheaf J (Type u)).mapIso eK)) p ?_
  have hW := Presheaf.isIso_freeAbelianSheaf_map_of_W J (toSheafify J P) (J.W_toSheafify P)
  refine subsingleton_ext_of_iso
    (asIso ((Presheaf.freeAbelianSheaf J).map (toSheafify J P))).symm p ?_
  -- distribute the free abelian sheaf functor over the coproduct; the coproduct of the free
  -- abelian sheaves is the image of the presheaf coproduct, which is how its existence is
  -- supplied here rather than left to instance search
  have hcomp : HasColimit (Discrete.functor (fun i : O => uliftYoneda.{u}.obj (V i)) ⋙
      Presheaf.freeAbelianSheaf J) :=
    HasColimit.mk ⟨(Presheaf.freeAbelianSheaf J).mapCocone (colimit.cocone _),
      isColimitOfPreserves (Presheaf.freeAbelianSheaf J) (colimit.isColimit _)⟩
  have hcop : HasCoproduct
      fun i : O => (Presheaf.freeAbelianSheaf J).obj (uliftYoneda.{u}.obj (V i)) :=
    hasColimit_of_iso (F := Discrete.functor (fun i : O => uliftYoneda.{u}.obj (V i)) ⋙
      Presheaf.freeAbelianSheaf J) (Discrete.natIso fun _ => Iso.refl _)
  refine subsingleton_ext_of_iso (PreservesCoproduct.iso (Presheaf.freeAbelianSheaf J)
    fun i : O => uliftYoneda.{u}.obj (V i)) p ?_
  have hfac : ∀ i : O, Subsingleton (Abelian.Ext.{w}
      ((Presheaf.freeAbelianSheaf J).obj (uliftYoneda.{u}.obj (V i))) F p) := fun i =>
    h₁ (V i) _ ((Functor.RepresentableBy.equivUliftYonedaIso _ (V i)).symm (Iso.refl _)) p hp
  exact ⟨fun a b => (Abelian.Ext.coproductAddEquiv
    (X := fun i : O => (Presheaf.freeAbelianSheaf J).obj (uliftYoneda.{u}.obj (V i))) F p).injective
      (funext fun i => (hfac i).elim _ _)⟩

end Stacks.Cohomology

end

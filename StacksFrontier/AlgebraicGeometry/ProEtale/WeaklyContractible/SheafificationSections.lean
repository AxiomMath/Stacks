module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings

/-!
# Sections of a sheafification over an object with disjoint-union refinements

Let `(C, J)` be a site and let `P` be a presheaf of sets on `C` which sends finite disjoint
unions to products, meaning that whenever a finite family of morphisms `V i ⟶ U` exhibits `U`
as the coproduct of the `V i`, the sections of `P` over `U` are the families of sections over
the `V i`. The empty family is included, so the sections of `P` over an initial object form a
singleton.

Over an object `U` all of whose covering sieves contain such a disjoint-union decomposition of
`U` itself, sheafification does not change the sections: the unit `P ⟶ P^#` is bijective at
`U`. Only two generic facts about the unit are used, local injectivity and local surjectivity.
Local injectivity turns two sections of `P` over `U` with the same image into a covering sieve
on which they agree; a decomposition inside that sieve identifies them, because the sections of
`P` over `U` are determined by their restrictions to the members of a decomposition. Local
surjectivity turns a section of `P^#` over `U` into a covering sieve on whose arrows it comes
from `P`; a decomposition inside that sieve assembles those local sections into a single section
of `P` over `U`, and the two then agree over `U` because `P^#` is a sheaf and the decomposition
generates a covering sieve.

The hypothesis on `P` is needed only for the decompositions that actually occur, so the main
statement takes it in the pointwise form of a bijection; the remaining statements supply that
bijection from the two standard sources. A functor preserving finite products gives it for every
colimit cofan, and for a site fibred over schemes it may be imposed only on the families whose
images form a disjoint clopen cover, which are the finite disjoint union decompositions of the
pro-étale site.

## Main definitions

* `CategoryTheory.GrothendieckTopology.SendsFiniteDisjointUnionsToProducts`: a presheaf of sets
  sends finite disjoint unions to products, including the empty one.

## Main results

* `CategoryTheory.GrothendieckTopology.bijective_toSheafify_app_of_splitRefinements`:
  sheafification is bijective on sections over an object whose covering sieves contain families
  for which the sections of the presheaf are determined by restriction.
* `CategoryTheory.GrothendieckTopology.bijective_app_of_isLocallyBijective_of_splitRefinements`:
  the same for any locally bijective morphism into a sheaf, with values in a concrete category.
* `GrothendieckTopology.sendsFiniteDisjointUnionsToProducts_of_preservesFiniteProducts`, in the
  same namespace: a presheaf preserving finite products sends finite disjoint unions to
  products.
* `CategoryTheory.GrothendieckTopology.bijective_toSheafify_app_of_disjointUnionRefinements`:
  the same conclusion from a presheaf sending finite disjoint unions to products together with
  covering sieves containing colimit cofans.
* `CategoryTheory.GrothendieckTopology.bijective_toSheafify_app_of_clopenRefinements`: the same
  conclusion on a site fibred over schemes, with both the hypothesis on the presheaf and the
  refinement property imposed only on families whose images form a disjoint clopen cover.

## Implementation notes

The value universe of the presheaf is independent of the site, and the two local bijectivity
instances for the unit of sheafification are assumed through
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`, which is where that independence
is paid for.

### No `@[stacks 0F63]`

This file is a prerequisite for [Tag 0F63](https://stacks.math.columbia.edu/tag/0F63) and does
not state it. That lemma says that for a presheaf of sets on the pro-étale site of a scheme
which sends finite disjoint unions to products, the associated sheaf has the same sections as
the presheaf over any affine weakly contractible object. It is
`bijective_toSheafify_app_of_clopenRefinements` below, applied to the small pro-étale site
`AlgebraicGeometry.ProEtale.SmallProetale` with its topology
`AlgebraicGeometry.ProEtale.SmallProetale.topology`, once the refinement hypothesis is available
there for an affine weakly contractible object. Three declarations are missing for that.

* The clopen-refinement property of Tag 098H for the small pro-étale site, say
  `AlgebraicGeometry.ProEtale.SmallProetale.exists_clopenRefinement_of_isWContractible`: every
  covering sieve of an affine object of `SmallProetale B S hS` whose ring of global sections is
  w-contractible contains a finite family of objects of that site whose images form a disjoint
  clopen cover. Only the big-site form
  `AlgebraicGeometry.ProEtale.exists_clopenRefinement_of_isWContractible` exists; the small-site
  form is constructed inside the proof of
  `AlgebraicGeometry.ProEtale.SmallProetale.surjective_sections_of_isWContractible` and is not
  stated separately.
* The implication (2) implies (1) of Tag 098H for the small pro-étale site, say
  `AlgebraicGeometry.ProEtale.SmallProetale.isWContractible_of_isWeaklyContractible`: an affine
  object of `SmallProetale B S hS` which is weakly contractible for the topology of that site
  has w-contractible ring of global sections. This is what turns the hypothesis of Tag 0F63,
  weak contractibility of the object, into the hypothesis of the previous item. It exists for a
  big pro-étale site as
  `AlgebraicGeometry.ProEtale.BigProetaleSite.isWContractible_of_isWeaklyContractible`
  and for the pro-étale topology on all schemes as
  `ProetaleWContractible.isWContractible_of_isWeaklyContractible`, and in neither form does it
  apply to the small site.
* The identification of a disjoint clopen cover with a coproduct, say
  `ProetaleWContractible.IsClopenDecompositionCover.isColimitCofan`: a finite family of open
  immersions with pairwise disjoint clopen images covering their target exhibits that target as
  the coproduct of the sources. Without it the hypothesis on the presheaf in
  `bijective_toSheafify_app_of_clopenRefinements` cannot be obtained from the general
  `SendsFiniteDisjointUnionsToProducts`, and so neither from
  `CategoryTheory.Limits.PreservesFiniteProducts`. The small pro-étale site is not known here to
  have finite coproducts at all; `CategoryTheory.Limits.HasFiniteCoproducts` is available only
  for the affine ind-étale site, as
  `AlgebraicGeometry.ProEtale.AffineIndEtaleProetale.hasFiniteCoproducts`.

## References

* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 00WB](https://stacks.math.columbia.edu/tag/00WB)
* [Stacks Project, Tag 0F63](https://stacks.math.columbia.edu/tag/0F63)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v w u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type w} [Category.{v} C]

/-- A presheaf of sets *sends finite disjoint unions to products* when, for every finite family
of morphisms exhibiting their common target as the coproduct of their sources, the sections over
the target are exactly the families of sections over the sources.

The empty family is included: taking `n = 0`, the condition says that the sections over an
initial object form a singleton, which for a presheaf on a site of schemes is the condition that
the empty scheme is sent to the singleton. -/
def SendsFiniteDisjointUnionsToProducts (P : Cᵒᵖ ⥤ Type t) : Prop :=
  ∀ (n : ℕ) (U : C) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U), IsColimit (Cofan.mk U f) →
    Function.Bijective (fun (x : P.obj (op U)) (i : Fin n) ↦ P.map (f i).op x)

/-- A presheaf of sets preserving finite products sends finite disjoint unions to products: a
colimit cofan becomes a limit fan in the opposite category, and a limit fan of types is the
product of its components. -/
theorem sendsFiniteDisjointUnionsToProducts_of_preservesFiniteProducts (P : Cᵒᵖ ⥤ Type t)
    [PreservesFiniteProducts P] : SendsFiniteDisjointUnionsToProducts P := by
  intro n U V f hc
  have hlim : IsLimit (Fan.mk (P.obj (op U)) (fun i ↦ P.map (f i).op)) :=
    (isLimitMapConeFanMkEquiv P (fun i ↦ op (V i)) _)
      (isLimitOfPreserves P (Cofan.IsColimit.op hc))
  rw [Function.bijective_iff_existsUnique]
  intro x
  obtain ⟨s, hs, hu⟩ := (Types.isLimit_iff _).mp ⟨hlim⟩ (fun j ↦ x j.as) (by
    rintro ⟨j⟩ ⟨k⟩ g
    obtain rfl := Discrete.eq_of_hom g
    simp)
  exact ⟨s, funext fun j ↦ hs ⟨j⟩, fun y hy ↦ hu y fun j ↦ congrFun hy j.as⟩

/-- Sheafification is bijective on sections over `U` as soon as every covering sieve of `U`
contains a finite family of morphisms to `U` which generates a covering sieve and along which
the sections of `P` over `U` restrict bijectively to families of sections over the sources.

The two directions use the two local bijectivity properties of the unit of sheafification. Two
sections of `P` over `U` with the same image agree on a covering sieve, hence on a family of the
given kind, hence are equal. A section of the sheafification over `U` comes from `P` on a
covering sieve, hence on a family of the given kind, and the resulting sections over the sources
assemble to a section of `P` over `U`; its image and the original section agree on the family,
so they are equal because the sheafification is a sheaf and the family generates a covering
sieve. -/
theorem bijective_toSheafify_app_of_splitRefinements
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type t)]
    [J.WEqualsLocallyBijective (Type t)]
    (P : Cᵒᵖ ⥤ Type t) (U : C)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        Sieve.ofArrows V f ∈ J U ∧ (∀ i, S.arrows (f i)) ∧
        Function.Bijective (fun (x : P.obj (op U)) (i : Fin n) ↦ P.map (f i).op x)) :
    Function.Bijective ((_root_.CategoryTheory.toSheafify J P).app (op U)) := by
  classical
  set Q := _root_.CategoryTheory.sheafify J P with hQdef
  have hQsheaf : Presheaf.IsSheaf J Q := ((presheafToSheaf J (Type t)).obj P).property
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨n, V, f, hcov, hmem, hbij⟩ :=
      href _ (Presheaf.equalizerSieve_mem J (_root_.CategoryTheory.toSheafify J P) x y hxy)
    exact hbij.injective (funext fun i ↦ hmem i)
  · intro x
    obtain ⟨n, V, f, hcov, hmem, hbij⟩ :=
      href _ (Presheaf.imageSieve_mem J (_root_.CategoryTheory.toSheafify J P) (U := op U) x)
    choose y hy using fun i ↦ (hmem i : ∃ _, _)
    obtain ⟨s, hs⟩ := hbij.surjective y
    refine ⟨s, ?_⟩
    have hsi (i : Fin n) : P.map (f i).op s = y i := congrFun hs i
    refine (hQsheaf.isSheafFor _ hcov).isSeparatedFor.ext ?_
    intro Y g hg
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    have hres : Q.map (f i).op ((_root_.CategoryTheory.toSheafify J P).app (op U) s) =
        Q.map (f i).op x := by
      rw [← NatTrans.naturality_apply (_root_.CategoryTheory.toSheafify J P) (f i).op s,
        hsi i, hy i]
    simp only [op_comp, Functor.map_comp, types_comp_apply, hres]

/-- **The split-refinement criterion for a locally bijective morphism.** Let `φ : P ⟶ Q` be a
locally injective and locally surjective morphism of presheaves with values in a concrete
category, whose target becomes a sheaf of sets after forgetting. If every covering sieve of `U`
contains a finite family of morphisms which generates a covering sieve and for which the
sections of `P` over `U` are determined by restriction, then `φ` is bijective on sections over
`U`.

This is `bijective_toSheafify_app_of_splitRefinements` with the unit of sheafification replaced
by an arbitrary locally bijective morphism to a sheaf; it applies in particular to the unit of
sheafification of presheaves of abelian groups. -/
theorem bijective_app_of_isLocallyBijective_of_splitRefinements
    {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    (J : GrothendieckTopology C) {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q)
    [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]
    (hQ : Presheaf.IsSheaf J (Q ⋙ forget A)) (U : C)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        Sieve.ofArrows V f ∈ J U ∧ (∀ i, S.arrows (f i)) ∧
        Function.Bijective (fun (x : ToType (P.obj (op U))) (i : Fin n) ↦ P.map (f i).op x)) :
    Function.Bijective (φ.app (op U)) := by
  classical
  have hQsheaf : Presieve.IsSheaf J (Q ⋙ forget A) :=
    (isSheaf_iff_isSheaf_of_type J _).mp hQ
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨n, V, f, hcov, hmem, hbij⟩ := href _ (Presheaf.equalizerSieve_mem J φ x y hxy)
    exact hbij.injective (funext fun i ↦ hmem i)
  · intro x
    obtain ⟨n, V, f, hcov, hmem, hbij⟩ := href _ (Presheaf.imageSieve_mem J φ x)
    choose y hy using fun i ↦ (hmem i : ∃ _, _)
    obtain ⟨s, hs⟩ := hbij.surjective y
    refine ⟨s, ?_⟩
    have hsi (i : Fin n) : P.map (f i).op s = y i := congrFun hs i
    refine (hQsheaf _ hcov).isSeparatedFor.ext ?_
    intro Y g hg
    obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
    have hres : Q.map (f i).op (φ.app (op U) s) = Q.map (f i).op x := by
      rw [← NatTrans.naturality_apply φ (f i).op s, hsi i, hy i]
    change Q.map (a ≫ f i).op (φ.app (op U) s) = Q.map (a ≫ f i).op x
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hres]

/-- Sheafification is bijective on sections over `U` for a presheaf of sets sending finite
disjoint unions to products, as soon as every covering sieve of `U` contains a finite family of
morphisms which generates a covering sieve and exhibits `U` as the coproduct of its sources. -/
theorem bijective_toSheafify_app_of_disjointUnionRefinements
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type t)]
    [J.WEqualsLocallyBijective (Type t)]
    (P : Cᵒᵖ ⥤ Type t) (hP : SendsFiniteDisjointUnionsToProducts P) (U : C)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U) (_ : IsColimit (Cofan.mk U f)),
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i)) :
    Function.Bijective ((_root_.CategoryTheory.toSheafify J P).app (op U)) := by
  refine bijective_toSheafify_app_of_splitRefinements J P U fun S hS ↦ ?_
  obtain ⟨n, V, f, hc, hcov, hmem⟩ := href S hS
  exact ⟨n, V, f, hcov, hmem, hP n U V f hc⟩

/-- Sheafification is bijective on sections over `U` on a site equipped with a functor `Q` to
schemes, for a presheaf of sets whose sections over the target of a family whose `Q`-images form
a disjoint clopen cover are the families of sections over the sources, as soon as every covering
sieve of `U` contains such a family generating a covering sieve.

On the pro-étale site a family whose images form a disjoint clopen cover is exactly a finite
disjoint union decomposition, so the hypothesis on the presheaf is the condition that it sends
finite disjoint unions to products, and the refinement hypothesis is the conclusion of
Tag 098H. -/
theorem bijective_toSheafify_app_of_clopenRefinements
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type t)]
    [J.WEqualsLocallyBijective (Type t)]
    (Q : C ⥤ AlgebraicGeometry.Scheme.{u}) (P : Cᵒᵖ ⥤ Type t) (U : C)
    (hP : ∀ (n : ℕ) (W : C) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ W),
      ProetaleWContractible.IsClopenDecompositionCover
        (fun i ↦ Q.obj (V i)) (fun i ↦ Q.map (f i)) →
      Function.Bijective (fun (x : P.obj (op W)) (i : Fin n) ↦ P.map (f i).op x))
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        ProetaleWContractible.IsClopenDecompositionCover
          (fun i ↦ Q.obj (V i)) (fun i ↦ Q.map (f i)) ∧
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i)) :
    Function.Bijective ((_root_.CategoryTheory.toSheafify J P).app (op U)) := by
  refine bijective_toSheafify_app_of_splitRefinements J P U fun S hS ↦ ?_
  obtain ⟨n, V, f, hdec, hcov, hmem⟩ := href S hS
  exact ⟨n, V, f, hcov, hmem, hP n U V f hdec⟩

end CategoryTheory.GrothendieckTopology

end

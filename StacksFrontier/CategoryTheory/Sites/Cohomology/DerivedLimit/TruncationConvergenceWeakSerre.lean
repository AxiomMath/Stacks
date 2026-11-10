module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationTowerConvergence
import StacksCore.Tactic.StacksAttribute

/-!
# Convergence of the truncation tower for a weak Serre subcategory of bounded local dimension

In the Olsson--Laszlo situation of Stacks 0D6R — a site `C`, a sheaf of rings `O`, a weak Serre
subcategory `A` of `O`-modules, and a class `B` of objects covering every object of `C`, each
`V ∈ B` carrying an integer bound `d_V` and a cofinal system of coverings of `V` on whose members
the cohomology of every module of `A` vanishes above `d_V` — let `E` be an object of `D_A(O)`,
that is, an object of the derived category of `O`-modules all of whose cohomology sheaves lie in
`A`. Then the canonical map

`E ⟶ R lim τ_{≥ -n} E`

of Derived Categories, Remark 0H72, is an isomorphism in `D(O)`. This is Stacks 0D6S.

## Main results

* `Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB` (Stacks 0D6S):
  the canonical map from an object of `D_A(O)` to a derived limit of its truncation tower is an
  isomorphism.
* `Stacks.Cohomology.hasProduct_truncGETower_of_enoughInjectives` and
  `Stacks.Cohomology.hasProduct_truncGETower_olssonLaszlo`: the truncation tower has a product
  in the derived category, so that the statement above needs no assumed product.

## Implementation notes

The proof is the Olsson--Laszlo specialisation of
`Stacks.Cohomology.isIso_to_isDerivedLimit_truncationGETower`, which is Stacks 0D6M and
0D6N: the degree-dependent bound `p(V, -)` of that lemma is taken to be the constant
`S.degreeBound V hV`, and its cofinal system of coverings of `V` to be `(S.coverings V hV).cov`.
Every cohomology sheaf of `E` lies in `A`, so the vanishing hypothesis of the general lemma is
exactly the standing vanishing hypothesis of the situation, with no restriction on the degree of
the cohomology sheaf involved; this is why a bound constant in the total degree suffices here,
whereas Stacks 0D6N, whose hypothesis only controls the cohomology sheaves in negative degrees,
needs `d_V + max(0, m)`.

Membership in `D_A(O)` is `DerivedCategoryB.derivedCategoryB`, applied to the object property
`S.A` of the situation; by definition it says that every cohomology sheaf of `E` satisfies `S.A`.
The truncation tower is `Stacks.DerivedLimit.truncGETower`, and the derived limit is supplied by
its defining distinguished triangle — the unfolding of
`CategoryTheory.Pretriangulated.IsDerivedLimit` — together with a map `c` whose composites with
all the projections of that triangle are the canonical truncation maps
`DerivedCategory.TStructure.t.truncGEπ`. This pins `c` to the canonical map of Remark 0H72
rather than to an arbitrary map to an arbitrary derived limit, which the predicate
`IsDerivedLimit` alone would not do, since it does not remember the first arrow of its triangle.

The product `∏ₙ τ_{≥ -n} E`, which the presenting triangle mentions, is not assumed: the general
lemma above takes it as an instance, and `hasProduct_truncGETower_olssonLaszlo` supplies it for
every object of `D(O)` in the situation. Its two ingredients are the countable products of
`SheafOfModules.{wModule} S.O`, which are the objectwise ones of
`SheafOfModules.hasLimitsOfShape`, and the `EnoughInjectives` field of the situation; the step
from them to a product in the derived category is Stacks 0BK7, in the form
`DerivedCategory.exists_isDerivedLimit_of_forall_isGE`, applied to the tower, each of whose
members `τ_{≥ -n} E` is bounded below. In particular the exactness of countable products, which
fails for sheaves, is nowhere used: only the members of the tower are resolved, and each is
resolved K-injectively because it is bounded below.

## References

* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0H72](https://stacks.math.columbia.edu/tag/0H72)
* [Stacks Project, Tag 0BK7](https://stacks.math.columbia.edu/tag/0BK7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u wRing wModule

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- **The truncation tower from below of an object of `D(A)` has a product.** If `A` is an
abelian category with countable products and enough injectives, then the family
`n ↦ τ_{≥ -n} E` has a product in `D(A)`: each of its members is bounded below, so
`DerivedCategory.exists_isDerivedLimit_of_forall_isGE` ([Stacks, Tag 0BK7]) applies. Each
`τ_{≥ -n} E` is represented by a K-injective complex, and the termwise product of those
complexes represents the product; no exactness of the products of `A` is used. -/
theorem hasProduct_truncGETower_of_enoughInjectives {A : Type*} [Category* A] [Abelian A]
    [HasProductsOfShape ℕ A] [EnoughInjectives A] [HasDerivedCategory A]
    (E : DerivedCategory A) :
    HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower A E).obj ⟨n⟩ :=
  (DerivedCategory.exists_isDerivedLimit_of_forall_isGE (Stacks.DerivedLimit.truncGETower A E)
    fun n ↦ ⟨-(n : ℤ), by
      change ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E).IsGE _
      infer_instance⟩).choose

/-- **In the Olsson--Laszlo situation the truncation tower of any object of `D(O)` has a
product.** The countable products of sheaves of modules are the objectwise ones
(`SheafOfModules.hasLimitsOfShape`), and the situation carries enough injectives as one of its
fields, so `hasProduct_truncGETower_of_enoughInjectives` applies. -/
instance hasProduct_truncGETower_olssonLaszlo
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (E : DerivedCategory (SheafOfModules.{wModule} S.O)) :
    HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) E).obj ⟨n⟩ :=
  haveI : HasLimitsOfShape (Discrete ℕ) (SheafOfModules.{wModule} S.O) :=
    SheafOfModules.hasLimitsOfShape.{wModule} (R := S.O) (Discrete ℕ)
  hasProduct_truncGETower_of_enoughInjectives E

/-- **Stacks Project, Tag 0D6S.** In the Olsson--Laszlo situation, for an object `E` of the
derived category whose cohomology sheaves all lie in the weak Serre subcategory `A`, the
canonical map from `E` to a derived limit of its tower of truncations `τ_{≥ -n} E` from below is
an isomorphism. -/
@[stacks 0D6S]
theorem isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB
    (S : OlssonLaszloSituation.{v, u, wRing, wModule})
    (E : DerivedCategory (SheafOfModules.{wModule} S.O))
    (hE : DerivedCategoryB.derivedCategoryB S.A E)
    (L : DerivedCategory (SheafOfModules.{wModule} S.O))
    (q : L ⟶ ∏ᶜ fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) E).obj ⟨n⟩)
    (hL : ∃ δ :
      (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) E).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧,
      Triangle.mk q (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) E).obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦
            (Stacks.DerivedLimit.truncGETower
              (SheafOfModules.{wModule} S.O) E).obj ⟨n⟩) (n + 1) ≫
            (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) E).map
              (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (SheafOfModules.{wModule} S.O)))
    (c : E ⟶ L)
    (hc : ∀ n : ℕ, c ≫ q ≫ Pi.π
      (fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower (SheafOfModules.{wModule} S.O) E).obj ⟨n⟩) n =
      (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  obtain ⟨δ, hL⟩ := hL
  exact isIso_to_isDerivedLimit_truncationGETower S.O E S.B S.basis_cover
    (fun V hV _ => S.degreeBound V hV) (fun V hV => (S.coverings V hV).cov)
    (fun V hV => (S.coverings V hV).isCover)
    (fun V hV => (S.coverings V hV).cofinal)
    (fun V hV 𝒰 h𝒰 i p m hm =>
      S.vanishing V hV 𝒰 h𝒰 i p hm _ (hE (m - (p : ℤ))))
    L c q δ hL hc

end Stacks.Cohomology

end

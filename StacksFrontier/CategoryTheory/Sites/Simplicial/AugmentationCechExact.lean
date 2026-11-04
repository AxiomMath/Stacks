module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Abelian.ExactOnHom
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechTermMate

/-!
# Exactness of the augmented Čech complex in every degree, for an injective sheaf

Let `S` be a simplicial-site situation of Stacks 09WE, `a` an augmentation of `S` towards a site
`(D, K)` as in Stacks 0D6Z, and `F` an abelian sheaf on the total site. Stacks 0D79 asserts that
the complex

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ a_{2,*}F_2 ⟶ …`

of `StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationCechComplex.lean` is exact in degrees
`-1` and `0` for every `F`, and exact everywhere when `F` is injective. The first half is proved
there, from the fact that `a_*F` is the limit of the cosimplicial sheaf `n ↦ a_{n,*}F_n`. This
file proves the second.

The argument is the source's. Exactness of a complex of abelian sheaves at a term is detected by
the hom-functors — `Stacks.CategoryTheory.ExactOnHom.exact_of_forall_function_exact`, which is
the Yoneda step, and where left exactness of `Hom(𝒢, -)` is no obstruction because `𝒢` may be
taken to be the kernel. The degree-`n` term `F ↦ a_{n,*}F_n` of this complex is a right adjoint
whose left adjoint is the degree-`n` term `𝒢 ↦ g_{n!}(a_n^{-1}𝒢)` of the resolution of
Stacks 0D78 (`cechTermAdjunction`), and the conjugate of each cosimplicial transition is the
corresponding structure map of that resolution
(`conjugateEquiv_abelianCosimplicialPushforward_map_app`), so `Hom(𝒢, -)` of this complex is
`Hom(-, F)` of that resolution. For injective `F` the latter is exact, the resolution being
exact.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.cechCoface` and `.cechDifferential`: the
  cosimplicial transitions of the complex of Stacks 0D79 at the cofaces, and their alternating
  sum, as natural transformations between the terms of the complex rather than morphisms at one
  sheaf.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.precompIsoEquiv`: precomposition with an
  isomorphism, as a bijection of hom-sets.

## Main results

* `CategoryTheory.CosimplicialObject.d_succ_eq_objD`: the degree-`j` differential of an
  alternating-coface complex is the alternating sum of the cofaces out of `⦋j⦌`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.augmentedCechComplex_d_eq`: at an abelian
  sheaf, `cechDifferential` is the differential of the complex of Stacks 0D79.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.conjugateEquiv_cechDifferential_app`: the
  conjugate of that differential is the differential of the resolution of Stacks 0D78, read
  through the identifications of its terms.
* `CategoryTheory.SimplicialSiteSituation.Augmentation`
  `.augmentedCechComplex_exactAt_of_injective`: **Stacks 0D79**, exactness in every degree for an
  injective abelian sheaf.

## Implementation notes

`cechCoface` is named rather than inlined so that the alternating sum is formed in the hom-group
of `abelianComponentPushforward S D K a ⦋j⦌ ⟶ abelianComponentPushforward S D K a ⦋j + 1⦌`. Writing
the summands as `(abelianCosimplicialPushforward S D K a).map (SimplexCategory.δ i)` instead makes
the sum's type the cosimplicial functor's own values at `⦋j⦌` and `⦋j + 1⦌`, which are the same
functors by definition but a different spelling, and then the generic sum lemmas for conjugates do
not fire on it.

The final statement carries no `HasSheafify` hypothesis: the instance is available for every
Grothendieck topology on a small site, and the intermediate results that need it — the ones built
from `cechTermAdjunction` — are confined to a section that takes it as a hypothesis.

## References

* [Stacks Project, Tag 0D79](https://stacks.math.columbia.edu/tag/0D79)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Topos.AbelianPushforward
open scoped Simplicial

universe v₁ u₁ u

namespace CategoryTheory.CosimplicialObject

/-- The differential of the alternating-coface complex of a cosimplicial object in degree `j` is
the alternating sum of the cofaces out of `⦋j⦌`. -/
theorem d_succ_eq_objD {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    (X : CosimplicialObject A) (j : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex A).obj X).d j (j + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD X j :=
  CochainComplex.of_d _ (AlgebraicTopology.AlternatingCofaceMapComplex.objD X) j

end CategoryTheory.CosimplicialObject

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- Precomposition with an isomorphism, as a bijection of hom-sets. -/
def precompIsoEquiv {C : Type*} [Category C] {A B : C} (e : A ≅ B) (F : C) :
    (A ⟶ F) ≃ (B ⟶ F) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp

/-- The cosimplicial transition of the complex of Stacks 0D79 at the `i`-th coface out of
`⦋j⦌`, as a natural transformation between the terms of the complex. Named so that the
alternating sum below is formed in the hom-group of those terms. -/
def cechCoface (j : ℕ) (i : Fin (j + 2)) :
    abelianComponentPushforward S D K a ⦋j⦌ ⟶ abelianComponentPushforward S D K a ⦋j + 1⦌ :=
  (abelianCosimplicialPushforward S D K a).map (SimplexCategory.δ i)

/-- The differential of the complex of Stacks 0D79, above its augmentation, as a natural
transformation between its terms: the alternating sum of the cosimplicial transitions at the
cofaces. -/
def cechDifferential (j : ℕ) :
    abelianComponentPushforward S D K a ⦋j⦌ ⟶ abelianComponentPushforward S D K a ⦋j + 1⦌ :=
  ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • cechCoface S D K a j i

/-- At an abelian sheaf on the total site the natural transformation is the differential of the
complex of Stacks 0D79. -/
theorem augmentedCechComplex_d_eq (j : ℕ) (F : Sheaf S.totalTopology Ab.{u}) :
    (augmentedCechComplex S D K a F).d (j + 1) (j + 2) =
      (cechDifferential S D K a j).app F := by
  have h : (cechDifferential S D K a j).app F =
      ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (cechCoface S D K a j i).app F :=
    (NatTrans.app_sum _ _ _).trans
      (Finset.sum_congr rfl fun i _ => NatTrans.app_zsmul _ _ _)
  exact (augmentedCechComplex_d_succ_succ S D K a F j (j + 1)).trans
    ((CosimplicialObject.d_succ_eq_objD (abelianCechDiagram S D K a F) j).trans h.symm)

section Conjugate

variable [HasSheafify K Ab.{u}]

/-- The left adjoint of a term of the complex of Stacks 0D79 is additive, the term itself being
so. -/
theorem additive_cechTermLowerShriek (k : SimplexCategory) :
    (cechTermLowerShriek S D K a k).Additive :=
  Stacks.CategoryTheory.ExactOnHom.additive_of_adjunction (cechTermAdjunction S D K a k)

/-- The conjugate of the differential is the differential of a simplicial object `X` whose
terms are identified with those of the resolution, if it is so for each coface. -/
private theorem conjugateEquiv_cechDifferential_app_of_coface (G : Sheaf K Ab.{u}) (j : ℕ)
    (X : SimplicialObject (Sheaf S.totalTopology Ab.{u}))
    (e : ∀ k : ℕ, X.obj (Opposite.op ⦋k⦌) ≅ resolutionTerm S D K a G k)
    (hcf : ∀ i : Fin (j + 2),
      ((conjugateEquiv (cechTermAdjunction S D K a ⦋j⦌)
            (cechTermAdjunction S D K a ⦋j + 1⦌)).symm (cechCoface S D K a j i)).app G =
        (e (j + 1)).inv ≫ X.map (SimplexCategory.δ i).op ≫ (e j).hom) :
    ((conjugateEquiv (cechTermAdjunction S D K a ⦋j⦌)
          (cechTermAdjunction S D K a ⦋j + 1⦌)).symm (cechDifferential S D K a j)).app G =
      (e (j + 1)).inv ≫
        ((AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
            X).d (j + 1) j ≫ (e j).hom := by
  let := additive_cechTermLowerShriek S D K a ⦋j + 1⦌
  rw [cechDifferential, Stacks.CategoryTheory.ExactOnHom.conjugateEquiv_symm_app_sum,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD]
  simp only [Stacks.CategoryTheory.ExactOnHom.conjugateEquiv_symm_app_zsmul, hcf,
    SimplicialObject.δ,
    Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp]

/-- **The conjugate of the differential of the complex of Stacks 0D79 is the differential of the
resolution of Stacks 0D78.** -/
theorem conjugateEquiv_cechDifferential_app (G : Sheaf K Ab.{u}) (j : ℕ) :
    ((conjugateEquiv (cechTermAdjunction S D K a ⦋j⦌)
          (cechTermAdjunction S D K a ⦋j + 1⦌)).symm (cechDifferential S D K a j)).app G =
      (degIso S D K a G (j + 1)).inv ≫
        ((AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
            (barSimplicial S ((totalInverseImageAb S D K a).obj G))).d (j + 1) j ≫
          (degIso S D K a G j).hom :=
  conjugateEquiv_cechDifferential_app_of_coface S D K a G j _ (degIso S D K a G) fun i =>
    conjugateEquiv_abelianCosimplicialPushforward_map_app S D K a G (SimplexCategory.δ i)

/-- **The conjugate of the differential of the complex of Stacks 0D79 is the differential of the
resolution of Stacks 0D78**, in the spelling of
`CategoryTheory.SimplicialSiteSituation.Augmentation.conjugateEquiv_cechDifferential_app` with the
resolution read as the simplex-coefficient resolution `barSimplicial'` and its terms identified
through `degIso'`. -/
theorem conjugateEquiv_cechDifferential_app' (G : Sheaf K Ab.{u}) (j : ℕ) :
    ((conjugateEquiv (cechTermAdjunction S D K a ⦋j⦌)
          (cechTermAdjunction S D K a ⦋j + 1⦌)).symm (cechDifferential S D K a j)).app G =
      (degIso' S D K a G (j + 1)).inv ≫
        ((AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
            ((barSimplicial' S).obj ((totalInverseImageAb S D K a).obj G))).d (j + 1) j ≫
          (degIso' S D K a G j).hom :=
  conjugateEquiv_cechDifferential_app_of_coface S D K a G j _ (degIso' S D K a G) fun i =>
    conjugateEquiv_abelianCosimplicialPushforward_map_app' S D K a G (SimplexCategory.δ i)

end Conjugate

/-- **Stacks 0D79**, exactness in every degree for an injective abelian sheaf: the complex

`0 ⟶ a_*F ⟶ a_{0,*}F_0 ⟶ a_{1,*}F_1 ⟶ a_{2,*}F_2 ⟶ …`

is exact at every term when `F` is an injective abelian sheaf on the total site. Degrees `0` and
`1` — the source's degrees `-1` and `0` — hold for every `F` and are
`augmentedCechComplex_exactAt_zero` and `augmentedCechComplex_exactAt_one`. Above them the
argument is the source's: a complex of abelian sheaves is exact at a term as soon as `Hom(𝒢, -)`
of it is exact for every `𝒢`, each term of this complex is a right adjoint whose left adjoint is
the corresponding term of the resolution of Stacks 0D78, the mate of each cosimplicial transition
is the corresponding structure map of that resolution, and `Hom(-, F)` of the resolution is exact
because `F` is injective. -/
@[stacks 0D79 "exactness in every degree for an injective abelian sheaf"]
theorem augmentedCechComplex_exactAt_of_injective (F : Sheaf S.totalTopology Ab.{u})
    [Injective F] (k : ℕ) : (augmentedCechComplex S D K a F).ExactAt k := by
  match k with
  | 0 => exact augmentedCechComplex_exactAt_zero S D K a F
  | 1 => exact augmentedCechComplex_exactAt_one S D K a F
  | (j + 2) =>
    rw [(augmentedCechComplex S D K a F).exactAt_iff' (j + 1) (j + 2) (j + 3)
      (CochainComplex.prev_nat_succ (j + 1)) (CochainComplex.next ℕ (j + 2))]
    refine Stacks.CategoryTheory.ExactOnHom.exact_of_forall_function_exact
      ((augmentedCechComplex S D K a F).d (j + 1) (j + 2))
      ((augmentedCechComplex S D K a F).d (j + 2) (j + 3)) (by simp) ?_
    intro T
    let := additive_cechTermLowerShriek S D K a ⦋j + 2⦌
    have hQexact :
        ((AlgebraicTopology.alternatingFaceMapComplex (Sheaf S.totalTopology Ab.{u})).obj
          (barSimplicial S ((totalInverseImageAb S D K a).obj T))).ExactAt (j + 1) :=
      (resolution S D K a T).exact_positive (j + 1) (Nat.succ_pos j)
    rw [HomologicalComplex.exactAt_iff' _ (j + 2) (j + 1) j (by simp) (by simp)] at hQexact
    have hExact : Function.Exact
        (fun h : (cechTermLowerShriek S D K a ⦋j⦌).obj T ⟶ F =>
          ((conjugateEquiv (cechTermAdjunction S D K a ⦋j⦌)
            (cechTermAdjunction S D K a ⦋j + 1⦌)).symm (cechDifferential S D K a j)).app T ≫ h)
        (fun h : (cechTermLowerShriek S D K a ⦋j + 1⦌).obj T ⟶ F =>
          ((conjugateEquiv (cechTermAdjunction S D K a ⦋j + 1⦌)
            (cechTermAdjunction S D K a ⦋j + 2⦌)).symm
              (cechDifferential S D K a (j + 1))).app T ≫ h) := by
      refine Stacks.CategoryTheory.ExactOnHom.function_exact_congr_symm
        (precompIsoEquiv (degIso S D K a T j) F)
        (precompIsoEquiv (degIso S D K a T (j + 1)) F)
        (precompIsoEquiv (degIso S D K a T (j + 2)) F) _ _ _ _ ?_ ?_ ?_
        (Stacks.CategoryTheory.ExactOnHom.function_exact_hom_of_exact _ hQexact (I := F))
      · simp [precompIsoEquiv]
      all_goals
        intro h
        change (degIso S D K a T _).inv ≫ _ = _
        rw [conjugateEquiv_cechDifferential_app]
        simp only [precompIsoEquiv, Equiv.coe_fn_mk, Category.assoc, Iso.hom_inv_id_assoc]
        rfl
    rw [augmentedCechComplex_d_eq, augmentedCechComplex_d_eq]
    exact Stacks.CategoryTheory.ExactOnHom.function_exact_of_conjugate
      (cechTermAdjunction S D K a ⦋j⦌) (cechTermAdjunction S D K a ⦋j + 1⦌)
      (cechTermAdjunction S D K a ⦋j + 2⦌) (cechDifferential S D K a j)
      (cechDifferential S D K a (j + 1)) T F hExact

end CategoryTheory.SimplicialSiteSituation.Augmentation

end

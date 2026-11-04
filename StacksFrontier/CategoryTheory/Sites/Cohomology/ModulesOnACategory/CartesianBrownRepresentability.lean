module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentabilityFromSizeBound
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementExists
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GZ0, parts (2), (3) and (4)

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
commutative rings on `C`, and write `QC(O) ⊆ D(O)` for the subcategory of cartesian objects
(Stacks 0GYV). Stacks 0GZ0 makes four assertions about `QC(O)`:

1. it is a strictly full, saturated, triangulated subcategory of `D(O)`, closed under arbitrary
   direct sums;
2. every contravariant cohomological functor `QC(O) ⥤ Ab` taking direct sums to products is
   representable;
3. every exact functor `F : QC(O) ⥤ 𝒟` of triangulated categories taking direct sums to direct
   sums has an exact right adjoint;
4. the inclusion `QC(O) ⥤ D(O)` has an exact right adjoint.

Assertion (1) is Stacks 0GYW, and is proved in the module
`CartesianObjectsTriangulatedSubcategory`. This file proves the other three, as the source proves
them: Stacks 0GYZ produces a cardinal bounding a generating family, and (2) is weak Brown
representability (Stacks 0GYG) applied to that family while (3) is the existence of a right adjoint
from the same family (Stacks 0GYH). Assertion (4) is (3) at the inclusion functor.

## Main results

* `exists_qc_generating_family`: `QC(O)` has a generating family in the sense of Stacks 0GYG,
  indexed by a type in the module universe. This is the unconditional form of Stacks 0GYZ that
  the two Brown representability statements consume.
* `exists_iso_preadditiveYoneda_of_isHomological`: assertion (2).
* `exists_isTriangulated_rightAdjoint_of_preservesCoproducts`: assertion (3).
* `exists_isTriangulated_rightAdjoint_qcι`: assertion (4).

## Implementation notes

Stacks 0GYZ is stated in
`QuasiCoherentEquivalence.exists_cardinal_small_nonzero_map_and_factorization` with its direct sums
formed in `D(O)`, which is how the source states it: `QC(O)` is a strictly full subcategory of
`D(O)` closed under arbitrary direct sums (Stacks 0GYW), so a direct sum of cartesian objects taken
in `D(O)` is their direct sum in `QC(O)`. Weak Brown representability, on the other hand, consumes
a factorization through the direct sums of the category it is applied to.
`exists_cardinal_qc_nonzero_map_and_factorization` moves the statement from the one shape to the
other, along `Limits.PreservesCoproduct.iso`, the isomorphism `QCι(∐ K) ≅ ∐ QCι(K n)` that
expresses that the inclusion preserves countable direct sums — which it does because `QC(O)` is
closed under them, so that the inclusion creates them.

Commutativity of the section rings of `O` is a hypothesis inherited from Stacks 0GYZ: in the
Stacks Project `O` is a sheaf of rings on `C` in the sense of commutative algebra, and the
extension of scalars `M ↦ M ⊗_{O(V)} O(U)` along a restriction map, which the cartesian
condition of Stacks 0GYV is about, does not exist without it.

The three statements are given for an arbitrary
`bc : Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData O`, which generalizes the
source: specializing `bc` to the derived extension of scalars along the restriction maps of `O`
recovers the assertions of the source verbatim. The narrowings that
`Stacks.ModulesOnACategory.CartesianObjects.canonicalBaseChangeData` imposes at that
specialization are recorded with assertion (1).

In assertion (3) the target category `𝒟` is given the same morphism universe as `QC(O)`, the
locally small situation of the source, and "taking direct sums to direct sums" is asked of the
direct sums indexed by types in the module universe — the two universe conventions of
Stacks 0GYH, where they are explained.

## References

* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GYH](https://stacks.math.columbia.edu/tag/0GYH)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-! ### Stacks 0GYZ with the direct sums formed in `QC(O)` -/

/-- **Stacks 0GYZ, with the direct sums of conclusion (2) formed in `QC(O)`.** There is a cardinal
`κ` such that every nonzero cartesian object receives a nonzero morphism from a cartesian object
of size at most `κ`, and every morphism `E ⟶ ⨁_n K_n` of `QC(O)` with `|E| ≤ κ` factors through a
direct sum `⨁_n E_n`, formed in `QC(O)`, of cartesian objects of size at most `κ` mapping to the
summands.

The source states conclusion (2) with the direct sums formed in `D(O)`, which is
`exists_cardinal_small_nonzero_map_and_factorization`; the two agree because the inclusion
`QC(O) ⥤ D(O)` creates countable direct sums, and this lemma transports the statement along the
resulting isomorphism `qcι_sigma_iso`. -/
theorem exists_cardinal_qc_nonzero_map_and_factorization (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x) :
    ∃ κ : Cardinal.{max u v r w},
      (∀ K : QC.{w} bc, ¬ IsZero K.obj →
          ∃ (E : QC.{w} bc) (f : E ⟶ K), f ≠ 0 ∧ derivedObjectSize.{w} O E.obj ≤ κ) ∧
        (∀ (E : QC.{w} bc) (K : ℕ → QC.{w} bc) (α : E ⟶ ∐ K),
          derivedObjectSize.{w} O E.obj ≤ κ →
          ∃ (E' : ℕ → QC.{w} bc) (f : ∀ n, E' n ⟶ K n) (β : E ⟶ ∐ E'),
            (∀ n, derivedObjectSize.{w} O (E' n).obj ≤ κ) ∧
              α = β ≫ Limits.Sigma.map f) := by
  obtain ⟨κ, hnonzero, hfactor⟩ :=
    exists_cardinal_small_nonzero_map_and_factorization.{w} O bc hO
  refine ⟨κ, hnonzero, ?_⟩
  intro E K α hE
  obtain ⟨E', f, β₀, hsz, heq⟩ :=
    hfactor E K ((QCι.{w} bc).map α ≫ (PreservesCoproduct.iso (QCι.{w} bc) K).hom) hE
  refine ⟨E', f,
    ObjectProperty.homMk (β₀ ≫ (PreservesCoproduct.iso (QCι.{w} bc) E').inv), hsz, ?_⟩
  apply (QCι.{w} bc).map_injective
  have key : (PreservesCoproduct.iso (QCι.{w} bc) E').inv ≫
        (QCι.{w} bc).map (Limits.Sigma.map f) =
      (Limits.Sigma.map fun n => (QCι.{w} bc).map (f n)) ≫
        (PreservesCoproduct.iso (QCι.{w} bc) K).inv := by
    refine Limits.Sigma.hom_ext _ _ fun n => ?_
    simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc,
      ι_comp_sigmaComparison, Limits.Sigma.ι_map_assoc, ← Functor.map_comp,
      Limits.Sigma.ι_map]
  have hα : (QCι.{w} bc).map α =
      β₀ ≫ (Limits.Sigma.map fun n => (QCι.{w} bc).map (f n)) ≫
        (PreservesCoproduct.iso (QCι.{w} bc) K).inv := by
    rw [← Category.assoc, ← heq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hmk : (QCι.{w} bc).map
      (ObjectProperty.homMk (β₀ ≫ (PreservesCoproduct.iso (QCι.{w} bc) E').inv) :
        E ⟶ ∐ E') = β₀ ≫ (PreservesCoproduct.iso (QCι.{w} bc) E').inv := rfl
  rw [Functor.map_comp, hmk]
  refine hα.trans ?_
  rw [← key]
  exact (Category.assoc _ _ _).symm

/-! ### A generating family for `QC(O)` -/

/-- **A generating family for `QC(O)`, in the sense of weak Brown representability
(Stacks 0GYG).** There is a family `E : ι → QC(O)` of cartesian objects, indexed by a type in the
module universe, such that every nonzero cartesian object receives a nonzero morphism from some
`E i`, and such that every morphism from some `E i` into a countable direct sum `∐ X` of
cartesian objects factors as a direct sum of morphisms `E (j n) ⟶ X n` precomposed with a
morphism `E i ⟶ ∐ fun n ↦ E (j n)`.

This is Stacks 0GYZ in the shape that Stacks 0GYG consumes: that tag produces a *cardinal*
bounding the size of the objects needed, and the cartesian objects of size at most a given
cardinal are, up to isomorphism, a family indexed by a type in the module universe
(`exists_small_qc_family_of_derivedObjectSize_le`). -/
theorem exists_qc_generating_family (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x) :
    ∃ (ι : Type (max u v r w)) (E : ι → QC.{w} bc),
      (∀ X : QC.{w} bc, ¬ IsZero X → ∃ (i : ι) (f : E i ⟶ X), f ≠ 0) ∧
        ∀ (X : ℕ → QC.{w} bc) (i : ι) (α : E i ⟶ ∐ X),
          ∃ (j : ℕ → ι) (β : ∀ n, E (j n) ⟶ X n) (γ : E i ⟶ ∐ fun n => E (j n)),
            α = γ ≫ Limits.Sigma.map β := by
  classical
  obtain ⟨κ, hnonzero, hfactor⟩ :=
    exists_cardinal_qc_nonzero_map_and_factorization.{w} bc hO
  obtain ⟨ι, E, hsize, hcov⟩ := exists_small_qc_family_of_derivedObjectSize_le.{w} bc κ
  refine ⟨ι, E, ?_, ?_⟩
  · intro X hX
    obtain ⟨E₀, f₀, hf₀, hsz⟩ :=
      hnonzero X (fun hz => hX ((isZero_qc_iff_isZero_obj.{w} bc X).2 hz))
    obtain ⟨i, hi⟩ := hcov E₀ hsz
    refine ⟨i, hi.some.hom ≫ f₀, fun hzero => hf₀ ?_⟩
    calc f₀ = hi.some.inv ≫ hi.some.hom ≫ f₀ := by simp
      _ = 0 := by rw [hzero]; simp
  · intro X i α
    obtain ⟨E', f, β, hE'size, hfac⟩ := hfactor (E i) X α (hsize i)
    have hj : ∀ n : ℕ, ∃ k : ι, Nonempty (E k ≅ E' n) := fun n => hcov (E' n) (hE'size n)
    choose j hjiso using hj
    have ee : ∀ n : ℕ, E (j n) ≅ E' n := fun n => (hjiso n).some
    refine ⟨j, fun n => (ee n).hom ≫ f n, β ≫ Limits.Sigma.map (fun n => (ee n).inv), ?_⟩
    rw [Category.assoc, Limits.Sigma.map_comp_map]
    simp only [Iso.inv_hom_id_assoc]
    exact hfac

/-! ### Stacks 0GZ0(2): representability of cohomological functors -/

/-- **Stacks 0GZ0, assertion (2).** Let `C` be a category, regarded as a site with the chaotic
topology, and let `O` be a presheaf of commutative rings on `C`. Every contravariant
cohomological functor on `QC(O)` which transforms direct sums into products is representable.

This is weak Brown representability (Stacks 0GYG) applied to the generating family of
`exists_qc_generating_family`, which is Stacks 0GYZ. -/
@[stacks 0GZ0 "part (2); part (1) is on the covering set of 0GYW, parts (3) and (4) below"]
theorem exists_iso_preadditiveYoneda_of_isHomological (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    (H : (QC.{w} bc)ᵒᵖ ⥤ AddCommGrpCat.{max u v r w}) [H.IsHomological]
    [∀ J : Type (max u v r w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC.{w} bc, Nonempty (preadditiveYoneda.obj K ≅ H) := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_qc_generating_family.{w} bc hO
  exact exists_iso_preadditiveYoneda_of_isHomological_of_generating.{w} bc E hE hE' H

/-! ### Stacks 0GZ0(3) and 0GZ0(4): existence of exact right adjoints -/

section RightAdjoint

variable {D : Type*} [Category.{max u v r w} D]
  [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Stacks 0GZ0, assertion (3).** Let `C` be a category, regarded as a site with the chaotic
topology, and let `O` be a presheaf of commutative rings on `C`. Every exact functor
`F : QC(O) ⥤ D` of triangulated categories which transforms direct sums into direct sums has a
right adjoint `G`, and `G` is again exact: the adjunction `F ⊣ G` is triangulated for a (unique)
`Functor.CommShift ℤ` structure on `G`.

This is Stacks 0GYH applied to the generating family of `exists_qc_generating_family`, which is
Stacks 0GYZ. -/
@[stacks 0GZ0 "part (3); part (1) is on the covering set of 0GYW, part (2) above, part (4) below"]
theorem exists_isTriangulated_rightAdjoint_of_preservesCoproducts (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x)
    (F : QC.{w} bc ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type (max u v r w), PreservesColimitsOfShape (Discrete α) F] :
    ∃ (G : D ⥤ QC.{w} bc) (adj : F ⊣ G) (_ : G.CommShift ℤ), adj.IsTriangulated := by
  obtain ⟨ι, E, hE, hE'⟩ := exists_qc_generating_family.{w} bc hO
  exact Pretriangulated.exists_isTriangulated_rightAdjoint_of_generating_of_factorsThroughSigma
    F E hE hE'

end RightAdjoint

/-- **Stacks 0GZ0, assertion (4).** Let `C` be a category, regarded as a site with the chaotic
topology, and let `O` be a presheaf of commutative rings on `C`. The inclusion
`QC(O) ⥤ D(O)` has an exact right adjoint.

This is assertion (3) at the inclusion functor: the inclusion is exact and transforms direct sums
into direct sums, `QC(O)` being a triangulated subcategory of `D(O)` closed under arbitrary direct
sums (Stacks 0GYW), so that the inclusion creates them. -/
@[stacks 0GZ0 "part (4); part (1) is on the covering set of 0GYW, parts (2) and (3) above"]
theorem exists_isTriangulated_rightAdjoint_qcι (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x) :
    ∃ (G : DMod.{w} O ⥤ QC.{w} bc) (adj : QCι.{w} bc ⊣ G) (_ : G.CommShift ℤ),
      adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint_of_preservesCoproducts.{w} bc hO (QCι.{w} bc)

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end

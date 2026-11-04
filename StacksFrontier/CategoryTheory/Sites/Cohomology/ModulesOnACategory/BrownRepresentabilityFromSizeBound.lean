module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.BrownRepresentabilityForCartesianObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedObjectSizeSmall
import StacksCore.Tactic.StacksAttribute

/-!
# Brown representability for cartesian objects from a cardinal bound

Let `C` be a category, regarded as a site with the chaotic topology, let `O` be a presheaf of
rings on `C` and let `bc` be derived base-change data for `O`. Stacks 0GZ0(2) says that a
contravariant cohomological functor on `QC(O)` which sends direct sums to products is
representable, and the source deduces it from Stacks 0GYZ together with weak Brown
representability (Stacks 0GYG).

Stacks 0GYZ produces a *cardinal* `κ` with two properties, while Stacks 0GYG consumes an
*indexed family* of objects.
  `exists_small_qc_family_of_derivedObjectSize_le` bridges
the two: the cartesian objects of size at most `κ` are, up to isomorphism, the members of a
family indexed by a type in the module universe. That is the content of
`StacksDraft.Ch21.Sec43.DerivedObjectSizeSmall`, specialized to `QC(O)` using the strict
fullness of `QC(O)` (Stacks 0GYW).

`exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound` is the resulting form of
Stacks 0GZ0(2): it takes exactly the two conclusions of Stacks 0GYZ as hypotheses and produces
the representing object. Combined with a proof of Stacks 0GYZ it gives the unconditional
statement.

## Main results

* `exists_small_qc_family_of_derivedObjectSize_le`: the cartesian objects of size at
  most `κ` form, up to isomorphism, a family indexed by a type in the module universe.
* `exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound`: Stacks 0GZ0(2) from
  the cardinal bound of Stacks 0GYZ.

## Implementation notes

The two hypotheses are stated as the source states the two conclusions of Stacks 0GYZ: a
nonzero cartesian object receives a nonzero map from one of size at most `κ`, and a map from an
object of size at most `κ` into a countable direct sum factors through a direct sum of objects
of size at most `κ` mapping to the summands. The factorization is phrased with `Limits.Sigma.map`
on the canonical coproducts, which is the shape `Stacks 0GYG` consumes; a formulation over an
arbitrary coproduct cocone implies this one by instantiating the cocone at the canonical
coproduct.

The size of a cartesian object means the size of the underlying object of `D(O)`, which is what
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedObjectSize` measures; `QC(O)` is a full
  subcategory, so no separate notion is
needed. Vanishing may equally be read in `QC(O)` or in `D(O)`:
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isZero_qc_iff_isZero_obj` identifies the two,
  because the inclusion is fully
faithful and preserves zero morphisms.

The statement is given for an arbitrary `bc :
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.BaseChangeData O`, which generalizes
the source: specializing `bc` to the derived extension of scalars along the restriction maps of
`O` recovers the assertion of the source verbatim.

## References

* [Stacks Project, Tag 0GZ0](https://stacks.math.columbia.edu/tag/0GZ0)
* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYG](https://stacks.math.columbia.edu/tag/0GYG)
* [Stacks Project, Tag 0GYW](https://stacks.math.columbia.edu/tag/0GYW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated.Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- A cartesian object is zero exactly when the underlying object of `D(O)` is zero: the
inclusion of a full subcategory is faithful and preserves zero morphisms, so it detects and
preserves the identity being zero. -/
lemma isZero_qc_iff_isZero_obj (bc : BaseChangeData.{w} O) (X : QC.{w} bc) :
    IsZero X ↔ IsZero X.obj := by
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero]
  refine ⟨fun h => by simpa using congrArg (ObjectProperty.ι (fun K => IsQC.{w} bc K)).map h,
    fun h => (ObjectProperty.ι (fun K => IsQC.{w} bc K)).map_injective (by simpa using h)⟩

/-- **The cartesian objects of bounded size form a small family up to isomorphism.** The objects
of `D(O)` of size at most `κ` do, by
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_small_family_of_derivedObjectSize_le`;
  keeping those that are cartesian keeps
the index type in the module universe, and every cartesian object of size at most `κ` is
isomorphic to one of them because `QC(O)` is strictly full (Stacks 0GYW). -/
theorem exists_small_qc_family_of_derivedObjectSize_le (bc : BaseChangeData.{w} O)
    (κ : Cardinal.{max u v r w}) :
    ∃ (ι : Type (max u v r w)) (E : ι → QC.{w} bc),
      (∀ i, derivedObjectSize.{w} O (E i).obj ≤ κ) ∧
        ∀ K : QC.{w} bc, derivedObjectSize.{w} O K.obj ≤ κ → ∃ i, Nonempty (E i ≅ K) := by
  obtain ⟨ι₀, E₀, hsize₀, hcov₀⟩ := exists_small_family_of_derivedObjectSize_le.{w} O κ
  refine ⟨{i : ι₀ // IsQC.{w} bc (E₀ i)}, fun i => ⟨E₀ i.1, i.2⟩, fun i => hsize₀ i.1, ?_⟩
  intro K hK
  obtain ⟨i, hi⟩ := hcov₀ K.obj hK
  exact ⟨⟨i, ObjectProperty.prop_of_iso (fun L => IsQC.{w} bc L) hi.some.symm K.property⟩,
    ⟨ObjectProperty.isoMk (fun L => IsQC.{w} bc L) hi.some⟩⟩

/-- **Stacks 0GZ0(2) from the cardinal bound of Stacks 0GYZ.** Suppose given a cardinal `κ` such
that every nonzero cartesian object receives a nonzero morphism from a cartesian object of size
at most `κ`, and such that every morphism from a cartesian object of size at most `κ` into a
countable direct sum of cartesian objects factors through a direct sum of cartesian objects of
size at most `κ` mapping to the summands. Then every contravariant cohomological functor on
`QC(O)` which transforms direct sums into products is representable.

These two hypotheses are the two conclusions of Stacks 0GYZ. The proof turns them into the
generating family that weak Brown representability
(`exists_iso_preadditiveYoneda_of_isHomological_of_generating`, Stacks 0GYG) asks
for, using the essential smallness of the cartesian objects of size at most `κ`. -/
theorem exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound
    (bc : BaseChangeData.{w} O) (κ : Cardinal.{max u v r w})
    (hnonzero : ∀ K : QC.{w} bc, ¬ IsZero K.obj →
      ∃ (E : QC.{w} bc) (f : E ⟶ K), f ≠ 0 ∧ derivedObjectSize.{w} O E.obj ≤ κ)
    (hfactor : ∀ (E : QC.{w} bc) (K : ℕ → QC.{w} bc) (α : E ⟶ ∐ K),
      derivedObjectSize.{w} O E.obj ≤ κ →
      ∃ (E' : ℕ → QC.{w} bc) (f : ∀ n, E' n ⟶ K n) (β : E ⟶ ∐ E'),
        (∀ n, derivedObjectSize.{w} O (E' n).obj ≤ κ) ∧ α = β ≫ Limits.Sigma.map f)
    (H : (QC.{w} bc)ᵒᵖ ⥤ AddCommGrpCat.{max u v r w}) [H.IsHomological]
    [∀ J : Type (max u v r w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC.{w} bc, Nonempty (preadditiveYoneda.obj K ≅ H) := by
  classical
  obtain ⟨ι, E, hsize, hcov⟩ :=
    exists_small_qc_family_of_derivedObjectSize_le.{w} bc κ
  refine exists_iso_preadditiveYoneda_of_isHomological_of_generating.{w} bc E ?_ ?_ H
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

/-- **Stacks 0GZ0(2) from Stacks 0GYZ, with the direct sums taken as arbitrary coproduct
cocones.** This is the form in which Stacks 0GYZ(2) is naturally stated — a direct sum is a
cocone together with its universal property, so the statement does not depend on a chosen
coproduct construction — and it implies the canonical-coproduct form
`exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound` by instantiating the
target cocone at `∐ K` and transporting the produced cocone to `∐ E'` along the isomorphism of
colimits. -/
theorem exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound_cofan
    (bc : BaseChangeData.{w} O) (κ : Cardinal.{max u v r w})
    (hnonzero : ∀ K : QC.{w} bc, ¬ IsZero K.obj →
      ∃ (E : QC.{w} bc) (f : E ⟶ K), f ≠ 0 ∧ derivedObjectSize.{w} O E.obj ≤ κ)
    (hfactor : ∀ (E : QC.{w} bc) (K : ℕ → QC.{w} bc) (t : Cofan K) (_ : IsColimit t)
        (α : E ⟶ t.pt), derivedObjectSize.{w} O E.obj ≤ κ →
      ∃ (E' : ℕ → QC.{w} bc) (f : ∀ n, E' n ⟶ K n) (t' : Cofan E') (_ : IsColimit t')
        (β : E ⟶ t'.pt) (g : t'.pt ⟶ t.pt),
        (∀ n, derivedObjectSize.{w} O (E' n).obj ≤ κ) ∧
          (∀ n, t'.ι.app ⟨n⟩ ≫ g = f n ≫ t.ι.app ⟨n⟩) ∧ β ≫ g = α)
    (H : (QC.{w} bc)ᵒᵖ ⥤ AddCommGrpCat.{max u v r w}) [H.IsHomological]
    [∀ J : Type (max u v r w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC.{w} bc, Nonempty (preadditiveYoneda.obj K ≅ H) := by
  refine exists_iso_preadditiveYoneda_of_isHomological_of_sizeBound.{w} bc κ hnonzero ?_ H
  intro E K α hE
  obtain ⟨E', f, t', ht', β, g, hsz, hcomp, hβ⟩ :=
    hfactor E K (Cofan.mk (∐ K) (Limits.Sigma.ι K)) (coproductIsCoproduct K) α hE
  refine ⟨E', f, β ≫ (ht'.coconePointUniqueUpToIso (coproductIsCoproduct E')).hom, hsz, ?_⟩
  have hg : (ht'.coconePointUniqueUpToIso (coproductIsCoproduct E')).hom ≫
      Limits.Sigma.map f = g := by
    refine Cofan.IsColimit.hom_ext ht' _ _ (fun n => ?_)
    have h₁ := ht'.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct E') ⟨n⟩
    have h₂ := hcomp n
    simp only [Cofan.inj, Cofan.mk_ι_app] at h₁ h₂ ⊢
    rw [← Category.assoc, h₁, Limits.Sigma.ι_map, h₂]
  rw [Category.assoc, hg, hβ]

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end

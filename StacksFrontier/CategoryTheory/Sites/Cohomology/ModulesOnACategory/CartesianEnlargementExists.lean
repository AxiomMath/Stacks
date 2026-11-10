module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementStep
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.SmallFactorizationThroughSums
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0GYZ

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf of
commutative rings on `C`. Write `QC(O) ⊆ D(O)` for the subcategory of cartesian objects
(Stacks 0GYV) and `|K|` for the size of an object of `D(O)`. Stacks 0GYZ asserts the existence of
a single cardinal `κ` with two properties:

1. every nonzero object `K` of `QC(O)` receives a nonzero morphism `E ⟶ K` of `QC(O)` with
   `|E| ≤ κ`;
2. every morphism `α : E ⟶ ⨁_n K_n` of `QC(O)` with `|E| ≤ κ` factors through a morphism
   `⨁_n E_n ⟶ ⨁_n K_n` coming from morphisms `E_n ⟶ K_n` of `QC(O)` with `|E_n| ≤ κ`.

This file proves both, as `exists_cardinal_small_nonzero_map_and_factorization`.

The key claim of the source's proof — that a small subcomplex of a complex representing a
cartesian object is contained in a small subcomplex which again represents a cartesian object —
is `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.HasCartesianEnlargement`, and it is proved
here as `exists_hasCartesianEnlargement` by assembling two results that were already available:
`exists_iterated_enlargement_containing_sections` runs the countable iteration and forms the
union, given a rule prescribing which sections of `F^•` must be absorbed at each stage, and
`exists_sections_rule_isIso_comparison_at_union` supplies that rule *at one morphism* of `C`
together with the guarantee that absorbing it repeatedly makes the union cartesian at that
morphism. The rule fed to the iteration is the union, over all morphisms of `C`, of the
per-morphism rules.

Granting the claim, conclusion (1) is
`exists_nonzero_map_of_size_le_of_cartesianEnlargement`. Conclusion (2) is deduced from its
analogue for `D(O)`, `exists_factorization_of_sum_of_derivedObjectSize_le`, by replacing each
summand produced there by a cartesian object of the same size bound: that replacement is
`exists_small_cartesian_factorization`, which factors an arbitrary morphism from a small object
into a cartesian object through a small *cartesian* object, by shrinking a representative of the
source (Stacks 0GYY), taking the image subcomplex of the resulting map of complexes, and
enlarging that image to a cartesian subcomplex.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_hasCartesianEnlargement`: the
  enlargement claim of the source's proof, for every sufficiently large cardinal.
* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_small_cartesian_factorization`: a
  morphism from a small object into a cartesian object factors through a small cartesian object.
* `exists_cardinal_small_nonzero_map_and_factorization`, in the same namespace: Stacks 0GYZ, both
  of its conclusions, for one cardinal.

## Implementation notes

All three statements are given in the form "there is a cardinal `κ₀` such that every `κ` above it
has the property", rather than "there is a `κ` with the property". The two are equivalent for a
single conclusion, but a property whose hypothesis and conclusion both read `≤ κ` is monotone in
neither direction, so the weaker form cannot be used to put two such properties at one cardinal —
which is what Stacks 0GYZ asserts.

The family of sections prescribed at a stage of the enlargement is indexed by the objects of `C`,
while the per-morphism rule returns two families, one over the target and one over the source of
the morphism. The two are glued by indexing the morphisms of `C` as triples `(Z, W, f : Z ⟶ W)`
and reading the morphism of `Cᵒᵖ` as `f.op : op W ⟶ op Z`: then the family over `V = op W` is a
family of sections over the object `W` of `C` on the nose, and likewise for `U = op Z`, so no
section is ever transported along an equality of objects of `Cᵒᵖ`.

The supremum of the per-morphism cardinals is taken over
`ULift (Σ Z : C, Σ W : C, (Z ⟶ W))`, lifted into the module universe, so that
`Cardinal.bddAbove_of_small` applies to it directly — the same device as in
`singleGeneratorBound`. The cardinality of that index type also enters the bound, since the
prescribed family at a stage is a union over the morphisms of `C` of families each small.

Conclusion (2) is stated with the coproducts formed in `D(O)`, the objects and the morphisms
between them being cartesian. That is the source's statement: `QC(O)` is a strictly full
subcategory of `D(O)` closed under arbitrary direct sums (Stacks 0GYW), so a coproduct of
cartesian objects taken in `D(O)` is their coproduct in `QC(O)`, and a morphism of `QC(O)` is
nothing but a morphism of `D(O)` between cartesian objects.

Commutativity of the section rings of `O` is a hypothesis of the source: in the Stacks Project
`O` is a sheaf of rings on `C` in the sense of commutative algebra, and extension of scalars
`M ↦ M ⊗_{O(V)} O(U)` along a restriction map does not exist without it.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
* [Stacks Project, Tag 0GYX](https://stacks.math.columbia.edu/tag/0GYX)
* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-! ### The enlargement claim of the source's proof -/

/-- **The enlargement claim of Stacks 0GYZ.** Let `O` be a presheaf of commutative rings on `C`.
There is a cardinal `κ₀` such that for every cardinal `κ` which is infinite and at least `κ₀`,
every subcomplex with at most `κ` sections of a complex representing a cartesian object is
contained in a subcomplex which again represents a cartesian object and still has at most `κ`
sections.

The rule prescribing the sections to absorb at a stage is the union over all morphisms of `C` of
the per-morphism rules of `exists_sections_rule_isIso_comparison_at_union`; the iteration and the
union are `exists_iterated_enlargement_containing_sections`. -/
theorem exists_hasCartesianEnlargement (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x) :
    ∃ κ₀ : Cardinal.{max u v r w}, ∀ κ : Cardinal.{max u v r w},
      max Cardinal.aleph0 κ₀ ≤ κ → HasCartesianEnlargement.{w} O bc κ := by
  classical
  obtain ⟨kap0, hkap0⟩ := exists_iterated_enlargement_containing_sections.{w} O
  choose kapm hkapm using fun
      (q : ULift.{max u v r w, max u v} (Σ Z : C, Σ W : C, (Z ⟶ W))) =>
    exists_sections_rule_isIso_comparison_at_union.{w} bc (Quiver.Hom.op q.down.2.2)
      (hO _) (hO _)
  set mu : Cardinal.{max u v r w} :=
    Cardinal.mk (ULift.{max u v r w, max u v} (Σ Z : C, Σ W : C, (Z ⟶ W))) with hmu
  set kapsup : Cardinal.{max u v r w} := ⨆ q, kapm q with hkapsup
  have hkapm_le : ∀ q, kapm q ≤ kapsup := fun q =>
    le_ciSup (f := kapm) Cardinal.bddAbove_of_small q
  refine ⟨max kap0 (max kapsup mu), fun kappa hkappa => ?_⟩
  have hal : Cardinal.aleph0 ≤ kappa := (le_max_left _ _).trans hkappa
  have hkap0_le : kap0 ≤ kappa :=
    (le_max_of_le_right (le_max_left _ _)).trans hkappa
  have hkapsup_le : kapsup ≤ kappa :=
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))).trans hkappa
  have hmu_le : mu ≤ kappa :=
    (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))).trans hkappa
  intro F hFQC S g hg hS
  choose Ms Ns hMs hNs hmain using fun
      (q : ULift.{max u v r w, max u v} (Σ Z : C, Σ W : C, (Z ⟶ W))) =>
    hkapm q F (hFQC (Quiver.Hom.op q.down.2.2))
  -- the rule fed to the iteration: all the per-morphism families at once
  set Omega : ∀ G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ, (G ⟶ F) →
      ∀ (i : ℤ) (Y : C), Set ((F.X i).obj (op Y)) :=
    fun G g' i Y =>
      {x | (∃ (Z : C) (f : Z ⟶ Y), x ∈ Ms ⟨⟨Z, Y, f⟩⟩ G g' i) ∨
        (∃ (W : C) (f : Y ⟶ W), x ∈ Ns ⟨⟨Y, W, f⟩⟩ G g' i)} with hOmega
  have hOmegaSize : ∀ (G : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (g' : G ⟶ F),
      complexSectionSize.{w} O G ≤ kappa →
        presheafSectionFamilySize.{w} (Omega G g') ≤ kappa := by
    intro G g' hGsize
    have hbig : ∀ P : ULift.{max u v r w, max u v} (Σ Z : C, Σ W : C, (Z ⟶ W)) →
        Type (max u v r w), (∀ q, Cardinal.mk (P q) ≤ kappa) →
          Cardinal.mk (Σ q, P q) ≤ kappa := by
      intro P hP
      rw [Cardinal.mk_sigma]
      refine le_trans (Cardinal.sum_le_sum _ (fun _ => kappa) hP) ?_
      rw [Cardinal.sum_const']
      exact Cardinal.mul_le_of_le hal hmu_le le_rfl
    have hleft := hbig (fun q => Σ i : ℤ, {x // x ∈ Ms q G g' i}) fun q =>
      (hMs q G g').trans (max_le ((hkapm_le q).trans hkapsup_le) hGsize)
    have hright := hbig (fun q => Σ i : ℤ, {x // x ∈ Ns q G g' i}) fun q =>
      (hNs q G g').trans (max_le ((hkapm_le q).trans hkapsup_le) hGsize)
    refine le_trans (Cardinal.mk_le_of_surjective
      (f := fun t : (Σ q : ULift.{max u v r w, max u v} (Σ Z : C, Σ W : C, (Z ⟶ W)),
            Σ i : ℤ, {x // x ∈ Ms q G g' i}) ⊕
          (Σ q : ULift.{max u v r w, max u v} (Σ Z : C, Σ W : C, (Z ⟶ W)),
            Σ i : ℤ, {x // x ∈ Ns q G g' i}) =>
        (match t with
          | Sum.inl ⟨q, i, x⟩ =>
              ⟨i, q.down.2.1, x.1, Or.inl ⟨q.down.1, q.down.2.2, x.2⟩⟩
          | Sum.inr ⟨q, i, x⟩ =>
              ⟨i, q.down.1, x.1, Or.inr ⟨q.down.2.1, q.down.2.2, x.2⟩⟩ :
          Σ i : ℤ, Σ Y : C, {x // x ∈ Omega G g' i Y})) ?_) ?_
    · rintro ⟨i, Y, x, hx⟩
      rcases hx with ⟨Z, f, hxf⟩ | ⟨W, f, hxf⟩
      · exact ⟨Sum.inl ⟨⟨⟨Z, Y, f⟩⟩, i, x, hxf⟩, rfl⟩
      · exact ⟨Sum.inr ⟨⟨⟨Y, W, f⟩⟩, i, x, hxf⟩, rfl⟩
    · rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact (Cardinal.add_le_max _ _).trans (max_le (max_le hleft hright) hal)
  obtain ⟨H, h, kS, G, γ, pp, k, -, hhmono, hkS, hHsize, hγ, hp, hk, hcont, hexh⟩ :=
    hkap0 F (Λ := kappa) (max_le hal hkap0_le) Omega hOmegaSize S g hg hS
  refine ⟨H, h, kS, hhmono, hkS, ?_, hHsize⟩
  intro U' V' a
  exact hmain ⟨⟨U'.unop, V'.unop, a.unop⟩⟩ H h G γ pp k hhmono hγ hp hk hexh
    (fun n i x hx => hcont n i V'.unop x (Or.inl ⟨U'.unop, a.unop, hx⟩))
    (fun n i x hx => hcont n i U'.unop x (Or.inr ⟨V'.unop, a.unop, hx⟩))

/-! ### Factoring a map into a cartesian object through a small cartesian object -/

/-- **A map from a small object into a cartesian object factors through a small cartesian
object.** Let `κ` be a cardinal with the enlargement property, infinite and above a cardinal
depending only on `C` and `O`. Then every morphism `φ : A ⟶ B` of `D(O)` with `B` cartesian and
`|A| ≤ κ` factors as `A ⟶ A' ⟶ B` with `A'` cartesian and `|A'| ≤ κ`.

A representative `F^•` of `B` is chosen, `φ` is presented as a right fraction, and Stacks 0GYY
shrinks the source of that fraction to a quasi-isomorphic subcomplex `ℰ^•` with at most `κ`
sections. The image subcomplex of `ℰ^• ⟶ F^•` is then no larger, and the enlargement property
turns it into a cartesian subcomplex of `F^•`, through which `φ` factors by construction. -/
theorem exists_small_cartesian_factorization (bc : BaseChangeData.{w} O) :
    ∃ κ₀ : Cardinal.{max u v r w}, ∀ κ : Cardinal.{max u v r w}, κ₀ ≤ κ →
      HasCartesianEnlargement.{w} O bc κ →
      ∀ (A B : DMod.{w} O) (φ : A ⟶ B), IsQC.{w} bc B →
        derivedObjectSize.{w} O A ≤ κ →
        ∃ (A' : DMod.{w} O) (a : A ⟶ A') (b : A' ⟶ B),
          IsQC.{w} bc A' ∧ derivedObjectSize.{w} O A' ≤ κ ∧ φ = a ≫ b := by
  classical
  obtain ⟨kqi, hkqi⟩ :=
    Stacks.ModulesOnACategory.exists_small_quasiIso_subcomplex_presheaf.{w}
      (chaoticRingSheaf.{u, v, r} O)
  have hkqi' : ∀ (F : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ)
      (L : DMod.{w} O), Nonempty (DerivedCategory.Q.obj F ≅ L) →
      ∃ (H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ) (h : H ⟶ F),
        Mono h ∧ QuasiIso h ∧
          complexSectionSize.{w} O H ≤ max kqi (derivedObjectSize.{w} O L) := hkqi
  clear hkqi
  refine ⟨kqi, fun kappa hkappa henl A B φ hB hA => ?_⟩
  obtain ⟨F, hFB, -⟩ := exists_representative_of_derivedObjectSize.{w} O B
  set e : DerivedCategory.Q.obj F ≅ B := hFB.some with he
  have hFQC : IsQC.{w} bc (DerivedCategory.Q.obj F) :=
    ObjectProperty.prop_of_iso (fun L => IsQC.{w} bc L) e.symm hB
  obtain ⟨A0, hA0, -⟩ := exists_representative_of_derivedObjectSize.{w} O A
  set eA : DerivedCategory.Q.obj A0 ≅ A := hA0.some with heA
  obtain ⟨E1, sq, hsq, gg, hfac⟩ := DerivedCategory.right_fac (eA.hom ≫ φ ≫ e.inv)
  have : IsIso (DerivedCategory.Q.map sq) := hsq
  obtain ⟨Ec, jc, hjmono, hjqi, hjsize⟩ :=
    hkqi' E1 A ⟨asIso (DerivedCategory.Q.map sq) ≪≫ eA⟩
  have : IsIso (DerivedCategory.Q.map jc) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hjqi
  have hsize : complexSectionSize.{w} O Ec ≤ kappa := hjsize.trans (max_le hkappa hA)
  obtain ⟨kk, -, hkkfac⟩ := exists_epi_factor_imageComplexSubmodule.{w} (jc ≫ gg)
  obtain ⟨Hh, hh, kkk, hhmono, hkkk, hHQC, hHsize⟩ :=
    henl F hFQC (imageComplexSubmodule.{w} (jc ≫ gg)).toComplex
      (imageComplexSubmodule.{w} (jc ≫ gg)).ι inferInstance
      ((complexSectionSize_imageComplexSubmodule_le.{w} (jc ≫ gg)).trans hsize)
  set theta : DerivedCategory.Q.obj Ec ≅ A :=
    asIso (DerivedCategory.Q.map jc) ≪≫ asIso (DerivedCategory.Q.map sq) ≪≫ eA with htheta
  refine ⟨DerivedCategory.Q.obj Hh, theta.inv ≫ DerivedCategory.Q.map (kk ≫ kkk),
    DerivedCategory.Q.map hh ≫ e.hom, hHQC,
    (derivedObjectSize_le_complexSectionSize.{w} O Hh).trans hHsize, ?_⟩
  have h1 : eA.hom ≫ φ =
      inv (DerivedCategory.Q.map sq) ≫ DerivedCategory.Q.map gg ≫ e.hom := by
    rw [← Category.assoc, ← hfac, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  have hthetaφ : theta.hom ≫ φ = DerivedCategory.Q.map (jc ≫ gg) ≫ e.hom := by
    rw [htheta, Iso.trans_hom, Iso.trans_hom, asIso_hom, asIso_hom,
      DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rw [h1]
    simp
  have hcomp : kk ≫ kkk ≫ hh = jc ≫ gg := by
    rw [hkkk, hkkfac]
  rw [Category.assoc, ← Category.assoc (DerivedCategory.Q.map (kk ≫ kkk)),
    ← DerivedCategory.Q.map_comp, Category.assoc, hcomp, ← hthetaφ, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-! ### Stacks 0GYZ -/

/-- **Stacks 0GYZ.** Let `C` be a category, regarded as a site with the chaotic topology, and let
`O` be a presheaf of commutative rings on `C`. There is a cardinal `κ` such that

1. every nonzero object `K` of `QC(O)` receives a nonzero morphism from an object of `QC(O)` of
   size at most `κ`, and
2. every morphism `α : E ⟶ ⨁_n K_n` of `QC(O)` with `|E| ≤ κ` factors through a morphism
   `⨁_n E_n ⟶ ⨁_n K_n` induced by morphisms `E_n ⟶ K_n` of `QC(O)` with `|E_n| ≤ κ`.

Conclusion (1) is `exists_nonzero_map_of_size_le_of_cartesianEnlargement` fed with
`exists_hasCartesianEnlargement`. Conclusion (2) comes from its analogue for `D(O)`,
`exists_factorization_of_sum_of_derivedObjectSize_le`, by replacing each of the summands it
produces with a cartesian object of the same size bound, which is
`exists_small_cartesian_factorization`. -/
@[stacks 0GYZ "both conclusions, at one cardinal, for a presheaf of commutative rings"]
theorem exists_cardinal_small_nonzero_map_and_factorization (bc : BaseChangeData.{w} O)
    (hO : ∀ (V : Cᵒᵖ) (x y : O.obj V), x * y = y * x) :
    ∃ κ : Cardinal.{max u v r w},
      (∀ K : QC.{w} bc, ¬ IsZero K.obj →
          ∃ (E : QC.{w} bc) (f : E ⟶ K), f ≠ 0 ∧ derivedObjectSize.{w} O E.obj ≤ κ) ∧
        (∀ (E : QC.{w} bc) (K : ℕ → QC.{w} bc) (α : E.obj ⟶ ∐ fun n => (K n).obj),
          derivedObjectSize.{w} O E.obj ≤ κ →
          ∃ (E' : ℕ → QC.{w} bc) (f : ∀ n, E' n ⟶ K n)
            (β : E.obj ⟶ ∐ fun n => (E' n).obj),
            (∀ n, derivedObjectSize.{w} O (E' n).obj ≤ κ) ∧
              α = β ≫ Limits.Sigma.map fun n => (QCι.{w} bc).map (f n)) := by
  classical
  obtain ⟨kenl, henl0⟩ := exists_hasCartesianEnlargement.{w} O bc hO
  obtain ⟨kcart, hcart⟩ := exists_small_cartesian_factorization.{w} O bc
  obtain ⟨ksum, hsum⟩ := exists_factorization_of_sum_of_derivedObjectSize_le.{w} O
  set kappa : Cardinal.{max u v r w} :=
    max (max Cardinal.aleph0 kenl)
      (max kcart (max ksum (singleGeneratorBound.{w} O))) with hkappa
  have henl : HasCartesianEnlargement.{w} O bc kappa := henl0 kappa (le_max_left _ _)
  have hgen : singleGeneratorBound.{w} O ≤ kappa :=
    le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hcartle : kcart ≤ kappa := le_max_of_le_right (le_max_left _ _)
  have hsumle : ksum ≤ kappa := le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  refine ⟨kappa, fun K hK => exists_nonzero_map_of_size_le_of_cartesianEnlargement.{w} O bc
    hgen henl K hK, ?_⟩
  intro E K α hE
  obtain ⟨E₀, f₀, β₀, hsize₀, heq₀⟩ :=
    hsum kappa hsumle E.obj (fun n => (K n).obj) α hE
  choose A' aa bb hA'QC hA'size hA'fac using fun n =>
    hcart kappa hcartle henl (E₀ n) ((K n).obj) (f₀ n) (K n).property (hsize₀ n)
  have hmap : (Limits.Sigma.map aa) ≫ (Limits.Sigma.map bb) = Limits.Sigma.map f₀ := by
    refine Limits.Sigma.hom_ext _ _ fun n => ?_
    simp only [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_map, hA'fac n, Category.assoc]
  refine ⟨fun n => ⟨A' n, hA'QC n⟩, fun n => ObjectProperty.homMk (bb n),
    β₀ ≫ Limits.Sigma.map aa, hA'size, ?_⟩
  change α = (β₀ ≫ Limits.Sigma.map aa) ≫ Limits.Sigma.map bb
  rw [Category.assoc, hmap]
  exact heq₀

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimeKilledTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.Reduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleExhaustion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.OpenClosedSequence

/-!
# Noetherian induction for the eight assertions of Tag 03SC

The proof of Stacks Tag 03SC reduces, for a constructible sheaf `F` of `F_ℓ`-vector spaces on a
reduced curve `X`, to a dense open `U = U_1 ⊔ ⋯ ⊔ U_n` with `F|_U` finite locally constant, then
to `j_! (F|_U)` by Tag 0GJA, and splits `j_!(F|_U)` over the components `U_i`, each of which is
Tag 03SD.

This file organizes the same argument as a Noetherian induction, one component at a time. For a
generic point `η` of an irreducible component of `X` take an open `U ∋ η` on which the eight
assertions hold for `j_! j⁻¹ F` (this is where Tag 03SD enters), and let `i : Z → X` be the closed
complement of `U`. In the short exact sequence `0 → j_! j⁻¹ F → F → i_* i⁻¹ F → 0` of Tag 095L,
the eight assertions hold for `i_* i⁻¹ F` by Tag 0A5D as soon as they hold for `i⁻¹ F` on `Z`,
which is the induction hypothesis because `Z` is a proper closed subset; Tag 0A5C then gives them
for `F`. The splitting of `j_!(F|_U)` over the components of `U` is not needed.

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_genericStep`: the eight assertions for every
  constructible sheaf killed by a prime on a separated scheme of finite type and dimension at most
  one over an algebraically closed field, given the generic step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Topology TopologicalSpace

universe u

namespace Stacks.EtaleCohomology

namespace TorsionCurveAssertions

/-- A sheaf killed by `ℓ` stays killed by `ℓ` under an additive functor. -/
theorem nsmul_id_map_eq_zero {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] (Φ : C ⥤ D) [Φ.Additive] {ℓ : ℕ} {G : C} (h : ℓ • 𝟙 G = 0) :
    ℓ • 𝟙 (Φ.obj G) = 0 := by
  rw [← Φ.map_id, ← Functor.map_nsmul, h, Φ.map_zero]

/-- An abelian sheaf on the small étale site of the empty scheme is zero. -/
theorem isZero_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z]
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) : IsZero G :=
  isZero_of_forall_isZero_sections.{u, u + 1} G fun V ↦
    isZero_sections_of_isEmpty.{u, u + 1} G V ⟨fun x ↦ IsEmpty.elim ‹_› (V.hom.base x)⟩

/-- A nonempty Noetherian scheme has a point whose closure is an irreducible component. -/
theorem exists_closure_mem_irreducibleComponents (Z : Scheme.{u}) [Nonempty Z] :
    ∃ η : Z, closure {η} ∈ irreducibleComponents Z := by
  obtain ⟨x⟩ := ‹Nonempty Z›
  obtain ⟨C, hC, -⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
  refine ⟨hC.1.genericPoint, ?_⟩
  have h := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents C hC).closure_eq] at h
  rw [h.def]
  exact hC

/-- A scheme of finite type over a field is Noetherian. -/
theorem isNoetherian_of_finiteType {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X := by
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

/-- An open set is strictly smaller than the complement of a closed set disjoint from it, as soon
as some point lies outside both. -/
theorem lt_compl_of_subset_compl {X : Type*} [TopologicalSpace X] (O : Opens X) {C : Set X}
    (hC : IsClosed C) (hCO : C ⊆ (O : Set X)ᶜ) {x : X} (hxO : x ∈ (O : Set X)ᶜ) (hxC : x ∉ C) :
    O < ⟨Cᶜ, hC.isOpen_compl⟩ :=
  lt_of_le_of_ne (fun _ hy hyC ↦ hCO hyC hy) fun h ↦ hxO (by rw [h]; exact hxC)

/-- Inverse image along a closed immersion preserves constructibility and being killed by `ℓ`. -/
private theorem inverseImage_constructible_and_nsmul_eq_zero {Y X : Scheme.{u}} (r : Y ⟶ X)
    [IsClosedImmersion r] {ℓ : ℕ} {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (hG : IsConstructibleSmallEtaleSheaf G) (hℓG : ℓ • 𝟙 G = 0) :
    IsConstructibleSmallEtaleSheaf ((etaleAbelianInverseImage.{u, u + 1} r).obj G) ∧
      ℓ • 𝟙 ((etaleAbelianInverseImage.{u, u + 1} r).obj G) = 0 :=
  ⟨IsConstructibleSmallEtaleSheaf.inverseImage_of_mono r hG,
    nsmul_id_map_eq_zero (etaleAbelianInverseImage.{u, u + 1} r) hℓG⟩

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **The Noetherian induction behind Tag 03SC**, inside a fixed Noetherian ambient scheme `X₀`:
by well-founded induction on the open complement `O` of a closed subscheme. -/
theorem of_genericStep_aux
    (hstep : ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) [IsSeparated g] [LocallyOfFiniteType g]
      [QuasiCompact g] [IsReduced Y]
      [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})],
      topologicalKrullDim Y ≤ 1 → ∀ ℓ : ℕ, ℓ.Prime →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}, IsConstructibleSmallEtaleSheaf G →
        ℓ • 𝟙 G = 0 → ∀ η : Y, closure {η} ∈ irreducibleComponents Y →
        ∃ (V : Scheme.{u}) (jV : V ⟶ Y) (_ : IsOpenImmersion jV), η ∈ Set.range jV.base ∧
          TorsionCurveAssertions g
            ((extensionByZero.{u, u + 1} jV).obj ((etaleRestriction.{u, u + 1} jV).obj G)))
    (X₀ : Scheme.{u}) [NoetherianSpace X₀] (O : X₀.Opens) :
    ∀ (Z : Scheme.{u}) (ι : Z ⟶ X₀) [IsClosedImmersion ι], Set.range ι.base = (O : Set X₀)ᶜ →
      ∀ (g : Z ⟶ Spec (.of k)) [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
        [HasExt.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})],
        topologicalKrullDim Z ≤ 1 → ∀ ℓ : ℕ, ℓ.Prime →
        ∀ G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}, IsConstructibleSmallEtaleSheaf G →
          ℓ • 𝟙 G = 0 → TorsionCurveAssertions g G := by
  induction O using WellFoundedGT.induction with
  | _ O ih =>
  intro Z ι _ hι g _ _ _ _ hdim ℓ hℓ G hG hℓG
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · exact of_isZero g (isZero_of_isEmpty G)
  -- pass to the reduction
  have := hasExt_of_enoughInjectives.{u + 1}
    (Sheaf Z.reduction.smallEtaleTopology AddCommGrpCat.{u + 1})
  refine of_reduction g G ?_
  set Y := Z.reduction
  set r := Z.reductionι
  set gY := r ≫ g
  have hdimY : topologicalKrullDim Y ≤ 1 :=
    (r.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim
  obtain ⟨hGY, hℓGY⟩ := inverseImage_constructible_and_nsmul_eq_zero r hG hℓG
  set GY := (etaleAbelianInverseImage.{u, u + 1} r).obj G
  have : Nonempty Y := ⟨(Z.surjective_reductionι (Classical.arbitrary Z)).choose⟩
  have : IsNoetherian Y := isNoetherian_of_finiteType gY
  obtain ⟨η, hη⟩ := exists_closure_mem_irreducibleComponents Y
  obtain ⟨V, jV, _, hηU, hU⟩ := hstep Y gY hdimY ℓ hℓ GY hGY hℓGY η hη
  -- the closed complement of `V`
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨(Set.range jV.base)ᶜ, jV.isOpenEmbedding.isOpen_range.isClosed_compl⟩ : Closeds Y)
  set W := I.subscheme
  set i : W ⟶ Y := I.subschemeι
  have hirange : Set.range i.base = (Set.range jV.base)ᶜ :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal _
  obtain ⟨_, hS⟩ := shortExact_extensionByZero_etaleAbelianDirectImage.{u, u + 1} i jV
    (by rw [hirange, compl_compl]) GY
  refine of_shortExact gY hS hU ?_
  -- the closed part, by the induction hypothesis and Tag 0A5D
  have := hasExt_of_enoughInjectives.{u + 1} (Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
  obtain ⟨hGW, hℓGW⟩ := inverseImage_constructible_and_nsmul_eq_zero i hGY hℓGY
  refine of_directImage_of_nsmul gY i hℓ hGW hℓGW ?_
  let c : W ⟶ X₀ := i ≫ r ≫ ι
  have hcrange : Set.range c.base ⊆ (O : Set X₀)ᶜ := fun _ ⟨w, hw⟩ ↦
    hw ▸ hι.subset ⟨(i ≫ r).base w, rfl⟩
  have hxC : ι.base (r.base η) ∉ Set.range c.base := by
    rintro ⟨w, hw⟩
    have : i.base w = η := (r ≫ ι).isClosedEmbedding.injective (by simpa [c] using hw)
    exact hirange.subset (Set.mem_range_self w) (this ▸ hηU)
  exact ih _ (lt_compl_of_subset_compl O c.isClosedEmbedding.isClosed_range hcrange
    (hι.subset (Set.mem_range_self _)) hxC) W c (by simp) (i ≫ gY)
    ((i.isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdimY) ℓ hℓ _ hGW hℓGW

/-- **The eight assertions of Tag 03SC for constructible sheaves killed by a prime**, given the
generic step: on a separated scheme of finite type and dimension at most one over an algebraically
closed field, every generic point of an irreducible component has an open neighbourhood `U` with
the eight assertions holding for `j_! j⁻¹ G`. -/
theorem of_genericStep
    (hstep : ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of k)) [IsSeparated g] [LocallyOfFiniteType g]
      [QuasiCompact g] [IsReduced Y]
      [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})],
      topologicalKrullDim Y ≤ 1 → ∀ ℓ : ℕ, ℓ.Prime →
      ∀ G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}, IsConstructibleSmallEtaleSheaf G →
        ℓ • 𝟙 G = 0 → ∀ η : Y, closure {η} ∈ irreducibleComponents Y →
        ∃ (V : Scheme.{u}) (jV : V ⟶ Y) (_ : IsOpenImmersion jV), η ∈ Set.range jV.base ∧
          TorsionCurveAssertions g
            ((extensionByZero.{u, u + 1} jV).obj ((etaleRestriction.{u, u + 1} jV).obj G)))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : IsConstructibleSmallEtaleSheaf G)
    (hℓG : ℓ • 𝟙 G = 0) : TorsionCurveAssertions f G := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  exact of_genericStep_aux hstep X ⊥ X (𝟙 X) (by simp) f hdim ℓ hℓ G hG hℓG

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end

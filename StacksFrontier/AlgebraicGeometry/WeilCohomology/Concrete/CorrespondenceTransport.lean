module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.TransposeGraph
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionAction

/-!
# Transport of correspondences along isomorphisms

An isomorphism `φ : X' ≅ X` of schemes smooth over a field `k` carries the part `X'_d` of `X'` of
dimension `d` isomorphically onto the part `X_d` of `X`. So isomorphisms `X' ≅ X` and `Y' ≅ Y`
over `k` induce an isomorphism `Corrʳ(X', Y') ≃ Corrʳ(X, Y)` of correspondences of mixed
dimension: on each block it is pushforward along `X'_d × Y'_e ≅ X_d × Y_e`. This file constructs
that transport and proves that it is compatible with composition of correspondences. It also
identifies the graph of an isomorphism with a transport of the diagonal. Composing with the graph
of an isomorphism is therefore transport along it. That is what the naturality of the
constraints of Stacks 0FG7 reduces to.

## Main definitions

* `Stacks.WeilCohomology.partMap`: the morphism `X'_d ⟶ X_d` of parts induced by an open
  immersion `X' ⟶ X` over the base, an isomorphism when the open immersion is.
* `Stacks.WeilCohomology.corrEquivOfIso`: the transport `Corrʳ(X', Y') ≃ Corrʳ(X, Y)`.

## Main results

* `Stacks.WeilCohomology.comp_corrEquivOfIso`: transport is compatible with composition.
* `Stacks.WeilCohomology.corrEquivOfIso_id`: transport along identities is the identity.

## References

* [Stacks Project, Tag 0FG7](https://stacks.math.columbia.edu/tag/0FG7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### Parts under open immersions -/

section Parts

variable {S X X' X'' : Scheme.{u}} (sX : X ⟶ S) (sX' : X' ⟶ S) (sX'' : X'' ⟶ S) [Smooth sX]
  [Smooth sX'] [Smooth sX''] (φ : X' ⟶ X) [IsOpenImmersion φ] (hφ : φ ≫ sX = sX')

include hφ in
/-- An open immersion over the base carries the part of dimension `d` into the part of
dimension `d`. -/
theorem range_dimPart_ι_comp_subset (d : ℕ) :
    Set.range ((dimPart sX' d).ι ≫ φ) ⊆ (dimPart sX d : Set X) :=
  range_subset_dimPart sX _ (relativeDimension_of_eq (by rw [Category.assoc, hφ])
    (relativeDimension_partBase sX' d))

/-- The morphism `X'_d ⟶ X_d` of parts of dimension `d` induced by an open immersion
`X' ⟶ X` over the base. -/
def partMap (d : ℕ) : (dimPart sX' d).toScheme ⟶ (dimPart sX d).toScheme :=
  IsOpenImmersion.lift (dimPart sX d).ι ((dimPart sX' d).ι ≫ φ)
    (by rw [Scheme.Opens.range_ι]; exact range_dimPart_ι_comp_subset sX sX' φ hφ d)

/-- The morphism of parts `X'_d ⟶ X_d` followed by the inclusion of `X_d` is the inclusion of
`X'_d` followed by `φ`. -/
@[reassoc (attr := simp)]
theorem partMap_ι (d : ℕ) :
    partMap sX sX' φ hφ d ≫ (dimPart sX d).ι = (dimPart sX' d).ι ≫ φ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The morphism of parts `X'_d ⟶ X_d` commutes with the structure morphisms to the base. -/
theorem partMap_comp_partBase (d : ℕ) :
    partMap sX sX' φ hφ d ≫ partBase sX d = partBase sX' d := by
  change partMap sX sX' φ hφ d ≫ (dimPart sX d).ι ≫ sX = (dimPart sX' d).ι ≫ sX'
  rw [partMap_ι_assoc, hφ]

/-- Two open immersions that are equal induce the same morphism of parts. -/
theorem partMap_congr {φ' : X' ⟶ X} [IsOpenImmersion φ'] (hφ' : φ' ≫ sX = sX') (h : φ = φ')
    (d : ℕ) : partMap sX sX' φ hφ d = partMap sX sX' φ' hφ' d := by
  subst h
  rfl

/-- The identity of `X` induces the identity of each part `X_d`. -/
theorem partMap_id (d : ℕ) : partMap sX sX (𝟙 X) (Category.id_comp sX) d = 𝟙 _ := by
  rw [← cancel_mono (dimPart sX d).ι, partMap_ι, Category.comp_id, Category.id_comp]

/-- The morphism of parts induced by a composite `ψ ≫ φ` of open immersions is the composite of
the induced morphisms. -/
theorem partMap_comp (ψ : X'' ⟶ X') [IsOpenImmersion ψ] (hψ : ψ ≫ sX' = sX'') (d : ℕ) :
    partMap sX sX'' (ψ ≫ φ) (by rw [Category.assoc, hφ, hψ]) d =
      partMap sX' sX'' ψ hψ d ≫ partMap sX sX' φ hφ d := by
  rw [← cancel_mono (dimPart sX d).ι, partMap_ι, Category.assoc, partMap_ι, partMap_ι_assoc]

/-- The morphism of parts induced by an isomorphism over the base is an isomorphism. -/
instance [IsIso φ] (d : ℕ) : IsIso (partMap sX sX' φ hφ d) := by
  have hinv : inv φ ≫ sX' = sX := by rw [IsIso.inv_comp_eq, hφ]
  refine ⟨⟨partMap sX' sX (inv φ) hinv d, ?_, ?_⟩⟩
  · rw [← cancel_mono (dimPart sX' d).ι, Category.assoc, partMap_ι, partMap_ι_assoc,
      IsIso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono (dimPart sX d).ι, Category.assoc, partMap_ι, partMap_ι_assoc,
      IsIso.inv_hom_id, Category.comp_id, Category.id_comp]

end Parts

/-! ### Transport of correspondences -/

section Transport

variable (k : Type u) [Field k] {X X' X'' Y Y' Y'' Z Z' : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sX' : X' ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sY' : Y' ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sX'] [IsSeparated sX'] [Smooth sY] [IsSeparated sY]
  [Smooth sY'] [IsSeparated sY'] (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y) [IsIso φY]
  (hφX : φX ≫ sX = sX') (hφY : φY ≫ sY = sY')

/-- **Transport of correspondences along isomorphisms** `φX : X' ≅ X` and `φY : Y' ≅ Y` over `k`:
`Corrʳ(X', Y') ≃ Corrʳ(X, Y)`, on the block `(d, e)` the pushforward along the isomorphism
`X'_d × Y'_e ≅ X_d × Y_e` of parts. -/
def corrEquivOfIso (r : ℤ) : Corr k sX' sY' r ≃ₗ[ℚ] Corr k sX sY r :=
  DirectSum.congrLinearEquiv fun d ↦ DirectSum.congrLinearEquiv fun e ↦
    correspondenceEquivOfIso (fieldChowSituation k) (partBase sX d) (partBase sY e)
      (partBase sX' d) (partBase sY' e) (partMap sX sX' φX hφX d) (partMap sY sY' φY hφY e)
      (partMap_comp_partBase sX sX' φX hφX d) (partMap_comp_partBase sY sY' φY hφY e) e r

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] in
/-- On the block `(d, e)`, transport is the pushforward along the isomorphism
`X'_d × Y'_e ≅ X_d × Y_e` of parts. -/
@[simp]
theorem corrEquivOfIso_lof_lof (r : ℤ) (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase sX' d) (partBase sY' e) e r) :
    corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r
        (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) =
      DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (correspondenceEquivOfIso (fieldChowSituation k) (partBase sX d) (partBase sY e)
          (partBase sX' d) (partBase sY' e) (partMap sX sX' φX hφX d) (partMap sY sY' φY hφY e)
          (partMap_comp_partBase sX sX' φX hφX d) (partMap_comp_partBase sY sY' φY hφY e) e r
          c)) := by
  simp [corrEquivOfIso, DirectSum.coe_congrLinearEquiv]

/-- Transport along isomorphisms of the base: depends only on the isomorphisms. -/
theorem correspondenceEquivOfIso_congr (C : ChowSituation.{u}) {A B A' B' : Scheme.{u}}
    (sA : A ⟶ C.S) (sB : B ⟶ C.S) (sA' : A' ⟶ C.S) (sB' : B' ⟶ C.S) [LocallyOfFiniteType sA]
    [LocallyOfFiniteType sB] [LocallyOfFiniteType sA'] [LocallyOfFiniteType sB']
    (φA φA' : A' ⟶ A) [IsIso φA] [IsIso φA'] (φB φB' : B' ⟶ B) [IsIso φB] [IsIso φB']
    (hφA : φA ≫ sA = sA') (hφA' : φA' ≫ sA = sA') (hφB : φB ≫ sB = sB') (hφB' : φB' ≫ sB = sB')
    (hA : φA = φA') (hB : φB = φB') (e r : ℤ) (c : Correspondence C sA' sB' e r) :
    correspondenceEquivOfIso C sA sB sA' sB' φA φB hφA hφB e r c =
      correspondenceEquivOfIso C sA sB sA' sB' φA' φB' hφA' hφB' e r c := by
  subst hA hB
  rfl

omit [IsSeparated sX] [IsSeparated sY] in
/-- Transport along the identities is the identity. -/
@[simp]
theorem corrEquivOfIso_id (r : ℤ) (c : Corr k sX sY r) :
    corrEquivOfIso k sX sX sY sY (𝟙 X) (𝟙 Y) (Category.id_comp _) (Category.id_comp _) r c = c := by
  induction c using Corr.induction_on with
  | zero => exact LinearEquiv.map_zero _
  | add a b ha hb => rw [map_add, ha, hb]
  | lof d e x =>
    rw [corrEquivOfIso_lof_lof, correspondenceEquivOfIso_congr _ _ _ _ _ _ (𝟙 _) _ (𝟙 _) _
      (Category.id_comp _) _ (Category.id_comp _) (partMap_id sX d) (partMap_id sY e),
      correspondenceEquivOfIso_id]

variable (sZ : Z ⟶ (fieldChowSituation k).S) (sZ' : Z' ⟶ (fieldChowSituation k).S) [Smooth sZ]
  [IsSeparated sZ] [Smooth sZ'] [IsSeparated sZ'] (φZ : Z' ⟶ Z) [IsIso φZ] (hφZ : φZ ≫ sZ = sZ')

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] [IsSeparated sZ]
  [IsSeparated sZ'] in
/-- Transport is compatible with composition of two correspondences, each concentrated in a
single block. -/
theorem comp_corrEquivOfIso_blocks {Δ : DiagonalClassFamily k} (hΔ : Δ.IsoInvariant)
    [IsProper sY] [IsProper sY'] (r s : ℤ) (d e : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX' d) (partBase sY' e) e r) (e' f : ℕ)
    (y : Correspondence (fieldChowSituation k) (partBase sY' e') (partBase sZ' f) f s) :
    comp k sX sY sZ Δ r s
        (corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)))
        (corrEquivOfIso k sY sY' sZ sZ' φY φZ hφY hφZ s
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))) =
      corrEquivOfIso k sX sX' sZ sZ' φX φZ hφX hφZ (r + s)
        (comp k sX' sY' sZ' Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
          (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))) := by
  by_cases he : e = e'
  · subst he
    rw [corrEquivOfIso_lof_lof, corrEquivOfIso_lof_lof, comp_lof_lof_lof_lof,
      comp_lof_lof_lof_lof, corrEquivOfIso_lof_lof,
      correspondenceEquivOfIso_composition k Δ (partBase sX d) (partBase sY e) (partBase sZ f)
        (partBase sX' d) (partBase sY' e) (partBase sZ' f) (partMap sX sX' φX hφX d)
        (partMap sY sY' φY hφY e) (partMap sZ sZ' φZ hφZ f) (partMap_comp_partBase sX sX' φX hφX d)
        (partMap_comp_partBase sY sY' φY hφY e) (partMap_comp_partBase sZ sZ' φZ hφZ f) hΔ
        (relativeDimension_partBase sX d) (relativeDimension_partBase sY e)
        (relativeDimension_partBase sZ f) (relativeDimension_partBase sX' d)
        (relativeDimension_partBase sY' e) (relativeDimension_partBase sZ' f)]
  · simp only [corrEquivOfIso_lof_lof, comp_lof_lof_lof_of_ne k sX sY sZ Δ r s d e e' he,
      comp_lof_lof_lof_of_ne k sX' sY' sZ' Δ r s d e e' he, LinearEquiv.map_zero]

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] [IsSeparated sZ]
  [IsSeparated sZ'] in
/-- Transport is compatible with composition when the first correspondence is concentrated in a
single block. -/
theorem comp_corrEquivOfIso_lof_lof {Δ : DiagonalClassFamily k} (hΔ : Δ.IsoInvariant)
    [IsProper sY] [IsProper sY'] (r s : ℤ) (d e : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase sX' d) (partBase sY' e) e r)
    (b : Corr k sY' sZ' s) :
    comp k sX sY sZ Δ r s
        (corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r
          (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)))
        (corrEquivOfIso k sY sY' sZ sZ' φY φZ hφY hφZ s b) =
      corrEquivOfIso k sX sX' sZ sZ' φX φZ hφX hφZ (r + s)
        (comp k sX' sY' sZ' Δ r s (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) b) := by
  induction b using Corr.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero]
  | add b b' hb hb' => simp only [LinearEquiv.map_add, LinearMap.map_add, hb, hb']
  | lof e' f y =>
    exact comp_corrEquivOfIso_blocks k sX sX' sY sY' φX φY hφX hφY sZ sZ' φZ hφZ hΔ r s d e x e' f y

omit [IsSeparated sX] [IsSeparated sX'] [IsSeparated sY] [IsSeparated sY'] [IsSeparated sZ]
  [IsSeparated sZ'] in
/-- **Composition of correspondences is natural with respect to isomorphisms over `k`**: for
isomorphisms `φX : X' ≅ X`, `φY : Y' ≅ Y`, `φZ : Z' ≅ Z` over `k`, the transport of `b ∘ a` is the
composition of the transports, for an iso-invariant family of diagonal classes. -/
theorem comp_corrEquivOfIso {Δ : DiagonalClassFamily k} (hΔ : Δ.IsoInvariant) [IsProper sY]
    [IsProper sY'] (r s : ℤ) (a : Corr k sX' sY' r) (b : Corr k sY' sZ' s) :
    comp k sX sY sZ Δ r s (corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r a)
        (corrEquivOfIso k sY sY' sZ sZ' φY φZ hφY hφZ s b) =
      corrEquivOfIso k sX sX' sZ sZ' φX φZ hφX hφZ (r + s) (comp k sX' sY' sZ' Δ r s a b) := by
  induction a using Corr.induction_on with
  | zero => simp only [LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.zero_apply]
  | add a a' ha ha' =>
    simp only [LinearEquiv.map_add, LinearMap.map_add, LinearMap.add_apply, ha, ha']
  | lof d e x =>
    exact comp_corrEquivOfIso_lof_lof k sX sX' sY sY' φX φY hφX hφY sZ sZ' φZ hφZ hΔ r s d e x b

end Transport

/-! ### Graphs of isomorphisms are transports of the diagonal -/

section Graph

variable (k : Type u) [Field k] {P Q Q' : Scheme.{u}} (sP : P ⟶ (fieldChowSituation k).S)
  (sQ : Q ⟶ (fieldChowSituation k).S) (sQ' : Q' ⟶ (fieldChowSituation k).S) [Smooth sP]
  [IsSeparated sP] [Smooth sQ] [IsSeparated sQ] [Smooth sQ'] [IsSeparated sQ']

omit [IsSeparated sP] [IsSeparated sQ] in
/-- An isomorphism over the base maps the part `Q_e` into the part `P_e`. -/
theorem mem_dimPart_of_isIso (ψ : Q ⟶ P) [IsIso ψ] (hψ : ψ ≫ sP = sQ) {e : ℕ} {y : Q}
    (hy : y ∈ dimPart sQ e) : ψ y ∈ dimPart sP e :=
  range_dimPart_ι_comp_subset sP sQ ψ hψ e ⟨⟨y, hy⟩, rfl⟩

variable (α : Q' ⟶ P) [IsIso α] (hα : α ≫ sP = sQ') (β : Q' ⟶ Q) [IsIso β] (hβ : β ≫ sQ = sQ')

omit [IsSeparated sQ] in
/-- The `(d, d)` block of the graph of `β⁻¹ ≫ α : Q ⟶ P` is the transport of the diagonal of
`Q'_d` along `α × β`. -/
theorem graphBlock_eq_correspondenceEquivOfIso (d : ℕ) :
    graphBlock k sP sQ (inv β ≫ α) (by rw [Category.assoc, hα, IsIso.inv_comp_eq, hβ]) d d =
      correspondenceEquivOfIso (fieldChowSituation k) (partBase sP d) (partBase sQ d)
        (partBase sQ' d) (partBase sQ' d) (partMap sP sQ' α hα d) (partMap sQ sQ' β hβ d)
        (partMap_comp_partBase sP sQ' α hα d) (partMap_comp_partBase sQ sQ' β hβ d) d 0
        (graphCorrespondence (partBase sQ' d) (partBase sQ' d) (𝟙 _) (Category.id_comp _) d) := by
  have hψ : (inv β ≫ α) ≫ sP = sQ := by rw [Category.assoc, hα, IsIso.inv_comp_eq, hβ]
  have hβ' : inv β ≫ sQ' = sQ := by rw [IsIso.inv_comp_eq, hβ]
  set A := ((dimPart sQ d).ι ≫ (inv β ≫ α)) ⁻¹ᵁ dimPart sP d with hA
  have hrange : Set.range A.ι = Set.range (𝟙 (dimPart sQ d).toScheme) := by
    rw [Scheme.Opens.range_ι]
    refine (Set.eq_univ_of_forall fun x ↦ ?_).trans (Set.range_id).symm
    exact mem_dimPart_of_isIso k sP sQ (inv β ≫ α) hψ x.2
  set m := prodHom (partBase sP d) (partBase sQ d) (partBase sQ' d) (partBase sQ' d)
    (partMap sP sQ' α hα d) (partMap sQ sQ' β hβ d) (partMap_comp_partBase sP sQ' α hα d)
    (partMap_comp_partBase sQ sQ' β hβ d)
  have : IsIso m := by
    refine ⟨prodHom (partBase sQ' d) (partBase sQ' d) (partBase sP d) (partBase sQ d)
      (inv (partMap sP sQ' α hα d)) (inv (partMap sQ sQ' β hβ d))
      (by rw [IsIso.inv_comp_eq, partMap_comp_partBase])
      (by rw [IsIso.inv_comp_eq, partMap_comp_partBase]), ?_, ?_⟩ <;>
      apply Limits.pullback.hom_ext <;> simp [m]
  have := isClosedImmersion_graphMorphism (partBase sQ' d) (partBase sQ' d) (𝟙 _)
    (Category.id_comp _)
  set ι := IsOpenImmersion.isoOfRangeEq A.ι (𝟙 _) hrange ≪≫ asIso (partMap sQ' sQ (inv β) hβ' d)
  have hι : ι.hom = A.ι ≫ partMap sQ' sQ (inv β) hβ' d := by
    simp only [ι, Iso.trans_hom, asIso_hom]
    congr 1
    simpa using IsOpenImmersion.isoOfRangeEq_hom_fac A.ι (𝟙 _) hrange
  have hcomp : ι.hom ≫
      (graphMorphism (partBase sQ' d) (partBase sQ' d) (𝟙 _) (Category.id_comp _) ≫ m) =
        graphPiece k sP sQ (inv β ≫ α) hψ d d := by
    rw [hι]
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, graphPiece_fst, ← cancel_mono (dimPart sP d).ι,
        morphismRestrict_ι]
      simp only [m, Category.assoc, Limits.pullback.lift_fst_assoc, partMap_ι]
      rw [Category.id_comp, partMap_ι_assoc]
    · rw [Category.assoc, Category.assoc, graphPiece_snd]
      simp only [m, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc]
      rw [Category.id_comp, ← partMap_comp,
        partMap_congr sQ sQ (inv β ≫ β) _ (Category.id_comp _) (IsIso.inv_hom_id β), partMap_id,
        Category.comp_id]
  rw [graphBlock, graphCorrespondence, correspondenceEquivOfIso_tmul,
    cycleAssociatedToClosedSubscheme_eq_of_iso _ _ _ _ _ hcomp]
  congr 1
  have key := properPushforward_cycleAssociatedToClosedSubscheme_of_isIso (fieldChowSituation k)
    _ _ (asIso m) (prodHom_comp_prodBase _ _ _ _ _ _ (partMap_comp_partBase sP sQ' α hα d)
      (partMap_comp_partBase sQ sQ' β hβ d))
    (graphMorphism (partBase sQ' d) (partBase sQ' d) (𝟙 _) (Category.id_comp _)) ((d : ℤ) - 0)
  exact (congrArg (QuotientAddGroup.mk' (rationalEquivalences _ _ _)) key).symm

set_option synthInstance.maxHeartbeats 200000 in
-- Lean v4.35.0: instance search for `AddMonoidHomClass` on `Corr` needs more heartbeats.
omit [IsSeparated sQ] in
/-- **The graph of `β⁻¹ ≫ α` is the transport of the diagonal along `α × β`**:
`[Γ_{β⁻¹ ≫ α}] = (α × β)_* [Δ_{Q'}]` in `Corr⁰(P, Q)`. -/
theorem graphCorr_eq_corrEquivOfIso [QuasiCompact sQ] [QuasiCompact sQ'] :
    graphCorr k sP sQ (inv β ≫ α) (by rw [Category.assoc, hα, IsIso.inv_comp_eq, hβ]) =
      corrEquivOfIso k sP sQ' sQ sQ' α β hα hβ 0 (diagonalCorr k sQ') := by
  have hψ : (inv β ≫ α) ≫ sP = sQ := by rw [Category.assoc, hα, IsIso.inv_comp_eq, hβ]
  have : CompactSpace Q := QuasiCompact.compactSpace_of_compactSpace sQ
  have : CompactSpace Q' := QuasiCompact.compactSpace_of_compactSpace sQ'
  set D := (finite_setOf_nonempty_dimPart sQ).toFinset
  have hQQ' : ∀ d, (dimPart sQ' d : Set Q').Nonempty → d ∈ D := fun d ⟨y, hy⟩ ↦
    (finite_setOf_nonempty_dimPart sQ).mem_toFinset.2 ⟨β y, mem_dimPart_of_isIso k sQ sQ' β hβ hy⟩
  have hD : ∀ d, ((inv β ≫ α) ⁻¹ᵁ dimPart sP d : Set Q).Nonempty → d ∈ D := by
    rintro d ⟨y, hy⟩
    obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sQ).exists_mem y
    have := (isClopenDecomposition_dimPart sP).eq_of_mem
      (mem_dimPart_of_isIso k sP sQ (inv β ≫ α) hψ he) hy
    exact (finite_setOf_nonempty_dimPart sQ).mem_toFinset.2 ⟨y, this ▸ he⟩
  rw [graphCorr_eq_sum k sP sQ (inv β ≫ α) hψ hD
    (fun e he ↦ (finite_setOf_nonempty_dimPart sQ).mem_toFinset.2 he)]
  unfold diagonalCorr
  rw [map_sum, Finset.sum_subset (fun d hd ↦ hQQ' d
      ((finite_setOf_nonempty_dimPart sQ').mem_toFinset.1 hd)) fun d _ hd ↦ ?_]
  · refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Finset.sum_eq_single_of_mem d ‹_› fun e _ hne ↦ by
      rw [graphBlock_eq_zero k sP sQ (inv β ≫ α) hψ fun y hy hy' ↦
        hne ((isClopenDecomposition_dimPart sP).eq_of_mem
          (mem_dimPart_of_isIso k sP sQ (inv β ≫ α) hψ hy) hy'), map_zero, map_zero],
      corrEquivOfIso_lof_lof, graphBlock_eq_correspondenceEquivOfIso k sP sQ sQ' α hα β hβ d]
  · have : IsEmpty (dimPart sQ' d).toScheme :=
      ⟨fun y ↦ hd ((finite_setOf_nonempty_dimPart sQ').mem_toFinset.2 ⟨y.1, y.2⟩)⟩
    rw [diagonalBlock, corrEquivOfIso_lof_lof,
      (subsingleton_correspondence_of_isEmpty_left (fieldChowSituation k) (partBase sQ' d)
        (partBase sQ' d) d 0).elim (graphCorrespondence (partBase sQ' d) (partBase sQ' d) (𝟙 _)
        (Category.id_comp _) d) 0, map_zero, map_zero, map_zero]

end Graph

/-! ### Composition with the graph of an isomorphism -/

section CompGraph

variable (k : Type u) [Field k] {X P Q Y Z : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sP : P ⟶ (fieldChowSituation k).S) (sQ : Q ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sP] [IsSeparated sP] [Smooth sQ] [IsSeparated sQ]
  [Smooth sY] [IsSeparated sY] [Smooth sZ] [IsSeparated sZ] {Δ : DiagonalClassFamily k}

omit [IsSeparated sQ] in
/-- The graph correspondence depends only on the morphism. -/
theorem graphCorr_congr [QuasiCompact sQ] {f f' : Q ⟶ P} (hf : f ≫ sP = sQ) (hf' : f' ≫ sP = sQ)
    (h : f = f') : graphCorr k sP sQ f hf = graphCorr k sP sQ f' hf' := by
  subst h
  rfl

omit [IsSeparated sX] [IsSeparated sY] in
/-- Transport commutes with the identification of degrees. -/
theorem corrEquivOfIso_corrCongr {X' Y' : Scheme.{u}} (sX' : X' ⟶ (fieldChowSituation k).S)
    (sY' : Y' ⟶ (fieldChowSituation k).S) [Smooth sX'] [IsSeparated sX'] [Smooth sY']
    [IsSeparated sY'] (φX : X' ⟶ X) [IsIso φX] (φY : Y' ⟶ Y) [IsIso φY] (hφX : φX ≫ sX = sX')
    (hφY : φY ≫ sY = sY') {r r' : ℤ} (h : r = r') (c : Corr k sX' sY' r) :
    corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r' (corrCongr k sX' sY' h c) =
      corrCongr k sX sY h (corrEquivOfIso k sX sX' sY sY' φX φY hφX hφY r c) := by
  subst h
  rw [corrCongr_self, corrCongr_self]

/-- **Composing with the graph of an isomorphism on the source side is transport**: for an
isomorphism `ψ : Q ⟶ P` over `k` and `h ∈ Corrˢ(Q, Y)`, `h ∘ [Γ_ψ] = (ψ × 1)_* h`. -/
theorem comp_graphCorr_left (hΔ : Δ.ProperIntersectionFormula) (hiso : Δ.IsoInvariant)
    [IsProper sP] [IsProper sQ] [QuasiCompact sY] (ψ : Q ⟶ P) [IsIso ψ] (hψ : ψ ≫ sP = sQ)
    (s : ℤ) (h : Corr k sQ sY s) :
    comp k sP sQ sY Δ 0 s (graphCorr k sP sQ ψ hψ) h =
      corrCongr k sP sY (zero_add s).symm
        (corrEquivOfIso k sP sQ sY sY ψ (𝟙 Y) hψ (Category.id_comp _) s h) := by
  have hg : graphCorr k sP sQ ψ hψ =
      corrEquivOfIso k sP sQ sQ sQ ψ (𝟙 Q) hψ (Category.id_comp _) 0 (diagonalCorr k sQ) :=
    (graphCorr_congr k sP sQ hψ _ (by simp)).trans
      (graphCorr_eq_corrEquivOfIso k sP sQ sQ ψ hψ (𝟙 Q) (Category.id_comp _))
  conv_lhs => rw [hg, ← corrEquivOfIso_id k sQ sY s h]
  rw [comp_corrEquivOfIso k sP sQ sQ sQ ψ (𝟙 Q) hψ (Category.id_comp _) sY sY (𝟙 Y)
    (Category.id_comp _) hiso 0 s, hΔ.comp_diagonalCorr k sQ sY s h, corrEquivOfIso_corrCongr]

omit [IsSeparated sZ] in
/-- **Composing with the graph of an isomorphism on the target side is transport**: for an
isomorphism `χ : Z ⟶ Y` over `k` and `h ∈ Corrʳ(X, Y)`, `[Γ_χ] ∘ h = (1 × χ⁻¹)_* h`. -/
theorem comp_graphCorr_right (hΔ : Δ.ProperIntersectionFormula) (hiso : Δ.IsoInvariant)
    [IsProper sX] [IsProper sY] [IsProper sZ] (χ : Z ⟶ Y) [IsIso χ] (hχ : χ ≫ sY = sZ) (r : ℤ)
    (h : Corr k sX sY r) :
    comp k sX sY sZ Δ r 0 h (graphCorr k sY sZ χ hχ) =
      corrCongr k sX sZ (add_zero r).symm
        (corrEquivOfIso k sX sX sZ sY (𝟙 X) (inv χ) (Category.id_comp _)
          (by rw [IsIso.inv_comp_eq, hχ]) r h) := by
  have hinv : inv χ ≫ sZ = sY := by rw [IsIso.inv_comp_eq, hχ]
  have hg : graphCorr k sY sZ χ hχ =
      corrEquivOfIso k sY sY sZ sY (𝟙 Y) (inv χ) (Category.id_comp _) hinv 0
        (diagonalCorr k sY) :=
    (graphCorr_congr k sY sZ hχ _ (by simp)).trans
      (graphCorr_eq_corrEquivOfIso k sY sZ sY (𝟙 Y) (Category.id_comp _) (inv χ) hinv)
  conv_lhs => rw [hg, ← corrEquivOfIso_id k sX sY r h]
  rw [comp_corrEquivOfIso k sX sX sY sY (𝟙 X) (𝟙 Y) (Category.id_comp _) (Category.id_comp _)
    sZ sY (inv χ) hinv hiso r 0, hΔ.diagonalCorr_comp k sX sY r h, corrEquivOfIso_corrCongr]

end CompGraph

end Stacks.WeilCohomology

end

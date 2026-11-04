module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CoproductCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCorrespondences
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Tensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.DimensionDecompositionAssoc
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The blocks of the correspondences of the projective space bundle formula

Let `p : P = 𝐏(ℰ) ⟶ X` be the projective bundle of a finite locally free module of rank `n + 1`
on a smooth projective scheme over `k`. The projection is smooth of relative dimension `n`, so
the part `P_e` of `P` of dimension `e` lies over the part `X_{e-n}` of `X`:

  `P_{d+n} = p⁻¹(X_d)`, and `P_e = ∅` for `e < n`.

Accordingly the graph `[Γ_p] ∈ Corr⁰(X, P)` and the correspondences
`c_i = c₁(pr₂^*𝒪_P(1))^i ∩ [Γ_p]` live only on the blocks `X_d × P_{d+n}`, where `Γ_p` is the graph
of the restriction `p_d : P_{d+n} ⟶ X_d`, flat of relative dimension `n`. Composing a block of a
correspondence `u ∈ Corrʳ(Z, X)` with `c_i` is then computed by
`Stacks.WeilCohomology.compositionInt_capPow_closedImmersion`:

  `(c_i ∘ u)_{f,d+n} = c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* u_{f,d}`.

## Main results

* `Stacks.WeilCohomology.dimPart_projectiveBundle`: `P_{d+n} = p⁻¹(X_d)`.
* `Stacks.WeilCohomology.not_mem_dimPart_projectiveBundle_of_lt`: `P_e = ∅` for `e < n`.
* `Stacks.WeilCohomology.graphCorr_apply_apply`: the blocks of a graph correspondence.
* `Stacks.WeilCohomology.projectiveBundleCorr_apply`: the `d`-th row of `c_i` is its block
  `(d, d + n)`.
* `Stacks.WeilCohomology.composition_blockTwistCap_graphBlock`: composing a block with `c_i` is
  `projectiveBundleBlockMap`, `x ↦ c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* x`.

## References

* [Stacks Project, Tag 0FGQ](https://stacks.math.columbia.edu/tag/0FGQ)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

section Bundle

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- The projection `p : P ⟶ X` of the projective bundle is flat. -/
instance : Flat (SmoothProjectiveScheme.bundleProj X E n).hom.left :=
  flat_bundleProj E n

/-- The projection `p : P ⟶ X` of the projective bundle is locally of finite type. -/
instance : LocallyOfFiniteType (SmoothProjectiveScheme.bundleProj X E n).hom.left :=
  locallyOfFiniteType_bundleProj E n

/-- The projection `p : P ⟶ X` of the projective bundle has relative dimension `n`. -/
theorem relativeDimension_projectiveBundleProj :
    RelativeDimension (SmoothProjectiveScheme.bundleProj X E n).hom.left n :=
  relativeDimension_bundleProj E n

/-- The preimage `p⁻¹(X_d)` lies in the part `P_{d+n}` of the projective bundle. -/
private theorem preimage_dimPart_le_dimPart_projectiveBundle (d : ℕ) :
    (SmoothProjectiveScheme.bundleProj X E n).hom.left ⁻¹ᵁ dimPart X.obj.hom d ≤
      dimPart (projectiveBundle X E n).obj.hom (d + n) := by
  set p := (SmoothProjectiveScheme.bundleProj X E n).hom.left
  have hp : p ≫ X.obj.hom = (projectiveBundle X E n).obj.hom := Over.w _
  have h1 : (p ⁻¹ᵁ dimPart X.obj.hom d).ι ≫ (projectiveBundle X E n).obj.hom =
      (p ∣_ dimPart X.obj.hom d) ≫ partBase X.obj.hom d := by
    rw [partBase, ← Category.assoc, morphismRestrict_ι, Category.assoc, hp]
  have hrel : RelativeDimension ((p ⁻¹ᵁ dimPart X.obj.hom d).ι ≫
      (projectiveBundle X E n).obj.hom) (d + n) := by
    refine relativeDimension_of_eq h1.symm ?_
    rw [add_comm]
    exact RelativeDimension.comp_of_flat _ _
      (relativeDimension_morphismRestrict _ n (relativeDimension_projectiveBundleProj X E n) _)
      (relativeDimension_partBase X.obj.hom d)
  exact fun x hx ↦ range_subset_dimPart _ _ hrel (by rw [Scheme.Opens.range_ι]; exact hx)

/-- Every point of the projective bundle lies in some part `P_{d+n}` over a part `X_d`. -/
private theorem exists_mem_dimPart_projectiveBundle (x : (projectiveBundle X E n).obj.left) :
    ∃ d : ℕ, (SmoothProjectiveScheme.bundleProj X E n).hom.left x ∈ dimPart X.obj.hom d ∧
      x ∈ dimPart (projectiveBundle X E n).obj.hom (d + n) := by
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart X.obj.hom).exists_mem
    ((SmoothProjectiveScheme.bundleProj X E n).hom.left x)
  exact ⟨d, hd, preimage_dimPart_le_dimPart_projectiveBundle X E n d hd⟩

/-- **The part of dimension `d + n` of the projective bundle is the preimage of the part of
dimension `d`**: `P_{d+n} = p⁻¹(X_d)`, the projection being smooth of relative dimension `n`. -/
theorem dimPart_projectiveBundle (d : ℕ) :
    dimPart (projectiveBundle X E n).obj.hom (d + n) =
      (SmoothProjectiveScheme.bundleProj X E n).hom.left ⁻¹ᵁ dimPart X.obj.hom d := by
  refine le_antisymm (fun x hx ↦ ?_) (preimage_dimPart_le_dimPart_projectiveBundle X E n d)
  obtain ⟨d', hd', hx'⟩ := exists_mem_dimPart_projectiveBundle X E n x
  have : d' + n = d + n := (isClopenDecomposition_dimPart _).eq_of_mem hx' hx
  rw [show d = d' by omega]
  exact hd'

/-- **The parts of dimension less than `n` of the projective bundle are empty.** -/
theorem not_mem_dimPart_projectiveBundle_of_lt {e : ℕ} (he : e < n)
    (x : (projectiveBundle X E n).obj.left) :
    x ∉ dimPart (projectiveBundle X E n).obj.hom e := by
  intro hx
  obtain ⟨d', -, hx'⟩ := exists_mem_dimPart_projectiveBundle X E n x
  have := (isClopenDecomposition_dimPart _).eq_of_mem hx hx'
  omega

end Bundle

section GraphBlocks

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sY : Y ⟶ (fieldChowSituation k).S)
  [Smooth sX] [IsSeparated sX] [Smooth sY] [IsSeparated sY] [QuasiCompact sY]

/-- **The blocks of the graph correspondence**: the `(d, e)` component of `[Γ_f] ∈ Corr⁰(X, Y)` is
the class of `Γ_f ∩ (X_d × Y_e)`. -/
theorem graphCorr_apply_apply (f : Y ⟶ X) (hf : f ≫ sX = sY) (d e : ℕ) :
    graphCorr k sX sY f hf d e = graphBlock k sX sY f hf d e := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  rw [graphCorr_eq_sum k sX sY f hf
    (D := insert d (finite_setOf_nonempty_preimage_dimPart k sX f).toFinset)
    (E := insert e (finite_setOf_nonempty_dimPart sY).toFinset)
    (fun d' hd' ↦ Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 hd'))
    (fun e' he' ↦ Finset.mem_insert_of_mem ((Set.Finite.mem_toFinset _).2 he'))]
  simp only [DirectSum.lof_eq_of]
  rw [DirectSum.sum_apply, Finset.sum_eq_single_of_mem d (Finset.mem_insert_self _ _)
    (fun d' _ hd' ↦ by
      rw [DirectSum.sum_apply]
      exact Finset.sum_eq_zero fun e' _ ↦ DirectSum.of_eq_of_ne _ _ _ (Ne.symm hd')),
    DirectSum.sum_apply]
  simp only [DirectSum.of_eq_same]
  rw [DirectSum.sum_apply, Finset.sum_eq_single_of_mem e (Finset.mem_insert_self _ _)
    (fun e' _ he' ↦ DirectSum.of_eq_of_ne _ _ _ (Ne.symm he')), DirectSum.of_eq_same]

end GraphBlocks

section BundleBlocks

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

/-- The blocks `(d, e)` of the graph of the projective bundle with `e ≠ d + n` vanish: the part
`P_e` does not meet `p⁻¹(X_d) = P_{d+n}`. -/
theorem graphBlock_projectiveBundle_eq_zero {d e : ℕ} (he : e ≠ d + n) :
    graphBlock k X.obj.hom (projectiveBundle X E n).obj.hom
      (SmoothProjectiveScheme.bundleProj X E n).hom.left
      (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d e = 0 := by
  refine graphBlock_eq_zero k _ _ _ _ fun y hy hpy ↦ he ?_
  exact (isClopenDecomposition_dimPart _).eq_of_mem hy
    (preimage_dimPart_le_dimPart_projectiveBundle X E n d hpy)

/-- The open subscheme `P_{d+n} ∩ p⁻¹(X_d)` of `P_{d+n}`, the source of the block `(d, d + n)` of
the graph of `p`. -/
abbrev projectiveBundleGraphOpen (d : ℕ) :
    (dimPart (projectiveBundle X E n).obj.hom (d + n)).toScheme.Opens :=
  ((dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
    (SmoothProjectiveScheme.bundleProj X E n).hom.left) ⁻¹ᵁ dimPart X.obj.hom d

/-- The open subscheme `P_{d+n} ∩ p⁻¹(X_d)` is all of `P_{d+n}`. -/
theorem projectiveBundleGraphOpen_eq_top (d : ℕ) : projectiveBundleGraphOpen X E n d = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  have hx : x.1 ∈ (SmoothProjectiveScheme.bundleProj X E n).hom.left ⁻¹ᵁ dimPart X.obj.hom d :=
    dimPart_projectiveBundle X E n d ▸ x.2
  exact hx

/-- The inclusion of `P_{d+n} ∩ p⁻¹(X_d)` into `P_{d+n}` is an isomorphism. -/
instance (d : ℕ) : IsIso (projectiveBundleGraphOpen X E n d).ι := by
  rw [projectiveBundleGraphOpen_eq_top]
  exact inferInstanceAs
    (IsIso (dimPart (projectiveBundle X E n).obj.hom (d + n)).toScheme.topIso.hom)

/-- **The restriction `p_d : P_{d+n} ⟶ X_d` of the projection** of the projective bundle. -/
def projectiveBundlePartProj (d : ℕ) :
    (dimPart (projectiveBundle X E n).obj.hom (d + n)).toScheme ⟶ (dimPart X.obj.hom d).toScheme :=
  inv (projectiveBundleGraphOpen X E n d).ι ≫
    ((dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
      (SmoothProjectiveScheme.bundleProj X E n).hom.left) ∣_ dimPart X.obj.hom d

/-- The restriction `p_d : P_{d+n} ⟶ X_d` followed by the inclusion `X_d ⟶ X` is the inclusion
`P_{d+n} ⟶ P` followed by `p`. -/
theorem projectiveBundlePartProj_ι (d : ℕ) :
    projectiveBundlePartProj X E n d ≫ (dimPart X.obj.hom d).ι =
      (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
        (SmoothProjectiveScheme.bundleProj X E n).hom.left := by
  rw [projectiveBundlePartProj, Category.assoc, morphismRestrict_ι, IsIso.inv_hom_id_assoc]

/-- The restriction `p_d : P_{d+n} ⟶ X_d` commutes with the structure morphisms of `P_{d+n}` and
`X_d` over `k`. -/
theorem projectiveBundlePartProj_partBase (d : ℕ) :
    projectiveBundlePartProj X E n d ≫ partBase X.obj.hom d =
      partBase (projectiveBundle X E n).obj.hom (d + n) := by
  rw [partBase, ← Category.assoc, projectiveBundlePartProj_ι, Category.assoc,
    Over.w (SmoothProjectiveScheme.bundleProj X E n).hom]

/-- The restriction `p_d : P_{d+n} ⟶ X_d` is flat. -/
instance (d : ℕ) : Flat (projectiveBundlePartProj X E n d) := by
  have : Flat ((dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
      (SmoothProjectiveScheme.bundleProj X E n).hom.left) := inferInstance
  have : Flat (((dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
      (SmoothProjectiveScheme.bundleProj X E n).hom.left) ∣_ dimPart X.obj.hom d) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict _ _).flip this
  rw [projectiveBundlePartProj]
  infer_instance

/-- The restriction `p_d : P_{d+n} ⟶ X_d` is locally of finite type. -/
instance (d : ℕ) : LocallyOfFiniteType (projectiveBundlePartProj X E n d) := by
  have : LocallyOfFiniteType ((dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
      (SmoothProjectiveScheme.bundleProj X E n).hom.left) := inferInstance
  have : LocallyOfFiniteType (((dimPart (projectiveBundle X E n).obj.hom (d + n)).ι ≫
      (SmoothProjectiveScheme.bundleProj X E n).hom.left) ∣_ dimPart X.obj.hom d) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict _ _).flip this
  rw [projectiveBundlePartProj]
  infer_instance

/-- The restriction `p_d : P_{d+n} ⟶ X_d` has relative dimension `n`. -/
theorem relativeDimension_projectiveBundlePartProj (d : ℕ) :
    RelativeDimension (projectiveBundlePartProj X E n d) n :=
  RelativeDimension.comp_isOpenImmersion _ _
    (relativeDimension_morphismRestrict _ n (RelativeDimension.comp_isOpenImmersion _ _
      (relativeDimension_projectiveBundleProj X E n)) _)

/-- The block `(d, d + n)` of the graph of `p` maps isomorphically to `P_{d+n}`, as the graph of
`p_d`. -/
theorem graphPiece_fst_projectiveBundle (d : ℕ) :
    graphPiece k X.obj.hom (projectiveBundle X E n).obj.hom
        (SmoothProjectiveScheme.bundleProj X E n).hom.left
        (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n) ≫
      pullback.fst (partBase X.obj.hom d) (partBase (projectiveBundle X E n).obj.hom (d + n)) =
    (graphPiece k X.obj.hom (projectiveBundle X E n).obj.hom
        (SmoothProjectiveScheme.bundleProj X E n).hom.left
        (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n) ≫
      pullback.snd (partBase X.obj.hom d) (partBase (projectiveBundle X E n).obj.hom (d + n))) ≫
      projectiveBundlePartProj X E n d := by
  rw [graphPiece_fst, graphPiece_snd, projectiveBundlePartProj, IsIso.hom_inv_id_assoc]

/-- The second projection from the block `(d, d + n)` of the graph of `p` to `P_{d+n}` is an
isomorphism. -/
instance (d : ℕ) : IsIso (graphPiece k X.obj.hom (projectiveBundle X E n).obj.hom
    (SmoothProjectiveScheme.bundleProj X E n).hom.left
    (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n) ≫
      pullback.snd (partBase X.obj.hom d) (partBase (projectiveBundle X E n).obj.hom (d + n))) := by
  rw [graphPiece_snd]
  infer_instance

end BundleBlocks

section BundleCorr

variable {k : Type u} [Field k] (X : (SmoothProjectiveScheme k).FullSubcategory)
  (E : X.obj.left.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]

local notation "𝒞" => fieldChowSituation k

/-- **The `d`-th row of `c_i`**: its only block is `(d, d + n)`, the cap
`c₁(pr₂^*𝒪(1))^i ∩ [Γ_p ∩ (X_d × P_{d+n})]`. -/
theorem projectiveBundleCorr_apply (i : ℕ) (d : ℕ) :
    SmoothProjectiveCorr.toCorr X (projectiveBundle X E n) (i : ℤ)
        (projectiveBundleCorr X E n i rfl) d =
      DirectSum.lof ℚ ℕ _ (d + n) (blockTwistCap k X.obj.hom (projectiveBundle X E n).obj.hom
        (projectiveBundleTwist X E n) i d (d + n) (by omega : (i : ℤ) = 0 + i)
        (graphBlock k X.obj.hom (projectiveBundle X E n).obj.hom
          (SmoothProjectiveScheme.bundleProj X E n).hom.left
          (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n))) := by
  ext e
  show blockTwistCap k X.obj.hom (projectiveBundle X E n).obj.hom
      (projectiveBundleTwist X E n) i d e (by omega : (i : ℤ) = 0 + i)
      (graphCorr k X.obj.hom (projectiveBundle X E n).obj.hom
        (SmoothProjectiveScheme.bundleProj X E n).hom.left
        (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d e) = _
  rw [graphCorr_apply_apply, DirectSum.lof_eq_of]
  by_cases he : e = d + n
  · subst he
    rw [DirectSum.of_eq_same]
  · rw [graphBlock_projectiveBundle_eq_zero X E n he, map_zero,
      DirectSum.of_eq_of_ne _ _ _ he]

variable {Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- The pullback `pr₂^*(𝒪(1)|_{P_{d+n}})` of the twist to the block `Z_f × P_{d+n}`. -/
abbrev partTwist (f d : ℕ) :
    (Limits.pullback (partBase Z.obj.hom f)
      (partBase (projectiveBundle X E n).obj.hom (d + n))).Modules :=
  (Scheme.Modules.pullback (pullback.snd (partBase Z.obj.hom f)
    (partBase (projectiveBundle X E n).obj.hom (d + n)))).obj
      ((Scheme.Modules.pullback (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι).obj
        (projectiveBundleTwist X E n))

/-- The pullback `pr₂^*(𝒪(1)|_{P_{d+n}})` to `Z_f × P_{d+n}` is invertible. -/
instance (f d : ℕ) : SheafOfModules.IsInvertible
    (Limits.pullback (partBase Z.obj.hom f)
      (partBase (projectiveBundle X E n).obj.hom (d + n))).sheaf.obj
    (Limits.pullback (partBase Z.obj.hom f)
      (partBase (projectiveBundle X E n).obj.hom (d + n))).ringCatSheaf.property
    (partTwist X E n (Z := Z) f d) := by
  have := GenuineChern.isInvertible_pullback (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι
    (projectiveBundleTwist X E n)
  exact GenuineChern.isInvertible_pullback _ _

/-- **The block map of `c_i ∘ -`**: `u ↦ c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* u`, from the block
`Corrʳ(Z_f, X_d)` to the block `Corr^{r+i}(Z_f, P_{d+n})`. -/
def projectiveBundleBlockMap (f d i : ℕ) (r : ℤ) :
    Correspondence 𝒞 (partBase Z.obj.hom f) (partBase X.obj.hom d) d r →ₗ[ℚ]
      Correspondence 𝒞 (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom (d + n))
        (d + n : ℕ) (r + i) :=
  (((capPow 𝒞 (prodBase (partBase Z.obj.hom f) (partBase (projectiveBundle X E n).obj.hom (d + n)))
      (invCap 𝒞 _ (partTwist X E n f d)) i ((d : ℤ) - r + n) (((d + n : ℕ) : ℤ) - (r + i))
      (by push_cast; omega)).comp
    (flatPullbackChowOfRelativeDimension 𝒞 _ _
      (prodMapRight (partBase Z.obj.hom f) (partBase X.obj.hom d)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (projectiveBundlePartProj X E n d)
        (projectiveBundlePartProj_partBase X E n d))
      (prodMapRight_comp_prodBase _ _ _ _ _) n
      (relativeDimension_prodMapRight _ _ _ _ _
        (relativeDimension_projectiveBundlePartProj X E n d))
      ((d : ℤ) - r))).toIntLinearMap).baseChange ℚ

/-- **The composition of a block with `c_i`**: for `x ∈ Corrʳ(Z_f, X_d)`, the composition of `x`
with the block `(d, d + n)` of `c_i` is `c₁(pr₂^*𝒪(1))^i ∩ (1 × p_d)^* x`. -/
theorem composition_blockTwistCap_graphBlock (f d i : ℕ) (r : ℤ)
    (x : Correspondence 𝒞 (partBase Z.obj.hom f) (partBase X.obj.hom d) d r) :
    composition k (partBase Z.obj.hom f) (partBase X.obj.hom d)
        (partBase (projectiveBundle X E n).obj.hom (d + n)) (canonicalDiagonalClassFamily k)
        (relativeDimension_partBase _ f) (relativeDimension_partBase _ d)
        (relativeDimension_partBase _ (d + n)) r i x
        (blockTwistCap k X.obj.hom (projectiveBundle X E n).obj.hom
          (projectiveBundleTwist X E n) i d (d + n) (by omega : (i : ℤ) = 0 + i)
          (graphBlock k X.obj.hom (projectiveBundle X E n).obj.hom
            (SmoothProjectiveScheme.bundleProj X E n).hom.left
            (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n))) =
      projectiveBundleBlockMap X E n f d i r x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, LinearMap.add_apply, ha, hb, map_add]
  | tmul q y =>
    simp only [graphBlock, blockTwistCap, LinearMap.baseChange_tmul, projectiveBundleBlockMap,
      composition_tmul, mul_one]
    congr 1
    have := GenuineChern.isInvertible_pullback
      (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι (projectiveBundleTwist X E n)
    have eL : blockTwist k X.obj.hom (projectiveBundle X E n).obj.hom
        (projectiveBundleTwist X E n) d (d + n) ≅
        (Scheme.Modules.pullback (pullback.snd (partBase X.obj.hom d)
          (partBase (projectiveBundle X E n).obj.hom (d + n)))).obj
          ((Scheme.Modules.pullback (dimPart (projectiveBundle X E n).obj.hom (d + n)).ι).obj
            (projectiveBundleTwist X E n)) :=
      ((Scheme.Modules.pullbackComp _ _).app _).symm
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply]
    rw [GenuineChern.capPow_invCap_congr 𝒞 _ eL]
    exact compositionInt_capPow_closedImmersion (partBase Z.obj.hom f) (partBase X.obj.hom d)
      (partBase (projectiveBundle X E n).obj.hom (d + n)) (relativeDimension_partBase _ f)
      (relativeDimension_partBase _ d) (relativeDimension_partBase _ (d + n))
      (projectiveBundlePartProj X E n d) (projectiveBundlePartProj_partBase X E n d)
      (relativeDimension_projectiveBundlePartProj X E n d) _ (by push_cast; ring) r i
      (graphPiece k X.obj.hom (projectiveBundle X E n).obj.hom
        (SmoothProjectiveScheme.bundleProj X E n).hom.left
        (Over.w (SmoothProjectiveScheme.bundleProj X E n).hom) d (d + n))
      (graphPiece_fst_projectiveBundle X E n d) y

end BundleCorr

end Stacks.WeilCohomology

end

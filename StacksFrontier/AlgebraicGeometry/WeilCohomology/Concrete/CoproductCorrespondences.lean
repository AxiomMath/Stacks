module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Coproduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SmoothTransversalComposition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Motives

/-!
# Correspondences of a disjoint union

Let `k` be a field and let `X`, `Y` be smooth projective schemes over `k`, with disjoint union
`X ⨿ Y` and coprojections `i : X ⟶ X ⨿ Y`, `j : Y ⟶ X ⨿ Y`. The graph classes
`[Γ_i] ∈ Corr⁰(X ⨿ Y, X)` and `[Γ_j] ∈ Corr⁰(X ⨿ Y, Y)` together with the classes of the
transposed graphs `[Γ_iᵗ] ∈ Corr⁰(X, X ⨿ Y)`, `[Γ_jᵗ] ∈ Corr⁰(Y, X ⨿ Y)` satisfy

  `[Γ_i] ∘ [Γ_iᵗ] = [Δ_X]`, `[Γ_j] ∘ [Γ_iᵗ] = 0`, `[Γ_i] ∘ [Γ_jᵗ] = 0`, `[Γ_j] ∘ [Γ_jᵗ] = [Δ_Y]`,
  `[Γ_iᵗ] ∘ [Γ_i] + [Γ_jᵗ] ∘ [Γ_j] = [Δ_{X ⨿ Y}]`.

These are the relations which make `h(X ⨿ Y)` a direct sum of `h(X)` and `h(Y)` in the category of
Chow motives, the case of equal twists in the proof of Stacks 0FGF ("a direct sum is given by
`(Y ⨿ Z, p + q, m)`, with obvious notation. Details omitted.").

Each relation is computed block by block on the decompositions of the schemes into their parts of
constant dimension, by the proper-intersection formula of Stacks 0FFD: every composite is the class
of the fibre product of two graph-like pieces over the middle factor, which is either a copy of a
part of `X` (respectively `Y`), embedded diagonally, or empty.

## Main definitions

* `Stacks.WeilCohomology.cographPiece`: for `f : X ⟶ P`, the transposed graph
  `Γ_fᵗ ∩ (X_e × P_d) ⟶ X_e × P_d`.
* `Stacks.WeilCohomology.cographCorr`: the class `[Γ_fᵗ] ∈ Corr⁰(X, P)` of the transposed graph,
  and `Stacks.WeilCohomology.cographHom` the same as a morphism of the category of
  correspondences of Stacks 0FG2.
* `Stacks.WeilCohomology.ChowMotiveCat.cographMap`, `Stacks.WeilCohomology.ChowMotiveCat.graphMap`:
  the morphisms `h(X) ⟶ h(P)` and `h(P) ⟶ h(X)` of Chow motives given by `[Γ_fᵗ]` and `[Γ_f]`;
  `graphMap f = h(f)` (`Stacks.WeilCohomology.ChowMotiveCat.graphMap_eq`).

## Main results

* `Stacks.WeilCohomology.comp_cographCorr_graphCorr_self`: `[Γ_f] ∘ [Γ_fᵗ] = [Δ_X]` for an open
  immersion `f`.
* `Stacks.WeilCohomology.comp_cographCorr_graphCorr_of_disjoint`: `[Γ_g] ∘ [Γ_fᵗ] = 0` when the
  images of `f` and `g` are disjoint.
* `Stacks.WeilCohomology.comp_graphCorr_cographCorr_add`:
  `[Γ_fᵗ] ∘ [Γ_f] + [Γ_gᵗ] ∘ [Γ_g] = [Δ_P]` when `f` and `g` are open and closed immersions with
  complementary images.
* `Stacks.WeilCohomology.cographHom_comp_graph_self`,
  `Stacks.WeilCohomology.cographHom_comp_graph_of_disjoint`,
  `Stacks.WeilCohomology.graph_comp_cographHom_add`: the three relations in the category of
  correspondences.
* `Stacks.WeilCohomology.ChowMotiveCat.biproductDataOfIsCompl`,
  `Stacks.WeilCohomology.ChowMotiveCat.coprodBiproductData`: `h(P)` is a direct sum of `h(X)` and
  `h(Y)` for open and closed immersions `X ⟶ P`, `Y ⟶ P` with complementary images, in particular
  for any coproduct `P = X ⨿ Y`.
* `Stacks.WeilCohomology.ChowMotiveCat.hasBinaryBiproduct_h` and
  `Stacks.WeilCohomology.ChowMotiveCat.hCoprodIsoBiprod`: `h(X ⨿ Y) ≅ h(X) ⊞ h(Y)`.

## References

* [Stacks Project, Tag 0FGF](https://stacks.math.columbia.edu/tag/0FGF)
* [Stacks Project, Tag 0FFD](https://stacks.math.columbia.edu/tag/0FFD)
* [Stacks Project, Tag 0FG4](https://stacks.math.columbia.edu/tag/0FG4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace Stacks.WeilCohomology

/-! ### Parts of constant dimension along an open immersion -/

section Parts

variable {X P S : Scheme.{u}} (sX : X ⟶ S) (sP : P ⟶ S) [Smooth sX] [Smooth sP]
  (f : X ⟶ P) [IsOpenImmersion f] (hf : f ≫ sP = sX)

omit [Smooth sP] in
/-- A point lies in the part `X_d` exactly when the local dimension of its fibre is `d`. -/
theorem mem_dimPart_iff_topologicalKrullDimAt (d : ℕ) (x : X) :
    x ∈ dimPart sX d ↔ topologicalKrullDimAt (sX.fiber (sX x)) (sX.asFiber x) = d := by
  have key : ∀ (e : ℕ) (y : X), y ∈ dimPart sX e →
      topologicalKrullDimAt (sX.fiber (sX y)) (sX.asFiber y) = e := by
    intro e y hy
    have h := (relativeDimension_iff_forall_topologicalKrullDimAt (partBase sX e) e).1
      (relativeDimension_partBase sX e) ⟨y, hy⟩
    rwa [fiberDimensionAt_comp_openImmersion (dimPart sX e).ι sX ⟨y, hy⟩] at h
  refine ⟨key d x, fun h ↦ ?_⟩
  obtain ⟨e, he⟩ := (isClopenDecomposition_dimPart sX).exists_mem x
  have he' := (key e x he).symm.trans h
  rwa [show e = d by exact_mod_cast he'] at he

include hf in
/-- An open immersion over the base preserves the parts of constant relative dimension: a point
lies in `X_d` exactly when its image lies in `P_d`. -/
theorem mem_dimPart_iff_of_isOpenImmersion (d : ℕ) (x : X) :
    x ∈ dimPart sX d ↔ f x ∈ dimPart sP d := by
  subst hf
  rw [mem_dimPart_iff_topologicalKrullDimAt, mem_dimPart_iff_topologicalKrullDimAt,
    fiberDimensionAt_comp_openImmersion f sP x]

include hf in
/-- Along an open immersion over the base, the part `X_e` maps into `P_e`: the preimage of `P_d`
in `X_e` is everything when `d = e`. -/
theorem preimage_dimPart_eq_top_of_isOpenImmersion (d : ℕ) :
    ((dimPart sX d).ι ≫ f) ⁻¹ᵁ dimPart sP d = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
  show ((dimPart sX d).ι ≫ f) x ∈ dimPart sP d
  rw [Scheme.Hom.comp_apply, ← mem_dimPart_iff_of_isOpenImmersion sX sP f hf]
  exact x.2

include hf in
/-- Along an open immersion over the base, the part `X_e` meets no part `P_d` with `d ≠ e`. -/
theorem isEmpty_preimage_dimPart_of_isOpenImmersion {d e : ℕ} (hde : d ≠ e) :
    IsEmpty (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).toScheme := by
  refine ⟨fun x ↦ ?_⟩
  have hx : ((dimPart sX e).ι ≫ f) x.1 ∈ dimPart sP d := x.2
  rw [Scheme.Hom.comp_apply, ← mem_dimPart_iff_of_isOpenImmersion sX sP f hf] at hx
  exact hde ((isClopenDecomposition_dimPart sX).eq_of_mem hx x.1.2)

end Parts

section PullbackOfMono

variable {C : Type*} [Category C] {A B : C} {f g φ : A ⟶ B} [Mono φ]

/-- Two morphisms equal to the same monomorphism have equal pullback projections. -/
theorem pullback_fst_eq_snd_of_eq_mono (hf : f = φ) (hg : g = φ) [HasPullback f g] :
    pullback.fst f g = pullback.snd f g := by
  subst hf hg
  exact (cancel_mono _).1 pullback.condition

/-- The pullback of two morphisms equal to the same monomorphism projects isomorphically. -/
theorem isIso_pullback_fst_of_eq_mono (hf : f = φ) (hg : g = φ) [HasPullback f g] :
    IsIso (pullback.fst f g) := by
  subst hf hg
  infer_instance

end PullbackOfMono

/-! ### The blocks of a transposed graph -/

section Blocks

variable (k : Type u) [Field k] {X P Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sP] [Smooth sZ] [IsSeparated sX] [IsSeparated sP] [IsSeparated sZ]

/-- **`Γ_fᵗ ∩ (X_e × P_d)`**: for `f : X ⟶ P`, the closed immersion of the open and closed
subscheme `X_e ∩ f⁻¹(P_d)` of `X_e` into `X_e × P_d` by `(1, f)`; the graph piece
`Γ_f ∩ (P_d × X_e)` followed by the factor switch. -/
def cographPiece (f : X ⟶ P) (hf : f ≫ sP = sX) (d e : ℕ) :
    (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).toScheme ⟶
      (Limits.pullback (partBase sX e) (partBase sP d) : Scheme.{u}) :=
  graphPiece k sP sX f hf d e ≫ (pullbackSymmetry (partBase sP d) (partBase sX e)).hom

/-- The transposed graph piece `Γ_fᵗ ∩ (X_e × P_d) ⟶ X_e × P_d` is a closed immersion. -/
instance isClosedImmersion_cographPiece (f : X ⟶ P) (hf : f ≫ sP = sX) (d e : ℕ) :
    IsClosedImmersion (cographPiece k sX sP f hf d e) := by
  rw [cographPiece]; infer_instance

/-- The first coordinate of `Γ_fᵗ ∩ (X_e × P_d) ⟶ X_e × P_d` is the inclusion into `X_e`. -/
@[reassoc (attr := simp)]
theorem cographPiece_fst (f : X ⟶ P) (hf : f ≫ sP = sX) (d e : ℕ) :
    cographPiece k sX sP f hf d e ≫ pullback.fst (partBase sX e) (partBase sP d) =
      (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).ι := by
  rw [cographPiece, Category.assoc, pullbackSymmetry_hom_comp_fst, graphPiece_snd]

/-- The second coordinate of `Γ_fᵗ ∩ (X_e × P_d) ⟶ X_e × P_d` is the restriction of `f`. -/
@[reassoc (attr := simp)]
theorem cographPiece_snd (f : X ⟶ P) (hf : f ≫ sP = sX) (d e : ℕ) :
    cographPiece k sX sP f hf d e ≫ pullback.snd (partBase sX e) (partBase sP d) =
      ((dimPart sX e).ι ≫ f) ∣_ dimPart sP d := by
  rw [cographPiece, Category.assoc, pullbackSymmetry_hom_comp_snd, graphPiece_fst]

/-- `Γ_fᵗ ∩ (X_e × P_d)` lies over `k` as the open subscheme `X_e ∩ f⁻¹(P_d)` of `X_e`. -/
theorem cographPiece_prodBase (f : X ⟶ P) (hf : f ≫ sP = sX) (d e : ℕ) :
    cographPiece k sX sP f hf d e ≫ prodBase (partBase sX e) (partBase sP d) =
      (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).ι ≫ partBase sX e := by
  rw [prodBase, ← Category.assoc, cographPiece_fst]

/-- **The `(e, d)` block of the transposed graph**: the class of `Γ_fᵗ ∩ (X_e × P_d)` in
`CH_d(X_e × P_d) ⊗ ℚ`, the summand of `Corr⁰(X, P)` indexed by `(e, d)`. -/
def cographBlock (f : X ⟶ P) (hf : f ≫ sP = sX) (e d : ℕ) :
    Correspondence (fieldChowSituation k) (partBase sX e) (partBase sP d) d 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
    (prodBase (partBase sX e) (partBase sP d)) (cographPiece k sX sP f hf d e) ((d : ℤ) - 0))

/-- **The transposed graph** `[Γ_fᵗ] ∈ Corr⁰(X, P)` of a morphism `f : X ⟶ P` over `k`, for `X`
quasi-compact: on the decompositions into equidimensional parts its `(e, e)` block is the class of
`Γ_fᵗ ∩ (X_e × P_e)`. When `f` maps each part `X_e` into `P_e` (an open immersion, for instance)
these are its only nonzero blocks. -/
def cographCorr [QuasiCompact sX] (f : X ⟶ P) (hf : f ≫ sP = sX) : Corr k sX sP 0 :=
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  ∑ e ∈ (finite_setOf_nonempty_dimPart sX).toFinset,
    DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ e (cographBlock k sX sP f hf e e))

omit [IsSeparated sX] [IsSeparated sP] in
/-- The open subscheme `X_e ∩ f⁻¹(P_d)` of `X_e` is smooth of relative dimension `e`. -/
theorem relativeDimension_preimage_dimPart (f : X ⟶ P) (d e : ℕ) :
    RelativeDimension ((((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).ι ≫ partBase sX e) e :=
  RelativeDimension.comp_isOpenImmersion _ _ (relativeDimension_partBase sX e)

omit [IsSeparated sX] in
/-- The inclusion of a part of constant dimension is a closed immersion. -/
instance isClosedImmersion_dimPart_ι (d : ℕ) : IsClosedImmersion (dimPart sX d).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact ((isClopenDecomposition_dimPart sX).isClopen d).isClosed)

omit [Smooth sX] [Smooth sP] [IsSeparated sP] in
/-- The diagonal of a part of constant dimension is a closed immersion. -/
instance isClosedImmersion_graphMorphism_partBase (d : ℕ) :
    IsClosedImmersion (graphMorphism (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _)) :=
  isClosedImmersion_graphMorphism _ _ _ _

/-- Restricted to the parts, an open immersion is a monomorphism. -/
instance mono_restrict_dimPart (f : X ⟶ P) [IsOpenImmersion f] (d e : ℕ) :
    Mono (((dimPart sX e).ι ≫ f) ∣_ dimPart sP d) := inferInstance

variable {Δ : DiagonalClassFamily k}

/-- If `a` and `b` project to the same monomorphism over the middle factor, their fibre product
over it is isomorphic to `A`, compatibly with any `j` that agrees with `a` and `b` on the outer
factors. -/
private theorem exists_iso_compositionFibre_of_eq_mono {S X' Y Z' A : Scheme.{u}}
    {sX' : X' ⟶ S} {sY : Y ⟶ S} {sZ' : Z' ⟶ S} (a : A ⟶ Limits.pullback sX' sY)
    (b : A ⟶ Limits.pullback sY sZ') (j : A ⟶ Limits.pullback sX' sZ') {c : A ⟶ Y} [Mono c]
    (ha : a ≫ pullback.snd sX' sY = c) (hb : b ≫ pullback.fst sY sZ' = c)
    (hj₁ : j ≫ pullback.fst sX' sZ' = a ≫ pullback.fst sX' sY)
    (hj₂ : j ≫ pullback.snd sX' sZ' = b ≫ pullback.snd sY sZ') :
    ∃ e : compositionFibre a b ≅ A, e.hom ≫ j = compositionFibre.toProduct a b := by
  have hfs := pullback_fst_eq_snd_of_eq_mono ha hb
  have := isIso_pullback_fst_of_eq_mono ha hb
  refine ⟨asIso (pullback.fst _ _), pullback.hom_ext ?_ ?_⟩
  · simp only [asIso_hom, Category.assoc, hj₁, compositionFibre.toProduct, pullback.lift_fst]
  · simp only [asIso_hom, Category.assoc, hj₂, compositionFibre.toProduct, pullback.lift_snd, hfs]

/-- **The transposed graph of an open immersion followed by its graph is the diagonal, blockwise.**
For an open immersion `f : X ⟶ P` over `k`,
`[Γ_f ∩ (P_d × X_d)] ∘ [Γ_fᵗ ∩ (X_d × P_d)] = [Δ_{X_d}]`: the fibre product over `P_d` of `X_d`
with itself along the monomorphism `f` is `X_d`, embedded diagonally. -/
theorem composition_cographBlock_graphBlock_self [IsProper sP] (f : X ⟶ P) [IsOpenImmersion f]
    (hf : f ≫ sP = sX) (d : ℕ) :
    composition k (partBase sX d) (partBase sP d) (partBase sX d) (canonicalDiagonalClassFamily k)
        (relativeDimension_partBase sX d) (relativeDimension_partBase sP d)
        (relativeDimension_partBase sX d) 0 0 (cographBlock k sX sP f hf d d)
        (graphBlock k sP sX f hf d d) =
      correspondenceCongr k (partBase sX d) (partBase sX d) (add_zero 0).symm
        (graphCorrespondence (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _) d) := by
  set A := ((dimPart sX d).ι ≫ f) ⁻¹ᵁ dimPart sP d with hA
  set φ := ((dimPart sX d).ι ≫ f) ∣_ dimPart sP d with hφ
  have ha : cographPiece k sX sP f hf d d ≫ pullback.snd (partBase sX d) (partBase sP d) = φ :=
    cographPiece_snd k sX sP f hf d d
  have hb : graphPiece k sP sX f hf d d ≫ pullback.fst (partBase sP d) (partBase sX d) = φ :=
    graphPiece_fst k sP sX f hf d d
  let j : A.toScheme ⟶ (Limits.pullback (partBase sX d) (partBase sX d) : Scheme.{u}) :=
    A.ι ≫ graphMorphism (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _)
  have := isClosedImmersion_graphMorphism (partBase sX d) (partBase sX d) (𝟙 _)
    (Category.id_comp _)
  have : IsClosedImmersion A.ι := IsClosedImmersion.of_isPreimmersion A.ι (by
    rw [Scheme.Opens.range_ι, hA, preimage_dimPart_eq_top_of_isOpenImmersion sX sP f hf d]
    exact isClopen_univ.isClosed)
  have : IsClosedImmersion j := by dsimp only [j]; infer_instance
  have hj₁ : j ≫ pullback.fst _ _ = A.ι := by
    simp only [j, Category.assoc, graphMorphism_fst, Category.comp_id]
  obtain ⟨e, he⟩ := exists_iso_compositionFibre_of_eq_mono (cographPiece k sX sP f hf d d)
    (graphPiece k sP sX f hf d d) j ha hb (hj₁.trans (cographPiece_fst k sX sP f hf d d).symm)
    (by
      simp only [j, Category.assoc, graphMorphism_snd, Category.comp_id, graphPiece_snd]
      rfl)
  have hjb : j ≫ prodBase (partBase sX d) (partBase sX d) = A.ι ≫ partBase sX d := by
    rw [prodBase, ← Category.assoc, hj₁]
  have hrel := relativeDimension_preimage_dimPart k sX sP f d d
  rw [cographBlock, graphBlock, composition_tmul, one_mul,
    compositionInt_smoothTransversal k (partBase sX d) (partBase sP d) (partBase sX d)
      (relativeDimension_partBase sX d) (relativeDimension_partBase sP d)
      (relativeDimension_partBase sX d) 0 0 (cographPiece k sX sP f hf d d)
      (graphPiece k sP sX f hf d d) j e he (cographPiece_prodBase k sX sP f hf d d)
      (graphPiece_prodBase k sP sX f hf d d) hjb hrel hrel hrel (by simp) (by simp) (by simp),
    graphCorrespondence, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme]
  have hrange : Set.range A.ι = Set.range (𝟙 (dimPart sX d).toScheme) := by
    rw [Scheme.Opens.range_ι, hA, preimage_dimPart_eq_top_of_isOpenImmersion sX sP f hf d]
    simp
  have hiso : (IsOpenImmersion.isoOfRangeEq A.ι (𝟙 _) hrange).hom = A.ι := by
    simpa using IsOpenImmersion.isoOfRangeEq_hom_fac A.ι (𝟙 _) hrange
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso _ _ j _
    (IsOpenImmersion.isoOfRangeEq A.ι (𝟙 _) hrange) (by rw [hiso])]

omit [IsSeparated sX] [IsSeparated sP] [IsSeparated sZ] in
/-- If the images of `f : X ⟶ P` and `g : Z ⟶ P` are disjoint, then so are those of their
restrictions to the parts over `P_d`. -/
theorem restrict_dimPart_apply_ne (f : X ⟶ P) (g : Z ⟶ P)
    (hfg : Disjoint (Set.range f) (Set.range g)) (d e e' : ℕ)
    (x : (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).toScheme)
    (z : (((dimPart sZ e').ι ≫ g) ⁻¹ᵁ dimPart sP d).toScheme) :
    (((dimPart sX e).ι ≫ f) ∣_ dimPart sP d) x ≠ (((dimPart sZ e').ι ≫ g) ∣_ dimPart sP d) z := by
  intro h
  have h' := congrArg (dimPart sP d).ι h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι, morphismRestrict_ι,
    Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply] at h'
  exact Set.disjoint_left.1 hfg ⟨_, rfl⟩ ⟨_, h'.symm⟩

/-- **The transposed graph of `f` followed by the graph of `g` vanishes, blockwise, when the images
of `f` and `g` are disjoint**: the fibre product over `P_d` is empty. -/
theorem composition_cographBlock_graphBlock_of_disjoint [IsProper sP] (f : X ⟶ P) (g : Z ⟶ P)
    (hf : f ≫ sP = sX) (hg : g ≫ sP = sZ) (hfg : Disjoint (Set.range f) (Set.range g))
    (d e : ℕ) :
    composition k (partBase sX d) (partBase sP d) (partBase sZ e) (canonicalDiagonalClassFamily k)
        (relativeDimension_partBase sX d) (relativeDimension_partBase sP d)
        (relativeDimension_partBase sZ e) 0 0 (cographBlock k sX sP f hf d d)
        (graphBlock k sP sZ g hg d e) = 0 := by
  have : IsEmpty
      (compositionFibre (cographPiece k sX sP f hf d d) (graphPiece k sP sZ g hg d e)) :=
    ⟨fun w ↦ by
      have hc : pullback.fst (cographPiece k sX sP f hf d d ≫
          pullback.snd (partBase sX d) (partBase sP d)) (graphPiece k sP sZ g hg d e ≫
            pullback.fst (partBase sP d) (partBase sZ e)) ≫
            (((dimPart sX d).ι ≫ f) ∣_ dimPart sP d) =
          pullback.snd _ _ ≫ (((dimPart sZ e).ι ≫ g) ∣_ dimPart sP d) := by
        rw [← cographPiece_snd, ← graphPiece_fst]
        exact pullback.condition
      have h := congrArg (fun t ↦ t w) hc
      simp only [Scheme.Hom.comp_apply] at h
      exact restrict_dimPart_apply_ne k sX sP sZ f g hfg d d e _ _ h⟩
  have hrelX := relativeDimension_preimage_dimPart k sX sP f d d
  have hrelZ := relativeDimension_preimage_dimPart k sZ sP g d e
  rw [cographBlock, graphBlock, composition_tmul, one_mul,
    DiagonalClassFamily.ProperIntersectionFormula.compositionInt_closedSubscheme k
      (partBase sX d) (partBase sP d) (partBase sZ e)
      (canonicalDiagonalClassFamily_properIntersectionFormula k) (relativeDimension_partBase sX d)
      (relativeDimension_partBase sP d)
      (relativeDimension_partBase sZ e) 0 0 (cographPiece k sX sP f hf d d)
      (graphPiece k sP sZ g hg d e)
      (fun T ↦ by
        rw [deltaDimension_congr (cographPiece_prodBase k sX sP f hf d d), sub_zero]
        exact deltaDimension_irreducibleComponent_of_relativeDimension k _ d hrelX T)
      (fun T ↦ by
        rw [deltaDimension_congr (graphPiece_prodBase k sP sZ g hg d e), sub_zero]
        exact deltaDimension_irreducibleComponent_of_relativeDimension k _ e hrelZ T)
      (schemeDeltaDimension_le_of_forall_irreducibleComponent _ fun V ↦
        isEmptyElim (V.2.1.nonempty.some))
      (fun w ↦ isEmptyElim w),
    cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty, QuotientAddGroup.mk_zero,
    TensorProduct.tmul_zero]

/-- **The graph of an open and closed immersion followed by its transposed graph, blockwise**:
`[Γ_fᵗ ∩ (X_e × P_e)] ∘ [Γ_f ∩ (P_e × X_e)]` is the class of the piece `X_e ⟶ P_e` of the
diagonal of `P_e`; the fibre product over `X_e` of `X_e` with itself is `X_e`. -/
theorem composition_graphBlock_cographBlock_self [IsProper sX] (f : X ⟶ P) [IsOpenImmersion f]
    [IsClosedImmersion f] (hf : f ≫ sP = sX) (e : ℕ) :
    composition k (partBase sP e) (partBase sX e) (partBase sP e) (canonicalDiagonalClassFamily k)
        (relativeDimension_partBase sP e) (relativeDimension_partBase sX e)
        (relativeDimension_partBase sP e) 0 0 (graphBlock k sP sX f hf e e)
        (cographBlock k sX sP f hf e e) =
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (partBase sP e) (partBase sP e))
        ((((dimPart sX e).ι ≫ f) ∣_ dimPart sP e) ≫
          graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _))
        ((e : ℤ) - (0 + 0))) := by
  set A := ((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP e with hA
  set φ := ((dimPart sX e).ι ≫ f) ∣_ dimPart sP e with hφ
  have ha : graphPiece k sP sX f hf e e ≫ pullback.snd (partBase sP e) (partBase sX e) = A.ι :=
    graphPiece_snd k sP sX f hf e e
  have hb : cographPiece k sX sP f hf e e ≫ pullback.fst (partBase sX e) (partBase sP e) = A.ι :=
    cographPiece_fst k sX sP f hf e e
  let j : A.toScheme ⟶ (Limits.pullback (partBase sP e) (partBase sP e) : Scheme.{u}) :=
    φ ≫ graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _)
  have := isClosedImmersion_graphMorphism (partBase sP e) (partBase sP e) (𝟙 _)
    (Category.id_comp _)
  obtain ⟨ε, hε⟩ := exists_iso_compositionFibre_of_eq_mono (graphPiece k sP sX f hf e e)
    (cographPiece k sX sP f hf e e) j ha hb
    (by
      simp only [j, Category.assoc, graphMorphism_fst, Category.comp_id, graphPiece_fst]
      rfl)
    (by
      simp only [j, Category.assoc, graphMorphism_snd, Category.comp_id, cographPiece_snd]
      rfl)
  have hjb : j ≫ prodBase (partBase sP e) (partBase sP e) = A.ι ≫ partBase sX e :=
    calc j ≫ prodBase (partBase sP e) (partBase sP e)
        = φ ≫ (graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _) ≫
            pullback.fst (partBase sP e) (partBase sP e)) ≫ partBase sP e := by
          simp only [j, prodBase, Category.assoc]
      _ = (φ ≫ (dimPart sP e).ι) ≫ sP := by
          rw [graphMorphism_fst, Category.id_comp, partBase, Category.assoc]
      _ = A.ι ≫ partBase sX e := by
          rw [hφ, morphismRestrict_ι, partBase, Category.assoc, Category.assoc, hf]
  have hrel := relativeDimension_preimage_dimPart k sX sP f e e
  rw [cographBlock, graphBlock, composition_tmul, one_mul,
    compositionInt_smoothTransversal k (partBase sP e) (partBase sX e) (partBase sP e)
      (relativeDimension_partBase sP e) (relativeDimension_partBase sX e)
      (relativeDimension_partBase sP e) 0 0 (graphPiece k sP sX f hf e e)
      (cographPiece k sX sP f hf e e) j ε hε (graphPiece_prodBase k sP sX f hf e e)
      (cographPiece_prodBase k sX sP f hf e e) hjb hrel hrel hrel (by simp) (by simp) (by simp)]

omit [IsSeparated sX] [IsSeparated sP] [IsSeparated sZ] in
/-- A point of `P_d` in the image of an open immersion `f : X ⟶ P` over `k` is in the image of
the restriction of `f` to the parts over `P_d`. -/
theorem mem_range_restrict_dimPart (f : X ⟶ P) [IsOpenImmersion f] (hf : f ≫ sP = sX) (d : ℕ)
    (w : (dimPart sP d).toScheme) (hw : (dimPart sP d).ι w ∈ Set.range f) :
    w ∈ Set.range (((dimPart sX d).ι ≫ f) ∣_ dimPart sP d) := by
  obtain ⟨x, hx⟩ := hw
  have hwmem : (dimPart sP d).ι w ∈ dimPart sP d := by
    rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
  have hxd : x ∈ dimPart sX d := by
    rw [mem_dimPart_iff_of_isOpenImmersion sX sP f hf, hx]; exact hwmem
  obtain ⟨y, rfl⟩ : x ∈ Set.range (dimPart sX d).ι := by rw [Scheme.Opens.range_ι]; exact hxd
  have hy : y ∈ ((dimPart sX d).ι ≫ f) ⁻¹ᵁ dimPart sP d := by
    show ((dimPart sX d).ι ≫ f) y ∈ dimPart sP d
    rw [Scheme.Hom.comp_apply, hx]; exact hwmem
  obtain ⟨z, rfl⟩ : y ∈ Set.range (((dimPart sX d).ι ≫ f) ⁻¹ᵁ dimPart sP d).ι := by
    rw [Scheme.Opens.range_ι]; exact hy
  refine ⟨z, ?_⟩
  apply (dimPart sP d).ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    hx]

omit [IsSeparated sX] [IsSeparated sZ] in
/-- **The diagonal of `P_e` is the sum of its pieces over two complementary open and closed
subschemes**: if `f : X ⟶ P` and `g : Z ⟶ P` are open immersions over `k` with complementary
images, the class of the diagonal of `P_e` is the sum of the classes of its pieces `X_e ⟶ P_e` and
`Z_e ⟶ P_e`. -/
theorem graphCorrespondence_id_eq_add (f : X ⟶ P) (g : Z ⟶ P) [IsOpenImmersion f]
    [IsOpenImmersion g] [IsClosedImmersion f] [IsClosedImmersion g] (hf : f ≫ sP = sX)
    (hg : g ≫ sP = sZ) (hfg : IsCompl (Set.range f) (Set.range g)) (e : ℕ) :
    (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (partBase sP e) (partBase sP e))
        ((((dimPart sX e).ι ≫ f) ∣_ dimPart sP e) ≫
          graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _))
        ((e : ℤ) - (0 + 0))) +
      (1 : ℚ) ⊗ₜ[ℤ] QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (prodBase (partBase sP e) (partBase sP e))
        ((((dimPart sZ e).ι ≫ g) ∣_ dimPart sP e) ≫
          graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _))
        ((e : ℤ) - (0 + 0))) =
      correspondenceCongr k (partBase sP e) (partBase sP e) (add_zero 0).symm
        (graphCorrespondence (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _) e) := by
  let F : Bool → Scheme.{u} := fun b ↦
    cond b (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP e).toScheme
      (((dimPart sZ e).ι ≫ g) ⁻¹ᵁ dimPart sP e).toScheme
  let j : ∀ b, F b ⟶ (dimPart sP e).toScheme := fun b ↦
    match b with
    | true => ((dimPart sX e).ι ≫ f) ∣_ dimPart sP e
    | false => ((dimPart sZ e).ι ≫ g) ∣_ dimPart sP e
  have : ∀ b, IsOpenImmersion (j b) := fun b ↦ by cases b <;> (dsimp [j]; infer_instance)
  have : ∀ b, IsClosedImmersion (j b ≫
      graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _)) :=
    fun b ↦ by cases b <;> (dsimp [j]; infer_instance)
  have hsum := cycleAssociatedToClosedSubscheme_eq_sum_of_isOpenImmersion
    (prodBase (partBase sP e) (partBase sP e))
    (graphMorphism (partBase sP e) (partBase sP e) (𝟙 _) (Category.id_comp _)) Finset.univ j
    (fun w ↦ by
      have hw : (dimPart sP e).ι w ∈ Set.range f ∪ Set.range g :=
        (hfg.sup_eq_top.symm ▸ Set.mem_univ ((dimPart sP e).ι w) :
          (dimPart sP e).ι w ∈ Set.range f ⊔ Set.range g)
      rcases hw with hw | hw
      · exact ⟨true, Finset.mem_univ _, mem_range_restrict_dimPart k sX sP f hf e w hw⟩
      · exact ⟨false, Finset.mem_univ _, mem_range_restrict_dimPart k sZ sP g hg e w hw⟩)
    (fun b _ b' _ hbb' ↦ by
      cases b <;> cases b'
      · exact absurd rfl hbb'
      · exact Set.disjoint_left.2 fun _ ⟨z, hz⟩ ⟨x, hx⟩ ↦
          restrict_dimPart_apply_ne k sX sP sZ f g hfg.disjoint e e e x z (hx.trans hz.symm)
      · exact Set.disjoint_left.2 fun _ ⟨x, hx⟩ ⟨z, hz⟩ ↦
          restrict_dimPart_apply_ne k sX sP sZ f g hfg.disjoint e e e x z (hx.trans hz.symm)
      · exact absurd rfl hbb')
    ((e : ℤ) - (0 + 0))
  rw [Fintype.sum_bool] at hsum
  rw [graphCorrespondence, correspondenceCongr_tmul,
    chowGroupDegreeEquiv_mk_cycleAssociatedToClosedSubscheme, ← TensorProduct.tmul_add,
    ← QuotientAddGroup.mk_add, ← hsum]

end Blocks

/-! ### The relations in mixed dimension -/

section Relations

variable (k : Type u) [Field k] {X P Z : Scheme.{u}}
  (sX : X ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S)
  (sZ : Z ⟶ (fieldChowSituation k).S)
  [Smooth sX] [Smooth sP] [Smooth sZ] [IsSeparated sX] [IsSeparated sP] [IsSeparated sZ]

omit [IsSeparated sX] in
/-- The block `(e, d)` of the transposed graph vanishes when `f` maps no point of `X_e` into
`P_d`. -/
theorem cographBlock_eq_zero (f : X ⟶ P) (hf : f ≫ sP = sX) {e d : ℕ}
    (h : ∀ x : X, x ∈ dimPart sX e → f x ∉ dimPart sP d) :
    cographBlock k sX sP f hf e d = 0 := by
  have : IsEmpty (((dimPart sX e).ι ≫ f) ⁻¹ᵁ dimPart sP d).toScheme :=
    ⟨fun x ↦ h x.1.1 x.1.2 x.2⟩
  rw [cographBlock, cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty, QuotientAddGroup.mk_zero,
    TensorProduct.tmul_zero]

/-- `[Γ_fᵗ]` is the sum of its diagonal blocks over any finite set of indices containing those of
the nonempty parts of `X`. -/
theorem cographCorr_eq_sum [QuasiCompact sX] (f : X ⟶ P) (hf : f ≫ sP = sX) {E : Finset ℕ}
    (hE : ∀ e, (dimPart sX e : Set X).Nonempty → e ∈ E) :
    cographCorr k sX sP f hf =
      ∑ e ∈ E, DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ e (cographBlock k sX sP f hf e e)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  unfold cographCorr
  refine Finset.sum_subset (fun e he ↦ hE e ((finite_setOf_nonempty_dimPart sX).mem_toFinset.1 he))
    fun e _ he ↦ ?_
  rw [cographBlock_eq_zero k sX sP f hf fun x hx _ ↦
    he ((finite_setOf_nonempty_dimPart sX).mem_toFinset.2 ⟨x, hx⟩), map_zero, map_zero]

/-- Composition of a finite sum of pure blocks with a finite sum of diagonal blocks. -/
theorem comp_sum_lof_lof_sum_lof_lof [IsProper sP] (Δ : DiagonalClassFamily k) (r s : ℤ)
    (D E : Finset ℕ)
    (c : ∀ d e : ℕ, Correspondence (fieldChowSituation k) (partBase sX d) (partBase sP e) e r)
    (c' : ∀ e : ℕ, Correspondence (fieldChowSituation k) (partBase sP e) (partBase sZ e) e s) :
    comp k sX sP sZ Δ r s (∑ d ∈ D, ∑ e ∈ E, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e (c d e)))
        (∑ e ∈ E, DirectSum.lof ℚ ℕ _ e (DirectSum.lof ℚ ℕ _ e (c' e))) =
      ∑ d ∈ D, ∑ e ∈ E, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e
        (composition k (partBase sX d) (partBase sP e) (partBase sZ e) Δ
          (relativeDimension_partBase sX d) (relativeDimension_partBase sP e)
          (relativeDimension_partBase sZ e) r s (c d e) (c' e))) := by
  rw [map_sum (comp k sX sP sZ Δ r s), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [map_sum (comp k sX sP sZ Δ r s), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun e he ↦ ?_
  rw [map_sum, Finset.sum_eq_single_of_mem e he, comp_lof_lof_lof_lof]
  intro e' _ hne
  exact comp_lof_lof_lof_of_ne k sX sP sZ Δ r s d e e' (Ne.symm hne) _ _

omit [Smooth sP] [Smooth sZ] [IsSeparated sP] [IsSeparated sZ] in
/-- `[Δ_X]` is the sum of its diagonal blocks over any finite set of indices containing those of
the nonempty parts of `X`. -/
theorem diagonalCorr_eq_sum [QuasiCompact sX] {D : Finset ℕ}
    (hD : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D) :
    diagonalCorr k sX = ∑ d ∈ D, diagonalBlock k sX d := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  refine Finset.sum_subset (fun d hd ↦ hD d
    ((finite_setOf_nonempty_dimPart sX).mem_toFinset.1 hd)) fun d _ hd ↦ ?_
  have : IsEmpty (dimPart sX d).toScheme := ⟨fun w ↦ hd
    ((finite_setOf_nonempty_dimPart sX).mem_toFinset.2 ⟨(dimPart sX d).ι w, by
      rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩⟩)⟩
  rw [diagonalBlock, graphCorrespondence, cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty,
    QuotientAddGroup.mk_zero, TensorProduct.tmul_zero, map_zero, map_zero]

set_option synthInstance.maxHeartbeats 200000 in
omit [Smooth sP] [Smooth sZ] [IsSeparated sP] [IsSeparated sZ] in
/-- Transport of a sum of diagonal blocks along an equality of degrees is blockwise. -/
theorem corrCongr_sum_diagonalBlock {r : ℤ} (h : 0 = r) (D : Finset ℕ) :
    corrCongr k sX sX h (∑ d ∈ D, diagonalBlock k sX d) =
      ∑ d ∈ D, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ d
        (correspondenceCongr k (partBase sX d) (partBase sX d) h
          (graphCorrespondence (partBase sX d) (partBase sX d) (𝟙 _) (Category.id_comp _) d))) := by
  simp only [map_sum, diagonalBlock, corrCongr_lof_lof]

/-- Along an open immersion, the block `(d, e)` of the graph vanishes for `e ≠ d`. -/
private theorem graphBlock_eq_zero_of_ne (k : Type u) [Field k] {X P : Scheme.{u}}
    (sX : X ⟶ (fieldChowSituation k).S) (sP : P ⟶ (fieldChowSituation k).S)
    [Smooth sX] [Smooth sP] [IsSeparated sP] (f : X ⟶ P) [IsOpenImmersion f]
    (hf : f ≫ sP = sX) {d e : ℕ} (hed : e ≠ d) : graphBlock k sP sX f hf d e = 0 :=
  graphBlock_eq_zero k sP sX f hf fun x hx hfx ↦ hed
    ((isClopenDecomposition_dimPart sX).eq_of_mem hx
      ((mem_dimPart_iff_of_isOpenImmersion sX sP f hf d x).2 hfx))

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **`[Γ_f] ∘ [Γ_fᵗ] = [Δ_X]`** for an open immersion `f : X ⟶ P` of schemes smooth and
separated over `k`, with `P` proper and `X` quasi-compact, the degrees `0 + 0` and `0` being
identified. -/
theorem comp_cographCorr_graphCorr_self [IsProper sP] [QuasiCompact sX] (f : X ⟶ P)
    [IsOpenImmersion f] (hf : f ≫ sP = sX) :
    comp k sX sP sX (canonicalDiagonalClassFamily k) 0 0 (cographCorr k sX sP f hf)
        (graphCorr k sP sX f hf) =
      corrCongr k sX sX (add_zero 0).symm (diagonalCorr k sX) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  set D := (finite_setOf_nonempty_dimPart sX).toFinset with hD
  have hmem : ∀ d, (dimPart sX d : Set X).Nonempty → d ∈ D := fun d h ↦
    (finite_setOf_nonempty_dimPart sX).mem_toFinset.2 h
  rw [cographCorr_eq_sum k sX sP f hf hmem,
    graphCorr_eq_sum k sP sX f hf (D := D) (E := D) (fun d ⟨x, hx⟩ ↦ hmem d ⟨x,
      (mem_dimPart_iff_of_isOpenImmersion sX sP f hf d x).2 hx⟩) hmem,
    map_sum (comp k sX sP sX (canonicalDiagonalClassFamily k) 0 0), LinearMap.sum_apply,
    diagonalCorr, map_sum (corrCongr k sX sX (add_zero (0 : ℤ)).symm)]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [comp_lof_lof_sum_sum k sX sP sX _ 0 0 d d _ hd D, Finset.sum_eq_single_of_mem d hd,
    composition_cographBlock_graphBlock_self k sX sP f hf d, diagonalBlock, corrCongr_lof_lof]
  intro m _ hm
  rw [graphBlock_eq_zero_of_ne k sX sP f hf hm, map_zero, map_zero, map_zero]

/-- **`[Γ_g] ∘ [Γ_fᵗ] = 0`** when the images of `f : X ⟶ P` and `g : Z ⟶ P` are disjoint. -/
theorem comp_cographCorr_graphCorr_of_disjoint [IsProper sP] [QuasiCompact sX] [QuasiCompact sZ]
    (f : X ⟶ P) (g : Z ⟶ P) (hf : f ≫ sP = sX) (hg : g ≫ sP = sZ)
    (hfg : Disjoint (Set.range f) (Set.range g)) :
    comp k sX sP sZ (canonicalDiagonalClassFamily k) 0 0 (cographCorr k sX sP f hf)
        (graphCorr k sP sZ g hg) = 0 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  set D := (finite_setOf_nonempty_dimPart sX).toFinset ∪
    (finite_setOf_nonempty_preimage_dimPart k sP g).toFinset with hD
  set N := (finite_setOf_nonempty_dimPart sZ).toFinset with hN
  rw [cographCorr_eq_sum k sX sP f hf (E := D) fun e h ↦ Finset.mem_union_left _
      ((finite_setOf_nonempty_dimPart sX).mem_toFinset.2 h),
    graphCorr_eq_sum k sP sZ g hg (D := D) (E := N)
      (fun d h ↦ Finset.mem_union_right _
        ((finite_setOf_nonempty_preimage_dimPart k sP g).mem_toFinset.2 h))
      (fun m h ↦ (finite_setOf_nonempty_dimPart sZ).mem_toFinset.2 h),
    map_sum (comp k sX sP sZ (canonicalDiagonalClassFamily k) 0 0), LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦ ?_
  rw [comp_lof_lof_sum_sum k sX sP sZ _ 0 0 d d _ hd N]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [composition_cographBlock_graphBlock_of_disjoint k sX sP sZ f g hf hg hfg d m, map_zero,
    map_zero]

omit [Smooth sZ] [IsSeparated sZ] in
/-- `[Γ_fᵗ] ∘ [Γ_f]`, for an open immersion `f : X ⟶ P`, is the sum of the diagonal block
composites `[Γ_fᵗ ∩ (X_d × P_d)] ∘ [Γ_f ∩ (P_d × X_d)]` over any finite set of indices containing
those of the nonempty parts of `P`. -/
theorem comp_graphCorr_cographCorr_eq_sum [IsProper sX] [QuasiCompact sP] (f : X ⟶ P)
    [IsOpenImmersion f] (hf : f ≫ sP = sX) {D : Finset ℕ}
    (hD : ∀ d, (dimPart sP d : Set P).Nonempty → d ∈ D) :
    comp k sP sX sP (canonicalDiagonalClassFamily k) 0 0 (graphCorr k sP sX f hf)
        (cographCorr k sX sP f hf) =
      ∑ d ∈ D, DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ d
        (composition k (partBase sP d) (partBase sX d) (partBase sP d)
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase sP d)
          (relativeDimension_partBase sX d) (relativeDimension_partBase sP d) 0 0
          (graphBlock k sP sX f hf d d) (cographBlock k sX sP f hf d d))) := by
  have hmemX : ∀ e, (dimPart sX e : Set X).Nonempty → e ∈ D := fun e ⟨x, hx⟩ ↦
    hD e ⟨f x, (mem_dimPart_iff_of_isOpenImmersion sX sP f hf e x).1 hx⟩
  have hmemfX : ∀ d, (f ⁻¹ᵁ dimPart sP d : Set X).Nonempty → d ∈ D := fun d ⟨x, hx⟩ ↦
    hD d ⟨f x, hx⟩
  rw [graphCorr_eq_sum k sP sX f hf hmemfX hmemX, cographCorr_eq_sum k sX sP f hf hmemX,
    comp_sum_lof_lof_sum_lof_lof]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  refine Finset.sum_eq_single_of_mem d hd fun e _ hne ↦ ?_
  rw [graphBlock_eq_zero_of_ne k sX sP f hf hne, LinearMap.map_zero₂, map_zero, map_zero]

/-- The `d`-th diagonal block of `[Γ_fᵗ] ∘ [Γ_f] + [Γ_gᵗ] ∘ [Γ_g]` is `[Δ_{P_d}]`, for open and
closed immersions `f`, `g` with complementary images. -/
theorem composition_graphBlock_cographBlock_add [IsProper sX] [IsProper sZ] (f : X ⟶ P)
    (g : Z ⟶ P) [IsOpenImmersion f] [IsOpenImmersion g] [IsClosedImmersion f]
    [IsClosedImmersion g] (hf : f ≫ sP = sX) (hg : g ≫ sP = sZ)
    (hfg : IsCompl (Set.range f) (Set.range g)) (d : ℕ) :
    composition k (partBase sP d) (partBase sX d) (partBase sP d)
        (canonicalDiagonalClassFamily k) (relativeDimension_partBase sP d)
        (relativeDimension_partBase sX d) (relativeDimension_partBase sP d) 0 0
        (graphBlock k sP sX f hf d d) (cographBlock k sX sP f hf d d) +
      composition k (partBase sP d) (partBase sZ d) (partBase sP d)
        (canonicalDiagonalClassFamily k) (relativeDimension_partBase sP d)
        (relativeDimension_partBase sZ d) (relativeDimension_partBase sP d) 0 0
        (graphBlock k sP sZ g hg d d) (cographBlock k sZ sP g hg d d) =
      correspondenceCongr k (partBase sP d) (partBase sP d) (add_zero 0).symm
        (graphCorrespondence (partBase sP d) (partBase sP d) (𝟙 _) (Category.id_comp _) d) := by
  rw [composition_graphBlock_cographBlock_self k sX sP f hf d,
    composition_graphBlock_cographBlock_self k sZ sP g hg d]
  exact graphCorrespondence_id_eq_add k sX sP sZ f g hf hg hfg d

/-- **`[Γ_fᵗ] ∘ [Γ_f] + [Γ_gᵗ] ∘ [Γ_g] = [Δ_P]`** for open and closed immersions `f : X ⟶ P`
and `g : Z ⟶ P` over `k` with complementary images, `X` and `Z` proper, the degrees `0 + 0` and
`0` being identified. -/
theorem comp_graphCorr_cographCorr_add [IsProper sX] [IsProper sZ] [QuasiCompact sP]
    (f : X ⟶ P) (g : Z ⟶ P) [IsOpenImmersion f] [IsOpenImmersion g] [IsClosedImmersion f]
    [IsClosedImmersion g] (hf : f ≫ sP = sX) (hg : g ≫ sP = sZ)
    (hfg : IsCompl (Set.range f) (Set.range g)) :
    comp k sP sX sP (canonicalDiagonalClassFamily k) 0 0 (graphCorr k sP sX f hf)
        (cographCorr k sX sP f hf) +
      comp k sP sZ sP (canonicalDiagonalClassFamily k) 0 0 (graphCorr k sP sZ g hg)
        (cographCorr k sZ sP g hg) =
      corrCongr k sP sP (add_zero 0).symm (diagonalCorr k sP) := by
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace sP
  have hmem : ∀ d, (dimPart sP d : Set P).Nonempty →
      d ∈ (finite_setOf_nonempty_dimPart sP).toFinset := fun d h ↦
    (finite_setOf_nonempty_dimPart sP).mem_toFinset.2 h
  rw [comp_graphCorr_cographCorr_eq_sum k sX sP f hf hmem,
    comp_graphCorr_cographCorr_eq_sum k sZ sP g hg hmem, ← Finset.sum_add_distrib,
    diagonalCorr_eq_sum k sP hmem, corrCongr_sum_diagonalBlock]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← map_add, ← map_add, composition_graphBlock_cographBlock_add k sX sP sZ f g hf hg hfg d]

end Relations

/-! ### The relations in the category of correspondences -/

section Category

open ChowMotiveCat

variable {k : Type u} [Field k] {X P Z : (SmoothProjectiveScheme k).FullSubcategory}

/-- The transposed graph `[Γ_fᵗ] ∈ Corr⁰(X, P)` of a morphism `f : X ⟶ P` of smooth projective
schemes over `k`. -/
def cographCorrespondenceSP (f : X ⟶ P) : SmoothProjectiveCorr X P 0 :=
  (SmoothProjectiveCorr.toCorr X P 0).symm
    (cographCorr k X.obj.hom P.obj.hom f.hom.left (Over.w f.hom))

/-- The transposed graph `[Γ_fᵗ] ∈ Corr⁰(X, P)` of a morphism `f : X ⟶ P` of smooth projective
schemes over `k`, as a morphism `X ⟶ P` of the category of correspondences. -/
def cographHom (f : X ⟶ P) :
    (GradedCompositionData.Obj.mk X : (canonicalCorrespondenceCompositionData k).Obj) ⟶
      GradedCompositionData.Obj.mk P :=
  homOf 0 (cographCorrespondenceSP f)

/-- The transposed graph `[Γ_fᵗ]` lies in degree `0` of the category of correspondences. -/
theorem cographHom_mem_grade (f : X ⟶ P) :
    cographHom f ∈ GradedCategory.grade (R := ℚ) _ _ 0 :=
  homOf_mem_grade _

/-- A degree-`(0 + 0)` correspondence transported from degree `0` is the same morphism of the
category of correspondences. -/
theorem homOf_corrCongr {Q : (SmoothProjectiveScheme k).FullSubcategory}
    (c : Corr k P.obj.hom Q.obj.hom 0) :
    homOf (0 + 0) ((SmoothProjectiveCorr.toCorr P Q (0 + 0)).symm
        (corrCongr k P.obj.hom Q.obj.hom (add_zero 0).symm c)) =
      homOf 0 ((SmoothProjectiveCorr.toCorr P Q 0).symm c) := by
  rw [homOf, homOf, DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact of_toCorr_symm_corrCongr (add_zero 0).symm ((SmoothProjectiveCorr.toCorr P Q 0).symm c)

/-- **`[Γ_f] ∘ [Γ_fᵗ] = 1`** in the category of correspondences, for `f : X ⟶ P` an open
immersion of smooth projective schemes over `k`. -/
theorem cographHom_comp_graph_self (f : X ⟶ P) [IsOpenImmersion f.hom.left] :
    cographHom f ≫ homOf 0 (graphCorrespondenceSP f) = 𝟙 (GradedCompositionData.Obj.mk X) := by
  rw [cographHom, homOf_comp_homOf, id_eq_homOf, correspondenceDiagonal, ← homOf_corrCongr,
    ← comp_cographCorr_graphCorr_self k X.obj.hom P.obj.hom f.hom.left (Over.w f.hom)]
  rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- **`[Γ_g] ∘ [Γ_fᵗ] = 0`** in the category of correspondences, for `f : X ⟶ P` and
`g : Z ⟶ P` with disjoint images. -/
theorem cographHom_comp_graph_of_disjoint (f : X ⟶ P) (g : Z ⟶ P)
    (hfg : Disjoint (Set.range f.hom.left) (Set.range g.hom.left)) :
    cographHom f ≫ homOf 0 (graphCorrespondenceSP g) = 0 := by
  rw [cographHom, homOf_comp_homOf]
  show homOf (0 + 0) ((SmoothProjectiveCorr.toCorr X Z (0 + 0)).symm
    (comp k X.obj.hom P.obj.hom Z.obj.hom (canonicalDiagonalClassFamily k) 0 0
      (cographCorr k X.obj.hom P.obj.hom f.hom.left (Over.w f.hom))
      (graphCorr k P.obj.hom Z.obj.hom g.hom.left (Over.w g.hom)))) = 0
  rw [comp_cographCorr_graphCorr_of_disjoint k X.obj.hom P.obj.hom Z.obj.hom f.hom.left g.hom.left
    (Over.w f.hom) (Over.w g.hom) hfg, map_zero, map_zero]

/-- **`[Γ_fᵗ] ∘ [Γ_f] + [Γ_gᵗ] ∘ [Γ_g] = 1`** in the category of correspondences, for
`f : X ⟶ P` and `g : Z ⟶ P` open and closed immersions with complementary images. -/
theorem graph_comp_cographHom_add (f : X ⟶ P) (g : Z ⟶ P) [IsOpenImmersion f.hom.left]
    [IsOpenImmersion g.hom.left] [IsClosedImmersion f.hom.left] [IsClosedImmersion g.hom.left]
    (hfg : IsCompl (Set.range f.hom.left) (Set.range g.hom.left)) :
    homOf 0 (graphCorrespondenceSP f) ≫ cographHom f +
        homOf 0 (graphCorrespondenceSP g) ≫ cographHom g =
      𝟙 (GradedCompositionData.Obj.mk P) := by
  rw [cographHom, cographHom, homOf_comp_homOf, homOf_comp_homOf, ← map_add, id_eq_homOf,
    correspondenceDiagonal, ← homOf_corrCongr,
    ← comp_graphCorr_cographCorr_add k X.obj.hom P.obj.hom Z.obj.hom f.hom.left g.hom.left
      (Over.w f.hom) (Over.w g.hom) hfg]
  rfl

end Category

/-! ### The motive of a disjoint union -/

namespace ChowMotiveCat

open CategoryTheory.GradedCategory Opposite

variable {k : Type u} [Field k] {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    {c : BinaryCofan X Y}

/-- The morphism `h(X) ⟶ h(P)` of motives given by the transposed graph `[Γ_fᵗ]` of
`f : X ⟶ P`. -/
def cographMap {P : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ P) :
    (h k).obj (op X) ⟶ (h k).obj (op P) :=
  ⟨cographHom f, cographHom_mem_grade f, Category.id_comp _, Category.comp_id _⟩

/-- The underlying correspondence of `cographMap f` is `[Γ_fᵗ]`. -/
@[simp]
theorem cographMap_val {P : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ P) :
    (cographMap f).val = cographHom f :=
  rfl

/-- The morphism `h(P) ⟶ h(Q)` of motives given by the graph `[Γ_f]` of `f : Q ⟶ P`; it is
`h(f)` (`Stacks.WeilCohomology.ChowMotiveCat.graphMap_eq`). -/
def graphMap {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) :
    (h k).obj (op P) ⟶ (h k).obj (op Q) :=
  ⟨homOf 0 (graphCorrespondenceSP f), homOf_mem_grade _, Category.id_comp _, Category.comp_id _⟩

/-- The morphism of motives given by the graph `[Γ_f]` is `h(f)`. -/
theorem graphMap_eq {P Q : (SmoothProjectiveScheme k).FullSubcategory} (f : Q ⟶ P) : graphMap f =
    (h k).map f.op :=
  TwistedKaroubi.hom_ext (by
    show homOf 0 (graphCorrespondenceSP f) = DirectSum.of _ 0 _
    rw [homOf, DirectSum.lof_eq_of]
    rfl)

/-- The projector of `h(X)` is the identity of `X` in the category of correspondences. -/
theorem h_obj_p (P : (SmoothProjectiveScheme k).FullSubcategory) :
    ((h k).obj (op P)).p =
      𝟙 (GradedCompositionData.Obj.mk P : (canonicalCorrespondenceCompositionData k).Obj) :=
  rfl

/-- The two coprojections of a coproduct `X ⨿ Y` of smooth projective schemes have disjoint
images. -/
theorem disjoint_range_inl_inr (hc : IsColimit c) :
    Disjoint (Set.range c.inl.hom.left) (Set.range c.inr.hom.left) :=
  (SmoothProjectiveScheme.isCompl_range_inl_inr hc).disjoint

/-- The underlying correspondence of `cographMap f ≫ graphMap g` is `[Γ_g] ∘ [Γ_fᵗ]`. -/
theorem cographMap_comp_graphMap_val {P Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ P)
    (g : Z ⟶ P) :
    (cographMap f ≫ graphMap g).val = cographHom f ≫ homOf 0 (graphCorrespondenceSP g) := by
  rw [TwistedKaroubi.comp_val]
  rfl

/-- The underlying correspondence of `graphMap f ≫ cographMap g` is `[Γ_gᵗ] ∘ [Γ_f]`. -/
theorem graphMap_comp_cographMap_val {P Z : (SmoothProjectiveScheme k).FullSubcategory} (f : Z ⟶ P)
    (g : Z ⟶ X) :
    (graphMap f ≫ cographMap g).val = homOf 0 (graphCorrespondenceSP f) ≫ cographHom g := by
  rw [TwistedKaroubi.comp_val]
  rfl

/-- `[Γ_f] ∘ [Γ_fᵗ] = 1` in `M_k`, for `f` an open immersion. -/
theorem cographMap_comp_graphMap_self {P : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ P)
    [IsOpenImmersion f.hom.left] : cographMap f ≫ graphMap f = 𝟙 _ :=
  TwistedKaroubi.hom_ext ((cographMap_comp_graphMap_val f f).trans (cographHom_comp_graph_self f))

/-- `[Γ_g] ∘ [Γ_fᵗ] = 0` in `M_k`, when the images of `f` and `g` are disjoint. -/
theorem cographMap_comp_graphMap_of_disjoint {P Z : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ P)
    (g : Z ⟶ P) (hfg : Disjoint (Set.range f.hom.left) (Set.range g.hom.left)) :
    cographMap f ≫ graphMap g = 0 :=
  TwistedKaroubi.hom_ext ((cographMap_comp_graphMap_val f g).trans
    (cographHom_comp_graph_of_disjoint f g hfg))

/-- `[Γ_fᵗ] ∘ [Γ_f] + [Γ_gᵗ] ∘ [Γ_g] = 1` in `M_k`, for open and closed immersions with
complementary images. -/
theorem graphMap_comp_cographMap_add {P Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ P)
    (g : Z ⟶ P)
    [IsOpenImmersion f.hom.left] [IsOpenImmersion g.hom.left] [IsClosedImmersion f.hom.left]
    [IsClosedImmersion g.hom.left] (hfg : IsCompl (Set.range f.hom.left) (Set.range g.hom.left)) :
    graphMap f ≫ cographMap f + graphMap g ≫ cographMap g = 𝟙 _ :=
  TwistedKaroubi.hom_ext (by
    rw [TwistedKaroubi.add_val, graphMap_comp_cographMap_val, graphMap_comp_cographMap_val]
    exact graph_comp_cographHom_add f g hfg)

/-- **A disjoint union decomposition gives a direct sum of motives.** For open and closed
immersions `f : X ⟶ P`, `g : Y ⟶ P` of smooth projective schemes over `k` with complementary
images, `h(P)` is a direct sum of `h(X)` and `h(Y)`: the projections are the graphs `[Γ_f] = h(f)`,
`[Γ_g] = h(g)` (`Stacks.WeilCohomology.ChowMotiveCat.graphMap_eq`) and the inclusions are the
transposed graphs. -/
def biproductDataOfIsCompl {P : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ P) (g : Y ⟶ P)
    [IsOpenImmersion f.hom.left] [IsOpenImmersion g.hom.left] [IsClosedImmersion f.hom.left]
    [IsClosedImmersion g.hom.left] (hfg : IsCompl (Set.range f.hom.left) (Set.range g.hom.left)) :
    BinaryBiproductData ((h k).obj (op X)) ((h k).obj (op Y)) where
  bicone :=
    { pt := (h k).obj (op P)
      fst := graphMap f
      snd := graphMap g
      inl := cographMap f
      inr := cographMap g
      inl_fst := cographMap_comp_graphMap_self f
      inl_snd := cographMap_comp_graphMap_of_disjoint f g hfg.disjoint
      inr_fst := cographMap_comp_graphMap_of_disjoint g f hfg.disjoint.symm
      inr_snd := cographMap_comp_graphMap_self g }
  isBilimit := isBinaryBilimitOfTotal _ (by
    apply TwistedKaroubi.hom_ext
    dsimp only
    rw [TwistedKaroubi.add_val, graphMap_comp_cographMap_val, graphMap_comp_cographMap_val,
      TwistedKaroubi.id_val, h_obj_p]
    exact graph_comp_cographHom_add f g hfg)

/-- **Stacks Project, Tag 0FGF, equal twists, for the motives of schemes.** For any coproduct
`X ⨿ Y` of smooth projective schemes over `k`, `h(X ⨿ Y)` is a direct sum of `h(X)` and `h(Y)` in
the category of Chow motives, with projections `h(i)`, `h(j)` for the coprojections `i`, `j` and
inclusions their transposed graphs: the fields of the bicone are, by definition, `graphMap c.inl`,
`graphMap c.inr`, `cographMap c.inl`, `cographMap c.inr`, with `graphMap f = h(f)`
(`Stacks.WeilCohomology.ChowMotiveCat.graphMap_eq`). -/
def coprodBiproductData (hc : IsColimit c) :
    BinaryBiproductData ((h k).obj (op X)) ((h k).obj (op Y)) :=
  haveI := SmoothProjectiveScheme.isOpenImmersion_inl hc
  haveI := SmoothProjectiveScheme.isOpenImmersion_inr hc
  haveI := SmoothProjectiveScheme.isClosedImmersion_inl hc
  haveI := SmoothProjectiveScheme.isClosedImmersion_inr hc
  biproductDataOfIsCompl c.inl c.inr (SmoothProjectiveScheme.isCompl_range_inl_inr hc)

/-- The vertex of the direct sum is `h(X ⨿ Y)`. -/
theorem coprodBiproductData_pt (hc : IsColimit c) :
    (coprodBiproductData hc).bicone.pt = (h k).obj (op c.pt) :=
  rfl

/-- The motives of two smooth projective schemes have a direct sum in `M_k`. -/
theorem hasBinaryBiproduct_h (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    HasBinaryBiproduct ((h k).obj (op X)) ((h k).obj (op Y)) :=
  HasBinaryBiproduct.mk (coprodBiproductData (SmoothProjectiveScheme.isColimitCoprodCofan X Y))

attribute [local instance] hasBinaryBiproduct_h in
/-- **`h(X ⨿ Y) ≅ h(X) ⊞ h(Y)`** in the category of Chow motives, for any coproduct `X ⨿ Y` of
smooth projective schemes over `k`. -/
def hCoprodIsoBiprod (hc : IsColimit c) :
    (h k).obj (op c.pt) ≅ (h k).obj (op X) ⊞ (h k).obj (op Y) :=
  biprod.uniqueUpToIso _ _ (coprodBiproductData hc).isBilimit

end ChowMotiveCat

end Stacks.WeilCohomology

end

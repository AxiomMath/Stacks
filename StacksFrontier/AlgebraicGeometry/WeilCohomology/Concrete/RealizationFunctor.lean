module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesUniversalProperty
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationClopen
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.RealizationCorrespondenceClass
public import StacksFrontier.CategoryTheory.GradedObject.Linear
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The realization of correspondences of degree zero on Weil cohomology

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) satisfying (A), (B) and (C), with
coefficient field `F` of characteristic zero. The proof of Stacks 0FHL first constructs a functor
`G` on the category of smooth projective schemes over `k` with correspondences of degree `0`:
`G(X) = H^*(X)`, and for `c ∈ Corr⁰(X, Y)`

  `G(c)(a) = pr₂,*(γ(c) ∪ pr₁^*a)`.

The source reduces to equidimensional schemes through the decomposition `X = ∐_d X_d` and
`H^*(X) = ∏_d H^*(X_d)` (Stacks 0FHJ). Correspondences of mixed dimension are, by construction,
sums of blocks `c_{d,e} ∈ Corr⁰(X_d, Y_e)` (Section 0FFZ), and accordingly
`G(c) = ∑_{d,e} (Y_e ⊂ Y)_! ∘ G(c_{d,e}) ∘ (X_d ⊂ X)^*`, with `G(c_{d,e})` the action of
Stacks 0FHL between the nonempty equidimensional `X_d`, `Y_e` (`WeilData.blockAct`) and `_!`
extension by zero (`WeilData.extendByZero`).

## Main definitions

* `Stacks.WeilCohomology.WeilData.cohomologyGraded`: `X ↦ (n ↦ H^n(X))`, a graded `F`-vector space.
* `Stacks.WeilCohomology.WeilData.corrMap`: `G(c)` in degree `n`.
* `Stacks.WeilCohomology.WeilData.corrFunctor`: the functor `G` on
  `DegreeZero ℚ (CorrespondenceCategory k)`.

## Main results

* `corrMap_comp`: `G(c' ∘ c) = G(c') ∘ G(c)`, the displayed computation of the source.
* `corrMap_diagonalCorr`: `G([Δ]) = id`, by Stacks 0FHH/0FHG and Stacks 0FHJ.

## References

* [Stacks Project, Tag 0FHL](https://stacks.math.columbia.edu/tag/0FHL)
* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
  CategoryTheory.GradedCategory

universe u w

namespace Stacks.WeilCohomology

namespace SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- The part `X_d` of `X` of dimension `d` (Stacks 02NM), as a smooth projective scheme. -/
abbrev part (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    (SmoothProjectiveScheme k).FullSubcategory :=
  clopenObj X (dimPart X.obj.hom d) ((isClopenDecomposition_dimPart X.obj.hom).isClopen d)

/-- The inclusion `X_d ⟶ X`. -/
abbrev partι (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) : part X d ⟶ X :=
  clopenι X (dimPart X.obj.hom d) ((isClopenDecomposition_dimPart X.obj.hom).isClopen d)

/-- The inclusion `X_d ⟶ X` is a closed immersion. -/
instance (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    IsClosedImmersion (partι X d).hom.left :=
  isClosedImmersion_ι_of_isClopen ((isClopenDecomposition_dimPart X.obj.hom).isClopen d)

/-- A nonempty part `X_d` is nonempty and equidimensional of dimension `d`. -/
theorem isNonemptyEquidimensional_part (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (h : Nonempty (part X d).obj.left) : IsNonemptyEquidimensional (part X d) d :=
  ⟨h, relativeDimension_partBase X.obj.hom d⟩

/-- The image of `X_d ⟶ X` is the open and closed subset `dimPart X d`. -/
theorem range_partι (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    Set.range (partι X d).hom.left = (dimPart X.obj.hom d : Set X.obj.left) :=
  Scheme.Opens.range_ι _

/-- Parts `X_d`, `X_{d'}` of different dimensions have disjoint images in `X`. -/
theorem disjoint_range_partι (X : (SmoothProjectiveScheme k).FullSubcategory) {d d' : ℕ}
    (h : d ≠ d') : Disjoint (Set.range (partι X d).hom.left) (Set.range (partι X d').hom.left) := by
  rw [range_partι, range_partι]
  exact TopologicalSpace.Opens.coe_disjoint.2 ((isClopenDecomposition_dimPart X.obj.hom).disjoint
    _ _ h)

/-- The finitely many dimensions of the nonempty parts of `X`. -/
def partSupport (X : (SmoothProjectiveScheme k).FullSubcategory) : Finset ℕ :=
  haveI : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  (finite_setOf_nonempty_dimPart X.obj.hom).toFinset

/-- `d ∈ partSupport X` exactly when the part of `X` of dimension `d` is nonempty. -/
theorem mem_partSupport {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} :
    d ∈ partSupport X ↔ (dimPart X.obj.hom d : Set X.obj.left).Nonempty := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  exact (finite_setOf_nonempty_dimPart X.obj.hom).mem_toFinset

/-- Every point of `X` lies in the image of `X_d ⟶ X` for some `d ∈ partSupport X`. -/
theorem exists_mem_partSupport (X : (SmoothProjectiveScheme k).FullSubcategory) (x : X.obj.left) :
    ∃ d ∈ partSupport X, x ∈ Set.range (partι X d).hom.left := by
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart X.obj.hom).exists_mem x
  exact ⟨d, mem_partSupport.2 ⟨x, hd⟩, by rw [range_partι]; exact hd⟩

/-- The scheme `X_d` is nonempty if and only if the subset `dimPart X d` of `X` is. -/
theorem nonempty_part_iff {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ} :
    Nonempty (part X d).obj.left ↔ (dimPart X.obj.hom d : Set X.obj.left).Nonempty :=
  ⟨fun ⟨x⟩ ↦ ⟨_, x.2⟩, fun ⟨x, hx⟩ ↦ ⟨⟨x, hx⟩⟩⟩

end SmoothProjectiveScheme

namespace WeilData

open SmoothProjectiveScheme

variable {k : Type u} [Field k] {F : Type w} [Field F] [CharZero F] (W : WeilData k F)

/-- **The cohomology of `X` as a graded `F`-vector space**, `n ↦ H^n(X)`. -/
def cohomologyGraded (X : (SmoothProjectiveScheme k).FullSubcategory) :
    GradedObject ℤ (ModuleCat.{w} F) :=
  fun n ↦ ModuleCat.of F (W.grade X n)

variable {W} (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)

/-- Extension by zero in one degree. -/
def extendDeg {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left]
    [IsClosedImmersion j.hom.left] (n : ℤ) : W.grade V n →ₗ[F] W.grade X n :=
  (extendByZero hA hB hC j).restrict fun _ hx ↦ extendByZero_mem j hx

/-- `extendDeg j n` is `extendByZero j` on `H^n(V)`. -/
@[simp]
theorem coe_extendDeg {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (n : ℤ) (x : W.grade V n) :
    (extendDeg hA hB hC j n x : W.H X) = extendByZero hA hB hC j x :=
  rfl

/-- The action `z ↦ blockAct z` in degree `n`, as an additive map. -/
def blockActHom {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e) (n : ℤ) :
    W.H (prod X Y) →+ (W.grade X n →ₗ[F] W.grade Y n) where
  toFun z := W.blockAct hA.perfectPairing hX hY z n
  map_zero' := blockAct_zero _ _ _ _
  map_add' _ _ := blockAct_add _ _ _ _ _ _

/-- Pre- and postcomposition with linear maps, as an additive map. -/
def compCompHom {M₁ M₂ M₃ M₄ : Type*} [AddCommGroup M₁] [Module F M₁] [AddCommGroup M₂]
    [Module F M₂] [AddCommGroup M₃] [Module F M₃] [AddCommGroup M₄] [Module F M₄]
    (g : M₃ →ₗ[F] M₄) (f : M₁ →ₗ[F] M₂) : (M₂ →ₗ[F] M₃) →+ (M₁ →ₗ[F] M₄) where
  toFun φ := g ∘ₗ φ ∘ₗ f
  map_zero' := by simp
  map_add' φ ψ := by simp [LinearMap.add_comp, LinearMap.comp_add]

open scoped Classical in
/-- **The action of a block** `c ∈ Corr⁰(X_d, Y_e)` on `H^n(X) → H^n(Y)`:
`(Y_e ⊂ Y)_! ∘ G(c) ∘ (X_d ⊂ X)^*`, and `0` when `X_d` or `Y_e` is empty. -/
def blockMap (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ) (r n : ℤ) :
    Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e r →+
      (W.grade X n →ₗ[F] W.grade Y n) :=
  if h : Nonempty (part X d).obj.left ∧ Nonempty (part Y e).obj.left then
    (compCompHom (extendDeg hA hB hC (partι Y e) n) (W.pullDeg (partι X d) n)).comp
      ((blockActHom hA (isNonemptyEquidimensional_part X h.1)
        (isNonemptyEquidimensional_part Y h.2) n).comp (W.corrClass (part X d) (part Y e) e r d))
  else 0

/-- For `X_d` and `Y_e` nonempty, `blockMap` of `c` is `(Y_e ⊂ Y)_! ∘ G(c) ∘ (X_d ⊂ X)^*`. -/
theorem blockMap_of_nonempty {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ} {r : ℤ}
    (n : ℤ) (hX : Nonempty (part X d).obj.left) (hY : Nonempty (part Y e).obj.left)
    (c : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e r) :
    blockMap hA hB hC X Y d e r n c = extendDeg hA hB hC (partι Y e) n ∘ₗ
      W.blockAct hA.perfectPairing (isNonemptyEquidimensional_part X hX)
        (isNonemptyEquidimensional_part Y hY) (W.corrClass (part X d) (part Y e) e r d c) n ∘ₗ
      W.pullDeg (partι X d) n := by
  classical
  rw [blockMap, dif_pos ⟨hX, hY⟩]
  rfl

/-- `blockMap` vanishes when `X_d` is empty. -/
theorem blockMap_of_isEmpty_left {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    {r : ℤ} (n : ℤ) (hX : ¬ Nonempty (part X d).obj.left) :
    blockMap hA hB hC X Y d e r n = 0 := by
  classical
  rw [blockMap, dif_neg fun h ↦ hX h.1]

/-- `blockMap` vanishes when `Y_e` is empty. -/
theorem blockMap_of_isEmpty_right {X Y : (SmoothProjectiveScheme k).FullSubcategory} {d e : ℕ}
    {r : ℤ} (n : ℤ) (hY : ¬ Nonempty (part Y e).obj.left) :
    blockMap hA hB hC X Y d e r n = 0 := by
  classical
  rw [blockMap, dif_neg fun h ↦ hY h.2]

/-- The blocks `Corrʳ(X_d, Y_e)` of `Corrʳ(X, Y)` are the correspondences between the smooth
projective schemes `X_d`, `Y_e`: the identity, between the two ways of writing the parts. -/
def blockEquiv (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ) (r : ℤ) :
    Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e r ≃ₗ[ℚ]
      Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e r :=
  LinearEquiv.refl ℚ _

/-- **`G(c)` in degree `n`** for a correspondence `c ∈ Corr⁰(X, Y)`: the sum of the actions of
its blocks. -/
def corrMap (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ) :
    Corr k X.obj.hom Y.obj.hom r →+ (W.grade X n →ₗ[F] W.grade Y n) :=
  DirectSum.toAddMonoid fun d ↦ DirectSum.toAddMonoid fun e ↦
    (blockMap hA hB hC X Y d e r n).comp (blockEquiv X Y d e r).toAddMonoidHom

/-- On a single block `c ∈ Corrʳ(X_d, Y_e)`, `corrMap` is the action `blockMap` of `c`. -/
theorem corrMap_lof_lof (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ) (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e r) :
    corrMap hA hB hC X Y r n (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) =
      blockMap hA hB hC X Y d e r n (blockEquiv X Y d e r c) := by
  rw [corrMap, DirectSum.lof_eq_of, DirectSum.toAddMonoid_of, DirectSum.lof_eq_of,
    DirectSum.toAddMonoid_of]
  rfl

/-- Restricting an extension by zero to the part it was extended from gives the class back. -/
theorem pullDeg_extendDeg {V X : (SmoothProjectiveScheme k).FullSubcategory} (j : V ⟶ X)
    [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left] (n : ℤ) :
    W.pullDeg j n ∘ₗ extendDeg hA hB hC j n = LinearMap.id :=
  LinearMap.ext fun x ↦ Subtype.ext (pull_extendByZero_self (hA := hA) (hB := hB) (hC := hC) j x)

/-- Restricting an extension by zero to a disjoint part gives zero. -/
theorem pullDeg_comp_extendDeg_of_disjoint {U V X : (SmoothProjectiveScheme k).FullSubcategory}
    (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion j.hom.left] [IsClosedImmersion j.hom.left]
    (hdisj : Disjoint (Set.range i.hom.left) (Set.range j.hom.left)) (n : ℤ) :
    W.pullDeg i n ∘ₗ extendDeg hA hB hC j n = 0 :=
  LinearMap.ext fun x ↦ Subtype.ext
    (pull_extendByZero_of_disjoint (hA := hA) (hB := hB) (hC := hC) i j hdisj x)

/-- A Chow class on an empty scheme vanishes. -/
theorem chowGroup_eq_zero_of_isEmpty {C : ChowSituation.{u}} {P : Scheme.{u}} {sP : P ⟶ C.S}
    [LocallyOfFiniteType sP] (h : P → False) {m : ℤ} (α : chowGroup C sP m) : α = 0 :=
  @Subsingleton.elim _ (@subsingleton_chowGroup_of_isEmpty C P sP _ ⟨h⟩ m) α 0

/-- **The composition law on blocks** (the displayed computation of the proof of Stacks 0FHL):
`G(c' ∘ c) = G(c') ∘ G(c)` for `c ∈ Corr⁰(X_d, Y_e)` and `c' ∈ Corr⁰(Y_e, Z_f)`. -/
theorem blockMap_composition (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) (d e f : ℕ)
    (n : ℤ) (x : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e 0)
    (y : Correspondence (fieldChowSituation k) (part Y e).obj.hom (part Z f).obj.hom f 0) :
    blockMap hA hB hC X Z d f (0 + 0) n
        (composition k (part X d).obj.hom (part Y e).obj.hom (part Z f).obj.hom
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase X.obj.hom d)
          (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Z.obj.hom f) 0 0
          x y) =
      blockMap hA hB hC Y Z e f 0 n y ∘ₗ blockMap hA hB hC X Y d e 0 n x := by
  by_cases hX : Nonempty (part X d).obj.left
  swap
  · rw [blockMap_of_isEmpty_left hA hB hC n hX, blockMap_of_isEmpty_left hA hB hC n hX,
      AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, LinearMap.comp_zero]
  by_cases hZ : Nonempty (part Z f).obj.left
  swap
  · rw [blockMap_of_isEmpty_right hA hB hC n hZ, blockMap_of_isEmpty_right hA hB hC n hZ,
      AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, LinearMap.zero_comp]
  by_cases hY : Nonempty (part Y e).obj.left
  swap
  · have hx : x = 0 := by
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul q α =>
        rw [chowGroup_eq_zero_of_isEmpty
          (fun z ↦ hY ⟨(Limits.pullback.snd (part X d).obj.hom (part Y e).obj.hom) z⟩) α,
          TensorProduct.tmul_zero]
      | add x x' hx hx' => rw [hx, hx', add_zero]
    rw [blockMap_of_isEmpty_right hA hB hC n hY, hx]
    simp only [map_zero, LinearMap.zero_apply, LinearMap.comp_zero]
  have hXd := isNonemptyEquidimensional_part X hX
  have hYe := isNonemptyEquidimensional_part Y hY
  have hZf := isNonemptyEquidimensional_part Z hZ
  rw [blockMap_of_nonempty hA hB hC n hX hZ, blockMap_of_nonempty hA hB hC n hY hZ,
    blockMap_of_nonempty hA hB hC n hX hY]
  have hcomp := blockAct_comp hA.perfectPairing hB.kunnethIsomorphism hB.kunnethTrace hXd hYe hZf
    (W.corrClass_mem (part X d) (part Y e) e 0 d x)
    (W.corrClass_mem (part Y e) (part Z f) f 0 e y) _
    (traceProj_corrClass_composition hA hB hC hXd hYe hZf x y) n
  refine LinearMap.ext fun a ↦ ?_
  have h₁ := LinearMap.congr_fun (pullDeg_extendDeg hA hB hC (partι Y e) n)
    (W.blockAct hA.perfectPairing hXd hYe (W.corrClass (part X d) (part Y e) e 0 d x) n
      (W.pullDeg (partι X d) n a))
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h₁
  simp only [LinearMap.comp_apply]
  rw [h₁]
  exact congrArg (extendDeg hA hB hC (partι Z f) n)
    (LinearMap.congr_fun hcomp (W.pullDeg (partι X d) n a))

/-- Composition of blocks, read in the two ways of writing the parts. -/
theorem blockEquiv_composition (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) (d e f : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (y : Correspondence (fieldChowSituation k) (partBase Y.obj.hom e) (partBase Z.obj.hom f) f 0) :
    blockEquiv X Z d f (0 + 0)
        (composition k (partBase X.obj.hom d) (partBase Y.obj.hom e) (partBase Z.obj.hom f)
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase X.obj.hom d)
          (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Z.obj.hom f) 0 0
          x y) =
      composition k (part X d).obj.hom (part Y e).obj.hom (part Z f).obj.hom
          (canonicalDiagonalClassFamily k) (relativeDimension_partBase X.obj.hom d)
          (relativeDimension_partBase Y.obj.hom e) (relativeDimension_partBase Z.obj.hom f) 0 0
          (blockEquiv X Y d e 0 x) (blockEquiv Y Z e f 0 y) :=
  rfl

/-- Blocks with different middle parts compose to zero. -/
theorem blockMap_comp_blockMap_of_ne (X Y Z : (SmoothProjectiveScheme k).FullSubcategory)
    {d e e' f : ℕ} (n : ℤ) (he : e ≠ e')
    (x : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e 0)
    (y : Correspondence (fieldChowSituation k) (part Y e').obj.hom (part Z f).obj.hom f 0) :
    blockMap hA hB hC Y Z e' f 0 n y ∘ₗ blockMap hA hB hC X Y d e 0 n x = 0 := by
  by_cases hX : Nonempty (part X d).obj.left
  swap
  · rw [blockMap_of_isEmpty_left hA hB hC n hX, AddMonoidHom.zero_apply, LinearMap.comp_zero]
  by_cases hY : Nonempty (part Y e).obj.left
  swap
  · rw [blockMap_of_isEmpty_right hA hB hC n hY, AddMonoidHom.zero_apply, LinearMap.comp_zero]
  by_cases hY' : Nonempty (part Y e').obj.left
  swap
  · rw [blockMap_of_isEmpty_left hA hB hC n hY', AddMonoidHom.zero_apply, LinearMap.zero_comp]
  by_cases hZ : Nonempty (part Z f).obj.left
  swap
  · rw [blockMap_of_isEmpty_right hA hB hC n hZ, AddMonoidHom.zero_apply, LinearMap.zero_comp]
  rw [blockMap_of_nonempty hA hB hC n hY' hZ, blockMap_of_nonempty hA hB hC n hX hY]
  have h₀ := pullDeg_comp_extendDeg_of_disjoint hA hB hC (partι Y e') (partι Y e)
    (disjoint_range_partι Y (Ne.symm he)) n
  refine LinearMap.ext fun a ↦ ?_
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [show W.pullDeg (partι Y e') n (extendDeg hA hB hC (partι Y e) n _) = 0 from
    LinearMap.congr_fun h₀ _, map_zero, map_zero]

/-- If `G(b ∘ a) = G(b) ∘ G(a)` and `G(b ∘ a') = G(b) ∘ G(a')`, then
`G(b ∘ (a + a')) = G(b) ∘ G(a + a')`. -/
theorem corrMap_comp_add_left {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ}
    {a a' : Corr k X.obj.hom Y.obj.hom 0} {b : Corr k Y.obj.hom Z.obj.hom 0}
    (ha : corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a b) =
      corrMap hA hB hC Y Z 0 n b ∘ₗ corrMap hA hB hC X Y 0 n a)
    (ha' : corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a' b) =
      corrMap hA hB hC Y Z 0 n b ∘ₗ corrMap hA hB hC X Y 0 n a') :
    corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 (a + a') b) =
      corrMap hA hB hC Y Z 0 n b ∘ₗ corrMap hA hB hC X Y 0 n (a + a') := by
  simp only [map_add, LinearMap.add_apply, ha, ha', LinearMap.comp_add]

/-- If `G(b ∘ a) = G(b) ∘ G(a)` and `G(b' ∘ a) = G(b') ∘ G(a)`, then
`G((b + b') ∘ a) = G(b + b') ∘ G(a)`. -/
theorem corrMap_comp_add_right {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ}
    {a : Corr k X.obj.hom Y.obj.hom 0} {b b' : Corr k Y.obj.hom Z.obj.hom 0}
    (hb : corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a b) =
      corrMap hA hB hC Y Z 0 n b ∘ₗ corrMap hA hB hC X Y 0 n a)
    (hb' : corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a b') =
      corrMap hA hB hC Y Z 0 n b' ∘ₗ corrMap hA hB hC X Y 0 n a) :
    corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a (b + b')) =
      corrMap hA hB hC Y Z 0 n (b + b') ∘ₗ corrMap hA hB hC X Y 0 n a := by
  simp only [map_add, hb, hb', LinearMap.add_comp]

/-- `G(b ∘ 0) = G(b) ∘ G(0)`. -/
theorem corrMap_comp_zero_left {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ}
    (b : Corr k Y.obj.hom Z.obj.hom 0) :
    corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 0 b) =
      corrMap hA hB hC Y Z 0 n b ∘ₗ corrMap hA hB hC X Y 0 n 0 := by
  rw [LinearMap.map_zero₂, AddMonoidHom.map_zero, AddMonoidHom.map_zero, LinearMap.comp_zero]

/-- `G(0 ∘ a) = G(0) ∘ G(a)`. -/
theorem corrMap_comp_zero_right {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ}
    (a : Corr k X.obj.hom Y.obj.hom 0) :
    corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a 0) =
      corrMap hA hB hC Y Z 0 n 0 ∘ₗ corrMap hA hB hC X Y 0 n a := by
  rw [LinearMap.map_zero, AddMonoidHom.map_zero, AddMonoidHom.map_zero, LinearMap.zero_comp]

/-- `G(y ∘ x) = G(y) ∘ G(x)` for single blocks `x ∈ Corr⁰(X_d, Y_e)` and
`y ∈ Corr⁰(Y_{e'}, Z_f)`. -/
theorem corrMap_comp_lof {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} {n : ℤ} (d e e' f : ℕ)
    (x : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e 0)
    (y : Correspondence (fieldChowSituation k) (partBase Y.obj.hom e') (partBase Z.obj.hom f) f
      0) :
    corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x))
        (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y))) =
      corrMap hA hB hC Y Z 0 n (DirectSum.lof ℚ ℕ _ e' (DirectSum.lof ℚ ℕ _ f y)) ∘ₗ
        corrMap hA hB hC X Y 0 n (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e x)) := by
  rw [corrMap_lof_lof, corrMap_lof_lof]
  by_cases he : e = e'
  · subst he
    rw [comp_lof_lof_lof_lof, corrMap_lof_lof, blockEquiv_composition]
    exact blockMap_composition hA hB hC X Y Z d e f n _ _
  · rw [comp_lof_lof_lof_of_ne k _ _ _ _ 0 0 d e e' he x, map_zero,
      blockMap_comp_blockMap_of_ne hA hB hC X Y Z n he _ _]

/-- **`G(c' ∘ c) = G(c') ∘ G(c)`** for correspondences of degree zero between smooth projective
schemes of mixed dimension: the composition law of the proof of Stacks 0FHL, block by block. -/
theorem corrMap_comp (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (a : Corr k X.obj.hom Y.obj.hom 0) (b : Corr k Y.obj.hom Z.obj.hom 0) :
    corrMap hA hB hC X Z (0 + 0) n (comp k X.obj.hom Y.obj.hom Z.obj.hom
      (canonicalDiagonalClassFamily k) 0 0 a b) =
      corrMap hA hB hC Y Z 0 n b ∘ₗ corrMap hA hB hC X Y 0 n a := by
  induction a using Corr.induction_on with
  | zero => exact corrMap_comp_zero_left hA hB hC b
  | add a a' ha ha' => exact corrMap_comp_add_left hA hB hC ha ha'
  | lof d e x =>
    induction b using Corr.induction_on with
    | zero => exact corrMap_comp_zero_right hA hB hC _
    | add b b' hb hb' => exact corrMap_comp_add_right hA hB hC hb hb'
    | lof e' f y => exact corrMap_comp_lof hA hB hC d e e' f x y

/-! ### The identity -/

include hA hB hC in
/-- **The class of the diagonal correspondence in trace form** (Stacks 0FHG for the diagonal):
`∫_{X × X} γ([Δ]) ∪ v = ∫_X Δ^*v` for `X` nonempty and equidimensional. -/
theorem traceProj_corrClass_graphCorrespondence_id {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) (v : W.H (prod X X)) :
    W.traceProj (prod X X) (d + d) (isNonemptyEquidimensional_prod hX hX)
        (W.corrClass X X d 0 d (graphCorrespondence X.obj.hom X.obj.hom (𝟙 _)
          (Category.id_comp _) d) * v) =
      W.traceProj X d hX (W.pull (diag X) v) :=
  traceProj_corrClass_closedSubscheme hA hB hC hX hX hX (diag X) v

/-- The diagonal block of `[Δ_X]`, read on the part `X_d`. -/
theorem blockEquiv_graphCorrespondence_id (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ) :
    blockEquiv X X d d 0 (graphCorrespondence (partBase X.obj.hom d) (partBase X.obj.hom d) (𝟙 _)
        (Category.id_comp _) d) =
      graphCorrespondence (part X d).obj.hom (part X d).obj.hom (𝟙 _) (Category.id_comp _) d :=
  rfl

/-- **The diagonal acts as the identity on each part** (Stacks 0FHH, 0FHG): for `X_d` nonempty,
`G([Δ_{X_d}])` is `(X_d ⊂ X)_! ∘ (X_d ⊂ X)^*`. -/
theorem blockMap_diagonal (X : (SmoothProjectiveScheme k).FullSubcategory) {d : ℕ}
    (hX : Nonempty (part X d).obj.left) (n : ℤ) :
    blockMap hA hB hC X X d d 0 n (blockEquiv X X d d 0 (graphCorrespondence (partBase X.obj.hom d)
        (partBase X.obj.hom d) (𝟙 _) (Category.id_comp _) d)) =
      extendDeg hA hB hC (partι X d) n ∘ₗ W.pullDeg (partι X d) n := by
  have hXd := isNonemptyEquidimensional_part X hX
  rw [blockMap_of_nonempty hA hB hC n hX hX, blockEquiv_graphCorrespondence_id,
    blockAct_eq_self hA.perfectPairing hXd
      (traceProj_corrClass_graphCorrespondence_id hA hB hC hXd) n,
    LinearMap.id_comp]

/-- **`G([Δ]) = id`**: the identity correspondence acts as the identity (the step "`G([Δ]) = id`
by Lemmas 0FHH and 0FHC" of the proof of Stacks 0FHL), the parts being a finite disjoint cover
(Stacks 0FHJ). -/
theorem corrMap_diagonalCorr (X : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) :
    corrMap hA hB hC X X 0 n (diagonalCorr k X.obj.hom) = LinearMap.id := by
  have : CompactSpace X.obj.left := QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  show corrMap hA hB hC X X 0 n (∑ d ∈ partSupport X, diagonalBlock k X.obj.hom d) = _
  rw [map_sum]
  refine LinearMap.ext fun a ↦ Subtype.ext ?_
  rw [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.id_apply]
  have h := sum_extendByZero_pull (hA := hA) (hB := hB) (hC := hC) (partSupport X) (partι X)
    (exists_mem_partSupport X) (fun s _ t _ hst ↦ disjoint_range_partι X hst) (a : W.H X)
  refine (Finset.sum_congr rfl fun d hd ↦ ?_).trans h
  rw [corrMap_lof_lof, blockMap_diagonal hA hB hC X (nonempty_part_iff.2 (mem_partSupport.1 hd)) n]
  rfl

/-! ### Linearity -/

/-- `blockMap` is `ℚ`-linear in the block. -/
theorem blockMap_smul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (d e : ℕ) (r n : ℤ) (q : ℚ)
    (c : Correspondence (fieldChowSituation k) (part X d).obj.hom (part Y e).obj.hom e r) :
    blockMap hA hB hC X Y d e r n (q • c) = (q : F) • blockMap hA hB hC X Y d e r n c := by
  by_cases hX : Nonempty (part X d).obj.left
  swap
  · rw [blockMap_of_isEmpty_left hA hB hC n hX, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply,
      smul_zero]
  by_cases hY : Nonempty (part Y e).obj.left
  swap
  · rw [blockMap_of_isEmpty_right hA hB hC n hY, AddMonoidHom.zero_apply,
      AddMonoidHom.zero_apply, smul_zero]
  rw [blockMap_of_nonempty hA hB hC n hX hY, blockMap_of_nonempty hA hB hC n hX hY,
    W.corrClass_smul, blockAct_smul, LinearMap.smul_comp, LinearMap.comp_smul]

/-- `G(q • c) = q • G(c)` for a single block `c ∈ Corrʳ(X_d, Y_e)`. -/
theorem corrMap_smul_lof (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ) (q : ℚ)
    (d e : ℕ)
    (c : Correspondence (fieldChowSituation k) (partBase X.obj.hom d) (partBase Y.obj.hom e) e r) :
    corrMap hA hB hC X Y r n (q • DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) =
      (q : F) • corrMap hA hB hC X Y r n (DirectSum.lof ℚ ℕ _ d (DirectSum.lof ℚ ℕ _ e c)) := by
  rw [← map_smul (DirectSum.lof ℚ ℕ _ d), ← map_smul (DirectSum.lof ℚ ℕ _ e), corrMap_lof_lof,
    corrMap_lof_lof, map_smul, blockMap_smul]

/-- `G` is `ℚ`-linear in the correspondence. -/
theorem corrMap_smul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (r n : ℤ) (q : ℚ)
    (a : Corr k X.obj.hom Y.obj.hom r) :
    corrMap hA hB hC X Y r n (q • a) = (q : F) • corrMap hA hB hC X Y r n a := by
  have h : (corrMap hA hB hC X Y r n).comp
      (LinearMap.lsmul ℚ (Corr k X.obj.hom Y.obj.hom r) q).toAddMonoidHom =
      (DistribSMul.toAddMonoidHom (W.grade X n →ₗ[F] W.grade Y n) (q : F)).comp
        (corrMap hA hB hC X Y r n) := by
    refine DirectSum.addHom_ext' fun d ↦ DirectSum.addHom_ext' fun e ↦ AddMonoidHom.ext fun c ↦ ?_
    exact corrMap_smul_lof hA hB hC X Y r n q d e c
  exact congrArg (fun φ ↦ φ a) h

/-! ### The functor on correspondences of degree zero -/

/-- The action of a morphism of correspondences of degree zero `f : X ⟶ Y` on `H^n`. -/
def corrHomMap {X Y : DegreeZero ℚ (CorrespondenceCategory k)} (f : X ⟶ Y) (n : ℤ) :
    W.grade X.as n →ₗ[F] W.grade Y.as n :=
  corrMap hA hB hC X.as Y.as 0 n (SmoothProjectiveCorr.toCorr X.as Y.as 0
    (ChowMotiveCat.component 0 (DegreeZero.val f)))

/-- Reading a homogeneous correspondence of degree `r = 0` in degree `0`. -/
theorem corrMap_component_homOf (X Y : (SmoothProjectiveScheme k).FullSubcategory) (n r : ℤ)
    (h : r = 0) (c : SmoothProjectiveCorr X Y r) :
    corrMap hA hB hC X Y 0 n (SmoothProjectiveCorr.toCorr X Y 0
        (ChowMotiveCat.component 0 (ChowMotiveCat.homOf r c))) =
      corrMap hA hB hC X Y r n (SmoothProjectiveCorr.toCorr X Y r c) := by
  subst h
  rw [ChowMotiveCat.component_homOf]

/-- A morphism of correspondences of degree zero is the homogeneous morphism given by its
degree-`0` component. -/
theorem val_eq_homOf {X Y : DegreeZero ℚ (CorrespondenceCategory k)} (f : X ⟶ Y) :
    DegreeZero.val f = ChowMotiveCat.homOf 0 (ChowMotiveCat.component 0 (DegreeZero.val f)) :=
  (ChowMotiveCat.homOf_component (DegreeZero.val_mem f)).symm

/-- The identity morphism acts as the identity on `H^n`. -/
theorem corrHomMap_id (X : DegreeZero ℚ (CorrespondenceCategory k)) (n : ℤ) :
    corrHomMap hA hB hC (𝟙 X) n = LinearMap.id := by
  rw [corrHomMap, DegreeZero.id_val]
  show corrMap hA hB hC X.as X.as 0 n (SmoothProjectiveCorr.toCorr X.as X.as 0
    (ChowMotiveCat.component 0 (𝟙 (GradedCompositionData.Obj.mk X.as :
      (canonicalCorrespondenceCompositionData k).Obj)))) = _
  rw [ChowMotiveCat.id_eq_homOf, ChowMotiveCat.component_homOf]
  exact corrMap_diagonalCorr hA hB hC X.as n

/-- The action on `H^n` of `f ≫ g` is the action of `g` after that of `f`. -/
theorem corrHomMap_comp {X Y Z : DegreeZero ℚ (CorrespondenceCategory k)} (f : X ⟶ Y)
    (g : Y ⟶ Z) (n : ℤ) :
    corrHomMap hA hB hC (f ≫ g) n = corrHomMap hA hB hC g n ∘ₗ corrHomMap hA hB hC f n := by
  have h : (DegreeZero.val (f ≫ g) : (GradedCompositionData.Obj.mk X.as :
      (canonicalCorrespondenceCompositionData k).Obj) ⟶ GradedCompositionData.Obj.mk Z.as) =
      ChowMotiveCat.homOf (0 + 0) ((canonicalCorrespondenceCompositionData k).comp
        (ChowMotiveCat.component 0 (DegreeZero.val f))
        (ChowMotiveCat.component 0 (DegreeZero.val g))) := by
    rw [← ChowMotiveCat.homOf_comp_homOf, ← val_eq_homOf, ← val_eq_homOf]
    rfl
  rw [corrHomMap, h, corrMap_component_homOf hA hB hC X.as Z.as n (0 + 0) (add_zero 0)]
  exact corrMap_comp hA hB hC X.as Y.as Z.as n _ _

/-- `G(x + y) = G(x) + G(y)` for correspondences `x y : SmoothProjectiveCorr X Y 0`. -/
theorem corrMap_toCorr_add (X Y : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ)
    (x y : SmoothProjectiveCorr X Y 0) :
    corrMap hA hB hC X Y 0 n (SmoothProjectiveCorr.toCorr X Y 0 (x + y)) =
      corrMap hA hB hC X Y 0 n (SmoothProjectiveCorr.toCorr X Y 0 x) +
      corrMap hA hB hC X Y 0 n (SmoothProjectiveCorr.toCorr X Y 0 y) := by
  rw [map_add (SmoothProjectiveCorr.toCorr X Y 0)]
  exact map_add (corrMap hA hB hC X Y 0 n) _ _

/-- `G(q • x) = q • G(x)` for a correspondence `x : SmoothProjectiveCorr X Y 0`. -/
theorem corrMap_toCorr_smul (X Y : (SmoothProjectiveScheme k).FullSubcategory) (n : ℤ) (q : ℚ)
    (x : SmoothProjectiveCorr X Y 0) :
    corrMap hA hB hC X Y 0 n (SmoothProjectiveCorr.toCorr X Y 0 (q • x)) =
      (q : F) • corrMap hA hB hC X Y 0 n (SmoothProjectiveCorr.toCorr X Y 0 x) := by
  rw [map_smul (SmoothProjectiveCorr.toCorr X Y 0)]
  exact corrMap_smul hA hB hC X Y 0 n q _

/-- The action on `H^n` is additive in the morphism. -/
theorem corrHomMap_add {X Y : DegreeZero ℚ (CorrespondenceCategory k)} (f g : X ⟶ Y) (n : ℤ) :
    corrHomMap hA hB hC (f + g) n = corrHomMap hA hB hC f n + corrHomMap hA hB hC g n := by
  rw [corrHomMap, corrHomMap, corrHomMap, DegreeZero.add_val,
    map_add (ChowMotiveCat.component (X := X.as) (Y := Y.as) 0)]
  exact corrMap_toCorr_add hA hB hC X.as Y.as n _ _

/-- The action on `H^n` is `ℚ`-linear in the morphism. -/
theorem corrHomMap_smul {X Y : DegreeZero ℚ (CorrespondenceCategory k)} (q : ℚ) (f : X ⟶ Y)
    (n : ℤ) : corrHomMap hA hB hC (q • f) n = (q : F) • corrHomMap hA hB hC f n := by
  rw [corrHomMap, corrHomMap, DegreeZero.smul_val,
    map_smul (ChowMotiveCat.component (X := X.as) (Y := Y.as) 0)]
  exact corrMap_toCorr_smul hA hB hC X.as Y.as n q _

/-- **The functor `G` of the proof of Stacks 0FHL** on smooth projective schemes over `k` with
correspondences of degree zero: `G(X) = H^*(X)`, `G(c)(a) = pr₂,*(γ(c) ∪ pr₁^*a)`, block by block
on the parts of constant dimension. -/
def corrFunctor : DegreeZero ℚ (CorrespondenceCategory k) ⥤ GradedObject ℤ (ModuleCat.{w} F) where
  obj X := W.cohomologyGraded X.as
  map f n := ModuleCat.ofHom (corrHomMap hA hB hC f n)
  map_id X := by
    funext n
    rw [corrHomMap_id]
    rfl
  map_comp f g := by
    funext n
    rw [corrHomMap_comp]
    rfl

/-- `G(X) = H^*(X)`. -/
@[simp]
theorem corrFunctor_obj (X : DegreeZero ℚ (CorrespondenceCategory k)) :
    (corrFunctor hA hB hC).obj X = W.cohomologyGraded X.as :=
  rfl

/-- `G(f)` acts on `H^n` by `corrHomMap f n`. -/
theorem corrFunctor_map_apply {X Y : DegreeZero ℚ (CorrespondenceCategory k)} (f : X ⟶ Y) (n : ℤ)
    (a : W.grade X.as n) : ((corrFunctor hA hB hC).map f n).hom a = corrHomMap hA hB hC f n a :=
  rfl

/-- The functor `G` is additive. -/
instance : (corrFunctor hA hB hC).Additive where
  map_add {X Y f g} := by
    funext n
    change ModuleCat.ofHom (corrHomMap hA hB hC (f + g) n) =
      ModuleCat.ofHom (corrHomMap hA hB hC f n) + ModuleCat.ofHom (corrHomMap hA hB hC g n)
    rw [corrHomMap_add]
    rfl

/-- The functor `G` is `ℚ`-linear. -/
instance : Functor.Linear ℚ (corrFunctor hA hB hC) where
  map_smul {X Y} f q := by
    funext n
    change ModuleCat.ofHom (corrHomMap hA hB hC (q • f) n) =
      q • ModuleCat.ofHom (corrHomMap hA hB hC f n)
    rw [corrHomMap_smul]
    rfl

end WeilData

end Stacks.WeilCohomology

end

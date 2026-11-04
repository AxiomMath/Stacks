module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClassCycleClassIntegral
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.ChowPushforward
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence

/-!
# Proper pushforward of codimension classes, rationally

For a morphism `f : X ⟶ Y` of smooth projective schemes over `k`, equidimensional of dimensions
`d` and `e`, the proper pushforward `f_* : CH^p(X) ⟶ CH^{p+e-d}(Y)` of axiom (C)(b)
(`Stacks.WeilCohomology.equidimensionalPushforward`) becomes, in `CH_*(-) ⊗ 𝐐`, the proper
pushforward `Stacks.Chow.rationalProperChowPushforward` of Stacks 02R5.

## Main results

* `Stacks.WeilCohomology.codimensionToRationalChow_equidimensionalPushforward`: the class of
  `f_*α` in `CH_*(Y) ⊗ 𝐐` is the pushforward of the class of `α`.
* `Stacks.Chow.rationalProperChowPushforward_comp`: Stacks 02R5 on `CH_*(-) ⊗ 𝐐`.
* `Stacks.WeilCohomology.codimensionToRationalChow_equidimensionalPushforward_comp`:
  `g_*(f_*α)` and `(g ∘ f)_*α` have the same class in `CH_*(-) ⊗ 𝐐`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-- **Stacks 02R5 on `CH_*(-) ⊗ 𝐐`**: proper pushforward is functorial. -/
theorem rationalProperChowPushforward_comp (C : ChowSituation.{u}) {X Y Z : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] {f : X ⟶ Y} [IsProper f] {g : Y ⟶ Z} [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
    (x : DirectSum ℤ fun j : ℤ => ℚ ⊗[ℤ] chowGroup C sX j) :
    rationalProperChowPushforward C sY sZ hg (rationalProperChowPushforward C sX sY hf x) =
      rationalProperChowPushforward C sX sZ (f := f ≫ g) (by rw [Category.assoc, hg, hf]) x := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of m t =>
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul r α =>
      rw [rationalProperChowPushforward_of_tmul, rationalProperChowPushforward_of_tmul,
        rationalProperChowPushforward_of_tmul,
        properChowPushforward_comp_apply C sX sY sZ f g (f ≫ g) rfl hf hg]
    | add t t' ht ht' => simp only [map_add, ht, ht']
  | add x y hx hy => simp only [map_add, hx, hy]

end Stacks.Chow

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-- A class of `CH^p(X)` has zero component on an empty part `X_d`. -/
private theorem codimensionChowGroup_apply_eq_zero_of_isEmpty
    {X : (SmoothProjectiveScheme k).FullSubcategory} (p : ℤ)
    (α : codimensionChowGroup k X.obj.hom p) {d : ℕ}
    (hd : IsEmpty (dimPart X.obj.hom d).toScheme) : α d = 0 :=
  have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) (partBase X.obj.hom d)
    ((d : ℤ) - p)
  Subsingleton.elim _ _

/-- For `X` equidimensional of dimension `d`, a class of `CH^p(X)` has zero component on the
parts of dimension other than `d`. -/
theorem codimensionChowGroup_apply_eq_zero_of_ne
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : RelativeDimension X.obj.hom d) (p : ℤ) (α : codimensionChowGroup k X.obj.hom p)
    {d' : ℕ} (hd' : d' ≠ d) : α d' = 0 :=
  codimensionChowGroup_apply_eq_zero_of_isEmpty p α (isEmpty_dimPart_of_ne X.obj.hom hX hd')

/-- **The class of `f_*α` in `CH_*(Y) ⊗ 𝐐` is `f_*` of the class of `α`.** For a morphism
`f : X ⟶ Y` of smooth projective schemes over `k`, equidimensional of dimensions `d` and `e`, and
`α ∈ CH^p(X)`, the proper pushforward `f_*α ∈ CH^q(Y)`, `q = p + e - d`, of axiom (C)(b) has class
`f_*[α]` in `CH_*(Y) ⊗ 𝐐`, for `f_*` the proper pushforward on `CH_*(-) ⊗ 𝐐`. -/
theorem codimensionToRationalChow_equidimensionalPushforward
    {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ} (hX : RelativeDimension X.obj.hom d)
    (hY : RelativeDimension Y.obj.hom e) (p q : ℤ) (h : q = p + e - d)
    (α : codimensionChowGroup k X.obj.hom p) :
    codimensionToRationalChow k Y.obj.hom q (equidimensionalPushforward f d e p q h α) =
      rationalProperChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom (f := f.hom.left)
        (Over.w f.hom) (codimensionToRationalChow k X.obj.hom p α) := by
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  -- the class of `α` is the pushforward of its component on `X_d`
  have hα : codimensionToRationalChow k X.obj.hom p α =
      rationalIncludePart k X.obj.hom d
        (DirectSum.of
          (fun j : ℤ => ℚ ⊗[ℤ] chowGroup (fieldChowSituation k) (partBase X.obj.hom d) j)
          ((d : ℤ) - p) ((1 : ℚ) ⊗ₜ[ℤ] α d)) := by
    rw [codimensionToRationalChow_apply]
    refine Finset.sum_eq_single d (fun d' _ hd' => ?_) (fun hd => ?_)
    · rw [codimensionChowGroup_apply_eq_zero_of_ne hX p α hd', TensorProduct.tmul_zero, map_zero,
        map_zero]
    · rw [codimensionChowGroup_apply_eq_zero_of_isEmpty p α
        ⟨fun y => hd ((mem_nonemptyDimParts k X.obj.hom).2 ⟨y.1, y.2⟩)⟩, TensorProduct.tmul_zero,
        map_zero, map_zero]
  rw [hα, rationalProperChowPushforward_of_tmul, rationalProperChowPushforward_of_tmul]
  rw [← sum_rationalIncludePart_rationalRestrictPart k Y.obj.hom
    (codimensionToRationalChow k Y.obj.hom q (equidimensionalPushforward f d e p q h α)),
    ← sum_rationalIncludePart_rationalRestrictPart k Y.obj.hom (DirectSum.of _ _ _)]
  refine Finset.sum_congr rfl fun e' he' => ?_
  obtain rfl : e' = e := by
    obtain ⟨y, hy⟩ := (mem_nonemptyDimParts k Y.obj.hom).1 he'
    exact eq_of_mem_dimPart Y.obj.hom hY hy
  congr 1
  rw [rationalRestrictPart_codimensionToRationalChow k Y.obj.hom q _ he', rationalChowMap_of_tmul]
  refine of_tmul_eq_of_tmul_of_heq _ _ (by omega) 1 ?_
  simp only [equidimensionalPushforward, AddMonoidHom.pi_apply]
  refine (chowGroupDegreeEquiv_heq _ _ _ _).trans (heq_of_eq ?_)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
  congr 1
  exact properChowPushforward_comp_apply (fieldChowSituation k) _ _ _ (dimPart X.obj.hom d).ι
    f.hom.left _ rfl rfl (Over.w f.hom) _ _ _ _ _ (α d)

/-- **`g_*(f_*α)` and `(g ∘ f)_*α` agree in `CH_*(-) ⊗ 𝐐`**, for morphisms `f : X ⟶ Y`,
`g : Y ⟶ Z` of smooth projective schemes over `k`, equidimensional of dimensions `d`, `e`, `c`. -/
theorem codimensionToRationalChow_equidimensionalPushforward_comp
    {X Y Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) {d e c : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e)
    (hZ : RelativeDimension Z.obj.hom c) (p q r : ℤ) (hq : q = p + e - d) (hr : r = q + c - e)
    (α : codimensionChowGroup k X.obj.hom p) :
    codimensionToRationalChow k Z.obj.hom r
        (equidimensionalPushforward g e c q r hr (equidimensionalPushforward f d e p q hq α)) =
      codimensionToRationalChow k Z.obj.hom r
        (equidimensionalPushforward (f ≫ g) d c p r (by omega) α) := by
  rw [codimensionToRationalChow_equidimensionalPushforward g hY hZ,
    codimensionToRationalChow_equidimensionalPushforward f hX hY,
    codimensionToRationalChow_equidimensionalPushforward (f ≫ g) hX hZ,
    rationalProperChowPushforward_comp]

end Stacks.WeilCohomology

end

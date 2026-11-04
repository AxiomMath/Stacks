module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinFunctoriality

/-!
# The exterior product on Chow groups graded by codimension, through Gysin maps

Let `k` be a field and let `X`, `Y` be smooth and proper over `k`, with projections
`pr₁ : X ×_k Y ⟶ X` and `pr₂ : X ×_k Y ⟶ Y`. Remark 0FHD of the Stacks Project uses, "omitting the
proof", that the exterior product of `α ∈ CH^i(X)` and `β ∈ CH^j(Y)` is

  `α × β = pr₁^!α · pr₂^!β`   in   `CH^{i+j}(X ×_k Y)`,

for `pr₁^!`, `pr₂^!` the Gysin maps of Stacks 0FF3 and `·` the intersection product of
Stacks 0FC0. This file proves it for the exterior product of
`Stacks.Chow.codimensionExteriorProduct`. Both sides are compared on the pieces
`X_d ×_k Y_e` of `(X ×_k Y)_{d+e}`; there the Gysin maps of the projections are flat pullbacks
(Stacks 0FF4, through `f^!(c ∩ [Y_e]) = res(c) ∩ [X_{d,e}]`), and the identity is the one of
constant dimension, `Stacks.Chow.selfIntersectionProduct_flatPullbackChow_fst_snd`.

## Main results

* `Stacks.Chow.codimensionExteriorProduct_eq_codimensionIntersectionProduct`:
  `α × β = pr₁^!α · pr₂^!β`.

## References

* [Stacks Project, Tag 0FHD](https://stacks.math.columbia.edu/tag/0FHD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

open Stacks.WeilCohomology (dimPart partBase relativeDimension_partBase fieldGysinSystem prodBase
  partProdMap partProdMap_fst partProdMap_snd
  canonicalDiagonalClassFamily)

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [Smooth sX] (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY]

/-- The canonical intersection product depends on the presentation of the scheme's structure
morphism and dimension only up to equality. -/
theorem selfIntersectionProduct_canonical_heq {W : Scheme.{u}}
    {sW sW' : W ⟶ (fieldChowSituation k).S}
    [LocallyOfFiniteType sW] [LocallyOfFiniteType sW'] [Smooth sW] [Smooth sW'] (hs : sW = sW')
    {N N' : ℕ} (hNN : N = N') (hN : RelativeDimension sW N) (hN' : RelativeDimension sW' N')
    {a a' b b' : ℤ} (ha : a = a') (hb : b = b') {x : chowGroup (fieldChowSituation k) sW a}
    {x' : chowGroup (fieldChowSituation k) sW' a'} {y : chowGroup (fieldChowSituation k) sW b}
    {y' : chowGroup (fieldChowSituation k) sW' b'} (hx : x ≍ x') (hy : y ≍ y') :
    selfIntersectionProduct (fieldChowSituation k)
        (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW N (canonicalDiagonalClassFamily k sW N hN) a b x y ≍
      selfIntersectionProduct (fieldChowSituation k)
          (Stacks.Chow.fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW' N' (canonicalDiagonalClassFamily k sW' N' hN') a' b' x' y' := by
  subst hs hNN ha hb
  cases hx
  cases hy
  rfl

/-- If `f : X ×_k Y ⟶ Z` restricts to a flat morphism `f'` of relative dimension `t` on
`X_d ×_k Y_{n-d}`, then on this piece `f^!` is the flat pullback along `f'`. -/
private theorem chowGroupRestrict_partProdIncl_codimensionGysin_of_comm {Z : Scheme.{u}}
    (sZ : Z ⟶ (fieldChowSituation k).S) [Smooth sZ] {f : pullback sX sY ⟶ Z}
    [LocallyOfFiniteType f] (hf : f ≫ sZ = prodBase sX sY) (n : ℕ) (d : Fin (n + 1)) (e t : ℕ)
    (he : e + t = n) (f' : pullback (partBase sX d) (partBase sY (n - d)) ⟶ (dimPart sZ e).toScheme)
    [LocallyOfFiniteType f'] [Flat f'] (hf' : f' ≫ partBase sZ e =
      prodBase (partBase sX d) (partBase sY (n - d))) (ht : RelativeDimension f' t)
    (hcomm : partProdIncl k sX sY n d ≫ (dimPart (prodBase sX sY) n).ι ≫ f =
      f' ≫ (dimPart sZ e).ι) (i : ℤ) (α : codimensionChowGroup k sZ i) :
    chowGroupRestrict (fieldChowSituation k) (partBase (prodBase sX sY) n)
        (prodBase (partBase sX d) (partBase sY (n - d))) (partProdIncl k sX sY n d)
        (partProdIncl_comp_partBase k sX sY n d) ((n : ℤ) - i)
        (codimensionGysin (prodBase sX sY) sZ (f := f) hf i α n) ≍
      flatPullbackChow (fieldChowSituation k) (prodBase (partBase sX d) (partBase sY (n - d)))
        (partBase sZ e) f' hf' t ht ((e : ℤ) - i)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) (α e) := by
  set Q := dimPartPiece (prodBase sX sY) sZ f n e with hQdef
  have hrange : Set.range (partProdIncl k sX sY n d) ⊆ Set.range Q.ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f ((dimPart (prodBase sX sY) n).ι (partProdIncl k sX sY n d p)) ∈ dimPart sZ e
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
    exact (show _ ∈ (dimPart sZ e : Set Z) from (dimPart sZ e).range_ι ▸ Set.mem_range_self _)
  let ψ' := IsOpenImmersion.lift Q.ι (partProdIncl k sX sY n d) hrange
  have hψ' : ψ' ≫ Q.ι = partProdIncl k sX sY n d := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion ψ' := by
    have : IsOpenImmersion (ψ' ≫ Q.ι) := by rw [hψ']; infer_instance
    exact IsOpenImmersion.of_comp _ Q.ι
  clear_value ψ'
  have hψ'base : ψ' ≫ dimPartPieceBase (prodBase sX sY) sZ f n e =
      prodBase (partBase sX d) (partBase sY (n - d)) := by
    change ψ' ≫ Q.ι ≫ partBase (prodBase sX sY) n = _
    rw [← Category.assoc, hψ', partProdIncl_comp_partBase]
  obtain ⟨c, hc⟩ := Stacks.WeilCohomology.capFundamentalClassSurjective k (partBase sZ e) e
    (relativeDimension_partBase sZ e) i (α e)
  rw [chowGroupRestrict_congr _ _ _ _ _ _ (ψ' ≫ Q.ι) hψ'.symm (by rw [Category.assoc]; exact
      hψ'base), ← chowGroupRestrict_comp (sU := dimPartPieceBase (prodBase sX sY) sZ f n e)
      (j := Q.ι) (hj := rfl) (i := ψ') (hi := hψ'base),
    chowGroupRestrict_codimensionGysin (prodBase sX sY) sZ hf i α n e, ← hc,
    eq_of_heq (dimPartPieceGysin_chowCohomologyCapFundamentalClass (prodBase sX sY) sZ hf n e i c),
    chowGroupRestrict_capFundamentalClass_restrictionOfEq _ _ _ _ _ _ _ _
      (Stacks.WeilCohomology.schemeDeltaDimension_le_of_relativeDimension _
        (relativeDimension_dimPartPieceBase (prodBase sX sY) sZ (f := f) n e)) i c]
  refine HEq.trans ?_ (flatPullbackChow_chowCohomologyCapFundamentalClass' (partBase sZ e)
    (prodBase (partBase sX d) (partBase sY (n - d))) f' hf' ht (relativeDimension_partBase sZ e) i
    c).symm
  refine (heq_of_eq ?_).trans (chowCohomologyCapFundamentalClass_heq_of_eq _ (by omega) _ _)
  congr 1
  refine chowCohomologyRestrictionOfEq_congr _ _ ?_ _ _ _ _
  refine (cancel_mono (dimPart sZ e).ι).1 ?_
  rw [Category.assoc, dimPartPieceHom_ι, ← Category.assoc ψ', hψ', hcomm]

variable [IsProper sX] [IsProper sY]

omit [IsProper sX] [IsProper sY] in
/-- **On `X_d ×_k Y_{n-d}`, `pr₁^!` is the flat pullback along the first projection.** -/
theorem chowGroupRestrict_partProdIncl_codimensionGysin_fst (n : ℕ) (d : Fin (n + 1)) (i : ℤ)
    (α : codimensionChowGroup k sX i) :
    chowGroupRestrict (fieldChowSituation k) (partBase (prodBase sX sY) n)
        (prodBase (partBase sX d) (partBase sY (n - d))) (partProdIncl k sX sY n d)
        (partProdIncl_comp_partBase k sX sY n d) ((n : ℤ) - i)
        (codimensionGysin (prodBase sX sY) sX (f := pullback.fst sX sY) rfl i α n) ≍
      flatPullbackChow (fieldChowSituation k) (prodBase (partBase sX d) (partBase sY (n - d)))
        (partBase sX d) (pullback.fst (partBase sX d) (partBase sY (n - d))) rfl (n - d)
        (Stacks.WeilCohomology.relativeDimension_fst k _ _ (relativeDimension_partBase sY (n - d)))
        ((d : ℤ) - i) (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (α d) := by
  have hdn : (d : ℕ) ≤ n := Nat.lt_succ_iff.1 d.2
  exact chowGroupRestrict_partProdIncl_codimensionGysin_of_comm sX sY sX rfl n d d (n - d)
    (by omega) _ _ (Stacks.WeilCohomology.relativeDimension_fst k _ _
      (relativeDimension_partBase sY (n - d))) (by rw [partProdIncl_ι_assoc, partProdMap_fst]) i α

omit [IsProper sX] [IsProper sY] in
/-- **On `X_d ×_k Y_{n-d}`, `pr₂^!` is the flat pullback along the second projection.** -/
theorem chowGroupRestrict_partProdIncl_codimensionGysin_snd (n : ℕ) (d : Fin (n + 1)) (j : ℤ)
    (β : codimensionChowGroup k sY j) :
    chowGroupRestrict (fieldChowSituation k) (partBase (prodBase sX sY) n)
        (prodBase (partBase sX d) (partBase sY (n - d))) (partProdIncl k sX sY n d)
        (partProdIncl_comp_partBase k sX sY n d) ((n : ℤ) - j)
        (codimensionGysin (prodBase sX sY) sY (f := pullback.snd sX sY) pullback.condition.symm j
          β n) ≍
      flatPullbackChow (fieldChowSituation k) (prodBase (partBase sX d) (partBase sY (n - d)))
        (partBase sY (n - d)) (pullback.snd (partBase sX d) (partBase sY (n - d)))
        pullback.condition.symm d
        (Stacks.WeilCohomology.relativeDimension_snd k _ _ (relativeDimension_partBase sX d))
        (((n - d : ℕ) : ℤ) - j)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
        (β (n - d)) := by
  have hdn : (d : ℕ) ≤ n := Nat.lt_succ_iff.1 d.2
  exact chowGroupRestrict_partProdIncl_codimensionGysin_of_comm sX sY sY pullback.condition.symm n
    d (n - d) d (by omega) _ _ (Stacks.WeilCohomology.relativeDimension_snd k _ _
      (relativeDimension_partBase sX d)) (by rw [partProdIncl_ι_assoc, partProdMap_snd]) j β

/-- **Remark 0FHD, the omitted identity, on Chow groups graded by codimension:
`α × β = pr₁^!α · pr₂^!β`** in `CH^{i+j}(X ×_k Y)`, for `X`, `Y` smooth and proper over `k`,
`pr₁^!`, `pr₂^!` the Gysin maps of the projections (Stacks 0FF3) and `·` the intersection product
of Stacks 0FC0. -/
theorem codimensionExteriorProduct_eq_codimensionIntersectionProduct (i j : ℤ)
    (α : codimensionChowGroup k sX i) (β : codimensionChowGroup k sY j) :
    codimensionExteriorProduct k sX sY i j α β =
      codimensionIntersectionProduct k (prodBase sX sY) i j
        (codimensionGysin (prodBase sX sY) sX (f := pullback.fst sX sY) rfl i α)
        (codimensionGysin (prodBase sX sY) sY (f := pullback.snd sX sY) pullback.condition.symm j
          β) := by
  funext n
  have hdec := isClopenDecomposition_partProdIncl k sX sY n
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) (partBase (prodBase sX sY) n)
    (fun d : ULift.{u} (Fin (n + 1)) ↦ prodBase (partBase sX d.down) (partBase sY (n - d.down)))
    (fun d ↦ partProdIncl k sX sY n d.down) (fun d ↦ partProdIncl_comp_partBase k sX sY n d.down)
    hdec (n - (i + j))).injective (funext fun d ↦ ?_)
  obtain ⟨d⟩ := d
  have hdn : (d : ℕ) ≤ n := Nat.lt_succ_iff.1 d.2
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
  -- the left-hand side: only the summand of `X_d ×_k Y_{n-d}` survives
  have hdisj : Pairwise fun a b : Fin (n + 1) ↦ Disjoint (Set.range (partProdIncl k sX sY n a).base)
      (Set.range (partProdIncl k sX sY n b).base) := fun a b hab ↦ by
    have h := TopologicalSpace.Opens.coe_disjoint.2
      (hdec.disjoint ⟨a⟩ ⟨b⟩ (fun h ↦ hab (congrArg ULift.down h)))
    simpa using h
  rw [codimensionExteriorProduct_apply]
  simp only [codimensionExteriorTerm, LinearMap.mk₂_apply]
  rw [chowGroupRestrict_sum_properChowPushforward (fieldChowSituation k)
    (partBase (prodBase sX sY) n)
    (fun d : Fin (n + 1) ↦ prodBase (partBase sX d) (partBase sY (n - d)))
    (fun d ↦ partProdIncl k sX sY n d) (fun d ↦ partProdIncl_comp_partBase k sX sY n d) hdisj]
  -- the right-hand side: the product restricts, and the Gysin maps become flat pullbacks
  have hU : RelativeDimension (prodBase (partBase sX d) (partBase sY (n - d))) n := by
    have h := Stacks.WeilCohomology.relativeDimension_prodBase k (partBase sX d)
      (partBase sY (n - d)) (relativeDimension_partBase sX d)
      (relativeDimension_partBase sY (n - d))
    rwa [Nat.sub_add_cancel hdn] at h
  rw [codimensionIntersectionProduct_apply, chowGroupRestrict_chowGroupDegreeEquiv,
    chowGroupRestrict_selfIntersectionProduct_canonical _ _ _ _
      (relativeDimension_partBase (prodBase sX sY) n) hU]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
    (HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm))
  refine (selfIntersectionProduct_flatPullbackChow_fst_snd (partBase sX d) (partBase sY (n - d))
    (relativeDimension_partBase sX d) (relativeDimension_partBase sY (n - d)) ((d : ℤ) - i)
    (((n - d : ℕ) : ℤ) - j) (α d) (β (n - d))).symm.trans ?_
  exact selfIntersectionProduct_canonical_heq rfl (by omega) _ _
    (by push_cast [Nat.cast_sub hdn]; ring) (by push_cast [Nat.cast_sub hdn]; ring)
    (chowGroupRestrict_partProdIncl_codimensionGysin_fst sX sY n d i α).symm
    (chowGroupRestrict_partProdIncl_codimensionGysin_snd sX sY n d j β).symm

end Stacks.Chow

end

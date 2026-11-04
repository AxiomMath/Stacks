module

public import StacksFrontier.AlgebraicGeometry.Chow.Intersection.CohenMacaulayIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionExteriorProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionGysinTransversal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.SmoothTransversalComposition

/-!
# The exterior product of the classes of two closed subschemes, graded by codimension

Let `k` be a field, let `V` and `W` be smooth and proper over `k` of constant dimensions `N` and
`M`, and let `A ⊆ V` and `B ⊆ W` be closed subschemes of constant dimensions `N - c` and `M - c'`.
The exterior product of Stacks 0FBV on Chow groups graded by codimension
(`Stacks.Chow.codimensionExteriorProduct`) carries the classes `[A] ∈ CH^c(V)` and
`[B] ∈ CH^{c'}(W)` of Stacks 02QU (`Stacks.WeilCohomology.closedSubschemeClass`) to the class of
the product:

  `[A] × [B] = [A ×_k B]`   in   `CH^{c+c'}(V ×_k W)`.

On the piece `V_d ×_k W_{n-d}` of the part `(V ×_k W)_n`, the exterior product is the exterior
product of the restrictions `[A]|_{V_d} = [A ×_V V_d]` and `[B]|_{W_{n-d}} = [B ×_W W_{n-d}]`,
which is the class of `(A ×_V V_d) ×_k (B ×_W W_{n-d})`
(`Stacks.Chow.Intersection.exteriorProduct_cycleAssociatedToClosedSubscheme`, the cycle form of
Stacks 0FBU for closed subschemes which need not be integral). That scheme is the inverse image of
`A ×_k B` in `V_d ×_k W_{n-d}` (`Stacks.Chow.isPullback_pullbackMap_pullbackSnd`), so it is also
the restriction of `[A ×_k B]`.

## Main results

* `Stacks.Chow.isPullback_pullbackMap_pullbackSnd`: `(A ×_V V') ×_S (B ×_W W')` is the inverse
  image of `A ×_S B` in `V' ×_S W'`.
* `Stacks.Chow.codimensionExteriorProduct_closedSubschemeClass`: `[A] × [B] = [A ×_k B]`.

## References

* [Stacks Project, Tag 0FBV](https://stacks.math.columbia.edu/tag/0FBV)
* [Stacks Project, Tag 0FBU](https://stacks.math.columbia.edu/tag/0FBU)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The product of two base changes -/

section Square

variable {𝒞 : Type*} [Category 𝒞] [HasPullbacks 𝒞] {S V W A B V' W' : 𝒞} (sV : V ⟶ S)
  (sW : W ⟶ S) (a : A ⟶ V) (b : B ⟶ W) (jV : V' ⟶ V) (jW : W' ⟶ W)

/-- **The product of two base changes is the base change of the product**:
`(A ×_V V') ×_S (B ×_W W')` is the inverse image of `A ×_S B ⟶ V ×_S W` in `V' ×_S W'`. -/
theorem isPullback_pullbackMap_pullbackSnd :
    IsPullback
      (pullback.map (pullback.snd a jV ≫ jV ≫ sV) (pullback.snd b jW ≫ jW ≫ sW) (a ≫ sV)
        (b ≫ sW) (pullback.fst a jV) (pullback.fst b jW) (𝟙 S)
        (by rw [Category.comp_id, ← pullback.condition_assoc])
        (by rw [Category.comp_id, ← pullback.condition_assoc]))
      (pullback.map (pullback.snd a jV ≫ jV ≫ sV) (pullback.snd b jW ≫ jW ≫ sW) (jV ≫ sV)
        (jW ≫ sW) (pullback.snd a jV) (pullback.snd b jW) (𝟙 S) (by simp) (by simp))
      (pullback.map (a ≫ sV) (b ≫ sW) sV sW a b (𝟙 S) (by simp) (by simp))
      (pullback.map (jV ≫ sV) (jW ≫ sW) sV sW jV jW (𝟙 S) (by simp) (by simp)) := by
  refine IsPullback.of_isLimit' ⟨pullback.hom_ext (by simp [pullback.condition])
    (by simp [pullback.condition])⟩ (PullbackCone.IsLimit.mk _ (fun s ↦ pullback.lift
      (pullback.lift (s.fst ≫ pullback.fst _ _) (s.snd ≫ pullback.fst _ _) ?_)
      (pullback.lift (s.fst ≫ pullback.snd _ _) (s.snd ≫ pullback.snd _ _) ?_) ?_)
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · simpa using s.condition =≫ pullback.fst sV sW
  · simpa using s.condition =≫ pullback.snd sV sW
  · simp only [Category.assoc, pullback.lift_snd_assoc]
    rw [pullback.condition]
  iterate 2
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc]
  · refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_) <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · simpa using h₁ =≫ pullback.fst _ _
    · simpa using h₂ =≫ pullback.fst _ _
    · simpa using h₁ =≫ pullback.snd _ _
    · simpa using h₂ =≫ pullback.snd _ _

end Square

/-! ### `[A] × [B] = [A ×_k B]` -/

section Exterior

open Stacks.WeilCohomology (dimPart partBase prodBase partProdMap partProdMap_comp_prodBase
  closedSubschemeClass closedSubschemeClass_apply isEmpty_dimPart_of_ne)

variable (k : Type u) [Field k] {V W A B : Scheme.{u}} (sV : V ⟶ (fieldChowSituation k).S)
  [Smooth sV] [IsProper sV] (sW : W ⟶ (fieldChowSituation k).S) [Smooth sW] [IsProper sW]
  (a : A ⟶ V) [IsClosedImmersion a] (b : B ⟶ W) [IsClosedImmersion b]

omit [IsProper sV] in
/-- The inverse image `A ×_V V_N` of a closed subscheme of constant dimension `n` in the part of
`V` of dimension `N` has every irreducible component of `δ`-dimension `n`, written `N - c`. -/
theorem deltaDimension_pullback_dimPart {N n : ℕ} (hA : RelativeDimension (a ≫ sV) n) (d : ℕ)
    (hd : d = N) (c : ℤ) (hc : c = N - n)
    (Z : irreducibleComponents (pullback a (dimPart sV d).ι : Scheme.{u})) :
    deltaDimension (fieldChowSituation k) (pullback.snd a (dimPart sV d).ι ≫ partBase sV d)
      ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩ = (d : ℤ) - c := by
  subst hd
  have h : RelativeDimension (pullback.fst a (dimPart sV d).ι ≫ a ≫ sV) n :=
    RelativeDimension.comp_isOpenImmersion _ _ hA
  have he : pullback.fst a (dimPart sV d).ι ≫ a ≫ sV =
      pullback.snd a (dimPart sV d).ι ≫ partBase sV d := by
    rw [pullback.condition_assoc]
  exact Stacks.WeilCohomology.deltaDimension_irreducibleComponent_of_relativeDimension_eq k _
    (RelativeDimension.congr he h)
    (m := (d : ℤ) - c) (by omega) Z

/-- **The exterior product of the classes of two closed subschemes is the class of their
product**, on Chow groups graded by codimension: for `V`, `W` smooth and proper over `k` of
constant dimensions `N` and `M`, and closed subschemes `A ⊆ V`, `B ⊆ W` of constant dimensions
`N - c` and `M - c'`, `[A] × [B] = [A ×_k B]` in `CH^{c+c'}(V ×_k W)` (Stacks 0FBV and 0FBU). -/
theorem codimensionExteriorProduct_closedSubschemeClass {N M n m : ℕ}
    (hV : RelativeDimension sV N) (hW : RelativeDimension sW M) (hA : RelativeDimension (a ≫ sV) n)
    (hB : RelativeDimension (b ≫ sW) m) (c c' : ℤ) (hc : c = N - n) (hc' : c' = M - m) :
    codimensionExteriorProduct k sV sW c c' (closedSubschemeClass sV a c)
        (closedSubschemeClass sW b c') =
      closedSubschemeClass (prodBase sV sW)
        (pullback.map (a ≫ sV) (b ≫ sW) sV sW a b (𝟙 _) (by simp) (by simp)) (c + c') := by
  funext p
  have hdec := isClopenDecomposition_partProdIncl k sV sW p
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) (partBase (prodBase sV sW) p)
    (fun d : ULift.{u} (Fin (p + 1)) ↦ prodBase (partBase sV d.down) (partBase sW (p - d.down)))
    (fun d ↦ partProdIncl k sV sW p d.down) (fun d ↦ partProdIncl_comp_partBase k sV sW p d.down)
    hdec (p - (c + c'))).injective (funext fun d ↦ ?_)
  obtain ⟨d⟩ := d
  have hdp : (d : ℕ) ≤ p := Nat.lt_succ_iff.1 d.2
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
  -- off the part `V_N ×_k W_M` the piece is empty
  by_cases hdN : (d : ℕ) = N ∧ p - d = M
  swap
  · have : IsEmpty (pullback (partBase sV d) (partBase sW (p - d)) : Scheme.{u}) := by
      rcases not_and_or.1 hdN with h | h
      · have := isEmpty_dimPart_of_ne sV hV h
        exact Function.isEmpty (pullback.fst (partBase sV d) (partBase sW (p - d))).base
      · have := isEmpty_dimPart_of_ne sW hW h
        exact Function.isEmpty (pullback.snd (partBase sV d) (partBase sW (p - d))).base
    have := subsingleton_chowGroup_of_isEmpty (fieldChowSituation k)
      (prodBase (partBase sV d) (partBase sW (p - d))) (p - (c + c'))
    exact Subsingleton.elim _ _
  obtain ⟨hd, hpd⟩ := hdN
  -- the left-hand side: only the summand of `V_d ×_k W_{p-d}` survives
  have hdisj : Pairwise fun x y : Fin (p + 1) ↦
      Disjoint (Set.range (partProdIncl k sV sW p x).base)
        (Set.range (partProdIncl k sV sW p y).base) := fun x y hxy ↦ by
    simpa using TopologicalSpace.Opens.coe_disjoint.2
      (hdec.disjoint ⟨x⟩ ⟨y⟩ (fun h ↦ hxy (congrArg ULift.down h)))
  rw [codimensionExteriorProduct_apply]
  simp only [codimensionExteriorTerm, LinearMap.mk₂_apply]
  rw [chowGroupRestrict_sum_properChowPushforward (fieldChowSituation k)
    (partBase (prodBase sV sW) p)
    (fun d : Fin (p + 1) ↦ prodBase (partBase sV d) (partBase sW (p - d)))
    (fun d ↦ partProdIncl k sV sW p d) (fun d ↦ partProdIncl_comp_partBase k sV sW p d) hdisj]
  rw [closedSubschemeClass_apply, closedSubschemeClass_apply,
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme,
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme, chowExteriorProduct_tmul_mk,
    Intersection.exteriorProduct_cycleAssociatedToClosedSubscheme k (partBase sV d)
      (partBase sW (p - d)) (pullback.snd a (dimPart sV d).ι)
      (pullback.snd b (dimPart sW (p - d)).ι) _ _ rfl rfl ?hA ?hB]
  case hA => exact deltaDimension_pullback_dimPart k sV a hA d hd c hc
  case hB =>
    exact iSup_le fun Z ↦ (congrArg (fun z : ℤ ↦ (z : EInt))
      (deltaDimension_pullback_dimPart k sW b hB (p - d) hpd c' hc' Z)).le
  -- the right-hand side: restrict along `V_d ×_k W_{p-d} ⟶ (V ×_k W)_p ⟶ V ×_k W`
  rw [closedSubschemeClass_apply, chowGroupRestrict_comp,
    chowGroupRestrict_congr _ _ _ _ _ _ (partProdMap sV sW d (p - d))
      (partProdIncl_ι k sV sW p d) (partProdMap_comp_prodBase sV sW d (p - d)),
    chowGroupRestrict_mk_cycleAssociatedToClosedSubscheme_of_isPullback _ _ _ _ _ _ _ _
      (isPullback_pullbackMap_pullbackSnd sV sW a b (dimPart sV d).ι (dimPart sW (p - d)).ι)]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  exact mk_cycleAssociatedToClosedSubscheme_heq _ _ _ (by push_cast [Nat.cast_sub hdp]; ring)

end Exterior

end Stacks.Chow

end

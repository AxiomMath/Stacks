module

public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLinesGluedAtDoublePointsPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.ClosedImmersionReducedLift

/-!
# The automorphism group of two projective lines glued at three double points is finite

Let `k` be an algebraically closed field, `a₀, a₁, a₂ ∈ k` pairwise distinct and
`X = ℙ¹_k ⨿_T ℙ¹_k` the curve obtained by gluing two copies of `ℙ¹_k` along the three double
points `T = ∐ᵢ Spec(k[t]/(t - aᵢ)²)`. **The group of automorphisms of `X` over `k` is finite.**

Let `φ` be an automorphism of `X` over `k`.

* Each copy of `ℙ¹_k` is mapped by `φ` onto an irreducible closed subset of `X`, which is the
  union of the two copies, so it lands in one copy; since `ℙ¹_k` is reduced, `φ` restricted to
  the copy factors through the copy it lands in (Stacks 0356). The two copies go to different
  copies, because the point at infinity of a copy is not on the other one, and the factorization
  is an automorphism of `ℙ¹_k` over `k`, its inverse coming from `φ⁻¹` in the same way.
* The points of `X` lying on both copies are the three points `x = aᵢ`, so each of the two
  automorphisms of `ℙ¹_k` permutes the three points.
* An automorphism of `ℙ¹_k` over `k` is determined by the permutation it induces on three
  distinct points (`AlgebraicGeometry.eq_id_of_fix_three`), and `φ` is determined by its
  restrictions to the two copies, `X` being their pushout.

So `φ` is determined by a finite amount of data: which copy each copy goes to, and two
permutations of three points.

## Main definitions

* `AlgebraicGeometry.gluedCurveComponent`: the two copies of `ℙ¹_k` in `X`, indexed by `Bool`.
* `AlgebraicGeometry.ProjectiveLinePermutingAut`: the automorphisms of `ℙ¹_k` over `k` mapping
  each of the three points `x = aᵢ` to one of them.

## Main results

* `AlgebraicGeometry.finite_projectiveLinePermutingAut`: there are finitely many of those.
* `AlgebraicGeometry.exists_comp_gluedCurveComponent_eq`: an automorphism of `X` over `k`
  restricts on each copy to such an automorphism followed by the inclusion of a copy.
* `AlgebraicGeometry.finite_aut_gluedCurve`: **the automorphism group of `X` over `k` is
  finite.**

## References

* [Stacks Project, Tag 0DSU](https://stacks.math.columbia.edu/tag/0DSU)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (pts : Fin 3 → k) (hpts : Function.Injective pts)

/-- The two copies of `ℙ¹_k` in the glued curve: `false` is the first, `true` the second. -/
def gluedCurveComponent : Bool → (projectiveLine k ⟶ gluedCurve k pts hpts)
  | false => gluedCurveInl k pts hpts
  | true => gluedCurveInr k pts hpts

/-- Each copy of `ℙ¹_k` is a closed subscheme of the glued curve. -/
instance isClosedImmersion_gluedCurveComponent (b : Bool) :
    IsClosedImmersion (gluedCurveComponent k pts hpts b) := by
  cases b
  exacts [isClosedImmersion_gluedCurveInl k pts hpts, isClosedImmersion_gluedCurveInr k pts hpts]

/-- Each copy of `ℙ¹_k` lies over `Spec k`. -/
@[reassoc (attr := simp)]
theorem gluedCurveComponent_comp_toBase (b : Bool) :
    gluedCurveComponent k pts hpts b ≫ gluedCurveToBase k pts hpts =
      projectiveLine k ↘ Spec (.of k) := by
  cases b
  exacts [gluedCurveInl_comp_toBase k pts hpts, gluedCurveInr_comp_toBase k pts hpts]

/-- Every point of the glued curve lies on one of the two copies of `ℙ¹_k`. -/
theorem gluedCurveComponent_jointly_surjective (p : gluedCurve k pts hpts) :
    ∃ b, p ∈ Set.range (gluedCurveComponent k pts hpts b).base := by
  rcases gluedCurve_jointly_surjective k pts hpts p with h | h
  exacts [⟨false, h⟩, ⟨true, h⟩]

/-- The point at infinity of one copy of `ℙ¹_k` does not lie on the other copy. -/
theorem gluedCurveComponent_infinity_notMem (b : Bool) :
    (gluedCurveComponent k pts hpts b).base (projectiveLineInfinity k) ∉
      Set.range (gluedCurveComponent k pts hpts (!b)).base := by
  cases b
  exacts [gluedCurveInl_infinity_notMem_range_gluedCurveInr k pts hpts,
    gluedCurveInr_infinity_notMem_range_gluedCurveInl k pts hpts]

/-- The range of one copy is not contained in the range of the other. -/
theorem not_range_gluedCurveComponent_subset (b : Bool) :
    ¬ Set.range (gluedCurveComponent k pts hpts b).base ⊆
      Set.range (gluedCurveComponent k pts hpts (!b)).base :=
  fun h ↦ gluedCurveComponent_infinity_notMem k pts hpts b (h ⟨_, rfl⟩)

/-- A point on both copies is one of the three points `x = aᵢ`, read on the first argument. -/
theorem exists_eq_of_gluedCurveComponent_eq (b : Bool) (x y : projectiveLine k)
    (h : (gluedCurveComponent k pts hpts b).base x =
      (gluedCurveComponent k pts hpts (!b)).base y) :
    ∃ i, x = (projectiveLineXChart k).base (affineLinePointOf (pts i)) := by
  cases b
  · exact (exists_eq_projectiveLinePoint_of_gluedCurveInl_eq_gluedCurveInr k pts hpts x y h).imp
      fun _ ↦ And.left
  · exact (exists_eq_projectiveLinePoint_of_gluedCurveInl_eq_gluedCurveInr k pts hpts y x
      h.symm).imp fun _ ↦ And.right

/-- Morphisms out of the glued curve agreeing on both copies are equal. -/
theorem gluedCurve_hom_ext {Y : Scheme.{u}} {f g : gluedCurve k pts hpts ⟶ Y}
    (h : ∀ b, gluedCurveComponent k pts hpts b ≫ f = gluedCurveComponent k pts hpts b ≫ g) :
    f = g :=
  (isPushout_gluedCurve k pts hpts).hom_ext (h false) (h true)

/-! ### The `k`-points `x = aᵢ` of the double points -/

/-- The evaluation of the `i`-th double point at its reduced point `t = aᵢ`. -/
def doublePointsEval (i : Fin 3) : DoublePoints pts →+* k :=
  (Ideal.Quotient.lift (doublePointIdeal (pts i)) (Polynomial.evalRingHom (pts i)) (by
    intro f hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    simp)).comp (Pi.evalRingHom _ i)

/-- The evaluation at `t = aᵢ` of the reduction of a polynomial is its value at `aᵢ`. -/
theorem doublePointsEval_comp_doublePointsMk (i : Fin 3) :
    (doublePointsEval k pts i).comp (doublePointsMk pts) = Polynomial.evalRingHom (pts i) := by
  ext f <;> simp [doublePointsEval, doublePointsMk]

/-- The point `x = aᵢ` of `ℙ¹_k` is the image of a `k`-point of the double points. -/
theorem projectiveLineXChartPoint_eq_comp_doublePointsToProjectiveLine (i : Fin 3) :
    projectiveLineXChartPoint (pts i) =
      Spec.map (CommRingCat.ofHom (doublePointsEval k pts i)) ≫
        doublePointsToProjectiveLine k pts := by
  rw [doublePointsToProjectiveLine_eq, doublePointsToAffineLine, ← Category.assoc,
    Spec_map_ofHom_comp_Spec_map_ofHom, doublePointsEval_comp_doublePointsMk]
  rfl

/-- The points `x = aᵢ` of the two copies of `ℙ¹_k` are identified in the glued curve. -/
theorem projectiveLineXChartPoint_comp_gluedCurveComponent (i : Fin 3) (b : Bool) :
    projectiveLineXChartPoint (pts i) ≫ gluedCurveComponent k pts hpts b =
      projectiveLineXChartPoint (pts i) ≫ gluedCurveComponent k pts hpts (!b) := by
  rw [projectiveLineXChartPoint_eq_comp_doublePointsToProjectiveLine, Category.assoc,
    Category.assoc]
  congr 1
  cases b
  exacts [doublePointsToProjectiveLine_comp_gluedCurveInl k pts hpts,
    (doublePointsToProjectiveLine_comp_gluedCurveInl k pts hpts).symm]

/-! ### Automorphisms of the projective line permuting the three points -/

/-- The automorphisms of `ℙ¹_k` over `k` mapping each of the three points `x = aᵢ` to one of
them. -/
abbrev ProjectiveLinePermutingAut : Type u :=
  {σ : projectiveLine k ≅ projectiveLine k //
    σ.hom ≫ (projectiveLine k ↘ Spec (.of k)) = projectiveLine k ↘ Spec (.of k) ∧
      ∀ i, ∃ j, projectiveLineXChartPoint (pts i) ≫ σ.hom = projectiveLineXChartPoint (pts j)}

include hpts in
/-- **There are finitely many automorphisms of `ℙ¹_k` over `k` permuting the three points**:
such an automorphism is determined by the permutation. -/
theorem finite_projectiveLinePermutingAut : Finite (ProjectiveLinePermutingAut k pts) := by
  classical
  let F : ProjectiveLinePermutingAut k pts → (Fin 3 → Fin 3) :=
    fun σ i ↦ (σ.2.2 i).choose
  have hF : ∀ σ i,
      projectiveLineXChartPoint (pts i) ≫ σ.1.hom = projectiveLineXChartPoint (pts (F σ i)) :=
    fun σ i ↦ (σ.2.2 i).choose_spec
  refine Finite.of_injective F fun σ₁ σ₂ h ↦ ?_
  have hfix (i : Fin 3) : projectiveLineXChartPoint (pts i) ≫ (σ₁.1.hom ≫ σ₂.1.inv) =
      projectiveLineXChartPoint (pts i) := by
    rw [← Category.assoc, hF σ₁ i, h, ← hF σ₂ i, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hover : (σ₁.1.hom ≫ σ₂.1.inv) ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLine k ↘ Spec (.of k) := by
    rw [Category.assoc, σ₂.1.inv_comp_eq.2 σ₂.2.1.symm, σ₁.2.1]
  have hid := eq_id_of_fix_three hover (hpts.ne (by decide : (0 : Fin 3) ≠ 1))
    (hpts.ne (by decide : (0 : Fin 3) ≠ 2)) (hpts.ne (by decide : (1 : Fin 3) ≠ 2))
    (hfix 0) (hfix 1) (hfix 2)
  apply Subtype.ext
  apply Iso.ext
  rw [← Category.comp_id σ₁.1.hom, ← σ₂.1.inv_hom_id, ← Category.assoc, hid, Category.id_comp]

/-! ### Restricting an automorphism of `X` to the two copies -/

variable {k pts hpts}

/-- An automorphism maps each copy into one copy. -/
theorem exists_range_comp_subset (φ : gluedCurve k pts hpts ⟶ gluedCurve k pts hpts) (b : Bool) :
    ∃ b', Set.range (gluedCurveComponent k pts hpts b ≫ φ).base ⊆
      Set.range (gluedCurveComponent k pts hpts b').base := by
  have hirr : IsIrreducible (Set.range (gluedCurveComponent k pts hpts b ≫ φ).base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ (projectiveLine k)).image _
      (gluedCurveComponent k pts hpts b ≫ φ).continuous.continuousOn
  have hcover : Set.range (gluedCurveComponent k pts hpts b ≫ φ).base ⊆
      Set.range (gluedCurveComponent k pts hpts false).base ∪
        Set.range (gluedCurveComponent k pts hpts true).base := by
    intro p _
    obtain ⟨c, hc⟩ := gluedCurveComponent_jointly_surjective k pts hpts p
    cases c
    exacts [Or.inl hc, Or.inr hc]
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 hirr.isPreirreducible _ _
    (gluedCurveComponent k pts hpts false).isClosedEmbedding.isClosed_range
    (gluedCurveComponent k pts hpts true).isClosedEmbedding.isClosed_range hcover with h | h
  exacts [⟨false, h⟩, ⟨true, h⟩]

/-- The factorization of an automorphism through the copy that a copy lands in. -/
def componentLift (φ : gluedCurve k pts hpts ⟶ gluedCurve k pts hpts) (b b' : Bool)
    (h : Set.range (gluedCurveComponent k pts hpts b ≫ φ).base ⊆
      Set.range (gluedCurveComponent k pts hpts b').base) :
    projectiveLine k ⟶ projectiveLine k :=
  IsClosedImmersion.liftOfReduced (gluedCurveComponent k pts hpts b') _ h

/-- `componentLift` followed by the inclusion of the target copy is the restriction of the
automorphism to the source copy. -/
@[reassoc (attr := simp)]
theorem componentLift_fac (φ : gluedCurve k pts hpts ⟶ gluedCurve k pts hpts) (b b' : Bool)
    (h : Set.range (gluedCurveComponent k pts hpts b ≫ φ).base ⊆
      Set.range (gluedCurveComponent k pts hpts b').base) :
    componentLift φ b b' h ≫ gluedCurveComponent k pts hpts b' =
      gluedCurveComponent k pts hpts b ≫ φ :=
  IsClosedImmersion.liftOfReduced_fac _ _ _

/-- If an isomorphism maps both copies into the same copy, the other copy is missed. -/
theorem ne_of_range_comp_subset (φ : gluedCurve k pts hpts ≅ gluedCurve k pts hpts)
    {c₁ c₂ : Bool}
    (h₁ : Set.range (gluedCurveComponent k pts hpts false ≫ φ.hom).base ⊆
      Set.range (gluedCurveComponent k pts hpts c₁).base)
    (h₂ : Set.range (gluedCurveComponent k pts hpts true ≫ φ.hom).base ⊆
      Set.range (gluedCurveComponent k pts hpts c₂).base) : c₂ = !c₁ := by
  by_contra hc
  obtain rfl : c₂ = c₁ := Bool.ne_not.1 hc
  apply not_range_gluedCurveComponent_subset k pts hpts (!c₂)
  rintro _ ⟨x, rfl⟩
  have hp : (gluedCurveComponent k pts hpts (!c₂)).base x =
      φ.hom.base (φ.inv.base ((gluedCurveComponent k pts hpts (!c₂)).base x)) := by
    show _ = (φ.inv ≫ φ.hom).base _
    rw [Iso.inv_hom_id]
    rfl
  obtain ⟨b, y, hy⟩ := gluedCurveComponent_jointly_surjective k pts hpts
    (φ.inv.base ((gluedCurveComponent k pts hpts (!c₂)).base x))
  rw [hp, ← hy, Bool.not_not]
  cases b
  exacts [h₁ ⟨y, rfl⟩, h₂ ⟨y, rfl⟩]

/-- The factorization of an automorphism through the copy that a copy lands in is an
automorphism of `ℙ¹_k`. -/
theorem isIso_componentLift (φ : gluedCurve k pts hpts ≅ gluedCurve k pts hpts) (b b' : Bool)
    (h : Set.range (gluedCurveComponent k pts hpts b ≫ φ.hom).base ⊆
      Set.range (gluedCurveComponent k pts hpts b').base) :
    IsIso (componentLift φ.hom b b' h) := by
  obtain ⟨b'', h'⟩ := exists_range_comp_subset φ.inv b'
  have e : gluedCurveComponent k pts hpts b =
      componentLift φ.hom b b' h ≫ componentLift φ.inv b' b'' h' ≫
        gluedCurveComponent k pts hpts b'' := by
    rw [componentLift_fac, componentLift_fac_assoc, Iso.hom_inv_id, Category.comp_id]
  have hb : b'' = b := by
    by_contra hne
    apply not_range_gluedCurveComponent_subset k pts hpts b
    rintro _ ⟨x, rfl⟩
    rw [e, ← Bool.eq_not_iff.2 hne]
    exact ⟨_, rfl⟩
  subst hb
  refine ⟨⟨componentLift φ.inv b' b'' h', ?_, ?_⟩⟩
  · rw [← cancel_mono (gluedCurveComponent k pts hpts b''), Category.assoc, ← e,
      Category.id_comp]
  · rw [← cancel_mono (gluedCurveComponent k pts hpts b'), Category.assoc, componentLift_fac,
      componentLift_fac_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- The factorization of an automorphism over `k` lies over `k`. -/
theorem componentLift_comp_structureMorphism
    (φ : gluedCurve k pts hpts ⟶ gluedCurve k pts hpts)
    (hφ : φ ≫ gluedCurveToBase k pts hpts = gluedCurveToBase k pts hpts) (b b' : Bool)
    (h : Set.range (gluedCurveComponent k pts hpts b ≫ φ).base ⊆
      Set.range (gluedCurveComponent k pts hpts b').base) :
    componentLift φ b b' h ≫ (projectiveLine k ↘ Spec (.of k)) =
      projectiveLine k ↘ Spec (.of k) := by
  nth_rw 1 [← gluedCurveComponent_comp_toBase k pts hpts b']
  rw [componentLift_fac_assoc, hφ, gluedCurveComponent_comp_toBase]

variable [IsAlgClosed k]

/-- The factorization of an automorphism permutes the three points. -/
theorem componentLift_permutes (φ : gluedCurve k pts hpts ≅ gluedCurve k pts hpts)
    (hφ : φ.hom ≫ gluedCurveToBase k pts hpts = gluedCurveToBase k pts hpts) {c₁ c₂ : Bool}
    (h₁ : Set.range (gluedCurveComponent k pts hpts false ≫ φ.hom).base ⊆
      Set.range (gluedCurveComponent k pts hpts c₁).base)
    (h₂ : Set.range (gluedCurveComponent k pts hpts true ≫ φ.hom).base ⊆
      Set.range (gluedCurveComponent k pts hpts c₂).base) (b : Bool) (i : Fin 3) :
    ∃ j, projectiveLineXChartPoint (pts i) ≫
      componentLift φ.hom b (if b then c₂ else c₁) (by cases b <;> assumption) =
        projectiveLineXChartPoint (pts j) := by
  have hc := ne_of_range_comp_subset φ h₁ h₂
  set σ := componentLift φ.hom b (if b then c₂ else c₁) (by cases b <;> assumption)
  set σ' := componentLift φ.hom (!b) (if b then c₁ else c₂) (by cases b <;> assumption)
  have hσ := componentLift_fac φ.hom b (if b then c₂ else c₁) (by cases b <;> assumption)
  have hσ' := componentLift_fac φ.hom (!b) (if b then c₁ else c₂) (by cases b <;> assumption)
  have hcc : (if b then c₁ else c₂) = !(if b then c₂ else c₁) := by cases b <;> simp [hc]
  let z := IsLocalRing.closedPoint k
  have e : (projectiveLineXChartPoint (pts i) ≫ σ ≫
      gluedCurveComponent k pts hpts (if b then c₂ else c₁)) =
      projectiveLineXChartPoint (pts i) ≫ σ' ≫
        gluedCurveComponent k pts hpts (if b then c₁ else c₂) := by
    rw [hσ, hσ', ← Category.assoc, ← Category.assoc,
      projectiveLineXChartPoint_comp_gluedCurveComponent k pts hpts i b]
  have e' := congrArg (fun f : Spec (.of k) ⟶ gluedCurve k pts hpts ↦ f.base z) e
  simp only [Scheme.Hom.comp_base, hcc] at e'
  obtain ⟨j, hj⟩ := exists_eq_of_gluedCurveComponent_eq k pts hpts _ _ _ e'
  refine ⟨j, projectiveLine_point_ext ?_ (projectiveLineXChartPoint_comp_structureMorphism _) ?_⟩
  · rw [Category.assoc, componentLift_comp_structureMorphism φ.hom hφ,
      projectiveLineXChartPoint_comp_structureMorphism]
  · exact hj.trans (projectiveLineXChartPoint_apply _ _).symm

/-- **An automorphism of the glued curve over `k` restricts on each copy to an automorphism of
`ℙ¹_k` permuting the three points, followed by the inclusion of a copy.** -/
theorem exists_comp_gluedCurveComponent_eq (φ : gluedCurve k pts hpts ≅ gluedCurve k pts hpts)
    (hφ : φ.hom ≫ gluedCurveToBase k pts hpts = gluedCurveToBase k pts hpts) (b : Bool) :
    ∃ (b' : Bool) (σ : ProjectiveLinePermutingAut k pts),
      σ.1.hom ≫ gluedCurveComponent k pts hpts b' = gluedCurveComponent k pts hpts b ≫ φ.hom := by
  obtain ⟨c₁, h₁⟩ := exists_range_comp_subset φ.hom false
  obtain ⟨c₂, h₂⟩ := exists_range_comp_subset φ.hom true
  have hb : Set.range (gluedCurveComponent k pts hpts b ≫ φ.hom).base ⊆
      Set.range (gluedCurveComponent k pts hpts (if b then c₂ else c₁)).base := by
    cases b <;> assumption
  have := isIso_componentLift φ b _ hb
  exact ⟨if b then c₂ else c₁, ⟨asIso (componentLift φ.hom b _ hb),
    componentLift_comp_structureMorphism φ.hom hφ b _ hb, componentLift_permutes φ hφ h₁ h₂ b⟩,
    componentLift_fac φ.hom b _ hb⟩

variable (k pts hpts)

/-- **The automorphism group of `X` over `k` is finite.** For `k` algebraically
closed and three distinct points, the group of automorphisms over `k` of the curve obtained by
gluing two copies of `ℙ¹_k` along the three double points `Spec(k[t]/(t - aᵢ)²)` is finite. -/
@[stacks 0DSU "the automorphism group of X over k is finite"]
theorem finite_aut_gluedCurve :
    Finite (Aut (Over.mk (gluedCurveToBase k pts hpts))) := by
  classical
  have := finite_projectiveLinePermutingAut k pts hpts
  have hdata : ∀ φ : Aut (Over.mk (gluedCurveToBase k pts hpts)), ∀ b : Bool,
      ∃ (b' : Bool) (σ : ProjectiveLinePermutingAut k pts),
        σ.1.hom ≫ gluedCurveComponent k pts hpts b' =
          gluedCurveComponent k pts hpts b ≫ φ.asIso.hom.left := fun φ b ↦
    exists_comp_gluedCurveComponent_eq ((Over.forget _).mapIso φ.asIso) (Over.w φ.asIso.hom) b
  let F : Aut (Over.mk (gluedCurveToBase k pts hpts)) →
      (Bool → Bool × ProjectiveLinePermutingAut k pts) :=
    fun φ b ↦ ((hdata φ b).choose, (hdata φ b).choose_spec.choose)
  refine Finite.of_injective F fun φ ψ h ↦ ?_
  have key : φ.asIso.hom.left = ψ.asIso.hom.left := by
    refine gluedCurve_hom_ext k pts hpts fun b ↦ ?_
    have h1 : (hdata φ b).choose = (hdata ψ b).choose := congrArg Prod.fst (congrFun h b)
    have h2 : (hdata φ b).choose_spec.choose.1.hom = (hdata ψ b).choose_spec.choose.1.hom :=
      congrArg (fun σ : ProjectiveLinePermutingAut k pts ↦ σ.1.hom)
        (congrArg Prod.snd (congrFun h b))
    rw [← (hdata φ b).choose_spec.choose_spec, ← (hdata ψ b).choose_spec.choose_spec, h2, h1]
  exact Aut.ext (Iso.ext (Over.OverMorphism.ext key))

end AlgebraicGeometry

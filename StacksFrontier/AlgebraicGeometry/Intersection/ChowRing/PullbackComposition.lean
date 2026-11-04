module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.PrincipalReductionExistence
public import StacksFrontier.AlgebraicGeometry.Intersection.ChowRing.Pullback

/-!
# Pullback along a composite of morphisms

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of nonsingular projective varieties. This file
proves `(g ∘ f)^* = f^* ∘ g^*` (Tag 0B2X, part (2)). The source's proof runs on
`X × Y × Z`, realised here as `W = (X × Y) ×_K Z` with the three projections

* `q₁₂ = pr_{X × Y} : W ⟶ X × Y`,
* `q₁₃ : W ⟶ X × Z`, and
* `q₂₃ : W ⟶ Y × Z`,

each a base change of a projection of a product of two varieties, hence flat and proper. On `W`
the pullback `q₂₃^*[Γ_g]` is the graph of `g ∘ pr_Y : X × Y ⟶ Z`, it meets `q₁₂^*[Γ_f]`
transversally, and their product maps isomorphically to `Γ_{g ∘ f}` under `q₁₃`.

## Main definitions

* `Stacks.Intersection.ChowRing.tripleProj₂₃`, `Stacks.Intersection.ChowRing.tripleProj₁₃`: the
  projections `q₂₃` and `q₁₃`.

## Main results

* `Stacks.Intersection.ChowRing.prYPullback_chowPullback`: `pr_Y^* ∘ g^* = (g ∘ pr_Y)^*`.
* `Stacks.Intersection.ChowRing.chowPullback_comp`: **Tag 0B2X, part (2)**,
  `(g ∘ f)^* = f^* ∘ g^*`.

## References

* [Stacks Project, Tag 0B2X](https://stacks.math.columbia.edu/tag/0B2X)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula

universe u

namespace Stacks.Intersection.ChowRing

/-! ### The triple product -/

section TripleProduct

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) (sZ : Z ⟶ Spec (.of K))

/-- The projection `q₂₃ : (X × Y) × Z ⟶ Y × Z`. -/
def tripleProj₂₃ : pullback (pullback.fst sX sY ≫ sX) sZ ⟶ pullback sY sZ :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd sX sY) (pullback.snd _ _) (by
    have h1 : pullback.snd sX sY ≫ sY = pullback.fst sX sY ≫ sX := pullback.condition.symm
    rw [Category.assoc, h1]
    exact pullback.condition)

/-- The projection `q₁₃ : (X × Y) × Z ⟶ X × Z`. -/
def tripleProj₁₃ : pullback (pullback.fst sX sY ≫ sX) sZ ⟶ pullback sX sZ :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst sX sY) (pullback.snd _ _) (by
    rw [Category.assoc]
    exact pullback.condition)

/-- `q₂₃` followed by the first projection of `Y × Z` is `(X × Y) × Z ⟶ X × Y ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem tripleProj₂₃_fst :
    tripleProj₂₃ sX sY sZ ≫ pullback.fst sY sZ = pullback.fst _ _ ≫ pullback.snd sX sY :=
  pullback.lift_fst _ _ _

/-- `q₂₃` followed by the second projection of `Y × Z` is the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem tripleProj₂₃_snd :
    tripleProj₂₃ sX sY sZ ≫ pullback.snd sY sZ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- `q₁₃` followed by the first projection of `X × Z` is `(X × Y) × Z ⟶ X × Y ⟶ X`. -/
@[reassoc (attr := simp)]
theorem tripleProj₁₃_fst :
    tripleProj₁₃ sX sY sZ ≫ pullback.fst sX sZ = pullback.fst _ _ ≫ pullback.fst sX sY :=
  pullback.lift_fst _ _ _

/-- `q₁₃` followed by the second projection of `X × Z` is the projection to `Z`. -/
@[reassoc (attr := simp)]
theorem tripleProj₁₃_snd :
    tripleProj₁₃ sX sY sZ ≫ pullback.snd sX sZ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- `(X × Y) × Z` is the fibre product of `X × Y` and `Y × Z` over `Y`. -/
theorem isPullback_tripleProj₂₃ :
    IsPullback (tripleProj₂₃ sX sY sZ) (pullback.fst (pullback.fst sX sY ≫ sX) sZ)
      (pullback.fst sY sZ) (pullback.snd sX sY) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd sY sZ) (h₂₂ := sY) (v₁₃ := sZ) ?_
    (tripleProj₂₃_fst sX sY sZ) (IsPullback.of_hasPullback sY sZ).flip
  rw [tripleProj₂₃_snd, ← pullback.condition]
  exact (IsPullback.of_hasPullback (pullback.fst sX sY ≫ sX) sZ).flip

/-- `(X × Y) × Z` is the fibre product of `X × Y` and `X × Z` over `X`. -/
theorem isPullback_tripleProj₁₃ :
    IsPullback (tripleProj₁₃ sX sY sZ) (pullback.fst (pullback.fst sX sY ≫ sX) sZ)
      (pullback.fst sX sZ) (pullback.fst sX sY) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd sX sZ) (h₂₂ := sX) (v₁₃ := sZ) ?_
    (tripleProj₁₃_fst sX sY sZ) (IsPullback.of_hasPullback sX sZ).flip
  rw [tripleProj₁₃_snd]
  exact (IsPullback.of_hasPullback (pullback.fst sX sY ≫ sX) sZ).flip

/-- `q₂₃` is flat when `X` is flat over `K`. -/
instance flat_tripleProj₂₃ [Flat sX] : Flat (tripleProj₂₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₂₃ sX sY sZ).flip inferInstance

/-- `q₂₃` is locally of finite type when `X` is. -/
instance locallyOfFiniteType_tripleProj₂₃ [LocallyOfFiniteType sX] :
    LocallyOfFiniteType (tripleProj₂₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₂₃ sX sY sZ).flip inferInstance

/-- `q₁₃` is locally of finite type when `Y` is. -/
instance locallyOfFiniteType_tripleProj₁₃ [LocallyOfFiniteType sY] :
    LocallyOfFiniteType (tripleProj₁₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₁₃ sX sY sZ).flip inferInstance

/-- `q₁₃` is flat when `Y` is flat over `K`. -/
instance flat_tripleProj₁₃ [Flat sY] : Flat (tripleProj₁₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₁₃ sX sY sZ).flip inferInstance

/-- `q₁₃` is proper when `Y` is proper over `K`. -/
instance isProper_tripleProj₁₃ [IsProper sY] : IsProper (tripleProj₁₃ sX sY sZ) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₁₃ sX sY sZ).flip inferInstance

/-- `q₂₃` is a morphism over `K`. -/
theorem tripleProj₂₃_comp_structure :
    tripleProj₂₃ sX sY sZ ≫ (pullback.fst sY sZ ≫ sY) =
      pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX) := by
  rw [tripleProj₂₃_fst_assoc, pullback.condition]

/-- `q₁₃` is a morphism over `K`. -/
theorem tripleProj₁₃_comp_structure :
    tripleProj₁₃ sX sY sZ ≫ (pullback.fst sX sZ ≫ sX) =
      pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX) := by
  rw [tripleProj₁₃_fst_assoc]

end TripleProduct

/-! ### The graph of `g ∘ pr_Y` -/

section GraphTriple

variable {K : Type u} [Field K] {X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of K)}
  {sY : Y ⟶ Spec (.of K)} {sZ : Z ⟶ Spec (.of K)} (f : X ⟶ Y) (hf : f ≫ sY = sX)
  (g : Y ⟶ Z) (hg : g ≫ sZ = sY)

include hg in
/-- The morphism `g ∘ pr_Y : X × Y ⟶ Z` is a morphism over `K`. -/
theorem snd_comp_comp_structure :
    (pullback.snd sX sY ≫ g) ≫ sZ = pullback.fst sX sY ≫ sX := by
  rw [Category.assoc, hg, pullback.condition]

/-- **The pullback of `Γ_g` to `(X × Y) × Z` is the graph of `g ∘ pr_Y`.** -/
theorem isPullback_graph_snd_comp :
    IsPullback (graph (pullback.snd sX sY ≫ g) (snd_comp_comp_structure g hg))
      (pullback.snd sX sY) (tripleProj₂₃ sX sY sZ) (graph g hg) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (pullback.fst sX sY ≫ sX) sZ)
    (h₂₂ := pullback.fst sY sZ) (v₁₃ := pullback.snd sX sY) ?_ ?_
    (isPullback_tripleProj₂₃ sX sY sZ).flip
  · rw [graph_fst, graph_fst]
    exact IsPullback.id_horiz _
  · apply pullback.hom_ext
    · rw [Category.assoc, tripleProj₂₃_fst, graph_fst_assoc, Category.assoc, graph_fst,
        Category.comp_id]
    · rw [Category.assoc, tripleProj₂₃_snd, graph_snd, Category.assoc, graph_snd]

/-- **The composite graph**: `X ⟶ X × Y ⟶ (X × Y) × Z ⟶ X × Z` is the graph of `g ∘ f`. -/
theorem graph_comp_graph_comp_tripleProj₁₃ :
    graph f hf ≫ graph (pullback.snd sX sY ≫ g) (snd_comp_comp_structure g hg) ≫
        tripleProj₁₃ sX sY sZ =
      graph (f ≫ g) (by rw [Category.assoc, hg, hf]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, tripleProj₁₃_fst, graph_fst_assoc, graph_fst,
      graph_fst]
  · rw [Category.assoc, Category.assoc, tripleProj₁₃_snd, graph_snd, graph_snd_assoc, graph_snd]

end GraphTriple

/-- The class of a closed subscheme does not depend on how its degree is spelled. -/
theorem mk_cycleAssociatedToClosedSubscheme_heq (C : ChowSituation.{u}) {T S : Scheme.{u}}
    (p : T ⟶ C.S) [LocallyOfFiniteType p] (i : S ⟶ T) [IsClosedImmersion i] {k k' : ℤ}
    (h : k = k') :
    QuotientAddGroup.mk' (rationalEquivalences C p k) (cycleAssociatedToClosedSubscheme C p i k) ≍
      QuotientAddGroup.mk' (rationalEquivalences C p k')
        (cycleAssociatedToClosedSubscheme C p i k') := by
  subst h; rfl

/-! ### `(g ∘ pr_Y)^* = pr_Y^* ∘ g^*` -/

/-- The dimension of `(X × Y) × Z` is that of `Y × Z` plus `dim X`, and that of `X × Z` plus
`dim Y`. -/
private theorem topologicalKrullDim_triple_pullback_eq (K : Type u) [Field K] [IsAlgClosed K]
    {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K))
    (sZ : Z ⟶ Spec (.of K)) [IsProjectiveVariety K sX] [IsProjectiveVariety K sY]
    [IsProjectiveVariety K sZ] {dX dY : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
    (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞)) :
    topologicalKrullDim (pullback (pullback.fst sX sY ≫ sX) sZ : Scheme.{u}) =
        topologicalKrullDim (pullback sY sZ : Scheme.{u}) + (dX : WithBot ℕ∞) ∧
      topologicalKrullDim (pullback (pullback.fst sX sY ≫ sX) sZ : Scheme.{u}) =
        topologicalKrullDim (pullback sX sZ : Scheme.{u}) + (dY : WithBot ℕ∞) := by
  simp only [topologicalKrullDim_pullback_of_isVariety, hdX, hdY]
  exact ⟨by ac_rfl, by ac_rfl⟩

section FlatComposite

variable (K : Type u) [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) (sZ : Z ⟶ Spec (.of K)) [IsProjectiveVariety K sX]
  [IsProjectiveVariety K sY] [IsProjectiveVariety K sZ] (hX : IsRegular X) (hY : IsRegular Y)
  (hZ : IsRegular Z) {dX dY dZ : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
  (hdZ : topologicalKrullDim Z = (dZ : WithBot ℕ∞)) (g : Y ⟶ Z) (hg : g ≫ sZ = sY)

include hdX hdY hdZ in
/-- **Pullback along `g ∘ pr_Y` is flat pullback along `pr_Y` after pullback along `g`.** The
source's base change of Lemma 0B10's proof: `pr_Y^* ∘ pr_{Y,*} = q₁₂,* ∘ q₂₃^*` on the cartesian
square formed by `(X × Y) × Z`, `X × Y`, `Y × Z` and `Y` (Tag 02RG), flat pullback along `q₂₃` is
multiplicative (Tag 0B0Z), `q₂₃^*[Γ_g]` is the graph of `g ∘ pr_Y`, and `q₂₃^* ∘ pr_Z^* = pr_Z^*`.
-/
theorem prYPullback_chowPullback {k l : ℤ} (hkl : k + dY = dZ + l)
    (c : chowGroup (fieldChowSituation K) sZ k) :
    prYPullback K sX sY hdX l (chowPullback K sY sZ hY hZ hdY hdZ g hg hkl c) =
      chowPullback K (pullback.fst sX sY ≫ sX) sZ (isRegular_pullback_of_isRegular sX sY hX hY)
        hZ (topologicalKrullDim_pullback_eq K sX sY hdX hdY) hdZ (pullback.snd sX sY ≫ g)
        (snd_comp_comp_structure g hg) (show k + ((dX + dY : ℕ) : ℤ) = dZ + (l + dX) by
          push_cast; omega) c := by
  have hYZ := isRegular_pullback_of_isRegular sY sZ hY hZ
  have hdYZ := topologicalKrullDim_pullback_eq K sY sZ hdY hdZ
  have hXY := isRegular_pullback_of_isRegular sX sY hX hY
  have hdXY := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have hW := isRegular_pullback_of_isRegular (pullback.fst sX sY ≫ sX) sZ hXY hZ
  have heW := (topologicalKrullDim_triple_pullback_eq K sX sY sZ hdX hdY).1
  have hbc := Stacks.Chow.flatPullbackChow_comp_properChowPushforward_of_isPullback
    (fieldChowSituation K) (pullback.fst sY sZ ≫ sY) sY
    (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX))
    (pullback.fst sX sY ≫ sX) (pullback.fst sY sZ) (pullback.snd sX sY)
    (tripleProj₂₃ sX sY sZ) (pullback.fst _ sZ) (isPullback_tripleProj₂₃ sX sY sZ) rfl
    pullback.condition.symm (tripleProj₂₃_comp_structure sX sY sZ) dX
    (ExteriorProductProjections.relativeDimension_pullbackSnd sX sY dX hdX) l
  simp only [chowPullback, AddMonoidHom.comp_apply, chowMul_apply, prYPullback,
    flatPullbackChowOfRelativeDimension]
  rw [← AddMonoidHom.comp_apply, hbc, AddMonoidHom.comp_apply]
  congr 1
  refine (flatPullbackChow_chowMulFun K (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫
    (pullback.fst sX sY ≫ sX)) (pullback.fst sY sZ ≫ sY) hW hYZ (tripleProj₂₃ sX sY sZ)
    (tripleProj₂₃_comp_structure sX sY sZ) dX heW hdYZ (r := (dY : ℤ)) (s := k + dY) (m := l)
    (by push_cast; omega) _ _).trans ?_
  refine chowMulFun_congr_heq (by push_cast; ring) (by push_cast; ring) ?_ ?_
  · have hδ : schemeDeltaDimension (fieldChowSituation K)
        (graph g hg ≫ (pullback.fst sY sZ ≫ sY)) ≤ ((dY : ℤ) : EInt) := by
      refine schemeDeltaDimension_le_of_forall_relativeDimension_le (fieldChowSituation K) _
        (graph g hg) fun y => relativeDimension_le_of_topologicalKrullDim_le
          (fieldChowSituation K) (fun _ _ => rfl) _ (graph g hg).isClosedEmbedding.isClosed_range
          ?_ (Set.mem_range_self y)
      rw [← Set.image_univ,
        topologicalKrullDim_image_eq_of_isEmbedding (graph g hg).isClosedEmbedding.isEmbedding,
        ← hdY]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph).le
    rw [graphClass, flatPullbackChowOfRelativeDimension_mk,
      flatPullback_cycleAssociatedToClosedSubscheme_of_le _ _ _ _ _ _ _ _ _ hδ,
      cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation K) _ _
        (graph (pullback.snd sX sY ≫ g) (snd_comp_comp_structure g hg))
        (isPullback_graph_snd_comp g hg).isoPullback.symm
        (IsPullback.isoPullback_inv_fst _), graphClass]
    exact mk_cycleAssociatedToClosedSubscheme_heq (fieldChowSituation K) _ _
      (by push_cast; ring)
  · refine (Stacks.Chow.flatPullbackChow_comp (fieldChowSituation K) _ (pullback.fst sY sZ ≫ sY) sZ
      (tripleProj₂₃ sX sY sZ) (pullback.snd sY sZ) (tripleProj₂₃_comp_structure sX sY sZ)
      pullback.condition.symm dX dY _ _ k
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c).trans
      (heq_of_eq ?_)
    exact DFunLike.congr_fun
      (Stacks.Chow.TensorZeroScheme.flatPullbackChowOfRelativeDimension_congr_hom
      (fieldChowSituation K) _ sZ (tripleProj₂₃_snd sX sY sZ) _ _ (dX + dY) _ _ k) c

end FlatComposite

/-- Flat pullback of a cycle along two equal morphisms of equal relative dimensions, read at a
point. -/
theorem flatPullback_apply_congr (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S)
    [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {f f' : X' ⟶ X}
    [LocallyOfFiniteType f] [Flat f] [LocallyOfFiniteType f'] [Flat f'] (hff : f = f')
    (hb : f ≫ sX = sX') (hb' : f' ≫ sX = sX') {r r' : ℕ} (hrr : r = r')
    (hr : AlgebraicGeometry.RelativeDimension f r) (hr' : AlgebraicGeometry.RelativeDimension f' r')
    (k : ℤ) (c : CycleGroup C sX k) (x : X') :
    (flatPullback C sX' sX f hb r hr k c).1 x = (flatPullback C sX' sX f' hb' r' hr' k c).1 x := by
  subst hff hrr; rfl

/-- Classes of cycles with the same coefficients are heterogeneously equal across a change of the
spelling of the degree. -/
theorem mk_heq_of_apply_eq (C : ChowSituation.{u}) {T : Scheme.{u}} (p : T ⟶ C.S)
    [LocallyOfFiniteType p] {i j : ℤ} (hij : i = j) {a : CycleGroup C p i} {b : CycleGroup C p j}
    (hab : ∀ x : T, a.1 x = b.1 x) :
    QuotientAddGroup.mk' (rationalEquivalences C p i) a ≍
      QuotientAddGroup.mk' (rationalEquivalences C p j) b := by
  subst hij
  have : a = b := Subtype.ext (Function.locallyFinsuppWithin.ext hab)
  rw [this]

/-! ### Tag 0B2X, part (2) -/

section Composition

variable (K : Type u) [Field K] [IsAlgClosed K] {X Y Z : Scheme.{u}} (sX : X ⟶ Spec (.of K))
  (sY : Y ⟶ Spec (.of K)) (sZ : Z ⟶ Spec (.of K)) [IsProjectiveVariety K sX]
  [IsProjectiveVariety K sY] [IsProjectiveVariety K sZ] (hX : IsRegular X) (hY : IsRegular Y)
  (hZ : IsRegular Z) {dX dY dZ : ℕ} (hdX : topologicalKrullDim X = (dX : WithBot ℕ∞))
  (hdY : topologicalKrullDim Y = (dY : WithBot ℕ∞))
  (hdZ : topologicalKrullDim Z = (dZ : WithBot ℕ∞)) (f : X ⟶ Y) (hf : f ≫ sY = sX)
  (g : Y ⟶ Z) (hg : g ≫ sZ = sY)

omit [IsAlgClosed K] in
/-- Pushing forward along `q₁₂` and then `pr_X` is pushing forward along `q₁₃` and then `pr_X`. -/
theorem prXPush_properChowPushforward_tripleProj₁₂ (d : ℤ)
    (w : chowGroup (fieldChowSituation K)
      (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX)) d) :
    prXPush K sX sY d (properChowPushforward (fieldChowSituation K) _ (pullback.fst sX sY ≫ sX)
        (pullback.fst (pullback.fst sX sY ≫ sX) sZ) rfl d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K) _ _
          _ rfl d) w) =
      prXPush K sX sZ d (properChowPushforward (fieldChowSituation K) _ (pullback.fst sX sZ ≫ sX)
        (tripleProj₁₃ sX sY sZ) (tripleProj₁₃_comp_structure sX sY sZ) d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K) _ _
          _ (tripleProj₁₃_comp_structure sX sY sZ) d) w) := by
  obtain ⟨ω, rfl⟩ := QuotientAddGroup.mk'_surjective _ w
  simp only [prXPush, properChowPushforward_mk]
  rw [properPushforward_properPushforward, properPushforward_properPushforward]
  exact congrArg _ (congrFun (properPushforward_congr (fieldChowSituation K) _ sX _ _
    (by rw [tripleProj₁₃_fst]) _ _ d) ω)

include hdX hdY in
/-- `q₁₃^* ∘ pr_Z^* = pr_Z^*` on `(X × Y) × Z`. -/
theorem flatPullback_snd_heq_tripleProj₁₃ {k : ℤ} (c : chowGroup (fieldChowSituation K) sZ k) :
    flatPullbackChowOfRelativeDimension (fieldChowSituation K)
        (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX)) sZ
        (pullback.snd (pullback.fst sX sY ≫ sX) sZ) pullback.condition.symm (dX + dY)
        (ExteriorProductProjections.relativeDimension_pullbackSnd (pullback.fst sX sY ≫ sX) sZ
          (dX + dY) (topologicalKrullDim_pullback_eq K sX sY hdX hdY)) k c ≍
      flatPullbackChowOfRelativeDimension (fieldChowSituation K)
        (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX))
        (pullback.fst sX sZ ≫ sX) (tripleProj₁₃ sX sY sZ) (tripleProj₁₃_comp_structure sX sY sZ)
        dY (relativeDimension_of_flat_of_isVariety K _ _ (tripleProj₁₃ sX sY sZ)
          (tripleProj₁₃_comp_structure sX sY sZ) dY (by
            rw [topologicalKrullDim_pullback_of_isVariety,
              topologicalKrullDim_pullback_of_isVariety,
              topologicalKrullDim_pullback_of_isVariety, hdY]
            ac_rfl)) (k + dX)
        (flatPullbackChowOfRelativeDimension (fieldChowSituation K) (pullback.fst sX sZ ≫ sX) sZ
          (pullback.snd sX sZ) pullback.condition.symm dX
          (ExteriorProductProjections.relativeDimension_pullbackSnd sX sZ dX hdX) k c) := by
  obtain ⟨γ, rfl⟩ := QuotientAddGroup.mk'_surjective _ c
  rw [flatPullbackChowOfRelativeDimension_mk, flatPullbackChowOfRelativeDimension_mk,
    flatPullbackChowOfRelativeDimension_mk]
  refine mk_heq_of_apply_eq (fieldChowSituation K) _ (by push_cast; ring) fun x => ?_
  rw [flatPullback_comp_apply]
  exact flatPullback_apply_congr (fieldChowSituation K) _ sZ (tripleProj₁₃_snd sX sY sZ).symm _ _
    (by ring) _ _ k γ x

/-- `q₁₃,*` carries the graph of `f`, pushed into `(X × Y) × Z` along the graph of `g ∘ pr_Y`, to
the graph of `g ∘ f`. -/
theorem properChowPushforward_tripleProj₁₃_graphPush :
    properChowPushforward (fieldChowSituation K) _ (pullback.fst sX sZ ≫ sX)
        (tripleProj₁₃ sX sY sZ) (tripleProj₁₃_comp_structure sX sY sZ) (dX : ℤ)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K) _ _
          _ (tripleProj₁₃_comp_structure sX sY sZ) (dX : ℤ))
        (graphPush K (pullback.fst sX sY ≫ sX) sZ (pullback.snd sX sY ≫ g)
          (snd_comp_comp_structure g hg) (dX : ℤ) (graphClass K sX sY (dX := dX) f hf)) =
      graphClass K sX sZ (dX := dX) (f ≫ g) (by rw [Category.assoc, hg, hf]) := by
  have : IsClosedImmersion ((graph f hf ≫ graph (pullback.snd sX sY ≫ g)
      (snd_comp_comp_structure g hg)) ≫ tripleProj₁₃ sX sY sZ) := by
    rw [Category.assoc, graph_comp_graph_comp_tripleProj₁₃ f hf g hg]; infer_instance
  rw [graphClass, graphPush, properChowPushforward_mk, properChowPushforward_mk,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp, graphClass,
    cycleAssociatedToClosedSubscheme_of_hom_eq (fieldChowSituation K) (pullback.fst sX sZ ≫ sX)
      (by rw [Category.assoc, graph_comp_graph_comp_tripleProj₁₃ f hf g hg]) (dX : ℤ)]

include hX hY hZ hdX hdY hdZ in
/-- **Stacks Project, Tag 0B2X, part (2).** For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of
nonsingular projective varieties, `(g ∘ f)^* = f^* ∘ g^*` on Chow groups. On
`W = (X × Y) × Z`, `f^*(g^*c) = pr_{X,*}(q₁₂^*[Γ_f] · q₂₃^*[Γ_g] · q₃^* c)` by base change
(Tag 02RG), the projection formula for `q₁₂` (Tag 0B10) and Tag 0B0Z; the product
`q₁₂^*[Γ_f] · q₂₃^*[Γ_g]` is the transversal intersection `{(x, f(x), g(f(x)))}`, which `q₁₃`
maps isomorphically onto `Γ_{g ∘ f}`, and the projection formula for `q₁₃` gives `(g ∘ f)^* c`. -/
@[stacks 0B2X "part (2): `(g ∘ f)^* = f^* ∘ g^*` for a composable pair of morphisms of \
nonsingular projective varieties, on Chow groups `CH_k(Z) → CH_l(Y) → CH_m(X)` with \
`k + dim Y = dim Z + l`, `l + dim X = dim Y + m`"]
theorem chowPullback_comp {k l m : ℤ} (hkl : k + dY = dZ + l) (hlm : l + dX = dY + m)
    (hkm : k + dX = dZ + m) (c : chowGroup (fieldChowSituation K) sZ k) :
    chowPullback K sX sZ hX hZ hdX hdZ (f ≫ g) (by rw [Category.assoc, hg, hf]) hkm c =
      chowPullback K sX sY hX hY hdX hdY f hf hlm
        (chowPullback K sY sZ hY hZ hdY hdZ g hg hkl c) := by
  have hXY := isRegular_pullback_of_isRegular sX sY hX hY
  have hdXY := topologicalKrullDim_pullback_eq K sX sY hdX hdY
  have hXZ := isRegular_pullback_of_isRegular sX sZ hX hZ
  have hdXZ := topologicalKrullDim_pullback_eq K sX sZ hdX hdZ
  have hW := isRegular_pullback_of_isRegular (pullback.fst sX sY ≫ sX) sZ hXY hZ
  have hdW := topologicalKrullDim_pullback_eq K (pullback.fst sX sY ≫ sX) sZ hdXY hdZ
  have he12 : topologicalKrullDim (pullback (pullback.fst sX sY ≫ sX) sZ : Scheme.{u}) =
      topologicalKrullDim (pullback sX sY : Scheme.{u}) + (dZ : WithBot ℕ∞) := by
    rw [topologicalKrullDim_pullback_of_isVariety K (pullback.fst sX sY ≫ sX) sZ, hdZ]
  have he13 := (topologicalKrullDim_triple_pullback_eq K sX sY sZ hdX hdY).2
  rw [show chowPullback K sX sY hX hY hdX hdY f hf hlm
      (chowPullback K sY sZ hY hZ hdY hdZ g hg hkl c)
      = prXPush K sX sY m (chowMulFun K _ hXY m (graphClass K sX sY (dX := dX) f hf)
        (prYPullback K sX sY hdX l (chowPullback K sY sZ hY hZ hdY hdZ g hg hkl c))) from rfl,
    prYPullback_chowPullback K sX sY sZ hX hY hZ hdX hdY hdZ g hg hkl c]
  simp only [chowPullback, AddMonoidHom.comp_apply, chowMul_apply]
  set Γf := graphClass K sX sY (dX := dX) f hf
  set Γh := graphClass K (pullback.fst sX sY ≫ sX) sZ (dX := dX + dY) (pullback.snd sX sY ≫ g)
    (snd_comp_comp_structure g hg)
  set Q3 := flatPullbackChowOfRelativeDimension (fieldChowSituation K)
    (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX)) sZ
    (pullback.snd (pullback.fst sX sY ≫ sX) sZ) pullback.condition.symm (dX + dY)
    (ExteriorProductProjections.relativeDimension_pullbackSnd (pullback.fst sX sY ≫ sX) sZ
      (dX + dY) hdXY) k c
  set F := flatPullbackChowOfRelativeDimension (fieldChowSituation K)
    (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX))
    (pullback.fst sX sY ≫ sX) (pullback.fst (pullback.fst sX sY ≫ sX) sZ) rfl dZ
    (relativeDimension_of_flat_of_isVariety K
      (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX))
      (pullback.fst sX sY ≫ sX) (pullback.fst (pullback.fst sX sY ≫ sX) sZ) rfl dZ he12)
    (dX : ℤ) Γf
  rw [chowMulFun_comm (hX := hXY) hdXY (by push_cast; omega),
    ← properChowPushforward_chowMulFun K
      (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX))
      (pullback.fst sX sY ≫ sX) hW hXY (pullback.fst (pullback.fst sX sY ≫ sX) sZ)
      rfl dZ he12 hdXY (r := l + dX) (s := dX) (n := m) (by push_cast; omega)]
  have e1 := chowMulFun_assoc (hX := hW) hdW (m₁ := l + dX) (m₂ := k + dX) (m := m)
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) Γh Q3 F
  have e2 := chowMulFun_comm (hX := hW) hdW (m := k + dX) (by push_cast; omega) Q3 F
  have e3 := chowMulFun_assoc (hX := hW) hdW (m₁ := (dX : ℤ)) (m₂ := k + dX) (m := m)
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) Γh F Q3
  have e4 : chowMulFun K _ hW (dX : ℤ) Γh F =
      graphPush K (pullback.fst sX sY ≫ sX) sZ (pullback.snd sX sY ≫ g)
        (snd_comp_comp_structure g hg) (dX : ℤ) Γf :=
    chowMulFun_graphClass_prXPullback K (pullback.fst sX sY ≫ sX) sZ hXY hZ hdXY hdZ
      (pullback.snd sX sY ≫ g) (snd_comp_comp_structure g hg) (dX : ℤ) Γf
  rw [e1, e2, ← e3, e4, prXPush_properChowPushforward_tripleProj₁₂,
    chowMulFun_congr_heq (hX := hW) rfl (by push_cast; ring) HEq.rfl
      (flatPullback_snd_heq_tripleProj₁₃ K sX sY sZ hdX hdY c),
    properChowPushforward_chowMulFun K
      (pullback.fst (pullback.fst sX sY ≫ sX) sZ ≫ (pullback.fst sX sY ≫ sX))
      (pullback.fst sX sZ ≫ sX) hW hXZ (tripleProj₁₃ sX sY sZ)
      (tripleProj₁₃_comp_structure sX sY sZ) dY he13 hdXZ (r := (dX : ℤ)) (s := k + dX) (n := m)
      (by push_cast; omega),
    properChowPushforward_tripleProj₁₃_graphPush K sX sY sZ f hf g hg]

end Composition

end Stacks.Intersection.ChowRing

end

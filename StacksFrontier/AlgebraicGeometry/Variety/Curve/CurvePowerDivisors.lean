/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePower
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ClosedImmersionTransport
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorIntersectionProper
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.PicardForm
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackInvertible

/-!
# Graph divisors on the powers of a curve, and restriction of intersection numbers to them

Let `C` be a smooth proper curve over an algebraically closed field `k` and
`C^(m+1) = C ×_k C^m` (`Stacks.CurvePower.power`). For a morphism `y : C^m ⟶ C` over `k`, the
graph of `y`,

`Γ_y = {(c, x) ∈ C ×_k C^m : c = y(x)}`,

is a degree-one Hilbert family of `C` over `C^m`, hence an effective Cartier divisor on `C^(m+1)`
([Stacks, Tag 0B9D]); for `y` a coordinate it is a diagonal `Δ_{0,j+1}`, for `y` constant it is
a fibre `{c₀} × C^m`. The graph section `s_y : C^m ⟶ C^(m+1)`, `x ↦ (y(x), x)`, identifies `C^m`
with `Γ_y`, and the intersection numbers on `C^(m+1)` whose first entry is `𝒪(Γ_y)` are the
intersection numbers on `C^m` of the restrictions along `s_y`:

`(𝒪(Γ_y) · 𝓛_1 ⋯ 𝓛_m · C^(m+1)) = (s_y^*𝓛_1 ⋯ s_y^*𝓛_m · C^m)`

(`Stacks.CurvePower.intersectionNumber_graph`), by [Stacks, Tag 0BEU] and [Stacks, Tag 0BET].

## Main definitions

* `Stacks.CurvePower.graphFamily`: the degree-one family `Γ_y`.
* `Stacks.CurvePower.graphSection`: the section `s_y : C^m ⟶ C^(m+1)`.

## Main results

* `Stacks.CurvePower.intersectionNumber_graph`: intersection numbers on `C^(m+1)` with first entry
  `𝒪(Γ_y)` are intersection numbers on `C^m` of the restrictions along `s_y`.
* `Stacks.CurvePower.powerForm_cons_graph`: the same statement for the intersection form on
  Picard classes.
* `Stacks.CurvePower.powerForm_reindex`: the intersection form of `C^m` is invariant under
  permutations of the coordinates.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.CurvePower

variable {k : Type u} [Field k] [IsAlgClosed k] (C : Over (Spec (.of k))) [IsVariety k C.hom]
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]

/-- **The graph of `y : C^m ⟶ C`**, a degree-one Hilbert family of `C` over `C^m`. -/
def graphFamily (m : ℕ) (y : power C m ⟶ C) : Stacks.Hilbert.HilbertFamily C (power C m) 1 where
  ideal := Stacks.Hilbert.pointIdeal C (power C m) y
  isFiniteLocallyFreeOfRank :=
    haveI := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C m) y
    Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal _ _ _

/-- The graph of `y : C^m ⟶ C` is an effective Cartier divisor on `C^(m+1)`. -/
instance isEffectiveCartierDivisor_graph (m : ℕ) (y : power C m ⟶ C) :
    Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Hilbert.pointIdeal C (power C m) y) :=
  (graphFamily C m y).isEffectiveCartierDivisor_ideal

/-- **The graph section** `s_y : C^m ⟶ C^(m+1)`, `x ↦ (y(x), x)`. -/
abbrev graphSection (m : ℕ) (y : power C m ⟶ C) : (power C m).left ⟶ (power C (m + 1)).left :=
  Stacks.Hilbert.pointGraph C (power C m) y

/-- The graph section is a closed immersion. -/
instance isClosedImmersion_graphSection (m : ℕ) (y : power C m ⟶ C) :
    IsClosedImmersion (graphSection C m y) :=
  Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C m) y

omit [IsAlgClosed k] [IsVariety k C.hom] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
/-- The graph section is a morphism over `k`. -/
theorem graphSection_comp_hom (m : ℕ) (y : power C m ⟶ C) :
    graphSection C m y ≫ (power C (m + 1)).hom = (power C m).hom := by
  change Stacks.Hilbert.pointGraph C (power C m) y ≫
    (pullback.fst C.hom (power C m).hom ≫ C.hom) = _
  rw [pullback.condition, ← Category.assoc, Stacks.Hilbert.pointGraph_comp_snd, Category.id_comp]

omit [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] in
variable {C} in
/-- The dimension of `C^m` for a curve `C`. -/
theorem topologicalKrullDim_power (hC : topologicalKrullDim C.left = 1) (m : ℕ) :
    topologicalKrullDim (power C m).left = (m : WithBot ℕ∞) := by
  rw [(isVariety_power_and_topologicalKrullDim C m).2, hC, mul_one]

/-- **Restriction of intersection numbers to a graph divisor.** For `𝓛_0 ≅ 𝒪(Γ_y)`,
`(𝓛_0 · 𝓛_1 ⋯ 𝓛_m · C^(m+1)) = (s_y^*𝓛_1 ⋯ s_y^*𝓛_m · C^m)`. -/
theorem intersectionNumber_graph (hC : topologicalKrullDim C.left = 1) (m : ℕ)
    (y : power C m ⟶ C) (L : Fin (m + 1) → (power C (m + 1)).left.Modules)
    [∀ q, SheafOfModules.IsInvertible (power C (m + 1)).left.presheaf
      (power C (m + 1)).left.ringCatSheaf.2 (L q)]
    (hL0 : L 0 ≅ (Stacks.Divisors.invertibleSheaf (Stacks.Hilbert.pointIdeal C (power C m) y) :
      (power C (m + 1)).left.Modules)) :
    intersectionNumber k (power C (m + 1)).hom (𝟙 _) (m + 1)
        (topologicalKrullDim_power hC (m + 1)).le L =
      intersectionNumber k (power C m).hom (𝟙 _) m (topologicalKrullDim_power hC m).le
        (fun q => (Scheme.Modules.pullback (graphSection C m y)).obj (L q.succ)) := by
  set Dv : (power C (m + 1)).left.IdealSheafData := Stacks.Hilbert.pointIdeal C (power C m) y
  have : Stacks.Divisors.IsEffectiveCartierDivisor Dv := isEffectiveCartierDivisor_graph C m y
  have h1 := intersectionNumber_eq_of_isEffectiveCartierDivisor' k (power C (m + 1)).hom
    (𝟙 _) m (topologicalKrullDim_power hC (m + 1)).le L Dv
    (((Scheme.Modules.pullbackId _).app (L 0)) ≪≫ hL0)
  rw [h1, intersectionNumber_congr_immersion k _ (Category.comp_id Dv.subschemeι) m _
    (fun t : Fin m => L t.succ)]
  have h2 := intersectionNumber_subschemeι_ker_eq k (power C (m + 1)).hom (graphSection C m y) m
    (topologicalKrullDim_power hC m)
    (topologicalKrullDim_subscheme_le_of_isEffectiveCartierDivisor_of_isProper k
      (power C (m + 1)).hom (𝟙 _) m (topologicalKrullDim_power hC (m + 1)).le Dv)
    (fun q : Fin m => L q.succ)
  refine Eq.trans ?_ (h2.symm.trans
    (intersectionNumber_congr_structure k (graphSection_comp_hom C m y) _ m _ _))
  rfl

/-- The intersection form of `C^m` on Picard classes. -/
abbrev powerForm (hC : topologicalKrullDim C.left = 1) (m : ℕ) :
    MultilinearMap ℤ (fun _ : Fin m =>
      Stacks.SheafOfModules.PicardGroup (power C m).left.presheaf
        (power C m).left.ringCatIsSheaf) ℤ :=
  picardIntersection k (power C m).hom (𝟙 _) m (topologicalKrullDim_power hC m).le

/-- The pullback along `f` of the representative of a Picard class is isomorphic to the
representative of the pulled-back class. -/
theorem nonempty_pullback_picardRep_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : Stacks.SheafOfModules.PicardGroup Y.presheaf Y.ringCatIsSheaf) :
    Nonempty ((Scheme.Modules.pullback f).obj (picardRep x) ≅
      picardRep (Stacks.Picard.schemePullbackClass f x)) := by
  have hinv : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj (picardRep x)) :=
    RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ _
  have h := nonempty_picardRep_picardClass_iso ((Scheme.Modules.pullback f).obj (picardRep x)) hinv
  have hcl : Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
      ((Scheme.Modules.pullback f).obj (picardRep x)) hinv =
      Stacks.Picard.schemePullbackClass f x := by
    have := Stacks.Picard.pullbackClass_classOf f.toLRSHom.toShHom (picardRep x)
      (isInvertible_picardRep x)
    rw [picardClass_picardRep] at this
    exact this.symm
  rw [hcl] at h
  exact ⟨h.some.symm⟩

/-- **Restriction of the intersection form to a graph divisor**, on Picard classes:
`([𝒪(Γ_y)] · x_1 ⋯ x_m · C^(m+1)) = (s_y^*x_1 ⋯ s_y^*x_m · C^m)`. -/
theorem powerForm_cons_graph (hC : topologicalKrullDim C.left = 1) (m : ℕ) (y : power C m ⟶ C)
    (x : Fin m → Stacks.SheafOfModules.PicardGroup (power C (m + 1)).left.presheaf
      (power C (m + 1)).left.ringCatIsSheaf) :
    powerForm C hC (m + 1)
        (Fin.cons (@Stacks.Divisors.picardClass _ (Stacks.Hilbert.pointIdeal C (power C m) y)
          (isEffectiveCartierDivisor_graph C m y)) x) =
      powerForm C hC m (fun q => Stacks.Picard.schemePullbackClass (graphSection C m y) (x q)) := by
  rw [powerForm, powerForm, picardIntersection_apply, picardIntersection_apply]
  have h0 : Nonempty (picardRep (Fin.cons (α := fun _ => Stacks.SheafOfModules.PicardGroup
      (power C (m + 1)).left.presheaf (power C (m + 1)).left.ringCatIsSheaf)
      (@Stacks.Divisors.picardClass _ (Stacks.Hilbert.pointIdeal C (power C m) y)
        (isEffectiveCartierDivisor_graph C m y)) x 0) ≅
      (Stacks.Divisors.invertibleSheaf (Stacks.Hilbert.pointIdeal C (power C m) y) :
        (power C (m + 1)).left.Modules)) :=
    nonempty_picardRep_picardClass_iso _ _
  rw [intersectionNumber_graph C hC m y _ h0.some]
  exact intersectionNumber_eq_of_forall_iso k _ _ m _ _ _ fun q =>
    nonempty_pullback_picardRep_iso _ _

/-- Reindexing by a permutation is an isomorphism of `C^m`. -/
instance isIso_reindex_perm (m : ℕ) (σ : Equiv.Perm (Fin m)) : IsIso (reindex C σ) :=
  ⟨⟨reindex C σ.symm, by rw [reindex_comp]; simp [reindex_id],
    by rw [reindex_comp]; simp [reindex_id]⟩⟩

/-- The underlying morphism of schemes of a reindexing by a permutation is an isomorphism. -/
instance isIso_reindex_perm_left (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    IsIso (reindex C σ).left :=
  inferInstanceAs (IsIso ((Over.forget _).map (reindex C σ)))

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- **The intersection form of `C^m` is invariant under permutations of the coordinates.** -/
theorem powerForm_reindex (hC : topologicalKrullDim C.left = 1) (m : ℕ) (σ : Equiv.Perm (Fin m))
    (x : Fin m → Stacks.SheafOfModules.PicardGroup (power C m).left.presheaf
      (power C m).left.ringCatIsSheaf) :
    powerForm C hC m (fun q => Stacks.Picard.schemePullbackClass (reindex C σ).left (x q)) =
      powerForm C hC m x := by
  set j := (reindex C σ).left
  rw [powerForm, picardIntersection_apply, picardIntersection_apply,
    ← intersectionNumber_eq_of_forall_iso k _ _ m _
      (fun q => (Scheme.Modules.pullback j).obj (picardRep (x q))) _
      (fun q => nonempty_pullback_picardRep_iso j (x q))]
  have hw : j ≫ (power C m).hom = (power C m).hom := Over.w (reindex C σ)
  have : IsIntegral (power C m).left := (isVariety_power C m).toIsIntegral
  have hker : topologicalKrullDim j.ker.subscheme ≤ (m : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_power hC m]
    exact j.ker.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le
  have h2 := intersectionNumber_subschemeι_ker_eq k (power C m).hom j m
    (topologicalKrullDim_power hC m) hker (fun q => picardRep (x q))
  rw [← intersectionNumber_congr_structure k hw _ m _ _, h2]
  have : IsIso j.ker.subschemeι := by
    have hiso : IsIso j.toImage :=
      IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι
        (Scheme.IdealSheafData.ker_subschemeι j.ker).symm
    have : j.ker.subschemeι = inv j.toImage ≫ j := by
      rw [IsIso.eq_inv_comp, j.toImage_imageι]
    rw [this]
    infer_instance
  have : IsLocallyNoetherian (power C m).left :=
    LocallyOfFiniteType.isLocallyNoetherian (power C m).hom
  exact intersectionNumber_eq_intersectionNumber_id k _ _ m _ _ _

end Stacks.CurvePower

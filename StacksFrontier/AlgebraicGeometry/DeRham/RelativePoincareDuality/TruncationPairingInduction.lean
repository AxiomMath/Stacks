module

public import
  StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TruncationPairingCompatibility
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.PushedPairingFiveLemma

/-!
# The induction over the stupid truncations

Let `Z` be a ringed space, `K`, `L`, `M` cochain complexes of `𝒪_Z`-modules, `K` vanishing in
negative degrees and `L` and `M` above `n`, and `g : Tot(K ⊗ L) ⟶ M` a morphism of complexes.
Push the pairings `Q(σ^{≤p}K) ⊗^L Q(σ^{≥q}L) ⟶ QM` (`p + q = n`) of the products
`StacksDraft.StupidTruncation.truncMul` along any push data
(`CategoryTheory.Functor.PairingPushData`)
for the derived tensor product. If the pushed pairings of the graded pieces
`Q(K^p[-p]) ⊗^L Q(L^q[-q]) ⟶ QM` are perfect at every shift, then so are those of all the
truncations: this is the induction on `p` in the proof of [Stacks, Tag 0G8K], whose steps are
the five lemma (`CategoryTheory.Functor.PairingPushData.allPerf_of_triangles_neg`) along the
distinguished triangles of the stupid filtrations of `K` and `L`, starting from `p = -1`, where
both truncations vanish.

## Main results

* `StacksDraft.StupidTruncation.pairingCompatible_stupidTruncLEι` and
  `StacksDraft.StupidTruncation.pairingCompatible_stupidTruncLEMapLE`: the compatibilities (b)
  and (c) of the proof of [Stacks, Tag 0G8K].
* `StacksDraft.StupidTruncation.allPerf_truncMul_of_graded`: the induction.
* `StacksDraft.StupidTruncation.allPerf_toTensor_of_graded`: at the end of the induction, the
  pairing `QK ⊗^L QL ⟶ QM` of `g` itself.
* `CategoryTheory.Functor.PairingPushData.allPerf_iff_of_pairingCompatible`: perfectness at every
  shift is invariant under isomorphisms of the paired objects.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace HomologicalComplex ComplexShape
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)

universe u

namespace CategoryTheory.Functor.PairingPushData

variable {C₁ C₂ C D : Type*} [Category* C₁] [Category* C₂] [Category* C] [Category* D]
  [HasZeroObject C₁] [HasZeroObject C₂] [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ]
  [∀ n : ℤ, (shiftFunctor C₁ n).Additive] [∀ n : ℤ, (shiftFunctor C₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂]
  {T : C₁ ⥤ C₂ ⥤ C} {T' : D ⥤ D ⥤ D} {R : C ⥤ D}
  [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [T.CommShift₂Int]
  [∀ Z : D, (T'.obj Z).Additive]

/-- A pairing between zero objects is perfect at every shift. -/
theorem allPerf_of_isZero (P₀ : PairingPushData T T' R) {K : C₁} {L : C₂} {M : C} {N : D}
    (τ : R.obj M ⟶ N) (β : (T.obj K).obj L ⟶ M) (hK : IsZero K) (hL : IsZero L) :
    P₀.AllPerf τ β := fun P _ Z =>
  have hK' : IsZero (P.R₁.obj K) := P.R₁.map_isZero hK
  have hL' : IsZero ((T'.obj Z).obj (P.R₂.obj L)) := (T'.obj Z).map_isZero (P.R₂.map_isZero hL)
  ⟨fun a b _ => hK'.eq_of_tgt a b, fun _ => ⟨0, hL'.eq_of_src _ _⟩⟩

/-- **Perfectness at every shift is invariant under isomorphisms of the paired objects**: for
pairings compatible along isomorphisms `e : K ⟶ K'` and `e' : L' ⟶ L`. -/
theorem allPerf_iff_of_pairingCompatible (P₀ : PairingPushData T T' R) {K K' : C₁} {L L' : C₂}
    {M : C} {N : D} (τ : R.obj M ⟶ N) {β : (T.obj K).obj L ⟶ M} {β' : (T.obj K').obj L' ⟶ M}
    (e : K ⟶ K') (e' : L' ⟶ L) [IsIso e] [IsIso e'] (h : T.PairingCompatible β β' e e') :
    P₀.AllPerf τ β ↔ P₀.AllPerf τ β' := by
  have key : ∀ (P : PairingPushData T T' R) (Z : D),
      Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β) Z) ↔
        Function.Bijective (T'.pairingPrecomp (P.pushedPairing τ β') Z) := by
    intro P Z
    have hc := P.pairingCompatible_pushedPairing τ h
    have hA : Function.Bijective (fun v : Z ⟶ P.R₁.obj K => v ≫ P.R₁.map e) :=
      (asIso (P.R₁.map e)).homToEquiv.bijective
    have hB : Function.Bijective (fun w : (T'.obj Z).obj (P.R₂.obj L) ⟶ N =>
        (T'.obj Z).map (P.R₂.map e') ≫ w) :=
      ((T'.obj Z).mapIso (asIso (P.R₂.map e'))).homFromEquiv.symm.bijective
    have hcomp : T'.pairingPrecomp (P.pushedPairing τ β') Z ∘ (fun v => v ≫ P.R₁.map e) =
        (fun w => (T'.obj Z).map (P.R₂.map e') ≫ w) ∘ T'.pairingPrecomp (P.pushedPairing τ β) Z :=
      funext fun v => hc.pairingPrecomp_comp v
    rw [← Function.Bijective.of_comp_iff _ hA, hcomp, Function.Bijective.of_comp_iff' hB]
  exact ⟨fun hβ P hP Z => (key P Z).1 (hβ P hP Z), fun hβ P hP Z => (key P Z).2 (hβ P hP Z)⟩

end CategoryTheory.Functor.PairingPushData

namespace StacksDraft.StupidTruncation

section Derived

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Abelian C₁] [Abelian C₂] [Abelian D] {hD : HasDerivedCategory D}
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  [∀ (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ), HasMapBifunctor K L F (up ℤ)]
  {K : CochainComplex C₁ ℤ} {L : CochainComplex C₂ ℤ} {M : CochainComplex D ℤ}
  (g : mapBifunctor K L F (up ℤ) ⟶ M) {n : ℤ} (hM : ∀ k, n < k → IsZero (M.X k))

/-- `mapBifunctorMap_stupidTruncLEι_truncMul` in the derived category. -/
theorem Q_map_comp_stupidTruncLEι (p q : ℤ) (hpq : p + q = n) :
    (DerivedCategory.Q (C := D)).map (mapBifunctorMap (stupidTruncLEι K p) (𝟙 _) F (up ℤ)) ≫
        (DerivedCategory.Q (C := D)).map (truncMul F g hM p q hpq) =
      (DerivedCategory.Q (C := D)).map (mapBifunctorMap (𝟙 _) (stupidTruncGEπ L q) F (up ℤ)) ≫
        (DerivedCategory.Q (C := D)).map (gradedMul F g hM p q hpq) :=
  (Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (mapBifunctorMap_stupidTruncLEι_truncMul F g hM p q hpq)).trans
      (Functor.map_comp _ _ _))

/-- `mapBifunctorMap_stupidTruncLEMapLE_truncMul` in the derived category. -/
theorem Q_map_comp_stupidTruncLEMapLE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    (DerivedCategory.Q (C := D)).map (mapBifunctorMap
        (stupidTruncLEMapLE K (show p' ≤ p' + 1 by omega)) (𝟙 _) F (up ℤ)) ≫
        (DerivedCategory.Q (C := D)).map (truncMul F g hM p' (q + 1) (by omega)) =
      (DerivedCategory.Q (C := D)).map (mapBifunctorMap (𝟙 _)
        (stupidTruncGEMapLE L (show q ≤ q + 1 by omega)) F (up ℤ)) ≫
        (DerivedCategory.Q (C := D)).map (truncMul F g hM (p' + 1) q hpq) :=
  (Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (mapBifunctorMap_stupidTruncLEMapLE_truncMul F g hM (p' + 1) p' rfl q hpq)).trans
      (Functor.map_comp _ _ _))

/-- `mapBifunctorMap_πStupidTrunc_truncMul` in the derived category. -/
theorem Q_map_comp_πStupidTrunc (p q : ℤ) (hpq : p + q = n) :
    (DerivedCategory.Q (C := D)).map (mapBifunctorMap (K.πStupidTrunc (embeddingUpIntLE p))
        (𝟙 (L.stupidTrunc (embeddingUpIntGE q))) F (up ℤ)) ≫
        (DerivedCategory.Q (C := D)).map (truncMul F g hM p q hpq) =
      (DerivedCategory.Q (C := D)).map (mapBifunctorMap (𝟙 K)
        (ιStupidTrunc L (embeddingUpIntGE q)) F (up ℤ)) ≫ (DerivedCategory.Q (C := D)).map g :=
  (Functor.map_comp _ _ _).symm.trans
    ((congrArg _ (mapBifunctorMap_πStupidTrunc_truncMul F g hM p q hpq)).trans
      (Functor.map_comp _ _ _))

end Derived

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {K L M : CochainComplex (ModulesOn Z) ℤ}
  (g : ((tensorComplexBifunctorOn Z).obj K).obj L ⟶ M) {n : ℤ}
  (hM : ∀ k, n < k → IsZero (M.X k))

/-- Pairings induced by maps `φ`, `φ'` of complexes are compatible once the maps of complexes
are, in the derived category. -/
private theorem pairingCompatible_toTensor_of_Q_map_comp
    {K₁ K₂ L₁ L₂ : CochainComplex (ModulesOn Z) ℤ} (f : K₁ ⟶ K₂) (f' : L₂ ⟶ L₁)
    (φ : mapBifunctor K₁ L₁ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)
      (up ℤ) ⟶ M)
    (φ' : mapBifunctor K₂ L₂ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)
      (up ℤ) ⟶ M)
    (h : DerivedCategory.Q.map (mapBifunctorMap f (𝟙 L₂)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (up ℤ)) ≫
        DerivedCategory.Q.map φ' =
      DerivedCategory.Q.map (mapBifunctorMap (𝟙 K₁) f'
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (up ℤ)) ≫
        DerivedCategory.Q.map φ) :
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor K₁ L₁ ≫ DerivedCategory.Q.map φ)
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor K₂ L₂ ≫ DerivedCategory.Q.map φ')
      (DerivedCategory.Q.map f) (DerivedCategory.Q.map f') := by
  have h₁ := (canonicalDerivedTensorProduct Z.sheaf).toTensor_naturality f (𝟙 L₂)
  have h₂ := (canonicalDerivedTensorProduct Z.sheaf).toTensor_naturality (𝟙 K₁) f'
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h₁ h₂
  unfold Functor.PairingCompatible
  rw [reassoc_of% h₁, reassoc_of% h₂]
  exact (Category.assoc _ _ _).trans ((congrArg _ h).trans (Category.assoc _ _ _).symm)

include hM in
/-- **The pairings of the top term of `σ^{≤p}K` and of the truncation are compatible along
`K^p[-p] ⟶ σ^{≤p}K` and `σ^{≥q}L ⟶ L^q[-q]`.** -/
theorem pairingCompatible_stupidTruncLEι (p q : ℤ) (hpq : p + q = n) :
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor
          ((single (ModulesOn Z) (up ℤ) p).obj (K.X p))
          ((single (ModulesOn Z) (up ℤ) q).obj (L.X q)) ≫
        DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p q hpq))
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE p))
          (L.stupidTrunc (embeddingUpIntGE q)) ≫
        DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p q hpq))
      (DerivedCategory.Q.map (stupidTruncLEι K p))
      (DerivedCategory.Q.map (stupidTruncGEπ L q)) := by
  exact pairingCompatible_toTensor_of_Q_map_comp Z _ _ _ _
    (Q_map_comp_stupidTruncLEι _ g hM p q hpq)

include hM in
/-- **The pairings of the truncations are compatible along `σ^{≤p}K ⟶ σ^{≤p'}K` and
`σ^{≥q+1}L ⟶ σ^{≥q}L`** (`p' + 1 = p`). -/
theorem pairingCompatible_stupidTruncLEMapLE (p' q : ℤ) (hpq : p' + 1 + q = n) :
    (derivedTensorProductFunctor Z.sheaf).PairingCompatible
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE (p' + 1)))
          (L.stupidTrunc (embeddingUpIntGE q)) ≫
        DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM (p' + 1) q hpq))
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor (K.stupidTrunc (embeddingUpIntLE p'))
          (L.stupidTrunc (embeddingUpIntGE (q + 1))) ≫
        DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p' (q + 1) (by omega)))
      (DerivedCategory.Q.map (stupidTruncLEMapLE K (show p' ≤ p' + 1 by omega)))
      (DerivedCategory.Q.map (stupidTruncGEMapLE L (show q ≤ q + 1 by omega))) := by
  exact pairingCompatible_toTensor_of_Q_map_comp Z _ _ _ _
    (Q_map_comp_stupidTruncLEMapLE _ g hM p' q hpq)

include hM in
/-- **The induction over the stupid truncations** ([Stacks, Tag 0G8K]). Let `K` vanish in
negative degrees and `L` above `n`. If the pushed pairings of the graded pieces
`Q(K^p[-p]) ⊗^L Q(L^q[-q]) ⟶ QM`, `p + q = n`, `p, q ≥ 0`, are perfect at every shift, then so are
those of the truncations `Q(σ^{≤p}K) ⊗^L Q(σ^{≥q}L) ⟶ QM` for `p ≥ -1`, `q ≥ 0`. -/
theorem allPerf_truncMul_of_graded {D' : Type*} [Category* D'] [Preadditive D']
    {T' : D' ⥤ D' ⥤ D'} [∀ X, (T'.obj X).Additive] [∀ Y, (T'.flip.obj Y).Additive]
    {R : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} Z.sheaf ⥤ D'} [R.Additive]
    (P₀ : Functor.PairingPushData (derivedTensorProductFunctor Z.sheaf) T' R) {N : D'}
    (τ : R.obj (DerivedCategory.Q.obj M) ⟶ N) (hK : ∀ k, k < 0 → IsZero (K.X k))
    (hL : ∀ k, n < k → IsZero (L.X k))
    (hgr : ∀ (p q : ℤ) (hpq : p + q = n), 0 ≤ p → 0 ≤ q →
      letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
      P₀.AllPerf τ ((canonicalDerivedTensorProduct Z.sheaf).toTensor
          ((single (ModulesOn Z) (up ℤ) p).obj (K.X p))
          ((single (ModulesOn Z) (up ℤ) q).obj (L.X q)) ≫
        DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p q hpq)))
    (p q : ℤ) (hpq : p + q = n) (hp : -1 ≤ p) (hq : 0 ≤ q) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    P₀.AllPerf τ ((canonicalDerivedTensorProduct Z.sheaf).toTensor
        (K.stupidTrunc (embeddingUpIntLE p)) (L.stupidTrunc (embeddingUpIntGE q)) ≫
      DerivedCategory.Q.map (truncMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        Z.sheaf) g hM p q hpq)) := by
  let := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
  induction p, hp using Int.leInduction generalizing q with
  | base =>
    refine P₀.allPerf_of_isZero τ _ (Functor.map_isZero _ ?_) (Functor.map_isZero _ ?_)
    · refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i => ?_)
      by_cases hi : i ≤ -1
      · exact ((hK i (by omega)).of_iso (stupidTruncLEXIso K (-1) i hi)).eq_of_src _ _
      · exact (CochainComplex.isZero_of_isStrictlyLE
          (K.stupidTrunc (embeddingUpIntLE (-1))) (-1) i (by omega)).eq_of_src _ _
    · refine (IsZero.iff_id_eq_zero _).2 (HomologicalComplex.hom_ext _ _ fun i => ?_)
      by_cases hi : q ≤ i
      · exact ((hL i (by omega)).of_iso (stupidTruncGEXIso L q i hi)).eq_of_src _ _
      · exact (CochainComplex.isZero_of_isStrictlyGE
          (L.stupidTrunc (embeddingUpIntGE q)) q i (by omega)).eq_of_src _ _
  | succ p' hp' ih =>
    exact P₀.allPerf_of_triangles_neg τ _
      (stupidTruncLESplitTriangleQ_distinguished K (p' + 1) p' rfl)
      _ (stupidTruncGESplitTriangleQ_distinguished L q)
      (pairingCompatible_connectingGE Z g hM p' q hpq)
      (pairingCompatible_stupidTruncLEι Z g hM (p' + 1) q hpq)
      (pairingCompatible_stupidTruncLEMapLE Z g hM p' q hpq)
      (pairingCompatible_connectingLE Z g hM p' q hpq)
      (hgr (p' + 1) q hpq (by omega) hq) (ih (q + 1) (by omega) (by omega))

include hM in
/-- **The pairing of a product perfect at every shift, from its graded pieces** ([Stacks,
Tag 0G8K]). Let `K` and `L` vanish in negative degrees and above `n ≥ 0`, and `M` above `n`. If
the pushed pairings of the graded pieces `Q(K^p[-p]) ⊗^L Q(L^q[-q]) ⟶ QM`, `p + q = n`,
`p, q ≥ 0`, of `g : Tot(K ⊗ L) ⟶ M` are perfect at every shift, then so is that of the pairing
`QK ⊗^L QL ⟶ Q(Tot(K ⊗ L)) ⟶ QM` itself. -/
theorem allPerf_toTensor_of_graded {D' : Type*} [Category* D'] [Preadditive D']
    {T' : D' ⥤ D' ⥤ D'} [∀ X, (T'.obj X).Additive] [∀ Y, (T'.flip.obj Y).Additive]
    {R : Stacks.DerivedTensor.RingedSite.DerivedModules.{u + 1, u} Z.sheaf ⥤ D'} [R.Additive]
    (P₀ : Functor.PairingPushData (derivedTensorProductFunctor Z.sheaf) T' R) {N : D'}
    (τ : R.obj (DerivedCategory.Q.obj M) ⟶ N) (hn : 0 ≤ n) (hK₀ : ∀ k, k < 0 → IsZero (K.X k))
    (hK : ∀ k, n < k → IsZero (K.X k)) (hL₀ : ∀ k, k < 0 → IsZero (L.X k))
    (hL : ∀ k, n < k → IsZero (L.X k))
    (hgr : ∀ (p q : ℤ) (hpq : p + q = n), 0 ≤ p → 0 ≤ q →
      letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
      P₀.AllPerf τ ((canonicalDerivedTensorProduct Z.sheaf).toTensor
          ((single (ModulesOn Z) (up ℤ) p).obj (K.X p))
          ((single (ModulesOn Z) (up ℤ) q).obj (L.X q)) ≫
        DerivedCategory.Q.map (gradedMul (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          Z.sheaf) g hM p q hpq))) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    P₀.AllPerf τ
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor K L ≫ DerivedCategory.Q.map g) := by
  let := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
  have hπ : IsIso (K.πStupidTrunc (embeddingUpIntLE n)) := by
    have : ∀ i, IsIso ((K.πStupidTrunc (embeddingUpIntLE n)).f i) := fun i => by
      by_cases hi : i ≤ n
      · exact isIso_πStupidTruncLE_f K n i hi
      · exact IsZero.isIso (hK i (by omega)) (CochainComplex.isZero_of_isStrictlyLE
          (K.stupidTrunc (embeddingUpIntLE n)) n i (by omega)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  have hι : IsIso (ιStupidTrunc L (embeddingUpIntGE 0)) := by
    have : ∀ i, IsIso ((ιStupidTrunc L (embeddingUpIntGE 0)).f i) := fun i => by
      by_cases hi : 0 ≤ i
      · rw [ιStupidTruncGE_f L 0 i hi]
        infer_instance
      · exact IsZero.isIso (CochainComplex.isZero_of_isStrictlyGE
          (L.stupidTrunc (embeddingUpIntGE 0)) 0 i (by omega)) (hL₀ i (by omega)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  exact (P₀.allPerf_iff_of_pairingCompatible τ
    (DerivedCategory.Q.map (K.πStupidTrunc (embeddingUpIntLE n)))
    (DerivedCategory.Q.map (ιStupidTrunc L (embeddingUpIntGE 0)))
    (pairingCompatible_toTensor_of_Q_map_comp Z _ _ _ _
      (Q_map_comp_πStupidTrunc _ g hM n 0 (add_zero n)))).2
    (allPerf_truncMul_of_graded Z g hM P₀ τ hK₀ hL hgr n 0 (add_zero n) (by omega) le_rfl)

end StacksDraft.StupidTruncation

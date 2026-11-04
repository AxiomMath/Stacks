module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.EulerCharacteristicFieldSpectrum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.IntersectionNumberDivisorSum
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberProperImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.IteratedFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.CycleResidueDegreeSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowGroupZeroDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroCycleDegree

/-!
# Intersection numbers of integral closed subspaces as degrees of iterated cap products

Let `X` be proper over a field `k`, `W ⊆ X` an integral closed subspace of dimension `e` and
`ℒ₁, …, ℒ_e` invertible. Then `(ℒ₁ ⋯ ℒ_e · W) = deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_e) ∩ [W])`.

The proof is by induction on `e`. The cap product with `c₁(ℒ_e)` sends `[W]` to the pushforward
of `div_{ℒ_e|_W}(t_W) = ∑_Z ord_Z(t_W) [Z]`, and the degree of the remaining iterated cap is
additive, so the right hand side is `∑_Z ord_Z(t_W) (ℒ₁ ⋯ ℒ_{e-1} · Z)` by induction. The left
hand side is the same sum by
`AlgebraicGeometry.Space.twistedEulerMixedDifference_cons_eq_finsum_divisorCycleCoefficients`,
after moving `ℒ_e` to the front and restricting to `W`. In dimension zero the intersection number
is `χ(W, 𝒪_W)`, which Stacks 0EDJ along `X ⟶ Spec k` computes as the degree of `W` over `k`
times `χ(Spec k, 𝒪) = 1`. A closed subspace is reduced to its components by Stacks 0EDE.

## Main definitions

* `AlgebraicGeometry.Space.iteratedFirstChernCapDegree`: the degree of the iterated cap product.

## Main results

* `AlgebraicGeometry.Space.map_cycle_eq_finsum_of_compactSpace`.
* `AlgebraicGeometry.Space.integralClosedSubspaceIntersectionNumber_eq_iteratedFirstChernCapDegree`.
* `AlgebraicGeometry.Space.intersectionNumber_eq_iteratedFirstChernCapDegree_closedSubspaceCycle`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Decomposition

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)

/-- **An additive map on the cycles of a quasi-compact space is determined by the integral
cycles.** If `φ [Z] = ψ(Z)` for every integral closed subspace of δ-dimension `k`, then
`φ α = ∑_Z α_Z ψ(Z)`. -/
theorem map_cycle_eq_finsum_of_compactSpace {k : ℤ}
    [CompactSpace (points D.site D.base D.base_mem X)] (φ : CycleGroup D sX k →+ ℤ)
    (ψ : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hψ : ∀ Z (hZ : deltaDimension D sX Z = k), φ (integralCycle D sX k Z hZ) = ψ Z)
    (α : CycleGroup D sX k) :
    φ α = ∑ᶠ Z, α.1 Z * ψ Z := by
  classical
  set s := (finite_support_of_compactSpace D sX k α).toFinset with hs
  let c : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sX k := fun Z =>
    if h : deltaDimension D sX Z = k then integralCycle D sX k Z h else 0
  have hα : α = ∑ Z ∈ s, α.1 Z • c Z := by
    refine Subtype.ext (funext fun W => ?_)
    rw [AddSubgroup.val_finset_sum, Finset.sum_apply]
    have hterm : ∀ Z ∈ s, ((α.1 Z • c Z : CycleGroup D sX k) : _ → ℤ) W =
        if Z = W then α.1 W else 0 := by
      intro Z hZ
      have hZ' : α.1 Z ≠ 0 := (Set.Finite.mem_toFinset _).1 hZ
      have hδ := α.2.2 Z hZ'
      simp only [c, dif_pos hδ, AddSubgroup.coe_zsmul, Pi.smul_apply, integralCycle_coe,
        integralCycleCoeff, smul_eq_mul]
      split_ifs with h₁ h₂ h₂
      · subst h₁; ring
      · exact absurd h₁.symm h₂
      · exact absurd h₂.symm h₁
      · ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    split_ifs with hW
    · rfl
    · exact not_not.1 fun h => hW ((Set.Finite.mem_toFinset _).2 h)
  conv_lhs => rw [hα, map_sum]
  rw [finsum_eq_sum_of_support_subset _ (s := s) ?_]
  · refine Finset.sum_congr rfl fun Z hZ => ?_
    have hZ' : α.1 Z ≠ 0 := (Set.Finite.mem_toFinset _).1 hZ
    rw [map_zsmul, smul_eq_mul]
    simp only [c, dif_pos (α.2.2 Z hZ'), hψ]
  · intro Z hZ
    exact (Set.Finite.mem_toFinset _).2 (left_ne_zero_of_mul hZ)

/-- Pushing a cycle forward from an integral closed subspace `W ⊆ X` and pairing its
coefficients with a function on the integral closed subspaces of `X` is pairing the original
coefficients with the function read on the images. -/
theorem finsum_integralClosedSubspacePushforward_mul (hX : D.IsGood sX)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (G : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) :
    ∑ᶠ V, (integralClosedSubspacePushforward D sX hX W k c).1 V * G V =
      ∑ᶠ V : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor,
        c.1 V * G (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 V) := by
  have hdecX := D.isDecentSpace_of_isGood sX hX
  set push := IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
    W.isClosedSubspace.1 hdecX W.isClosedSubspace.2 with hpush
  have hinj : Function.Injective push := IntegralClosedSubspace.injective_pushforward D.site
    D.base D.base_mem hX.1 W.isClosedSubspace.1 hdecX W.isClosedSubspace.2
  set F : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ := fun V =>
    (integralClosedSubspacePushforward D sX hX W k c).1 V * G V with hF
  have hsupp : Function.support F ⊆ Set.range push := by
    intro V hV
    by_contra hVr
    apply hV
    have h0 : (integralClosedSubspacePushforward D sX hX W k c).1 V = 0 :=
      cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1 hdecX
        W.isClosedSubspace.2 c.1 V fun V' hV' => hVr ⟨V', hV'⟩
    simp only [hF, h0, zero_mul]
  show ∑ᶠ V, F V = _
  rw [show F = (Set.range push).indicator F from (Set.indicator_eq_self.2 hsupp).symm,
    ← finsum_mem_def, finsum_mem_range hinj]
  refine finsum_congr fun V => ?_
  simp only [hF]
  rw [show (integralClosedSubspacePushforward D sX hX W k c).1 (push V) = c.1 V from
      cycleClosedPushforward_apply_pushforward D hX.1 W.isClosedSubspace.1 hdecX
        W.isClosedSubspace.2 c.1 V]

end Decomposition

section Field

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)

/-- The degree `deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_e) ∩ α)` of the iterated cap product of an `e`-cycle, as an
additive map: the degree of Stacks 0ESG on the class of the iterated cap product. -/
def iteratedFirstChernCapDegree (e : ℕ) (L : Fin e → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hL : ∀ j, IsInvertibleModule (⟨X.1, X.2⟩ : AlgebraicSpaces B (Spec (.of k)) hk) (L j)) :
    CycleGroup (fieldSpaceSituation k B hk) f ((0 : ℤ) + (e : ℕ)) →+ ℤ :=
  (chowGroupZeroDegree.{u} (fieldSpaceSituation k B hk) f
    (isGood_fieldSpaceSituation_of_isProper k B hk X hf) (𝟙 _)
    (isGood_fieldSpaceSituation_id k B hk) (Category.comp_id f) hf inferInstance
    (fieldSpaceSituation_deltaValue_id k B hk) (fieldSpacePoint k B hk)).comp
    ((chowClass.{u} (fieldSpaceSituation k B hk) f
      (isGood_fieldSpaceSituation_of_isProper k B hk X hf) 0).comp
      (iteratedFirstChernCapCycle (fieldSpaceSituation k B hk) f
        (isGood_fieldSpaceSituation_of_isProper k B hk X hf) e L hL 0))

/-- The degree of the iterated cap product of a cycle is the cycle-level degree of the iterated
cap product. -/
theorem iteratedFirstChernCapDegree_apply (e : ℕ)
    (L : Fin e → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hL : ∀ j, IsInvertibleModule (⟨X.1, X.2⟩ : AlgebraicSpaces B (Spec (.of k)) hk) (L j))
    (α : CycleGroup (fieldSpaceSituation k B hk) f ((0 : ℤ) + (e : ℕ))) :
    iteratedFirstChernCapDegree k B hk X f hf e L hL α =
      cycleDegree (fieldSpaceSituation k B hk) f
        (isGood_fieldSpaceSituation_of_isProper k B hk X hf) (𝟙 _)
        (isGood_fieldSpaceSituation_id k B hk) (Category.comp_id f) hf (fieldSpacePoint k B hk)
        (iteratedFirstChernCapCycle (fieldSpaceSituation k B hk) f
          (isGood_fieldSpaceSituation_of_isProper k B hk X hf) e L hL 0 α) :=
  chowGroupZeroDegree_chowClass.{u} _ _ _ _ _ _ _ inferInstance
    (fieldSpaceSituation_deltaValue_id k B hk) _ _

/-- **The intersection number of the point of `Spec k` is one**: `χ(Spec k, i_*𝒪_W) = 1` for the
integral closed subspace `W` of `Spec k`. By Stacks 0EDE it is `χ(Spec k, 𝒪) = 1`, both modules
having length one at the point. -/
theorem intersectionNumber_baseObject_eq_one
    (W : IntegralClosedSubspace B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk)))
    (hW : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 = (0 : ℕ))
    (L : Fin 0 → Modules.{u, u} B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)))
    [∀ j, Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk)))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk
        (yoneda.obj (baseObject k B hk))
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk))).O).property (L j)] :
    intersectionNumber.{u, w} k B hk
      ⟨yoneda.obj (baseObject k B hk),
        isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
      (closedSubspaceToSpace B (Spec (.of k)) hk
        ⟨yoneda.obj (baseObject k B hk),
          isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
        ⟨W.subspace, W.isClosedSubspace⟩) 0 (𝟙 _) (isProper_id_baseObject k B hk)
      (closedSubspaceInclusion B (Spec (.of k)) hk
        ⟨yoneda.obj (baseObject k B hk),
          isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
        ⟨W.subspace, W.isClosedSubspace⟩) W.isClosedSubspace.2 hW L = 1 := by
  set P : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj (baseObject k B hk),
      isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
  have hLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk P.1 P.2 (𝟙 _)
    (isProper_id_baseObject k B hk)
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk P.1
      (fun T : Scheme.{u} => IsLocallyNoetherian T)) := ⟨hLN⟩
  have hO : IsCoherent B (Spec (.of k)) hk P.1 P.2 (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O)) :=
    inferInstance
  rw [intersectionNumber_eq_twistedEulerMixedDifference,
    ← twistedEulerMixedDifference_unit_baseObject.{u, w} k B hk L hO]
  have hall : ∀ S : Set (points B (Spec (.of k)) hk P.1), S.Nonempty → S = Set.univ :=
    fun S ⟨p, hp⟩ => Set.eq_univ_of_forall fun q => Subsingleton.elim p q ▸ hp
  have hTcl : IsClosed (Set.univ : Set (points B (Spec (.of k)) hk P.1)) := isClosed_univ
  have : DiscreteTopology (points B (Spec (.of k)) hk P.1) := ⟨Subsingleton.elim _ _⟩
  have hTd : topologicalKrullDim (Set.univ : Set (points B (Spec (.of k)) hk P.1)) ≤ (0 : ℕ) :=
    (topologicalKrullDim_subspace_le _ _).trans
      (topologicalKrullDim_zero_of_discreteTopology _)
  let x : irreducibleComponents (Set.univ : Set (points B (Spec (.of k)) hk P.1)) →
      GeometricPoint B (Spec (.of k)) hk P.1 := fun _ =>
    canonicalGeometricPoint B (Spec (.of k)) hk P.1 (W.ambientGenericPoint B (Spec (.of k)) hk)
  have hx : ∀ C : irreducibleComponents (Set.univ : Set (points B (Spec (.of k)) hk P.1)),
      IsGenericPoint (x C).image (Subtype.val '' (C : Set (Set.univ : Set _))) := by
    intro C
    have hne : (Subtype.val '' C.1).Nonempty := C.2.1.nonempty.image _
    rw [hall _ hne, isGenericPoint_def, hall _ (Set.singleton_nonempty _),
      closure_univ]
  rw [twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk P (𝟙 _)
      (isProper_id_baseObject k B hk) L _ _ hTcl hTd x hx (Set.subset_univ _),
    twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk P (𝟙 _)
      (isProper_id_baseObject k B hk) L _ hO hTcl hTd x hx (Set.subset_univ _)]
  refine finsum_congr fun C => ?_
  congr 2
  refine congrArg ENat.toNat ((geometricLength_modulePushforward_unit_eq_one B (Spec (.of k)) hk P
    W (x C.1) (canonicalGeometricPoint_image _ _ _ _ _)).trans
    (geometricLength_structureSheafModule_eq_one_of_isIntegralSpace B (Spec (.of k)) hk P
      (isIntegralSpace_yoneda_baseObject k B hk) (x C.1) ?_).symm)
  show closure {(x C.1).image} ∈ irreducibleComponents (points B (Spec (.of k)) hk P.1)
  have : IrreducibleSpace (points B (Spec (.of k)) hk P.1) :=
    (isIntegralSpace_yoneda_baseObject k B hk).2.2
  rw [irreducibleComponents_eq_singleton,
    hall _ (closure_nonempty_iff.2 (Set.singleton_nonempty _))]
  rfl

/-- An integral closed subspace of `X` has dimension `n` iff its `δ`-dimension is `n`. -/
private theorem dimension_integralClosedSubspace_eq_natCast_iff
    (hf : IsProper B (Spec (.of k)) hk f) (V : IntegralClosedSubspace B (Spec (.of k)) hk X.1)
    (n : ℕ) :
    dimension B (Spec (.of k)) hk V.subspace.toFunctor V.isClosedSubspace.1 = n ↔
      deltaDimension (fieldSpaceSituation k B hk) f V = n := by
  obtain ⟨h0, hdimV⟩ := dimension_integralClosedSubspace_eq_deltaDimension k B hk X hf V
  rw [hdimV]
  constructor
  · intro h
    have h' : (deltaDimension (fieldSpaceSituation k B hk) f V).toNat = n := by exact_mod_cast h
    omega
  · intro h
    rw [h]
    simp

/-- **The base case: a point.** For an integral closed subspace `W ⊆ X` of dimension zero,
`χ(W, 𝒪_W) = deg [W]`. -/
theorem integralClosedSubspaceIntersectionNumber_eq_iteratedFirstChernCapDegree_zero
    (W : IntegralClosedSubspace B (Spec (.of k)) hk X.1)
    (hW : deltaDimension (fieldSpaceSituation k B hk) f W = (0 : ℤ) + ((0 : ℕ) : ℤ))
    (L : Fin 0 → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    integralClosedSubspaceIntersectionNumber.{u, w} k B hk X f hf L W =
      iteratedFirstChernCapDegree k B hk X f hf 0 L hL
        (integralCycle (fieldSpaceSituation k B hk) f _ W hW) := by
  have hX := isGood_fieldSpaceSituation_of_isProper k B hk X hf
  have hXdec := (fieldSpaceSituation k B hk).isDecentSpace_of_isGood f hX
  set P : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj (baseObject k B hk),
      isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)⟩
  have hPdec := (fieldSpaceSituation k B hk).isDecentSpace_of_isGood (𝟙 _)
    (isGood_fieldSpaceSituation_id k B hk)
  have hdimW : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 =
      ((0 : ℕ) : WithBot ℕ∞) :=
    (dimension_integralClosedSubspace_eq_natCast_iff k B hk X f hf W 0).2 (by rw [hW]; simp)
  rw [integralClosedSubspaceIntersectionNumber_of_dimension_eq.{u, w} k B hk X f hf L W hdimW]
  refine Eq.trans ?_ (iteratedFirstChernCapDegree_apply k B hk X f hf 0 L hL _).symm
  -- the right hand side is the residue degree of `W`
  rw [cycleDegree_eq_finsum (fieldSpaceSituation k B hk) f hX (𝟙 _)
    (isGood_fieldSpaceSituation_id k B hk) (Category.comp_id f) hf inferInstance
    (fieldSpaceSituation_deltaValue_id k B hk) (fieldSpacePoint k B hk) _]
  have hcoe : ∀ Z, ((iteratedFirstChernCapCycle (fieldSpaceSituation k B hk) f hX 0 L hL 0)
      (integralCycle (fieldSpaceSituation k B hk) f _ W hW)).1 Z =
      integralCycleCoeff (fieldSpaceSituation k B hk) W Z := fun Z =>
    congrFun (iteratedFirstChernCapCycle_zero (fieldSpaceSituation k B hk) f hX L hL 0 _) Z
  rw [finsum_eq_single _ W (fun Z hZ => by
    rw [hcoe, show integralCycleCoeff (fieldSpaceSituation k B hk) W Z = 0 from if_neg hZ,
      zero_mul])]
  rw [hcoe, show integralCycleCoeff (fieldSpaceSituation k B hk) W W = 1 from if_pos rfl, one_mul]
  -- the left hand side through Stacks 0EDJ along `X ⟶ Spec k`
  let fm : X ⟶ P := ObjectProperty.homMk f
  let L₀ : Fin 0 → Modules.{u, u} B (Spec (.of k)) hk P.1 P.2 := fun j => j.elim0
  have hL₀ : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk P.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk P.1 P.2).O).property (L₀ j) := fun j => j.elim0
  set W'' := IntegralClosedSubspace.closureImage B (Spec (.of k)) hk P.2 hPdec fm.hom W
    with hW''def
  have hdimW'' : dimension B (Spec (.of k)) hk W''.subspace.toFunctor W''.isClosedSubspace.1 =
      (0 : ℕ) := by
    refine (dimension_integralClosedSubspace_eq_natCast_iff k B hk P (𝟙 _)
      (isProper_id_baseObject k B hk) W'' 0).2 ?_
    exact fieldSpaceSituation_deltaValue_id k B hk _
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk fm (L₀ j)
  have hfam : intersectionNumber.{u, w} k B hk X
      (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩) 0 f hf
      (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩)
      W.isClosedSubspace.2 hdimW L =
      intersectionNumber.{u, w} k B hk X
      (closedSubspaceToSpace B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩) 0 f hf
      (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩)
      W.isClosedSubspace.2 hdimW (fun j => (modulePullback B (Spec (.of k)) hk fm).obj (L₀ j)) :=
    twistedEulerMixedDifference_congr_family.{u, w} k B hk X f hf L _
      (isCoherent_structureSheafPushforward B (Spec (.of k)) hk
        (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) _
        W.isClosedSubspace.2) (fun j => j.elim0)
  rw [hfam]
  refine (intersectionNumber_modulePullback_eq_degree_mul.{u, w} k B hk (𝟙 _)
    (isProper_id_baseObject k B hk) f hf fm W hdimW L₀ hdimW'').trans ?_
  rw [intersectionNumber_baseObject_eq_one.{u, w} k B hk W'' hdimW'' L₀, mul_one]
  -- the degree of `W` over its image is the residue degree at its generic point
  have hc := residueFieldDegreeAt_comp B (Spec (.of k)) hk W''.isClosedSubspace.1 P.2
    W.isIntegralSpace.isDecentSpace W''.isIntegralSpace.isDecentSpace hPdec
    (IntegralClosedSubspace.toClosureImage B (Spec (.of k)) hk P.2 hPdec fm.hom W)
    W''.subspace.ι (W.genericPoint B (Spec (.of k)) hk)
  rw [residueFieldDegreeAt_eq_one_of_mono B (Spec (.of k)) hk P.2 _ hPdec W''.subspace.ι, mul_one,
    IntegralClosedSubspace.toClosureImage_ι] at hc
  have h3 : degree B (Spec (.of k)) hk W.isClosedSubspace.1 W''.isClosedSubspace.1
      W.isIntegralSpace W''.isIntegralSpace
      (IntegralClosedSubspace.toClosureImage B (Spec (.of k)) hk P.2 hPdec fm.hom W) =
      cycleResidueDegree (fieldSpaceSituation k B hk) f hX (𝟙 _)
        (isGood_fieldSpaceSituation_id k B hk) f
        (W.ambientGenericPoint B (Spec (.of k)) hk) :=
    hc.symm.trans (cycleResidueDegree_ι_comp (fieldSpaceSituation k B hk) f hX (𝟙 _)
      (isGood_fieldSpaceSituation_id k B hk) f W (W.genericPoint B (Spec (.of k)) hk))
  exact_mod_cast h3

/-- **Intersection numbers of integral closed subspaces as degrees of iterated cap products.** For
an integral closed subspace `W ⊆ X` of dimension `e` and invertible `ℒ₁, …, ℒ_e`,
`(ℒ₁ ⋯ ℒ_e · W) = deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_e) ∩ [W])`. -/
theorem integralClosedSubspaceIntersectionNumber_eq_iteratedFirstChernCapDegree (e : ℕ) :
    ∀ (W : IntegralClosedSubspace B (Spec (.of k)) hk X.1)
      (hW : deltaDimension (fieldSpaceSituation k B hk) f W = (0 : ℤ) + (e : ℕ))
      (L : Fin e → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
      [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)],
      integralClosedSubspaceIntersectionNumber.{u, w} k B hk X f hf L W =
        iteratedFirstChernCapDegree k B hk X f hf e L hL
          (integralCycle (fieldSpaceSituation k B hk) f _ W hW) := by
  induction e with
  | zero =>
    exact integralClosedSubspaceIntersectionNumber_eq_iteratedFirstChernCapDegree_zero k B hk X f hf
  | succ e ih =>
    intro W hW L hL
    have hX := isGood_fieldSpaceSituation_of_isProper k B hk X hf
    have hXdec := (fieldSpaceSituation k B hk).isDecentSpace_of_isGood f hX
    -- the integral closed subspace `W` as an algebraic space proper over `k`
    set Y := closedSubspaceToSpace B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩ with hYdef
    set i := closedSubspaceInclusion B (Spec (.of k)) hk X ⟨W.subspace, W.isClosedSubspace⟩
      with hidef
    have hi : IsClosedImmersion B (Spec (.of k)) hk i.hom := W.isClosedSubspace.2
    have hfY : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
      isProper_comp B (Spec (.of k)) hk Y.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk Y.2 X.2 i.hom hi) hf
    have hLY := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
    -- dimensions
    have hdimW : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 =
        (e + 1 : ℕ) :=
      (dimension_integralClosedSubspace_eq_natCast_iff k B hk X f hf W (e + 1)).2
        (by rw [hW]; simp)
    obtain ⟨-, htop⟩ := topologicalKrullDim_points_eq_deltaDimension (fieldSpaceSituation k B hk) f
      hX (fieldSpaceSituation_hasJacobson k B hk) (fun _ _ => rfl) W
    have hdimY : topologicalKrullDim (points B (Spec (.of k)) hk Y.1) = (e : WithBot ℕ∞) + 1 := by
      rw [htop, hW]
      simp
    have hn : deltaDimensionClosed (fieldSpaceSituation k B hk) (i.hom ≫ f)
        (isGood_fieldSpaceSituation_of_isProper k B hk Y hfY) Set.univ isClosed_univ =
          (((e : ℤ) + 1 : ℤ) : EInt) := by
      refine (deltaDimensionClosed_univ_integralClosedSubspace (fieldSpaceSituation k B hk) f hX
        W).trans ?_
      rw [hW]
      push_cast
      ring_nf
    -- the left hand side
    rw [integralClosedSubspaceIntersectionNumber_of_dimension_eq.{u, w} k B hk X f hf L W hdimW]
    refine (intersectionNumber_eq_twistedEulerMixedDifference_closedSubspace.{u, w} k B hk X f hf
      L Y i hi hdimW).trans ?_
    -- move `ℒ_{e+1}|_W` to the front and expand along the divisor of `t_W`
    set N := (modulePullback B (Spec (.of k)) hk i).obj (L (Fin.last e)) with hNdef
    set Mf : Fin e → Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2 :=
      fun j => (modulePullback B (Spec (.of k)) hk i).obj (L j.castSucc) with hMfdef
    have hNinst : Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk Y.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O).property N := hLY (Fin.last e)
    have hMinst : ∀ j, Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B (Spec (.of k)) hk Y.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O).property (Mf j) :=
      fun j => hLY j.castSucc
    have hfam : ∀ j, (modulePullback B (Spec (.of k)) hk i).obj (L j) ≅
        (Fin.snoc (α := fun _ => Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2) Mf N j) := by
      intro j
      refine eqToIso ?_
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]
      | cast j => rw [Fin.snoc_castSucc]
    have := isInvertible_snoc k B hk Y N Mf
    rw [twistedEulerMixedDifference_congr_family.{u, w} k B hk Y (i.hom ≫ f) hfY _ _ _ hfam,
      twistedEulerMixedDifference_snoc_eq_cons.{u, w} k B hk Y (i.hom ≫ f) hfY _ _ N Mf]
    have hsetup := subspaceDivisorSetupOfIsGood (fieldSpaceSituation k B hk) f hX
    refine (twistedEulerMixedDifference_cons_eq_finsum_divisorCycleCoefficients.{u, w} k B hk Y
      (i.hom ≫ f) hfY W.isIntegralSpace hdimY hn N
      (componentMeromorphicSection f hX hsetup (L (Fin.last e)) (hL _) W)
      (isRegularMeromorphicSection_componentMeromorphicSection f hX hsetup (L (Fin.last e))
        (hL _) W) Mf).trans ?_
    -- the right hand side: the cap with `c₁(ℒ_{e+1})` sends `[W]` to the pushforward of `div(t_W)`
    have hW' : deltaDimension (fieldSpaceSituation k B hk) f W = ((0 : ℤ) + (e : ℕ)) + 1 := by
      rw [hW]
      push_cast
      ring
    have hLinit : ∀ j, Stacks.SheafOfModules.IsInvertible
        (structurePresheaf B (Spec (.of k)) hk X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (Fin.init L j) :=
      fun j => hL _
    have hRHS : iteratedFirstChernCapDegree k B hk X f hf (e + 1) L hL
        (integralCycle (fieldSpaceSituation k B hk) f _ W hW) =
        iteratedFirstChernCapDegree k B hk X f hf e (Fin.init L) hLinit
          (integralClosedSubspacePushforward (fieldSpaceSituation k B hk) f hX W ((0 : ℤ) + (e : ℕ))
            (canonicalFirstChernRule (fieldSpaceSituation k B hk) f hX (L (Fin.last e)) (hL _)
              ((0 : ℤ) + (e : ℕ)) W hW')) := by
      have hcast : cycleGroupCast (fieldSpaceSituation k B hk) f (by push_cast; ring)
          (integralCycle (fieldSpaceSituation k B hk) f _ W hW) =
          integralCycle (fieldSpaceSituation k B hk) f (((0 : ℤ) + (e : ℕ)) + 1) W hW' :=
        Subtype.ext rfl
      unfold iteratedFirstChernCapDegree
      simp only [AddMonoidHom.comp_apply]
      congr 2
      show iteratedFirstChernCapCycle (fieldSpaceSituation k B hk) f hX e (Fin.init L) hLinit 0
        (firstChernCapCycleMap (fieldSpaceSituation k B hk) f hX ((0 : ℤ) + (e : ℕ))
          (canonicalFirstChernRule (fieldSpaceSituation k B hk) f hX (L (Fin.last e)) (hL _)
            ((0 : ℤ) + (e : ℕ)))
          (cycleGroupCast (fieldSpaceSituation k B hk) f (by push_cast; ring)
            (integralCycle (fieldSpaceSituation k B hk) f _ W hW))) = _
      rw [hcast, firstChernCapCycleMap_integralCycle]
    have := noetherianSpace_points_of_isProper_baseObject k B hk X.1 X.2 f hf
    rw [hRHS, map_cycle_eq_finsum_of_compactSpace (fieldSpaceSituation k B hk) f _
      (integralClosedSubspaceIntersectionNumber.{u, w} k B hk X f hf (Fin.init L))
      (fun Z hZ => (ih Z hZ (Fin.init L)).symm),
      finsum_integralClosedSubspacePushforward_mul]
    refine finsum_congr fun V => ?_
    set c := canonicalFirstChernRule (fieldSpaceSituation k B hk) f hX (L (Fin.last e)) (hL _)
      ((0 : ℤ) + (e : ℕ)) W hW' with hcdef
    show c.1 V * _ = c.1 V * _
    by_cases hc : c.1 V = 0
    · rw [hc, zero_mul, zero_mul]
    congr 1
    have hδV : deltaDimension (fieldSpaceSituation k B hk) (i.hom ≫ f) V = (e : ℤ) :=
      (c.2.2 V hc).trans (zero_add _)
    have hδPV : deltaDimension (fieldSpaceSituation k B hk) f
        (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2 hXdec hi V) = (e : ℤ) :=
      (IntegralClosedSubspace.deltaDimension_pushforward (fieldSpaceSituation k B hk) f hX.2.2 X.2
        Y.2 hXdec hi V).trans hδV
    have hdimV : dimension B (Spec (.of k)) hk V.subspace.toFunctor V.isClosedSubspace.1 = e :=
      (dimension_integralClosedSubspace_eq_natCast_iff k B hk Y (i.hom ≫ f) hfY V e).2 hδV
    have hdimPV : dimension B (Spec (.of k)) hk
        (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2 hXdec hi
          V).subspace.toFunctor
        (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2 hXdec hi
          V).isClosedSubspace.1
        = e :=
      (dimension_integralClosedSubspace_eq_natCast_iff k B hk X f hf _ e).2 hδPV
    rw [integralClosedSubspaceIntersectionNumber_of_dimension_eq.{u, w} k B hk Y (i.hom ≫ f) hfY Mf
      V hdimV]
    rw [integralClosedSubspaceIntersectionNumber_of_dimension_eq.{u, w} k B hk X f hf (Fin.init L)
      _ hdimPV]
    exact (intersectionNumber_integralClosedSubspacePushforward.{u, w} k B hk X f hf (Fin.init L) i
      hi V hdimV hdimPV).symm

/-- **Intersection numbers of closed subspaces as degrees of iterated cap products.** For a closed
subspace `Z ⊆ X` of dimension `d` and invertible `ℒ₁, …, ℒ_d`,
`(ℒ₁ ⋯ ℒ_d · Z) = deg(c₁(ℒ₁) ∩ ⋯ ∩ c₁(ℒ_d) ∩ [Z]_d)`. By Stacks 0EDE both sides are
`∑_C m_C (ℒ₁ ⋯ ℒ_d · Z_C)` over the irreducible components of `|Z|` of dimension `d`. -/
theorem intersectionNumber_eq_iteratedFirstChernCapDegree_closedSubspaceCycle
    (Z : ClosedSubspaces B (Spec (.of k)) hk X.1) (d : ℕ)
    (hd : dimension B (Spec (.of k)) hk Z.1.toFunctor Z.2.1 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [hL : ∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    intersectionNumber.{u, w} k B hk X (closedSubspaceToSpace B (Spec (.of k)) hk X Z) d f hf
        (closedSubspaceInclusion B (Spec (.of k)) hk X Z) Z.2.2 hd L =
      iteratedFirstChernCapDegree k B hk X f hf d L hL
        (cycleGroupCast (fieldSpaceSituation k B hk) f (zero_add _).symm
          (closedSubspaceCycle (fieldSpaceSituation k B hk) f
            (isGood_fieldSpaceSituation_of_isProper k B hk X hf) Z.1 Z.2 d
            (deltaDimensionSubspace_le_of_dimension_eq k B hk X hf Z hd))) := by
  have hX := isGood_fieldSpaceSituation_of_isProper k B hk X hf
  have hXdec := (fieldSpaceSituation k B hk).isDecentSpace_of_isGood f hX
  have hLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf
  have hdim := deltaDimensionSubspace_le_of_dimension_eq k B hk X hf Z hd
  rw [intersectionNumber_eq_twistedEulerMixedDifference]
  set T := subspacePointSet B (Spec (.of k)) hk X.1 Z.1 with hTdef
  have hTcl : IsClosed T :=
    isClosed_subspacePointSet_of_isClosedSubspace (fieldSpaceSituation k B hk) X.2 Z.1 Z.2
  have hTd : topologicalKrullDim T ≤ d := by
    rw [hTdef, subspacePointSet, ← dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B
      (Spec (.of k)) hk X.2 hXdec Z.2.1 Z.1.ι Z.2.2, hd]
  let x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk X.1 := fun C =>
    canonicalGeometricPoint B (Spec (.of k)) hk X.1
      ((closedSetComponent B (Spec (.of k)) hk X.2 hXdec T hTcl C).ambientGenericPoint
        B (Spec (.of k)) hk)
  have hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)) := by
    intro C
    rw [canonicalGeometricPoint_image]
    have h := (closedSetComponent B (Spec (.of k)) hk X.2 hXdec T hTcl
      C).isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk X.2
    rwa [subspacePointSet_closedSetComponent] at h
  have hFT : moduleSupportSet B (Spec (.of k)) hk X (structureSheafPushforward B (Spec (.of k)) hk
      (closedSubspaceInclusion B (Spec (.of k)) hk X Z)) ⊆ T :=
    (moduleSupportSet_structureSheafPushforward_of_isClosedImmersion B (Spec (.of k)) hk _
      Z.2.2).le
  rw [twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk X f hf L _ _ hTcl hTd x
    hx hFT]
  have := noetherianSpace_points_of_isProper_baseObject k B hk X.1 X.2 f hf
  rw [map_cycle_eq_finsum_of_compactSpace (fieldSpaceSituation k B hk) f _
    (integralClosedSubspaceIntersectionNumber.{u, w} k B hk X f hf L)
    (fun V hV => (integralClosedSubspaceIntersectionNumber_eq_iteratedFirstChernCapDegree.{u, w}
      k B hk X f hf d V hV L).symm)]
  let φ : {C : irreducibleComponents T //
      topologicalKrullDim (Subtype.val '' (C : Set T)) = d} →
      IntegralClosedSubspace B (Spec (.of k)) hk X.1 := fun C =>
    closedSetComponent B (Spec (.of k)) hk X.2 hXdec T hTcl C.1
  have hφ : Function.Injective φ := by
    intro C₁ C₂ h
    have h' := congrArg (fun V : IntegralClosedSubspace B (Spec (.of k)) hk X.1 =>
      subspacePointSet B (Spec (.of k)) hk X.1 V.subspace) h
    simp only [φ, subspacePointSet_closedSetComponent] at h'
    exact Subtype.ext (Subtype.ext (Subtype.val_injective.image_injective h'))
  have hsupp : Function.support (fun V : IntegralClosedSubspace B (Spec (.of k)) hk X.1 =>
      (cycleGroupCast (fieldSpaceSituation k B hk) f (zero_add _).symm
          (closedSubspaceCycle (fieldSpaceSituation k B hk) f hX Z.1 Z.2 d hdim)).1 V *
        integralClosedSubspaceIntersectionNumber.{u, w} k B hk X f hf L V) ⊆ Set.range φ := by
    intro V hV
    have hc : (closedSubspaceCycle (fieldSpaceSituation k B hk) f hX Z.1 Z.2 d hdim).1 V ≠ 0 :=
      left_ne_zero_of_mul hV
    obtain ⟨W', hW'⟩ : ∃ W' : IntegralClosedSubspace B (Spec (.of k)) hk Z.1.toFunctor,
        closedSubspaceComponentImage (fieldSpaceSituation k B hk) f hX Z.1 Z.2 W' = V := by
      by_contra h
      have h0 := closedSubspaceCycle_apply_eq_zero_of_forall_ne (fieldSpaceSituation k B hk) f hX
        Z.1 Z.2 d hdim V (fun W' hW' => h ⟨W', hW'⟩)
      exact hc h0
    have hδ : deltaDimension (fieldSpaceSituation k B hk) f
        (closedSubspaceComponentImage (fieldSpaceSituation k B hk) f hX Z.1 Z.2 W') = d := by
      by_contra h
      rw [← hW', closedSubspaceCycle_apply_closedSubspaceComponentImage, if_neg h] at hc
      exact hc rfl
    obtain ⟨C, hC⟩ := exists_irreducibleComponents_closedSubspaceComponentImage
      (fieldSpaceSituation k B hk) f hX Z.1 Z.2 d hdim W' hδ
    have hVeq := (eq_closedSetComponent B (Spec (.of k)) hk X.2 hXdec T hTcl C _ hC).trans hW'
    have hdimC : topologicalKrullDim (Subtype.val '' (C : Set T)) = d := by
      rw [← hC]
      have h := dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk X.2
        hXdec
        (closedSubspaceComponentImage (fieldSpaceSituation k B hk) f hX Z.1 Z.2
          W').isClosedSubspace.1
        (closedSubspaceComponentImage (fieldSpaceSituation k B hk) f hX Z.1 Z.2 W').subspace.ι
        (closedSubspaceComponentImage (fieldSpaceSituation k B hk) f hX Z.1 Z.2
          W').isClosedSubspace.2
      exact h.symm.trans ((dimension_integralClosedSubspace_eq_natCast_iff k B hk X f hf _ d).2 hδ)
    exact ⟨⟨C, hdimC⟩, hVeq⟩
  conv_rhs => rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range φ)
    (fun V hV => ⟨fun _ => hsupp hV, fun _ => Set.mem_univ _⟩), finsum_mem_range hφ]
  refine finsum_congr fun C => ?_
  have hdimφ :
      dimension B (Spec (.of k)) hk (φ C).subspace.toFunctor (φ C).isClosedSubspace.1 = d := by
    exact (dimension_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 hXdec
      (Subtype.val '' (C.1 : Set T))
      (closedSetComponentPoints B (Spec (.of k)) hk T hTcl C.1).isClosed).trans C.2
  rw [integralClosedSubspaceIntersectionNumber_of_dimension_eq.{u, w} k B hk X f hf L (φ C) hdimφ]
  obtain ⟨W', hW'⟩ := exists_closedSubspaceComponentImage_eq_closedSetComponent
    (fieldSpaceSituation k B hk) f hX Z.1 Z.2 C.1
  have hδ : deltaDimension (fieldSpaceSituation k B hk) f
      (closedSubspaceComponentImage (fieldSpaceSituation k B hk) f hX Z.1 Z.2 W') = d := by
    rw [hW']
    exact (dimension_integralClosedSubspace_eq_natCast_iff k B hk X f hf _ d).1 hdimφ
  have hcoef : (cycleGroupCast (fieldSpaceSituation k B hk) f (zero_add _).symm
      (closedSubspaceCycle (fieldSpaceSituation k B hk) f hX Z.1 Z.2 d hdim)).1 (φ C) =
      ((geometricLength B (Spec (.of k)) hk X (x C.1) (structureSheafPushforward B (Spec (.of k)) hk
        (closedSubspaceInclusion B (Spec (.of k)) hk X Z))).toNat : ℤ) := by
    show (closedSubspaceCycle (fieldSpaceSituation k B hk) f hX Z.1 Z.2 d hdim).1
      (closedSetComponent B (Spec (.of k)) hk X.2 hXdec T hTcl C.1) = _
    rw [← hW', closedSubspaceCycle_apply_closedSubspaceComponentImage, if_pos hδ]
    set x' := canonicalGeometricPoint B (Spec (.of k)) hk Z.1.toFunctor
      (W'.ambientGenericPoint B (Spec (.of k)) hk)
    have himg : (x C.1).image = (geometricPointMap Z.1.ι x').image := by
      rw [geometricPointMap_image, canonicalGeometricPoint_image, canonicalGeometricPoint_image,
        ← hW']
      exact IntegralClosedSubspace.ambientGenericPoint_pushforward B (Spec (.of k)) hk X.2 Z.2.1
        hXdec Z.2.2 W'
    have : (structureSheafPushforward B (Spec (.of k)) hk
        (closedSubspaceInclusion B (Spec (.of k)) hk X Z)).IsQuasicoherentOnSite :=
      (isCoherent_structureSheafPushforward B (Spec (.of k)) hk hLN _ Z.2.2).toIsQuasicoherentOnSite
    rw [geometricLength_eq_of_image_eq B (Spec (.of k)) hk X.2 _ _ himg]
    exact congrArg (fun n : ℕ∞ => ((n.toNat : ℕ) : ℤ))
      (geometricLength_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk
        (closedSubspaceInclusion B (Spec (.of k)) hk X Z) Z.2.2 x' _).symm
  rw [hcoef]
  rfl


end Field

end AlgebraicGeometry.Space

end

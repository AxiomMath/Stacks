module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFormalPullbackCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Algebraizing a map to a completion on an algebraic space: existence

Let `F` be a Noetherian algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a quasi-coherent
sheaf of ideals on its small étale site, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a map whose levelwise kernels and cokernels
are annihilated by a power of `𝓘`.  This file proves the **existence** half of Stacks 08BB: there
are a coherent module `M`, a map `a : M ⟶ G` whose kernel and cokernel are annihilated by a power
of `𝓘`, and an isomorphism `β : E ≅ M^∧` with `α = a^∧ ∘ β`.  Together with the uniqueness half
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian` this is the whole
of Stacks 08BB.

The module `M` is the formal pullback `G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E` of
`AlgebraicGeometry.Space.formalPullback`, a single global object, and `a` is its projection to
`G`.  No étale descent is performed: everything is read off the sections over the affine étale
charts, which are Noetherian because `F` is, and there the formal pullback is the module produced
by the formal-glueing descent of Stacks 0889 (the affine case of the source's proof).

* `M` is coherent: it is cartesian on affine charts,
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_formalPullback`, hence quasi-coherent, and
  its sections over the affine charts are finite modules.
* The kernel and the cokernel of `a` are annihilated by the same power `𝓘 ^ t` as the levelwise
  kernels and cokernels of `α`.
* The projections `M ⟶ lim E ⟶ E_n` kill `𝓘 ⁿ⁺¹ M`, and the induced maps `M / 𝓘 ⁿ⁺¹ M ⟶ E_n`
  are isomorphisms, because on the sections over an affine chart the projection is the reduction
  modulo `𝓘(V) ⁿ⁺¹`.  They assemble into the inverse of `β`.

## Main results

* `AlgebraicGeometry.Space.C1573.isIso_modules_of_bijective_app_affineChart` — a morphism of
  `𝒪_F`-modules bijective on the sections over every affine étale chart is an isomorphism.
* `AlgebraicGeometry.Space.C1573.idealPowerMultiple_eq_bot_of_isAffine` — a module cartesian on
  affine charts whose sections over the affine charts are annihilated by `𝓘 ^ k` is annihilated
  by `𝓘 ^ k`.
* `AlgebraicGeometry.Space.C1573.isCoherent_formalPullback` — the formal pullback is coherent.
* `AlgebraicGeometry.Space.C1573.exists_algebraization` — **Stacks 08BB, existence.**

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/- The site-generic abelian structure on sheaves of modules, which the import of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageChartSections` brings into scope, is
universe polymorphic, as is its Grothendieck abelian structure, and both leave universe
constraints stuck when instance search tries them on
`AlgebraicGeometry.Space.Modules`; the instance of Mathlib is the one used throughout. -/
open _root_.AlgebraicGeometry.Space.C1573
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

set_option synthInstance.maxHeartbeats 400000 in
/-- Kernels of `𝒪_F`-modules, found once (instance search for them times out). -/
noncomputable instance (priority := high) hasKernels_modules_CoherentCompletionExistence :
    HasKernels (Modules.{u, u} B S hS F hF) :=
  inferInstance

/-- Each kernel of `𝒪_F`-modules, from `hasKernels_modules_CoherentCompletionExistence`. -/
noncomputable instance (priority := high) hasKernel_modules_CoherentCompletionExistence
    {M N : Modules.{u, u} B S hS F hF} (f : M ⟶ N) : HasKernel f :=
  HasKernels.has_limit f

/-! ### Detecting isomorphisms and annihilation on the affine charts -/

/-- **A morphism of `𝒪_F`-modules which is bijective on the sections over every affine étale
chart is an isomorphism.**  The affine charts are cover dense in the small étale site,
`AlgebraicGeometry.Space.isCoverDense_affineEtaleInclusion`, so the morphism is locally injective
and locally surjective. -/
theorem C1573.isIso_modules_of_bijective_app_affineChart {M N : Modules.{u, u} B S hS F hF}
    (φ : M ⟶ N)
    (h : ∀ V : SmallEtale B S hS F, IsAffine (chartScheme V) →
      Function.Bijective (φ.val.app (op V)).hom) :
    IsIso φ := by
  have hcov := (SmallEtale.isCoverDense_affineEtaleInclusion B S hS F hF).is_cover
  have hinj : PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS F hF).J
      φ.val := by
    refine ⟨fun {Z} x y hxy => ?_⟩
    refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_ (hcov Z.unop)
    rintro W g ⟨⟨A, lift, map, fac⟩⟩
    rw [← fac]
    refine (Presheaf.equalizerSieve x y).downward_closed ?_ lift
    refine (h A.obj A.property).1 ?_
    have hx := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) map.op x
    have hy := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) map.op y
    exact hx.trans ((congrArg (((PresheafOfModules.toPresheaf _).obj N.val).map map.op) hxy).trans
      hy.symm)
  have hsurj : PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS F hF).J
      φ.val := by
    refine ⟨fun {Z} s => ?_⟩
    refine (smallEtaleRingedSite B S hS F hF).J.superset_covering ?_ (hcov Z)
    rintro W g ⟨⟨A, lift, map, fac⟩⟩
    rw [← fac]
    refine (Presheaf.imageSieve _ s).downward_closed ?_ lift
    exact (h A.obj A.property).2 (((PresheafOfModules.toPresheaf _).obj N.val).map map.op s)
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

/-- **A module cartesian on affine charts whose sections over the affine charts are annihilated
by `𝓘 ^ k` is annihilated by `𝓘 ^ k`.**  The projection `M ⟶ M / 𝓘 ^ k M` is bijective on the
sections over an affine chart, where its kernel is `𝓘(V) ^ k M(V) = 0`, hence an isomorphism; and
every product of a section of `𝓘 ^ k` with a section of `M` dies under it. -/
theorem C1573.idealPowerMultiple_eq_bot_of_isAffine
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M) (k : ℕ)
    (h : ∀ V : SmallEtale B S hS F, IsAffine (chartScheme V) →
      ∀ r ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ k, ∀ x : M.val.obj (op V), r • x = 0) :
    idealPowerMultiple B S hS F hF 𝓘 k M = ⊥ := by
  have hiso : IsIso (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι) := by
    refine isIso_modules_of_bijective_app_affineChart B S hS F hF _ fun V hV => ⟨?_,
      surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k hV⟩
    rw [← LinearMap.ker_eq_bot, ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart k
      hV, eq_bot_iff]
    exact Submodule.smul_le.2 fun r hr x _ => (h V hV r hr x).symm ▸ Submodule.zero_mem _
  refine (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 k M).2 fun U r hr x => ?_
  have hmem := le_idealPowerMultiple_obj B S hS F hF 𝓘 k M U
    (Submodule.smul_mem_smul hr (Submodule.mem_top : x ∈ ⊤))
  have h0 := (cokernel_π_app_eq_zero_iff B S hS F hF _ (op U) (r • x)).2 hmem
  have hbij := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op U)).map
        (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι))
  exact hbij.1 (h0.trans
    ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 k M).ι).val.app (op U)).hom.map_zero.symm)

/-- Equal morphisms of `𝒪_F`-modules agree on every section over every chart. -/
private theorem val_app_apply_congr {M N : Modules.{u, u} B S hS F hF} {f g : M ⟶ N}
    (h : f = g) (V : SmallEtale B S hS F) (p : M.val.obj (op V)) :
    f.val.app (op V) p = g.val.app (op V) p := h ▸ rfl

/-! ### The formal pullback is coherent -/

variable [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (G : Modules.{u, u} B S hS F hF) (hG : IsCoherent B S hS F hF G)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α)

include hIcart hE hG hα in
/-- **The formal pullback is coherent**: it is cartesian on affine charts, hence quasi-coherent,
and its sections over the affine charts, which are Noetherian, are finite. -/
theorem C1573.isCoherent_formalPullback :
    IsCoherent B S hS F hF (formalPullback B S hS F hF 𝓘 G α) :=
  isCoherent_of_isQuasicoherentOnSite_of_forall_affine_moduleFinite B S hS F hF Fact.out _
    (isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
      (isCartesianOnAffineCharts_formalPullback B S hS F hF 𝓘 hIcart hE G hG α hα))
    fun _A hA => moduleFinite_formalPullback_sections B S hS F hF 𝓘 hIcart hE G hG α
      (isNoetherianAffineChart_of_isAffine B S hS F hF hA) hα

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hE in
/-- **`𝓘 ^ t` annihilates the kernel of the projection of the formal pullback to `G`.** -/
theorem C1573.idealPowerMultiple_kernel_formalPullbackMap_eq_bot {t : ℕ}
    (ht : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.app (op k))) = ⊥) :
    idealPowerMultiple B S hS F hF 𝓘 t (kernel (formalPullbackMap B S hS F hF 𝓘 G α)) = ⊥ := by
  refine (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 t _).2 fun U r hr x => ?_
  refine SheafOfModules.kernel_ι_val_app_injective (formalPullbackMap B S hS F hF 𝓘 G α) (op U) ?_
  have hx : (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op U)
      ((kernel.ι (formalPullbackMap B S hS F hF 𝓘 G α)).val.app (op U) x) = 0 :=
    (SheafOfModules.exact_kernel_ι_val_app (formalPullbackMap B S hS F hF 𝓘 G α) (op U)
      _).2 ⟨x, rfl⟩
  rw [((kernel.ι (formalPullbackMap B S hS F hF 𝓘 G α)).val.app (op U)).hom.map_smul,
    smul_eq_zero_of_formalPullbackMap_eq_zero B S hS F hF 𝓘 G α ht U r hr _ hx,
    ((kernel.ι (formalPullbackMap B S hS F hF 𝓘 G α)).val.app (op U)).hom.map_zero]

include hIcart hE hG hα in
/-- **`𝓘 ^ t` annihilates the cokernel of the projection of the formal pullback to `G`**, for the
exponent `t` annihilating the levelwise cokernels of `α`.  Over an affine chart a section of the
cokernel is the class of a section `g` of `G`, and `𝓘(V) ^ t g` lifts to the formal pullback by
`AlgebraicGeometry.Space.exists_formalPullbackMap_eq_smul`. -/
theorem C1573.idealPowerMultiple_cokernel_formalPullbackMap_eq_bot {t : ℕ}
    (ht : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥) :
    idealPowerMultiple B S hS F hF 𝓘 t (cokernel (formalPullbackMap B S hS F hF 𝓘 G α)) = ⊥ := by
  have hPcart := isCartesianOnAffineCharts_formalPullback B S hS F hF 𝓘 hIcart hE G hG α hα
  have hGcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
    hG.toIsQuasicoherentOnSite
  refine idealPowerMultiple_eq_bot_of_isAffine B S hS F hF 𝓘 hIcart _
    (isCartesianOnAffineCharts_cokernel_of_cartesian _ hPcart hGcart) t fun V hV r hr x => ?_
  obtain ⟨g, rfl⟩ := surjective_val_app_cokernel_π_of_cartesian
    (formalPullbackMap B S hS F hF 𝓘 G α) hPcart hGcart V hV x
  obtain ⟨p, hp⟩ := exists_formalPullbackMap_eq_smul B S hS F hF 𝓘 hIcart hE G hG α
    (isNoetherianAffineChart_of_isAffine B S hS F hF hV) ht r hr g
  rw [← ((cokernel.π (formalPullbackMap B S hS F hF 𝓘 G α)).val.app (op V)).hom.map_smul, ← hp]
  exact val_app_apply_congr B S hS F hF (cokernel.condition (formalPullbackMap B S hS F hF 𝓘 G α))
    V p

/-! ### The comparison of the completion of the formal pullback with `E` -/

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
/-- The map `P / 𝓘 ⁿ⁺¹ P ⟶ E_n` induced by the projection of the formal pullback onto level
`n`, which kills `𝓘 ⁿ⁺¹ P` because `E_n` is annihilated by `𝓘 ⁿ⁺¹`. -/
def C1573.formalPullbackCompletionLevel (n : ℕ) :
    idealPowerQuotient B S hS F hF 𝓘 (n + 1) (formalPullback B S hS F hF 𝓘 G α) ⟶ E.obj (op n) :=
  cokernel.desc _ (formalPullbackLevel B S hS F hF 𝓘 G α n)
    (idealPowerMultiple_ι_comp_eq_zero_of_eq_bot B S hS F hF 𝓘 (n + 1) _ (hE.2.1 n))

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
/-- The composite of the projection `P ⟶ P / 𝓘 ⁿ⁺¹ P` with the map `P / 𝓘 ⁿ⁺¹ P ⟶ E_n` is the
projection of the formal pullback onto level `n`. -/
theorem C1573.π_formalPullbackCompletionLevel (n : ℕ) :
    cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) (formalPullback B S hS F hF 𝓘 G α)).ι ≫
        formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α n =
      formalPullbackLevel B S hS F hF 𝓘 G α n :=
  cokernel.π_desc _ _ _

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
/-- The maps `P / 𝓘 ⁿ⁺¹ P ⟶ E_n` are compatible with the transition maps. -/
theorem C1573.idealPowerQuotientMapOfLE_formalPullbackCompletionLevel {j k : ℕ} (h : j ≤ k) :
    idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1)
        (formalPullback B S hS F hF 𝓘 G α) ≫
      formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α j =
    formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α k ≫ E.map (homOfLE h).op := by
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (k + 1)
    (formalPullback B S hS F hF 𝓘 G α)).ι)).1 ?_
  rw [← Category.assoc, π_comp_idealPowerQuotientMapOfLE, π_formalPullbackCompletionLevel,
    ← Category.assoc, π_formalPullbackCompletionLevel, Category.assoc]
  exact congrArg (formalPullbackProj B S hS F hF 𝓘 G α ≫ ·) (limit.w E (homOfLE h).op).symm

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hG in
/-- The maps `P / 𝓘 ⁿ⁺¹ P ⟶ E_n` form a morphism of inverse systems. -/
def C1573.formalPullbackCompletionMap :
    adicQuotientSystem B S hS F hF 𝓘 (formalPullback B S hS F hF 𝓘 G α) ⟶ E where
  app n := formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α n.unop
  naturality _ _ g :=
    idealPowerQuotientMapOfLE_formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α (leOfHom g.unop)

include hIcart hG hα in
/-- **The maps `P / 𝓘 ⁿ⁺¹ P ⟶ E_n` are isomorphisms.**  On the sections over an affine chart the
projection of `P` onto `E_n` is the reduction modulo `𝓘(V) ⁿ⁺¹`,
`AlgebraicGeometry.Space.formalPullbackLevel_app_surjective_ker`, and so is the projection onto
`P / 𝓘 ⁿ⁺¹ P`. -/
theorem C1573.isIso_formalPullbackCompletionLevel (n : ℕ) :
    IsIso (formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α n) := by
  have hPcart := isCartesianOnAffineCharts_formalPullback B S hS F hF 𝓘 hIcart hE G hG α hα
  refine isIso_modules_of_bijective_app_affineChart B S hS F hF _ fun V hV => ?_
  obtain ⟨hsurj, hker⟩ := formalPullbackLevel_app_surjective_ker B S hS F hF 𝓘 hIcart hE G hG α
    (isNoetherianAffineChart_of_isAffine B S hS F hF hV) hα n
  have hcomp : ∀ p, (formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α n).val.app (op V)
      ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
        (formalPullback B S hS F hF 𝓘 G α)).ι).val.app (op V) p) =
      (formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op V) p := fun p =>
    val_app_apply_congr B S hS F hF (π_formalPullbackCompletionLevel B S hS F hF 𝓘 hE G α n) V p
  have hπ := surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ hPcart (n + 1) hV
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨p, rfl⟩ := hπ x
    obtain ⟨q, rfl⟩ := hπ y
    rw [hcomp, hcomp] at hxy
    rw [← sub_eq_zero, ← map_sub]
    have hmem : p - q ∈ LinearMap.ker
        ((cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1)
          (formalPullback B S hS F hF 𝓘 G α)).ι).val.app (op V)).hom := by
      rwa [ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart _ hPcart (n + 1) hV, ← hker,
        LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hmem
  · obtain ⟨p, rfl⟩ := hsurj y
    exact ⟨_, hcomp p⟩

/-! ### Stacks 08BB, existence -/

omit [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
  hIcart hE hG hα in
/-- The defining square of the formal pullback, read at level `n`: the projection to `E_n`
followed by `α_n` is the projection to `G` followed by the reduction modulo `𝓘 ⁿ⁺¹`. -/
theorem C1573.formalPullbackLevel_comp_app (n : ℕ) :
    formalPullbackLevel B S hS F hF 𝓘 G α n ≫ α.app (op n) =
      formalPullbackMap B S hS F hF 𝓘 G α ≫
        cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) G).ι := by
  rw [Category.assoc, ← limMap_π α (op n), ← Category.assoc,
    ← formalPullback_comm B S hS F hF 𝓘 G α, Category.assoc, completionToLimit_π]
  rfl

omit hIcart hE hG hα in
/-- **Stacks 08BB, existence.**  Let `F` be an algebraic space whose étale charts are locally
Noetherian — for instance a Noetherian algebraic space — and `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of
ideals.  A map `α : E ⟶ G^∧` from a coherent `𝓘`-adic system to the completion of a coherent
module, whose levelwise kernels and cokernels are annihilated by a power of `𝓘`, is the
completion of a map `a : M ⟶ G` of coherent modules whose kernel and cokernel are annihilated by
a power of `𝓘`: there is an isomorphism `β : E ≅ M^∧` with `α = a^∧ ∘ β`.

`M` is the formal pullback `G ×_{lim G / 𝓘 ⁿ⁺¹ G} lim E`, coherent by
`AlgebraicGeometry.Space.C1573.isCoherent_formalPullback`, and `a` its projection to `G`; the
inverse of `β` is `AlgebraicGeometry.Space.C1573.formalPullbackCompletionMap`, invertible by
`AlgebraicGeometry.Space.C1573.isIso_formalPullbackCompletionLevel`. The kernel and the cokernel
of `a` are annihilated by the exponent annihilating the levelwise kernels and cokernels of `α`.

The source assumes `F` Noetherian; only the local Noetherianity of its étale charts, which the
completion functor of Stacks 08B4 is stated with, is used.  The uniqueness half of Stacks 08BB is
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian`. -/
theorem C1573.exists_algebraization (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    {G : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α.hom) :
    ∃ (M : CoherentModules.{u, u} B S hS F hF) (a : M ⟶ G)
      (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M),
      IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a ∧
        α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a := by
  have hIcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF
    𝓘.toSheafOfModules hI
  let α' : E.obj ⟶ adicQuotientSystem B S hS F hF 𝓘 G.obj := α.hom
  obtain ⟨t, ht0, htk⟩ := id hα
  let M : CoherentModules.{u, u} B S hS F hF :=
    ⟨formalPullback B S hS F hF 𝓘 G.obj α',
      isCoherent_formalPullback B S hS F hF 𝓘 hIcart E.property G.obj G.property α' hα⟩
  let a : M ⟶ G := ObjectProperty.homMk (formalPullbackMap B S hS F hF 𝓘 G.obj α')
  let β' : (completionFunctor B S hS F hF 𝓘 hI).obj M ⟶ E :=
    ObjectProperty.homMk (formalPullbackCompletionMap B S hS F hF 𝓘 E.property G.obj α')
  have hβiso : IsIso β'.hom := by
    have : ∀ n : ℕᵒᵖ, IsIso (β'.hom.app n) := fun n =>
      isIso_formalPullbackCompletionLevel B S hS F hF 𝓘 hIcart E.property G.obj G.property α'
        hα n.unop
    exact NatIso.isIso_of_isIso_app _
  have : IsIso ((ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)).map β') := hβiso
  have : IsIso β' :=
    isIso_of_fully_faithful (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) β'
  have hfac : β' ≫ α = (completionFunctor B S hS F hF 𝓘 hI).map a := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext n
    obtain ⟨n⟩ := n
    refine (cancel_epi (completionTermProjection B S hS F hF 𝓘 hI M n)).1 ?_
    rw [completionTermProjection_naturality]
    show completionTermProjection B S hS F hF 𝓘 hI M n ≫
        formalPullbackCompletionLevel B S hS F hF 𝓘 E.property G.obj α' n ≫ α'.app (op n) = _
    exact (Category.assoc (completionTermProjection B S hS F hF 𝓘 hI M n)
      (formalPullbackCompletionLevel B S hS F hF 𝓘 E.property G.obj α' n)
      (α'.app (op n))).symm.trans ((congrArg (· ≫ α'.app (op n))
      (π_formalPullbackCompletionLevel B S hS F hF 𝓘 E.property G.obj α' n)).trans
      (formalPullbackLevel_comp_app B S hS F hF 𝓘 G.obj α' n))
  refine ⟨M, a, (asIso β').symm, ⟨t, ht0, ?_, ?_⟩, ?_⟩
  · exact idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘
      (PreservesKernel.iso (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)) a).symm t
      (idealPowerMultiple_kernel_formalPullbackMap_eq_bot B S hS F hF 𝓘 G.obj α'
        (fun k => (htk k).1))
  · exact idealPowerMultiple_eq_bot_of_iso B S hS F hF 𝓘
      (PreservesCokernel.iso (ObjectProperty.ι (isCoherent.{u, u} B S hS F hF)) a).symm t
      (idealPowerMultiple_cokernel_formalPullbackMap_eq_bot B S hS F hF 𝓘 hIcart E.property
        G.obj G.property α' hα (fun k => (htk k).2))
  · rw [Iso.symm_hom, asIso_inv, ← hfac, IsIso.inv_hom_id_assoc]

end AlgebraicGeometry.Space

end

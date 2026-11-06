module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerAdicFiltration
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalAnnihilation
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.GenericFreeComparison
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.LocallyFiniteCoproductIso

/-!
# The dévissage of a dimension layer without a Noetherian hypothesis

This file is the remaining step of Tag 02S9 over a scheme which is only locally of finite type
over the base: every coherent `𝒪_X`-module whose support has delta-dimension at most `k` has its
class in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` in the image of the map from `Z_k(X)`.

## Main results

* `Stacks.Chow.of_eq_of_supp_kernel_cokernel` — two objects of `Coh_{≤k}(X)` joined by a
  morphism whose kernel and cokernel, computed on the underlying `𝒪_X`-modules, are supported in
  delta-dimension at most `k - 1`, have the same class in the layer.
* `Stacks.Chow.exists_mem_nhds_finite_topDimension` — the points of delta-dimension exactly `k`
  in the support of a coherent module of support dimension at most `k` form a locally finite
  set.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-! ### Kernels and cokernels in a dimension layer, read on the underlying modules -/

/-- The functor carrying an object of `Coh_{≤k}(X)` to the `𝒪_X`-module underlying it. -/
def dimLEForget : CoherentModulesDimLE C f k ⥤ X.Modules :=
  (coherentModulesDimLE C f k).ι ⋙ (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι

/-- The functor to `𝒪_X`-modules preserves finite limits: both inclusions are inclusions of weak
Serre subcategories, hence exact. -/
instance preservesFiniteLimits_dimLEForget : PreservesFiniteLimits (dimLEForget C f k) := by
  let h₁ : PreservesFiniteLimits (coherentModulesDimLE C f k).ι :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  let h₂ : PreservesFiniteLimits (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _
  change PreservesFiniteLimits ((coherentModulesDimLE C f k).ι ⋙
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι)
  exact comp_preservesFiniteLimits _ _

/-- The functor to `𝒪_X`-modules preserves finite colimits, for the same reason. -/
instance preservesFiniteColimits_dimLEForget : PreservesFiniteColimits (dimLEForget C f k) := by
  let h₁ : PreservesFiniteColimits (coherentModulesDimLE C f k).ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  let h₂ : PreservesFiniteColimits (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _
  change PreservesFiniteColimits ((coherentModulesDimLE C f k).ι ⋙
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι)
  exact comp_preservesFiniteColimits _ _

/-- **Two objects of a dimension layer joined by a morphism which is generically invertible have
the same class.** The morphism and the hypotheses on its kernel and cokernel are all on the
underlying `𝒪_X`-modules, which is the form in which a construction delivers them; the inclusions
of the two Serre subcategories involved are fully faithful, so the morphism comes from one of the
layer, and they are exact, so the kernel and cokernel there have the same underlying modules. -/
theorem of_eq_of_supp_kernel_cokernel (A B : CoherentModulesDimLE C f k)
    (ψ : A.obj.obj ⟶ B.obj.obj)
    (hker : ∀ x ∈ SheafOfModules.supp (kernel ψ),
      relativeDimension C.dimensionFunction f x ≤ k - 1)
    (hcoker : ∀ x ∈ SheafOfModules.supp (cokernel ψ),
      relativeDimension C.dimensionFunction f x ≤ k - 1) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj B) := by
  have FF : (dimLEForget C f k).FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  have hφ : (dimLEForget C f k).map (FF.preimage ψ) = ψ := FF.map_preimage ψ
  have key : ∀ (K : CoherentModulesDimLE C f k) (N : X.Modules),
      ((dimLEForget C f k).obj K ≅ N) →
      (∀ x ∈ SheafOfModules.supp N, relativeDimension C.dimensionFunction f x ≤ k - 1) →
      lowerDimensionClass C f (k - 1) k K := fun K N e hN ↦
    (dimLEObj C f (k - 1) _ (AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
      K.obj.property) fun x hx ↦ hN x ((SheafOfModules.supp_eq_of_iso e).subset hx)).property
  exact of_eq_of_lowerDimensionClass_kernel_cokernel C f k (FF.preimage ψ)
    (key _ _ (PreservesKernel.iso (dimLEForget C f k) (FF.preimage ψ) ≪≫ kernelIsoOfEq hφ) hker)
    (key _ _ (PreservesCokernel.iso (dimLEForget C f k) (FF.preimage ψ) ≪≫ cokernelIsoOfEq hφ)
      hcoker)

/-! ### The top-dimensional points of the support are locally finite -/

/-- **The points of delta-dimension exactly `k` in the support of a coherent module whose support
has delta-dimension at most `k` form a locally finite set.** Each such point is the generic point
of an irreducible component of the support by Stacks 02QW, those components form a locally finite
family, and a component has only one generic point. -/
theorem exists_mem_nhds_finite_topDimension (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F)
    (hFk : ∀ x ∈ SheafOfModules.supp F, relativeDimension C.dimensionFunction f x ≤ k)
    (x : X) : ∃ t ∈ nhds x, {y : X | y ∈ SheafOfModules.supp F ∧
      relativeDimension C.dimensionFunction f y = k ∧ y ∈ t}.Finite := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := hF
  have hFk' : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt) :=
    (schemeDeltaDimension_reducedSupport_le_iff C f F k).2 hFk
  obtain ⟨t, htx, hfin⟩ := locallyFinite_irreducibleComponents_supp F x
  refine ⟨t, htx, ?_⟩
  set points : Set X := {y : X | y ∈ SheafOfModules.supp F ∧
    relativeDimension C.dimensionFunction f y = k ∧ y ∈ t} with hpoints
  have hgen (y : points) :
      ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
        IsGenericPoint y.1 (Subtype.val '' Z.1 : Set X) :=
    isGenericPoint_component_supp_of_relativeDimension_eq C f F k y.1 hFk' y.2.1 y.2.2.1
  set K : Set (irreducibleComponents (SheafOfModules.supp F : Set X)) :=
    {Z | ((Subtype.val '' Z.1 : Set X) ∩ t).Nonempty} with hK
  have : Finite K := hfin.to_subtype
  have hinj : Function.Injective fun y : points ↦
      (⟨(hgen y).choose, ⟨y.1, (hgen y).choose_spec.mem, y.2.2.2⟩⟩ : K) := by
    intro y z hyz
    have hcomp : (hgen y).choose = (hgen z).choose := congrArg Subtype.val hyz
    exact Subtype.ext ((hgen y).choose_spec.eq (hcomp ▸ (hgen z).choose_spec))
  have : Finite points := Finite.of_injective _ hinj
  exact Set.toFinite points

/-- The structure sheaf of the integral closed subscheme attached to a point, with its structure
sheaf spelled as the unit of the category of modules rather than through
`Stacks.Ample.unitModule`. -/
theorem integralComponentStructureSheaf_eq (x : X) :
    integralComponentStructureSheaf x =
      (Scheme.Modules.pushforward (integralComponentAt x).subschemeι).obj
        (SheafOfModules.unit (integralComponentAt x).subscheme.ringCatSheaf) :=
  rfl

/-! ### Generic invertibility over a set of top-dimensional points -/

/-- The inclusion of a kernel is a monomorphism. Supplied as an explicit proof: with the category
of modules on a scheme, instance search cannot discharge its own `HasZeroMorphisms` side
condition. -/
private theorem mono_kernel_ι {F G : X.Modules} (ψ : F ⟶ G) : Mono (kernel.ι ψ) := by
  have hfork : Mono (Fork.ι (Fork.ofι (kernel.ι ψ)
      ((kernel.condition ψ).trans comp_zero.symm))) :=
    Fork.IsLimit.mono (kernelIsKernel ψ)
  exact hfork

/-- **A morphism of `Coh_{≤k}(X)` invertible near every top-dimensional point of the supports of
its two terms induces an equality of classes in the layer.** The points are collected in a set
`S`; what is asked of `S` is that it contain every point of delta-dimension exactly `k` of either
support, and that the morphism be invertible on a neighbourhood of each of its members. The
kernel and the cokernel then have no point of delta-dimension `k` in their supports, so they lie
in `Coh_{≤k-1}(X)`. -/
theorem of_eq_of_isIso_near_topDimension (A B : CoherentModulesDimLE C f k)
    (ψ : A.obj.obj ⟶ B.obj.obj) (S : Set X)
    (hAtop : ∀ y ∈ SheafOfModules.supp A.obj.obj,
      relativeDimension C.dimensionFunction f y = k → y ∈ S)
    (hBtop : ∀ y ∈ SheafOfModules.supp B.obj.obj,
      relativeDimension C.dimensionFunction f y = k → y ∈ S)
    (hgen : ∀ y ∈ S, ∃ W : X.Opens, y ∈ W ∧
      IsIso ((Scheme.Modules.restrictFunctor W.ι).map ψ)) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj A) =
      GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj B) := by
  have key : ∀ (K T : X.Modules), SheafOfModules.supp K ⊆ SheafOfModules.supp T →
      (∀ y ∈ SheafOfModules.supp T, relativeDimension C.dimensionFunction f y ≤ k) →
      (∀ y ∈ SheafOfModules.supp T, relativeDimension C.dimensionFunction f y = k → y ∈ S) →
      (∀ W : X.Opens, IsIso ((Scheme.Modules.restrictFunctor W.ι).map ψ) →
        IsZero ((Scheme.Modules.restrictFunctor W.ι).obj K)) →
      ∀ y ∈ SheafOfModules.supp K, relativeDimension C.dimensionFunction f y ≤ k - 1 :=
    fun K T hKT hdim htop hz y hy ↦ by
      by_cases hyk : relativeDimension C.dimensionFunction f y = k
      · obtain ⟨W, hyW, hW⟩ := hgen y (htop y (hKT hy) hyk)
        exact absurd hyW (Stacks.Coherent.supp_subset_compl_of_isZero_restrict W K (hz W hW) hy)
      · have := hdim y (hKT hy)
        omega
  refine of_eq_of_supp_kernel_cokernel C f k A B ψ
    (key _ A.obj.obj ?_ (relativeDimension_le_of_mem_supp_dimLE C f k A) hAtop fun W hW ↦
      Stacks.Coherent.isZero_restrict_kernel_of_isIso_restrict W ψ hW)
    (key _ B.obj.obj ?_ (relativeDimension_le_of_mem_supp_dimLE C f k B) hBtop fun W hW ↦
      Stacks.Coherent.isZero_restrict_cokernel_of_isIso_restrict W ψ hW)
  · exact fun y hy ↦ @supp_subset_of_mono X _ _ (kernel.ι ψ) (mono_kernel_ι ψ) y hy
  · exact fun y hy ↦ Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_cokernel_subset ψ hy

/-! ### The comparison at one point -/

/-- **[Stacks, Tag 01YE] at a point, in the shape the dévissage of a dimension layer consumes.**
Let `G` be a coherent `𝒪_X`-module whose stalk at `x` is annihilated by the maximal ideal of
`𝒪_{X, x}`. Then there is a coherent module `M` supported in `closure {x}` with morphisms to
`⨁_{j < r} 𝒪_{closure {x}}` and to `G`, both invertible on one open neighbourhood of `x`.

This is `Stacks.Chow.exists_free_comparison_near_genericPoint` applied to the integral closed
subscheme attached to `x`, whose generic point is `x` itself. -/
theorem exists_free_comparison_at [IsLocallyNoetherian X] (G : X.Modules)
    (hGc : _root_.SheafOfModules.IsCoherent G) (x : X)
    (hkill : Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G x) :
    ∃ (r : ℕ) (M : X.Modules) (_ : _root_.SheafOfModules.IsCoherent M)
      (jm : M ⟶ ∐ fun _ : Fin r ↦ integralComponentStructureSheaf x) (β : M ⟶ G) (V : X.Opens),
      x ∈ V ∧ SheafOfModules.supp M ⊆ closure {x} ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map jm) ∧
      IsIso ((Scheme.Modules.restrictFunctor V.ι).map β) := by
  have := hGc
  have hint : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hirr : IrreducibleSpace (integralComponentAt x).subscheme :=
    irreducibleSpace_of_isIntegral _
  have hξ : IsGenericPoint (genericPoint (integralComponentAt x).subscheme)
      (Set.univ : Set (integralComponentAt x).subscheme) :=
    genericPoint_spec _
  have hbase : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x := by
    have h1 : closure {(integralComponentAt x).subschemeι.base
                        (genericPoint (integralComponentAt x).subscheme)} =
        closure ({x} : Set X) := by
      rw [← range_eq_closure_singleton, Scheme.IdealSheafData.range_subschemeι,
        coe_support_integralComponentAt]
    exact IsGenericPoint.eq h1 isGenericPoint_closure
  have hkx : Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G
      ((integralComponentAt x).subschemeι.base
        (genericPoint (integralComponentAt x).subscheme)) := by
    rw [hbase]; exact hkill
  obtain ⟨r, M, hMc, jm, β, V, hV, hsuppM, hjm, hβ⟩ :=
    exists_free_comparison_near_genericPoint (integralComponentAt x).subschemeι
      (genericPoint (integralComponentAt x).subscheme) hξ G hkx
  refine ⟨r, M, hMc, ?_, β, V, hbase ▸ hV, ?_, ?_, hβ⟩
  · rw [integralComponentStructureSheaf_eq]; exact jm
  · refine hsuppM.trans ?_
    rw [range_eq_closure_singleton, hbase]
  · exact hjm

/-- The comparison at a point which carries nothing: the zero module, with the empty coproduct of
structure sheaves and the zero morphism. -/
theorem exists_zero_comparison_at (G : X.Modules) (x : X) :
    ∃ (M : X.Modules) (_ : _root_.SheafOfModules.IsCoherent M)
      (_ : M ⟶ ∐ fun _ : Fin 0 ↦ integralComponentStructureSheaf x) (_ : M ⟶ G),
      SheafOfModules.supp M = ∅ := by
  have hzero : IsZero (∐ fun _ : Fin 0 ↦ integralComponentStructureSheaf x) :=
    (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j ↦ Fin.elim0 j)
  refine ⟨∐ fun _ : Fin 0 ↦ integralComponentStructureSheaf x,
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
      (Stacks.SheafOfModules.isCoherent_of_isZero hzero), 𝟙 _, 0, ?_⟩
  exact Set.subset_eq_empty ((supp_coproduct_subset_of_finite _).trans
    (Set.iUnion_subset fun j ↦ Fin.elim0 j)) rfl

/-! ### The top-dimensional points of a support, and their closures -/

/-- The points of delta-dimension exactly `k` in the support of an `𝒪_X`-module. -/
def topDimensionPoints (G : X.Modules) : Set X :=
  {x | x ∈ SheafOfModules.supp G ∧ relativeDimension C.dimensionFunction f x = k}

/-- The closure of a point of delta-dimension exactly `k` in the support of `G`, and the empty
set at every other point. -/
def topDimensionClosure (G : X.Modules) (x : X) : Set X :=
  letI := Classical.propDecidable (x ∈ topDimensionPoints C f k G)
  if x ∈ topDimensionPoints C f k G then closure {x} else ∅

omit [LocallyOfFiniteType f] in
/-- At a point of `topDimensionPoints`, `topDimensionClosure` is the closure of the point. -/
theorem topDimensionClosure_of_mem {G : X.Modules} {x : X}
    (hx : x ∈ topDimensionPoints C f k G) :
    topDimensionClosure C f k G x = closure {x} := by
  simp only [topDimensionClosure]
  exact ite_eq_left hx

omit [LocallyOfFiniteType f] in
/-- At a point outside `topDimensionPoints`, `topDimensionClosure` is empty. -/
theorem topDimensionClosure_of_notMem {G : X.Modules} {x : X}
    (hx : x ∉ topDimensionPoints C f k G) : topDimensionClosure C f k G x = ∅ := by
  simp only [topDimensionClosure]
  exact ite_eq_right hx

omit [LocallyOfFiniteType f] in
/-- Each `topDimensionClosure C f k G x` is closed. -/
theorem isClosed_topDimensionClosure (G : X.Modules) (x : X) :
    IsClosed (topDimensionClosure C f k G x) := by
  by_cases hx : x ∈ topDimensionPoints C f k G
  · rw [topDimensionClosure_of_mem C f k hx]; exact isClosed_closure
  · rw [topDimensionClosure_of_notMem C f k hx]; exact isClosed_empty

/-- Every point of `topDimensionClosure C f k G x` has relative dimension at most `k`. -/
theorem relativeDimension_le_of_mem_topDimensionClosure (G : X.Modules) (x : X) {y : X}
    (hy : y ∈ topDimensionClosure C f k G x) :
    relativeDimension C.dimensionFunction f y ≤ k := by
  by_cases hx : x ∈ topDimensionPoints C f k G
  · rw [topDimensionClosure_of_mem C f k hx] at hy
    exact le_trans (relativeDimension_le_of_mem_closure C f hy) (le_of_eq hx.2)
  · rw [topDimensionClosure_of_notMem C f k hx] at hy; exact hy.elim

/-- A point of delta-dimension exactly `k` lying in the closure of a top-dimensional point of
`supp G` is itself one: the relative dimension drops strictly along a nontrivial
specialization. -/
theorem mem_topDimensionPoints_of_mem_topDimensionClosure (G : X.Modules) {x y : X}
    (hy : y ∈ topDimensionClosure C f k G x)
    (hyk : relativeDimension C.dimensionFunction f y = k) :
    y ∈ topDimensionPoints C f k G := by
  by_cases hx : x ∈ topDimensionPoints C f k G
  · rw [topDimensionClosure_of_mem C f k hx] at hy
    by_cases hyx : y = x
    · exact hyx ▸ hx
    · have hlt := relativeDimension_lt_of_mem_closure_of_ne C f hy hyx
      rw [hyk, hx.2] at hlt
      exact absurd hlt (lt_irrefl k)
  · rw [topDimensionClosure_of_notMem C f k hx] at hy; exact hy.elim

/-- A top-dimensional point of `supp G` lies outside the closure of every other point of
`supp G` of delta-dimension `k`. -/
theorem notMem_topDimensionClosure_of_ne (G : X.Modules) {x : X}
    (hx : x ∈ topDimensionPoints C f k G) (y : X) (hy : y ≠ x) :
    x ∉ topDimensionClosure C f k G y := by
  intro hmem
  by_cases hPy : y ∈ topDimensionPoints C f k G
  · rw [topDimensionClosure_of_mem C f k hPy] at hmem
    have hlt := relativeDimension_lt_of_mem_closure_of_ne C f hmem (Ne.symm hy)
    rw [hx.2, hPy.2] at hlt
    exact absurd hlt (lt_irrefl k)
  · rw [topDimensionClosure_of_notMem C f k hPy] at hmem
    exact hmem

/-- For a coherent module `G` whose support has relative dimension at most `k`, the family
`topDimensionClosure C f k G` is locally finite. -/
theorem locallyFinite_topDimensionClosure (G : X.Modules)
    (hGc : _root_.SheafOfModules.IsCoherent G)
    (hGdim : ∀ x ∈ SheafOfModules.supp G, relativeDimension C.dimensionFunction f x ≤ k) :
    LocallyFinite (topDimensionClosure C f k G) := by
  intro y
  obtain ⟨t, ht, hfin⟩ := exists_mem_nhds_finite_topDimension C f k G hGc hGdim y
  refine ⟨interior t, isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 ht),
    hfin.subset ?_⟩
  rintro z ⟨w, hwZ, hwt⟩
  have hPz : z ∈ topDimensionPoints C f k G := by
    by_contra h
    rw [topDimensionClosure_of_notMem C f k h] at hwZ
    exact hwZ
  rw [topDimensionClosure_of_mem C f k hPz] at hwZ
  exact ⟨hPz.1, hPz.2, interior_subset
    ((specializes_iff_mem_closure.2 hwZ).mem_open isOpen_interior hwt)⟩

/-! ### The dévissage of a module killed at every top-dimensional point -/

omit [LocallyOfFiniteType f] in
/-- **The comparison data at every point of `X` at once.** At a top-dimensional point of
`supp G` it is [Stacks, Tag 01YE]; elsewhere it is the zero module. -/
theorem exists_comparison_family [IsLocallyNoetherian X] (G : X.Modules)
    (hGc : _root_.SheafOfModules.IsCoherent G)
    (hkill : ∀ x ∈ topDimensionPoints C f k G,
      Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G x) :
    ∃ (r : X → ℕ) (M : ∀ _ : X, X.Modules)
      (_ : ∀ x, _root_.SheafOfModules.IsCoherent (M x))
      (jm : ∀ x, M x ⟶ ∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x)
      (β : ∀ x, M x ⟶ G) (V : X → X.Opens),
      (∀ x, r x ≠ 0 → x ∈ topDimensionPoints C f k G) ∧
      (∀ x, SheafOfModules.supp (M x) ⊆ topDimensionClosure C f k G x) ∧
      (∀ x ∈ topDimensionPoints C f k G, x ∈ V x ∧
        IsIso ((Scheme.Modules.restrictFunctor (V x).ι).map (jm x)) ∧
        IsIso ((Scheme.Modules.restrictFunctor (V x).ι).map (β x))) := by
  have h : ∀ x : X, ∃ (r : ℕ) (M : X.Modules) (_ : _root_.SheafOfModules.IsCoherent M)
      (jm : M ⟶ ∐ fun _ : Fin r ↦ integralComponentStructureSheaf x) (β : M ⟶ G) (V : X.Opens),
      (r ≠ 0 → x ∈ topDimensionPoints C f k G) ∧
      SheafOfModules.supp M ⊆ topDimensionClosure C f k G x ∧
      (x ∈ topDimensionPoints C f k G → x ∈ V ∧
        IsIso ((Scheme.Modules.restrictFunctor V.ι).map jm) ∧
        IsIso ((Scheme.Modules.restrictFunctor V.ι).map β)) := by
    intro x
    by_cases hx : x ∈ topDimensionPoints C f k G
    · obtain ⟨r, M, hMc, jm, β, V, hV, hsupp, hjm, hβ⟩ :=
        exists_free_comparison_at G hGc x (hkill x hx)
      refine ⟨r, M, hMc, jm, β, V, fun _ ↦ hx, ?_, fun _ ↦ ⟨hV, hjm, hβ⟩⟩
      rw [topDimensionClosure_of_mem C f k hx]
      exact hsupp
    · obtain ⟨M, hMc, jm, β, hsupp⟩ := exists_zero_comparison_at G x
      refine ⟨0, M, hMc, jm, β, ⊥, fun h ↦ absurd rfl h, ?_, fun h ↦ absurd h hx⟩
      rw [topDimensionClosure_of_notMem C f k hx, hsupp]
  choose r M hMc jm β V h1 h2 h3 using h
  exact ⟨r, M, hMc, jm, β, V, h1, h2, h3⟩

/-- **The class of a coherent module killed at every top-dimensional point of its support lies in
the image of the map from cycles**, over a scheme merely locally of finite type over the base.

For each point `ξ` of `supp G` of delta-dimension exactly `k`,
`Stacks.Chow.exists_free_comparison_at` — [Stacks, Tag 01YE] over a locally Noetherian scheme —
supplies a coherent module `M_ξ` supported in `Z_ξ = closure {ξ}` together with morphisms
`M_ξ ⟶ ⨁_{j < r_ξ} 𝒪_{Z_ξ}` and `M_ξ ⟶ G`, both invertible near `ξ`. Those points form a locally
finite set, so the direct sums `⨁_ξ M_ξ` and `⨁_ξ ⨁_{j < r_ξ} 𝒪_{Z_ξ}` are coherent, and the two
induced morphisms

`⨁_ξ M_ξ ⟶ G`  and  `⨁_ξ M_ξ ⟶ ⨁_ξ ⨁_{j < r_ξ} 𝒪_{Z_ξ}`

are invertible near every point of delta-dimension `k`: near `ξ` only the `ξ`-th summand
survives. Their kernels and cokernels therefore have support of delta-dimension at most `k - 1`,
so all three classes in `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` agree, and the last is the class of the
locally finite direct sum attached to the coefficient function `ξ ↦ r_ξ`. -/
theorem dimensionLayerClassMemRange_of_stalkKilled (G : X.Modules)
    (hGc : _root_.SheafOfModules.IsCoherent G)
    (hGdim : ∀ x ∈ SheafOfModules.supp G, relativeDimension C.dimensionFunction f x ≤ k)
    (hkill : ∀ x ∈ topDimensionPoints C f k G,
      Stacks.ClosedImmersion.StalkKilledByMaximalIdeal G x) :
    GrothendieckGroup.of ((lowerDimensionClass C f (k - 1) k).isoModSerre.Q.obj
      (dimLEObj C f k G hGc hGdim)) ∈ (cycleDimensionLayerHom C f k).range := by
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨r, M, hMc, jm, β, V, hrT, hsuppM, hisoT⟩ :=
    exists_comparison_family C f k G hGc hkill
  have hTlf : LocallyFinite (topDimensionClosure C f k G) :=
    locallyFinite_topDimensionClosure C f k G hGc hGdim
  have hTcl := isClosed_topDimensionClosure C f k G
  have hrlf : LocallyFiniteSupport r := by
    intro y
    obtain ⟨t, ht, hfin⟩ := exists_mem_nhds_finite_topDimension C f k G hGc hGdim y
    refine ⟨t, ht, hfin.subset ?_⟩
    rintro z ⟨hzt, hz⟩
    exact ⟨(hrT z hz).1, (hrT z hz).2, hzt⟩
  have hsuppQ : ∀ x : X, SheafOfModules.supp
      (∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x) ⊆
      topDimensionClosure C f k G x := by
    intro x
    refine (supp_coproduct_subset_of_finite _).trans (Set.iUnion_subset fun a ↦ ?_)
    have hrx : r x ≠ 0 := by
      intro h
      have := a.isLt
      omega
    rw [supp_integralComponentStructureSheaf, topDimensionClosure_of_mem C f k (hrT x hrx)]
  have hAc : _root_.SheafOfModules.IsCoherent (∐ M) :=
    isCoherent_coproduct_of_locallyFinite M hMc (hTlf.subset hsuppM)
  have eB : (∐ fun x : X ↦ ∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x) ≅
      cycleStructureSheaf r :=
    coproductSigmaIso fun i : Σ x : X, Fin (r x) ↦ integralComponentStructureSheaf i.1
  have hBc : _root_.SheafOfModules.IsCoherent
      (∐ fun x : X ↦ ∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x) :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso' eB
      (isCoherent_cycleStructureSheaf r hrlf)
  have hdim_top : ∀ N : X → X.Modules, (∀ x, SheafOfModules.supp (N x) ⊆
      topDimensionClosure C f k G x) → ∀ y ∈ SheafOfModules.supp (∐ N),
      relativeDimension C.dimensionFunction f y ≤ k ∧
      (relativeDimension C.dimensionFunction f y = k → y ∈ topDimensionPoints C f k G) :=
    fun N hN y hy ↦ by
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (supp_sigma_subset_iUnion_supp N hy)
      exact ⟨relativeDimension_le_of_mem_topDimensionClosure C f k G x (hN x hx),
        mem_topDimensionPoints_of_mem_topDimensionClosure C f k G (hN x hx)⟩
  have hAdim : ∀ y ∈ SheafOfModules.supp (∐ M),
      relativeDimension C.dimensionFunction f y ≤ k := fun y hy ↦ (hdim_top M hsuppM y hy).1
  have hAtop : ∀ y ∈ SheafOfModules.supp (∐ M),
      relativeDimension C.dimensionFunction f y = k → y ∈ topDimensionPoints C f k G :=
    fun y hy ↦ (hdim_top M hsuppM y hy).2
  have hBdim : ∀ y ∈ SheafOfModules.supp
      (∐ fun x : X ↦ ∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x),
      relativeDimension C.dimensionFunction f y ≤ k := fun y hy ↦ (hdim_top _ hsuppQ y hy).1
  have hBtop : ∀ y ∈ SheafOfModules.supp
      (∐ fun x : X ↦ ∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x),
      relativeDimension C.dimensionFunction f y = k → y ∈ topDimensionPoints C f k G :=
    fun y hy ↦ (hdim_top _ hsuppQ y hy).2
  have hAG := of_eq_of_isIso_near_topDimension C f k (dimLEObj C f k (∐ M) hAc hAdim)
    (dimLEObj C f k G hGc hGdim) (Sigma.desc (f := M) β) (topDimensionPoints C f k G)
    hAtop (fun y hy hyk ↦ ⟨hy, hyk⟩)
    fun y hy ↦ exists_isIso_restrict_desc M (topDimensionClosure C f k G) hsuppM hTcl hTlf β y y
      (notMem_topDimensionClosure_of_ne C f k G hy) (V y) (hisoT y hy).1 (hisoT y hy).2.2
  have hAB := of_eq_of_isIso_near_topDimension C f k (dimLEObj C f k (∐ M) hAc hAdim)
    (dimLEObj C f k _ hBc hBdim)
    (CategoryTheory.Limits.Sigma.map (g := M)
      (f := fun x : X ↦ ∐ fun _ : Fin (r x) ↦ integralComponentStructureSheaf x) jm)
    (topDimensionPoints C f k G) hAtop hBtop
    fun y hy ↦ exists_isIso_restrict_sigmaMap M _ (topDimensionClosure C f k G) hsuppM hsuppQ
      hTcl hTlf jm y y (notMem_topDimensionClosure_of_ne C f k G hy) (V y) (hisoT y hy).1
      (hisoT y hy).2.1
  have hBS := of_eq_of_module_iso C f k (dimLEObj C f k _ hBc hBdim)
    (cycleStructureSheafDimLE C f k ⟨r, hrlf, fun x hx ↦ (hrT x hx).2⟩) eB
  rw [← hAG, hAB, hBS]
  exact cycleStructureSheafClass_mem_range C f k ⟨r, hrlf, fun x hx ↦ (hrT x hx).2⟩

end Stacks.Chow

end

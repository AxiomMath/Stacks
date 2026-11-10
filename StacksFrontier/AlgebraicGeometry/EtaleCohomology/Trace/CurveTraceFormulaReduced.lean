module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveTraceFormulaOfCore
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteProjectivePullback
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
public import StacksFrontier.Topology.Dimension.KrullSeparation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace formula on a reduced curve from its core

Let `X` be a reduced separated scheme of finite type and dimension at most one over a finite field
`k`, and `F` a sheaf of `Λ`-modules on `X_étale` with perfect stalks which is locally constant
with finite projective values on a dense open `O` of `X`. Then
`Stacks.EtaleCohomology.CurveTraceCore` gives the trace formula of [Stacks, Tag 03UG] for `F`.

This is the reduction of Step 3 of the source to its good open pieces. The smooth locus `S` of
`X` is a dense open (`k` is perfect), and so is `O ∩ S`; removing the finitely many rational
points of `X` gives an open `O₁` containing every generic point of `X` which is not a closed
point. Around each such generic point `η` choose an affine open of `O₁` meeting no other
irreducible component; these are integral affine smooth curves without rational points, pairwise
disjoint, on which `F` is locally constant with finite projective values, and the complement of
their union is a finite set of closed points
(`Stacks.Topology.Dimension.exists_disjoint_irreducible_opens_of_topologicalKrullDim_le_one`).
Then `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_curveTraceCore`
applies.

The standard model `HasDerivedCategory.standard` of the derived categories is used because the
consumed trace and Frobenius objects (`perfectDerivedTrace`, `canonicalCompactSupportFrobenius`)
are defined there.

## Main results

* `Stacks.Topology.Dimension.exists_disjoint_irreducible_opens_of_topologicalKrullDim_le_one`
* `Stacks.EtaleCohomology.cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology Set

universe u

namespace Stacks.Topology.Dimension

/-- **Disjoint irreducible opens around the non-closed generic points.** In a Noetherian sober
`T0` space of Krull dimension at most one, let `O` be an open containing every generic point of an
irreducible component which is not a closed point, and `P` a property of opens such that every
point has arbitrarily small `P`-neighbourhoods. Then there are finitely many pairwise disjoint
irreducible `P`-opens contained in `O`, each containing a non-closed point, whose union has a
finite complement consisting of closed points. -/
public theorem exists_disjoint_irreducible_opens_of_topologicalKrullDim_le_one {X : Type u}
    [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X] [T0Space X]
    (hdim : topologicalKrullDim X ≤ 1) (P : Set X → Prop)
    (hP : ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ V, P V ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ U)
    (O : Set X) (hO : IsOpen O) (hgen : ∀ x ∈ genericPoints X, ¬ IsClosed ({x} : Set X) → x ∈ O) :
    ∃ (ι : Type u) (_ : Finite ι) (Z : ι → Set X), Pairwise (Function.onFun Disjoint Z) ∧
      (∀ i, P (Z i) ∧ IsOpen (Z i) ∧ Z i ⊆ O ∧ IsIrreducible (Z i) ∧
        ∃ x ∈ Z i, ¬ IsClosed ({x} : Set X)) ∧
      ((⋃ i, Z i)ᶜ).Finite ∧ ∀ x ∈ (⋃ i, Z i)ᶜ, IsClosed ({x} : Set X) := by
  classical
  let ι := {η : X // η ∈ genericPoints X ∧ ¬ IsClosed ({η} : Set X)}
  have hgenFin : (genericPoints X).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have : Finite ι := (hgenFin.subset fun x hx => hx.1).to_subtype
  -- every point lies in the closure of a generic point
  have hcover : ∀ x : X, ∃ ζ ∈ genericPoints X, x ∈ closure ({ζ} : Set X) := fun x =>
    ⟨_, (genericPoints.ofComponent
      ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).2,
      (genericPoints.isGenericPoint_ofComponent
        ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).symm ▸ mem_irreducibleComponent⟩
  -- distinct generic points do not lie in each other's closures
  have hsep : ∀ ζ ∈ genericPoints X, ∀ η ∈ genericPoints X, η ∈ closure ({ζ} : Set X) → η = ζ := by
    intro ζ hζ η hη h
    have hle : closure ({η} : Set X) ⊆ closure {ζ} :=
      closure_minimal (singleton_subset_iff.2 h) isClosed_closure
    exact congrArg Subtype.val (genericPoints.component_injective
      (a₁ := ⟨η, hη⟩) (a₂ := ⟨ζ, hζ⟩) (Subtype.ext (subset_antisymm hle (hη.2 hζ.1 hle))))
  let N : ι → Set X := fun η => (⋃ ζ ∈ {ζ ∈ genericPoints X | ζ ≠ η.1}, closure ({ζ} : Set X))ᶜ
  have hNo : ∀ η, IsOpen (N η) := fun η =>
    ((hgenFin.subset fun ζ hζ => hζ.1).isClosed_biUnion fun _ _ => isClosed_closure).isOpen_compl
  have hηN : ∀ η : ι, η.1 ∈ N η := by
    intro η hmem
    obtain ⟨ζ, ⟨hζ, hne⟩, hηζ⟩ := mem_iUnion₂.1 hmem
    exact hne (hsep ζ hζ η.1 η.2.1 hηζ).symm
  choose V hVP hVo hηV hVsub using fun η : ι =>
    hP η.1 (O ∩ N η) (hO.inter (hNo η)) ⟨hgen η.1 η.2.1 η.2.2, hηN η⟩
  -- a point of `V η` lies in the closure of `η` only
  have hVcl : ∀ η : ι, ∀ x ∈ V η, ∀ ζ ∈ genericPoints X, x ∈ closure ({ζ} : Set X) → ζ = η.1 := by
    intro η x hx ζ hζ hxζ
    by_contra hne
    exact (hVsub η hx).2 (mem_iUnion₂.2 ⟨ζ, ⟨hζ, hne⟩, hxζ⟩)
  refine ⟨ι, inferInstance, V, ?_, fun η => ⟨hVP η, hVo η, fun x hx => (hVsub η hx).1, ?_,
    η.1, hηV η, η.2.2⟩, ?_⟩
  · intro η η' hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    obtain ⟨ζ, hζ, hxζ⟩ := hcover x
    exact hne (Subtype.ext ((hVcl η x hx ζ hζ hxζ).symm.trans (hVcl η' x hx' ζ hζ hxζ)))
  · refine ⟨⟨η.1, hηV η⟩, (isIrreducible_singleton (x := η.1)).closure.2.open_subset (hVo η) ?_⟩
    intro x hx
    obtain ⟨ζ, hζ, hxζ⟩ := hcover x
    exact hVcl η x hx ζ hζ hxζ ▸ hxζ
  have hclosed : ∀ x ∈ (⋃ η, V η)ᶜ, IsClosed ({x} : Set X) := by
    intro x hx
    by_contra hxc
    refine hxc (isClosed_singleton_of_not_irreducibleComponent_subset hdim
      (T := closure ({x} : Set X)) isClosed_closure (fun C hC hCx => ?_)
      (subset_closure (mem_singleton x)))
    have hxgen : x ∈ genericPoints X := by
      change closure {x} ∈ irreducibleComponents X
      rw [subset_antisymm (hC.2 isIrreducible_singleton.closure hCx) hCx]
      exact hC
    exact hx (mem_iUnion.2 ⟨⟨x, hxgen, hxc⟩, hηV ⟨x, hxgen, hxc⟩⟩)
  refine ⟨?_, hclosed⟩
  obtain ⟨S, hSf, hScl, hSi, hST⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isOpen_iUnion hVo).isClosed_compl
  rw [hST]
  refine hSf.sUnion fun t ht => ?_
  obtain ⟨p, hp⟩ := QuasiSober.sober (hSi t ht) (hScl t ht)
  have hpc : closure ({p} : Set X) = t := isGenericPoint_def.1 hp
  have hpT : p ∈ (⋃ η, V η)ᶜ :=
    hST ▸ mem_sUnion.2 ⟨t, ht, hpc ▸ subset_closure (mem_singleton p)⟩
  rw [← hpc, (hclosed p hpT).closure_eq]
  exact finite_singleton p

end Stacks.Topology.Dimension

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme Stacks.Frobenius
  CategoryTheory.FilteredDerived

namespace Stacks.EtaleCohomology

/-- The image of a rational point of a separated scheme over a field is a closed point: the
rational point is a section of a separated morphism, hence proper. -/
@[sga "1 II 4.17" "special case"]
theorem isClosed_singleton_of_rationalPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] (y : rationalPoints f) :
    IsClosed ({y.1.base default} : Set X) := by
  have : IsProper (y.1 ≫ f) := by rw [y.2]; infer_instance
  have : IsProper y.1 := IsProper.of_comp y.1 f
  have h := y.1.isClosedMap.isClosed_range
  have : Set.range y.1.base = {y.1.base default} := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      rw [Subsingleton.elim t default]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  rwa [this] at h

section Standard

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k] (kbar : Type u)
  [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  [CharP kbar p] (hcard : Fintype.card k = p ^ q)

/-- **The trace formula `T''(X̄, j_! K) = T'(X̄, j_! K)` for a bounded complex on a reduced curve,
from the core.** Let `X` be a reduced separated scheme of finite type and dimension at most one
over `k` with a compactification `j : X ⟶ X̄`, and `K` a complex with perfect stalks concentrated
in degrees `[a, a + N]` whose terms are locally constant with finite projective values on a dense
open `O` of `X`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense_of_bounded
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (J : CompactificationOf (Over.mk f))
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) (hFs : HasPerfectStalks Λ K) (a : ℤ)
    (N : ℕ) (hlo : ∀ n, n < a → IsZero (K.obj.X n)) (hhi : ∀ n, a + N < n → IsZero (K.obj.X n))
    (O : X.Opens) (hO : Dense (O : Set X))
    (hF : ∀ n, a ≤ n → n ≤ a + N → Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      O.toScheme.smallEtaleTopology ((etaleModuleRestriction.{u, 0} Λ O.ι).obj (K.obj.X n))) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj K)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have := finite_rationalPoints f
  let R : Set X := Set.range fun y : rationalPoints f => y.1.base default
  have hRcl : IsClosed R := by
    rw [← Set.biUnion_of_singleton R]
    refine (Set.finite_range _).isClosed_biUnion fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx
    exact isClosed_singleton_of_rationalPoint f y
  let O₁ : Set X := (O : Set X) ∩ f.smoothLocus ∩ Rᶜ
  have hO₁ : IsOpen O₁ := (O.isOpen.inter f.smoothLocus.isOpen).inter hRcl.isOpen_compl
  have hgen : ∀ x ∈ genericPoints X, ¬ IsClosed ({x} : Set X) → x ∈ O₁ := by
    intro x hx hxc
    refine ⟨⟨TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense O.isOpen hO hx,
      TopologicalSpace.NoetherianSpace.mem_of_mem_genericPoints_of_dense f.smoothLocus.isOpen
        f.dense_smoothLocus_of_perfectField hx⟩, ?_⟩
    rintro ⟨y, rfl⟩
    exact hxc (isClosed_singleton_of_rationalPoint f y)
  obtain ⟨ι, hι, Zs, hdisj, hZ, hTfin, hTcl⟩ :=
    Stacks.Topology.Dimension.exists_disjoint_irreducible_opens_of_topologicalKrullDim_le_one
      hdim (fun V => ∃ U : X.affineOpens, ((U : X.Opens) : Set X) = V) (fun x U hU hx => by
        obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx hU
        exact ⟨V, ⟨⟨V, hV⟩, rfl⟩, V.isOpen, hxV, hVU⟩) O₁ hO₁ hgen
  choose Ua hUa using fun i => (hZ i).1
  let Z : ι → X.Opens := fun i => (Ua i).1
  have hZs : ∀ i, (Z i : Set X) = Zs i := hUa
  have : ∀ i, IsAffine (Z i) := fun i => (Ua i).2
  have : ∀ i, IrreducibleSpace (Z i) := fun i =>
    isIrreducible_iff_irreducibleSpace.mp ((hZs i).symm ▸ (hZ i).2.2.2.1)
  have : ∀ i, IsIntegral (Z i) := fun i => isIntegral_of_irreducibleSpace_of_isReduced _
  have : ∀ i, Smooth ((Z i).ι ≫ f) := fun i => by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    refine top_le_iff.1 fun x _ => ?_
    have hx : (Z i).ι x ∈ Zs i := by
      rw [← hZs i, ← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact ((hZ i).2.2.1 hx).1.2
  have hdimZ : ∀ i, topologicalKrullDim (Z i) = 1 := by
    intro i
    refine le_antisymm ((topologicalKrullDim_subspace_le X (Z i : Set X)).trans hdim) ?_
    obtain ⟨x, hxZ, hxc⟩ := (hZ i).2.2.2.2
    rw [← hZs i] at hxZ
    obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints ⟨x, hxZ⟩ (Z i).isOpen.isLocallyClosed
    obtain ⟨g, hg⟩ := QuasiSober.sober ((hZs i).symm ▸ (hZ i).2.2.2.1 : IsIrreducible
      (Z i : Set X)).closure isClosed_closure
    have hgZ : g ∈ (Z i : Set X) := (hg.mem_open_set_iff (Z i).isOpen).2
      ⟨x, subset_closure hxZ, hxZ⟩
    have hgy : g ⤳ y := by
      rw [specializes_iff_mem_closure, hg.def]
      exact subset_closure hyZ
    have hgne : g ≠ y := by
      rintro rfl
      apply hxc
      have : closure (Z i : Set X) = {g} := by
        rw [← hg.def]
        exact hyc.closure_eq
      have hx' : x ∈ ({g} : Set X) := this ▸ subset_closure hxZ
      rw [Set.mem_singleton_iff.1 hx']
      exact hyc
    exact one_le_topologicalKrullDim_of_specializes_of_ne
      (x := (⟨g, hgZ⟩ : (Z i : Set X))) (y := ⟨y, hyZ⟩)
      (Topology.IsInducing.subtypeVal.specializes_iff.1 hgy)
      (fun h => hgne (congrArg Subtype.val h))
  have hrat : ∀ i, IsEmpty (rationalPoints ((Z i).ι ≫ f)) := by
    intro i
    refine ⟨fun y => ?_⟩
    have hx : (Z i).ι (y.1.base default) ∈ Zs i := by
      rw [← hZs i, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    exact ((hZ i).2.2.1 hx).2 ⟨⟨y.1 ≫ (Z i).ι, by rw [Category.assoc]; exact y.2⟩, rfl⟩
  have hloc : ∀ i n, a ≤ n → n ≤ a + N → ∀ (V : Scheme.{u}) (e : V ⟶ X) [IsOpenImmersion e],
      Set.range e.base ⊆ Z i → Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        V.smallEtaleTopology ((etaleModuleRestriction.{u, 0} Λ e).obj (K.obj.X n)) := by
    intro i n hn hn' V e _ he
    have hsub : Set.range e.base ⊆ Set.range O.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact fun x hx => ((hZ i).2.2.1 (hZs i ▸ he hx)).1.1
    obtain ⟨e', he'⟩ : ∃ e', e' ≫ O.ι = e := ⟨_, IsOpenImmersion.lift_fac O.ι e hsub⟩
    subst he'
    have : IsOpenImmersion e' := IsOpenImmersion.of_comp e' O.ι
    refine Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
      ((etaleModuleRestrictionCompIso.{u, 0} Λ e' O.ι).app (K.obj.X n)) ?_
    exact isFiniteProjectiveLocallyConstant_etaleModuleRestriction Λ e' _ (hF n hn hn')
  have hU : (⋃ i, (Z i : Set X)) = ⋃ i, Zs i := by simp only [hZs]
  exact cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_bounded Λ kbar p q hcard
    hcore f J K hFs a N hlo hhi Z (fun i j hij => by
      change Disjoint (Z i) (Z j)
      rw [disjoint_iff, ← SetLike.coe_set_eq, TopologicalSpace.Opens.coe_inf,
        TopologicalSpace.Opens.coe_bot, hZs, hZs, ← Set.disjoint_iff_inter_eq_empty]
      exact hdisj hij) hdimZ hrat hloc (hU ▸ hTfin) (hU ▸ hTcl)

/-- **The trace formula `T''(X̄, j_! F) = T'(X̄, j_! F)` on a reduced curve, from the core.** Let
`X` be a reduced separated scheme of finite type and dimension at most one over `k` with a
compactification `j : X ⟶ X̄`, and `F` a sheaf of `Λ`-modules with perfect stalks which is locally
constant with finite projective values on a dense open `O` of `X`. -/
theorem cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense
    [Algebra.IsAlgebraic k kbar] {hΛ : (Nat.card Λ : k) ≠ 0}
    (hcore : CurveTraceCore Λ k hΛ kbar p q hcard) {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (J : CompactificationOf (Over.mk f))
    (F : EtaleModules.{u, 0} Λ X)
    (hFs : HasPerfectStalks Λ
      ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
    (O : X.Opens) (hO : Dense (O : Set X))
    (hF : Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ O.toScheme.smallEtaleTopology
      ((etaleModuleRestriction.{u, 0} Λ O.ι).obj F)) :
    CohomologicalTraceFormula Λ kbar p q hcard (Over.mk J.toBase)
      ((etaleModuleExtensionByZero.{u, 0} Λ J.immersion).mapCochainComplexPlus.obj
        ⟨(CochainComplex.singleFunctor _ 0).obj F, CochainComplex.plus_singleFunctor_obj F⟩)
      (hasPerfectStalks_extensionByZero Λ J.immersion _ hFs) :=
  cohomologicalTraceFormula_extensionByZero_of_curveTraceCore_of_dense_of_bounded Λ kbar p q hcard
    hcore f hdim J _ hFs 0 0 (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega))
    (fun n hn => HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)) O hO
    (fun n hn hn' => by
      obtain rfl : n = 0 := by omega
      exact Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr _ _
        ((etaleModuleRestriction.{u, 0} Λ O.ι).mapIso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm) hF)

end Standard

end Stacks.EtaleCohomology

end

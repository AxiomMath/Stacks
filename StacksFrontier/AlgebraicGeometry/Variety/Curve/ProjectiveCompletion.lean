module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.FibrePoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Noetherian.GenericPointsDenseOpen
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0BXV: the projective completion of a scheme of dimension at most one

[Stacks, Tag 0BXV] says that a separated scheme `X` of finite type over a field `k` with
`dim(X) ≤ 1` admits an open immersion `j : X ⟶ X̄` with

1. `X̄` H-projective over `k`, i.e. a closed subscheme of `ℙᵈ_k` for some `d`;
2. `j(X) ⊆ X̄` dense and scheme-theoretically dense;
3. `X̄ \ X = {x₁, …, xₙ}` a finite set of closed points of `X̄`.

## Main results

* `Stacks.CurveProjectiveCompletion.exists_projective_completion_aux_of_isHQuasiProjective`:
  the completion of an H-quasi-projective `X`, with its structure morphism locally of finite type
  and `dim(X̄) ≤ 1`.
* `Stacks.CurveProjectiveCompletion.exists_projective_completion_aux`: the same completion, with
  the existence of ample invertible sheaves in dimension at most one, [Stacks, Tag 09NZ], as the
  hypothesis `h09NZ`.
* `Stacks.CurveProjectiveCompletion.exists_projective_completion`: [Stacks, Tag 0BXV] with the
  hypothesis `h09NZ`.
* `Stacks.CurveProjectiveCompletion.exists_projective_completion_of_dimension_le_one`:
  [Stacks, Tag 0BXV].

## Implementation notes

H-projectivity is `AlgebraicGeometry.IsProjectiveMorphism`, clause (2) of [Stacks, Tag 01W8]: a
closed immersion into `AlgebraicGeometry.projectiveSpaceOver d S` over the base.

Scheme-theoretic density is `AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense` applied to
`AlgebraicGeometry.Scheme.Hom.opensRange` of the open immersion, and topological density is
`AlgebraicGeometry.IsDominant`.

Clause (3) is spelled as a pair: the complement of the range is finite, and every point outside
the range is closed.

## References

* [Stacks Project, Tag 0BXV](https://stacks.math.columbia.edu/tag/0BXV)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 01R7](https://stacks.math.columbia.edu/tag/01R7)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.CurveProjectiveCompletion

/-! ### Generic points and dense opens -/

/-- If `x ⤳ y` with `x ≠ y` in a T0 space, then `closure {y} < closure {x}` as irreducible closed
subsets. -/
theorem closureSingleton_lt_of_specializes {Z : Type*} [TopologicalSpace Z] [T0Space Z] {x y : Z}
    (hxy : x ⤳ y) (hne : x ≠ y) :
    IrreducibleCloseds.closureSingleton y < IrreducibleCloseds.closureSingleton x := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [← SetLike.coe_subset_coe, IrreducibleCloseds.coe_closureSingleton,
      IrreducibleCloseds.coe_closureSingleton]
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hxy)) isClosed_closure
  · intro heq
    have hclosures : closure ({y} : Set Z) = closure {x} := by
      simpa only [IrreducibleCloseds.coe_closureSingleton] using
        congrArg (fun C : IrreducibleCloseds Z => (C : Set Z)) heq
    have hyx : y ⤳ x := by
      rw [specializes_iff_mem_closure, hclosures]
      exact subset_closure rfl
    exact hne (hxy.antisymm hyx).eq

/-- In a quasi-sober T0 space, if `U` contains every generic point of an irreducible component,
then every point `z` is a specialization of some point of `U`. -/
theorem exists_specializes_mem_of_genericPoints_subset {Z : Type*} [TopologicalSpace Z]
    [T0Space Z] [QuasiSober Z] {U : Set Z} (hgeneric : genericPoints Z ⊆ U) (z : Z) :
    ∃ η : Z, η ⤳ z ∧ η ∈ U := by
  have hirr : IsIrreducible (irreducibleComponent z) := isIrreducible_irreducibleComponent
  refine ⟨hirr.genericPoint, ?_, hgeneric ?_⟩
  · exact (hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent).specializes
      mem_irreducibleComponent
  · show closure ({hirr.genericPoint} : Set Z) ∈ irreducibleComponents Z
    rw [(hirr.isGenericPoint_genericPoint isClosed_irreducibleComponent).def]
    exact irreducibleComponent_mem_irreducibleComponents z

/-- In a Noetherian quasi-sober T0 space of dimension at most one, the complement of an open
subset containing all the generic points is a finite set of closed points. -/
@[ega "II 7.4.3" "partial"]
theorem finite_compl_of_genericPoints_subset {Z : Type*} [TopologicalSpace Z] [T0Space Z]
    [QuasiSober Z] [NoetherianSpace Z] {U : Set Z} (hU : IsOpen U)
    (hdim : topologicalKrullDim Z ≤ 1) (hgeneric : genericPoints Z ⊆ U) :
    (Uᶜ).Finite ∧ ∀ z ∈ Uᶜ, IsClosed ({z} : Set Z) := by
  obtain ⟨S, hSfinite, hSclosed, hSirred, hScover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hU.isClosed_compl
  have hsingleton : ∀ C ∈ S, ∃ z, C = {z} := by
    intro C hC
    have hCirr : IsIrreducible C := hSirred C hC
    set η := hCirr.genericPoint
    have hηC : IsGenericPoint η C := hCirr.isGenericPoint_genericPoint (hSclosed C hC)
    have hnotU : η ∉ U := (hScover ▸ Set.mem_sUnion.mpr ⟨C, hC, hηC.mem⟩ : η ∈ Uᶜ)
    obtain ⟨ξ, hξη, hξU⟩ := exists_specializes_mem_of_genericPoints_subset hgeneric η
    have hξne : ξ ≠ η := fun h => hnotU (h ▸ hξU)
    have hEq : ∀ z ∈ C, z = η := by
      intro z hz
      by_contra hne
      have h01 := closureSingleton_lt_of_specializes (hηC.specializes hz) (Ne.symm hne)
      have h12 := closureSingleton_lt_of_specializes hξη hξne
      have hchain : (2 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
        unfold topologicalKrullDim Order.krullDim
        refine le_iSup_of_le
          (((RelSeries.singleton _ (IrreducibleCloseds.closureSingleton ξ)).cons
            (IrreducibleCloseds.closureSingleton η) h12).cons
              (IrreducibleCloseds.closureSingleton z) (by exact h01)) le_rfl
      exact absurd (hchain.trans hdim) (by norm_num)
    exact ⟨η, Set.eq_singleton_iff_unique_mem.mpr ⟨hηC.mem, hEq⟩⟩
  refine ⟨?_, ?_⟩
  · rw [hScover]
    refine hSfinite.sUnion fun C hC => ?_
    obtain ⟨z, rfl⟩ := hsingleton C hC
    exact Set.finite_singleton z
  · intro z hz
    obtain ⟨C, hC, hzC⟩ := Set.mem_sUnion.mp (hScover ▸ hz)
    obtain ⟨w, hw⟩ := hsingleton C hC
    rw [hw, Set.mem_singleton_iff] at hzC
    subst hzC
    exact hw ▸ hSclosed C hC

/-! ### Residue fields along an open immersion -/

/-- For an open immersion `j : X ⟶ Y` over `Spec k`, the residue fields of `X` at `x` and of `Y`
at `j x` have the same transcendence degree over `k`. -/
theorem trdeg_residueField_of_isOpenImmersion (k : Type u) [Field k] {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (f : X ⟶ Spec (CommRingCat.of k))
    (q : Y ⟶ Spec (CommRingCat.of k)) (hq : j ≫ q = f) (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra k (Y.residueField (j x)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation (j x)).hom.toAlgebra
    Algebra.trdeg k (X.residueField x) = Algebra.trdeg k (Y.residueField (j x)) := by
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra k (Y.residueField (j x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation (j x)).hom.toAlgebra
  let e : Y.residueField (j x) ≃ₐ[k] X.residueField x :=
    { RingEquiv.ofBijective (j.residueFieldMap x).hom
        ⟨(ConcreteCategory.bijective_of_isIso _).1,
          (ConcreteCategory.bijective_of_isIso _).2⟩ with
      commutes' := fun a ↦ by
        show (j.residueFieldMap x).hom
            (((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫ Y.Γevaluation (j x)).hom a) =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom a
        rw [← hq, Scheme.Hom.comp_appTop]
        exact Scheme.Γevaluation_naturality_apply j x
          (q.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) }
  exact e.trdeg_eq.symm

/-- If `j : X ⟶ Y` is an open immersion with dense image over `Spec k`, with both structure
morphisms locally of finite type and `Y` Noetherian, then `dim(Y) ≤ dim(X)`. -/
@[ega "IV 10.6.2" "partial", ega "IV 5.2.5" "partial"]
theorem topologicalKrullDim_le_of_dense_isOpenImmersion (k : Type u) [Field k]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (f : X ⟶ Spec (CommRingCat.of k))
    (q : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [LocallyOfFiniteType q]
    [NoetherianSpace Y] (hq : j ≫ q = f) (hdense : Dense (Set.range j.base)) :
    topologicalKrullDim (Y : Type u) ≤ topologicalKrullDim (X : Type u) := by
  rw [topologicalKrullDim_eq_iSup_trdeg_residueField k Y q]
  refine iSup_le fun y => ?_
  obtain ⟨y, hygen⟩ := y
  obtain ⟨x, rfl⟩ := NoetherianSpace.mem_of_mem_genericPoints_of_dense
    j.isOpenEmbedding.isOpen_range hdense hygen
  have hxgen : x ∈ genericPoints X := genericPoints_preimage_of_isOpenImmersion j hygen
  have h := trdeg_residueField_of_isOpenImmersion k j f q hq x
  refine (congrArg (fun d : Cardinal => (Cardinal.toENat d : WithBot ℕ∞)) h.symm).trans_le ?_
  rw [topologicalKrullDim_eq_iSup_trdeg_residueField k X f]
  exact le_iSup_of_le (⟨x, hxgen⟩ : genericPoints X) le_rfl

/-! ### Stacks Tag 0BXV -/

/-- A separated scheme `X` of finite type over a field `k` with `dim(X) ≤ 1` whose structure
morphism is H-quasi-projective has an open immersion `j : X ⟶ X̄` into an H-projective `k`-scheme
`X̄`, locally of finite type over `k` with `dim(X̄) ≤ 1`, such that `j` is dominant with
scheme-theoretically dense image and `X̄ \ j(X)` is a finite set of closed points. -/
theorem exists_projective_completion_aux_of_isHQuasiProjective
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hqp : AlgebraicGeometry.IsHQuasiProjective f)
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = f ∧ IsProjectiveMorphism q ∧ LocallyOfFiniteType q ∧
        topologicalKrullDim (Y : Type u) ≤ 1 ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y) := by
  obtain ⟨n, g, hg, hgqc, hgf⟩ := hqp
  have : IsImmersion g := hg
  have : QuasiCompact g := hgqc
  have hj : IsOpenImmersion g.toImage := isOpenImmersion_toImage g (Or.inl hgqc)
  have : IsOpenImmersion g.toImage := hj
  set q := g.imageι ≫ (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  have hjq : g.toImage ≫ q = f := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact hgf
  have hproj : IsProjectiveMorphism q := ⟨n, g.imageι, inferInstance, rfl⟩
  have := isProper_projectiveSpaceOver n (Spec (CommRingCat.of k))
  have hqft : LocallyOfFiniteType q := inferInstance
  have : IsLocallyNoetherian g.image := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace g.image := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian g.image := AlgebraicGeometry.IsNoetherian.mk
  have hdom : IsDominant g.toImage := isDominant_toImage g (Or.inl hgqc)
  have hstd : Scheme.Opens.IsSchemeTheoreticallyDense g.toImage.opensRange :=
    isSchemeTheoreticallyDense_toImage g (Or.inl hgqc)
  have hdimY : topologicalKrullDim (g.image : Type u) ≤ 1 :=
    (topologicalKrullDim_le_of_dense_isOpenImmersion k g.toImage f q hjq hdom.denseRange).trans hdim
  obtain ⟨hfin, hclosed⟩ :=
    finite_compl_of_genericPoints_subset g.toImage.isOpenEmbedding.isOpen_range hdimY
      ((isDominant_iff_genericPoints_subset_range g.toImage).mp hdom)
  exact ⟨g.image, _, g.toImage, hj, hjq, hproj, hqft, hdimY, hdom, hstd, hfin, hclosed⟩

/-- Assuming `h09NZ`, the statement of [Stacks, Tag 09NZ], a separated scheme `X` of finite type
over a field `k` with `dim(X) ≤ 1` has an open immersion `j : X ⟶ X̄` into an H-projective
`k`-scheme `X̄`, locally of finite type over `k` with `dim(X̄) ≤ 1`, such that `j` is dominant with
scheme-theoretically dense image and `X̄ \ j(X)` is a finite set of closed points. -/
theorem exists_projective_completion_aux
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = f ∧ IsProjectiveMorphism q ∧ LocallyOfFiniteType q ∧
        topologicalKrullDim (Y : Type u) ≤ 1 ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y) :=
  exists_projective_completion_aux_of_isHQuasiProjective k f
    (Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_ampleOfNoetherianSeparatedDimLEOne
      h09NZ f hdim) hdim

/-- Assuming `h09NZ`, the statement of [Stacks, Tag 09NZ]: let `X` be a separated scheme of
finite type over a field `k` with `dim(X) ≤ 1`. Then there is an open immersion `j : X ⟶ X̄` such
that

1. `X̄` is H-projective over `k`, a closed subscheme of `ℙᵈ_k` for some `d`;
2. `j(X)` is dense and scheme-theoretically dense in `X̄`;
3. `X̄ \ j(X)` is a finite set of closed points of `X̄`. -/
theorem exists_projective_completion
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = f ∧ IsProjectiveMorphism q ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y) := by
  obtain ⟨Y, q, j, hj, hjq, hproj, -, -, hdom, hstd, hfin, hclosed⟩ :=
    exists_projective_completion_aux h09NZ k f hdim
  exact ⟨Y, q, j, hj, hjq, hproj, hdom, hstd, hfin, hclosed⟩

/-- Let `X` be a separated scheme of finite type over a field `k` with `dim(X) ≤ 1`. Then there
is an open immersion `j : X ⟶ X̄` such that

1. `X̄` is H-projective over `k`, a closed subscheme of `ℙᵈ_k` for some `d`;
2. `j(X)` is dense and scheme-theoretically dense in `X̄`;
3. `X̄ \ j(X)` is a finite set of closed points of `X̄`. -/
@[stacks 0BXV "the whole tag: all three clauses, for every separated scheme of finite type over \
`k` of dimension at most one"]
theorem exists_projective_completion_of_dimension_le_one
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Y) (hj : IsOpenImmersion j),
      letI : IsOpenImmersion j := hj
      j ≫ q = f ∧ IsProjectiveMorphism q ∧ IsDominant j ∧
        Scheme.Opens.IsSchemeTheoreticallyDense j.opensRange ∧
        ((Set.range j.base)ᶜ).Finite ∧
        ∀ y : Y, y ∉ Set.range j.base → IsClosed ({y} : Set Y) :=
  exists_projective_completion (fun Y _ _ hdimY =>
    Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one
      Y hdimY) k f hdim

end Stacks.CurveProjectiveCompletion

end

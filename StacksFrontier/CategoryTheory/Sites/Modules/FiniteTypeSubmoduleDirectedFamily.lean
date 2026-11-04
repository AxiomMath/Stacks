module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.CategoryTheory.Sites.Modules.SubmoduleSupLocal
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleFilteredColimitSections
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen

/-!
# A finite type submodule inside a directed family of submodules

Let `M` be a sheaf of modules on a site, `(N_i)` a directed family of submodules of `M` and
`G ⊆ M` a submodule of finite type every local section of which lies, locally, in some `N_i`.
If every covering family of the final object is refined by a finite covering family of
quasi-compact objects, then `G` is contained in a single `N_i`.  On a quasi-compact topological
space with a basis of quasi-compact opens, in particular on a quasi-compact scheme, the
refinement exists.

This is the containment form of the second assertion of Stacks 01BB: the family need not be
indexed by a small category, and no colimit is formed.

## Main results

* `Stacks.SheafOfModules.exists_le_of_isFiniteType_of_finiteRefinement`: the containment on a
  site.
* `Stacks.SheafOfModules.exists_le_of_isFiniteType_of_compactSpace`: on a quasi-compact space
  with a basis of quasi-compact opens.
* `Stacks.SheafOfModules.exists_le_of_isFiniteType_of_compactSpace_scheme`: on a quasi-compact
  scheme.

## Implementation notes

The finitely many local generators of the finite type submodule live on a covering family; its
finite quasi-compact refinement carries finitely many restricted generators, each a section over
a quasi-compact object lying locally in members of the family, so it lies in one member
(`Stacks.SheafOfModules.exists_mem_of_isQuasiCompactObject`).  A common member for all of them
contains the whole submodule by local generation.

## References

* [Stacks Project, Tag 01BB](https://stacks.math.columbia.edu/tag/01BB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace Stacks.SheafOfModules

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A finite type submodule lies in one member of a locally exhausting directed family**, on a
site where every covering family of the final object is refined by a finite covering family of
quasi-compact objects. -/
theorem exists_le_of_isFiniteType_of_finiteRefinement
    (href : ∀ {I : Type u} (W : I → C), J.CoversTop W →
      ∃ (κ : Type u) (_ : Finite κ) (V : κ → C) (b : κ → I),
        (∀ t, Nonempty (V t ⟶ W (b t))) ∧ (∀ t, J.IsQuasiCompactObject (V t)) ∧ J.CoversTop V)
    {M : _root_.SheafOfModules.{u} R}
    {ι : Type*} [Nonempty ι] (N : ι → M.Submodule) (hN : Directed (· ≤ ·) N)
    (G : M.Submodule) (hG : G.toSheafOfModules.IsFiniteType)
    (hloc : ∀ (V : C) (x : M.val.obj (op V)), x ∈ G.obj (op V) → ∃ T : Sieve V, T ∈ J V ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ V), T f → ∃ i, M.val.map f.op x ∈ (N i).obj (op Y)) :
    ∃ i, G ≤ N i := by
  classical
  obtain ⟨I₀, W, hW, hgen⟩ :=
    (isFiniteTypeSections_of_isFiniteType (J := J) G.toSheafOfModules).exists_generators
  choose n s hs using hgen
  obtain ⟨κ, hκ, V, b, hq, hVqc, hVcov⟩ := href W hW
  let q : ∀ t, V t ⟶ W (b t) := fun t => (hq t).some
  -- the restricted generators, as sections of `M`
  let σ : ∀ t (j : Fin (n (b t))), M.val.obj (op (V t)) := fun t j =>
    (G.toSheafOfModules.val.restrictₛₗ (q t).op (s (b t) j)).1
  have hσ : ∀ p : (Σ t : κ, Fin (n (b t))), ∃ i, σ p.1 p.2 ∈ (N i).obj (op (V p.1)) := by
    intro p
    obtain ⟨T, hT, hTN⟩ := hloc (V p.1) (σ p.1 p.2)
      (G.toSheafOfModules.val.restrictₛₗ (q p.1).op (s (b p.1) p.2)).2
    exact exists_mem_of_isQuasiCompactObject N hN (hVqc p.1) _ T hT hTN
  choose i hi using hσ
  have := Fintype.ofFinite κ
  obtain ⟨i₀, hi₀⟩ := hN.finset_le (Finset.univ.image i)
  have hσ₀ : ∀ t j, σ t j ∈ (N i₀).obj (op (V t)) := fun t j =>
    _root_.SheafOfModules.Submodule.le_iff.1
      (hi₀ (i ⟨t, j⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))) _ (hi ⟨t, j⟩)
  refine ⟨i₀, _root_.SheafOfModules.Submodule.le_iff.2 fun Z x hx => ?_⟩
  let x' : G.toSheafOfModules.val.obj Z := ⟨x, hx⟩
  refine (N i₀).isSheaf x (J.transitive (hVcov Z.unop) _ fun Y g hg => ?_)
  obtain ⟨t, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  -- local generation by the restricted generators
  obtain ⟨S', hS', hlin⟩ :=
    generatesLocally_restrict (q t) (hs (b t)) Y h (G.toSheafOfModules.val.map g.op x')
  refine J.superset_covering ?_ hS'
  intro Y'' a ha
  obtain ⟨coef, hcoef⟩ := hlin Y'' a ha
  have hval := congrArg Subtype.val hcoef
  change M.val.map (a ≫ g).op x ∈ (N i₀).obj (op Y'')
  rw [op_comp, M.val.map_comp_apply]
  change (G.toSheafOfModules.val.restrictₛₗ a.op (G.toSheafOfModules.val.map g.op x')).1 ∈ _
  rw [← hval]
  have hP : (∑ j, coef j • G.toSheafOfModules.val.restrictₛₗ (a ≫ h).op
      (G.toSheafOfModules.val.restrictₛₗ (q t).op (s (b t) j))) ∈
        ((N i₀).obj (op Y'')).comap (G.ι.val.app (op Y'')).hom :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ((N i₀).map_mem (a ≫ h).op (hσ₀ t j))
  exact hP

end Site

section Space

variable {X : Type u} [TopologicalSpace X]

/-- On a quasi-compact space with a basis of quasi-compact opens, every open cover is refined by
a finite cover by quasi-compact opens. -/
theorem exists_finite_compact_refinement [CompactSpace X]
    (hB : ∀ (x : X) (U : TopologicalSpace.Opens X), x ∈ U →
      ∃ V : TopologicalSpace.Opens X, V ≤ U ∧ x ∈ V ∧ IsCompact (V : Set X))
    {I : Type u} (W : I → TopologicalSpace.Opens X)
    (hW : (Opens.grothendieckTopology X).CoversTop W) :
    ∃ (κ : Type u) (_ : Finite κ) (V : κ → TopologicalSpace.Opens X) (b : κ → I),
      (∀ t, Nonempty (V t ⟶ W (b t))) ∧
        (∀ t, (Opens.grothendieckTopology X).IsQuasiCompactObject (V t)) ∧
          (Opens.grothendieckTopology X).CoversTop V := by
  classical
  have hW' := (Opens.coversTop_iff X W).1 hW
  have hmem : ∀ x : X, ∃ i, x ∈ W i := fun x => by
    have : x ∈ (⨆ i, W i) := by rw [hW'.iSup_eq_top]; trivial
    simpa using this
  choose b₀ hb₀ using hmem
  choose V₀ hV₀le hxV₀ hV₀c using fun x => hB x (W (b₀ x)) (hb₀ x)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V₀ x : Set X))
    (fun x => (V₀ x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hxV₀ x⟩
  refine ⟨F, inferInstance, fun t => V₀ t.1, fun t => b₀ t.1, fun t => ⟨homOfLE (hV₀le t.1)⟩,
    fun t => Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact _ (hV₀c t.1), ?_⟩
  refine (Opens.coversTop_iff X _).2 (TopologicalSpace.IsOpenCover.mk ?_)
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **A finite type submodule lies in one member of a locally exhausting directed family**, on a
quasi-compact space with a basis of quasi-compact opens. -/
theorem exists_le_of_isFiniteType_of_compactSpace [CompactSpace X]
    (hB : ∀ (x : X) (U : TopologicalSpace.Opens X), x ∈ U →
      ∃ V : TopologicalSpace.Opens X, V ≤ U ∧ x ∈ V ∧ IsCompact (V : Set X))
    {M : _root_.SheafOfModules.{u} R}
    {ι : Type*} [Nonempty ι] (N : ι → M.Submodule) (hN : Directed (· ≤ ·) N)
    (G : M.Submodule) (hG : G.toSheafOfModules.IsFiniteType)
    (hloc : ∀ (V : TopologicalSpace.Opens X) (x : M.val.obj (op V)), x ∈ G.obj (op V) →
      ∃ T : Sieve V, T ∈ Opens.grothendieckTopology X V ∧
      ∀ ⦃Y : TopologicalSpace.Opens X⦄ (f : Y ⟶ V), T f →
        ∃ i, M.val.map f.op x ∈ (N i).obj (op Y)) :
    ∃ i, G ≤ N i :=
  exists_le_of_isFiniteType_of_finiteRefinement
    (fun W hW => exists_finite_compact_refinement hB W hW) N hN G hG hloc

end Space

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules in
/-- **A finite type submodule lies in one member of a locally exhausting directed family**, on a
quasi-compact scheme. -/
theorem exists_le_of_isFiniteType_of_compactSpace_scheme {T : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace T] {M : T.Modules}
    {ι : Type*} [Nonempty ι] (N : ι → M.Submodule) (hN : Directed (· ≤ ·) N)
    (G : M.Submodule) (hG : G.toSheafOfModules.IsFiniteType)
    (hloc : ∀ (V : T.Opens) (x : M.val.obj (op V)), x ∈ G.obj (op V) → ∃ S : Sieve V,
      S ∈ Opens.grothendieckTopology T V ∧
      ∀ ⦃Y : T.Opens⦄ (f : Y ⟶ V), S f → ∃ i, M.val.map f.op x ∈ (N i).obj (op Y)) :
    ∃ i, G ≤ N i := by
  refine exists_le_of_isFiniteType_of_compactSpace (fun x U hx => ?_) N hN G hG hloc
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact ⟨V, hVU, hxV, hV.isCompact⟩

end Stacks.SheafOfModules

end

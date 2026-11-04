module

public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLinesOfClosedSubset

/-!
# Lines through a point meeting a small closed set only at that point

Let `B ⊆ 𝐏(V)` be a closed subset of codimension at least two at each of its points and `p` a
closed point, **possibly lying on `B`**. Then a general line through `p` meets `B` at most in `p`:
there is a nonempty Zariski open subset of `𝐏(V)` each of whose closed points `q` lies, with `p`,
on a line `ℓ` with `ℓ ∩ B ⊆ {p}`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_lines_inter_subset_singleton`: the
  nonempty open set of second points of lines through `p` meeting `B` at most in `p`.

## Implementation notes

The projection away from `p` need not be finite on `B` minus `p`, so the image of `B` minus `p`
need not be closed; its *closure* is a proper closed subset of `𝐏(W_p)`, since the closure of the
image of a scheme of finite type has at most its dimension
(`AlgebraicGeometry.topologicalKrullDim_closure_image_le`).

## References

* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **A general line through `p` meets `B` at most in `p`**, for `B` closed of codimension at
least two at each of its points and `p` any closed point. -/
public theorem exists_isOpen_lines_inter_subset_singleton [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (hV : 3 ≤ Module.finrank k V)
    (B : Set (projectiveSpaceOfModule k V)) (hB : IsClosed B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k V)) →
        ∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧
          p ∈ linearSubspace k V W ∧ q ∈ linearSubspace k V W ∧
          linearSubspace k V W ∩ B ⊆ {p} := by
  set Wp := pointSubmodule k V p with hWp
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); lia⟩
  have hWrank : Module.finrank k ↥Wp = n := by
    have h := finrank_pointSubmodule_add_one k V p hp
    rw [← hWp] at h
    lia
  have hWnt : Nontrivial ↥Wp := Module.nontrivial_of_finrank_pos (R := k) (by lia)
  set D := projectionDomain k V Wp with hD
  have hDp : ((D : (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) =
      {p}ᶜ := coe_mapDomain_pointSubmodule k V p hp
  set A : Set D.toScheme := D.ι.base ⁻¹' B with hA
  have hAc : IsClosed A := hB.preimage D.ι.continuous
  set S := closure ((projection k V Wp).base '' A) with hS
  obtain ⟨j, hj⟩ : ∃ j, n = j + 2 := ⟨n - 2, by lia⟩
  have hdimB : topologicalKrullDim B ≤ (j : WithBot ℕ∞) := by
    refine topologicalKrullDim_le_of_forall_le_codimension (e := 2) hB ?_
      (fun x hx => by exact_mod_cast hcodim x hx)
    rw [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn, hj]
  have hdimA : topologicalKrullDim A ≤ topologicalKrullDim B := by
    refine Topology.IsInducing.topologicalKrullDim_le
      (f := fun x : A => (⟨D.ι.base x.1, x.2⟩ : ↥B)) ?_
    refine Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val ?_
    exact D.ι.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
  have hdimS : topologicalKrullDim S ≤ (j : WithBot ℕ∞) :=
    ((topologicalKrullDim_closure_image_le k (projection k V Wp)
      (D.ι ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k ↥Wp)
      (projection_comp_toSpec k V Wp) hAc).trans hdimA).trans hdimB
  have hSne : S ≠ Set.univ := by
    intro hS'
    rw [hS', IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph,
      topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (n := j + 1)
        (by rw [hWrank, hj])] at hdimS
    have : j + 1 ≤ j := by exact_mod_cast hdimS
    lia
  obtain ⟨g, hg, hgS⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k ↥Wp isClosed_closure hSne
  obtain ⟨f, hfg⟩ := LinearMap.dualMap_surjective_of_injective Wp.injective_subtype g
  have hcomp : f ∘ₗ Wp.subtype = g := by
    refine LinearMap.ext fun w => ?_
    rw [← hfg, LinearMap.dualMap_apply]
    rfl
  subst hcomp
  have hf : f ≠ 0 := fun h0 => hg (by rw [h0, LinearMap.zero_comp])
  have hqD : linearFunctionalPoint k V f hf ∈
      ((D : (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_mapDomain_subtype]
    intro hmem
    refine hg (LinearMap.ext fun w => ?_)
    have hw := (mem_linearSubspace_iff k V Wp _).mp hmem w.2
    rw [pointSubmodule_linearFunctionalPoint] at hw
    exact LinearMap.mem_ker.mp hw
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : D.toScheme,
      (y₀.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf :=
    ⟨⟨linearFunctionalPoint k V f hf, hqD⟩, rfl⟩
  refine ⟨D.ι.base '' ((projection k V Wp).base ⁻¹' Sᶜ),
    D.ι.isOpenEmbedding.isOpenMap _ (isClosed_closure.isOpen_compl.preimage (by fun_prop)),
    ⟨_, y₀, ?_, rfl⟩, ?_⟩
  · show projection k V Wp y₀ ∉ S
    rw [projection_eq_linearFunctionalPoint k V Wp y₀ f hf hg hy₀]
    exact hgS
  rintro q ⟨y, hyS, rfl⟩ hyc
  have hymem : (y.val : projectiveSpaceOfModule k V) ∈
      ((D : (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := y.2
  rw [hDp] at hymem
  obtain ⟨f', hf', hfy⟩ := exists_eq_linearFunctionalPoint k V y.val hyc
  have hgne : f' ∘ₗ Wp.subtype ≠ 0 := by
    intro h0
    refine hymem ?_
    have hle : Wp ≤ pointSubmodule k V (y.val : projectiveSpaceOfModule k V) := by
      rw [hfy, pointSubmodule_linearFunctionalPoint]
      intro w hw
      exact LinearMap.mem_ker.mpr (congrArg (fun g : Module.Dual k ↥Wp => g ⟨w, hw⟩) h0)
    have hmem := (mem_linearSubspace_iff k V Wp _).mpr hle
    rwa [hWp, linearSubspace_pointSubmodule k V p hp, Set.mem_singleton_iff] at hmem
  have hyproj : projection k V Wp y =
      linearFunctionalPoint k ↥Wp (f' ∘ₗ Wp.subtype) hgne :=
    projection_eq_linearFunctionalPoint k V Wp y f' hf' hgne hfy
  refine ⟨lineSubmodule k V p y.val, finrank_quotient_lineSubmodule k V hp hyc (Ne.symm hymem),
    left_mem_linearSubspace_lineSubmodule k V _ _,
    right_mem_linearSubspace_lineSubmodule k V _ _, ?_⟩
  rintro z ⟨hzL, hzB⟩
  by_contra hzp
  have hzD : z ∈ ((D : (projectiveSpaceOfModule k V).Opens) :
      Set (projectiveSpaceOfModule k V)) := by
    rwa [hDp]
  obtain ⟨w, hw⟩ : ∃ w : D.toScheme, (w.val : projectiveSpaceOfModule k V) = z := ⟨⟨z, hzD⟩, rfl⟩
  refine hyS (subset_closure ⟨w, by
    show (w.val : projectiveSpaceOfModule k V) ∈ B
    rwa [hw], ?_⟩)
  show projection k V Wp w = projection k V Wp y
  rw [hyproj]
  refine projection_eq_linearFunctionalPoint_of_mem k V Wp w _ hgne
    (lineSubmodule k V p y.val) (fun v hv => ?_) (by rwa [hw])
  refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
  rw [hfy, pointSubmodule_linearFunctionalPoint]
  exact LinearMap.mem_ker.mpr hv

end AlgebraicGeometry.ProjectiveSpaceOfModule

end

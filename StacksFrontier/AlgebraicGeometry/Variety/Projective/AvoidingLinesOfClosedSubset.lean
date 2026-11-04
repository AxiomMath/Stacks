module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
import all StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension

/-!
# Lines through a point avoiding a closed subset of codimension two

Let `V` be a finite-dimensional vector space of dimension at least three over an algebraically
closed field `k`, let `B ⊆ 𝐏(V)` be a closed subset every point of which has closure of
codimension at least two, and let `p` be a closed point of `𝐏(V)` outside `B`. Then some
projective line through `p` misses `B`, and the closed points of some nonempty open subset of
`𝐏(V)` all lie on such lines.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isNoetherian_projectiveSpaceOfModule` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.noetherianSpace_opens`: the projective space of a
  nonzero finite-dimensional vector space is a Noetherian scheme, and each of its open
  subschemes has a Noetherian underlying space.
* `le_codimension_closureSingleton_of_mem`: the closure of a point of an irreducible closed
  subset has at least the codimension of that subset.
* `topologicalKrullDim_le_of_forall_le_codimension`: a closed subset of a quasi-sober space all
  of whose points have codimension at least `e` has dimension at most `dim X - e`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.three_le_finrank_of_two_le_codimension`: a
  projective space carrying an irreducible closed subset of codimension at least two has
  `dim_k V ≥ 3`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_line_disjoint_of_forall_codimension_ge_two`
  and, in the same namespace,
  `exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two`: both conclusions for
  a closed subset `B` of codimension at least two.

## References

* [Stacks Project, Tag 0B2T](https://stacks.math.columbia.edu/tag/0B2T)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 0CYQ](https://stacks.math.columbia.edu/tag/0CYQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared

/-- **The closure of a point of an irreducible closed subset has at least the codimension of
that subset.** -/
public theorem le_codimension_closureSingleton_of_mem {X : Type*} [TopologicalSpace X]
    {e : ℕ∞} (B : IrreducibleCloseds X) (hB : e ≤ codimension B) {x : X}
    (hx : x ∈ (B : Set X)) :
    e ≤ codimension (IrreducibleCloseds.closureSingleton x) := by
  refine hB.trans ?_
  rw [codimension_eq_coheight, codimension_eq_coheight]
  exact Order.coheight_anti (SetLike.coe_subset_coe.mp
    (B.isClosed'.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)))

/-- **A closed subset all of whose points have codimension at least `e` has dimension at most
`dim X - e`.** Here `X` is quasi-sober and the codimension of a point is that of its closure. -/
public theorem topologicalKrullDim_le_of_forall_le_codimension {X : Type*} [TopologicalSpace X]
    [QuasiSober X] {B : Set X} (hB : IsClosed B) {m e : ℕ}
    (hX : topologicalKrullDim X ≤ ((m + e : ℕ) : WithBot ℕ∞))
    (hcodim : ∀ x ∈ B, (e : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    topologicalKrullDim B ≤ (m : WithBot ℕ∞) := by
  refine topologicalKrullDim_le_of_forall_closure hB fun x hx ↦ ?_
  have hcc := topologicalKrullDim_add_codimension_le (IrreducibleCloseds.closureSingleton x)
  rw [IrreducibleCloseds.coe_closureSingleton] at hcc
  have h : topologicalKrullDim (closure ({x} : Set X)) + ((e : ℕ) : WithBot ℕ∞) ≤
      ((m + e : ℕ) : WithBot ℕ∞) :=
    le_trans (add_le_add le_rfl (by simpa using WithBot.coe_le_coe.mpr (hcodim x hx)))
      (hcc.trans hX)
  rw [Nat.cast_add] at h
  exact ENat.WithBot.add_le_add_natCast_right_iff.mp h

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

open Stacks.AlgebraicGeometry.ProjTwistChain

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **The projective space of a nonzero finite-dimensional vector space is a Noetherian
scheme.** -/
public instance isNoetherian_projectiveSpaceOfModule [FiniteDimensional k V] [Nontrivial V] :
    IsNoetherian (projectiveSpaceOfModule k V) :=
  haveI : IsLocallyNoetherian (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec k V)
  haveI : CompactSpace (projectiveSpaceOfModule k V) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec k V)
  {}

/-- **An open subscheme of the projective space of a nonzero finite-dimensional vector space has
a Noetherian underlying space.** -/
public instance noetherianSpace_opens [FiniteDimensional k V] [Nontrivial V]
    (U : (projectiveSpaceOfModule k V).Opens) : NoetherianSpace U.toScheme :=
  U.ι.isOpenEmbedding.isInducing.noetherianSpace

/-- The hyperplane of a closed point of `𝐏(V)` has dimension at least two once `V` has dimension
at least three. -/
private theorem two_le_finrank_pointSubmodule_of_three_le_finrank [IsAlgClosed k]
    [FiniteDimensional k V] (hV : 3 ≤ Module.finrank k V) (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    2 ≤ Module.finrank k ↥(pointSubmodule k V p) := by
  have h := finrank_pointSubmodule_add_one k V p hp
  omega

/-- The hyperplane of a closed point of `𝐏(V)` is nontrivial once `V` has dimension at least
three. -/
private theorem nontrivial_pointSubmodule_of_three_le_finrank [IsAlgClosed k]
    [FiniteDimensional k V] (hV : 3 ≤ Module.finrank k V) (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V))) :
    Nontrivial ↥(pointSubmodule k V p) :=
  Module.nontrivial_of_finrank_pos (R := k)
    (lt_of_lt_of_le Nat.zero_lt_two
      (two_le_finrank_pointSubmodule_of_three_le_finrank k V hV p hp))

/-- The image of a closed set `B` not containing `p` under the projection away from `p` is
closed. -/
private theorem isClosed_image_projection_pointSubmodule [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (hV : 3 ≤ Module.finrank k V)
    (B : Set (projectiveSpaceOfModule k V)) (hB : IsClosed B)
    (p : projectiveSpaceOfModule k V) (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ B) :
    IsClosed ((projection k V (pointSubmodule k V p)).base ''
      ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' B)) := by
  have hWnt := nontrivial_pointSubmodule_of_three_le_finrank k V hV p hp
  exact isClosed_image_projection k V (pointSubmodule k V p) hB (by
    rw [linearSubspace_pointSubmodule k V p hp]
    exact Set.disjoint_singleton_right.mpr hpB)

/-- **A projective space carrying an irreducible closed subset of codimension at least two has
dimension at least two**, that is `dim_k V ≥ 3`. -/
public theorem three_le_finrank_of_two_le_codimension [FiniteDimensional k V] [Nontrivial V]
    (B : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hcodim : (2 : ℕ∞) ≤ codimension B) :
    3 ≤ Module.finrank k V := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hB0 : (0 : WithBot ℕ∞) ≤
      topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) := by
    have : Nonempty ↥(B : Set (projectiveSpaceOfModule k V)) :=
      B.isIrreducible'.nonempty.to_subtype
    have : Nonempty (IrreducibleCloseds ↥(B : Set (projectiveSpaceOfModule k V))) :=
      ⟨IrreducibleCloseds.closureSingleton (Classical.arbitrary _)⟩
    exact Order.krullDim_nonneg
  have hle : topologicalKrullDim (B : Set (projectiveSpaceOfModule k V)) + 2 ≤
      (n : WithBot ℕ∞) :=
    le_trans (add_le_add le_rfl (by simpa using WithBot.coe_le_coe.mpr hcodim))
      (topologicalKrullDim_add_codimension_le_projectiveSpaceOfModule hn B)
  have hn2 : 2 ≤ n := by
    exact_mod_cast ((zero_add (2 : WithBot ℕ∞)).symm.trans_le (add_le_add hB0 le_rfl)).trans hle
  omega

/-- **The image of a closed set `B` of codimension at least two under the projection away from `p`
is not all of `𝐏(W_p)`.** -/
private theorem image_projection_ne_univ_of_forall_codimension [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V]
    (hV : 3 ≤ Module.finrank k V) (B : Set (projectiveSpaceOfModule k V)) (hB : IsClosed B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ B) :
    (projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' B) ≠ Set.univ := by
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank k V = n + 1 :=
    ⟨Module.finrank k V - 1, by have := Module.finrank_pos (R := k) (M := V); omega⟩
  have hWrank : Module.finrank k ↥(pointSubmodule k V p) = n := by
    have h := finrank_pointSubmodule_add_one k V p hp
    omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨j, hj⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have hle : topologicalKrullDim B + 2 ≤ (n : WithBot ℕ∞) := by
    have hdimB : topologicalKrullDim B ≤ (j : WithBot ℕ∞) := by
      refine topologicalKrullDim_le_of_forall_le_codimension (e := 2) hB ?_
        (fun x hx ↦ mod_cast hcodim x hx)
      rw [topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hn, hj]
    refine le_trans (add_le_add hdimB (le_refl (2 : WithBot ℕ∞))) ?_
    rw [hj]
    push_cast
    exact le_rfl
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : Nontrivial ↥(pointSubmodule k V p) :=
    Module.nontrivial_of_finrank_pos (R := k) (by omega)
  intro hcontra
  have hSdim := topologicalKrullDim_image_projection_le k V (pointSubmodule k V p) hB (by
      rw [linearSubspace_pointSubmodule k V p hp]
      exact Set.disjoint_singleton_right.mpr hpB)
  rw [hcontra] at hSdim
  have huniv : topologicalKrullDim
      (Set.univ : Set (projectiveSpaceOfModule k ↥(pointSubmodule k V p))) =
        (m : WithBot ℕ∞) := by
    rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph]
    exact topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq (by rw [hWrank, hm])
  rw [huniv] at hSdim
  have hfin : (m : WithBot ℕ∞) + 2 ≤ (n : WithBot ℕ∞) :=
    le_trans (add_le_add hSdim (le_refl (2 : WithBot ℕ∞))) hle
  rw [hm] at hfin
  have hbad : m + 2 ≤ m + 1 := by exact_mod_cast hfin
  omega

/-- **The line joining `p` to a closed point `y` misses `B` when no point of `B` projects onto the
projection of `y`.** -/
private theorem lineSubmodule_spec_of_isClosed [IsAlgClosed k] [FiniteDimensional k V]
    (B : Set (projectiveSpaceOfModule k V)) (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ B)
    (y : (projectionDomain k V (pointSubmodule k V p)).toScheme)
    (hyc : IsClosed ({(y.val : projectiveSpaceOfModule k V)} :
      Set (projectiveSpaceOfModule k V)))
    (hyB : ∀ z : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      (z.val : projectiveSpaceOfModule k V) ∈ B →
      projection k V (pointSubmodule k V p) z ≠ projection k V (pointSubmodule k V p) y) :
    Module.finrank k (V ⧸ lineSubmodule k V p y.val) = 2 ∧
      p ∈ linearSubspace k V (lineSubmodule k V p y.val) ∧
      (y.val : projectiveSpaceOfModule k V) ∈
        linearSubspace k V (lineSubmodule k V p y.val) ∧
      Disjoint (linearSubspace k V (lineSubmodule k V p y.val)) B := by
  have hDp : ((projectionDomain k V (pointSubmodule k V p) :
      (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) = {p}ᶜ :=
    coe_mapDomain_pointSubmodule k V p hp
  have hymem : (y.val : projectiveSpaceOfModule k V) ∈
      ((projectionDomain k V (pointSubmodule k V p) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := y.2
  rw [hDp] at hymem
  obtain ⟨f, hf, hfy⟩ := exists_eq_linearFunctionalPoint k V y.val hyc
  have hgne : f ∘ₗ (pointSubmodule k V p).subtype ≠ 0 := by
    intro h0
    refine hymem ?_
    have hle : pointSubmodule k V p ≤
        pointSubmodule k V (y.val : projectiveSpaceOfModule k V) := by
      rw [hfy, pointSubmodule_linearFunctionalPoint]
      intro w hw
      exact LinearMap.mem_ker.mpr (congrArg (fun g : Module.Dual k ↥(pointSubmodule k V p) ↦
        g ⟨w, hw⟩) h0)
    have hmem := (mem_linearSubspace_iff k V (pointSubmodule k V p) _).mpr hle
    rwa [linearSubspace_pointSubmodule k V p hp, Set.mem_singleton_iff] at hmem
  have hyproj : projection k V (pointSubmodule k V p) y =
      linearFunctionalPoint k ↥(pointSubmodule k V p)
        (f ∘ₗ (pointSubmodule k V p).subtype) hgne :=
    projection_eq_linearFunctionalPoint k V (pointSubmodule k V p) y f hf hgne hfy
  refine ⟨finrank_quotient_lineSubmodule k V hp hyc (Ne.symm hymem),
    left_mem_linearSubspace_lineSubmodule k V _ _,
    right_mem_linearSubspace_lineSubmodule k V _ _, Set.disjoint_left.mpr fun z hzL hzB ↦ ?_⟩
  have hzp : z ≠ p := fun h0 ↦ hpB (h0 ▸ hzB)
  have hzD : z ∈ ((projectionDomain k V (pointSubmodule k V p) :
      (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rwa [hDp]
  obtain ⟨w, hw⟩ : ∃ w : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      (w.val : projectiveSpaceOfModule k V) = z := ⟨⟨z, hzD⟩, rfl⟩
  refine hyB w (by rw [hw]; exact hzB) ?_
  rw [hyproj]
  refine projection_eq_linearFunctionalPoint_of_mem k V (pointSubmodule k V p) w _ hgne
    (lineSubmodule k V p y.val) (fun v hv ↦ ?_) (by rw [hw]; exact hzL)
  refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
  rw [hfy, pointSubmodule_linearFunctionalPoint]
  exact LinearMap.mem_ker.mpr hv

/-- **A closed point of `𝐏(V)` off `p` whose projection avoids the image of `B`.** -/
private theorem exists_closedPoint_projection_notMem_image_of_forall_codimension [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] (hV : 3 ≤ Module.finrank k V)
    (B : Set (projectiveSpaceOfModule k V)) (hB : IsClosed B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ B) :
    ∃ y : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      IsClosed ({(y.val : projectiveSpaceOfModule k V)} :
        Set (projectiveSpaceOfModule k V)) ∧
      projection k V (pointSubmodule k V p) y ∉
        (projection k V (pointSubmodule k V p)).base ''
          ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' B) := by
  have hWnt := nontrivial_pointSubmodule_of_three_le_finrank k V hV p hp
  have hSclosed := isClosed_image_projection_pointSubmodule k V hV B hB p hp hpB
  obtain ⟨g, hg, hgS⟩ := exists_linearFunctionalPoint_notMem_of_ne_univ k
    ↥(pointSubmodule k V p) hSclosed
    (image_projection_ne_univ_of_forall_codimension k V hV B hB hcodim p hp hpB)
  obtain ⟨f, hfg⟩ := LinearMap.dualMap_surjective_of_injective
    (pointSubmodule k V p).injective_subtype g
  have hcomp : f ∘ₗ (pointSubmodule k V p).subtype = g := by
    refine LinearMap.ext fun w ↦ ?_
    rw [← hfg, LinearMap.dualMap_apply]
    rfl
  subst hcomp
  have hf : f ≠ 0 := fun h0 ↦ hg (by rw [h0, LinearMap.zero_comp])
  have hqD : linearFunctionalPoint k V f hf ∈
      ((projectionDomain k V (pointSubmodule k V p) :
        (projectiveSpaceOfModule k V).Opens) : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_mapDomain_subtype]
    intro hmem
    refine hg (LinearMap.ext fun w ↦ ?_)
    have hw := (mem_linearSubspace_iff k V (pointSubmodule k V p) _).mp hmem w.2
    rw [pointSubmodule_linearFunctionalPoint] at hw
    exact LinearMap.mem_ker.mp hw
  obtain ⟨y, hy⟩ : ∃ y : (projectionDomain k V (pointSubmodule k V p)).toScheme,
      (y.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf :=
    ⟨⟨linearFunctionalPoint k V f hf, hqD⟩, rfl⟩
  refine ⟨y, by rw [hy]; exact linearFunctionalPoint_isClosed k V f hf, ?_⟩
  rwa [projection_eq_linearFunctionalPoint k V (pointSubmodule k V p) y f hf hg hy]

/-- **Existence of an avoiding line, for a closed subset of codimension at least two.** Let `B`
be a closed subset of the projective space of a finite-dimensional vector space of dimension at
least three over an algebraically closed field, every point of which has codimension at least
two — equivalently, since `𝐏(V)` is sober, every irreducible component of `B` has codimension at
least two. Let `p` be a closed point outside `B`. Then some projective line through `p` is
disjoint from `B`. -/
public theorem exists_line_disjoint_of_forall_codimension_ge_two [IsAlgClosed k]
    [FiniteDimensional k V] [Nontrivial V] (hV : 3 ≤ Module.finrank k V)
    (B : Set (projectiveSpaceOfModule k V)) (hB : IsClosed B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ B) :
    ∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧
      p ∈ linearSubspace k V W ∧ Disjoint (linearSubspace k V W) B := by
  obtain ⟨y, hyc, hyS⟩ :=
    exists_closedPoint_projection_notMem_image_of_forall_codimension k V hV B hB hcodim p hp hpB
  obtain ⟨h2, hpL, -, hdisj⟩ := lineSubmodule_spec_of_isClosed k V B p hp hpB y hyc
    fun z hzB heq ↦ hyS ⟨z, hzB, heq⟩
  exact ⟨lineSubmodule k V p y.val, h2, hpL, hdisj⟩

/-- **An open subset swept out by avoiding lines, for a closed subset of codimension at least
two.** With `B` and `p` as in
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_line_disjoint_of_forall_codimension_ge_two`
there is a nonempty open subset of `𝐏(V)` each of whose closed points lies on a projective line
through `p` disjoint from `B`. -/
public theorem exists_isOpen_subset_union_lines_disjoint_of_forall_codimension_ge_two
    [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (hV : 3 ≤ Module.finrank k V)
    (B : Set (projectiveSpaceOfModule k V)) (hB : IsClosed B)
    (hcodim : ∀ x ∈ B, (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (p : projectiveSpaceOfModule k V)
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hpB : p ∉ B) :
    ∃ U : Set (projectiveSpaceOfModule k V), IsOpen U ∧ U.Nonempty ∧
      ∀ q ∈ U, IsClosed ({q} : Set (projectiveSpaceOfModule k V)) →
        ∃ W : Submodule k V, Module.finrank k (V ⧸ W) = 2 ∧
          p ∈ linearSubspace k V W ∧ q ∈ linearSubspace k V W ∧
          Disjoint (linearSubspace k V W) B := by
  have hSclosed := isClosed_image_projection_pointSubmodule k V hV B hB p hp hpB
  obtain ⟨y, hyc, hyS⟩ :=
    exists_closedPoint_projection_notMem_image_of_forall_codimension k V hV B hB hcodim p hp hpB
  refine ⟨(projectionDomain k V (pointSubmodule k V p)).ι.base ''
    ((projection k V (pointSubmodule k V p)).base ⁻¹'
      ((projection k V (pointSubmodule k V p)).base ''
        ((projectionDomain k V (pointSubmodule k V p)).ι.base ⁻¹' B))ᶜ),
    (projectionDomain k V (pointSubmodule k V p)).ι.isOpenEmbedding.isOpenMap _
      (hSclosed.isOpen_compl.preimage (by fun_prop)), ⟨y.val, y, hyS, rfl⟩, ?_⟩
  rintro q ⟨z, hzS, rfl⟩ hqc
  obtain ⟨h2, hpL, hqL, hdisj⟩ := lineSubmodule_spec_of_isClosed k V B p hp hpB z hqc
    fun w hwB heq ↦ hzS ⟨w, hwB, heq⟩
  exact ⟨lineSubmodule k V p z.val, h2, hpL, hqL, hdisj⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end

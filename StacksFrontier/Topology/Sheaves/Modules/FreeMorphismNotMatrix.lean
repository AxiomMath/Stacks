module

public import Mathlib.Topology.Sheaves.CommRingCat
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeAssociatedSheafBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection

/-!
# A morphism of free sheaves of modules not given by a matrix

Countably many copies of the real line, glued at their origins, carry the sheaf of continuous
real functions. The free sheaves of modules on `ℕ` and on `ℕ × ℕ` over this ringed space carry a
morphism whose value on a basis section is, on every neighbourhood of the common origin,
supported on infinitely many target basis sections. No homomorphism of the free modules of
global sections over such a neighbourhood induces it.

## Main definitions

* `Stacks.Bouquet.Point` is the set of points of the countable bouquet of lines: a common origin
  together with the nonzero points of countably many real lines.
* `Stacks.Bouquet.topology` is the bouquet topology, in which a neighbourhood of the origin
  contains an interval of one radius on every branch.

## Main results

* `Stacks.Bouquet.exists_freeSheafMorphism_not_locally_finite` is the second half of
  **Tag 01BL**: the counterexample, a morphism of sheaves associated to free modules which on no
  neighbourhood of the origin is a finite combination of target basis sections.

## Implementation notes

The source and target of the counterexample are the sheaves associated to the free modules
`ℕ →₀ Γ(X, 𝒪_X)` and `(ℕ × ℕ) →₀ Γ(X, 𝒪_X)`, identified with the free sheaves of modules by
`Stacks.AssociatedSheaf.exists_free_iso_associatedSheaf_freeModule`, which is the first half of
the tag. The morphism is built on the free sheaves, where a map out of a coproduct is a family of
maps out of the structure sheaf, each given by a global section of the target: the `j`-th of them
is the section `columnSection j` glued from the cutoff function `cutoff ((j + 1) * ·)` on branch
`i`, which vanishes on the uniform neighbourhood of radius `1 / (j + 1)` and so glues with zero
across the origin.

Non-finiteness at the origin is read off by the coordinate projections `freeProjection`: a
neighbourhood `U` of the origin contains the uniform neighbourhood of some radius `1 / (n + 1)`,
and then the `(4 * (n + 1))`-th basis section is sent to a section whose `(4 * (n + 1), i)`-th
coordinate is nonzero for every branch `i`, while a finite combination of basis sections has
only finitely many branches among its coordinates.

The universes are those of the source statement, which fixes them all at `0`; at equal universes
the free sheaf and its canonical inclusion are `SheafOfModules.free` and
`SheafOfModules.ιFree`, and the structure sheaf is `SheafOfModules.unit`, with no universe
lift, so the library names are used directly. The two sheafification hypotheses of
`SheafOfModules.free` are supplied by `Stacks.AssociatedSheaf.hasModuleSheafify` and
`Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective`, theorems about every ringed
space, declared local instances for this file.

## References

* [Stacks Project, Tag 01BL](https://stacks.math.columbia.edu/tag/01BL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.AssociatedSheaf

namespace Stacks.Bouquet

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective


/-- A common origin and the nonzero points on countably many copies of the real line. -/
public abbrev Point := Unit ⊕ (ℕ × {x : ℝ // x ≠ 0})

/-- The common origin of the bouquet. -/
public def origin : Point := Sum.inl ()

/-- The point with coordinate `x` on branch `i`, away from the common origin. -/
public def branch (i : ℕ) (x : {x : ℝ // x ≠ 0}) : Point := Sum.inr (i, x)

/-- A neighborhood of the origin of uniform radius `1/(n+1)` on all branches. -/
public def uniformNeighborhood (n : ℕ) : Set Point :=
  {p | p = origin ∨ ∃ i x, p = branch i x ∧ |(x : ℝ)| < (1 : ℝ) / (n + 1)}

/-- An open set supported away from zero on one branch. -/
public def branchOpen (i : ℕ) (V : Set ℝ) : Set Point :=
  {p | ∃ x : {x : ℝ // x ≠ 0}, p = branch i x ∧ (x : ℝ) ∈ V}

/-- The bouquet topology: away from the origin it is the ordinary real-line
topology, while neighborhoods of the origin contain a uniform interval on
every branch. -/
@[instance_reducible] public def topology : TopologicalSpace Point :=
  TopologicalSpace.generateFrom
    ({s | ∃ n : ℕ, s = uniformNeighborhood n} ∪
      {s | ∃ (i : ℕ) (V : Set ℝ), IsOpen V ∧ (0 : ℝ) ∉ V ∧ s = branchOpen i V})

/-- The bouquet topology `Stacks.Bouquet.topology`, as the instance on `Point`. -/
public instance : TopologicalSpace Point := topology

private lemma uniformNeighborhood_antitone : Antitone uniformNeighborhood := by
  intro n m h p hp
  rcases hp with hp | ⟨i, x, rfl, hx⟩
  · exact Or.inl hp
  · exact Or.inr ⟨i, x, rfl, hx.trans_le (one_div_le_one_div_of_le
      (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1))⟩

private lemma exists_uniformNeighborhood_subset {s : Set Point}
    (hs : IsOpen s) (h : origin ∈ s) : ∃ n, uniformNeighborhood n ⊆ s := by
  induction hs with
  | basic s hs =>
      rcases hs with ⟨n, rfl⟩ | ⟨i, V, hV, h0, rfl⟩
      · exact ⟨n, Set.Subset.rfl⟩
      · obtain ⟨_, ⟨⟩, _⟩ := h
  | univ => exact ⟨0, Set.subset_univ _⟩
  | inter s t hs ht ihs iht =>
      obtain ⟨n, hn⟩ := ihs h.1
      obtain ⟨m, hm⟩ := iht h.2
      exact ⟨max n m, fun p hp =>
        ⟨hn (uniformNeighborhood_antitone (le_max_left _ _) hp),
         hm (uniformNeighborhood_antitone (le_max_right _ _) hp)⟩⟩
  | sUnion S hS ih =>
      obtain ⟨s, hs, hp⟩ := h
      obtain ⟨n, hn⟩ := ih s hs hp
      exact ⟨n, fun p hp => ⟨s, hs, hn hp⟩⟩

private lemma isOpen_uniformNeighborhood (n : ℕ) : IsOpen (uniformNeighborhood n) :=
  TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨n, rfl⟩)

private lemma isOpen_branchOpen (i : ℕ) {V : Set ℝ} (hV : IsOpen V) :
    IsOpen (branchOpen i V) := by
  have he : branchOpen i V = branchOpen i (V \ {0}) := by
    ext p
    simp only [branchOpen, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    exact ⟨fun ⟨x, h, hx⟩ => ⟨x, h, hx, x.property⟩, fun ⟨x, h, hx, _⟩ => ⟨x, h, hx⟩⟩
  rw [he]
  exact TopologicalSpace.isOpen_generateFrom_of_mem
    (Or.inr ⟨i, V \ {0}, hV.sdiff isClosed_singleton, by simp, rfl⟩)

private lemma continuous_of_uniform_zero (g : Point → ℝ) (n : ℕ)
    (hzero : ∀ p ∈ uniformNeighborhood n, g p = 0)
    (f : ℕ → ℝ → ℝ) (hf : ∀ i, Continuous (f i))
    (hbranch : ∀ i x, g (branch i x) = f i x) : Continuous g := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  rcases p with u | ⟨i, x⟩
  · cases u
    change g origin ∈ V at hp
    refine ⟨uniformNeighborhood n, ?_, isOpen_uniformNeighborhood n, Or.inl rfl⟩
    intro p hp'
    show g p ∈ V
    rw [hzero p hp']
    simpa only [Set.mem_preimage, hzero origin (Or.inl rfl)] using hp
  · refine ⟨branchOpen i ((f i) ⁻¹' V), ?_,
      isOpen_branchOpen i (hV.preimage (hf i)), ?_⟩
    · rintro p ⟨y, rfl, hy⟩
      simpa only [Set.mem_preimage, hbranch] using hy
    · change g (branch i x) ∈ V at hp
      exact ⟨x, rfl, by simpa only [Set.mem_preimage, ← hbranch] using hp⟩

private noncomputable def cutoff (x : ℝ) : ℝ := min 1 (max 0 (|x| - 1))

private lemma continuous_cutoff : Continuous cutoff :=
  continuous_const.min (continuous_const.max (continuous_abs.sub continuous_const))

private lemma cutoff_zero {x : ℝ} (hx : |x| < 1) : cutoff x = 0 := by
  simp [cutoff, max_eq_left (by linarith : |x| - 1 ≤ 0)]

private lemma cutoff_one {x : ℝ} (hx : 2 < |x|) : cutoff x = 1 := by
  simp [cutoff, max_eq_right (by linarith : 0 ≤ |x| - 1),
    min_eq_left (by linarith : 1 ≤ |x| - 1)]

private noncomputable def columnFunction (j : ℕ) : Point → ℝ
  | Sum.inl _ => 0
  | Sum.inr p => cutoff ((j + 1) * (p.2 : ℝ))

private lemma columnFunction_zero (j : ℕ) (p : Point)
    (hp : p ∈ uniformNeighborhood j) : columnFunction j p = 0 := by
  rcases hp with rfl | ⟨i, x, rfl, hx⟩
  · rfl
  · apply cutoff_zero
    have hj : (0 : ℝ) < j + 1 := by positivity
    rw [abs_mul, abs_of_pos hj]
    have := (lt_div_iff₀ hj).mp hx
    nlinarith

private lemma continuous_columnFunction (j : ℕ) : Continuous (columnFunction j) :=
  continuous_of_uniform_zero _ j (columnFunction_zero j) (fun _ x => cutoff ((j + 1) * x))
    (fun _ => continuous_cutoff.comp (continuous_const.mul continuous_id)) fun _ _ => rfl

private noncomputable abbrev ringedSpace : RingedSpace.{0, 0} where
  carrier := TopCat.of Point
  presheaf := TopCat.presheafToTopCommRing (X := TopCat.of Point) (TopCommRingCat.of ℝ)
  IsSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat) _).mpr
    (TopCat.sheafToTop (X := TopCat.of Point) (TopCat.of ℝ)).property

private lemma restrict_basisSection (X : RingedSpace.{0, 0})
    {I : Type} (i : I) {U V : Opens X} (h : V ≤ U) :
    (SheafOfModules.free (R := structureSheafRing X) I).val.map (homOfLE h).op
        (basisSection X U i) =
      basisSection X V i := by
  have hone := PresheafOfModules.unit_map_one (R := (structureSheafRing X).obj) (homOfLE h).op
  have hnat := PresheafOfModules.naturality_apply
    (SheafOfModules.ιFree (R := structureSheafRing X) (I := I) i).val (homOfLE h).op
    (1 : (structureSheafRing X).obj.obj (op U))
  exact hnat.symm.trans (congrArg
    (fun z => (SheafOfModules.ιFree (R := structureSheafRing X) (I := I) i).val.app (op V) z) hone)

private noncomputable def homOfGlobalSection (X : RingedSpace.{0, 0})
    (F : SheafOfModules.{0} (structureSheafRing X)) (s : F.val.obj (op ⊤)) :
    SheafOfModules.unit (structureSheafRing X) ⟶ F :=
  F.unitHomEquiv.symm (ofTop X F s)

private lemma homOfGlobalSection_one (X : RingedSpace.{0, 0})
    (F : SheafOfModules.{0} (structureSheafRing X)) (s : F.val.obj (op ⊤)) (U : Opens X) :
    (homOfGlobalSection X F s).val.app (op U) ((1 : (structureSheafRing X).obj.obj (op U))) =
      F.val.map (homOfLE le_top).op s := by
  show (F.unitHomEquiv (homOfGlobalSection X F s)).val (op U) = _
  rw [homOfGlobalSection, Equiv.apply_symm_apply]
  rfl

private noncomputable def unitSection (X : RingedSpace.{0, 0}) (U : Opens X) :
    (SheafOfModules.unit (structureSheafRing X)).val.obj (op U) :=
  (1 : (structureSheafRing X).obj.obj (op U))

private lemma freeProjection_ι (X : RingedSpace.{0, 0}) {I : Type} [DecidableEq I] (i j : I) :
    SheafOfModules.ιFree (R := structureSheafRing X) j ≫
        SheafOfModules.freeProjection (R := structureSheafRing X) i =
      if i = j then 𝟙 _ else 0 := by
  rw [SheafOfModules.ιFree_comp_freeProjection]
  exact if_congr eq_comm rfl rfl

private lemma freeProjection_basis (X : RingedSpace.{0, 0}) {I : Type} [DecidableEq I] (i j : I)
    (U : Opens X) :
    (SheafOfModules.freeProjection (R := structureSheafRing X) i).val.app (op U)
        (basisSection X U j) =
      if i = j then unitSection X U else 0 := by
  classical
  have h := congrArg (fun f : SheafOfModules.unit (structureSheafRing X) ⟶
      SheafOfModules.unit (structureSheafRing X) => f.val.app (op U) (unitSection X U))
    (freeProjection_ι X i j)
  by_cases hij : i = j
  · simp only [ite_eq_left hij] at h ⊢
    exact h
  · simp only [ite_eq_right hij] at h ⊢
    exact h

private noncomputable def columnScalarRaw (j : ℕ) (U : Opens ringedSpace) :
    ringedSpace.presheaf.obj (op U) :=
  TopCat.ofHom ⟨fun p => columnFunction j p.1,
    (continuous_columnFunction j).comp continuous_subtype_val⟩

private noncomputable abbrev columnScalar (j : ℕ) (U : Opens ringedSpace) :
    (structureSheafRing ringedSpace).obj.obj (op U) := columnScalarRaw j U

private lemma restrict_columnScalar (j : ℕ) {U V : Opens ringedSpace} (h : V ≤ U) :
    (structureSheafRing ringedSpace).obj.map (homOfLE h).op (columnScalar j U) =
      columnScalar j V := rfl

private lemma columnScalar_zero (j : ℕ) (U : Opens ringedSpace)
    (hU : ∀ p : ringedSpace, p ∈ U → p ∈ uniformNeighborhood j) : columnScalar j U = 0 := by
  show columnScalarRaw j U = 0
  exact TopCat.hom_ext (ContinuousMap.ext fun p => columnFunction_zero j p.1 (hU p.1 p.2))

private noncomputable def columnCover (j : ℕ) : Option ℕ → Opens ringedSpace
  | none => ⟨uniformNeighborhood j, isOpen_uniformNeighborhood j⟩
  | some i => ⟨branchOpen i Set.univ, isOpen_branchOpen i isOpen_univ⟩

private lemma columnCover_covers (j : ℕ) :
    (⊤ : Opens ringedSpace) ≤ ⨆ i, columnCover j i := by
  intro p _
  rw [Opens.mem_iSup]
  rcases p with ⟨⟩ | ⟨i, x⟩
  · exact ⟨none, Or.inl rfl⟩
  · exact ⟨some i, x, rfl, Set.mem_univ _⟩

private noncomputable def columnLocalSection (j : ℕ) (a : Option ℕ) :
    (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.obj
      (op (columnCover j a)) :=
  match a with
  | none => 0
  | some i => columnScalar j (columnCover j (some i)) •
      basisSection ringedSpace (columnCover j (some i)) (j, i)

private lemma restrict_columnLocalSection (j i : ℕ) {U : Opens ringedSpace}
    (f : op (columnCover j (some i)) ⟶ op U) :
    (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.presheaf.map f
      (columnLocalSection j (some i)) =
      columnScalar j U • basisSection ringedSpace U (j, i) := by
  have h : U ≤ columnCover j (some i) := leOfHom f.unop
  obtain rfl : f = (homOfLE h).op := Subsingleton.elim _ _
  show (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.map (homOfLE h).op
    (columnLocalSection j (some i)) = _
  unfold columnLocalSection
  rw [PresheafOfModules.map_smul, restrict_basisSection]
  rfl

private lemma columnLocalSection_compatible (j : ℕ) :
    TopCat.Presheaf.IsCompatible
      (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.presheaf
      (columnCover j) (columnLocalSection j) := by
  intro a b
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some i =>
          rw [restrict_columnLocalSection,
            columnScalar_zero j (columnCover j none ⊓ columnCover j (some i))
              (fun p hp => hp.1), zero_smul]
          exact map_zero _
  | some i =>
      cases b with
      | none =>
          rw [restrict_columnLocalSection,
            columnScalar_zero j (columnCover j (some i) ⊓ columnCover j none)
              (fun p hp => hp.2), zero_smul]
          exact (map_zero _).symm
      | some k =>
          by_cases hik : i = k
          · subst k
            rfl
          · rw [restrict_columnLocalSection, restrict_columnLocalSection,
              columnScalar_zero j _ fun p hp => by
                obtain ⟨x, hx, _⟩ := hp.1
                obtain ⟨y, hy, _⟩ := hp.2
                exact (hik (congrArg Prod.fst (Sum.inr.inj (hx.symm.trans hy)))).elim,
              zero_smul, zero_smul]

private lemma exists_columnSection (j : ℕ) :
    ∃ s : (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.obj (op ⊤),
      ∀ i, (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.map
        (homOfLE le_top).op s = columnLocalSection j i := by
  let F : TopCat.Sheaf AddCommGrpCat ringedSpace.carrier :=
    ⟨_, (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).isSheaf⟩
  exact (F.existsUnique_gluing' (columnCover j) ⊤ (fun _ => homOfLE le_top)
    (columnCover_covers j) (columnLocalSection j) (columnLocalSection_compatible j)).exists

private noncomputable def columnSection (j : ℕ) :
    (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.obj (op ⊤) :=
  (exists_columnSection j).choose

private lemma columnSection_restrict (j : ℕ) (i : Option ℕ) :
    (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.map
      (homOfLE (show columnCover j i ≤ ⊤ from le_top)).op (columnSection j) =
      columnLocalSection j i := (exists_columnSection j).choose_spec i

private lemma columnSection_project (j i : ℕ) (x : {x : ℝ // x ≠ 0}) (k : ℕ × ℕ) :
    (((SheafOfModules.freeProjection (R := structureSheafRing ringedSpace) k).val.app
        (op ⊤) (columnSection j))).hom ⟨branch i x, Set.mem_univ _⟩ =
      if k = (j, i) then cutoff ((j + 1) * (x : ℝ)) else 0 := by
  classical
  have hx : branch i x ∈ columnCover j (some i) := ⟨x, rfl, Set.mem_univ _⟩
  have h := PresheafOfModules.naturality_apply
    (SheafOfModules.freeProjection (R := structureSheafRing ringedSpace) k).val
    (homOfLE (show columnCover j (some i) ≤ ⊤ from le_top)).op (columnSection j)
  rw [columnSection_restrict] at h
  have he := congrArg (fun r : (SheafOfModules.unit (structureSheafRing ringedSpace)).val.obj
    (op (columnCover j (some i))) => r.hom ⟨branch i x, hx⟩) h
  change _ = (((SheafOfModules.freeProjection (R := structureSheafRing ringedSpace) k).val.app
    (op ⊤) (columnSection j))).hom ⟨branch i x, Set.mem_univ _⟩ at he
  rw [← he]
  dsimp only [columnLocalSection]
  rw [map_smul, freeProjection_basis ringedSpace k (j, i) (columnCover j (some i))]
  by_cases hk : k = (j, i)
  · simp only [ite_eq_left hk]
    show cutoff ((j + 1) * (x : ℝ)) * 1 = _
    exact mul_one _
  · simp only [ite_eq_right hk, smul_zero]
    rfl

private noncomputable def freeMorphism :
    SheafOfModules.free (R := structureSheafRing ringedSpace) ℕ ⟶
      SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ) :=
  CategoryTheory.Limits.Sigma.desc
    (fun j => homOfGlobalSection ringedSpace _ (columnSection j))

private lemma freeMorphism_basis (j : ℕ) (U : Opens ringedSpace) :
    freeMorphism.val.app (op U) (basisSection ringedSpace U j) =
      (SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ)).val.map
        (homOfLE le_top).op (columnSection j) := by
  have h : SheafOfModules.ιFree (R := structureSheafRing ringedSpace) j ≫ freeMorphism =
      homOfGlobalSection ringedSpace _ (columnSection j) :=
    CategoryTheory.Limits.Sigma.ι_desc _ _
  have he := congrArg (fun f : SheafOfModules.unit (structureSheafRing ringedSpace) ⟶
    SheafOfModules.free (R := structureSheafRing ringedSpace) (ℕ × ℕ) =>
      f.val.app (op U) ((1 : (structureSheafRing ringedSpace).obj.obj (op U)))) h
  exact he.trans (homOfGlobalSection_one _ _ _ _)

private lemma freeMorphism_project (U : Opens ringedSpace) (j i : ℕ)
    (x : {x : ℝ // x ≠ 0}) (hx : branch i x ∈ U) (k : ℕ × ℕ) :
    (((SheafOfModules.freeProjection (R := structureSheafRing ringedSpace) k).val.app (op U)
      (freeMorphism.val.app (op U) (basisSection ringedSpace U j)))).hom
        ⟨branch i x, hx⟩ =
      if k = (j, i) then cutoff ((j + 1) * (x : ℝ)) else 0 := by
  rw [freeMorphism_basis, PresheafOfModules.naturality_apply]
  exact columnSection_project j i x k

private lemma freeProjection_sum_eq_zero (X : RingedSpace.{0, 0}) {I : Type} [DecidableEq I]
    (U : Opens X) (g : I →₀ (structureSheafRing X).obj.obj (op U)) (i : I)
    (hi : i ∉ g.support) :
    (SheafOfModules.freeProjection (R := structureSheafRing X) i).val.app (op U)
      (g.sum (fun k r => r • basisSection X U k)) = 0 := by
  classical
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [map_smul, freeProjection_basis, ite_eq_right (by rintro rfl; exact hi hk), smul_zero]

private lemma freeMorphism_not_finite (U : Opens ringedSpace)
    (hU : origin ∈ U) :
    ∃ j : ℕ, ∀ g : (ℕ × ℕ) →₀ (structureSheafRing ringedSpace).obj.obj (op U),
      freeMorphism.val.app (op U) (basisSection ringedSpace U j) ≠
        g.sum (fun k r => r • basisSection ringedSpace U k) := by
  classical
  obtain ⟨n, hn⟩ := exists_uniformNeighborhood_subset U.isOpen hU
  refine ⟨4 * (n + 1), fun g he => ?_⟩
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset (g.support.image Prod.snd)
  have hki : (4 * (n + 1), i) ∉ g.support := fun hk => hi (Finset.mem_image.mpr ⟨_, hk, rfl⟩)
  let x : {x : ℝ // x ≠ 0} := ⟨(3 : ℝ) / (4 * (n + 1)), by positivity⟩
  have hx : branch i x ∈ U := hn (Or.inr ⟨i, x, rfl, by
    dsimp [x]
    rw [abs_of_pos (by positivity)]
    have hp : (0 : ℝ) < n + 1 := by positivity
    apply (div_lt_div_iff₀ (by positivity) hp).mpr
    nlinarith⟩)
  have hv := freeMorphism_project U (4 * (n + 1)) i x hx (4 * (n + 1), i)
  rw [he, freeProjection_sum_eq_zero _ _ g _ hki, ite_eq_left rfl] at hv
  have hf : cutoff (((4 * (n + 1) : ℕ) + 1) * (x : ℝ)) = 1 := by
    apply cutoff_one
    dsimp [x]
    rw [abs_of_pos (by positivity)]
    have hp : (0 : ℝ) < n + 1 := by positivity
    push_cast
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (n + 1))).mpr
    nlinarith
  rw [hf] at hv
  exact (zero_ne_one : (0 : ℝ) ≠ 1) hv

private lemma sheafIso_inv_hom_apply (X : RingedSpace.{0, 0})
    {F G : SheafOfModules.{0} (structureSheafRing X)} (e : F ≅ G)
    (U : Opens X) (x : F.val.obj (op U)) :
    e.inv.val.app (op U) (e.hom.val.app (op U) x) = x :=
  congrArg (fun f : F ⟶ F => f.val.app (op U) x) e.hom_inv_id

/-- The countable bouquet carries a morphism of sheaves associated to free
modules that does not locally come from a homomorphism of the free modules:
its value on a basis section is never a finite target-basis combination on
any neighborhood of the common origin. -/
@[stacks 01BL "non-module-induced morphism"]
public theorem exists_freeSheafMorphism_not_locally_finite :
    ∃ (X : RingedSpace.{0, 0}) (e : X ≃ₜ Point)
      (σ : X.presheaf ≅
        TopCat.presheafToTopCommRing (X := X.carrier) (TopCommRingCat.of ℝ))
      (s : SheafOfModules.free (R := structureSheafRing X) ℕ ≅
        associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤)))
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            (ℕ →₀ X.presheaf.obj (op ⊤))))
      (t : SheafOfModules.free (R := structureSheafRing X) (ℕ × ℕ) ≅
        associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤)))
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            ((ℕ × ℕ) →₀ X.presheaf.obj (op ⊤))))
      (φ : associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤)))
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            (ℕ →₀ X.presheaf.obj (op ⊤))) ⟶
        associatedSheaf X (RingHom.id (X.presheaf.obj (op ⊤)))
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            ((ℕ × ℕ) →₀ X.presheaf.obj (op ⊤)))),
      (∀ j : ℕ, s.hom.val.app (op ⊤) (basisSection X ⊤ j) =
        ((associatedSheafAdjunction X
          (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            (ℕ →₀ X.presheaf.obj (op ⊤)))) (Finsupp.single j 1)) ∧
      (∀ k : ℕ × ℕ, t.hom.val.app (op ⊤) (basisSection X ⊤ k) =
        ((associatedSheafAdjunction X
          (RingHom.id (X.presheaf.obj (op ⊤)))).unit.app
          (ModuleCat.of (X.presheaf.obj (op ⊤))
            ((ℕ × ℕ) →₀ X.presheaf.obj (op ⊤)))) (Finsupp.single k 1)) ∧
      (∃ (f : ℝ → ℝ) (_ : Continuous f),
        (∀ x : ℝ, |x| < 1 → f x = 0) ∧
        (∀ x : ℝ, 2 < |x| → f x = 1) ∧
        (∃ π : (ℕ × ℕ) →
            (SheafOfModules.free (R := structureSheafRing X) (ℕ × ℕ) ⟶
              SheafOfModules.unit (structureSheafRing X)),
          (∀ k l : ℕ × ℕ,
            SheafOfModules.ιFree (R := structureSheafRing X) l ≫ π k = if k = l then 𝟙 _ else 0) ∧
          (∀ (U : Opens X) (j i : ℕ) (x : {x : ℝ // x ≠ 0})
            (hx : e.symm (branch i x) ∈ U) (k : ℕ × ℕ),
            ((σ.hom.app (op U)
              ((π k).val.app (op U)
                (t.inv.val.app (op U)
                  (φ.val.app (op U)
                    (s.hom.val.app (op U) (basisSection X U j))))))).hom
                ⟨e.symm (branch i x), hx⟩ =
              if k = (j, i) then f ((j + 1) * (x : ℝ)) else 0))) ∧
      (∀ U : Opens X, e.symm origin ∈ U →
        ∃ j : ℕ, ∀ g : (ℕ × ℕ) →₀ (structureSheafRing X).obj.obj (op U),
          φ.val.app (op U) (s.hom.val.app (op U) (basisSection X U j)) ≠
            t.hom.val.app (op U)
              (g.sum (fun k r => r • basisSection X U k))) := by
  classical
  obtain ⟨s, hs⟩ := exists_free_iso_associatedSheaf_freeModule ringedSpace ℕ
  obtain ⟨t, ht⟩ := exists_free_iso_associatedSheaf_freeModule ringedSpace (ℕ × ℕ)
  have key : ∀ (U : Opens ringedSpace) (j : ℕ),
      t.inv.val.app (op U) ((s.inv ≫ freeMorphism ≫ t.hom).val.app (op U)
        (s.hom.val.app (op U) (basisSection ringedSpace U j))) =
      freeMorphism.val.app (op U) (basisSection ringedSpace U j) := fun U j => by
    change t.inv.val.app (op U) (t.hom.val.app (op U) (freeMorphism.val.app (op U)
      (s.inv.val.app (op U) (s.hom.val.app (op U) _)))) = _
    rw [sheafIso_inv_hom_apply, sheafIso_inv_hom_apply]
  refine ⟨ringedSpace, Homeomorph.refl _, Iso.refl _, s, t,
    s.inv ≫ freeMorphism ≫ t.hom, hs, ht, ?_, ?_⟩
  · refine ⟨cutoff, continuous_cutoff, fun x hx => cutoff_zero hx,
      fun x hx => cutoff_one hx,
      SheafOfModules.freeProjection (R := structureSheafRing ringedSpace),
      freeProjection_ι ringedSpace, ?_⟩
    intro U j i x hx k
    rw [key U j]
    exact freeMorphism_project U j i x hx k
  · intro U hU
    obtain ⟨j, hj⟩ := freeMorphism_not_finite U hU
    refine ⟨j, fun g h => hj g ?_⟩
    rw [← key U j, h, sheafIso_inv_hom_apply]

end Stacks.Bouquet

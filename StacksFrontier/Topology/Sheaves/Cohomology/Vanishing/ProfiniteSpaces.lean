module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Profinite.ClopenRefinement
public import StacksFrontier.Topology.Profinite.Defs
public import StacksFrontier.Topology.Sheaves.EpiMono.Defs

/-!
# Higher cohomology on a profinite space vanishes

Let `X` be a profinite topological space, that is compact, Hausdorff and totally disconnected.
Then `H^q(X, F) = 0` for every abelian sheaf `F` on `X` and every `q > 0`. This is Stacks 0A3F.

The proof is the source's: global sections is an exact functor on `X`. Indeed, let `f : F ⟶ G`
be an epimorphism of abelian sheaves and let `t` be a global section of `G`. Epimorphisms of
abelian sheaves are local surjections, so `t` lifts over an open covering `{U_x}_{x ∈ X}`.
Refine that covering, by Stacks 08ZZ, to a finite covering of `X` by pairwise *disjoint*
clopen subsets `W_1, …, W_n`. The chosen local lifts over the `W_j` are then automatically
compatible — their pairwise intersections are empty, and a sheaf has a single section over the
empty open — so they glue to a global section of `F` lifting `t`. Hence global sections
preserves epimorphisms; being also left exact, it is exact, and therefore its higher right
derived functors vanish on every object.

## Main definitions

* `Stacks.CohomologyVanishing.abelianSheafCohomology`: sheaf cohomology of an abelian sheaf
  on a topological space, as the right derived functor of global sections.

## Main results

* `Stacks.CohomologyVanishing.preservesEpimorphisms_globalSections_of_isProfiniteStacks`: on a
  profinite space, global sections of abelian sheaves is right exact.
* `Stacks.CohomologyVanishing.isZero_abelianSheafCohomology_of_isProfiniteStacks`: on a
  profinite space, every positive-degree cohomology group of every abelian sheaf vanishes.

## Implementation notes

The global sections functor is `(sheafSections _ AddCommGrpCat).obj (op ⊤)`, that is
evaluation on the top open set, and cohomology is its right derived functor. Vanishing is
expressed as `CategoryTheory.Limits.IsZero`.

The gluing step is carried out after applying `AddCommGrpCat.uliftFunctor` to raise the sheaf
into the universe `max u w` of the space: Mathlib's unique-gluing API for a sheaf on a
`TopCat` needs the value category's universe to contain the space's, whereas the statement is
proved for a coefficient universe `w` independent of the universe `u` of the space. Lifting
and lowering changes nothing, since `ULift` is fully faithful on sections.

The additivity instance below is the universe-independent form of
`Stacks.Cohomology.ModuleComparison.sheafSections_additive`, which is stated only for a
coefficient universe equal to the universe of the space; the two agree whenever both apply.

## References

* [Stacks Project, Tag 0A3F](https://stacks.math.columbia.edu/tag/0A3F)
* [Stacks Project, Tag 08ZZ](https://stacks.math.columbia.edu/tag/08ZZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.CohomologyVanishing

universe u w

variable {X : Type u} [TopologicalSpace X]

/-- A family of sections of an abelian sheaf over pairwise disjoint opens is compatible: each
pairwise intersection is empty, and a sheaf has a single section over the empty open. -/
private theorem isCompatible_of_pairwise_inf_eq_bot {ι : Type*}
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) (V : ι → Opens X)
    (hV : Pairwise fun i j ↦ V i ⊓ V j = ⊥) (s : ∀ j, ToType (F.obj.obj (op (V j)))) :
    TopCat.Presheaf.IsCompatible (X := TopCat.of X) F.obj V s := by
  intro i j
  obtain rfl | hij := eq_or_ne i j
  · rfl
  · have hbot : (⊥ : Sieve (⊥ : Opens X)) ∈ Opens.grothendieckTopology X (⊥ : Opens X) :=
      (Opens.mem_grothendieckTopology (T := X) (U := ⊥) (S := ⊥)).2 (by simp)
    have : Subsingleton (F.obj.obj (op (V i ⊓ V j))) := by
      rw [hV hij]
      exact AddCommGrpCat.subsingleton_of_isZero
        (Sheaf.isTerminalOfBotCover F (⊥ : Opens X) hbot).isZero
    exact Subsingleton.elim _ _

/-- An open cover of a profinite space is refined by a finite cover by pairwise disjoint opens. -/
private theorem exists_fin_pairwise_disjoint_opens_refinement
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) :
    ∃ (n : ℕ) (V : Fin n → Opens X), (⊤ : Opens X) ≤ iSup V ∧
      (Pairwise fun i j ↦ V i ⊓ V j = ⊥) ∧ ∀ j, ∃ i, V j ≤ U i := by
  obtain ⟨n, W, hWref, hWcov, hWdisj⟩ := hU.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, fun j ↦ ⟨W j, (W j).isClopen'.2⟩, fun x _ ↦ ?_, fun i j hij ↦ ?_,
    fun j ↦ (hWref j).2⟩
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hWcov (Set.mem_univ x))
    exact Opens.mem_iSup.mpr ⟨j, hj⟩
  · apply SetLike.coe_injective
    show (W i : Set X) ∩ (W j : Set X) = ∅
    exact congrArg (fun A : Clopens X ↦ (A : Set X)) (disjoint_iff.mp (hWdisj hij))

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]

/-- On a profinite space, global sections of abelian sheaves preserves epimorphisms: a local
lift of a global section over an arbitrary covering can be rearranged, using Stacks 08ZZ, into
a lift over a finite covering by pairwise disjoint clopens, and such lifts glue. -/
private lemma epi_globalSections_map_of_isProfiniteStacks
    [((Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w})]
    (hX : IsProfiniteStacks X)
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}} (f : F ⟶ G) [Epi f] :
    Epi (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
      (op (⊤ : Opens X))).map f) := by
  refine (AddCommGrpCat.epi_iff_surjective _).2 fun t ↦ ?_
  have hloc : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) f.hom :=
    (Sheaf.isLocallySurjective_iff_epi' (J := Opens.grothendieckTopology X) AddCommGrpCat f).2
      inferInstance
  choose U i hi using fun x : X ↦ hloc.imageSieve_mem t x (by simp)
  have hOpen : TopologicalSpace.IsOpenCover U :=
    le_antisymm le_top fun x _ ↦ Opens.mem_iSup.mpr ⟨x, (hi x).2⟩
  obtain ⟨_, _, _⟩ := (isProfiniteStacks_iff_compact_t2_totallyDisconnected X).mp hX
  obtain ⟨n, V, hVcov, hV, hVref⟩ := exists_fin_pairwise_disjoint_opens_refinement hOpen
  choose x hx using hVref
  choose a ha using fun j ↦ (hi (x j)).1
  let K := sheafCompose (Opens.grothendieckTopology X) AddCommGrpCat.uliftFunctor.{u, w}
  let F₁ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} := K.obj F
  let G₁ : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{max u w} := K.obj G
  let f₁ : F₁ ⟶ G₁ := K.map f
  let F₁' : TopCat.Sheaf AddCommGrpCat.{max u w} (TopCat.of X) := F₁
  let G₁' : TopCat.Sheaf AddCommGrpCat.{max u w} (TopCat.of X) := G₁
  let t₁ : ToType (G₁'.obj.obj (op (⊤ : Opens X))) := ULift.up t
  let incl : ∀ j, V j ⟶ U (x j) := fun j ↦ homOfLE (hx j)
  let s : ∀ j, ToType (F₁.obj.obj (op (V j))) := fun j ↦
    F₁.obj.map (incl j).op (ULift.up (a j))
  obtain ⟨r, hr, -⟩ := F₁'.existsUnique_gluing' V ⊤ (fun j ↦ homOfLE le_top) hVcov s
    (isCompatible_of_pairwise_inf_eq_bot F₁ V hV s)
  have hglobal : f₁.hom.app (op ⊤) r = t₁ := by
    refine G₁'.eq_of_locally_eq' V ⊤ (fun j ↦ homOfLE le_top) hVcov
      (f₁.hom.app (op ⊤) r) t₁ fun j ↦ ?_
    rw [← ConcreteCategory.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply, hr j]
    dsimp [s]
    rw [NatTrans.naturality_apply f₁.hom (incl j).op (ULift.up (a j)),
      show f₁.hom.app (op (U (x j))) (ULift.up (a j)) =
        ULift.up ((G.obj.map (i (x j)).op) t) from congrArg ULift.up (ha j)]
    show ULift.up ((G.obj.map (incl j).op) ((G.obj.map (i (x j)).op) t)) =
      ULift.up ((G.obj.map (homOfLE (show V j ≤ ⊤ from le_top)).op) t)
    rw [← Functor.map_comp_apply, ← op_comp,
      Subsingleton.elim (incl j ≫ i (x j)) (homOfLE le_top)]
  exact ⟨r.down, congrArg ULift.down hglobal⟩

/-- **On a profinite space, global sections of abelian sheaves is right exact.** -/
theorem preservesEpimorphisms_globalSections_of_isProfiniteStacks
    [((Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w})]
    (hX : IsProfiniteStacks X) :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
      (op (⊤ : Opens X))).PreservesEpimorphisms :=
  ⟨fun f _ ↦ epi_globalSections_map_of_isProfiniteStacks hX f⟩

/-- Evaluation of abelian sheaves on the whole space is additive. -/
instance globalSections_additive :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
      (op (⊤ : Opens X))).Additive :=
  inferInstanceAs (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op ⊤)).Additive

variable [EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})]

/-- The `q`-th cohomology of an abelian sheaf on `X`, as the `q`-th right derived functor of
global sections. -/
noncomputable abbrev abelianSheafCohomology (q : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w}) : AddCommGrpCat.{w} :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
    (op (⊤ : Opens X))).rightDerived q).obj F

/-- **Stacks 0A3F.** If `X` is profinite, then every positive-degree cohomology group of
every abelian sheaf on `X` is zero. -/
@[stacks 0A3F]
theorem isZero_abelianSheafCohomology_of_isProfiniteStacks
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hX : IsProfiniteStacks X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{w})
    (q : ℕ) (hq : 0 < q) :
    IsZero (abelianSheafCohomology q F) := by
  let E := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{w}).obj
    (op (⊤ : Opens X))
  have : E.PreservesEpimorphisms := preservesEpimorphisms_globalSections_of_isProfiniteStacks hX
  have : PreservesFiniteLimits E :=
    preservesFiniteLimits_of_natIso
      (sheafSectionsNatIsoEvaluation (Opens.grothendieckTopology X) AddCommGrpCat.{w}).symm
  have : E.PreservesHomology := Functor.preservesHomology_of_preservesEpis_and_kernels E
  let I := injectiveResolution F
  refine IsZero.of_iso ?_ (I.isoRightDerivedObj E q)
  show IsZero (((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q)
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  rw [HomologicalComplex.exactAt_iff]
  exact (HomologicalComplex.exactAt_iff _ _ |>.mp (I.cocomplex_exactAt_succ n)).map E

end Stacks.CohomologyVanishing

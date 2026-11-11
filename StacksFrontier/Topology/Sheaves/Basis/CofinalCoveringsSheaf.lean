module

public import StacksFrontier.Topology.Sheaves.Basis.CofinalCoverings
public import StacksFrontier.Topology.Sheaves.Basis.Sheaf

/-!
# Stacks 009K — the sheaf condition on a basis from a cofinal system of coverings

Let `B` be a basis for the topology of `X` and `C` a cofinal system of coverings of the members
of `B`, and for each covering `U = ⋃ Uᵢ` in `C` let coverings `Uᵢ ⊓ Uⱼ = ⋃ Uᵢⱼₖ` by members of `B`
be given. Stacks 009K says that a presheaf of sets `F` on `B` is a sheaf on `B` (Stacks 009J,
`IsSheafOnBasis`: the condition `(**)` for every covering and every choice of the `Uᵢⱼₖ`) iff
`(**)` holds for the coverings in `C` with the given `Uᵢⱼₖ`. This is
`isSheafOnBasis_iff_forall_mem_cofinalSystem`.

The key step is `sheafConditionStarStar_of_cofinal`: `(**)` on `C` for one choice of
intersection coverings gives `(**)` for every basis covering and every choice of intersection
coverings. `BasisPresheaf.toPresheafOnBasisOpenStruct` and
`isSheafOnBasis_iff_forall_sheafConditionStarStar` identify `IsSheafOnBasis` for a
`BasisPresheaf` with that universally quantified form of `(**)`, and
`GivenIntersectionCoverings.extend` extends choices given on `C` to every basis covering.
-/

@[expose] public section

open TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- **Independence of the choice of intersection coverings.** If `(**)` holds on the cofinal
system `C` with the choices `all`, then `(**)` holds for every basis covering `𝒰` of every
`U ∈ B` and for *every* choice `𝒰ij` of basis coverings of the intersections. -/
theorem sheafConditionStarStar_of_cofinal
    {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B) (all : GivenIntersectionCoverings B)
    (F : BasisPresheaf B) (hC : SheafConditionOnCofinalSystem F C all)
    {U : Opens X} (hU : U ∈ B) (𝒰 : BasisCovering B U)
    (𝒰ij : IntersectionCoverings B 𝒰) :
    SheafConditionStarStar F hU 𝒰 𝒰ij := fun s hs =>
  sheafCondition_cofinal_implies_basis hB C all F hC U hU 𝒰 s fun i j _ =>
    local_to_global_on_subopen hB C all F hC (𝒰.mem_basis i) (𝒰.mem_basis j) (s i) (s j) _ _
      (𝒰ij.mem_basis i j) (𝒰ij.le_left i j) (𝒰ij.le_right i j) (𝒰ij.isCovering i j) (hs i j)
      _ _ _

/-- Every basis covering of `U` admits a choice of basis coverings of the intersections
`Uᵢ ⊓ Uⱼ`, when `B` is a basis. -/
lemma IntersectionCoverings.nonempty {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {U : Opens X} (𝒰 : BasisCovering B U) : Nonempty (IntersectionCoverings B 𝒰) := by
  choose 𝒲 _ _ using fun i j => exists_basis_refinement hB (W := 𝒰.obj i ⊓ 𝒰.obj j)
    (fun _ : PUnit.{u + 1} => 𝒰.obj i ⊓ 𝒰.obj j) (le_iSup_of_le PUnit.unit le_rfl)
  exact ⟨{ idx := fun i j => (𝒲 i j).ι
           obj := fun i j => (𝒲 i j).obj
           mem_basis := fun i j => (𝒲 i j).mem_basis
           le_left := fun i j k => ((𝒲 i j).obj_le k).trans inf_le_left
           le_right := fun i j k => ((𝒲 i j).obj_le k).trans inf_le_right
           isCovering := fun i j => (𝒲 i j).isCovering }⟩

/-- Extend a choice of intersection coverings given for the coverings of a cofinal system `C`
to a choice for every basis covering. -/
noncomputable def GivenIntersectionCoverings.extend {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B)
    (ch : ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U), 𝒰 ∈ C.cov U hU →
      IntersectionCoverings B 𝒰) :
    GivenIntersectionCoverings B where
  ij U hU 𝒰 := by
    classical
    exact if h : 𝒰 ∈ C.cov U hU then ch U hU 𝒰 h else (IntersectionCoverings.nonempty hB 𝒰).some

/-- On a covering of the cofinal system, the extended choice is the given one. -/
lemma GivenIntersectionCoverings.extend_ij_of_mem {B : Set (Opens X)} (hB : Opens.IsBasis B)
    (C : CofinalSystem B)
    (ch : ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U), 𝒰 ∈ C.cov U hU →
      IntersectionCoverings B 𝒰)
    {U : Opens X} (hU : U ∈ B) {𝒰 : BasisCovering B U} (h : 𝒰 ∈ C.cov U hU) :
    (extend hB C ch).ij U hU 𝒰 = ch U hU 𝒰 h :=
  by simp [extend, h]

/-- The underlying presheaf on `B` of a `BasisPresheaf`, in the form used by the Stacks 009J
sheaf condition `IsSheafOnBasis`. -/
def BasisPresheaf.toPresheafOnBasisOpenStruct {B : Set (Opens X)} (F : BasisPresheaf B) :
    PresheafOnBasisOpenStruct B where
  obj := F.obj
  res := F.restrict
  res_id hU s := F.restrict_id _ hU s
  res_comp := F.restrict_comp

/-- The Stacks 009J sheaf condition for a `BasisPresheaf` is `(**)` for every basis covering of
every `U ∈ B` and every choice of basis coverings of the intersections. -/
theorem isSheafOnBasis_iff_forall_sheafConditionStarStar {B : Set (Opens X)}
    (hB : Opens.IsBasis B) (F : BasisPresheaf B) :
    IsSheafOnBasis hB F.toPresheafOnBasisOpenStruct ↔
      ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U) (𝒰ij : IntersectionCoverings B 𝒰),
        SheafConditionStarStar F hU 𝒰 𝒰ij := by
  constructor
  · intro h U hU 𝒰 𝒰ij s hs
    exact h hU 𝒰.obj 𝒰.mem_basis 𝒰.isCovering.symm 𝒰ij.obj 𝒰ij.mem_basis
      (fun i j => (𝒰ij.isCovering i j).symm) s hs
  · intro h U hU I Uι hUι hcover J V hV hVcover s hs
    exact h U hU ⟨I, Uι, hUι, hcover.symm⟩
      ⟨J, V, hV, fun i j k => ((le_iSup (V i j) k).trans_eq (hVcover i j).symm).trans inf_le_left,
        fun i j k => ((le_iSup (V i j) k).trans_eq (hVcover i j).symm).trans inf_le_right,
        fun i j => (hVcover i j).symm⟩ s hs

/-- **Cofinal systems of coverings and the sheaf condition on a basis.** Let `B` be a basis for
the topology of `X`, let `C` be a cofinal system of coverings (`C U ⊆ Cov_B(U)` for each `U ∈ B`),
and for each covering `𝒰 : U = ⋃ Uᵢ` in `C U` let `ch U hU 𝒰 h𝒰` be given coverings
`Uᵢ ⊓ Uⱼ = ⋃ Uᵢⱼₖ` by basis elements. A presheaf of sets `F` on `B` is a sheaf on `B` (Stacks 009J,
the condition `(**)` for every covering and every choice of the `Uᵢⱼₖ`) iff `(**)` holds for every
`U ∈ B` and every `𝒰 ∈ C U` with the given coverings `ch U hU 𝒰 h𝒰`. -/
@[stacks 009K "both directions; the sheaf on B is the Stacks 009J notion, over every choice of \
intersection coverings, and the coverings of the intersections are given for the coverings in C"]
theorem isSheafOnBasis_iff_forall_mem_cofinalSystem
    {B : Set (Opens X)} (hB : Opens.IsBasis B) (C : CofinalSystem B)
    (ch : ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U), 𝒰 ∈ C.cov U hU →
      IntersectionCoverings B 𝒰)
    (F : BasisPresheaf B) :
    IsSheafOnBasis hB F.toPresheafOnBasisOpenStruct ↔
      ∀ (U : Opens X) (hU : U ∈ B) (𝒰 : BasisCovering B U) (h𝒰 : 𝒰 ∈ C.cov U hU),
        SheafConditionStarStar F hU 𝒰 (ch U hU 𝒰 h𝒰) := by
  rw [isSheafOnBasis_iff_forall_sheafConditionStarStar]
  refine ⟨fun h U hU 𝒰 _ => h U hU 𝒰 _, fun h U hU 𝒰 𝒰ij => ?_⟩
  refine sheafConditionStarStar_of_cofinal hB C (GivenIntersectionCoverings.extend hB C ch) F
    (fun U' hU' 𝒰' h𝒰' => ?_) hU 𝒰 𝒰ij
  rw [GivenIntersectionCoverings.extend_ij_of_mem hB C ch hU' h𝒰']
  exact h U' hU' 𝒰' h𝒰'

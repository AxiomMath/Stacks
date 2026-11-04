module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceAcyclicCover
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# A complex with quasi-coherent cohomology is the derived limit of its truncations

Let `X` be a scheme and let `E` be an object of `D(𝒪_X)` all of whose cohomology sheaves are
quasi-coherent. Then the canonical map `E ⟶ R lim τ_{≥ -n} E` into any derived limit of the tower
of canonical truncations from below is an isomorphism. This is [Stacks, Tag 08D3].

## Main results

* `TopologicalSpace.Opens.hasEnoughObjects_of_isBasis`: a basis of opens covers every object of
  the site of opens.
* `AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen`: [Stacks, Tag 01XB] with its
  conclusion read in modules over the sections of the structure sheaf rather than in abelian
  groups.
* `AlgebraicGeometry.isIso_of_isDerivedLimit_truncGETower`: [Stacks, Tag 08D3].
* `AlgebraicGeometry.exists_isDerivedLimit_truncGETower_of_isQuasicoherent`: the same statement
  packaged as `CategoryTheory.Pretriangulated.IsDerivedLimit` of the tower at `E` itself.

## Implementation notes

A derived limit is presented by the structural morphism to the product together with the
distinguished triangle characterising it, rather than by a chosen construction; the canonical map
out of `E` is pinned down by requiring its composites with the product projections to be the
canonical truncation maps.

## References

* [Stacks Project, Tag 08D3](https://stacks.math.columbia.edu/tag/08D3)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 0D6M](https://stacks.math.columbia.edu/tag/0D6M)
* [Stacks Project, Tag 0BK7](https://stacks.math.columbia.edu/tag/0BK7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open TopologicalSpace

universe u

attribute [local instance] HasDerivedCategory.standard

namespace TopologicalSpace.Opens

/-- If `B` is a basis of the opens of a space `T`, then the site of opens of `T` has enough
`B`-objects in the sense of [Stacks, Tag 090L]: every open is covered by the members of `B`
contained in it. -/
theorem hasEnoughObjects_of_isBasis {T : Type u} [TopologicalSpace T] {B : Set (Opens T)}
    (hB : Opens.IsBasis B) :
    (Opens.grothendieckTopology T).HasEnoughObjects (· ∈ B) := by
  intro U
  refine ⟨{V : Opens T // V ∈ B ∧ V ≤ U}, fun i ↦ i.1, fun i ↦ homOfLE i.2.2, ?_,
    fun i ↦ i.2.1⟩
  refine (Opens.mem_grothendieckTopology T).2 fun x hx ↦ ?_
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
  exact ⟨V, homOfLE hVU, (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨V, hV, hVU⟩, 𝟙 V, by simp⟩, hxV⟩

end TopologicalSpace.Opens

namespace AlgebraicGeometry

/-- The higher right derived functors of sections over an affine open of a scheme, as modules
over the sections of the structure sheaf, vanish on a quasi-coherent module. -/
theorem isZero_rightDerived_evaluation_of_isAffineOpen (X : Scheme.{u}) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived p).obj F) :=
  ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F U hU p hp)
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf U p).app F)))

variable (X : Scheme.{u})

/-- The vanishing hypothesis of Spaltenstein's criterion for a complex with quasi-coherent
cohomology on a scheme: on an affine open every cohomology sheaf of `E` is acyclic. -/
theorem isZero_rightDerived_evaluation_homologyFunctor_of_isAffineOpen
    (E : DerivedCategory X.Modules)
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    (U : X.Opens) (hU : U ∈ X.affineOpens) (p : ℕ) (hp : 0 < p) (q : ℤ) :
    IsZero (((SheafOfModules.evaluation X.ringCatSheaf (op U)).rightDerived p).obj
      ((DerivedCategory.homologyFunctor X.Modules q).obj E)) :=
  have := hE q
  isZero_rightDerived_evaluation_of_isAffineOpen X _ U hU p hp

/-- Let `X` be a scheme and let `E` be an object of `D(𝒪_X)` whose cohomology sheaves are all
quasi-coherent. Then the canonical map from `E` to a derived limit `L` of the tower
`n ↦ τ_{≥ -n} E` of canonical truncations from below is an isomorphism.

The derived limit is presented by its structural morphism `p` to the product of the tower and the
distinguished triangle `hL` characterising it; the map `c` out of `E` is the canonical one because
its composites with the product projections are required to be the truncation maps. -/
@[stacks 08D3]
theorem isIso_of_isDerivedLimit_truncGETower
    (E : DerivedCategory X.Modules)
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent)
    [HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩]
    (L : DerivedCategory X.Modules) (c : E ⟶ L)
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hL : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower X.Modules E).map
            (homOfLE (Nat.le_succ n)).op) δ ∈ distTriang (DerivedCategory X.Modules))
    (hc : ∀ n : ℕ, c ≫ p ≫
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩) n =
        (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E) :
    IsIso c := by
  have := Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower X.ringCatSheaf E
  exact Stacks.Cohomology.AcyclicCover.isIso_to_isDerivedLimit_truncGETower_of_acyclic
    X.ringCatSheaf E (· ∈ X.affineOpens)
    (Opens.hasEnoughObjects_of_isBasis X.isBasis_affineOpens)
    (isZero_rightDerived_evaluation_homologyFunctor_of_isAffineOpen X E hE)
    L c p δ hL hc

/-- A complex with quasi-coherent cohomology on a scheme is a derived limit of the tower of its
canonical truncations from below; in particular the product of the tower exists. -/
theorem exists_isDerivedLimit_truncGETower_of_isQuasicoherent
    (E : DerivedCategory X.Modules)
    (hE : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj E).IsQuasicoherent) :
    ∃ _ : HasProduct fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower X.Modules E).obj ⟨n⟩,
      IsDerivedLimit (Stacks.DerivedLimit.truncGETower X.Modules E) E := by
  have : EnoughInjectives X.Modules := IsGrothendieckAbelian.enoughInjectives
  obtain ⟨hprod, -⟩ := DerivedCategory.exists_isDerivedLimit_of_forall_isGE
    (Stacks.DerivedLimit.truncGETower X.Modules E)
    fun n ↦ ⟨-(n : ℤ), inferInstanceAs
      (((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj E).IsGE (-(n : ℤ)))⟩
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower X.Modules E)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app E)
    (fun n ↦ Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map E
      (homOfLE (Nat.le_succ n)).op)
    (isIso_of_isDerivedLimit_truncGETower X E hE)
  exact ⟨hprod, _, δ, hδ⟩

end AlgebraicGeometry

end

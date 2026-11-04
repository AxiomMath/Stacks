module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DescentDatumOfLocallyGivenObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.UniquenessOverACover
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.LocallyGivenOfGlobalObject

/-!
# The uniqueness clause of Tag 0D68 for a saturated collection

Let `(X, 𝒪_X)` be a ringed space and let `(ℬ, K_U, ρ^U_V)` be a system of locally given derived
objects on it, as in Situation 0D67. The uniqueness clause of [Stacks, Tag 0D68], relativized to
an open subset, is the predicate `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`. It holds for
every system whose collection is saturated, in the sense that an open which is the union of the
members contained in it is itself a member. In particular it holds for the system
`Stacks.DerivedGlueing.locallyGivenOfTop`, whose collection is all the opens of `X`, and for that
system the two statements of [Stacks, Tag 0D69] hold whenever the prescribed objects have no
negative self-Ext.

## Main results

* `Stacks.DerivedGlueing.exists_unique_solutionOverIso_of_mem_opens`: two solutions over a member
  of the collection are identified by a unique isomorphism of solutions.
* `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_of_sSup_covered_mem`: the uniqueness clause of
  [Stacks, Tag 0D68] for a saturated collection.
* `Stacks.DerivedGlueing.hasUniqueSolutionOverIso_locallyGivenOfTop`: the uniqueness clause for
  the system `Stacks.DerivedGlueing.locallyGivenOfTop`.
* `Stacks.DerivedGlueing.exists_unique_overlapIso_locallyGivenOfTop` and
  `Stacks.DerivedGlueing.restrictOverlapHom_cocycle_locallyGivenOfTop`: the two statements of
  [Stacks, Tag 0D69] for the system `Stacks.DerivedGlueing.locallyGivenOfTop`.

## References

* [Stacks Project, Tag 0D67](https://stacks.math.columbia.edu/tag/0D67)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
* [Stacks Project, Tag 0D69](https://stacks.math.columbia.edu/tag/0D69)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- Let `O` be a member of the collection. A morphism between two solutions over `O` that commutes
with their identifications over `O` commutes with their identifications over every member
contained in `O`. -/
theorem SolutionOver.isCompatibleHom_of_self {S : LocallyGiven X} {O : Opens X.carrier}
    (hO : O ∈ S.opens) (A B : SolutionOver S O) (ψ : A.obj ⟶ B.obj)
    (h : (S.restriction O O le_rfl).map ψ ≫ (B.rho O hO le_rfl).hom =
      (A.rho O hO le_rfl).hom) :
    A.IsCompatibleHom B ψ := by
  intro W hW hWO
  rw [← A.compatibility O W hWO hO hW le_rfl, ← B.compatibility O W hWO hO hW le_rfl,
    ← Category.assoc, (S.restrictionComp W O O hWO le_rfl).hom.naturality ψ,
    Functor.comp_map, Category.assoc, ← Functor.map_comp_assoc, h]

/-- Two solutions over a member of the collection are identified by a unique isomorphism of
solutions. -/
theorem exists_unique_solutionOverIso_of_mem_opens {S : LocallyGiven X} {O : Opens X.carrier}
    (hO : O ∈ S.opens) (A B : SolutionOver S O) :
    ∃! φ : A.obj ≅ B.obj, A.IsCompatibleHom B φ.hom := by
  set φ : A.obj ≅ B.obj := ((restrictionSelfIso S O le_rfl).app A.obj).symm ≪≫
    A.rho O hO le_rfl ≪≫ (B.rho O hO le_rfl).symm ≪≫
      (restrictionSelfIso S O le_rfl).app B.obj with hφdef
  have key : (S.restriction O O le_rfl).map φ.hom =
      (A.rho O hO le_rfl).hom ≫ (B.rho O hO le_rfl).inv := by
    rw [← cancel_mono ((restrictionSelfIso S O le_rfl).app B.obj).hom,
      restrictionSelfIso_naturality, hφdef]
    simp
  refine ⟨φ, SolutionOver.isCompatibleHom_of_self hO A B _ ?_, fun ψ hψ => Iso.ext ?_⟩
  · rw [key, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · refine restrictionSelf_map_injective S O le_rfl ?_
    rw [key, ← hψ O hO le_rfl, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- If every open which is the union of the members of the collection contained in it is itself a
member, then the relativized uniqueness clause `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`
of [Stacks, Tag 0D68] holds. -/
theorem hasUniqueSolutionOverIso_of_sSup_covered_mem (S : LocallyGiven X)
    (hmem : ∀ O : Opens X.carrier, O = sSup {W | W ∈ S.opens ∧ W ≤ O} → O ∈ S.opens) :
    HasUniqueSolutionOverIso S :=
  fun O hO _ _ A B => exists_unique_solutionOverIso_of_mem_opens (hmem O hO) A B

/-- The system `Stacks.DerivedGlueing.locallyGivenOfTop X K` of all opens satisfies the relativized
uniqueness clause `Stacks.DerivedGlueing.HasUniqueSolutionOverIso`. -/
theorem hasUniqueSolutionOverIso_locallyGivenOfTop (X : RingedSpace.{u, u})
    (K : OpenDerivedCategory X ⊤) :
    HasUniqueSolutionOverIso (locallyGivenOfTop X K) :=
  hasUniqueSolutionOverIso_of_sSup_covered_mem _ fun O _ => Set.mem_univ O

/-- For the system `Stacks.DerivedGlueing.locallyGivenOfTop X K`, the intersection of two members
is the supremum of the members contained in it. -/
theorem inter_eq_sSup_covered_locallyGivenOfTop (X : RingedSpace.{u, u})
    (K : OpenDerivedCategory X ⊤) :
    ∀ U ∈ (locallyGivenOfTop X K).opens, ∀ V ∈ (locallyGivenOfTop X K).opens,
      U ⊓ V = sSup {W | W ∈ (locallyGivenOfTop X K).opens ∧ W ≤ U ⊓ V} :=
  fun _ _ _ _ => le_antisymm (le_sSup ⟨Set.mem_univ _, le_rfl⟩) (sSup_le fun _ hW => hW.2)

/-! ### The two statements of Tag 0D69 for the system of all opens -/

/-- If the prescribed objects of the system `Stacks.DerivedGlueing.locallyGivenOfTop X K` have no
negative self-Ext, then for any two opens `U` and `V` the restrictions to `U ⊓ V` of the objects
on `U` and on `V` are identified by a unique isomorphism compatible with the system. -/
theorem exists_unique_overlapIso_locallyGivenOfTop (X : RingedSpace.{u, u})
    (K : OpenDerivedCategory X ⊤)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ (locallyGivenOfTop X K).opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((locallyGivenOfTop X K).obj U hU)
        ((locallyGivenOfTop X K).obj U hU) i))
    (U V : Opens X.carrier) :
    ∃! φ : ((locallyGivenOfTop X K).restriction (U ⊓ V) U inf_le_left).obj
          ((locallyGivenOfTop X K).obj U (Set.mem_univ U)) ≅
        ((locallyGivenOfTop X K).restriction (U ⊓ V) V inf_le_right).obj
          ((locallyGivenOfTop X K).obj V (Set.mem_univ V)),
      IsOverlapHom (locallyGivenOfTop X K) (Set.mem_univ U) (Set.mem_univ V)
        inf_le_left inf_le_right φ.hom :=
  exists_unique_overlapIso (locallyGivenOfTop X K)
    (hasUniqueSolutionOverIso_locallyGivenOfTop X K)
    (inter_eq_sSup_covered_locallyGivenOfTop X K) hExt U V (Set.mem_univ U) (Set.mem_univ V)

/-- If the prescribed objects of the system `Stacks.DerivedGlueing.locallyGivenOfTop X K` have no
negative self-Ext, then compatible isomorphisms over `U ⊓ V`, `V ⊓ W` and `U ⊓ W` satisfy the
cocycle condition over `U ⊓ V ⊓ W`. -/
theorem restrictOverlapHom_cocycle_locallyGivenOfTop (X : RingedSpace.{u, u})
    (K : OpenDerivedCategory X ⊤)
    (hExt : ∀ (U : Opens X.carrier) (hU : U ∈ (locallyGivenOfTop X K).opens), ∀ i : ℤ, i < 0 →
      Subsingleton (ShiftedHom ((locallyGivenOfTop X K).obj U hU)
        ((locallyGivenOfTop X K).obj U hU) i))
    (U V W : Opens X.carrier)
    (φUV : ((locallyGivenOfTop X K).restriction (U ⊓ V) U inf_le_left).obj
        ((locallyGivenOfTop X K).obj U (Set.mem_univ U)) ≅
      ((locallyGivenOfTop X K).restriction (U ⊓ V) V inf_le_right).obj
        ((locallyGivenOfTop X K).obj V (Set.mem_univ V)))
    (hφUV : IsOverlapHom (locallyGivenOfTop X K) (Set.mem_univ U) (Set.mem_univ V)
      inf_le_left inf_le_right φUV.hom)
    (φVW : ((locallyGivenOfTop X K).restriction (V ⊓ W) V inf_le_left).obj
        ((locallyGivenOfTop X K).obj V (Set.mem_univ V)) ≅
      ((locallyGivenOfTop X K).restriction (V ⊓ W) W inf_le_right).obj
        ((locallyGivenOfTop X K).obj W (Set.mem_univ W)))
    (hφVW : IsOverlapHom (locallyGivenOfTop X K) (Set.mem_univ V) (Set.mem_univ W)
      inf_le_left inf_le_right φVW.hom)
    (φUW : ((locallyGivenOfTop X K).restriction (U ⊓ W) U inf_le_left).obj
        ((locallyGivenOfTop X K).obj U (Set.mem_univ U)) ≅
      ((locallyGivenOfTop X K).restriction (U ⊓ W) W inf_le_right).obj
        ((locallyGivenOfTop X K).obj W (Set.mem_univ W)))
    (hφUW : IsOverlapHom (locallyGivenOfTop X K) (Set.mem_univ U) (Set.mem_univ W)
      inf_le_left inf_le_right φUW.hom) :
    restrictOverlapHom (locallyGivenOfTop X K) (Set.mem_univ U) (Set.mem_univ W)
        inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U ⊓ V ⊓ W ≤ U ⊓ W) φUW.hom =
      restrictOverlapHom (locallyGivenOfTop X K) (Set.mem_univ U) (Set.mem_univ V)
          inf_le_left inf_le_right (inf_le_left : U ⊓ V ⊓ W ≤ U ⊓ V) φUV.hom ≫
        restrictOverlapHom (locallyGivenOfTop X K) (Set.mem_univ V) (Set.mem_univ W)
          inf_le_left inf_le_right
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U ⊓ V ⊓ W ≤ V ⊓ W) φVW.hom :=
  restrictOverlapHom_cocycle (locallyGivenOfTop X K)
    (hasUniqueSolutionOverIso_locallyGivenOfTop X K)
    (inter_eq_sSup_covered_locallyGivenOfTop X K) hExt U V W
    (Set.mem_univ U) (Set.mem_univ V) (Set.mem_univ W) φUV hφUV φVW hφVW φUW hφUW

end Stacks.DerivedGlueing

end

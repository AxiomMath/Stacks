module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.LocallyConstantOpens
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.ConstructibleCurves.UnibranchGenericPoints

/-!
# Irreducible unibranch opens on which a constructible sheaf is locally constant

Let `X` be of finite type over a field and `ℱ` a constructible sheaf of `Λ`-modules on
`X_étale`. There are finitely many pairwise disjoint opens `W_a ⊆ X` with dense union, each
irreducible and geometrically unibranch, such that `ℱ|_{W_a}` is locally constant of finite type.

## Main results

* `Stacks.EtaleCohomology.exists_unibranch_opens_isFiniteTypeLocallyConstant`: the statement
  above, with the hypotheses of Stacks 0GJI on `X`.

## References

* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
-/

@[expose] public noncomputable section

open CategoryTheory Topology TopologicalSpace
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

/-- **A constructible sheaf on a curve is locally constant of finite type on finitely many
pairwise disjoint irreducible geometrically unibranch opens with dense union.** -/
theorem exists_unibranch_opens_isFiniteTypeLocallyConstant {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k)) [IsSeparated π]
    [LocallyOfFiniteType π] [QuasiCompact π] (_hX : topologicalKrullDim X ≤ 1)
    (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    ∃ (ι : Type u) (_ : Finite ι) (W : ι → X.Opens),
      Pairwise (fun a b => Disjoint (W a) (W b)) ∧ Dense ((⨆ a, W a : X.Opens) : Set X) ∧
      ∀ a, IrreducibleSpace (W a) ∧ IsGeometricallyUnibranch (W a).toScheme ∧
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (W a).toScheme.smallEtaleTopology
          ((etaleModuleRestriction.{u, r} Λ (W a).ι).obj F) := by
  classical
  have hNag : IsNagataScheme X := isNagataScheme_of_locallyOfFiniteType_over_field k π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian X := ⟨⟩
  let ι := irreducibleComponents X
  have hfin : Finite ι := NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hgen : ∀ a : ι, ∃ η : X, closure {η} = (a : Set X) := fun a =>
    (QuasiSober.sober a.2.1 (isClosed_of_mem_irreducibleComponents _ a.2)).imp
      fun _ h => isGenericPoint_def.mp h
  choose η hη using hgen
  have hηgen : ∀ a, closure {η a} ∈ irreducibleComponents X := fun a => (hη a).symm ▸ a.2
  choose O hηO hO using fun a =>
    exists_isOpen_isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction Λ F hF (η a)
  choose N hηN hN using fun a => exists_mem_forall_isGeometricallyUnibranchAt hNag (η a) (hηgen a)
  let R : ι → X.Opens := fun a => ⟨(⋃ b ∈ {b : ι | b ≠ a}, (b : Set X))ᶜ,
    (Set.toFinite _).isClosed_biUnion (fun b _ => isClosed_of_mem_irreducibleComponents _ b.2)
      |>.isOpen_compl⟩
  let W : ι → X.Opens := fun a => O a ⊓ N a ⊓ R a
  have hsub : ∀ a b : ι, (a : Set X) ⊆ b → a = b := fun a b h =>
    Subtype.ext (le_antisymm h (a.2.2 b.2.1 h))
  have hηW : ∀ a, η a ∈ W a := by
    intro a
    refine ⟨⟨hηO a, hηN a⟩, fun hb => ?_⟩
    obtain ⟨b, hba, hb⟩ := Set.mem_iUnion₂.1 hb
    refine hba (hsub a b ?_).symm
    rw [← hη a]
    exact closure_minimal (Set.singleton_subset_iff.2 hb)
      (isClosed_of_mem_irreducibleComponents _ b.2)
  have hWsub : ∀ a, (W a : Set X) ⊆ a := by
    intro a y hy
    obtain ⟨-, hyR⟩ := hy
    by_contra hya
    refine hyR (Set.mem_iUnion₂.2 ⟨⟨irreducibleComponent y,
      irreducibleComponent_mem_irreducibleComponents y⟩, fun h => hya ?_, mem_irreducibleComponent⟩)
    rw [← h]
    exact mem_irreducibleComponent
  refine ⟨ι, hfin, W, fun a b hab => ?_, ?_, fun a => ⟨?_, ?_, ?_⟩⟩
  · show Disjoint (W a) (W b)
    rw [disjoint_iff, eq_bot_iff]
    intro y hy
    exact hy.2.2 (Set.mem_iUnion₂.2 ⟨a, hab, hWsub a hy.1⟩)
  · rw [dense_iff_closure_eq, TopologicalSpace.Opens.coe_iSup, Set.eq_univ_iff_forall]
    intro y
    obtain ⟨c, hc, hyc⟩ := Set.mem_sUnion.1
      ((sUnion_irreducibleComponents (X := X)).symm ▸ Set.mem_univ y :
        y ∈ ⋃₀ irreducibleComponents X)
    rw [show c = ((⟨c, hc⟩ : ι) : Set X) from rfl, ← hη ⟨c, hc⟩] at hyc
    exact closure_mono (Set.singleton_subset_iff.2
      (Set.mem_iUnion.2 ⟨⟨c, hc⟩, hηW ⟨c, hc⟩⟩)) hyc
  · exact Subtype.irreducibleSpace
      ⟨⟨η a, hηW a⟩, a.2.1.2.open_subset (W a).isOpen (hWsub a)⟩
  · exact fun y => isGeometricallyUnibranchRing_of_ringEquiv
      ((W a).stalkIso y).symm.commRingCatIsoToRingEquiv (hN a y.1 y.2.1.2)
  · exact hO a (W a) (fun y hy => hy.1.1) ((hη a).symm ▸ hWsub a)

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.LocallyConstantAssembly
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericInduction
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleExhaustion

/-!
# The generic step of the proof of Stacks Tag 03SC

On a reduced separated scheme of finite type and dimension at most one over an algebraically
closed field, let `η` be the generic point of an irreducible component and `G` a constructible
sheaf killed by a prime `ℓ`. There is an open `U ∋ η`, contained in the closure of `η` and in the
smooth locus, on which `G` is finite locally constant (generic local constancy, the hypothesis
`hD1`). `U` is irreducible, hence connected, and smooth over the field, so every scheme étale over
`U` is normal; Tag 03SD (`TorsionCurveAssertions.extensionByZero_of_isFiniteLocallyConstant`) gives
the eight assertions for `j_! j⁻¹ G`. With the Noetherian induction of
`TorsionCurveAssertions.of_genericStep` and the reduction to constructible sheaves killed by a
prime, this proves Tag 03SC from generic local constancy (`hD1`), Tag 0A3R (`h0A3R`) and Tag 0A5B
(`h0A5B`).

## Main results

* `Stacks.EtaleCohomology.TorsionCurveAssertions.of_genericLocalConstancy`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- A dense open subset of a Noetherian space contains the generic point of every irreducible
component. -/
theorem mem_of_dense_of_mem_irreducibleComponents {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] {V : Set α} (hVo : IsOpen V) (hV : Dense V) {η : α}
    (hη : closure {η} ∈ irreducibleComponents α) : η ∈ V := by
  obtain ⟨W, hWo, hηW, hWsub⟩ :=
    exists_isOpen_mem_subset_closure_of_mem_irreducibleComponents hη
  obtain ⟨y, hyW, hyV⟩ := hV.inter_open_nonempty W hWo ⟨η, hηW⟩
  have hsp : η ⤳ y := specializes_iff_mem_closure.mpr (hWsub hyW)
  exact hsp.mem_open hVo hyV

namespace TorsionCurveAssertions

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- **Stacks Tag 03SC for constructible sheaves killed by a prime**, from generic local
constancy, Tag 0A3R and Tag 0A5B. -/
theorem of_genericLocalConstancy
    (hD1 : ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsReduced Y]
      (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}), IsConstructibleSmallEtaleSheaf G →
      ∀ η : Y, closure {η} ∈ irreducibleComponents Y → ∀ N : Set Y, IsOpen N → η ∈ N →
      ∃ U : Y.Opens, η ∈ U ∧ (U : Set Y) ⊆ closure {η} ∧ (U : Set Y) ⊆ N ∧
        Stacks.ConstantSheaf.IsFiniteLocallyConstant (U : Scheme.{u}).smallEtaleTopology
          ((etaleRestriction.{u, u + 1} U.ι).obj G))
    (h0A3R : ∀ {ℓ : ℕ}, ℓ.Prime → ∀ (S : Scheme.{u}) [ConnectedSpace S]
      (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u + 1} (ZMod ℓ))),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) (smallEtaleTopology S) F →
      ∃ (T : Scheme.{u}) (g : T ⟶ S) (d : ℕ), IsFinite g ∧ Etale g ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d ∧ ¬ ℓ ∣ d ∧
        ∃ X : RelSeries (ConstantRankOneStep.{u + 1, u} ℓ
            ((smallEtalePullbackZMod.{u + 1, u} ℓ g).obj F)),
          IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow)
    (h0A5B : ∀ {ℓ : ℕ}, ℓ.Prime → ∀ (Yb : Scheme.{u}) (pY : Yb ⟶ Spec (.of k)) [IsSeparated pY]
      [LocallyOfFiniteType pY] [QuasiCompact pY]
      [HasExt.{u + 1} (Sheaf Yb.smallEtaleTopology AddCommGrpCat.{u + 1})],
      topologicalKrullDim Yb ≤ 1 → IsNormal Yb →
        TorsionCurveAssertions pY (StrongTorsionCurveAssertions.constantZModAb Yb ℓ))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : IsConstructibleSmallEtaleSheaf G)
    (hℓG : ℓ • 𝟙 G = 0) : TorsionCurveAssertions f G := by
  refine of_genericStep (fun Y g _ _ _ _ _ hdimY ℓ hℓ G hG hℓG η hη => ?_) f hdim ℓ hℓ G hG hℓG
  have : IsNoetherian Y := isNoetherian_of_finiteType g
  have : IsLocallyNoetherian (Spec (.of k)) := inferInstance
  have hsmo := g.dense_smoothLocus_of_perfectField
  have hηN : η ∈ (g.smoothLocus : Set Y) :=
    mem_of_dense_of_mem_irreducibleComponents g.smoothLocus.isOpen hsmo hη
  obtain ⟨U, hηU, hUsub, hUN, hlcc⟩ := hD1 Y G hG η hη _ g.smoothLocus.isOpen hηN
  -- `U` is irreducible, hence connected
  have hirr : IsIrreducible (U : Set Y) :=
    ⟨⟨η, hηU⟩, (isIrreducible_singleton.closure.isPreirreducible).open_subset U.isOpen hUsub⟩
  have : IrreducibleSpace (U : Scheme.{u}) := isIrreducible_iff_irreducibleSpace.mp hirr
  have : ConnectedSpace (U : Scheme.{u}) := inferInstance
  -- `U` is smooth over `k`, so its étale covers are normal
  have hsm : Smooth (U.ι ≫ g) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact eq_top_iff.mpr fun x _ => hUN x.2
  have hnormal : ∀ (T : Scheme.{u}) (t : T ⟶ (U : Scheme.{u})), Etale t → IsNormal T := by
    intro T t ht
    have : Smooth (t ≫ U.ι ≫ g) := inferInstance
    exact isNormal_of_isRegular _ (isRegular_of_smooth_over_field (t ≫ U.ι ≫ g))
  refine ⟨U, U.ι, inferInstance, ⟨⟨η, hηU⟩, rfl⟩, ?_⟩
  exact extensionByZero_of_isFiniteLocallyConstant g hdimY hℓ G hℓG U hlcc
    (fun F hF => h0A3R hℓ U F hF) hnormal (fun Yb pY _ _ _ _ h1 h2 => h0A5B hℓ Yb pY h1 h2)

/-- **Stacks Tag 03SC for torsion sheaves**, from generic local constancy, Tag 0A3R and
Tag 0A5B. -/
theorem of_genericLocalConstancy_of_torsion
    (hD1 : ∀ (Y : Scheme.{u}) [IsNoetherian Y] [IsReduced Y]
      (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}), IsConstructibleSmallEtaleSheaf G →
      ∀ η : Y, closure {η} ∈ irreducibleComponents Y → ∀ N : Set Y, IsOpen N → η ∈ N →
      ∃ U : Y.Opens, η ∈ U ∧ (U : Set Y) ⊆ closure {η} ∧ (U : Set Y) ⊆ N ∧
        Stacks.ConstantSheaf.IsFiniteLocallyConstant (U : Scheme.{u}).smallEtaleTopology
          ((etaleRestriction.{u, u + 1} U.ι).obj G))
    (h0A3R : ∀ {ℓ : ℕ}, ℓ.Prime → ∀ (S : Scheme.{u}) [ConnectedSpace S]
      (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u + 1} (ZMod ℓ))),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) (smallEtaleTopology S) F →
      ∃ (T : Scheme.{u}) (g : T ⟶ S) (d : ℕ), IsFinite g ∧ Etale g ∧
        Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d ∧ ¬ ℓ ∣ d ∧
        ∃ X : RelSeries (ConstantRankOneStep.{u + 1, u} ℓ
            ((smallEtalePullbackZMod.{u + 1, u} ℓ g).obj F)),
          IsZero (Subobject.underlying.obj X.head) ∧ IsIso X.last.arrow)
    (h0A5B : ∀ {ℓ : ℕ}, ℓ.Prime → ∀ (Yb : Scheme.{u}) (pY : Yb ⟶ Spec (.of k)) [IsSeparated pY]
      [LocallyOfFiniteType pY] [QuasiCompact pY]
      [HasExt.{u + 1} (Sheaf Yb.smallEtaleTopology AddCommGrpCat.{u + 1})],
      topologicalKrullDim Yb ≤ 1 → IsNormal Yb →
        TorsionCurveAssertions pY (StrongTorsionCurveAssertions.constantZModAb Yb ℓ))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hdim : topologicalKrullDim X ≤ 1) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    TorsionCurveAssertions f F := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  exact of_constructible f (fun ℓ hℓ G hG hℓG =>
    of_genericLocalConstancy hD1 h0A3R h0A5B f hdim ℓ hℓ G hG hℓG) F hF

end TorsionCurveAssertions

end Stacks.EtaleCohomology

end

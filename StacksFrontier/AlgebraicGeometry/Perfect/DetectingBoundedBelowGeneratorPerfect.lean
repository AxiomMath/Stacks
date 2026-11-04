module

public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedAboveGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundedBelowGenerator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.BoundedAboveOnAQuasiCompactSite
public import StacksFrontier.Topology.Sheaves.Cohomology.FilteredColimits.SectionsOverAQuasiCompactOpen

/-!
# Detecting boundedness below with a perfect generator: the steps that use perfectness

Let `X` be a quasi-compact, quasi-separated scheme, let `G` be a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)`, and let `E` be an object of `D_QCoh(𝒪_X)`. This module proves two
steps of [Stacks, Tag 0GEQ] that use the perfectness of `G`.

* The eventual vanishing, as `i → -∞`, of `Ext^i_X(G, E)` agrees with that of
  `H^i(X, G^∨ ⊗^L E)`, the two groups being the same in every degree by
  `Stacks.SheafOfModules.subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect`,
  which takes no hypothesis but perfectness of `G`.
* A bounded-below `E` receives nothing from the shifts `G⟦-i⟧` for `i ≪ 0`, because a perfect
  `G` on a quasi-compact space is bounded above and nothing goes from an object bounded above to
  an object bounded below it.

## Main results

* `Stacks.SheafOfModules.eventually_subsingleton_ext_iff_isZero_homology_atBot`
* `Stacks.SheafOfModules.eventually_subsingleton_shiftedHom_of_plus`

## References

* [Stacks Project, Proposition 36.40.6 (Tag 0GEQ)](https://stacks.math.columbia.edu/tag/0GEQ)
* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- **Stacks 0GEQ, condition (1) implies condition (2).** For a perfect generator `G` of
`D_QCoh(𝒪_X)` on a quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`,
if `E` lies in `D⁺(𝒪_X)` then the groups `Hom_{D(𝒪_X)}(G⟦-i⟧, E)` vanish for `i ≪ 0`.

The source deduces this from Stacks 09M4, but the window of that tag is not needed: `G` is
perfect on a quasi-compact space, hence bounded above by
`AlgebraicGeometry.RingedSite.exists_isLE_of_isPerfect`, say in degrees `≤ b`, so `G⟦-i⟧` is in
degrees `≤ b + i`, while `E` is in degrees `≥ d` for some `d`; and a morphism from an object
bounded above by `b + i` to one bounded below by `d` is zero as soon as `b + i < d`, which is
the case for every `i ≤ d - b - 1`. -/
theorem eventually_subsingleton_shiftedHom_of_plus
    (hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent)
    (hplus : (DerivedCategory.TStructure.t (C := StructureSheafModules X.sheaf)).plus E) :
    ∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ E) := by
  have := hqc
  obtain ⟨d, hd⟩ := hplus
  obtain ⟨b, hb⟩ := AlgebraicGeometry.RingedSite.exists_isLE_of_isPerfect (ringedSite X.sheaf)
    ⊤ isTerminalTop
    (Stacks.Cohomology.Sections.isQuasiCompactObject_of_isCompact ⊤
      (by simpa using isCompact_univ)) G hG
  have : DerivedCategory.IsLE (C := StructureSheafModules X.sheaf) G b := hb
  refine ⟨d - b - 1, fun i hi => ⟨fun u v => ?_⟩⟩
  have : (G⟦-i⟧).IsLE (b + i) :=
    DerivedCategory.TStructure.t.isLE_shift G b (-i) (b + i) (by omega)
  have h := fun w : G⟦-i⟧ ⟶ E => DerivedCategory.TStructure.t.zero_of_isLE_of_isGE w (b + i) d
    (by omega) inferInstance hd
  rw [h u, h v]

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]


variable [∀ V : Opens X.toPresheafedSpace.carrier,
    HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]

/-- **Stacks 0GEQ, conditions (3) and (5).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the groups
`Ext^i_X(G, E)` vanish for `i ≪ 0` exactly when the cohomology groups
`H^i(X, G^∨ ⊗^L_{𝒪_X} E)` do.

The two conditions hold of the same `i`, by
`subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect`. -/
theorem eventually_subsingleton_ext_iff_isZero_homology_atBot
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    (∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G E i)) ↔
      ∃ N : ℤ, ∀ n ≤ N, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) :=
  exists_congr fun _ => forall₂_congr fun i _ =>
    subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect G E hG i

end Stacks.SheafOfModules

end

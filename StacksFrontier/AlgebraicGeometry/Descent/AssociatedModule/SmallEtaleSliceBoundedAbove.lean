module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceConservativity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentObligation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedAboveGeneral
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleImageSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Local boundedness above of a complex with pseudo-coherent étale pullback

Let `S` be a scheme, let `E` be an object of `D(𝒪_S)` and suppose that `ε^*E` is
`m`-pseudo-coherent on the small étale site of `S`, where `ε^*` is
`AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf`. This module shows that **the opens of `S`
on which the cohomology sheaves of `E` restrict to zero in all sufficiently large degrees cover
every open of `S`**.

## Main results

* `AlgebraicGeometry.SmallEtale.exists_opens_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale`:
  around every point of every open of `S` there is an open on which the cohomology of `E`
  vanishes in high degrees.
* `AlgebraicGeometry.SmallEtale.boundedOpens_mem_grothendieckTopology`: those opens cut out a
  covering sieve of every open of `S`.

## References

* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

omit [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))] in
/-- **The bound on an étale object passes to its image open.** If the cohomology sheaf
`H^j(ε^*E)` restricted to an object `T` of the small étale site of `S` vanishes, then its
restriction to `ε(im T)` vanishes too. -/
public theorem isZero_over_opensObj_imageOpen_of_isZero_over
    (T : SmallEtale B S hS) (M : SheafOfModules.{u} (structureSheaf B S hS))
    (h : IsZero (M.over T)) :
    IsZero (M.over ((opensToSmallEtale B S hS).obj (imageOpen B S hS T))) :=
  Stacks.SheafOfModules.isZero_of_coversTop
    (Stacks.SheafOfModules.coversTop_over_of_ofArrows_mem (topology B S hS)
      ((opensToSmallEtale B S hS).obj (imageOpen B S hS T)) (fun _ : Unit => T)
      (fun _ => toImageOpen B S hS T) (ofArrows_toImageOpen_mem_topology B S hS T))
    _ fun _ => Stacks.SheafOfModules.isZero_over_over_of_isZero_over M _ _ h

/-- **Around every point of every open of `S` there is an open on which `E` is bounded above.**
Let `E` be an object of `D(𝒪_S)` whose pullback `ε^*E` is `m`-pseudo-coherent on the small étale
site of `S`. Then every point `x` of every open `U` of `S` lies in an open `V ≤ U` and there is
an integer `b` with `H^j(E)|_V = 0` for every `j > b`. -/
public theorem exists_opens_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) m)
    (U : S.Opens) (x : ↥S) (hx : x ∈ U) :
    ∃ V : S.Opens, V ≤ U ∧ x ∈ V ∧ ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} S.ringCatSheaf) j).obj E)).over V) := by
  obtain ⟨S₀, hS₀, hdata⟩ :=
    AlgebraicGeometry.RingedSite.exists_local_isZero_homology_gt_general
      (smallEtaleRingedSite B S hS)
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) m hE
      ((opensToSmallEtale B S hS).obj U)
  obtain ⟨Z, g, hg, hxZ⟩ := exists_mem_arrows_mem_range B S hS hS₀
    (⟨x, hx⟩ : (toScheme B S hS).obj ((opensToSmallEtale B S hS).obj U))
  obtain ⟨T, q, f₀, hf₀, rfl⟩ := hg
  obtain ⟨b, hb⟩ := hdata f₀ hf₀
  refine ⟨imageOpen B S hS Z, ?_, ?_, b, fun j hj => ?_⟩
  · calc imageOpen B S hS Z ≤ imageOpen B S hS T := imageOpen_le_imageOpen B S hS q
      _ ≤ imageOpen B S hS ((opensToSmallEtale B S hS).obj U) :=
        imageOpen_le_imageOpen B S hS f₀
      _ = U := imageOpen_opensObj B S hS U
  · obtain ⟨z, hz⟩ := hxZ
    refine ⟨z, ?_⟩
    rw [BigEtaleOver.hom_hom_eq B S hS (q ≫ f₀).hom]
    exact congrArg Subtype.val hz
  · exact isZero_homology_over_of_isZero_homology_over_associatedModule B S hS _ E j
      (isZero_over_opensObj_imageOpen_of_isZero_over B S hS Z _
        (Stacks.SheafOfModules.isZero_over_of_hom _ q (hb j hj)))

/-- If `ε^*E` is `m`-pseudo-coherent on the small étale site of `S`, then for every open `U` of
`S` the opens `V` of `S` on which the cohomology sheaves `H^j(E)|_V` vanish for all sufficiently
large `j` generate a covering sieve of `U` in the Zariski topology. -/
public theorem boundedOpens_mem_grothendieckTopology
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (m : ℤ)
    (hE : (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) m)
    (U : S.Opens) :
    Sieve.ofObjects
      (Subtype.val : {V : S.Opens // ∃ b : ℤ, ∀ j : ℤ, b < j →
        IsZero ((((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} S.ringCatSheaf) j).obj E)).over V)} → S.Opens) U ∈
      Opens.grothendieckTopology ↥S U := by
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V, hVU, hxV, b, hb⟩ :=
    exists_opens_isZero_homology_gt_of_isPseudoCoherentFromSmallEtale B S hS E m hE U x hx
  exact ⟨V, homOfLE hVU, ⟨⟨V, b, hb⟩, ⟨𝟙 _⟩⟩, hxV⟩

end AlgebraicGeometry.SmallEtale

end

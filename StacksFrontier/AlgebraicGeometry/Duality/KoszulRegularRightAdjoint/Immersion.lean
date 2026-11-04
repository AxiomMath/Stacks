module

public import StacksFrontier.AlgebraicGeometry.Conormal.KoszulRank
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulRegularRightAdjoint.TopDegree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.Flat
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence

/-!
# The twisted inverse image of the structure sheaf along a Koszul-regular closed immersion

Let `i : Z ⟶ X` be a Koszul-regular closed immersion of schemes with `X` quasi-compact and
quasi-separated, whose conormal sheaf is finite locally free of rank `r`, and let `c` be the right
adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_X)`. Then

`c(𝒪_X) ≅ ⋀ʳ 𝒩[-r]`

in `D(𝒪_Z)`, where `𝒩` is the normal sheaf of `i`.

## Main results

* `Stacks.Duality.KoszulRegular.exists_koszulPresentation_of_isKoszulRegularImmersion`: the
  defining ideal has, near every point of `Z`, a Koszul-regular presentation of length `r`.
* `Stacks.Duality.KoszulRegular.twistedInverseImageIsoOfIsKoszulRegularImmersion`:
  `⋀ʳ 𝒩[-r] ≅ c(𝒪_X)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Duality.KoszulRegular

open Stacks.AlgebraicGeometry.RegularIdealSheaf

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **A Koszul-regular closed immersion whose conormal sheaf has constant rank `r` has
Koszul-regular presentations of length `r` near every point of the support.** -/
theorem exists_koszulPresentation_of_isKoszulRegularImmersion
    (hi : IsKoszulRegularImmersion i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := Z.ringCatSheaf)
      (Stacks.Conormal.conormalSheaf i) r] :
    ∀ x ∈ idealQuotientSupport X.toRingedSpace (idealOf i),
      ∃ d : KoszulPresentation X.toRingedSpace (idealOf i), x ∈ d.U ∧ d.r = r := by
  intro x hx
  have hxr : x ∈ Set.range i.base := by
    by_contra h
    exact notMem_idealQuotientSupport_definingIdealOfHom_of_notMem_closure i x
      (by rwa [i.isClosedEmbedding.isClosed_range.closure_eq]) hx
  obtain ⟨z, rfl⟩ := hxr
  have hcob : i.base z ∈ i.coborderRange := by
    rw [Stacks.Divisors.coborderRange_eq_top i]
    trivial
  have hz : i.liftCoborder.base z = ⟨i.base z, hcob⟩ :=
    Subtype.ext (congrArg (fun g : Z ⟶ X => g.base z) i.liftCoborder_ι)
  obtain ⟨W, hzW, c, f, hK, hG⟩ :=
    (isKoszulRegularImmersion_iff i _ (restrictSubmodule_coborderRange_definingIdealOfHom i)).mp
      hi ⟨i.base z, hcob⟩
      ((mem_idealQuotientSupport_restrictSubmodule_iff _ _ _).mpr hx)
  have hrank : c = r :=
    Stacks.Conormal.eq_rank_of_isKoszulSequenceExactOn i r z W (hz ▸ hzW) f hK
      (restrictSubmodule_coborderRange_definingIdealOfHom i ▸ hG)
  exact ⟨⟨imOpen _ W, c, f, (isKoszulSequenceExactOn_restrict_iff _ W f _).mp hK,
    (isGeneratedByOn_restrictSubmodule_iff _ _ W f).mp hG⟩, ⟨⟨i.base z, hcob⟩, hzW, rfl⟩, hrank⟩

/-- **`c(𝒪_X) ≅ ⋀ʳ 𝒩[-r]`** for a Koszul-regular closed immersion `i : Z ⟶ X` with `X`
quasi-compact and quasi-separated whose conormal sheaf is finite locally free of rank `r`, where
`c` is the right adjoint of `Ri_*` on `D_QCoh` and `𝒩` is the normal sheaf of `i`. -/
def twistedInverseImageIsoOfIsKoszulRegularImmersion [CompactSpace X] [QuasiSeparatedSpace X]
    (hpush : ∀ (K : quasiCoherentDerivedCategory Z) (n : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules n).obj
        ((derivedPushforward i).obj K.obj)).IsQuasicoherent)
    [(quasiCoherentDerivedPushforward i hpush).IsLeftAdjoint]
    (hi : IsKoszulRegularImmersion i) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := Z.ringCatSheaf)
      (Stacks.Conormal.conormalSheaf i) r] :
    (DerivedCategory.singleFunctor Z.Modules r).obj
        (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) r) ≅
      ((twistedInverseImage i hpush).obj
        (DerivedPushforward.derivedStructureSheaf X)).obj :=
  haveI := perfect_of_isKoszulRegularImmersion i hi
  twistedInverseImageIso i inferInstance
    (exists_koszulPresentation_of_isKoszulRegularImmersion i hi r)

end Stacks.Duality.KoszulRegular

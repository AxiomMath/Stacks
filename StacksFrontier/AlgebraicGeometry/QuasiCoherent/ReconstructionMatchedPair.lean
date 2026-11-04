module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionTargetAffine

/-!
# Gabriel–Rosenberg reconstruction for a matched pair of opens

Let `X` and `Y` be quasi-compact and quasi-separated schemes and `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` an
equivalence.  Let `U ⊆ X` be an *affine* open and `V ⊆ Y` a quasi-compact open whose closed
complements `Z` and `T` are matched by `e`, in the sense that `e` carries the quasi-coherent
modules supported on `Z` onto those supported on `T`.  This file puts **steps 6, 7 and 8** of
[Stacks, Tag 0GPJ] together for that pair: `V` is affine and there are

* an equivalence `F_U : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` with
  `e.functor ⋙ (restriction to V) ≅ (restriction to U) ⋙ F_U`,
* an isomorphism of schemes `f_U : V ≅ U`, and
* an invertible sheaf `L_U` of `𝒪_V`-modules

such that `F_U` is inverse image along `f_U` followed by `- ⊗_{𝒪_V} L_U`.

Step 6 is `AlgebraicGeometry.exists_isEquivalence_restrictionSquare`, step 7 is
`AlgebraicGeometry.isAffine_of_supportedCorrespondence`, and step 8 is the affine case of
[Stacks, Tag 0GPJ],
`AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence`, applied to
`F_U`.  As in the affine case the comparison of functors is stated after forgetting
quasi-coherence, between functors into all `𝒪_V`-modules.

## Main results

* `AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_supportedCorrespondence` — **steps 6, 7
  and 8** with the matched pair `(U, V)` given.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Steps 6, 7 and 8 of [Stacks, Tag 0GPJ] -/

section Reconstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

section Matched

variable (Z : Set X) (T : Set Y)
  (hcorr : ∀ E, quasicoherentSupportedOn X Z E ↔
    quasicoherentSupportedOn Y T (e.functor.obj E))

include e hcorr

/-- **Steps 6, 7 and 8 of [Stacks, Tag 0GPJ] together, for a matched pair of opens.**  Let `X` and
`Y` be quasi-compact and quasi-separated schemes and `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` an equivalence.
Let `U ⊆ X` be an *affine* open and `V ⊆ Y` a quasi-compact open whose closed complements `Z` and
`T` are matched by `e`, in the sense that `e` carries the quasi-coherent modules supported on `Z`
onto those supported on `T`.  Then `V` is affine and there are

* an equivalence `F_U : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` with
  `e.functor ⋙ (restriction to V) ≅ (restriction to U) ⋙ F_U`,
* an isomorphism of schemes `f_U : V ≅ U`, and
* an invertible sheaf `L_U` of `𝒪_V`-modules

such that `F_U` is inverse image along `f_U` followed by `- ⊗_{𝒪_V} L_U`. -/
theorem exists_schemeIso_invertibleSheaf_of_supportedCorrespondence (U : X.Opens)
    (hUZ : (U : Set X) = Zᶜ) (hU : IsCompact (U : Set X)) (hUaff : IsAffineOpen U) (V : Y.Opens)
    (hVT : (V : Set Y) = Tᶜ) (hV : IsCompact (V : Set Y)) :
    IsAffine V.toScheme ∧
      ∃ (F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
          (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory)
        (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf),
        F.IsEquivalence ∧
          Stacks.SheafOfModules.IsInvertible V.toScheme.presheaf V.toScheme.ringCatSheaf.2 L ∧
          Nonempty (e.functor ⋙ quasicoherentRestriction V.ι ≅
            quasicoherentRestriction U.ι ⋙ F) ∧
          Nonempty (F ⋙ ObjectProperty.ι
              (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
            pullbackTensorFunctor f.hom L) := by
  have : IsAffine U.toScheme := hUaff
  have : IsAffine V.toScheme :=
    isAffine_of_supportedCorrespondence e Z T hcorr U hUZ hU hUaff V hVT hV
  refine ⟨inferInstance, ?_⟩
  obtain ⟨F, hF, ⟨sq⟩⟩ :=
    exists_isEquivalence_restrictionSquare e Z T hcorr U hUZ hU V hVT hV
  have := hF
  obtain ⟨f, L, hL, ⟨i⟩⟩ := exists_schemeIso_invertibleSheaf_of_quasicoherentEquivalence F
  exact ⟨F, f, L, hF, hL, ⟨sq⟩, ⟨i⟩⟩

end Matched

end Reconstruction

end AlgebraicGeometry

end

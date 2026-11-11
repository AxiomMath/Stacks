module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionMatchedPair

/-!
# Gabriel–Rosenberg reconstruction localized at one affine open

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  Let `U ⊆ X` be an affine open and let `G` be a
finitely presented quasi-coherent `𝒪_X`-module whose support is the complement of `U`.  This
file runs **steps 3 to 8** of [Stacks, Tag 0GPJ] at that one open: the matched open `V ⊆ Y` is
produced rather than hypothesised, being the complement of the support of `e.functor.obj G`, and
it is quasi-compact (**step 4**) and affine (**step 7**), with an equivalence
`F_U : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` compatible with `e` and the two restrictions (**step 6**), an
isomorphism of schemes `f_U : V ≅ U` and an invertible sheaf `L_U` of `𝒪_V`-modules such that
`F_U` is inverse image along `f_U` followed by `- ⊗_{𝒪_V} L_U` (**step 8**).

The matching hypothesis that
`AlgebraicGeometry.exists_schemeIso_invertibleSheaf_of_supportedCorrespondence`
consumes is discharged by [Stacks, Tag 0GPG] in the form
`AlgebraicGeometry.quasicoherentSupportedOn_supportSet_correspondence`, and quasi-compactness of
`V` by `AlgebraicGeometry.isCompact_compl_supportSet`.

What is *not* here is the production of `G` — step 2 — nor the covering assertion, which is the
business of `StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionGlobalForm.lean`.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_schemeIso_invertibleSheaf_of_isFinitePresentation` —
  **steps 3 to 8** with only `U` and `G` given, `V` being produced.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.3 (Tag 0GPG)](https://stacks.math.columbia.edu/tag/0GPG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

section Reconstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

/-- **Stacks Project, Tag 0GPJ, steps 3 to 8: the local form of the proposition.**  Let `X` and
`Y` be quasi-compact and quasi-separated schemes and let `e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an
equivalence.  Let `U ⊆ X` be an affine open and let `G` be a finitely presented quasi-coherent
`𝒪_X`-module whose support is the complement of `U`.  Then there is a quasi-compact open
`V ⊆ Y` — namely the complement of the support of `e.functor.obj G` — which is affine, and there
are an equivalence `F_U : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` compatible with `e` and the two restrictions, an
isomorphism of schemes `f_U : V ≅ U` and an invertible sheaf `L_U` of `𝒪_V`-modules such that
`F_U` is inverse image along `f_U` followed by `- ⊗_{𝒪_V} L_U`. -/
theorem exists_isAffineOpen_schemeIso_invertibleSheaf_of_isFinitePresentation (U : X.Opens)
    (hUaff : IsAffineOpen U)
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj]
    (hG : supportSet G.obj = (U : Set X)ᶜ) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ IsCompact (V : Set Y) ∧
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
  have hfp : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) (e.functor.obj G).obj :=
    isFinitePresentation_map_of_equivalence e G
  have hqc : ((e.functor.obj G).obj).IsQuasicoherent := (e.functor.obj G).property
  have hft : ((e.functor.obj G).obj).IsFiniteType := inferInstance
  have hV : IsCompact (supportComplement (e.functor.obj G).obj : Set Y) :=
    isCompact_compl_supportSet (e.functor.obj G).obj
  have hUZ : (U : Set X) = (supportSet G.obj)ᶜ := by rw [hG, compl_compl]
  obtain ⟨haff, hrest⟩ := exists_schemeIso_invertibleSheaf_of_supportedCorrespondence e
    (supportSet G.obj) (supportSet (e.functor.obj G).obj)
    (quasicoherentSupportedOn_supportSet_correspondence e G) U hUZ hUaff.isCompact hUaff
    (supportComplement (e.functor.obj G).obj) (coe_supportComplement _) hV
  exact ⟨supportComplement (e.functor.obj G).obj, haff, hV, hrest⟩

end Reconstruction

end AlgebraicGeometry

end

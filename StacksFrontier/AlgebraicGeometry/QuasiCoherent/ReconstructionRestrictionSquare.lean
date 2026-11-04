module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ModuleSupportComplement
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.SupportedSerreEquivalence
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.InverseImage

/-!
# The restriction square of Gabriel–Rosenberg reconstruction

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence.  This file carries out **step 6** of
[Stacks, Tag 0GPJ]: for quasi-compact opens `U ⊆ X` and `V ⊆ Y` whose closed complements `Z` and
`T` are *matched* by `e` — meaning `e` carries the quasi-coherent modules supported on `Z` onto
those supported on `T` — the equivalence descends to an equivalence
`F_U : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` fitting in a commuting square with the two restrictions.

Both restrictions are Serre localizations by [Stacks, Tag 0GPH], so the matching of the Serre
subcategories makes `e.functor` a morphism of localizers between them and the descended functor
is the localized functor of that morphism.  Also recorded here is the form of
[Stacks, Tag 0GPG] that supplies the matching hypothesis in practice: the complement of the
support of a finitely presented quasi-coherent module `G` on `X` is matched with the complement
of the support of `e.functor.obj G`.

## Implementation notes

The matching of Serre subcategories is an equality of classes of *objects*, while a morphism of
localizers wants an equality of classes of *morphisms*; the bridge is
`CategoryTheory.ObjectProperty.isoModSerre_eq_inverseImage_of_iff`, and
`CategoryTheory.ObjectProperty.isLocalizedEquivalence_localizerMorphismOfIff` then makes the
induced functor an equivalence.  The square is `CategoryTheory.LocalizerMorphism.catCommSq`.

The result is stated as an existential rather than as a named functor.  The induced functor is
`CategoryTheory.LocalizerMorphism.localizedFunctor`, whose elaboration consumes the two
`CategoryTheory.Functor.IsLocalization` instances supplied by [Stacks, Tag 0GPH] and the two
exactness instances of `e.functor`; naming it would force those instance arguments to be matched
again at every use, and nothing downstream needs the functor to be a particular term.

## Main results

* `AlgebraicGeometry.quasicoherentSupportedOn_supportSet_correspondence` — [Stacks, Tag 0GPG] in
  the form the localization step consumes.
* `AlgebraicGeometry.exists_isEquivalence_restrictionSquare` — **step 6**.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
* [Stacks Project, Lemma 56.6.3 (Tag 0GPG)](https://stacks.math.columbia.edu/tag/0GPG)
* [Stacks Project, Lemma 56.6.4 (Tag 0GPH)](https://stacks.math.columbia.edu/tag/0GPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Step 6 of [Stacks, Tag 0GPJ] -/

section Reconstruction

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)

/-- **[Stacks, Tag 0GPG] in the form the localization step consumes.**  For a finitely presented
quasi-coherent module `G` on `X`, the equivalence `e` matches the Serre subcategory of modules
supported on the support of `G` with the Serre subcategory of modules supported on the support of
`e.functor.obj G`.  This is `AlgebraicGeometry.isSupportedOn_map_equivalence_iff` read through
`AlgebraicGeometry.quasicoherentSupportedOn_supportSet`. -/
theorem quasicoherentSupportedOn_supportSet_correspondence
    (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj]
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    quasicoherentSupportedOn X (supportSet G.obj) E ↔
      quasicoherentSupportedOn Y (supportSet (e.functor.obj G).obj) (e.functor.obj E) :=
  (isSupportedOn_map_equivalence_iff e G E).symm

section Matched

variable (Z : Set X) (T : Set Y)
  (hcorr : ∀ E, quasicoherentSupportedOn X Z E ↔
    quasicoherentSupportedOn Y T (e.functor.obj E))

include e hcorr

/-- **Step 6 of [Stacks, Tag 0GPJ].**  Let `U ⊆ X` and `V ⊆ Y` be quasi-compact opens with closed
complements `Z` and `T`, and suppose the equivalence `e` matches the quasi-coherent modules
supported on `Z` with those supported on `T`.  Then there is an equivalence
`F_U : QCoh(𝒪_U) ≌ QCoh(𝒪_V)` and a commuting square
`e.functor ⋙ (restriction to V) ≅ (restriction to U) ⋙ F_U`.

Both restrictions are Serre localizations by [Stacks, Tag 0GPH], and the matching of the Serre
subcategories makes `e.functor` a morphism of localizers between them, by
`CategoryTheory.ObjectProperty.localizerMorphismOfIff`. -/
theorem exists_isEquivalence_restrictionSquare (U : X.Opens) (hUZ : (U : Set X) = Zᶜ)
    (hU : IsCompact (U : Set X)) (V : Y.Opens) (hVT : (V : Set Y) = Tᶜ)
    (hV : IsCompact (V : Set Y)) :
    ∃ F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
        (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory,
      F.IsEquivalence ∧
        Nonempty (e.functor ⋙ quasicoherentRestriction V.ι ≅
          quasicoherentRestriction U.ι ⋙ F) := by
  have hloc₁ := quasicoherentRestriction_isLocalization X Z U hUZ hU
  have hloc₂ := quasicoherentRestriction_isLocalization Y T V hVT hV
  set Φ := ObjectProperty.localizerMorphismOfIff (P := quasicoherentSupportedOn X Z)
    (Q := quasicoherentSupportedOn Y T) e.functor hcorr with hΦ
  have hΦeq : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_localizerMorphismOfIff e.functor hcorr
  refine ⟨Φ.localizedFunctor (quasicoherentRestriction U.ι) (quasicoherentRestriction V.ι),
    inferInstance, ⟨?_⟩⟩
  exact CatCommSq.iso Φ.functor (quasicoherentRestriction U.ι)
    (quasicoherentRestriction V.ι) _

end Matched

end Reconstruction

end AlgebraicGeometry

end

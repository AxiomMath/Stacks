module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TruncationQuasiIso

/-!
# The truncation map of a complex of abelian sheaves becomes a quasi-isomorphism

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF].  This module is the
argument of [Stacks, Proposition 60.23.1, Tag 07LM] for the leading assertion, isolated from any
particular complex and read on complexes of abelian **sheaves** on `Cris(X/S)`.

Let `C` be a cochain complex of abelian sheaves on `Cris(X/S)` concentrated in nonnegative
degrees, `D` a complex concentrated in degree zero, and `σ : C ⟶ D` a map of complexes whose
degree-zero component is an isomorphism.  If `Ru_{X/S, *}` kills `C^n` for every `n ≥ 1`, then
`σ` becomes an isomorphism of `D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}`.

The proof is the source's: `σ` sits in the degreewise split short exact sequence
`0 ⟶ σ^{≥1}C ⟶ C ⟶ D ⟶ 0`, hence in a distinguished triangle of `K⁺(Ab(Cris(X/S)))` by
[Stacks, Tag 0118], which `DerivedCategory.Plus.Qh` and the exact functor `Ru_{X/S, *}` carry to a
distinguished triangle of `D⁺(Ab(X_{Zar}))`.  Its first vertex is `Ru_{X/S, *}(σ^{≥1}C)`, which
vanishes by Leray's acyclicity lemma [Stacks, Tag 015E]; a distinguished triangle whose first
vertex is zero has an invertible second map.

`...SmallSite.isIso_derivedZariskiDirectImageFunctor_map_abelianPlusTruncation` of
`SmallSite/TruncationQuasiIso.lean` is the same argument for a complex of abelian *presheaves*,
sheafified termwise; the version here is the one to use when the differentials of the complex are
available only as maps of sheaves, which is the case for the de Rham complex of a crystal that is
not the structure sheaf.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `sheafTruncGE` — the brutal truncation `σ^{≥1}C`.
* `sheafShortComplex` and `sheafSplitting` — the short complex `0 ⟶ σ^{≥1}C ⟶ C ⟶ D ⟶ 0` and its
  degreewise splitting.
* `sheafPlusTruncation` — the map `σ`, read in `C⁺(Ab(Cris(X/S)))`.
* `sheafTrianglePlus` and `sheafTrianglePlus_distinguished` — the triangle it generates.

## Main results

* `isIso_derivedZariskiDirectImageFunctor_map_sheafPlusTruncation` — the conclusion above.

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable (S : GlobalCrystallineSituation.{u})
  (C D : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ)
  [C.IsStrictlyGE 0] [D.IsStrictlyGE 0] (σ : C ⟶ D)

namespace SmallSite

section SheafTruncation

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

open Pretriangulated

attribute [local instance] crysCommShiftDerivedZariskiDirectImageFunctor
  crysIsTriangulatedDerivedZariskiDirectImageFunctor crysAdditiveDerivedZariskiDirectImage

/-- **The brutal truncation `σ^{≥1}C`.**  It is the third vertex of the triangle of the truncation
map, and the vanishing hypothesis is exactly that `Ru_{X/S, *}` kills each of its terms. -/
def sheafTruncGE : CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ :=
  C.stupidTrunc (ComplexShape.embeddingUpIntGE 1)

/-- The brutal truncation `σ^{≥1}C` is strictly concentrated in degrees `≥ 1`. -/
instance sheafTruncGE_isStrictlyGE : (sheafTruncGE S C).IsStrictlyGE 1 :=
  inferInstanceAs ((C.stupidTrunc
    (ComplexShape.embeddingUpIntGE 1)).IsStrictlySupported (ComplexShape.embeddingUpIntGE 1))

/-- **The short complex `0 ⟶ σ^{≥1}C ⟶ C ⟶ D ⟶ 0`**, whose second map is `σ`. -/
def sheafShortComplex (hD : ∀ n : ℤ, n ≠ 0 → IsZero (D.X n)) :
    ShortComplex (CochainComplex (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) ℤ) :=
  ShortComplex.mk (HomologicalComplex.ιStupidTrunc C (ComplexShape.embeddingUpIntGE 1)) σ (by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    by_cases hn : n = 0
    · subst hn
      exact (CochainComplex.isZero_of_isStrictlyGE (sheafTruncGE S C) 1 0
        (by omega)).eq_of_src _ _
    · exact (hD n hn).eq_of_tgt _ _)

/-- **The short complex is degreewise split.**  In degree zero its first term vanishes and its
second map is `σ⁰`, which is assumed invertible; in a degree `≥ 1` its first map is an identity
and its last term vanishes; in a negative degree everything vanishes. -/
noncomputable def sheafSplitting (hD : ∀ n : ℤ, n ≠ 0 → IsZero (D.X n)) (hσ : IsIso (σ.f 0))
    (n : ℤ) :
    ((sheafShortComplex S C D σ hD).map (HomologicalComplex.eval _ _ n)).Splitting := by
  by_cases hn : n = 0
  · subst hn
    exact ShortComplex.Splitting.ofIsZeroOfIsIso _
      (CochainComplex.isZero_of_isStrictlyGE (sheafTruncGE S C) 1 0 (by omega)) hσ
  · refine ShortComplex.Splitting.ofIsIsoOfIsZero _ ?_ (hD n hn)
    by_cases hn1 : (1 : ℤ) ≤ n
    · exact HomologicalComplex.isIso_ιStupidTrunc_f _ _ (i := (n - 1).toNat)
        (by change (1 : ℤ) + ((n - 1).toNat : ℤ) = n; omega)
    · exact IsZero.isIso
        (CochainComplex.isZero_of_isStrictlyGE (sheafTruncGE S C) 1 n (by omega))
        (CochainComplex.isZero_of_isStrictlyGE C 0 n (by omega)) _

/-! #### The distinguished triangle of the truncation map -/

/-- `σ^{≥1}C`, read as a bounded below complex. -/
def sheafPlusTruncGE : CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ⟨sheafTruncGE S C, ⟨1, inferInstance⟩⟩

/-- `C`, read as a bounded below complex. -/
def sheafPlusComplex : CochainComplex.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  ⟨C, ⟨0, inferInstance⟩⟩

/-- **`σ`, read in `C⁺(Ab(Cris(X/S)))`.** -/
def sheafPlusTruncation : sheafPlusComplex S C ⟶ sheafPlusComplex S D :=
  ObjectProperty.homMk σ

/-- The inclusion `σ^{≥1}C ⟶ C`, in `C⁺(Ab(Cris(X/S)))`. -/
def sheafPlusIota : sheafPlusTruncGE S C ⟶ sheafPlusComplex S C :=
  ObjectProperty.homMk (HomologicalComplex.ιStupidTrunc C (ComplexShape.embeddingUpIntGE 1))

/-- **The triangle `σ^{≥1}C ⟶ C ⟶ D ⟶ (σ^{≥1}C)⟦1⟧` of `K⁺(Ab(Cris(X/S)))`** attached to the
degreewise split short exact sequence `sheafShortComplex`. -/
noncomputable def sheafTrianglePlus (hD : ∀ n : ℤ, n ≠ 0 → IsZero (D.X n))
    (hσ : IsIso (σ.f 0)) :
    Triangle (HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) :=
  Triangle.mk
    ((HomotopyCategory.Plus.quotient _).map (sheafPlusIota S C))
    ((HomotopyCategory.Plus.quotient _).map (sheafPlusTruncation S C D σ))
    (ObjectProperty.homMk
      ((CochainComplex.trianglehOfDegreewiseSplit (sheafShortComplex S C D σ hD)
          (sheafSplitting S C D σ hD hσ)).mor₃ ≫
        ((HomotopyCategory.Plus.ι _).commShiftIso (1 : ℤ)).inv.app
          ((HomotopyCategory.Plus.quotient _).obj (sheafPlusTruncGE S C))))

omit [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] in
/-- **The triangle of the truncation map is distinguished in `K⁺`**, by [Stacks, Tag 0118] and the
fact that `K⁺ ⥤ K` is fully faithful and triangulated. -/
theorem sheafTrianglePlus_distinguished (hD : ∀ n : ℤ, n ≠ 0 → IsZero (D.X n))
    (hσ : IsIso (σ.f 0)) :
    sheafTrianglePlus S C D σ hD hσ ∈
      distTriang (HomotopyCategory.Plus (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})) := by
  rw [← Functor.map_distinguished_iff (HomotopyCategory.Plus.ι _)]
  refine isomorphic_distinguished _
    (CochainComplex.trianglehOfDegreewiseSplit_distinguished (sheafShortComplex S C D σ hD)
      (sheafSplitting S C D σ hD hσ)) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  iterate 2 exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have h : (CategoryTheory.shiftFunctor
        (HomotopyCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ)) (1 : ℤ)).map
          (Iso.refl ((HomotopyCategory.Plus.ι _).mapTriangle.obj
            (sheafTrianglePlus S C D σ hD hσ)).obj₁).hom = 𝟙 _ := by simp
    refine (congrArg (_ ≫ ·) h).trans ((Category.comp_id _).trans ?_)
    refine Eq.trans ?_ (Category.id_comp _).symm
    simp only [sheafTrianglePlus, Functor.mapTriangle, Triangle.mk_mor₃]
    exact (Category.assoc _ _ _).trans
      ((congrArg _ (Iso.inv_hom_id_app _ _)).trans (Category.comp_id _))

omit [C.IsStrictlyGE 0] in
/-- Under the vanishing hypothesis, `Ru_{X/S, *}` kills every term of `σ^{≥1}C`. -/
theorem isZero_derivedZariskiDirectImage_sheafTruncGE_X
    (hV : ∀ n : ℤ, 1 ≤ n → IsZero ((derivedZariskiDirectImage S).obj (C.X n))) (n : ℤ) :
    IsZero ((derivedZariskiDirectImage S).obj ((sheafTruncGE S C).X n)) := by
  by_cases hn : (1 : ℤ) ≤ n
  · refine IsZero.of_iso (hV n hn) ((derivedZariskiDirectImage S).mapIso ?_)
    exact HomologicalComplex.stupidTruncXIso C (ComplexShape.embeddingUpIntGE 1)
      (i := (n - 1).toNat) (by change (1 : ℤ) + ((n - 1).toNat : ℤ) = n; omega)
  · exact Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE
      (sheafTruncGE S C) 1 n (by omega))

/-- **The leading assertion of [Stacks, Tag 07LM] for a complex of abelian sheaves.**  Let `C` be
a cochain complex of abelian sheaves on `Cris(X/S)` concentrated in nonnegative degrees, `D` a
complex concentrated in degree zero, and `σ : C ⟶ D` a map of complexes whose degree-zero
component is an isomorphism.  If `Ru_{X/S, *}` kills `C^n` for every `n ≥ 1`, then `σ` becomes an
isomorphism of `D⁺(Ab(X_{Zar}))` after `Ru_{X/S, *}`.

The proof is the source's; see the module documentation.  No tag attribute is placed: this is the
source's derivation read at a generality the tag does not state. -/
theorem isIso_derivedZariskiDirectImageFunctor_map_sheafPlusTruncation
    (hD : ∀ n : ℤ, n ≠ 0 → IsZero (D.X n)) (hσ : IsIso (σ.f 0))
    (hV : ∀ n : ℤ, 1 ≤ n → IsZero ((derivedZariskiDirectImage S).obj (C.X n))) :
    IsIso ((derivedZariskiDirectImageFunctor S).map
      (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.quotient _).map (sheafPlusTruncation S C D σ)))) := by
  have hT := (derivedZariskiDirectImageFunctor S).map_distinguished _
    (DerivedCategory.Plus.Qh.map_distinguished _
      (sheafTrianglePlus_distinguished S C D σ hD hσ))
  refine (Triangle.isZero₁_iff_isIso₂ _ hT).1 ?_
  exact isZero_derivedZariskiDirectImageFunctor_obj_of_termwise S (sheafPlusTruncGE S C)
    (isZero_derivedZariskiDirectImage_sheafTruncGE_X S C hV)

end SheafTruncation

end SmallSite

end Crystalline.GlobalCrystallineSituation

end

end

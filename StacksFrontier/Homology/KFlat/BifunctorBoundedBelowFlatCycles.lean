module

public import StacksFrontier.Homology.KFlat.BifunctorTruncationGE
public import StacksFrontier.Homology.KFlat.Flat

/-!
# Bounded below complexes whose terms and cycles are flat

Let `F : A ⥤ B ⥤ D` be a bifunctor which is additive in each variable, let `Φ : C ⥤ B` be an
additive functor out of an abelian category which commutes with sequential colimits, and let
`K` be a cochain complex of `C` which is strictly bounded below. If every term `Kᵠ` and every
cycle object `Zᵠ(K)` becomes, after `Φ` and placed in a single degree, a complex which is
K-flat for `F`, then the complex `Φ(K)` is K-flat for `F`.

## Main results

* `CochainComplex.KFlatBifunctor.kFlat_mapHomologicalComplex_of_isStrictlyGE`: if `K` is
  strictly bounded below and each `Φ(Kᵠ)` and each `Φ(Zᵠ(K))`, placed in degree `q`, is K-flat
  for `F`, then `Φ(K)` is K-flat for `F`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.KFlatBifunctor

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Preadditive A] [Abelian B] [Abelian C] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]

variable [∀ K : HomologicalComplex₂ D (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    K.HasTotal (ComplexShape.up ℤ)]
  [HasColimitsOfShape ℕ B] [HasColimitsOfShape ℕ C] [HasColimitsOfShape ℕ D]

omit [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
    (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
    K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)] in
/-- **A strictly bounded below complex whose terms and cycles are flat gives a K-flat complex.**
Let `Φ : C ⥤ B` be additive and commute with sequential colimits, and let `K` be a complex of
`C` which is strictly bounded below. If each `Φ(Kᵠ)` and each `Φ(Zᵠ(K))`, placed in degree `q`,
is K-flat for `F`, then `Φ(K)` is K-flat for `F`. Here `hF` says that `F` commutes with
sequential colimits in its second variable and `hexact` that sequential colimits are exact in
`D`. -/
theorem kFlat_mapHomologicalComplex_of_isStrictlyGE (Φ : C ⥤ B) [Φ.Additive]
    [PreservesColimitsOfShape ℕ Φ] (K : CochainComplex C ℤ) (a : ℤ) [K.IsStrictlyGE a]
    (hF : ∀ X : A, PreservesColimitsOfShape ℕ (F.obj X))
    (hexact : ∀ (E : ℕ ⥤ CochainComplex D ℤ) (s : Cocone E), IsColimit s →
      (∀ i, (E.obj i).Acyclic) → s.pt.Acyclic)
    (hterm : ∀ q : ℤ, KFlat F ((single B (ComplexShape.up ℤ) q).obj (Φ.obj (K.X q))))
    (hcyc : ∀ q : ℤ, KFlat F ((single B (ComplexShape.up ℤ) q).obj (Φ.obj (K.cycles q)))) :
    KFlat F ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have : PreservesColimitsOfShape ℕ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)) :=
    ⟨fun {_} ↦ CochainComplex.KFlat.preservesColimit_mapHomologicalComplex _ Φ⟩
  refine kFlat_of_isColimit F _ (isColimitOfPreserves (Φ.mapHomologicalComplex _)
    (CochainComplex.KFlat.truncLECocone_isColimit K)) hF hexact (fun n ↦ ?_)
  show KFlat F ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.truncLE (n : ℤ)))
  refine kFlat_of_isStrictlyLE_of_isStrictlyGE F _ (n : ℤ) a (fun q ↦ ?_)
  rcases lt_trichotomy q (n : ℤ) with hq | rfl | hq
  · exact (hterm q).of_iso F ((single B (ComplexShape.up ℤ) q).mapIso
      (Φ.mapIso (K.truncLEXIso (n : ℤ) q hq)).symm)
  · exact (hcyc _).of_iso F ((single B (ComplexShape.up ℤ) _).mapIso
      (Φ.mapIso (K.truncLEXIsoCycles (n : ℤ))).symm)
  · exact kFlat_single_of_isZero F
      (((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.truncLE (n : ℤ))).X q)
      (CochainComplex.isZero_of_isStrictlyLE _ (n : ℤ) q hq) q

end CochainComplex.KFlatBifunctor

end

module

public import StacksFrontier.Algebra.Homology.TriangleOfSESHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.Interface

/-!
# The connecting morphism of the extension of a short exact sequence of `ℕ`-indexed complexes

## Main results

* `extendedHomologyIso_conj_mapExtendTriangleδ`: conjugating by
  `Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` the connecting morphism of
  the derived-category triangle of the degreewise image of a sequence of complexes gives the
  snake-lemma connecting morphism of that sequence.  This discharges the first two of the three
  pieces described below.

The first two of the three pieces this field was once reduced to, which split along the factors
of
`Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso`, are

1. the snake-lemma connecting morphism of a short exact sequence of cochain complexes against
   the connecting morphism of its distinguished triangle in the derived category —
   `DerivedCategory.homologySequenceδ_triangleOfSES` of
   `StacksFrontier.Algebra.Homology.TriangleOfSESHomology`, and
   `extendedHomologyIso` literally contains the `DerivedCategory.homologyFunctorFactors` that
   lemma is stated with;
2. compatibility of
   `Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyTailIso` with the connecting
   morphism, i.e. the connecting morphism of the `ℤ`-extension of a short exact sequence of
   `ℕ`-indexed complexes against that of the sequence itself —
   `extendedHomologyTailIso_hom_δ`.

The passage from `D⁺(ℬ)` to `D(ℬ)` is made through the fully faithful inclusion
`DerivedCategory.Plus.ι`, which is forced: `DerivedCategory.triangleOfSESδ` lives in `D(ℬ)`, and
`extendedHomologyIso_conj_mapExtendTriangleδ` — pieces 1 and 2 — is stated with
`DerivedCategory.homologyFunctor`, so the comparison cannot be kept inside `D⁺(ℬ)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.Cohomology.HigherDirectImagePresheaf

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- `n` and `n + 1`, as degrees of a cochain complex of abelian groups indexed by `ℤ`, are
adjacent.  This is the spelling of the degree hypothesis that
`CategoryTheory.ShortComplex.ShortExact.δ` asks for; the equality form `↑n + 1 = ↑(n + 1)` is
definitionally the same but does not re-elaborate, so every declaration below uses this one
term. -/
theorem up_rel_natCast_succ (n : ℕ) :
    (ComplexShape.up ℤ).Rel (n : ℤ) ((n + 1 : ℕ) : ℤ) := by
  simp [ComplexShape.up_Rel]

/-- **Applying `F` degreewise and extending by zero commute, as an isomorphism of short
complexes.**  The components are `derivedMapExtendIso`, and the two squares commute by
`derivedMapExtendIso_naturality`. -/
noncomputable def mapExtendShortComplexIso (R : ShortComplex (CochainComplex A ℕ)) :
    (R.map (ComplexShape.embeddingUpNat.extendFunctor A)).map
        (F.mapHomologicalComplex (ComplexShape.up ℤ)) ≅
      (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).map
        (ComplexShape.embeddingUpNat.extendFunctor B) :=
  ShortComplex.isoMk (derivedMapExtendIso F ComplexShape.embeddingUpNat R.X₁)
    (derivedMapExtendIso F ComplexShape.embeddingUpNat R.X₂)
    (derivedMapExtendIso F ComplexShape.embeddingUpNat R.X₃)
    (derivedMapExtendIso_naturality F R.f).symm (derivedMapExtendIso_naturality F R.g).symm

omit [HasDerivedCategory B] in
/-- **If `F` applied degreewise keeps a short complex of `ℕ`-indexed complexes short exact, then
so does extending it to `ℤ` and then applying `F` degreewise.**  `F` itself need not be exact:
the hypothesis is the conclusion for the `ℕ`-indexed sequence, which in the application holds
because the sequence of injective resolutions is split in each degree. -/
theorem shortExact_mapExtend {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) :
    ((R.map (ComplexShape.embeddingUpNat.extendFunctor A)).map
      (F.mapHomologicalComplex (ComplexShape.up ℤ))).ShortExact :=
  ShortComplex.shortExact_of_iso (mapExtendShortComplexIso F R).symm
    (ComplexShape.embeddingUpNat.shortExact_map_extendFunctor hFR)

/-- The snake-lemma connecting morphism of `shortExact_mapExtend`, with its source and target
spelled through the complexes themselves rather than through the projections of the short
complex.  The two spellings are definitionally equal, but only this one is syntactically the
one `extendedHomologyTailIso` and `extendedHomologyIso` present, and reassociating a composite
across the difference defeats both `rw` and `simp`. -/
noncomputable def mapExtendδ {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (R.X₃.extend ComplexShape.embeddingUpNat)).homology (n : ℤ) ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (R.X₁.extend ComplexShape.embeddingUpNat)).homology ((n + 1 : ℕ) : ℤ) :=
  (shortExact_mapExtend F hFR).δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (up_rel_natCast_succ n)

/-- The connecting morphism in cohomology of `DerivedCategory.triangleOfSES` of
`shortExact_mapExtend`, with its source and target spelled through the complexes rather than
through `CategoryTheory.Pretriangulated.Triangle.obj₁` and `.obj₃`.  The two spellings are
definitionally equal, but `CategoryTheory.Functor.mapTriangle` and
`CategoryTheory.Pretriangulated.Triangle.mk` are semireducible, so the projections do not
reduce in a rewrite motive.  **This morphism is the target of the remaining obligation.** -/
noncomputable def mapExtendTriangleδ {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).obj
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (R.X₃.extend ComplexShape.embeddingUpNat))) ⟶
      (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).obj
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (R.X₁.extend ComplexShape.embeddingUpNat))) :=
  DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES (shortExact_mapExtend F hFR))
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (up_rel_natCast_succ n)

omit [HasDerivedCategory B] in
/-- **`extendedHomologyTailIso` carries the connecting morphism of the extended sequence to the
connecting morphism of the `ℕ`-indexed one.**  This is the second of the three pieces of the
`derivedδ_eq` obligation: `extendedHomologyTailIso` is `derivedMapExtendIso` followed by
`HomologicalComplex.extendHomologyIso`, and the two factors are discharged respectively by
`HomologicalComplex.HomologySequence.δ_naturality` and by
`HomologicalComplex.HomologySequence.δ_extendFunctor`. -/
theorem extendedHomologyTailIso_hom_δ {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    (extendedHomologyTailIso F R.X₃ n).hom ≫ hFR.δ n (n + 1) rfl =
      mapExtendδ F hFR n ≫ (extendedHomologyTailIso F R.X₁ (n + 1)).hom := by
  have p2 := HomologicalComplex.HomologySequence.δ_naturality
    (mapExtendShortComplexIso F R).hom (shortExact_mapExtend F hFR)
    (ComplexShape.embeddingUpNat.shortExact_map_extendFunctor hFR)
    (n : ℤ) ((n + 1 : ℕ) : ℤ) (up_rel_natCast_succ n)
  have p3 := HomologicalComplex.HomologySequence.δ_extendFunctor
    (C := B) ComplexShape.embeddingUpNat hFR (i := n) (j := n + 1) rfl
    (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) (by simp) (by simp) (up_rel_natCast_succ n)
  have t₁ : (mapExtendShortComplexIso F R).hom.τ₁ =
      (derivedMapExtendIso F ComplexShape.embeddingUpNat R.X₁).hom := rfl
  have t₃ : (mapExtendShortComplexIso F R).hom.τ₃ =
      (derivedMapExtendIso F ComplexShape.embeddingUpNat R.X₃).hom := rfl
  rw [t₁, t₃] at p2
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at p2 p3
  simp only [extendedHomologyTailIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [Category.assoc, ← p3]
  exact (Category.assoc _ _ _).symm.trans ((p2.symm =≫ _).trans (Category.assoc _ _ _))

/-- The transport step of `extendedHomologyIso_conj_mapExtendTriangleδ`: given that a morphism
`d` of the derived category induces `mapExtendδ` on cohomology, conjugating it by
`extendedHomologyIso` gives the connecting morphism of the `ℕ`-indexed sequence.  Stated with
`d` as a variable because the hypothesis has to be rewritten by `extendedHomologyTailIso_hom_δ`
and reassociated, which is impossible while the connecting morphism of a triangle — whose
source and target do not reduce — sits in the composite. -/
private theorem extendedHomologyIso_conj_of_factors
    {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ)
    (d : (DerivedCategory.homologyFunctor B (n : ℤ)).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (R.X₃.extend ComplexShape.embeddingUpNat)))) ⟶
        (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (R.X₁.extend ComplexShape.embeddingUpNat)))))
    (hd : (DerivedCategory.homologyFunctor B (n : ℤ)).map
            ((DerivedCategory.quotientCompQhIso B).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (R.X₃.extend ComplexShape.embeddingUpNat))) ≫
          (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (R.X₃.extend ComplexShape.embeddingUpNat)) ≫
          (homologyFunctorObjIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (R.X₃.extend ComplexShape.embeddingUpNat)) (n : ℤ)).hom ≫
          mapExtendδ F hFR n =
        d ≫ (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
            ((DerivedCategory.quotientCompQhIso B).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (R.X₁.extend ComplexShape.embeddingUpNat))) ≫
          (DerivedCategory.homologyFunctorFactors B ((n + 1 : ℕ) : ℤ)).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (R.X₁.extend ComplexShape.embeddingUpNat)) ≫
          (homologyFunctorObjIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (R.X₁.extend ComplexShape.embeddingUpNat)) ((n + 1 : ℕ) : ℤ)).hom) :
    (extendedHomologyIso F R.X₃ n).inv ≫ d ≫ (extendedHomologyIso F R.X₁ (n + 1)).hom =
      hFR.δ n (n + 1) rfl := by
  rw [Iso.inv_comp_eq]
  simp only [extendedHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc]
  rw [extendedHomologyTailIso_hom_δ F hFR n]
  have key := hd =≫ (extendedHomologyTailIso F R.X₁ (n + 1)).hom
  simp only [Category.assoc] at key
  exact key.symm

/-- **Pieces 1 and 2 of the `derivedδ_eq` obligation, assembled.**  Conjugating by
`extendedHomologyIso` the connecting morphism of the derived-category triangle attached to the
degreewise-`F` image of the extended sequence gives the connecting morphism of the `ℕ`-indexed
sequence.

The first factor of `extendedHomologyIso` is `DerivedCategory.quotientCompQhIso`, which is
cancelled against the two explicit occurrences here; the second is
`DerivedCategory.homologyFunctorFactors`, handled by
`DerivedCategory.homologySequenceδ_triangleOfSES`; the last two are handled by
`extendedHomologyTailIso_hom_δ`. -/
theorem extendedHomologyIso_conj_mapExtendTriangleδ
    {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    (extendedHomologyIso F R.X₃ n).inv ≫
        ((DerivedCategory.homologyFunctor B (n : ℤ)).map
            ((DerivedCategory.quotientCompQhIso B).hom.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (R.X₃.extend ComplexShape.embeddingUpNat))) ≫
          mapExtendTriangleδ F hFR n ≫
          (DerivedCategory.homologyFunctor B ((n + 1 : ℕ) : ℤ)).map
            ((DerivedCategory.quotientCompQhIso B).inv.app
              ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
                (R.X₁.extend ComplexShape.embeddingUpNat)))) ≫
        (extendedHomologyIso F R.X₁ (n + 1)).hom =
      hFR.δ n (n + 1) rfl := by
  refine extendedHomologyIso_conj_of_factors F hFR n _ ?_
  have p1 : (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (R.X₃.extend ComplexShape.embeddingUpNat)) ≫ mapExtendδ F hFR n =
        mapExtendTriangleδ F hFR n ≫
          (DerivedCategory.homologyFunctorFactors B ((n + 1 : ℕ) : ℤ)).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (R.X₁.extend ComplexShape.embeddingUpNat)) :=
    DerivedCategory.homologySequenceδ_triangleOfSES (shortExact_mapExtend F hFR)
      (n : ℤ) ((n + 1 : ℕ) : ℤ) (up_rel_natCast_succ n)
  have e₃ : (homologyFunctorObjIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (R.X₃.extend ComplexShape.embeddingUpNat)) (n : ℤ)).hom ≫ mapExtendδ F hFR n =
      mapExtendδ F hFR n := Category.id_comp _
  have e₁ : (DerivedCategory.homologyFunctorFactors B ((n + 1 : ℕ) : ℤ)).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (R.X₁.extend ComplexShape.embeddingUpNat)) ≫
        (homologyFunctorObjIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (R.X₁.extend ComplexShape.embeddingUpNat)) ((n + 1 : ℕ) : ℤ)).hom =
      (DerivedCategory.homologyFunctorFactors B ((n + 1 : ℕ) : ℤ)).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (R.X₁.extend ComplexShape.embeddingUpNat)) := Category.comp_id _
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact whisker_eq _ ((whisker_eq _ e₃).trans (p1.trans (whisker_eq _ e₁.symm)))

/-! ### The remaining obligation, reduced to a single commuting square -/

section Comparison

variable [HasDerivedCategory A] [EnoughInjectives A] {M : A}

/-- **The derived-category half of `derivedPlusResolutionHomologyIso`, before taking
cohomology.**  It compares `RF(M[0])` with the image under `RF`'s unit of the extension of the
injective resolution `I`; `derivedPlusResolutionHomologyIso` is this isomorphism with
`DerivedCategory.Plus.homologyFunctor` applied, which holds by `rfl`
(`derivedPlusResolutionHomologyIso_hom`). -/
noncomputable def derivedPlusResolutionIso (I : InjectiveResolution M) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).obj
        ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I)) :=
  F.rightDerivedFunctorPlus.mapIso (resolutionDerivedIso I) ≪≫
    (asIso (F.rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I)))).symm

/-- **`RF(M[0])`, read in the full derived category `D(ℬ)`, against `Q` of the degreewise
`F`-image of the extension of the injective resolution `I`.**  This is `derivedPlusResolutionIso`
pushed along the fully faithful inclusion `DerivedCategory.Plus.ι` and composed with
`DerivedCategory.quotientCompQhIso`.

The composite is given a name of its own, with its source and target written out, because the
two factors meet at an object presented as `DerivedCategory.Plus.ι.obj (Plus.Qh.obj _)` on one
side and as `DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj _)` on the other;
across that junction neither `rw` nor `simp` fires, and the index of
`DerivedCategory.quotientCompQhIso` is spelled through `HomotopyCategory.Plus.ι` unless it is
pinned here. -/
noncomputable def resolutionDerivedComparison (I : InjectiveResolution M) :
    DerivedCategory.Plus.ι.obj (F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj M)) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat)) :=
  DerivedCategory.Plus.ι.mapIso (derivedPlusResolutionIso F I) ≪≫
    (DerivedCategory.quotientCompQhIso B).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat))

/-- The two factors of `resolutionDerivedComparison`. -/
theorem resolutionDerivedComparison_hom (I : InjectiveResolution M) :
    (resolutionDerivedComparison F I).hom =
      DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I).hom ≫
        ((DerivedCategory.quotientCompQhIso B).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat))).hom := rfl

/-- The two factors of the inverse of `resolutionDerivedComparison`. -/
theorem resolutionDerivedComparison_inv (I : InjectiveResolution M) :
    (resolutionDerivedComparison F I).inv =
      ((DerivedCategory.quotientCompQhIso B).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (I.cocomplex.extend ComplexShape.embeddingUpNat))).inv ≫
        DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I).inv := rfl

/-- `derivedPlusResolutionHomologyIso` is `derivedPlusResolutionIso` with cohomology applied,
read in the full derived category. -/
theorem derivedPlusResolutionHomologyIso_hom (I : InjectiveResolution M) (n : ℕ) :
    (derivedPlusResolutionHomologyIso F I n).hom =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I).hom) := rfl

/-- The inverse form of `derivedPlusResolutionHomologyIso_hom`. -/
theorem derivedPlusResolutionHomologyIso_inv (I : InjectiveResolution M) (n : ℕ) :
    (derivedPlusResolutionHomologyIso F I n).inv =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (DerivedCategory.Plus.ι.map (derivedPlusResolutionIso F I).inv) := rfl

end Comparison

omit [HasDerivedCategory B] in
/-- The connecting morphism of `DerivedCategory.triangleOfSES` of `shortExact_mapExtend`, with
source and target spelled through the complexes rather than through the projections of the short
complex.  Named for the same reason as `mapExtendTriangleδ`: the two spellings are definitionally
equal, but `CategoryTheory.ShortComplex.map` does not reduce in a rewrite motive, so an equation
stated at the unnamed spelling defeats `rw`. -/
noncomputable def mapExtendSESδ [HasDerivedCategory B] {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (R.X₃.extend ComplexShape.embeddingUpNat)) ⟶
      (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (R.X₁.extend ComplexShape.embeddingUpNat)))⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ (shortExact_mapExtend F hFR)

/-- `mapExtendTriangleδ` is `Functor.shiftMap` of `mapExtendSESδ`: `DerivedCategory.Plus` is not
involved, and `DerivedCategory.HomologySequence.δ` of a triangle is by definition
`Functor.shiftMap` of its third morphism. -/
theorem mapExtendTriangleδ_eq {R : ShortComplex (CochainComplex A ℕ)}
    (hFR : (R.map (F.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact) (n : ℕ) :
    mapExtendTriangleδ F hFR n =
      (DerivedCategory.homologyFunctor B 0).shiftMap (mapExtendSESδ F hFR)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) := rfl

end Stacks.Cohomology.HigherDirectImagePresheaf

end

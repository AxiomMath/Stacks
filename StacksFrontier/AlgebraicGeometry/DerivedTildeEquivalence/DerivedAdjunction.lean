module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.AbsoluteRightDerived

/-!
# The derived adjunction of an exact left adjoint and the right derived functor of its adjoint

Let `adj : F ⊣ G` be an adjunction of additive functors between abelian categories with `F`
exact, so that `F` induces a functor `LF` on unbounded derived categories, and suppose every
cochain complex in the target admits a quasi-isomorphism into a K-injective complex, so that `G`
has an unbounded right derived functor `RG`. Then `LF ⊣ RG`, and the unit of this adjunction is
the degreewise unit of `adj` followed by the canonical comparisons.

This is the mechanism behind the affine derived Spec–Γ equivalence (Stacks 06Z0): there `F` is
sheafification `M ↦ M̃`, `G` is global sections, `LF` is derived sheafification and `RG` is
derived global sections.

Mathlib's `CategoryTheory.Adjunction.derived` does the work, once three things are supplied: the
adjunction read on homotopy categories, which is the localization of the degreewise adjunction
along the quotient functors; the fact that `LF` is the left derived functor of its degreewise
functor, which holds because the comparison is an isomorphism; and absoluteness of `RG`, which is
`Stacks.SmallDerivedCategory.isRightDerivedFunctor_comp_of_exists_quasiIso_isKInjective`.

## Main definitions

* `Stacks.SmallDerivedCategory.homotopyAdjunction` — `adj` read on homotopy categories.
* `Stacks.SmallDerivedCategory.rightDerivedComparisonQ` — the comparison
  `Q(G(K)) ⟶ RG(Q(K))` on cochain complexes.
* `Stacks.SmallDerivedCategory.derivedAdjunction` — the adjunction `LF ⊣ RG`.

## Main results

* `Stacks.SmallDerivedCategory.derivedAdjunction_unit_app_Q` — the normalization of the derived
  unit on the image of a cochain complex.

## Implementation notes

Everything is stated for abstract abelian categories rather than for sheaves of modules. That is
not only for generality: `(Spec R).Modules` and `SheafOfModules (Spec R).ringCatSheaf` are
definitionally equal but not at the transparency `rw` uses to build its motive, so a diagram
chase performed directly on the derived sheafification data fails to typecheck where it mentions
the quasi-coherent-cohomology subcategory. Chasing in the abstract setting and instantiating
afterwards avoids this, and needs no `backward.isDefEq.respectTransparency` override.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Stacks.SmallDerivedCategory

section Squares

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] {C₂ : Type*} [Category* C₂]
  [Preadditive C₂] (F : C₁ ⥤ C₂) [F.Additive]

/-- The square relating the degreewise and the homotopy-category extensions of an additive
functor; it is `CategoryTheory.Functor.mapHomotopyCategoryFactors`. -/
instance catCommSq_mapHomologicalComplex :
    CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ))
      (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ))
      (F.mapHomotopyCategory (ComplexShape.up ℤ)) :=
  ⟨(F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm⟩

end Squares

variable {C₁ : Type*} [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type*} [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
  {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive] (adj : F ⊣ G)

/-- An adjunction of additive functors between abelian categories, read on the homotopy
categories of cochain complexes: it is the localization of the degreewise adjunction along the
quotient functors, which are the localizations at the homotopy equivalences. -/
def homotopyAdjunction :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⊣ G.mapHomotopyCategory (ComplexShape.up ℤ) :=
  (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences C₁ (ComplexShape.up ℤ))
    (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ))
    (HomologicalComplex.homotopyEquivalences C₂ (ComplexShape.up ℤ)) _ _

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] in
/-- The unit of `homotopyAdjunction` on the image of a cochain complex `M` is the image of the
degreewise unit of `adj` at `M`, followed by the comparisons for `G` and `F`. -/
lemma homotopyAdjunction_unit_app_quotient (M : CochainComplex C₁ ℤ) :
    (homotopyAdjunction adj).unit.app
        ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M) =
      (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M) ≫
        ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app M) :=
  Adjunction.localization_unit_app _ _ _ _ _ _ _ M

section

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {LF : DerivedCategory C₁ ⥤ DerivedCategory C₂} (e : LF ≅ F.mapDerivedCategory)

/-- The comparison exhibiting `LF` as the functor induced by `F` on the homotopy category. -/
def leftDerivedFactorsQh :
    DerivedCategory.Qh ⋙ LF ≅ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  isoWhiskerLeft DerivedCategory.Qh e ≪≫ F.mapDerivedCategoryFactorsh

/-- The comparison exhibiting `LF` as the functor induced by `F` degreewise. -/
def leftDerivedFactorsQ :
    DerivedCategory.Q ⋙ LF ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  isoWhiskerLeft DerivedCategory.Q e ≪≫ F.mapDerivedCategoryFactors

/-- The degreewise and homotopy-category comparisons for `LF` agree, in the sense that both
compute the image under `LF` of the identification of `Q` with `quotient ⋙ Qh`. -/
lemma leftDerivedFactorsQ_hom_app (M : CochainComplex C₁ ℤ) :
    LF.map ((DerivedCategory.quotientCompQhIso C₁).hom.app M) ≫
        (leftDerivedFactorsQ e).hom.app M =
      (leftDerivedFactorsQh e).hom.app ((HomotopyCategory.quotient _ _).obj M) ≫
        DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M) ≫
        (DerivedCategory.quotientCompQhIso C₂).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
  dsimp only [leftDerivedFactorsQ, leftDerivedFactorsQh, Iso.trans_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerLeft_app]
  rw [Functor.mapDerivedCategoryFactorsh_hom_app, NatTrans.naturality_assoc]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

end

section

variable {RG : DerivedCategory C₂ ⥤ DerivedCategory C₁}
  (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)

/-- The comparison from the complex of `G`-sections of a cochain complex to the right derived
functor `RG` evaluated on the complex it represents. -/
def rightDerivedComparisonQ :
    G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RG :=
  whiskerLeft _ (DerivedCategory.quotientCompQhIso C₁).inv ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv) DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    whiskerLeft (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)) β ≫
    (Functor.associator _ _ _).inv ≫
    whiskerRight (DerivedCategory.quotientCompQhIso C₂).hom RG

/-- The component of `rightDerivedComparisonQ β` at a cochain complex `K` is the comparison for
`G` on `K`, followed by `β` at the image of `K` in the homotopy category, conjugated by the
identifications of `Q` with `quotient ⋙ Qh`. -/
lemma rightDerivedComparisonQ_app (K : CochainComplex C₂ ℤ) :
    (rightDerivedComparisonQ β).app K =
      (DerivedCategory.quotientCompQhIso C₁).inv.app _ ≫
        DerivedCategory.Qh.map
          ((G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
        β.app ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj K) ≫
        RG.map ((DerivedCategory.quotientCompQhIso C₂).hom.app K) := by
  simp [rightDerivedComparisonQ]

end

/-! ### The derived adjunction -/

section

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {LF : DerivedCategory C₁ ⥤ DerivedCategory C₂} (e : LF ≅ F.mapDerivedCategory)
  {RG : DerivedCategory C₂ ⥤ DerivedCategory C₁}
  (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RG)

/-- `LF` is the left derived functor of the functor induced by `F` on the homotopy category:
the comparison is an isomorphism, `F` being exact. -/
instance isLeftDerivedFunctor_leftDerivedFactorsQh :
    Functor.IsLeftDerivedFunctor LF (leftDerivedFactorsQh e).hom
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (leftDerivedFactorsQh e)

/-- `LF ⋙ RG` is the left derived functor of `F_K ⋙ Qh ⋙ RG`, again because the comparison
for `LF` is an isomorphism. This is the absoluteness hypothesis on the left-hand side of
`CategoryTheory.Adjunction.derived`. -/
instance isLeftDerivedFunctor_leftDerivedFactorsQh_comp :
    Functor.IsLeftDerivedFunctor (LF ⋙ RG)
      ((Functor.associator _ _ _).inv ≫ whiskerRight (leftDerivedFactorsQh e).hom RG)
      (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (leftDerivedFactorsQh e) RG)

variable (hC₂ : ∀ K : CochainComplex C₂ ℤ, ∃ (I : CochainComplex C₂ ℤ) (f : K ⟶ I),
    I.IsKInjective ∧ QuasiIso f)
  [RG.IsRightDerivedFunctor β (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ))]

include hC₂ in
/-- `RG ⋙ LF` is the right derived functor of `G_K ⋙ Qh ⋙ LF`: a right derived functor
computed by K-injective resolutions is absolute. This is the absoluteness hypothesis on the
right-hand side of `CategoryTheory.Adjunction.derived`. -/
theorem isRightDerivedFunctor_comp_leftDerived :
    Functor.IsRightDerivedFunctor (RG ⋙ LF)
      (whiskerRight β LF ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_comp_of_exists_quasiIso_isKInjective hC₂ _ _ _ _

/-- **The derived adjunction.** Let `adj : F ⊣ G` be an adjunction of additive functors between
abelian categories with `F` exact, let `LF` be the induced functor on unbounded derived
categories and `RG` the unbounded right derived functor of `G`, which exists because every
complex in `C₂` admits a quasi-isomorphism into a K-injective complex. Then `LF ⊣ RG`. -/
def derivedAdjunction : LF ⊣ RG :=
  haveI := isRightDerivedFunctor_comp_leftDerived (LF := LF) β hC₂
  (homotopyAdjunction adj).derived
    (HomotopyCategory.quasiIso C₁ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso C₂ (ComplexShape.up ℤ)) (leftDerivedFactorsQh e).hom β

/-- The unit of the derived adjunction, on the image of an object of the homotopy category, is
the unit of `adj` read on the homotopy category followed by the comparison for `RG`. -/
lemma derivedAdjunction_unit_app_Qh (X : HomotopyCategory C₁ (ComplexShape.up ℤ)) :
    (derivedAdjunction adj e β hC₂).unit.app (DerivedCategory.Qh.obj X) ≫
        RG.map ((leftDerivedFactorsQh e).hom.app X) =
      DerivedCategory.Qh.map ((homotopyAdjunction adj).unit.app X) ≫
        β.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X) := by
  have := isRightDerivedFunctor_comp_leftDerived (LF := LF) β hC₂
  dsimp only [derivedAdjunction]
  rw [Adjunction.derived_unit]
  exact Adjunction.derivedη_fac_app _ _ _ _ X

omit [HasDerivedCategory C₁] [HasDerivedCategory C₂] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] in
/-- The unit of `homotopyAdjunction` on the image of a cochain complex, with the comparison for
`F` moved to the other side. -/
lemma homotopyAdjunction_unit_app_quotient' (M : CochainComplex C₁ ℤ) :
    (HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M) ≫
        (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
      (homotopyAdjunction adj).unit.app
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M) ≫
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M) := by
  rw [homotopyAdjunction_unit_app_quotient adj M]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The normalization of the derived unit.** On the image of a cochain complex `M`, the unit of
`derivedAdjunction` is the degreewise unit of `adj` followed by the comparison for `RG`, read
through the comparison for `LF`. This equation determines the derived adjunction, hence also its
counit. -/
lemma derivedAdjunction_unit_app_Q (M : CochainComplex C₁ ℤ) :
    (derivedAdjunction adj e β hC₂).unit.app (DerivedCategory.Q.obj M) ≫
        RG.map ((leftDerivedFactorsQ e).hom.app M) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M) ≫
        (rightDerivedComparisonQ β).app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) := by
  have hnat := (derivedAdjunction adj e β hC₂).unit.naturality
    ((DerivedCategory.quotientCompQhIso C₁).hom.app M)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C₁).hom.app M), ← Category.assoc, hnat,
    Category.assoc, ← Functor.map_comp, leftDerivedFactorsQ_hom_app e M,
    rightDerivedComparisonQ_app]
  have hβ : β.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M)) ≫
        RG.map (DerivedCategory.Qh.map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M)) =
      DerivedCategory.Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app M)) ≫
        β.app ((HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
    (β.naturality _).symm
  have hq : DerivedCategory.Q.map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M) ≫
        (DerivedCategory.quotientCompQhIso C₁).inv.app
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) =
      (DerivedCategory.quotientCompQhIso C₁).inv.app M ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).map
          ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M)) :=
    DerivedCategory.quotientCompQhIso_inv_naturality _
  rw [reassoc_of% hq, Iso.hom_inv_id_app_assoc,
    Functor.map_comp, Functor.map_comp]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (derivedAdjunction_unit_app_Qh adj e β hC₂
    ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj M)), reassoc_of% hβ]
  simp only [← Functor.map_comp_assoc]
  rw [homotopyAdjunction_unit_app_quotient' adj M]

end

end Stacks.SmallDerivedCategory

end

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitOfComplexesByPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek computed by a point resolution, at abelian coefficients

Let `C` be a small category with the chaotic topology and let `U_•` be a cosimplicial object of
`C` which is a point resolution. This file proves the **derived** form of [Stacks, Tag 08Q9] at
abelian-group coefficients:

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(Ab)`, naturally in the abelian presheaf `ℱ`,

where `ℱ(U_•)` is the Moore complex of the simplicial abelian group obtained by evaluating `ℱ` on
`U_•`, read as a cochain complex over `ℤ` with the simplicial degree `n` in cohomological degree
`-n`, and `Lπ_!` is the total left derived functor of the colimit over `Cᵒᵖ`.

The degreewise statement — `L_nπ_!(ℱ) = H_n(ℱ(U_•))` for each `n` — is
`Stacks.ChaoticSite.leftDerivedColimitNatIso`; it determines only the cohomology of the two sides,
whereas the isomorphism here is one of functors to `D(Ab)`.

## Main definitions

* `Stacks.ChaoticSite.AbelianValued.mooreCochainComplex`: the Moore complex of `ℱ(U_•)` as a
  cochain complex over `ℤ`, functorially in `ℱ`.
* `Stacks.ChaoticSite.AbelianValued.mooreCochainAugmentation`: its augmentation to
  `(colim ℱ)[0]`, as a natural transformation.
* `Stacks.ChaoticSite.AbelianValued.mooreBicomplex` and
  `Stacks.ChaoticSite.AbelianValued.mooreBicomplexFunctor`: the double complex
  `Z^{p,q} = (K^p(U_•))^q` of a complex of abelian presheaves, as a functor of that complex.
* `Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitOfResolution`: the comparison
  `Q(Tot(Z_K)) ≅ Lπ_!(K^•)` attached to a resolution of a bounded above complex `K^•`.

## Main results

* `Stacks.ChaoticSite.AbelianValued.quasiIso_mooreCochainAugmentation`: for a projective abelian
  presheaf the extended Moore complex of `ℱ(U_•)` is a resolution of `colim ℱ`.
* `Stacks.ChaoticSite.AbelianValued.quasiIso_mooreBicomplexColumnTotalMap` and
  `Stacks.ChaoticSite.AbelianValued.quasiIso_mooreBicomplexTotalMap`: the two filtrations of the
  double complex.
* `Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitOfResolution_naturality_of_epi`: the
  comparison is natural in the complex when the chosen resolution of the target is degreewise
  epimorphic.
* `Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimit`: **the derived form of
  [Stacks, Tag 08Q9] at abelian coefficients, as an isomorphism of functors.**

## Implementation notes

The isomorphism is obtained by comparing the two filtrations of the double complex
`Z^{p,q} = (K^p(U_•))^q` obtained by evaluating a projective resolution `K^•` of `ℱ` on `U_•`.
The Moore-cochain constructions are instances of those of
`Stacks.ChaoticSite.GeneralValued.mooreCochainComplex`, stated for an arbitrary abelian category
of coefficients.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
* [Stacks Project, Tag 0649](https://stacks.math.columbia.edu/tag/0649)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology StacksDraft.TotalComplexQuasiIso

namespace Stacks.ChaoticSite.AbelianValued

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The Moore complex of `ℱ(U_•)` as a cochain complex over `ℤ` -/

section MooreCochain

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The Moore complex of `ℱ(U_•)` read as a cochain complex over `ℤ`**, the simplicial degree
`n` sitting in cohomological degree `-n`. This is
`Stacks.ChaoticSite.GeneralValued.mooreCochainComplex` at abelian-group coefficients: the
reindexing along `ComplexShape.embeddingUpIntLE 0` of
`Stacks.ChaoticSite.cosimplicialMooreComplex`. -/
abbrev mooreCochainComplex :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  GeneralValued.mooreCochainComplex U AddCommGrpCat.{u}

end MooreCochain

/-! ### The augmentation of the extended Moore complex -/

section Augmentation

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  (F : Cᵒᵖ ⥤ AddCommGrpCat.{u})

/-- **The augmentation `ℱ(U_•) ⟶ (colim ℱ)[0]`**, as a natural transformation of functors of the
abelian presheaf `ℱ`: in degree zero it is the colimit injection at `U_0`. This is
`Stacks.ChaoticSite.GeneralValued.mooreCochainAugmentation` at abelian-group coefficients. -/
abbrev mooreCochainAugmentation :
    mooreCochainComplex U ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) ⋙
        HomologicalComplex.single AddCommGrpCat.{u} (ComplexShape.up ℤ) 0 :=
  GeneralValued.mooreCochainAugmentation U

/-- **For a projective abelian presheaf the extended Moore complex of `ℱ(U_•)` is a resolution of
`colim ℱ`**, when `U_•` is a point resolution. -/
lemma quasiIso_mooreCochainAugmentation (hU : IsPointResolution U) [Projective F] :
    QuasiIso ((mooreCochainAugmentation U).app F) :=
  GeneralValued.quasiIso_mooreCochainAugmentation U F
    (fun n => isZero_cosimplicialHomology_projective_succ U hU n F)
    (colimitι_isColimit U hU F)

end Augmentation

/-! ### The double complex of a complex of abelian presheaves -/

section Bicomplex

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The double complex of a complex of abelian presheaves, as a functor of that complex**:
`Z^{p,q} = (K^p(U_•))^q`, whose column `p` is the extended Moore complex of `K^p(U_•)` and whose
row `q` is `K^•(U_{-q})`. -/
abbrev mooreBicomplexFunctor : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ ⥤
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreCochainComplex U).mapHomologicalComplex (ComplexShape.up ℤ)

variable (P : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ)

/-- **The double complex obtained by evaluating a complex of abelian presheaves on the
cosimplicial object `U_•`.** -/
abbrev mooreBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreBicomplexFunctor U).obj P

/-- **The columnwise augmentation of the double complex**, `Z ⟶ (colim K^•)[0]`: in each column
it is the augmentation `K^p(U_•) ⟶ (colim K^p)[0]` of the extended Moore complex. -/
abbrev mooreBicomplexColumnMap :
    mooreBicomplex U P ⟶
      singleRowZero
        (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  (NatTrans.mapHomologicalComplex (mooreCochainAugmentation U) (ComplexShape.up ℤ)).app P

/-- **The first filtration of the double complex**: for a bounded above complex of projective
abelian presheaves the columnwise augmentation is a quasi-isomorphism on total complexes, so
`Tot(Z) ≃ colim K^•`. This is [Stacks, Tag 0133] for double complexes bounded above, with the
hypothesis on the columns. -/
lemma quasiIso_mooreBicomplexColumnTotalMap (hU : IsPointResolution U)
    [P.IsStrictlyLE 0] [∀ n, Projective (P.X n)] :
    QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) :=
  GeneralValued.quasiIso_mooreBicomplexColumnTotalMap U P
    fun p => quasiIso_mooreCochainAugmentation U (P.X p) hU

/-- **The second filtration of the double complex, for an arbitrary quasi-isomorphism of bounded
above complexes**: a quasi-isomorphism `K^• ⟶ L^•` induces a quasi-isomorphism on the total
complexes of the associated double complexes. This is [Stacks, Tag 0133] with the hypothesis on
the rows. -/
lemma quasiIso_mooreBicomplexTotalMap {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f)
      (ComplexShape.up ℤ)) := by
  have hz : ∀ (M : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) [M.IsStrictlyLE 0] (p q : ℤ),
      0 < p ∨ 0 < q →
      IsZero ((((mooreBicomplexFunctor U).obj M).X p).X q) := fun M _ p q hpq => by
    rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{u}
        (ComplexShape.up ℤ) q) (GeneralValued.isZero_mooreBicomplex_X U M p
          (CochainComplex.isZero_of_isStrictlyLE M 0 p hp))
    · exact GeneralValued.isZero_mooreBicomplex_X_X U M p q hq
  refine quasiIso_total_map_of_upperBound_flip ((mooreBicomplexFunctor U).map f) 0 0
    (fun p q => hz K p q) (fun p q => hz L p q) fun q => ?_
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (mooreCochainComplex U ⋙ HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) q)

end Bicomplex

/-! ### The comparison with derived lower shriek -/

section Derived

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The total complex of the double complex is the degreewise colimit of a bounded above
complex of projectives**, in the derived category. -/
def totalQIsoColimOfResolution (hU : IsPointResolution U)
    (P : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) [P.IsStrictlyLE 0]
    [∀ n, Projective (P.X n)] :
    DerivedCategory.Q.obj ((mooreBicomplex U P).total (ComplexShape.up ℤ)) ≅
      DerivedCategory.Q.obj
        (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  have _h1 : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexColumnTotalMap U P hU
  have _h2 : IsIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)) := isIso_totalSingleRowZeroUnit _
  asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
    (ComplexShape.up ℤ))) ≪≫
    (DerivedCategory.Q.mapIso (asIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P)))).symm

/-- **The first filtration is natural in the complex of projective abelian presheaves**: the
identification `Tot(Z_P) ≃ colim P^•` commutes with a morphism `P^• ⟶ P'^•`. -/
lemma totalQIsoColimOfResolution_naturality_complex (hU : IsPointResolution U)
    {P P' : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [P.IsStrictlyLE 0] [P'.IsStrictlyLE 0]
    [∀ n, Projective (P.X n)] [∀ n, Projective (P'.X n)] (g : P ⟶ P') :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map g)
            (ComplexShape.up ℤ)) ≫
        (totalQIsoColimOfResolution U hU P').hom =
      (totalQIsoColimOfResolution U hU P).hom ≫
        DerivedCategory.Q.map
          (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) := by
  have hcol : (mooreBicomplexFunctor U).map g ≫ mooreBicomplexColumnMap U P' =
      mooreBicomplexColumnMap U P ≫
        ((HomologicalComplex.single AddCommGrpCat.{u}
          (ComplexShape.up ℤ) 0).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
              (ComplexShape.up ℤ)).map g) :=
    (NatTrans.mapHomologicalComplex (mooreCochainAugmentation U) (ComplexShape.up ℤ)).naturality g
  have hunit := totalSingleRowZeroUnit_naturality (A := AddCommGrpCat.{u})
    (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g)
  dsimp only [totalQIsoColimOfResolution, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    asIso_hom, asIso_inv]
  rw [Functor.map_inv, Functor.map_inv, ← Functor.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp, hcol, HomologicalComplex₂.total.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Functor.map_comp,
    ← Functor.map_comp, hunit]

/-- **Derived lower shriek of a bounded above complex of abelian presheaves is the total complex
of its double complex on a point resolution**, for a given resolution `ε : R^• ⟶ K^•` by
projective abelian presheaves: `Q(Tot(Z_K)) ≅ Lπ_!(K^•)` in `D(Ab)`. -/
def totalQIsoDerivedColimitOfResolution (hU : IsPointResolution U)
    (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) [K.IsStrictlyLE 0]
    (R : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ) [R.IsStrictlyLE 0]
    [∀ n, Projective (R.X n)] (ε : R ⟶ K) [QuasiIso ε] :
    DerivedCategory.Q.obj ((mooreBicomplex U K).total (ComplexShape.up ℤ)) ≅
      (totalDerivedColimit C AddCommGrpCat.{u}).obj (DerivedCategory.Q.obj K) :=
  have _hKP : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  have _hrow : QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexTotalMap U ε
  (asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map
      ((mooreBicomplexFunctor U).map ε) (ComplexShape.up ℤ)))).symm ≪≫
    totalQIsoColimOfResolution U hU R ≪≫
    (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
      AddCommGrpCat.{u} R).symm ≪≫
    (totalDerivedColimit C AddCommGrpCat.{u}).mapIso (asIso (DerivedCategory.Q.map ε))

/-- **The comparison is natural in the complex**, for a morphism `g : R^• ⟶ S^•` of the chosen
resolutions lifting `f : K^• ⟶ L^•`. -/
theorem totalQIsoDerivedColimitOfResolution_naturality (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    {R S : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [R.IsStrictlyLE 0] [S.IsStrictlyLE 0]
    [∀ n, Projective (R.X n)] [∀ n, Projective (S.X n)]
    (ε : R ⟶ K) [QuasiIso ε] (η : S ⟶ L) [QuasiIso η]
    (f : K ⟶ L) (g : R ⟶ S) (hg : g ≫ η = ε ≫ f) :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f)
            (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitOfResolution U hU L S η).hom =
      (totalQIsoDerivedColimitOfResolution U hU K R ε).hom ≫
        (totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map f) := by
  have _ : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  have _ : S.IsKProjective := CochainComplex.isKProjective_of_projective S 0
  have _ : QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map ε)
    (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexTotalMap U ε
  have _ : QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map η)
    (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexTotalMap U η
  dsimp only [totalQIsoDerivedColimitOfResolution, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom, asIso_inv]
  rw [← cancel_epi (DerivedCategory.Q.map
    (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map ε) (ComplexShape.up ℤ)))]
  slice_lhs 1 2 => rw [← Functor.map_comp, ← HomologicalComplex₂.total.map_comp,
    ← Functor.map_comp, ← hg, Functor.map_comp, HomologicalComplex₂.total.map_comp,
    Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [totalQIsoColimOfResolution_naturality_complex U hU g]
  have hk := Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective_naturality C
    AddCommGrpCat.{u} g
  have hk' : DerivedCategory.Q.map
        (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) ≫
        (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
          AddCommGrpCat.{u} S).inv =
      (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
          AddCommGrpCat.{u} R).inv ≫
        (totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map g) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hk.symm
  slice_lhs 2 3 => rw [hk']
  simp only [Category.assoc, ← Functor.map_comp, hg]

/-- **The comparison is natural in the complex**, for any morphism `f : K^• ⟶ L^•`, provided the
chosen resolution of `L^•` is degreewise epimorphic. -/
theorem totalQIsoDerivedColimitOfResolution_naturality_of_epi (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    {R S : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ} [R.IsStrictlyLE 0] [S.IsStrictlyLE 0]
    [hR : ∀ n, Projective (R.X n)] [∀ n, Projective (S.X n)]
    (ε : R ⟶ K) [QuasiIso ε] (η : S ⟶ L) [QuasiIso η] (hη : ∀ n, Epi (η.f n)) (f : K ⟶ L) :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f)
            (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitOfResolution U hU L S η).hom =
      (totalQIsoDerivedColimitOfResolution U hU K R ε).hom ≫
        (totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map f) := by
  have _ : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.exists_lift_of_quasiIso η (ε ≫ f)).2 hR hη
  exact totalQIsoDerivedColimitOfResolution_naturality U hU ε η f g hg

end Derived

/-! ### The derived form of Tag 08Q9 at abelian coefficients -/

section Keystone

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **For an abelian presheaf placed in degree zero the total complex of the double complex is
the extended Moore complex**: `Q(ℱ(U_•)) ≅ Q(Tot(Z_{ℱ[0]}))` in `D(Ab)`. -/
def mooreCochainQIsoTotalSingle (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      DerivedCategory.Q.obj ((mooreBicomplex U
        ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
          (ComplexShape.up ℤ) 0).obj F)).total (ComplexShape.up ℤ)) :=
  let := hasTotal_singleColumn ((mooreCochainComplex U).obj F) (0 : ℤ)
  have _h1 : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)) :=
    ModuleValued.isIso_total_map_of_isIso _
  DerivedCategory.Q.mapIso
      (ModuleValued.totalSingleColumnZeroIso ((mooreCochainComplex U).obj F)) ≪≫
    DerivedCategory.Q.mapIso (asIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)))

/-- **`Stacks.ChaoticSite.AbelianValued.mooreCochainQIsoTotalSingle` is natural in the abelian
presheaf.** -/
lemma mooreCochainQIsoTotalSingle_naturality {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (a : F ⟶ G) :
    DerivedCategory.Q.map ((mooreCochainComplex U).map a) ≫
        (mooreCochainQIsoTotalSingle U G).hom =
      (mooreCochainQIsoTotalSingle U F).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℤ) 0).map a)) (ComplexShape.up ℤ)) := by
  have _ := hasTotal_singleColumn ((mooreCochainComplex U).obj F) (0 : ℤ)
  have _ := hasTotal_singleColumn ((mooreCochainComplex U).obj G) (0 : ℤ)
  have h1 := ModuleValued.totalSingleColumnZeroIso_hom_naturality
    ((mooreCochainComplex U).map a)
  have h2 : (HomologicalComplex.single (CochainComplex AddCommGrpCat.{u} ℤ)
          (ComplexShape.up ℤ) 0).map ((mooreCochainComplex U).map a) ≫
        (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
          (ComplexShape.up ℤ) 0).inv.app G =
      (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
          (ComplexShape.up ℤ) 0).inv.app F ≫
        (mooreBicomplexFunctor U).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℤ) 0).map a) :=
    (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
      (ComplexShape.up ℤ) 0).inv.naturality a
  have hchain : (mooreCochainComplex U).map a ≫
        (ModuleValued.totalSingleColumnZeroIso ((mooreCochainComplex U).obj G)).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.singleMapHomologicalComplex
          (mooreCochainComplex U) (ComplexShape.up ℤ) 0).app G).inv (ComplexShape.up ℤ) =
      (ModuleValued.totalSingleColumnZeroIso ((mooreCochainComplex U).obj F)).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.singleMapHomologicalComplex
          (mooreCochainComplex U) (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℤ) 0).map a)) (ComplexShape.up ℤ) := by
    simp only [Iso.app_inv]
    rw [← Category.assoc, h1, Category.assoc, ← HomologicalComplex₂.total.map_comp, h2,
      HomologicalComplex₂.total.map_comp]
  have hQ := congrArg DerivedCategory.Q.map hchain
  dsimp only [mooreCochainQIsoTotalSingle, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simpa only [Functor.map_comp, Category.assoc] using hQ

/-- **A resolution of `ℱ[0]` by a bounded above complex of projective abelian presheaves whose
structure morphism is epimorphic in every degree**, as produced by [Stacks, Tag 0646]. -/
def singleProjectiveResolution (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ProjectiveResolutionLemma.ProjectiveResolutionComplex
      ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0).obj F) 0 :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0).obj F)
    inferInstance).choose

/-- The structure morphism of
`Stacks.ChaoticSite.AbelianValued.singleProjectiveResolution` is epimorphic in every degree. -/
lemma epi_singleProjectiveResolution_α (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℤ) :
    Epi ((singleProjectiveResolution F).α.f n) :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0).obj F)
    inferInstance).choose_spec n

/-- **The derived form of [Stacks, Tag 08Q9] at abelian coefficients, at one abelian presheaf**:
`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(Ab)`. -/
def mooreCochainIsoDerivedColimitApp (hU : IsPointResolution U)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      (totalDerivedColimit C AddCommGrpCat.{u}).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
          (ComplexShape.up ℤ) 0).obj F)) :=
  have := (singleProjectiveResolution F).projective
  have := (singleProjectiveResolution F).boundedAbove
  have := (singleProjectiveResolution F).quasiIso
  mooreCochainQIsoTotalSingle U F ≪≫
    totalQIsoDerivedColimitOfResolution U hU _ (singleProjectiveResolution F).complex
      (singleProjectiveResolution F).α

/-- **`Stacks.ChaoticSite.AbelianValued.mooreCochainIsoDerivedColimitApp` is natural in the
abelian presheaf.** -/
lemma mooreCochainIsoDerivedColimitApp_naturality (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (a : F ⟶ G) :
    DerivedCategory.Q.map ((mooreCochainComplex U).map a) ≫
        (mooreCochainIsoDerivedColimitApp U hU G).hom =
      (mooreCochainIsoDerivedColimitApp U hU F).hom ≫
        (totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
            (ComplexShape.up ℤ) 0).map a)) := by
  have := (singleProjectiveResolution F).projective
  have := (singleProjectiveResolution F).boundedAbove
  have := (singleProjectiveResolution F).quasiIso
  have := (singleProjectiveResolution G).projective
  have := (singleProjectiveResolution G).boundedAbove
  have := (singleProjectiveResolution G).quasiIso
  have htie := mooreCochainQIsoTotalSingle_naturality U a
  have hcmp := totalQIsoDerivedColimitOfResolution_naturality_of_epi U hU
    (singleProjectiveResolution F).α (singleProjectiveResolution G).α
    (epi_singleProjectiveResolution_α G)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0).map a)
  dsimp only [mooreCochainIsoDerivedColimitApp, Iso.trans_hom]
  rw [← Category.assoc, htie, Category.assoc, hcmp, Category.assoc]

/-- **The derived form of [Stacks, Tag 08Q9] at abelian coefficients, as an isomorphism of
functors.** Let `C` be a small category with the chaotic topology and let `U_•` be a cosimplicial
object of `C` which is a point resolution. Then

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(Ab)`,

**naturally in the abelian presheaf `ℱ`**, where the left side is the extended Moore complex of
the simplicial abelian group `ℱ(U_•)` and `Lπ_!` is the total left derived functor of the colimit
over `Cᵒᵖ`, which is `π_!` on the chaotic site by [Stacks, Tag 08PF]. -/
@[stacks 08Q9 "derived-category form at abelian coefficients, natural in the coefficient \
  presheaf: the extended Moore complex of the evaluation on a point resolution is derived lower \
  shriek as an isomorphism of functors. The degreewise form \
  `Stacks.ChaoticSite.leftDerivedColimitNatIso` gives only the cohomology of the two sides and \
  cannot transport a morphism of coefficients"]
def mooreCochainNatIsoDerivedColimit (hU : IsPointResolution U) :
    mooreCochainComplex U ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun F => mooreCochainIsoDerivedColimitApp U hU F)
    (fun a => mooreCochainIsoDerivedColimitApp_naturality U hU a)

/-- **Derived lower shriek inverts a morphism of abelian presheaves exactly when the induced
morphism of extended Moore complexes is a quasi-isomorphism**, for `U_•` a point resolution. -/
theorem isIso_totalDerivedColimit_single_map_iff (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (a : F ⟶ G) :
    IsIso ((totalDerivedColimit C AddCommGrpCat.{u}).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (Cᵒᵖ ⥤ AddCommGrpCat.{u})
          (ComplexShape.up ℤ) 0).map a))) ↔
      QuasiIso ((mooreCochainComplex U).map a) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact (NatIso.isIso_map_iff (mooreCochainNatIsoDerivedColimit U hU) a).symm

end Keystone

end Stacks.ChaoticSite.AbelianValued

end

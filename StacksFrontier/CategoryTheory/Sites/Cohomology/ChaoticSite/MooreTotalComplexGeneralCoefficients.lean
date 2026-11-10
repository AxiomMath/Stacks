module

public import
StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The two filtrations of the Moore double complex, at general coefficients

Let `C` be a small category, let `A` be an abelian category with colimits of shape `Cᵒᵖ` and let
`U_•` be a cosimplicial object of `C`. For a complex `K^•` of `A`-valued presheaves,
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.MooreCochainComplex` builds the double
complex `Z^{p,q} = (K^p(U_•))^q` and compares it, through its *first* filtration, with the
degreewise colimit of `K^•`. This module adds the *second* filtration and assembles the two into
the comparison

`Q(ℱ(U_•)) ≅ Q(colim R^•)` in `D(A)`

attached to a bounded above resolution `ε : R^• ⟶ ℱ[0]` of a single presheaf `ℱ`.

## Relation to the abelian-coefficient file

This is
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian`
with `AddCommGrpCat` replaced by an arbitrary abelian `A`, and with the requirement that the
resolving complex be degreewise *projective* replaced by the only consequence of projectivity the
argument uses: that the Moore augmentation of each of its terms be a quasi-isomorphism. That
hypothesis is carried explicitly, as `haug`, so the development below is free of both the
coefficient category and the mechanism producing the resolution. The abelian-coefficient file
discharges `haug` from `Stacks.ChaoticSite.AbelianValued.quasiIso_mooreCochainAugmentation` and
then continues, past the point reached here, to identify `Q(colim R^•)` with derived lower shriek
by a K-projectivity argument; that last step genuinely needs projective terms and is *not*
reproduced here.

## Main definitions

* `Stacks.ChaoticSite.GeneralValued.totalQIsoColimOfAugmentation`: the comparison
  `Q(Tot(Z_P)) ≅ Q(colim P^•)` through the first filtration, for a bounded above complex `P^•`
  whose terms have quasi-isomorphic Moore augmentation.
* `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoTotalSingle`: for a presheaf `ℱ` placed in
  degree zero the total complex of the double complex is the extended Moore complex of `ℱ(U_•)`.
* `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution`: **the extended Moore
  complex of `ℱ(U_•)` is, in `D(A)`, the degreewise colimit of any bounded above resolution of
  `ℱ` whose terms have quasi-isomorphic Moore augmentation.**

## Main results

* `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreBicomplexTotalMap`: the second filtration of
  the double complex — a quasi-isomorphism of bounded above complexes of presheaves induces a
  quasi-isomorphism on the total complexes. This is [Stacks, Tag 0133] with the hypothesis on the
  rows, and it needs nothing of the coefficient category: the row `q` is evaluation at an object
  of the site, an exact functor.
* `Stacks.ChaoticSite.GeneralValued.totalQIsoColimOfAugmentation_naturality_complex`: the first
  filtration is natural in the complex.
* `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoTotalSingle_naturality`: the identification
  of the total complex of a double complex concentrated in degree zero is natural in the
  presheaf.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open StacksDraft.TotalComplexQuasiIso

namespace Stacks.ChaoticSite.GeneralValued

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The second filtration of the double complex -/

section SecondFiltration

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  {A : Type*} [Category* A] [Abelian A]

/-- **The second filtration of the double complex, for an arbitrary quasi-isomorphism of bounded
above complexes of presheaves**: a quasi-isomorphism `K^• ⟶ L^•` induces a quasi-isomorphism on
the total complexes of the associated double complexes. This is [Stacks, Tag 0133] with the
hypothesis on the rows; the row `q` of `Z^{p,q} = (K^p(U_•))^q` is evaluation at the object
`U_{-q}` of the site, an exact functor of the presheaf by
`Stacks.ChaoticSite.GeneralValued.preservesHomology_mooreCochainComplex_comp_eval`, so no
homology is computed and the coefficient category contributes nothing. -/
@[sga "4 Vbis 2.3.3" "special case"]
lemma quasiIso_mooreBicomplexTotalMap {K L : CochainComplex (Cᵒᵖ ⥤ A) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U A).map f)
      (ComplexShape.up ℤ)) := by
  refine quasiIso_total_map_of_upperBound_flip ((mooreBicomplexFunctor U A).map f) 0 0
    (fun p q hpq => ?_) (fun p q hpq => ?_) (fun q => ?_)
  · rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
        (isZero_mooreBicomplex_X U K p (CochainComplex.isZero_of_isStrictlyLE K 0 p hp))
    · exact isZero_mooreBicomplex_X_X U K p q hq
  · rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
        (isZero_mooreBicomplex_X U L p (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
    · exact isZero_mooreBicomplex_X_X U L p q hq
  · have h : (flipHom ((mooreBicomplexFunctor U A).map f)).f q =
        ((mooreCochainComplex U A ⋙ HomologicalComplex.eval A
          (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℤ)).map f := rfl
    rw [h]
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f
      (mooreCochainComplex U A ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) q)

end SecondFiltration

/-! ### The first filtration in the derived category -/

section FirstFiltration

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  {A : Type*} [Category* A] [Abelian A] [HasColimitsOfShape Cᵒᵖ A]

/-- **The total complex of the double complex is the degreewise colimit of a bounded above
complex whose terms have quasi-isomorphic Moore augmentation**, in the derived category: the
comparison through the first filtration
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreBicomplexColumnTotalMap`, followed by the
identification `StacksDraft.TotalComplexQuasiIso.totalSingleRowZeroUnit` of a complex with the
total complex of the double complex concentrated in its row zero. No projectivity enters: the
hypothesis `haug` is exactly what projectivity would be used for. -/
def totalQIsoColimOfAugmentation (P : CochainComplex (Cᵒᵖ ⥤ A) ℤ) [P.IsStrictlyLE 0]
    (haug : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation U).app (P.X p))) :
    DerivedCategory.Q.obj ((mooreBicomplex U P).total (ComplexShape.up ℤ)) ≅
      DerivedCategory.Q.obj
        (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have _h1 : QuasiIso (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexColumnTotalMap U P haug
  have _h2 : IsIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) :=
    isIso_totalSingleRowZeroUnit _
  asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map (mooreBicomplexColumnMap U P)
    (ComplexShape.up ℤ))) ≪≫
    (DerivedCategory.Q.mapIso (asIso (totalSingleRowZeroUnit
      (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))).symm

/-- **The first filtration is natural in the complex of presheaves**: the identification
`Tot(Z_P) ≃ colim P^•` of
`Stacks.ChaoticSite.GeneralValued.totalQIsoColimOfAugmentation` commutes with a morphism
`P^• ⟶ P'^•`. -/
lemma totalQIsoColimOfAugmentation_naturality_complex
    {P P' : CochainComplex (Cᵒᵖ ⥤ A) ℤ} [P.IsStrictlyLE 0] [P'.IsStrictlyLE 0]
    (haug : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation U).app (P.X p)))
    (haug' : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation U).app (P'.X p))) (g : P ⟶ P') :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U A).map g)
            (ComplexShape.up ℤ)) ≫
        (totalQIsoColimOfAugmentation U P' haug').hom =
      (totalQIsoColimOfAugmentation U P haug).hom ≫
        DerivedCategory.Q.map
          (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).map g) := by
  have hcol : (mooreBicomplexFunctor U A).map g ≫ mooreBicomplexColumnMap U P' =
      mooreBicomplexColumnMap U P ≫
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).map g) :=
    (NatTrans.mapHomologicalComplex (mooreCochainAugmentation U) (ComplexShape.up ℤ)).naturality g
  have hunit := totalSingleRowZeroUnit_naturality (A := A)
    (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).map g)
  dsimp only [totalQIsoColimOfAugmentation, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    asIso_hom, asIso_inv]
  rw [Functor.map_inv, Functor.map_inv, ← Functor.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp, hcol, HomologicalComplex₂.total.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Functor.map_comp,
    ← Functor.map_comp, hunit]

end FirstFiltration

/-! ### A presheaf placed in degree zero -/

section Single

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  {A : Type*} [Category* A] [Abelian A]

/-- **The double complex concentrated in the column zero at the extended Moore complex of
`ℱ(U_•)` has a total complex**: only one of its columns is nonzero, so each of the coproducts
defining the total complex is finite. This is
`StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn` stated at the composed functor
`ℱ ↦ (ℱ(U_•))[0]`, which is the shape in which
`HomologicalComplex.singleMapHomologicalComplex` presents its source; the general abelian
category supplies no coproducts of its own, so this instance is what makes the total complex of
that source exist. -/
instance hasTotal_singleMooreCochainComplex (F : Cᵒᵖ ⥤ A) :
    HomologicalComplex₂.HasTotal
      ((mooreCochainComplex U A ⋙
        HomologicalComplex.single (CochainComplex A ℤ) (ComplexShape.up ℤ) 0).obj F)
      (ComplexShape.up ℤ) :=
  hasTotal_singleColumn ((mooreCochainComplex U A).obj F) 0

/-- **The double complex of a presheaf placed in degree zero has a total complex**: `ℱ[0]` is
strictly `≤ 0`, so the double complex is bounded above. This is
`Stacks.ChaoticSite.GeneralValued.hasTotal_mooreBicomplex` stated at the composed functor
`ℱ ↦ Z_{ℱ[0]}`, which is the shape in which
`HomologicalComplex.singleMapHomologicalComplex` presents its target. -/
instance hasTotal_mooreBicomplexSingle (F : Cᵒᵖ ⥤ A) :
    HomologicalComplex₂.HasTotal
      ((HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0 ⋙
        (mooreCochainComplex U A).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
      (ComplexShape.up ℤ) :=
  hasTotal_mooreBicomplex U ((HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0).obj F)

/-- **For a presheaf placed in degree zero the total complex of the double complex is the
extended Moore complex**: `Q(ℱ(U_•)) ≅ Q(Tot(Z_{ℱ[0]}))` in `D(A)`. The double complex of `ℱ[0]`
is concentrated in the column zero, where it is `ℱ(U_•)`, so
`Stacks.ChaoticSite.ModuleValued.totalSingleColumnZeroIso` identifies the two. No resolution of
`ℱ` enters. -/
def mooreCochainQIsoTotalSingle (F : Cᵒᵖ ⥤ A) :
    DerivedCategory.Q.obj ((mooreCochainComplex U A).obj F) ≅
      DerivedCategory.Q.obj ((mooreBicomplex U
        ((HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0).obj F)).total
          (ComplexShape.up ℤ)) :=
  letI := hasTotal_singleColumn ((mooreCochainComplex U A).obj F) (0 : ℤ)
  have _h1 : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U A)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)) :=
    ModuleValued.isIso_total_map_of_isIso _
  DerivedCategory.Q.mapIso
      (ModuleValued.totalSingleColumnZeroIso ((mooreCochainComplex U A).obj F)) ≪≫
    DerivedCategory.Q.mapIso (asIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U A)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)))

/-- **`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoTotalSingle` is natural in the
presheaf.** -/
lemma mooreCochainQIsoTotalSingle_naturality {F G : Cᵒᵖ ⥤ A} (a : F ⟶ G) :
    DerivedCategory.Q.map ((mooreCochainComplex U A).map a) ≫
        (mooreCochainQIsoTotalSingle U G).hom =
      (mooreCochainQIsoTotalSingle U F).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U A).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0).map a))
            (ComplexShape.up ℤ)) := by
  have := hasTotal_singleColumn ((mooreCochainComplex U A).obj F) (0 : ℤ)
  have := hasTotal_singleColumn ((mooreCochainComplex U A).obj G) (0 : ℤ)
  have h1 := ModuleValued.totalSingleColumnZeroIso_hom_naturality
    ((mooreCochainComplex U A).map a)
  have h2 : (HomologicalComplex.single (CochainComplex A ℤ) (ComplexShape.up ℤ) 0).map
          ((mooreCochainComplex U A).map a) ≫
        (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U A)
          (ComplexShape.up ℤ) 0).inv.app G =
      (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U A)
          (ComplexShape.up ℤ) 0).inv.app F ≫
        (mooreBicomplexFunctor U A).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0).map a) :=
    (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U A)
      (ComplexShape.up ℤ) 0).inv.naturality a
  have hchain : (mooreCochainComplex U A).map a ≫
        (ModuleValued.totalSingleColumnZeroIso ((mooreCochainComplex U A).obj G)).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.singleMapHomologicalComplex
          (mooreCochainComplex U A) (ComplexShape.up ℤ) 0).app G).inv (ComplexShape.up ℤ) =
      (ModuleValued.totalSingleColumnZeroIso ((mooreCochainComplex U A).obj F)).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.singleMapHomologicalComplex
          (mooreCochainComplex U A) (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((mooreBicomplexFunctor U A).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0).map a))
            (ComplexShape.up ℤ) := by
    simp only [Iso.app_inv]
    rw [← Category.assoc, h1, Category.assoc, ← HomologicalComplex₂.total.map_comp, h2,
      HomologicalComplex₂.total.map_comp]
  have hQ := congrArg DerivedCategory.Q.map hchain
  dsimp only [mooreCochainQIsoTotalSingle, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simpa only [Functor.map_comp, Category.assoc] using hQ

end Single

/-! ### The assembled comparison -/

section Assembled

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)
  {A : Type*} [Category* A] [Abelian A] [HasColimitsOfShape Cᵒᵖ A]

/-- **The extended Moore complex of `ℱ(U_•)` is the degreewise colimit of a resolution of `ℱ`**:
for a bounded above complex `R^•` of `A`-valued presheaves, a quasi-isomorphism
`ε : R^• ⟶ ℱ[0]`, and the hypothesis that the Moore augmentation of each term `R^p` be a
quasi-isomorphism,

`Q(ℱ(U_•)) ≅ Q(colim R^•)` in `D(A)`.

This is the two filtrations of the double complex `Z^{p,q} = (R^p(U_•))^q` put together: the
second filtration `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreBicomplexTotalMap` moves `ε`
across to `Tot(Z_{ℱ[0]})`, which is the extended Moore complex of `ℱ(U_•)` by
`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoTotalSingle`, and the first filtration
`Stacks.ChaoticSite.GeneralValued.totalQIsoColimOfAugmentation` identifies `Tot(Z_{R^•})` with
`colim R^•`.

Neither projectivity of the terms of `R^•` nor a point resolution is assumed; the resolution may
be any bounded above one whose terms satisfy the single property `haug`. Identifying the right
side with derived lower shriek is a further step, which does need K-projectivity, and is carried
at abelian-group coefficients by
`Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitOfResolution`. -/
def mooreCochainQIsoColimOfResolution
    (F : Cᵒᵖ ⥤ A) (R : CochainComplex (Cᵒᵖ ⥤ A) ℤ) [R.IsStrictlyLE 0]
    (ε : R ⟶ (HomologicalComplex.single (Cᵒᵖ ⥤ A) (ComplexShape.up ℤ) 0).obj F) [QuasiIso ε]
    (haug : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation U).app (R.X p))) :
    DerivedCategory.Q.obj ((mooreCochainComplex U A).obj F) ≅
      DerivedCategory.Q.obj
        (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) :=
  have _hrow : QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U A).map ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexTotalMap U ε
  mooreCochainQIsoTotalSingle U F ≪≫
    (asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map
      ((mooreBicomplexFunctor U A).map ε) (ComplexShape.up ℤ)))).symm ≪≫
    totalQIsoColimOfAugmentation U R haug

/-- **The total complex of the Moore double complex of a bounded above complex of presheaves is
the degreewise colimit of a resolution of it**: for bounded above complexes `K^•` and `R^•` of
`A`-valued presheaves, a quasi-isomorphism `ε : R^• ⟶ K^•`, and the hypothesis that the Moore
augmentation of each term `R^p` be a quasi-isomorphism,

`Q(Tot(Z_{K^•})) ≅ Q(colim R^•)` in `D(A)`,

where `Z^{p,q} = (K^p(U_•))^q`.

This is `Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoColimOfResolution` with the resolved
object allowed to be a complex rather than a presheaf placed in degree zero. The two filtrations
enter in the same way, and neither needs a new hypothesis: the second filtration
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreBicomplexTotalMap` is already stated for an
arbitrary quasi-isomorphism of bounded above complexes, and the first filtration
`Stacks.ChaoticSite.GeneralValued.totalQIsoColimOfAugmentation` only ever sees `R^•`. What the
degree-zero case has on top of this is
`Stacks.ChaoticSite.GeneralValued.mooreCochainQIsoTotalSingle`, which rewrites the total complex
of `Z_{ℱ[0]}` as the extended Moore complex of `ℱ(U_•)`; for a general `K^•` no such rewriting is
available and the total complex is the answer. -/
def mooreBicomplexTotalQIsoColimOfResolution
    (K R : CochainComplex (Cᵒᵖ ⥤ A) ℤ) [K.IsStrictlyLE 0] [R.IsStrictlyLE 0] (ε : R ⟶ K)
    [QuasiIso ε] (haug : ∀ p : ℤ, QuasiIso ((mooreCochainAugmentation U).app (R.X p))) :
    DerivedCategory.Q.obj ((mooreBicomplex U K).total (ComplexShape.up ℤ)) ≅
      DerivedCategory.Q.obj
        (((colim : (Cᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) :=
  have _hrow : QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U A).map ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexTotalMap U ε
  (asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map
    ((mooreBicomplexFunctor U A).map ε) (ComplexShape.up ℤ)))).symm ≪≫
    totalQIsoColimOfAugmentation U R haug

end Assembled

end Stacks.ChaoticSite.GeneralValued

end

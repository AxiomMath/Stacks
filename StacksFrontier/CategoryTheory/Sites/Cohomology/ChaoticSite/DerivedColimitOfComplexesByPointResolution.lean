module

public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitOnKProjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek of a bounded above complex, computed by a point resolution

Let `C` be a small category with the chaotic topology, let `B` be a ring, so that a `B̲`-module is
a diagram of `B`-modules on `Cᵒᵖ`, and let `U_•` be a cosimplicial object of `C` which is a point
resolution. For a *single* `B̲`-module `ℱ` the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolution`
identifies `Lπ_!(ℱ)` with the extended Moore complex of `ℱ(U_•)`. This file proves the same
statement for an arbitrary cochain complex `K^•` of `B̲`-modules bounded above by `0`:

`Q(Tot(Z_K)) ≅ Lπ_!(K^•)` in `D(B)`,

where `Z_K` is the double complex `Z^{p,q} = (K^p(U_•))^q` obtained by evaluating `K^•` on `U_•`,
and `Tot` is its total complex. For `K^• = ℱ[0]` the total complex is the extended Moore complex
of `ℱ(U_•)` and the statement specialises to the previous one.

The isomorphism is built from a resolution `ε : R^• ⟶ K^•` of `K^•` by a bounded above complex of
projective diagrams, exactly as in the single-module case: the two filtrations of `Z_R` compare
`Tot(Z_R)` with `Tot(Z_K)` and with the degreewise colimit `colim R^•`, and `Lπ_!` of the
K-projective complex `R^•` is that degreewise colimit.

## Naturality in the complex

The isomorphism is also shown to be **natural in `K^•`**, which the single-module statement is
not. The resolution is a parameter, so a morphism `f : K^• ⟶ L^•` is accompanied by a morphism
`g : R^• ⟶ S^•` of the chosen resolutions lifting it, and all four factors of the comparison are
natural in that pair. Such a lift exists on the nose whenever the resolution of the target is
degreewise epimorphic — which is how [Stacks, Tag 0646] produces resolutions — by
[Stacks, Tag 0649] (`CochainComplex.IsKProjective.exists_lift_of_quasiIso`), so no functorial
choice of resolution is needed: one lift per morphism suffices, and it is unique up to the
homotopy that the comparison does not see.

## Main definitions

* `Stacks.ChaoticSite.ModuleValued.mooreBicomplexFunctor`: the formation of the double complex
  `Z_K`, as a functor of the complex `K^•`.
* `Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution`: the isomorphism
  `Q(Tot(Z_K)) ≅ Lπ_!(K^•)` attached to a resolution of `K^•`.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoTotalSingle`: for a complex concentrated in
  degree zero the total complex of the double complex is the extended Moore complex,
  `Q(ℱ(U_•)) ≅ Q(Tot(Z_{ℱ[0]}))`.
* `Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimit`: **the derived form of
  [Stacks, Tag 08Q9] at module coefficients, as an isomorphism of functors** —
  `Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`, natural in the `B̲`-module `ℱ`.

## Main results

* `Stacks.ChaoticSite.ModuleValued.quasiIso_mooreBicomplexTotalMap`: the second filtration for
  an arbitrary quasi-isomorphism of bounded above complexes — a quasi-isomorphism `K^• ⟶ L^•`
  induces one on the total complexes of the double complexes. This generalises
  `Stacks.ChaoticSite.ModuleValued.quasiIso_mooreBicomplexRowTotalMap`, which is the case of a
  resolution of a complex concentrated in degree zero.
* `Stacks.ChaoticSite.ModuleValued.totalQIsoColimOfResolution_naturality_complex`: the first
  filtration is natural in the complex of projective diagrams.
* `Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution_naturality` and
  `Stacks.ChaoticSite.ModuleValued.totalQIsoDerivedColimitOfResolution_naturality_of_epi`:
  **the comparison is natural in the complex**, given a lift of the morphism to the chosen
  resolutions, respectively given only that the resolution of the target is degreewise
  epimorphic.

## Implementation notes

The computation of `Lπ_!` on a K-projective complex used here is
`Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective`, the statement for an arbitrary
total left derived functor, whose naturality in the complex is
`Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective_naturality`.

## References

* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
* [Stacks Project, Tag 0649](https://stacks.math.columbia.edu/tag/0649)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.CategoryHomology StacksDraft.TotalComplexQuasiIso

namespace Stacks.ChaoticSite.ModuleValued

universe u

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] {B : Type u} [Ring B] (U : CosimplicialObject C)

/-- **The double complex of a complex of diagrams, as a functor of that complex.** On objects it
is `Stacks.ChaoticSite.ModuleValued.mooreBicomplex`, and on a morphism `f : K^• ⟶ L^•` it is in
the column `p` the extended Moore complex of `K^p(U_•) ⟶ L^p(U_•)`. For a resolution of a complex
concentrated in degree zero its value is
`Stacks.ChaoticSite.ModuleValued.mooreBicomplexRowMap`. -/
abbrev mooreBicomplexFunctor : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ ⥤
    HomologicalComplex₂ (ModuleCat.{u} B) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (mooreCochainComplex U).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The second filtration of the double complex, for an arbitrary quasi-isomorphism of bounded
above complexes**: a quasi-isomorphism `K^• ⟶ L^•` induces a quasi-isomorphism on the total
complexes of the associated double complexes, so `Tot(Z_K) ≃ Tot(Z_L)`. This is
[Stacks, Tag 0133] for double complexes bounded above, with the hypothesis on the rows. -/
lemma quasiIso_mooreBicomplexTotalMap {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f)
      (ComplexShape.up ℤ)) := by
  have hZ : ∀ (M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [M.IsStrictlyLE 0] (p q : ℤ),
      0 < p ∨ 0 < q → IsZero (((mooreBicomplex U M).X p).X q) := by
    intro M _ p q hpq
    rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval (ModuleCat.{u} B)
        (ComplexShape.up ℤ) q) (GeneralValued.isZero_mooreBicomplex_X U M p
          (CochainComplex.isZero_of_isStrictlyLE M 0 p hp))
    · exact GeneralValued.isZero_mooreBicomplex_X_X U M p q hq
  refine quasiIso_total_map_of_upperBound_flip ((mooreBicomplexFunctor U).map f) 0 0
    (hZ K) (hZ L) (fun q => ?_)
  have h : (flipHom ((mooreBicomplexFunctor U).map f)).f q =
      ((mooreCochainComplex U ⋙ HomologicalComplex.eval (ModuleCat.{u} B)
        (ComplexShape.up ℤ) q).mapHomologicalComplex (ComplexShape.up ℤ)).map f := rfl
  rw [h]
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f
    (mooreCochainComplex U ⋙ HomologicalComplex.eval (ModuleCat.{u} B) (ComplexShape.up ℤ) q)

/-- **The first filtration of the double complex is natural in the complex of projective
diagrams**: the identification `Tot(Z_P) ≃ colim P^•` commutes with a morphism `P^• ⟶ P'^•`. -/
lemma totalQIsoColimOfResolution_naturality_complex (hU : IsPointResolution U)
    {P P' : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [P.IsStrictlyLE 0] [P'.IsStrictlyLE 0]
    [∀ n, Projective (P.X n)] [∀ n, Projective (P'.X n)] (g : P ⟶ P') :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map g) (ComplexShape.up ℤ)) ≫
        (totalQIsoColimOfResolution U hU P').hom =
      (totalQIsoColimOfResolution U hU P).hom ≫
        DerivedCategory.Q.map
          (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
            (ComplexShape.up ℤ)).map g) := by
  have hcol : (mooreBicomplexFunctor U).map g ≫ mooreBicomplexColumnMap U P' =
      mooreBicomplexColumnMap U P ≫
        ((HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
            (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
              (ComplexShape.up ℤ)).map g) :=
    (NatTrans.mapHomologicalComplex (mooreCochainAugmentation U) (ComplexShape.up ℤ)).naturality g
  have hunit := totalSingleRowZeroUnit_naturality (A := ModuleCat.{u} B)
    (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g)
  dsimp only [totalQIsoColimOfResolution, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    asIso_hom, asIso_inv]
  rw [Functor.map_inv, Functor.map_inv, ← Functor.map_comp_assoc,
    ← HomologicalComplex₂.total.map_comp, hcol, HomologicalComplex₂.total.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp, ← Functor.map_comp,
    ← Functor.map_comp, hunit]

/-- **Derived lower shriek of a bounded above complex of `B̲`-modules is the total complex of its
double complex on a point resolution**, for a given resolution `ε : R^• ⟶ K^•` by projective
diagrams: `Q(Tot(Z_K)) ≅ Lπ_!(K^•)` in `D(B)`.

The isomorphism is the composite of the second filtration of `Z_R`, which compares `Tot(Z_R)`
with `Tot(Z_K)`, the first filtration, which compares it with the degreewise colimit of `R^•`,
and the computation of `Lπ_!` on the K-projective complex `R^•`. -/
def totalQIsoDerivedColimitOfResolution (hU : IsPointResolution U)
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [K.IsStrictlyLE 0]
    (R : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ) [R.IsStrictlyLE 0]
    [∀ n, Projective (R.X n)] (ε : R ⟶ K) [QuasiIso ε] :
    DerivedCategory.Q.obj ((mooreBicomplex U K).total (ComplexShape.up ℤ)) ≅
      (totalDerivedColimit C (ModuleCat.{u} B)).obj (DerivedCategory.Q.obj K) :=
  have _hKP : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  have _hrow : QuasiIso (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map ε)
      (ComplexShape.up ℤ)) := quasiIso_mooreBicomplexTotalMap U ε
  (asIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map
      ((mooreBicomplexFunctor U).map ε) (ComplexShape.up ℤ)))).symm ≪≫
    totalQIsoColimOfResolution U hU R ≪≫
    (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
      (ModuleCat.{u} B) R).symm ≪≫
    (totalDerivedColimit C (ModuleCat.{u} B)).mapIso (asIso (DerivedCategory.Q.map ε))

/-- **The comparison is natural in the complex**, for a morphism `g : R^• ⟶ S^•` of the chosen
resolutions lifting `f : K^• ⟶ L^•`. -/
theorem totalQIsoDerivedColimitOfResolution_naturality (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    {R S : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [R.IsStrictlyLE 0] [S.IsStrictlyLE 0]
    [∀ n, Projective (R.X n)] [∀ n, Projective (S.X n)]
    (ε : R ⟶ K) [QuasiIso ε] (η : S ⟶ L) [QuasiIso η]
    (f : K ⟶ L) (g : R ⟶ S) (hg : g ≫ η = ε ≫ f) :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f) (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitOfResolution U hU L S η).hom =
      (totalQIsoDerivedColimitOfResolution U hU K R ε).hom ≫
        (totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map f) := by
  have _ : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  have _ : S.IsKProjective := CochainComplex.isKProjective_of_projective S 0
  have _ := quasiIso_mooreBicomplexTotalMap U ε
  have _ := quasiIso_mooreBicomplexTotalMap U η
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
    (ModuleCat.{u} B) g
  have hk' : DerivedCategory.Q.map
        (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g) ≫
        (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
          (ModuleCat.{u} B) S).inv =
      (Stacks.CategoryHomology.totalDerivedColimitObjIsoOfIsKProjective C
          (ModuleCat.{u} B) R).inv ≫
        (totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map g) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hk.symm
  slice_lhs 2 3 => rw [hk']
  simp only [Category.assoc, ← Functor.map_comp, hg]

/-- **The comparison is natural in the complex, with no lift supplied**, provided the chosen
resolution of the target is degreewise epimorphic, as the resolutions of [Stacks, Tag 0646] are.
-/
theorem totalQIsoDerivedColimitOfResolution_naturality_of_epi (hU : IsPointResolution U)
    {K L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    {R S : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} B) ℤ} [R.IsStrictlyLE 0] [S.IsStrictlyLE 0]
    [hR : ∀ n, Projective (R.X n)] [∀ n, Projective (S.X n)]
    (ε : R ⟶ K) [QuasiIso ε] (η : S ⟶ L) [QuasiIso η] (hη : ∀ n, Epi (η.f n)) (f : K ⟶ L) :
    DerivedCategory.Q.map
          (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map f) (ComplexShape.up ℤ)) ≫
        (totalQIsoDerivedColimitOfResolution U hU L S η).hom =
      (totalQIsoDerivedColimitOfResolution U hU K R ε).hom ≫
        (totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map f) := by
  have _ : R.IsKProjective := CochainComplex.isKProjective_of_projective R 0
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.exists_lift_of_quasiIso η (ε ≫ f)).2 hR hη
  exact totalQIsoDerivedColimitOfResolution_naturality U hU ε η f g hg

/-! ### The derived form of Tag 08Q9 at module coefficients, naturally in the module -/

/-- **For a diagram placed in degree zero the total complex of the double complex is the extended
Moore complex**: `Q(ℱ(U_•)) ≅ Q(Tot(Z_{ℱ[0]}))` in `D(B)`. The double complex of `ℱ[0]` is
concentrated in the column `0`, where it is the extended Moore complex of `ℱ(U_•)`, and the total
complex of a double complex concentrated in the column `0` is that column. -/
def mooreCochainQIsoTotalSingle (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      DerivedCategory.Q.obj ((mooreBicomplex U
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)).total
          (ComplexShape.up ℤ)) :=
  let := hasTotal_singleColumn ((mooreCochainComplex U).obj F) (0 : ℤ)
  have _h1 : IsIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)) :=
    isIso_total_map_of_isIso _
  DerivedCategory.Q.mapIso (totalSingleColumnZeroIso ((mooreCochainComplex U).obj F)) ≪≫
    DerivedCategory.Q.mapIso (asIso (HomologicalComplex₂.total.map
      ((HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
        (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ)))

/-- **`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoTotalSingle` is natural in the
diagram.** -/
lemma mooreCochainQIsoTotalSingle_naturality {F G : Cᵒᵖ ⥤ ModuleCat.{u} B} (a : F ⟶ G) :
    DerivedCategory.Q.map ((mooreCochainComplex U).map a) ≫
        (mooreCochainQIsoTotalSingle U G).hom =
      (mooreCochainQIsoTotalSingle U F).hom ≫ DerivedCategory.Q.map
        (HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).map a))
          (ComplexShape.up ℤ)) := by
  have _ := hasTotal_singleColumn ((mooreCochainComplex U).obj F) (0 : ℤ)
  have _ := hasTotal_singleColumn ((mooreCochainComplex U).obj G) (0 : ℤ)
  have h1 := totalSingleColumnZeroIso_hom_naturality ((mooreCochainComplex U).map a)
  have h2 : (HomologicalComplex.single (CochainComplex (ModuleCat.{u} B) ℤ)
          (ComplexShape.up ℤ) 0).map ((mooreCochainComplex U).map a) ≫
        (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
          (ComplexShape.up ℤ) 0).inv.app G =
      (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
          (ComplexShape.up ℤ) 0).inv.app F ≫
        (mooreBicomplexFunctor U).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).map a) :=
    (HomologicalComplex.singleMapHomologicalComplex (mooreCochainComplex U)
      (ComplexShape.up ℤ) 0).inv.naturality a
  have hchain : (mooreCochainComplex U).map a ≫
        (totalSingleColumnZeroIso ((mooreCochainComplex U).obj G)).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.singleMapHomologicalComplex
          (mooreCochainComplex U) (ComplexShape.up ℤ) 0).app G).inv (ComplexShape.up ℤ) =
      (totalSingleColumnZeroIso ((mooreCochainComplex U).obj F)).hom ≫
        HomologicalComplex₂.total.map ((HomologicalComplex.singleMapHomologicalComplex
          (mooreCochainComplex U) (ComplexShape.up ℤ) 0).app F).inv (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map ((mooreBicomplexFunctor U).map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).map a))
          (ComplexShape.up ℤ) := by
    simp only [Iso.app_inv]
    rw [← Category.assoc, h1, Category.assoc, ← HomologicalComplex₂.total.map_comp, h2,
      HomologicalComplex₂.total.map_comp]
  have hQ := congrArg DerivedCategory.Q.map hchain
  dsimp only [mooreCochainQIsoTotalSingle, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simpa only [Functor.map_comp, Category.assoc] using hQ

/-- **A resolution of `ℱ[0]` by a bounded above complex of projective diagrams whose structure
morphism is epimorphic in every degree**, as produced by [Stacks, Tag 0646]. -/
def singleProjectiveResolution (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    ProjectiveResolutionLemma.ProjectiveResolutionComplex
      ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F) 0 :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    inferInstance).choose

/-- The structure morphism of `Stacks.ChaoticSite.ModuleValued.singleProjectiveResolution` is
epimorphic in every degree. -/
lemma epi_singleProjectiveResolution_α (F : Cᵒᵖ ⥤ ModuleCat.{u} B) (n : ℤ) :
    Epi ((singleProjectiveResolution F).α.f n) :=
  (ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)
    inferInstance).choose_spec n

/-- **The derived form of [Stacks, Tag 08Q9] at module coefficients, at one diagram**:
`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`. It is the comparison for the complex `ℱ[0]` attached to the
resolution `Stacks.ChaoticSite.ModuleValued.singleProjectiveResolution`, preceded by the
identification of the total complex of the double complex of `ℱ[0]` with the extended Moore
complex of `ℱ(U_•)`. -/
def mooreCochainIsoDerivedColimitApp (hU : IsPointResolution U) (F : Cᵒᵖ ⥤ ModuleCat.{u} B) :
    DerivedCategory.Q.obj ((mooreCochainComplex U).obj F) ≅
      (totalDerivedColimit C (ModuleCat.{u} B)).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).obj F)) :=
  have := (singleProjectiveResolution F).projective
  have := (singleProjectiveResolution F).boundedAbove
  have := (singleProjectiveResolution F).quasiIso
  mooreCochainQIsoTotalSingle U F ≪≫
    totalQIsoDerivedColimitOfResolution U hU _ (singleProjectiveResolution F).complex
      (singleProjectiveResolution F).α

/-- **`Stacks.ChaoticSite.ModuleValued.mooreCochainIsoDerivedColimitApp` is natural in the
diagram.** -/
lemma mooreCochainIsoDerivedColimitApp_naturality (hU : IsPointResolution U)
    {F G : Cᵒᵖ ⥤ ModuleCat.{u} B} (a : F ⟶ G) :
    DerivedCategory.Q.map ((mooreCochainComplex U).map a) ≫
        (mooreCochainIsoDerivedColimitApp U hU G).hom =
      (mooreCochainIsoDerivedColimitApp U hU F).hom ≫
        (totalDerivedColimit C (ModuleCat.{u} B)).map (DerivedCategory.Q.map
          ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).map a)) := by
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
    ((HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0).map a)
  dsimp only [mooreCochainIsoDerivedColimitApp, Iso.trans_hom]
  rw [← Category.assoc, htie, Category.assoc, hcmp, Category.assoc]

/-- **The derived form of [Stacks, Tag 08Q9] at module coefficients, as an isomorphism of
functors.** Let `C` be a small category with the chaotic topology, `B` a ring, and `U_•` a
cosimplicial object of `C` which is a point resolution. Then

`Q(ℱ(U_•)) ≅ Lπ_!(ℱ)` in `D(B)`,

**naturally in the diagram `ℱ` of `B`-modules**, where the left side is the extended Moore complex
of the simplicial `B`-module `ℱ(U_•)` and `Lπ_!` is the total left derived functor of the colimit
over `Cᵒᵖ`, which is `π_!` on the chaotic site by [Stacks, Tag 08PF]. -/
@[stacks 08Q9 "derived-category form at module coefficients, natural in the coefficient module: \
  the extended Moore complex of the evaluation on a point resolution is derived lower shriek as \
  an isomorphism of functors. Neither the degreewise form \
  `Stacks.ChaoticSite.leftDerivedColimitNatIso` nor the object-level \
  `Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit` provides this"]
def mooreCochainNatIsoDerivedColimit (hU : IsPointResolution U) :
    mooreCochainComplex (B := B) U ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single (Cᵒᵖ ⥤ ModuleCat.{u} B) (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙ totalDerivedColimit C (ModuleCat.{u} B) :=
  NatIso.ofComponents (fun F => mooreCochainIsoDerivedColimitApp U hU F)
    (fun a => mooreCochainIsoDerivedColimitApp_naturality U hU a)

end Stacks.ChaoticSite.ModuleValued

end

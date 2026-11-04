module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorPrecomposeExact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
import StacksCore.Tactic.StacksAttribute

/-!
# The coherator across an elementary distinguished square (Stacks 0CR6)

Let `(U ⊆ X, j_V : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` with `X`, `U`, `V` quasi-compact and quasi-separated, and let `P = U ×_X V`.  Remark
0CR6 of the Stacks project says that the coherators `DQ_X`, `DQ_U`, `DQ_V`, `DQ_P` (the right
adjoints of the inclusions `D_QCoh ⥤ D`, Stacks 0CR4) exist, and that for every `K` in `D(𝒪_X)`
there is a canonical distinguished triangle

`DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{P,*}DQ_P(K|_P) ⟶ DQ_X(K)[1]`,

obtained by applying the exact functor `DQ_X` to the Mayer–Vietoris triangle of Stacks 08GW and
using Stacks 0CR5 three times.  That is
`AlgebraicGeometry.Space.coherator_edsMayerVietoris_triangle`, whose statement writes the two maps
of the triangle out as exactly that composite.

## Main definitions and results

* `CategoryTheory.Pretriangulated.exists_mem_distTriang_map_biprodLift_biprodDesc_conj`: an exact
  functor carries a distinguished triangle `K ⟶ A ⊞ A' ⟶ P ⟶ K[1]` to a distinguished triangle
  with the images of its maps conjugated by any isomorphisms of the three image vertices.
* `AlgebraicGeometry.Space.restrictPushIsoDerivedPushforwardComp`: for an étale `j : Y ⟶ X`, the
  canonical isomorphism `R(j_*((-)|_Y)) ≅ Rj_* ∘ (-)|_Y` of right derived functors.
* `AlgebraicGeometry.Space.coheratorRestrictPushObjIso`: the isomorphism
  `DQ_X(R(j_*(K|_Y))) ≅ Rj_*DQ_Y(K|_Y)`, from the previous one and the étale case of Stacks 0CR5,
  `AlgebraicGeometry.Space.coheratorDerivedPushforwardIsoOfIsEtale`.
* `AlgebraicGeometry.Space.isQuasiCompact_edsInterHom`,
  `AlgebraicGeometry.Space.isQuasiSeparated_edsInterHom`: `P ⟶ X` is quasi-compact and
  quasi-separated.
* `AlgebraicGeometry.Space.coherator_edsMayerVietoris_triangle`: **Stacks 0CR6**.

## Implementation notes

The derived categories are the standard models `HasDerivedCategory.standard` of the neighbouring
files of this chapter, which is where the Mayer–Vietoris triangle of Stacks 08GW and the étale
case of Stacks 0CR5 are stated.  The coherators enter as arbitrary right adjoints, with their
adjunctions: they are unique up to unique isomorphism, and the statement holds for each choice.

## References

* [Stacks Project, Tag 0CR6](https://stacks.math.columbia.edu/tag/0CR6)
* [Stacks Project, Tag 0CR4](https://stacks.math.columbia.edu/tag/0CR4)
* [Stacks Project, Tag 0CR5](https://stacks.math.columbia.edu/tag/0CR5)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.SheafOfModules.Tensor (ringSheaf)
open CategoryTheory.PushforwardMayerVietoris

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace CategoryTheory.Pretriangulated

/-- An exact functor carries a distinguished triangle `K ⟶ A ⊞ A' ⟶ P ⟶ K[1]` whose maps are
`biprod.lift u v` and `biprod.desc p q` to a distinguished triangle
`G K ⟶ M ⊞ M' ⟶ N ⟶ (G K)[1]` for any isomorphisms `G A ≅ M`, `G A' ≅ M'`, `G P ≅ N`, with
maps the images of `u`, `v`, `p`, `q` under `G` conjugated by those isomorphisms. -/
theorem exists_mem_distTriang_map_biprodLift_biprodDesc_conj
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (G : C ⥤ D) [G.CommShift ℤ] [G.IsTriangulated]
    {K A A' P : C} (u : K ⟶ A) (v : K ⟶ A') (p : A ⟶ P) (q : A' ⟶ P)
    (δ : P ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (biprod.lift u v) (biprod.desc p q) δ ∈ distTriang C)
    {M M' N : D} (eA : G.obj A ≅ M) (eA' : G.obj A' ≅ M') (eP : G.obj P ≅ N) :
    ∃ δ' : N ⟶ (G.obj K)⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift (G.map u ≫ eA.hom) (G.map v ≫ eA'.hom))
        (biprod.desc (eA.inv ≫ G.map p ≫ eP.hom) (eA'.inv ≫ G.map q ≫ eP.hom)) δ' ∈
        distTriang D := by
  have : PreservesBinaryBiproduct A A' G := preservesBinaryBiproduct_of_preservesBinaryCoproduct G
  have hGT : Triangle.mk (G.map (biprod.lift u v)) (G.map (biprod.desc p q))
      (G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K) ∈ distTriang D :=
    G.map_distinguished _ hT
  refine ⟨eP.inv ≫ G.map δ ≫ (G.commShiftIso (1 : ℤ)).hom.app K,
    isomorphic_distinguished _ hGT _ (Triangle.isoMk _ _ (Iso.refl _)
    (biprod.mapIso eA.symm eA'.symm ≪≫ (G.mapBiprod A A').symm) eP.symm ?_ ?_ ?_)⟩
  · dsimp
    rw [Category.id_comp, biprod.mapIso_hom, Iso.symm_hom, Iso.symm_hom, biprod.lift_map_assoc]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, biprod.lift_mapBiprod]
  · apply biprod.hom_ext' <;> dsimp <;>
    simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, biprod.mapIso_hom, Iso.symm_hom, biprod.inl_map_assoc,
      biprod.inr_map_assoc, Functor.mapBiprod_inv, ← G.map_comp, biprod.inl_desc, biprod.inr_desc]
  · dsimp
    simp only [Functor.map_id, Category.comp_id]

end CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard isGrothendieckAbelian_modules
  enoughInjectives_modules
attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat
  hasRightDerivedFunctor_mapHomotopyCategory_modules hasRightDerivedFunctor_modulePushforward

/-! ### One vertex: `DQ_X(R(j_*((-)|_Y)))` is `Rj_* DQ_Y((-)|_Y)` -/

section Etale

variable {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W) (hj : IsEtale B S hS j.hom)

/-- **`R(j_*((-)|_Y)) ≅ Rj_* ∘ (-)|_Y` for an étale `j : Y ⟶ W`**, canonically: the restriction
`(-)|_Y` is exact and carries K-injective complexes to K-injective complexes, so
`(-)|_Y ⋙ Rj_*` is a right derived functor of `j_*((-)|_Y)`
(`Stacks.DerivedFunctor.isRightDerivedFunctor_precompose`), and two right derived functors of
one functor are canonically isomorphic (`CategoryTheory.Functor.rightDerivedUnique`).  Here
`Rj_*` is the chosen total right derived functor of the direct image. -/
def restrictPushIsoDerivedPushforwardComp
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))] :
    R ≅ (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory ⋙
      ((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)) :=
  have := Stacks.DerivedFunctor.isRightDerivedFunctor_precompose
    (etaleModulePullback.{u, u} B S hS j hj) (modulePushforward B S hS j)
    (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
    (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
    (exists_quasiIso_isKInjective_modules B S hS Y.1 Y.2)
    (exists_quasiIso_isKInjective_modules B S hS W.1 W.2)
    (isKInjective_etaleModulePullback_mapHomologicalComplex B S hS j hj)
  Functor.rightDerivedUnique R _ αR (Stacks.DerivedFunctor.precomposeUnit _ _ _
    (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))))
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))

/-- **The isomorphism `DQ_W(R(j_*(E|_Y))) ≅ Rj_* DQ_Y(E|_Y)` of Remark 0CR6 at one vertex**, for
an étale quasi-compact quasi-separated `j : Y ⟶ W`: the coherator `DQ_W` applied to the canonical
isomorphism `R(j_*((-)|_Y)) ≅ Rj_* ∘ (-)|_Y`
(`AlgebraicGeometry.Space.restrictPushIsoDerivedPushforwardComp`), followed by the isomorphism
`DQ_W ∘ Rj_* ≅ Rj_* ∘ DQ_Y` of Stacks 0CR5 for `j`
(`AlgebraicGeometry.Space.coheratorDerivedPushforwardIsoOfIsEtale`). -/
def coheratorRestrictPushObjIso (hjqc : IsQuasiCompact B S hS j.hom)
    (hjqs : IsQuasiSeparated B S hS j.hom)
    (R : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αR : (etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor αR
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))]
    (DQW : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      (qcohDerivedCategoryB B S hS W).FullSubcategory)
    (adjW : (qcohDerivedCategoryB B S hS W).ι ⊣ DQW)
    (DQY : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤
      (qcohDerivedCategoryB B S hS Y).FullSubcategory)
    (adjY : (qcohDerivedCategoryB B S hS Y).ι ⊣ DQY)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    (qcohDerivedCategoryB B S hS W).ι.obj (DQW.obj (R.obj E)) ≅
      (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))).obj
        ((qcohDerivedCategoryB B S hS Y).ι.obj
          (DQY.obj ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E))) :=
  (qcohDerivedCategoryB B S hS W).ι.mapIso
      (DQW.mapIso ((restrictPushIsoDerivedPushforwardComp B S hS j hj R αR).app E)) ≪≫
    (qcohDerivedCategoryB B S hS W).ι.mapIso
      ((coheratorDerivedPushforwardIsoOfIsEtale B S hS j hj hjqc hjqs _
        (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
        DQW adjW DQY adjY).app
        ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E)).symm ≪≫
    ((qcohDerivedCategoryB B S hS W).liftCompιIso ((qcohDerivedCategoryB B S hS Y).ι ⋙
      (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))))
      (fun E => derivedCategoryB_derivedPushforward_obj_of_isQuasiCompact_of_isQuasiSeparated
        B S hS j hjqc hjqs _
          (((modulePushforward B S hS j).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ)))
        E.obj E.property)).app
      (DQY.obj ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj E))

end Etale

/-! ### The intersection of the square -/

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- `j_{U ×_X V} : U ×_X V ⟶ X` is quasi-compact when `X` is quasi-separated and `U`, `V` are
quasi-compact: it is the base change `U ×_X V ⟶ U` of the quasi-compact `j_V` (Stacks 03HF)
followed by the quasi-compact `j_U` (Stacks 03HG), and `j_U`, `j_V` are quasi-compact by
Stacks 073B. -/
theorem isQuasiCompact_edsInterHom
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVqc : IsQuasiCompactSpace B S hS V) :
    IsQuasiCompact B S hS (edsInterHom B S hS hsq).hom :=
  IsQuasiCompact.comp B S hS (edsOpen B S hS hsq).2 W.2
    (isQuasiCompact_of_isPullback B S hS
      (IsPullback.of_hasPullback (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom).flip
      (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hWqs hVqc _))
    (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hWqs hUqc _)

/-- `j_{U ×_X V} : U ×_X V ⟶ X` is quasi-separated when `U` and `V` are quasi-separated: it is the
base change `U ×_X V ⟶ U` of the quasi-separated `j_V` followed by the quasi-separated `j_U`
(Stacks 073B, 03KQ). -/
theorem isQuasiSeparated_edsInterHom
    (hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Uo.toFunctor)
    (hVqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal V) :
    IsQuasiSeparated B S hS (edsInterHom B S hS hsq).hom :=
  isQuasiSeparated_comp B S hS (edsInter B S hS hsq).2 (edsOpen B S hS hsq).2 _ _
    (isQuasiSeparated_of_isPullback B S hS
      (IsPullback.of_hasPullback (edsOpenHom B S hS hsq).hom (edsEtaleHom B S hS hsq).hom).flip
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal
        (edsEtale B S hS hsq).2 hVqs _))
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal
      (edsOpen B S hS hsq).2 hUqs _)

end Square

/-! ### Remark 0CR6 -/

section Remark

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- **Stacks 0CR6.**  Let `S` be a scheme and `(U ⊆ X, j_V : V ⟶ X)` an elementary distinguished
square of algebraic spaces over `S` (here `X = W`, `U = Uo`, `j_V = fV`) with `X`, `U` and `V`
quasi-compact and quasi-separated, and let `P = U ×_X V`.

1. *The functors `DQ_X`, `DQ_U`, `DQ_V`, `DQ_P` exist*: the four inclusions
   `D_QCoh ⥤ D` have right adjoints (Stacks 0CR4, at the four spaces; `P` is quasi-compact and
   quasi-separated by `AlgebraicGeometry.Space.isQuasiCompact_edsInterHom` and
   `AlgebraicGeometry.Space.isQuasiSeparated_edsInterHom`).
2. *The canonical triangle*: for every choice of these right adjoints, with their adjunctions,
   and every `K` in `D(𝒪_X)` there is a distinguished triangle

   `DQ_X(K) ⟶ Rj_{U,*}DQ_U(K|_U) ⊕ Rj_{V,*}DQ_V(K|_V) ⟶ Rj_{P,*}DQ_P(K|_P) ⟶ DQ_X(K)[1]`

   **whose two maps are the canonical ones**: the exact functor `DQ_X` applied to the two maps of
   the Mayer–Vietoris triangle of Stacks 08GW
   (`AlgebraicGeometry.Space.exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek`,
   whose maps are written out here verbatim: the derived units `K ⟶ R(j_{Y,*}(K|_Y))` and the
   difference of the derived comparisons `R(j_{U,*}(K|_U)) ⟶ R(j_{P,*}(K|_P))`,
   `R(j_{V,*}(K|_V)) ⟶ R(j_{P,*}(K|_P))`), conjugated by the three isomorphisms
   `DQ_X(R(j_{Y,*}(K|_Y))) ≅ Rj_{Y,*}DQ_Y(K|_Y)`
   (`AlgebraicGeometry.Space.coheratorRestrictPushObjIso`), which are Stacks 0CR5 for the étale
   morphism `j_Y` composed with `DQ_X` of the canonical identification
   `R(j_{Y,*}((-)|_Y)) ≅ Rj_{Y,*}((-)|_Y)`.  Only the connecting map is existentially
   quantified, as in Stacks 08GW.

`Rj_{Y,*}` is the chosen total right derived functor of the direct image along `j_Y`, and the
derived categories are the standard model `HasDerivedCategory.standard`, in which Stacks 08GW is
stated.  The hypotheses are the source's: `hWqc`, `hWqs` say that `X` is quasi-compact and
quasi-separated, `hUqc`, `hUqs` that `U` is, and `hVqc`, `hVqs` that `V` is (quasi-separated in
the absolute sense, over `Spec ℤ`, as in Stacks 0CR4). -/
@[stacks 0CR6]
theorem coherator_edsMayerVietoris_triangle
    (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal W.1)
    (hUqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Uo.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V)
    (hVqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal V) :
    ((qcohDerivedCategoryB B S hS W).ι.IsLeftAdjoint ∧
      (qcohDerivedCategoryB B S hS (edsOpen B S hS hsq)).ι.IsLeftAdjoint ∧
      (qcohDerivedCategoryB B S hS (edsEtale B S hS hsq)).ι.IsLeftAdjoint ∧
      (qcohDerivedCategoryB B S hS (edsInter B S hS hsq)).ι.IsLeftAdjoint) ∧
    ∀ (DQX : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
        (qcohDerivedCategoryB B S hS W).FullSubcategory)
      (adjX : (qcohDerivedCategoryB B S hS W).ι ⊣ DQX)
      (DQU : DerivedCategory (Modules.{u, u} B S hS (edsOpen B S hS hsq).1
          (edsOpen B S hS hsq).2) ⥤
        (qcohDerivedCategoryB B S hS (edsOpen B S hS hsq)).FullSubcategory)
      (adjU : (qcohDerivedCategoryB B S hS (edsOpen B S hS hsq)).ι ⊣ DQU)
      (DQV : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
          (edsEtale B S hS hsq).2) ⥤
        (qcohDerivedCategoryB B S hS (edsEtale B S hS hsq)).FullSubcategory)
      (adjV : (qcohDerivedCategoryB B S hS (edsEtale B S hS hsq)).ι ⊣ DQV)
      (DQP : DerivedCategory (Modules.{u, u} B S hS (edsInter B S hS hsq).1
          (edsInter B S hS hsq).2) ⥤
        (qcohDerivedCategoryB B S hS (edsInter B S hS hsq)).FullSubcategory)
      (adjP : (qcohDerivedCategoryB B S hS (edsInter B S hS hsq)).ι ⊣ DQP)
      (K : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)),
      ∃ δ, Triangle.mk
        (biprod.lift
          ((qcohDerivedCategoryB B S hS W).ι.map (DQX.map
            ((derivedUnitOfNatTrans (edsAdjOpen B S hS hsq).unit
              (edsDerivedRestrictPushOpen B S hS hsq)
              (edsTotalRightDerivedUnitOpen B S hS hsq)).app K)) ≫
            (coheratorRestrictPushObjIso B S hS (edsOpenHom B S hS hsq)
              (isEtale_edsOpenHom B S hS hsq)
              (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hWqs hUqc _)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal
                (edsOpen B S hS hsq).2 hUqs _)
              (edsDerivedRestrictPushOpen B S hS hsq) (edsTotalRightDerivedUnitOpen B S hS hsq)
              DQX adjX DQU adjU K).hom)
          ((qcohDerivedCategoryB B S hS W).ι.map (DQX.map
            ((derivedUnitOfNatTrans (edsAdjEtale B S hS hsq).unit
              (edsDerivedRestrictPushEtale B S hS hsq)
              (edsTotalRightDerivedUnitEtale B S hS hsq)).app K)) ≫
            (coheratorRestrictPushObjIso B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS hsq)
              (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hWqs hVqc _)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal
                (edsEtale B S hS hsq).2 hVqs _)
              (edsDerivedRestrictPushEtale B S hS hsq) (edsTotalRightDerivedUnitEtale B S hS hsq)
              DQX adjX DQV adjV K).hom))
        (biprod.desc
          ((coheratorRestrictPushObjIso B S hS (edsOpenHom B S hS hsq)
              (isEtale_edsOpenHom B S hS hsq)
              (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hWqs hUqc _)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal
                (edsOpen B S hS hsq).2 hUqs _)
              (edsDerivedRestrictPushOpen B S hS hsq) (edsTotalRightDerivedUnitOpen B S hS hsq)
              DQX adjX DQU adjU K).inv ≫
            (qcohDerivedCategoryB B S hS W).ι.map (DQX.map
            ((Functor.rightDerivedNatTrans (edsDerivedRestrictPushOpen B S hS hsq)
              (edsDerivedRestrictPushInter B S hS hsq)
              (edsTotalRightDerivedUnitOpen B S hS hsq)
              (edsTotalRightDerivedUnitInter B S hS hsq)
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (conjugateEquiv ((edsAdjOpen B S hS hsq).comp
                    (edsLowerShriekAdjOpen B S hS hsq))
                  ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                  (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
                    (edsLowerShriekAdjInter B S hS hsq)))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app K)) ≫
            (coheratorRestrictPushObjIso B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)
              (isQuasiCompact_edsInterHom B S hS hsq hWqs hUqc hVqc)
              (isQuasiSeparated_edsInterHom B S hS hsq hUqs hVqs)
              (edsDerivedRestrictPushInter B S hS hsq) (edsTotalRightDerivedUnitInter B S hS hsq)
              DQX adjX DQP adjP K).hom)
          ((coheratorRestrictPushObjIso B S hS (edsEtaleHom B S hS hsq)
              (isEtale_edsEtaleHom B S hS hsq)
              (isQuasiCompact_of_isQuasiCompactSpace B S hS B.contains_terminal W.2 hWqs hVqc _)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS B.contains_terminal
                (edsEtale B S hS hsq).2 hVqs _)
              (edsDerivedRestrictPushEtale B S hS hsq) (edsTotalRightDerivedUnitEtale B S hS hsq)
              DQX adjX DQV adjV K).inv ≫
            (qcohDerivedCategoryB B S hS W).ι.map (DQX.map
            (-((Functor.rightDerivedNatTrans (edsDerivedRestrictPushEtale B S hS hsq)
              (edsDerivedRestrictPushInter B S hS hsq)
              (edsTotalRightDerivedUnitEtale B S hS hsq)
              (edsTotalRightDerivedUnitInter B S hS hsq)
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ))
              (Functor.whiskerRight (NatTrans.mapHomotopyCategory
                (conjugateEquiv ((edsAdjEtale B S hS hsq).comp
                    (edsLowerShriekAdjEtale B S hS hsq))
                  ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
                  (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
                    (edsLowerShriekAdjInter B S hS hsq)))
                (ComplexShape.up ℤ)) DerivedCategory.Qh)).app K))) ≫
            (coheratorRestrictPushObjIso B S hS (edsInterHom B S hS hsq)
              (isEtale_edsInterHom B S hS hsq)
              (isQuasiCompact_edsInterHom B S hS hsq hWqs hUqc hVqc)
              (isQuasiSeparated_edsInterHom B S hS hsq hUqs hVqs)
              (edsDerivedRestrictPushInter B S hS hsq) (edsTotalRightDerivedUnitInter B S hS hsq)
              DQX adjX DQP adjP K).hom))
        δ ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) := by
  refine ⟨⟨isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite B S hS W hWqc hWqs
      (HasDerivedCategory.standard _),
    isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite B S hS (edsOpen B S hS hsq) hUqc hUqs
      (HasDerivedCategory.standard _),
    isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite B S hS (edsEtale B S hS hsq) hVqc hVqs
      (HasDerivedCategory.standard _),
    isLeftAdjoint_ι_derivedCategoryB_isQuasicoherentOnSite B S hS (edsInter B S hS hsq)
      (isQuasiCompactSpace_of_isQuasiCompact B S hS W.2 hWqc _
        (isQuasiCompact_edsInterHom B S hS hsq hWqs hUqc hVqc))
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal
        (edsInter B S hS hsq).2 hWqs (isQuasiSeparated_edsInterHom B S hS hsq hUqs hVqs))
      (HasDerivedCategory.standard _)⟩, ?_⟩
  intro DQX adjX DQU adjU DQV adjV DQP adjP K
  let : DQX.CommShift ℤ := adjX.rightAdjointCommShift ℤ
  let : adjX.CommShift ℤ := adjX.commShift_of_leftAdjoint ℤ
  have : adjX.IsTriangulated := Adjunction.IsTriangulated.mk' adjX
  obtain ⟨δ, hT⟩ :=
    exists_mem_distTriang_edsDerivedRestrictPushMayerVietorisLowerShriek B S hS hsq K
  exact exists_mem_distTriang_map_biprodLift_biprodDesc_conj
    (DQX ⋙ (qcohDerivedCategoryB B S hS W).ι) _ _ _ _ δ hT _ _ _

end Remark

end AlgebraicGeometry.Space

end

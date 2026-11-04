module

public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceFibre
public import StacksFrontier.Cotangent.SheavesOfRings.PolynomialChartSpaceFibred
public import StacksFrontier.Cotangent.StandardResolution
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.ProjectionLowerShriekAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.Derived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.PointResolution.FibreHomology
import StacksCore.Tactic.StacksAttribute

/-!
# The standard resolutions of the sections of an algebraic space as cosimplicial charts

Let `X` be an algebraic space over a ring `Λ`, let `C_{X/Λ}` be its category of polynomial charts,
fibred over the small étale site `X_étale`, and let `π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)` be the
induced morphism of topoi. For an object `U` of `X_étale` let `P_{•,U}` be the standard
resolution of `𝒪_X(U)` over `Λ` and put `𝐀_{•,U} = Spec(P_{•,U})`. A morphism `V ⟶ U` of
`X_étale` restricts the sections, hence maps `P_{•,U} ⟶ P_{•,V}`, hence maps the charts
`𝐀_{•,V} ⟶ 𝐀_{•,U}` over `V ⟶ U`; so `U ↦ 𝐀_{•,U}` is a functor from `X_étale` to cosimplicial
objects of `C_{X/Λ}` lying over the identity. Its fibrewise cosimplicial objects satisfy the
condition of Cohomology on Sites, Lemma 08Q9 by Tag 08PT, so the computation of `Lπ_!` by a
fibrewise point resolution applies: this is Stacks 08VL.

All declarations are in the namespace `AlgebraicGeometry.Space.PolynomialChart`.

## Main definitions

* `standardResolutionChart`: the functor `U ↦ 𝐀_{•,U}`.
* `fibredCategorySituation`: the fibred category situation of Tag 08P8 formed by
  `C_{X/Λ} ⥤ X_étale` over the ringed site `(X_étale, 𝒪_X)`.

## Main results

* `standardResolutionChart_comp_whiskeringRight`: `U ↦ 𝐀_{•,U}` lies over the identity of
  `X_étale`.
* `exists_homotopyEquivalences_standardResolutionChart`: the condition of Tag 08Q9 on each
  `𝐀_{•,U}`.
* `standardResolutionChart_computes_derivedAbelianLowerShriek`: **Stacks 08VL**.

## Implementation notes

The complex of presheaves, its fibrewise homology and the two comparisons with `Lπ_!` are those of
an arbitrary fibrewise point resolution of a fibred category, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/PointResolution/`; the derived lower
shriek exists with no hypothesis by
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriekAcyclic.lean`.
Abelian sheaves are taken with sections in `Type (u + 1)`, the universe of the objects of
`C_{X/Λ}`, in which `π` is formed.

## References

* [Stacks Project, Tag 08VL](https://stacks.math.columbia.edu/tag/08VL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.PolynomialChart

noncomputable section

variable (Λ : Type u) [CommRing Λ] (B : BigFppfSite.{u})
  (hS : B.Contains (Spec (CommRingCat.of Λ)))
  (X : (BigFppfOver B (Spec (CommRingCat.of Λ)) hS)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (CommRingCat.of Λ)) hS X)

/-- The morphism of polynomial charts `specChart a ⟶ specChart b` over an arrow `f : V ⟶ U` of
the small étale site attached to a map of `Λ`-algebras `ψ` between the polynomial algebras which
is compatible with the augmentations `a ⟶ 𝒪_X(V)`, `b ⟶ 𝒪_X(U)` and restriction along `f`. -/
def specChartHomOver {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (f : V ⟶ U)
    {a : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X V)}
    {b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)}
    (ψ : b.unop.obj.left ⟶ a.unop.obj.left)
    (hψ : ψ ≫ a.unop.obj.hom = b.unop.obj.hom ≫ sectionsAlgebraRestrict Λ B hS X f) :
    specChart Λ B hS X hX V a ⟶ specChart Λ B hS X hX U b where
  openMap := f
  affine := Spec.map (CommRingCat.ofHom ψ.hom.toRingHom)
  map_comm := by
    change specAugmentation Λ B hS X V a.unop.obj.hom ≫
        Spec.map (CommRingCat.ofHom ψ.hom.toRingHom) =
      (smallEtaleToScheme Λ B hS X).map f ≫ specAugmentation Λ B hS X U b.unop.obj.hom
    have h : CommRingCat.ofHom ψ.hom.toRingHom ≫
        augmentationRingHom Λ B hS X V a.unop.obj.hom =
        augmentationRingHom Λ B hS X U b.unop.obj.hom ≫
          ((smallEtaleToScheme Λ B hS X).map f).appTop := by
      ext x
      exact commAlgCat_apply_congr Λ hψ x
    rw [specAugmentation, specAugmentation, Category.assoc, ← Spec.map_comp, h, Spec.map_comp,
      ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc]
  base_comm := by
    change Spec.map (CommRingCat.ofHom ψ.hom.toRingHom) ≫ (specChart Λ B hS X hX U b).toBase =
      (specChart Λ B hS X hX V a).toBase
    rw [specChart_toBase, specChart_toBase, ← Spec.map_comp]
    congr 1
    ext r
    exact ψ.hom.commutes r

/-- The map of affine spaces of `specChartHomOver f ψ hψ` is the spectrum of `ψ`. -/
@[simp]
theorem specChartHomOver_affine {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (f : V ⟶ U)
    {a : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X V)}
    {b : CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U)}
    (ψ : b.unop.obj.left ⟶ a.unop.obj.left)
    (hψ : ψ ≫ a.unop.obj.hom = b.unop.obj.hom ≫ sectionsAlgebraRestrict Λ B hS X f) :
    (specChartHomOver Λ B hS X hX f ψ hψ).affine =
      Spec.map (CommRingCat.ofHom ψ.hom.toRingHom) := rfl

/-- The standard resolution `P_{•,U}` of `𝒪_X(U)` over `Λ`, functorially in the object `U` of the
small étale site of `X`. -/
abbrev sectionsStandardResolution :
    (SmallEtale B (Spec (CommRingCat.of Λ)) hS X)ᵒᵖ ⥤
      SimplicialObject.Augmented (CommAlgCat.{u} Λ) :=
  sectionsAlgebraPresheaf Λ B hS X ⋙ CommAlgCat.standardResolutionFunctor.{u, u} Λ

/-- **Stacks 08VL.** The functorial cosimplicial polynomial charts of the standard resolutions:
over an object `U` of the small étale site of `X` it is `𝐀_{•,U} = Spec(P_{•,U})`, read in
`C_{X/Λ}`, and an arrow `V ⟶ U` induces `𝐀_{•,V} ⟶ 𝐀_{•,U}` through the map of standard
resolutions `P_{•,U} ⟶ P_{•,V}` given by restriction of sections. -/
def standardResolutionChart :
    SmallEtale B (Spec (CommRingCat.of Λ)) hS X ⥤
      CosimplicialObject (PolynomialChart Λ B hS X hX) where
  obj U := standardChartCosimplicialObject Λ B hS X hX U ⋙ Functor.Fiber.fiberInclusion
  map {V U} f :=
    { app := fun n => specChartHomOver Λ B hS X hX f
        (((sectionsStandardResolution Λ B hS X).map f.op).left.app (op n))
        (NatTrans.congr_app ((sectionsStandardResolution Λ B hS X).map f.op).w (op n))
      naturality := fun {n m} g => by
        refine Hom.ext rfl ?_
        · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
          rw [← Spec.map_comp, ← Spec.map_comp]
          congr 1
          ext x
          exact (commAlgCat_apply_congr Λ
            (((sectionsStandardResolution Λ B hS X).map f.op).left.naturality g.op) x).symm }
  map_id U := by
    refine NatTrans.ext (funext fun n => Hom.ext rfl ?_)
    · change Spec.map _ = 𝟙 _
      rw [← Spec.map_id]
      congr 1
      ext x
      change ((((sectionsStandardResolution Λ B hS X).map (𝟙 (op U))).left.app (op n)).hom x) = x
      rw [CategoryTheory.Functor.map_id]
      rfl
  map_comp {W V U} f g := by
    refine NatTrans.ext (funext fun n => Hom.ext rfl ?_)
    · change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      ext x
      change ((((sectionsStandardResolution Λ B hS X).map (g.op ≫ f.op)).left.app (op n)).hom x) =
        _
      rw [CategoryTheory.Functor.map_comp]
      rfl

/-- The chart in degree `n` of `standardResolutionChart` over `U` lies over `U`. -/
@[simp]
theorem standardResolutionChart_obj_obj_openPart (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X)
    (n : SimplexCategory) :
    (((standardResolutionChart Λ B hS X hX).obj U).obj n).openPart = U := rfl

/-- The arrow of the small étale site underlying the chart map induced by `f : V ⟶ U` is `f`. -/
@[simp]
theorem standardResolutionChart_map_app_openMap
    {U V : SmallEtale B (Spec (CommRingCat.of Λ)) hS X} (f : V ⟶ U) (n : SimplexCategory) :
    (((standardResolutionChart Λ B hS X hX).map f).app n).openMap = f := rfl

/-- `𝐀_{•,U}` lies in the fibre of `C_{X/Λ}` over `U`: composing it with the forgetful functor to
the small étale site gives the constant functor at `U`. -/
theorem standardResolutionChart_comp_openFunctor
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    (standardResolutionChart Λ B hS X hX).obj U ⋙
        openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX) =
      (Functor.const SimplexCategory).obj U :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => rfl

/-- Read in the fibre over `U`, the cosimplicial charts of `standardResolutionChart` over `U` are
`standardChartCosimplicialObject`. -/
theorem inducedFunctor_standardResolutionChart_comp_openFunctor
    (U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X) :
    Functor.Fiber.inducedFunctor (standardResolutionChart_comp_openFunctor Λ B hS X hX U) =
      standardChartCosimplicialObject Λ B hS X hX U := rfl

/-- The fibred category situation of Tag 08P8 formed by the polynomial charts of `X`: the small
étale ringed site `(X_étale, 𝒪_X)` and the fibred forgetful functor `C_{X/Λ} ⥤ X_étale`. -/
def fibredCategorySituation :
    Stacks.Sites.FibredCategory.FibredCategorySituation.{u + 1, u, u + 1, u, u} where
  base := smallEtaleRingedSite B (Spec (CommRingCat.of Λ)) hS X hX
  C := PolynomialChart Λ B hS X hX
  p := openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)
  isFibered := openFunctor_isFibered Λ B hS X hX

/-- `U ↦ 𝐀_{•,U}` lies over the identity of the small étale site: postcomposed with the forgetful
functor, every `𝐀_{•,U}` is the constant cosimplicial object at `U` and every map
`𝐀_{•,V} ⟶ 𝐀_{•,U}` is the constant one at the given arrow `V ⟶ U`. -/
theorem standardResolutionChart_comp_whiskeringRight :
    (standardResolutionChart Λ B hS X hX : (fibredCategorySituation Λ B hS X hX).base.C ⥤
        CosimplicialObject (fibredCategorySituation Λ B hS X hX).C) ⋙
      (Functor.whiskeringRight SimplexCategory (fibredCategorySituation Λ B hS X hX).C
        (fibredCategorySituation Λ B hS X hX).base.C).obj
          (fibredCategorySituation Λ B hS X hX).p =
      Functor.const SimplexCategory :=
  CategoryTheory.Functor.ext (fun U => standardResolutionChart_comp_openFunctor Λ B hS X hX U)
    fun V U f => by
      ext n
      simp only [NatTrans.comp_app, eqToHom_app, Functor.const_map_app]
      exact (Category.id_comp _).symm.trans (Category.comp_id _).symm

/-- **The condition of Tag 08Q9 on `U ↦ 𝐀_{•,U}`.** For every object `U` of the small étale site
and every object `W` of the fibre over `U`, the simplicial set `Mor(𝐀_{•,U}, W)` of the fibre is
homotopy equivalent to a singleton. This is
`exists_homotopyEquivalences_standardChartMor`, read through
`standardResolutionChart_comp_whiskeringRight`. -/
theorem exists_homotopyEquivalences_standardResolutionChart
    (U : (fibredCategorySituation Λ B hS X hX).base.C)
    (W : (fibredCategorySituation Λ B hS X hX).p.Fiber U) :
    ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj
          (standardResolutionChart_comp_whiskeringRight Λ B hS X hX) U)).op ⋙ yoneda.obj W ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
      SimplicialObject.homotopyEquivalences (Type u) f :=
  exists_homotopyEquivalences_standardChartMor Λ B hS X hX U W

/-- The small étale site of `X` has fibre products, read on the base of the fibred category
situation. -/
instance hasPullbacks_fibredCategorySituation_base :
    HasPullbacks (fibredCategorySituation Λ B hS X hX).base.C :=
  inferInstanceAs (HasPullbacks (SmallEtale B (Spec (CommRingCat.of Λ)) hS X))

section Remark

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 08VL.** Let `X` be an algebraic space over a ring `Λ`, let `C_{X/Λ}` be its category
of polynomial charts, fibred over `X_étale`, and let `π : Sh(C_{X/Λ}) ⟶ Sh(X_étale)` be the
induced morphism of topoi. For an object `U` of `X_étale` let `P_{•,U}` be the standard resolution
of `𝒪_X(U)` over `Λ` and `𝐀_{•,U} = Spec(P_{•,U})` (`standardResolutionChart`). Then:

* the fibre of `C_{X/Λ}` over `U` is the site `C_{𝒪_X(U)/Λ}`, and through this identification
  `𝐀_{•,U}` is the cosimplicial object of `P_{•,U}`;
* `𝐀_{•,U}` is a cosimplicial object of the fibre over `U`, functorially in `U`;
* it is a cosimplicial object as in Cohomology on Sites, Lemma 08Q9: every simplicial set
  `Mor(𝐀_{•,U}, W)` is homotopy equivalent to a singleton;
* for every abelian sheaf `ℱ` on `C_{X/Λ}`, the homology at `U` of the complex of presheaves
  `U ↦ ℱ(𝐀_{•,U})` is the homology `H_n(C_U, ℱ|_{C_U})` of `ℱ` on the fibre category;
* its sheafified homology computes `L_nπ_!(ℱ)`;
* the complex of sheaves whose term in degree `-n` is the sheafification of `U ↦ ℱ(𝐀_{n,U})`
  computes `Lπ_!(ℱ)`. -/
@[stacks 08VL]
theorem standardResolutionChart_computes_derivedAbelianLowerShriek :
    (∀ U : SmallEtale B (Spec (CommRingCat.of Λ)) hS X,
      ∃ e : (openFunctor (Λ := Λ) (B := B) (hS := hS) (X := X) (hX := hX)).Fiber U ≌
          CommAlgCat.polynomialSite Λ (sectionsAlgebra Λ B hS X U),
        Nonempty (standardChartCosimplicialObject Λ B hS X hX U ⋙ e.functor ≅
          CommAlgCat.resolutionCosimplicialObject
            (CommAlgCat.standardResolution.{u, u} Λ (sectionsAlgebra Λ B hS X U)).hom
            (CommAlgCat.standardResolution_isResolution.{u, u} Λ
              (sectionsAlgebra Λ B hS X U)).isPolynomialAlgebra)) ∧
    (standardResolutionChart Λ B hS X hX : (fibredCategorySituation Λ B hS X hX).base.C ⥤
        CosimplicialObject (fibredCategorySituation Λ B hS X hX).C) ⋙
      (Functor.whiskeringRight SimplexCategory (fibredCategorySituation Λ B hS X hX).C
        (fibredCategorySituation Λ B hS X hX).base.C).obj
          (fibredCategorySituation Λ B hS X hX).p =
      Functor.const SimplexCategory ∧
    (∀ (U : (fibredCategorySituation Λ B hS X hX).base.C)
      (W : (fibredCategorySituation Λ B hS X hX).p.Fiber U),
      ∃ f : (Functor.Fiber.inducedFunctor (Functor.congr_obj
            (standardResolutionChart_comp_whiskeringRight Λ B hS X hX) U)).op ⋙
            yoneda.obj W ⟶
          (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1},
        SimplicialObject.homotopyEquivalences (Type u) f) ∧
    ∀ F : Sheaf (fibredCategorySituation Λ B hS X hX).topology AddCommGrpCat.{u + 1},
      (∀ (U : (fibredCategorySituation Λ B hS X hX).base.C) (n : ℕ),
        Nonempty (((((fibredCategorySituation Λ B hS X hX).pointMooreComplex
            (standardResolutionChart Λ B hS X hX)).obj F.obj).homology n).obj (op U) ≅
          Stacks.CategoryHomology.categoryHomology.{u + 1, u + 1}
            ((fibredCategorySituation Λ B hS X hX).smallFiberRestriction F.obj U) n)) ∧
      (∀ n : ℕ, Nonempty ((DerivedCategory.homologyFunctor _ (-(n : ℤ))).obj
          ((fibredCategorySituation Λ B hS X hX).derivedAbelianLowerShriek.obj
            ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
        (presheafToSheaf (fibredCategorySituation Λ B hS X hX).base.J AddCommGrpCat.{u + 1}).obj
          ((((fibredCategorySituation Λ B hS X hX).pointMooreComplex
            (standardResolutionChart Λ B hS X hX)).obj F.obj).homology n))) ∧
      Nonempty ((fibredCategorySituation Λ B hS X hX).derivedAbelianLowerShriek.obj
          ((DerivedCategory.singleFunctor _ 0).obj F) ≅
        DerivedCategory.Q.obj ((fibredCategorySituation Λ B hS X hX).pointSheafComplex
          (standardResolutionChart Λ B hS X hX) F.obj)) := by
  have hover := standardResolutionChart_comp_whiskeringRight Λ B hS X hX
  have hhtpy := exists_homotopyEquivalences_standardResolutionChart Λ B hS X hX
  refine ⟨fun U => ⟨fibreEquivalence Λ B hS X hX U, ⟨Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (fibreEquivalence Λ B hS X hX U).counitIso ≪≫
        Functor.rightUnitor _⟩⟩,
    hover, hhtpy, fun F => ⟨fun U n => ?_, fun n => ?_, ?_⟩⟩
  · exact ⟨(fibredCategorySituation Λ B hS X hX).categoryHomologyFiberIso
      hover hhtpy F.obj U n⟩
  · exact (fibredCategorySituation Λ B hS X hX).nonempty_derivedAbelianLowerShriekHomologyIso
      hover hhtpy F n
  · exact (fibredCategorySituation Λ B hS X hX).nonempty_derivedAbelianLowerShriekIso
      hover hhtpy F

end Remark

end

end AlgebraicGeometry.Space.PolynomialChart

end

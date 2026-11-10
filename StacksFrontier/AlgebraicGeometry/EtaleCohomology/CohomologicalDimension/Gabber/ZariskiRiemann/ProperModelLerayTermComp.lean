module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLimitStep
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeMate
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.DegreewiseForgetExcisionSquare

/-!
# The pasting law for the base change map on higher direct images

For a commutative square `g' ≫ f = f' ≫ g` of schemes and an abelian sheaf `F`,
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange` is the
degree-`q` base change map `g⁻¹ R^q f_* F ⟶ R^q f'_* (g')⁻¹ F`, read off the derived base change
map `g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` on cohomology sheaves. This file proves that these maps paste
along a tower of two commutative squares
(`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange_comp`). For
the transition maps `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.lerayTermMap`
of the Leray `E₂`-terms of proper models in Gabber's Zariski–Riemann argument, this is the cocycle
of the base change maps of the squares `𝟙 ≫ j = j' ≫ π` along a composite of refinements.

The pasting law is read off the pasting law for the derived base change map,
`Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange_comp_app`. That reading needs the derived
composition isomorphism of inverse images to be compatible with the comparisons of an exact
functor with the homology functors and with the functors placing a sheaf in degree `0`; these
coherences are stated in the development for
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso`, so the first result here identifies
the étale composition isomorphism
`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'` with it.

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianRightDerivedBaseChangeMap` — the degree-`q` base change map
  at an arbitrary coefficient universe.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_inv_eq` — the derived
  composition isomorphism of étale inverse images is that of the degreewise functors.
* `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_homology` and
  `Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_single` — its compatibility with
  homology and with the single functors.
* `Stacks.EtaleCohomology.etaleAbelianRightDerivedBaseChangeMap_comp` and
  `Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange_comp` — **the
  pasting law for the base change map on higher direct images.**

## Implementation notes

The pasting law is proved at an arbitrary coefficient universe `v` and specialised to `v = 0`.
Proved directly at `v = 0`, the rewrite with the single-functor coherence produced a kernel
deterministic timeout: the coherence, instantiated from its universe-polymorphic statement, spells
the coefficient universe `max (u + 1) 0` where the goal's explicit binders spell `u + 1`. At a
general `v` every universe is spelled `max (u + 1) v` and the kernel check is immediate.

## References

* [Stacks Project, Tag 0A4A](https://stacks.math.columbia.edu/tag/0A4A)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Bridge

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)

/-- The lifting of the degreewise composite of two inverse images along `Qh`, written out. -/
private alias liftingIso_comp' := Stacks.EtaleCohomology.liftingIso_comp

/-- The inverse of the derived composition isomorphism at the object represented by a complex. -/
private alias etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh' :=
  Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh

/-- **The derived composition isomorphism of étale inverse images is Mathlib's.** The inverse of
`Stacks.EtaleCohomology.etaleAbelianDerivedInverseImageCompIso'` is the composition isomorphism
`CategoryTheory.Functor.mapDerivedCategoryCompIsoOfCompIso` of the degreewise functors, attached to
the inverse of the composition isomorphism `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` of inverse images of sheaves.
Both are lifts along `DerivedCategory.Qh` of the same degreewise transformation. -/
theorem etaleAbelianDerivedInverseImageCompIso'_inv_eq :
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).inv =
      (Functor.mapDerivedCategoryCompIsoOfCompIso
        (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).symm).hom := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) fun K => ?_
  rw [etaleAbelianDerivedInverseImageCompIso'_inv_app_Qh',
    Functor.mapDerivedCategoryCompIso_hom_app_Qh]

/-- **The derived composition isomorphism on cohomology sheaves.** Through the comparisons
`Hⁿ(m⁻¹ K) ≅ m⁻¹ Hⁿ(K)` of the exact inverse images with the homology functors, the derived
composition isomorphism `(f ≫ g)⁻¹ ≅ g⁻¹ ⋙ f⁻¹` is the composition isomorphism of inverse images
of sheaves. -/
theorem etaleAbelianDerivedInverseImageCompIso'_homology (n : ℤ)
    (K : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) :
    ((etaleAbelianInverseImage.{u, v} fg).mapDerivedCategoryHomologyIso n).inv.app K ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).hom.app K) =
      (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).hom.app
          ((DerivedCategory.homologyFunctor _ n).obj K) ≫
        (etaleAbelianInverseImage.{u, v} f).map
          (((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryHomologyIso n).inv.app K) ≫
        ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryHomologyIso n).inv.app
          ((etaleAbelianDerivedInverseImage.{u, v} g).obj K) := by
  have h := congrArg (fun τ => τ.app K)
    (Stacks.DerivedIndexing.mapDerivedCategoryHomologyIso_compIso
      (F := etaleAbelianInverseImage.{u, v} g) (G := etaleAbelianInverseImage.{u, v} f)
      (H := etaleAbelianInverseImage.{u, v} fg)
      (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).symm n)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    ← etaleAbelianDerivedInverseImageCompIso'_inv_eq] at h
  have hiso : ((DerivedCategory.homologyFunctor _ n).mapIso
        ((etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).app K)).symm ≪≫
      ((etaleAbelianInverseImage.{u, v} fg).mapDerivedCategoryHomologyIso n).app K =
      ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryHomologyIso n).app
          ((etaleAbelianDerivedInverseImage.{u, v} g).obj K) ≪≫
        (etaleAbelianInverseImage.{u, v} f).mapIso
          (((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryHomologyIso n).app K) ≪≫
        ((etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).app
          ((DerivedCategory.homologyFunctor _ n).obj K)).symm :=
    Iso.ext h
  have h' := congrArg Iso.inv hiso
  simpa using h'

/-- **The derived composition isomorphism on a sheaf placed in degree `0`.** Through the
comparisons `m⁻¹ (F[0]) ≅ (m⁻¹ F)[0]`, the derived composition isomorphism
`g⁻¹ ⋙ f⁻¹ ≅ (f ≫ g)⁻¹` is the composition isomorphism of inverse images of sheaves. -/
theorem etaleAbelianDerivedInverseImageCompIso'_single
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianDerivedInverseImageCompIso'.{u, v} f g fg hfg).inv.app
          ((DerivedCategory.singleFunctor _ 0).obj F) ≫
        ((etaleAbelianInverseImage.{u, v} fg).mapDerivedCategorySingleFunctor 0).hom.app F =
      (etaleAbelianDerivedInverseImage.{u, v} f).map
          (((etaleAbelianInverseImage.{u, v} g).mapDerivedCategorySingleFunctor 0).hom.app F) ≫
        ((etaleAbelianInverseImage.{u, v} f).mapDerivedCategorySingleFunctor 0).hom.app
          ((etaleAbelianInverseImage.{u, v} g).obj F) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).inv.app F) := by
  have h := congrArg (fun τ => τ.app F)
    (Stacks.DerivedIndexing.mapDerivedCategorySingleFunctor_compIso
      (F := etaleAbelianInverseImage.{u, v} g) (G := etaleAbelianInverseImage.{u, v} f)
      (H := etaleAbelianInverseImage.{u, v} fg)
      (etaleAbelianInverseImageCompIso'.{u, v} f g fg hfg).symm 0)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_hom,
    ← etaleAbelianDerivedInverseImageCompIso'_inv_eq] at h
  exact h

end Bridge

section Pasting

variable {S T W X Y Z : Scheme.{u}}

/-- **The degree-`q` base change map of a commutative square, at an arbitrary coefficient
universe.** For a commutative square `g' ≫ f = f' ≫ g` and an abelian sheaf `F`, the morphism
`g⁻¹ (R^q f_* F) ⟶ R^q f'_* ((g')⁻¹ F)` read off the derived base change map on `q`-th cohomology
sheaves. At `v = 0` it is
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange`
(`etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq`); stating the pasting law at a
general `v` keeps every universe spelled `max (u + 1) v` throughout its proof. -/
def etaleAbelianRightDerivedBaseChangeMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    (etaleAbelianInverseImage.{u, v} g).obj
        (((etaleAbelianDirectImage.{u, v} f).rightDerived q).obj F) ⟶
      ((etaleAbelianDirectImage.{u, v} f').rightDerived q).obj
        ((etaleAbelianInverseImage.{u, v} g').obj F) :=
  ((etaleAbelianInverseImage.{u, v} g).mapIso
      (etaleAbelianRightDerivedDirectImageIsoHomology.{v, u} f q F)).hom ≫
    (((etaleAbelianInverseImage.{u, v} g).mapDerivedCategoryHomologyIso q).app _).inv ≫
    (DerivedCategory.homologyFunctor _ q).map
      (etaleAbelianSheafDerivedBaseChange.{u, v} f g g' f' h F) ≫
    (DerivedCategory.homologyFunctor _ q).map
      ((etaleAbelianDerivedDirectImage.{u, v} f').map
        (((etaleAbelianInverseImage.{u, v} g').mapDerivedCategorySingleFunctor 0).app F).hom) ≫
    (etaleAbelianRightDerivedDirectImageIsoHomology.{v, u} f' q _).inv

/-- At `v = 0` the base change map at a general coefficient universe is
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange`. -/
theorem etaleAbelianInverseImageRightDerivedDirectImageBaseChange_eq {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : g' ≫ f = f' ≫ g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    etaleAbelianInverseImageRightDerivedDirectImageBaseChange f g g' f' h F q =
      etaleAbelianRightDerivedBaseChangeMap.{u, 0} f g g' f' h F q :=
  rfl

variable (f : X ⟶ S) (g : T ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (i : W ⟶ X) (j : Z ⟶ W) (k : Z ⟶ Y)
  (sq₁ : e ≫ g = h ≫ f) (sq₂ : k ≫ h = j ≫ i)
  (a : W ⟶ S) (ha : a = i ≫ f) (b : Z ⟶ T) (hb : b = k ≫ e) (hyp : b ≫ g = j ≫ a)

/-- Naturality of the comparison of inverse image with homology, inverted. -/
@[reassoc]
private theorem pc_nI (q : ℕ)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (φ : K ⟶ L) :
    (etaleAbelianInverseImage.{u, v} i).map
        ((DerivedCategory.homologyFunctor _ (q : ℤ)).map φ) ≫
      ((etaleAbelianInverseImage.{u, v} i).mapDerivedCategoryHomologyIso q).inv.app L =
    ((etaleAbelianInverseImage.{u, v} i).mapDerivedCategoryHomologyIso q).inv.app K ≫
      (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedInverseImage.{u, v} i).map φ) :=
  ((etaleAbelianInverseImage.{u, v} i).mapDerivedCategoryHomologyIso q).inv.naturality φ

/-- Naturality of the derived base change map, on cohomology sheaves. -/
@[reassoc]
private theorem pc_nB (q : ℕ)
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})}
    (φ : K ⟶ L) :
    (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedInverseImage.{u, v} i).map
          ((etaleAbelianDerivedDirectImage.{u, v} h).map φ)) ≫
      (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedBaseChange.{u, v} h i k j sq₂).app L) =
    (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedBaseChange.{u, v} h i k j sq₂).app K) ≫
      (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedDirectImage.{u, v} j).map
          ((etaleAbelianDerivedInverseImage.{u, v} k).map φ)) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ ((etaleAbelianDerivedBaseChange.{u, v} h i k j sq₂).naturality φ)

/-- Naturality of the composition isomorphism of inverse images. -/
@[reassoc]
private theorem pc_nC {A A' : Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (φ : A ⟶ A') :
    (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).hom.app A ≫
      (etaleAbelianInverseImage.{u, v} i).map ((etaleAbelianInverseImage.{u, v} f).map φ) =
    (etaleAbelianInverseImage.{u, v} a).map φ ≫
      (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).hom.app A' :=
  ((etaleAbelianInverseImageCompIso'.{u, v} i f a ha).hom.naturality φ).symm

/-- Naturality of the comparison of `R^q j_*` with the cohomology sheaves of `Rj_*`. -/
@[reassoc]
private theorem pc_nR (q : ℕ) {A A' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    (φ : A ⟶ A') :
    (etaleAbelianRightDerivedDirectImageIsoHomology.{v, u} j q A).inv ≫
      ((etaleAbelianDirectImage.{u, v} j).rightDerived q).map φ =
    (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedDirectImage.{u, v} j).map
          ((DerivedCategory.singleFunctor _ 0).map φ)) ≫
      (etaleAbelianRightDerivedDirectImageIsoHomology.{v, u} j q A').inv := by
  simp only [etaleAbelianRightDerivedDirectImageIsoHomology, Iso.symm_inv, Iso.app_hom]
  exact (NatTrans.naturality _ φ).symm

/-- **The pasting law for the base change map on higher direct images**, at an arbitrary
coefficient universe. For a tower of two commutative squares `e ≫ g = h ≫ f` and
`k ≫ h = j ≫ i` of schemes, with outer rectangle `b ≫ g = j ≫ a` where `a = i ≫ f` and
`b = k ≫ e`, the degree-`q` base change map `a⁻¹ R^q g_* F ⟶ R^q j_* b⁻¹ F` of the rectangle is
`i⁻¹` of the base change map of the lower square followed by the base change map of the upper
square, read through the composition isomorphisms of inverse images. Nothing is assumed of the
squares beyond commutativity. -/
theorem etaleAbelianRightDerivedBaseChangeMap_comp
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    etaleAbelianRightDerivedBaseChangeMap.{u, v} g a b j hyp F q =
      (etaleAbelianInverseImageCompIso'.{u, v} i f a ha).hom.app
          (((etaleAbelianDirectImage.{u, v} g).rightDerived q).obj F) ≫
        (etaleAbelianInverseImage.{u, v} i).map
          (etaleAbelianRightDerivedBaseChangeMap.{u, v} g f e h sq₁ F q) ≫
        etaleAbelianRightDerivedBaseChangeMap.{u, v} h i k j sq₂
          ((etaleAbelianInverseImage.{u, v} e).obj F) q ≫
        ((etaleAbelianDirectImage.{u, v} j).rightDerived q).map
          ((etaleAbelianInverseImageCompIso'.{u, v} k e b hb).inv.app F) := by
  have hH := etaleAbelianDerivedInverseImageCompIso'_homology.{u, v} i f a ha (q : ℤ)
    ((etaleAbelianDerivedDirectImage.{u, v} g).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))
  have hS := congrArg (fun φ => (DerivedCategory.homologyFunctor _ (q : ℤ)).map
        ((etaleAbelianDerivedDirectImage.{u, v} j).map φ))
    (etaleAbelianDerivedInverseImageCompIso'_single.{u, v} k e b hb F)
  simp only [Functor.map_comp] at hS
  dsimp only [etaleAbelianRightDerivedBaseChangeMap, etaleAbelianSheafDerivedBaseChange]
  rw [etaleAbelianDerivedBaseChange_comp_app.{u, v} f g h e i j k sq₁ sq₂ a ha b hb hyp]
  simp only [Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.app_inv, Iso.app_hom,
    Functor.comp_obj]
  simp only [Functor.comp_obj] at hH hS
  rw [Iso.inv_hom_id_map_assoc, pc_nI_assoc, pc_nI_assoc, pc_nB_assoc, pc_nR,
    reassoc_of% hS.symm, pc_nC_assoc, ← reassoc_of% hH]

/-- **The pasting law for the base change map on higher direct images**, for
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange`: the case
`v = 0` of `Stacks.EtaleCohomology.etaleAbelianRightDerivedBaseChangeMap_comp`. -/
theorem etaleAbelianInverseImageRightDerivedDirectImageBaseChange_comp
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    etaleAbelianInverseImageRightDerivedDirectImageBaseChange g a b j hyp F q =
      (etaleAbelianInverseImageCompIso'.{u, 0} i f a ha).hom.app
          (((etaleAbelianDirectImage.{u, 0} g).rightDerived q).obj F) ≫
        (etaleAbelianInverseImage.{u, 0} i).map
          (etaleAbelianInverseImageRightDerivedDirectImageBaseChange g f e h sq₁ F q) ≫
        etaleAbelianInverseImageRightDerivedDirectImageBaseChange h i k j sq₂
          ((etaleAbelianInverseImage.{u, 0} e).obj F) q ≫
        ((etaleAbelianDirectImage.{u, 0} j).rightDerived q).map
          ((etaleAbelianInverseImageCompIso'.{u, 0} k e b hb).inv.app F) :=
  etaleAbelianRightDerivedBaseChangeMap_comp.{u, 0} f g h e i j k sq₁ sq₂ a ha b hb hyp F q

end Pasting

end Stacks.EtaleCohomology

end

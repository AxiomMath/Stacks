module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteDirectImageDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.IntegralDirectImageAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RefinedTorsionFinitePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.FiniteDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.PrimaryVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteSheafCohomology

/-!
# The curve-cohomology assertions pass to a finite direct image

For a finite morphism `f : X ⟶ Y` of schemes of finite type over a field `k` and an abelian sheaf
`F` on the small étale site of `X`, the étale cohomology of `f_* F` on `Y` is identified with that
of `F` on `X`, compatibly with restriction along cartesian squares. Consequently, if statements
(1) – (8) of Situation 0A52 hold for `F`, then they hold for `f_* F`.

## Main definitions

* `Stacks.EtaleCohomology.directImageCohomologyMap`: the comparison map
  `H^q(Y, f_* F) → H^q(X, F)`.
* `Stacks.EtaleCohomology.directImageRestrictionHom`: the comparison of the two restricted
  cohomologies across a commutative square.
* `Stacks.EtaleCohomology.CurveCohomologyAssertions`: statements (1) – (8) of Situation 0A52 for
  one abelian sheaf.

## Main results

* `Stacks.EtaleCohomology.bijective_directImageCohomologyMap`: for `f` integral the comparison
  map is bijective in every degree.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_isPullback`: for a cartesian square with
  `f` finite the base change comparison of abelian sheaves is an isomorphism.
* `Stacks.EtaleCohomology.bijective_restriction_of_isPullback`: bijectivity of restriction
  transfers across a cartesian square with `f` finite.
* `Stacks.EtaleCohomology.curveCohomologyAssertions_smallEtaleDirectImageAb`: statements (1) – (8)
  of Situation 0A52 pass from `F` to `f_* F` for `f` finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace Stacks.EtaleCohomology

section Collapse

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **The comparison of the two étale cohomologies, written out.** For `f : X ⟶ Y` and `F` an
abelian sheaf on the small étale site of `X`, the map `H^q(Y, f_* F) → H^q(X, F)` that restricts
a class along `f` and then applies the counit `f^{-1} f_* F ⟶ F` of the
inverse-image/direct-image adjunction. -/
def directImageCohomologyMap
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q →+ Sheaf.H.{w} F q :=
  (Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).counit.app F) q).comp
    (etaleCohomologyRestrictionMap.{u, v, w} f ((smallEtaleDirectImageAb f).obj F) q)

/-- The comparison map is restriction along `f` followed by the counit, by definition. -/
theorem directImageCohomologyMap_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    directImageCohomologyMap.{u, v, w} f F q x =
      Sheaf.H.map ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).counit.app F) q
        (etaleCohomologyRestrictionMap.{u, v, w} f ((smallEtaleDirectImageAb f).obj F) q x) :=
  rfl

/-- **Stacks 03YU, statement 1, through the adjunction: the comparison is bijective.** For `f`
integral — a finite morphism, for instance — the comparison
`Stacks.EtaleCohomology.directImageCohomologyMap` is a bijection in every degree. -/
theorem bijective_directImageCohomologyMap [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ) :
    Function.Bijective (directImageCohomologyMap.{u, v, w} f F q) := by
  let : IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    Sheaf.isGrothendieckAbelian_of_essentiallySmall X.smallEtaleTopology _
  let : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    CategoryTheory.IsGrothendieckAbelian.enoughInjectives
  have heq : (directImageCohomologyMap.{u, v, w} f F q :
        Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q → Sheaf.H.{w} F q) =
      ((Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, v} f).app
          (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))).inv).precomp F (zero_add q)) ∘
        (Stacks.ExtAdjunction.extMap (etaleAbelianInverseImageDirectImageAdj.{u, v} f)
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
            (AddCommGrpCat.of (ULift.{max (u + 1) v} ℤ))) F q) := by
    funext x
    rw [directImageCohomologyMap_apply.{u, v, w}, Function.comp_apply, Sheaf.H.map_apply,
      etaleCohomologyRestrictionMap_apply.{u, v, w}, Ext.comp_assoc_of_third_deg_zero,
      Stacks.ExtAdjunction.precomp_apply, Stacks.ExtAdjunction.extMap_apply]
  rw [heq]
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso _ q).comp
    (Stacks.ExtAdjunction.extMap_bijective _ _ F q)

end Collapse

section Naturality

/-- Restriction on étale cohomology is natural in the abelian sheaf: restricting the image of a
class under a map of coefficients is the image of its restriction under the inverse image of that
map. -/
private theorem etaleCohomologyRestrictionMap_sheafH_map {Z Z' : Scheme.{u}} (i : Z' ⟶ Z)
    {G G' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (c : G ⟶ G')
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (q : ℕ) (x : Sheaf.H.{w} G q) :
    etaleCohomologyRestrictionMap.{u, v, w} i G' q (Sheaf.H.map c q x) =
      Sheaf.H.map ((etaleAbelianInverseImage.{u, v} i).map c) q
        (etaleCohomologyRestrictionMap.{u, v, w} i G q x) := by
  simp only [Sheaf.H.map_apply, etaleCohomologyRestrictionMap_apply.{u, v, w},
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- **An isomorphism of abelian sheaves is a bijection on étale cohomology**, the inverse
isomorphism inducing the inverse bijection. -/
theorem bijective_sheafH_map {Z : Scheme.{u}}
    {G G' : Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (c : G ⟶ G') [IsIso c]
    [HasExt.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (q : ℕ) :
    Function.Bijective (Sheaf.H.map.{w} c q) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Sheaf.H.map (inv c) q, fun x ↦ ?_, fun y ↦ ?_⟩
  · rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]
  · rw [← Sheaf.H.map_comp_apply, IsIso.inv_hom_id, Sheaf.H.map_id_apply]

end Naturality

section BaseChangeSquare

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (i : Y' ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y')
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- **One leg of the square.** Restricting along `i` and then along `f'` is restricting along the
common composite, the square being commutative. -/
private theorem restrictionLegTarget (hsq : j ≫ f = f' ≫ i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    etaleCohomologyRestrictionMap.{u, v, w} f'
        ((etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} i).obj F) q
        (etaleCohomologyRestrictionMap.{u, v, w} i
          ((smallEtaleDirectImageAb f).obj F) q x) =
      Sheaf.H.map ((etaleAbelianInverseImageCompIso'.{u, v} f' i (j ≫ f) hsq).hom.app
          ((smallEtaleDirectImageAb f).obj F)) q
        (etaleCohomologyRestrictionMap.{u, v, w} (j ≫ f)
          ((smallEtaleDirectImageAb f).obj F) q x) := by
  show etaleCohomologyRestrictionMap.{u, v, w} f'
      ((etaleAbelianInverseImage.{u, v} i).obj ((smallEtaleDirectImageAb f).obj F)) q
      (etaleCohomologyRestrictionMap.{u, v, w} i
        ((smallEtaleDirectImageAb f).obj F) q x) = _
  rw [← etaleCohomologyRestrictionMap_comp.{u, v, w} i f' (j ≫ f) hsq
    ((smallEtaleDirectImageAb f).obj F) q x, ← Sheaf.H.map_comp_apply, Iso.inv_hom_id_app,
    Sheaf.H.map_id_apply]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- **The base change comparison read against the two counits.** The geometric content of the
comparison square, as an identity of morphisms of abelian sheaves on `X'_étale`: the base change
comparison followed by the counit for `f'` is the counit for `f`, once the two comparisons of the
composite inverse images around the square are inserted. -/
private theorem compIsoHomCompCounit (hsq : j ≫ f = f' ≫ i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImageCompIso'.{u, v} f' i (j ≫ f) hsq).hom.app
          ((smallEtaleDirectImageAb f).obj F) ≫
        (etaleAbelianInverseImage.{u, v} f').map
            ((etaleAbelianBaseChange.{u, v} f i j f' hsq).app F) ≫
          (etaleAbelianInverseImageDirectImageAdj.{u, v} f').counit.app
            ((etaleAbelianInverseImage.{u, v} j).obj F) =
      (etaleAbelianInverseImageCompIso'.{u, v} j f (j ≫ f) rfl).hom.app
          ((smallEtaleDirectImageAb f).obj F) ≫
        (etaleAbelianInverseImage.{u, v} j).map
          ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).counit.app F) := by
  rw [etaleAbelianBaseChange_eq_mateEquiv.{u, v} f i j f' hsq (j ≫ f) rfl hsq, mateEquiv_counit]
  simp [TwoSquare.mk]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] in
/-- The target-side composite of the comparison square, assembled into a single map of
coefficients applied to the restriction along the common composite. -/
private theorem legTarget (hsq : j ≫ f = f' ≫ i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    directImageCohomologyMap.{u, v, w} f' ((etaleAbelianInverseImage.{u, v} j).obj F) q
        (Sheaf.H.map ((etaleAbelianBaseChange.{u, v} f i j f' hsq).app F) q
          (etaleCohomologyRestrictionMap.{u, v, w} i
            ((smallEtaleDirectImageAb f).obj F) q x)) =
      Sheaf.H.map ((etaleAbelianInverseImageCompIso'.{u, v} f' i (j ≫ f) hsq).hom.app
            ((smallEtaleDirectImageAb f).obj F) ≫
          (etaleAbelianInverseImage.{u, v} f').map
              ((etaleAbelianBaseChange.{u, v} f i j f' hsq).app F) ≫
            (etaleAbelianInverseImageDirectImageAdj.{u, v} f').counit.app
              ((etaleAbelianInverseImage.{u, v} j).obj F)) q
        (etaleCohomologyRestrictionMap.{u, v, w} (j ≫ f)
          ((smallEtaleDirectImageAb f).obj F) q x) := by
  rw [directImageCohomologyMap_apply.{u, v, w},
    etaleCohomologyRestrictionMap_sheafH_map.{u, v, w},
    restrictionLegTarget.{u, v, w} f i j f' hsq F q x, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply]

/-- The source-side composite of the comparison square, assembled the same way. -/
private theorem legSource
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    etaleCohomologyRestrictionMap.{u, v, w} j F q
        (directImageCohomologyMap.{u, v, w} f F q x) =
      Sheaf.H.map ((etaleAbelianInverseImageCompIso'.{u, v} j f (j ≫ f) rfl).hom.app
            ((smallEtaleDirectImageAb f).obj F) ≫
          (etaleAbelianInverseImage.{u, v} j).map
            ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).counit.app F)) q
        (etaleCohomologyRestrictionMap.{u, v, w} (j ≫ f)
          ((smallEtaleDirectImageAb f).obj F) q x) := by
  rw [directImageCohomologyMap_apply.{u, v, w},
    etaleCohomologyRestrictionMap_sheafH_map.{u, v, w},
    restrictionLegTarget.{u, v, w} f f j j rfl F q x, ← Sheaf.H.map_comp_apply]

/-- **The comparison of the two cohomologies commutes with the two restriction maps around a
commutative square.** For a commutative square `j ≫ f = f' ≫ i` of schemes and an abelian sheaf
`F` on `X_étale`: restricting a class of `H^q(Y, f_* F)` along `i`, carrying it along the base
change comparison `i^{-1} f_* F ⟶ f'_* j^{-1} F` of Tag 0A2A and comparing the cohomology of
`f'_* j^{-1} F` with that of `j^{-1} F` gives the same class as comparing the cohomology of
`f_* F` with that of `F` and then restricting along `j`. Neither morphism need be integral and
the square need not be cartesian. -/
theorem directImageCohomologyMap_baseChange (hsq : j ≫ f = f' ≫ i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (q : ℕ)
    (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    directImageCohomologyMap.{u, v, w} f' ((etaleAbelianInverseImage.{u, v} j).obj F) q
        (Sheaf.H.map ((etaleAbelianBaseChange.{u, v} f i j f' hsq).app F) q
          (etaleCohomologyRestrictionMap.{u, v, w} i
            ((smallEtaleDirectImageAb f).obj F) q x)) =
      etaleCohomologyRestrictionMap.{u, v, w} j F q
        (directImageCohomologyMap.{u, v, w} f F q x) := by
  rw [legTarget.{u, v, w} f i j f' hsq F q x, legSource.{u, v, w} f j F q x,
    compIsoHomCompCounit.{u, v} f i j f' hsq F]

end BaseChangeSquare

section Cartesian

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (i : Y' ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y')
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})]

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- **Stacks 0959 at abelian coefficients.** For a cartesian square `j ≫ f = f' ≫ i` of schemes
with `f` finite, the underived base change comparison `i^{-1} f_* ⟶ f'_* j^{-1}` of abelian
sheaves on the small étale sites is an isomorphism. No big étale site is assumed. -/
theorem isIso_etaleAbelianBaseChange_of_isPullback [IsFinite f]
    (sq : IsPullback j f' f i) :
    IsIso (etaleAbelianBaseChange.{u, 0} f i j f' sq.w) := by
  have := small_single.{u} Y'
  obtain ⟨B, hB⟩ :=
    BigEtaleSite.exists_contains_of_small ({X, Y, X', Y'} : Set AlgebraicGeometry.Scheme.{u})
  have hX : B.Contains X := hB X (by simp)
  have hY : B.Contains Y := hB Y (by simp)
  have hX' : B.Contains X' := hB X' (by simp)
  have hY' : B.Contains Y' := hB Y' (by simp)
  have : IsFinite
      (B.inclusion.map (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f)) :=
    ‹IsFinite f›
  exact isIso_etaleAbelianBaseChange_of_isFinite B
    (ObjectProperty.homMk (X := B.obj X hX) (Y := B.obj Y hY) f)
    (ObjectProperty.homMk (X := B.obj Y' hY') (Y := B.obj Y hY) i)
    (ObjectProperty.homMk (X := B.obj X' hX') (Y := B.obj X hX) j)
    (ObjectProperty.homMk (X := B.obj X' hX') (Y := B.obj Y' hY') f') sq

/-- **The comparison of the two restricted cohomologies across a commutative square.** The base
change comparison `i^{-1} f_* F ⟶ f'_* j^{-1} F` on cohomology, followed by the comparison of the
cohomology of `f'_* j^{-1} F` with that of `j^{-1} F`. -/
def directImageRestrictionHom (hsq : j ≫ f = f' ≫ i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} i).obj
        ((smallEtaleDirectImageAb f).obj F)) q →+
      Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} j).obj F) q :=
  (directImageCohomologyMap.{u, 0, w} f' ((etaleAbelianInverseImage.{u, 0} j).obj F) q).comp
    (Sheaf.H.map.{w} ((etaleAbelianBaseChange.{u, 0} f i j f' hsq).app F) q)

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- The comparison map is the base change comparison on cohomology followed by the comparison of
the two cohomologies for `f'`, by definition. -/
theorem directImageRestrictionHom_apply (hsq : j ≫ f = f' ≫ i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (y : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, 0} i).obj
      ((smallEtaleDirectImageAb f).obj F)) q) :
    directImageRestrictionHom.{u, w} f i j f' hsq F q y =
      directImageCohomologyMap.{u, 0, w} f' ((etaleAbelianInverseImage.{u, 0} j).obj F) q
        (Sheaf.H.map ((etaleAbelianBaseChange.{u, 0} f i j f' hsq).app F) q y) :=
  rfl

omit [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})] in
/-- **The comparison is bijective for a cartesian square with `f` finite.** For a cartesian
square `j ≫ f = f' ≫ i` with `f` finite, `Stacks.EtaleCohomology.directImageRestrictionHom` is a
bijection in every degree. -/
theorem bijective_directImageRestrictionHom [IsFinite f] (sq : IsPullback j f' f i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective (directImageRestrictionHom.{u, w} f i j f' sq.w F q) := by
  have : IsIso (etaleAbelianBaseChange.{u, 0} f i j f' sq.w) :=
    isIso_etaleAbelianBaseChange_of_isPullback.{u} f i j f' sq
  have : IsFinite f' := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹IsFinite f›
  exact (bijective_directImageCohomologyMap.{u, 0, w} f'
      ((etaleAbelianInverseImage.{u, 0} j).obj F) q).comp
    (bijective_sheafH_map.{u, 0, w} ((etaleAbelianBaseChange.{u, 0} f i j f' sq.w).app F) q)

/-- **The comparison commutes with the two restriction maps** around a cartesian square with `f`
finite. -/
theorem directImageRestrictionHom_comm [IsFinite f] (sq : IsPullback j f' f i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) :
    directImageRestrictionHom.{u, w} f i j f' sq.w F q
        (etaleCohomologyRestrictionMap.{u, 0, w} i
          ((smallEtaleDirectImageAb f).obj F) q x) =
      etaleCohomologyRestrictionMap.{u, 0, w} j F q
        (directImageCohomologyMap.{u, 0, w} f F q x) := by
  rw [directImageRestrictionHom_apply.{u, w} f i j f' sq.w F q]
  exact directImageCohomologyMap_baseChange.{u, 0, w} f i j f' sq.w F q x

/-- **Bijectivity of restriction transfers across a cartesian square with `f` finite.** -/
theorem bijective_restriction_of_isPullback [IsFinite f] (sq : IsPullback j f' f i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hq : Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} j F q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, w} i
      ((smallEtaleDirectImageAb f).obj F) q) :=
  bijective_of_comparisonSquare (bijective_directImageCohomologyMap.{u, 0, w} f F q)
    (bijective_directImageRestrictionHom.{u, w} f i j f' sq F q)
    (directImageRestrictionHom_comm.{u, w} f i j f' sq F q) hq

/-- **Surjectivity of restriction in degree two transfers across a cartesian square with `f`
finite.** -/
theorem surjective_restriction_of_isPullback [IsFinite f] (sq : IsPullback j f' f i)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hq : Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} j F 2)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, w} i
      ((smallEtaleDirectImageAb f).obj F) 2) :=
  surjective_of_comparisonSquare
    (bijective_directImageCohomologyMap.{u, 0, w} f F 2).surjective
    (bijective_directImageRestrictionHom.{u, w} f i j f' sq F 2).injective
    (directImageRestrictionHom_comm.{u, w} f i j f' sq F 2) hq

end Cartesian

section IntegralDirectImage

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (i : Y' ⟶ Y) (j : X' ⟶ X)
  [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  [HasExt.{w} (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
  {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}

/-- Vanishing of the étale cohomology of `F` in a degree gives vanishing of that of `f_* F` in
the same degree, for `f` integral. -/
private theorem subsingleton_smallEtaleDirectImageAb_of_isIntegralHom [IsIntegralHom f] (q : ℕ)
    (hq : Subsingleton (Sheaf.H.{w} F q)) :
    Subsingleton (Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) := by
  have := hq
  exact (bijective_directImageCohomologyMap.{u, v, w} f F q).injective.subsingleton

/-- Finiteness of the étale cohomology of `F` in a degree gives finiteness of that of `f_* F` in
the same degree, for `f` integral. -/
private theorem finite_smallEtaleDirectImageAb_of_isIntegralHom [IsIntegralHom f] (q : ℕ)
    (hq : Finite (Sheaf.H.{w} F q)) :
    Finite (Sheaf.H.{w} ((smallEtaleDirectImageAb f).obj F) q) := by
  have := hq
  exact Finite.of_injective (directImageCohomologyMap.{u, v, w} f F q)
    (bijective_directImageCohomologyMap.{u, v, w} f F q).injective

end IntegralDirectImage

section Assertions

/-- **The eight statements of Situation 0A52 for one abelian sheaf, as the source states them.**
For a scheme `Z` with structure morphism `π` to the spectrum of a field `k`, contained in the big
étale site `B`, and an abelian sheaf `G` on the small étale site of `Z`:

1. `H^q(Z, G) = 0` for `q > 2`;
2. `H^q(Z, G) = 0` for `q > 1` if `Z` is affine;
3. `H^q(Z, G) = 0` for `q > 1` if `p = char(k) > 0` and `G` is `p`-power torsion;
4. `H^q(Z, G)` is finite if `G` is constructible and torsion prime to `char(k)`;
5. `H^q(Z, G)` is finite if `Z` is proper and `G` is constructible;
6. `H^q(Z, G) → H^q(Z_{k'}, G|_{Z_{k'}})` is bijective for every extension `k'/k` of
   algebraically closed fields if `G` is torsion prime to `char(k)`;
7. the same map is bijective for every such `k'/k` if `Z` is proper;
8. `H²(Z, G) → H²(U, G|_U)` is surjective for every open `U ⊆ Z`.

Each statement is an implication from the condition under which it applies, which is how the
source reads "statements (1) – (8) hold": those that apply are true. Constructibility is
`Stacks.EtaleCohomology.IsConstructibleEtaleSheaf`, Stacks 03RW on the small étale site of
Stacks 021B cut out of `B`; "torsion prime to `char(k)`" is local annihilation by integers prime
to the exponential characteristic `ringExpChar k`, which in characteristic zero is just torsion.
The restriction to `Z_{k'}` is restriction along the projection
`Stacks.EtaleCohomology.scalarExtensionFst` of the scalar extension, and the restriction to `U`
is restriction along the open immersion `U.ι`. Cohomology is `CategoryTheory.Sheaf.H` with
coefficients in `AddCommGrpCat.{u + 1}`, the universe in which the sections of an abelian sheaf
on the small étale site of a `Scheme.{u}` live. -/
structure CurveCohomologyAssertions (B : BigEtaleSite.{u}) {k : Type u} [Field k]
    {Z : Scheme.{u}} (hZ : B.Contains Z) (π : Z ⟶ Spec (.of k))
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop where
  /-- **Statement (1), Tag 0A53.** The étale cohomology of `G` vanishes above degree two. -/
  vanishing : ∀ q : ℕ, 2 < q → Subsingleton (Sheaf.H.{u + 1} G q)
  /-- **Statement (2), Tag 0A54.** If `Z` is affine then the étale cohomology of `G` vanishes
  above degree one. -/
  vanishing_of_isAffine : IsAffine Z → ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{u + 1} G q)
  /-- **Statement (3), Tag 0A55.** If `p = char(k)` is positive and `G` is `p`-power torsion
  then the étale cohomology of `G` vanishes above degree one. -/
  vanishing_of_isPrimePowerTorsion : 0 < ringChar k →
    Stacks.Torsion.IsPrimePowerTorsion Z.smallEtaleTopology (ringChar k) G →
      ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{u + 1} G q)
  /-- **Statement (4), Tag 0A56.** If `G` is constructible and torsion prime to `char(k)` then
  its étale cohomology is finite in every degree. -/
  finite_of_isPrimeToCharacteristicTorsion : IsConstructibleEtaleSheaf B hZ G →
    Stacks.Torsion.IsPrimeToCharacteristicTorsion Z.smallEtaleTopology (ringExpChar k) G →
      ∀ q : ℕ, Finite (Sheaf.H.{u + 1} G q)
  /-- **Statement (5), Tag 0A57.** If `Z` is proper over `k` and `G` is constructible then its
  étale cohomology is finite in every degree. -/
  finite_of_isProper : IsProper π → IsConstructibleEtaleSheaf B hZ G →
    ∀ q : ℕ, Finite (Sheaf.H.{u + 1} G q)
  /-- **Statement (6), Tag 0A58.** If `G` is torsion prime to `char(k)` then for every extension
  `k'/k` of algebraically closed fields the restriction `H^q(Z, G) → H^q(Z_{k'}, G|_{Z_{k'}})` is
  bijective in every degree. -/
  bijective_restriction_of_isPrimeToCharacteristicTorsion :
    Stacks.Torsion.IsPrimeToCharacteristicTorsion Z.smallEtaleTopology (ringExpChar k) G →
      ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k'] (q : ℕ),
        Function.Bijective
          (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π) G q)
  /-- **Statement (7), Tag 0A59.** If `Z` is proper over `k` then for every extension `k'/k` of
  algebraically closed fields the restriction `H^q(Z, G) → H^q(Z_{k'}, G|_{Z_{k'}})` is
  bijective in every degree. -/
  bijective_restriction_of_isProper : IsProper π →
    ∀ (k' : Type u) [Field k'] [Algebra k k'] [IsAlgClosed k'] (q : ℕ),
      Function.Bijective
        (etaleCohomologyRestrictionMap.{u, 0, u + 1} (scalarExtensionFst k k' π) G q)
  /-- **Statement (8), Tag 0A5A.** For every open `U ⊆ Z` the restriction
  `H²(Z, G) → H²(U, G|_U)` is surjective. -/
  surjective_restriction : ∀ U : Z.Opens,
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} U.ι G 2)

end Assertions

section ScalarExtensionSquare

/-- **Scalar extension of a morphism is a cartesian square.** For `f : X ⟶ Y` over `Spec k` and a
field extension `k'/k`, the square formed by `f`, its scalar extension `X_{k'} ⟶ Y_{k'}` and the
two projections of the scalar extensions is cartesian. -/
private theorem isPullback_scalarExtensionFst (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    {X Y : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ Spec (.of k)) :
    IsPullback (scalarExtensionFst k k' (f ≫ π))
      (Limits.pullback.map (f ≫ π) (Spec.map (CommRingCat.ofHom (algebraMap k k'))) π
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f (𝟙 _) (𝟙 _)
        (by simp) (by simp))
      f (scalarExtensionFst k k' π) := by
  refine IsPullback.of_bot ?_ (Limits.pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback π (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  rw [Limits.pullback.lift_snd, Category.comp_id]
  exact IsPullback.of_hasPullback _ _

end ScalarExtensionSquare

section Faithful

variable (B : BigEtaleSite.{u}) {k : Type u} [Field k] {X Y : Scheme.{u}}
  (hX : B.Contains X) (hY : B.Contains Y)

/-- Let `k` be a field, let `f : X ⟶ Y` be a finite morphism of schemes of finite type over `k`,
and let `F` be an abelian sheaf on the small étale site of `X`. If statements (1) – (8) of
Situation 0A52 hold for `F`, then they hold for `f_* F`.

Statements (1) – (8) are `Stacks.EtaleCohomology.CurveCohomologyAssertions`, read on `X`
relative to its structure morphism `f ≫ π` and on `Y` relative to `π`, with constructibility read
in a big étale site `B` containing both schemes. The remaining hypotheses of Situation 0A52 —
that `k` is algebraically closed, that `X` and `Y` are separated of dimension at most one, and
that `F` is torsion — are not assumed. -/
@[stacks 0A5D "statements (1)-(8) of Situation 0A52 pass to f_* for finite f"]
theorem curveCohomologyAssertions_smallEtaleDirectImageAb (π : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType π] [QuasiCompact π] (f : X ⟶ Y) [IsFinite f]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (h : CurveCohomologyAssertions B hX (f ≫ π) F) :
    CurveCohomologyAssertions B hY π ((smallEtaleDirectImageAb f).obj F) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ π)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ π)
  have : IsNoetherian X := {}
  refine
    { vanishing := fun q hq ↦
        subsingleton_smallEtaleDirectImageAb_of_isIntegralHom.{u, 0, u + 1} f q (h.vanishing q hq)
      vanishing_of_isAffine := fun hY' q hq ↦ ?_
      vanishing_of_isPrimePowerTorsion := fun hp htorsion q hq ↦
        subsingleton_smallEtaleDirectImageAb_of_isIntegralHom.{u, 0, u + 1} f q
          (h.vanishing_of_isPrimePowerTorsion hp
            (isPrimePowerTorsion_of_smallEtaleDirectImageAb f F _ htorsion) q hq)
      finite_of_isPrimeToCharacteristicTorsion := fun hconstr htorsion q ↦
        finite_smallEtaleDirectImageAb_of_isIntegralHom.{u, 0, u + 1} f q
          (h.finite_of_isPrimeToCharacteristicTorsion
            (isConstructibleEtaleSheaf_of_smallEtaleDirectImageAb B f hX hY F hconstr)
            (isPrimeToCharacteristicTorsion_of_smallEtaleDirectImageAb f F _ htorsion) q)
      finite_of_isProper := fun hproper hconstr q ↦ ?_
      bijective_restriction_of_isPrimeToCharacteristicTorsion := fun htorsion k' _ _ _ q ↦
        bijective_restriction_of_isPullback.{u, u + 1} f _ _ _
          (isPullback_scalarExtensionFst k k' f π) F q
          (h.bijective_restriction_of_isPrimeToCharacteristicTorsion
            (isPrimeToCharacteristicTorsion_of_smallEtaleDirectImageAb f F _ htorsion) k' q)
      bijective_restriction_of_isProper := fun hproper k' _ _ _ q ↦ ?_
      surjective_restriction := fun V ↦
        surjective_restriction_of_isPullback.{u, u + 1} f V.ι (f ⁻¹ᵁ V).ι (f ∣_ V)
          (isPullback_morphismRestrict f V).flip F (h.surjective_restriction (f ⁻¹ᵁ V)) }
  · have : IsAffine Y := hY'
    exact subsingleton_smallEtaleDirectImageAb_of_isIntegralHom.{u, 0, u + 1} f q
      (h.vanishing_of_isAffine (isAffine_of_isAffineHom f) q hq)
  · have : IsProper π := hproper
    exact finite_smallEtaleDirectImageAb_of_isIntegralHom.{u, 0, u + 1} f q
      (h.finite_of_isProper inferInstance
        (isConstructibleEtaleSheaf_of_smallEtaleDirectImageAb B f hX hY F hconstr) q)
  · have : IsProper π := hproper
    exact bijective_restriction_of_isPullback.{u, u + 1} f _ _ _
      (isPullback_scalarExtensionFst k k' f π) F q
      (h.bijective_restriction_of_isProper inferInstance k' q)

end Faithful

end Stacks.EtaleCohomology

end

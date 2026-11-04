module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.Homotopy
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# A split relative Čech complex is contractible

Let `f : 𝒰 ⥤ 𝒳` be a `1`-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, and let `𝓕` be an abelian sheaf on one of the five sites associated with `𝒳`. The
relative Čech complex `𝒦^•(f, 𝓕)` of `Stacks.RelativeCech.complex` is a complex of abelian
presheaves on `𝒳`; sheafifying it degreewise gives a complex of abelian sheaves, and the unit of
the right-Kan-extension adjunction augments it by `𝓕` in degree `0`, producing the *extended*
relative Čech complex

`𝓕 ⟶ f_{0,*}f_0⁻¹𝓕 ⟶ f_{1,*}f_1⁻¹𝓕 ⟶ f_{2,*}f_2⁻¹𝓕 ⟶ …`

If `f` has a section up to a vertical `2`-isomorphism — a `1`-morphism `s : 𝒳 ⥤ 𝒰` together with
`α : s ⋙ f ≅ 𝟭 𝒳` whose components lie over identities — then that extended complex is homotopic
to zero.

## Main definitions

* `Stacks.RelativeCech.augmentation`: the canonical map `F ⟶ f_{n,*}f_n⁻¹F` of abelian
  presheaves.
* `Stacks.RelativeCech.extendedComplex`: the extended relative Čech complex of an abelian
  presheaf.
* `Stacks.RelativeCech.sheafComplex`: the relative Čech complex sheafified degreewise.
* `Stacks.RelativeCech.sheafAugmentation`: its canonical augmentation by `𝓕`.
* `Stacks.RelativeCech.extendedSheafComplex`: the extended relative Čech complex of an abelian
  sheaf.

## Main results

* `Stacks.RelativeCech.nonempty_homotopy_extendedSheafComplex_id_zero`: the identity of the
  extended relative Čech complex is homotopic to zero.
* `Stacks.RelativeCech.nonempty_homotopy_extendedComplex_id_zero` is the same statement before
  sheafifying, which is where the contraction is actually built.
* `Stacks.RelativeCech.augmentation_comp_d` and
  `Stacks.RelativeCech.sheafAugmentation_comp_d`: the augmentation is a cocycle, which is what
  makes the extended complexes complexes.
* `Stacks.RelativeCech.extendedSheafComplexXZeroIso`,
  `Stacks.RelativeCech.extendedSheafComplex_X_succ` and
  `Stacks.RelativeCech.extendedSheafComplex_d_succ` identify the terms and differentials of the
  extended complex.

## Implementation notes

The contraction is built at the presheaf level and then sheafified. Inserting the section as a
new first coordinate of a relative Čech tuple is a `1`-morphism `𝒰_n ⥤ 𝒰_{n+1}`, and pullback
along it gives maps `f_{n+1,*}f_{n+1}⁻¹F ⟶ f_{n,*}f_n⁻¹F` whose two composites with the Čech
differentials add up to the identity; in degree `0` the corresponding map splits the
augmentation. Verticality of the components of `α` is exactly what makes the inserted coordinate
an object of the relative Čech nerve. `Stacks.Cech.homotopyOfContraction` then turns that
contraction of an `ℕ`-indexed cochain complex into a homotopy between its identity and zero, and
sheafification, being additive, carries that homotopy over by
`CategoryTheory.Functor.mapHomotopy`. Degree `0` of the sheafified extended complex is the
sheafification of the underlying presheaf of `𝓕`, which is `𝓕` itself up to the canonical
isomorphism `Stacks.RelativeCech.extendedSheafComplexXZeroIso`; the remaining terms are those of
`Stacks.RelativeCech.sheafComplex`, shifted by one.

All the maps involved are obtained from the counit of a right Kan extension along a projection of
the relative Čech nerve, so the identities between them are proved by the universal property
`CategoryTheory.Functor.hom_ext_of_isRightKanExtension` together with the defining factorisation
`Stacks.RelativeCech.reindexMap_fac`; where two reindexings agree only after a computation on
objects, that computation is isolated in `prependSection_reindex_face_obj`.

The augmented complex is indexed by `ℕ` with the sheaf in degree `0`, which is the source's
integer-indexed complex shifted up by one; `Stacks.Cech.extendedComplex` records the same
convention for the absolute Čech complex.

The `Abelian` instance on `AddCommGrpCat` is taken out of the instance set over the sheafified
material and reinstated by hand inside the proofs: it is only needed there, and leaving it in
scope makes the sheafification instances for a coefficient universe of the form `max …` loop.

## References

* [Stacks Project, Tag 06XA](https://stacks.math.columbia.edu/tag/06XA)
* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
* [Stacks Project, Tag 06X6](https://stacks.math.columbia.edu/tag/06X6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

namespace Stacks.RelativeCech

universe u vᵤ vₓ wᵤ wₓ t

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰]
    {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]

/-- The map `P ⋙ ran Q (Q ⋙ F) ⟶ P ⋙ F` for `P = H ⋙ Q`: whiskering the counit by `H`. -/
private def whiskerRanCounit {A B C E : Type*} [Category* A] [Category* B] [Category* C]
    [Category* E] (H : A ⥤ B) (Q : B ⥤ C) (P : A ⥤ C) (hh : P = H ⋙ Q) (F : C ⥤ E)
    [∀ G : B ⥤ E, Q.HasRightKanExtension G] : P ⋙ Q.ran.obj (Q ⋙ F) ⟶ P ⋙ F := by
  subst hh
  exact Functor.whiskerLeft H (Q.ranCounit.app (Q ⋙ F))

/-- The contracting map `f_{n+1,*}f_{n+1}⁻¹F ⟶ f_{n,*}f_n⁻¹F`: pullback along
`Stacks.Cech.prependSection`. -/
private def prependSectionMap
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (n : ℕ) (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1) ⟶
      term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F n := by
  let P := Tuple.projection q f n
  let Q := Tuple.projection q f (n + 1)
  let H := Cech.prependSection q f n s α hα
  have hh : P.op = H.op ⋙ Q.op := by
    dsimp [P, Q, H, Cech.prependSection]
    rfl
  let β := whiskerRanCounit H.op Q.op P.op hh F
  exact (P.op.ranAdjunction AddCommGrpCat.{max vᵤ vₓ wₓ t}).homEquiv _ _ β

/-- The contracting map `f_{0,*}f_0⁻¹F ⟶ F` in degree `0`: pullback along
`Stacks.Cech.sectionTuple`. -/
private def sectionMap
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F 0 ⟶ F := by
  let P : 𝒳 ⥤ 𝒳 := 𝟭 𝒳
  let Q := Tuple.projection q f 0
  let H := Cech.sectionTuple q f s α hα
  have hh : P.op = H.op ⋙ Q.op := by
    dsimp [P, H, Cech.sectionTuple, Q, Tuple.projection]
    rfl
  let β := whiskerRanCounit H.op Q.op P.op hh F
  exact (P.op.ranAdjunction AddCommGrpCat.{max vᵤ vₓ wₓ t}).homEquiv _ _ β ≫
    P.op.ranCounit.app (P.op ⋙ F)

/-- The canonical map `F ⟶ f_{n,*}f_n⁻¹F` of abelian presheaves: the unit of the
right-Kan-extension adjunction along the `n`-th projection of the relative Čech nerve. -/
public def augmentation
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t}) (n : ℕ) :
    F ⟶ term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F n :=
  ((Tuple.projection q f n).op.ranAdjunction
    AddCommGrpCat.{max vᵤ vₓ wₓ t}).unit.app F

/-- The Kan-extension counit undoes the adjunction hom-equivalence. -/
private lemma whiskerLeft_homEquiv_comp_ranCounit {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (L : C ⥤ D) [∀ F : C ⥤ E, L.HasRightKanExtension F] {F : C ⥤ E} {G : D ⥤ E}
    (β : L ⋙ G ⟶ F) :
    Functor.whiskerLeft L (((L.ranAdjunction E).homEquiv _ _) β) ≫ L.ranCounit.app F = β := by
  simpa [Functor.ranAdjunction_counit] using
    ((L.ranAdjunction E).homEquiv_counit (g := (L.ranAdjunction E).homEquiv _ _ β)).symm

/-- Reindexing along the `0`-th coface undoes prepending the section. -/
private lemma faceZero_comp_prepend
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (n : ℕ) (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F
        (SimplexCategory.δ (0 : Fin (n + 2))) ≫
      prependSectionMap q f F n s α hα = 𝟙 _ := by
  let P := Tuple.projection q f n
  let Q := Tuple.projection q f (n + 1)
  let H := Cech.prependSection q f n s α hα
  apply (P.op.ran.obj (P.op ⋙ F)).hom_ext_of_isRightKanExtension
    (P.op.ranCounit.app (P.op ⋙ F))
  rw [Functor.whiskerLeft_comp, Category.assoc]
  dsimp only [prependSectionMap]
  have hh : P.op = H.op ⋙ Q.op := by
    dsimp [P, H, Cech.prependSection]
    rfl
  let β := whiskerRanCounit H.op Q.op P.op hh F
  have hfac := whiskerLeft_homEquiv_comp_ranCounit P.op β
  show _ ≫ (Functor.whiskerLeft P.op ((P.op.ranAdjunction _).homEquiv _ _ β) ≫
    P.op.ranCounit.app (P.op ⋙ F)) = _
  rw [hfac]
  let R := Tuple.reindex q f (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom
  show Functor.whiskerLeft H.op
      (Functor.whiskerLeft Q.op
        (reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
          q f F (SimplexCategory.δ (0 : Fin (n + 2)))) ≫
        Q.op.ranCounit.app (Q.op ⋙ F)) =
    Functor.whiskerLeft H.op (Functor.whiskerLeft R.op
      (P.op.ranCounit.app (P.op ⋙ F)))
  rw [reindexMap_fac.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} (p := q) (f := f) F
    (SimplexCategory.δ (0 : Fin (n + 2)))]

/-- The contracting map in degree `0` is pullback along the section tuple, written through the
counit of the right Kan extension. -/
private lemma sectionMap_eq_whiskeredCounit
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    sectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα =
      Functor.whiskerLeft (Cech.sectionTuple q f s α hα).op
        ((Tuple.projection q f 0).op.ranCounit.app
          ((Tuple.projection q f 0).op ⋙ F)) := by
  let P : 𝒳 ⥤ 𝒳 := 𝟭 𝒳
  let Q := Tuple.projection q f 0
  let H := Cech.sectionTuple q f s α hα
  have hh : P.op = H.op ⋙ Q.op := by
    dsimp [P, H, Cech.sectionTuple, Q, Tuple.projection]
    rfl
  let β := whiskerRanCounit H.op Q.op P.op hh F
  have hfac := whiskerLeft_homEquiv_comp_ranCounit P.op β
  dsimp [sectionMap]
  ext x z
  show ((((P.op.ranAdjunction _).homEquiv _ _ β).app x ≫
    (P.op.ranCounit.app (P.op ⋙ F)).app x).hom z) = (β.app x).hom z
  exact congrArg (fun m : (Q.op.ran.obj (Q.op ⋙ F)).obj x ⟶ F.obj x => m.hom z)
    (by simpa [P] using congr_app hfac x)

/-- The contracting map in degree `0` splits the augmentation. -/
private lemma augmentation_comp_sectionMap
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 ≫
      sectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα = 𝟙 F := by
  rw [sectionMap_eq_whiskeredCounit]
  ext x z
  dsimp [augmentation]
  let Q := Tuple.projection q f 0
  let H := Cech.sectionTuple q f s α hα
  have h := Q.op.ranCounit_app_app_ranAdjunction_unit_app_app
    (H := AddCommGrpCat.{max vᵤ vₓ wₓ t}) (G := F) (X := H.op.obj x)
  exact congrArg (fun m : F.obj x ⟶ F.obj x => m.hom z)
    (by simpa [Q, H, Cech.sectionTuple, Tuple.projection] using h)

/-- The defining factorisation of the contracting map through the Kan-extension counit. -/
private lemma prependSectionMap_fac
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (n : ℕ) (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    let P := Tuple.projection q f n
    let Q := Tuple.projection q f (n + 1)
    Functor.whiskerLeft P.op
        (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα) ≫
        P.op.ranCounit.app (P.op ⋙ F) =
      Functor.whiskerLeft (Cech.prependSection q f n s α hα).op
        (Q.op.ranCounit.app (Q.op ⋙ F)) := by
  let P := Tuple.projection q f n
  let Q := Tuple.projection q f (n + 1)
  let H := Cech.prependSection q f n s α hα
  have hh : P.op = H.op ⋙ Q.op := by
    dsimp [P, Q, H, Cech.prependSection]
    rfl
  let β := whiskerRanCounit H.op Q.op P.op hh F
  have hfac := whiskerLeft_homEquiv_comp_ranCounit P.op β
  dsimp only [prependSectionMap]
  exact hfac

/-- Prepending the section intertwines the coface `δ_{i+1}` upstairs with the coface `δ_i`
downstairs, at the level of relative Čech tuples. -/
private lemma prependSection_reindex_face_obj
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (n : ℕ) (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x))
    (i : Fin (n + 2)) (a : Tuple q f (n + 1)) :
    (Cech.prependSection q f (n + 1) s α hα ⋙
        Tuple.reindex q f (SimplexCategory.δ i.succ).toOrderHom).obj a =
      (Tuple.reindex q f
        (SimplexCategory.δ i).toOrderHom ⋙ Cech.prependSection q f n s α hα).obj a := by
  dsimp only [Functor.comp_obj, Tuple.reindex, SimplexCategory.δ]
  rw [Tuple.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩
  · funext k
    cases k using Fin.cases with
    | zero => simp [Cech.prependSection]
    | succ k =>
      simp only [Cech.prependSection, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk, Fin.cases_succ]
      rw [show i.succ.succAboveOrderEmb.toOrderHom k.succ =
        (i.succAbove k).succ from Fin.succ_succAbove_succ i k]
      rfl
  · apply Function.hfunext rfl
    intro k l h
    cases h
    cases k using Fin.cases with
    | zero =>
      simp only [Cech.prependSection, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk]
      rfl
    | succ k =>
      simp only [Cech.prependSection, SimplexCategory.mkHom,
        SimplexCategory.Hom.toOrderHom_mk]
      rw [show i.succ.succAboveOrderEmb.toOrderHom k.succ =
        (i.succAbove k).succ from Fin.succ_succAbove_succ i k]
      rfl

/-- Prepending the section intertwines the coface pullback `δ_{i+1}` upstairs with the coface
pullback `δ_i` downstairs. -/
private lemma reindexMap_faceSucc_comp_prepend
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (n : ℕ) (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x))
    (i : Fin (n + 2)) :
    reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ i.succ) ≫
      prependSectionMap q f F (n + 1) s α hα =
    prependSectionMap q f F n s α hα ≫
      reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ i) := by
  let P := Tuple.projection q f (n + 1)
  let Q := Tuple.projection q f (n + 2)
  let R := Tuple.projection q f n
  let H := Cech.prependSection q f (n + 1) s α hα
  let J := Cech.prependSection q f n s α hα
  let D := Tuple.reindex q f (SimplexCategory.δ i.succ).toOrderHom
  let E := Tuple.reindex q f (SimplexCategory.δ i).toOrderHom
  have hfacH : Functor.whiskerLeft P.op
      (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F (n + 1) s α hα) ≫
      P.op.ranCounit.app (P.op ⋙ F) =
    Functor.whiskerLeft H.op (Q.op.ranCounit.app (Q.op ⋙ F)) := by
    simpa [P, Q, H] using
      prependSectionMap_fac.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F (n + 1) s α hα
  have hfacJ : Functor.whiskerLeft R.op
      (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα) ≫
      R.op.ranCounit.app (R.op ⋙ F) =
    Functor.whiskerLeft J.op (P.op.ranCounit.app (P.op ⋙ F)) := by
    simpa [P, R, J] using
      prependSectionMap_fac.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα
  apply (P.op.ran.obj (P.op ⋙ F)).hom_ext_of_isRightKanExtension
    (P.op.ranCounit.app (P.op ⋙ F))
  simp only [Functor.whiskerLeft_comp, Category.assoc]
  rw [hfacH]
  ext x z
  have hd := congr_app (reindexMap_fac.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
    (p := q) (f := f) F (SimplexCategory.δ i.succ)) (H.op.obj x)
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at hd
  have hd' :
      (reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
        q f F (SimplexCategory.δ i.succ)).app (P.op.obj x) ≫
      (Q.op.ranCounit.app (Q.op ⋙ F)).app (H.op.obj x) =
      (P.op.ranCounit.app (P.op ⋙ F)).app (D.op.obj (H.op.obj x)) := by
    convert hd using 1
    simp [P, Q, H, D, Tuple.projection, Tuple.reindex, Cech.prependSection]
  have hi' :
      (reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
        q f F (SimplexCategory.δ i)).app (P.op.obj x) ≫
        (P.op.ranCounit.app (P.op ⋙ F)).app x =
      (R.op.ranCounit.app (R.op ⋙ F)).app (E.op.obj x) := by
    simpa [P, R, E, Functor.whiskerLeft_app, NatTrans.comp_app] using
      congr_app (reindexMap_fac.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
        (p := q) (f := f) F (SimplexCategory.δ i)) x
  have hj' :
      (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα).app
        (R.op.obj (E.op.obj x)) ≫
        (R.op.ranCounit.app (R.op ⋙ F)).app (E.op.obj x) =
      (P.op.ranCounit.app (P.op ⋙ F)).app (J.op.obj (E.op.obj x)) := by
    simpa [P, R, J, Functor.whiskerLeft_app, NatTrans.comp_app] using
      congr_app hfacJ (E.op.obj x)
  have hobj' : D.op.obj (H.op.obj x) = J.op.obj (E.op.obj x) := by
    simpa [Functor.comp_obj, H, D, E, J] using congrArg Opposite.op
      (prependSection_reindex_face_obj q f n s α hα i x.unop)
  have hmiddle :
      (P.op.ranCounit.app (P.op ⋙ F)).app (D.op.obj (H.op.obj x)) =
        (P.op.ranCounit.app (P.op ⋙ F)).app (J.op.obj (E.op.obj x)) :=
    eq_of_heq (congr_arg_heq (P.op.ranCounit.app (P.op ⋙ F)).app hobj')
  have hcalc :
      (reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
        q f F (SimplexCategory.δ i.succ)).app (P.op.obj x) ≫
        (Q.op.ranCounit.app (Q.op ⋙ F)).app (H.op.obj x) =
      (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα).app (P.op.obj x) ≫
        (reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
          q f F (SimplexCategory.δ i)).app (P.op.obj x) ≫
      (P.op.ranCounit.app (P.op ⋙ F)).app x := by
    refine hd'.trans (hmiddle.trans (hj'.symm.trans ?_))
    show (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα).app
      (P.op.obj x) ≫ (R.op.ranCounit.app (R.op ⋙ F)).app (E.op.obj x) = _
    rw [← hi']
  exact congrArg (fun φ : (P.op ⋙ term q f F (n + 1)).obj x ⟶
      (P.op ⋙ F).obj x => φ.hom z) hcalc

/-- The augmentations are compatible with every simplicial reindexing, since the projections of
the relative Čech nerve are `1`-morphisms over `𝒳`. -/
public theorem augmentation_comp_reindexMap
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F m ≫
      reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F φ =
      augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n := by
  let P := Tuple.projection q f m
  let Q := Tuple.projection q f n
  let D := Tuple.reindex q f φ.toOrderHom
  apply (Q.op.ran.obj (Q.op ⋙ F)).hom_ext_of_isRightKanExtension
    (Q.op.ranCounit.app (Q.op ⋙ F))
  rw [Functor.whiskerLeft_comp, Category.assoc, reindexMap_fac]
  exact NatTrans.ext <| funext fun x => (P.op.ranCounit_app_app_ranAdjunction_unit_app_app
    (H := AddCommGrpCat.{max vᵤ vₓ wₓ t}) (G := F) (X := D.op.obj x)).trans
    (Q.op.ranCounit_app_app_ranAdjunction_unit_app_app
      (H := AddCommGrpCat.{max vᵤ vₓ wₓ t}) (G := F) (X := x)).symm

/-- Reindexing along the first coface, after prepending the section, is the contracting map
followed by the augmentation. -/
private lemma faceOne_comp_prepend
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ (1 : Fin 2)) ≫
      prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 s α hα =
    sectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα ≫
      augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 := by
  let P := Tuple.projection q f 0
  let Q := Tuple.projection q f 1
  let H := Cech.prependSection q f 0 s α hα
  let D := Tuple.reindex q f (SimplexCategory.δ (1 : Fin 2)).toOrderHom
  apply (P.op.ran.obj (P.op ⋙ F)).hom_ext_of_isRightKanExtension
    (P.op.ranCounit.app (P.op ⋙ F))
  simp only [Functor.whiskerLeft_comp, Category.assoc]
  rw [prependSectionMap_fac, sectionMap_eq_whiskeredCounit]
  apply NatTrans.ext
  funext x
  have hface := congr_app
    (reindexMap_fac.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}
      (p := q) (f := f) F (SimplexCategory.δ (1 : Fin 2))) (H.op.obj x)
  have hunit := P.op.ranCounit_app_app_ranAdjunction_unit_app_app
    (H := AddCommGrpCat.{max vᵤ vₓ wₓ t}) (G := F) (X := x)
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app] at hface ⊢
  dsimp only [augmentation]
  rw [hunit]
  have hobj : D.op.obj (H.op.obj x) = (Cech.sectionTuple q f s α hα).op.obj (P.op.obj x) := by
    apply congrArg Opposite.op
    dsimp only [D, H, P, Tuple.reindex, Tuple.projection, SimplexCategory.δ]
    rw [Tuple.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · funext index
      fin_cases index
      rfl
    · apply Function.hfunext rfl
      intro index other equality
      cases equality
      fin_cases index
      rfl
  have hmiddle : (P.op.ranCounit.app (P.op ⋙ F)).app (D.op.obj (H.op.obj x)) =
      (P.op.ranCounit.app (P.op ⋙ F)).app
        ((Cech.sectionTuple q f s α hα).op.obj (P.op.obj x)) :=
    eq_of_heq (congr_arg_heq (P.op.ranCounit.app (P.op ⋙ F)).app hobj)
  exact (hface.trans hmiddle).trans (Category.id_comp _).symm

/-- The augmentation of abelian presheaves lies in the kernel of the first differential of the
relative Čech complex. -/
public theorem augmentation_comp_d
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t}) :
    augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 ≫
      (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d 0 1 = 0 := by
  have hd : (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d 0 1 =
      ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
        reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ i) :=
    complex_d.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F 0
  have hsum : augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 ≫
      (∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) •
        reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ i)) = 0 := by
    rw [Preadditive.comp_sum]
    simp [augmentation_comp_reindexMap, Fin.sum_univ_two]
  exact (congrArg (fun φ => augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 ≫ φ) hd).trans
    hsum

/-- The contraction identity in degree `0`, at the level of abelian presheaves. -/
private lemma differential_comp_prepend_zero
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    (sectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα ≫
        augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 :
      term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F 0 ⟶
        term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F 0) +
      ((complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d 0 1 ≫
          prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0 s α hα :
        term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F 0 ⟶
          term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F 0) = 𝟙 _ := by
  rw [complex_d.{wᵤ, wₓ, _, vᵤ, vₓ, _, t}, Fin.sum_univ_two]
  simp [Preadditive.add_comp, faceZero_comp_prepend, faceOne_comp_prepend]

/-- The contraction identity in the positive degrees, at the level of abelian presheaves. -/
private lemma differential_comp_prepend_succ
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (n : ℕ) (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα ≫
        (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d n (n + 1) :
      term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1) ⟶
        term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1)) +
      ((complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d (n + 1) (n + 2) ≫
          prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F (n + 1) s α hα :
        term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1) ⟶
          term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1)) = 𝟙 _ := by
  rw [complex_d.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1)]
  show (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα ≫
      (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).d n (n + 1) :
        term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1) ⟶
          term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1)) +
    (∑ i : Fin (n + 3), (-1 : ℤ) ^ (i : ℕ) •
        reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ i)) ≫
      prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F (n + 1) s α hα = _
  rw [Preadditive.sum_comp, Fin.sum_univ_succ]
  simp only [Preadditive.zsmul_comp, Fin.val_zero, pow_zero, one_zsmul,
    faceZero_comp_prepend, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
    Preadditive.neg_comp, reindexMap_faceSucc_comp_prepend, Finset.sum_neg_distrib]
  rw [complex_d.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F n]
  show (prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα ≫
      (∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
          reindexMap.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (SimplexCategory.δ j) :
        term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F n ⟶
          term.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F (n + 1))) + _ = _
  rw [Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul]
  abel

/-- The extended relative Čech complex of an abelian presheaf:
`F ⟶ f_{0,*}f_0⁻¹F ⟶ f_{1,*}f_1⁻¹F ⟶ …`, indexed by `ℕ` with `F` in degree `0`. -/
public def extendedComplex
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t}) :
    CochainComplex (𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t}) ℕ :=
  (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f F).augment
    (augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F 0)
    (augmentation_comp_d.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F)

/-- A section up to a vertical `2`-isomorphism contracts the extended relative Čech complex of
an abelian presheaf. -/
public theorem nonempty_homotopy_extendedComplex_id_zero
    (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    (f : 𝒰 ⥤ 𝒳) (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max vᵤ vₓ wₓ t})
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    Nonempty (Homotopy (𝟙 (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F)) 0) := by
  let h : ∀ n, (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F).X (n + 1) ⟶
      (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F).X n
    | 0 => sectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα
    | n + 1 => prependSectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα
  have h₀ : (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F).d 0 1 ≫ h 0 = 𝟙 _ :=
    augmentation_comp_sectionMap.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα
  have hs : ∀ n, h n ≫ (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F).d n (n + 1) +
      (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F).d (n + 1) (n + 2) ≫ h (n + 1) = 𝟙 _ := by
    rintro (_ | n)
    · exact differential_comp_prepend_zero.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F s α hα
    · exact differential_comp_prepend_succ.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F n s α hα
  exact ⟨Cech.homotopyOfContraction (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f F) h h₀ hs⟩

section Sheafified

attribute [-instance] AddCommGrpCat.instAbelian

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰] {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
  (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (f : 𝒰 ⥤ 𝒳)
  (τ : AlgebraicGeometry.SiteKind)
  [HasSheafify (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max vᵤ vₓ wₓ t}]
  (𝓕 : Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max vᵤ vₓ wₓ t})

/-- The relative Čech complex `𝒦^•(f, 𝓕)` of an abelian sheaf, sheafified degreewise: a complex
of abelian sheaves on the site associated with `𝒳` for the topology `τ`. -/
public def sheafComplex :
    CochainComplex (Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) ℕ :=
  ((presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max vᵤ vₓ wₓ t}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f 𝓕.obj)

/-- The canonical augmentation from an abelian sheaf to degree `0` of its sheafified relative
Čech complex: the unit of the right-Kan-extension adjunction along the degree-`0` projection of
the relative Čech nerve, sheafified. -/
public def sheafAugmentation :
    𝓕 ⟶ (sheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).X 0 :=
  (sheafificationIso 𝓕).hom ≫
    (presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}).map
      (((Tuple.projection q f 0).op.ranAdjunction
        AddCommGrpCat.{max vᵤ vₓ wₓ t}).unit.app 𝓕.obj)

/-- The augmentation lies in the kernel of the first differential of the sheafified relative
Čech complex, which is what makes the extended complex a complex. -/
public theorem sheafAugmentation_comp_d :
    sheafAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕 ≫
      (sheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).d 0 1 = 0 := by
  let : Abelian AddCommGrpCat.{max vᵤ vₓ wₓ t} := AddCommGrpCat.instAbelian
  let L := presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max vᵤ vₓ wₓ t}
  let P := complex.{wᵤ, wₓ, _, vᵤ, vₓ, _, t} q f 𝓕.obj
  let a := augmentation.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f 𝓕.obj 0
  show (sheafificationIso 𝓕).hom ≫ L.map a ≫ L.map (P.d 0 1) = 0
  rw [show L.map a ≫ L.map (P.d 0 1) = L.map (a ≫ P.d 0 1) from (L.map_comp _ _).symm,
    augmentation_comp_d, L.map_zero, comp_zero]

/-- The extended relative Čech complex of an abelian sheaf:
`𝓕 ⟶ f_{0,*}f_0⁻¹𝓕 ⟶ f_{1,*}f_1⁻¹𝓕 ⟶ …` in abelian sheaves, obtained by sheafifying the
extended relative Čech complex of abelian presheaves degreewise. -/
public def extendedSheafComplex :
    CochainComplex (Sheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) ℕ :=
  ((presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
    AddCommGrpCat.{max vᵤ vₓ wₓ t}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (extendedComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f 𝓕.obj)

/-- Degree `0` of the extended relative Čech complex of an abelian sheaf is canonically `𝓕`
itself: the sheafification of the underlying presheaf of a sheaf is that sheaf. -/
public def extendedSheafComplexXZeroIso :
    (extendedSheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).X 0 ≅ 𝓕 :=
  (sheafificationIso 𝓕).symm

/-- In positive degrees the extended relative Čech complex of an abelian sheaf is the sheafified
relative Čech complex shifted by one. -/
@[simp] public theorem extendedSheafComplex_X_succ (n : ℕ) :
    (extendedSheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).X (n + 1) =
      (sheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).X n :=
  rfl

/-- In positive degrees the differential of the extended relative Čech complex of an abelian
sheaf is the differential of the sheafified relative Čech complex. -/
public theorem extendedSheafComplex_d_succ (n : ℕ) :
    (extendedSheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).d (n + 1) (n + 2) =
      (sheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕).d n (n + 1) :=
  rfl

/-- **Stacks 06XA.** If there is a `1`-morphism `s : 𝒳 ⥤ 𝒰` such that `f ∘ s` is `2`-isomorphic
to `id_𝒳` by a vertical `2`-isomorphism, then the extended relative Čech complex is homotopic to
zero: its identity is homotopic to its zero endomorphism. -/
@[stacks 06XA]
public theorem nonempty_homotopy_extendedSheafComplex_id_zero
    (s : 𝒳 ⥤ 𝒰) (α : s ⋙ f ≅ 𝟭 𝒳)
    (hα : ∀ x : 𝒳, q.IsHomLift (𝟙 (q.obj x)) (α.hom.app x)) :
    Nonempty (Homotopy
      (𝟙 (extendedSheafComplex.{u, vᵤ, vₓ, wᵤ, wₓ, t} B S hS q f τ 𝓕)) 0) := by
  let : Abelian AddCommGrpCat.{max vᵤ vₓ wₓ t} := AddCommGrpCat.instAbelian
  obtain ⟨H⟩ :=
    nonempty_homotopy_extendedComplex_id_zero.{u, vᵤ, vₓ, wᵤ, wₓ, t} q f 𝓕.obj s α hα
  have H' := Functor.mapHomotopy
    (presheafToSheaf (AlgebraicGeometry.BigFppfOver.associatedTopology B S hS q τ)
      AddCommGrpCat.{max vᵤ vₓ wₓ t}) H
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at H'
  exact ⟨H'⟩

end Sheafified

end Stacks.RelativeCech

end

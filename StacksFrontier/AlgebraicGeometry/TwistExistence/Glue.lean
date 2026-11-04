module

public import StacksFrontier.AlgebraicGeometry.TwistExistence.Overlap

/-!
# Tag 01NR's first uniqueness assertion

The chart comparisons of two sets of twist data on a relative Proj agree on the overlaps
(`Stacks.AlgebraicGeometry.TwistExistence.cmp_agreeOn`), so they glue; the glued isomorphism is
multiplicative and commutes with the homogeneous-section maps, because each comparison is; and
`Stacks.AlgebraicGeometry.TwistUnique.isUniqueTwistData_of_exists` then upgrades existence to
`∃!`. This file carries that out, and proves
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsUniqueTwistData`.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistExistence.glueLoc` and `glueIso`: **the glued comparison of the
  `n`-th glued pieces of two twist data**, as a local isomorphism on the whole relative Proj and
  as an isomorphism of sheaves of modules.
* `Stacks.AlgebraicGeometry.TwistExistence.glueAlgIso`: **the isomorphism of the two glued graded
  algebras.**

## Main results

* `Stacks.AlgebraicGeometry.TwistExistence.glueIso_mul`: the glued isomorphism is multiplicative,
  on the sections over **every** open of the relative Proj and not only over those inside a
  chart.
* `Stacks.AlgebraicGeometry.TwistExistence.glueIso_psi`: it commutes with the
  homogeneous-section maps.
* `Stacks.AlgebraicGeometry.TwistExistence.isUniqueTwistData`: **Tag 01NR's first uniqueness
  assertion.** Any two sets of twist data on a relative Proj are carried into each other by a
  unique isomorphism of graded algebras commuting with the homogeneous-section maps.

## The route

Both `glueIso_mul` and `glueIso_psi` are statements about sections over an arbitrary open, while
the comparisons are only available over the inverse images of the affine opens of the base. Both
are therefore checked on a covering and assembled by the separation half of the sheaf axiom for
the target — `TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf`. The covering is the inverse
images of the affine opens for the product, which cover the relative Proj
(`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.iSup_toBase_preimage_eq_top`), and the inverse
images of the affine opens *contained in the given open of the base* for the section maps
(`Stacks.AlgebraicGeometry.ChartTransRelativeProj.le_iSup_preimage_affine_le`); the second cannot
be replaced by the first, since an affine open whose inverse image meets the inverse image of
`V` need not be contained in `V` — the structure morphism of a relative Proj need not be
surjective.

Both reductions use only that every morphism in sight commutes with restriction: the glued
isomorphism and the homogeneous-section maps because they are morphisms of sheaves of modules,
and the products because compatibility with restriction is a field of
`Stacks.BilinearMap`.

## What is not done here

**No `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed.** Tag 01NR's
existence assertion is untouched, and so are the chart formulas of
`StacksFrontier/AlgebraicGeometry/RelativeProjTwists/Statement.lean`, which are proved for an
arbitrary twist datum and therefore still say nothing about a canonical one.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.TwistExistence

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-! ### The glued comparison -/

/-- The chart comparisons of two twist data, as a family indexed by the affine opens of the
base. -/
public def cmpFamily (D E : TwistData A) (n : ℤ) (i : S.affineOpens) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val (E.algebra.piece n).val
      ((relativeProj A).toBase ⁻¹ᵁ (i.1 : S.Opens)) :=
  cmp D E (i.1 : S.Opens) i.2 n

/-- The family agrees on all overlaps, which is
`Stacks.AlgebraicGeometry.TwistExistence.cmp_agreeOn`. -/
public theorem cmpFamily_agree (D E : TwistData A) (n : ℤ) (i j : S.affineOpens)
    (V : (relativeProj A).scheme.Opens)
    (hVi : V ≤ (relativeProj A).toBase ⁻¹ᵁ (i.1 : S.Opens))
    (hVj : V ≤ (relativeProj A).toBase ⁻¹ᵁ (j.1 : S.Opens))
    (x : (D.algebra.piece n).val.obj (op V)) :
    (cmpFamily D E n i).app V hVi x = (cmpFamily D E n j).app V hVj x :=
  cmp_agreeOn D E (i.1 : S.Opens) (j.1 : S.Opens) i.2 j.2 n V hVi hVj x

/-- **The glued comparison**, as a local isomorphism on the whole relative Proj. -/
public def glueLoc (D E : TwistData A) (n : ℤ) :
    TopCat.Sheaf.LocalModuleEquiv (D.algebra.piece n).val (E.algebra.piece n).val ⊤ :=
  TopCat.Sheaf.LocalModuleEquiv.glueLE (D.algebra.piece n).isSheaf
    (E.algebra.piece n).isSheaf (cmpFamily D E n) (cmpFamily_agree D E n)
    (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)).ge

/-- Over an open inside the inverse image of an affine open of the base, the glued comparison is
the comparison attached to that affine open. -/
public theorem glueLoc_app_of_le (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U) (n : ℤ)
    (V : (relativeProj A).scheme.Opens) (hVU : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (glueLoc D E n).app V le_top x = (cmp D E U hU n).app V hVU x :=
  TopCat.Sheaf.LocalModuleEquiv.glueLE_app_of_le (D.algebra.piece n).isSheaf
    (E.algebra.piece n).isSheaf (cmpFamily D E n) (cmpFamily_agree D E n)
    (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)).ge
    (i := ⟨U, hU⟩) le_top hVU x

/-- **The glued comparison of the `n`-th glued pieces of two twist data.** -/
public def glueIso (D E : TwistData A) (n : ℤ) : D.algebra.piece n ≅ E.algebra.piece n :=
  isoOfLocalEquiv (X := (relativeProj A).scheme) (glueLoc D E n)

/-- Over an open inside the inverse image of an affine open of the base, the glued isomorphism is
the comparison attached to that affine open. -/
public theorem glueIso_hom_app_of_le (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U)
    (n : ℤ) (V : (relativeProj A).scheme.Opens) (hVU : V ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (x : (D.algebra.piece n).val.obj (op V)) :
    (glueIso D E n).hom.val.app (op V) x = (cmp D E U hU n).app V hVU x :=
  (isoOfLocalEquiv_hom_app (X := (relativeProj A).scheme) (glueLoc D E n) V x).trans
    (glueLoc_app_of_le D E U hU n V hVU x)

/-! ### Multiplicativity and the homogeneous-section maps -/

/-- Restricting the glued isomorphism to an open inside the inverse image of an affine open of the
base gives the comparison attached to that affine open, applied to the restriction. -/
private theorem resLE_glueIso_hom_app (D E : TwistData A) (U : S.Opens) (hU : IsAffineOpen U)
    (n : ℤ) {V W : (relativeProj A).scheme.Opens} (hWV : W ≤ V)
    (hWU : W ≤ (relativeProj A).toBase ⁻¹ᵁ U) (x : (D.algebra.piece n).val.obj (op V)) :
    (E.algebra.piece n).val.resLE hWV ((glueIso D E n).hom.val.app (op V) x) =
      (cmp D E U hU n).app W hWU ((D.algebra.piece n).val.resLE hWV x) :=
  (PresheafOfModules.app_resLE (glueIso D E n).hom.val hWV x).symm.trans
    (glueIso_hom_app_of_le D E U hU n W hWU _)

/-- **The glued isomorphism is multiplicative**, on the sections over every open of the relative
Proj. Checked on the covering by the inverse images of the affine opens of the base, where it is
a chart comparison, and assembled by the separation half of the sheaf axiom. -/
public theorem glueIso_mul (D E : TwistData A) (i j : ℤ)
    (V : (relativeProj A).scheme.Opensᵒᵖ) (x : (D.algebra.piece i).val.obj V)
    (y : (D.algebra.piece j).val.obj V) :
    (glueIso D E (i + j)).hom.val.app V ((D.algebra.mul i j).app V x y) =
      (E.algebra.mul i j).app V ((glueIso D E i).hom.val.app V x)
        ((glueIso D E j).hom.val.app V y) := by
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (E.algebra.piece (i + j)).isSheaf
    (fun m : S.affineOpens => V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens))
    (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf
      (RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)) V.unop) fun m => ?_
  have hWV : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens) ≤ V.unop := inf_le_left
  have hWU : V.unop ⊓ (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens) ≤
    (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens) := inf_le_right
  refine (resLE_glueIso_hom_app D E _ m.2 _ hWV hWU _).trans ?_
  refine Eq.trans (congrArg ((cmp D E _ m.2 (i + j)).app _ hWU)
    ((D.algebra.mul i j).naturality (homOfLE hWV).op x y)) ?_
  refine (cmp_mul D E _ m.2 i j _ hWU _ _).trans ?_
  refine Eq.trans (TwistRigidity.mul_app_congr E.algebra i j _
    (resLE_glueIso_hom_app D E _ m.2 i hWV hWU x).symm
    (resLE_glueIso_hom_app D E _ m.2 j hWV hWU y).symm) ?_
  exact ((E.algebra.mul i j).naturality (homOfLE hWV).op _ _).symm

/-- **The glued isomorphism commutes with the homogeneous-section maps.** Checked on the covering
of the inverse image of an open of the base by the inverse images of the affine opens *contained
in it*. -/
public theorem glueIso_psi (D E : TwistData A) (k : ℕ) :
    D.ψ k ≫ (Scheme.Modules.pushforward (relativeProj A).toBase).map
      (glueIso D E (k : ℤ)).hom = E.ψ k := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun s => ?_))
  refine TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (E.algebra.piece (k : ℤ)).isSheaf
    (fun m : {m : S.affineOpens // (m.1 : S.Opens) ≤ V.unop} =>
      (relativeProj A).toBase ⁻¹ᵁ (m.1.1 : S.Opens))
    (fun m => preimage_le_preimage (m.1.1 : S.Opens) V.unop m.2)
    (ChartTransRelativeProj.le_iSup_preimage_affine_le A V.unop) fun m => ?_
  refine (resLE_glueIso_hom_app D E (m.1.1 : S.Opens) m.1.2 (k : ℤ)
    (preimage_le_preimage (m.1.1 : S.Opens) V.unop m.2) le_rfl _).trans ?_
  refine Eq.trans (congrArg ((cmp D E (m.1.1 : S.Opens) m.1.2 (k : ℤ)).app _ le_rfl)
    (PresheafOfModules.app_resLE (D.ψ k).val m.2 s).symm) ?_
  refine Eq.trans (cmp_psi D E (m.1.1 : S.Opens) m.1.2 k
    ((A.piece (k : ℤ)).val.resLE m.2 s)) ?_
  exact PresheafOfModules.app_resLE (E.ψ k).val m.2 s

/-! ### The isomorphism of graded algebras -/

/-- The forward homomorphism of graded algebras. -/
public def glueHom (D E : TwistData A) : D.algebra ⟶ E.algebra where
  app n := (glueIso D E n).hom
  map_mul i j V x y := glueIso_mul D E i j V x y

/-- The backward homomorphism of graded algebras: multiplicativity transports along the
isomorphism, the forward components being injective on sections. -/
public def glueInvHom (D E : TwistData A) : E.algebra ⟶ D.algebra where
  app n := (glueIso D E n).inv
  map_mul i j V x y :=
    ((TwistRigidity.iso_inv_app_hom_app (glueIso D E (i + j)) V
          ((D.algebra.mul i j).app V ((glueIso D E i).inv.val.app V x)
            ((glueIso D E j).inv.val.app V y))).symm.trans
        (congrArg ((glueIso D E (i + j)).inv.val.app V)
          ((glueIso_mul D E i j V _ _).trans
            (TwistRigidity.mul_app_congr E.algebra i j V
              (TwistRigidity.iso_hom_app_inv_app (glueIso D E i) V x)
              (TwistRigidity.iso_hom_app_inv_app (glueIso D E j) V y))))).symm

/-- **The isomorphism of the two glued graded algebras.** -/
public def glueAlgIso (D E : TwistData A) : D.algebra ≅ E.algebra where
  hom := glueHom D E
  inv := glueInvHom D E
  hom_inv_id :=
    SheafOfModules.GradedAlgebra.Hom.ext fun n => (glueIso D E n).hom_inv_id
  inv_hom_id :=
    SheafOfModules.GradedAlgebra.Hom.ext fun n => (glueIso D E n).inv_hom_id

/-- **Tag 01NR's first uniqueness assertion.** Any two sets of twist data on a relative Proj are
carried into each other by a *unique* isomorphism of graded algebras commuting with the
homogeneous-section maps. The existence half is the glued comparison of this file; the
uniqueness half is
`Stacks.AlgebraicGeometry.TwistUnique.isUniqueTwistData_of_exists`. -/
@[stacks 01NR "uniqueness of the complete structure"]
public theorem isUniqueTwistData (A : SheafGradedAlgebra S) : IsUniqueTwistData A :=
  TwistUnique.isUniqueTwistData_of_exists A
    fun D E => ⟨glueAlgIso D E, fun k => glueIso_psi D E k⟩

end Stacks.AlgebraicGeometry.TwistExistence

end

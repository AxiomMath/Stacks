module

public import StacksFrontier.AlgebraicGeometry.SymTwistChart.Proj
public import StacksFrontier.AlgebraicGeometry.TwistGenerator.Basic

/-!
# A graded ring homomorphism out of `Γ(U, Sym E)` is determined in degree one

Let `X` be a scheme, `E` a quasi-coherent `𝒪_X`-module and `U` an affine open. The graded ring of
sections `Γ(U, Sym E)` is the symmetric algebra of `Γ(E, U)` over `Γ(X, U)`
(`Stacks.SymGraded.AffinePieces.symSectionRingEquiv`), and a ring homomorphism out of a symmetric
algebra is determined by its values on the base ring and on the degree-one generators
(`SymmetricAlgebra.ringHom_ext`). **So a homomorphism out of `Γ(U, Sym E)` is determined by its
values on the structure map and on the degree-one summand**, which is
`Stacks.SymTwistChart.gradedRingHom_ext_degree_one`.

That is the extensionality principle with which the chart comparison
`Stacks.SymTwistChart.chartGradedHom` of
`StacksFrontier/AlgebraicGeometry/SymTwistChart/Proj.lean` is identified with its variants: there is
nothing to check beyond degree one. This file supplies the principle and the two degree-one
computations the identifications need — what the comparison does in degree one, and how the
degree-one summand restricts to a smaller open — together with the fact that the generator cut
out by a trivialization generates the module of sections, which is what makes two trivializations
differ by a unit.

## Main definitions

* `Stacks.SymTwistChart.symOne`: **the degree-one homogeneous section of `Sym(E)` over `U` cut
  out by a section of `E`**, with `symOne_smul` for its linearity.

## Main results

* `Stacks.SymTwistChart.symSectionRingEquiv_symm_algebraMap` and
  `Stacks.SymTwistChart.symSectionRingEquiv_of_symOne`: the two values of the identification
  `Γ(U, Sym E) ≅ Sym_{Γ(X,U)} Γ(E, U)` that the extensionality principle consumes — the structure
  map goes to the base ring, and the degree-one summand to the degree-one generators.
* `Stacks.SymTwistChart.gradedRingHom_ext_degree_one`: **two graded ring homomorphisms out of
  `Γ(U, Sym E)` agreeing on the structure map and on the degree-one summand are equal.**
* `Stacks.SymTwistChart.chartRingEquiv_of_symOne`: **the chart comparison in degree one is
  `x ↦ x ⊗ g`.**
* `Stacks.SymTwistChart.resPiece_symOne`: the degree-one summand restricts by restricting the
  section of `E`.
* `Stacks.SymTwistChart.bijective_toSpanSingleton_generator`: **the generator cut out by a
  trivialization generates `Γ(L, U)` over `Γ(X, U)`.**

## Implementation notes

**Why the extensionality principle is not the `Algebra.adjoin` one.** Degree-one generation of
`Γ(U, Sym E)` is already available as
`Stacks.SymGraded.isGeneratedInDegreeOne_schemeSheafGradedAlgebra`, in the form
`Algebra.adjoin (grading U 0) (grading U 1) = ⊤`. Using it would force two further lemmas — that
every element of `grading U 0` is a structure-map image and every element of `grading U 1` a
degree-one generator — because the `adjoin` statement quantifies over the *submodules* while
every computation here is about the explicit generators. Going through
`SymmetricAlgebra.ringHom_ext` instead, with
`Stacks.SymGraded.AffinePieces.symSectionRingEquiv` transporting, states the hypotheses directly
at the elements that occur: `A.strHom U r` and `DirectSum.of _ 1 (symOne E hqc m)`.

**Why `symOne` is written with `Stacks.SymGraded.siteGen` and not with
`Stacks.SymGraded.ιG`.** The degree-one element of the presheaf of
sectionwise graded pieces is `ιG Γ(E, U) m`, but that term cannot be written down here: `ιG`
takes its base ring as an instance-implicit argument, and the ring by which
`Stacks.SymGraded.siteGradedPiece` is indexed is `𝒪_X ⋙ forget₂ CommRingCat RingCat` evaluated
at `U`, a spelling at which instance search finds neither `Module … Γ(E, U)` nor, one level up,
`CommRing`. Each way of supplying it — a type ascription at the `Γ(X, U)` spelling, pinning the
semilinear map, a local bridge instance — fails at a different point, because the instance the
site presheaf uses is carried by `E.val` itself rather than synthesized. `Stacks.SymGraded.siteGen`
is a *declaration* whose application is exactly `ιG` at that spelling, so writing `symOne`
through it needs no instance search at all; and its naturality, which is a field of the morphism,
is then what proves `resPiece_symOne` with no sectionwise computation.

**Degree casts.** `Stacks.SymGraded.AffinePieces.pieceSectionsEquiv` is indexed by `ℤ` and the
homogeneous summands by `ℕ`; the degree-one summand is
`sectionPieces U 1 = Γ(A.piece ((1 : ℕ) : ℤ), U)` and `gradedPiece Γ(E, U) (1 : ℤ)` is
`SymPow.symmetricPower 1` by `rfl` (`Stacks.SymGraded.gradedPiece_natCast`), so the two spellings
of the degree are the same term up to `whnf` and no rewrite is needed.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SymGraded.AffinePieces (pieceSectionsEquiv symSectionRingEquiv symSectionAlgEquiv)
open Stacks.SymGraded (gradedPiece)

universe u

namespace Stacks.SymTwistChart

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### The degree-one homogeneous sections -/

section Ext

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)
  {U : X.Opens}

/-- **The degree-one homogeneous section of `Sym(E)` over `U` cut out by a section of `E`**: the
image of `m` under the degree-one generator `E ⟶ Sym(E)₁`, spelled as the sheafification unit
applied to the sectionwise degree-one inclusion `Stacks.SymGraded.siteGen`. -/
public abbrev symOne (m : Γ(E, U)) :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U 1 :=
  PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
      (Stacks.SymGraded.siteGradedPiece E.val 1)) (op U)
    (PresheafOfModules.Hom.app (Stacks.SymGraded.siteGen E.val) (op U) m)

omit [E.IsQuasicoherent] in
/-- **The degree-one homogeneous sections are linear in the section of `E`.** Both
`Stacks.SymGraded.siteGen` and the sheafification unit are morphisms of presheaves of modules,
so each is linear on sections. -/
public theorem symOne_smul (r : Γ(X, U)) (m : Γ(E, U)) :
    symOne E hqc (r • m) = r • symOne E hqc m :=
  (congrArg (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
        (𝟙 X.ringCatSheaf.obj) (Stacks.SymGraded.siteGradedPiece E.val 1)) (op U))
      ((PresheafOfModules.Hom.app (Stacks.SymGraded.siteGen E.val) (op U)).hom.map_smul
        r m)).trans
    ((PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
        (Stacks.SymGraded.siteGradedPiece E.val 1)) (op U)).hom.map_smul r
      (PresheafOfModules.Hom.app (Stacks.SymGraded.siteGen E.val) (op U) m))

variable (hUaff : IsAffineOpen U)

/-- **The identification `Γ(U, Sym E) ≅ Sym_{Γ(X,U)} Γ(E, U)` carries the structure map to the
base ring.** This is `Stacks.SymGraded.AffinePieces.symSectionAlgEquiv`, which says the
identification is one of `Γ(X, U)`-algebras, read backwards. -/
public theorem symSectionRingEquiv_symm_algebraMap (r : Γ(X, U)) :
    (symSectionRingEquiv E hUaff hqc).symm
        (algebraMap Γ(X, U) (SymmetricAlgebra Γ(X, U) Γ(E, U)) r) =
      (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).strHom U r := by
  let := Stacks.SymGraded.AffinePieces.sectionAlgebra E hqc (V := U)
  exact (symSectionRingEquiv E hUaff hqc).symm_apply_eq.2
    ((symSectionAlgEquiv E hUaff hqc).commutes r).symm

/-- **The identification carries the degree-one summand to the degree-one generators.** On the
degree-one summand the identification is the inverse of the sheafification unit followed by the
inclusion of `Sym¹` into `Sym` (`Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of`), and the
sheafification unit of `Stacks.SymGraded.siteGen` is exactly what `symOne` is. -/
public theorem symSectionRingEquiv_of_symOne (m : Γ(E, U)) :
    symSectionRingEquiv E hUaff hqc
        (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
          (symOne E hqc m)) =
      SymmetricAlgebra.ι Γ(X, U) Γ(E, U) m :=
  (Stacks.SymGraded.AffinePieces.symSectionRingEquiv_of E hUaff hqc 1 _).trans
    (congrArg (fun y : gradedPiece (R := Γ(X, U)) Γ(E, U) 1 =>
        (y : SymmetricAlgebra Γ(X, U) Γ(E, U)))
      ((pieceSectionsEquiv E hUaff 1).symm_apply_apply
        (PresheafOfModules.Hom.app (Stacks.SymGraded.siteGen E.val) (op U) m)))

/-- The inverse identification carries the degree-one generators to the degree-one summand. -/
private theorem symSectionRingEquiv_symm_ι (m : Γ(E, U)) :
    (symSectionRingEquiv E hUaff hqc).symm (SymmetricAlgebra.ι Γ(X, U) Γ(E, U) m) =
      DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
        (symOne E hqc m) :=
  (symSectionRingEquiv E hUaff hqc).symm_apply_eq.2
    (symSectionRingEquiv_of_symOne E hqc hUaff m).symm

include hUaff in
/-- **A graded ring homomorphism out of `Γ(U, Sym E)` is determined in degree one.** Two graded
ring homomorphisms out of the graded ring of sections of `Sym(E)` over an affine open which agree
on the structure map and on the degree-one summand are equal.

The ring of sections is the symmetric algebra of `Γ(E, U)` over `Γ(X, U)`, and a ring
homomorphism out of a symmetric algebra is determined by its values on the base ring and on the
degree-one generators (`SymmetricAlgebra.ringHom_ext`); the two hypotheses are exactly those two
families of values, read through `Stacks.SymGraded.AffinePieces.symSectionRingEquiv`. -/
public theorem gradedRingHom_ext_degree_one {B τ : Type*} [CommRing B] [SetLike τ B]
    {ℬ : ℕ → τ}
    {φ ψ : (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).grading U →+*ᵍ ℬ}
    (h0 : ∀ r : Γ(X, U),
      φ ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).strHom U r) =
        ψ ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).strHom U r))
    (h1 : ∀ m : Γ(E, U),
      φ (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
          (symOne E hqc m)) =
        ψ (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).sectionPieces U) 1
          (symOne E hqc m))) :
    φ = ψ := by
  have key : φ.toRingHom.comp (symSectionRingEquiv E hUaff hqc).symm.toRingHom =
      ψ.toRingHom.comp (symSectionRingEquiv E hUaff hqc).symm.toRingHom := by
    refine SymmetricAlgebra.ringHom_ext (fun r => ?_) (fun m => ?_)
    · exact (congrArg φ (symSectionRingEquiv_symm_algebraMap E hqc hUaff r)).trans
        ((h0 r).trans (congrArg ψ (symSectionRingEquiv_symm_algebraMap E hqc hUaff r)).symm)
    · exact (congrArg φ (symSectionRingEquiv_symm_ι E hqc hUaff m)).trans
        ((h1 m).trans (congrArg ψ (symSectionRingEquiv_symm_ι E hqc hUaff m)).symm)
  refine GradedRingHom.ext fun x => ?_
  simpa using RingHom.congr_fun key (symSectionRingEquiv E hUaff hqc x)

end Ext

/-! ### Restriction in degree one -/

section Res

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (hqc : Stacks.SymGraded.IsQuasicoherentPieces E)

omit [E.IsQuasicoherent] in
/-- **The degree-one homogeneous sections restrict by restricting the section of `E`.** Both
`Stacks.SymGraded.siteGen` and the sheafification unit are morphisms of presheaves of modules,
so this is their naturality, twice; no affineness is involved. -/
public theorem resPiece_symOne {U U' : X.Opens} (h : U' ≤ U) (m : Γ(E, U)) :
    (Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).resPiece h 1 (symOne E hqc m) =
      symOne E hqc (E.val.map (homOfLE h).op m) := by
  refine Eq.trans ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqc).resPiece_apply h 1
    (symOne E hqc m)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
      (Stacks.SymGraded.siteGradedPiece E.val 1)) (homOfLE h).op
    (PresheafOfModules.Hom.app (Stacks.SymGraded.siteGen E.val) (op U) m)).symm ?_
  exact congrArg (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit
      (𝟙 X.ringCatSheaf.obj) (Stacks.SymGraded.siteGradedPiece E.val 1)) (op U'))
    (PresheafOfModules.naturality_apply (Stacks.SymGraded.siteGen E.val) (homOfLE h).op m).symm

end Res

/-! ### The comparison in degree one -/

section Degree

variable {X : Scheme.{u}} (E L : X.Modules)
  [E.IsQuasicoherent] [(tensorObj E L).IsQuasicoherent]
  (hqcE : Stacks.SymGraded.IsQuasicoherentPieces E)
  (hqcEL : Stacks.SymGraded.IsQuasicoherentPieces (tensorObj E L))
  {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
  (hUaff : IsAffineOpen U)

/-- **The chart comparison in degree one is `x ↦ x ⊗ g`.** On the degree-one summand the
comparison of the graded section rings is the equivalence of modules of sections it was built
from, which is tensoring with the generator cut out by the trivialization. Together with
`Stacks.SymTwistChart.chartRingEquiv_strHom` this determines the comparison, by
`Stacks.SymTwistChart.gradedRingHom_ext_degree_one`. -/
public theorem chartRingEquiv_of_symOne (m : Γ(E, U)) :
    chartRingEquiv E L hqcE hqcEL e hUaff
        (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionPieces U) 1
          (symOne E hqcE m)) =
      DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra
          (tensorObj E L) hqcEL).sectionPieces U) 1
        (symOne (tensorObj E L) hqcEL (sectionsEquiv E L e m)) := by
  refine (symSectionRingEquiv (tensorObj E L) hUaff hqcEL).injective ?_
  have hrfl : chartRingEquiv E L hqcE hqcEL e hUaff
        (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionPieces U) 1
          (symOne E hqcE m)) =
      (symSectionRingEquiv (tensorObj E L) hUaff hqcEL).symm
        (SymmetricAlgebra.mapEquiv (sectionsEquiv E L e)
          (symSectionRingEquiv E hUaff hqcE
            (DirectSum.of ((Stacks.SymGraded.schemeSheafGradedAlgebra E hqcE).sectionPieces U) 1
              (symOne E hqcE m)))) := rfl
  rw [hrfl, RingEquiv.apply_symm_apply, symSectionRingEquiv_of_symOne,
    SymmetricAlgebra.mapEquiv_ι, symSectionRingEquiv_of_symOne]

end Degree

/-! ### The generator of a trivialization generates -/

/-- **The generator cut out by a trivialization generates the module of sections.** The
trivialization is an isomorphism of `L|_U` with the structure sheaf of the localized site, so its
inverse acts bijectively on sections over `U`, and on `r` it acts by `r • g`, the generator being
the image of `1`.

With `Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton` this is what makes the
generators of two trivializations differ by a unit of `𝒪_X(U)`, hence what makes the chart
isomorphism independent of the trivialization. -/
public theorem bijective_toSpanSingleton_generator {X : Scheme.{u}} (L : X.Modules)
    {U : X.Opens} (e : L.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Function.Bijective (fun r : Γ(X, U) => r • generator L e) := by
  have hfun : ∀ r : Γ(X, U),
      r • generator L e = e.inv.val.app (op (Over.mk (𝟙 U))) r := by
    intro r
    refine Eq.trans ((e.inv.val.app (op (Over.mk (𝟙 U)))).hom.map_smul r
      (1 : (X.ringCatSheaf.over U).obj.obj (op (Over.mk (𝟙 U))))).symm ?_
    exact congrArg (fun y => e.inv.val.app (op (Over.mk (𝟙 U))) y)
      (mul_one (r : (X.ringCatSheaf.over U).obj.obj (op (Over.mk (𝟙 U)))))
  refine Eq.mpr (congrArg Function.Bijective (funext hfun)) ?_
  exact ((SheafOfModules.forget (X.ringCatSheaf.over U) ⋙
    PresheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).mapIso e.symm).toLinearEquiv.bijective

end Stacks.SymTwistChart

end

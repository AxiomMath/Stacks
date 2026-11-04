module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietorisAndHom.HomComplexMaps
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.InternalHomTermwiseSplit
import StacksCore.Tactic.StacksAttribute

/-!
# The derived internal Hom is a triangulated functor of its dualized variable

Let `(C, O)` be a ringed site and `M` an object of `D(O)`.  This file proves that the derived
internal Hom in its **contravariant** variable,

`RSheafHom(-, M) : D(O)ᵒᵖ ⥤ D(O)`,

carries distinguished triangles to distinguished triangles, for the commutation datum
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShift` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomSourceCommShift`.

## Main results

* `AlgebraicGeometry.RingedSite.homMap_homOfDegreewiseSplit_shift`: **the sign identity.**  The
  connecting morphism which the chosen commutation datum produces from that of a degreewise
  split short complex is exactly the one the induced splittings produce.
* `AlgebraicGeometry.RingedSite.mapTriangleOpTriangleOfDegreewiseSplitIso`: the internal Hom
  complex carries the opposite of the triangle of a degreewise split short complex to the
  triangle of the induced splittings.
* `AlgebraicGeometry.RingedSite.derivedSheafHomFlipIsTriangulated`: **the derived internal Hom
  into a fixed object is a triangulated functor of its dualized variable.**  With this the
  dévissage step
  `AlgebraicGeometry.RingedSite.isIso_derivedTensorDualToSheafHom_of_distTriang` applies with
  no instance arguments.
* `Stacks.Homology.DegreewiseSplitTriangle.Q_mapTriangle_triangleOfDegreewiseSplit_distinguished`
  and `…exists_iso_Q_mapTriangle_triangleOfDegreewiseSplit`: degreewise split short complexes
  of complexes present exactly the distinguished triangles of a derived category.
* `Stacks.CategoryTheory.OppositeShift.opTriangleMapTriangleIso`:
  `CategoryTheory.Functor.mapTriangle` commutes with the passage to the opposite category, for
  a shift-compatible functor between categories which need not be pretriangulated.

## Implementation notes

The route is the one the source's proof of Stacks 08JC indicates, carried out with a *chosen*
connecting morphism rather than an existential one.  A distinguished triangle of `D(O)ᵒᵖ` is the
opposite of one of `D(O)`; a distinguished triangle of `D(O)` is the image of the triangle of a
degreewise split short complex of complexes, by
`CochainComplex.triangleOfDegreewiseSplit`; the internal Hom complex reverses such a short
complex and the result is again degreewise split, by
`AlgebraicGeometry.RingedSite.internalHomTermwiseSplitting`; and the sign identity says that the
connecting morphism of that image splitting is the one the commutation datum of the source shift
produces.  The existential form of Stacks 08JC,
`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`, is **not** used and could
not be: a triangle `(f, g, δ)` being distinguished does not make `(f, g, δ')` distinguished for
a different `δ'`.

The signs are the ones `CochainComplex.HomComplex.Cochain.leftShift` carries.  A degree-`n`
cochain acquires `(-1)^(1-n)` from the source shift and the Hom-complex differential contributes
`(-1)^(n+1)`; the two cancel, which is why the identification is an equality of morphisms of
complexes and not merely a homotopy.

Three statements about the shift of an opposite category are proved here because Mathlib's forms
are unusable in this file.  Mathlib states
`CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctorApp` only for
pretriangulated source and target, and the category of cochain complexes is not pretriangulated;
and the two spellings `F.op.obj X` and `op (F.obj X.unop)` of one object make such statements not
type-correct at `implicit` transparency, since `CategoryTheory.Functor.op` is semireducible, so
that no rewriting tactic will traverse them — which is why Mathlib's own proofs there carry
the options `backward.defeqAttrib.useBackward` (turned on) and
`backward.isDefEq.respectTransparency` (turned off).  Doing the rewriting inside `conv`,
which rewrites a subterm without type-checking the whole target, dispenses with the options.

The universes are the diagonal `RingedSite.{u, u, u}` with modules in `u`, as the construction of
the internal Hom complex forces; the two general statements about derived categories and the
three about opposite shifts are stated at their own universes.

## References

* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 014L](https://stacks.math.columbia.edu/tag/014L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
  CochainComplex.HomComplex

universe v₁ v₂ u₁ u₂ w v u

namespace Stacks.CategoryTheory.OppositeShift

open CategoryTheory.Pretriangulated.Opposite

variable {C : Type u₁} [Category.{v₁} C] [HasShift C ℤ]

/-- **The counit of `CategoryTheory.Pretriangulated.opShiftFunctorEquivalence`, read through
`unop`.**  It is the canonical identification of the double shift with the identity: the
identification `CategoryTheory.Pretriangulated.shiftFunctorOpIso` it carries is the identity on
`unop`s. -/
lemma opShiftFunctorEquivalence_counitIso_inv_app_unop (Y : C) (n : ℤ) :
    ((opShiftFunctorEquivalence C n).counitIso.inv.app (op Y)).unop =
      (shiftFunctorCompIsoId C n (-n) (by omega)).hom.app Y := by
  refine Eq.trans (congrArg Quiver.Hom.unop
    (Pretriangulated.opShiftFunctorEquivalence_counitIso_inv_app (op Y) n (-n) (by omega))) ?_
  conv_lhs =>
    rw [unop_comp, Quiver.Hom.unop_op, shiftFunctorOpIso_inv_app_unop (op (Y⟦n⟧)) n]
    dsimp only [CategoryTheory.Functor.comp_obj,
      Pretriangulated.opShiftFunctorEquivalence_functor,
      Pretriangulated.opShiftFunctorEquivalence_inverse, CategoryTheory.Functor.op_obj,
      shiftFunctor_op_obj_unop, Opposite.unop_op]
    rw [Category.id_comp]

/-- **The connecting morphism of the opposite of a triangle, read through `unop`.**  It is the
shift by `-1` of the connecting morphism, followed by the canonical identification of the
double shift with the identity: the shift of `CategoryTheory.Pretriangulated.Opposite` is the
shift by the negated degree, and the identification `CategoryTheory.Pretriangulated.
shiftFunctorOpIso` which the counit of `CategoryTheory.Pretriangulated.
opShiftFunctorEquivalence` inserts is the identity on `unop`s. -/
lemma opTriangle_mor₃_unop (T : Triangle C) :
    ((triangleOpEquivalence C).functor.obj (op T)).mor₃.unop =
      T.mor₃⟦(-1 : ℤ)⟧' ≫ (shiftFunctorCompIsoId C 1 (-1) (by omega)).hom.app T.obj₁ := by
  change (((opShiftFunctorEquivalence C 1).counitIso.inv.app (op T.obj₁) ≫
      (T.mor₃.op)⟦(1 : ℤ)⟧').unop) = _
  conv_lhs =>
    rw [unop_comp, opShiftFunctorEquivalence_counitIso_inv_app_unop T.obj₁ 1,
      shiftFunctor_op_map_unop (T.mor₃.op) 1, Quiver.Hom.unop_op]
  rfl

section OpFunctor

variable {D : Type u₂} [Category.{v₂} D] [HasShift D ℤ] (F : C ⥤ D) [F.CommShift ℤ]

/-- **The commutation isomorphism of the opposite functor, read through `unop`.**  It is the
inverse of the commutation isomorphism of `F` at the negated degree: the two identifications
`CategoryTheory.Pretriangulated.shiftFunctorOpIso` which
`CategoryTheory.Functor.op_commShiftIso_hom_app` inserts are the identity on `unop`s.

Mathlib states that formula in the opposite category, where the two spellings `F.op.obj X` and
`op (F.obj X.unop)` of one object both occur; `CategoryTheory.Functor.op` is semireducible, so
the statement is not type-correct at `implicit` transparency and no rewriting tactic can act on
it.  Read through `unop` the formula is free of `CategoryTheory.Functor.op`. -/
lemma op_commShiftIso_hom_app_unop (X : Cᵒᵖ) (n : ℤ) :
    ((F.op.commShiftIso n).hom.app X).unop = (F.commShiftIso (-n)).inv.app X.unop := by
  refine Eq.trans (congrArg Quiver.Hom.unop
    (CategoryTheory.Functor.op_commShiftIso_hom_app F X n (-n) (by omega))) ?_
  conv_lhs =>
    rw [unop_comp, unop_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op,
      shiftFunctorOpIso_inv_app_unop (op (F.obj X.unop)) n,
      shiftFunctorOpIso_hom_app_unop X n]
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.op_obj,
      shiftFunctor_op_obj_unop, Opposite.unop_op]
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- **`CategoryTheory.Functor.mapTriangle` commutes with the passage to the opposite
category**, for a shift-compatible functor between categories which need not be
pretriangulated.

Mathlib's `CategoryTheory.Functor.mapTriangleOpCompTriangleOpEquivalenceFunctorApp` is the same
statement under the hypothesis that both categories are pretriangulated; the category of
cochain complexes is not, so that form is unavailable for the localization functor of a derived
category.  The content is the coherence
`CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app` of the commutation datum; what the
two spellings `F.op.obj X` and `op (F.obj X.unop)` of one object cost is that the rewriting has
to happen inside `conv`, which does not type-check the whole target. -/
noncomputable def opTriangleMapTriangleIso (T : Triangle C) :
    (triangleOpEquivalence D).functor.obj (op (F.mapTriangle.obj T)) ≅
      F.op.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      dsimp only [Pretriangulated.triangleOpEquivalence,
        Pretriangulated.TriangleOpEquivalence.functor, CategoryTheory.Functor.mapTriangle,
        Pretriangulated.Triangle.mk, Iso.refl_hom]
      refine Quiver.Hom.unop_inj ?_
      conv_lhs =>
        rw [CategoryTheory.Functor.map_id, Category.comp_id, unop_comp,
          opShiftFunctorEquivalence_counitIso_inv_app_unop (F.obj T.obj₁) 1,
          shiftFunctor_op_map_unop ((F.map T.mor₃ ≫
            (F.commShiftIso (1 : ℤ)).hom.app T.obj₁).op) 1, Quiver.Hom.unop_op]
        dsimp only [CategoryTheory.Functor.comp_obj,
          Pretriangulated.opShiftFunctorEquivalence_functor,
          Pretriangulated.opShiftFunctorEquivalence_inverse, CategoryTheory.Functor.op_obj,
          shiftFunctor_op_obj_unop, Opposite.unop_op]
        rw [CategoryTheory.Functor.map_comp]
      conv_rhs =>
        rw [Category.id_comp, unop_comp, op_commShiftIso_hom_app_unop,
          CategoryTheory.Functor.op_map, Quiver.Hom.unop_op, unop_comp,
          opShiftFunctorEquivalence_counitIso_inv_app_unop T.obj₁ 1,
          shiftFunctor_op_map_unop (T.mor₃.op) 1, Quiver.Hom.unop_op]
        dsimp only [CategoryTheory.Functor.comp_obj,
          Pretriangulated.opShiftFunctorEquivalence_functor,
          Pretriangulated.opShiftFunctorEquivalence_inverse, CategoryTheory.Functor.op_obj,
          shiftFunctor_op_obj_unop, Opposite.unop_op]
        rw [CategoryTheory.Functor.map_comp,
          CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app]
      simp only [Category.assoc]
      rw [CategoryTheory.Functor.commShiftIso_hom_naturality_assoc,
        Iso.inv_hom_id_app_assoc])

end OpFunctor

end Stacks.CategoryTheory.OppositeShift

namespace Stacks.Homology.DegreewiseSplitTriangle

open DerivedCategory CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The triangle of a degreewise split short complex is distinguished in the derived
category.**  Two rotations carry it to the mapping-cone triangle of its connecting morphism,
by `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`. -/
theorem Q_mapTriangle_triangleOfDegreewiseSplit_distinguished
    (S : ShortComplex (CochainComplex A ℤ))
    (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting) :
    Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ) ∈
      distTriang (DerivedCategory A) := by
  rw [Pretriangulated.rotate_distinguished_triangle,
    Pretriangulated.rotate_distinguished_triangle]
  refine Pretriangulated.isomorphic_distinguished _ ?_ _
    ((Pretriangulated.rotate _).mapIso (Q.mapTriangleRotateIso.app _) ≪≫
      Q.mapTriangleRotateIso.app _ ≪≫
      Q.mapTriangle.mapIso (triangleOfDegreewiseSplitRotateRotateIso S σ))
  exact (mem_distTriang_iff _).2 ⟨_, _, _, ⟨Iso.refl _⟩⟩

/-- **Every distinguished triangle of the derived category is the triangle of a degreewise
split short complex of complexes.**  The presentation is the one of
`CochainComplex.mappingCone.triangleRotateShortComplex` applied to the morphism whose mapping
cone triangle presents the inverse rotation. -/
theorem exists_iso_Q_mapTriangle_triangleOfDegreewiseSplit
    (T : Triangle (DerivedCategory A))
    (hT : T ∈ distTriang (DerivedCategory A)) :
    ∃ (S : ShortComplex (CochainComplex A ℤ))
      (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting),
      Nonempty (T ≅ Q.mapTriangle.obj (triangleOfDegreewiseSplit S σ)) := by
  obtain ⟨K, L, f, ⟨e⟩⟩ := (mem_distTriang_iff T.invRotate).mp
    (Pretriangulated.inv_rot_of_distTriang _ hT)
  exact ⟨_, mappingCone.triangleRotateShortComplexSplitting f,
    ⟨(Pretriangulated.invRotCompRot.app T).symm ≪≫ (Pretriangulated.rotate _).mapIso e ≪≫
      Q.mapTriangleRotateIso.app (mappingCone.triangle f) ≪≫
      Q.mapTriangle.mapIso (mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit f)⟩⟩

end Stacks.Homology.DegreewiseSplitTriangle

namespace AlgebraicGeometry.RingedSite

open Stacks.Cohomology.InternalHom


variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]

section Split

variable {A B M :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- Precomposition with a degreewise family of morphisms acts on the sections of the internal
Hom complex by precomposition on cochains. -/
lemma sectionsEquiv_precompDegreeMap (f : ∀ p, A.X p ⟶ B.X p) (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X B M).obj.X n).val.obj (op U)) (p q : ℤ) (hpq : p + n = q) :
    (((sheafHomComplex X A M).sectionsEquiv U n
        ((precompDegreeMap (sheafHomComplex X B M) (sheafHomComplex X A M) f n).val.app
          (op U) s)).v p q hpq) =
      (f p).over U ≫ ((sheafHomComplex X B M).sectionsEquiv U n s).v p q hpq := by
  rw [SheafHomComplex.sectionsEquiv_apply, SheafHomComplex.sectionsEquiv_apply]
  exact Cochain.congr_v
    (Stacks.Homology.componentIso_inv_hom_apply ((sheafHomComplex X A M).sectionsIso U) n _)
    p q hpq

/-- The projection description of `Stacks.Cohomology.InternalHom.precompDegreeMap`: its
composite with a projection of the product description of the term is precomposition in that
factor. -/
lemma homDegreeProjection_precompDegreeMap (f : ∀ p, A.X p ⟶ B.X p) (n q : ℤ) :
    precompDegreeMap (sheafHomComplex X B M) (sheafHomComplex X A M) f n ≫
        homDegreeProjection X A M n q =
      homDegreeProjection X B M n q ≫ internalHomPre X (f (-q)) := by
  ext U s
  rw [comp_val_app_apply, comp_val_app_apply, homDegreeProjection_val_app_apply,
    homDegreeProjection_val_app_apply]
  refine Eq.trans (congrArg SheafOfModules.Hom.val
    (sectionsEquiv_precompDegreeMap X f n U.unop s (-q) (n - q) (by omega))) ?_
  rfl

/-- **`AlgebraicGeometry.RingedSite.homDegreeFamilyMap` is precomposition on sections.**  The
two constructions of the morphism of degree-`n` terms induced by a degreewise family — one from
the product description of the term, one from the description of the sections as cochains of the
restrictions — agree, both being characterised by their composites with the projections. -/
lemma homDegreeFamilyMap_eq_precompDegreeMap (f : ∀ p, A.X p ⟶ B.X p) (n : ℤ) :
    homDegreeFamilyMap X f M n =
      precompDegreeMap (sheafHomComplex X B M) (sheafHomComplex X A M) f n :=
  homDegree_hom_ext X n _ _ fun q => by
    rw [homDegreeFamilyMap_homDegreeProjection, homDegreeProjection_precompDegreeMap]

/-- `homDegreeFamilyMap` acts on the sections of the internal Hom complex by precomposition on
cochains. -/
lemma sectionsEquiv_homDegreeFamilyMap (f : ∀ p, A.X p ⟶ B.X p) (n : ℤ) (U : X.C)
    (s : ((sheafHomComplex X B M).obj.X n).val.obj (op U)) (p q : ℤ) (hpq : p + n = q) :
    (((sheafHomComplex X A M).sectionsEquiv U n
        ((homDegreeFamilyMap X f M n).val.app (op U) s)).v p q hpq) =
      (f p).over U ≫ ((sheafHomComplex X B M).sectionsEquiv U n s).v p q hpq := by
  rw [homDegreeFamilyMap_eq_precompDegreeMap]
  exact sectionsEquiv_precompDegreeMap X f n U s p q hpq

variable (S : ShortComplex
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
  (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

end Split

section OpTriangle

open Pretriangulated.Opposite CochainComplex

attribute [local implicit_reducible] sheafHomComplexBifunctor

variable (S : ShortComplex
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ))
  (σ : ∀ n, (S.map (HomologicalComplex.eval _ _ n)).Splitting)

/-- The triangle of a degreewise split short complex of complexes of `O`-modules, read in the
opposite category.  Its third vertex is the first term of the short complex. -/
abbrev opTriangleOfDegreewiseSplit :
    Triangle
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)ᵒᵖ :=
  (triangleOpEquivalence (CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)).functor.obj
    (op (triangleOfDegreewiseSplit S σ))

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- **The connecting morphism of the opposite triangle, in each degree.**  Read through `unop`
it is the cocycle of the splittings, with no sign and no shift left over: the sign carried by
the shift of the opposite category cancels against the one carried by `Cochain.rightShift` in
`CochainComplex.homOfDegreewiseSplit`. -/
lemma opTriangleOfDegreewiseSplit_mor₃_unop :
    (opTriangleOfDegreewiseSplit X S σ).mor₃.unop =
      (homOfDegreewiseSplit S σ)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) 1 (-1)
          (by omega)).hom.app S.X₁ :=
  Stacks.CategoryTheory.OppositeShift.opTriangle_mor₃_unop (triangleOfDegreewiseSplit S σ)

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- **The connecting morphism of the opposite triangle, in each degree.**  Read through `unop`
it is the cocycle of the splittings, with no sign and no shift left over: the identification of
the double shift of the opposite category is the identity in each degree. -/
lemma homOfDegreewiseSplit_shift_f (p : ℤ) :
    ((homOfDegreewiseSplit S σ)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) 1 (-1)
          (by omega)).hom.app S.X₁).f p =
      (cocycleOfDegreewiseSplit S σ).1.v (p + (-1)) p (by omega) := by
  have hre : ∀ (A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (k a b b' : ℤ)
      (hb : b = b') (z : Cochain A B k) (hab : a + k = b) (hbb : B.X b = B.X b'),
      z.v a b hab ≫ eqToHom hbb = z.v a b' (by omega) := by
    intro A B k a b b' hb z hab hbb
    subst hb
    simp
  simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    HomologicalComplex.comp_f, shiftFunctor_map_f', homOfDegreewiseSplit_f,
    shiftFunctorAdd'_inv_app_f', shiftFunctorZero_hom_app_f, HomologicalComplex.XIsoOfEq,
    eqToIso.hom, eqToHom_trans]
  refine hre _ _ _ _ _ _ ?_ _ _ _
  omega

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- The cocycle of a degreewise split short complex, in each degree. -/
lemma cocycleOfDegreewiseSplit_v (p q : ℤ) (hpq : p + 1 = q) :
    (cocycleOfDegreewiseSplit S σ).1.v p q hpq =
      ((σ p).s : S.X₃.X p ⟶ S.X₂.X p) ≫ S.X₂.d p q ≫ ((σ q).r : S.X₂.X q ⟶ S.X₁.X q) :=
  rfl

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] in
/-- The cocycle of the internal Hom complexes of a degreewise split short complex, in each
degree: it is the differential of the middle internal Hom complex conjugated by the
precompositions. -/
lemma cocycle_internalHomShortComplex_v
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (a b : ℤ) (hab : a + 1 = b) :
    (cocycleOfDegreewiseSplit (internalHomShortComplex X S N)
        (internalHomTermwiseSplitting X S N σ)).1.v a b hab =
      homDegreeFamilyMap X (fun p => (σ p).r) N a ≫
        (sheafHomComplex X S.X₂ N).obj.d a b ≫
        homDegreeFamilyMap X (fun p => (σ p).s) N b :=
  rfl

/-- **The connecting morphism of the image triangle is the one of the image splittings.**  This
is the sign identity at the heart of the exactness of the internal Hom complex in its
contravariant variable: the sign `(-1)^(1-n)` carried by the source shift of a degree-`n`
cochain and the sign `(-1)^(n+1)` carried by the Hom-complex differential cancel, so that the
morphism `SheafHom(S₁, M) ⟶ SheafHom(S₃, M)⟦1⟧` which the chosen commutation datum produces
from the connecting morphism of `S` is exactly the one produced by the induced splittings. -/
lemma homMap_homOfDegreewiseSplit_shift
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X ((homOfDegreewiseSplit S σ)⟦(-1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId (CochainComplex
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) 1 (-1)
          (by omega)).hom.app S.X₁) (𝟙 N) =
      homOfDegreewiseSplit (internalHomShortComplex X S N) (internalHomTermwiseSplitting X S N σ) ≫
        (sheafHomSourceShiftIso' X (K := S.X₃) (M := N) (-1) 1 (by omega)).hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  rw [HomologicalComplex.comp_f, homMap_f, homOfDegreewiseSplit_f,
    sheafHomSourceShiftIso'_hom_f, cocycle_internalHomShortComplex_v X S σ N n (n + 1) rfl]
  refine sheafHom_ext X fun U s => ?_
  apply ((sheafHomComplex X (S.X₃⟦(-1 : ℤ)⟧) N).sectionsEquiv U n).injective
  rw [comp_val_app_apply, comp_val_app_apply, comp_val_app_apply,
    sectionsEquiv_sourceShiftHom, sectionsEquiv_homMapHom]
  refine Cochain.ext _ _ fun p q hpq => ?_
  have over_comp {A B C : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
      (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).over U = f.over U ≫ g.over U := by
    ext V x
    rfl
  have over_zero {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} :
      (0 : A ⟶ B).over U = 0 := by
    ext V x
    rfl
  have hoid : SheafOfModules.Hom.over (𝟙 (N.X q)) U = 𝟙 ((restrictComplex X N U).X q) := by
    ext V x
    rfl
  have hsr : SheafOfModules.Hom.over
        ((σ (p + (-1))).s : S.X₃.X (p + (-1)) ⟶ S.X₂.X (p + (-1))) U ≫
      SheafOfModules.Hom.over
        ((σ (p + (-1))).r : S.X₂.X (p + (-1)) ⟶ S.X₁.X (p + (-1))) U = 0 := by
    rw [← over_comp, show ((σ (p + (-1))).s : S.X₃.X (p + (-1)) ⟶ S.X₂.X (p + (-1))) ≫
      ((σ (p + (-1))).r : S.X₂.X (p + (-1)) ⟶ S.X₁.X (p + (-1))) = 0 from (σ (p + (-1))).s_r,
      over_zero]
  rw [cochainConj_v, HomologicalComplex.id_f, hoid, Category.comp_id, cochainSourceShift_v,
    sectionsEquiv_homDegreeFamilyMap, SheafHomComplex.sectionsEquiv_d,
    δ_v n (n + 1) rfl _ (p + (-1)) q (by omega) (q - 1) p rfl (by omega),
    Preadditive.comp_add, sectionsEquiv_homDegreeFamilyMap, sectionsEquiv_homDegreeFamilyMap]
  simp only [Category.assoc]
  rw [reassoc_of% hsr, Limits.zero_comp, zero_add, Linear.comp_units_smul, smul_smul,
    ← Int.negOnePow_add, show -1 * n + -1 * (-1 - 1) / 2 + (n + 1) = 2 by omega,
    Int.negOnePow_even 2 even_two, one_smul, homOfDegreewiseSplit_shift_f,
    cocycleOfDegreewiseSplit_v, over_comp, over_comp,
    show (restrictComplex X S.X₂ U).d (p + (-1)) p =
      SheafOfModules.Hom.over (S.X₂.d (p + (-1)) p) U from rfl]
  simp only [Category.assoc]

/-- **The connecting morphism of the image of the opposite triangle.**  Combining
`AlgebraicGeometry.RingedSite.opTriangleOfDegreewiseSplit_mor₃_unop` with the sign identity. -/
lemma homMap_opTriangleOfDegreewiseSplit_mor₃
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    homMap X ((opTriangleOfDegreewiseSplit X S σ).mor₃.unop) (𝟙 N) =
      homOfDegreewiseSplit (internalHomShortComplex X S N) (internalHomTermwiseSplitting X S N σ) ≫
        (sheafHomSourceShiftIso' X (K := S.X₃) (M := N) (-1) 1 (by omega)).hom :=
  (congrArg (fun k => homMap X k (𝟙 N))
    (opTriangleOfDegreewiseSplit_mor₃_unop X S σ)).trans
    (homMap_homOfDegreewiseSplit_shift X S σ N)

/-- The connecting morphism of the image under `SheafHom(-, M)` of the opposite triangle of a
degreewise split short complex, in the form the third square of a triangle isomorphism asks
for. -/
lemma flip_map_opTriangle_mor₃_comp_commShiftIso
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor X).flip.obj N).map
          (opTriangleOfDegreewiseSplit X S σ).mor₃ ≫
        (((sheafHomComplexBifunctor X).flip.obj N).commShiftIso (1 : ℤ)).hom.app (op S.X₃) =
      homOfDegreewiseSplit (internalHomShortComplex X S N)
          (internalHomTermwiseSplitting X S N σ) := by
  have he : (((sheafHomComplexBifunctor X).flip.obj N).commShiftIso (1 : ℤ)).inv.app
        (op S.X₃) =
      (sheafHomSourceShiftIso' X (K := S.X₃) (M := N) (-1) 1 (by omega)).hom :=
    sheafHomOpCommShiftIso_inv_app X N 1 (op S.X₃)
  have key : ((sheafHomComplexBifunctor X).flip.obj N).map
        (opTriangleOfDegreewiseSplit X S σ).mor₃ =
      homOfDegreewiseSplit (internalHomShortComplex X S N) (internalHomTermwiseSplitting X S N σ) ≫
        (((sheafHomComplexBifunctor X).flip.obj N).commShiftIso (1 : ℤ)).inv.app
          (op S.X₃) := by
    rw [he]
    exact homMap_opTriangleOfDegreewiseSplit_mor₃ X S σ N
  refine Eq.trans (congrArg (fun k => k ≫
    (((sheafHomComplexBifunctor X).flip.obj N).commShiftIso (1 : ℤ)).hom.app (op S.X₃)) key) ?_
  refine Eq.trans (Category.assoc _ _ _) (Eq.trans (congrArg (fun k =>
      homOfDegreewiseSplit (internalHomShortComplex X S N)
        (internalHomTermwiseSplitting X S N σ) ≫ k)
    (Iso.inv_hom_id_app (((sheafHomComplexBifunctor X).flip.obj N).commShiftIso (1 : ℤ))
      (op S.X₃))) (Category.comp_id _))

/-- **The internal Hom complex carries the opposite triangle of a degreewise split short
complex to the triangle of the induced splittings.**  The three vertices and the first two
morphisms agree on the nose; the third is the sign identity
`AlgebraicGeometry.RingedSite.homMap_homOfDegreewiseSplit_shift`. -/
noncomputable def mapTriangleOpTriangleOfDegreewiseSplitIso
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((sheafHomComplexBifunctor X).flip.obj N).mapTriangle.obj
        (opTriangleOfDegreewiseSplit X S σ) ≅
      triangleOfDegreewiseSplit (internalHomShortComplex X S N)
        (internalHomTermwiseSplitting X S N σ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (by
    simp only [Iso.refl_hom]
    exact flip_map_opTriangle_mor₃_comp_commShiftIso X S σ N)

end OpTriangle

section Derived

open Pretriangulated Pretriangulated.Opposite CochainComplex
open Stacks.Homology.DegreewiseSplitTriangle

attribute [local instance] HasDerivedCategory.standard derivedSheafHomFlipLifting
  derivedSheafHomModelFlipCommShift

/-- **The derived internal Hom into the class of a complex is a triangulated functor of its
dualized variable.**

Every distinguished triangle of `D(O)ᵒᵖ` is the opposite of one of `D(O)`, and every
distinguished triangle of `D(O)` is the image of the triangle of a degreewise split short
complex of complexes; so the claim is carried by the chain-level identification
`AlgebraicGeometry.RingedSite.mapTriangleOpTriangleOfDegreewiseSplitIso` along the localization
of the dualized variable. -/
theorem isTriangulated_derivedSheafHomFlip_of_Q
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    letI := derivedSheafHomFlipCommShiftOfQ X N
    ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj N)).IsTriangulated := by
  let := derivedSheafHomFlipCommShiftOfQ X N
  refine ⟨fun T hT => ?_⟩
  obtain ⟨T₀, hT₀, ⟨eT⟩⟩ := (Pretriangulated.mem_distTriang_op_iff' T).1 hT
  obtain ⟨S, σ, ⟨e₀⟩⟩ := exists_iso_Q_mapTriangle_triangleOfDegreewiseSplit T₀ hT₀
  refine Pretriangulated.isomorphic_distinguished _
    (Q_mapTriangle_triangleOfDegreewiseSplit_distinguished
      (internalHomShortComplex X S ((kInjectiveResolution X).obj N))
      (internalHomTermwiseSplitting X S ((kInjectiveResolution X).obj N) σ)) _ ?_
  exact ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj N)).mapTriangle.mapIso
      (eT ≪≫ (Pretriangulated.triangleOpEquivalence _).functor.mapIso (Iso.op e₀.symm) ≪≫
        Stacks.CategoryTheory.OppositeShift.opTriangleMapTriangleIso DerivedCategory.Q
          (triangleOfDegreewiseSplit S σ)) ≪≫
    ((CategoryTheory.Functor.mapTriangleCompIso DerivedCategory.Q.op
        ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj N))).app _).symm ≪≫
    (CategoryTheory.Functor.mapTriangleIso (Localization.Lifting.iso DerivedCategory.Q.op
        (HomologicalComplex.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)).op
        ((derivedSheafHomModel X).flip.obj N)
        ((derivedSheafHomBifunctor X).flip.obj (DerivedCategory.Q.obj N)))).app _ ≪≫
    (let := CategoryTheory.Functor.CommShift.ofIso_compatibility
        (derivedSheafHomModelFlipIso X N) ℤ;
      (CategoryTheory.Functor.mapTriangleIso (derivedSheafHomModelFlipIso X N)).symm.app _) ≪≫
    (CategoryTheory.Functor.mapTriangleCompIso
      ((sheafHomComplexBifunctor X).flip.obj ((kInjectiveResolution X).obj N))
      DerivedCategory.Q).app _ ≪≫
    DerivedCategory.Q.mapTriangle.mapIso
      (mapTriangleOpTriangleOfDegreewiseSplitIso X S σ ((kInjectiveResolution X).obj N))

/-- **The derived internal Hom into a fixed object is a triangulated functor of its dualized
variable.**  This is `AlgebraicGeometry.RingedSite.isTriangulated_derivedSheafHomFlip_of_Q`
transported along the isomorphism of the fixed object with the class of a complex, which is the
same isomorphism along which
`AlgebraicGeometry.RingedSite.derivedSheafHomFlipCommShift` transports the commutation datum, so
`CategoryTheory.Functor.CommShift.ofIso_compatibility` makes it compatible with the shift. -/
instance derivedSheafHomFlipIsTriangulated
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedSheafHomBifunctor X).flip.obj M).IsTriangulated := by
  let := derivedSheafHomFlipCommShiftOfQ X (DerivedCategory.Q.objPreimage M)
  let : ((derivedSheafHomBifunctor X).flip.obj
      (DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage M))).IsTriangulated :=
    isTriangulated_derivedSheafHomFlip_of_Q X (DerivedCategory.Q.objPreimage M)
  let := CategoryTheory.Functor.CommShift.ofIso
    ((derivedSheafHomBifunctor X).flip.mapIso (DerivedCategory.Q.objObjPreimageIso M)) ℤ
  let := CategoryTheory.Functor.CommShift.ofIso_compatibility
    ((derivedSheafHomBifunctor X).flip.mapIso (DerivedCategory.Q.objObjPreimageIso M)) ℤ
  exact CategoryTheory.Functor.isTriangulated_of_iso
    ((derivedSheafHomBifunctor X).flip.mapIso (DerivedCategory.Q.objObjPreimageIso M))

end Derived

end AlgebraicGeometry.RingedSite

end

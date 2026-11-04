module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolution

/-!
# The Čech complex of a split family is exact in positive degrees

A family of morphisms `{U_i → X}` is *split* when one of its members admits a section, i.e.
when there is `s : X ⟶ U_{i_0}` with `s ≫ (U_{i_0} → X) = 𝟙 X`.  For such a family the Čech
complex of **any** presheaf is exact in every positive degree: the augmented Čech object is
contractible, the section providing an extra degeneracy.

This is *only* the split case: a general covering family has no section; see the
implementation notes below.

## Main definitions

* `Stacks.CechSite.familyFormalCoproduct`: the formal coproduct of the members of a family,
  the object whose Mathlib Čech object is the one this file's complexes are built from.
* `Stacks.CechSite.cechOpIso`: the identification of the opposite of the Čech **cochain**
  complex with the alternating **face** map complex, in the opposite category, of the
  corresponding simplicial object.

## Main results

* `Stacks.CechSite.exactAt_cochainComplexFunctor_of_sectionFromTerminal`: for
  `U : FormalCoproduct C` and a terminal `T`, a morphism `T ⟶ U.obj i₀` makes Mathlib's
  `CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor U.cech` exact in every positive
  degree, at every presheaf.
* `Stacks.CechSite.exactAt_cechComplex_of_section`: the same for the Čech complex
  `Stacks.CechSite.cechComplex` of a `CategoryTheory.PreZeroHypercover` one of whose members
  admits a section.
* `Stacks.CechSite.SheafLevel.complexFunctor_obj_eq`: the sheaf-level Čech complex is the Čech
  complex of the Čech diagram.

## Implementation notes

Two facts make this short.

First, `Stacks.CechSite.cechSimplicialObject E` and Mathlib's
`CategoryTheory.Limits.FormalCoproduct.cech` of
`Stacks.CechSite.familyFormalCoproduct E` are *equal by `rfl`* once `Over X` has finite
products — see `Stacks.CechSite.cechSimplicialObject_eq`.  The two definitions agree field by
field: `FormalCoproduct.power` has `I := α → U.I` and `obj i := ∏ᶜ (U.obj ∘ i)`, which for
`U.obj = fun i ↦ Over.mk (E.f i)` is `Stacks.CechSite.cechFormalCoproduct`'s
`obj i := ∏ᶜ (fun a ↦ Over.mk (E.f (i a)))`, and `FormalCoproduct.mapPower` agrees with
`Stacks.CechSite.cechFormalCoproductMap`.  So Mathlib's
`CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech` applies to this file's complexes
directly, with no comparison isomorphism to build.  The finite-products hypothesis is what
`FormalCoproduct.power` and `FormalCoproduct.cech` ask for, and it is *strictly stronger* than
what `Stacks.CechSite.cechComplex` itself needs; the statements below therefore use the
`HasProduct` instances that `HasFiniteProducts (Over X)` derives, and do not apply verbatim to
a complex built with a competing choice of those instances.

Second, `extraDegeneracyCech` produces a `SimplicialObject.Augmented.ExtraDegeneracy`, whose
only homological consequence in Mathlib is `ExtraDegeneracy.homotopyEquiv`, stated for the
alternating **face** map complex of a **simplicial** object; whereas the Čech complex is the
alternating **coface** map complex of a **cosimplicial** object, and Mathlib proves nothing
about the latter.  The bridge taken here is the opposite category: the contravariant evaluation
`FormalCoproduct.evalOp` is turned into a covariant functor into `Aᵒᵖ` by
`CategoryTheory.Functor.rightOp`, `ExtraDegeneracy.map` transports the extra degeneracy along
it, `CategoryTheory.SimplicialSiteSituation.exactAt_of_extraDegeneracy` gives exactness there,
and `CategoryTheory.HomologicalComplex.exactAt_op_iff` brings it back.  What that needs is
`Stacks.CechSite.cechOpIso`, and its two sides agree degreewise on the nose — only the
differentials need an argument, and that argument is `Stacks.CechSite.cechObjD_op`: the coface
maps of the cosimplicial object and the face maps of the simplicial object in `Aᵒᵖ` are
opposite to each other by `rfl`, so the two alternating sums correspond under
`CategoryTheory.op_sum` and `CategoryTheory.op_zsmul`.

**The statement at the sheaf-level complex** is
`Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_section`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/SheafLevelSplitFamilyExactness.lean`, and not
here, because it cannot be *derived* here inside one declaration.  `complexFunctor_obj_eq`
identifies `Stacks.CechSite.SheafLevel.complexFunctor` with `Stacks.CechSite.cechComplex` of
the Čech diagram, so `exactAt_cechComplex_of_section` is the right statement for it; but
`exactAt_cechComplex_of_section` is stated under `[Abelian A]`, so the
`CategoryTheory.Preadditive` instance in its `cechComplex` is `Abelian.toPreadditive`, whereas
`complexFunctor` carries `CategoryTheory.SheafOfModules.instPreadditive`.  The two are
definitionally equal — the `Abelian` instance of sheaves of modules is built by
`CategoryTheory.abelianOfAdjunction` from that very `Preadditive` — but unifying the two
complexes field by field with the instances unfolded inside each field exceeds the
per-declaration elaboration budget.  The other file splits that cost across declarations.

**The general covering family.**  Nothing below applies to a covering family that admits no
section.  The exactness of the Čech complex of such a family over an object `W` mapping to a
member of the family is
`Stacks.CechObjectFamily.exactAt_cechComplexFunctor_prodRestriction_of_hom` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/BaseChangedFamilyComplexExactness.lean`,
which base-changes the coefficients instead of comparing complexes.  For a non-terminal `X`
the sheaf-level complex is not a resolution at all.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AQ](https://stacks.math.columbia.edu/tag/03AQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology SimplicialObject
open scoped Simplicial

universe w v u v' u'

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [Abelian A] [HasFiniteProducts C]
  (U : FormalCoproduct.{w} C) (P : Cᵒᵖ ⥤ A)

/-- The evaluation of a presheaf on formal coproducts, read as a covariant functor into the
opposite category.  This is the functor along which an extra degeneracy of the Čech object is
transported. -/
noncomputable abbrev evalOpRightOp : FormalCoproduct.{w} C ⥤ Aᵒᵖ :=
  ((FormalCoproduct.evalOp.{w} C A).obj P).rightOp

/-- The simplicial object in `Aᵒᵖ` obtained by evaluating `P` on the Čech object of `U`. -/
noncomputable abbrev cechSimplicialOp : SimplicialObject Aᵒᵖ :=
  U.cech ⋙ evalOpRightOp P

/-- The cosimplicial object in `A` whose alternating coface map complex is the Čech complex. -/
noncomputable abbrev cechCosimplicial : CosimplicialObject A :=
  (FormalCoproduct.cosimplicialObjectFunctor U.cech).obj P

/-- **The alternating sums correspond.**  The face differential of the simplicial object in
`Aᵒᵖ` is opposite to the coface differential of the cosimplicial object in `A`, because the
individual coface maps are opposite to the individual face maps on the nose. -/
theorem cechObjD_op (n : ℕ) :
    AlternatingFaceMapComplex.objD (cechSimplicialOp U P) n =
      (AlternatingCofaceMapComplex.objD (cechCosimplicial U P) n).op := by
  rw [AlternatingFaceMapComplex.objD, AlternatingCofaceMapComplex.objD, op_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [op_zsmul]
  rfl

/-- **The Čech cochain complex, opposed, is an alternating face map complex.**  Its degree-`n`
terms agree with those of the alternating face map complex of
`Stacks.CechSite.cechSimplicialOp` by definition; the differentials agree by
`Stacks.CechSite.cechObjD_op`. -/
noncomputable def cechOpIso :
    ((FormalCoproduct.cochainComplexFunctor U.cech).obj P).op ≅
      (alternatingFaceMapComplex Aᵒᵖ).obj (cechSimplicialOp U P) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun i j hij ↦ by
    obtain rfl : j + 1 = i := hij
    have hd : ((FormalCoproduct.cochainComplexFunctor U.cech).obj P).d j (j + 1) =
        AlternatingCofaceMapComplex.objD (cechCosimplicial U P) j :=
      Stacks.CategoryTheory.CechComplex.alternatingCofaceMapComplex_obj_d
        (cechCosimplicial U P) j
    exact (Category.id_comp _).trans
      ((ChainComplex.of_d (fun n ↦ (cechSimplicialOp U P).obj (op (⦋n⦌ : SimplexCategory)))
          (AlternatingFaceMapComplex.objD (cechSimplicialOp U P)) j).trans
        ((cechObjD_op U P j).trans
          ((congrArg Quiver.Hom.op hd.symm).trans (Category.comp_id _).symm))))

/-- **The Čech complex of a split formal coproduct is exact in positive degrees.**  If `T` is
terminal and some component `U.obj i₀` admits a morphism from `T`, then the Čech cochain
complex of `U` at any presheaf `P` is exact in every degree `n > 0`.

The hypothesis is the one of `CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech`: for
`C = Over X` and `U` the formal coproduct of a family `{U_i → X}` it says that `U_{i_0} → X`
admits a section, i.e. that the family is *split*.  This is **not** the case of a general
covering family. -/
theorem exactAt_cochainComplexFunctor_of_sectionFromTerminal {T : C} (hT : IsTerminal T)
    {i₀ : U.I} (d : T ⟶ U.obj i₀) (n : ℕ) (hn : 0 < n) :
    ((FormalCoproduct.cochainComplexFunctor U.cech).obj P).ExactAt n := by
  rw [← HomologicalComplex.exactAt_op_iff]
  exact (CategoryTheory.SimplicialSiteSituation.exactAt_of_extraDegeneracy _
    ((U.extraDegeneracyCech hT d).map (evalOpRightOp P)) n hn).of_iso (cechOpIso U P).symm

section Family

variable {X : C} (E : PreZeroHypercover.{w} X) [HasFiniteProducts (Over X)]

/-- **The formal coproduct of the members of a family of morphisms with fixed target**, taken
in the slice `Over X`.  Its Mathlib Čech object is the simplicial object underlying
`Stacks.CechSite.cechComplex`. -/
noncomputable abbrev familyFormalCoproduct : FormalCoproduct.{w} (Over X) :=
  FormalCoproduct.mk E.I₀ (fun i ↦ Over.mk (E.f i))

omit [HasFiniteProducts C] in
/-- The simplicial object of iterated fibre products built in
`Stacks.CechSite.cechSimplicialObject` **is** Mathlib's Čech object of
`Stacks.CechSite.familyFormalCoproduct`: the index types, the chosen products and the
reindexing maps agree field by field. -/
theorem cechSimplicialObject_eq :
    cechSimplicialObject E = (familyFormalCoproduct E).cech := rfl

omit [HasFiniteProducts C] in
/-- **The Čech complex of a family one of whose members admits a section is exact in positive
degrees**, at every presheaf with values in an abelian category with products.

A *section* of the `i₀`-th member is `s : X ⟶ E.X i₀` with `s ≫ E.f i₀ = 𝟙 X`; it makes the
augmented Čech object contractible.  A general covering family has no such section, so this
does **not** prove that the Čech complex of a covering is a resolution. -/
theorem exactAt_cechComplex_of_section (P : Cᵒᵖ ⥤ A) {i₀ : E.I₀} (s : X ⟶ E.X i₀)
    (hs : s ≫ E.f i₀ = 𝟙 X) (n : ℕ) (hn : 0 < n) :
    (cechComplex E P).ExactAt n :=
  exactAt_cochainComplexFunctor_of_sectionFromTerminal (familyFormalCoproduct E)
    ((Over.forget X).op ⋙ P) Over.mkIdTerminal (Over.homMk s hs) n hn

end Family

namespace SheafLevel

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasBinaryProducts C]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasProducts.{w} (SheafOfModules.{w} R)]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {X : C} (E : PreZeroHypercover.{w} X) [HasFiniteProducts (Over X)]

omit [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The sheaf-level Čech complex is the Čech complex of the Čech diagram, as a presheaf with
values in the sheaves of modules. -/
theorem complexFunctor_obj_eq (F : SheafOfModules.{w} R) :
    (Stacks.CechSite.SheafLevel.complexFunctor R E).obj F =
      cechComplex E (Stacks.CechSite.SheafLevel.diagramObj R F) := rfl

end SheafLevel

end Stacks.CechSite

end

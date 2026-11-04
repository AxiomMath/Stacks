module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Injective
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexOfAFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexIsAResolution
public import StacksFrontier.CategoryTheory.Sites.IntegralCechHomology

/-!
# The Čech complex of a family of morphisms, and its vanishing for injectives

Let `E` be a family of morphisms `E.f j : E.X j ⟶ X` in a category `C`, presented as a
`CategoryTheory.PreZeroHypercover`, whose finite nonempty fibre products over `X` exist. For an
additive presheaf `F` the *Čech complex* of `E` with coefficients in `F` is the cochain complex
whose degree-`n` term is the product, over tuples `i : Fin (n + 1) → E.I₀`, of the value of `F`
on the fibre product of the `E.X (i p)` over `X`, with the alternating sum of the coface maps as
differential; its cohomology objects are the *Čech cohomology* objects of `F` for `E`.

That complex is `Stacks.CechSite.cechComplex`, its cohomology objects are
`Stacks.CechSite.cechCohomology`, and `Stacks.CechSite.homIntegralCechComplexIso` identifies the
Čech complex with the complex of maps out of the integral Čech complex (Tag 03AS). For an
injective abelian presheaf the positive-degree Čech cohomology vanishes, by the vanishing of the
positive-degree homology of the integral Čech complex
(`Stacks.CechSite.integralCechComplex_homology_isZero`, Tag 03AT) together with the exactness of
`Hom(-, I)`. This is the presheaf-level core of Tag 03AW, which is stated for an injective sheaf
on a site and also identifies the degree-zero cohomology.

## Main definitions

* `Stacks.IntegralCech.uliftCechComplexIso`: lifting the coefficient universe of a presheaf
  commutes with forming its Čech complex.

## Main results

* `Stacks.IntegralCech.isZero_cechCohomology_of_injective`: the positive-degree Čech
  cohomology of an injective abelian presheaf vanishes.

## References

* [The Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [The Stacks Project, Tag 03AS](https://stacks.math.columbia.edu/tag/03AS)
* [The Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [The Stacks Project, Tag 03AW](https://stacks.math.columbia.edu/tag/03AW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open AlgebraicTopology Opposite

section Injectives

universe w v u a

namespace Stacks.IntegralCech

open Stacks.CechSite

/-- Lifting the coefficient universe of an abelian presheaf commutes with forming its Čech
complex: the universe lift of the Čech complex of `I` is the Čech complex of the lifted
presheaf. -/
noncomputable def uliftCechComplexIso
    {C : Type u} [Category.{max v w} C] {X : C} (E : PreZeroHypercover.{w} X)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (I : Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) :
    ((AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex _).obj
      (Stacks.CechSite.cechComplex E I)) ≅
        Stacks.CechSite.cechComplex E (I ⋙ AddCommGrpCat.uliftFunctor.{u}) := by
  let L := AddCommGrpCat.uliftFunctor.{u, max v w}
  let T : CosimplicialObject AddCommGrpCat.{max v w} :=
    (Stacks.CechSite.cechSimplicialObject E).rightOp ⋙
      (FormalCoproduct.evalOp.{w} (Over X) AddCommGrpCat.{max v w}).obj
        ((Over.forget X).op ⋙ I)
  let T' : CosimplicialObject AddCommGrpCat.{max u v w} :=
    (Stacks.CechSite.cechSimplicialObject E).rightOp ⋙
      (FormalCoproduct.evalOp.{w} (Over X) AddCommGrpCat.{max u v w}).obj
        ((Over.forget X).op ⋙ I ⋙ L)
  let P := (Over.forget X).op ⋙ I
  let e₀ : (FormalCoproduct.evalOp.{w} (Over X) AddCommGrpCat.{max v w}).obj P ⋙ L ≅
      (FormalCoproduct.evalOp.{w} (Over X) AddCommGrpCat.{max u v w}).obj (P ⋙ L) :=
    NatIso.ofComponents (fun Y ↦ PreservesProduct.iso L (fun i ↦ P.obj (op (Y.unop.obj i))))
      (by
        intro Y Z f
        apply Pi.hom_ext
        intro i
        dsimp only [Functor.comp_map, Functor.comp_obj, FormalCoproduct.evalOp]
        simp only [PreservesProduct.iso_hom, Category.assoc, piComparison_comp_π,
          Pi.lift_π, piComparison_comp_π_assoc, ← L.map_comp])
  let e : T ⋙ L ≅ T' := Functor.isoWhiskerLeft
    (Stacks.CechSite.cechSimplicialObject E).rightOp e₀
  let e' : (L.mapHomologicalComplex _).obj (Stacks.CechSite.cechComplex E I) ≅
      (AlgebraicTopology.alternatingCofaceMapComplex _).obj (T ⋙ L) := by
    refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _) ?_
    intro i j hij
    obtain rfl : i + 1 = j := hij
    change 𝟙 _ ≫ _ = L.map _ ≫ 𝟙 _
    simp only [Category.comp_id]
    symm
    change L.map ((AlgebraicTopology.AlternatingCofaceMapComplex.obj T).d i (i + 1)) =
      (AlgebraicTopology.AlternatingCofaceMapComplex.obj (T ⋙ L)).d i (i + 1)
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of_d,
      AlgebraicTopology.AlternatingCofaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul]
    rfl
  exact e' ≪≫ (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso e

/-- The positive-degree Čech cohomology of an injective abelian presheaf vanishes. This is the
presheaf-level core of Tag 03AW; it rests on the exactness of the integral Čech complex in
positive degrees (Tag 03AT). -/
lemma isZero_cechCohomology_of_injective
    {C : Type u} [Category.{max v w} C] {X : C} (E : PreZeroHypercover.{w} X)
    [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (I : Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (Stacks.CechSite.cechCohomology E I p) := by
  let K := Stacks.CechSite.integralCechComplex.{w, max v w, u, v} E
  have hK : K.ExactAt p := (HomologicalComplex.exactAt_iff_isZero_homology _ p).2
    (Stacks.CechSite.integralCechComplex_homology_isZero.{w, max v w, u, v} E p hp)
  have : (preadditiveYoneda.obj I).PreservesEpimorphisms :=
    (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj I).1 inferInstance
  have : (preadditiveYoneda.obj I).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hHom : ((homComplexFunctor K).obj I).ExactAt p :=
    ShortComplex.Exact.map hK.op (preadditiveYoneda.obj I)
  have hLift := hHom.of_iso ((homIntegralCechComplexIso.{w, max v w, u, v} E).app I)
  have hMap := hLift.of_iso (uliftCechComplexIso E I).symm
  have hExact : (Stacks.CechSite.cechComplex E I).ExactAt p :=
    ((Stacks.CechSite.cechComplex E I).sc p |>.exact_map_iff_of_faithful
      AddCommGrpCat.uliftFunctor).1 hMap
  exact hExact.isZero_homology

end Stacks.IntegralCech
end Injectives

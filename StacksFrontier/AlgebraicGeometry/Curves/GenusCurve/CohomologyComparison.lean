module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# The two presentations of the cohomology of a module on a scheme over a field

For a scheme `X` over a field `k`, the cohomology of a module on `X` has two presentations in
this repository: `AlgebraicGeometry.structureSheafCohomology`, the right derived functor of
global sections taken after pushforward to `Spec k`, which is what the genus of Stacks 0BY7 is
defined from; and `AlgebraicGeometry.cohomologyOverField`, the right derived functor of
evaluation on `X` with scalars restricted along the structure morphism, which is what the
finiteness and Euler-characteristic results are stated in.  This file identifies them, so that
facts proved about one reach the other.

## Main definitions

* `AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`: the cohomology of the
  structure sheaf that defines the genus is the cohomology over the ground field.

## Main results

* `AlgebraicGeometry.comp_appTop_hom_eq_comp_appLE_hom'`: the two spellings of the ring map
  making the global functions on `X` an algebra over the ground field agree.

## Implementation notes

Global sections after pushforward along `f` *is* evaluation on `X` followed by restriction of
scalars along `f`, so the two differ only by the order in which the restriction of scalars and
the right derived functor are taken; and restriction of scalars preserves homology, so it
commutes with passing to right derived functors.  That last step is
`rightDerivedCompObjIso` below, which has no counterpart in the library: the two existing
composition comparisons for right derived functors,
`Stacks.RightDerivedComp.objIso` and `Stacks.DerivedIndexing.rightDerivedPlusCompIso`, both put
their hypotheses on the *left* factor, whereas here the hypothesis is that the right factor
preserves homology.

The remaining discrepancy is a spelling one: `structureSheafCohomology` restricts scalars along
`Scheme.Hom.appTop` and `cohomologyOverField` along `Scheme.Hom.appLE ⊤ ⊤`.  These are equal by
`AlgebraicGeometry.Scheme.Hom.app_eq_appLE`, and `ModuleCat.restrictScalarsCongr` transports
along the equality.

The declarations are split further than the mathematics requires.  Elaborated as a single term
the comparison needs about 226 000 heartbeats and exceeds the default budget; splitting off the
`appTop`-versus-`appLE` transport and the derived-functor comparison brings the heaviest
declaration to about 130 000.  That is also why this file is not `@[expose]`: an exposed public
definition may not mention the private plumbing.

The two spellings of the coefficient ring — the `RingCat` carrier
`X.ringCatSheaf.obj.obj (op ⊤)` on the evaluation side and the `CommRingCat` carrier
`Γ(X, ⊤)` on the restriction side — are definitionally but not syntactically equal, which is
why the additivity and homology-preservation arguments are passed positionally rather than
found by instance search.

## References

* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `T` preserves homology, the right derived functors of `G ⋙ T` are obtained by applying
`T` to the right derived functors of `G`: homology of the complex obtained from an injective
resolution may be taken before or after applying `T`. -/
private def rightDerivedCompObjIso {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]
    (G : C ⥤ D) [G.Additive] (T : D ⥤ E) [T.Additive] [T.PreservesHomology]
    (A : C) (n : ℕ) :
    ((G ⋙ T).rightDerived n).obj A ≅ T.obj ((G.rightDerived n).obj A) := by
  let I := injectiveResolution A
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  exact I.isoRightDerivedObj (G ⋙ T) n ≪≫
    (HomologicalComplex.homologyFunctor E _ n).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ T)) _).app I.cocomplex).symm ≪≫
    (K.sc n).mapHomologyIso T ≪≫
    T.mapIso (I.isoRightDerivedObj G n).symm

/-- The two spellings of the ring map making the global functions on `X` an algebra over the
ground field, through `Scheme.Hom.appTop` and through `Scheme.Hom.appLE` at the top opens,
agree. -/
private theorem comp_appTop_hom_eq_comp_appLE_hom (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom := by
  have happ : f.appTop = f.appLE ⊤ ⊤ (by simp) := by
    simpa [Scheme.Hom.appTop] using
      (Scheme.Hom.app_eq_appLE (f := f) (U := (⊤ : (Spec (.of k)).Opens)))
  exact congrArg (fun g => ((Scheme.ΓSpecIso (.of k)).inv ≫ g).hom) happ

/-- The two spellings of the ring map making the global functions on `X` an algebra over the
ground field, through `Scheme.Hom.appTop` and through `Scheme.Hom.appLE` at the top opens,
agree. -/
public theorem comp_appTop_hom_eq_comp_appLE_hom' (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom :=
  comp_appTop_hom_eq_comp_appLE_hom k f

/-- The cohomology of the structure sheaf that defines the genus, written as the cohomology of
evaluation on `X` with scalars restricted along `Scheme.Hom.appTop`. -/
private def structureSheafCohomologyIsoRestrictScalarsRightDerived (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ) :
    structureSheafCohomology f n ≅
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        (((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n).obj
          (SheafOfModules.unit X.ringCatSheaf)) := by
  let E := SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))
  let R := ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hEAdd : E.Additive := evaluationAdditive X
  have hRAdd : R.Additive := inferInstance
  have hRPres : R.PreservesHomology := inferInstance
  exact @rightDerivedCompObjIso _ _ _ _ _ _ _ _ _ _ E hEAdd R hRAdd hRPres
    (SheafOfModules.unit X.ringCatSheaf) n

/-- **The cohomology of the structure sheaf that defines the genus is the cohomology over the
ground field.** -/
public def structureSheafCohomologyIsoCohomologyOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (n : ℕ) :
    structureSheafCohomology f n ≅
      cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n :=
  structureSheafCohomologyIsoRestrictScalarsRightDerived k f n ≪≫
    (ModuleCat.restrictScalarsCongr (comp_appTop_hom_eq_comp_appLE_hom k f)).app _

end AlgebraicGeometry

end

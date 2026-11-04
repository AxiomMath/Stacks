module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedCochainComplex
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.EvaluationAcyclic
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctorAssembly
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomVariant

/-!
# Conservativity of the forgetful functor `D(E, d) ⥤ D(Ab)`, and what it reflects

Let `C` be a differential graded category over a commutative ring `R`, let `K` be an object of
it, let `E = C(K, K)` be the one-object differential graded subcategory on `K` and let
`U = ` `DGCategory.endDerivedForget` be the forgetful functor `D(E) ⥤ D(ModuleCat R)`. This file
proves that `U` reflects isomorphisms, and settles what that does and does not buy for the
hypothesis `hU` of `CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor` — the step
the proof of [Stacks, Tag 09LK] passes over.

## Conservativity

`U` is evaluation at the unique object of `E`
(`DGCategory.RightModule.derivedEvaluationForget`), descended through the Verdier quotient of
`K(Mod^dg(E))` by the acyclic modules. A morphism of `D(E)` is a left fraction `f / s` with `s`
inverted, so invertibility of a morphism reduces to membership of the numerator in the class of
morphisms with acyclic cone. The distinguished triangles of `K(Mod^dg(E))` are the triangles of
admissible short exact sequences, and such a sequence evaluates to a *degreewise split* short
exact sequence of complexes of `R`-modules, whose distinguished triangle in `K(ModuleCat R)` has
the complex of the quotient module as its third vertex
(`DGCategory.RightModule.quasiIso_quotient_map_cochainMap_a_iff`, the `iff` strengthening of
`DGCategory.RightModule.quasiIso_quotient_map_cochainMap_a`). So evaluation inverts the numerator
exactly when the complex of the cone at the unique object is acyclic — and because `E` has only
one object that is exactly acyclicity of the cone. This is the only place the one-object
hypothesis enters: for a `C` with several objects, evaluation at one of them does not reflect
isomorphisms, since a module can be acyclic at that object and nowhere else.

## What conservativity reflects, and the hypothesis `hU`

`hU` asks that a cocone on Deligne's ind-object `X/W ⥤ D(E, d)` whose `U`-image is a value of
`R(Hom(K, -) ⋙ U)` at `X` be already a value of `R Hom(K, -)` at `X`. Conservativity reduces
that, exactly, to the plain assertion that `R Hom(K, -)` is defined at `X` at all:
`CategoryTheory.Functor.isRightDerivedValueAt_of_mapCocone` turns a value *somewhere* into the
value *at the prescribed cocone*, by comparing colimits across `U`. Hence
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor_of_isRightDerivable`: the
`D(E, d)`-level universal property follows from Tag 09LK's own hypothesis, step 3, and
everywhere-definedness of the `D(E, d)`-valued `R Hom(K, -)` — with no reflection hypothesis. The
converse implication holds too
(`CochainComplex.isRightDerivable_derivedHomReflectorSource_of_reflects`), so `hU` is not a
further assumption at all: given Tag 09LK's hypothesis and step 3 it *is*
everywhere-definedness.

What is *not* bought is that everywhere-definedness, and this file does not pretend otherwise.
Two results already in this repository say that it cannot be bought by the two routes one would
try, and they are the reason this file stops where it does.

* **Conservativity alone does not reflect right derivability**, even with a zero object and split
  idempotents in the source:
  `CategoryTheory.SingleObjWithZero.exists_conservative_not_reflecting_isRightDerivable`. So the
  hypotheses `[G.Full] [G.Faithful]` of
  `CategoryTheory.Functor.IsRightDerivable.of_comp` cannot be weakened to the conservativity
  proved below, and no variant of
  `CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_comp` with
  conservativity in place of full faithfulness is true. That counterexample category is not
  additive, so it leaves open — it does not refute — a statement restricted to additive exact
  functors of triangulated categories, which `U` is.
* **The detour through eventual constancy is closed for precisely these ind-objects.**
  Conservativity does reflect *eventual* constancy
  (`CategoryTheory.Functor.isEventuallyConstantFrom_of_comp`), so essential constancy in `D(Ab)`
  would transport if it forced eventual constancy. It does not:
  `CochainComplex.isEssentiallyConstantInd_and_not_isEventuallyConstantFrom` exhibits, for every
  `K` that is not K-projective and every zero object `X` of `K(A)`, an ind-object of Tag 05S9's
  shape whose image in `D(Ab)` is essentially constant and which is eventually constant from no
  index — and the second half is proved out of *every* object and index, so the gap is not a
  feature of a special `X`. (That statement is proved in the differential graded *algebra*
  encoding of `E`; the argument uses only exactness of `Hom(K, -)` and that the transition
  morphisms are the quasi-isomorphisms, so it is the same obstruction in either encoding.)

So the residue of `hU`, after conservativity has been used for all it is worth, is the single
implication

`R(Hom(K, -) ⋙ U)` everywhere defined `⟹` `R Hom(K, -)` everywhere defined,

for this additive exact conservative `U`; it is neither proved nor refuted here, and the two
results above say that it is not reachable from conservativity and not reachable through eventual
constancy.

## Main results

* `DGCategory.RightModule.quasiIso_quotient_map_cochainMap_a_iff`: an admissible short exact
  sequence evaluates to a quasi-isomorphism exactly when the complex of its quotient module is
  acyclic.
* `DGCategory.RightModule.trW_of_isIso_cochainComplexToDerived`: for a differential graded
  category with one object, evaluation at it detects the morphisms with acyclic cone.
* `DGCategory.isIso_iff_isIso_endDerivedForget_map` and
  `DGCategory.endDerivedForget_reflectsIsomorphisms`: **`U` reflects isomorphisms.**
* `CategoryTheory.Functor.isRightDerivedValueAt_of_mapCocone` and
  `CategoryTheory.Functor.reflects_isRightDerivedValueAt`: a functor reflecting isomorphisms
  reflects right-derived values at a prescribed cocone, as soon as the right derived functor is
  defined there.
* `CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor_of_isRightDerivable`:
  **`hU` discharged** from everywhere-definedness of the `D(E, d)`-valued right derived functor.
* `CochainComplex.isRightDerivable_derivedHomReflectorSource_of_reflects`: the converse, so that
  `hU` and that everywhere-definedness are **equivalent** given Tag 09LK's own hypothesis and
  step 3.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9) for a value of a right derived functor;
  [Tag 05PU](https://stacks.math.columbia.edu/tag/05PU) for essential constancy.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace DGCategory

universe w v u r

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- **An admissible short exact sequence evaluates to a quasi-isomorphism exactly when the
complex of its quotient module at `X` is acyclic.** The evaluated sequence is degreewise split,
so it sits in a distinguished triangle of `K(ModuleCat R)` whose third vertex is the complex of
the quotient module; a morphism of the homotopy category is a quasi-isomorphism exactly when the
third vertex of a distinguished triangle on it is acyclic. This is the `iff` strengthening of
`DGCategory.RightModule.quasiIso_quotient_map_cochainMap_a`, whose forward direction is what
makes evaluation descend to the derived categories and whose backward direction is what makes
the descent conservative over a one-object differential graded category. -/
theorem quasiIso_quotient_map_cochainMap_a_iff {x y z : RightModule.{v} C}
    (E : GradedSplitShortExact (A := rightModuleCategory.{v} C) x y z) (X : C.Obj) :
    HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
          (cochainMap E.a X)) ↔ (z.cochainComplex X).Acyclic := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  refine Iff.trans ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{v} R)).trW_iff_of_distinguished
    _ (CochainComplex.trianglehOfDegreewiseSplit_distinguished (gradedSplitShortComplex E X)
      (gradedSplitSplitting E X))) ?_
  exact HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _

variable [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **Evaluation at `X` detects the morphisms with acyclic cone, when `X` is the only object.**
If evaluation at `X`, followed by the localization of complexes of `R`-modules, inverts `f`, then
the cone of `f` is acyclic — the converse of
`DGCategory.RightModule.trW_isInvertedBy_cochainComplexOnK_comp_Qh`.

A distinguished triangle on `f` is isomorphic to the triangle of an admissible short exact
sequence; evaluation carries the isomorphism of triangles to one of triangles, so the first arrow
of that sequence is inverted too, hence is a quasi-isomorphism, hence the complex of its quotient
module at `X` is acyclic. Subsingletonness of the objects turns that into acyclicity of the
module, and the isomorphism of triangles carries it back to the cone of `f`. Without it the
statement is false: a module can be acyclic at `X` and at no other object. -/
theorem trW_of_isIso_cochainComplexToDerived [Subsingleton C.Obj] (X : C.Obj)
    {M N : (rightModuleCategory.{v} C).K} (f : M ⟶ N)
    (h : IsIso ((cochainComplexToDerived C X).map f)) : (acyclicProperty C).trW f := by
  obtain ⟨Z, g, hgh, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
  refine ((acyclicProperty C).trW_iff_of_distinguished _ hT).2 ?_
  have hT' := hT
  rw [distinguishedTriangles_rightModuleHomotopyCategory] at hT'
  obtain ⟨x, y, z, E, ⟨e⟩⟩ := hT'
  have : IsIso e.hom.hom₁ := (Triangle.π₁.mapIso e).isIso_hom
  have : IsIso e.hom.hom₂ := (Triangle.π₂.mapIso e).isIso_hom
  have heq : (cochainComplexToDerived C X).map e.hom.hom₁ ≫ (cochainComplexToDerived C X).map
        (GradedSplitShortExact.associatedKTriangle
          (rightModuleConeSituation.{v} C).shift E).mor₁ =
      (cochainComplexToDerived C X).map f ≫ (cochainComplexToDerived C X).map e.hom.hom₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ e.hom.comm₁.symm
  have : IsIso ((cochainComplexToDerived C X).map e.hom.hom₁ ≫
      (cochainComplexToDerived C X).map (GradedSplitShortExact.associatedKTriangle
        (rightModuleConeSituation.{v} C).shift E).mor₁) := by rw [heq]; infer_instance
  have : IsIso ((cochainComplexToDerived C X).map (GradedSplitShortExact.associatedKTriangle
      (rightModuleConeSituation.{v} C).shift E).mor₁) :=
    IsIso.of_isIso_comp_left ((cochainComplexToDerived C X).map e.hom.hom₁) _
  have hq : HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
        (cochainMap E.a X)) := (DerivedCategory.isIso_Qh_map_iff _).1 this
  have hz : (z.cochainComplex X).Acyclic := (quasiIso_quotient_map_cochainMap_a_iff E X).1 hq
  refine (acyclicProperty C).prop_of_iso (Triangle.π₃.mapIso e).symm ?_
  exact (acyclicProperty_iff z).2 fun Y => Subsingleton.elim X Y ▸ hz

/-- **Evaluation at the unique object detects isomorphisms.** A morphism of `D(C)`, for `C` a
differential graded category with a single object, is invertible exactly when its image under
evaluation at that object is invertible in `D(ModuleCat R)`.

Write the morphism as a left fraction `f / s`; the denominator is inverted by the quotient
functor, so invertibility of the morphism is invertibility of the numerator, which
`DGCategory.RightModule.trW_of_isIso_cochainComplexToDerived` reads off from the evaluated
numerator. -/
theorem isIso_iff_isIso_derivedEvaluationForget_map [Subsingleton C.Obj] (X : C.Obj)
    {M N : derivedCategory C} (φ : M ⟶ N) :
    IsIso φ ↔ IsIso ((derivedEvaluationForget C X).map φ) := by
  refine ⟨fun _ => inferInstance, fun h => ?_⟩
  have := Localization.essSurj (derivedQ C) (acyclicProperty C).trW
  set eX := (derivedQ C).objObjPreimageIso M with hEX
  set eY := (derivedQ C).objObjPreimageIso N with hEY
  obtain ⟨α, hα⟩ := Localization.exists_leftFraction (derivedQ C) (acyclicProperty C).trW
    (eX.hom ≫ φ ≫ eY.inv)
  have hfac : (eX.hom ≫ φ ≫ eY.inv) ≫ (derivedQ C).map α.s = (derivedQ C).map α.f := by
    rw [hα]
    exact MorphismProperty.LeftFraction.map_comp_map_s α _ _
  have hs : IsIso ((derivedQ C).map α.s) :=
    Localization.inverts (derivedQ C) (acyclicProperty C).trW _ α.hs
  have hUf : IsIso ((derivedEvaluationForget C X).map ((derivedQ C).map α.f)) := by
    rw [← hfac]
    simp only [Functor.map_comp]
    infer_instance
  have hf : (acyclicProperty C).trW α.f := by
    refine trW_of_isIso_cochainComplexToDerived X α.f ?_
    exact (NatIso.isIso_map_iff (derivedEvaluationForgetCompIso C X) α.f).mp hUf
  have hfiso : IsIso ((derivedQ C).map α.f) :=
    Localization.inverts (derivedQ C) (acyclicProperty C).trW _ hf
  have hmid : IsIso (eX.hom ≫ φ ≫ eY.inv) := by
    have : IsIso ((eX.hom ≫ φ ≫ eY.inv) ≫ (derivedQ C).map α.s) := by rw [hfac]; exact hfiso
    exact IsIso.of_isIso_comp_right _ ((derivedQ C).map α.s)
  have hφ : φ = eX.inv ≫ (eX.hom ≫ φ ≫ eY.inv) ≫ eY.hom := by simp
  rw [hφ]
  infer_instance

end RightModule

variable {R : Type r} [CommRing R]

variable (C : DGCategory.{v, u} R) (K : C.Obj) [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- **Cohomology detects isomorphisms through the forgetful functor `D(E, d) ⥤ D(ModuleCat R)`.**
A morphism of `D(E, d)` is invertible exactly when the morphism of `D(ModuleCat R)` it induces
on underlying complexes is. -/
theorem isIso_iff_isIso_endDerivedForget_map {M N : RightModule.derivedCategory
    (endDGCategory C K)} (φ : M ⟶ N) :
    IsIso φ ↔ IsIso ((endDerivedForget.{w} C K).map φ) :=
  RightModule.isIso_iff_isIso_derivedEvaluationForget_map (C := endDGCategory C K) PUnit.unit φ

/-- **The forgetful functor `D(E, d) ⥤ D(ModuleCat R)` reflects isomorphisms.** This is the
conservativity that the proof of [Stacks, Tag 09LK] appeals to, for the functor `U` that proof
uses: a right differential graded `C(K, K)`-module is a complex of `R`-modules with an action,
and forgetting the action does not change the cohomology. -/
instance endDerivedForget_reflectsIsomorphisms :
    (endDerivedForget.{w} C K).ReflectsIsomorphisms where
  reflects φ _ := (isIso_iff_isIso_endDerivedForget_map C K φ).2 inferInstance

end DGCategory

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  {D'' : Type u₃} [Category.{v₃} D'']

/-- **A conservative functor reflects a value of a right derived functor at a prescribed cocone,
once the right derived functor is known to be defined at that object.** Let `U` reflect
isomorphisms, let `c` be a cocone on Deligne's ind-object `X/W ⥤ 𝒟'` of `F`, let its `U`-image be
a value of `R(F ⋙ U)` at `X` in the sense of Tag 05S9, and let `RF` be defined at `X` *at all*.
Then `c` itself is a value of `RF` at `X`.

The point is that the conclusion is about the *given* cocone, which is what the proof of
[Stacks, Tag 09LK] consumes: a value of `RF` cannot be manufactured from the hypotheses (see
`CategoryTheory.EssentiallyConstantInd.exists_isEssentiallyConstantWith_of_comp`, where the
vertex is produced by splitting an idempotent and full faithfulness is indispensable), but once
*some* value `c'` exists, conservativity pins `c` down: the canonical comparison `c'.pt ⟶ c.pt`
becomes, after `U`, the comparison between two colimit cocones of one diagram — `U.mapCocone c'`
is a colimit because a value is carried forward by any functor
(`CategoryTheory.Functor.IsRightDerivedValueAt.comp`) — hence invertible, hence invertible before
`U`, and the essential-constancy datum transports along an isomorphism of cocones
(`CategoryTheory.Functor.isRightDerivedValueAt_of_isColimit`).

So the cocone-wise reflection asked for by Tag 09LK is no stronger than the plain assertion that
the right derived functor of the unforgetful `F` is defined; it is *that* assertion which the
source leaves unproved, and which
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero` shows does
not follow from conservativity alone. -/
theorem isRightDerivedValueAt_of_mapCocone (F : D ⥤ D') (W : MorphismProperty D) (U : D' ⥤ D'')
    [U.ReflectsIsomorphisms] (X : D)
    {c : Limits.Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (hdef : ∃ c', F.IsRightDerivedValueAt W X c')
    (hc : (F ⋙ U).IsRightDerivedValueAt W X (U.mapCocone c)) :
    F.IsRightDerivedValueAt W X c := by
  obtain ⟨c', hc'⟩ := hdef
  refine isRightDerivedValueAt_of_isColimit F W X ⟨c', hc'⟩ ?_
  have hφ : ∀ j, c'.ι.app j ≫ hc'.isColimit.desc c = c.ι.app j := hc'.isColimit.fac c
  have hUc' : Limits.IsColimit (U.mapCocone c') := (hc'.comp U).isColimit
  have hmap : U.map (hc'.isColimit.desc c) =
      (hUc'.coconePointUniqueUpToIso hc.isColimit).hom := by
    refine hUc'.hom_ext fun j => ?_
    rw [hUc'.comp_coconePointUniqueUpToIso_hom]
    exact (U.map_comp _ _).symm.trans (congrArg U.map (hφ j))
  have : IsIso (U.map (hc'.isColimit.desc c)) := by rw [hmap]; infer_instance
  have : IsIso (hc'.isColimit.desc c) := isIso_of_reflects_iso (hc'.isColimit.desc c) U
  exact Limits.IsColimit.ofIsoColimit hc'.isColimit
    (Limits.Cocones.ext (asIso (hc'.isColimit.desc c)) hφ)

/-- **A conservative functor reflects right-derived values whenever the right derived functor is
everywhere defined.** This is `CategoryTheory.Functor.isRightDerivedValueAt_of_mapCocone` in the
shape in which the proof of [Stacks, Tag 09LK] uses it: `U` reflects isomorphisms and `RF` is
right derivable, and the conclusion is the reflection of values at every object and every
cocone. -/
theorem reflects_isRightDerivedValueAt (F : D ⥤ D') (W : MorphismProperty D) (U : D' ⥤ D'')
    [U.ReflectsIsomorphisms] (hdef : F.IsRightDerivable W) (X : D)
    (c : Limits.Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F))
    (hc : (F ⋙ U).IsRightDerivedValueAt W X (U.mapCocone c)) :
    F.IsRightDerivedValueAt W X c :=
  isRightDerivedValueAt_of_mapCocone F W U X (hdef X) hc

end CategoryTheory.Functor

namespace CochainComplex

universe w' v'

variable (A : Type) [Category.{0} A] [Abelian A]
  [((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{v'} A]
  [HasDerivedCategory.{w'} (ModuleCat.{0} ℤ)]

/-- **The `D(E, d)`-level universal property of Tag 09LK, with the reflection along `U` replaced
by everywhere-definedness of the `D(E, d)`-valued right derived functor.** This is
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor` with its hypothesis `hU`
discharged: conservativity of `U` (`DGCategory.endDerivedForget_reflectsIsomorphisms`) turns the
cocone-wise reflection of right-derived values into the plain assertion `hdef` that the
`D(E, d)`-valued `R Hom(K, -)` is defined at every object
(`CategoryTheory.Functor.reflects_isRightDerivedValueAt`).

So the reflection hypothesis is *not* an extra assumption beyond definedness: everything in
Tag 09LK's conclusion except definedness at the `D(E, d)` level follows from the source's own
hypothesis `h`, from step 3's `hstep3`, and from conservativity. Like its unprimed companion this
is deliberately **not** registered as `09LK`: `hdef` is not among Tag 09LK's hypotheses, and the
module docstring records why conservativity cannot supply it. -/
theorem isRightDerivedFunctor_derivedHomReflectorFunctor_of_isRightDerivable
    (β : derivedHomReflectorSource A K ⟶
      DerivedCategory.Qh ⋙ derivedHomReflectorFunctor A K)
    (h : (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hstep3 : (derivedHomReflectorFunctor A K ⋙ derivedHomReflectorForget A K).IsRightDerivedFunctor
      (derivedHomReflectorForgetUnit A K β)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hdef : (derivedHomReflectorSource A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomReflectorFunctor A K).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_derivedHomReflectorFunctor A K β h hstep3 fun X _ hc =>
    Functor.isRightDerivedValueAt_of_mapCocone (derivedHomReflectorSource A K)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (derivedHomReflectorForget A K) X
      (hdef X) hc

/-- **The reflection hypothesis `hU` of Tag 09LK implies everywhere-definedness**, so with
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor_of_isRightDerivable` the two are
*equivalent* in the presence of Tag 09LK's own hypothesis `h` and step 3's conclusion `hstep3`:
`h` and `hstep3` make the `U`-image of the comparison cocone at `X` a value of
`R(Hom(K, -) ⋙ U)`, so `hU` carries it back and exhibits a value of the `D(E, d)`-valued
`R Hom(K, -)` at `X`.

This is what locates the gap in Tag 09LK's proof exactly: nothing is missing beyond
everywhere-definedness at the `D(E, d)` level, and the reflection the source appeals to is a
restatement of it rather than a further assumption. -/
theorem isRightDerivable_derivedHomReflectorSource_of_reflects
    (β : derivedHomReflectorSource A K ⟶
      DerivedCategory.Qh ⋙ derivedHomReflectorFunctor A K)
    (h : (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hstep3 : (derivedHomReflectorFunctor A K ⋙ derivedHomReflectorForget A K).IsRightDerivedFunctor
      (derivedHomReflectorForgetUnit A K β)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hU : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ))
      (c : Limits.Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ derivedHomReflectorSource A K)),
      (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K).IsRightDerivedValueAt
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X
          ((derivedHomReflectorForget A K).mapCocone c) →
        (derivedHomReflectorSource A K).IsRightDerivedValueAt
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X c) :
    (derivedHomReflectorSource A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  have := hstep3
  intro X
  refine ⟨_, hU X (Functor.derivedUnitCocone (derivedHomReflectorSource A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomReflectorFunctor A K) β X) ?_⟩
  refine Functor.isRightDerivedValueAt_of_isColimit
    (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X (h X) ?_
  refine Limits.IsColimit.ofIsoColimit (Functor.isRightDerivedValueAt_derivedUnitCocone
    (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomReflectorFunctor A K ⋙ derivedHomReflectorForget A K)
    (derivedHomReflectorForgetUnit A K β) h X).isColimit
    (Limits.Cocones.ext (Iso.refl _) fun s => ?_)
  simp [Functor.derivedUnitCocone_ι_app, derivedHomReflectorForgetUnit]

end CochainComplex

end

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismDGCategory
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.AcyclicTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.CochainComplexFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Triangulated

/-!
# Evaluation at an object, on the derived categories

Let `C` be a differential graded category over a commutative ring `R` and let `X` be an object
of `C`. Evaluation at `X` is the functor `ev_X : K(Mod^dg(C)) ⥤ K(ModuleCat R)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.CochainComplexFunctor`, sending a
right differential graded module to the complex `M X` of `R`-modules. This file descends it to
the derived categories:

`ev_X : D(C) ⥤ D(ModuleCat R)`.

For the one-object differential graded category `E = C(K, K)` this is the forgetful functor out
of the derived category of right differential graded `E`-modules — a right differential graded
`E`-module is a single complex of `R`-modules with an action of `C(K, K)`, and evaluation at the
unique object forgets the action. That is the functor that step 3 of the replacement proof of
[Stacks, Tag 09LK] takes as its `U`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean`).

## Why the descent exists

`D(C)` is the Verdier quotient of `K(Mod^dg(C))` by the acyclic modules, so what has to be
checked is that evaluation at `X` inverts every morphism whose cone is acyclic. The distinguished
triangles of `K(Mod^dg(C))` are the triangles of admissible short exact sequences
(`DGCategory.distinguishedTriangles_rightModuleHomotopyCategory`), and an admissible short exact
sequence is one that is split in each degree as a sequence of graded modules; evaluating it at
`X` gives a *degreewise split* short exact sequence of complexes of `R`-modules. Mathlib's
`CochainComplex.trianglehOfDegreewiseSplit_distinguished` turns that into a distinguished
triangle of `K(ModuleCat R)` whose third vertex is the complex of the quotient module, so when
the quotient module is acyclic the first morphism lies in `HomotopyCategory.quasiIso`, which the
localization `DerivedCategory.Qh` inverts. A general morphism with acyclic cone is carried to
such a morphism by an isomorphism of triangles.

So the descent is obtained from the universal property of the localization alone, and not from
`CategoryTheory.ObjectProperty.descend`: the latter would need evaluation at `X` to be exact,
which is a statement about the differential graded shift of `Mod^dg(C)` against Mathlib's shift
of complexes, and is not proved here. Nothing downstream needs it — the `U` of step 3 of
[Stacks, Tag 09LK] is an arbitrary functor.

## Main definitions

* `DGCategory.RightModule.gradedSplitShortComplex` and
  `DGCategory.RightModule.gradedSplitSplitting`: the degreewise split short complex of complexes
  of `R`-modules obtained by evaluating an admissible short exact sequence at `X`.
* `DGCategory.RightModule.derivedEvaluationForget`: **the functor
  `ev_X : D(C) ⥤ D(ModuleCat R)`.**
* `DGCategory.RightModule.derivedEvaluationForgetCompIso`: the identification
  `Q_C ⋙ ev_X ≅ ev_X ⋙ Q` of its restriction along the quotient functor.
* `DGCategory.endDerivedForget`: the same functor for the one-object differential graded
  category `C(K, K)`, that is the forgetful functor `D(C(K, K)) ⥤ D(ModuleCat R)`.

## Main results

* `DGCategory.RightModule.app_comp_eq`: an identity between composites of degree-zero
  homogeneous morphisms, read elementwise.
* `DGCategory.RightModule.quasiIso_quotient_map_cochainMap_a`: the first morphism of an
  admissible short exact sequence with acyclic quotient evaluates to a quasi-isomorphism.
* `DGCategory.RightModule.trW_isInvertedBy_cochainComplexOnK_comp_Qh`: evaluation at `X`,
  followed by the localization of complexes of `R`-modules, inverts every morphism whose cone is
  acyclic.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
-/

@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace RightModule

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-! ### Identities between composites, read elementwise -/

/-- **An identity between composites of degree-zero homogeneous morphisms, elementwise.** The
composite of `Mod^dg(C)` is composition of maps, so an identity of composites of degree-zero
morphisms says exactly that the two sides agree on every element in every degree. -/
theorem app_comp_eq {M N P : RightModule.{v} C} {ψ : (rightModuleCategory.{v} C).Hom N P 0}
    {φ : (rightModuleCategory.{v} C).Hom M N 0} {χ : (rightModuleCategory.{v} C).Hom M P 0}
    (hc : (rightModuleCategory.{v} C).comp (show (0 : ℤ) + 0 = 0 by omega) ψ φ = χ)
    {x : C.Obj} (i : ℤ) (a : M.obj x i) :
    app ψ (add_zero i) (app φ (add_zero i) a) = app χ (add_zero i) a := by
  rw [← app_homComp_zero ψ φ (by omega) i (add_zero i) a]
  exact congrArg (fun ξ : (rightModuleCategory.{v} C).Hom M P 0 => app ξ (add_zero i) a) hc

/-! ### An admissible short exact sequence, evaluated at an object -/

variable {x y z : RightModule.{v} C}
  (E : GradedSplitShortExact (A := rightModuleCategory.{v} C) x y z) (X : C.Obj)

/-- **An admissible short exact sequence, evaluated at `X`.** Its two closed arrows become maps
of complexes of `R`-modules, and they compose to zero. -/
def gradedSplitShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) where
  X₁ := x.cochainComplex X
  X₂ := y.cochainComplex X
  X₃ := z.cochainComplex X
  f := cochainMap E.a X
  g := cochainMap E.b X
  zero := by
    have key : ∀ (i : ℤ) (a : x.obj X i),
        app E.b.1 (add_zero i) (app E.a.1 (add_zero i) a) = 0 := fun i a =>
      (app_comp_eq E.comp_zero i a).trans (zero_app _ _)
    ext i a
    exact key i a

/-- **The splitting of the evaluated sequence in each degree.** The two unclosed arrows of the
graded splitting are degree-zero homogeneous morphisms, so they have a component in each degree,
and the four identities of a graded splitting are the four identities of a splitting of a short
complex — the only difference is the order in which a composite is written. -/
def gradedSplitSplitting (i : ℤ) :
    ((gradedSplitShortComplex E X).map (HomologicalComplex.eval _ _ i)).Splitting where
  r := cochainMapComponent E.π X i
  s := cochainMapComponent E.s X i
  f_r := by
    have key : ∀ a : x.obj X i, app E.π (add_zero i) (app E.a.1 (add_zero i) a) = a := fun a =>
      (app_comp_eq E.π_a i a).trans (objCast_rfl (M := x) X a)
    ext a
    exact key a
  s_g := by
    have key : ∀ a : z.obj X i, app E.b.1 (add_zero i) (app E.s (add_zero i) a) = a := fun a =>
      (app_comp_eq E.b_s i a).trans (objCast_rfl (M := z) X a)
    ext a
    exact key a
  id := by
    have key : ∀ a : y.obj X i,
        app E.a.1 (add_zero i) (app E.π (add_zero i) a) +
          app E.s (add_zero i) (app E.b.1 (add_zero i) a) = a := by
      intro a
      have h1 : app (homComp (show (0 : ℤ) + 0 = 0 by omega) E.a.1 E.π) (add_zero i) a +
          app (homComp (show (0 : ℤ) + 0 = 0 by omega) E.s E.b.1) (add_zero i) a =
            app (homId y) (add_zero i) a :=
        congrArg (fun ξ : (rightModuleCategory.{v} C).Hom y y 0 => app ξ (add_zero i) a)
          E.a_π_add_s_b
      rw [app_homComp_zero, app_homComp_zero] at h1
      exact h1.trans (objCast_rfl (M := y) X a)
    ext a
    exact key a

/-! ### The evaluated sequence is a quasi-isomorphism when the quotient is acyclic -/

/-- **An admissible short exact sequence with acyclic quotient evaluates to a
quasi-isomorphism.** The evaluated sequence is degreewise split, hence sits in a distinguished
triangle of `K(ModuleCat R)` whose third vertex is the complex of the quotient module; if that
complex is acyclic, the first morphism has acyclic cone, which is what a quasi-isomorphism of
the homotopy category is. -/
theorem quasiIso_quotient_map_cochainMap_a (hz : (z.cochainComplex X).Acyclic) :
    HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
        (cochainMap E.a X)) := by
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ⟨_, _, _,
    CochainComplex.trianglehOfDegreewiseSplit_distinguished (gradedSplitShortComplex E X)
      (gradedSplitSplitting E X),
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 hz⟩

/-! ### The descent to the derived categories -/

variable (C) [HasDerivedCategory.{w} (ModuleCat.{v} R)]

/-- Evaluation at `X`, followed by the localization of complexes of `R`-modules at the
quasi-isomorphisms: the functor `K(Mod^dg(C)) ⥤ D(ModuleCat R)` that descends to the derived
category of right differential graded modules. -/
noncomputable abbrev cochainComplexToDerived (X : C.Obj) :
    (rightModuleCategory.{v} C).K ⥤ DerivedCategory (ModuleCat.{v} R) :=
  cochainComplexOnK.{v} X ⋙ DerivedCategory.Qh

/-- **Evaluation at `X` inverts the morphisms with acyclic cone.** A morphism of
`K(Mod^dg(C))` with acyclic cone sits in a distinguished triangle with acyclic third vertex;
that triangle is isomorphic to the triangle of an admissible short exact sequence, whose
quotient module is therefore acyclic too, and the first arrow of that sequence evaluates to a
quasi-isomorphism. The isomorphism of triangles carries the conclusion back. -/
theorem trW_isInvertedBy_cochainComplexOnK_comp_Qh (X : C.Obj) :
    (acyclicProperty C).trW.IsInvertedBy (cochainComplexToDerived C X) := by
  rintro M N s ⟨Z, g, h, hT, hZ⟩
  rw [distinguishedTriangles_rightModuleHomotopyCategory] at hT
  obtain ⟨x, y, z, E, ⟨e⟩⟩ := hT
  have hz : acyclicProperty C z :=
    (acyclicProperty C).prop_of_iso (Triangle.π₃.mapIso e) hZ
  have : IsIso ((cochainComplexToDerived C X).map
      (GradedSplitShortExact.associatedKTriangle
        (rightModuleConeSituation.{v} C).shift E).mor₁) :=
    Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)) _
      (quasiIso_quotient_map_cochainMap_a E X ((acyclicProperty_iff z).1 hz X))
  have : IsIso e.hom.hom₁ := (Triangle.π₁.mapIso e).isIso_hom
  have : IsIso e.hom.hom₂ := (Triangle.π₂.mapIso e).isIso_hom
  have : IsIso ((cochainComplexToDerived C X).map (s ≫ e.hom.hom₂)) := by
    rw [show s ≫ e.hom.hom₂ = e.hom.hom₁ ≫ (GradedSplitShortExact.associatedKTriangle
      (rightModuleConeSituation.{v} C).shift E).mor₁ from e.hom.comm₁, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at this
  exact IsIso.of_isIso_comp_right ((cochainComplexToDerived C X).map s)
    ((cochainComplexToDerived C X).map e.hom.hom₂)

/-- **Evaluation at `X` on the derived categories**, `ev_X : D(C) ⥤ D(ModuleCat R)`: the descent
of `ev_X : K(Mod^dg(C)) ⥤ K(ModuleCat R)`, followed by the localization of complexes of
`R`-modules, through the Verdier quotient of `K(Mod^dg(C))` by the acyclic modules. It exists
because that composite inverts every morphism with acyclic cone.

For the one-object differential graded category `C(K, K)` this is the forgetful functor
`D(C(K, K)) ⥤ D(ModuleCat R)`; see `DGCategory.endDerivedForget`. -/
noncomputable def derivedEvaluationForget (X : C.Obj) :
    RightModule.derivedCategory C ⥤ DerivedCategory (ModuleCat.{v} R) :=
  Localization.lift (cochainComplexToDerived C X)
    (trW_isInvertedBy_cochainComplexOnK_comp_Qh C X) (derivedQ C)

/-- **Evaluation at `X` on the derived categories agrees with evaluation at `X`.** Restricting
`DGCategory.RightModule.derivedEvaluationForget` along the quotient functor of `D(C)` gives back
evaluation at `X` followed by the localization of complexes of `R`-modules. -/
noncomputable def derivedEvaluationForgetCompIso (X : C.Obj) :
    derivedQ C ⋙ derivedEvaluationForget C X ≅
      cochainComplexToDerived C X :=
  Localization.fac (cochainComplexToDerived C X)
    (trW_isInvertedBy_cochainComplexOnK_comp_Qh C X) (derivedQ C)

end RightModule

/-- **The forgetful functor out of the derived category of a one-object differential graded
category.** For `K` an object of `C` and `E = C(K, K)` the one-object differential graded
subcategory on it, a right differential graded `E`-module is a complex of `R`-modules together
with an action of `C(K, K)`; forgetting that action and passing to derived categories gives

`D(E) ⥤ D(ModuleCat R)`,

which is evaluation at the unique object of `E`. This is the functor `U` that step 3 of the
replacement proof of [Stacks, Tag 09LK] consumes, and the reflector
`R̃ : D(A) ⥤ D(E)` of
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomReflectorExists.lean`
lands in its source. -/
noncomputable def endDerivedForget {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
    (K : C.Obj) [HasDerivedCategory.{w} (ModuleCat.{v} R)] :
    RightModule.derivedCategory (endDGCategory C K) ⥤ DerivedCategory (ModuleCat.{v} R) :=
  RightModule.derivedEvaluationForget (endDGCategory C K) PUnit.unit

end DGCategory

end

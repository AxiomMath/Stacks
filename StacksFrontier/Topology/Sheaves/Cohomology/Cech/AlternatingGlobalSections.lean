module

public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingAugmentation
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.GlobalSectionsToCech
import StacksCore.Tactic.StacksAttribute

/-!
# Global sections and the total alternating Čech complex

Let `X` be a topological space and let `U : I → Opens X` be a family of open subsets. A global
section of an abelian presheaf on `X` restricts to an alternating Čech cochain of degree zero,
and that cochain is killed by the Čech differential. Applying this in every cohomological
degree of a complex of abelian presheaves and including the degree-zero Čech summand into the
total complex gives the canonical map
`Γ(X, F^•) ⟶ Tot(Č_alt(U, F^•))` of Stacks 08C0, natural in `F^•`.

## Main definitions

* `Stacks.Cech.globalSectionsUliftComplexFunctor`: sections over the whole space, degreewise,
  lifted to the universe of Čech cochains.
* `Stacks.Cech.globalSectionsAlternatingCechRestriction` and
  `Stacks.Cech.globalSectionsAlternatingCechRestrictionInt`: restriction of a global section
  into alternating Čech degree zero, for the nonnegatively graded and for the
  integer-indexed alternating Čech complex.
* `Stacks.Cech.globalSectionsToAlternatingCech`: the natural map from the complex of global
  sections to the total alternating Čech complex.

## Main results

* `Stacks.Cech.globalSectionsToAlternatingCech_app_f` characterizes the components of the map:
  in every cohomological degree it is the degree-zero restriction followed by the inclusion of
  the degree-zero Čech summand, so all of its positive Čech components vanish.

## Implementation notes

No covering hypothesis and no finiteness hypothesis is needed for this map; the family of
opens is arbitrary, and a client supplies a covering equation only where it uses one.

The degree-zero restriction is the augmentation of the alternating Čech complex taken at the
whole space, so it is `Stacks.Cech.alternatingCechAugmentation` at `⊤` rather than a second
construction. Its two compatibilities — with the Čech differential and with a morphism of
coefficient presheaves — are proved here in the integer-indexed complex, where the comparison
isomorphism with the nonnegatively graded one is named once, as
`alternatingCechExtendXIsoZero` and `alternatingCechExtendXIsoOne`, so that it is a single
fixed term wherever it occurs.

The identification of the degree-zero row of the alternating Čech bicomplex of a complex `K`
with the family of alternating Čech complexes of the terms of `K` is discharged once, at the
point of use, by the compatibilities `Stacks.Cech.ιTotalZero_comm` and
`Stacks.Cech.ιTotalZero_naturality`, which are stated for abstract data over an arbitrary
preadditive category and are shared with the non-alternating map of Stacks 07M9.

Čech cochains for a family indexed by `I : Type v` and coefficients in `AddCommGrpCat.{w}`
live in `AddCommGrpCat.{max v w}`, so a global section is lifted into that universe; the
space, the index and the coefficient universes are otherwise independent.

## References

* [Stacks Project, Tag 08C0](https://stacks.math.columbia.edu/tag/08C0)
* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u v w

namespace Stacks.Cech

variable (X : TopCat.{u}) {I : Type v} (U : I → Opens X)

/-- The functor taking a complex of abelian presheaves on `X` to its complex of sections over
the whole space, lifted to the universe of Čech cochains. -/
noncomputable def globalSectionsUliftComplexFunctor :
    CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max v w} ℤ :=
  (((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op ⊤)) ⋙
    AddCommGrpCat.uliftFunctor.{v, w}).mapHomologicalComplex (up ℤ)

/-- The functor of lifted global sections is additive. -/
instance globalSectionsUliftComplexFunctor_additive :
    (globalSectionsUliftComplexFunctor.{u, v, w} X).Additive :=
  inferInstanceAs ((((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{w}).obj (op ⊤)) ⋙
    AddCommGrpCat.uliftFunctor.{v, w}).mapHomologicalComplex (up ℤ)).Additive

/-- Restriction of a global section to each member of the family, as an alternating Čech
cochain of degree zero. -/
noncomputable def globalSectionsAlternatingCechRestriction
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (AddCommGrpCat.uliftFunctor.{v, w}).obj (F.obj (op ⊤)) ⟶
      (alternatingCechComplex U F).X 0 :=
  alternatingCechAugmentation X F U (fun _ ↦ le_top)

/-- The restriction of a global section into alternating Čech degree zero is a Čech cocycle. -/
@[reassoc]
lemma globalSectionsAlternatingCechRestriction_d (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    globalSectionsAlternatingCechRestriction X U F ≫
      (alternatingCechComplex U F).d 0 1 = 0 :=
  alternatingCechAugmentation_d X F U (fun _ ↦ le_top)

/-- Degree zero of the integer-indexed alternating Čech complex is degree zero of the
nonnegatively graded one. -/
noncomputable def alternatingCechExtendXIsoZero (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ((alternatingCechComplexFunctorInt U).obj F).X 0 ≅ (alternatingCechComplex U F).X 0 :=
  (alternatingCechComplex U F).extendXIso embeddingUpNat (i := 0) (i' := 0) rfl

/-- Degree one of the integer-indexed alternating Čech complex is degree one of the
nonnegatively graded one. -/
noncomputable def alternatingCechExtendXIsoOne (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ((alternatingCechComplexFunctorInt U).obj F).X 1 ≅ (alternatingCechComplex U F).X 1 :=
  (alternatingCechComplex U F).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl

/-- The augmentation in degree zero of the integer-indexed alternating Čech complex. -/
noncomputable def globalSectionsAlternatingCechRestrictionInt
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (AddCommGrpCat.uliftFunctor.{v, w}).obj (F.obj (op ⊤)) ⟶
      ((alternatingCechComplexFunctorInt U).obj F).X 0 :=
  globalSectionsAlternatingCechRestriction X U F ≫ (alternatingCechExtendXIsoZero X U F).inv

/-- The restriction of a global section into alternating Čech degree zero is natural in the
coefficient presheaf. -/
@[reassoc]
lemma globalSectionsAlternatingCechRestriction_naturality
    {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}} (a : F ⟶ G) :
    (AddCommGrpCat.uliftFunctor.{v, w}).map (a.app (op ⊤)) ≫
        globalSectionsAlternatingCechRestriction X U G =
      globalSectionsAlternatingCechRestriction X U F ≫ (alternatingCechMap U a).f 0 := by
  exact AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun s ↦ Subtype.ext <| funext fun i ↦
    restr_app a (le_top : CechCochains.inter U i ≤ ⊤) s.down

/-- The differential of the integer-indexed alternating Čech complex out of degree zero, read
through the comparison isomorphisms with the nonnegatively graded complex. -/
lemma alternatingCechComplexFunctorInt_d_zero_one (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ((alternatingCechComplexFunctorInt U).obj F).d 0 1 =
      (alternatingCechExtendXIsoZero X U F).hom ≫ (alternatingCechComplex U F).d 0 1 ≫
        (alternatingCechExtendXIsoOne X U F).inv :=
  HomologicalComplex.extend_d_eq _ embeddingUpNat rfl rfl

/-- The degree-zero component of the integer-indexed alternating Čech complex of a morphism of
presheaves, read through the comparison isomorphisms. -/
lemma alternatingCechComplexFunctorInt_map_f_zero
    {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}} (a : F ⟶ G) :
    ((alternatingCechComplexFunctorInt U).map a).f 0 =
      (alternatingCechExtendXIsoZero X U F).hom ≫ (alternatingCechMap U a).f 0 ≫
        (alternatingCechExtendXIsoZero X U G).inv :=
  HomologicalComplex.extendMap_f _ embeddingUpNat rfl

/-- The augmentation into degree zero of the integer-indexed alternating Čech complex is a Čech
cocycle. -/
@[reassoc]
lemma globalSectionsAlternatingCechRestrictionInt_d
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    globalSectionsAlternatingCechRestrictionInt X U F ≫
      ((alternatingCechComplexFunctorInt U).obj F).d 0 1 = 0 := by
  rw [globalSectionsAlternatingCechRestrictionInt,
    alternatingCechComplexFunctorInt_d_zero_one, Category.assoc, Iso.inv_hom_id_assoc,
    globalSectionsAlternatingCechRestriction_d_assoc, zero_comp]

/-- The augmentation into degree zero of the integer-indexed alternating Čech complex is
natural in the coefficient presheaf. -/
@[reassoc]
lemma globalSectionsAlternatingCechRestrictionInt_naturality
    {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}} (a : F ⟶ G) :
    (AddCommGrpCat.uliftFunctor.{v, w}).map (a.app (op ⊤)) ≫
        globalSectionsAlternatingCechRestrictionInt X U G =
      globalSectionsAlternatingCechRestrictionInt X U F ≫
        ((alternatingCechComplexFunctorInt U).map a).f 0 := by
  rw [globalSectionsAlternatingCechRestrictionInt,
    globalSectionsAlternatingCechRestrictionInt,
    alternatingCechComplexFunctorInt_map_f_zero, Category.assoc, Iso.inv_hom_id_assoc,
    globalSectionsAlternatingCechRestriction_naturality_assoc]

/-- **Stacks Project, Tag 08C0.** The functorial map from the complex of global sections to the
total alternating Čech complex: in each cohomological degree a section is sent, in Čech degree
zero, to its restrictions to the members of the family. -/
@[stacks 08C0]
noncomputable def globalSectionsToAlternatingCech :
    globalSectionsUliftComplexFunctor.{u, v, w} X ⟶ alternatingCechTotalComplexFunctor U where
  app K :=
    { f := fun n ↦ globalSectionsAlternatingCechRestrictionInt X U (K.X n) ≫
        ((alternatingCechBicomplexFunctor U).obj K).ιTotal (up ℤ) 0 n n (by simp)
      comm' := by
        rintro n _ rfl
        exact ιTotalZero_comm ((alternatingCechBicomplexFunctor U).obj K)
          ((globalSectionsUliftComplexFunctor.{u, v, w} X).obj K)
          (fun n ↦ globalSectionsAlternatingCechRestrictionInt X U (K.X n))
          (fun n ↦ globalSectionsAlternatingCechRestrictionInt_d X U (K.X n))
          (fun n ↦ globalSectionsAlternatingCechRestrictionInt_naturality X U
            (K.d n (n + 1))) n }
  naturality K L f := by
    refine HomologicalComplex.Hom.ext (funext fun n ↦ ?_)
    exact ιTotalZero_naturality ((alternatingCechBicomplexFunctor U).obj K)
      ((alternatingCechBicomplexFunctor U).obj L) ((alternatingCechBicomplexFunctor U).map f)
      ((globalSectionsUliftComplexFunctor.{u, v, w} X).obj K)
      ((globalSectionsUliftComplexFunctor.{u, v, w} X).obj L)
      ((globalSectionsUliftComplexFunctor.{u, v, w} X).map f)
      (fun n ↦ globalSectionsAlternatingCechRestrictionInt X U (K.X n))
      (fun n ↦ globalSectionsAlternatingCechRestrictionInt X U (L.X n))
      (fun n ↦ globalSectionsAlternatingCechRestrictionInt_naturality X U (f.f n)) n

/-- **Stacks Project, Tag 08C0.** In every cohomological degree the canonical map restricts a
global section into alternating Čech degree zero and includes that summand into the total
complex; in particular all of its positive Čech components vanish. -/
@[simp, stacks 08C0 "degree-zero restrictions and vanishing higher components"]
lemma globalSectionsToAlternatingCech_app_f
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{w}) ℤ) (n : ℤ) :
    ((globalSectionsToAlternatingCech X U).app K).f n =
      globalSectionsAlternatingCechRestrictionInt X U (K.X n) ≫
        ((alternatingCechBicomplexFunctor U).obj K).ιTotal (up ℤ) 0 n n (by simp) := rfl

end Stacks.Cech

end

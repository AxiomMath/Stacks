module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingComplexFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.RecoveryA.GlobalSectionsToCech

/-!
# The alternating Čech comparison, naturally in the presheaf and totalized

Let `X` be a topological space and `U : I → Opens X` a family of open subsets. Both the
alternating Čech complex of Stacks 01FH and Mathlib's Čech complex are functors of the
coefficient presheaf, and the canonical inclusion of the first into the second is natural: a
morphism of presheaves acts on cochains by applying it to every section, and that action
carries alternating cochains to alternating cochains. Applying that natural transformation
degreewise to a complex of abelian presheaves and totalizing the two Čech bicomplexes gives
the comparison `Tot(Č_alt(𝒰, F^•)) ⟶ Tot(Č(𝒰, F^•))` of unbounded Čech complexes, which is a
quasi-isomorphism as soon as `F^•` vanishes in low degrees.

## Main definitions

* `Stacks.Cech.alternatingCechInclusionNatTrans`: the canonical inclusion of the alternating
  Čech complex into Mathlib's Čech complex, as a natural transformation of functors of the
  coefficient presheaf.
* `Stacks.Cech.cechBicomplexRowsMap`: the same transformation applied degreewise to a complex
  of abelian presheaves, with the Čech degree placed second.
* `Stacks.Cech.alternatingCechTotalInclusion`: its flip, totalized — the natural map
  `Tot(Č_alt(𝒰, F^•)) ⟶ Tot(Č(𝒰, F^•))`.

## Main results

* `Stacks.Cech.cechComplexFunctor_map_f_comp_cechπ`: a morphism of presheaves acts on
  Mathlib's Čech complex componentwise, in the spelling `Stacks.Cech.cechπ` of the
  projections.
* `Stacks.Cech.alternatingCochainMap_comp_inclusion_f`: the naturality square of the
  canonical inclusion, degreewise.
* `Stacks.Cech.quasiIso_alternatingCechTotalInclusion_app`: for a complex of abelian
  presheaves vanishing in low degrees, the totalized comparison is a quasi-isomorphism.

## Implementation notes

The naturality square is checked on components: both sides are morphisms into the degreewise
product of Mathlib's Čech complex, so `Stacks.Cech.cechπ_hom_ext` reduces the equation to one
component per tuple of indices, and each component is an equation between morphisms of abelian
groups which on a section `s` says that `a` applied to the value of `s` is the value of `a`
applied to `s`. No transport of the alternating condition across the comparison isomorphism
is needed, and in particular no reducibility option: the alternating subgroup enters only
through `AddSubgroup.subtype`, and the component equations are closed pointwise on sections.

The coefficient universe of the naturality statement is `max v w` for an index type
`I : Type v`, as in `StacksFrontier.Topology.Sheaves.Cohomology.Cech.ComplexComparison`: the
products occurring in Mathlib's Čech complex are indexed by the tuples `Fin (p + 1) → I`, so
the ambient universe of abelian groups must contain the index universe. The totalization is
stated at `w := v`, because `Stacks.Cech.cechTotalComplexFunctor` takes the index universe and
the coefficient universe to be the same.

The two bicomplexes are assembled by `Functor.whiskerRight` rather than by horizontal
composition with an identity, so that the degreewise formula
`Stacks.Cech.cechBicomplexRowsMap_app_f` holds by `rfl` and no `Category.id_comp` has to be
rewritten underneath a type that mentions `Functor.mapHomologicalComplex`.

The quasi-isomorphy is proved on the bicomplex with the Čech degree *second*, where the
columns in the sense of [Stacks, Tag 0133] are the Čech complexes of the terms of `F^•`, and
then transported to the flip along `HomologicalComplex₂.totalFlipIso`. Its hypothesis that
`F^•` vanishes below some degree is a genuine mathematical input; see the docstring of
`Stacks.Cech.quasiIso_alternatingCechTotalInclusion_app`.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace Stacks.Cech

open CechCochains

variable {X : TopCat.{u}} {I : Type v} (U : I → Opens X)

section Naturality

variable {F G : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max v w}}

/-- A morphism of presheaves acts on Mathlib's Čech complex componentwise: in every degree,
the induced map followed by the projection indexed by a tuple is the projection followed by
the value of the morphism on the corresponding intersection. -/
private theorem cechComplexFunctor_map_f_comp_π (a : F ⟶ G) (p : ℕ) (x : Fin (p + 1) → I) :
    ((CategoryTheory.cechComplexFunctor U).map a).f p ≫
        _root_.Stacks.CategoryTheory.CechComplex.π U G p x =
      _root_.Stacks.CategoryTheory.CechComplex.π U F p x ≫
        a.app (op (_root_.Stacks.CategoryTheory.CechComplex.inter U x)) :=
  limMap_π _ _

/-- A morphism of presheaves acts on Mathlib's Čech complex componentwise, written with the
projections `Stacks.Cech.cechπ` of the explicit model. -/
theorem cechComplexFunctor_map_f_comp_cechπ (a : F ⟶ G) (p : ℕ) (x : Fin (p + 1) → I) :
    ((CategoryTheory.cechComplexFunctor U).map a).f p ≫ cechπ U G p x =
      cechπ U F p x ≫ a.app (op (inter U x)) := by
  rw [cechπ_eq, cechπ_eq, ← Category.assoc, cechComplexFunctor_map_f_comp_π,
    Category.assoc, Category.assoc]
  simp only [interSectionsIso, Functor.mapIso_hom]
  exact congrArg (_root_.Stacks.CategoryTheory.CechComplex.π U F p x ≫ ·)
    (a.naturality _).symm

/-- **The naturality square of the canonical inclusion, degreewise.** In every degree, the
action of a morphism of presheaves on alternating cochains followed by the inclusion into
Mathlib's Čech complex is the inclusion followed by the action on Mathlib's Čech complex. -/
theorem alternatingCochainMap_comp_inclusion_f (a : F ⟶ G) (p : ℕ) :
    alternatingCochainMap U a p ≫ (alternatingCechInclusionToCechComplexFunctor U G).f p =
      (alternatingCechInclusionToCechComplexFunctor U F).f p ≫
        ((CategoryTheory.cechComplexFunctor U).map a).f p := by
  refine cechπ_hom_ext U G fun y ↦ ?_
  have key (H : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max v w}) :
      (alternatingCechInclusionToCechComplexFunctor U H).f p ≫ cechπ U H p y =
        AddCommGrpCat.ofHom (alternatingSubgroup U H p).subtype ≫ cochainEval U H p y := by
    rw [alternatingCechInclusionToCechComplexFunctor_f, Category.assoc,
      cechComplexObjIso_hom_comp_cechπ_eval]
  rw [Category.assoc, Category.assoc, key, cechComplexFunctor_map_f_comp_cechπ,
    reassoc_of% (key F)]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  rfl

end Naturality

/-- **Stacks 01FH, naturally in the coefficient presheaf.** The canonical inclusion of the
alternating Čech complex into Mathlib's Čech complex is a natural transformation of functors
of the coefficient presheaf. -/
noncomputable def alternatingCechInclusionNatTrans :
    alternatingCechComplexFunctor U ⟶
      CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{max v w}) U where
  app F := alternatingCechInclusionToCechComplexFunctor U F
  naturality _ _ a :=
    HomologicalComplex.Hom.ext (funext fun p ↦ alternatingCochainMap_comp_inclusion_f U a p)

/-- The component of `Stacks.Cech.alternatingCechInclusionNatTrans` at a presheaf `F` is the
canonical inclusion of the alternating Čech complex of `F` into Mathlib's Čech complex. -/
@[simp]
theorem alternatingCechInclusionNatTrans_app
    (F : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{max v w}) :
    (alternatingCechInclusionNatTrans U).app F =
      alternatingCechInclusionToCechComplexFunctor U F :=
  rfl

section Total

/-- The map of Čech bicomplexes underlying `Stacks.Cech.alternatingCechTotalInclusion`, with
the Čech degree placed *second*: in each degree of the complex of coefficients it is the
canonical inclusion of Stacks 01FH, extended by zero to integer Čech degrees. -/
noncomputable def cechBicomplexRowsMap :
    (alternatingCechComplexFunctor.{u, v, v} U ⋙
        ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ) ⟶
      (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U ⋙
        ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatTrans.mapHomologicalComplex
    (Functor.whiskerRight (alternatingCechInclusionNatTrans.{u, v, v} U)
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}))
    (ComplexShape.up ℤ)

/-- In degree `q` of the complex of coefficients, `Stacks.Cech.cechBicomplexRowsMap` is the
canonical inclusion for the presheaf `K.X q`, extended to integer Čech degrees. -/
@[simp]
theorem cechBicomplexRowsMap_app_f
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) (q : ℤ) :
    ((cechBicomplexRowsMap U).app K).f q =
      (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{v}).map
        (alternatingCechInclusionToCechComplexFunctor U (K.X q)) :=
  rfl

/-- **The totalized alternating Čech comparison.** The natural map
`Tot(Č_alt(𝒰, F^•)) ⟶ Tot(Č(𝒰, F^•))` obtained by applying the alternating Čech comparison
degreewise to a complex of abelian presheaves, flipping the two gradings so that the Čech
degree comes first, and totalizing. -/
noncomputable def alternatingCechTotalInclusion :
    alternatingCechTotalComplexFunctor U ⟶ cechTotalComplexFunctor U :=
  Functor.whiskerRight
    (Functor.whiskerRight (cechBicomplexRowsMap U)
      (HomologicalComplex₂.flipFunctor AddCommGrpCat.{v}
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)))
    (HomologicalComplex₂.totalFunctor AddCommGrpCat.{v}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The totalized comparison at a complex `K` is the total complex of the flip of
`Stacks.Cech.cechBicomplexRowsMap`. -/
theorem alternatingCechTotalInclusion_app
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) :
    (alternatingCechTotalInclusion U).app K =
      HomologicalComplex₂.total.map
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{v}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map ((cechBicomplexRowsMap U).app K))
        (ComplexShape.up ℤ) :=
  rfl

section QuasiIso

/-- A Čech bicomplex of a complex of presheaves vanishes in negative Čech degrees. -/
private theorem isZero_rows_X_X
    (W : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex AddCommGrpCat.{v} ℕ)
    [W.PreservesZeroMorphisms]
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) (q p : ℤ) (hp : p < 0) :
    IsZero ((((((W ⋙ ComplexShape.embeddingUpNat.extendFunctor
      AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X q).X p)) := by
  show IsZero (((W.obj (K.X q)).extend ComplexShape.embeddingUpNat).X p)
  refine HomologicalComplex.isZero_extend_X _ _ p fun i hi ↦ ?_
  have hi' : (i : ℤ) = p := hi
  omega

/-- Where the complex of coefficients vanishes, so does its Čech bicomplex. -/
private theorem isZero_rows_X
    (W : ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ⥤ CochainComplex AddCommGrpCat.{v} ℕ)
    [W.PreservesZeroMorphisms]
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) (q : ℤ) (hq : IsZero (K.X q)) :
    IsZero ((((W ⋙ ComplexShape.embeddingUpNat.extendFunctor
      AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X q) := by
  show IsZero ((W ⋙ ComplexShape.embeddingUpNat.extendFunctor
    AddCommGrpCat.{v}).obj (K.X q))
  exact Functor.map_isZero _ hq

variable [LinearOrder I]

/-- In every degree of the complex of coefficients the Čech comparison is a
quasi-isomorphism, by Stacks 01FM. -/
private theorem quasiIso_cechBicomplexRowsMap_app_f
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) (q : ℤ) :
    QuasiIso (((cechBicomplexRowsMap U).app K).f q) := by
  have h : QuasiIso (alternatingCechInclusionToCechComplexFunctor U (K.X q)) :=
    quasiIso_alternatingCechInclusion_comp U (K.X q)
  exact inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (alternatingCechInclusionToCechComplexFunctor U (K.X q))
      ComplexShape.embeddingUpNat))

/-- **The totalized alternating Čech comparison of a complex of abelian presheaves that
vanishes in low degrees is a quasi-isomorphism.** The rows of the two Čech bicomplexes are the
Čech complexes of the terms of `K`, and the comparison is a homotopy equivalence on each of
them by Stacks 01FM; [Stacks, Tag 0133] passes that to the total complexes.

The hypothesis `hK` is a genuine mathematical input and not an artefact: it is the convergence
condition of [Stacks, Tag 0133]. Without it the antidiagonals of the Čech bicomplex carry
infinitely many nonzero terms, and the comparison of total complexes is not controlled by the
comparison of the rows. -/
theorem quasiIso_alternatingCechTotalInclusion_app
    (K : CochainComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{v}) ℤ) (a : ℤ)
    (hK : ∀ q : ℤ, q < a → IsZero (K.X q)) :
    QuasiIso ((alternatingCechTotalInclusion U).app K) := by
  have hrows := StacksDraft.TotalComplexQuasiIso.quasiIso_total_map
    ((cechBicomplexRowsMap U).app K) a
    (fun q p hp ↦ isZero_rows_X_X (alternatingCechComplexFunctor.{u, v, v} U) K q p hp)
    (fun q hq ↦ isZero_rows_X (alternatingCechComplexFunctor.{u, v, v} U) K q (hK q hq))
    (fun q p hp ↦ isZero_rows_X_X
      (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U) K q p hp)
    (fun q hq ↦ isZero_rows_X
      (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U) K q (hK q hq))
    (quasiIso_cechBicomplexRowsMap_app_f U K)
  have hnat := StacksDraft.TotalComplexQuasiIso.totalFlipIso_naturality
    ((cechBicomplexRowsMap U).app K)
  rw [alternatingCechTotalInclusion_app]
  have hcomp : QuasiIso (HomologicalComplex₂.total.map
      (StacksDraft.TotalComplexQuasiIso.flipHom ((cechBicomplexRowsMap U).app K))
      (ComplexShape.up ℤ) ≫
      (HomologicalComplex₂.totalFlipIso
        (((CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U ⋙
          ComplexShape.embeddingUpNat.extendFunctor
            AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (ComplexShape.up ℤ)).hom) := by
    rw [hnat]
    infer_instance
  have hiso : QuasiIso (HomologicalComplex₂.totalFlipIso
      (((CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{v}) U ⋙
        ComplexShape.embeddingUpNat.extendFunctor
          AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (ComplexShape.up ℤ)).hom := inferInstance
  exact quasiIso_of_comp_right (hφ := hiso) (hφφ' := hcomp) _ _

end QuasiIso

end Total

end Stacks.Cech

end

module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import StacksFrontier.Homology.HomologyColimit

/-!
# Homology of a diagram of short complexes

Taking homology of a diagram of short complexes termwise agrees with taking the homology of the
corresponding short complex of diagrams. The two descriptions are exchanged by
`CategoryTheory.ShortComplex.FunctorEquivalence`, and the comparison is `mapHomologyIso` at each
evaluation functor.

The statement mentions only an abelian category and an index category, so it is collected here
rather than restated by each development that needs it.

## Main results

The comparison isomorphism itself is `Stacks.HomologyColimit.compHomologyFunctorIso`; this file
records the colimit-preservation statements it yields.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology

universe v u

/-- For every degree `i`, the functor sending a `ℤ`-indexed cochain complex to its short complex
in degree `i` preserves colimits of shape `J`. -/
public lemma preservesColimitsOfShape_shortComplexFunctor
    {A : Type v} [Category.{u} A] [HasZeroMorphisms A] [Preadditive A]
    {J : Type*} [Category J]
    [HasColimitsOfShape J A] (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) i) :=
  ⟨fun {_} => ⟨fun hs => ⟨by
    refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_ <;>
      exact isColimitOfPreserves (HomologicalComplex.eval A (ComplexShape.up ℤ) _) hs⟩⟩⟩

/-- In an abelian category in which colimits of shape `J` exist and are exact, the homology
functor on short complexes preserves colimits of shape `J`. -/
public lemma preservesColimitsOfShape_shortComplex_homologyFunctor
    {A : Type v} [Category.{u} A] [Abelian A]
    {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor A) := by
  refine ⟨fun {E} => preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone E) ?_⟩
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (Stacks.HomologyColimit.compHomologyFunctorIso E)
      (colimit.cocone ((ShortComplex.FunctorEquivalence.inverse J A).obj E).homology)).symm
      (colimit.isColimit _))
    (Cocone.ext (((ShortComplex.FunctorEquivalence.inverse J A).obj E).mapHomologyIso
      (colim : (J ⥤ A) ⥤ A)).symm (fun j => ?_))
  set T := (ShortComplex.FunctorEquivalence.inverse J A).obj E with hT
  let ι : (evaluation J A).obj j ⟶ (colim : (J ⥤ A) ⥤ A) :=
    { app := fun X => colimit.ι X j
      naturality := fun X Y f => by simp }
  have key : ι.app T.homology = (T.mapHomologyIso ((evaluation J A).obj j)).inv ≫
      ShortComplex.homologyMap (T.mapNatTrans ι) ≫ (T.mapHomologyIso colim).hom :=
    NatTrans.app_homology ι T
  change ((T.mapHomologyIso ((evaluation J A).obj j)).hom ≫ ι.app T.homology) ≫
      (T.mapHomologyIso (colim : (J ⥤ A) ⥤ A)).inv
    = ShortComplex.homologyMap (T.mapNatTrans ι)
  rw [key]
  simp

/-! ### Coproducts split along a sum of index types

These mention only a category with the relevant (co)limits, so they are collected here rather
than restated by each resolution that needs them. -/

/-- A coproduct of an empty family is initial. -/
public noncomputable def isInitial_coproduct_of_isEmpty {C : Type*} [Category C]
    {I : Type*} [IsEmpty I] (F : I → C) [HasCoproduct F] : IsInitial (∐ F) := by
  refine IsInitial.ofUniqueHom (fun _ ↦ Sigma.desc (fun i ↦ isEmptyElim i)) ?_
  intro Y f
  exact colimit.hom_ext (fun i ↦ isEmptyElim i.as)

/-- A coproduct indexed by a sum type is the biproduct of its two partial coproducts. -/
public noncomputable def coproductSumIso {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasBinaryBiproducts C] {α β : Type*} (H : α ⊕ β → C) [HasCoproduct H]
    [HasCoproduct (fun a ↦ H (Sum.inl a))] [HasCoproduct (fun b ↦ H (Sum.inr b))] :
    (∐ H) ≅ (∐ fun a ↦ H (Sum.inl a)) ⊞ (∐ fun b ↦ H (Sum.inr b)) := by
  let F : α → C := fun a ↦ H (Sum.inl a)
  let G : β → C := fun b ↦ H (Sum.inr b)
  let c : Cofan H := Cofan.mk ((∐ F) ⊞ (∐ G)) (fun
    | Sum.inl a => Sigma.ι F a ≫ biprod.inl
    | Sum.inr b => Sigma.ι G b ≫ biprod.inr)
  have hc : IsColimit c := by
    refine Cofan.IsColimit.mk c (fun s ↦ biprod.desc
      (Sigma.desc fun a ↦ (show F a ⟶ s.pt from s.inj (Sum.inl a)))
      (Sigma.desc fun b ↦ (show G b ⟶ s.pt from s.inj (Sum.inr b)))) ?_ ?_
    · intro s j
      cases j with
      | inl a =>
          change (Sigma.ι F a ≫ biprod.inl) ≫ _ = _
          rw [Category.assoc, biprod.inl_desc, Sigma.ι_comp_desc]
      | inr b =>
          change (Sigma.ι G b ≫ biprod.inr) ≫ _ = _
          rw [Category.assoc, biprod.inr_desc, Sigma.ι_comp_desc]
    · intro s m hm
      refine biprod.hom_ext' _ _ (colimit.hom_ext fun a ↦ ?_) (colimit.hom_ext fun b ↦ ?_)
      · have h := hm (Sum.inl a.as)
        change (Sigma.ι F a.as ≫ biprod.inl) ≫ m = s.inj (Sum.inl a.as) at h
        change Sigma.ι F a.as ≫ biprod.inl ≫ m = _
        rw [biprod.inl_desc, Sigma.ι_comp_desc]
        simpa only [Category.assoc] using h
      · have h := hm (Sum.inr b.as)
        change (Sigma.ι G b.as ≫ biprod.inr) ≫ m = s.inj (Sum.inr b.as) at h
        change Sigma.ι G b.as ≫ biprod.inr ≫ m = _
        rw [biprod.inr_desc, Sigma.ι_comp_desc]
        simpa only [Category.assoc] using h
  exact IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc

/-- The cokernel of `biprod.inl : M ⟶ M ⊞ T` is `T`: the biproduct splits it. -/
public noncomputable def cokernelInlIso {C : Type*} [Category C] [Abelian C] (M T : C) :
    cokernel (biprod.inl : M ⟶ M ⊞ T) ≅ T := by
  let S : ShortComplex C := ShortComplex.mk (biprod.inl : M ⟶ M ⊞ T) biprod.snd (by simp)
  let s : S.Splitting := { r := biprod.fst, s := biprod.inr, id := by simp [S] }
  exact (cokernelIsCokernel S.f).coconePointUniqueUpToIso s.gIsCokernel

end Stacks.Cohomology

end

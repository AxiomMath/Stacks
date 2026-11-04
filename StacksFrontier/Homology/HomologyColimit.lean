module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# The homology functor preserves colimits of a shape with exact colimits

In an abelian category with colimits of shape `J` which are exact, taking homology commutes with
those colimits: both for short complexes and, in each degree, for homological complexes of any
shape.

## Main results

* `Stacks.HomologyColimit.preservesColimitsOfShape_shortComplex_homologyFunctor`: the homology
  functor on short complexes preserves colimits of shape `J`.
* `Stacks.HomologyColimit.preservesColimitsOfShape_shortComplexFunctor`: in a category with zero
  morphisms, the functor taking a homological complex to its short complex in a degree preserves
  colimits of shape `J`.
* `Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor`: the degree-`i` homology
  functor on complexes of any shape `c` preserves colimits of shape `J`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v

namespace Stacks.HomologyColimit

variable {A : Type v} [Category.{w} A]

/-- Taking the short complex of a homological complex in a degree preserves colimits of
shape `J`. -/
lemma preservesColimitsOfShape_shortComplexFunctor [HasZeroMorphisms A] {J : Type*} [Category J]
    [HasColimitsOfShape J A] {ι : Type*} (c : ComplexShape ι) (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.shortComplexFunctor A c i) :=
  ⟨fun {_} ↦ ⟨fun hs ↦
    have h := fun k ↦ isColimitOfPreserves (HomologicalComplex.eval A c k) hs
    ⟨ShortComplex.isColimitOfIsColimitπ _ (h _) (h _) (h _)⟩⟩⟩

section

variable [Abelian A]

/-- For a diagram `E` of short complexes, the diagram `E ⋙ ShortComplex.homologyFunctor A` of
homologies is isomorphic to the homology of the short complex of diagrams corresponding to `E`. -/
def compHomologyFunctorIso {J : Type*} [Category J] (E : J ⥤ ShortComplex A) :
    E ⋙ ShortComplex.homologyFunctor A ≅
      ((ShortComplex.FunctorEquivalence.inverse J A).obj E).homology :=
  NatIso.ofComponents
    (fun j ↦ ((ShortComplex.FunctorEquivalence.inverse J A).obj E).mapHomologyIso
      ((evaluation J A).obj j))
    (fun {j j'} φ ↦ by
      change ShortComplex.homologyMap
            (((ShortComplex.FunctorEquivalence.inverse J A).obj E).mapNatTrans
              ((evaluation J A).map φ)) ≫
          (((ShortComplex.FunctorEquivalence.inverse J A).obj E).mapHomologyIso
            ((evaluation J A).obj j')).hom
        = (((ShortComplex.FunctorEquivalence.inverse J A).obj E).mapHomologyIso
            ((evaluation J A).obj j)).hom ≫
          ((evaluation J A).map φ).app
            ((ShortComplex.FunctorEquivalence.inverse J A).obj E).homology
      rw [NatTrans.app_homology, Iso.hom_inv_id_assoc])

/-- **The homology functor on short complexes preserves colimits of a shape whose colimits are
exact.** -/
lemma preservesColimitsOfShape_shortComplex_homologyFunctor {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor A) := by
  refine ⟨fun {E} => preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone E) ?_⟩
  set T := (ShortComplex.FunctorEquivalence.inverse J A).obj E
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (compHomologyFunctorIso E)
      (colimit.cocone T.homology)).symm (colimit.isColimit _))
    (Cocone.ext (T.mapHomologyIso (colim : (J ⥤ A) ⥤ A)).symm (fun j ↦ ?_))
  let ι : (evaluation J A).obj j ⟶ (colim : (J ⥤ A) ⥤ A) :=
    { app := fun X ↦ colimit.ι X j
      naturality := fun X Y f ↦ by simp }
  change ((T.mapHomologyIso ((evaluation J A).obj j)).hom ≫ ι.app T.homology) ≫
      (T.mapHomologyIso (colim : (J ⥤ A) ⥤ A)).inv
    = ShortComplex.homologyMap (T.mapNatTrans ι)
  simp [NatTrans.app_homology ι T]

/-- The degree-`i` homology of a homological complex commutes with colimits of shape `J` when
those are exact. -/
lemma preservesColimitsOfShape_homologyFunctor {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {ι : Type*} (c : ComplexShape ι)
    (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor A c i) :=
  have := preservesColimitsOfShape_shortComplexFunctor (A := A) (J := J) c i
  have := preservesColimitsOfShape_shortComplex_homologyFunctor (A := A) (J := J)
  preservesColimitsOfShape_of_natIso (HomologicalComplex.homologyFunctorIso A c i).symm

end

end Stacks.HomologyColimit

end

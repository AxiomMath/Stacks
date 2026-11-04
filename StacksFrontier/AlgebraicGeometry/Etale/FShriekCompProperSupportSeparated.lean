module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekCompProperSupportStalk

/-!
# The map `c'` of Stacks 0F79 when the first morphism is separated

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site with `f` and `f ≫ g` locally
quasi-finite and `g` separated and locally of finite type. If `f` is separated as well, the map
`c' : (f ≫ g)_! F ⟶ g_!(f_! F)` of Stacks 0F79 is the identification `(g ∘ f)_! = g_! ∘ f_!` of
proper-support direct images of Stacks 0F50, read through the identifications of Stacks 0F6N of
the finite-support models of `(f ≫ g)_!` and `f_!` with the proper-support models. This is the
input to part (c) of Stacks 0F79.

## Main results

* `AlgebraicGeometry.SmallEtale.sepCompShriekMap_eq_of_isSeparated` — `c'` is the
  identification of Stacks 0F50 when `f` is separated.

## Implementation notes

Both sides satisfy the germ formula `AlgebraicGeometry.SmallEtale.IsSepCompMap`, which
determines a morphism into `g_!(f_! F)` (`AlgebraicGeometry.SmallEtale.eq_of_isSepCompMap`). For
the identification of Stacks 0F50 the germ formula is the computation of
`AlgebraicGeometry.SmallEtale.hasCompShriekStalks_separatedCompShriekMap`: a section with proper
support has, at a point of a geometric fibre, the germ of the section itself, and the two
readings of a section of `F` over `W ×_Z X` and over `(W ×_Z Y) ×_Y X` have the same germs.

## References

* [Stacks Project, Tag 0F79](https://stacks.math.columbia.edu/tag/0F79)
* [Stacks Project, Tag 0F50](https://stacks.math.columbia.edu/tag/0F50)
* [Stacks Project, Tag 0F6N](https://stacks.math.columbia.edu/tag/0F6N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsSeparated (B.inclusion.map g)] [LocallyOfFiniteType (B.inclusion.map g)]
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  [LocallyQuasiFinite (B.inclusion.map (f ≫ g))] [IsSeparated (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- The identification of Stacks 0F50, read through the identifications of Stacks 0F6N,
satisfies the germ formula of Stacks 0F79. -/
public theorem isSepCompMap_of_isSeparated :
    letI := isSeparated_map_comp B f g
    IsSepCompMap B f g F
      ((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).hom.app F ≫
        (properSupportFunctor_compIso B f g).val.inv.app F ≫
        (properSupportFunctor.{u, max (u + 1) v} B g).map
          ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F)) := by
  let := isSeparated_map_comp B f g
  intro s W w σ y x
  let ρ := ((fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).hom.app F).hom.app (op W) σ
  let ρ₂ := ((properSupportFunctor_compIso B f g).val.inv.app F).hom.app (op W) ρ
  have hm := properSupportSection_map.{u, max (u + 1) v} B g
    ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F) W ρ₂
  have h1 := fShriekStalkIso_germ_fShriekFunctorIsoProperSupport_inv.{u, v} B f F
    (y.toGeometricPoint B g s) (baseChange B g W) (fiberPointElement B g s W w y)
    (properSupportSection.{u, max (u + 1) v} B g _ W ρ₂) x
  have h2 := properSupportSection_properSupportFunctor_compIso_inv'.{u, max (u + 1) v}
    B f g F W ρ
  have h3 := etaleGerm_map B X.obj X.property
    ((compFiberPointOf B f g s y x).toGeometricPoint B (f ≫ g) s) F.obj
    ((smallEtaleBaseChange_compIso B X Y Z f g).val.hom.app W) _ _
    (fiberPointElement_compIso B f g s W w y x) (properSupportSection B (f ≫ g) F W ρ)
  have h4 := etaleGerm_properSupportSection_fShriekFunctorIsoProperSupport_hom.{u, v} B (f ≫ g)
    F s W w (compFiberPointOf B f g s y x) σ
  refine (congrArg (fun z => ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
    (etaleGerm B Y.obj Y.property (y.toGeometricPoint B g s)
      ((fShriekFunctor.{u, v} B f).obj F).obj (baseChange B g W)
      (fiberPointElement B g s W w y) z) : fiberStalks.{u, max (u + 1) v} B f _ F) x) hm).trans ?_
  refine h1.trans ?_
  refine (congrArg (etaleGerm B X.obj X.property _ F.obj _ _) h2).trans ?_
  exact h3.trans h4

/-- **The map `c'` of Stacks 0F79 for separated `f`.** If `f` is separated as well, the map
`c' : (f ≫ g)_! F ⟶ g_!(f_! F)` is the identification `(g ∘ f)_! = g_! ∘ f_!` of proper-support
direct images of Stacks 0F50, read through the identifications of Stacks 0F6N of `(f ≫ g)_!` and
`f_!` with their proper-support models. -/
public theorem sepCompShriekMap_eq_of_isSeparated :
    letI := isSeparated_map_comp B f g
    sepCompShriekMap B f g F =
      (fShriekFunctorIsoProperSupport.{u, v} B (f ≫ g)).hom.app F ≫
        (properSupportFunctor_compIso B f g).val.inv.app F ≫
        (properSupportFunctor.{u, max (u + 1) v} B g).map
          ((fShriekFunctorIsoProperSupport.{u, v} B f).inv.app F) :=
  let := isSeparated_map_comp B f g
  eq_of_isSepCompMap B f g F (isSepCompMap_sepCompShriekMap B f g F)
    (isSepCompMap_of_isSeparated B f g F)

end AlgebraicGeometry.SmallEtale

end

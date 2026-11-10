module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionFiber
import StacksCore.Tactic.StacksAttribute

/-!
# The counit of extension by zero on stalks

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S`, let `x̄` be a
geometric point of `Y` and let `G` be an abelian sheaf on the small étale site of `Y`. The counit
of the extension-by-zero adjunction is a map `f_!(G|_X) ⟶ G`. The stalk at `x̄` of its source is
the direct sum, over the lifts `t` of `x̄` to `X`, of the stalks of `G|_X` at those lifts, and each
of those stalks is the stalk of `G` at `x̄`. Under these identifications the stalk of the counit
is the fold map: the map out of the direct sum whose component at every lift is the
identification of the stalk of `G|_X` at that lift with the stalk of `G` at `x̄`.

## Main results

* `AlgebraicGeometry.Space.EtaleShriekStalk.liftedStalkι_stalkExtensionByZeroIso_inv_counit`:
  the component at one lift of the stalk of the counit is the identification of the stalk of
  `G|_X` at that lift with the stalk of `G` at `x̄`.
* `AlgebraicGeometry.Space.EtaleShriekStalk.stalkExtensionByZeroIso_inv_counit`: the stalk of
  the counit is the fold map over the lifts.
* `AlgebraicGeometry.Space.EtaleShriekStalk.isIso_sheafFiber_counit_of_unique`: at a geometric
  point with exactly one lift the stalk of the counit is an isomorphism.
* `AlgebraicGeometry.Space.EtaleShriekStalk.isZero_sheafFiber_restriction_shriek_of_isEmpty`:
  at a geometric point with no lift the source of the counit has vanishing stalk.

## References

* [Stacks Project, Tag 08GT](https://stacks.math.columbia.edu/tag/08GT)
* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace EtaleShriekStalk

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
  (x : GeometricPoint B S hS Y.1)

section Presheaf

variable (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})

/-- The decomposition of the stalk of the extension by zero of `F` as the direct sum of the stalks
of `F` at the lifts, with its source the fibre of the presheaf underlying the extension by zero. -/
private def pStalkIso :
    (etaleSitePoint B S hS Y.1 x Y.2).presheafFiber.obj
        ((abelianEtaleExtensionByZero B S hS f hf).obj F).obj ≅
      ∐ fun t : GeometricPointLift B S hS f.hom x =>
        (liftSitePoint B S hS f t).sheafFiber.obj F :=
  stalkExtensionByZeroIso B S hS f hf x F

/-- The inclusion of the summand of one lift, with its source spelled as the fibre of the
presheaf underlying the sheaf. -/
private def pι (t : GeometricPointLift B S hS f.hom x) :
    (liftSitePoint B S hS f t).presheafFiber.obj F.obj ⟶
      ∐ fun s : GeometricPointLift B S hS f.hom x =>
        (liftSitePoint B S hS f s).sheafFiber.obj F :=
  Sigma.ι (fun s : GeometricPointLift B S hS f.hom x =>
    (liftSitePoint B S hS f s).sheafFiber.obj F) t

/-- The decomposition `pStalkIso` sends the germ of a section over `W`, read in the extension by
zero through the unit, to its germ at the induced lift in the corresponding summand. -/
private theorem pStalkIso_germ (W : SmallEtale B S hS X.1)
    (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    extensionByZeroUnitApp B S hS f hf F W ≫
        (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
            ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w)
            ((abelianEtaleExtensionByZero B S hS f hf).obj F).obj ≫
          (pStalkIso B S hS f hf x F).hom =
      (liftSitePoint B S hS f t).toPresheafFiber W w F.obj ≫ pι B S hS f x F t :=
  stalkExtensionByZeroIso_germ B S hS f hf x F W t w

/-- The germ at a lift, pushed into the fibre of the extension by zero through the inverse of
`pStalkIso`, is the germ over the composite chart of that section read in the extension by zero
through the unit. -/
private theorem pι_pStalkIso_inv (W : SmallEtale B S hS X.1)
    (t : GeometricPointLift B S hS f.hom x)
    (w : (liftSitePoint B S hS f t).fiber.obj W) :
    ((liftSitePoint B S hS f t).toPresheafFiber W w F.obj ≫ pι B S hS f x F t) ≫
        (pStalkIso B S hS f hf x F).inv =
      extensionByZeroUnitApp B S hS f hf F W ≫
        (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
          ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w)
          ((abelianEtaleExtensionByZero B S hS f hf).obj F).obj := by
  rw [← pStalkIso_germ B S hS f hf x F W t w, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end Presheaf

section Counit

variable (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u})

/-- The identification of the stalk of `G|_X` at a lift with the stalk of `G` at `x̄`, between
the fibres of the underlying presheaves. -/
private def pRestr (t : GeometricPointLift B S hS f.hom x) :
    (liftSitePoint B S hS f t).presheafFiber.obj
        ((abelianEtaleRestriction B S hS f hf).obj G).obj ⟶
      (etaleSitePoint B S hS Y.1 x Y.2).presheafFiber.obj G.obj :=
  (restrictionSheafFiberIso B S hS f hf t).hom.app G

/-- `pRestr` sends the germ at a lift of a section of `G|_X` over `W` to the germ at `x̄` of the
same section over the composite chart. -/
private theorem pRestr_germ (t : GeometricPointLift B S hS f.hom x)
    (W : SmallEtale B S hS X.1) (w : (liftSitePoint B S hS f t).fiber.obj W) :
    (liftSitePoint B S hS f t).toPresheafFiber W w
          ((abelianEtaleRestriction B S hS f hf).obj G).obj ≫
        pRestr B S hS f hf x G t =
      (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
        ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w) G.obj :=
  restrictionSheafFiberIso_toPresheafFiber B S hS f hf t G W w

/-- The component at one lift of the fibre of the counit, spelled on the presheaf side. -/
private theorem pι_pStalkIsoC_inv_counit (t : GeometricPointLift B S hS f.hom x) :
    pι B S hS f x ((abelianEtaleRestriction B S hS f hf).obj G) t ≫
        (pStalkIso B S hS f hf x ((abelianEtaleRestriction B S hS f hf).obj G)).inv ≫
          (etaleSitePoint B S hS Y.1 x Y.2).presheafFiber.map
            ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G).hom =
      pRestr B S hS f hf x G t := by
  apply (liftSitePoint B S hS f t).presheafFiber_hom_ext
  intro W w
  have h3 : extensionByZeroUnitApp B S hS f hf
        ((abelianEtaleRestriction B S hS f hf).obj G) W ≫
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G).hom.app
        (op ((smallEtalePostcomp B S hS f hf).obj W)) = 𝟙 _ :=
    congrArg (fun k : (abelianEtaleRestriction B S hS f hf).obj G ⟶
        (abelianEtaleRestriction B S hS f hf).obj G => k.hom.app (op W))
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).right_triangle_components (Y := G))
  have hnat : (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
          ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w)
          ((abelianEtaleExtensionByZero B S hS f hf).obj
            ((abelianEtaleRestriction B S hS f hf).obj G)).obj ≫
        (etaleSitePoint B S hS Y.1 x Y.2).presheafFiber.map
          ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G).hom =
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G).hom.app
          (op ((smallEtalePostcomp B S hS f hf).obj W)) ≫
        (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
          ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w) G.obj :=
    (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber_naturality
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G).hom
      ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w)
  have hfin := congrArg
    (fun m : ((abelianEtaleRestriction B S hS f hf).obj G).obj.obj (op W) ⟶
        ((abelianEtaleRestriction B S hS f hf).obj G).obj.obj (op W) =>
      m ≫ (etaleSitePoint B S hS Y.1 x Y.2).toPresheafFiber
        ((smallEtalePostcomp B S hS f hf).obj W) (pushLift B S hS f hf W t w) G.obj) h3
  rw [pRestr_germ, ← Category.assoc, ← Category.assoc, pι_pStalkIso_inv, Category.assoc, hnat]
  exact (Category.assoc _ _ _).symm.trans (hfin.trans (Category.id_comp _))

/-- Under the decomposition of the stalk of `f_!(G|_X)` as the direct sum over the lifts of `x̄`
of the stalks of `G|_X`, the stalk of the counit `f_!(G|_X) ⟶ G` restricts on the summand of a
lift `t` to the identification of the stalk of `G|_X` at `t` with the stalk of `G` at `x̄`. -/
@[stacks 08GU "the counit on one summand of the stalk"]
theorem liftedStalkι_stalkExtensionByZeroIso_inv_counit
    (t : GeometricPointLift B S hS f.hom x) :
    liftedStalkι B S hS f x ((abelianEtaleRestriction B S hS f hf).obj G) t ≫
        (stalkExtensionByZeroIso B S hS f hf x
            ((abelianEtaleRestriction B S hS f hf).obj G)).inv ≫
          (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
            ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G) =
      (restrictionSheafFiberIso B S hS f hf t).hom.app G :=
  pι_pStalkIsoC_inv_counit B S hS f hf x G t

/-- The stalk of the counit of extension by zero is the fold map: under the decomposition of the
stalk of `f_!(G|_X)` as the direct sum over the lifts `t` of `x̄` of the stalks of `G|_X` at
those lifts, and the identification of each of those with the stalk of `G` at `x̄`, the counit
`f_!(G|_X) ⟶ G` becomes the map out of the direct sum whose component at every lift is that
identification. -/
@[stacks 08GU "the counit on stalks"]
theorem stalkExtensionByZeroIso_inv_counit :
    (stalkExtensionByZeroIso B S hS f hf x
          ((abelianEtaleRestriction B S hS f hf).obj G)).inv ≫
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G) =
      Sigma.desc fun t : GeometricPointLift B S hS f.hom x =>
        (restrictionSheafFiberIso B S hS f hf t).hom.app G := by
  refine Sigma.hom_ext _ _ fun t => ?_
  rw [Sigma.ι_comp_desc]
  exact liftedStalkι_stalkExtensionByZeroIso_inv_counit B S hS f hf x G t

end Counit

/-- A coproduct of abelian groups indexed by a type with exactly one element is its single
summand. -/
theorem isIso_sigma_ι_of_unique {I : Type u} [Unique I] (K : I → AddCommGrpCat.{u}) (i : I) :
    IsIso (Sigma.ι K i) := by
  obtain rfl : i = default := Subsingleton.elim i default
  refine ⟨Sigma.desc fun j => eqToHom (congrArg K (Subsingleton.elim j default)), ?_, ?_⟩
  · simp
  · refine Sigma.hom_ext _ _ fun j => ?_
    obtain rfl : j = default := Subsingleton.elim j default
    simp

/-- At a geometric point of `Y` with exactly one lift to `X`, the stalk of the counit of
extension by zero is an isomorphism. -/
theorem isIso_sheafFiber_counit_of_unique
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u})
    [Unique (GeometricPointLift B S hS f.hom x)] :
    IsIso ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
      ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G)) := by
  have h := liftedStalkι_stalkExtensionByZeroIso_inv_counit B S hS f hf x G default
  have h₁ : IsIso (liftedStalkι B S hS f x
      ((abelianEtaleRestriction B S hS f hf).obj G) default) :=
    isIso_sigma_ι_of_unique _ default
  have h₂ : IsIso (liftedStalkι B S hS f x
        ((abelianEtaleRestriction B S hS f hf).obj G) default ≫
      (stalkExtensionByZeroIso B S hS f hf x
          ((abelianEtaleRestriction B S hS f hf).obj G)).inv ≫
        (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
          ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G)) := by
    rw [h]
    infer_instance
  have h₃ : IsIso ((stalkExtensionByZeroIso B S hS f hf x
        ((abelianEtaleRestriction B S hS f hf).obj G)).inv ≫
      (etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.map
        ((abelianEtaleExtensionByZeroAdjunction B S hS f hf).counit.app G)) :=
    IsIso.of_isIso_comp_left (liftedStalkι B S hS f x
      ((abelianEtaleRestriction B S hS f hf).obj G) default) _
  exact IsIso.of_isIso_comp_left (stalkExtensionByZeroIso B S hS f hf x
    ((abelianEtaleRestriction B S hS f hf).obj G)).inv _

/-- At a geometric point of `Y` with no lift to `X`, the stalk of `f_!(G|_X)` vanishes. -/
theorem isZero_sheafFiber_restriction_shriek_of_isEmpty
    (G : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u})
    [IsEmpty (GeometricPointLift B S hS f.hom x)] :
    IsZero ((etaleSitePoint B S hS Y.1 x Y.2).sheafFiber.obj
      ((abelianEtaleExtensionByZero B S hS f hf).obj
        ((abelianEtaleRestriction B S hS f hf).obj G))) :=
  isZero_stalkExtensionByZero_of_isEmpty B S hS f hf x _

end EtaleShriekStalk

end AlgebraicGeometry.Space

end

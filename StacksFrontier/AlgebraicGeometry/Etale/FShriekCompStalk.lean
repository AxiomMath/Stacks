module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekStalkDecomposition

/-!
# The regrouping of the geometric fibre of a composite

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of a big étale site and `s` a geometric point of `Z`.
A point of the geometric fibre of `f ≫ g` over `s` is the same thing as a point `ȳ` of the
geometric fibre of `g` over `s` together with a point of the geometric fibre of `f` over `ȳ`. On
the stalk decompositions of Stacks 0F5F this regrouping is the map

`⊕_{x̄ ↦ s} F_x̄ ⟶ ⊕_{ȳ ↦ s} (f_! F)_ȳ = ⊕_{ȳ ↦ s} ⊕_{x̄ ↦ ȳ} F_x̄`,

which is the behaviour on stalks of the comparison `(f ≫ g)_! ⟶ g_! f_!` of Stacks 0F6T.

## Main definitions

* `AlgebraicGeometry.SmallEtale.compFiberStalksMap` — the regrouping map.

## Main results

* `AlgebraicGeometry.SmallEtale.compFiberStalksMap_apply` — its components.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped DirectSum

universe u v

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
  (s : GeometricPoint Z.obj)

/-- The point of the geometric fibre of `g` below a point of the geometric fibre of `f ≫ g`. -/
public def compFiberPoint (x : GeometricFiberPoint B (f ≫ g) s) : GeometricFiberPoint B g s :=
  ⟨x.1 ≫ B.inclusion.map f, by rw [Category.assoc, ← Functor.map_comp]; exact x.2⟩

/-- A point of the geometric fibre of `f ≫ g`, as a point of the geometric fibre of `f` over the
point below it. -/
public def compFiberPointLift (x : GeometricFiberPoint B (f ≫ g) s) :
    GeometricFiberPoint B f ((compFiberPoint B f g s x).toGeometricPoint B g s) :=
  ⟨x.1, rfl⟩

/-- A point of the geometric fibre of `f` over a point of the geometric fibre of `g`, as a point
of the geometric fibre of `f ≫ g`. -/
public def compFiberPointOf (y : GeometricFiberPoint B g s)
    (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    GeometricFiberPoint B (f ≫ g) s :=
  ⟨x.1, by rw [Functor.map_comp, ← Category.assoc, x.2]; exact y.2⟩

/-- The point below `compFiberPointOf B f g s y x` is `y`. -/
public theorem compFiberPoint_compFiberPointOf (y : GeometricFiberPoint B g s)
    (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    compFiberPoint B f g s (compFiberPointOf B f g s y x) = y :=
  Subtype.ext x.2

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})

/-- **The regrouping of the geometric fibre of a composite** on the stalk decompositions of
Stacks 0F5F: the summand of a point `x̄` of the geometric fibre of `f ≫ g` goes to the summand of
`f(x̄)`, and inside the stalk of `f_! F` there to the summand of `x̄`. -/
public def compFiberStalksMap :
    fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F →+
      fiberStalks.{u, max (u + 1) v} B g s ((fShriekFunctor.{u, v} B f).obj F) :=
  letI := Classical.decEq (GeometricFiberPoint B (f ≫ g) s)
  letI := Classical.decEq (GeometricFiberPoint B g s)
  DirectSum.toAddMonoid fun x =>
    letI := Classical.decEq (GeometricFiberPoint B f
      ((compFiberPoint B f g s x).toGeometricPoint B g s))
    (DirectSum.of (fun y : GeometricFiberPoint B g s =>
        ↑(etaleStalk B Y.obj Y.property (y.toGeometricPoint B g s)
          ((fShriekFunctor.{u, v} B f).obj F).obj)) (compFiberPoint B f g s x)).comp
      ((ConcreteCategory.hom (fShriekStalkIso.{u, v} B f
          ((compFiberPoint B f g s x).toGeometricPoint B g s) F).inv).comp
        (DirectSum.of (fun x' : GeometricFiberPoint B f
            ((compFiberPoint B f g s x).toGeometricPoint B g s) =>
            ↑(etaleStalk B X.obj X.property (x'.toGeometricPoint B f _) F.obj))
            (compFiberPointLift B f g s x)))

/-- **The components of the regrouping.** -/
public theorem compFiberStalksMap_apply (ξ : fiberStalks.{u, max (u + 1) v} B (f ≫ g) s F)
    (y : GeometricFiberPoint B g s) (x : GeometricFiberPoint B f (y.toGeometricPoint B g s)) :
    ((fShriekStalkIso.{u, v} B f (y.toGeometricPoint B g s) F).hom
        ((compFiberStalksMap B f g s F ξ : fiberStalks.{u, max (u + 1) v} B g s _) y) :
          fiberStalks.{u, max (u + 1) v} B f _ F) x =
      ξ (compFiberPointOf B f g s y x) := by
  let := Classical.decEq (GeometricFiberPoint B (f ≫ g) s)
  let := Classical.decEq (GeometricFiberPoint B g s)
  classical
  induction ξ using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]; rfl
  | add a b ha hb =>
    rw [map_add, DirectSum.add_apply, map_add, DirectSum.add_apply, ha, hb]
    rfl
  | of x₀ b =>
    let := Classical.decEq (GeometricFiberPoint B f
      ((compFiberPoint B f g s x₀).toGeometricPoint B g s))
    simp only [compFiberStalksMap, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
    by_cases hy : compFiberPoint B f g s x₀ = y
    · subst hy
      rw [DirectSum.of_eq_same]
      change ((fShriekStalkIso.{u, v} B f _ F).hom ((fShriekStalkIso.{u, v} B f _ F).inv
        (DirectSum.of (fun x' : GeometricFiberPoint B f
          ((compFiberPoint B f g s x₀).toGeometricPoint B g s) =>
          ↑(etaleStalk B X.obj X.property (x'.toGeometricPoint B f _) F.obj))
          (compFiberPointLift B f g s x₀) b)) : fiberStalks.{u, max (u + 1) v} B f _ F) x = _
      rw [Iso.inv_hom_id_apply]
      let b' : ↑(etaleStalk B X.obj X.property ((compFiberPointLift B f g s x₀).toGeometricPoint
          B f ((compFiberPoint B f g s x₀).toGeometricPoint B g s)) F.obj) := b
      by_cases hx : compFiberPointLift B f g s x₀ = x
      · subst hx
        refine (DirectSum.of_eq_same (β := fun x' : GeometricFiberPoint B f
          ((compFiberPoint B f g s x₀).toGeometricPoint B g s) =>
            ↑(etaleStalk B X.obj X.property (x'.toGeometricPoint B f _) F.obj))
          (compFiberPointLift B f g s x₀) b').trans ?_
        exact (DirectSum.of_eq_same (β := fun x : GeometricFiberPoint B (f ≫ g) s =>
          ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) F.obj)) x₀ b).symm
      · refine (DirectSum.of_eq_of_ne (β := fun x' : GeometricFiberPoint B f
          ((compFiberPoint B f g s x₀).toGeometricPoint B g s) =>
            ↑(etaleStalk B X.obj X.property (x'.toGeometricPoint B f _) F.obj))
          (compFiberPointLift B f g s x₀) x b' (Ne.symm hx)).trans ?_
        refine (DirectSum.of_eq_of_ne (β := fun x : GeometricFiberPoint B (f ≫ g) s =>
          ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) F.obj)) x₀
          (compFiberPointOf B f g s _ x) b fun hc => hx ?_).symm
        exact Subtype.ext (congrArg Subtype.val hc).symm
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hy), map_zero, DirectSum.zero_apply]
      refine (DirectSum.of_eq_of_ne (β := fun x : GeometricFiberPoint B (f ≫ g) s =>
          ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B (f ≫ g) s) F.obj)) x₀
          (compFiberPointOf B f g s y x) b fun hc => hy ?_).symm
      rw [← hc]
      exact compFiberPoint_compFiberPointOf B f g s y x

end AlgebraicGeometry.SmallEtale

end

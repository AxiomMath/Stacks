module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.MorphismComposition
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardBaseChangeUnconditional
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories

/-!
# FiniteBaseChangeSiteTransferUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.FiniteBaseChangeSiteTransfer`,
stated as separate declarations beside the ones there: over more general coefficient universes,
or with inputs that are carried there as hypotheses discharged, together with the new results
built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite

universe v' u' u v

namespace AlgebraicGeometry.SmallEtale

section Abstract

end Abstract

section TwoSquares

variable {C₁ C₂ C₃ C₄ C₇ C₈ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₇] [Category* C₈]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {Bo : C₃ ⥤ C₄}

end TwoSquares

section Sections

variable (A : Type u') [Category.{v'} A] {C D : Type*} [Category* C] [Category* D]

end Sections

section Presentations

variable (A : Type u') [Category.{v'} A] (B : BigEtaleSite.{u})

end Presentations

section Mates

variable (B : BigEtaleSite.{u}) (A : Type u') [Category.{v'} A]

variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)

end Mates

section Cube

variable (B : BigEtaleSite.{u}) (A : Type u') [Category.{v'} A] [HasLimitsOfSize.{u, u} A]
variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)
variable
  {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) A ⥤ Sheaf (Scheme.smallEtaleTopology Y'.obj) A}
  {LBg : Sheaf (topology B Y.obj Y.property) A ⥤ Sheaf (topology B Y'.obj Y'.property) A}
  {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) A ⥤ Sheaf (Scheme.smallEtaleTopology X'.obj) A}
  {LBg' : Sheaf (topology B X.obj X.property) A ⥤ Sheaf (topology B X'.obj X'.property) A}
  (adjUg : LUg ⊣ unboundedPushforward B A g) (adjBg : LBg ⊣ B.smallPushforward g A)
  (adjUg' : LUg' ⊣ unboundedPushforward B A g') (adjBg' : LBg' ⊣ B.smallPushforward g' A)

end Cube

section Transfer

variable (B : BigEtaleSite.{u})
variable {X X' Y Y' : B.Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')

/-- **The 2-cell whose mate is the base change comparison of Stacks 0959 is
`AlgebraicGeometry.SmallEtale.boundedBaseChangeMate`.**
`AlgebraicGeometry.smallEtaleBaseChangeMateUniv` is built from the comparisons at the
written-out composites `g' ≫ f` and `f' ≫ g` together with a transport along the commutativity
of the square; the form used here takes the diagonal as a named morphism, so that the transport
sits inside the two comparisons instead. -/
public theorem smallEtaleBaseChangeMate_eq_boundedBaseChangeMate_univ (h : g' ≫ f = f' ≫ g)
    (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P) :
    smallEtaleBaseChangeMateUniv.{u, v} B g' f' f g h =
      boundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f' P hP₁ hP₂ := by
  subst hP₂
  rw [boundedBaseChangeMate, boundedPushforwardCompIso, boundedPushforwardCompIso,
    smallEtaleBaseChange_factoredCompIso, smallEtaleBaseChange_factoredCompIso,
    comp'_trans_eqToIso (kk :=
      congrArg (fun m : X' ⟶ Y => B.smallPushforward m (Type (max (u + 1) v))) hP₁),
    comp'_trans_eqToIso (kk := rfl), smallEtaleBaseChangeMateUniv,
    smallEtaleSheafPushforwardCompIso, smallEtaleSheafPushforwardCompIso]
  simp

/-- **Stacks 0959 on Mathlib's presentation of the small étale site.** Consider a cartesian
square

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

of the underlying category of a big étale site with `f` finite, and a choice of left adjoints of
the direct images along base change by `g` and by `g'` for sheaves of sets on *Mathlib's* small
étale sites. Then the base change comparison `g⁻¹ f_* ⟶ (f')_* (g')⁻¹` for those sites — the
mate of `AlgebraicGeometry.SmallEtale.unboundedBaseChangeMate` — is an isomorphism.

`AlgebraicGeometry.isIso_smallEtaleBaseChangeNatTrans_univ` is the same statement for the
size-bounded small étale sites of Stacks 021B. The passage between the two is
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, whose hypothesis is
`AlgebraicGeometry.SmallEtale.baseChangeMate_cube_eq`; the functor at the corner that has to
reflect isomorphisms is restriction along the embedding of the bounded site of `Y'`, which is
one half of the equivalence `AlgebraicGeometry.SmallEtale.sheafEquiv`. -/
public theorem isIso_mateEquiv_symm_unboundedBaseChangeMate_univ
    (sq : IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
      (B.inclusion.map g))
    [IsFinite (B.inclusion.map f)] (h : g' ≫ f = f' ≫ g)
    (P : X' ⟶ Y) (hP₁ : g' ≫ f = P) (hP₂ : f' ≫ g = P)
    {LUg : Sheaf (Scheme.smallEtaleTopology Y.obj) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.smallEtaleTopology Y'.obj) (Type (max (u + 1) v))}
    {LUg' : Sheaf (Scheme.smallEtaleTopology X.obj) (Type (max (u + 1) v)) ⥤
      Sheaf (Scheme.smallEtaleTopology X'.obj) (Type (max (u + 1) v))}
    (adjUg : LUg ⊣ unboundedPushforward B (Type (max (u + 1) v)) g)
    (adjUg' : LUg' ⊣ unboundedPushforward B (Type (max (u + 1) v)) g') :
    IsIso ((mateEquiv adjUg' adjUg).symm
      (unboundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f' P hP₁ hP₂)).natTrans := by
  have hEq : ((toEtaleSite B Y'.obj Y'.property).sheafPushforwardContinuous (Type (max (u + 1) v))
      (topology B Y'.obj Y'.property) Y'.obj.smallEtaleTopology).IsEquivalence :=
    (sheafEquiv B Y'.obj Y'.property (Type (max (u + 1) v))).isEquivalence_inverse
  have hb : IsIso ((mateEquiv (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
        (B.smallPullbackAdjunction g (Type (max (u + 1) v)))).symm
      (boundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f' P hP₁ hP₂)).natTrans := by
    have hall : ∀ F, IsIso ((smallEtaleBaseChangeNatTransUniv.{u, v} B g' f' f g h).app F) :=
      fun F => isIso_smallEtaleBaseChangeNatTrans_univ.{u, v} B g' f' f g sq h F
    have hiso : IsIso (smallEtaleBaseChangeNatTransUniv.{u, v} B g' f' f g h) :=
      NatIso.isIso_of_isIso_app _
    rw [← smallEtaleBaseChangeMate_eq_boundedBaseChangeMate_univ.{u, v} B f g g' f' h P hP₁ hP₂]
    exact hiso
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    adjUg' adjUg (B.smallPullbackAdjunction g' (Type (max (u + 1) v)))
    (B.smallPullbackAdjunction g (Type (max (u + 1) v)))
    (restrictionPullbackBaseChange B (Type (max (u + 1) v)) g' adjUg' _)
    (restrictionPullbackBaseChange B (Type (max (u + 1) v)) g adjUg _)
    (toEtaleSitePushforwardBaseChangeIso B f (Type (max (u + 1) v))).hom
    (toEtaleSitePushforwardBaseChangeIso B f' (Type (max (u + 1) v))).inv
    (unboundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f' P hP₁ hP₂)
    (boundedBaseChangeMate B (Type (max (u + 1) v)) f g g' f' P hP₁ hP₂)
    (baseChangeMate_cube_eq B (Type (max (u + 1) v)) f g g' f' P hP₁ hP₂ adjUg _ adjUg' _)

end Transfer

end AlgebraicGeometry.SmallEtale

end

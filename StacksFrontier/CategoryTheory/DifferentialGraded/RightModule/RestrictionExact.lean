module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Restriction
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Triangulated

/-!
# Restriction of right differential graded modules is exact

Let `F : E ⥤ C` be a functor of differential graded categories over a commutative ring `R`.
Restriction along `F` is the functor of differential graded categories
`F^* : Mod^dg(C) ⥤ Mod^dg(E)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Restriction`. It commutes with the
shift on the nose — `F^*(M⟦n⟧) = (F^* M)⟦n⟧` as right differential graded `E`-modules, not
merely up to isomorphism — because the shift changes only the degrees and the sign of the
differential, and restriction changes only the object at which a module is evaluated. By
Tag 0FQF, in the form `DGCategory.DGFunctor.CommShiftB.isTriangulated`, the induced functor

`K(F^*) : K(Mod^dg(C)) ⥤ K(Mod^dg(E))`

is therefore an exact functor of triangulated categories.

## Main definitions

* `DGCategory.commShiftB_restrictDGFunctor`: the commutation of restriction with the shift
  functors of axiom (B), in the form Tag 0FQF asks for.
* `DGCategory.restrictOnK`: the induced functor `K(Mod^dg(C)) ⥤ K(Mod^dg(E))`, with its
  `CategoryTheory.Functor.CommShift` as an instance.

## Main results

* `DGCategory.RightModule.restrict_shift`: `F^*(M⟦n⟧) = (F^* M)⟦n⟧`.
* `DGCategory.isStrictKShift_rightModuleShiftAxiomB`: the translation that axiom (B) for
  `Mod^dg(C)` puts on the homotopy category is the strict one, so the two coherences Mathlib's
  `CategoryTheory.Functor.CommShift` demands are automatic.
* `DGCategory.isTriangulated_restrictOnK`: `K(F^*)` is exact.

## Implementation notes

All three fields of `DGCategory.DGFunctor.CommShiftB` hold by reflexivity. The shift of a
module replaces `M.obj x i` by `M.obj x (i + n)` and multiplies the differential by
`(-1)^n`, while restriction replaces `x` by `F x`; the two operations act on different
arguments and commute definitionally, and the Koszul sign `(-1)^{np}` that the shift of a
degree-`p` morphism carries is a scalar, untouched by restriction. The identification
`Hom(M, N)^{k + n} ≃ Hom(M, N⟦n⟧)^k` of axiom (B) likewise only renames the target degree of
each component.

`DGCategory.isStrictKShift_rightModuleShiftAxiomB` is not a hypothesis on `F`: it records that
the `HasShift` that `DGCategory.rightModuleShiftAxiomB` puts on `K(Mod^dg(C))` is built by
`DGCategory.strictHasShift` from equalities of functors, so its coherence isomorphisms are
`eqToIso`s. It is exactly what
`DGCategory.DGFunctor.CommShiftK.ofCommShiftB` needs, and it is the reason no strictification
has to be interposed here.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type r} [CommRing R] {E C : DGCategory.{v, u} R}

namespace RightModule

/-- **Restriction commutes with the shift on the nose.** The shift changes the degree at which
a module is evaluated and the sign of its differential; restriction changes the object at
which it is evaluated. -/
theorem restrict_shift (F : DGFunctor E C) (M : RightModule.{w} C) (n : ℤ) :
    restrict F (shift M n) = shift (restrict F M) n := rfl

/-- The restriction of the shift of a homogeneous morphism is the shift of its restriction. -/
theorem restrictHom_shiftMap (F : DGFunctor E C) {M N : RightModule.{w} C} {p : ℤ}
    (φ : HomogeneousMap M N p) (n : ℤ) :
    restrictHom F (shiftMap φ n) = shiftMap (restrictHom F φ) n := rfl

/-- Restriction commutes with the identification `Hom(M, N)^{k + n} ≃ Hom(M, N⟦n⟧)^k` of
axiom (B). -/
theorem restrictHom_toShiftHom (F : DGFunctor E C) {M N : RightModule.{w} C} (n k : ℤ)
    (φ : HomogeneousMap M N (k + n)) :
    restrictHom F (toShiftHom n φ) = toShiftHom n (restrictHom F φ) := rfl

end RightModule

/-- **The translation of `K(Mod^dg(C))` supplied by axiom (B) is strict.** It is assembled by
`DGCategory.strictHasShift` from the equalities `(-)⟦0⟧ = 𝟭` and `(-)⟦n + m⟧ = (-)⟦n⟧ ⋙ (-)⟦m⟧`
of functors on the homotopy category, so its two coherence isomorphisms are the corresponding
`eqToIso`s. -/
theorem isStrictKShift_rightModuleShiftAxiomB (C : DGCategory.{v, u} R) :
    (rightModuleShiftAxiomB.{w} C).IsStrictKShift :=
  ⟨⟨rightModuleShift_onK_zero C, rfl⟩, fun a b => ⟨rightModuleShift_onK_add C a b, rfl⟩⟩

/-- **Restriction commutes with the shift**, in the form Tag 0FQF asks for: the equality
`F^*(M⟦n⟧) = (F^* M)⟦n⟧` on modules, its counterpart on homogeneous morphisms, and the
compatibility with the identifications `Hom(M, N)^{k + n} ≃ Hom(M, N⟦n⟧)^k` of axiom (B). All
three hold by reflexivity. -/
theorem commShiftB_restrictDGFunctor (F : DGFunctor E C) :
    (restrictDGFunctor.{w} F).CommShiftB (rightModuleShiftAxiomB.{w} C)
      (rightModuleShiftAxiomB.{w} E) where
  obj _ _ := rfl
  map := fun _ {_ _ _} _ => HEq.rfl
  toShift _ _ _ _ _ := HEq.rfl

/-- The commutation of restriction with the shift, together with the two coherences of the
comparison isomorphisms with the `ℤ`-action data of the translations; the latter are supplied
by the strictness of those translations. -/
theorem commShiftK_restrictDGFunctor (F : DGFunctor E C) :
    (restrictDGFunctor.{w} F).CommShiftK (rightModuleShiftAxiomB.{w} C)
      (rightModuleShiftAxiomB.{w} E) :=
  DGFunctor.CommShiftK.ofCommShiftB (commShiftB_restrictDGFunctor.{w} F)
    (isStrictKShift_rightModuleShiftAxiomB.{w} C) (isStrictKShift_rightModuleShiftAxiomB.{w} E)

/-- **The functor induced by restriction on the homotopy categories**,
`K(Mod^dg(C)) ⥤ K(Mod^dg(E))`. -/
abbrev restrictOnK (F : DGFunctor E C) :
    (rightModuleCategory.{w} C).K ⥤ (rightModuleCategory.{w} E).K :=
  (restrictDGFunctor.{w} F).onK

/-- The induced functor commutes with the translations of the two homotopy categories. -/
noncomputable instance commShiftRestrictOnK (F : DGFunctor E C) :
    (restrictOnK.{w} F).CommShift ℤ :=
  (commShiftK_restrictDGFunctor.{w} F).commShift

/-- **Restriction is exact.** The functor `K(Mod^dg(C)) ⥤ K(Mod^dg(E))` induced by restriction
along a functor `F : E ⥤ C` of differential graded categories is an exact functor of
triangulated categories: this is Tag 0FQF, whose hypothesis `F(x⟦1⟧) = F(x)⟦1⟧` is
`DGCategory.commShiftB_restrictDGFunctor`. -/
theorem isTriangulated_restrictOnK (F : DGFunctor E C) : (restrictOnK.{w} F).IsTriangulated :=
  DGFunctor.CommShiftK.isTriangulated (rightModuleConeSituation.{w} C)
    (rightModuleConeSituation.{w} E) (commShiftK_restrictDGFunctor.{w} F)

/-- The functor `restrictOnK F` induced by restriction on the homotopy categories is a
triangulated functor. -/
instance (F : DGFunctor E C) : (restrictOnK.{w} F).IsTriangulated :=
  isTriangulated_restrictOnK.{w} F

end DGCategory

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullbackIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.HomogeneousProdLeft

/-!
# The pullback comparison for exterior algebras on an ordered product of generators

Let `f : X ⟶ Y` be a morphism of ringed spaces, `A` an exterior algebra of a sheaf of
`𝒪_Y`-modules `M` with degree-one generator `ι`, and `B` an exterior algebra of `f^*M` with
degree-one generator `κ`. The comparison of [Stacks, Tag 01CI],
`Stacks.PullbackExteriorAlgebra.pieceIso`, is an isomorphism `f^*(A_n) ≅ B_n` in every degree.
This file computes it on the pullback-unit image of an **ordered product of degree-one
generators**: for local sections `s₀, …, s_{p-1}` of `M` over an open `U` of `Y`,

`pieceIso (f^*(ι s₀ ⋯ ι s_{p-1})) = κ(f^*s₀) ⋯ κ(f^*s_{p-1})`

over `f⁻¹U`.

## Main results

* `Stacks.GradedAlgebra.homogeneousProd_generator_naturality` and
  `homogeneousProdLeft_generator_naturality`: **an ordered product of degree-one generators
  commutes with restriction.** Stated at the presheaf level, for an arbitrary morphism into
  degree one, so that it serves every consumer that moves such a product between opens; the
  pullback comparison below is only one of them.
* `Stacks.PullbackExteriorAlgebra.pieceIso_homogeneousProd`: the comparison carries the
  pullback-unit image of `Stacks.GradedAlgebra.homogeneousProd` of degree-one generators of `A`
  to the ordered product of the corresponding degree-one generators of `B`.
* `Stacks.PullbackExteriorAlgebra.pieceIso_homogeneousProdLeft`: the same statement for the
  left-handed product `Stacks.GradedAlgebra.homogeneousProdLeft`.
* `Stacks.PullbackExteriorAlgebra.pieceIso_inv_homogeneousProd` and
  `pieceIso_inv_homogeneousProdLeft`: both statements in the `inv` direction, which is the
  orientation a composite of comparisons assembled out of inverses presents this factor in.

## Implementation notes

**The restriction-naturality is not a new induction.**
`Stacks.GradedAlgebra.homogeneousProd_naturality` already states that the ordered product of
degree-one *sections* commutes with restriction, by that induction; what the two lemmas above
add is the naturality of the generator folded in, which is the form every consumer wants and
had been re-derived inline.

`Stacks.GradedAlgebra.homogeneousProd` is built from the unit of the algebra and its
multiplication, so its inductive content is exactly the three section formulas that the
comparison satisfies:
`Stacks.PullbackExteriorAlgebra.comparisonHom_one` for the empty product,
`Stacks.PullbackExteriorAlgebra.comparisonHom_mul` for the step that peels the last factor, and
`Stacks.PullbackExteriorAlgebra.comparisonHom_generator` for that factor itself. The induction
is on the length of the product and needs nothing else; in particular no degree transport
appears, because the recursion of `homogeneousProd` multiplies on the right and `(p : ℤ) + 1` is
definitionally `((p + 1 : ℕ) : ℤ)`.

**Why `SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd_comp` does not prove this.**
That lemma is the same bookkeeping for a unital homomorphism of sheaves of graded algebras, but
its variable block fixes **one** site and **one** sheaf of rings for both algebras
(`{A B : GradedAlgebra (toRingCat J Osharp)}`). Here `A` lives on `Y` and `B` on `X`, over the
two structure sheaves, and the comparison is not a morphism in any one category of sheaves of
graded algebras: it is a morphism `f^*A ⟶ B`, whose source is the pullback. So the induction has
to be redone against the three section formulas, which is what this file does.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI) — pullback and the
  tensor, exterior and symmetric algebras of a sheaf of modules.
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW) — sheaves of graded
  algebras.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open SheafOfModules.GradedAlgebra

universe u v w a

/-! ### An ordered product of generators under a restriction map -/

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {Pc : ℤ → PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (A : Stacks.GradedAlgebra Pc)
  {N : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}

/-- **An ordered product of degree-one generators commutes with restriction**: restricting the
product of the images of `s₀, …, s_{p-1}` under a morphism `ι` into degree one is the product of
the images of the restricted sections.

This is `Stacks.GradedAlgebra.homogeneousProd_naturality` with the naturality of `ι` folded in.
The two are always used together — the ordered products that occur in practice are products of
generators, not of arbitrary degree-one sections — and the pair had been inlined at
`SheafOfModules.germ_homogeneousProd_res` and
`Stacks.RegularSequence.map_exteriorBasisSection` before this was stated. -/
theorem homogeneousProd_generator_naturality (ι : N ⟶ Pc 1) {U V : Cᵒᵖ} (h : U ⟶ V) (p : ℕ)
    (s : Fin p → N.obj U) :
    (Pc (p : ℤ)).map h (A.homogeneousProd U p fun i ↦ ι.app U (s i)) =
      A.homogeneousProd V p fun i ↦ ι.app V (N.map h (s i)) :=
  (A.homogeneousProd_naturality h p fun i ↦ ι.app U (s i)).trans
    (congrArg (A.homogeneousProd V p)
      (funext fun i ↦ (PresheafOfModules.naturality_apply ι h (s i)).symm))

/-- The left-handed form of `Stacks.GradedAlgebra.homogeneousProd_generator_naturality`. -/
theorem homogeneousProdLeft_generator_naturality (ι : N ⟶ Pc 1) {U V : Cᵒᵖ} (h : U ⟶ V) (p : ℕ)
    (s : Fin p → N.obj U) :
    (Pc (p : ℤ)).map h (A.homogeneousProdLeft U p fun i ↦ ι.app U (s i)) =
      A.homogeneousProdLeft V p fun i ↦ ι.app V (N.map h (s i)) :=
  (congrArg ((Pc (p : ℤ)).map h) (A.homogeneousProdLeft_eq_homogeneousProd U p _)).trans
    ((A.homogeneousProd_generator_naturality ι h p s).trans
      (A.homogeneousProdLeft_eq_homogeneousProd V p _).symm)

end Stacks.GradedAlgebra

namespace Stacks.PullbackExteriorAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))
  {M : SheafOfModules.{u} (structureRingSheaf Y)} {ι : M ⟶ A.piece 1}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}

/-- **The comparison of [Stacks, Tag 01CI] carries an ordered product of degree-one generators
to the ordered product of the generators of the pulled-back sections.**

The induction is on the length of the product: the empty product is the unit, handled by
`Stacks.PullbackExteriorAlgebra.comparisonHom_one`; the step peels the last factor with
`Stacks.PullbackExteriorAlgebra.comparisonHom_mul` and identifies it with
`Stacks.PullbackExteriorAlgebra.comparisonHom_generator`. -/
theorem pieceIso_homogeneousProd (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ)
    (U : (Opens Y.carrier)ᵒᵖ) (p : ℕ) (s : Fin p → M.val.obj U) :
    (pieceIso f A hA hB.1 hB (p : ℤ)).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece (p : ℤ)) U
          (A.toPresheafGradedAlgebra.homogeneousProd U p fun i ↦ ι.val.app U (s i))) =
      B.toPresheafGradedAlgebra.homogeneousProd ((opensMap f).op.obj U) p
        fun i ↦ κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U (s i)) := by
  induction p with
  | zero => exact comparisonHom_one f A hA hB.1 U
  | succ p ih =>
      refine (comparisonHom_mul f A hA hB.1 (p : ℤ) 1 U
        (A.toPresheafGradedAlgebra.homogeneousProd U p fun i ↦ ι.val.app U (s i.castSucc))
        (ι.val.app U (s (Fin.last p)))).trans ?_
      exact congrArg₂ (fun x y ↦ (B.mul (p : ℤ) 1).app ((opensMap f).op.obj U) x y)
        (ih fun i ↦ s i.castSucc)
        (comparisonHom_generator f A hA hB.1 U (s (Fin.last p)))

/-- The left-handed form of `Stacks.PullbackExteriorAlgebra.pieceIso_homogeneousProd`, for the
ordered product `Stacks.GradedAlgebra.homogeneousProdLeft`, which is the shape the de Rham
development states its products in. -/
theorem pieceIso_homogeneousProdLeft (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ)
    (U : (Opens Y.carrier)ᵒᵖ) (p : ℕ) (s : Fin p → M.val.obj U) :
    (pieceIso f A hA hB.1 hB (p : ℤ)).hom.val.app ((opensMap f).op.obj U)
        (pullbackUnit f (A.piece (p : ℤ)) U
          (A.toPresheafGradedAlgebra.homogeneousProdLeft U p fun i ↦ ι.val.app U (s i))) =
      B.toPresheafGradedAlgebra.homogeneousProdLeft ((opensMap f).op.obj U) p
        fun i ↦ κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U (s i)) := by
  simp only [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd]
  exact pieceIso_homogeneousProd f A hA hB U p s

/-- **The `inv` direction of `Stacks.PullbackExteriorAlgebra.pieceIso_homogeneousProd`.** This
is the orientation a composite of comparisons presents the factor in when it is assembled as
`D.inv ≫ C.inv ≫ B.inv ≫ A.hom`; since `pieceIso` is an isomorphism it is the forward statement
with both sides hit by the inverse. -/
theorem pieceIso_inv_homogeneousProd (hA : IsExteriorAlgebra A ι) (hB : IsExteriorAlgebra B κ)
    (U : (Opens Y.carrier)ᵒᵖ) (p : ℕ) (s : Fin p → M.val.obj U) :
    (pieceIso f A hA hB.1 hB (p : ℤ)).inv.val.app ((opensMap f).op.obj U)
        (B.toPresheafGradedAlgebra.homogeneousProd ((opensMap f).op.obj U) p
          fun i ↦ κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U (s i))) =
      pullbackUnit f (A.piece (p : ℤ)) U
        (A.toPresheafGradedAlgebra.homogeneousProd U p fun i ↦ ι.val.app U (s i)) :=
  (congrArg ((pieceIso f A hA hB.1 hB (p : ℤ)).inv.val.app ((opensMap f).op.obj U))
      (pieceIso_homogeneousProd f A hA hB U p s).symm).trans
    (Stacks.SheafOfModules.inv_val_app_hom_val_app (pieceIso f A hA hB.1 hB (p : ℤ))
      ((opensMap f).op.obj U) _)

/-- The `inv` direction of `Stacks.PullbackExteriorAlgebra.pieceIso_homogeneousProdLeft`. -/
theorem pieceIso_inv_homogeneousProdLeft (hA : IsExteriorAlgebra A ι)
    (hB : IsExteriorAlgebra B κ) (U : (Opens Y.carrier)ᵒᵖ) (p : ℕ) (s : Fin p → M.val.obj U) :
    (pieceIso f A hA hB.1 hB (p : ℤ)).inv.val.app ((opensMap f).op.obj U)
        (B.toPresheafGradedAlgebra.homogeneousProdLeft ((opensMap f).op.obj U) p
          fun i ↦ κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U (s i))) =
      pullbackUnit f (A.piece (p : ℤ)) U
        (A.toPresheafGradedAlgebra.homogeneousProdLeft U p fun i ↦ ι.val.app U (s i)) :=
  by
  simp only [Stacks.GradedAlgebra.homogeneousProdLeft_eq_homogeneousProd]
  exact pieceIso_inv_homogeneousProd f A hA hB U p s

end Stacks.PullbackExteriorAlgebra

end

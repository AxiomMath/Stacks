module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Deformation.ToposThickening.SectionwiseDerivation

/-!
# Twisting a homomorphism into a first order thickening by a derivation

Let `S` be a layer of the diagram of [Stacks Project, Tag 08UG] — a
`Deformation.ToposThickening.LiftSquare`, so a first order thickening `S.O' ⟶ S.O` whose ideal
is identified section by section with a module `S.G` — let `R` be any sheaf of commutative rings
on the site, and let `b : R ⟶ S.O'` be a homomorphism. A section-wise derivation `δ` of `R` with
values in `S.G`, the scalars acting through `S.reduction ∘ b`, twists `b` into a second
homomorphism

`x ↦ b(x) + incl (δ x)`.

That it is again a homomorphism of sheaves of rings is the square-zero computation of the
thickening: the cross terms of the product are the two Leibniz terms, because `S.O'` acts on its
ideal through the reduction, and the remaining term is a product of two sections of the ideal,
which vanishes.

This is the construction Step 3 of the proof of [Stacks Project, Tag 08UG] opens with. There the
source is the polynomial presentation `R = 𝒪_{ℬ'₁}[ℰ]` of Step 1, `b` is the algebra map into
`𝒪'₂`, and `δ` is `θ ∘ d` for a factorization `θ` of the obstruction homomorphism through the
degree `0` term of `NL(α)`; the twisted map is the source's `b + θ ∘ d`, which is then descended
along the presentation by
`Stacks.Sites.RingDescent.existsUnique_desc`
(`StacksFrontier/CategoryTheory/Sites/RingSheafDescent.lean`).

## Main definitions

* `Deformation.ToposThickening.LiftSquare.twist`: the twisted homomorphism `b + incl ∘ δ`.

## Main results

* `Deformation.ToposThickening.LiftSquare.twist_apply`: the formula `b(x) + incl (δ x)`, which
  pins the twisted homomorphism down.
* `Deformation.ToposThickening.LiftSquare.twist_comp_reduction`: twisting does not change the
  reduction, since the ideal is killed by it. This is why a twist of a homomorphism lying over a
  prescribed map still lies over it.
* `Deformation.ToposThickening.LiftSquare.twist_eq_of_apply_eq_zero`: on a section killed by the
  derivation the twist agrees with `b`. With `twist_comp_reduction` this is how the clauses of a
  diagram are checked for a twisted homomorphism.
* `Deformation.ToposThickening.LiftSquare.twist_zero`: the zero derivation twists trivially.

## Implementation notes

The acting object is not declared here: a derivation of `R` into the ideal module of `S` along
`b` is exactly a `Deformation.ToposThickening.SectionwiseDerivation` of `R` with values in
`S.G` whose scalars act through `b ≫ S.reduction`, so that is the type `twist` takes, and the
zero derivation, the sum of two derivations and their additive group are the ones stated once
there (`StacksFrontier/Deformation/ToposThickening/LiftingBetweenThickenings.lean`). The
derivations of a `DerivationSituation`, `Deformation.ToposThickening.Derivation`, extend that
same substrate by the two vanishing conditions of the source's diagram; neither type
generalizes the other — a `Derivation` is a derivation out of the thickened structure sheaf of
the diagram's own front layer which in addition kills the ideal and the image of the thickened
base, whereas here the source is an arbitrary sheaf of rings and no vanishing is asked — but
the section-wise family with its three laws, and `twist`, are what both need.

The relation to `Deformation.ToposThickening.LiftDiagram.translate`: that is the case
`R = D.front.O'`, `b = p.hom` for a lift `p`, with the derivation coming from a
`Deformation.ToposThickening.Derivation`. It is left as it stands rather than rewritten through
`twist`, since its clause-(2) consumers depend on its definitional shape; what is recorded here
is that the two computations are the same one.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

namespace LiftSquare

/-! ### The twisted homomorphism -/

/-- **Twisting a homomorphism into a first order thickening by a derivation:** the map
`x ↦ b(x) + incl (δ x)`. It is again a homomorphism of sheaves of commutative rings, by the
square-zero computation of the thickening. -/
public noncomputable def twist (S : LiftSquare J) {R : Sheaf J CommRingCat.{w}} (b : R ⟶ S.O')
    (δ : SectionwiseDerivation R S.G (b ≫ S.reduction)) : R ⟶ S.O' where
  hom :=
    { app := fun U => CommRingCat.ofHom
        { toFun := fun x => b.hom.app U x + S.incl (δ.toFun U x)
          map_one' := by
            rw [δ.map_one U, S.incl_zero, add_zero]
            simp
          map_mul' := fun x y => by
            have hbx : b.hom.app U x * S.incl (δ.toFun U y) =
                S.incl (toRingSection J
                  (S.reduction.hom.app U (b.hom.app U x)) • δ.toFun U y) := by
              rw [S.mul_incl]
            have hby : b.hom.app U y * S.incl (δ.toFun U x) =
                S.incl (toRingSection J
                  (S.reduction.hom.app U (b.hom.app U y)) • δ.toFun U x) := by
              rw [S.mul_incl]
            have h0 : S.incl (δ.toFun U x) * S.incl (δ.toFun U y) = 0 :=
              S.incl_mul_incl _ _
            have hb : b.hom.app U (x * y) = b.hom.app U x * b.hom.app U y := by simp
            rw [hb, δ.leibniz U x y]
            simp only [sheafHom_comp_apply]
            rw [S.incl_add, ← hbx, ← hby]
            linear_combination -h0
          map_zero' := by rw [δ.map_zero U, S.incl_zero, add_zero]; simp
          map_add' := fun x y => by
            have hb : b.hom.app U (x + y) = b.hom.app U x + b.hom.app U y := by simp
            rw [hb, δ.map_add' U x y, S.incl_add]
            abel }
      naturality := fun {U V} h => by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change b.hom.app V (R.obj.map h x) + S.incl (δ.toFun V (R.obj.map h x)) =
          S.O'.obj.map h (b.hom.app U x + S.incl (δ.toFun U x))
        rw [δ.naturality h x, S.incl_naturality, sheafHom_naturality_apply]
        exact (map_add _ _ _).symm }

/-- **The formula determining a twist.** -/
@[simp]
public theorem twist_apply (S : LiftSquare J) {R : Sheaf J CommRingCat.{w}} (b : R ⟶ S.O')
    (δ : SectionwiseDerivation R S.G (b ≫ S.reduction)) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (S.twist b δ).hom.app U x = b.hom.app U x + S.incl (δ.toFun U x) := rfl

/-- **Twisting does not change the reduction**, the ideal being killed by it. -/
public theorem twist_comp_reduction (S : LiftSquare J) {R : Sheaf J CommRingCat.{w}}
    (b : R ⟶ S.O') (δ : SectionwiseDerivation R S.G (b ≫ S.reduction)) :
    S.twist b δ ≫ S.reduction = b ≫ S.reduction := by
  refine sheafHom_ext J fun U x => ?_
  show S.reduction.hom.app U (b.hom.app U x + S.incl (δ.toFun U x)) =
    S.reduction.hom.app U (b.hom.app U x)
  rw [map_add, S.reduction_incl, add_zero]

/-- **On a section killed by the derivation the twist agrees with `b`.** -/
public theorem twist_eq_of_apply_eq_zero (S : LiftSquare J) {R : Sheaf J CommRingCat.{w}}
    (b : R ⟶ S.O') (δ : SectionwiseDerivation R S.G (b ≫ S.reduction)) {U : Cᵒᵖ} {x : R.obj.obj U}
    (hx : δ.toFun U x = 0) :
    (S.twist b δ).hom.app U x = b.hom.app U x := by
  rw [twist_apply, hx, S.incl_zero, add_zero]

/-- The zero derivation twists trivially. -/
public theorem twist_zero (S : LiftSquare J) {R : Sheaf J CommRingCat.{w}} (b : R ⟶ S.O') :
    S.twist b 0 = b := by
  refine sheafHom_ext J fun U x => ?_
  rw [twist_apply, SectionwiseDerivation.zero_toFun, S.incl_zero, add_zero]

end LiftSquare

end Deformation.ToposThickening

end

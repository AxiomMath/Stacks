module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The wedge product on the relative de Rham complex

Let `φ : A ⟶ B` be a morphism of sheaves of commutative rings on a topological space, with `B` the
structure sheaf of a ringed space `X`, let `Ω = Ω_{B/A}` be the sheaf of relative differentials and
let `B` also denote a package of the three algebras of Stacks Section 17.21 for `Ω`.

Wedging differential forms is `A`-bilinear and obeys the graded Leibniz rule
`d(ω ∧ η) = dω ∧ η + (-1)^p ω ∧ dη`, which is exactly the condition for the family of wedge
multiplications `Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ` to assemble into a single morphism of complexes of sheaves of
`A`-modules

`∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•`

out of the total complex of the tensor-product bicomplex. This file assembles it.

The components and the Leibniz rule they satisfy are supplied by
`StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic`; what is added here is the descent of
that
family to the total complex, together with the identification of the resulting morphism on local
pure tensors, which is what pins it down as the wedge product rather than some other morphism of
complexes.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.wedgeProduct`: **the wedge product
  `∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•`**, as a morphism of complexes of sheaves of `A`-modules.

## Main results

* `AlgebraicGeometry.SheafOfModules.wedgeProduct_summand_unit_apply`: **on the `(p, q)` summand
  of the total complex the wedge product is wedge multiplication of a `p`-form by a `q`-form.**
  This is what identifies `AlgebraicGeometry.SheafOfModules.wedgeProduct` as the morphism of
  Tag 0FM2.

## Implementation notes

The degree-`n` component is the descent of the components of degrees `(p, q)` with `p + q = n`
along the coproduct decomposition of the total complex
(`CategoryTheory.HomologicalComplex.mapBifunctorDesc`), so the only thing to check is that it
commutes with the differentials. That check reduces, on each summand, to the Leibniz rule
`AlgebraicGeometry.SheafOfModules.exteriorProductComponent_d`; the Koszul signs of the total
complex of two copies of `ComplexShape.up ℕ` are `1` and `(-1)^p`, which is where the sign of the
Leibniz rule comes from.

The target of the degree-`(p, q)` component is `Ωᵖ⁺ᵠ` and the degree-`n` term of the complex is
`Ωⁿ`, so a reindexing isomorphism `HomologicalComplex.XIsoOfEq` appears in the descent. The
identification on pure tensors is therefore stated as a heterogeneous equality: the two sides
live in the exterior powers of degrees `((p + q : ℕ) : ℤ)` and `(p : ℤ) + q`.

The de Rham differential is a hypothesis rather than
`AlgebraicGeometry.SheafOfModules.deRhamDifferential`: everything here holds for an arbitrary one,
and there is only one (`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.eq`).

## References

* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct DirectSum
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- The degree-`n` component of the wedge product: the descent of the wedge multiplications
`Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ` with `p + q = n` along the coproduct decomposition of the degree-`n` term of
the total complex. -/
noncomputable def wedgeProductDesc (n : ℕ) :
    (tensorSquare B D).X n ⟶ (deRhamComplex B D).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := deRhamComplex B D) (K₂ := deRhamComplex B D)
    (F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
    (c := ComplexShape.up ℕ) fun p q h =>
    exteriorProductComponent B p q ≫ ((deRhamComplex B D).XIsoOfEq (show p + q = n from h)).hom

/-- The degree-`n` component of the wedge product, restricted to the `(p, q)` summand of the
total complex, is wedge multiplication of a `p`-form by a `q`-form. -/
@[reassoc (attr := simp)]
theorem ι_wedgeProductDesc (p q n : ℕ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
      (deRhamComplex B D) (deRhamComplex B D)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℕ) p q n h ≫ wedgeProductDesc B D n =
      exteriorProductComponent B p q ≫ ((deRhamComplex B D).XIsoOfEq h).hom :=
  HomologicalComplex.ι_mapBifunctorDesc
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) _ p q h

/-- The first Koszul sign of the total complex of two copies of `ComplexShape.up ℕ` is trivial. -/
private theorem ε₁_up_nat (p q : ℕ) :
    ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) = 1 :=
  rfl

/-- The second Koszul sign of the total complex of two copies of `ComplexShape.up ℕ` is the sign
`(-1)^p` of the graded Leibniz rule. -/
private theorem ε₂_up_nat (p q : ℕ) :
    ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (p, q) =
      (-1 : ℤˣ) ^ p :=
  rfl

/-- On the `(p, q)` summand, the degree-`(p + q)` component of the descent is the wedge
multiplication. -/
private theorem ι_wedgeProductDesc_add (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
      (deRhamComplex B D) (deRhamComplex B D)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℕ) p q (p + q) rfl ≫ wedgeProductDesc B D (p + q) =
      exteriorProductComponent B p q := by
  simp only [ι_wedgeProductDesc, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  exact Category.comp_id _

private theorem ι_tensorSquare_d_wedgeProductDesc (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor
        (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
        (deRhamComplex B D) (deRhamComplex B D)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
        (ComplexShape.up ℕ) p q (p + q) rfl ≫
      ((tensorSquare B D).d (p + q) (p + q + 1) ≫ wedgeProductDesc B D (p + q + 1)) =
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map
        ((deRhamComplex B D).d p (p + 1))).app ((deRhamComplex B D).X q) ≫
      exteriorProductComponent B (p + 1) q ≫
        ((deRhamComplex B D).XIsoOfEq (show p + 1 + q = p + q + 1 by omega)).hom +
      (-1 : ℤ) ^ p •
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).obj
          ((deRhamComplex B D).X p)).map ((deRhamComplex B D).d q (q + 1)) ≫
          exteriorProductComponent B p (q + 1) ≫
            ((deRhamComplex B D).XIsoOfEq
              (show p + (q + 1) = p + q + 1 by omega)).hom) := by
  have hπ₁ : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p + 1, q) = p + q + 1 := show p + 1 + q = p + q + 1 by omega
  have hπ₂ : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p, q + 1) = p + q + 1 := show p + (q + 1) = p + q + 1 by omega
  have hd : (tensorSquare B D).d (p + q) (p + q + 1) =
      HomologicalComplex.mapBifunctor.D₁
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
          (deRhamComplex B D) (deRhamComplex B D)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) (p + q)
          (p + q + 1) +
        HomologicalComplex.mapBifunctor.D₂
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
          (deRhamComplex B D) (deRhamComplex B D)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) (p + q)
          (p + q + 1) :=
    HomologicalComplex.mapBifunctor.d_eq
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) _ _ _ _ _ _
  rw [hd]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl) q (p + q + 1) hπ₁,
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl) (p + q + 1) hπ₂,
    Linear.units_smul_comp, Category.assoc, ι_wedgeProductDesc,
    ε₁_up_nat, ε₂_up_nat, one_smul]
  rw [Units.smul_def]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rfl

/-- **The graded Leibniz rule, read on a single summand of the total complex.** On the `(p, q)`
summand the two ways round the square — descend and then differentiate, or differentiate in the
total complex and then descend — agree. This is the one computation behind
`AlgebraicGeometry.SheafOfModules.wedgeProduct`. -/
private theorem ι_wedgeProductDesc_comm (p q : ℕ) :
    HomologicalComplex.ιMapBifunctor
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
      (deRhamComplex B D) (deRhamComplex B D)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℕ) p q (p + q) rfl ≫
        (wedgeProductDesc B D (p + q) ≫ (deRhamComplex B D).d (p + q) (p + q + 1)) =
      HomologicalComplex.ιMapBifunctor
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
        (deRhamComplex B D) (deRhamComplex B D)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A)
          (ComplexShape.up ℕ) p q (p + q) rfl ≫
        ((tensorSquare B D).d (p + q) (p + q + 1) ≫ wedgeProductDesc B D (p + q + 1)) := by
  rw [← Category.assoc, ι_wedgeProductDesc_add]
  exact (exteriorProductComponent_d B D p q).trans
    (ι_tensorSquare_d_wedgeProductDesc B D p q).symm

/-- Degreewise, the descent of the wedge multiplications commutes with the differentials. -/
private theorem wedgeProductDesc_comm (n : ℕ) :
    wedgeProductDesc B D n ≫ (deRhamComplex B D).d n (n + 1) =
      (tensorSquare B D).d n (n + 1) ≫ wedgeProductDesc B D (n + 1) := by
  refine HomologicalComplex.mapBifunctor.hom_ext
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) fun p q hpq => ?_
  obtain rfl : p + q = n := hpq
  exact ι_wedgeProductDesc_comm B D p q

/-- **Stacks Project, Tag 0FM2.** The wedge product
`∧ : Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` of relative differential forms, as a morphism of complexes of
sheaves of `A`-modules: on the `(p, q)` summand of the total complex it is wedge multiplication of
a `p`-form by a `q`-form, and the graded Leibniz rule is exactly the statement that this family
commutes with the differentials. -/
@[stacks 0FM2]
noncomputable def wedgeProduct : tensorSquare B D ⟶ deRhamComplex B D where
  f := wedgeProductDesc B D
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact wedgeProductDesc_comm B D i

/-- The degree-`n` component of the wedge product is the descent of the wedge multiplications of
total degree `n`. -/
@[simp]
theorem wedgeProduct_f (n : ℕ) : (wedgeProduct B D).f n = wedgeProductDesc B D n := rfl

/-- **Stacks Project, Tag 0FM2.** On the `(p, q)` summand of the total complex the wedge product
sends a local pure tensor `ω ⊗ η` to the wedge product `ω ∧ η`.

The two sides live in the exterior powers of degrees `((p + q : ℕ) : ℤ)` and `(p : ℤ) + q`, which
is why this is a heterogeneous equality. -/
@[stacks 0FM2]
theorem wedgeProduct_summand_unit_apply (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) (η : (deRhamTerm B q).val.obj U) :
    HEq ((HomologicalComplex.ιMapBifunctor
      (D := _root_.SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A))
            (deRhamComplex B D) (deRhamComplex B D)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A) (ComplexShape.up ℕ) p q
              (p + q) rfl ≫
          (wedgeProduct B D).f (p + q)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
          (PresheafOfModules.tensorObj ((deRhamTerm B p)).val ((deRhamTerm B q)).val)).app U
            (ω ⊗ₜ[A.obj.obj U] η)))
      ((B.exterior.mul (p : ℤ) (q : ℤ)).app U ω η) := by
  refine heq_of_eq (Eq.trans ?_ (exteriorProductComponent_unit_apply B p q U ω η))
  exact congrArg (fun k => k.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf A)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf A).obj)).unit.app
      (PresheafOfModules.tensorObj ((deRhamTerm B p)).val ((deRhamTerm B q)).val)).app U
        (ω ⊗ₜ[A.obj.obj U] η))) (ι_wedgeProductDesc_add B D p q)

end AlgebraicGeometry.SheafOfModules

end

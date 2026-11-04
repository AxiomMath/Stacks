module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorOverlap

/-!
# Two trivialisations read Saltman's projector as the same point

Let `T` be a scheme, let `d = n + 1`, let `B` be a sheaf of `𝒪_T`-algebras and let
`M₁ M₂ : B ≅ Mat_d(𝒪_T)` be two trivialisations of it as a matrix algebra. Each of them
trivialises the `d`-fold tensor power of `B` as the endomorphism algebra of the free sheaf of
`𝒪_T`-modules of rank `d ^ d`,
$$
B^{\otimes d} \cong \mathrm{Mat}_d(\mathcal{O}_T)^{\otimes d}
  \cong \mathcal{H}om(\mathcal{O}_T^d, \mathcal{O}_T^d)^{\otimes d}
  \cong \mathcal{H}om((\mathcal{O}_T^d)^{\otimes d}, (\mathcal{O}_T^d)^{\otimes d})
  \cong \mathcal{H}om(\mathcal{O}_T^{d^d}, \mathcal{O}_T^{d^d}),
$$
and the content of this file is that **the two resulting points of `B^{⊗ d}` attached to
Saltman's projector `altProjFree T d` are equal.**

This is the overlap step of [Stacks, Tag 0A2L] in the shape its consumer wants. The step itself —
that the `d`-fold tensor power of an automorphism of `Mat_d(𝒪_T)` fixes the projector — is
`Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowEndConj_altProjFree`. What is added here
is the identification of the comparison automorphism of the two trivialisations with such a tensor
power: the two composites differ only in their first factor `natTensorPowCongr M_k d`, so their
comparison is `natTensorPowCongr (M₁⁻¹ ≫ M₂) d` conjugated by the two factors they share, and
that conjugate is by definition
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowEndConjFree T n (M₁.symm ≪≫ M₂)`.
`CategoryTheory.MonoidalClosed.curry'_comp_inv_hom_eq_iff` then turns a fixed point of the
comparison automorphism into an equality of the two points.

The only computation is the functoriality of
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowCongr` in its isomorphism, which the library did
not record: two inductions whose steps are the interchange law
`CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowTrivIso`: the trivialisation of `B^{⊗ d}` as
  the endomorphism algebra of the free sheaf of rank `d ^ d` induced by a trivialisation of `B`
  as `Mat_d(𝒪_T)`.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowCongr_trans` and
  `Stacks.EtaleCohomology.BrauerScheme.natTensorPowCongr_inv_comp_hom`: the tensor power of an
  isomorphism of sheaves of algebras is functorial in that isomorphism.
* `Stacks.EtaleCohomology.BrauerScheme.natTensorPowTrivIso_inv_comp_hom`: **the comparison
  automorphism of the two induced trivialisations of `B^{⊗ d}` is the `d`-fold tensor power of the
  comparison automorphism `M₁⁻¹ ≫ M₂` of `Mat_d(𝒪_T)`.**
* `Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowTrivIso_altProjFree`: that comparison
  automorphism fixes Saltman's projector.
* `Stacks.EtaleCohomology.BrauerScheme.curry'_altProjFree_comp_natTensorPowTrivIso_inv`: **the two
  trivialisations read Saltman's projector as the same point of `B^{⊗ d}`.**

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

variable {T : Scheme.{u}}

/-! ### Two reassociations, with every object a variable -/

/-- **The comparison of two isomorphisms which share their second factor**, with that factor
conjugated out. Stated for an abstract category, with every object a variable, so that it applies
to the tensor-power spellings: the two sides differ by reassociation only, which is a
*propositional* equality, so a statement about the tensor-power spellings cannot be reached by
`show`. This is the discipline of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerFreeMatrix`. -/
theorem trans_inv_comp_trans_hom {C : Type*} [Category C] {X Y W : C} (P₁ P₂ : X ≅ Y)
    (Z : Y ≅ W) :
    (P₁ ≪≫ Z).inv ≫ (P₂ ≪≫ Z).hom = Z.inv ≫ (P₁.inv ≫ P₂.hom) ≫ Z.hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]

/-- **A two-step conjugation is the conjugation by the composite.** Stated for an abstract
category, with every object a variable, for the same reason as
`Stacks.EtaleCohomology.BrauerScheme.trans_inv_comp_trans_hom`. -/
theorem symm_trans_conj_hom {C : Type*} [Category C] {X Y W : C} (Q : X ≅ Y) (R : Y ≅ W)
    (e : X ≅ X) :
    (R.symm ≪≫ (Q.symm ≪≫ e ≪≫ Q) ≪≫ R).hom
      = (Q ≪≫ R).inv ≫ e.hom ≫ (Q ≪≫ R).hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc]

/-! ### The tensor power of an isomorphism is functorial -/

/-- **The tensor power of a composite of isomorphisms of sheaves of algebras is the composite of
the tensor powers.** The induction step is the interchange law. -/
theorem natTensorPowCongr_trans {A B D : AlgebraSheaf T} (e₁ : A ≅ B) (e₂ : B ≅ D) :
    ∀ n : ℕ, natTensorPowCongr (e₁ ≪≫ e₂) n = natTensorPowCongr e₁ n ≪≫ natTensorPowCongr e₂ n
  | 0 => by
    refine Iso.ext ?_
    show 𝟙 (Stacks.TensorPowers.natTensorPow A 0) = 𝟙 _ ≫ 𝟙 _
    rw [Category.comp_id]
  | n + 1 => by
    refine Iso.ext ?_
    have ih := natTensorPowCongr_trans e₁ e₂ n
    show (natTensorPowCongr (e₁ ≪≫ e₂) n).hom ⊗ₘ (e₁.hom ≫ e₂.hom)
      = ((natTensorPowCongr e₁ n).hom ⊗ₘ e₁.hom) ≫ ((natTensorPowCongr e₂ n).hom ⊗ₘ e₂.hom)
    rw [tensorHom_comp_tensorHom, ih]
    rfl

/-- **The comparison of the tensor powers of two isomorphisms with the same source and target is
the tensor power of their comparison.** -/
theorem natTensorPowCongr_inv_comp_hom {A B : AlgebraSheaf T} (M₁ M₂ : A ≅ B) (n : ℕ) :
    (natTensorPowCongr M₁ n).inv ≫ (natTensorPowCongr M₂ n).hom
      = (natTensorPowCongr (M₁.symm ≪≫ M₂) n).hom := by
  have hiso : natTensorPowCongr M₂ n
      = natTensorPowCongr M₁ n ≪≫ natTensorPowCongr (M₁.symm ≪≫ M₂) n := by
    rw [← natTensorPowCongr_trans]
    refine congrArg (fun e : A ≅ B => natTensorPowCongr e n) (Iso.ext ?_)
    show M₂.hom = M₁.hom ≫ M₁.inv ≫ M₂.hom
    rw [M₁.hom_inv_id_assoc]
  calc (natTensorPowCongr M₁ n).inv ≫ (natTensorPowCongr M₂ n).hom
      = (natTensorPowCongr M₁ n).inv ≫ (natTensorPowCongr M₁ n).hom ≫
          (natTensorPowCongr (M₁.symm ≪≫ M₂) n).hom := by
        rw [← Iso.trans_hom, ← hiso]
    _ = (natTensorPowCongr (M₁.symm ≪≫ M₂) n).hom :=
        (natTensorPowCongr M₁ n).inv_hom_id_assoc _

/-! ### The induced trivialisation of the tensor power -/

/-- **The trivialisation of `B^{⊗ (n+1)}` as the endomorphism algebra of the free sheaf of
`𝒪_T`-modules of rank `(n+1) ^ (n+1)` induced by a trivialisation `M` of `B` as
`Mat_{n+1}(𝒪_T)`**: the tensor power of `M`, the identification of a tensor power of an
endomorphism algebra with the endomorphism algebra of the tensor power, and the identification of
the tensor power of the free sheaf of rank `n+1` with the free sheaf of rank `(n+1) ^ (n+1)`. -/
def natTensorPowTrivIso {B : AlgebraSheaf T} {n : ℕ} (M : B ≅ matrixAlgebra T (n + 1)) :
    Stacks.TensorPowers.natTensorPow B (n + 1) ≅
      endAlgebra (freeModule T (ULift.{u, 0} (Fin (n + 1) → Fin (n + 1)))) :=
  natTensorPowCongr M (n + 1) ≪≫
    natTensorPowEndAlgebraIso (isFiniteLocallyFree_free (S := T)
      (ULift.{u, 0} (Fin (n + 1)))) n ≪≫
    endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1))

/-- **The comparison automorphism of the two trivialisations of `B^{⊗ (n+1)}` induced by two
trivialisations of `B` is the `(n+1)`-fold tensor power of the comparison automorphism of
`Mat_{n+1}(𝒪_T)`.** The two composites share their last two factors, so the comparison is the
comparison of the first factors conjugated by those; and that conjugate is
`natTensorPowEndConjFree` by definition. -/
theorem natTensorPowTrivIso_inv_comp_hom {B : AlgebraSheaf T} {n : ℕ}
    (M₁ M₂ : B ≅ matrixAlgebra T (n + 1)) :
    (natTensorPowTrivIso M₁).inv ≫ (natTensorPowTrivIso M₂).hom
      = (natTensorPowEndConjFree T n (M₁.symm ≪≫ M₂)).hom := by
  have h1 := trans_inv_comp_trans_hom (natTensorPowCongr M₁ (n + 1))
    (natTensorPowCongr M₂ (n + 1))
    (natTensorPowEndAlgebraIso (isFiniteLocallyFree_free (S := T)
        (ULift.{u, 0} (Fin (n + 1)))) n ≪≫
      endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1)))
  have h2 := symm_trans_conj_hom
    (natTensorPowEndAlgebraIso (isFiniteLocallyFree_free (S := T)
      (ULift.{u, 0} (Fin (n + 1)))) n)
    (endAlgebraCongr (natTensorPowFreeIso T (n + 1) (n + 1)))
    (natTensorPowCongr (M₁.symm ≪≫ M₂) (n + 1))
  rw [natTensorPowCongr_inv_comp_hom] at h1
  exact h1.trans h2.symm

/-- **The comparison automorphism of the two induced trivialisations of `B^{⊗ (n+1)}` fixes
Saltman's projector.** This is the overlap step
`Stacks.EtaleCohomology.BrauerScheme.pointMap_natTensorPowEndConj_altProjFree`, with the
comparison automorphism identified by
`Stacks.EtaleCohomology.BrauerScheme.natTensorPowTrivIso_inv_comp_hom`. -/
theorem pointMap_natTensorPowTrivIso_altProjFree {B : AlgebraSheaf T} {n : ℕ}
    (M₁ M₂ : B ≅ matrixAlgebra T (n + 1)) :
    MonoidalClosed.pointMap ((natTensorPowTrivIso M₁).inv ≫ (natTensorPowTrivIso M₂).hom)
        (altProjFree T (n + 1))
      = altProjFree T (n + 1) := by
  rw [natTensorPowTrivIso_inv_comp_hom]
  exact pointMap_natTensorPowEndConj_altProjFree T n (M₁.symm ≪≫ M₂)

/-- **THE OVERLAP STEP OF [Stacks, Tag 0A2L], IN THE SHAPE ITS CONSUMER WANTS: two
trivialisations of a sheaf of `𝒪_T`-algebras `B` as `Mat_{n+1}(𝒪_T)` read Saltman's projector as
the same point of `B^{⊗ (n+1)}`.** -/
theorem curry'_altProjFree_comp_natTensorPowTrivIso_inv {B : AlgebraSheaf T} {n : ℕ}
    (M₁ M₂ : B ≅ matrixAlgebra T (n + 1)) :
    MonoidalClosed.curry' (altProjFree T (n + 1)) ≫ (natTensorPowTrivIso M₁).inv.hom
      = MonoidalClosed.curry' (altProjFree T (n + 1)) ≫ (natTensorPowTrivIso M₂).inv.hom :=
  (MonoidalClosed.curry'_comp_inv_hom_eq_iff (natTensorPowTrivIso M₁) (natTensorPowTrivIso M₂)
    (altProjFree T (n + 1))).2 (pointMap_natTensorPowTrivIso_altProjFree M₁ M₂)

end Stacks.EtaleCohomology.BrauerScheme

end

end

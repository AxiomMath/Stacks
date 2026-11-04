module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedRelativeTensorUnitor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedExtensionByZeroTensor

/-!
# The unit isomorphism of the relative tensor product of differential graded modules

Let `O` be a sheaf of commutative rings on a site and let `A` be a sheaf of differential graded
`O`-algebras. Regarding `A` as a right differential graded module over itself, the relative
tensor product `A ⊗_A N` with a left differential graded `A`-module `N` is `N`, as a cochain
complex of sheaves of modules: this file constructs that isomorphism and draws the two
consequences that `A` is flat and K-flat as a module over itself.

## Main definitions

* `SheafOfModules.RelativeTensor.dgUnitorIso` is **the unit isomorphism** `A ⊗_A N ≅ N` of
  cochain complexes of sheaves of modules.

## Main results

* `SheafOfModules.RelativeTensor.unitorHom_comm_d`: the degreewise unitor of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedRelativeTensorUnitor.lean` commutes with
  the differentials, which is what makes it a morphism of complexes. The content is the Leibniz
  rule of the left action of `A` on `N`.
* `SheafOfModules.RelativeTensor.ofDifferentialGraded_regularModule`: the right graded module
  underlying the regular right differential graded module is the regular right graded module of
  the underlying graded algebra.
* `SheafOfModules.RelativeTensor.isGradedFlat_ofDifferentialGraded_regularModule` and
  `SheafOfModules.RelativeTensor.isKFlat_regularModule` are conditions (1) and (2) in the
  definition of a good right differential graded module, for `A` as a module over itself. Each
  is one clause of that definition, so neither carries Tag 0FSA: the tag is registered on the
  definition, `SheafOfModules.IsGoodToposBaseChange` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`.

## Implementation notes

The unit isomorphism is a genuine isomorphism of cochain complexes, assembled from the
degreewise isomorphisms by `CategoryTheory.HomologicalComplex.Hom.isoOfComponents`; the
hypothesis of that constructor is the commutation with the differentials, so compatibility with
the differential is proved rather than assumed.

The commutation is checked on a local section `a ⊗ y` through
`SheafOfModules.RelativeTensor.dgTensor_d_tmul`, which computes the differential of `A ⊗_A N`
there. That lemma lives in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedExtensionByZeroTensor.lean`,
which is therefore imported; the alternative was a second copy of it under another name, and
reusing the one proved result was preferred to duplicating it.

On the two sides of the commutation the degrees agree only propositionally, `(p + 1) + q` on one
and `(p + q) + 1` on the other, and both the Leibniz rule of
`SheafOfModules.LeftDifferentialGradedModule` and the shifted indices
`SheafOfModules.RelativeTensor.tensorIndexShiftLeft` and `tensorIndexShiftRight` record that by a
transport. The two transports are along the same equality of integers, so proof irrelevance
identifies them and the proof needs no cast lemma of its own; the index is destructured and its
defining equality substituted first, which removes the transport coming from the unitor itself.

K-flatness is acyclicity of `A ⊗_A N` for acyclic `N`, and it is exactly the unit isomorphism
transported along `CategoryTheory.HomologicalComplex.ExactAt.of_iso`: `A ⊗_A N` is isomorphic to
`N` as a complex, so it is acyclic precisely when `N` is. Flatness as a graded module is the
degreewise statement of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedRelativeTensorUnitor.lean`, applied to the
underlying graded algebra.

## References

* [Stacks Project, Tag 0FRM](https://stacks.math.columbia.edu/tag/0FRM)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

open scoped TensorProduct

universe t m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})]
  {Osharp : Sheaf J CommRingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

namespace RelativeTensor

/-- The right graded module underlying the regular right differential graded module of `A` is
the regular right graded module of the graded algebra underlying `A`. -/
theorem ofDifferentialGraded_regularModule :
    GradedModule.ofDifferentialGraded (DifferentialGradedModule.regularModule A) =
      GradedModule.regularModule A.toGradedAlgebra := rfl

variable (N : LeftDifferentialGradedModule.{t, m, m} A)

section Sheafify

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasWeakSheafify J AddCommGrpCat.{m}]

/-- **The unitor commutes with the differentials.** On a local section `a ⊗ y` this is the
Leibniz rule for the left action of `A` on `N`, the differential of `A ⊗_A N` being
`d(a ⊗ y) = da ⊗ y + (-1)^{deg a} a ⊗ dy`. -/
theorem unitorHom_comm_d (n : ℤ) :
    unitorHom (gN N) n ≫ N.complex.d n (n + 1) =
      (dgTensor (DifferentialGradedModule.regularModule A) N).d n (n + 1) ≫
        unitorHom (gN N) (n + 1) := by
  refine gradedTensor_hom_ext (GradedModule.regularModule A.toGradedAlgebra) (gN N)
    fun p X x y ↦ ?_
  obtain ⟨⟨r, q⟩, h⟩ := p
  subst h
  refine Eq.trans (congrArg (fun z ↦ PresheafOfModules.Hom.app
    (N.complex.d (r + q) (r + q + 1)).val X z)
      (unitorHom_tmul (gN N) (r + q) (⟨(r, q), rfl⟩ : TensorIndex (r + q)) X x y)) ?_
  refine Eq.trans (N.leibniz r q X x y) ?_
  refine Eq.trans ?_ (congrArg (fun z ↦ PresheafOfModules.Hom.app
    (unitorHom (gN N) (r + q + 1)).val X z)
      (dgTensor_d_tmul (DifferentialGradedModule.regularModule A) N (r + q)
        (⟨(r, q), rfl⟩ : TensorIndex (r + q)) X x y)).symm
  refine Eq.trans ?_ (map_add (ConcreteCategory.hom (PresheafOfModules.Hom.app
    (unitorHom (gN N) (r + q + 1)).val X)) _ _).symm
  refine congrArg₂ (fun u w ↦ u + w) ?_ ?_
  · exact (unitorHom_tmul (gN N) (r + q + 1)
      (tensorIndexShiftLeft (⟨(r, q), rfl⟩ : TensorIndex (r + q))) X _ y).symm
  · refine Eq.trans ?_ (map_zsmul (ConcreteCategory.hom (PresheafOfModules.Hom.app
      (unitorHom (gN N) (r + q + 1)).val X)) _ _).symm
    exact congrArg (fun z ↦ (Int.negOnePow r : ℤ) • z)
      (unitorHom_tmul (gN N) (r + q + 1)
        (tensorIndexShiftRight (⟨(r, q), rfl⟩ : TensorIndex (r + q))) X x _).symm

/-- **The unit isomorphism of the relative tensor product of differential graded modules**:
`A ⊗_A N ≅ N` as cochain complexes of sheaves of modules, for `A` a sheaf of differential graded
algebras acting on itself on the right and `N` a left differential graded `A`-module. -/
@[stacks 0FRM "the unit isomorphism A ⊗_A N ≅ N of complexes, for A the regular right module"]
noncomputable def dgUnitorIso :
    dgTensor (DifferentialGradedModule.regularModule A) N ≅ N.complex :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ unitorIso (gN N) n)
    (fun i j hij ↦ by
      obtain rfl : j = i + 1 := hij.symm
      exact unitorHom_comm_d N i)

/-- **Condition (1) of a good differential graded module for the regular module.** A sheaf of
differential graded algebras is flat as a right graded module over itself.

This is one clause of the definition of goodness and so carries no tag of its own; the
definition is `SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
whose first conjunct this discharges for `A` over itself. -/
theorem isGradedFlat_ofDifferentialGraded_regularModule
    (A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)) :
    IsGradedFlat
      (GradedModule.ofDifferentialGraded (DifferentialGradedModule.regularModule A)) :=
  isGradedFlat_regularModule A.toGradedAlgebra

end Sheafify

section KFlat

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

/-- **Condition (2) of a good differential graded module for the regular module.** A sheaf of
differential graded algebras is K-flat as a right differential graded module over itself:
`A ⊗_A N` is isomorphic to `N` as a complex, so it is acyclic whenever `N` is.

This is one clause of the definition of goodness and so carries no tag of its own; the
definition is `SheafOfModules.IsGoodToposBaseChange`, whose second conjunct this discharges for
`A` over itself. -/
theorem isKFlat_regularModule (A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)) :
    IsKFlat (DifferentialGradedModule.regularModule A) :=
  fun N hN i ↦ (hN i).of_iso (dgUnitorIso N).symm

end KFlat

end RelativeTensor

end SheafOfModules

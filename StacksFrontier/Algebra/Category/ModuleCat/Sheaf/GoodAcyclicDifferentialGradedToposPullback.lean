module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackAcyclic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposPullbackGood
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodAcyclicDifferentialGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforward

/-!
# Pullbacks of good acyclic differential graded modules

Let `(Sh(C), O)` be a ringed topos, let `A` be a sheaf of differential graded `O`-algebras and
let `P` be a good acyclic right differential graded `A`-module. Clause (2) of Tag 0FSI: for every
morphism of ringed topoi `(f, f♯) : (Sh(C'), O') ⟶ (Sh(C), O)`, every sheaf of differential graded
`O'`-algebras `A'` and every homomorphism `φ : f⁻¹A ⟶ A'` of differential graded
`f⁻¹O`-algebras, the pullback `f^*P` is acyclic and good.

The homomorphism `φ` is written in its adjoint form, a unital `ψ : A ⟶ f_*A'`, and the pullback
`f^*P` is an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`; such an object exists
(`exists_toposBaseChange`) and is unique up to unique isomorphism, and the theorem is stated for
every one of them. Goodness is `SheafOfModules.IsGoodToposBaseChange`, the definition of Tag 0FSA.

## Main results

* `SheafOfModules.DifferentialGradedModule.acyclic_dgTensor_of_isGood_of_acyclic_topos`:
  **Tag 0FSI (1)**, at a ringed topos.
* `SheafOfModules.DifferentialGradedModule.exists_toposCorepresentableBy_and_acyclic_and_isGood`:
  **Tag 0FSI (2)**.
* `SheafOfModules.DifferentialGradedModule.acyclic_and_isGood_toposPullbackModule`: the case
  `A' = f^*A`, `φ` the identity, for the pullback `f^*P = toposPullbackModule f P` itself.

The registered forms are at ringed topoi `RingedTopos.{u, u, u}`, where every instance the
constructions need is found; `..._of_univ` are the same statements at the general universes.

## Implementation notes

Both halves are proved elsewhere and only assembled here: the acyclicity is
`acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange` (reading `f^*P` as
`f⁻¹P ⊗_{f⁻¹A} A'`, a base change over `(Sh(C'), f⁻¹O)`, and applying clause (1) there), the
goodness is `SheafOfModules.isGoodToposBaseChange_of_toposCorepresentableBy` (a base change of
`f^*P` is a base change of `P` along a composite). The coefficient universe is the universe
`max u v` of the source site `C' : Type u` with `Category.{v} C'`, where sheaves of modules on it
live; the target site may have its own universes.

## References

* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe v₁ u₁ v₂ u₂

namespace SheafOfModules.DifferentialGradedModule

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, max u₁ v₁}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify Y.J AddCommGrpCat.{max u₁ v₁}] [HasSheafify Y.J (Type (max u₁ v₁))]
  {X : AlgebraicGeometry.RingedTopos.{v₁, u₁, max u₁ v₁}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max u₁ v₁} RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget RingCat.{max u₁ v₁})]
  [X.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max u₁ v₁})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁}]
  [HasSheafify X.J AddCommGrpCat.{max u₁ v₁}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable {A : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁} (toRingCat Y.J Y.O)}
  {P : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} A}

/-- **Tag 0FSI (2).** Let `P` be a good acyclic right differential graded `A`-module. For every
morphism of ringed topoi `f : (Sh(C'), O') ⟶ (Sh(C), O)`, every sheaf of differential graded
`O'`-algebras `B` and every unital homomorphism `ψ : A ⟶ f_*B` (the adjoint form of a
homomorphism `f⁻¹A ⟶ B` of differential graded `f⁻¹O`-algebras), the pullback of `P` along
`(f, B, ψ)` — an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)` — exists, and every such object is
acyclic and good. -/
theorem exists_toposCorepresentableBy_and_acyclic_and_isGood_of_univ
    (hP : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} P) (hac : P.complex.Acyclic)
    (f : RingedToposHom X Y) (B : DifferentialGradedAlgebra.{max u₁ v₁, max u₁ v₁}
      (toRingCat X.J X.O))
    (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules f) B) (hψ : ψ.IsUnital) :
    (∃ T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B,
        Nonempty ((toposPushforward (toposDirectImageModules f) ψ hψ ⋙
          coyoneda.obj (Opposite.op P)).CorepresentableBy T)) ∧
      ∀ T : DifferentialGradedModule.{max u₁ v₁, max u₁ v₁, max u₁ v₁} B,
        (toposPushforward (toposDirectImageModules f) ψ hψ ⋙
            coyoneda.obj (Opposite.op P)).CorepresentableBy T →
          T.complex.Acyclic ∧ IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} T :=
  ⟨exists_toposBaseChange f ψ hψ P, fun _ eT =>
    ⟨acyclic_of_toposCorepresentableBy_of_isGoodToposBaseChange f ψ hψ hP hac eT,
      isGoodToposBaseChange_of_toposCorepresentableBy f ψ hψ hP eT⟩⟩

/-- **The pullback `f^*P` of a good acyclic module is acyclic and good**: Tag 0FSI (2) at the
universal base change `(f, f^*A, η)`. -/
theorem acyclic_and_isGood_toposPullbackModule_of_univ
    (hP : IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} P) (hac : P.complex.Acyclic)
    (f : RingedToposHom X Y) :
    (toposPullbackModule f P).complex.Acyclic ∧
      IsGoodToposBaseChange.{max u₁ v₁, v₁, u₁} (toposPullbackModule f P) :=
  (exists_toposCorepresentableBy_and_acyclic_and_isGood_of_univ hP hac f _ _
    (isUnital_toposPullbackUnit f A)).2 _ (toposPullbackCorepresentableBy f P)

section Tag

universe u

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **Tag 0FSI (1).** *"Let `(C, O)` be a ringed site. Let `A` be a sheaf of differential graded
algebras on `(C, O)`. Let `P` be a good acyclic right differential graded `A`-module. Then for any
differential graded left `A`-module `N` the tensor product `P ⊗_A N` is acyclic."*

Goodness is `SheafOfModules.IsGoodToposBaseChange`, the definition of Tag 0FSA. -/
@[stacks 0FSI "part (1)"]
theorem acyclic_dgTensor_of_isGood_of_acyclic_topos {Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
    {P : DifferentialGradedModule.{u, u, u} A} (good : IsGoodToposBaseChange.{u, u, u} P)
    (acyclic : P.complex.Acyclic) (N : LeftDifferentialGradedModule.{u, u, u} A) :
    (RelativeTensor.dgTensor P N).Acyclic :=
  acyclic_dgTensor_of_isGoodToposBaseChange_of_acyclic good acyclic N

/-- **Tag 0FSI (2).** *"Let `(C, O)` be a ringed site. Let `A` be a sheaf of differential graded
algebras on `(C, O)`. Let `P` be a good acyclic right differential graded `A`-module. Then for any
morphism `(f, f♯) : (Sh(C'), O') ⟶ (Sh(C), O)` of ringed topoi and any differential graded
`O'`-algebra `A'` and any map `φ : f⁻¹A ⟶ A'` of differential graded `f⁻¹O`-algebras the pullback
`f^*P` is acyclic and good."*

The map `φ` is written in its adjoint form, a unital `ψ : A ⟶ f_*A'`. The pullback `f^*P` along
`(f, A', ψ)` is an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`: one exists, and every one is
acyclic and good, goodness being `SheafOfModules.IsGoodToposBaseChange`, the definition of
Tag 0FSA. -/
@[stacks 0FSI "part (2)"]
theorem exists_toposCorepresentableBy_and_acyclic_and_isGood
    {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
    {P : DifferentialGradedModule.{u, u, u} A} (good : IsGoodToposBaseChange.{u, u, u} P)
    (acyclic : P.complex.Acyclic) (f : RingedToposHom X Y)
    (A' : DifferentialGradedAlgebra.{u, u} (toRingCat X.J X.O))
    (ψ : A ⟶ toposPushforwardAlgebra (toposDirectImageModules (X := X) (Y := Y) f) A')
    (hψ : ψ.IsUnital) :
    (∃ T : DifferentialGradedModule.{u, u, u} A',
        Nonempty ((toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) ψ hψ ⋙
          coyoneda.obj (Opposite.op P)).CorepresentableBy T)) ∧
      ∀ T : DifferentialGradedModule.{u, u, u} A',
        (toposPushforward (toposDirectImageModules (X := X) (Y := Y) f) ψ hψ ⋙
            coyoneda.obj (Opposite.op P)).CorepresentableBy T →
          T.complex.Acyclic ∧ IsGoodToposBaseChange.{u, u, u} T :=
  exists_toposCorepresentableBy_and_acyclic_and_isGood_of_univ good acyclic f A' ψ hψ

/-- **The pullback `f^*P` of a good acyclic module is acyclic and good**, at the universal base
change `(f, f^*A, η)`. -/
theorem acyclic_and_isGood_toposPullbackModule {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
    {A : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}
    {P : DifferentialGradedModule.{u, u, u} A} (good : IsGoodToposBaseChange.{u, u, u} P)
    (acyclic : P.complex.Acyclic) (f : RingedToposHom X Y) :
    (toposPullbackModule f P).complex.Acyclic ∧
      IsGoodToposBaseChange.{u, u, u} (toposPullbackModule f P) :=
  acyclic_and_isGood_toposPullbackModule_of_univ good acyclic f

end Tag

end SheafOfModules.DifferentialGradedModule

end

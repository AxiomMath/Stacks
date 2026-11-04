module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAlgebraResolutionQuasiIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedAlgebraGood
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Good resolutions of sheaves of differential graded algebras

Let `(C, O)` be a ringed site and let `(B, d)` be a sheaf of differential graded `O`-algebras.
**Tag 0FU2**: there is a quasi-isomorphism of sheaves of differential graded `O`-algebras
`(A, d) ⟶ (B, d)` such that `A` is graded flat and K-flat as a complex of `O`-modules, and stays
so after pullback along every morphism of ringed topoi.

The algebra `A` is the free differential graded algebra `O⟨⨿ₖ Sₖ⟩` on all the generators of the
tower `A₀ ⟶ A₁ ⟶ ⋯ ⟶ B` of the source, built in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAlgebraResolutionTower.lean`;
`A ⟶ B` is a quasi-isomorphism by
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedAlgebraResolutionQuasiIso.lean`;
and its differential is triangular, so `A` is good by Tag 0FU1.

## Main results

* `SheafOfModules.exists_good_quasiIso_differentialGradedAlgebra_of_instances`: the resolution
  over any ringed topos carrying the sheafification instances of the construction.
* `SheafOfModules.exists_good_quasiIso_differentialGradedAlgebra`: **Tag 0FU2**, at a ringed
  topos in one universe.

## Implementation notes

The flatness conditions of the source, together with their persistence after pullback, are
read as goodness in the sense of Tag 0FSA, `SheafOfModules.IsGoodToposBaseChange`, of the
underlying complex of `A` regarded as a right differential graded module over `(O, 0)`, the
structure sheaf placed in degree zero (`SheafOfModules.DifferentialGradedAlgebra.toUnitModule`).
Its first two conditions say that `A` is flat as a graded `O`-module and K-flat as a complex of
`O`-modules; its third says that along every morphism of ringed topoi `f`, every sheaf of
differential graded algebras `B'` on the source of `f` and every unital homomorphism
`(O, 0) ⟶ f_*B'`, the pullback of `A` exists and is again flat as a graded module and K-flat.
Taking `B' = (O', 0)` is the source's clause, so this reading is at least as strong as the
source's. It is the reading under which Tag 0FU1 is proved in this development.

The construction is carried out over an arbitrary ringed topos with the sheafification
instances it uses (`exists_good_quasiIso_differentialGradedAlgebra_of_instances`); the tag is
registered at a ringed topos in one universe, where every one of those instances is discharged.
The universes of the construction are written out in the proof: left to unification, the
existential's universe metavariables are fixed to `0` before the algebra is seen.

## References

* [Stacks Project, Tag 0FU2](https://stacks.math.columbia.edu/tag/0FU2)
* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules

section General

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]

/-- **A good resolution of a sheaf of differential graded algebras**, over any ringed topos
carrying the sheafification instances of the construction. Tag 0FU2 is
`SheafOfModules.exists_good_quasiIso_differentialGradedAlgebra`. -/
theorem exists_good_quasiIso_differentialGradedAlgebra_of_instances
    (B : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)) :
    ∃ (A : DifferentialGradedAlgebra.{w, w} (toRingCat Y.J Y.O)) (f : A ⟶ B),
      (∀ U : Y.Cᵒᵖ, (f.toHomologicalComplex.f 0).val.app U (A.one.eval U) = B.one.eval U) ∧
        QuasiIso f.toHomologicalComplex ∧
          IsGoodToposBaseChange.{w, v₁, u₁} (DifferentialGradedAlgebra.toUnitModule A) :=
  ⟨resolutionAlgebra.{w, v₂, u₂} B, resolutionHom.{w, v₂, u₂} B,
    resolutionHom_isUnital.{w, v₂, u₂} B, quasiIso_resolutionHom.{w, v₂, u₂} B,
    freeDGAlgebra_isGoodToposBaseChange (resolutionGens.{w, v₂, u₂} B) (resolutionδ B)
      (resolution_hδ B) (resolutionδ_isTriangular B)⟩

end General

section Tag

universe u

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

variable {Y : AlgebraicGeometry.RingedTopos.{u, u, u}}

/-- **Tag 0FU2.** *"Let `(C, O)` be a ringed site. Let `(B, d)` be a differential graded
`O`-algebra. There exists a quasi-isomorphism of differential graded `O`-algebras
`(A, d) ⟶ (B, d)` such that `A` is graded flat and K-flat as a complex of `O`-modules and such
that the same is true after pullback by any morphism of ringed topoi."*

The homomorphism is unital; graded flatness, K-flatness and their persistence after pullback are
the goodness of Tag 0FSA of `A` over `(O, 0)`. -/
@[stacks 0FU2]
theorem exists_good_quasiIso_differentialGradedAlgebra
    (B : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)) :
    ∃ (A : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)) (f : A ⟶ B),
      (∀ U : Y.Cᵒᵖ, (f.toHomologicalComplex.f 0).val.app U (A.one.eval U) = B.one.eval U) ∧
        QuasiIso f.toHomologicalComplex ∧
          IsGoodToposBaseChange.{u, v₁, u₁}
            (DifferentialGradedAlgebra.toUnitModule (Osharp := Y.O) A) :=
  exists_good_quasiIso_differentialGradedAlgebra_of_instances.{u, v₁, u₁, u, u} (Y := Y) B

end Tag

end SheafOfModules

end

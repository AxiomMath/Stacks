module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.CompactHomology

/-!
# Trivial duality between group cohomology and group homology

Let `G` be a topological group and `M` a discrete `G`-module. The trivial duality of
[Stacks, Tag 03VI] identifies the homology of the compact `G`-module `M^∧ = Hom(M, S¹)` with the
dual of the cohomology of `M`:

`H_i(G, M^∧) ≅ Hⁱ(G, M)^∧`,

naturally in `M`, where on the right `Hⁱ(G, M)` is a discrete abelian group and `(-)^∧` its
Pontryagin dual, a compact abelian group. The anti-equivalence `M ↦ M^∧` takes injective
resolutions of `M` to projective resolutions of `M^∧`, the duality functor on discrete abelian
groups is exact (it is an anti-equivalence), and in degree zero the coinvariants of `M^∧` are
dual to the invariants of `M` (`Stacks.GroupHomology.compactCoinvariantsDualIso`).

## Main definitions

* `Stacks.GroupHomology.trivialGroupModule`: an abelian group as a discrete module over the
  trivial group.
* `Stacks.GroupHomology.trivialGroupModuleEquivalence`: abelian groups are discrete modules over
  the trivial group.
* `Stacks.GroupHomology.addCommGrpDual`: the Pontryagin dual `A ↦ A^∧ = Hom(A, S¹)` of a discrete
  abelian group, as a compact abelian group; it is exact.
* `Stacks.GroupHomology.compactDualCoinvariantsIso G`: `(M^∧)_G ≅ (M^G)^∧`, naturally in the
  discrete `G`-module `M`.
* `Stacks.GroupHomology.groupHomologyCompactDualIso G i`: the trivial duality
  `H_i(G, M^∧) ≅ Hⁱ(G, M)^∧`, naturally in `M`.

## Implementation notes

The cohomology `Hⁱ(G, -)` is `continuousGroupCohomologyFunctor`, defined through the derived
category with the instance `HasDerivedCategory.standard`; the proof of the trivial duality uses
the same instance, so that it computes that functor.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Stacks.GroupCohomology

universe u v

namespace Stacks.GroupHomology

section TrivialGroup

/-- An abelian group, as a discrete module over the trivial group. -/
def trivialGroupModuleObj (A : AddCommGrpCat.{v}) : ContinuousGModule.{0, v} PUnit.{1} :=
  letI := trivialDistribMulAction A
  ofDistribMulAction (G := PUnit.{1}) (M := A)
    (isContinuous_ofDistribMulAction_iff.mpr fun _ ↦ by
      convert isOpen_univ
      exact Set.eq_univ_of_forall fun _ ↦ rfl)

/-- An abelian group, as a discrete module over the trivial group, functorially. -/
def trivialGroupModule : AddCommGrpCat.{v} ⥤ ContinuousGModule.{0, v} PUnit.{1} where
  obj := trivialGroupModuleObj
  map {A B} f := (gModuleHomEquiv PUnit.{1} (trivialGroupModuleObj A)
    (trivialGroupModuleObj B)).symm ⟨f.hom, fun _ _ ↦ rfl⟩
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The underlying abelian group of a trivial module is the group itself. -/
def trivialGroupModuleCompUnderlyingIso :
    trivialGroupModule.{v} ⋙ trivialGroupModuleUnderlying.{v} ≅ 𝟭 AddCommGrpCat.{v} :=
  NatIso.ofComponents (fun A ↦ AddEquiv.toAddCommGrpIso (AddEquiv.refl A))
    fun _ ↦ AddCommGrpCat.ext fun _ ↦ rfl

/-- A discrete module over the trivial group is the trivial module on its underlying group. -/
def underlyingCompTrivialGroupModuleIso :
    trivialGroupModuleUnderlying.{v} ⋙ trivialGroupModule.{v} ≅
      𝟭 (ContinuousGModule.{0, v} PUnit.{1}) :=
  NatIso.ofComponents
    (fun X ↦ isoOfAddEquiv (AddEquiv.refl X.obj.obj.V) fun g x ↦ by
      change x = (X.obj.obj.ρ g).asHom.hom x
      rw [Subsingleton.elim g 1, map_one]
      rfl)
    fun _ ↦ by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      exact ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- Abelian groups are the discrete modules over the trivial group. -/
def trivialGroupModuleEquivalence : AddCommGrpCat.{v} ≌ ContinuousGModule.{0, v} PUnit.{1} :=
  CategoryTheory.Equivalence.mk trivialGroupModule trivialGroupModuleUnderlying
    trivialGroupModuleCompUnderlyingIso.symm underlyingCompTrivialGroupModuleIso

/-- **The Pontryagin dual of a discrete abelian group**, `A ↦ A^∧ = Hom(A, S¹)`, as a compact
abelian group: the dual of `A` viewed as a discrete module over the trivial group. -/
def addCommGrpDual : AddCommGrpCat.{v}ᵒᵖ ⥤ CompactAddCommGrp.{v} :=
  (trivialGroupModuleEquivalence.op.trans (compactDualEquivalence.{0, v} PUnit.{1})).functor

/-- The functor `addCommGrpDual` is the dual of the trivial module. -/
lemma addCommGrpDual_eq :
    addCommGrpDual.{v} = trivialGroupModule.op ⋙ compactDual.{0, v} PUnit.{1} := rfl

instance : addCommGrpDual.{v}.IsEquivalence :=
  inferInstanceAs (trivialGroupModuleEquivalence.op.trans
    (compactDualEquivalence.{0, v} PUnit.{1})).functor.IsEquivalence

instance : addCommGrpDual.{v}.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The duality of discrete abelian groups is exact**: it is an anti-equivalence onto compact
abelian groups, so it preserves finite limits and colimits, hence homology. -/
instance : addCommGrpDual.{v}.PreservesHomology := inferInstance

end TrivialGroup

section Duality

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A natural isomorphism `F ≅ F'` of functors out of an opposite category, as a natural
isomorphism `F'.rightOp ≅ F.rightOp`. -/
def rightOpIsoOfIso {C D : Type*} [Category* C] [Category* D] {F F' : Cᵒᵖ ⥤ D} (α : F ≅ F') :
    F'.rightOp ≅ F.rightOp :=
  NatIso.ofComponents (fun X ↦ (α.app (op X)).op)
    fun f ↦ Quiver.Hom.unop_inj (by simp)

/-- **The coinvariants of the dual are the dual of the invariants**: `(M^∧)_G ≅ (M^G)^∧`,
naturally in the discrete `G`-module `M`. It is obtained from
`Stacks.GroupHomology.compactCoinvariantsDualIso`, the characters of `(M^∧)_G` being the
invariants of `M^∧^∧ = M`, by Pontryagin duality for compact abelian groups. -/
def compactDualCoinvariantsIso :
    (compactDualEquivalence.{u, v} G).functor ⋙ compactCoinvariantsFunctor.{u, v} G ≅
      (continuousGModuleInvariants.{u, v} G).op ⋙ addCommGrpDual.{v} :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (compactDual G ⋙ compactCoinvariantsFunctor G)
      (compactEvaluationIso.{0, v} PUnit.{1}) ≪≫
    Functor.isoWhiskerLeft (compactDual G ⋙ compactCoinvariantsFunctor G)
      (Functor.isoWhiskerRight
        (rightOpIsoOfIso
          (Functor.isoWhiskerLeft (discreteDual.{0, v} PUnit.{1})
              underlyingCompTrivialGroupModuleIso ≪≫ Functor.rightUnitor _))
        (compactDual.{0, v} PUnit.{1})) ≪≫
    Functor.isoWhiskerLeft (compactDual G)
      (Functor.isoWhiskerRight
        (rightOpIsoOfIso (Functor.isoWhiskerRight (compactCoinvariantsDualIso.{u, v} G)
          trivialGroupModule.{v}).symm)
        (compactDual.{0, v} PUnit.{1})) ≪≫
    Functor.isoWhiskerRight (NatIso.op (discreteEvaluationIso.{u, v} G))
      ((continuousGModuleInvariants.{u, v} G).op ⋙ addCommGrpDual.{v}) ≪≫
    Functor.leftUnitor _

/-- **Trivial duality** `Hⁱ(G, M)^∧ = H_i(G, M^∧)`: for a discrete `G`-module `M`, the homology
of the compact `G`-module `M^∧ = Hom(M, S¹)` is the Pontryagin dual of the cohomology of `M`,
naturally in `M`. -/
@[stacks 03VI "trivial duality H^i(G, M)^∧ = H_i(G, M^∧)"]
def groupHomologyCompactDualIso (i : ℕ) :
    compactDual.{u, max u v} G ⋙ groupHomologyFunctor.{u, v} G i ≅
      (continuousGroupCohomologyFunctor.{u, v} G i).op ⋙ addCommGrpDual.{max u v} :=
  letI := HasDerivedCategory.standard (ContinuousGModule.{u, max u v} G)
  letI := HasDerivedCategory.standard AddCommGrpCat.{max u v}
  (compactDualEquivalence.{u, max u v} G).leftDerivedCompRightDerivedPlusIsoOfAntiEquivalence
    (continuousGModuleInvariants.{u, max u v} G) (compactCoinvariantsFunctor.{u, max u v} G)
    addCommGrpDual.{max u v} (compactDualCoinvariantsIso.{u, max u v} G) i

/-- The objectwise form of the trivial duality: `H_i(G, M^∧) ≅ Hⁱ(G, M)^∧` for a discrete
`G`-module `M`. -/
def groupHomologyCompactDualObjIso (i : ℕ) (M : ContinuousGModule.{u, max u v} G) :
    groupHomology.{u, v} G i ((compactDual.{u, max u v} G).obj (op M)) ≅
      addCommGrpDual.{max u v}.obj (op (continuousGroupCohomology.{u, v} G i M)) :=
  (groupHomologyCompactDualIso.{u, v} G i).app (op M)

end Duality

end Stacks.GroupHomology

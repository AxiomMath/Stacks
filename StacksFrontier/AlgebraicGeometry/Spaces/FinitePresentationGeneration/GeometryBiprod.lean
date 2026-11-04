module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationBiproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits

/-!
# A biproduct of sheaves of modules of finite presentation on a site

Let `R` be a sheaf of rings on a site `C` and let `A` and `B` be sheaves of `R`-modules of
finite presentation.  Then `A ⊞ B` is of finite presentation.

The proof is the site version of `AlgebraicGeometry.isFinitePresentation_biprod`: `A` and `B`
have finite presentations over the members of two covering families; the objects admitting an
arrow into a member of each family again cover, over such an object both presentations restrict
(`Stacks.SheafOfModules.LocalKernel.presentationOver`), and the biproduct of the two restricted
presentations (`SheafOfModules.Presentation.biprod`) presents the biproduct of the restrictions,
which is the restriction of the biproduct because restriction to a slice is additive.

## Main results

* `Stacks.SheafOfModules.overBiprodIso`: the restriction of a biproduct to a slice is the
  biproduct of the restrictions.
* `Stacks.SheafOfModules.isFinitePresentation_biprod`: a binary biproduct of sheaves of modules
  of finite presentation on a site is of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits SheafOfModules

universe u v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective

/-- Restriction of sheaves of modules to a slice is additive: it is computed sectionwise. -/
instance overFunctor_additive_of_site (U : C) : (overFunctor.{u} R U).Additive where
  map_add := rfl

/-- The restriction of a binary biproduct of sheaves of modules to the slice over `U` is the
biproduct of the restrictions: restriction is additive. -/
noncomputable def overBiprodIso (A B : _root_.SheafOfModules.{u} R) [HasBinaryBiproduct A B]
    (U : C) : (A ⊞ B).over U ≅ (A.over U) ⊞ (B.over U) :=
  haveI := preservesBinaryBiproduct_of_preservesBiproduct (overFunctor.{u} R U) A B
  (overFunctor R U).mapBiprod A B

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A binary biproduct of sheaves of modules of finite presentation is of finite
presentation.** -/
theorem isFinitePresentation_biprod (A B : _root_.SheafOfModules.{u} R) [HasBinaryBiproduct A B]
    (hA : A.IsFinitePresentation) (hB : B.IsFinitePresentation) :
    (A ⊞ B).IsFinitePresentation := by
  classical
  let : ∀ (V W : C) (f : W ⟶ V), PreservesColimitsOfSize.{u, u} (overMap.{u} R f) :=
    fun _ _ f => Stacks.SheafOfModules.overMap_preservesColimits R f
  obtain ⟨qA, hqA⟩ := hA.exists_quasicoherentData
  obtain ⟨qB, hqB⟩ := hB.exists_quasicoherentData
  let I := Σ i : qA.I, Σ j : qB.I, {V : C // Nonempty ((V ⟶ qA.X i) × (V ⟶ qB.X j))}
  let Y (z : I) : C := z.2.2.1
  have hP (z : I) := hqA.isFinite_presentation z.1
  have hQ (z : I) := hqB.isFinite_presentation z.2.1
  let P (z : I) := Stacks.SheafOfModules.LocalKernel.presentationOver
    (Classical.choice z.2.2.2).1 (qA.presentation z.1)
  let Q (z : I) := Stacks.SheafOfModules.LocalKernel.presentationOver
    (Classical.choice z.2.2.2).2 (qB.presentation z.2.1)
  let T (z : I) := (P z).biprod (Q z)
  have hcov : J.CoversTop Y := fun W =>
    J.transitive (qA.coversTop W) (Sieve.ofObjects Y W) (by
      intro V f hf
      refine J.superset_covering ?_ (qB.coversTop V)
      intro Z g hg
      obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff qA.X f).mp hf
      obtain ⟨j, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff qB.X g).mp hg
      exact (Sieve.mem_ofObjects_iff Y (g ≫ f)).2 ⟨⟨i, j, Z, ⟨(g ≫ b, c)⟩⟩, ⟨𝟙 Z⟩⟩)
  let q : (A ⊞ B).QuasicoherentData :=
    { I := I
      X := Y
      coversTop := hcov
      presentation := fun z => (T z).ofIsIso (overBiprodIso A B (Y z)).inv }
  refine ⟨⟨q, ⟨fun z => ?_⟩⟩⟩
  have : (T z).IsFinite := Presentation.isFinite_biprod _ _
  infer_instance

end Stacks.SheafOfModules

end

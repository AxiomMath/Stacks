module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafifiedDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedModules

/-!
# The underlying module of the ungraded realisation of a graded module

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedModules.lean` builds the ungraded
realisation `⨁ₙ Mₙ` of a graded module over a graded algebra of presheaves of modules: a presheaf
of modules over the ungraded realisation of the algebra, and — by sheafification — a sheaf of
modules over it. This file answers what that sheaf of modules is *as a module over the base
sheaf of rings* `R`: it is the coproduct `∐ₙ Mₙ` of the homogeneous pieces.

This is for a graded *module* what
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafifiedDirectSum.lean` is for a graded
*algebra*, and the proof has the same two steps: the sheafification unit is a locally bijective
morphism of presheaves of `R`-modules from the objectwise direct sum into the realisation, so
`Stacks.sheafifyIsoOfLocallyBijective` identifies the realisation with the sheafification of that
direct sum, and `Stacks.sheafifyDirectSumIso` identifies the latter with the coproduct.

## Main definitions

* `Stacks.RightGradedModule.restrictScalarsUnit`: the sheafification unit of the ungraded
  realisation, read as a morphism of presheaves of `R`-modules out of the objectwise direct sum of
  the homogeneous pieces.
* `Stacks.RightGradedModule.directSumIsoRestrictScalars`: **the ungraded realisation of a graded
  module, as a module over the base sheaf of rings, is the sheafification of the objectwise
  direct sum of its homogeneous pieces.**
* `SheafOfModules.GradedModule.coprodIsoUngradedSheafModule`: **the underlying `R`-module of the
  ungraded realisation of a graded module over a sheaf of graded algebras is the coproduct
  `∐ₙ Mₙ` of its homogeneous pieces.**

## Main results

* `Stacks.RightGradedModule.restrictScalarsUnit_app`: the comparison morphism is the sheafification
  unit on sections, which is what makes it locally bijective.

## Implementation notes

**The one piece of input is `Stacks.RightGradedModule.act_structureMap`.** The sheafification unit
is semilinear over the ungraded realisation of the *algebra*; what is needed is semilinearity over
the base sheaf of rings `R`, along `σ : R ⟶ T`. Restricting the scalars of the unit along
`Stacks.GradedAlgebra.structureHom` turns the first into the second, and the module structure one
gets that way is the direct sum's own `R`-action precisely because
`Stacks.RightGradedModule.act_structureMap` says the realisation's action by `A.structureMap X r`
*is* the action of `r` on the direct sum. Without that lemma the comparison morphism is not even
`R`-linear.

**Local bijectivity is read off the sheafification unit of the underlying abelian presheaf.**
`CategoryTheory.Presheaf.IsLocallyInjective` and `IsLocallySurjective` are propositions about the
maps on sections and about a sieve depending only on the source presheaf, and the source presheaf
here is `Stacks.directSumAb` on the nose, so the two instances for
`CategoryTheory.toSheafify` apply directly; no comparison of presheaves is needed. This is the
same device `Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom` uses.

**All degrees, not only the nonnegative ones.** The algebra of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafifiedDirectSum.lean` is reindexed onto `ℕ`
through `Stacks.directSumNatToInt`, because a relative spectrum consumes a nonnegatively graded
algebra. A graded module has no such restriction, so the coproduct here is over all of `ℤ` and
no vanishing hypothesis on the negative pieces is needed.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.RightGradedModule

section Comparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {ι : Type} [DecidableEq ι] [AddMonoid ι] {P Q : ι → PresheafOfModules.{w} R.obj}
  {A : GradedAlgebra P} (M : RightGradedModule A Q) (hadd : ∀ i j : ι, i + j = j + i)
  (hc : ∀ (i j : ι) (W : Cᵒᵖ) (x : (P i).obj W) (y : (P j).obj W),
    HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))
  {T : Sheaf J RingCat.{w}} (α : A.totalPresheaf ⟶ T.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (σ : R ⟶ T)

/-- The ungraded realisation of a graded module, sheafified along a locally bijective morphism
`α` out of the ungraded realisation of the algebra: a sheaf of modules over the target of `α`. -/
noncomputable def sheafifiedTotal : SheafOfModules.{w} T :=
  (PresheafOfModules.sheafification α).obj (M.totalPresheafModule hadd hc)

/-- The sheafification unit of the ungraded realisation, as a morphism of presheaves of modules
over the ungraded realisation of the algebra. -/
noncomputable def totalUnitHom :
    M.totalPresheafModule hadd hc ⟶ (PresheafOfModules.restrictScalars α).obj
      ((SheafOfModules.forget T).obj (M.sheafifiedTotal hadd hc α)) :=
  (PresheafOfModules.sheafificationAdjunction α).unit.app _

variable (fac : A.structureHom ≫ α = σ.hom)

/-- **The comparison morphism**: the sheafification unit of the ungraded realisation, read as a
morphism of presheaves of modules over the base sheaf of rings out of the objectwise direct sum
of the homogeneous pieces.

It is `R`-linear because the realisation's action by the image of the structure map is the
direct sum's own action, which is `Stacks.RightGradedModule.act_structureMap`. -/
noncomputable def restrictScalarsUnit :
    directSum Q ⟶ ((SheafOfModules.restrictScalars.{w} σ).obj
      (M.sheafifiedTotal hadd hc α)).val where
  app X := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (σ.hom.app X).hom).obj
        ((M.sheafifiedTotal hadd hc α).val.obj X))
    { toFun := fun z => (M.totalUnitHom hadd hc α).app X z
      map_add' := fun z z' => map_add ((M.totalUnitHom hadd hc α).app X).hom z z'
      map_smul' := fun r z => by
        have hr : (α.app X).hom (A.structureMap X r) = (σ.hom.app X).hom r :=
          congrArg (fun f : R.obj ⟶ T.obj => (f.app X).hom r) fac
        refine Eq.trans ?_ (Eq.trans
          (((M.totalUnitHom hadd hc α).app X).hom.map_smul (A.structureMap X r) z) ?_)
        · exact congrArg (fun y => ((M.totalUnitHom hadd hc α).app X).hom y)
            (M.act_structureMap r z).symm
        · have key : ∀ (t t' : T.obj.obj X)
              (y : (M.sheafifiedTotal hadd hc α).val.obj X), t = t' → t • y = t' • y :=
            fun _ _ _ h => by rw [h]
          exact key ((α.app X).hom (A.structureMap X r)) ((σ.hom.app X).hom r)
            (((M.totalUnitHom hadd hc α).app X).hom z) hr }
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    exact PresheafOfModules.naturality_apply (M.totalUnitHom hadd hc α) f z

include fac

/-- The comparison morphism is locally injective, being the sheafification unit of the
objectwise direct sum on sections. -/
lemma isLocallyInjective_restrictScalarsUnit :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf R.obj).map (M.restrictScalarsUnit hadd hc α σ fac)) :=
  ⟨fun x y h => Presheaf.equalizerSieve_mem J
    (CategoryTheory.toSheafify J (M.totalPresheafModule hadd hc).presheaf) x y h⟩

/-- The comparison morphism is locally surjective, being the sheafification unit of the
objectwise direct sum on sections. -/
lemma isLocallySurjective_restrictScalarsUnit :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (M.restrictScalarsUnit hadd hc α σ fac)) :=
  ⟨fun s => Presheaf.imageSieve_mem J
    (CategoryTheory.toSheafify J (M.totalPresheafModule hadd hc).presheaf) s⟩

/-- **The ungraded realisation of a graded module, read as a module over the base sheaf of rings,
is the sheafification of the objectwise direct sum of its homogeneous pieces.** -/
noncomputable def directSumIsoRestrictScalars :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (directSum Q) ≅
      (SheafOfModules.restrictScalars.{w} σ).obj (M.sheafifiedTotal hadd hc α) :=
  sheafifyIsoOfLocallyBijective (M.restrictScalarsUnit hadd hc α σ fac)
    (M.isLocallyInjective_restrictScalarsUnit hadd hc α σ fac)
    (M.isLocallySurjective_restrictScalarsUnit hadd hc α σ fac)

end Comparison

end Stacks.RightGradedModule

namespace SheafOfModules

open CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A : GradedAlgebra.{w, w} R}

/-- **The underlying `R`-module of the ungraded realisation of a graded module over a sheaf of
graded algebras is the coproduct `∐ₙ Mₙ` of its homogeneous pieces.**

This is `SheafOfModules.GradedModule.ungradedSheafModule` with its scalars restricted along
`SheafOfModules.GradedAlgebra.ungradedStructureMap`, which is the shape in which quasi-coherence
of the realisation over the base is asked for. -/
noncomputable def GradedModule.coprodIsoUngradedSheafModule (F : GradedModule.{w, w, w} A)
    (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) [HasCoproduct F.piece] :
    (∐ F.piece) ≅
      (SheafOfModules.restrictScalars.{w} A.ungradedStructureMap).obj
        (F.ungradedSheafModule hc) :=
  (Stacks.sheafifyDirectSumIso F.piece).symm ≪≫
    F.toPresheafRightGradedModule.directSumIsoRestrictScalars (fun i j => add_comm i j) hc
      (A.toPresheafGradedAlgebra.toTotalSheaf J) A.ungradedStructureMap rfl

end SheafOfModules

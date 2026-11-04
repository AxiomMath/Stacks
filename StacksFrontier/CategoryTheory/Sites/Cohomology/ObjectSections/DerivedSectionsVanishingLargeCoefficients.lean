module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Derived module sections from derived abelian sections, with large coefficients

Let `(C, J)` be a site with `C : Type u` and `Category.{v} C`, and `R` a sheaf of rings whose
rings, like the sheaves of modules over it, lie in a universe `max u v t` containing the objects
and the morphisms of the site. For a sheaf of `R`-modules `F` and an object `U`, the right
derived functors of the module-valued sections `Γ(U, -)` at `F` agree, after forgetting the
module structure, with the right derived functors of abelian sections over `U` at the underlying
abelian sheaf of `F` (Stacks 03FD). So the vanishing of the latter forces that of the former.

The acyclicity input is that the underlying abelian sheaf of an injective sheaf of modules has
no higher abelian cohomology over `U`: abelian sections over `U` are corepresented by the free
abelian sheaf on `uliftYoneda.obj U`
(`Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections`), which
is sectionwise torsion free, and `Ext` into such an underlying abelian sheaf from a sectionwise
torsion-free sheaf vanishes (`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`).
The underlying abelian sheaf functor is exact, so `Stacks.RightDerivedComp.objIsoOfAcyclicImage`
identifies the derived functors of the composite.

`Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation` is the same transfer
with the coefficients pinned to the morphism universe of the site, through `Sheaf.H'`; the big
sites of algebraic stacks carry their modules one universe above their morphisms, which is why
this form is needed.

## Main results

In the namespace `Stacks.Cohomology.ObjectSections`:

* `isZero_rightDerived_sheafSections_toSheaf_of_injective`: the underlying abelian sheaf of an
  injective sheaf of modules is acyclic for sections.
* `isZero_rightDerived_evaluation_of_isZero_rightDerived_sheafSections`:
  **vanishing of derived abelian sections forces vanishing of derived module sections.**

## References

* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Abelian

universe t v u

namespace Stacks.Cohomology.ObjectSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max u v t}]
  [HasExt.{max u v t} (Sheaf J AddCommGrpCat.{max u v t})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max u v t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v t})]
  (R : Sheaf J RingCat.{max u v t})

/-- **The underlying abelian sheaf of an injective sheaf of modules is acyclic for sections over
any object**, with the coefficients in a universe containing the objects and morphisms of the
site. -/
theorem isZero_rightDerived_sheafSections_toSheaf_of_injective
    (I : SheafOfModules.{max u v t} R) [Injective I] (U : C) (n : ℕ) (hn : 0 < n) :
    IsZero ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op U)).rightDerived n).obj
      ((SheafOfModules.toSheaf R).obj I)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨e⟩ :=
    Stacks.Cohomology.FreeYonedaUnivLE.nonempty_extFunctorObj_iso_rightDerived_sections.{t}
      J U (k + 1)
  refine IsZero.of_iso ?_ (e.app _).symm
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  have htf : ∀ V, Module.IsTorsionFree ℤ
      (((Stacks.Cohomology.FreeYonedaUnivLE.freeYoneda.{max u t} J).obj U).obj.obj V) := by
    intro V
    refine ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun Y => ?_) V
    change Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{max u t} (Y.unop ⟶ U)))
    exact Module.Flat.isTorsionFree
  exact (ext_eq_zero_of_isTorsionFree J R I _ htf k a).trans
    (ext_eq_zero_of_isTorsionFree J R I _ htf k b).symm

/-- **Vanishing of the derived abelian sections of the underlying abelian sheaf forces vanishing
of the derived module-valued sections** (Stacks 03FD), with the coefficients in a universe
containing the objects and morphisms of the site. -/
theorem isZero_rightDerived_evaluation_of_isZero_rightDerived_sheafSections
    [HasInjectiveResolutions (SheafOfModules.{max u v t} R)]
    (F : SheafOfModules.{max u v t} R) (U : C) (n : ℕ)
    (h : IsZero ((((sheafSections J AddCommGrpCat.{max u v t}).obj (op U)).rightDerived n).obj
      ((SheafOfModules.toSheaf R).obj F))) :
    IsZero (((SheafOfModules.evaluation R (op U)).rightDerived n).obj F) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{max u v t} R) :=
    toSheaf_preservesFiniteColimits J R
  have hA : ∀ m, 0 < m → IsZero (((SheafOfModules.toSheaf R).rightDerived m).obj F) :=
    fun m hm => (SheafOfModules.toSheaf R).isZero_rightDerived_of_exact F m hm
  have hGT : ∀ Z : SheafOfModules.{max u v t} R, Injective Z →
      Stacks.RightDerivedComp.acyclic ((sheafSections J AddCommGrpCat.{max u v t}).obj (op U))
        ((SheafOfModules.toSheaf R).obj Z) := fun Z hZ m hm =>
    have := hZ
    isZero_rightDerived_sheafSections_toSheaf_of_injective.{t} J R Z U m hm
  have h₁ := h.of_iso (Stacks.RightDerivedComp.objIsoOfAcyclicImage
    (SheafOfModules.toSheaf R) ((sheafSections J AddCommGrpCat.{max u v t}).obj (op U)) hA hGT n)
  have : (forget₂ (ModuleCat.{max u v t} (R.obj.obj (op U)))
      AddCommGrpCat.{max u v t}).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have h₂ := h₁.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    (SheafOfModules.evaluation R (op U))
    (forget₂ (ModuleCat.{max u v t} (R.obj.obj (op U))) AddCommGrpCat.{max u v t})
    (SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{max u v t}).obj (op U))
    (Iso.refl _) n).app F)
  rw [AddCommGrpCat.isZero_iff_subsingleton] at h₂
  exact (ModuleCat.isZero_iff_subsingleton).2 h₂

end Stacks.Cohomology.ObjectSections

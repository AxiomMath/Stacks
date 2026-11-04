module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# A totally acyclic sheaf of modules is acyclic for global sections, on a site with large objects

Let `(C, J)` be a site whose objects need not form a small type, `𝒪` a sheaf of rings on it and
`M` a sheaf of `𝒪`-modules whose underlying abelian sheaf is totally acyclic in the sense of
Stacks 072Y. Then the higher right derived functors of the global sections functor `Γ(C, -)` of
Stacks 071H vanish at `M`. This is part (3) of Stacks 0731, whose small-site form is
`Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections`.

## Main definitions

* `Stacks.Cohomology.GlobalSectionsLargeSite.terminalPresheaf`: the terminal presheaf of sets,
  and `Stacks.Cohomology.GlobalSectionsLargeSite.terminalSheaf` the same as a sheaf.
* `Stacks.Cohomology.GlobalSectionsLargeSite.homAddEquivSections`: the global sections of a
  sheaf of modules are the morphisms out of the free abelian sheaf on the terminal sheaf into its
  underlying abelian sheaf.
* `Stacks.Cohomology.GlobalSectionsLargeSite.globalSectionsCorepresentation`: the same, as an
  isomorphism of functors to abelian groups.

## Main results

* `isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic` (in the namespace
  `Stacks.Cohomology.GlobalSectionsLargeSite`): **part (3) of Stacks 0731** on a site whose
  objects need not be small.

## Implementation notes

The proof is the source's: global sections are sections over the final object `e` of the topos,
so part (3) is total acyclicity at `K = e`. Concretely, global sections of a sheaf of modules,
after forgetting the module structure, are corepresented on abelian sheaves by the free abelian
sheaf `ℤ_e` on the terminal sheaf (`globalSectionsCorepresentation`). So the derived functors of
`Γ(C, -)` are those of the composite of the forgetful functor `toSheaf` to abelian sheaves with
`Hom(ℤ_e, -)`. The forgetful functor is exact and carries injective modules to abelian sheaves
with no positive `Ext` out of the torsion-free `ℤ_e`
(`Stacks.Cohomology.ObjectSections.ext_eq_zero_of_isTorsionFree`, the acyclicity behind
Stacks 03FD, which is stated for sites with large objects), so the collapse
`Stacks.RightDerivedComp.objIsoOfAcyclicImage` identifies the derived functors of the composite
with `Ext(ℤ_e, -)` of the underlying abelian sheaf, which total acyclicity kills.

The small-site proof instead routes through the named comparison
`ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying` and the corepresentation of
`CategoryTheory.Sheaf.Γ` by the constant sheaf, both of which are stated for a
`CategoryTheory.SmallCategory`. The route above needs neither. The `Ext`-universe is the morphism
universe `max u' u` of the categories of sheaves, which is also the universe of the global
sections; the sheafification, `Ext` and injectivity inputs are instance arguments.

## References

* [Stacks Project, Lemma 21.14.3 (Tag 0731)](https://stacks.math.columbia.edu/tag/0731)
* [Stacks Project, Definition 21.13.4 (Tag 072Y)](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks Project, Lemma 21.12.4 (Tag 03FD)](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u u'

namespace Stacks.Cohomology.GlobalSectionsLargeSite

variable {C : Type u'} [Category.{u} C] (J : GrothendieckTopology C)

/-- The terminal presheaf of sets on `C`, with values in `Type u`. -/
abbrev terminalPresheaf : Cᵒᵖ ⥤ Type u := (Functor.const Cᵒᵖ).obj PUnit.{u + 1}

/-- The terminal presheaf of sets is a sheaf, for every topology. -/
def terminalSheaf : Sheaf J (Type u) :=
  ⟨terminalPresheaf, Presheaf.isSheaf_of_isTerminal J Types.isTerminalPUnit⟩

variable (R : Sheaf J RingCat.{u})

/-- Morphisms out of the free abelian presheaf on the terminal presheaf of sets into the
underlying abelian presheaf of a sheaf of modules are its global sections: a morphism is
determined by the images of the generator, which form a compatible family of sections. -/
def freeHomAddEquivSections (M : SheafOfModules.{u} R) :
    (terminalPresheaf ⋙ AddCommGrpCat.free ⟶ ((SheafOfModules.toSheaf R).obj M).obj) ≃+
      M.sections where
  toFun φ := M.val.sectionsMk (fun U => φ.app U (FreeAbelianGroup.of PUnit.unit)) (by
    intro U V f
    exact (ConcreteCategory.congr_hom (φ.naturality f) (FreeAbelianGroup.of PUnit.unit)).symm)
  invFun s :=
    { app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun _ => s.eval U))
      naturality U V f := by
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro x
        exact ((FreeAbelianGroup.lift_apply_of _ x).trans (M.val.sections_property s f).symm).trans
          (congrArg (M.val.map f) (FreeAbelianGroup.lift_apply_of _ x).symm) }
  left_inv φ := by
    ext U : 2
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    exact FreeAbelianGroup.lift_apply_of _ x
  right_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact FreeAbelianGroup.lift_apply_of _ PUnit.unit
  map_add' φ ψ := by
    apply PresheafOfModules.sections_ext
    intro U
    rfl

variable [HasSheafify J AddCommGrpCat.{u}]

/-- **The morphisms out of the free abelian sheaf on the terminal sheaf into the underlying
abelian sheaf of a sheaf of modules are its global sections.** This is the sheafification
adjunction followed by `freeHomAddEquivSections`. -/
def homAddEquivSections (M : SheafOfModules.{u} R) :
    ((Presheaf.freeAbelianSheaf J).obj (terminalSheaf J).obj ⟶
      (SheafOfModules.toSheaf R).obj M) ≃+ M.sections :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ _).trans
    (freeHomAddEquivSections J R M)

/-- `homAddEquivSections` turns composition with the underlying morphism of abelian sheaves of
a morphism of sheaves of modules into the induced map of global sections. -/
lemma homAddEquivSections_naturality {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (a : (Presheaf.freeAbelianSheaf J).obj (terminalSheaf J).obj ⟶
      (SheafOfModules.toSheaf R).obj M) :
    homAddEquivSections J R N (a ≫ (SheafOfModules.toSheaf R).map f) =
      SheafOfModules.sectionsMap f (homAddEquivSections J R M a) :=
  (congrArg (freeHomAddEquivSections J R N)
    ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv_naturality_right a
      ((SheafOfModules.toSheaf R).map f))).trans rfl

/-- **Global sections of sheaves of modules, valued in abelian groups, are corepresented on the
underlying abelian sheaves by the free abelian sheaf on the terminal sheaf.** -/
def globalSectionsCorepresentation :
    globalSectionsFunctor.{u', u, u, u} R ⋙
        forget₂ (ModuleCat.{max u' u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u' u} ≅
      SheafOfModules.toSheaf R ⋙ preadditiveCoyoneda.obj
        (op ((Presheaf.freeAbelianSheaf J).obj (terminalSheaf J).obj)) :=
  NatIso.ofComponents (fun M => (homAddEquivSections J R M).symm.toAddCommGrpIso) (by
    intro M N f
    ext s
    apply (homAddEquivSections J R N).injective
    change homAddEquivSections J R N ((homAddEquivSections J R N).symm
        (SheafOfModules.sectionsMap f s)) =
      homAddEquivSections J R N ((homAddEquivSections J R M).symm s ≫
        (SheafOfModules.toSheaf R).map f)
    rw [homAddEquivSections_naturality]
    exact (AddEquiv.apply_symm_apply _ _).trans
      (congrArg (SheafOfModules.sectionsMap f) (AddEquiv.apply_symm_apply _ s).symm))

/-- The free abelian sheaf on the terminal sheaf is sectionwise torsion free. -/
lemma isTorsionFree_freeAbelianSheaf_terminal (U : Cᵒᵖ) :
    Module.IsTorsionFree ℤ (((Presheaf.freeAbelianSheaf J).obj (terminalSheaf J).obj).obj.obj U) :=
  ModuleSheafCohomology.isTorsionFree_sheafify J (terminalPresheaf ⋙ AddCommGrpCat.free)
    (fun V ↦ by
      show Module.IsTorsionFree ℤ (FreeAbelianGroup PUnit)
      exact Module.Flat.isTorsionFree) U

variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasExt.{max u' u} (Sheaf J AddCommGrpCat.{u})] [EnoughInjectives (Sheaf J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{u})]
  [HasInjectiveResolutions (SheafOfModules.{u} R)]

/-- **Stacks 0731, part (3), on a site whose objects need not be small.** A sheaf of modules
whose underlying abelian sheaf is totally acyclic has vanishing higher right derived global
sections.

Global sections, forgotten to abelian groups, are `Hom(ℤ_e, -)` of the underlying abelian sheaf
(`globalSectionsCorepresentation`); the forgetful functor is exact and carries injective modules
to `Hom(ℤ_e, -)`-acyclic sheaves, so the derived functors of the composite are those of
`Hom(ℤ_e, -)`, that is `Ext(ℤ_e, -)`, at the underlying abelian sheaf; and total acyclicity at
the terminal sheaf `e` is the vanishing of exactly those. -/
@[stacks 0731 "part (3): the functor of global sections, on a site whose objects need not be \
small"]
theorem isZero_rightDerived_globalSectionsFunctor_of_isTotallyAcyclic
    (M : SheafOfModules.{u} R)
    (hM : IsTotallyAcyclic J ((SheafOfModules.toSheaf R).obj M)) (n : ℕ)
    (hn : 0 < n) :
    IsZero (((globalSectionsFunctor.{u', u, u, u} R).rightDerived n).obj M) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let X := (Presheaf.freeAbelianSheaf J).obj (terminalSheaf J).obj
  let G := SheafOfModules.toSheaf R
  let T := preadditiveCoyoneda.obj (op X)
  let E := globalSectionsFunctor.{u', u, u, u} R
  let F := forget₂ (ModuleCat.{max u' u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u' u}
  have : PreservesFiniteColimits G := ObjectSections.toSheaf_preservesFiniteColimits J R
  -- `Ext(ℤ_e, -)` vanishing in positive degree gives vanishing of the derived functors of `T`.
  have hT : ∀ (Y : Sheaf J AddCommGrpCat.{u}) (p : ℕ),
      Subsingleton (Ext.{max u' u} X Y (p + 1)) → IsZero ((T.rightDerived (p + 1)).obj Y) :=
    fun Y p h => (@AddCommGrpCat.isZero_of_subsingleton _ h).of_iso
      ((ModuleSheafCohomology.rightDerivedCoyonedaSuccIso X p).app Y)
  have hcollapse : IsZero (((G ⋙ T).rightDerived (n + 1)).obj M) :=
    (hT _ n (hM (terminalSheaf J) (n + 1) (by omega))).of_iso
      (Stacks.RightDerivedComp.objIsoOfAcyclicImage G T
        (fun p hp => Functor.isZero_rightDerived_of_exact G M p hp) (fun Z _ p hp => by
          obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
          have h := ObjectSections.ext_eq_zero_of_isTorsionFree.{max u' u} J R Z X
            (isTorsionFree_freeAbelianSheaf_terminal J) p
          exact hT _ p ⟨fun a b => (h a).trans (h b).symm⟩) (n + 1))
  have hcomp : IsZero (((E ⋙ F).rightDerived (n + 1)).obj M) :=
    hcollapse.of_iso ((ModuleSheafCohomology.rightDerivedIso
      (globalSectionsCorepresentation J R) (n + 1)).app M)
  have hforg : IsZero ((E.rightDerived (n + 1) ⋙ F).obj M) := by
    obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology E F (n + 1) M
    exact hcomp.of_iso e
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero hforg)

end Stacks.Cohomology.GlobalSectionsLargeSite

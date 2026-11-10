module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally

/-!
# Cohomology of a module sheaf over an open as `Ext`-theoretic sheaf cohomology

The cohomology of a sheaf of modules on a scheme `X` over an open `U` is
`Hgroup X.ringCatSheaf U n F`, the `n`-th right derived functor of `Γ(U, -)` computed in
`Mod(𝒪_X)`. The Mayer--Vietoris long exact sequence available for it is the one of a
Mayer--Vietoris square on a site, which is stated for `CategoryTheory.Sheaf.H'`, the
`Ext`-groups out of the sheafification of the free abelian presheaf on `yoneda.obj U`. This
file identifies the two in positive degree and extracts the consequence of the long exact
sequence that a vanishing argument needs.

## Main definitions

* `AlgebraicGeometry.hgroupIsoSheafCohomology`: the identification
  `H^{n+1}(U, F) ≅ H^{n+1}(U, F♭)` of the derived-functor cohomology of a module sheaf with the
  `Ext`-theoretic cohomology of its underlying abelian sheaf.

## Main results

* `AlgebraicGeometry.isZero_sheafCohomology_bot`: `Ext`-theoretic sheaf cohomology over the
  empty open vanishes in every degree.
* `AlgebraicGeometry.isZero_sheafCohomology_sup`: the Mayer--Vietoris vanishing step. If the
  degree-`n + 1` cohomology over `U` and over `V` vanishes and the degree-`n` cohomology over
  `U ⊓ V` vanishes, then the degree-`n + 1` cohomology over `U ⊔ V` vanishes.

## Implementation notes

The comparison is assembled from results already in the library: Stacks 03FD in the named form
`ModuleSheafCohomology.sectionsComparisonIso` moves the derivation from `Mod(𝒪_X)` to abelian
sheaves, `ModuleSheafCohomology.evaluationRepresentation` says that sections over `U` are
corepresented by the sheafification of the free abelian presheaf on `yoneda.obj U`, and
`ModuleSheafCohomology.rightDerivedCoyonedaSuccIso` identifies the right derived functors of a
corepresented functor with `Ext` out of the corepresenting object in positive degree. The last
step is why the comparison is restricted to positive degrees; that is no loss, since the
vanishing statements it is used for are about positive degrees.

`Ext`-theoretic cohomology needs the smallness hypothesis `HasExt`, which Mathlib deliberately
does not register as an instance. It is carried as a hypothesis here and discharged by
`CategoryTheory.Abelian.hasExt_of_enoughInjectives` wherever a statement not mentioning `Ext`
is proved.

## References

* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The underlying abelian sheaf of a module sheaf on a scheme. -/
abbrev Scheme.Modules.toAbelianSheaf (F : X.Modules) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj F

/-- **Positive-degree comparison of the two cohomologies of a module sheaf**, assembled from
[Stacks, Tag 03FD]. The degree-`n + 1` cohomology of `F` over an open `U`, computed as a right
derived functor of `Γ(U, -)` in `Mod(𝒪_X)`, agrees with the degree-`n + 1` `Ext`-theoretic sheaf
cohomology of the underlying abelian sheaf of `F` over `U`. -/
def hgroupIsoSheafCohomology (F : X.Modules) (U : X.Opens) (n : ℕ) :
    Hgroup X.ringCatSheaf U (n + 1) F ≅ Sheaf.H' F.toAbelianSheaf (n + 1) U :=
  ((ModuleSheafCohomology.sectionsComparisonIso (Opens.grothendieckTopology X)
      X.ringCatSheaf U (n + 1)).app F) ≪≫
    ((Functor.isoWhiskerLeft (SheafOfModules.toSheaf X.ringCatSheaf)
      (ModuleSheafCohomology.rightDerivedIso
          (ModuleSheafCohomology.evaluationRepresentation
            (Opens.grothendieckTopology X) U) (n + 1) ≪≫
        ModuleSheafCohomology.rightDerivedCoyonedaSuccIso _ n)).app F)

end AlgebraicGeometry

namespace Stacks.Cohomology.UniformVanishing

variable {T : Type u} [TopologicalSpace T]
  [HasSheafify (Opens.grothendieckTopology T) AddCommGrpCat.{u}]

section Bot

/-- The free abelian sheaf on the empty open is a zero object: a morphism out of it to a sheaf
`G` is a section of `G` over the empty open, and those form a zero group. -/
theorem isZero_freeYonedaSheaf_bot :
    IsZero (Stacks.Cohomology.Locality.freeYonedaSheaf
      (J := Opens.grothendieckTopology T) (⊥ : Opens T)) := by
  set J := Opens.grothendieckTopology T
  have hbot : (⊥ : Sieve (⊥ : Opens T)) ∈ J (⊥ : Opens T) :=
    (Opens.mem_grothendieckTopology (T := T) (U := ⊥) (S := ⊥)).2 (by simp)
  have hsections (G : Sheaf J AddCommGrpCat.{u}) :
      Subsingleton (G.obj.obj (op (⊥ : Opens T))) :=
    AddCommGrpCat.subsingleton_of_isZero
      (Sheaf.isTerminalOfBotCover G (⊥ : Opens T) hbot).isZero
  refine IsInitial.isZero (IsInitial.ofUnique _ (h := fun G => ?_))
  exact
    { default := ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ G).symm
        (Stacks.Cohomology.Locality.repEquiv (⊥ : Opens T) G.obj |>.symm 0)
      uniq := fun f =>
        (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ G).trans
            (Stacks.Cohomology.Locality.repEquiv (⊥ : Opens T) G.obj)).injective
          ((hsections G).elim _ _) }

variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]

/-- **Sheaf cohomology over the empty open vanishes in every degree.** The object
corepresenting sections over the empty open is a zero object, so every `Ext`-group out of it
is trivial. -/
theorem isZero_sheafCohomology_bot
    (G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ) :
    IsZero (Sheaf.H' G p (⊥ : Opens T)) := by
  have hP := isZero_freeYonedaSheaf_bot (T := T)
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  change Subsingleton (Ext.{u} (Stacks.Cohomology.Locality.freeYonedaSheaf
    (J := Opens.grothendieckTopology T) (⊥ : Opens T)) G p)
  cases p with
  | zero =>
    have : Subsingleton (Stacks.Cohomology.Locality.freeYonedaSheaf
        (J := Opens.grothendieckTopology T) (⊥ : Opens T) ⟶ G) :=
      ⟨hP.eq_of_src⟩
    exact (Equiv.subsingleton_congr Ext.addEquiv₀.toEquiv).2 inferInstance
  | succ p =>
    have : Projective (Stacks.Cohomology.Locality.freeYonedaSheaf
      (J := Opens.grothendieckTopology T) (⊥ : Opens T)) := hP.projective
    exact subsingleton_of_forall_eq 0 Ext.eq_zero_of_projective

section MayerVietoris

/-- **The Mayer--Vietoris vanishing step**, [Stacks, Tag 01EB]. If the degree-`n + 1` sheaf
cohomology of `G` vanishes over each of two opens and its degree-`n` cohomology vanishes over
their intersection, then its degree-`n + 1` cohomology vanishes over their union. -/
theorem isZero_sheafCohomology_sup
    (G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (U V : Opens T) (n : ℕ)
    (hU : IsZero (Sheaf.H' G (n + 1) U)) (hV : IsZero (Sheaf.H' G (n + 1) V))
    (hUV : IsZero (Sheaf.H' G n (U ⊓ V))) :
    IsZero (Sheaf.H' G (n + 1) (U ⊔ V)) := by
  set S := Opens.mayerVietorisSquare U V
  have hseq := S.sequence_exact G n (n + 1) rfl
  have hg : (hseq.sc 2).g = 0 := by
    have h₂ : (G.cohomologyPresheaf (n + 1)).map S.f₂₄.op = 0 := hU.eq_of_tgt _ _
    have h₃ : (G.cohomologyPresheaf (n + 1)).map S.f₃₄.op = 0 := hV.eq_of_tgt _ _
    change biprod.lift ((G.cohomologyPresheaf (n + 1)).map S.f₂₄.op)
      ((G.cohomologyPresheaf (n + 1)).map S.f₃₄.op) = 0
    rw [h₂, h₃]
    apply biprod.hom_ext <;> simp
  exact (hseq.exact 2).isZero_X₂ (hUV.eq_of_src _ _) hg

end MayerVietoris

end Bot

end Stacks.Cohomology.UniformVanishing

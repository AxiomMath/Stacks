module

public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Detecting quasi-isomorphisms of sheaves on presheaves, at independent universes

Two small general facts about abelian sheaves on a site, both needed for the dévissage of
[Stacks, Tag 0D6J] and both stated here with the site's object and hom universes and the
coefficient universe independent of one another.

## Main results

* `Stacks.Cohomology.sheafQuasiIso_of_presheafQuasiIso`: a morphism of complexes of abelian
  sheaves is a quasi-isomorphism as soon as it is one on underlying presheaves.
* `Stacks.Cohomology.isTorsionFree_freeYoneda`: the free abelian sheaf on an object of the site
  is sectionwise torsion free.

## Implementation notes

Neither proof is new.  The first is the proof of
`Stacks.Cohomology.SupportedComplexes.sheafQuasiIso_of_presheafQuasiIso` transcribed verbatim --
its body never mentions a universe or smallness, every step being sheafification's exactness and
`sheafificationNatIso` -- but that statement is pinned to `{C : Type u} [Category.{u} C]` with
coefficients at the same `u`, which excludes a site that is large and only essentially small with
coefficients above its own universe.  So the statement is restated here at free universes and the
pinned one is an instance of it.

The second is four lines: the sections of the free abelian presheaf on `U` are
`FreeAbelianGroup (ULift (V ⟶ U))`, which is torsion free because free modules are flat, and
sheafification preserves sectionwise torsion-freeness.

**Where to look when a site-level result does not fit.**  The collapse is in the *specialisation*,
not the file: the thing specialised is usually public and stated at independent universes, while
the specialisation pins them.  When a site-level statement does not fit, look for the generic
form it came from before restating anything.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe s t v u w

namespace Stacks.Cohomology

/-- **A morphism of complexes of abelian sheaves is a quasi-isomorphism as soon as it is one on
the underlying complexes of presheaves.**  Sheafification is exact and undoes the inclusion of
sheaves into presheaves, so the morphism is isomorphic, as an arrow, to the sheafification of its
presheaf-level counterpart. -/
theorem sheafQuasiIso_of_presheafQuasiIso
    {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{s}]
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{s}) ℤ} (f : K ⟶ L)
    (hf : QuasiIso (((sheafToPresheaf J AddCommGrpCat.{s}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) : QuasiIso f := by
  let F := sheafToPresheaf J AddCommGrpCat.{s}
  let G := presheafToSheaf J AddCommGrpCat.{s}
  let c := ComplexShape.up ℤ
  let _ : G.Additive := Functor.additive_of_preserves_binary_products G
  let e : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ≅
      𝟭 (CochainComplex (Sheaf J AddCommGrpCat.{s}) ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) c ≪≫
      NatIso.mapHomologicalComplex (sheafificationNatIso J AddCommGrpCat.{s}).symm c ≪≫
      Functor.mapHomologicalComplexIdIso _ c
  let sf := (G.mapHomologicalComplex c).map ((F.mapHomologicalComplex c).map f)
  have hsf : QuasiIso sf :=
    HomologicalComplex.quasiIso_map_of_preservesHomology
      ((F.mapHomologicalComplex c).map f) G
  exact quasiIso_of_arrow_mk_iso sf f
    (Arrow.isoMk (e.app K) (e.app L) (by simpa [sf] using (e.hom.naturality f).symm))

/-- **The free abelian sheaf on an object of the site is sectionwise torsion free.**  Its
sections before sheafification are a free abelian group, hence flat, hence torsion free, and
sheafification preserves sectionwise torsion-freeness. -/
theorem isTorsionFree_freeYoneda {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max v t}] (U : C) (V : Cᵒᵖ) :
    Module.IsTorsionFree ℤ (((FreeYonedaUnivLE.freeYoneda.{t} J).obj U).obj.obj V) :=
  ModuleSheafCohomology.isTorsionFree_sheafify J _ (fun W => by
    change Module.IsTorsionFree ℤ (FreeAbelianGroup (ULift.{t} (W.unop ⟶ U)))
    exact Module.Flat.isTorsionFree) V

end Stacks.Cohomology

end

module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules

/-!
# Full faithfulness of the Comparison Lemma for modules, at an arbitrary section universe

`Stacks.DenseSubsiteModules.moduleRestriction` restricts sheaves of modules along a dense
subsite inclusion `v : C ⥤ C'`, and is stated with a *single* universe `w` for the sections of
the sheaf of rings and for the sections of the modules. That is a feature of the statement, not
of the mathematics: Mathlib's `SheafOfModules.{m} R` already allows the module sections to lie
in a universe `m` independent of the universe `r` of the ring sections, and the restriction
functor for a general pair `(r, m)` is `SheafOfModules.pushforward.{m} (𝟙 _)`, written here
`Stacks.DenseSubsiteModules.moduleRestrictionRaised`.

**This file proves that that functor is fully faithful for every pair of universes**, with the
dense-subsite hypothesis as its only input.

The distinction matters because a *global presentation* of a module with sections in `Type m`
on a site with objects in `Type u` and morphisms in `Type v`, over rings with sections in
`Type r`, is built from modules with sections in `Type (max u v r m)` — strictly larger than
`m` whenever the site is not small. Reflecting a global presentation along a restriction
functor therefore asks for the restriction functor *at that raised module universe*, over the
*unraised* sheaf of rings, which is exactly the pair `(r, max u v r m)` the single-universe
statement cannot express. What the reflection needs there is only full faithfulness, and that
is what is proved here; essential surjectivity, i.e. the Comparison Lemma proper, is not
needed and is not proved here.

## Main definitions

* `Stacks.DenseSubsiteModules.moduleRestrictionRaised`: restriction of sheaves of modules along
  a dense subsite inclusion, with the universe of the module sections independent of the
  universe of the ring sections. At equal universes it is
  `Stacks.DenseSubsiteModules.moduleRestriction`, on the nose.

## Main results

* `Stacks.DenseSubsiteModules.faithful_moduleRestrictionRaised` and
  `Stacks.DenseSubsiteModules.full_moduleRestrictionRaised`, packaged as
  `Stacks.DenseSubsiteModules.fullyFaithful_moduleRestrictionRaised`: **restriction of sheaves
  of modules to a dense subsite is fully faithful at every universe of module sections.**

## Implementation notes

Both proofs are those of the corresponding instances for
`Stacks.DenseSubsiteModules.moduleRestriction`, with the module universe freed from the ring
universe. Nothing else changes, because neither proof touches the ring sections: faithfulness
is inherited from `CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous`
through the equality `Stacks.DenseSubsiteModules.moduleRestrictionRaised_comp_toSheaf` of
functors into sheaves of abelian groups — which still holds by `rfl`, restriction of modules
and restriction of the underlying sheaves of abelian groups being the same operation on
sections — and fullness only has to check that the morphism of abelian-group sheaves produced
by `CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous` is linear, which is a
local condition on sections checked after restricting along a cover by images.

The two statements are theorems rather than instances: at `m = r` they would duplicate the
instances already carried by `Stacks.DenseSubsiteModules.moduleRestriction`, which is the same
functor. Consumers introduce them with `haveI`.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe r m u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (J : GrothendieckTopology C) (K : GrothendieckTopology C')
  (v : C ⥤ C') [v.IsDenseSubsite J K] (R : Sheaf K RingCat.{r})

/-- Restriction of sheaves of modules along a dense subsite inclusion, with the universe `m` of
the module sections independent of the universe `r` of the ring sections. At `m = r` this is
`Stacks.DenseSubsiteModules.moduleRestriction`. -/
noncomputable abbrev moduleRestrictionRaised :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} (ringRestriction J K v R) :=
  SheafOfModules.pushforward.{m} (𝟙 (ringRestriction J K v R))

/-- Restriction of sheaves of modules is, on the nose, restriction of the underlying sheaves of
abelian groups — at any universe of module sections. -/
theorem moduleRestrictionRaised_comp_toSheaf :
    moduleRestrictionRaised.{r, m} J K v R ⋙
        SheafOfModules.toSheaf.{m} (ringRestriction J K v R) =
      SheafOfModules.toSheaf.{m} R ⋙ v.sheafPushforwardContinuous AddCommGrpCat.{m} J K := rfl

/-- **Restriction of sheaves of modules to a dense subsite is faithful**, at any universe of
module sections. -/
theorem faithful_moduleRestrictionRaised : (moduleRestrictionRaised.{r, m} J K v R).Faithful := by
  exact Functor.Faithful.of_comp_eq (moduleRestrictionRaised_comp_toSheaf.{r, m} J K v R)

/-- **Restriction of sheaves of modules to a dense subsite is full**, at any universe of module
sections. -/
theorem full_moduleRestrictionRaised : (moduleRestrictionRaised.{r, m} J K v R).Full where
  map_surjective {M N} f := by
    have := Functor.IsDenseSubsite.isCoverDense J K v
    obtain ⟨g, hg⟩ := (v.sheafPushforwardContinuous AddCommGrpCat.{m} J K).map_surjective
      (X := (SheafOfModules.toSheaf.{m} R).obj M) (Y := (SheafOfModules.toSheaf.{m} R).obj N)
      ((SheafOfModules.toSheaf.{m} (ringRestriction J K v R)).map f)
    have key : ∀ (Y : C) (x : M.val.obj (op (v.obj Y))),
        g.hom.app (op (v.obj Y)) x = f.val.app (op Y) x := fun Y x ↦
      CategoryTheory.congr_fun
        (NatTrans.congr_app (congrArg (sheafToPresheaf J AddCommGrpCat.{m}).map hg) (op Y)) x
    refine ⟨⟨PresheafOfModules.homMk g.hom ?_⟩, ?_⟩
    · rintro ⟨X⟩ a x
      refine Functor.IsCoverDense.ext (K := K) v
        ((sheafCompose K (forget AddCommGrpCat.{m})).obj
          ((SheafOfModules.toSheaf.{m} R).obj N)) X (fun {Y} hY ↦ ?_)
      have nat : ∀ (y : M.val.obj (op X)),
          N.val.map hY.op (g.hom.app (op X) y) =
            g.hom.app (op (v.obj Y)) (M.val.map hY.op y) := fun y ↦
        (CategoryTheory.congr_fun (g.hom.naturality hY.op) y).symm
      refine (nat (a • x)).trans
        (Eq.trans ?_ (N.val.map_smul hY.op a (g.hom.app (op X) x)).symm)
      rw [M.val.map_smul]
      refine (key Y _).trans (((f.val.app (op Y)).hom.map_smul _ _).trans ?_)
      congr 1
      exact (key Y _).symm.trans (nat x).symm
    · exact SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun Y ↦
        ModuleCat.hom_ext (LinearMap.ext fun x ↦ key Y.unop x))

/-- **Restriction of sheaves of modules to a dense subsite is fully faithful**, at any universe
of module sections — the half of the Comparison Lemma for sheaves of modules that needs no
hypothesis beyond the dense-subsite inclusion, and no relation between the universe of the
module sections and the universe of the ring sections. -/
noncomputable def fullyFaithful_moduleRestrictionRaised :
    (moduleRestrictionRaised.{r, m} J K v R).FullyFaithful :=
  haveI := full_moduleRestrictionRaised.{r, m} J K v R
  haveI := faithful_moduleRestrictionRaised.{r, m} J K v R
  .ofFullyFaithful _

end Stacks.DenseSubsiteModules

end

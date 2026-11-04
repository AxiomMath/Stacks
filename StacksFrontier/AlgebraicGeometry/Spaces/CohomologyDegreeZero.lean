module

public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModulePresentationColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Degree-zero cohomology of modules on a ringed site is global sections

For a sheaf of rings `O` on a site `(C, J)`, the cohomology of `O`-modules of
[Stacks, Tag 071H] is the right derived functor of the global-sections functor
`Stacks.Cohomology.SiteModules.globalSectionsFunctor`.  Since that functor is left exact, its
zeroth right derived functor is itself; the content of this file is that left exactness, and
the resulting identification of `H⁰` with `Γ`.

Left exactness is not formal: `Stacks.Cohomology.SiteModules.globalSectionsFunctor` is
defined by hand, as compatible families of sections, rather than as a limit or as a right
adjoint.  The proof identifies it, after forgetting the module structure, with Mathlib's
global-sections functor `CategoryTheory.Sheaf.Γ` on sheaves of abelian groups, which is a
right adjoint and therefore preserves all limits.  Both are limits of the same diagram — the
sections of the underlying presheaf over all objects of the site — so the comparison is the
uniqueness of a limit cone.

Everything is proved for the four independent universes of
`Stacks.Cohomology.SiteModules.globalModuleCohomology`, which is what makes it applicable to
the small étale ringed site of an algebraic space; the last section draws that conclusion for
`AlgebraicGeometry.Space.cohomologyOverBase`.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsForgetCone` and
  `Stacks.Cohomology.SiteModules.isLimitGlobalSectionsForgetCone`: the compatible global
  sections of a sheaf of modules, with the module structure forgotten, as a limit cone over
  the diagram of its sections on the objects of the site.
* `Stacks.Cohomology.SiteModules.globalSectionsForgetAddCommGrpIso`: the comparison of
  `Stacks.Cohomology.SiteModules.globalSectionsFunctor` with `CategoryTheory.Sheaf.Γ`.
* `Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso`: **`H⁰ = Γ`.**  Degree-zero
  cohomology of `O`-modules is naturally isomorphic to global sections, with no hypothesis
  beyond a site and a sheaf of rings on it.
* `Stacks.Cohomology.SiteModules.unitULift`: the structure sheaf as a sheaf of modules over
  itself, with its sections lifted into a larger module universe.
* `Stacks.Cohomology.SiteModules.unitULiftSectionsEquiv` and
  `Stacks.Cohomology.SiteModules.unitULiftSectionsLinearEquiv`: its global sections are the
  ring `Γ(C, O)` of global functions, as a module over itself.
* `Stacks.Cohomology.SiteModules.cohomologyZeroUnitLinearEquiv`: `H⁰(C, O) = Γ(C, O)`.
* `AlgebraicGeometry.Space.cohomologyOverBaseZeroIso` and
  `AlgebraicGeometry.Space.cohomologyOverBaseZeroLinearEquiv`: for an algebraic space over
  `Spec A`, degree-zero cohomology over the base ring is the `A`-module of global sections of
  the module.

## Main results

* `Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor`: global sections
  of sheaves of modules on an arbitrary site preserve finite limits.  This is the only
  proposition below; everything else in this file is data.

## Implementation notes

The module universe of `Stacks.Cohomology.SiteModules.globalSectionsFunctor` enters the
statements only through the constraint that it contain the universe of the objects of the
site: `globalSectionsFunctor` lands in `ModuleCat.{max u w'}` for a module universe `w'`, and
the comparison with `CategoryTheory.Sheaf.Γ` compares it with a functor valued in
`AddCommGrpCat.{w'}`.  The statements below are therefore written at module universe
`max u w`, which is the general solution of `max u w' = w'`, and the cohomological consequences
specialise it at `w := max v r w` to reach the universe `max u v r w` of
`Stacks.Cohomology.SiteModules.globalModuleCohomology`.  `unitULift` is the exception: its
module universe is `max r w`, since lifting the structure sheaf constrains only the universe
of the structure rings, and it is likewise specialised at `w := max u v r w`.

`globalSectionsForgetAddCommGrpIso` and `preservesFiniteLimits_globalSectionsFunctor` carry
`CategoryTheory.HasWeakSheafify` and `CategoryTheory.HasGlobalSectionsFunctor` as instance
hypotheses, since they are what give `CategoryTheory.Sheaf.Γ` a meaning, and a user may have
them from a terminal object of the site rather than from sheafification.  At the module
universe of cohomology both are automatic — sheafification of abelian presheaves is
`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`, which holds for every site, and
the global-sections functor then exists because `AddCommGrpCat` has limits of the required
size — so `globalModuleCohomologyZeroIso` is unconditional.  The `have` is mandatory there:
`site_hasSheafify_addCommGrp` is a theorem, not an instance.

**What this generalises, and the deduplication it owes.**  Four of the declarations below
already exist in the library with all four universes equal, which is exactly why they could
not be reused here; none of those modules is editable from this one, so the merge is a
follow-up rather than part of this file.

* `Stacks.Cohomology.moduleSectionsCone` and `Stacks.Cohomology.moduleSectionsConeIsLimit` of
  `StacksDraft.Ch21.Sec14.TotallyAcyclicGlobalSections` are `globalSectionsForgetCone` and
  `isLimitGlobalSectionsForgetCone` for a `CategoryTheory.SmallCategory` site at module
  universe equal to the site's.  The cone point here is phrased as the value of
  `globalSectionsFunctor` composed with the forgetful functor, rather than as
  `AddCommGrpCat.of M.sections`, so that the comparison isomorphism typechecks on the nose;
  the two are the same cone.
* `Stacks.Cohomology.globalSectionsUnderlyingIso` of that same module is
  `globalSectionsForgetAddCommGrpIso` reversed, again at a single universe.  It is proved
  through `CategoryTheory.Sheaf.ΓNatIsoLim` and so needs `CategoryTheory.Limits.HasLimitsOfShape
  Cᵒᵖ`; the proof here goes through `CategoryTheory.Sheaf.isLimitConeΓ` and needs only
  `CategoryTheory.HasGlobalSectionsFunctor`.
* `Stacks.Cohomology.SiteModules.globalSectionsFunctor_preservesFiniteLimits` of
  `StacksDraft.Ch21.Sec5.FirstCohomologyAndExtensions` is
  `preservesFiniteLimits_globalSectionsFunctor` at a single universe, proved instead from
  corepresentability by the structure sheaf.  That route needs no sheafification hypothesis,
  but it does need the structure sheaf to be a module in the ambient universe, which is
  precisely what fails here; the general form proved below subsumes it, with both instance
  hypotheses automatic on a small site.

`unitULift` exists for the same reason: `CategoryTheory.SheafOfModules.unit` puts the module
sections in the universe `r` of the structure rings, whereas cohomology of modules on the
small étale site of an algebraic space over a `Scheme.{u}` lives at module universe
`max (u + 1) w`, and no `w` makes those equal.  It is not a new construction — it is
`Stacks.SheafOfModules.moduleULift` applied to `CategoryTheory.SheafOfModules.unit`, and
`Stacks.SheafOfModules.moduleULiftFullyFaithful` therefore applies to it.  It is deliberately
*not* built from `Stacks.SheafOfModules.FlatResolution.uliftUnit`, which is a presheaf of modules
carrying no sheaf condition and whose underlying presheaf is not syntactically a composite with
`AddCommGrpCat.uliftFunctor`, so `CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf` does not apply
to it; `Stacks.SheafOfModules.moduleULift` already packages that proof.

There is no `A`-linear form of `cohomologyZeroUnitLinearEquiv` over an algebraic space:
`Stacks.Cohomology.SiteModules.GlobalSectionRing` of the small étale ringed site lies in
`Type (u + 1)` while `AlgebraicGeometry.Space.cohomologyOverBase` is valued in
`ModuleCat.{max (u + 1) w}`, so the two sides are not objects of one category for free `w`.
Compose `cohomologyOverBaseZeroIso` with `unitULiftSectionsEquiv` to get the bijection.

No `@[stacks]` attribute is carried.  [Stacks, Tag 071H] is registered in
`StacksDraft.Ch21.Sec2.CohomologyOfModulesOnASite` on the construction of cohomology itself;
the left exactness of global sections and the resulting degree-zero identification are not an
enumerated part of that tag, and the algebraic-space statement is not a part of
[Stacks, Tag 08AS], which has a single conclusion about finiteness.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The compatible global sections of a sheaf of `R`-modules, with the module structure
forgotten, as a cone over the diagram of the sections of its underlying sheaf of abelian
groups on the objects of the site.  The leg at `U` is evaluation of a compatible family at
`U`, and the cone condition is the compatibility of the family. -/
def globalSectionsForgetCone (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{max u w} R) :
    Cone ((SheafOfModules.toSheaf.{max u w} R).obj M).obj where
  pt := (forget₂ (ModuleCat.{max u w} (RingCat.sectionsSubring R.obj))
      AddCommGrpCat.{max u w}).obj ((globalSectionsFunctor.{u, v, r, max u w} R).obj M)
  π :=
    { app U := AddCommGrpCat.ofHom
        { toFun s := s.eval U
          map_zero' := rfl
          map_add' _ _ := rfl }
      naturality := by
        intro U V f
        ext s
        exact (M.val.sections_property s f).symm }

/-- The leg of `Stacks.Cohomology.SiteModules.globalSectionsForgetCone` at `U` is evaluation
of a compatible family of global sections at `U`. -/
@[simp]
lemma globalSectionsForgetCone_π_app_apply (R : Sheaf J RingCat.{r})
    (M : SheafOfModules.{max u w} R) (U : Cᵒᵖ) (s : M.sections) :
    (globalSectionsForgetCone.{u, v, r, w} R M).π.app U s = s.eval U := rfl

/-- `Stacks.Cohomology.SiteModules.globalSectionsForgetCone` is a limit cone: a compatible
family of sections is exactly a point of the limit of the sections over the site.  The lift of
a cone assembles the components into a compatible family, which is possible because the cone
condition is the compatibility condition. -/
def isLimitGlobalSectionsForgetCone (R : Sheaf J RingCat.{r})
    (M : SheafOfModules.{max u w} R) : IsLimit (globalSectionsForgetCone.{u, v, r, w} R M) where
  lift c := AddCommGrpCat.ofHom
    { toFun x := M.val.sectionsMk (fun U => c.π.app U x)
        (fun _ _ f => ConcreteCategory.congr_hom (c.w f) x)
      map_zero' := PresheafOfModules.sections_ext _ _ fun U => (c.π.app U).hom.map_zero
      map_add' _ _ := PresheafOfModules.sections_ext _ _ fun U => (c.π.app U).hom.map_add _ _ }
  fac _ _ := rfl
  uniq _ _ hm := AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun x =>
    PresheafOfModules.sections_ext _ _ fun U => ConcreteCategory.congr_hom (hm U) x

/-- Global sections of sheaves of modules, read in abelian groups, is Mathlib's global
sections functor `CategoryTheory.Sheaf.Γ` on the underlying sheaves of abelian groups.

Both sides are limits of the diagram of sections over the objects of the site —
`Stacks.Cohomology.SiteModules.isLimitGlobalSectionsForgetCone` on the left and
`CategoryTheory.Sheaf.isLimitConeΓ` on the right — so the components are the uniqueness
isomorphism of a limit cone, and naturality is checked leg by leg against
`CategoryTheory.Sheaf.ΓRes_naturality`. -/
def globalSectionsForgetAddCommGrpIso (R : Sheaf J RingCat.{r})
    [HasWeakSheafify J AddCommGrpCat.{max u w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{max u w}] :
    globalSectionsFunctor.{u, v, r, max u w} R ⋙
        forget₂ (ModuleCat.{max u w} (RingCat.sectionsSubring R.obj))
          AddCommGrpCat.{max u w} ≅
      SheafOfModules.toSheaf.{max u w} R ⋙ Sheaf.Γ J AddCommGrpCat.{max u w} := by
  refine NatIso.ofComponents (fun M =>
    (isLimitGlobalSectionsForgetCone.{u, v, r, w} R M).conePointUniqueUpToIso
      (Sheaf.isLimitConeΓ ((SheafOfModules.toSheaf.{max u w} R).obj M))) ?_
  intro M N f
  let cM := globalSectionsForgetCone.{u, v, r, w} R M
  let cN := globalSectionsForgetCone.{u, v, r, w} R N
  let hM := isLimitGlobalSectionsForgetCone.{u, v, r, w} R M
  let hN := isLimitGlobalSectionsForgetCone.{u, v, r, w} R N
  let qM := Sheaf.isLimitConeΓ ((SheafOfModules.toSheaf.{max u w} R).obj M)
  let qN := Sheaf.isLimitConeΓ ((SheafOfModules.toSheaf.{max u w} R).obj N)
  let F := globalSectionsFunctor.{u, v, r, max u w} R
  let V := forget₂ (ModuleCat.{max u w} (RingCat.sectionsSubring R.obj))
    AddCommGrpCat.{max u w}
  let eM := hM.conePointUniqueUpToIso qM
  let eN := hN.conePointUniqueUpToIso qN
  apply qN.hom_ext
  intro U
  have h1 : ((F ⋙ V).map f ≫ eN.hom) ≫
      (Sheaf.coneΓ ((SheafOfModules.toSheaf.{max u w} R).obj N)).π.app U =
        (F ⋙ V).map f ≫ cN.π.app U :=
    (Category.assoc _ _ _).trans (congrArg (fun g => (F ⋙ V).map f ≫ g)
      (IsLimit.conePointUniqueUpToIso_hom_comp hN qN U))
  have h2 : (F ⋙ V).map f ≫ cN.π.app U =
      cM.π.app U ≫ ((SheafOfModules.toSheaf.{max u w} R).map f).hom.app U := by
    ext s
    rfl
  have h3 : cM.π.app U ≫ ((SheafOfModules.toSheaf.{max u w} R).map f).hom.app U =
      (eM.hom ≫ (Sheaf.coneΓ ((SheafOfModules.toSheaf.{max u w} R).obj M)).π.app U) ≫
        ((SheafOfModules.toSheaf.{max u w} R).map f).hom.app U :=
    congrArg (fun g => g ≫ ((SheafOfModules.toSheaf.{max u w} R).map f).hom.app U)
      (IsLimit.conePointUniqueUpToIso_hom_comp hM qM U).symm
  have hnat : (Sheaf.coneΓ ((SheafOfModules.toSheaf.{max u w} R).obj M)).π.app U ≫
        ((SheafOfModules.toSheaf.{max u w} R).map f).hom.app U =
      (SheafOfModules.toSheaf.{max u w} R ⋙ Sheaf.Γ J AddCommGrpCat.{max u w}).map f ≫
        (Sheaf.coneΓ ((SheafOfModules.toSheaf.{max u w} R).obj N)).π.app U :=
    (Sheaf.ΓRes_naturality ((SheafOfModules.toSheaf.{max u w} R).map f) U).symm
  have h4 : (eM.hom ≫
        (Sheaf.coneΓ ((SheafOfModules.toSheaf.{max u w} R).obj M)).π.app U) ≫
      ((SheafOfModules.toSheaf.{max u w} R).map f).hom.app U =
      (eM.hom ≫ (SheafOfModules.toSheaf.{max u w} R ⋙
        Sheaf.Γ J AddCommGrpCat.{max u w}).map f) ≫
        (Sheaf.coneΓ ((SheafOfModules.toSheaf.{max u w} R).obj N)).π.app U :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => eM.hom ≫ g) hnat).trans (Category.assoc _ _ _).symm)
  exact h1.trans (h2.trans (h3.trans h4))

/-- **Global sections of sheaves of modules on a site are left exact.**  They preserve finite
limits in any module universe containing the universe of the objects of the site.

The forgetful functor to abelian groups reflects finite limits, and after composing with it
global sections become `CategoryTheory.Sheaf.Γ` precomposed with
`CategoryTheory.SheafOfModules.toSheaf` by
`Stacks.Cohomology.SiteModules.globalSectionsForgetAddCommGrpIso`; the first is a right
adjoint and the second preserves finite limits. -/
@[sga "4½ Arcata 1.6.5" "more general"]
theorem preservesFiniteLimits_globalSectionsFunctor (R : Sheaf J RingCat.{r})
    [HasWeakSheafify J AddCommGrpCat.{max u w}]
    [HasGlobalSectionsFunctor J AddCommGrpCat.{max u w}] :
    PreservesFiniteLimits (globalSectionsFunctor.{u, v, r, max u w} R) := by
  have h : PreservesFiniteLimits (globalSectionsFunctor.{u, v, r, max u w} R ⋙
      forget₂ (ModuleCat.{max u w} (RingCat.sectionsSubring R.obj))
        AddCommGrpCat.{max u w}) :=
    preservesFiniteLimits_of_natIso (globalSectionsForgetAddCommGrpIso.{u, v, r, w} R).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{max u w} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u w})

/-- **`H⁰ = Γ`.**  Degree-zero cohomology of `O`-modules on a site, in the sense of
[Stacks, Tag 071H], is naturally isomorphic to the functor of global sections.

This is `CategoryTheory.Functor.rightDerivedZeroIsoSelf` for
`Stacks.Cohomology.SiteModules.globalSectionsFunctor`, whose left exactness is
`Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor`.  There are no
hypotheses: sheafification of abelian presheaves in the module universe of cohomology is
supplied by `Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`, which holds for every
site. -/
def globalModuleCohomologyZeroIso (O : Sheaf J RingCat.{r}) :
    globalModuleCohomology.{u, v, r, w} O 0 ≅
      globalSectionsFunctor.{u, v, r, max u v r w} O := by
  have hs := site_hasSheafify_addCommGrp.{u, v, max r w} (J := J)
  have := preservesFiniteLimits_globalSectionsFunctor.{u, v, r, max v r w} O
  exact Functor.rightDerivedZeroIsoSelf _

/-- The structure sheaf as a sheaf of modules over itself, with its sections lifted into a
larger module universe: `Stacks.SheafOfModules.moduleULift` applied to
`CategoryTheory.SheafOfModules.unit`.

`CategoryTheory.SheafOfModules.unit` puts the module sections in the universe `r` of the
structure rings, which is in general not the module universe `max u v r w` of
`Stacks.Cohomology.SiteModules.globalModuleCohomology`; instantiating `w` at that universe
gives the structure sheaf as a module there.  Nothing is constructed here that
`Stacks.SheafOfModules.moduleULift` does not already construct, so the full and faithful comparison
`Stacks.SheafOfModules.moduleULiftFullyFaithful` applies to it. -/
def unitULift (R : Sheaf J RingCat.{r}) : SheafOfModules.{max r w} R :=
  (Stacks.SheafOfModules.moduleULift.{w, r} R).obj (SheafOfModules.unit R)

/-- The sections of `Stacks.Cohomology.SiteModules.unitULift` over an object of the site are
the sections of the structure sheaf there, lifted.  Not a `simp` lemma: its left-hand side is
a coerced type. -/
lemma unitULift_val_obj (R : Sheaf J RingCat.{r}) (X : Cᵒᵖ) :
    ((unitULift.{u, v, r, w} R).val.obj X : Type _) = ULift.{w} (R.obj.obj X) := rfl

/-- The global sections of `Stacks.Cohomology.SiteModules.unitULift` are the global sections
of the structure sheaf, that is, the ring `Γ(C, O)`: a compatible family of lifted sections is
a compatible family of sections, read through `ULift`. -/
def unitULiftSectionsEquiv (R : Sheaf J RingCat.{r}) :
    (unitULift.{u, v, r, w} R).sections ≃ GlobalSectionRing R where
  toFun s := ⟨fun U => (s.eval U).down, by
    intro U V f
    exact congrArg ULift.down ((unitULift.{u, v, r, w} R).val.sections_property s f)⟩
  invFun s := ⟨fun U => ULift.up (s.1 U), by
    intro _ _ f
    exact ULift.ext _ _ (s.2 f)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Stacks.Cohomology.SiteModules.unitULiftSectionsEquiv` forgets the lift, sectionwise. -/
@[simp]
lemma unitULiftSectionsEquiv_apply_val (R : Sheaf J RingCat.{r})
    (s : (unitULift.{u, v, r, w} R).sections) (U : Cᵒᵖ) :
    (unitULiftSectionsEquiv.{u, v, r, w} R s).val U = (s.eval U).down := rfl

/-- `Stacks.Cohomology.SiteModules.unitULiftSectionsEquiv` reinstates the lift, sectionwise. -/
@[simp]
lemma unitULiftSectionsEquiv_symm_apply_eval (R : Sheaf J RingCat.{r})
    (a : GlobalSectionRing R) (U : Cᵒᵖ) :
    ((unitULiftSectionsEquiv.{u, v, r, w} R).symm a).eval U = ULift.up (a.val U) := rfl

/-- `Stacks.Cohomology.SiteModules.unitULiftSectionsEquiv` is an isomorphism of
`Γ(C, O)`-modules: the global sections of the structure sheaf are free of rank one over
themselves.  Both the additivity and the linearity hold sectionwise by definition, because the
action of a global scalar on global sections is the sectionwise multiplication. -/
def unitULiftSectionsLinearEquiv (R : Sheaf J RingCat.{r}) :
    (unitULift.{u, v, r, w} R).sections ≃ₗ[GlobalSectionRing R] GlobalSectionRing R :=
  { unitULiftSectionsEquiv.{u, v, r, w} R with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- The underlying function of `Stacks.Cohomology.SiteModules.unitULiftSectionsLinearEquiv` is
that of `Stacks.Cohomology.SiteModules.unitULiftSectionsEquiv`. -/
@[simp]
lemma unitULiftSectionsLinearEquiv_apply (R : Sheaf J RingCat.{r})
    (s : (unitULift.{u, v, r, w} R).sections) :
    unitULiftSectionsLinearEquiv.{u, v, r, w} R s = unitULiftSectionsEquiv.{u, v, r, w} R s :=
  rfl

/-- **`H⁰(C, O) = Γ(C, O)`.**  The degree-zero cohomology of the structure sheaf, as a sheaf
of modules over itself, is the ring of global functions, as a module over itself.

This is `Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso` evaluated at
`Stacks.Cohomology.SiteModules.unitULift` and composed with
`Stacks.Cohomology.SiteModules.unitULiftSectionsLinearEquiv`. -/
def cohomologyZeroUnitLinearEquiv (O : Sheaf J RingCat.{r}) :
    (globalModuleCohomology.{u, v, r, w} O 0).obj (unitULift.{u, v, r, max u v r w} O) ≃ₗ[
        GlobalSectionRing O] GlobalSectionRing O :=
  (((globalModuleCohomologyZeroIso.{u, v, r, w} O).app
    (unitULift.{u, v, r, max u v r w} O)).toLinearEquiv).trans
      (unitULiftSectionsLinearEquiv.{u, v, r, max u v r w} O)

end Stacks.Cohomology.SiteModules

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **Degree-zero cohomology of an `𝒪_X`-module over the base ring is its module of global
sections.**  For an algebraic space `X` over `Spec A` and an `𝒪_X`-module `M`, the degree-zero
cohomology module `AlgebraicGeometry.Space.cohomologyOverBase` is the `A`-module of compatible
global sections of `M` on the small étale site, the `A`-action being the one of
`AlgebraicGeometry.Space.baseRingHom`.

This is `Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso` for the small étale
ringed site, pushed through restriction of scalars.  It is unconditional: no Noetherian
hypothesis on `A`, no morphism `X ⟶ Spec A`, no properness and no quasi-coherence. -/
def cohomologyOverBaseZeroIso (M : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX) :
    cohomologyOverBase.{u, w} A B hA X hX M 0 ≅
      (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
        (@ModuleCat.of _ _ M.sections _
          (Stacks.Cohomology.SiteModules.sectionsModule
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) M)) :=
  (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).mapIso
    ((Stacks.Cohomology.SiteModules.globalModuleCohomologyZeroIso.{u + 1, u, u, max (u + 1) w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))).app M)

/-- The `A`-linear form of `AlgebraicGeometry.Space.cohomologyOverBaseZeroIso`, which is what
a finiteness argument for [Stacks, Tag 08AS] consumes: degree-zero cohomology over the base
ring is `A`-linearly isomorphic to the global sections of the module. -/
def cohomologyOverBaseZeroLinearEquiv
    (M : Modules.{u, max (u + 1) w} B (Spec (.of A)) hA X hX) :
    cohomologyOverBase.{u, w} A B hA X hX M 0 ≃ₗ[A]
      (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
        (@ModuleCat.of _ _ M.sections _
          (Stacks.Cohomology.SiteModules.sectionsModule
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) M)) :=
  (cohomologyOverBaseZeroIso.{u, w} A B hA X hX M).toLinearEquiv

end AlgebraicGeometry.Space

end

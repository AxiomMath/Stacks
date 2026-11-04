module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SheafSectionsRightDerived
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.Homology.Injectives.Sheaf.DiagramChasing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived sections over an object, against the cohomology of the site

Let `(C, J)` be a site. The cohomology of the site is `CategoryTheory.Sheaf.functorH J p`, the
`Ext`-groups out of the constant abelian sheaf on `ℤ`; the derived sections over an object `W` of
`C` are the right derived functors of `(sheafSections J _).obj (op W)`. The two agree when `W` is
**terminal**, and that is the only general reason for them to agree: in degree zero the
agreement says exactly that the sections over `W` corepresent the same functor as the constant
sheaf, so that a sheaf with no sections over `W` has no global section at all.

This file proves both directions of that dichotomy, with no hypothesis on the site beyond the
abelian machinery, and it is what pins down the content of a hypothesis of the shape
"derived sections over `W` are the cohomology of the site" when `W` is *not* terminal.

## Main definitions

* `rightDerivedSectionsIsoFunctorH` — **the right derived functors of sections over a terminal
  object are the cohomology of the site**, in every degree. Sections over a terminal object are
  global sections (`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), whose right derived functors are
  the `Ext`-groups out of the constant sheaf (`rightDerivedΓIsoFunctorH`). The terminal object is
  arbitrary rather than a chosen one, because the objects a cohomology comparison is taken over
  are often images of a terminal object and are terminal without being equal to any canonical
  choice.
* `functorHZeroIsoCoyoneda` — the degree-zero cohomology of the site is the group of morphisms
  out of the constant sheaf on `ℤ`, which is the group of global sections.
* `sectionsIsoFunctorHZero` — from an isomorphism between the degree-zero derived sections over
  `W` and the degree-zero cohomology of the site, the sections over `W` *themselves* are that
  cohomology: taking sections over an object is left exact (Stacks 05PP), so its zeroth right
  derived functor is itself.

## Main results

* `subsingleton_hom_constantSheaf_of_subsingleton_sections` — **what such an isomorphism asserts
  in degree zero.** If the degree-zero derived sections over `W` are the degree-zero cohomology of
  the site, then every abelian sheaf with no nonzero section over `W` has no nonzero morphism out
  of the constant sheaf on `ℤ`, i.e. no nonzero global section. The hypothesis is therefore not a
  descent statement: it is the statement that `W` detects global sections, which for a terminal
  `W` is the sheaf axiom for the maximal sieve and for a general `W` fails as soon as some sheaf
  is supported away from `W`.
* `subsingleton_functorH_zero_of_subsingleton_sections` — the same conclusion written with
  `CategoryTheory.Sheaf.H`.

## Implementation notes

The coefficient universe is `AddCommGrpCat.{max u v}` for a site with objects in `Type u` and
morphisms in `Type v`. That is the shape in which `rightDerivedΓIsoFunctorH` (whose coefficients
are `AddCommGrpCat.{max u w}` for a free `w`) and
`Stacks.Injectives.preservesFiniteLimits_sheafSections` (whose coefficients are
`AddCommGrpCat.{max u v}`) are simultaneously available, and it is how
every site in this development is instantiated: the small étale sites of a scheme have objects
one universe above their morphisms, and the small models of them have the two equal.

Additivity of the sections functors is `CategoryTheory.Sheaf.additive_sheafSections_obj` and left
exactness is `Stacks.Injectives.preservesFiniteLimits_sheafSections`; neither is restated here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe v u

namespace Stacks.Cohomology.GlobalSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max u v})]
  [HasExt.{max u v} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] additive_Γ

/-- **The right derived functors of sections over a terminal object of a site are the cohomology
of that site.** Sections over a terminal object are global sections
(`CategoryTheory.Sheaf.ΓNatIsoSheafSections`), whose right derived functors are the `Ext`-groups
out of the constant sheaf on `ℤ` (`rightDerivedΓIsoFunctorH`). The terminal object is arbitrary:
the objects such a comparison is taken over are images of terminal objects, not a canonical
choice. -/
@[sga "4½ Arcata 1.6.5"]
def rightDerivedSectionsIsoFunctorH (W : C) (hW : IsTerminal W) (p : ℕ) :
    (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).rightDerived p) ≅
      Sheaf.functorH J p :=
  haveI : HasTerminal C := hW.hasTerminal
  (Functor.rightDerivedIsoOfNatIso
      (Sheaf.ΓNatIsoSheafSections J AddCommGrpCat.{max u v} hW) p).symm ≪≫
    rightDerivedΓIsoFunctorH J p

/-- **The degree-zero cohomology of a site is the group of morphisms out of the constant sheaf on
`ℤ`**, that is, the group of global sections. This is `Ext` in degree zero being morphisms. -/
def functorHZeroIsoCoyoneda :
    Sheaf.functorH J 0 ≅ preadditiveCoyoneda.obj
      (op ((constantSheaf J AddCommGrpCat.{max u v}).obj
        (AddCommGrpCat.of (ULift.{max u v} ℤ)))) :=
  ModuleSheafCohomology.extZeroIsoCoyoneda _

/-- **The sections over `W` are the degree-zero cohomology of the site as soon as their zeroth
right derived functor is.** Taking sections over an object of a site is left exact (Stacks 05PP),
so its zeroth right derived functor is itself. -/
def sectionsIsoFunctorHZero (W : C)
    (e : (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).rightDerived 0) ≅
      Sheaf.functorH J 0) :
    (sheafSections J AddCommGrpCat.{max u v}).obj (op W) ≅ Sheaf.functorH J 0 :=
  haveI := Stacks.Injectives.preservesFiniteLimits_sheafSections J (op W)
  (Functor.rightDerivedZeroIsoSelf
    ((sheafSections J AddCommGrpCat.{max u v}).obj (op W))).symm ≪≫ e

/-- Under the isomorphism of `sectionsIsoFunctorHZero`, a sheaf with no nonzero section over `W`
has vanishing degree-zero cohomology. -/
private theorem isZero_functorH_zero_of_subsingleton_sections (W : C)
    (e : (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).rightDerived 0) ≅
      Sheaf.functorH J 0)
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) (h : Subsingleton (𝒢.obj.obj (op W))) :
    IsZero ((Sheaf.functorH J 0).obj 𝒢) :=
  have : Subsingleton
      (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).obj 𝒢 : AddCommGrpCat.{max u v}) := h
  (AddCommGrpCat.isZero_of_subsingleton
    (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).obj 𝒢)).of_iso
      ((sectionsIsoFunctorHZero J W e).app 𝒢).symm

/-- **What an isomorphism "derived sections over `W` are the cohomology of the site" asserts in
degree zero.** Under such an isomorphism, an abelian sheaf with no nonzero section over `W` has
no nonzero morphism out of the constant sheaf on `ℤ`, i.e. no nonzero global section: the object
`W` *detects global sections*.

For a terminal `W` this is the sheaf axiom and the isomorphism is
`rightDerivedSectionsIsoFunctorH`. For a general `W` it is not a descent statement of any kind,
and it fails for every site carrying a nonzero sheaf whose sections over `W` vanish — for
instance the small étale site of a scheme and a sheaf supported at a point outside the image of
`W`. -/
theorem subsingleton_hom_constantSheaf_of_subsingleton_sections (W : C)
    (e : (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).rightDerived 0) ≅
      Sheaf.functorH J 0)
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) (h : Subsingleton (𝒢.obj.obj (op W))) :
    Subsingleton ((constantSheaf J AddCommGrpCat.{max u v}).obj
      (AddCommGrpCat.of (ULift.{max u v} ℤ)) ⟶ 𝒢) :=
  AddCommGrpCat.subsingleton_of_isZero
    ((isZero_functorH_zero_of_subsingleton_sections J W e 𝒢 h).of_iso
      ((functorHZeroIsoCoyoneda J).app 𝒢).symm)

/-- `subsingleton_hom_constantSheaf_of_subsingleton_sections` written with
`CategoryTheory.Sheaf.H`: under such an isomorphism, a sheaf with no nonzero section over `W` has
vanishing degree-zero cohomology over the whole site. -/
theorem subsingleton_functorH_zero_of_subsingleton_sections (W : C)
    (e : (((sheafSections J AddCommGrpCat.{max u v}).obj (op W)).rightDerived 0) ≅
      Sheaf.functorH J 0)
    (𝒢 : Sheaf J AddCommGrpCat.{max u v}) (h : Subsingleton (𝒢.obj.obj (op W))) :
    Subsingleton (Sheaf.H.{max u v, max u v} 𝒢 0) :=
  AddCommGrpCat.subsingleton_of_isZero
    (isZero_functorH_zero_of_subsingleton_sections J W e 𝒢 h)

end Stacks.Cohomology.GlobalSections

end
